/*
 * scheduler.c
 * Tugas 2 OS - Varian SRTF (Shortest Remaining Time First)
 *
 * BAGIAN FILE INI: PIC Algoritma Inti SRTF & Process State
 *   - loop penjadwalan SRTF (preemptive)
 *   - pencatatan kejadian preemption
 *   - pencatatan perubahan state tiap proses (Bagian 7)
 *   - hasil jejak eksekusi (segmen) untuk dipakai PIC lain
 *
 * Data yang dihasilkan srtf_run() untuk PIC lain:
 *   Process.start_time       -> waktu pertama kali RUNNING (PIC 4: Response Time)
 *   Process.completion_time  -> Completion Time (PIC 4: TAT, WT)
 *   SimResult.segments       -> jejak eksekusi {pid, start, end}, pid = -1 berarti CPU idle
 *                               (PIC 3: Gantt Chart dan Context Switch)
 *   SimResult.preemptions    -> daftar kejadian preemption (PIC 3: Preemption Information)
 *
 * Fungsi init_process() dan main() di bawah hanya kerangka sementara untuk
 * pengujian. Bagian input (PIC 1), Gantt Chart dan Context Switch (PIC 3),
 * serta metrik (PIC 4) akan menggantikan bagian bertanda [SEMENTARA].
 */

#include <stdio.h>

#define MAX_PROC     50
#define MAX_HISTORY  128   /* tiap proses paling banyak ~2n+2 entri state */
#define MAX_SEGMENTS 1024
#define MAX_PREEMPT  128

/* ---------- Struktur data ---------- */

typedef enum { NEW, READY, RUNNING, BLOCKED, TERMINATED } State;

typedef struct {
    State state;
    int   time;
} StateEntry;

typedef struct {
    int pid;
    int arrival_time;
    int burst_time;
    int remaining_time;
    State state;
    int start_time;        /* -1 selama proses belum pernah RUNNING */
    int completion_time;
    StateEntry history[MAX_HISTORY];
    int history_count;
} Process;

typedef struct {
    int pid;               /* -1 berarti CPU idle */
    int start;
    int end;
} Segment;

typedef struct {
    int time;
    int preempted_pid;
    int remaining;         /* sisa BT proses yang di-preempt saat itu */
    int next_pid;
} PreemptEvent;

typedef struct {
    Segment      segments[MAX_SEGMENTS];
    int          segment_count;
    PreemptEvent preemptions[MAX_PREEMPT];
    int          preempt_count;
    int          total_time;
} SimResult;

/* ---------- Pencatatan state ---------- */

static const char *state_name(State s) {
    switch (s) {
        case NEW:        return "NEW";
        case READY:      return "READY";
        case RUNNING:    return "RUNNING";
        case BLOCKED:    return "BLOCKED";
        case TERMINATED: return "TERMINATED";
    }
    return "?";
}

/* Ubah state proses dan catat waktu perubahannya. */
static void log_state(Process *p, State s, int t) {
    p->state = s;
    if (p->history_count < MAX_HISTORY) {
        p->history[p->history_count].state = s;
        p->history[p->history_count].time  = t;
        p->history_count++;
    }
}

/* [SEMENTARA] Seharusnya dibuat PIC 1 bersama pembacaan input. */
static void init_process(Process *p, int pid, int at, int bt) {
    p->pid             = pid;
    p->arrival_time    = at;
    p->burst_time      = bt;
    p->remaining_time  = bt;
    p->state           = NEW;
    p->start_time      = -1;
    p->completion_time = 0;
    p->history_count   = 0;
    p->history[p->history_count].state = NEW;
    p->history[p->history_count].time  = 0;
    p->history_count++;
}

/* ---------- Pencatatan jejak eksekusi ---------- */

/* Tambahkan 1 satuan waktu [t, t+1) untuk pid (-1 = idle).
 * Tick yang berurutan untuk pid yang sama otomatis digabung jadi satu segmen. */
static void add_tick(SimResult *r, int pid, int t) {
    if (r->segment_count > 0) {
        Segment *last = &r->segments[r->segment_count - 1];
        if (last->pid == pid && last->end == t) {
            last->end = t + 1;
            return;
        }
    }
    if (r->segment_count < MAX_SEGMENTS) {
        Segment *s = &r->segments[r->segment_count++];
        s->pid   = pid;
        s->start = t;
        s->end   = t + 1;
    }
}

/* ---------- Algoritma SRTF ---------- */

/*
 * Memilih proses READY dengan sisa burst time terkecil.
 * Aturan tie-break kalau sisa burst time sama:
 *   1. Arrival Time terkecil
 *   2. PID terkecil
 * Mengembalikan indeks proses, atau -1 kalau tidak ada proses READY.
 */
static int pick_shortest_ready(const Process p[], int n) {
    int best = -1;
    for (int i = 0; i < n; i++) {
        if (p[i].state != READY) continue;
        if (best == -1) { best = i; continue; }

        if (p[i].remaining_time < p[best].remaining_time) {
            best = i;
        } else if (p[i].remaining_time == p[best].remaining_time) {
            if (p[i].arrival_time < p[best].arrival_time ||
                (p[i].arrival_time == p[best].arrival_time && p[i].pid < p[best].pid)) {
                best = i;
            }
        }
    }
    return best;
}

/*
 * Simulasi SRTF per satuan waktu (t bertambah 1 tiap iterasi).
 * Keputusan penjadwalan diambil di awal setiap satuan waktu:
 *   1. Proses yang Arrival Time-nya sudah tercapai berubah NEW -> READY.
 *   2. Cari proses READY dengan sisa burst time terkecil.
 *   3. Kalau CPU kosong, proses itu langsung dijalankan.
 *      Kalau CPU sedang dipakai, proses itu hanya menggantikan (preempt)
 *      bila sisa burst time-nya LEBIH KECIL dari proses yang sedang jalan.
 *      Kalau sama, proses yang sedang jalan dilanjutkan supaya tidak ada
 *      context switch yang tidak perlu.
 *   4. Proses yang berjalan dieksekusi 1 satuan waktu. Bila sisa burst
 *      time menjadi 0, proses TERMINATED dan Completion Time dicatat.
 * Asumsi: semua burst time > 0 (divalidasi oleh bagian input).
 */
void srtf_run(Process p[], int n, SimResult *res) {
    int t = 0;
    int done = 0;
    int running = -1;      /* indeks proses yang sedang RUNNING, -1 = idle */

    res->segment_count = 0;
    res->preempt_count = 0;

    while (done < n) {
        /* 1. Kedatangan proses: NEW -> READY */
        for (int i = 0; i < n; i++) {
            if (p[i].state == NEW && p[i].arrival_time <= t) {
                log_state(&p[i], READY, t);
            }
        }

        /* 2. Kandidat terbaik di antara proses READY */
        int best = pick_shortest_ready(p, n);

        /* 3. Keputusan: dispatch atau preempt */
        int dispatch = 0;
        if (running == -1) {
            if (best != -1) dispatch = 1;
        } else if (best != -1 &&
                   p[best].remaining_time < p[running].remaining_time) {
            if (res->preempt_count < MAX_PREEMPT) {
                PreemptEvent *e = &res->preemptions[res->preempt_count++];
                e->time          = t;
                e->preempted_pid = p[running].pid;
                e->remaining     = p[running].remaining_time;
                e->next_pid      = p[best].pid;
            }
            log_state(&p[running], READY, t);   /* RUNNING -> READY */
            dispatch = 1;
        }

        if (dispatch) {
            log_state(&p[best], RUNNING, t);    /* READY -> RUNNING */
            if (p[best].start_time == -1) {
                p[best].start_time = t;         /* untuk Response Time */
            }
            running = best;
        }

        /* 4. Eksekusi 1 satuan waktu (atau idle kalau tidak ada proses) */
        if (running == -1) {
            add_tick(res, -1, t);
            t++;
            continue;
        }

        add_tick(res, p[running].pid, t);
        p[running].remaining_time--;
        t++;

        if (p[running].remaining_time == 0) {
            p[running].completion_time = t;
            log_state(&p[running], TERMINATED, t);
            running = -1;
            done++;
        }
    }

    res->total_time = t;
}

/* ---------- Output bagian ini ---------- */

static void print_separator(void) {
    for (int i = 0; i < 69; i++) putchar('=');
    putchar('\n');
}

/* Output "PREEMPTION INFORMATION" khusus Varian SRTF. */
void print_preemption_info(const SimResult *res) {
    print_separator();
    printf("PREEMPTION INFORMATION\n");
    print_separator();

    if (res->preempt_count == 0) {
        printf("Tidak ada preemption.\n");
    }
    for (int i = 0; i < res->preempt_count; i++) {
        const PreemptEvent *e = &res->preemptions[i];
        printf("t=%d : P%d PREEMPTED (sisa BT=%d) -> P%d RUNNING\n",
               e->time, e->preempted_pid, e->remaining, e->next_pid);
    }
    printf("\nTotal Preemption : %d\n", res->preempt_count);
}

/* Output Bagian 7: PROCESS STATE TRANSITIONS. */
void print_state_transitions(const Process p[], int n) {
    print_separator();
    printf("PROCESS STATE TRANSITIONS\n");
    print_separator();

    for (int i = 0; i < n; i++) {
        printf("P%d : ", p[i].pid);
        for (int k = 0; k < p[i].history_count; k++) {
            if (k > 0) printf(" -> ");
            if (p[i].history[k].state == NEW) {
                printf("NEW");
            } else {
                printf("%s (t=%d)", state_name(p[i].history[k].state),
                       p[i].history[k].time);
            }
        }
        printf("\n");
    }
}

/* ---------- [SEMENTARA] main untuk pengujian ---------- */

int main(void) {
    Process p[MAX_PROC];
    SimResult res;
    int n;

    printf("Jumlah proses: ");
    if (scanf("%d", &n) != 1 || n < 1 || n > MAX_PROC) {
        fprintf(stderr, "Jumlah proses harus 1 sampai %d\n", MAX_PROC);
        return 1;
    }
    for (int i = 0; i < n; i++) {
        int at, bt;
        printf("P%d - masukkan Arrival Time dan Burst Time: ", i + 1);
        if (scanf("%d %d", &at, &bt) != 2 || at < 0 || bt < 1) {
            fprintf(stderr, "Input tidak valid (AT >= 0, BT >= 1)\n");
            return 1;
        }
        init_process(&p[i], i + 1, at, bt);
    }
    printf("\n");

    srtf_run(p, n, &res);

    /* [SEMENTARA] Pengganti Gantt Chart (PIC 3) dan Scheduling Table (PIC 4). */
    printf("[DEBUG] Jejak eksekusi:");
    for (int i = 0; i < res.segment_count; i++) {
        if (res.segments[i].pid == -1)
            printf(" | IDLE %d-%d", res.segments[i].start, res.segments[i].end);
        else
            printf(" | P%d %d-%d", res.segments[i].pid,
                   res.segments[i].start, res.segments[i].end);
    }
    printf(" |\n");
    for (int i = 0; i < n; i++) {
        printf("[DEBUG] P%d AT=%d BT=%d ST=%d CT=%d\n", p[i].pid,
               p[i].arrival_time, p[i].burst_time,
               p[i].start_time, p[i].completion_time);
    }
    printf("\n");

    print_preemption_info(&res);
    printf("\n");
    print_state_transitions(p, n);

    return 0;
}
