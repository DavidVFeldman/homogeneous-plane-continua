/* probe3.c — does every arm of a class satisfy a disjunction of ordered patterns?
 *
 * usage: probe3 <span> <basepoint> <trigger> <patterns> [conds...]
 *   trigger  : le<x> or ge<x>
 *   patterns : semicolon-separated; each pattern is a comma-separated list of steps,
 *              a step is l<x> (a time with value <= x) or g<x> (a time with value >= x);
 *              the steps of a pattern must occur in the given order, all before the trigger.
 *   conds    : L<tl>,<th> or H<tl>,<th>
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXCL 200
#define MAXCOND 8
#define MAXPAT 8
#define MAXSTEP 4

static int HH, p_base;

typedef struct { int type; int a; int b; } Clause;
static Clause CL[MAXCL];
static int ncl;

typedef struct { int kind; int tl; int th; } Cond;
static Cond CD[MAXCOND];
static int ncond;

typedef struct { int nstep; int le[MAXSTEP]; int x[MAXSTEP]; } Pat;  /* le = 1 means <= x */
static Pat PT[MAXPAT];
static int npat;

static int trig_le = 1, trig_x = 0;

typedef struct {
    unsigned char v;
    unsigned char cst[MAXCOND];
    unsigned char st[MAXCL];
    unsigned char pp[MAXPAT];      /* how many steps of the pattern have been matched */
} State;

static void st_update(State *S, int v) {
    for (int c = 0; c < ncond; c++) {
        unsigned char s = S->cst[c];
        if (CD[c].kind == 0) { if (v <= CD[c].tl + 1) s |= 1; }
        else {
            if ((s & 2) && v >= CD[c].th - 2) s |= 4;
            if (v >= CD[c].th) s |= 1;
            if (v <= CD[c].tl + 1) s |= 2;
        }
        S->cst[c] = s;
    }
    for (int c = 0; c < ncl; c++) {
        int a = CL[c].a, b = CL[c].b;
        unsigned char q = S->st[c], nq = q;
        if (CL[c].type == 0) {
            if (q == 2 && v >= a && v <= a + 1 && v != a) nq = 3;
            if (q >= 1 && nq < 2 && v >= b - 2 && v <= b - 1) nq = 2;
            if (v == a) nq = 1;
        } else {
            if (q == 2 && v >= b - 2 && v <= b - 1 && v != b) nq = 3;
            if (q >= 1 && nq < 2 && v >= a && v <= a + 1) nq = 2;
            if (v == b) nq = 1;
        }
        S->st[c] = nq;
    }
    for (int c = 0; c < npat; c++) {
        int k = S->pp[c];
        if (k < PT[c].nstep) {
            int ok = PT[c].le[k] ? (v <= PT[c].x[k]) : (v >= PT[c].x[k]);
            if (ok) S->pp[c] = (unsigned char)(k + 1);
        }
    }
    S->v = (unsigned char)v;
}

static int st_admissible(const State *S, int v) {
    for (int c = 0; c < ncond; c++) {
        if (CD[c].kind == 0) { if (v >= CD[c].th && !(S->cst[c] & 1)) return 0; }
        else { if (v <= CD[c].tl && !((S->cst[c] & 1) || (S->cst[c] & 4))) return 0; }
    }
    for (int c = 0; c < ncl; c++) {
        unsigned char q = S->st[c];
        if (q == 0 || q == 3) continue;
        if (CL[c].type == 0) { if (v == CL[c].b) return 0; }
        else { if (v == CL[c].a) return 0; }
    }
    return 1;
}

static int probe_violated(const State *S, int v) {
    int fires = trig_le ? (v <= trig_x) : (v >= trig_x);
    if (!fires) return 0;
    for (int c = 0; c < npat; c++) if (S->pp[c] >= PT[c].nstep) return 0;
    return 1;
}

#define HASHBITS 25
#define HASHSIZE (1u << HASHBITS)
static unsigned long long *htab;

static unsigned long long st_hash(const State *S) {
    unsigned long long x = 1469598103934665603ULL;
    x ^= S->v; x *= 1099511628211ULL;
    for (int c = 0; c < ncond; c++) { x ^= S->cst[c]; x *= 1099511628211ULL; }
    for (int c = 0; c < ncl; c++) { x ^= S->st[c]; x *= 1099511628211ULL; }
    for (int c = 0; c < npat; c++) { x ^= S->pp[c]; x *= 1099511628211ULL; }
    return x ? x : 1;
}

static int seen_insert(unsigned long long key) {
    unsigned idx = (unsigned)((key * 1146111111111111111ULL) >> (64 - HASHBITS));
    while (htab[idx] != 0) { if (htab[idx] == key) return 1; idx = (idx + 1) & (HASHSIZE - 1); }
    htab[idx] = key;
    return 0;
}

typedef struct { State s; int parent; } Node;
static Node *pool;
static int pooln;
static int POOLCAP = 8000000;

int main(int argc, char **argv) {
    htab = malloc(sizeof(unsigned long long) * HASHSIZE);
    pool = malloc(sizeof(Node) * POOLCAP);
    if (!htab || !pool) { fprintf(stderr, "oom\n"); return 1; }
    HH = atoi(argv[1]);
    p_base = atoi(argv[2]);
    trig_le = strncmp(argv[3], "le", 2) == 0;
    trig_x = atoi(argv[3] + 2);
    /* patterns */
    {
        char buf[512];
        strncpy(buf, argv[4], sizeof(buf) - 1);
        buf[sizeof(buf) - 1] = 0;
        char *save1 = NULL;
        for (char *p = strtok_r(buf, ";", &save1); p; p = strtok_r(NULL, ";", &save1)) {
            Pat pt; pt.nstep = 0;
            char *save2 = NULL;
            for (char *q = strtok_r(p, ",", &save2); q; q = strtok_r(NULL, ",", &save2)) {
                pt.le[pt.nstep] = (q[0] == 'l');
                pt.x[pt.nstep] = atoi(q + 1);
                pt.nstep++;
            }
            PT[npat++] = pt;
        }
    }
    ncl = 0;
    for (int a = 0; a <= HH - 3; a++)
        for (int b = a + 3; b <= HH; b++) {
            if (ncl < MAXCL) CL[ncl++] = (Clause){0, a, b};
            if (ncl < MAXCL) CL[ncl++] = (Clause){1, a, b};
        }
    ncond = 0;
    for (int i = 5; i < argc; i++) {
        int kind = argv[i][0] == 'L' ? 1 : 0;
        int tl, th;
        sscanf(argv[i] + 1, "%d,%d", &tl, &th);
        CD[ncond++] = (Cond){kind, tl, th};
    }
    printf("span %d basepoint %d; conditions:", HH, p_base);
    for (int c = 0; c < ncond; c++)
        printf(" %s(%d,%d)", CD[c].kind ? "LowAt" : "HighAt", CD[c].tl, CD[c].th);
    printf("\nprobe: every %s %d is preceded by one of %d patterns:", trig_le ? "descent to" :
           "ascent to", trig_x, npat);
    for (int c = 0; c < npat; c++) {
        printf(" [");
        for (int k = 0; k < PT[c].nstep; k++)
            printf("%s%d%s", PT[c].le[k] ? "<=" : ">=", PT[c].x[k],
                   k + 1 < PT[c].nstep ? " then " : "");
        printf("]");
    }
    printf("\n");
    fflush(stdout);

    memset(htab, 0, sizeof(unsigned long long) * HASHSIZE);
    pooln = 0;
    State s0;
    memset(&s0, 0, sizeof(s0));
    st_update(&s0, p_base);
    seen_insert(st_hash(&s0));
    pool[pooln].s = s0; pool[pooln].parent = -1; pooln++;
    for (int head = 0; head < pooln; head++) {
        State cur = pool[head].s;
        for (int dv = -1; dv <= 1; dv++) {
            int v2 = (int)cur.v + dv;
            if (v2 < 0 || v2 > HH) continue;
            if (!st_admissible(&cur, v2)) continue;
            if (probe_violated(&cur, v2)) {
                unsigned char tmp[2048];
                int k = 0;
                tmp[k++] = (unsigned char)v2;
                int q = head;
                while (q >= 0 && k < 2048) { tmp[k++] = pool[q].s.v; q = pool[q].parent; }
                printf("VIOLATED by the arm: ");
                for (int i = k - 1; i >= 0; i--) printf("%d", tmp[i]);
                printf("\n");
                return 0;
            }
            State nx = cur;
            st_update(&nx, v2);
            if (!seen_insert(st_hash(&nx))) {
                if (pooln >= POOLCAP) { fprintf(stderr, "pool overflow\n"); exit(1); }
                pool[pooln].s = nx; pool[pooln].parent = head; pooln++;
            }
        }
    }
    printf("HOLDS on the whole class (%d states)\n", pooln);
    return 0;
}
