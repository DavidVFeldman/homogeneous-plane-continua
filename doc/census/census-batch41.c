/* census-batch40.c — span eight: branching on the dichotomy, with the full crookedness family.
 *
 * Background.  Batch 38 proved `s3_span_seven_of_cases`: at EVERY span, a basepoint of a
 * faithful crooked sequence is served unless both arms are simultaneously `HighAt (p-3) H` and
 * `LowAt L (p+3)`, where `p` is the level of the basepoint.  It also proved `dichotomy_at`: for
 * every pair of levels tl + 3 <= th, either both arms are `LowAt tl th` or both arms are
 * `HighAt tl th`, so one may branch on any level pair and serve the two branches by two walks.
 *
 * Batch 39 adds the crookedness clause family in full: on a single arm, for ANY levels
 * a + 3 <= b,
 *
 *   Cl(a,b) : s < t, f s <= a, f t >= b  ->  exists s<u<u'<t with f u >= b-2 and f u' <= a+1
 *   Dl(a,b) : s < t, f s >= b, f t <= a  ->  exists s<u<u'<t with f u <= a+1 and f u' >= b-2
 *
 * (batch 38's `Zig` is Cl(1,H)); see `HPC/Fold/Crook.lean`.  Each is a history flag with a reset,
 * so the automaton below is exact for the language it describes, and that language contains
 * every real arm: a walk serving it serves every arm.
 *
 * The search is over (level, condition flags, clause states, set of legal walk times); it is a
 * reachability search with no length bound, so a positive answer covers arms of every length.
 *
 * Usage: cc -O2 -o census39 census-batch40.c && ./census39 [span] [maxlen] [depth] [basepoint]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXLEN 30
#define MAXCL 160
#define MAXCOND 16

static int HH, p_base;

typedef struct { int type; int a; int b; } Clause;   /* 0 = Cl, 1 = Dl */
static Clause CL[MAXCL];
static int ncl;

typedef struct { int kind; int tl; int th; } Cond;   /* 0 = HighAt, 1 = LowAt */
static Cond CD[MAXCOND];
static int ncond;

typedef struct {
    unsigned char v;
    unsigned char cst[MAXCOND];
    unsigned char st[MAXCL];          /* bits 0-1 clause state, bit 4 = reset seen */
    unsigned mask;
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
    /* exact clause automaton: states 0 = the trigger level has never occurred,
       1 = since the last trigger nothing, 2 = since the last trigger the first witness level,
       3 = since the last trigger the first witness level and then the second */
    for (int c = 0; c < ncl; c++) {
        int a = CL[c].a, b = CL[c].b;
        unsigned char q = S->st[c], nq = q;
        if (CL[c].type == 0) {                       /* s at level a, t at level b */
            if (q == 2 && v >= a && v <= a + 1 && v != a) nq = 3;
            if (q >= 1 && nq < 2 && v >= b - 2 && v <= b - 1) nq = 2;
            if (v == a) nq = 1;
        } else {                                     /* s at level b, t at level a */
            if (q == 2 && v >= b - 2 && v <= b - 1 && v != b) nq = 3;
            if (q >= 1 && nq < 2 && v >= a && v <= a + 1) nq = 2;
            if (v == b) nq = 1;
        }
        S->st[c] = nq;
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

static int W[MAXLEN];
static int wlen;

static unsigned advance(unsigned mask, int v) {
    unsigned nm = 0;
    unsigned spread = mask | (mask << 1) | (mask >> 1);
    for (int u = 0; u < wlen; u++) {
        if (!((spread >> u) & 1u)) continue;
        int d = v - W[u];
        if (d >= -1 && d <= 1) nm |= (1u << u);
    }
    return nm;
}

#define HASHBITS 23
#define HASHSIZE (1u << HASHBITS)
static unsigned long long *htab;

static unsigned long long st_hash(const State *S) {
    unsigned long long x = 1469598103934665603ULL;
    x ^= S->v; x *= 1099511628211ULL;
    for (int c = 0; c < ncond; c++) { x ^= S->cst[c]; x *= 1099511628211ULL; }
    for (int c = 0; c < ncl; c++) { x ^= S->st[c]; x *= 1099511628211ULL; }
    for (int i = 0; i < 4; i++) { x ^= (S->mask >> (8 * i)) & 0xff; x *= 1099511628211ULL; }
    return x ? x : 1;
}

static int seen_insert(unsigned long long key) {
    unsigned idx = (unsigned)((key * 1146111111111111111ULL) >> (64 - HASHBITS));
    while (htab[idx] != 0) { if (htab[idx] == key) return 1; idx = (idx + 1) & (HASHSIZE - 1); }
    htab[idx] = key;
    return 0;
}

/* BFS pool with parent links, so a failing arm can be reconstructed */
typedef struct { State s; int parent; } Node;
static Node *pool;
static int pooln;
static int POOLCAP = 3000000;

static unsigned char killer[512];
static int killer_len;

/* 1 = the walk serves every arm of the class; 0 = a failing arm exists (in `killer`) */
static int serves(void) {
    if (p_base - W[0] < -1 || p_base - W[0] > 1) { killer_len = 1; killer[0] = (unsigned char)p_base; return 0; }
    memset(htab, 0, sizeof(unsigned long long) * HASHSIZE);
    pooln = 0;
    State s0;
    memset(&s0, 0, sizeof(s0));
    st_update(&s0, p_base);
    s0.mask = 1u;
    seen_insert(st_hash(&s0));
    pool[pooln].s = s0; pool[pooln].parent = -1; pooln++;
    for (int head = 0; head < pooln; head++) {
        State cur = pool[head].s;
        for (int dv = -1; dv <= 1; dv++) {
            int v2 = (int)cur.v + dv;
            if (v2 < 0 || v2 > HH) continue;
            if (!st_admissible(&cur, v2)) continue;
            State nx = cur;
            st_update(&nx, v2);
            nx.mask = advance(cur.mask, v2);
            if (nx.mask == 0) {
                /* reconstruct */
                int k = 0;
                unsigned char tmp[512];
                tmp[k++] = (unsigned char)v2;
                int q = head;
                while (q >= 0 && k < 512) { tmp[k++] = pool[q].s.v; q = pool[q].parent; }
                killer_len = k;
                for (int i = 0; i < k; i++) killer[i] = tmp[k - 1 - i];
                return 0;
            }
            if (!seen_insert(st_hash(&nx))) {
                if (pooln >= POOLCAP) { fprintf(stderr, "pool overflow\n"); exit(1); }
                pool[pooln].s = nx; pool[pooln].parent = head; pooln++;
            }
        }
    }
    return 1;
}

/* ---- sample arms, used only to filter walks quickly ---- */
#define MAXSAMP 20000
static unsigned char samples[MAXSAMP][512];
static int samplen[MAXSAMP];
static int nsamples;

static int folds_sample(int idx) {
    int v0 = samples[idx][0];
    if (v0 - W[0] < -1 || v0 - W[0] > 1) return 0;
    unsigned mask = 1u;
    for (int j = 1; j < samplen[idx]; j++) { mask = advance(mask, samples[idx][j]); if (!mask) return 0; }
    return 1;
}

static void print_walk(void) {
    printf("["); for (int u = 0; u < wlen; u++) printf("%d%s", W[u], u + 1 < wlen ? "," : ""); printf("]");
}

/* walks of a k-leg shape: from s0, alternately up and down, with given turning points */
static int build_legs(int s0, int *e, int nlegs, int dir) {
    int n = 0, v = s0;
    if (v < 0 || v > HH) return 0;
    W[n++] = v;
    for (int l = 0; l < nlegs; l++) {
        int target = e[l];
        int d = (l % 2 == 0) ? dir : -dir;
        if (d > 0 && target <= v) return 0;
        if (d < 0 && target >= v) return 0;
        while (v != target) { v += d; if (n >= MAXLEN) return 0; if (v < 0 || v > HH) return 0; W[n++] = v; }
    }
    wlen = n;
    return 1;
}

static int g_nlegs = 3;

static int rec_legs(int s0, int *e, int nlegs, int idx, int dir, int maxlen) {
    if (idx == nlegs) {
        if (!build_legs(s0, e, nlegs, dir)) return 0;
        if (wlen > maxlen) return 0;
        for (int s = 0; s < nsamples; s++) if (!folds_sample(s)) return 0;
        if (serves()) return 1;
        if (nsamples < MAXSAMP) {
            memcpy(samples[nsamples], killer, killer_len);
            samplen[nsamples] = killer_len; nsamples++;
        }
        return 0;
    }
    for (int t = 0; t <= HH; t++) { e[idx] = t; if (rec_legs(s0, e, nlegs, idx + 1, dir, maxlen)) return 1; }
    return 0;
}

static int find_shape_walk(int maxlen) {
    nsamples = 0;
    int e[8];
    for (int nlegs = 3; nlegs <= g_nlegs; nlegs++) {
        for (;;) {
            int before = nsamples;
            for (int dir = 1; dir >= -1; dir -= 2)
                for (int s0 = p_base - 1; s0 <= p_base + 1; s0++) {
                    if (s0 < 0 || s0 > HH) continue;
                    if (rec_legs(s0, e, nlegs, 0, dir, maxlen)) return wlen;
                }
            if (nsamples == before) break;
        }
    }
    return 0;
}

static int try_len(int len, int *progress) {
    wlen = len; *progress = 0;
    for (int w0 = p_base - 1; w0 <= p_base + 1; w0++) {
        if (w0 < 0 || w0 > HH) continue;
        long long total = 1LL << (len - 1);
        for (long long bits = 0; bits < total; bits++) {
            W[0] = w0;
            int ok = 1;
            for (int u = 1; u < len; u++) {
                W[u] = W[u - 1] + (((bits >> (u - 1)) & 1) ? 1 : -1);
                if (W[u] < 0 || W[u] > HH) { ok = 0; break; }
            }
            if (!ok) continue;
            int good = 1;
            for (int s = 0; s < nsamples; s++) if (!folds_sample(s)) { good = 0; break; }
            if (!good) continue;
            if (serves()) return 1;
            if (nsamples < MAXSAMP) {
                memcpy(samples[nsamples], killer, killer_len);
                samplen[nsamples] = killer_len; nsamples++; *progress = 1;
                return 0;
            }
            return 0;
        }
    }
    return 0;
}

static int find_walk_all(int maxlen) {
    nsamples = 0;
    for (int len = 3; len <= maxlen; len++) {
        for (;;) {
            int progress = 0;
            if (try_len(len, &progress)) return len;
            if (!progress) break;
        }
    }
    return 0;
}

static void set_all_clauses(void) {
    ncl = 0;
    for (int a = 0; a <= HH - 3; a++)
        for (int b = a + 3; b <= HH; b++) {
            if (ncl < MAXCL) CL[ncl++] = (Clause){0, a, b};
            if (ncl < MAXCL) CL[ncl++] = (Clause){1, a, b};
        }
}

static int g_maxlen;
static int g_shapes = 1;

static int find_walk(int maxlen) {
    if (g_shapes) return find_shape_walk(maxlen);
    return find_walk_all(maxlen);
}

static void indent(int k) { for (int i = 0; i < k; i++) printf("  "); }

static int solve(int depth, int ind) {
    int len = find_walk(g_maxlen);
    if (len) {
        indent(ind); printf("served, walk len %d: ", len); print_walk(); printf("\n");
        fflush(stdout);
        return 1;
    }
    if (depth == 0) return 0;
    for (int tl = 0; tl + 3 <= HH; tl++)
        for (int th = tl + 3; th <= HH; th++) {
            int base = ncond;
            if (base + 1 > MAXCOND) return 0;
            CD[base] = (Cond){1, tl, th}; ncond = base + 1;
            int okL = find_walk(g_maxlen);
            int wl[MAXLEN], wll = wlen;
            memcpy(wl, W, sizeof(W));
            if (!okL) {
                if (depth >= 2) {
                    indent(ind); printf("[split (%d,%d): LowAt branch needs a deeper tree]\n", tl, th);
                    fflush(stdout);
                    okL = solve(depth - 1, ind + 1);
                    wll = 0;
                }
                if (!okL) { ncond = base; continue; }
            }
            CD[base] = (Cond){0, tl, th}; ncond = base + 1;
            int okH = find_walk(g_maxlen);
            int wh[MAXLEN], whl = wlen;
            memcpy(wh, W, sizeof(W));
            if (!okH) {
                if (depth >= 2) {
                    indent(ind); printf("[split (%d,%d): HighAt branch needs a deeper tree]\n", tl, th);
                    fflush(stdout);
                    okH = solve(depth - 1, ind + 1);
                    whl = 0;
                }
            }
            ncond = base;
            if (okH) {
                indent(ind); printf("SPLIT at (%d,%d):\n", tl, th);
                if (wll) {
                    indent(ind + 1); printf("LowAt  branch: [");
                    for (int u = 0; u < wll; u++) printf("%d%s", wl[u], u + 1 < wll ? "," : "");
                    printf("]\n");
                }
                if (whl) {
                    indent(ind + 1); printf("HighAt branch: [");
                    for (int u = 0; u < whl; u++) printf("%d%s", wh[u], u + 1 < whl ? "," : "");
                    printf("]\n");
                }
                fflush(stdout);
                return 1;
            }
        }
    return 0;
}

int main(int argc, char **argv) {
    htab = malloc(sizeof(unsigned long long) * HASHSIZE);
    pool = malloc(sizeof(Node) * POOLCAP);
    if (!htab || !pool) { fprintf(stderr, "oom\n"); return 1; }
    HH = argc > 1 ? atoi(argv[1]) : 8;
    g_maxlen = argc > 2 ? atoi(argv[2]) : 16;
    int depth = argc > 3 ? atoi(argv[3]) : 1;
    int only_p = argc > 4 ? atoi(argv[4]) : -1;
    g_shapes = argc > 5 ? atoi(argv[5]) : 1;
    g_nlegs = argc > 6 ? atoi(argv[6]) : 4;
    set_all_clauses();
    for (p_base = 3; p_base + 3 <= HH; p_base++) {
        if (only_p >= 0 && p_base != only_p) continue;
        printf("######## span %d, basepoint %d ########\n", HH, p_base);
        fflush(stdout);
        ncond = 0;
        CD[ncond++] = (Cond){0, p_base - 3, HH};
        CD[ncond++] = (Cond){1, 0, p_base + 3};
        if (!solve(depth, 1)) printf("  NOT SOLVED at depth %d, maxlen %d\n", depth, g_maxlen);
        fflush(stdout);
    }
    return 0;
}
