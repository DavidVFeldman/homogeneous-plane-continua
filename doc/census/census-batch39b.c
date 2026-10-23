/* census-batch39b.c — can the span-eight leaf be split into branches on which the batch-38
 * bump-walk theorem already applies?
 *
 * `foldsOnto_bumpWalk_of_switch` (batch 38) folds any 1-Lipschitz arm in [L,H] based at an
 * interior level p onto `bumpWalk p H` as soon as the arm satisfies the *switch condition*
 *
 *     SW  : before the arm ever falls to p-3 there is a time s >= H-p with f s >= H-2,
 *
 * and its reflection `foldsOnto_bumpWalk'_of_switch` needs
 *
 *     SW' : before the arm ever rises to p+3 there is a time s >= p-L with f s <= L+2.
 *
 * `dichotomy_at` (batch 38) lets one branch on any level pair tl + 3 <= th, both arms getting
 * the same condition.  This program searches for a decision tree over such pairs, on top of the
 * leaf conditions, all of whose leaves force SW or SW'.  The arms are constrained by the leaf
 * conditions, the branch conditions, and the full crookedness clause family
 *
 *   Cl(a,b) : s<t, f s <= a, f t >= b -> exists s<u<u'<t, f u >= b-2, f u' <= a+1
 *   Dl(a,b) : s<t, f s >= b, f t <= a -> exists s<u<u'<t, f u <= a+1, f u' >= b-2
 *
 * which hold on both arms at every span.
 *
 * Usage: cc -O2 -o census39b census-batch39b.c && ./census39b [span] [depth]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXCL 160
#define MAXCOND 8

static int HH, p_base;

typedef struct { int type; int a; int b; } Clause;
static Clause CL[MAXCL];
static int ncl;

typedef struct { int kind; int tl; int th; } Cond;   /* 0 = HighAt, 1 = LowAt */
static Cond CD[MAXCOND];
static int ncond;

typedef struct {
    signed char v, tm;          /* level; time capped */
    unsigned char sw, sw2;      /* switch flags */
    unsigned char lam, vee;     /* CritLam / CritVee flag words */
    unsigned char cst[MAXCOND];
    unsigned char st[MAXCL];
    unsigned sr[MAXCL / 32 + 1];
} Full;

static int TCAP;

static void full_update(Full *F, int v, int newtime) {
    for (int c = 0; c < ncond; c++) {
        unsigned char s = F->cst[c];
        if (CD[c].kind == 0) { if (v <= CD[c].tl + 1) s |= 1; }
        else {
            if ((s & 2) && v >= CD[c].th - 2) s |= 4;
            if (v >= CD[c].th) s |= 1;
            if (v <= CD[c].tl + 1) s |= 2;
        }
        F->cst[c] = s;
    }
    for (int c = 0; c < ncl; c++) {
        int a = CL[c].a, b = CL[c].b;
        unsigned char s = F->st[c];
        if (CL[c].type == 0) {
            if (v <= a) { s = 0; F->sr[c >> 5] |= 1u << (c & 31); }
            else { if (s >= 1 && v <= a + 1) s = 2; else if (v >= b - 2 && s == 0) s = 1; }
        } else {
            if (v >= b) { s = 0; F->sr[c >> 5] |= 1u << (c & 31); }
            else { if (s >= 1 && v >= b - 2) s = 2; else if (v <= a + 1 && s == 0) s = 1; }
        }
        F->st[c] = s;
    }
    {   /* CritLam flags (kappa = HH - 1, interior p):
           bit0 seen >= kappa; bit1 seen >= kappa-1 once; bit2 twice;
           bit3 non-ascending step seen; bit4 (bit3 then later >= kappa-1) */
        int kap = HH - 1;
        unsigned char s = F->lam;
        if (v >= kap - 1) { if (s & 8) s |= 16; }
        if (v >= kap) s |= 1;
        if (v >= kap - 1) { if (s & 2) s |= 4; else s |= 2; }
        if (v <= F->v) s |= 8;                    /* the step just taken was non-ascending */
        F->lam = s;
        /* CritVee flags, mirrored (kappa' = L + 1 = 1) */
        int kav = 1;
        unsigned char t = F->vee;
        if (v <= kav + 1) { if (t & 8) t |= 16; }
        if (v <= kav) t |= 1;
        if (v <= kav + 1) { if (t & 2) t |= 4; else t |= 2; }
        if (v >= F->v) t |= 8;
        F->vee = t;
    }
    if (newtime >= HH - p_base && v >= HH - 2) F->sw = 1;
    if (newtime >= p_base && v <= 2) F->sw2 = 1;     /* L = 0, so p - L = p, L + 2 = 2 */
    F->v = (signed char)v;
    F->tm = (signed char)(newtime > TCAP ? TCAP : newtime);
}

static int cond_admissible(const Full *F, int v) {
    for (int c = 0; c < ncond; c++) {
        if (CD[c].kind == 0) { if (v >= CD[c].th && !(F->cst[c] & 1)) return 0; }
        else { if (v <= CD[c].tl && !((F->cst[c] & 1) || (F->cst[c] & 4))) return 0; }
    }
    for (int c = 0; c < ncl; c++) {
        if (!((F->sr[c >> 5] >> (c & 31)) & 1u)) continue;
        if (CL[c].type == 0) { if (v >= CL[c].b && F->st[c] != 2) return 0; }
        else { if (v <= CL[c].a && F->st[c] != 2) return 0; }
    }
    return 1;
}

#define HASHBITS 22
#define HASHSIZE (1u << HASHBITS)
static unsigned long long *htab;

static unsigned long long state_hash(const Full *F) {
    unsigned long long x = 1469598103934665603ULL;
    const unsigned char *q = (const unsigned char *)F;
    size_t n = sizeof(signed char) * 2 + 2;
    for (size_t i = 0; i < n; i++) { x ^= q[i]; x *= 1099511628211ULL; }
    x ^= F->lam; x *= 1099511628211ULL;
    x ^= F->vee; x *= 1099511628211ULL;
    for (int c = 0; c < ncond; c++) { x ^= F->cst[c]; x *= 1099511628211ULL; }
    for (int c = 0; c < ncl; c++) {
        x ^= (unsigned char)(F->st[c] | (((F->sr[c >> 5] >> (c & 31)) & 1u) << 4));
        x *= 1099511628211ULL;
    }
    return x ? x : 1;
}

static int seen_insert(unsigned long long key) {
    unsigned idx = (unsigned)((key * 1146111111111111111ULL) >> (64 - HASHBITS));
    while (htab[idx] != 0) { if (htab[idx] == key) return 1; idx = (idx + 1) & (HASHSIZE - 1); }
    htab[idx] = key;
    return 0;
}

static Full *stk;
static int stkn;

/* which : 0 = test SW, 1 = test SW' ; returns 1 if every admissible arm satisfies it */
static int implies_switch(int which) {
    memset(htab, 0, sizeof(unsigned long long) * HASHSIZE);
    TCAP = HH + 2;
    stkn = 0;
    Full nd;
    memset(&nd, 0, sizeof(nd));
    full_update(&nd, p_base, 0);
    seen_insert(state_hash(&nd));
    stk[stkn++] = nd;
    while (stkn > 0) {
        Full cur = stk[--stkn];
        for (int dv = -1; dv <= 1; dv++) {
            int v2 = cur.v + dv;
            if (v2 < 0 || v2 > HH) continue;
            if (!cond_admissible(&cur, v2)) continue;
            if (which == 0 && v2 <= p_base - 3 && !cur.sw) return 0;
            if (which == 1 && v2 >= p_base + 3 && !cur.sw2) return 0;
            if (which == 2 && v2 <= p_base - 2 && !((cur.lam & 1) || (cur.lam & 4) || (cur.lam & 16))) return 0;
            if (which == 3 && v2 >= p_base + 2 && !((cur.vee & 1) || (cur.vee & 4) || (cur.vee & 16))) return 0;
            Full nx = cur;
            full_update(&nx, v2, cur.tm + 1);
            if (!seen_insert(state_hash(&nx))) {
                if (stkn >= 2000000) { fprintf(stderr, "stack overflow\n"); exit(1); }
                stk[stkn++] = nx;
            }
        }
    }
    return 1;
}

static void indent(int k) { for (int i = 0; i < k; i++) printf("  "); }

static int solve(int depth, int ind) {
    if (implies_switch(2)) { indent(ind); printf("CritLam holds -> the Lambda walk serves\n"); return 1; }
    if (implies_switch(3)) { indent(ind); printf("CritVee holds -> the V walk serves\n"); return 1; }
    if (implies_switch(0)) { indent(ind); printf("SW  holds -> bumpWalk serves\n"); return 1; }
    if (implies_switch(1)) { indent(ind); printf("SW' holds -> bumpWalk' serves\n"); return 1; }
    if (depth == 0) return 0;
    for (int tl = 0; tl + 3 <= HH; tl++)
        for (int th = tl + 3; th <= HH; th++) {
            int base = ncond;
            if (base + 1 > MAXCOND) return 0;
            CD[base] = (Cond){1, tl, th}; ncond = base + 1;
            /* cheap pre-test of both branches at depth 0 before recursing */
            int q1 = implies_switch(2) || implies_switch(3) || implies_switch(0) || implies_switch(1);
            CD[base] = (Cond){0, tl, th};
            int q2 = implies_switch(2) || implies_switch(3) || implies_switch(0) || implies_switch(1);
            ncond = base;
            if (depth == 1 && !(q1 && q2)) continue;
            CD[base] = (Cond){1, tl, th}; ncond = base + 1;
            char buf[4096]; buf[0] = 0;
            int okL;
            {
                printf("%*s[try split (%d,%d), LowAt branch]\n", ind * 2, "", tl, th);
                okL = solve(depth - 1, ind + 1);
            }
            ncond = base;
            if (!okL) continue;
            CD[base] = (Cond){0, tl, th}; ncond = base + 1;
            printf("%*s[try split (%d,%d), HighAt branch]\n", ind * 2, "", tl, th);
            int okH = solve(depth - 1, ind + 1);
            ncond = base;
            if (okH) { indent(ind); printf("SPLIT at (%d,%d) works\n", tl, th); return 1; }
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

int main(int argc, char **argv) {
    htab = malloc(sizeof(unsigned long long) * HASHSIZE);
    stk = malloc(sizeof(Full) * 2000001);
    if (!htab || !stk) { fprintf(stderr, "oom\n"); return 1; }
    HH = argc > 1 ? atoi(argv[1]) : 8;
    int depth = argc > 2 ? atoi(argv[2]) : 2;
    set_all_clauses();
    for (p_base = 3; p_base + 3 <= HH; p_base++) {
        printf("######## span %d, basepoint %d ########\n", HH, p_base);
        ncond = 0;
        CD[ncond++] = (Cond){0, p_base - 3, HH};
        CD[ncond++] = (Cond){1, 0, p_base + 3};
        if (!solve(depth, 1)) printf("  NOT SOLVED at depth %d\n", depth);
        fflush(stdout);
    }
    return 0;
}
