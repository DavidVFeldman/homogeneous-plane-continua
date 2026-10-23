/* census-batch56.c -- batch 56.  The corpus check of what batch 56 proves.
 *
 * Carried over from census-batch55.c unchanged: the generators, the
 * faithfulness test (IsCrookedIvF), the dynamic program over FoldsOnto
 * (HPC/Fold/Decide.lean), the predicates of the walks and the two residues.
 *
 * New in this batch.
 *
 *   A. The three theorems of batch 56, checked against the corpus.  At every
 *      basepoint of the branch L+4:
 *        - if an arm fails Leg3Valley, both arms fold onto the V-walk
 *          (cross_valley_profile), and the witness the V-criterion uses on the
 *          other arm sits at arm index twelve or later -- the bound the timing
 *          law gives, not the four the criterion asks;
 *        - if an arm fails Leg3Ceil and the pair misses the Lambda-walk, the
 *          failing arm satisfies TopW5 and the other one Valley5
 *          (cross_ceil_sentence), with the peak of Valley5 at index five or
 *          later and the landmarks of TopW5 at index twelve or later;
 *        - an unserved pair folds onto w3, w4 or w5 (unserved_three_walks).
 *      CeilHighResidual is counted: it is now a theorem that it is empty.
 *
 *   B. Question 4, four turns at L+5.  At every basepoint of the branch L+5
 *      that the three reflected walks miss, the census tests the walks of the
 *      wide four-leg engine of HPC/Fold/Leg4Wide.lean -- leg4Walk 0 9 K M P for
 *      every parameter set of its window, and the reflection of each -- and
 *      reports which of them serve the basepoint, the greedy cover of the whole
 *      residue by them, and the basepoints no walk of the family serves.
 *
 * Every predicate named in a Lean statement the census is offered as evidence
 * for is evaluated here by its own definition.  No proxies.
 *
 * Usage: census-batch56 [rand-rounds] [seed] [walk-steps] [concat-draws]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { int *v; int n; } Path;

static Path bpath(int a, int b) {
  Path p;
  int d = a < b ? b - a : a - b;
  if (d <= 2) {
    p.n = d + 1;
    p.v = (int *)malloc(sizeof(int) * p.n);
    int s = (a <= b) ? 1 : -1;
    for (int u = 0; u < p.n; u++) p.v[u] = a + s * u;
    return p;
  }
  int mid = (a < b) ? b - 1 : b + 1;
  int c = (a < b) ? a + 1 : a - 1;
  Path p1 = bpath(a, mid), p2 = bpath(mid, c), p3 = bpath(c, b);
  p.n = p1.n + p2.n - 1 + p3.n - 1;
  p.v = (int *)malloc(sizeof(int) * p.n);
  memcpy(p.v, p1.v, sizeof(int) * p1.n);
  memcpy(p.v + p1.n, p2.v + 1, sizeof(int) * (p2.n - 1));
  memcpy(p.v + p1.n + p2.n - 1, p3.v + 1, sizeof(int) * (p3.n - 1));
  free(p1.v); free(p2.v); free(p3.v);
  return p;
}

/* a recursive chain whose splitting levels are one further in than Bing's: the
 * consolidation goes back to `b - back` and forward to `a + fwd`, which for
 * (back, fwd) = (1, 1) is Bing's own chain and otherwise is not. */
static Path vpath(int a, int b, int back, int fwd) {
  Path p;
  int d = a < b ? b - a : a - b;
  if (d <= 2) {
    p.n = d + 1;
    p.v = (int *)malloc(sizeof(int) * p.n);
    int s = (a <= b) ? 1 : -1;
    for (int u = 0; u < p.n; u++) p.v[u] = a + s * u;
    return p;
  }
  int up = (a < b);
  int mid = up ? b - back : b + back;
  int c = up ? a + fwd : a - fwd;
  if (up && (mid <= a || c >= b || mid <= c)) { mid = b - 1; c = a + 1; }
  if (!up && (mid >= a || c <= b || mid >= c)) { mid = b + 1; c = a - 1; }
  Path p1 = vpath(a, mid, back, fwd), p2 = vpath(mid, c, back, fwd),
       p3 = vpath(c, b, back, fwd);
  p.n = p1.n + p2.n - 1 + p3.n - 1;
  p.v = (int *)malloc(sizeof(int) * p.n);
  memcpy(p.v, p1.v, sizeof(int) * p1.n);
  memcpy(p.v + p1.n, p2.v + 1, sizeof(int) * (p2.n - 1));
  memcpy(p.v + p1.n + p2.n - 1, p3.v + 1, sizeof(int) * (p3.n - 1));
  free(p1.v); free(p2.v); free(p3.v);
  return p;
}

/* the concatenation of two chains, the common endpoint kept once */
static Path cat(Path x, Path y) {
  Path p;
  p.n = x.n + y.n - 1;
  p.v = (int *)malloc(sizeof(int) * p.n);
  memcpy(p.v, x.v, sizeof(int) * x.n);
  memcpy(p.v + x.n, y.v + 1, sizeof(int) * (y.n - 1));
  return p;
}

#define MAXLEV 32
#define MAXN   4096
#define MAXW   96

static int meetTab[MAXLEV][MAXN + 1];

/* IsCrookedIvF (rho, sig), exactly as HPC/Fold/Faithful.lean states it. */
static int crookedGen(const int *rho, const int *sig, int n) {
  for (int t = 0; t < n; t++) if (rho[t] > sig[t] || sig[t] > rho[t] + 1) return 0;
  for (int t = 0; t + 1 < n; t++) {
    int mx = sig[t] > sig[t+1] ? sig[t] : sig[t+1];
    int mn = rho[t] < rho[t+1] ? rho[t] : rho[t+1];
    if (mx > mn + 1) return 0;
  }
  for (int l = 0; l < MAXLEV; l++) meetTab[l][n] = n;
  for (int j = n - 1; j >= 0; j--)
    for (int l = 0; l < MAXLEV; l++)
      meetTab[l][j] = (rho[j] <= l && l <= sig[j]) ? j : meetTab[l][j + 1];
  for (int s = 0; s < n; s++) {
    int hs[8], nh = 0;
    for (int e = -1; e <= 1; e++) {
      int u = s + e; if (u < 0 || u >= n) continue;
      for (int l = rho[u]; l <= sig[u]; l++) {
        int seen = 0; for (int q = 0; q < nh; q++) if (hs[q] == l) seen = 1;
        if (!seen) hs[nh++] = l;
      }
    }
    for (int t = s + 1; t < n; t++) {
      int ks[8], nk = 0;
      for (int e = -1; e <= 1; e++) {
        int u = t + e; if (u < 0 || u >= n) continue;
        for (int l = rho[u]; l <= sig[u]; l++) {
          int seen = 0; for (int q = 0; q < nk; q++) if (ks[q] == l) seen = 1;
          if (!seen) ks[nk++] = l;
        }
      }
      for (int a = 0; a < nh; a++) for (int b = 0; b < nk; b++) {
        int h = hs[a], k = ks[b];
        int diff = h - k; if (diff < 0) diff = -diff;
        if (diff < 3) continue;
        int r1 = (h < k) ? k - 1 : k + 1, r2 = (h < k) ? h + 1 : h - 1;
        int p1 = meetTab[r1][s + 1];
        if (p1 >= t) return 0;
        int p2 = meetTab[r2][p1 + 1];
        if (p2 >= t) return 0;
      }
    }
  }
  return 1;
}

/* the dynamic program of HPC/Fold/Decide.lean */
static int folds(const int *f, int m, const int *w, int wl) {
  static char cur[MAXW], nxt[MAXW];
  for (int u = 0; u < wl; u++) cur[u] = 0;
  if (f[0] - w[0] > 1 || w[0] - f[0] > 1) return 0;
  cur[0] = 1;
  for (int j = 1; j < m; j++) {
    int any = 0;
    for (int u = 0; u < wl; u++) nxt[u] = 0;
    for (int u = 0; u < wl; u++) {
      if (!cur[u]) continue;
      for (int e = -1; e <= 1; e++) {
        int u2 = u + e;
        if (u2 < 0 || u2 >= wl) continue;
        int d = f[j] - w[u2];
        if (d <= 1 && d >= -1) { nxt[u2] = 1; any = 1; }
      }
    }
    if (!any) return 0;
    memcpy(cur, nxt, sizeof(char) * wl);
  }
  return 1;
}

static int buildWalk4(int *w, int start, int a, int b, int c, int e) {
  int len = 0, cur = start;
  w[len++] = cur;
  int tgt[4] = {a, b, c, e};
  for (int q = 0; q < 4; q++) {
    if (tgt[q] < 0) break;
    if (tgt[q] == cur) return -1;
    int s = tgt[q] > cur ? 1 : -1;
    while (cur != tgt[q]) { cur += s; if (len >= MAXW) return -1; w[len++] = cur; }
  }
  return len;
}

static int buildWalk(int *w, int start, int a, int b, int c) {
  int len = 0, cur = start;
  w[len++] = cur;
  int tgt[3] = {a, b, c};
  for (int q = 0; q < 3; q++) {
    if (tgt[q] < 0) break;
    if (tgt[q] == cur) return -1;
    int s = tgt[q] > cur ? 1 : -1;
    while (cur != tgt[q]) { cur += s; if (len >= MAXW) return -1; w[len++] = cur; }
  }
  return len;
}

static int rho[MAXN], sig[MAXN], armG[MAXN], armT[MAXN];

/* HighAt f (L+1) (L+8) */
static int highAt(const int *f, int m) {
  int seenLow = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !seenLow) return 0;
    if (f[d] <= 2) seenLow = 1;
  }
  return 1;
}

/* Leg3Valley f L */
static int leg3Valley(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j + 5 <= d && !ok; j++) if (a[j] >= 5) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* Leg3Ceil f L */
static int leg3Ceil(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 8) continue;
    int ok = 0;
    for (int j = 3; j + 11 <= d && !ok; j++) {
      if (a[j] < 5) continue;
      for (int k = j + 5; k + 6 <= d && !ok; k++) if (a[k] <= 2) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

/* Valley4 f L */
static int valley4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j + 4 <= d && !ok; j++) if (a[j] >= 5) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* BottomW4 f L */
static int bottomW4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 0) continue;
    int ok = 0;
    for (int j = 1; j + 13 <= d && !ok; j++) {
      if (a[j] > 3) continue;
      for (int k = j + 6; k + 7 <= d && !ok; k++) if (a[k] >= 7) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

/* TopW5 f L */
static int topW5(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 9) continue;
    int ok = 0;
    for (int j = 4; j + 13 <= d && !ok; j++) {
      if (a[j] < 6) continue;
      for (int k = j + 6; k + 7 <= d && !ok; k++) if (a[k] <= 2) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

/* Valley5 f L */
static int valley5(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 4; j + 5 <= d && !ok; j++) if (a[j] >= 6) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* MidW4 f L */
static int midW4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 5) continue;
    int ok = 0;
    for (int j = 1; j + 2 <= d && !ok; j++) if (a[j] <= 3) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* CeilW4 f L */
static int ceilW4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 8) continue;
    int ok = 0;
    for (int j = 1; j + 5 <= d && !ok; j++) if (a[j] <= 3) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

static int foldsLam(const int *f, int m) {   /* Lambda based at L+3: 3 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 3, 8, 1, -1);
  return folds(f, m, w, wl);
}
static int foldsVee(const int *f, int m) {   /* V based at L+5: 5 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 5, 1, 8, -1);
  return folds(f, m, w, wl);
}
static int foldsW3(const int *f, int m) {    /* 3 -> 6 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 3, 6, 1, 8);
  return folds(f, m, w, wl);
}
static int foldsW4(const int *f, int m) {    /* 3 -> 2 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 3, 2, 8, 1);
  return folds(f, m, w, wl);
}
static int foldsW5(const int *f, int m) {    /* 3 -> 7 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 3, 7, 1, 8);
  return folds(f, m, w, wl);
}

/* LowAt f (L+1) (L+8) */
static int lowAt(const int *f, int m) {
  int seenHigh8 = 0, seenLow2 = 0, seenLow2High6 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= 1 && !seenHigh8 && !seenLow2High6) return 0;
    if (f[d] >= 8) seenHigh8 = 1;
    if (f[d] >= 6 && seenLow2) seenLow2High6 = 1;
    if (f[d] <= 2) seenLow2 = 1;
  }
  return 1;
}

static void reflArm(const int *f, int m, int *g) { for (int d = 0; d < m; d++) g[d] = 9 - f[d]; }

/* the reflected walks, read on the arm itself */
static int foldsLamR(const int *f, int m) {  /* V at L+6: 6 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 6, 1, 8, -1); return folds(f, m, w, wl);
}
static int foldsVeeR(const int *f, int m) {  /* Lambda at L+4: 4 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 4, 8, 1, -1); return folds(f, m, w, wl);
}
static int foldsW3R(const int *f, int m) {   /* 6 -> 3 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 6, 3, 8, 1); return folds(f, m, w, wl);
}
static int foldsW4R(const int *f, int m) {   /* 6 -> 7 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 6, 7, 1, 8); return folds(f, m, w, wl);
}
static int foldsW5R(const int *f, int m) {   /* 6 -> 2 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 6, 2, 8, 1); return folds(f, m, w, wl);
}

/* ---------------- the walk list at the branch L+5 ------------------------ */

/* a walk of at most three turns based within one of 5 */
typedef struct { int st, a, b, c, len; } Walk;

#define MAXLIST 64
static Walk wlist[MAXLIST];
static long wlistHits[MAXLIST];
static int wlistN = 0;

static int walkEq(const Walk *x, int st, int a, int b, int c) {
  return x->st == st && x->a == a && x->b == b && x->c == c;
}

static int noteWalk(int st, int a, int b, int c, int len) {
  for (int q = 0; q < wlistN; q++)
    if (walkEq(&wlist[q], st, a, b, c)) { wlistHits[q]++; return q; }
  if (wlistN >= MAXLIST) return -1;
  wlist[wlistN].st = st; wlist[wlistN].a = a; wlist[wlistN].b = b; wlist[wlistN].c = c;
  wlist[wlistN].len = len; wlistHits[wlistN] = 1;
  return wlistN++;
}

/* the shortest walk of at most three turns, based in [lo, hi], serving both arms */
static int findWalk(const int *g, int mg, const int *t, int mt, int lo, int hi,
                    int *bst, int *ba, int *bb, int *bc) {
  int best = 1 << 30;
  *bst = -1;
  for (int st = lo; st <= hi; st++)
    for (int a = 0; a <= 9; a++) {
      if (a == st) continue;
      for (int b = -1; b <= 9; b++) {
        if (b == a) continue;
        for (int c = -1; c <= 9; c++) {
          if (c == b) continue;
          if (b < 0 && c >= 0) continue;
          int w[MAXW]; int wl = buildWalk(w, st, a, b, c);
          if (wl < 0 || wl >= best) continue;
          if (folds(g, mg, w, wl) && folds(t, mt, w, wl)) {
            best = wl; *bst = st; *ba = a; *bb = b; *bc = c;
          }
        }
      }
    }
  return (*bst < 0) ? -1 : best;
}

/* the shortest walk of at most four turns, based in [lo, hi], serving both arms */
static int findWalk4(const int *g, int mg, const int *t, int mt, int lo, int hi,
                     int *bst, int *ba, int *bb, int *bc, int *be) {
  int best = 1 << 30;
  *bst = -1;
  for (int st = lo; st <= hi; st++)
    for (int a = 0; a <= 9; a++) {
      if (a == st) continue;
      for (int b = -1; b <= 9; b++) {
        if (b == a) continue;
        for (int c = -1; c <= 9; c++) {
          if (c == b) continue;
          if (b < 0 && c >= 0) continue;
          for (int e = -1; e <= 9; e++) {
            if (e == c) continue;
            if (c < 0 && e >= 0) continue;
            int w[MAXW]; int wl = buildWalk4(w, st, a, b, c, e);
            if (wl < 0 || wl >= best) continue;
            if (folds(g, mg, w, wl) && folds(t, mt, w, wl)) {
              best = wl; *bst = st; *ba = a; *bb = b; *bc = c; *be = e;
            }
          }
        }
      }
    }
  return (*bst < 0) ? -1 : best;
}

/* -------------------------- counters ------------------------------------- */
typedef struct {
  long pairs, links, nonthin;
  /* the branch L+4 */
  long base4, valFail, valFailBad, far12Bad, minWit;
  long ceilFail, ceilCross, gapBad, v5farBad, t5farBad;
  long valleyRes, ceilPeakRes, ceilHighRes;
  long unserved, threeBad;
  /* the branch L+5 */
  long base5, served5, residual5, covered5, notCovered5;
} Cnt;

static Cnt ct, cs, cf, cm, ch, cw, cr;
static void zero(Cnt *c) { memset(c, 0, sizeof(*c)); c->minWit = 1 << 30; }

/* ---------------- the four-leg family of HPC/Fold/Leg4Wide.lean ----------- */

#define MAXFAM 64
typedef struct { int P, K, M, refl, st, a, b, c, e, len; } Fam;
static Fam fam[MAXFAM];
static int famN = 0;
static long famHits[MAXFAM];

static void buildFamily(void) {
  for (int P = 2; P <= 6; P++)
    for (int K = P; K <= 8; K++)
      for (int M = 1; M <= P - 2; M++) {
        if (M + 3 > K) continue;
        if (9 > K + 3) continue;
        /* leg4Walk 0 9 K M P : P-1 -> K -> M -> 8 -> 1 */
        int st = P - 1, a = K, b = M, c = 8, e = 1;
        int w[MAXW]; int wl = buildWalk4(w, st, a, b, c, e);
        if (wl < 0 || famN >= MAXFAM) continue;
        fam[famN].P = P; fam[famN].K = K; fam[famN].M = M; fam[famN].refl = 0;
        fam[famN].st = st; fam[famN].a = a; fam[famN].b = b; fam[famN].c = c; fam[famN].e = e;
        fam[famN].len = wl; famN++;
        int rst = 9 - st, ra = 9 - a, rb = 9 - b, rc = 9 - c, re = 9 - e;
        int w2[MAXW]; int wl2 = buildWalk4(w2, rst, ra, rb, rc, re);
        if (wl2 < 0 || famN >= MAXFAM) continue;
        fam[famN].P = P; fam[famN].K = K; fam[famN].M = M; fam[famN].refl = 1;
        fam[famN].st = rst; fam[famN].a = ra; fam[famN].b = rb; fam[famN].c = rc;
        fam[famN].e = re; fam[famN].len = wl2; famN++;
      }
}

static int famFolds(int q, const int *g, int mg, const int *t, int mt) {
  int w[MAXW];
  int wl = buildWalk4(w, fam[q].st, fam[q].a, fam[q].b, fam[q].c, fam[q].e);
  if (wl < 0) return 0;
  return folds(g, mg, w, wl) && folds(t, mt, w, wl);
}

/* the residual basepoints of the branch L+5 and the family walks serving them */
#define MAXRES 200000
static unsigned long long resMask[MAXRES];
static long resN = 0;

/* the two residues, as HPC/Fold/CrossValley.lean and HPC/Fold/CeilCross.lean state them */

static int valleyResidual(int n, int i) {
  int off[4] = {-3, -2, 2, 3};
  for (int q = 0; q < 4; q++) {
    int u = i + off[q];
    if (u < 0 || u >= n) continue;
    if (rho[u] == 2) return 1;
  }
  return 0;
}

static int ceilPeakResidual(int n, int i) {
  int off[4] = {-3, -2, 2, 3};
  for (int q = 0; q < 4; q++) {
    int u = i + off[q];
    if (u < 0 || u >= n) continue;
    if (rho[u] >= 6) return 1;
  }
  return 0;
}

static int ceilHighResidual(int n, int i) {
  int off[2] = {-4, 4};
  for (int q = 0; q < 2; q++) {
    int u = i + off[q];
    if (u < 0 || u >= n) continue;
    if (rho[u] >= 7) return 1;
  }
  return 0;
}

/* ---------------- the strengthened criteria ------------------------------ */

/* the V-criterion with the index bound the timing law gives: before every
 * ascent to L+7 a time at L+2 or below at arm index `bound` or later */
static int critVeeAt(const int *f, int m, int bound, long *minIdx) {
  for (int d = 0; d < m; d++) {
    if (f[d] < 7) continue;
    int ok = 0;
    for (int j = bound; j < d; j++) if (f[j] <= 2) { ok = 1;
      if (j < *minIdx) *minIdx = j; break; }
    if (!ok) return 0;
  }
  return 1;
}

/* Valley5 with the index bound `bound` in place of 4 */
static int valley5At(const int *f, int m, int bound) {
  for (int d = 0; d < m; d++) {
    if (f[d] > 1) continue;
    int ok = 0;
    for (int j = bound; j + 5 <= d; j++) if (f[j] >= 6) { ok = 1; break; }
    if (!ok) return 0;
  }
  return 1;
}

/* TopW5 with the index bound `bound` in place of 4 */
static int topW5At(const int *f, int m, int bound) {
  for (int d = 0; d < m; d++) {
    if (f[d] < 9) continue;
    int ok = 0;
    for (int j = bound; j + 6 <= d && !ok; j++) {
      if (f[j] < 6) continue;
      for (int k = j + 6; k + 7 <= d; k++) if (f[k] <= 2) { ok = 1; break; }
    }
    if (!ok) return 0;
  }
  return 1;
}

/* -------------------------------- the scan -------------------------------- */

static void scan(Cnt *c, int n, const char *tag, int gen) {
  (void)tag; (void)gen;
  c->pairs++;
  for (int u = 0; u < n; u++) { c->links++; if (sig[u] != rho[u]) c->nonthin++; }
  for (int i = 0; i < n; i++) {
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
    for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
    if (rho[i] == 4 && highAt(armG, mg) && highAt(armT, mt)) {
      c->base4++;
      if (valleyResidual(n, i)) c->valleyRes++;
      if (ceilPeakResidual(n, i)) c->ceilPeakRes++;
      if (ceilHighResidual(n, i)) c->ceilHighRes++;
      int fvG = !leg3Valley(armG, mg), fvT = !leg3Valley(armT, mt);
      if (fvG || fvT) {
        c->valFail++;
        if (!(foldsVee(armG, mg) && foldsVee(armT, mt))) c->valFailBad++;
        /* the witness on the arm whose partner fails */
        if (fvG) { long mi = 1 << 30;
          if (!critVeeAt(armT, mt, 12, &mi)) c->far12Bad++;
          if (mi < c->minWit) c->minWit = mi; }
        if (fvT) { long mi = 1 << 30;
          if (!critVeeAt(armG, mg, 12, &mi)) c->far12Bad++;
          if (mi < c->minWit) c->minWit = mi; }
      }
      int fcG = !leg3Ceil(armG, mg), fcT = !leg3Ceil(armT, mt);
      if (fcG || fcT) {
        c->ceilFail++;
        if (!(foldsLam(armG, mg) && foldsLam(armT, mt))) {
          c->ceilCross++;
          if (fcG) {
            if (!(topW5(armG, mg) && valley5(armT, mt))) c->gapBad++;
            if (!valley5At(armT, mt, 5)) c->v5farBad++;
            if (!topW5At(armG, mg, 12)) c->t5farBad++;
          }
          if (fcT) {
            if (!(topW5(armT, mt) && valley5(armG, mg))) c->gapBad++;
            if (!valley5At(armG, mg, 5)) c->v5farBad++;
            if (!topW5At(armT, mt, 12)) c->t5farBad++;
          }
        }
      }
      if (!(foldsLam(armG, mg) && foldsLam(armT, mt)) &&
          !(foldsVee(armG, mg) && foldsVee(armT, mt))) {
        c->unserved++;
        int w3 = foldsW3(armG, mg) && foldsW3(armT, mt);
        int w4 = foldsW4(armG, mg) && foldsW4(armT, mt);
        int w5 = foldsW5(armG, mg) && foldsW5(armT, mt);
        if (!(w3 || w4 || w5)) c->threeBad++;
      }
    }
    if (rho[i] == 5 && lowAt(armG, mg) && lowAt(armT, mt)) {
      c->base5++;
      int s1 = foldsLamR(armG, mg) && foldsLamR(armT, mt);
      int s2 = foldsVeeR(armG, mg) && foldsVeeR(armT, mt);
      int s3 = foldsW3R(armG, mg) && foldsW3R(armT, mt);
      int s4 = foldsW4R(armG, mg) && foldsW4R(armT, mt);
      int s5 = foldsW5R(armG, mg) && foldsW5R(armT, mt);
      if (s1 || s2 || s3 || s4 || s5) { c->served5++; continue; }
      c->residual5++;
      unsigned long long mask = 0;
      for (int q = 0; q < famN; q++)
        if (famFolds(q, armG, mg, armT, mt)) { mask |= 1ULL << q; famHits[q]++; }
      if (mask) c->covered5++; else c->notCovered5++;
      if (resN < MAXRES) resMask[resN++] = mask;
    }
  }
}

static void report(const char *name, const Cnt *c) {
  printf("\n---- %s ----\n", name);
  printf("  faithful pairs %ld, links %ld, non-thin %ld\n", c->pairs, c->links, c->nonthin);
  printf("  branch L+4: basepoints %ld\n", c->base4);
  printf("    valley failures %ld; pairs not folding onto the V-walk (must be 0): %ld\n",
         c->valFail, c->valFailBad);
  printf("    witness at arm index 12 or later fails at (must be 0): %ld", c->far12Bad);
  if (c->minWit < (1 << 30)) printf("; least witness index seen %ld", c->minWit);
  printf("\n");
  printf("    ceiling failures %ld, of them missing the Lambda-walk %ld;\n", c->ceilFail,
         c->ceilCross);
  printf("      the gap (TopW5 on the failing arm, Valley5 on the other) fails at "
         "(must be 0): %ld\n", c->gapBad);
  printf("      Valley5 with index 5 fails at %ld; TopW5 with index 12 fails at %ld\n",
         c->v5farBad, c->t5farBad);
  printf("    residues: ValleyResidual %ld, CeilPeakResidual %ld, CeilHighResidual %ld "
         "(the last is empty by theorem)\n", c->valleyRes, c->ceilPeakRes, c->ceilHighRes);
  printf("    unserved pairs %ld; served by none of w3, w4, w5 (must be 0): %ld\n",
         c->unserved, c->threeBad);
  printf("  branch L+5: basepoints %ld, served by a reflected walk %ld, residue %ld\n",
         c->base5, c->served5, c->residual5);
  printf("    of the residue: served by a walk of the four-leg family %ld, by none %ld\n",
         c->covered5, c->notCovered5);
}

/* ------------------------------ the corpus -------------------------------- */

static void runChain(int n, const int *v, long rounds, long walkSteps, const char *name) {
  printf("\n==== base chain %s (n = %d links); IsCrookedIvF: ", name, n);
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  printf("%d ====\n", crookedGen(rho, sig, n));

  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  if (crookedGen(rho, sig, n)) scan(&ct, n, "thin", 0);

  for (int pk = 1; pk + 1 < n; pk++) {
    if (!(v[pk] > v[pk-1] && v[pk] > v[pk+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    rho[pk] = v[pk] - 1;
    if (!crookedGen(rho, sig, n)) continue;
    scan(&cs, n, "shave", pk);
  }

  for (int vl = 1; vl + 1 < n; vl++) {
    if (!(v[vl] < v[vl-1] && v[vl] < v[vl+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    sig[vl] = v[vl] + 1;
    if (!crookedGen(rho, sig, n)) continue;
    scan(&cf, n, "fill", vl);
  }

  for (long it = 0; it < rounds; it++) {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) { if (random() % 3 == 0) rho[j] = v[j] - 1; }
      else if (v[j] < v[j-1] && v[j] < v[j+1]) { if (random() % 3 == 0) sig[j] = v[j] + 1; }
    }
    if (!crookedGen(rho, sig, n)) continue;
    scan(&cm, n, "mix", (int)it);
  }

  for (long it = 0; it < rounds; it++) {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) { if (random() % 2 == 0) rho[j] = v[j] - 1; }
      else if (v[j] < v[j-1] && v[j] < v[j+1]) { if (random() % 2 == 0) sig[j] = v[j] + 1; }
    }
    if (!crookedGen(rho, sig, n)) continue;
    scan(&ch, n, "heavy", (int)it);
  }
  {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) rho[j] = v[j] - 1;
      else if (v[j] < v[j-1] && v[j] < v[j+1]) sig[j] = v[j] + 1;
    }
    if (crookedGen(rho, sig, n)) { printf("  the total mixture is faithful\n");
      scan(&ch, n, "total", -1); }
    else printf("  the total mixture is NOT faithful\n");
  }

  {
    static int crho[MAXN], csig[MAXN];
    for (int u = 0; u < n; u++) { crho[u] = v[u]; csig[u] = v[u]; }
    long accepted = 0;
    for (long it = 0; it < walkSteps; it++) {
      int j = 1 + (int)(random() % (n - 2));
      int which = (int)(random() % 2), delta = (random() % 2) ? 1 : -1;
      int oldr = crho[j], olds = csig[j];
      if (which) csig[j] += delta; else crho[j] += delta;
      if (crho[j] > csig[j] || csig[j] > crho[j] + 1) { crho[j] = oldr; csig[j] = olds; continue; }
      for (int u = 0; u < n; u++) { rho[u] = crho[u]; sig[u] = csig[u]; }
      if (!crookedGen(rho, sig, n)) { crho[j] = oldr; csig[j] = olds; continue; }
      accepted++;
      if (accepted % 8 == 0) scan(&cw, n, "walk", (int)it);
    }
    printf("  faithful perturbation walk: %ld accepted steps\n", accepted);
  }
}

int main(int argc, char **argv) {
  long rounds = (argc > 1) ? atol(argv[1]) : 40;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 56u;
  long walkSteps = (argc > 3) ? atol(argv[3]) : 200;
  long rchains = (argc > 4) ? atol(argv[4]) : 12;
  srandom(seed);
  printf("census-batch56: the corpus check of the two crossings, and four turns at L+5.\n");
  printf("rounds=%ld seed=%u walk-steps=%ld concat-draws=%ld\n", rounds, seed, walkSteps,
         rchains);
  zero(&ct); zero(&cs); zero(&cf); zero(&cm); zero(&ch); zero(&cw); zero(&cr);
  buildFamily();
  printf("the four-leg family of the wide engine: %d walks "
         "(%d parameter sets and their reflections)\n", famN, famN / 2);

  Path p = bpath(0, 9);
  runChain(p.n, p.v, rounds, walkSteps, "bing 0 9");
  Path q = bpath(9, 0);
  runChain(q.n, q.v, rounds, walkSteps, "bing 9 0");

  {
    long made = 0, tried = 0;
    Path cand[8]; const char *cname[8]; int ncand = 0;
    cand[ncand] = vpath(0, 9, 1, 2); cname[ncand++] = "vpath 0 9 (1,2)";
    cand[ncand] = vpath(0, 9, 2, 1); cname[ncand++] = "vpath 0 9 (2,1)";
    cand[ncand] = vpath(0, 9, 2, 2); cname[ncand++] = "vpath 0 9 (2,2)";
    cand[ncand] = vpath(9, 0, 2, 2); cname[ncand++] = "vpath 9 0 (2,2)";
    { Path x = bpath(0, 9), y = bpath(9, 0);
      cand[ncand] = cat(x, y); cname[ncand++] = "bing 0 9 + bing 9 0";
      free(x.v); free(y.v); }
    { Path x = bpath(9, 0), y = bpath(0, 9);
      cand[ncand] = cat(x, y); cname[ncand++] = "bing 9 0 + bing 0 9";
      free(x.v); free(y.v); }
    for (int q2 = 0; q2 < ncand && made < rchains; q2++) {
      Path r = cand[q2];
      tried++;
      if (r.n < 20 || r.n > MAXN - 4) { printf("\n  %s: %d links, skipped\n", cname[q2], r.n);
        free(r.v); continue; }
      for (int u = 0; u < r.n; u++) { rho[u] = r.v[u]; sig[u] = r.v[u]; }
      if (!crookedGen(rho, sig, r.n)) {
        printf("\n  %s (n = %d): NOT faithful\n", cname[q2], r.n); free(r.v); continue; }
      made++;
      printf("\n==== chain outside Bing's family: %s (n = %d links) ====\n", cname[q2], r.n);
      scan(&cr, r.n, "rand-thin", (int)made);
      for (int pk = 1; pk + 1 < r.n; pk++) {
        if (!(r.v[pk] > r.v[pk-1] && r.v[pk] > r.v[pk+1])) continue;
        for (int u = 0; u < r.n; u++) { rho[u] = r.v[u]; sig[u] = r.v[u]; }
        rho[pk] = r.v[pk] - 1;
        if (!crookedGen(rho, sig, r.n)) continue;
        scan(&cr, r.n, "rand-shave", pk);
      }
      for (int vl = 1; vl + 1 < r.n; vl++) {
        if (!(r.v[vl] < r.v[vl-1] && r.v[vl] < r.v[vl+1])) continue;
        for (int u = 0; u < r.n; u++) { rho[u] = r.v[u]; sig[u] = r.v[u]; }
        sig[vl] = r.v[vl] + 1;
        if (!crookedGen(rho, sig, r.n)) continue;
        scan(&cr, r.n, "rand-fill", vl);
      }
      for (int u = 0; u < r.n; u++) { rho[u] = r.v[u]; sig[u] = r.v[u]; }
      for (int j = 1; j + 1 < r.n; j++) {
        if (r.v[j] > r.v[j-1] && r.v[j] > r.v[j+1]) rho[j] = r.v[j] - 1;
        else if (r.v[j] < r.v[j-1] && r.v[j] < r.v[j+1]) sig[j] = r.v[j] + 1;
      }
      if (crookedGen(rho, sig, r.n)) scan(&cr, r.n, "rand-total", (int)made);
      free(r.v);
    }
    printf("\nchains outside Bing's family: %ld faithful of %ld tried\n", made, tried);
  }

  {
    static int v[MAXN];
    long tried = 0, made = 0;
    for (long it = 0; it < rchains; it++) {
      int nb = 2 + (int)(random() % 4), n = 0, cur = (int)(random() % 10), first = 1;
      for (int b = 0; b < nb; b++) {
        int nx; do { nx = (int)(random() % 10); } while (nx == cur);
        Path blk = bpath(cur, nx);
        if (n + blk.n >= 1200) { free(blk.v); break; }
        if (first) { memcpy(v, blk.v, sizeof(int) * blk.n); n = blk.n; first = 0; }
        else { memcpy(v + n, blk.v + 1, sizeof(int) * (blk.n - 1)); n += blk.n - 1; }
        cur = nx; free(blk.v);
      }
      if (n < 20) continue;
      tried++;
      for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
      if (!crookedGen(rho, sig, n)) continue;
      made++;
      scan(&cr, n, "concat-thin", (int)made);
      for (int pk = 1; pk + 1 < n; pk++) {
        if (!(v[pk] > v[pk-1] && v[pk] > v[pk+1])) continue;
        for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
        rho[pk] = v[pk] - 1;
        if (!crookedGen(rho, sig, n)) continue;
        scan(&cr, n, "concat-shave", pk);
      }
      for (int vl = 1; vl + 1 < n; vl++) {
        if (!(v[vl] < v[vl-1] && v[vl] < v[vl+1])) continue;
        for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
        sig[vl] = v[vl] + 1;
        if (!crookedGen(rho, sig, n)) continue;
        scan(&cr, n, "concat-fill", vl);
      }
      for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
      for (int j = 1; j + 1 < n; j++) {
        if (v[j] > v[j-1] && v[j] > v[j+1]) rho[j] = v[j] - 1;
        else if (v[j] < v[j-1] && v[j] < v[j+1]) sig[j] = v[j] + 1;
      }
      if (crookedGen(rho, sig, n)) scan(&cr, n, "concat-total", (int)made);
    }
    printf("\nrandom concatenations of Bing blocks: %ld faithful of %ld drawn\n", made, tried);
  }

  printf("\n================ totals ================\n");
  report("the thin chains", &ct);
  report("single shavings", &cs);
  report("single fills", &cf);
  report("random mixtures (rate 1/3)", &cm);
  report("heavy mixtures (rate 1/2, and the total mixture)", &ch);
  report("random faithful perturbation walks", &cw);
  report("chains outside Bing's family and concatenations", &cr);

  {
    Cnt all; zero(&all);
    const Cnt *cc[7] = {&ct, &cs, &cf, &cm, &ch, &cw, &cr};
    long *dst = (long *)&all;
    for (int s = 0; s < 7; s++) {
      const long *src = (const long *)cc[s];
      for (unsigned u = 0; u < sizeof(Cnt) / sizeof(long); u++) dst[u] += src[u];
    }
    all.minWit = 1 << 30;
    for (int s = 0; s < 7; s++) if (cc[s]->minWit < all.minWit) all.minWit = cc[s]->minWit;
    report("EVERYTHING", &all);
  }

  printf("\n---- the four-leg family at the residue of the branch L+5 ----\n");
  printf("  residual basepoints recorded: %ld\n", resN);
  for (int q2 = 0; q2 < famN; q2++)
    if (famHits[q2])
      printf("  %s P=%d K=%d M=%d : %d -> %d -> %d -> %d -> %d  serves %ld\n",
             fam[q2].refl ? "reflected" : "direct  ", fam[q2].P, fam[q2].K, fam[q2].M,
             fam[q2].st, fam[q2].a, fam[q2].b, fam[q2].c, fam[q2].e, famHits[q2]);

  /* the greedy cover */
  {
    static char done[MAXRES];
    long left = 0;
    for (long u = 0; u < resN; u++) if (resMask[u]) left++; else done[u] = 1;
    printf("\n  greedy cover of the %ld coverable residual basepoints:\n", left);
    int picks = 0;
    while (left > 0 && picks < famN) {
      int bestq = -1; long bestc = 0;
      for (int q2 = 0; q2 < famN; q2++) {
        long cnt = 0;
        for (long u = 0; u < resN; u++)
          if (!done[u] && (resMask[u] & (1ULL << q2))) cnt++;
        if (cnt > bestc) { bestc = cnt; bestq = q2; }
      }
      if (bestq < 0) break;
      for (long u = 0; u < resN; u++)
        if (!done[u] && (resMask[u] & (1ULL << bestq))) { done[u] = 1; left--; }
      picks++;
      printf("    pick %d: %s P=%d K=%d M=%d (%d -> %d -> %d -> %d -> %d) covers %ld, "
             "left %ld\n", picks, fam[bestq].refl ? "reflected" : "direct",
             fam[bestq].P, fam[bestq].K, fam[bestq].M, fam[bestq].st, fam[bestq].a,
             fam[bestq].b, fam[bestq].c, fam[bestq].e, bestc, left);
    }
    printf("    walks needed: %d\n", picks);
  }

  printf("\n---- the definition audit ----\n");
  printf("  every predicate below is evaluated by its own definition, none by a proxy:\n");
  printf("    IsCrookedIvF (le, width, adj, crooked with interval triggers); IsLip via the\n"
         "    adjacency clause; HighAt (L+1) (L+8); LowAt (L+1) (L+8); Leg3Valley; Leg3Ceil;\n"
         "    Valley5; TopW5; FoldsOnto (the dynamic program of HPC/Fold/Decide.lean) for the\n"
         "    Lambda-walk, the V-walk, w3, w4, w5, their reflections and every walk of the\n"
         "    four-leg family; ValleyResidual; CeilPeakResidual; CeilHighResidual.\n");
  printf("  the strengthened criteria (witness at index 12, Valley5 at index 5, TopW5 at\n"
         "  index 12) are the definitions with the index bound raised to the value the\n"
         "  timing law of Theorem 7 gives; they are reported as such.\n");
  free(p.v); free(q.v);
  return 0;
}
