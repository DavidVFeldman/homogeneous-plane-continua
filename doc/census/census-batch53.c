/* census-batch53.c -- batch 53.  The ceiling crossing, the list of walks at the
 * branch L+5, and the valley residue.
 *
 * Carried over from census-batch52.c: the generators, the faithfulness test
 * (IsCrookedIvF), the dynamic program over FoldsOnto (HPC/Fold/Decide.lean),
 * the predicates of the walks and the exactness audit.
 *
 * New in this batch.
 *
 *   A. The target `cross_ceil_sentence` (commission 1, question 2), over a
 *      wider corpus: at every branch basepoint (rho i = L+4, both arms
 *      HighAt (L+1) (L+8)) at which some arm fails Leg3Ceil and the pair does
 *      not fold onto the Lambda-walk, does the pair satisfy the sentence of w4
 *      on both arms or the sentence of w5 on both arms?
 *
 *   B. The valley residue (commission 2, question 3).  Three predicates are
 *      separated, in increasing strength of the exclusion they would give:
 *        - ValleyResidual, exactly as HPC/Fold/CrossValley.lean states it:
 *          rho stands at L+2 two or three steps to one side of the basepoint;
 *        - the *narrow* residue: such a time u at which no level at or below
 *          L+1 is met by the interval [rho, sig] at u-1, u or u+1, so that the
 *          faithfulness clause anchored within one of u cannot return a time at
 *          L+2 or below (this is the configuration the sharpened dichotomy of
 *          HPC/Fold/CrossValleyNear.lean leaves);
 *        - the narrow residue *together with* an arm failing Leg3Valley, which
 *          is the only configuration in which the dichotomy is called on.
 *      Each is counted, and the conclusion of the work item is checked there.
 *
 *   C. The list of walks at the branch L+5 (commission question 1).  For every
 *      unserved pair of the branch that none of the three reflected walks
 *      serves, the shortest walk of at most three turns based within one of
 *      L+5 that serves it is computed, and a histogram of those walks is
 *      printed; then every missed pair is tested against the whole list, so
 *      the census states a covering list rather than a single miss count.
 *      Alongside: the sigma-route.  The reflection of the general model sends
 *      (rho, sig) to (9 - sig, 9 - rho), so the branch L+5 of rho is the branch
 *      L+4 of tau = 9 - sig; the census asks whether the three walks of L+4,
 *      read on the arms of tau, serve every pair of the branch.
 *
 *   D. A generator outside Bing's family: a randomised recursive chain
 *      (rpath), whose splitting points are chosen at random and which is kept
 *      only when the thin pair is faithful.
 *
 * Usage: census-batch53 [rand-rounds] [seed] [walk-steps] [crook-cap]
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
  long base, unserved, w3, w4, w5, threeOK, threeBad, sentence, sentenceBad;
  long exact, exactBad;
  /* A: the ceiling crossing */
  long ceilCase, ceilLamFree, ceilLamFreeW4, ceilLamFreeW5, ceilLamFreeEither,
       ceilLamFreeNeither;
  long ceilUnserved, ceilUnservedW4, ceilUnservedW5, ceilUnservedNeither;
  /* the arm dichotomies the ceiling case would consume */
  long armChecks, v5FailLam, v5FailVee, v5FailBad, t5Fail, t5FailLam, t5FailBad,
       m4Fail, m4FailLV, m4FailBad, b4Fail, b4FailLV, b4FailBad;
  long ceilFailV5, ceilFailT5, ceilFailBoth;
  /* the two residues of the ceiling crossing (HPC/Fold/CeilCross.lean) */
  long ceilResPeak, ceilResHigh, ceilResEither, ceilLamFreeCovered;
  long gapTopFail, gapValleyFail;
  /* B: the valley residue */
  long valleyFail, valleyFailCross;
  long residual, residualNarrow, residualWithFail, residualNarrowWithFail,
       residualNarrowWithFailBad;
  /* C: the branch L+5 */
  long base5, unserved5, w3R, w4R, w5R, threeOK5, threeBad5;
  long listOK5, listBad5;
  long tau4, tauHigh, tauThree, tauThreeBad;
} Cnt;

static void zero(Cnt *c) { memset(c, 0, sizeof(*c)); }

/* ---------------- the valley residue, on the sequence -------------------- */

/* ValleyResidual rho i L, exactly as HPC/Fold/CrossValley.lean states it */
static int valleyResidual(int n, int i) {
  int off[4] = {-3, -2, 2, 3};
  for (int q = 0; q < 4; q++) {
    int u = i + off[q];
    if (u < 0 || u >= n) continue;
    if (rho[u] == 2) return 1;
  }
  return 0;
}

/* CeilPeakResidual rho i L: rho stands at L+6 or above two or three steps to
 * one side of the basepoint. */
static int ceilPeakResidual(int n, int i) {
  int off[4] = {-3, -2, 2, 3};
  for (int q = 0; q < 4; q++) {
    int u = i + off[q];
    if (u < 0 || u >= n) continue;
    if (rho[u] >= 6) return 1;
  }
  return 0;
}

/* CeilHighResidual rho i L: rho stands at L+7 or above exactly four steps to
 * one side of the basepoint. */
static int ceilHighResidual(int n, int i) {
  int off[2] = {-4, 4};
  for (int q = 0; q < 2; q++) {
    int u = i + off[q];
    if (u < 0 || u >= n) continue;
    if (rho[u] >= 7) return 1;
  }
  return 0;
}

/* the narrow residue: such a time u at which no level <= 1 is met by the
 * interval [rho, sig] at u-1, u or u+1 -- the configuration the faithfulness
 * clause anchored within one of u cannot get below L+2 from. */
static int valleyResidualNarrow(int n, int i) {
  int off[4] = {-3, -2, 2, 3};
  for (int q = 0; q < 4; q++) {
    int u = i + off[q];
    if (u < 0 || u >= n) continue;
    if (rho[u] != 2) continue;
    int low = 0;
    for (int e = -1; e <= 1; e++) {
      int v = u + e; if (v < 0 || v >= n) continue;
      if (rho[v] <= 1) low = 1;
    }
    if (!low) return 1;
  }
  return 0;
}

/* -------------------------- the scan ------------------------------------- */

static FILE *sampleFile = NULL;
static int sampleWant = 0, sampleHave = 0;

static void dumpPair(const char *what, const char *tag, int gen, int i,
                     const int *g, int mg, const int *t, int mt) {
  if (!sampleFile || sampleHave >= sampleWant) return;
  sampleHave++;
  fprintf(sampleFile, "%s [%s %d] basepoint %d  arms %d/%d\n", what, tag, gen, i, mg, mt);
  fprintf(sampleFile, "  forward :");
  for (int d = 0; d < mg && d < 80; d++) fprintf(sampleFile, " %d", g[d]);
  fprintf(sampleFile, "\n  backward:");
  for (int d = 0; d < mt && d < 80; d++) fprintf(sampleFile, " %d", t[d]);
  fprintf(sampleFile, "\n");
}

static void scan(Cnt *c, int n, const char *tag, int gen) {
  static int gG[MAXN], gT[MAXN], tauG[MAXN], tauT[MAXN];
  c->pairs++; c->links += n;
  for (int u = 0; u < n; u++) if (sig[u] != rho[u]) c->nonthin++;
  for (int i = 0; i < n; i++) {
    int mg = n - i, mt = i + 1;
    if (rho[i] == 4) {
      for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
      for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
      if (!highAt(armG, mg) || !highAt(armT, mt)) continue;
      c->base++;
      int vG = leg3Valley(armG, mg), vT = leg3Valley(armT, mt);
      int cG = leg3Ceil(armG, mg), cT = leg3Ceil(armT, mt);
      int q4G = valley4(armG, mg), q4T = valley4(armT, mt);
      int fvG = foldsVee(armG, mg), fvT = foldsVee(armT, mt);
      int flG = foldsLam(armG, mg), flT = foldsLam(armT, mt);
      int f3G = foldsW3(armG, mg), f3T = foldsW3(armT, mt);
      int f4G = foldsW4(armG, mg), f4T = foldsW4(armT, mt);
      int f5G = foldsW5(armG, mg), f5T = foldsW5(armT, mt);
      int m4G = midW4(armG, mg) && bottomW4(armG, mg);
      int m4T = midW4(armT, mt) && bottomW4(armT, mt);
      int t5G = valley5(armG, mg) && topW5(armG, mg);
      int t5T = valley5(armT, mt) && topW5(armT, mt);
      int unserved = !((flG && flT) || (fvG && fvT));

      /* the exactness audit */
      {
        const int *ar[2] = {armG, armT}; int ml[2] = {mg, mt};
        int f3[2] = {f3G, f3T}, f4[2] = {f4G, f4T}, f5[2] = {f5G, f5T};
        for (int s = 0; s < 2; s++) {
          int land = valley4(ar[s], ml[s]) && leg3Ceil(ar[s], ml[s]);
          int w4c = midW4(ar[s], ml[s]) && ceilW4(ar[s], ml[s]) && bottomW4(ar[s], ml[s]);
          int w5c = valley5(ar[s], ml[s]) && topW5(ar[s], ml[s]);
          c->exact += 3;
          if (land != f3[s] || w4c != f4[s] || w5c != f5[s]) { c->exactBad++;
            printf("  [%s %d] EXACTNESS fails at the branch L+4: basepoint %d arm %d\n",
                   tag, gen, i, s); }
        }
      }

      /* A: the ceiling crossing, exactly as cross_ceil_sentence states it */
      if (!cG || !cT) {
        c->ceilCase++;
        if (!(flG && flT)) {
          c->ceilLamFree++;
          {
            int r1 = ceilPeakResidual(n, i), r2 = ceilHighResidual(n, i);
            if (r1) c->ceilResPeak++;
            if (r2) c->ceilResHigh++;
            if (r1 || r2) c->ceilResEither++; else c->ceilLamFreeCovered++;
            /* the two clauses the reduction of HPC/Fold/CeilArm.lean still needs */
            if (!cG) {
              if (!topW5(armG, mg)) c->gapTopFail++;
              if (!valley5(armT, mt)) c->gapValleyFail++;
            }
            if (!cT) {
              if (!topW5(armT, mt)) c->gapTopFail++;
              if (!valley5(armG, mg)) c->gapValleyFail++;
            }
          }
          if (m4G && m4T) c->ceilLamFreeW4++;
          if (t5G && t5T) c->ceilLamFreeW5++;
          if ((m4G && m4T) || (t5G && t5T)) c->ceilLamFreeEither++;
          else {
            c->ceilLamFreeNeither++;
            printf("  [%s %d] cross_ceil_sentence FAILS: basepoint %d "
                   "(Leg3Ceil G=%d T=%d; lam G=%d T=%d; w4 G=%d T=%d; w5 G=%d T=%d; "
                   "vee G=%d T=%d)\n", tag, gen, i, cG, cT, flG, flT, m4G, m4T, t5G, t5T,
                   fvG, fvT);
            dumpPair("CEILING", tag, gen, i, armG, mg, armT, mt);
          }
        }
      }

      /* A': the arm dichotomies the ceiling case would consume, and the
       * unserved form of the crossing */
      {
        const int *ar[2] = {armG, armT}; int ml[2] = {mg, mt};
        int fl[2] = {flG, flT}, fv[2] = {fvG, fvT};
        for (int s = 0; s < 2; s++) {
          int m0 = ml[s];
          c->armChecks++;
          if (!valley5(ar[s], m0)) {
            c->v5FailLam++;
            if (fv[s]) c->v5FailVee++;
            else { c->v5FailBad++;
              printf("  [%s %d] an arm failing Valley5 does NOT fold onto the V-walk: "
                     "basepoint %d arm %d\n", tag, gen, i, s); }
          }
          if (!topW5(ar[s], m0)) {
            c->t5Fail++;
            if (fl[s]) c->t5FailLam++; else c->t5FailBad++;
          }
          if (!midW4(ar[s], m0)) {
            c->m4Fail++;
            if (fl[s] || fv[s]) c->m4FailLV++; else c->m4FailBad++;
          }
          if (!bottomW4(ar[s], m0)) {
            c->b4Fail++;
            if (fl[s] || fv[s]) c->b4FailLV++; else c->b4FailBad++;
          }
          if (!leg3Ceil(ar[s], m0)) {
            int nv5 = !valley5(ar[s], m0), nt5 = !topW5(ar[s], m0);
            if (nv5) c->ceilFailV5++;
            if (nt5) c->ceilFailT5++;
            if (nv5 && nt5) c->ceilFailBoth++;
          }
        }
      }
      if ((!cG || !cT) && unserved) {
        c->ceilUnserved++;
        if (m4G && m4T) c->ceilUnservedW4++;
        if (t5G && t5T) c->ceilUnservedW5++;
        if (!((m4G && m4T) || (t5G && t5T))) c->ceilUnservedNeither++;
        if (sampleHave < sampleWant && sampleFile) {
          fprintf(sampleFile,
                  "unserved ceiling case [%s %d] basepoint %d: Leg3Ceil G=%d T=%d, "
                  "Valley5 G=%d T=%d, TopW5 G=%d T=%d, MidW4 G=%d T=%d, BottomW4 G=%d T=%d, "
                  "CeilW4 G=%d T=%d, lam G=%d T=%d, vee G=%d T=%d\n",
                  tag, gen, i, cG, cT, valley5(armG, mg), valley5(armT, mt),
                  topW5(armG, mg), topW5(armT, mt), midW4(armG, mg), midW4(armT, mt),
                  bottomW4(armG, mg), bottomW4(armT, mt), ceilW4(armG, mg), ceilW4(armT, mt),
                  flG, flT, fvG, fvT);
          sampleHave++;
        }
      }

      /* B: the valley residue */
      {
        int res = valleyResidual(n, i), resN = valleyResidualNarrow(n, i);
        if (res) c->residual++;
        if (resN) c->residualNarrow++;
        if (!vG || !vT) {
          c->valleyFail++;
          if (fvG && fvT) c->valleyFailCross++;
          if (res) c->residualWithFail++;
          if (resN) {
            c->residualNarrowWithFail++;
            if (!(fvG && fvT)) { c->residualNarrowWithFailBad++;
              printf("  [%s %d] cross_valley_profile FAILS in the narrow residue: "
                     "basepoint %d\n", tag, gen, i);
              dumpPair("VALLEY", tag, gen, i, armG, mg, armT, mt); }
            else dumpPair("narrow residue with a failing arm", tag, gen, i, armG, mg, armT, mt);
          }
        }
      }

      if (!unserved) continue;
      c->unserved++;
      {
        int s3 = f3G && f3T, s4 = f4G && f4T, s5 = f5G && f5T;
        if (s3) c->w3++;
        if (s4) c->w4++;
        if (s5) c->w5++;
        int sent = (q4G && cG && q4T && cT) || (m4G && m4T) || (t5G && t5T);
        if (sent) c->sentence++;
        if (sent != (s3 || s4 || s5)) { c->sentenceBad++;
          printf("  [%s %d] three_walks_iff_sentence FAILS: basepoint %d\n", tag, gen, i); }
        if (s3 || s4 || s5) c->threeOK++;
        else { c->threeBad++;
          printf("  [%s %d] WORK ITEM unserved_three_walks FAILS: basepoint %d\n", tag, gen, i);
          dumpPair("THREE WALKS", tag, gen, i, armG, mg, armT, mt); }
      }
    } else if (rho[i] == 5) {
      for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
      for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
      if (!lowAt(armG, mg) || !lowAt(armT, mt)) continue;
      c->base5++;
      reflArm(armG, mg, gG);
      reflArm(armT, mt, gT);

      /* the sigma-route: tau = 9 - sig, whose basepoint level is 9 - sig i */
      for (int d = 0; d < mg; d++) tauG[d] = 9 - sig[i + d];
      for (int d = 0; d < mt; d++) tauT[d] = 9 - sig[i - d];
      if (tauG[0] == 4) {
        c->tau4++;
        if (highAt(tauG, mg) && highAt(tauT, mt)) {
          c->tauHigh++;
          int a3 = foldsW3(tauG, mg) && foldsW3(tauT, mt);
          int a4 = foldsW4(tauG, mg) && foldsW4(tauT, mt);
          int a5 = foldsW5(tauG, mg) && foldsW5(tauT, mt);
          int al = foldsLam(tauG, mg) && foldsLam(tauT, mt);
          int av = foldsVee(tauG, mg) && foldsVee(tauT, mt);
          if (a3 || a4 || a5 || al || av) c->tauThree++;
          else c->tauThreeBad++;
        }
      }

      {
        int flG = foldsLamR(armG, mg), flT = foldsLamR(armT, mt);
        int fvG = foldsVeeR(armG, mg), fvT = foldsVeeR(armT, mt);
        if ((flG && flT) || (fvG && fvT)) continue;
        c->unserved5++;
        int s3 = foldsW3R(armG, mg) && foldsW3R(armT, mt);
        int s4 = foldsW4R(armG, mg) && foldsW4R(armT, mt);
        int s5 = foldsW5R(armG, mg) && foldsW5R(armT, mt);
        if (s3) c->w3R++;
        if (s4) c->w4R++;
        if (s5) c->w5R++;
        if (s3 || s4 || s5) { c->threeOK5++; continue; }
        c->threeBad5++;
        /* the walk list: the shortest serving walk based within one of L+5 */
        int st, a, b, cc;
        int len = findWalk(armG, mg, armT, mt, 4, 6, &st, &a, &b, &cc);
        if (len < 0) {
          c->listBad5++;
          int st4, a4, b4, c4, e4;
          int len4 = findWalk4(armG, mg, armT, mt, 4, 6, &st4, &a4, &b4, &c4, &e4);
          if (len4 < 0)
            printf("  [%s %d] NO walk of at most FOUR turns serves a pair of the branch L+5: "
                   "basepoint %d\n", tag, gen, i);
          else
            printf("  [%s %d] no three-turn walk at the branch L+5, basepoint %d; shortest "
                   "four-turn walk (%d times): %d -> %d -> %d -> %d -> %d\n",
                   tag, gen, i, len4, st4, a4, b4, c4, e4);
          dumpPair("L+5 UNSERVED", tag, gen, i, armG, mg, armT, mt);
        } else {
          c->listOK5++;
          noteWalk(st, a, b, cc, len);
        }
      }
    }
  }
}

/* -------------------------- reporting ------------------------------------ */

static void report(const char *name, const Cnt *c) {
  printf("\n-- %s --\n", name);
  printf("faithful pairs: %ld; non-thin links %ld/%ld (%.5f)\n", c->pairs, c->nonthin, c->links,
         c->links ? (double)c->nonthin / (double)c->links : 0.0);
  printf("branch L+4: basepoints %ld, unserved %ld; served by w3 %ld, w4 %ld, w5 %ld; "
         "by one of the three %ld; BY NONE %ld\n", c->base, c->unserved, c->w3, c->w4, c->w5,
         c->threeOK, c->threeBad);
  printf("  sentence holds at %ld unserved pairs; equivalence failures %ld; "
         "exactness checks %ld / failures %ld\n", c->sentence, c->sentenceBad, c->exact,
         c->exactBad);
  printf("TARGET 1 (cross_ceil_sentence): basepoints with an arm failing Leg3Ceil %ld; "
         "of those, pairs missing the Lambda-walk %ld\n", c->ceilCase, c->ceilLamFree);
  printf("  there: w4 sentence on both arms %ld, w5 sentence on both arms %ld, one of the two "
         "%ld, NEITHER %ld\n", c->ceilLamFreeW4, c->ceilLamFreeW5, c->ceilLamFreeEither,
         c->ceilLamFreeNeither);
  printf("  with the pair unserved by both canonical walks: %ld; w4 sentence %ld, w5 sentence "
         "%ld, NEITHER %ld\n", c->ceilUnserved, c->ceilUnservedW4, c->ceilUnservedW5,
         c->ceilUnservedNeither);
  printf("  arm dichotomies over %ld arms of the branch: arms failing Valley5 %ld (fold onto the "
         "V-walk %ld, FAILURES %ld); failing TopW5 %ld (fold onto the Lambda-walk %ld, others "
         "%ld); failing MidW4 %ld (fold onto a canonical walk %ld, others %ld); failing BottomW4 "
         "%ld (fold onto a canonical walk %ld, others %ld)\n", c->armChecks, c->v5FailLam,
         c->v5FailVee, c->v5FailBad, c->t5Fail, c->t5FailLam, c->t5FailBad, c->m4Fail,
         c->m4FailLV, c->m4FailBad, c->b4Fail, c->b4FailLV, c->b4FailBad);
  printf("  arms failing Leg3Ceil that also fail Valley5: %ld, TopW5: %ld, both: %ld\n",
         c->ceilFailV5, c->ceilFailT5, c->ceilFailBoth);
  printf("  of the Lambda-free ceiling configurations: CeilPeakResidual %ld, CeilHighResidual "
         "%ld, one of the two %ld, NEITHER (so covered by cross_ceil_sentence_of_not_residual) "
         "%ld\n", c->ceilResPeak, c->ceilResHigh, c->ceilResEither, c->ceilLamFreeCovered);
  printf("  the two clauses the reduction still needs, over those configurations: TopW5 fails on "
         "the failing arm %ld times, Valley5 fails on the other arm %ld times\n",
         c->gapTopFail, c->gapValleyFail);
  printf("TARGET 2 (cross_valley_profile): basepoints with an arm failing Leg3Valley %ld, "
         "of which both arms fold onto the V-walk %ld\n", c->valleyFail, c->valleyFailCross);
  printf("  ValleyResidual at a branch basepoint: %ld (narrow: %ld); with a failing arm: %ld "
         "(narrow: %ld); conclusion FAILS there: %ld\n", c->residual, c->residualNarrow,
         c->residualWithFail, c->residualNarrowWithFail, c->residualNarrowWithFailBad);
  printf("QUESTION 1 (the branch L+5): basepoints %ld, unserved %ld; served by the reflection "
         "of w3 %ld, of w4 %ld, of w5 %ld; by one of the three %ld; BY NONE %ld\n",
         c->base5, c->unserved5, c->w3R, c->w4R, c->w5R, c->threeOK5, c->threeBad5);
  printf("  of those, served by some walk of at most three turns based within one of L+5: %ld; "
         "by none: %ld\n", c->listOK5, c->listBad5);
  printf("  the sigma-route: basepoints where tau = 9 - sig stands at L+4: %ld, of which both "
         "tau-arms are HighAt: %ld; there one of the five walks serves the tau-pair %ld times, "
         "NONE %ld\n", c->tau4, c->tauHigh, c->tauThree, c->tauThreeBad);
}

static Cnt ct, cs, cf, cm, ch, cw, cr;

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
      for (int u = 0; u < n; u++) { rho[u] = crho[u]; sig[u] = csig[u]; }
      if (which == 0) rho[j] += delta; else sig[j] += delta;
      if (rho[j] > sig[j] || sig[j] > rho[j] + 1) continue;
      if (rho[j] < 0 || sig[j] > 9) continue;
      if (!crookedGen(rho, sig, n)) continue;
      accepted++;
      for (int u = 0; u < n; u++) { crho[u] = rho[u]; csig[u] = sig[u]; }
      scan(&cw, n, "walk", (int)accepted);
    }
    printf("  random perturbation walk: %ld steps tried, %ld accepted\n", walkSteps, accepted);
  }
}

int main(int argc, char **argv) {
  long rounds = (argc > 1) ? atol(argv[1]) : 40;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 53u;
  long walkSteps = (argc > 3) ? atol(argv[3]) : 200;
  long rchains = (argc > 4) ? atol(argv[4]) : 12;
  srandom(seed);
  sampleFile = fopen("census-batch53-sample.txt", "w");
  sampleWant = 40;
  printf("census-batch53: the ceiling crossing, the valley residue, the list of walks at L+5.\n");
  printf("rounds=%ld seed=%u walk-steps=%ld random-chains=%ld\n", rounds, seed, walkSteps,
         rchains);
  zero(&ct); zero(&cs); zero(&cf); zero(&cm); zero(&ch); zero(&cw); zero(&cr);

  Path p = bpath(0, 9);
  runChain(p.n, p.v, rounds, walkSteps, "bing 0 9");
  Path q = bpath(9, 0);
  runChain(q.n, q.v, rounds, walkSteps, "bing 9 0");

  /* the chains outside Bing's family */
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
      /* its single shavings and fills, and one heavy mixture */
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
    printf("\nrandom chains: %ld faithful of %ld tried\n", made, tried);
  }

  printf("\n================ totals ================\n");
  report("the thin chains", &ct);
  report("single shavings", &cs);
  report("single fills", &cf);
  report("random mixtures (rate 1/3)", &cm);
  report("heavy mixtures (rate 1/2, and the total mixture)", &ch);
  report("random faithful perturbation walks", &cw);
  report("chains outside Bing's family", &cr);

  {
    Cnt all; zero(&all);
    const Cnt *cc[7] = {&ct, &cs, &cf, &cm, &ch, &cw, &cr};
    long *dst = (long *)&all;
    for (int s = 0; s < 7; s++) {
      const long *src = (const long *)cc[s];
      for (unsigned u = 0; u < sizeof(Cnt) / sizeof(long); u++) dst[u] += src[u];
    }
    report("EVERYTHING", &all);
  }

  printf("\n---- the walks that serve the pairs of the branch L+5 the three reflected walks "
         "miss ----\n");
  for (int q2 = 0; q2 < wlistN; q2++)
    printf("  %d -> %d -> %d -> %d  (%d times): shortest serving walk at %ld pairs\n",
           wlist[q2].st, wlist[q2].a, wlist[q2].b, wlist[q2].c, wlist[q2].len, wlistHits[q2]);
  if (wlistN >= MAXLIST) printf("  (the list is full: more walks occur)\n");

  if (sampleFile) fclose(sampleFile);
  free(p.v); free(q.v);
  return 0;
}
