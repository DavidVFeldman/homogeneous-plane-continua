/* census-batch55.c -- batch 55.  The witness inside the residue, and the
 * sigma-route with the walk allowed to change.
 *
 * Carried over from census-batch54.c unchanged: the generators, the
 * faithfulness test (IsCrookedIvF), the dynamic program over FoldsOnto
 * (HPC/Fold/Decide.lean), the predicates of the walks, the residues of both
 * crossings, the exactness audit and the walk histograms inside each residue.
 *
 * New in this batch.
 *
 *   A. Question 1, the witness inside the residue.  At every pair of the valley
 *      residue with exactly one failing arm the census locates, on the arm that
 *      does not fail, the witness the V-criterion uses: the first time at L+2 or
 *      below at arm index four or later before that arm's ascent to L+7.  It
 *      records the index, the level, the distance to the ascent, and whether the
 *      witness lies further out than the residual time.  It then asks whether a
 *      single application of the crookedness clause of IsCrookedIvF forces such
 *      a time -- the anchors, the levels, and the whole range the returned time
 *      can occupy inside the window the criterion asks for -- and records every
 *      such anchoring as a scheme, in arm coordinates, measured both from the
 *      basepoint and from the ascent.  A scheme that occurs at every residual
 *      pair is the step the proof has not made.  The same is done at the
 *      ceiling peak residue for TopW5, whose witness is a pair: a time at L+6 or
 *      above at index four or later, and a later time at L+2 or below.
 *
 *   B. Question 2, the sigma-route with the walk allowed to change.  At every
 *      basepoint of the branch L+5 where tau = 9 - sig stands at L+4 with both
 *      arms HighAt, the census folds the tau-pair and the pair of 9 - rho onto
 *      each of the five walks and counts the basepoints where the tau-pair is
 *      served and the pair of 9 - rho is served by NONE of the five: those, and
 *      only those, would refute the implication asked about.
 *
 * Every predicate named in a Lean statement the census is offered as evidence
 * for is evaluated here by its own definition -- hypotheses, residues and
 * conclusions alike -- and the audit list is printed at the end.  No proxies.
 *
 * Usage: census-batch55 [rand-rounds] [seed] [walk-steps] [concat-draws]
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
  /* batch 55: the sigma-route with the walk allowed to change */
  long sigTau, sigRefl, sigBoth, sigLost, sigWalkLost;
  long sigLostLam, sigLostVee, sigLostW3, sigLostW4, sigLostW5;
  /* batch 54: the sharpened residues and the walks inside them */
  long resNarrowLean, resNarrowLeanWithFail;
  long ceilFlatG, ceilFlatT, ceilPeakAndFlat, ceilCoveredNarrow;
  long wValley[7], wValleyNarrow[7], wCeilPeak[7], wCeilHigh[7], wCeilSharp[7];
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


/* ValleyNarrowResidual rho i L, exactly as HPC/Fold/ValleyNarrow.lean states it:
 * a time at L+2 two or three steps to one side of the basepoint at which the
 * sequence stands at L+2 or above at that time and at both neighbours. */
static int valleyNarrowResidualLean(int n, int i) {
  int off[4] = {-3, -2, 2, 3};
  for (int q = 0; q < 4; q++) {
    int u = i + off[q];
    if (u < 0 || u >= n) continue;
    if (rho[u] != 2) continue;
    int ok = 1;
    for (int e = -1; e <= 1; e++) {
      int v = u + e; if (v < 0 || v >= n) continue;
      if (rho[v] < 2) ok = 0;
    }
    if (ok) return 1;
  }
  return 0;
}

/* CeilFarFlatG rho i L, exactly as HPC/Fold/CeilNarrow.lean states it: a time at
 * exactly L+2 two or more steps past the basepoint, with the sequence at L+2 or
 * above at both of its neighbours and at every time from i+2 up to it. */
static int ceilFarFlatG(int n, int i) {
  for (int w = i + 2; w < n; w++) {
    if (rho[w] <= 1) return 0;
    if (rho[w] != 2) continue;
    int ok = 1;
    for (int e = -1; e <= 1; e++) {
      int v = w + e; if (v < 0 || v >= n) continue;
      if (rho[v] < 2) ok = 0;
    }
    if (ok) return 1;
  }
  return 0;
}

/* CeilFarFlatT rho i L, the mirror */
static int ceilFarFlatT(int n, int i) {
  for (int w = i - 2; w >= 0; w--) {
    if (rho[w] <= 1) return 0;
    if (rho[w] != 2) continue;
    int ok = 1;
    for (int e = -1; e <= 1; e++) {
      int v = w + e; if (v < 0 || v >= n) continue;
      if (rho[v] < 2) ok = 0;
    }
    if (ok) return 1;
  }
  return 0;
}

/* which of the five walks of the branch L+4 serve the pair; hits[5] counts the
 * basepoints no one of them serves */
static void residueWalks(long *hits, const int *g, int mg, const int *t, int mt) {
  int served = 0;
  if (foldsLam(g, mg) && foldsLam(t, mt)) { hits[0]++; served = 1; }
  if (foldsVee(g, mg) && foldsVee(t, mt)) { hits[1]++; served = 1; }
  if (foldsW3(g, mg)  && foldsW3(t, mt))  { hits[2]++; served = 1; }
  if (foldsW4(g, mg)  && foldsW4(t, mt))  { hits[3]++; served = 1; }
  if (foldsW5(g, mg)  && foldsW5(t, mt))  { hits[4]++; served = 1; }
  if (!served) hits[5]++;
  hits[6]++;
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

/* ------------------- the witness inside the residue (question 1) ---------
 *
 * At a residual pair the V-criterion holds on the arm Y that does not fail:
 * there is a time at L+2 or below, at arm index four or later, before Y's
 * ascent to L+7.  The proof reaches only the residual time at index two or
 * three.  This module locates the witness the criterion actually uses and asks
 * whether one application of the crookedness clause of IsCrookedIvF forces it.
 *
 * An application is given by two anchors s < t (global indices) and two levels
 * h, k with |h - k| >= 3, h met by the interval [rho, sig] within one step of s
 * and k met within one step of t.  It returns r and r' with s < r < r' < t, at
 * levels k-1 and h+1 when h < k, and k+1 and h-1 when k < h.  The application
 *
 *   FORCES the witness  when the level of one of the two returned times is at
 *     most 2 and the whole range that time can occupy -- [s+1, t-2] for r,
 *     [s+2, t-1] for r' -- lies inside the window the criterion asks for;
 *   REALISES it         when the first times at those levels, read as the
 *     faithfulness test reads them, land inside the window.
 *
 * Only the forcing applications are proof steps; the realising ones say what
 * the model does.  Each forcing application is recorded as a scheme, in arm
 * coordinates (distance from the basepoint along Y, positive towards Y), in two
 * families: offsets from the basepoint, and offsets from the ascent.  A scheme
 * that appears at every residual pair is the missing step.
 */

#define MAXSCHEME 40000
#ifndef ANCHORFAR
#define ANCHORFAR 24
#endif
#ifndef ANCHORSPAN
#define ANCHORSPAN 20
#endif
typedef struct { int fam, ds, dt, h, k; long cnt; } Scheme;
static Scheme schemes[MAXSCHEME];
static int nschemes = 0;
static int schemeOverflow = 0;

/* a hash table over the schemes, keyed by (fam, ds, dt, h, k) */
#define SCHEMEHASH (1 << 18)
static int schemeSlot[SCHEMEHASH];
static int schemeHashInit = 0;

static int noteScheme(int fam, int ds, int dt, int h, int k) {
  if (!schemeHashInit) {
    for (int q = 0; q < SCHEMEHASH; q++) schemeSlot[q] = -1;
    schemeHashInit = 1;
  }
  unsigned key = ((unsigned)(ds + 128) << 24) ^ ((unsigned)(dt + 128) << 16) ^
                 ((unsigned)(h + 16) << 8) ^ (unsigned)(k + 16) ^ ((unsigned)fam << 30);
  unsigned x = key * 2654435761u;
  unsigned pos = x & (SCHEMEHASH - 1);
  while (schemeSlot[pos] >= 0) {
    int q = schemeSlot[pos];
    if (schemes[q].fam == fam && schemes[q].ds == ds && schemes[q].dt == dt &&
        schemes[q].h == h && schemes[q].k == k) return q;
    pos = (pos + 1) & (SCHEMEHASH - 1);
  }
  if (nschemes >= MAXSCHEME) { schemeOverflow = 1; return -1; }
  schemes[nschemes].fam = fam; schemes[nschemes].ds = ds; schemes[nschemes].dt = dt;
  schemes[nschemes].h = h; schemes[nschemes].k = k; schemes[nschemes].cnt = 0;
  schemeSlot[pos] = nschemes;
  return nschemes++;
}

/* the levels met by the interval [rho, sig] within one step of the index x */
static int metLevels(int n, int x, int *out) {
  int nh = 0;
  for (int e = -1; e <= 1; e++) {
    int u = x + e; if (u < 0 || u >= n) continue;
    for (int l = rho[u]; l <= sig[u]; l++) {
      int seen = 0; for (int q = 0; q < nh; q++) if (out[q] == l) seen = 1;
      if (!seen && nh < 16) out[nh++] = l;
    }
  }
  return nh;
}

/* the first index at or after j whose interval meets the level l, or n */
static int firstMeet(int n, int j, int l) {
  for (int u = j; u < n; u++) if (rho[u] <= l && l <= sig[u]) return u;
  return n;
}

/* the witness analysis at one residual pair.
 *   [wlo, whi] : the window of global indices the criterion accepts
 *   i, dir     : the basepoint and the direction of the arm Y
 *   de         : the arm index of Y's ascent
 * Returns 1 if some application forces a time at level <= 2 inside the window.
 * `realised` is set when some application realises one.  The forcing schemes
 * are recorded. */
static int clauseAtWindow(int n, int wlo, int whi, int i, int dir, int de,
                          int *realised, long *nforcing) {
  int found = 0;
  int local[256], nlocal = 0;
  *realised = 0;
  *nforcing = 0;
  if (wlo > whi) return 0;
  /* the anchors are searched near the basepoint and at a bounded span: an
   * application further out than ANCHORFAR steps, or of span more than
   * ANCHORSPAN, is not looked for.  Both bounds are recorded in the report. */
  int slo = wlo - 2, shi = whi;
  if (slo < i - ANCHORFAR) slo = i - ANCHORFAR;
  if (shi > i + ANCHORFAR) shi = i + ANCHORFAR;
  for (int s = slo; s <= shi; s++) {
    if (s < 0 || s >= n) continue;
    int hs[16]; int nh = metLevels(n, s, hs);
    int thi = s + ANCHORSPAN;
    if (thi > whi + 2) thi = whi + 2;
    for (int t = s + 2; t <= thi; t++) {
      if (t < 0 || t >= n) continue;
      int ks[16]; int nk = metLevels(n, t, ks);
      for (int a = 0; a < nh; a++) for (int b = 0; b < nk; b++) {
        int h = hs[a], k = ks[b];
        int diff = h - k; if (diff < 0) diff = -diff;
        if (diff < 3) continue;
        int l1 = (h < k) ? (k - 1) : (k + 1);      /* the level of r  */
        int l2 = (h < k) ? (h + 1) : (h - 1);      /* the level of r' */
        int forces = 0;
        if (l1 <= 2 && s + 1 >= wlo && t - 2 <= whi) forces = 1;
        if (l2 <= 2 && s + 2 >= wlo && t - 1 <= whi) forces = 1;
        if (forces) {
          found = 1; (*nforcing)++;
          int ds = (s - i) * dir, dt = (t - i) * dir;
          int q1 = noteScheme(1, ds, dt, h, k);
          int q2 = noteScheme(2, ds - de, dt - de, h, k);
          if (q1 >= 0) { int seen = 0;
            for (int z = 0; z < nlocal; z++) if (local[z] == q1) seen = 1;
            if (!seen && nlocal < 256) local[nlocal++] = q1; }
          if (q2 >= 0) { int seen = 0;
            for (int z = 0; z < nlocal; z++) if (local[z] == q2) seen = 1;
            if (!seen && nlocal < 256) local[nlocal++] = q2; }
        }
        if (!*realised) {
          int p1 = firstMeet(n, s + 1, l1);
          if (p1 < t) {
            int p2 = firstMeet(n, p1 + 1, l2);
            if (p2 < t) {
              if (l1 <= 2 && p1 >= wlo && p1 <= whi) *realised = 1;
              if (l2 <= 2 && p2 >= wlo && p2 <= whi) *realised = 1;
            }
          }
        }
      }
    }
  }
  for (int z = 0; z < nlocal; z++) schemes[local[z]].cnt++;
  return found;
}


/* ---------- the sigma-route counterexample, shrunk to a small window -------
 *
 * A basepoint where the tau-pair is served by one of the five walks and the
 * pair of 9 - rho is served by none refutes the implication asked in question
 * 2.  The window around such a basepoint is shrunk, from both ends, as far as
 * the following all keep holding on the window:
 *
 *   the window is faithful (IsCrookedIvF), rho stands at L+5 at the basepoint,
 *   both arms of rho are LowAt, tau stands at L+4 with both arms HighAt and the
 *   tau-pair folds onto one of the five walks, and the pair of 9 - rho folds
 *   onto none of them.
 *
 * The shrunk window is written out as two base-sixteen numerals, so that the
 * verdicts can be re-decided by the kernel in Lean.
 */

static FILE *sigmaFile = NULL;
static int sigmaWant = 6, sigmaHave = 0;

static int sigmaOK(const int *r, const int *g, int n2, int i2) {
  static int aG[MAXN], aT[MAXN], tG[MAXN], tT[MAXN], rG[MAXN], rT[MAXN];
  int mg = n2 - i2, mt = i2 + 1;
  if (i2 < 0 || i2 >= n2) return 0;
  if (r[i2] != 5) return 0;
  for (int d = 0; d < mg; d++) { aG[d] = r[i2 + d]; tG[d] = 9 - g[i2 + d]; rG[d] = 9 - r[i2 + d]; }
  for (int d = 0; d < mt; d++) { aT[d] = r[i2 - d]; tT[d] = 9 - g[i2 - d]; rT[d] = 9 - r[i2 - d]; }
  if (!lowAt(aG, mg) || !lowAt(aT, mt)) return 0;
  if (tG[0] != 4) return 0;
  if (!highAt(tG, mg) || !highAt(tT, mt)) return 0;
  int aTau = (foldsLam(tG, mg) && foldsLam(tT, mt)) || (foldsVee(tG, mg) && foldsVee(tT, mt)) ||
             (foldsW3(tG, mg) && foldsW3(tT, mt)) || (foldsW4(tG, mg) && foldsW4(tT, mt)) ||
             (foldsW5(tG, mg) && foldsW5(tT, mt));
  int aRef = (foldsLam(rG, mg) && foldsLam(rT, mt)) || (foldsVee(rG, mg) && foldsVee(rT, mt)) ||
             (foldsW3(rG, mg) && foldsW3(rT, mt)) || (foldsW4(rG, mg) && foldsW4(rT, mt)) ||
             (foldsW5(rG, mg) && foldsW5(rT, mt));
  if (!aTau || aRef) return 0;
  return crookedGen(r, g, n2);
}

static void sigmaCounterexample(int n, int i, const char *tag, int gen) {
  if (!sigmaFile || sigmaHave >= sigmaWant) return;
  int lo = 0, hi = n - 1;
  while (lo < i && sigmaOK(rho + lo + 1, sig + lo + 1, hi - lo, i - lo - 1)) lo++;
  while (hi > i && sigmaOK(rho + lo, sig + lo, hi - lo, i - lo)) hi--;
  int n2 = hi - lo + 1, i2 = i - lo;
  if (!sigmaOK(rho + lo, sig + lo, n2, i2)) return;
  sigmaHave++;
  fprintf(sigmaFile, "sigma-route counterexample %d [%s %d]: window [%d, %d] of %d, "
          "basepoint %d of %d links\n", sigmaHave, tag, gen, lo, hi, n, i2, n2);
  fprintf(sigmaFile, "  rho:");
  for (int u = 0; u < n2; u++) fprintf(sigmaFile, " %d", rho[lo + u]);
  fprintf(sigmaFile, "\n  sig:");
  for (int u = 0; u < n2; u++) fprintf(sigmaFile, " %d", sig[lo + u]);
  fprintf(sigmaFile, "\n  rho hex (low digit first):");
  for (int u = 0; u < n2; u++) fprintf(sigmaFile, "%x", rho[lo + u]);
  fprintf(sigmaFile, "\n  sig hex (low digit first):");
  for (int u = 0; u < n2; u++) fprintf(sigmaFile, "%x", sig[lo + u]);
  {
    static int tG[MAXN], tT[MAXN], rG[MAXN], rT[MAXN];
    int mg = n2 - i2, mt = i2 + 1;
    for (int d = 0; d < mg; d++) { tG[d] = 9 - sig[lo + i2 + d]; rG[d] = 9 - rho[lo + i2 + d]; }
    for (int d = 0; d < mt; d++) { tT[d] = 9 - sig[lo + i2 - d]; rT[d] = 9 - rho[lo + i2 - d]; }
    fprintf(sigmaFile, "\n  tau forward (%d steps):", mg);
    for (int d = 0; d < mg; d++) fprintf(sigmaFile, " %d", tG[d]);
    fprintf(sigmaFile, "\n  tau backward (%d steps):", mt);
    for (int d = 0; d < mt; d++) fprintf(sigmaFile, " %d", tT[d]);
    fprintf(sigmaFile, "\n  9-rho forward:");
    for (int d = 0; d < mg; d++) fprintf(sigmaFile, " %d", rG[d]);
    fprintf(sigmaFile, "\n  9-rho backward:");
    for (int d = 0; d < mt; d++) fprintf(sigmaFile, " %d", rT[d]);
    fprintf(sigmaFile, "\n  tau folds:  Lam %d V %d w3 %d w4 %d w5 %d\n",
            foldsLam(tG, mg) && foldsLam(tT, mt), foldsVee(tG, mg) && foldsVee(tT, mt),
            foldsW3(tG, mg) && foldsW3(tT, mt), foldsW4(tG, mg) && foldsW4(tT, mt),
            foldsW5(tG, mg) && foldsW5(tT, mt));
    fprintf(sigmaFile, "  9-rho folds: Lam %d V %d w3 %d w4 %d w5 %d\n",
            foldsLam(rG, mg) && foldsLam(rT, mt), foldsVee(rG, mg) && foldsVee(rT, mt),
            foldsW3(rG, mg) && foldsW3(rT, mt), foldsW4(rG, mg) && foldsW4(rT, mt),
            foldsW5(rG, mg) && foldsW5(rT, mt));
    fprintf(sigmaFile, "  tau hex forward:");
    for (int d = 0; d < mg; d++) fprintf(sigmaFile, "%x", tG[d]);
    fprintf(sigmaFile, "\n  tau hex backward:");
    for (int d = 0; d < mt; d++) fprintf(sigmaFile, "%x", tT[d]);
    fprintf(sigmaFile, "\n  9-rho hex forward:");
    for (int d = 0; d < mg; d++) fprintf(sigmaFile, "%x", rG[d]);
    fprintf(sigmaFile, "\n  9-rho hex backward:");
    for (int d = 0; d < mt; d++) fprintf(sigmaFile, "%x", rT[d]);
    fprintf(sigmaFile, "\n");
  }
  fflush(sigmaFile);
}

/* the witness statistics of the valley residue */
typedef struct {
  long pairs;            /* residual pairs with exactly one failing arm */
  long bothFail;         /* residual pairs where both arms fail Leg3Valley */
  long noAscent;         /* Y never reaches L+7: the criterion is vacuous */
  long hasWitness;       /* the criterion holds on Y */
  long noWitness;        /* it does not -- a counterexample to the conclusion */
  long forced, realised, neither;
  long witIdx[32];       /* the arm index of the first witness, capped at 31 */
  long witLev[12];       /* its level */
  long gap[32];          /* the distance from the witness to the ascent */
  long pastResidual;     /* the witness lies further out than the residual time */
} Wit;

static Wit wv, wc;

static void witZero(Wit *w) { memset(w, 0, sizeof(*w)); }

/* the residual time of the valley residue, as an arm offset with a sign:
 * returns the offset (-3, -2, 2 or 3) or 0 if there is none */
static int residualOffset(int n, int i) {
  int off[4] = {-3, -2, 2, 3};
  for (int q = 0; q < 4; q++) {
    int u = i + off[q];
    if (u < 0 || u >= n) continue;
    if (rho[u] == 2) return off[q];
  }
  return 0;
}

/* Y is the arm of direction dir (arm index d is the global index i + dir*d),
 * of length m. */
static void witnessValley(int n, int i, int dir, const int *armY, int m,
                          const char *tag, int gen) {
  int de = -1;
  for (int d = 0; d < m; d++) if (armY[d] >= 7) { de = d; break; }
  if (de < 0) { wv.noAscent++; return; }
  wv.pairs++;
  int first = -1;
  for (int d = 4; d < de; d++) if (armY[d] <= 2) { first = d; break; }
  if (first < 0) {
    wv.noWitness++;
    printf("  [%s %d] the V-criterion FAILS on the arm of a residual pair: "
           "basepoint %d dir %d ascent at %d\n", tag, gen, i, dir, de);
    return;
  }
  wv.hasWitness++;
  wv.witIdx[first < 31 ? first : 31]++;
  wv.witLev[armY[first] < 11 ? armY[first] : 11]++;
  wv.gap[(de - first) < 31 ? (de - first) : 31]++;
  { int ro = residualOffset(n, i);
    int rarm = ro * dir;                 /* the residual time in Y's coordinates */
    if (first > rarm) wv.pastResidual++; }
  int wlo, whi;
  if (dir > 0) { wlo = i + 4; whi = i + de - 1; }
  else { wlo = i - (de - 1); whi = i - 4; }
  int realised; long nf;
  int forced = clauseAtWindow(n, wlo, whi, i, dir, de, &realised, &nf);
  if (forced) wv.forced++;
  if (realised) wv.realised++;
  if (!forced && !realised) wv.neither++;
}

/* the ceiling residue: the criterion is TopW5 on the arm, whose witness is a
 * pair -- a time at L+6 or above at index four or later, and after it a time at
 * L+2 or below, seven steps or more before the ascent to L+9.  The low time is
 * the one the clause would have to produce. */
static void witnessCeil(int n, int i, int dir, const int *armY, int m,
                        const char *tag, int gen) {
  int de = -1;
  for (int d = 0; d < m; d++) if (armY[d] >= 9) { de = d; break; }
  if (de < 0) { wc.noAscent++; return; }
  wc.pairs++;
  int bj = -1, bk = -1;
  for (int j = 4; j + 13 <= de && bj < 0; j++) {
    if (armY[j] < 6) continue;
    for (int k = j + 6; k + 7 <= de; k++)
      if (armY[k] <= 2) { bj = j; bk = k; break; }
  }
  if (bj < 0) {
    wc.noWitness++;
    printf("  [%s %d] TopW5 FAILS on the arm of a ceiling residual pair: "
           "basepoint %d dir %d ascent at %d\n", tag, gen, i, dir, de);
    return;
  }
  wc.hasWitness++;
  wc.witIdx[bk < 31 ? bk : 31]++;
  wc.witLev[armY[bk] < 11 ? armY[bk] : 11]++;
  wc.gap[(de - bk) < 31 ? (de - bk) : 31]++;
  int wlo, whi;
  if (dir > 0) { wlo = i + bj + 6; whi = i + de - 7; }
  else { wlo = i - (de - 7); whi = i - (bj + 6); }
  int realised; long nf;
  int forced = clauseAtWindow(n, wlo, whi, i, dir, de, &realised, &nf);
  if (forced) wc.forced++;
  if (realised) wc.realised++;
  if (!forced && !realised) wc.neither++;
  if (sampleFile && sampleHave < sampleWant) {
    sampleHave++;
    fprintf(sampleFile, "ceiling residual witness [%s %d] basepoint %d dir %d: "
            "ascent %d, high witness %d (level %d), low witness %d (level %d), "
            "forced %d realised %d\n", tag, gen, i, dir, de, bj, armY[bj], bk,
            armY[bk], forced, realised);
  }
}

static void witReport(const char *what, const Wit *w) {
  printf("\n-- the witness inside %s --\n", what);
  printf("  pairs analysed %ld; both arms fail %ld; no ascent on the arm %ld\n",
         w->pairs, w->bothFail, w->noAscent);
  printf("  the criterion holds at %ld, fails at %ld\n", w->hasWitness, w->noWitness);
  printf("  one application of the clause FORCES the witness at %ld, realises one at %ld, "
         "does neither at %ld\n", w->forced, w->realised, w->neither);
  printf("  the arm index of the first witness:");
  for (int q = 0; q < 32; q++) if (w->witIdx[q]) printf(" %d:%ld", q, w->witIdx[q]);
  printf("\n  its level:");
  for (int q = 0; q < 12; q++) if (w->witLev[q]) printf(" %d:%ld", q, w->witLev[q]);
  printf("\n  its distance from the ascent:");
  for (int q = 0; q < 32; q++) if (w->gap[q]) printf(" %d:%ld", q, w->gap[q]);
  printf("\n  the witness lies further out than the residual time at %ld of %ld\n",
         w->pastResidual, w->hasWitness);
}

static void schemeReport(long pairs) {
  printf("\n-- the anchorings that force the witness --\n");
  if (schemeOverflow) printf("  (the scheme table overflowed; the counts below are partial)\n");
  printf("  %d schemes recorded over %ld pairs; the anchors were searched within %d\n"
         "  steps of the basepoint and at a span of at most %d\n",
         nschemes, pairs, ANCHORFAR, ANCHORSPAN);
  for (int fam = 1; fam <= 2; fam++) {
    long best = 0; int nbest = 0;
    for (int q = 0; q < nschemes; q++)
      if (schemes[q].fam == fam && schemes[q].cnt > best) { best = schemes[q].cnt; }
    for (int q = 0; q < nschemes; q++)
      if (schemes[q].fam == fam && schemes[q].cnt == best) nbest++;
    printf("  family %d (%s): the widest scheme covers %ld of %ld pairs (%d schemes do)\n",
           fam, fam == 1 ? "anchors measured from the basepoint"
                         : "anchors measured from the ascent", best, pairs, nbest);
    int shown = 0;
    for (int q = 0; q < nschemes && shown < 12; q++)
      if (schemes[q].fam == fam && schemes[q].cnt == best) {
        printf("    s at %+d, t at %+d, h = %d, k = %d : %ld pairs\n",
               schemes[q].ds, schemes[q].dt, schemes[q].h, schemes[q].k, schemes[q].cnt);
        shown++;
      }
  }
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
            { int fg = ceilFarFlatG(n, i), ft = ceilFarFlatT(n, i);
              if (fg) c->ceilFlatG++;
              if (ft) c->ceilFlatT++;
              if (r1 && (fg || ft)) c->ceilPeakAndFlat++;
              if (!(r1 && (fg || ft)) && !r2) c->ceilCoveredNarrow++;
              if (r1) { residueWalks(c->wCeilPeak, armG, mg, armT, mt);
                /* question 1 at the ceiling: TopW5 on the arm that does not fail */
                if (!cG && !cT) wc.bothFail++;
                else if (!cG) witnessCeil(n, i, -1, armT, mt, tag, gen);
                else witnessCeil(n, i, 1, armG, mg, tag, gen); }
              if (r2) residueWalks(c->wCeilHigh, armG, mg, armT, mt);
              if (r1 && (fg || ft)) residueWalks(c->wCeilSharp, armG, mg, armT, mt); }
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
        int resL = valleyNarrowResidualLean(n, i);
        if (resL) c->resNarrowLean++;
        if (!vG || !vT) {
          c->valleyFail++;
          if (fvG && fvT) c->valleyFailCross++;
          if (res) { c->residualWithFail++; residueWalks(c->wValley, armG, mg, armT, mt);
            /* question 1: where is the witness, and does the clause force it? */
            if (!vG && !vT) wv.bothFail++;
            else if (!vG) witnessValley(n, i, -1, armT, mt, tag, gen);
            else witnessValley(n, i, 1, armG, mg, tag, gen); }
          if (resL) { c->resNarrowLeanWithFail++;
                      residueWalks(c->wValleyNarrow, armG, mg, armT, mt); }
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
          /* question 2: does a fold of tau = 9 - sig yield a fold of 9 - rho
           * onto SOME walk of the five?  The five walks are tried on both. */
          {
            static int refG[MAXN], refT[MAXN];
            for (int d = 0; d < mg; d++) refG[d] = 9 - rho[i + d];
            for (int d = 0; d < mt; d++) refT[d] = 9 - rho[i - d];
            int b3 = foldsW3(refG, mg) && foldsW3(refT, mt);
            int b4 = foldsW4(refG, mg) && foldsW4(refT, mt);
            int b5 = foldsW5(refG, mg) && foldsW5(refT, mt);
            int bl = foldsLam(refG, mg) && foldsLam(refT, mt);
            int bv = foldsVee(refG, mg) && foldsVee(refT, mt);
            int tauOK = a3 || a4 || a5 || al || av;
            int refOK = b3 || b4 || b5 || bl || bv;
            if (tauOK) c->sigTau++;
            if (refOK) c->sigRefl++;
            if (tauOK && refOK) c->sigBoth++;
            if (tauOK && !refOK) { c->sigLost++;
              printf("  [%s %d] the sigma-route IMPLICATION FAILS: tau folds, 9 - rho "
                     "folds onto no walk of the five: basepoint %d\n", tag, gen, i);
              sigmaCounterexample(n, i, tag, gen); }
            /* the individual walk, lost or kept */
            if (al && !bl) c->sigLostLam++;
            if (av && !bv) c->sigLostVee++;
            if (a3 && !b3) c->sigLostW3++;
            if (a4 && !b4) c->sigLostW4++;
            if (a5 && !b5) c->sigLostW5++;
            if (tauOK && refOK &&
                ((al && !bl) || (av && !bv) || (a3 && !b3) || (a4 && !b4) || (a5 && !b5)))
              c->sigWalkLost++;
          }
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

/* the walks that serve the pairs of a residue */
static void reportWalks(const char *what, const long *h) {
  if (h[6] == 0) { printf("  walks inside %s: the residue is empty\n", what); return; }
  printf("  walks inside %s (%ld basepoints): Lambda %ld, V %ld, w3 %ld, w4 %ld, w5 %ld; "
         "served by NONE of the five %ld\n", what, h[6], h[0], h[1], h[2], h[3], h[4], h[5]);
}

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
  printf("BATCH 54, the sharpened residues: ValleyNarrowResidual %ld (with a failing arm %ld); "
         "CeilFarFlatG %ld, CeilFarFlatT %ld over the Lambda-free ceiling configurations; "
         "CeilPeakResidual together with one of the two %ld; covered by "
         "cross_ceil_sentence_of_not_narrow_residual %ld\n",
         c->resNarrowLean, c->resNarrowLeanWithFail, c->ceilFlatG, c->ceilFlatT,
         c->ceilPeakAndFlat, c->ceilCoveredNarrow);
  reportWalks("the valley residue with a failing arm", c->wValley);
  reportWalks("the narrow valley residue with a failing arm", c->wValleyNarrow);
  reportWalks("the ceiling peak residue", c->wCeilPeak);
  reportWalks("the ceiling high residue", c->wCeilHigh);
  reportWalks("the sharpened ceiling residue (peak and a flat narrow bottom)", c->wCeilSharp);
  printf("  the sigma-route: basepoints where tau = 9 - sig stands at L+4: %ld, of which both "
         "tau-arms are HighAt: %ld; there one of the five walks serves the tau-pair %ld times, "
         "NONE %ld\n", c->tau4, c->tauHigh, c->tauThree, c->tauThreeBad);
  printf("  QUESTION 2 (the sigma-route with the walk allowed to change): the tau-pair is "
         "served by one of the five at %ld basepoints, the pair of 9 - rho at %ld, both at "
         "%ld; tau served and 9 - rho served by NONE: %ld\n",
         c->sigTau, c->sigRefl, c->sigBoth, c->sigLost);
  printf("    the individual walk is lost (serves tau, not 9 - rho) at: Lambda %ld, V %ld, "
         "w3 %ld, w4 %ld, w5 %ld; basepoints where some walk is lost but another serves: "
         "%ld\n", c->sigLostLam, c->sigLostVee, c->sigLostW3, c->sigLostW4, c->sigLostW5,
         c->sigWalkLost);
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
  sampleFile = fopen("census-batch55-sample.txt", "w");
  sigmaFile = fopen("census-batch55-sigma.txt", "w");
  sampleWant = 40;
  printf("census-batch55: the witness inside the residue, and the sigma-route with the "
         "walk allowed to change.\n");
  printf("rounds=%ld seed=%u walk-steps=%ld concat-draws=%ld\n", rounds, seed, walkSteps,
         rchains);
  zero(&ct); zero(&cs); zero(&cf); zero(&cm); zero(&ch); zero(&cw); zero(&cr);
  witZero(&wv); witZero(&wc);

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

  /* the new generator: random concatenations of Bing blocks */
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

  witReport("the valley residue (ValleyResidual with a failing arm)", &wv);
  witReport("the ceiling peak residue (CeilPeakResidual, Lambda-free)", &wc);
  schemeReport(wv.hasWitness + wc.hasWitness);

  printf("\n---- the definition audit ----\n");
  printf("  every predicate below is evaluated by its own definition, none by a proxy:\n");
  printf("    IsCrookedIvF (le, width, adj, crooked with interval triggers); IsLip via the\n"
         "    adjacency clause; HighAt (L+1) (L+8); LowAt (L+1) (L+8); Leg3Valley; Leg3Ceil;\n"
         "    Valley4; Valley5; TopW5; MidW4; CeilW4; BottomW4; FoldsOnto (the dynamic program of\n"
         "    HPC/Fold/Decide.lean) for the Lambda-walk, the V-walk, w3, w4, w5 and their\n"
         "    reflections; ValleyResidual; ValleyNarrowResidual; CeilPeakResidual;\n"
         "    CeilHighResidual; CeilFarFlatG; CeilFarFlatT.\n");
  printf("  the one proxy, reported as a proxy: the *narrow* valley residue of batch 53\n"
         "  (valleyResidualNarrow) reads the interval pair, and is kept beside the Lean\n"
         "  predicate ValleyNarrowResidual, which reads rho alone.\n");
  printf("  New in batch 55: the witness analysis reads the V-criterion and TopW5 as their\n"
         "  definitions read them, and the crookedness clause of IsCrookedIvF as the\n"
         "  structure field states it -- anchors within one step, levels three apart, two\n"
         "  returned times strictly between the anchors.  The sigma-route question uses the\n"
         "  same FoldsOnto dynamic program on tau = 9 - sig and on 9 - rho.\n");
  if (sampleFile) fclose(sampleFile);
  free(p.v); free(q.v);
  return 0;
}
