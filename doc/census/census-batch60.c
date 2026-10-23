/* census-batch60.c -- batch 60.  The two ascent clauses of the branch's best
 * walk, read as arm-only dichotomies, and the crossings they leave.
 *
 * New in this batch.
 *
 *   A. Question 1.  The best walk of the branch L+5 is the reflected parameter
 *      set (P, K, M) = (4, 6, 2), i.e. L+6 -> L+3 -> L+7 -> L+1 -> L+8, whose
 *      *ceiling* clause the branch hypothesis LowAt (L+1) (L+8) already gives
 *      (land_down1_of_lowAt_low, HPC/Fold/LandLowAt.lean).  What is left are its
 *      two ascent clauses, read on the reflected arm:
 *
 *        floor  (trigger: the reflected arm descends to 1, i.e. the arm rises
 *                to L+8)  -- the "L+8 clause";
 *        deep   (trigger: the reflected arm descends to 0, i.e. the arm rises
 *                to L+9)  -- the "L+9 clause".
 *
 *      The census evaluates the landmark sentence of that walk clause by clause
 *      on every arm of the branch, and, for every arm that fails a clause, asks
 *      whether the arm *by itself* satisfies the landmark sentence -- the exact
 *      criterion -- of some other walk of the four-leg family.  That is the
 *      arm-only dichotomy of the commission, and it is decidable per arm.
 *
 *   B. Question 2.  The crossings: basepoints whose two arms fail *different*
 *      clauses of the best walk.  The census counts them and reports whether
 *      some single walk of the family serves both arms there (the exact
 *      criterion on each arm), which is what the pair needs.
 *
 * Everything else is carried over from census-batch59.c unchanged.  Its header
 * follows.
 *
 * census-batch59.c -- batch 59.  The branch L+5, read by the *exact* criterion
 * of a four-leg walk: the landmark sentence Leg4Land of HPC/Fold/Leg4Land.lean.
 *
 * New in this batch.
 *
 *   A. Question 1.  foldsOnto_leg4_iff_leg4Land says that, for a 1-Lipschitz arm
 *      of the band whose first level is within one of P-1, folding onto
 *      leg4Walk L H K M P is *equivalent* to the landmark sentence.  The census
 *      evaluates both, by their own definitions, on every arm of the branch and
 *      every parameter set of the window and its reflection, and reports the
 *      disagreements (the theorem says there are none).  The engine's criterion
 *      Leg4Crit is evaluated alongside, so the gain is measured.
 *
 *   B. Question 2.  The 175-link arm of HPC/Fold/Audit58.lean -- the window of
 *      bing 0 9 at its link 811, which meets the criterion of no parameter set
 *      of the engine -- is read by the exact criterion: which walks of the
 *      family serve it, and what the landmark chains are.
 *
 *   C. Question 3.  Exhaustiveness at L+5.  With an exact criterion per walk the
 *      statement "every basepoint of the branch is served by one of a finite
 *      list of walks" is decidable arm by arm, and the census reports it: the
 *      basepoints served by some walk of the family, those served by none, and a
 *      greedy cover of the whole branch by walks.
 *
 * Carried over from census-batch58.c unchanged: the generators, the
 * faithfulness test, the dynamic program, the branch-L+4 block, the
 * reflected-branch block and the whole corpus.  The original header follows.
 *
 * census-batch58.c -- batch 58.  The branch L+5, read by the *criteria* of the
 * four-leg engine rather than by the fold: for every parameter set (P, K, M) of
 * the window of foldsOnto_leg4W (HPC/Fold/Leg4Wide.lean) and its reflection,
 * the three announcements the engine asks for are evaluated on each arm of the
 * branch, in point form and in interval form.
 *
 * New in this batch.
 *
 *   A. Question 1.  The walk L+4 -> L+7 -> L+1 -> L+8 -> L+1 is the engine at
 *      (P, K, M) = (5, 7, 1).  The census counts, per arm, which of its three
 *      announcements -- hfloor, hdeep, hceil -- fails, and how often, so that
 *      the announcements LowAt (L+1) (L+8) and the crookedness clause can be
 *      expected to supply are separated from the ones they cannot.
 *
 *   B. Question 1, second half.  The same for every (P, K, M) of the window,
 *      in particular the walks with the peak K one level lower.  Reported:
 *      how many basepoints of the branch have *some* parameter set whose
 *      criterion holds on both arms, the greedy cover of the branch by
 *      criteria, and how many have none.
 *
 *   C. Question 3.  The same criteria with the high landmarks read on the
 *      interval (sig >= l) instead of on the point (rho >= l), the low
 *      landmarks on the low end of the interval; the triggers stay on rho.
 *      Sufficiency is tested directly: a basepoint at which the interval
 *      criterion holds on an arm and the arm does *not* fold onto the walk
 *      refutes the interval reading of the engine.
 *
 * Carried over from census-batch57.c unchanged: the generators, the
 * faithfulness test, the dynamic program, the branch-L+4 block, the
 * reflected-branch block and the whole corpus.  The original header follows.
 *
 * census-batch57.c -- batch 57.  The branch L+5, read through the reflection
 * of each arm: which of the four statements that close the branch L+4 survive
 * the reflection, and where the one level is lost.
 *
 * Carried over from census-batch56.c unchanged: the generators, the
 * faithfulness test (IsCrookedIvF), the dynamic program over FoldsOnto, the
 * predicates of the walks, the four-leg family and the whole corpus.
 *
 * New in this batch.  At every basepoint of the branch L+5 the two arms are
 * reflected in the level 9 -- armRefl of HPC/Fold/ArmReflect.lean -- so that
 * they are based at 4 and HighAt (L+1) (L+8), and the four statements of the
 * branch L+4 are evaluated on the reflected arms:
 *
 *    - the reflected valley crossing: an arm failing Leg3Valley forces the
 *      pair onto the V-walk;
 *    - the reflected ceiling crossing: an arm failing Leg3Ceil, with the pair
 *      missing the Lambda-walk, gives TopW5 on the failing arm and Valley5 on
 *      the other;
 *    - the three walks: an unserved pair folds onto w3, w4 or w5;
 *    - the one level: when the V-criterion is read on the partner arm, the
 *      census counts separately how often it fails in *point* form (a time of
 *      rho at 2 or below) and in *interval* form (a link whose interval meets
 *      that level, that is sig >= 7 on the unreflected sequence).  The gap
 *      between the two counts is exactly the level the general model loses.
 *
 * The first few failures of the reflected valley crossing are dumped in full.
 *
 * The original file's header follows.
 *
 * census-batch56.c -- batch 56.  The corpus check of what batch 56 proves.
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
  /* the branch L+5, read through the reflection of each arm */
  long reflBad;                    /* LowAt does not reflect to HighAt (must be 0) */
  long valFail5, valFail5Bad;      /* an arm fails the reflected valley clause; the pair
                                    * then misses the reflected V-walk */
  long ceilFail5, ceilCross5, gap5Bad;
  long unserved5, three5Bad;       /* unserved by the two reflected canonical walks;
                                    * then missing all three of w3R, w4R, w5R */
  /* the one level: the criterion in point form fails but holds in interval form */
  long critRhoBad5, critIvBad5, critIvSaves5;
  /* batch 58: the criteria of the four-leg engine at the branch L+5 */
  long critAny5, critNone5;        /* some (P,K,M) whose point criterion holds on both arms */
  long critAnyIv5, critNoneIv5;    /* the same in interval form */
  long critSoundBad5;              /* point criterion holds on both arms, the pair does not
                                    * fold onto the walk (must be 0: the engine is a theorem) */
  long critIvSuffBad5;             /* interval criterion holds on an arm, the arm does not fold */
  long w1Base, w1Floor, w1Deep, w1Ceil, w1All;   /* walk47181, per arm, point form */
  long w1BaseIv, w1FloorIv, w1DeepIv, w1CeilIv, w1AllIv;   /* the same, interval form */
  long w1Arms;                     /* arms of the branch examined (two per basepoint) */
  long w1Both, w1BothIv;           /* basepoints where both arms meet it */
  /* batch 59: the exact criterion, the landmark sentence */
  long landArms;                   /* arms x parameter sets examined */
  long landHolds, foldHolds;       /* the sentence holds; the arm folds */
  long landNotFold, foldNotLand;   /* the two disagreements (both must be 0) */
  long critHoldsPt;                /* the engine's criterion holds (point form) */
  long landNotCrit;                /* the sentence holds where the engine's criterion fails */
  long landAny5, landNone5;        /* a parameter set serving both arms of a basepoint */
  long w1Folds;                    /* basepoints where both arms fold onto it */
  /* batch 60: the clauses of the best walk, and the arm-only dichotomies */
  long b60Arms;                    /* arms of the branch examined (two per basepoint) */
  long b60Ok;                      /* the whole sentence of the best walk holds on the arm */
  long b60Base, b60Floor, b60Deep, b60Ceil;   /* arms failing each clause */
  long b60CeilOnly;                /* arms failing the ceiling clause alone (the branch
                                    * hypothesis is supposed to exclude these) */
  long b60FloorAlt, b60FloorNone;  /* floor-failing arms served / not served by another walk */
  long b60DeepAlt, b60DeepNone;    /* the same for the deep clause */
  long b60AnyFail, b60AnyAlt, b60AnyNone;     /* any clause */
  long b60Cross, b60CrossServed, b60CrossNone;/* the two arms fail different clause sets */
  long b60Pairs, b60PairBothOk;    /* basepoints; both arms meet the best walk */
  /* batch 60: the arm-only trichotomy wb / w8 / w3 */
  long b60TriArms, b60TriWb, b60TriW8, b60TriW3, b60TriNone;
  long b60TriPairShared, b60TriPairCross;
  long b60Quad4Cross, b60Quad5Cross, b60Quad6Cross;  /* crossings as the list grows */
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

/* the same walk, one arm at a time */
static int famFoldsArm(int q, const int *g, int mg) {
  int w[MAXW];
  int wl = buildWalk4(w, fam[q].st, fam[q].a, fam[q].b, fam[q].c, fam[q].e);
  if (wl < 0) return 0;
  return folds(g, mg, w, wl);
}

/* ---- the criteria of the wide four-leg engine, evaluated on an arm --------
 *
 * foldsOnto_leg4W (HPC/Fold/Leg4Wide.lean) asks, with L = 0 and H = 9, for a
 * base in [P-1, P] below K, and three announcements:
 *
 *   hfloor: every d with f d <= P-3 is preceded by a time at K or above, or by
 *           a time at P-2 or below followed by one at K-1 or above;
 *   hdeep:  every d with f d <= P-4 is preceded by a time at K+2 or above, or
 *           by a time at M-1 or below followed by one at H-2 or above, or by a
 *           time at K+1 or above, then one at M or below, then one at H-2 or
 *           above;
 *   hceil:  every d with f d >= K+2 is preceded by a time at M-1 or below, or
 *           by a time at K+1 or above followed by one at M+1 or below, or by a
 *           time at P-2 or below, then one at K or above, then one at M+1 or
 *           below.
 *
 * `p` is the point sequence of the arm; `lo` and `hi` are the two ends of the
 * link's interval, in the arm's own orientation.  Point form is lo = hi = p;
 * interval form reads every "at l or above" landmark on `hi` and every "at l or
 * below" landmark on `lo`, the triggers staying on `p`.  The return value is a
 * bitmask of the clauses that fail: 1 base, 2 hfloor, 4 hdeep, 8 hceil. */
static int critLeg4Mask(const int *p, const int *lo, const int *hi, int m,
                        int K, int M, int P) {
  int bad = 0;
  const int H = 9;
  if (!(p[0] >= P - 1 && p[0] <= P && p[0] <= K - 1)) return 1;
  { int fA = 0, b1 = 0, fB = 0;
    for (int d = 0; d < m; d++) {
      if (p[d] <= P - 3 && !(fA || fB)) { bad |= 2; break; }
      if (hi[d] >= K) fA = 1;
      if (b1 && hi[d] >= K - 1) fB = 1;
      if (lo[d] <= P - 2) b1 = 1;
    } }
  { int fA = 0, b1 = 0, fB = 0, c1 = 0, c2 = 0, fC = 0;
    for (int d = 0; d < m; d++) {
      if (p[d] <= P - 4 && !(fA || fB || fC)) { bad |= 4; break; }
      if (hi[d] >= K + 2) fA = 1;
      if (b1 && hi[d] >= H - 2) fB = 1;
      if (lo[d] <= M - 1) b1 = 1;
      if (c2 && hi[d] >= H - 2) fC = 1;
      if (c1 && lo[d] <= M) c2 = 1;
      if (hi[d] >= K + 1) c1 = 1;
    } }
  { int fA = 0, b1 = 0, fB = 0, c1 = 0, c2 = 0, fC = 0;
    for (int d = 0; d < m; d++) {
      if (p[d] >= K + 2 && !(fA || fB || fC)) { bad |= 8; break; }
      if (lo[d] <= M - 1) fA = 1;
      if (b1 && lo[d] <= M + 1) fB = 1;
      if (hi[d] >= K + 1) b1 = 1;
      if (c2 && lo[d] <= M + 1) fC = 1;
      if (c1 && hi[d] >= K) c2 = 1;
      if (lo[d] <= P - 2) c1 = 1;
    } }
  return bad;
}

/* ---- the landmark sentence Leg4Land of HPC/Fold/Leg4Land.lean --------------
 *
 * The walk leg4Walk 0 9 K M P has its landmark positions at
 *
 *   A = K - P + 1        (the peak, level K)
 *   B = 2K - P + 1 - M   (the valley, level M)
 *   C = 2K - P + 9 - 2M  (the top of the third leg, level 8)
 *
 * and the sentence asks, by its own definition:
 *
 *   base   : the first level is within one of P-1;
 *   floor  : before every d with f d <= P-3 a step j with j >= A, f j >= K-1 and
 *            j + (K - 1 - f d) <= d;
 *   deep   : before every d with f d <= M-2 three steps j, k, l with j >= A,
 *            f j >= K-1, k >= j + (K-M), f k <= M+1, l >= k + (8-M),
 *            f l >= 7 and l + (7 - f d) <= d;
 *   ceiling: before every d with f d >= K+2 two steps j, k with j >= A,
 *            f j >= K-1, k >= j + (K-M), f k <= M+1 and k + (f d - M - 1) <= d.
 *
 * The existential chains are evaluated greedily -- the earliest j, then the
 * earliest k after it, then the earliest l -- which is equivalent to the
 * definition because every constraint of the chain is monotone in the index;
 * landLeg4Brute below evaluates the existentials literally, and the two are
 * compared on a sample as a check on that step. */
static int landChain[3];
static int landLeg4(const int *f, int m, int K, int M, int P) {
  const int H = 9;
  int A = K - P + 1;
  landChain[0] = landChain[1] = landChain[2] = -1;
  if (f[0] < P - 2 || f[0] > P) return 0;
  int t1 = -1, t2 = -1, t3 = -1;
  for (int j = A; j < m; j++) if (f[j] >= K - 1) { t1 = j; break; }
  if (t1 >= 0) for (int k = t1 + (K - M); k < m; k++) if (f[k] <= M + 1) { t2 = k; break; }
  if (t2 >= 0) for (int l = t2 + (H - 1 - M); l < m; l++) if (f[l] >= H - 2) { t3 = l; break; }
  landChain[0] = t1; landChain[1] = t2; landChain[2] = t3;
  for (int d = 0; d < m; d++) {
    if (f[d] <= P - 3 && (t1 < 0 || t1 + (K - 1 - f[d]) > d)) return 0;
    if (f[d] <= M - 2 && (t3 < 0 || t3 + (H - 2 - f[d]) > d)) return 0;
    if (f[d] >= K + 2 && (t2 < 0 || t2 + (f[d] - M - 1) > d)) return 0;
  }
  return 1;
}

/* The same sentence, clause by clause: a bitmask of the clauses that fail.
 *   1 base, 2 floor, 4 deep floor, 8 ceiling.
 * Read on the *reflected* arm at (P, K, M) = (4, 6, 2) the floor clause is the
 * arm's L+8 ascent clause, the deep clause its L+9 ascent clause and the
 * ceiling clause its descent clause. */
static int landLeg4Mask(const int *f, int m, int K, int M, int P) {
  const int H = 9;
  int A = K - P + 1;
  int bad = 0;
  if (f[0] < P - 2 || f[0] > P) bad |= 1;
  int t1 = -1, t2 = -1, t3 = -1;
  for (int j = A; j < m; j++) if (j >= 0 && f[j] >= K - 1) { t1 = j; break; }
  if (t1 >= 0) for (int k = t1 + (K - M); k < m; k++) if (k >= 0 && f[k] <= M + 1) { t2 = k; break; }
  if (t2 >= 0) for (int l = t2 + (H - 1 - M); l < m; l++) if (l >= 0 && f[l] >= H - 2) { t3 = l; break; }
  for (int d = 0; d < m; d++) {
    if (f[d] <= P - 3 && (t1 < 0 || t1 + (K - 1 - f[d]) > d)) bad |= 2;
    if (f[d] <= M - 2 && (t3 < 0 || t3 + (H - 2 - f[d]) > d)) bad |= 4;
    if (f[d] >= K + 2 && (t2 < 0 || t2 + (f[d] - M - 1) > d)) bad |= 8;
  }
  return bad;
}

/* the same sentence with its existentials searched literally; quadratic and
 * cubic, so only used on short arms as a check on the greedy reading */
static int landLeg4Brute(const int *f, int m, int K, int M, int P) {
  const int H = 9;
  int A = K - P + 1;
  if (f[0] < P - 2 || f[0] > P) return 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= P - 3) {
      int ok = 0;
      for (int j = 0; j < m && !ok; j++)
        if (j >= A && f[j] >= K - 1 && j + (K - 1 - f[d]) <= d) ok = 1;
      if (!ok) return 0;
    }
    if (f[d] <= M - 2) {
      int ok = 0;
      for (int j = 0; j < m && !ok; j++) {
        if (!(j >= A && f[j] >= K - 1)) continue;
        for (int k = 0; k < m && !ok; k++) {
          if (!(k >= j + (K - M) && f[k] <= M + 1)) continue;
          for (int l = 0; l < m && !ok; l++)
            if (l >= k + (H - 1 - M) && f[l] >= H - 2 && l + (H - 2 - f[d]) <= d) ok = 1;
        }
      }
      if (!ok) return 0;
    }
    if (f[d] >= K + 2) {
      int ok = 0;
      for (int j = 0; j < m && !ok; j++) {
        if (!(j >= A && f[j] >= K - 1)) continue;
        for (int k = 0; k < m && !ok; k++)
          if (k >= j + (K - M) && f[k] <= M + 1 && k + (f[d] - M - 1) <= d) ok = 1;
      }
      if (!ok) return 0;
    }
  }
  return 1;
}

/* the fold onto the *direct* walk of a parameter set, P-1 -> K -> M -> 8 -> 1 */
static int foldsDirect(const int *f, int m, int K, int M, int P) {
  int w[MAXW];
  int wl = buildWalk4(w, P - 1, K, M, 8, 1);
  if (wl < 0) return 0;
  return folds(f, m, w, wl);
}

#define BRUTECAP 40000
static long bruteSamples = 0, bruteBad = 0;
#define FOLDCAP 400000
static long foldSamples = 0;

/* the residual basepoints of the branch L+5 and the family walks serving them */
#define MAXRES 200000
static unsigned long long resMask[MAXRES];
static long resN = 0;

/* batch 59: the walks of the family serving both arms at a basepoint of the branch */
static unsigned long long critMaskPt[MAXRES];
static long critN = 0;
static long critHits[MAXFAM];

/* batch 60: which walks serve an arm that fails a clause of the best walk */
static long altFloorHits[MAXFAM], altDeepHits[MAXFAM];
/* the walks serving both arms at a crossing of the three */
static long triCrossHits[MAXFAM];
static unsigned long long triCrossMask[16384];
static long triCrossN = 0;
/* the masks of the serving walks, per clause-failing arm, for a greedy cover */
#define MAXALT 200000
static unsigned long long altFloorMask[MAXALT], altDeepMask[MAXALT];
static long altFloorN = 0, altDeepN = 0;

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
      if (j < *minIdx) *minIdx = j;
      break; }
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

/* ---- the branch L+5, read through the reflection of each arm ------------- */

/* the reflected arm and the lower end of its reflected interval: the interval of
 * the link `u` is [rho u, sig u], and its reflection in the level 9 is
 * [9 - sig u, 9 - rho u]; the reflected *point* sequence is 9 - rho, the upper
 * end, which is what `armRefl` of HPC/Fold/ArmReflect.lean is. */
static int gG[MAXN], gT[MAXN], gGlo[MAXN], gTlo[MAXN];

/* the V-criterion on the reflected arm, in point form: before every ascent to 7,
 * a time at 2 or below at index `bound` or later */
static int critVeePt(const int *g, int m, int bound) {
  for (int d = 0; d < m; d++) {
    if (g[d] < 7) continue;
    int ok = 0;
    for (int j = bound; j < d; j++) if (g[j] <= 2) { ok = 1; break; }
    if (!ok) return 0;
  }
  return 1;
}

/* the same criterion in interval form: the witness is a link whose reflected
 * interval *meets* the level 2, that is a link of the sequence with sig >= 7 */
static int critVeeIv(const int *g, const int *glo, int m, int bound) {
  for (int d = 0; d < m; d++) {
    if (g[d] < 7) continue;
    int ok = 0;
    for (int j = bound; j < d; j++) if (glo[j] <= 2) { ok = 1; break; }
    if (!ok) return 0;
  }
  return 1;
}

static long sampleN = 0;
#define MAXSAMPLE 3
static void dumpSample(const char *why, int n, int i, int mg, int mt) {
  if (sampleN >= MAXSAMPLE) return;
  sampleN++;
  printf("\n  ---- sample %ld: %s (n = %d, basepoint %d) ----\n", sampleN, why, n, i);
  printf("    rho:");
  for (int u = 0; u < n; u++) printf(" %d", rho[u]);
  printf("\n    sig:");
  for (int u = 0; u < n; u++) printf(" %d", sig[u]);
  printf("\n    reflected forward arm (%d):", mg);
  for (int d = 0; d < mg; d++) printf(" %d", gG[d]);
  printf("\n    reflected backward arm (%d):", mt);
  for (int d = 0; d < mt; d++) printf(" %d", gT[d]);
  printf("\n");
}

/* ---- shrinking a failure of the reflected valley crossing to a window ----- */

/* All the conditions the counterexample needs, tested on the window [a, b] of
 * the current pair, with the basepoint at the index `i` of the whole: the
 * window is faithful, the basepoint is a basepoint of the branch L+5, an arm
 * reflected in the level 9 fails the valley clause, and the pair misses the
 * reflected V-walk. */
static int wrho[MAXN], wsig[MAXN], wgG[MAXN], wgT[MAXN];

static int okWindow(int a, int b, int i) {
  if (a > i || b < i) return 0;
  int len = b - a + 1;
  for (int u = 0; u < len; u++) { wrho[u] = rho[a + u]; wsig[u] = sig[a + u]; }
  if (!crookedGen(wrho, wsig, len)) return 0;
  int j = i - a, mg = len - j, mt = j + 1;
  if (wrho[j] != 5) return 0;
  static int aG[MAXN], aT[MAXN];
  for (int d = 0; d < mg; d++) aG[d] = wrho[j + d];
  for (int d = 0; d < mt; d++) aT[d] = wrho[j - d];
  if (!(lowAt(aG, mg) && lowAt(aT, mt))) return 0;
  for (int d = 0; d < mg; d++) wgG[d] = 9 - aG[d];
  for (int d = 0; d < mt; d++) wgT[d] = 9 - aT[d];
  if (leg3Valley(wgG, mg) && leg3Valley(wgT, mt)) return 0;
  if (foldsVee(wgG, mg) && foldsVee(wgT, mt)) return 0;
  return 1;
}

static int emitted = 0;

static void emitWindow(int n, int i, const char *tag) {
  if (emitted) return;
  if (!okWindow(0, n - 1, i)) return;
  int a = 0, b = n - 1;
  int steps[5] = {64, 16, 4, 1, 1};
  for (int pass = 0; pass < 5; pass++) {
    int st = steps[pass];
    while (a + st <= i && okWindow(a + st, b, i)) a += st;
    while (b - st >= i && okWindow(a, b - st, i)) b -= st;
  }
  emitted = 1;
  int len = b - a + 1, j = i - a, mg = len - j, mt = j + 1;
  okWindow(a, b, i);
  printf("\n======== the counterexample window (%s) ========\n", tag);
  printf("  window [%d, %d] of %d links; basepoint %d of %d links; arms %d and %d\n",
         a, b, n, j, len, mg, mt);
  printf("  rho:");
  for (int u = 0; u < len; u++) printf(" %d", wrho[u]);
  printf("\n  sig:");
  for (int u = 0; u < len; u++) printf(" %d", wsig[u]);
  printf("\n  rho as a base-sixteen numeral (most significant digit last link): 0x");
  for (int u = len - 1; u >= 0; u--) printf("%x", wrho[u]);
  printf("\n  sig as a base-sixteen numeral: 0x");
  for (int u = len - 1; u >= 0; u--) printf("%x", wsig[u]);
  printf("\n  the reflected forward arm (%d):", mg);
  for (int d = 0; d < mg; d++) printf(" %d", wgG[d]);
  printf("\n  the reflected backward arm (%d):", mt);
  for (int d = 0; d < mt; d++) printf(" %d", wgT[d]);
  printf("\n  reflected forward arm fails Leg3Valley: %d; backward: %d\n",
         !leg3Valley(wgG, mg), !leg3Valley(wgT, mt));
  printf("  reflected forward arm folds onto the V-walk: %d; backward: %d\n",
         foldsVee(wgG, mg), foldsVee(wgT, mt));
  printf("  reflected arms HighAt (L+1) (L+8): %d and %d\n",
         highAt(wgG, mg), highAt(wgT, mt));
  printf("  the window is faithful (IsCrookedIvF): %d\n", crookedGen(wrho, wsig, len));
  printf("========================================================\n");
}

/* ---- batch 58: the two witnesses -----------------------------------------
 *
 * (a) a basepoint of the branch L+5 at which *no* parameter set of the window
 *     of the wide four-leg engine has its criterion on both arms;
 * (b) an arm which meets the criterion of a parameter set with the landmarks
 *     read on the interval and does not fold onto its walk.
 */

static int nrho[MAXN], nsig[MAXN];

/* the conditions of witness (a), on the window [a, b] with basepoint i */
static int okWindowNC(int a, int b, int i) {
  if (a > i || b < i) return 0;
  int len = b - a + 1;
  for (int u = 0; u < len; u++) { nrho[u] = rho[a + u]; nsig[u] = sig[a + u]; }
  if (!crookedGen(nrho, nsig, len)) return 0;
  int j = i - a, mg = len - j, mt = j + 1;
  if (nrho[j] != 5) return 0;
  static int aG[MAXN], aT[MAXN], rG[MAXN], rT[MAXN];
  for (int d = 0; d < mg; d++) { aG[d] = nrho[j + d]; rG[d] = 9 - aG[d]; }
  for (int d = 0; d < mt; d++) { aT[d] = nrho[j - d]; rT[d] = 9 - aT[d]; }
  if (!(lowAt(aG, mg) && lowAt(aT, mt))) return 0;
  for (int q = 0; q < famN; q++) {
    int K = fam[q].K, M = fam[q].M, P = fam[q].P, bG, bT;
    if (!fam[q].refl) {
      bG = critLeg4Mask(aG, aG, aG, mg, K, M, P);
      bT = critLeg4Mask(aT, aT, aT, mt, K, M, P);
    } else {
      bG = critLeg4Mask(rG, rG, rG, mg, K, M, P);
      bT = critLeg4Mask(rT, rT, rT, mt, K, M, P);
    }
    if (bG == 0 && bT == 0) return 0;
  }
  return 1;
}

static int emittedNC = 0;

static void emitNoCrit(int n, int i) {
  if (emittedNC) return;
  if (!okWindowNC(0, n - 1, i)) return;
  int a = 0, b = n - 1;
  int steps[5] = {64, 16, 4, 1, 1};
  for (int pass = 0; pass < 5; pass++) {
    int st = steps[pass];
    while (a + st <= i && okWindowNC(a + st, b, i)) a += st;
    while (b - st >= i && okWindowNC(a, b - st, i)) b -= st;
  }
  emittedNC = 1;
  int len = b - a + 1, j = i - a;
  okWindowNC(a, b, i);
  printf("\n======== witness (a): no four-leg criterion at a basepoint of the branch "
         "========\n");
  printf("  window [%d, %d] of %d links; basepoint %d of %d links\n", a, b, n, j, len);
  printf("  rho:");
  for (int u = 0; u < len; u++) printf(" %d", nrho[u]);
  printf("\n  sig:");
  for (int u = 0; u < len; u++) printf(" %d", nsig[u]);
  printf("\n  rho as a base-sixteen numeral (most significant digit last link): 0x");
  for (int u = len - 1; u >= 0; u--) printf("%x", nrho[u]);
  printf("\n  sig as a base-sixteen numeral: 0x");
  for (int u = len - 1; u >= 0; u--) printf("%x", nsig[u]);
  printf("\n  the window is faithful (IsCrookedIvF): %d\n", crookedGen(nrho, nsig, len));
  printf("==================================================================\n");
}

/* ---- the shortest prefix of a forward arm that no walk serves ---------------
 *
 * A fold is inherited by a prefix: if the whole arm folds onto a walk then so
 * does every prefix of it.  The same holds for `LowAt` and for faithfulness.  So
 * the shortest prefix of a forward arm that *no* walk of the family serves is a
 * counterexample in its own right, read as a faithful pair whose basepoint is
 * its first link -- the backward arm is then the single basepoint link, which
 * folds onto every walk whose first level it meets.
 *
 * The condition is monotone in the length, so the shortest such prefix is found
 * by bisection. */
static int bestNoCritLen = 1 << 30, bestNoCritI = -1, bestNoCritN = -1;
static int bestNoCritRho[MAXN], bestNoCritSig[MAXN];

/* does the prefix of length `len` of the forward arm at `i` meet no criterion? */
static int prefixNoCrit(int i, int len) {
  static int aG[MAXN], rG[MAXN];
  for (int d = 0; d < len; d++) { aG[d] = rho[i + d]; rG[d] = 9 - aG[d]; }
  for (int q = 0; q < famN; q++) {
    int K = fam[q].K, M = fam[q].M, P = fam[q].P;
    int la = fam[q].refl ? landLeg4(rG, len, K, M, P)
                         : landLeg4(aG, len, K, M, P);
    if (la) return 0;
  }
  return 1;
}

static void noteNoCrit(int n, int i, int mg) {
  if (mg >= bestNoCritLen) return;
  if (!prefixNoCrit(i, mg)) return;
  int lo = 1, hi = mg;
  while (lo < hi) {
    int mid = (lo + hi) / 2;
    if (prefixNoCrit(i, mid)) hi = mid; else lo = mid + 1;
  }
  if (lo >= bestNoCritLen) return;
  bestNoCritLen = lo; bestNoCritI = i; bestNoCritN = n;
  for (int u = 0; u < lo; u++) { bestNoCritRho[u] = rho[i + u]; bestNoCritSig[u] = sig[i + u]; }
}

static void reportNoCrit(void) {
  if (bestNoCritI < 0) {
    printf("\n  every arm of the branch is served by some walk of the family\n"); return; }
  int len = bestNoCritLen;
  for (int u = 0; u < len; u++) { nrho[u] = bestNoCritRho[u]; nsig[u] = bestNoCritSig[u]; }
  printf("\n======== the shortest arm of the branch served by no four-leg walk ========\n");
  printf("  the forward arm at the basepoint %d of a chain of %d links, cut to %d links\n",
         bestNoCritI, bestNoCritN, len);
  printf("  rho:");
  for (int u = 0; u < len; u++) printf(" %d", nrho[u]);
  printf("\n  sig:");
  for (int u = 0; u < len; u++) printf(" %d", nsig[u]);
  printf("\n  rho as a base-sixteen numeral (most significant digit last link): 0x");
  for (int u = len - 1; u >= 0; u--) printf("%x", nrho[u]);
  printf("\n  sig as a base-sixteen numeral: 0x");
  for (int u = len - 1; u >= 0; u--) printf("%x", nsig[u]);
  printf("\n  faithful (IsCrookedIvF): %d; LowAt on the arm: %d\n",
         crookedGen(nrho, nsig, len), lowAt(nrho, len));
  printf("  the fold and the landmark sentence, per parameter set:\n");
  {
    static int aG[MAXN], rG[MAXN];
    for (int d = 0; d < len; d++) { aG[d] = nrho[d]; rG[d] = 9 - aG[d]; }
    for (int q = 0; q < famN; q++) {
      const int *a = fam[q].refl ? rG : aG;
      int fo = foldsDirect(a, len, fam[q].K, fam[q].M, fam[q].P);
      int la = landLeg4(a, len, fam[q].K, fam[q].M, fam[q].P);
      printf("    %s P=%d K=%d M=%d : folds %d, landmark sentence %d\n",
             fam[q].refl ? "reflected" : "direct  ", fam[q].P, fam[q].K, fam[q].M, fo, la);
    }
  }
  printf("==================================================================\n");
}

/* ---- batch 60: the shortest arm witnessing a failure of a dichotomy --------
 *
 * An arm that fails a clause of the best walk and that no walk of the family
 * serves refutes the arm-only dichotomy of question 1.  Both conditions are
 * monotone in the length of a prefix -- a clause once failed stays failed, and
 * an arm no walk serves has no prefix-extension any walk serves -- so the
 * shortest such prefix is found by bisection, exactly as in noteNoCrit. */
static int prefixAltFail(int i, int len, int clause) {
  static int aG[MAXN], rG[MAXN];
  for (int d = 0; d < len; d++) { aG[d] = rho[i + d]; rG[d] = 9 - aG[d]; }
  if (!(landLeg4Mask(rG, len, 6, 2, 4) & clause)) return 0;
  for (int q = 0; q < famN; q++) {
    int K = fam[q].K, M = fam[q].M, P = fam[q].P;
    int la = fam[q].refl ? landLeg4(rG, len, K, M, P) : landLeg4(aG, len, K, M, P);
    if (la) return 0;
  }
  return 1;
}

static int bestAltLen[2] = {1 << 30, 1 << 30}, bestAltI[2] = {-1, -1}, bestAltN[2] = {-1, -1};
static int bestAltRho[2][MAXN], bestAltSig[2][MAXN];

static void noteAltFail(int which, int clause, int n, int i, int mg) {
  if (mg >= bestAltLen[which]) return;
  if (!prefixAltFail(i, mg, clause)) return;
  int lo = 1, hi = mg;
  while (lo < hi) {
    int mid = (lo + hi) / 2;
    if (prefixAltFail(i, mid, clause)) hi = mid; else lo = mid + 1;
  }
  if (lo >= bestAltLen[which]) return;
  bestAltLen[which] = lo; bestAltI[which] = i; bestAltN[which] = n;
  for (int u = 0; u < lo; u++) {
    bestAltRho[which][u] = rho[i + u]; bestAltSig[which][u] = sig[i + u];
  }
}

static void reportAltFail(int which, const char *name) {
  if (bestAltI[which] < 0) {
    printf("\n  every arm failing the %s clause of the best walk is served by another "
           "walk of the family\n", name);
    return;
  }
  int len = bestAltLen[which];
  printf("\n======== an arm failing the %s clause and served by no walk ========\n", name);
  printf("  the forward arm at the basepoint %d of a chain of %d links, cut to %d links\n",
         bestAltI[which], bestAltN[which], len);
  printf("  rho:");
  for (int u = 0; u < len; u++) printf(" %d", bestAltRho[which][u]);
  printf("\n  sig:");
  for (int u = 0; u < len; u++) printf(" %d", bestAltSig[which][u]);
  printf("\n  rho as a base-sixteen numeral (most significant digit last link): 0x");
  for (int u = len - 1; u >= 0; u--) printf("%x", bestAltRho[which][u]);
  printf("\n==================================================================\n");
}

/* a greedy cover of the recorded clause-failing arms by walks of the family */
static void greedyAlt(const char *name, unsigned long long *mask, long nmask) {
  static char done[MAXALT];
  if (nmask == 0) { printf("  no %s-failing arms recorded\n", name); return; }
  memset(done, 0, sizeof(done));
  long left = nmask, picks = 0, none = 0;
  for (long t = 0; t < nmask; t++) if (mask[t] == 0) { done[t] = 1; left--; none++; }
  printf("  greedy cover of the %ld recorded %s-failing arms (%ld served by no walk):\n",
         nmask, name, none);
  while (left > 0 && picks < 12) {
    int best = -1; long bestc = 0;
    for (int q = 0; q < famN; q++) {
      long cnt = 0;
      for (long t = 0; t < nmask; t++)
        if (!done[t] && (mask[t] & (1ULL << q))) cnt++;
      if (cnt > bestc) { bestc = cnt; best = q; }
    }
    if (best < 0) break;
    for (long t = 0; t < nmask; t++)
      if (!done[t] && (mask[t] & (1ULL << best))) { done[t] = 1; left--; }
    picks++;
    printf("    pick %ld: %s P=%d K=%d M=%d (%d -> %d -> %d -> %d -> %d) covers %ld, left %ld\n",
           picks, fam[best].refl ? "reflected" : "direct   ", fam[best].P, fam[best].K,
           fam[best].M, fam[best].st, fam[best].a, fam[best].b, fam[best].c, fam[best].e,
           bestc, left);
  }
  printf("    walks needed: %ld; arms left uncovered: %ld\n", picks, left);
}

/* -------------------------------- the scan -------------------------------- */

static void scan(Cnt *c, int n, const char *tag, int gen) {
  (void)gen;
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
      /* the two arms, reflected in the level 9: they are based at 4 */
      for (int d = 0; d < mg; d++) { gG[d] = 9 - rho[i + d]; gGlo[d] = 9 - sig[i + d]; }
      for (int d = 0; d < mt; d++) { gT[d] = 9 - rho[i - d]; gTlo[d] = 9 - sig[i - d]; }
      if (!(highAt(gG, mg) && highAt(gT, mt))) c->reflBad++;
      /* the reflected valley crossing: if an arm fails the reflected valley clause,
       * does the pair fold onto the reflected V-walk? */
      int fvG = !leg3Valley(gG, mg), fvT = !leg3Valley(gT, mt);
      if (fvG || fvT) {
        c->valFail5++;
        if (!(foldsVee(gG, mg) && foldsVee(gT, mt))) {
          c->valFail5Bad++;
          dumpSample("an arm fails the reflected valley clause and the pair misses "
                     "the reflected V-walk", n, i, mg, mt);
          emitWindow(n, i, tag);
        }
        /* the one level: the V-criterion on the partner arm, point form against
         * interval form */
        if (fvG) {
          int pt = critVeePt(gT, mt, 4), iv = critVeeIv(gT, gTlo, mt, 4);
          if (!pt) c->critRhoBad5++;
          if (!iv) c->critIvBad5++;
          if (!pt && iv) c->critIvSaves5++;
        }
        if (fvT) {
          int pt = critVeePt(gG, mg, 4), iv = critVeeIv(gG, gGlo, mg, 4);
          if (!pt) c->critRhoBad5++;
          if (!iv) c->critIvBad5++;
          if (!pt && iv) c->critIvSaves5++;
        }
      }
      /* the reflected ceiling crossing */
      int fcG = !leg3Ceil(gG, mg), fcT = !leg3Ceil(gT, mt);
      if (fcG || fcT) {
        c->ceilFail5++;
        if (!(foldsLam(gG, mg) && foldsLam(gT, mt))) {
          c->ceilCross5++;
          if (fcG && !(topW5(gG, mg) && valley5(gT, mt))) c->gap5Bad++;
          if (fcT && !(topW5(gT, mt) && valley5(gG, mg))) c->gap5Bad++;
        }
      }
      if (!(foldsLam(gG, mg) && foldsLam(gT, mt)) &&
          !(foldsVee(gG, mg) && foldsVee(gT, mt))) {
        c->unserved5++;
        int w3 = foldsW3(gG, mg) && foldsW3(gT, mt);
        int w4 = foldsW4(gG, mg) && foldsW4(gT, mt);
        int w5 = foldsW5(gG, mg) && foldsW5(gT, mt);
        if (!(w3 || w4 || w5)) c->three5Bad++;
      }
      /* ---- batch 59: the exact criterion, against the fold itself ---- */
      {
        unsigned long long mland = 0;
        for (int q = 0; q < famN; q++) {
          int K = fam[q].K, M = fam[q].M, P = fam[q].P;
          const int *aG = fam[q].refl ? gG : armG;
          const int *aT = fam[q].refl ? gT : armT;
          int lG = landLeg4(aG, mg, K, M, P), lT = landLeg4(aT, mt, K, M, P);
          int cG = (critLeg4Mask(aG, aG, aG, mg, K, M, P) == 0);
          int cT = (critLeg4Mask(aT, aT, aT, mt, K, M, P) == 0);
          c->landArms += 2;
          c->landHolds += lG + lT;
          c->critHoldsPt += cG + cT;
          if (lG && !cG) c->landNotCrit++;
          if (lT && !cT) c->landNotCrit++;
          /* the fold is quadratic where the sentence is linear, so it is run on a
           * capped sample -- in both directions, which is the theorem on the corpus */
          if (foldSamples < FOLDCAP) {
            foldSamples += 2;
            int fG = foldsDirect(aG, mg, K, M, P), fT = foldsDirect(aT, mt, K, M, P);
            c->foldHolds += fG + fT;
            if (lG && !fG) c->landNotFold++;
            if (lT && !fT) c->landNotFold++;
            if (fG && !lG) c->foldNotLand++;
            if (fT && !lT) c->foldNotLand++;
          }
          if (mg <= 40 && bruteSamples < BRUTECAP) {
            bruteSamples++;
            if (landLeg4Brute(aG, mg, K, M, P) != lG) bruteBad++;
          }
          if (lG && lT) { mland |= 1ULL << q; critHits[q]++; }
        }
        if (mland) c->landAny5++; else { c->landNone5++; emitNoCrit(n, i); }
        noteNoCrit(n, i, mg);
        if (critN < MAXRES) { critMaskPt[critN] = mland; critN++; }
      }
      /* ---- batch 60: the clauses of the best walk, arm by arm ---- */
      {
        const int Kb = 6, Mb = 2, Pb = 4;   /* reflected: 6 -> 3 -> 7 -> 1 -> 8 */
        int bmask[2]; const int *arms[2]; int alen[2];
        bmask[0] = landLeg4Mask(gG, mg, Kb, Mb, Pb);
        bmask[1] = landLeg4Mask(gT, mt, Kb, Mb, Pb);
        arms[0] = gG; arms[1] = gT; alen[0] = mg; alen[1] = mt;
        (void)arms; (void)alen;
        unsigned long long serves[2] = {0, 0};
        for (int q = 0; q < famN; q++) {
          int K = fam[q].K, M = fam[q].M, P = fam[q].P;
          const int *aG = fam[q].refl ? gG : armG;
          const int *aT = fam[q].refl ? gT : armT;
          if (!(fam[q].refl && K == Kb && M == Mb && P == Pb)) {
            if (landLeg4(aG, mg, K, M, P)) serves[0] |= 1ULL << q;
            if (landLeg4(aT, mt, K, M, P)) serves[1] |= 1ULL << q;
          }
        }
        c->b60Pairs++;
        if (bmask[0] == 0 && bmask[1] == 0) c->b60PairBothOk++;
        for (int s = 0; s < 2; s++) {
          int bm = bmask[s];
          c->b60Arms++;
          if (bm == 0) { c->b60Ok++; continue; }
          if (bm & 1) c->b60Base++;
          if (bm & 2) c->b60Floor++;
          if (bm & 4) c->b60Deep++;
          if (bm & 8) c->b60Ceil++;
          if (bm == 8) c->b60CeilOnly++;
          c->b60AnyFail++;
          if (serves[s]) c->b60AnyAlt++; else c->b60AnyNone++;
          if (bm & 2) {
            if (serves[s]) c->b60FloorAlt++; else c->b60FloorNone++;
            for (int q = 0; q < famN; q++) if (serves[s] & (1ULL << q)) altFloorHits[q]++;
            if (altFloorN < MAXALT) altFloorMask[altFloorN++] = serves[s];
            if (s == 0 && !serves[s]) noteAltFail(0, 2, n, i, mg);
          }
          if (bm & 4) {
            if (serves[s]) c->b60DeepAlt++; else c->b60DeepNone++;
            for (int q = 0; q < famN; q++) if (serves[s] & (1ULL << q)) altDeepHits[q]++;
            if (altDeepN < MAXALT) altDeepMask[altDeepN++] = serves[s];
            if (s == 0 && !serves[s]) noteAltFail(1, 4, n, i, mg);
          }
        }
        /* the trichotomy: wb = reflected (4,6,2), w8 = direct (5,8,1),
         * w3 = reflected (4,6,1) */
        {
          int tG = 0, tT = 0;
          if (bmask[0] == 0) tG |= 1;
          if (landLeg4(armG, mg, 8, 1, 5)) tG |= 2;
          if (landLeg4(gG, mg, 6, 1, 4)) tG |= 4;
          if (bmask[1] == 0) tT |= 1;
          if (landLeg4(armT, mt, 8, 1, 5)) tT |= 2;
          if (landLeg4(gT, mt, 6, 1, 4)) tT |= 4;
          c->b60TriArms += 2;
          if (tG & 1) c->b60TriWb++;
          if (tG & 2) c->b60TriW8++;
          if (tG & 4) c->b60TriW3++;
          if (tT & 1) c->b60TriWb++;
          if (tT & 2) c->b60TriW8++;
          if (tT & 4) c->b60TriW3++;
          if (tG == 0) c->b60TriNone++;
          if (tT == 0) c->b60TriNone++;
          /* the same list grown by direct (5,7,2) and by reflected (4,7,2) */
          {
            int qG = tG, qT = tT;
            if (landLeg4(armG, mg, 7, 2, 5)) qG |= 8;
            if (landLeg4(armT, mt, 7, 2, 5)) qT |= 8;
            if (!(qG & qT)) c->b60Quad4Cross++;
            if (landLeg4(armG, mg, 8, 1, 6)) qG |= 16;
            if (landLeg4(armT, mt, 8, 1, 6)) qT |= 16;
            if (!(qG & qT)) c->b60Quad5Cross++;
            if (landLeg4(gG, mg, 7, 2, 4)) qG |= 32;
            if (landLeg4(gT, mt, 7, 2, 4)) qT |= 32;
            if (!(qG & qT)) c->b60Quad6Cross++;
          }
          if (tG & tT) c->b60TriPairShared++;
          else {
            c->b60TriPairCross++;
            unsigned long long both = 0;
            for (int q = 0; q < famN; q++) {
              int K = fam[q].K, M = fam[q].M, P = fam[q].P;
              const int *aG = fam[q].refl ? gG : armG;
              const int *aT = fam[q].refl ? gT : armT;
              if (landLeg4(aG, mg, K, M, P) && landLeg4(aT, mt, K, M, P)) {
                both |= 1ULL << q; triCrossHits[q]++;
              }
            }
            if (triCrossN < 16384) triCrossMask[triCrossN++] = both;
          }
        }
        if (bmask[0] != bmask[1] && bmask[0] != 0 && bmask[1] != 0) {
          c->b60Cross++;
          /* the pair needs one walk serving both arms; the best walk serves neither */
          if (serves[0] & serves[1]) c->b60CrossServed++; else c->b60CrossNone++;
        }
      }
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
  printf("    the reflection of LowAt is HighAt: fails at %ld (must be 0)\n", c->reflBad);
  printf("    reflected valley failures %ld; pairs then missing the reflected V-walk: %ld\n",
         c->valFail5, c->valFail5Bad);
  printf("      the V-criterion on the partner arm: fails in point form %ld, in interval "
         "form %ld;\n      interval form saves it %ld times\n",
         c->critRhoBad5, c->critIvBad5, c->critIvSaves5);
  printf("    reflected ceiling failures %ld, of them missing the reflected Lambda-walk "
         "%ld;\n      the gap (TopW5 on the failing arm, Valley5 on the other) fails at %ld\n",
         c->ceilFail5, c->ceilCross5, c->gap5Bad);
  printf("    unserved by the two reflected canonical walks %ld; served by none of w3R, "
         "w4R, w5R: %ld\n", c->unserved5, c->three5Bad);
  printf("  batch 59, the exact criterion at the branch L+5:\n");
  printf("    arms x parameter sets %ld; the landmark sentence holds %ld\n",
         c->landArms, c->landHolds);
  printf("    of a capped sample of %ld arms x parameter sets, the arm folds %ld times\n",
         foldSamples, c->foldHolds);
  printf("    the sentence holds and the arm does not fold (must be 0): %ld\n", c->landNotFold);
  printf("    the arm folds and the sentence fails (must be 0): %ld\n", c->foldNotLand);
  printf("    the engine's criterion holds %ld; the sentence holds where it fails %ld\n",
         c->critHoldsPt, c->landNotCrit);
  printf("    basepoints with a parameter set serving *both* arms: %ld; with none: %ld\n",
         c->landAny5, c->landNone5);
  printf("  batch 60, the best walk L+6 -> L+3 -> L+7 -> L+1 -> L+8 (reflected P=4 K=6 M=2):\n");
  printf("    arms %ld; its landmark sentence holds on %ld; basepoints %ld, both arms %ld\n",
         c->b60Arms, c->b60Ok, c->b60Pairs, c->b60PairBothOk);
  printf("    arms failing: base %ld, floor (the L+8 clause) %ld, deep (the L+9 clause) %ld, "
         "ceiling (the descent) %ld\n", c->b60Base, c->b60Floor, c->b60Deep, c->b60Ceil);
  printf("    arms failing the ceiling clause alone (the branch hypothesis should exclude "
         "these): %ld\n", c->b60CeilOnly);
  printf("    the dichotomy, arm by arm: of the %ld arms failing some clause, %ld satisfy the "
         "landmark\n      sentence of another walk of the family and %ld satisfy none\n",
         c->b60AnyFail, c->b60AnyAlt, c->b60AnyNone);
  printf("      floor-failing arms: served by another walk %ld, by none %ld\n",
         c->b60FloorAlt, c->b60FloorNone);
  printf("      deep-failing arms:  served by another walk %ld, by none %ld\n",
         c->b60DeepAlt, c->b60DeepNone);
  printf("    crossings (the two arms fail different clause sets): %ld; some walk serves both "
         "arms %ld, none %ld\n", c->b60Cross, c->b60CrossServed, c->b60CrossNone);
  printf("    the arm-only trichotomy wb = reflected (4,6,2), w8 = direct (5,8,1), "
         "w3 = reflected (4,6,1):\n");
  printf("      arms %ld; served by wb %ld, by w8 %ld, by w3 %ld, by none of the three "
         "(must be 0): %ld\n", c->b60TriArms, c->b60TriWb, c->b60TriW8, c->b60TriW3,
         c->b60TriNone);
  printf("      basepoints with one of the three serving both arms %ld; crossings of the "
         "three %ld\n", c->b60TriPairShared, c->b60TriPairCross);
  printf("      crossings when the list is grown by direct (5,7,2): %ld; also by direct "
         "(6,8,1): %ld;\n        also by reflected (4,7,2): %ld\n",
         c->b60Quad4Cross, c->b60Quad5Cross, c->b60Quad6Cross);
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
  printf("census-batch60: the two ascent clauses of the branch's best walk, as\n"
         "arm-only dichotomies, and the crossings they leave.\n");
  printf("rounds=%ld seed=%u walk-steps=%ld concat-draws=%ld\n", rounds, seed, walkSteps,
         rchains);
  zero(&ct); zero(&cs); zero(&cf); zero(&cm); zero(&ch); zero(&cw); zero(&cr);
  buildFamily();
  printf("the four-leg family of the wide engine: %d walks "
         "(%d parameter sets and their reflections)\n", famN, famN / 2);

  /* ---- question 2: the 175-link arm of HPC/Fold/Audit58.lean ------------ */
  {
    Path b = bpath(0, 9);
    printf("\nquestion 2: the arm of Audit58 -- bing 0 9 (%d links) from its link 811, "
           "175 links\n", b.n);
    static int arm[MAXN], armR[MAXN];
    int m175 = 175;
    for (int t = 0; t < m175; t++) { arm[t] = b.v[811 + t]; armR[t] = 9 - arm[t]; }
    printf("  the arm begins %d %d %d %d %d ... and ends ... %d %d %d\n",
           arm[0], arm[1], arm[2], arm[3], arm[4], arm[172], arm[173], arm[174]);
    int served = 0, crit = 0;
    for (int q = 0; q < famN; q++) {
      int K = fam[q].K, M = fam[q].M, P = fam[q].P;
      const int *a = fam[q].refl ? armR : arm;
      int fo = foldsDirect(a, m175, K, M, P);
      int la = landLeg4(a, m175, K, M, P);
      int t1 = landChain[0], t2 = landChain[1], t3 = landChain[2];
      int cr = (critLeg4Mask(a, a, a, m175, K, M, P) == 0);
      if (cr) crit++;
      if (fo != la) printf("  DISAGREEMENT at P%d K%d M%d %s\n", P, K, M,
                           fam[q].refl ? "reflected" : "direct");
      if (fo) {
        served++;
        printf("  served by (P,K,M) = (%d,%d,%d) %s: walk %d -> %d -> %d -> 8 -> 1;"
               " landmark chain %d, %d, %d; engine's criterion %s\n",
               P, K, M, fam[q].refl ? "reflected" : "direct   ",
               P - 1, K, M, t1, t2, t3, cr ? "holds" : "fails");
      }
    }
    printf("  walks of the family serving the arm: %d of %d; "
           "parameter sets whose engine criterion holds: %d\n", served, famN, crit);
    free(b.v);
  }

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

  printf("\n---- the four-leg family over the whole branch L+5 ----\n");
  printf("  basepoints of the branch L+5 recorded: %ld\n", critN);
  for (int q2 = 0; q2 < famN; q2++)
    if (critHits[q2])
      printf("  %s P=%d K=%d M=%d : %d -> %d -> %d -> %d -> %d  serves both arms at %ld\n",
             fam[q2].refl ? "reflected" : "direct  ", fam[q2].P, fam[q2].K, fam[q2].M,
             fam[q2].st, fam[q2].a, fam[q2].b, fam[q2].c, fam[q2].e, critHits[q2]);

  {
    static char done[MAXRES];
    memset(done, 0, sizeof(done));
    long left = 0;
    for (long u = 0; u < critN; u++) if (critMaskPt[u]) left++; else done[u] = 1;
    printf("\n  greedy cover of the branch by walks: %ld of %ld basepoints are served by "
           "some walk\n", left, critN);
    int picks = 0;
    while (left > 0 && picks < famN) {
      int bestq = -1; long bestc = 0;
      for (int q2 = 0; q2 < famN; q2++) {
        long cnt = 0;
        for (long u = 0; u < critN; u++)
          if (!done[u] && (critMaskPt[u] & (1ULL << q2))) cnt++;
        if (cnt > bestc) { bestc = cnt; bestq = q2; }
      }
      if (bestq < 0) break;
      for (long u = 0; u < critN; u++)
        if (!done[u] && (critMaskPt[u] & (1ULL << bestq))) { done[u] = 1; left--; }
      picks++;
      printf("    pick %d: %s P=%d K=%d M=%d (%d -> %d -> %d -> %d -> %d) covers %ld, "
             "left %ld\n", picks, fam[bestq].refl ? "reflected" : "direct",
             fam[bestq].P, fam[bestq].K, fam[bestq].M, fam[bestq].st, fam[bestq].a,
             fam[bestq].b, fam[bestq].c, fam[bestq].e, bestc, left);
    }
    printf("    walks needed: %d\n", picks);
  }

  printf("\n  the landmark sentence read literally (the existentials searched) against the\n"
         "  greedy reading of the chains: %ld samples, %ld disagreements\n",
         bruteSamples, bruteBad);

  reportNoCrit();

  printf("\n---- batch 60: the walks serving an arm that fails a clause of the best walk ----\n");
  printf("  floor-failing arms (the arm rises to L+8 without the landmark chain):\n");
  for (int q2 = 0; q2 < famN; q2++)
    if (altFloorHits[q2])
      printf("    %s P=%d K=%d M=%d : %d -> %d -> %d -> %d -> %d  serves %ld\n",
             fam[q2].refl ? "reflected" : "direct  ", fam[q2].P, fam[q2].K, fam[q2].M,
             fam[q2].st, fam[q2].a, fam[q2].b, fam[q2].c, fam[q2].e, altFloorHits[q2]);
  greedyAlt("floor", altFloorMask, altFloorN);
  printf("  deep-failing arms (the arm rises to L+9 without the landmark chain):\n");
  for (int q2 = 0; q2 < famN; q2++)
    if (altDeepHits[q2])
      printf("    %s P=%d K=%d M=%d : %d -> %d -> %d -> %d -> %d  serves %ld\n",
             fam[q2].refl ? "reflected" : "direct  ", fam[q2].P, fam[q2].K, fam[q2].M,
             fam[q2].st, fam[q2].a, fam[q2].b, fam[q2].c, fam[q2].e, altDeepHits[q2]);
  greedyAlt("deep", altDeepMask, altDeepN);
  printf("\n---- batch 60: the crossings of the three walks ----\n");
  printf("  crossing basepoints recorded: %ld; the walks serving both arms there:\n", triCrossN);
  for (int q2 = 0; q2 < famN; q2++)
    if (triCrossHits[q2])
      printf("    %s P=%d K=%d M=%d : %d -> %d -> %d -> %d -> %d  serves both arms at %ld\n",
             fam[q2].refl ? "reflected" : "direct  ", fam[q2].P, fam[q2].K, fam[q2].M,
             fam[q2].st, fam[q2].a, fam[q2].b, fam[q2].c, fam[q2].e, triCrossHits[q2]);
  {
    long none = 0;
    for (long t = 0; t < triCrossN; t++) if (triCrossMask[t] == 0) none++;
    printf("  crossings served by no walk of the family at all: %ld\n", none);
  }
  reportAltFail(0, "floor");
  reportAltFail(1, "deep");

  printf("\n---- the definition audit ----\n");
  printf("  every predicate below is evaluated by its own definition, none by a proxy:\n");
  printf("    IsCrookedIvF (le, width, adj, crooked with interval triggers); IsLip via the\n"
         "    adjacency clause; HighAt (L+1) (L+8); LowAt (L+1) (L+8); Leg3Valley; Leg3Ceil;\n"
         "    Valley5; TopW5; FoldsOnto (the dynamic program of HPC/Fold/Decide.lean) for the\n"
         "    Lambda-walk, the V-walk, w3, w4, w5, their reflections and every walk of the\n"
         "    four-leg family; ValleyResidual; CeilPeakResidual; CeilHighResidual.\n");
  printf("    Leg4Land, the landmark sentence of HPC/Fold/Leg4Land.lean, clause by clause,\n"
         "    with the index bounds the walk's own positions dictate; Leg4Crit, the criterion\n"
         "    of the engine, as the three announcements of foldsOnto_leg4W.\n");
  printf("  the strengthened criteria (witness at index 12, Valley5 at index 5, TopW5 at\n"
         "  index 12) are the definitions with the index bound raised to the value the\n"
         "  timing law of Theorem 7 gives; they are reported as such.\n");
  printf("  the criteria of the four-leg engine are the three announcements of\n"
         "  foldsOnto_leg4W together with its base condition, written out at L = 0,\n"
         "  H = 9 and the parameter set (P, K, M); the interval form is the same with\n"
         "  every high landmark read on sig and every low landmark on rho of the link,\n"
         "  the triggers left on the point sequence, and is reported as such.\n");
  free(p.v); free(q.v);
  return 0;
}
