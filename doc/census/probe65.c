/* census-batch61.c -- batch 61.  The crossing at the branch L+5.
 *
 * New in this batch.
 *
 *   A. Question 1.  A *five-walk crossing* is a basepoint of the branch L+5 at
 *      which no one of the five walks of s3_span_nine_mid5_of_leg4FiveCrossL5
 *      (HPC/Fold/LandTri.lean) has its exact criterion -- the landmark sentence
 *      Leg4Land -- on both arms:
 *
 *        w8 : direct    (P,K,M) = (5,8,1)   4 -> 8 -> 1 -> 8 -> 1
 *        w3 : reflected (P,K,M) = (4,6,1)   6 -> 3 -> 8 -> 1 -> 8
 *        wb : reflected (P,K,M) = (4,6,2)   6 -> 3 -> 7 -> 1 -> 8
 *        w72: direct    (P,K,M) = (5,7,2)   4 -> 7 -> 2 -> 8 -> 1
 *        w81: direct    (P,K,M) = (6,8,1)   5 -> 8 -> 1 -> 8 -> 1
 *
 *      Every such crossing of the corpus is stored whole -- both arms and the
 *      faithful pair it came from, duplicates merged -- and then:
 *
 *        (i)  for each crossing, the walks of the four-leg family that serve
 *             both arms, by the exact criterion and by the fold itself;
 *        (ii) for each crossing, the *shortest* walk of any shape (up to six
 *             turns, levels in [0,9]) onto which both arms fold;
 *       (iii) whether one walk serves every crossing at once -- question 2,
 *             "is five the list?".
 *
 *      The shape of each crossing is printed: which of the three walks serves
 *      each arm, where the {w8}-arm first reaches 8, where the other arm
 *      descends, and the first levels of both arms.  Up to three crossings are
 *      shrunk to a minimal faithful window and dumped in full.
 *
 *   B. Everything else is carried over from census-batch60.c unchanged, and its
 *      header follows.
 *
 * census-batch60.c -- batch 60.  The two ascent clauses of the branch's best
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
  /* batch 61: the list grown by w71 = direct (5,7,1), the walk the crossings pick out */
  long b61Cross4, b61Cross6;
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

/* ---- batch 61: the crossings of the list of five, stored whole ------------
 *
 * Each five-walk crossing is kept with both arms and with the faithful pair it
 * was found in, so that the search for a walk serving all of them can be run
 * once the corpus has been swept.  Two crossings with the same pair of arms are
 * the same crossing and are merged. */

#define MAXCROSS 2048

typedef struct {
  int mg, mt, n, i, tG, tT, qG, qT;
  int *g, *t, *pr, *ps;
} Cross;

static Cross crx[MAXCROSS];
static long crxN = 0, crxDup = 0, crxOver = 0;

static int crossSame(const Cross *c, const int *g, int mg, const int *t, int mt) {
  if (c->mg != mg || c->mt != mt) return 0;
  for (int d = 0; d < mg; d++) if (c->g[d] != g[d]) return 0;
  for (int d = 0; d < mt; d++) if (c->t[d] != t[d]) return 0;
  return 1;
}

static void noteCross(int n, int i, const int *g, int mg, const int *t, int mt,
                      int tG, int tT, int qG, int qT) {
  for (long q = 0; q < crxN; q++)
    if (crossSame(&crx[q], g, mg, t, mt)) { crxDup++; return; }
  if (crxN >= MAXCROSS) { crxOver++; return; }
  Cross *c = &crx[crxN++];
  c->mg = mg; c->mt = mt; c->n = n; c->i = i;
  c->tG = tG; c->tT = tT; c->qG = qG; c->qT = qT;
  c->g = (int *)malloc(sizeof(int) * (size_t)mg);
  c->t = (int *)malloc(sizeof(int) * (size_t)mt);
  c->pr = (int *)malloc(sizeof(int) * (size_t)n);
  c->ps = (int *)malloc(sizeof(int) * (size_t)n);
  memcpy(c->g, g, sizeof(int) * (size_t)mg);
  memcpy(c->t, t, sizeof(int) * (size_t)mt);
  memcpy(c->pr, rho, sizeof(int) * (size_t)n);
  memcpy(c->ps, sig, sizeof(int) * (size_t)n);
}
/* ---- batch 62: the crossings of the *three* walks, stored whole ----------
 *
 * Question 1 of batch 62 is about the crossing of the trichotomy: one arm served
 * by w8, the other by wb or w3.  Those are stored here, with both arms and the
 * faithful pair, so that the batch-62 measurements can be made on them. */

static Cross crx3[MAXCROSS];
static long crx3N = 0, crx3Dup = 0, crx3Over = 0;

static void noteCross3(int n, int i, const int *g, int mg, const int *t, int mt,
                       int tG, int tT) {
  for (long q = 0; q < crx3N; q++)
    if (crossSame(&crx3[q], g, mg, t, mt)) { crx3Dup++; return; }
  if (crx3N >= MAXCROSS) { crx3Over++; return; }
  Cross *c = &crx3[crx3N++];
  c->mg = mg; c->mt = mt; c->n = n; c->i = i;
  c->tG = tG; c->tT = tT; c->qG = 0; c->qT = 0;
  c->g = (int *)malloc(sizeof(int) * (size_t)mg);
  c->t = (int *)malloc(sizeof(int) * (size_t)mt);
  c->pr = (int *)malloc(sizeof(int) * (size_t)n);
  c->ps = (int *)malloc(sizeof(int) * (size_t)n);
  memcpy(c->g, g, sizeof(int) * (size_t)mg);
  memcpy(c->t, t, sizeof(int) * (size_t)mt);
  memcpy(c->pr, rho, sizeof(int) * (size_t)n);
  memcpy(c->ps, sig, sizeof(int) * (size_t)n);
}

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


/* ======================= batch 65 : globals ===============================
 *
 * Mid2Floor read as a fact about a single arm of the branch, over every

/* ===================== probe 65 =========================================
 *
 * The basepoint 145 of Bing's chain `bing 0 9`, read link by link: the
 * counterexample to CrossMid2L5 of HPC/Fold/CrossMid2Fail65.lean, and what
 * else holds there.  Then a sweep of the plain chain for every basepoint of
 * the branch whose arms fail Mid2Floor, with the trichotomy tag of each.
 *
 * Every predicate is the definition of the Lean file it names, written out at
 * L = 0 and searched literally; no criterion of the engine is used. */

static int mid2Floor(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] != 2) continue;
    int ok = 0;
    for (int j = 3; j + 4 <= d && !ok; j++) if (f[j] >= 6) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}
static int hasMid2(const int *f, int m) {
  for (int d = 0; d < m; d++) if (f[d] == 2) return 1;
  return 0;
}
static int deep72Clause(const int *f, int m) { (void)f; (void)m; return 0; }
static int touchesZero(const int *f, int m) {
  for (int d = 0; d < m; d++) if (f[d] <= 0) return 1;
  return 0;
}
static int reachesNine(const int *f, int m) {
  for (int d = 0; d < m; d++) if (f[d] >= 9) return 1;
  return 0;
}
static int w8FloorFailLow(const int *f, int m, int lev) { (void)f; (void)m; (void)lev; return 0; }

static int aG[MAXN], aT[MAXN], rG[MAXN], rT[MAXN];

static void tagsAt(const int *v, int n, int i, int *tG, int *tT, int *pmg, int *pmt) {
  int mg = n - i, mt = i + 1;
  for (int d = 0; d < mg; d++) { aG[d] = v[i + d]; rG[d] = 9 - aG[d]; }
  for (int d = 0; d < mt; d++) { aT[d] = v[i - d]; rT[d] = 9 - aT[d]; }
  *tG = 0; *tT = 0; *pmg = mg; *pmt = mt;
  if (landLeg4(rG, mg, 6, 2, 4)) *tG |= 1;
  if (landLeg4(aG, mg, 8, 1, 5)) *tG |= 2;
  if (landLeg4(rG, mg, 6, 1, 4)) *tG |= 4;
  if (landLeg4(rT, mt, 6, 2, 4)) *tT |= 1;
  if (landLeg4(aT, mt, 8, 1, 5)) *tT |= 2;
  if (landLeg4(rT, mt, 6, 1, 4)) *tT |= 4;
}

int main(void) {
  Path p = bpath(0, 9);
  int n = p.n; const int *v = p.v;
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  printf("probe65: bing 0 9, %d links, faithful (thin): %d\n", n, crookedGen(rho, sig, n));
  printf("  the chain attains 0 at link 0 (%d) and 9 at link %d (%d)\n",
         v[0], n - 1, v[n-1]);

  int i = 145;
  int tG, tT, mg, mt;
  tagsAt(v, n, i, &tG, &tT, &mg, &mt);
  printf("\n---- the basepoint 145 ----\n");
  printf("  rho[145] = %d;  arms %d (forward) and %d (backward)\n", v[i], mg, mt);
  printf("  LowAt on the arms: forward %d, backward %d\n", lowAt(aG, mg), lowAt(aT, mt));
  printf("  the backward arm begins:");
  for (int d = 0; d < 20; d++) printf(" %d", aT[d]);
  printf("\n  the forward arm begins:");
  for (int d = 0; d < 20; d++) printf(" %d", aG[d]);
  printf("\n  Mid2Floor: forward %d, backward %d\n", mid2Floor(aG, mg), mid2Floor(aT, mt));
  printf("  the backward arm descends to exactly 2 first at index ");
  for (int d = 0; d < mt; d++) if (aT[d] == 2) { printf("%d\n", d); break; }
  printf("  tags (1 = wb reflected (4,6,2), 2 = w8 direct (5,8,1), 4 = w3 reflected (4,6,1)):"
         "  forward %d, backward %d;  a crossing of the trichotomy: %d\n",
         tG, tT, (tG & tT) == 0);
  printf("  w71 (5,7,1): forward %d, backward %d;  w72 (5,7,2): forward %d, backward %d\n",
         landLeg4(aG, mg, 7, 1, 5), landLeg4(aT, mt, 7, 1, 5),
         landLeg4(aG, mg, 7, 2, 5), landLeg4(aT, mt, 7, 2, 5));
  printf("  the pair folds onto the wb walk 6 -> 3 -> 7 -> 1 -> 8 (both arms, reflected): %d\n",
         landLeg4(rG, mg, 6, 2, 4) && landLeg4(rT, mt, 6, 2, 4));
  printf("  the forward arm touches 0: %d;  reaches 9: %d;  the backward arm touches 0: %d\n",
         touchesZero(aG, mg), reachesNine(aG, mg), touchesZero(aT, mt));

  printf("\n---- every basepoint of the branch in the plain chain ----\n");
  long base = 0, fail = 0, failCross = 0, early = 0;
  for (int q = 0; q < n; q++) {
    if (v[q] != 5) continue;
    int g, t, m1, m2;
    tagsAt(v, n, q, &g, &t, &m1, &m2);
    if (!(lowAt(aG, m1) && lowAt(aT, m2))) continue;
    base++;
    int fG = !mid2Floor(aG, m1), fT = !mid2Floor(aT, m2);
    if (fG || fT) {
      fail++;
      if (!(g & t)) failCross++;
      int e = 0;
      for (int d = 0; d <= 6 && d < m1; d++) if (aG[d] <= 2) e = 1;
      for (int d = 0; d <= 6 && d < m2; d++) if (aT[d] <= 2) e = 1;
      if (e) early++;
      if (fail <= 8)
        printf("  basepoint %4d: Mid2Floor fails on the %s arm;  tags %d and %d;  "
               "crossing %d;  early %d\n", q, fG ? "forward" : "backward", g, t,
               (g & t) == 0, e);
    }
  }
  printf("  basepoints of the branch: %ld;  with an arm failing Mid2Floor: %ld;  of those,\n"
         "  crossings of the trichotomy: %ld;  with a descent to 2 or below within six arm\n"
         "  indices: %ld\n", base, fail, failCross, early);
  free(p.v);
  return 0;
}
