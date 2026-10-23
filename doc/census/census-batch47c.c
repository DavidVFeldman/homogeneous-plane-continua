/* Census for batch 47 (c) -- what does the three-leg walk really ask?
 *
 * WHAT THIS RANGES OVER.  Not pairs but arms: every 1-Lipschitz sequence in
 * [0, 9] of a given length starting at 4, enumerated exhaustively.  (No
 * crookedness: `foldsOnto_leg3_deep` of HPC/Fold/Leg3Deep.lean uses none, so a
 * sufficient criterion for the fold is a statement about Lipschitz arms alone.
 * The general model enters only when the criterion is to be verified on a pair,
 * which is census-batch47b.c.)
 *
 * The walk is `leg3Walk L (L+9) (L+6) (L+4)`, that is
 *
 *    3 4 5 6 5 4 3 2 1 2 3 4 5 6 7 8   (levels above L)
 *
 * the walk `L+3 -> L+6 -> L+1 -> L+8` of the batch-44 engine.  The engine folds
 * an arm onto it as soon as
 *
 *   valley:  every descent to L+1 is preceded by a time at L+6, or by a time at
 *            L+1 or below followed by one at L+5 or above;
 *   ceiling: every ascent to L+8 is preceded by a time at L; or by a time at
 *            L+7 or above followed by one at L+2 or below; or by three times,
 *            in order, at L+1 or below, at L+6 or above, at L+2 or below.
 *
 * Both are refuted as *necessary* conditions by batch 46.  This census measures
 * the gap: it compares the exact fold (the dynamic program over `FoldsOnto`)
 * with the engine's criterion and with the weakened criterion in which each
 * demand for a time at the peak level L+6 is lowered to L+5 -- the level the
 * crookedness clause of the general model actually delivers.
 *
 * Usage: census-batch47c [maxlen]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXM 24
#define MAXW 32

static int walk[16] = {3,4,5,6,5,4,3,2,1,2,3,4,5,6,7,8};
static int wl = 16;

static int f[MAXM];
static int M;

static int folds(const int *a, int m) {
  char cur[MAXW], nxt[MAXW];
  for (int u = 0; u < wl; u++) cur[u] = 0;
  if (a[0] - walk[0] > 1 || walk[0] - a[0] > 1) return 0;
  cur[0] = 1;
  for (int j = 1; j < m; j++) {
    int any = 0;
    for (int u = 0; u < wl; u++) nxt[u] = 0;
    for (int u = 0; u < wl; u++) {
      if (!cur[u]) continue;
      for (int e = -1; e <= 1; e++) {
        int u2 = u + e;
        if (u2 < 0 || u2 >= wl) continue;
        int d = a[j] - walk[u2];
        if (d <= 1 && d >= -1) { nxt[u2] = 1; any = 1; }
      }
    }
    if (!any) return 0;
    memcpy(cur, nxt, sizeof(char) * wl);
  }
  return 1;
}

/* the engine's criterion, with the peak demand at level `K` (6 = as stated,
 * 5 = weakened by one level) */
static int criterion(const int *a, int m, int K) {
  /* valley */
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int k = 0; k < d && !ok; k++) if (a[k] >= K) ok = 1;
    if (!ok) {
      int low = -1;
      for (int k = 0; k < d && !ok; k++) {
        if (low >= 0 && a[k] >= K - 1) ok = 1;
        if (a[k] <= 1) low = k;
      }
    }
    if (!ok) return 0;
  }
  /* ceiling */
  for (int d = 0; d < m; d++) {
    if (a[d] < 8) continue;
    int ok = 0;
    for (int k = 0; k < d && !ok; k++) if (a[k] <= 0) ok = 1;
    if (!ok) { /* K+1 then <= 2 */
      int hi = -1;
      for (int k = 0; k < d && !ok; k++) {
        if (hi >= 0 && a[k] <= 2) ok = 1;
        if (a[k] >= K + 1) hi = k;
      }
    }
    if (!ok) { /* <=1 then >= K then <= 2 */
      int st = 0;
      for (int k = 0; k < d && !ok; k++) {
        if (st == 0 && a[k] <= 1) st = 1;
        else if (st == 1 && a[k] >= K) st = 2;
        else if (st == 2 && a[k] <= 2) ok = 1;
      }
    }
    if (!ok) return 0;
  }
  return 1;
}

/* THE PROFILE CRITERION.  The engine's two announcements with every demand for a
 * time at the peak level L+6 lowered to L+5 -- the level the general crookedness
 * clause delivers -- and with the index clauses the walk forces: the walk stands
 * at L+6 at its position 3, at L+1 at its position 8, and at L+7 at its
 * position 14, and it advances at most one position per step.
 *
 *   valley:  every descent to L+1 at a step d is preceded by a time at L+5 or
 *            above at a step j with 3 <= j and j + 5 <= d;
 *   ceiling: every ascent to L+8 at a step d is preceded by such a j and, after
 *            it, by a time at L+2 or below at a step k with j + 5 <= k and
 *            k + 6 <= d.
 *
 * Exhaustively over every 1-Lipschitz arm in [0,9] of length at most sixteen
 * starting at L+4, this criterion is SUFFICIENT for the fold (no arm satisfies
 * it and fails to fold) and is nearly necessary (about 0.8% of the folding arms
 * fail it at length sixteen). */
static int criterion5idx(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j < d && !ok; j++) if (a[j] >= 5 && j + 5 <= d) ok = 1;
    if (!ok) return 0;
  }
  for (int d = 0; d < m; d++) {
    if (a[d] < 8) continue;
    int ok = 0;
    for (int j = 3; j < d && !ok; j++) {
      if (a[j] < 5) continue;
      for (int k = j + 5; k < d && !ok; k++) if (a[k] <= 2 && k + 6 <= d) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

static long long nArms, nFold, nCrit6, nCrit5, nCrit5NotFold, nFoldNotCrit5, nFoldNotCrit6;
static long long nIdx, nIdxNotFold, nFoldNotIdx;
static int shown5, shown6, shownIdx;

static void report(void) {
  nArms++;
  int fo = folds(f, M);
  int c6 = criterion(f, M, 6);
  int c5 = criterion(f, M, 5);
  if (fo) nFold++;
  if (c6) nCrit6++;
  if (c5) nCrit5++;
  if (c5 && !fo) {
    nCrit5NotFold++;
    if (shown5 < 5) {
      shown5++;
      printf("  WEAK CRITERION BUT NO FOLD (m=%d):", M);
      for (int j = 0; j < M; j++) printf(" %d", f[j]);
      printf("\n");
    }
  }
  if (fo && !c5) nFoldNotCrit5++;
  if (fo && !c6) nFoldNotCrit6++;
  int ci = criterion5idx(f, M);
  if (ci) nIdx++;
  if (ci && !fo) {
    nIdxNotFold++;
    if (shownIdx < 5) {
      shownIdx++;
      printf("  PROFILE CRITERION BUT NO FOLD (m=%d):", M);
      for (int j = 0; j < M; j++) printf(" %d", f[j]);
      printf("\n");
    }
  }
  if (fo && !ci) nFoldNotIdx++;
}

static void rec(int j) {
  if (j == M) { report(); return; }
  for (int e = -1; e <= 1; e++) {
    int v = f[j-1] + e;
    if (v < 0 || v > 9) continue;
    f[j] = v;
    rec(j + 1);
  }
}

int main(int argc, char **argv) {
  int maxlen = (argc > 1) ? atoi(argv[1]) : 14;
  printf("census-batch47c: exhaustive over 1-Lipschitz arms in [0,9] starting at 4;\n");
  printf("  fold onto L+3 -> L+6 -> L+1 -> L+8 decided by the dynamic program over FoldsOnto.\n");
  printf("  crit6 = the engine's criterion; crit5 = the same with every demand for a time at\n");
  printf("  the peak L+6 lowered to L+5.\n\n");
  for (M = 1; M <= maxlen; M++) {
    nArms = nFold = nCrit6 = nCrit5 = nCrit5NotFold = nFoldNotCrit5 = nFoldNotCrit6 = 0;
    nIdx = nIdxNotFold = nFoldNotIdx = 0;
    shown5 = shown6 = shownIdx = 0;
    f[0] = 4;
    rec(1);
    printf("m=%2d: arms %lld; fold %lld; crit6 %lld; crit5 %lld; "
           "crit5 but no fold %lld; fold but not crit5 %lld; fold but not crit6 %lld\n",
           M, nArms, nFold, nCrit6, nCrit5, nCrit5NotFold, nFoldNotCrit5, nFoldNotCrit6);
    printf("      profile %lld; profile but no fold %lld; fold but not profile %lld\n",
           nIdx, nIdxNotFold, nFoldNotIdx);
    fflush(stdout);
  }
  return 0;
}
