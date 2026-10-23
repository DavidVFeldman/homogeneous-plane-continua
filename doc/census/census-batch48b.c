/* Census for batch 48 (b) -- commission 48, question 2.3: the general shape of
 * the criterion.
 *
 * THE SENTENCE UNDER TEST.  Both criteria of the development -- the Lambda
 * criterion of HPC/Fold/Profile.lean and the three-leg criterion `Leg3Valley`,
 * `Leg3Ceil` of HPC/Fold/Leg3Profile.lean -- read: at each landmark of the walk,
 * the arm has stood within one of the landmark's level at a step no earlier than
 * the landmark's position, in order.  Written out for an arbitrary zigzag walk
 * `w` of positions `0 .. len-1`, with landmarks (turning points) at positions
 * p_1 < ... < p_T and levels l_1, ..., l_T:
 *
 *   for every step `d` of the arm, let u(d) be the EARLIEST walk position that
 *   serves the arm's level there (|arm d - w u| <= 1), and let r(d) be the
 *   number of landmarks strictly before u(d).  Then there must be steps
 *   j_1 < ... < j_r <= d with |arm j_s - l_s| <= 1, with
 *   j_s >= j_{s-1} + (p_s - p_{s-1})   (j_0 = 0, p_0 = 0)
 *   and d >= j_r + (u(d) - p_r).
 *
 * The clauses of `Leg3Valley` and `Leg3Ceil` are exactly this sentence for the
 * walk `L+3 -> L+6 -> L+1 -> L+8`, and the Lambda criterion is it for the walk
 * `p -> kappa -> L+1`.
 *
 * WHAT IS TESTED.  Is the sentence SUFFICIENT for `FoldsOnto`, for an arbitrary
 * zigzag walk?  For each walk of a family, over every 1-Lipschitz arm in [0, 9]
 * of length at most `M` starting within one of the walk's first level, and over
 * random longer arms, we ask whether an arm meeting the criterion folds.  Every
 * fold is decided exactly by the dynamic program over `FoldsOnto`; nothing is
 * assumed about the walk.  Failures are printed with the arm that fails.
 *
 * Usage: census-batch48b [maxlen] [random-arms] [maxrandlen] [seed]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXW  96
#define MAXM  256

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

/* the landmarks of a walk: its turning points, in order, with the direction of
 * the turn -- `lmUp` is 1 at a peak and 0 at a valley.  "Within one of the
 * landmark's level" is read one-sidedly, as both criteria of the development
 * read it: at a peak `l` the arm must stand at `l - 1` OR ABOVE, at a valley
 * `l` at `l + 1` or below. */
static int lmPos[8], lmLev[8], lmUp[8], nLm;
static void landmarks(const int *w, int wl) {
  nLm = 0;
  for (int u = 1; u + 1 < wl; u++)
    if ((w[u] > w[u-1] && w[u] > w[u+1]) || (w[u] < w[u-1] && w[u] < w[u+1])) {
      lmPos[nLm] = u; lmLev[nLm] = w[u]; lmUp[nLm] = (w[u] > w[u-1]); nLm++;
    }
}

/* the earliest walk position serving the level v, or -1 */
static int firstServe(const int *w, int wl, int v) {
  for (int u = 0; u < wl; u++) { int d = v - w[u]; if (d <= 1 && d >= -1) return u; }
  return -1;
}

/* THE SENTENCE.  Greedy is exact here: to satisfy the chain of landmarks as
 * early as possible, take at each landmark the earliest admissible step. */
static int criterion(const int *f, int m, const int *w, int wl) {
  for (int d = 0; d < m; d++) {
    int u = firstServe(w, wl, f[d]);
    if (u < 0) return 0;                    /* the level is off the walk entirely */
    int r = 0;
    while (r < nLm && lmPos[r] < u) r++;    /* landmarks strictly before u */
    if (r == 0) continue;
    int j = 0, prevPos = 0, ok = 1;
    for (int s = 0; s < r; s++) {
      int need = j + (lmPos[s] - prevPos);
      int found = -1;
      for (int q = need; q <= d; q++) {
        int ok2 = lmUp[s] ? (f[q] >= lmLev[s] - 1) : (f[q] <= lmLev[s] + 1);
        if (ok2) { found = q; break; }
      }
      if (found < 0) { ok = 0; break; }
      j = found; prevPos = lmPos[s];
    }
    if (!ok) return 0;
    if (d < j + (u - prevPos)) return 0;
  }
  return 1;
}

static int arm[MAXM], w[MAXW], wl;
static long long nArms, nCrit, nCritFold, nBad, nFold, nFoldNoCrit, nLeg3Diff, nLeg3Strict;
static int leg3Mode;

/* `Leg3Valley` and `Leg3Ceil` of HPC/Fold/Leg3Profile.lean, verbatim, used to
 * check that the general sentence specialises to them on the three-leg walk */
static int leg3Crit(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j + 5 <= d && !ok; j++) if (a[j] >= 5) ok = 1;
    if (!ok) return 0;
  }
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

static void leaf(int m) {
  nArms++;
  int fd = folds(arm, m, w, wl);
  if (fd) nFold++;
  int cr = criterion(arm, m, w, wl);
  if (leg3Mode && arm[0] == 4) {
    int lc = leg3Crit(arm, m);
    if (lc && !cr) nLeg3Strict++;
    if (cr && !lc) nLeg3Diff++;
  }
  if (!cr) { if (fd) nFoldNoCrit++; return; }
  nCrit++;
  if (fd) { nCritFold++; return; }
  nBad++;
  if (nBad <= 5) {
    printf("    COUNTEREXAMPLE: arm");
    for (int j = 0; j < m; j++) printf(" %d", arm[j]);
    printf("  meets the criterion and does not fold\n");
  }
}

static void rec(int j, int m) {
  if (j == m) { leaf(m); return; }
  for (int e = -1; e <= 1; e++) {
    int v = arm[j-1] + e;
    if (v < 0 || v > 9) continue;
    arm[j] = v;
    rec(j + 1, m);
  }
}

int main(int argc, char **argv) {
  int maxlen = (argc > 1) ? atoi(argv[1]) : 13;
  long randArms = (argc > 2) ? atol(argv[2]) : 200000;
  int maxrand = (argc > 3) ? atoi(argv[3]) : 60;
  unsigned seed = (argc > 4) ? (unsigned)atoi(argv[4]) : 48u;
  srandom(seed);

  /* the family of zigzag walks: one, two and three turns inside [0, 9] */
  int fam[64][4], nf = 0;
  int starts[3] = {3, 4, 5};
  for (int si = 0; si < 3; si++) {
    int st = starts[si];
    int peaks[3] = {6, 7, 8};
    for (int pi = 0; pi < 3; pi++) {
      fam[nf][0] = st; fam[nf][1] = peaks[pi]; fam[nf][2] = 1; fam[nf][3] = -1; nf++;
      fam[nf][0] = st; fam[nf][1] = peaks[pi]; fam[nf][2] = 1; fam[nf][3] = 8; nf++;
      fam[nf][0] = st; fam[nf][1] = 1; fam[nf][2] = peaks[pi]; fam[nf][3] = -1; nf++;
      fam[nf][0] = st; fam[nf][1] = 1; fam[nf][2] = peaks[pi]; fam[nf][3] = 0; nf++;
      fam[nf][0] = st; fam[nf][1] = 0; fam[nf][2] = peaks[pi]; fam[nf][3] = 2; nf++;
      fam[nf][0] = st; fam[nf][1] = peaks[pi]; fam[nf][2] = 2; fam[nf][3] = 9; nf++;
    }
  }

  printf("census-batch48b: is the landmark sentence sufficient for FoldsOnto?\n");
  printf("walks tested: %d; exhaustive over 1-Lipschitz arms in [0,9] of length <= %d,\n"
         "then %ld random arms of length <= %d per walk (seed %u).\n\n",
         nf, maxlen, randArms, maxrand, seed);

  long long totArms = 0, totCrit = 0, totBad = 0;
  int badWalks = 0;
  for (int q = 0; q < nf; q++) {
    wl = buildWalk(w, fam[q][0], fam[q][1], fam[q][2], fam[q][3]);
    if (wl < 0) continue;
    landmarks(w, wl);
    nArms = nCrit = nCritFold = nBad = nFold = nFoldNoCrit = nLeg3Diff = nLeg3Strict = 0;
    leg3Mode = (fam[q][0] == 3 && fam[q][1] == 6 && fam[q][2] == 1 && fam[q][3] == 8);
    for (int m = 2; m <= maxlen; m++)
      for (int s = -1; s <= 1; s++) {
        int v0 = w[0] + s;
        if (v0 < 0 || v0 > 9) continue;
        arm[0] = v0;
        rec(1, m);
      }
    /* random longer arms */
    for (long it = 0; it < randArms; it++) {
      int m = 14 + (int)(random() % (maxrand - 13));
      int v0 = w[0] + (int)(random() % 3) - 1;
      if (v0 < 0 || v0 > 9) v0 = w[0];
      arm[0] = v0;
      for (int j = 1; j < m; j++) {
        int v;
        do { v = arm[j-1] + (int)(random() % 3) - 1; } while (v < 0 || v > 9);
        arm[j] = v;
      }
      leaf(m);
    }
    printf("walk %2d:", q);
    for (int u = 0; u < wl; u++) printf(" %d", w[u]);
    printf("   (%d landmarks)  arms %lld, folding %lld; meeting the criterion %lld, of which"
           " folding %lld, FAILING %lld; folding without the criterion %lld\n",
           nLm, nArms, nFold, nCrit, nCritFold, nBad, nFoldNoCrit);
    if (leg3Mode)
      printf("           [this is the three-leg walk: arms based at L+4 meeting the general"
             " sentence but not (Leg3Valley and Leg3Ceil): %lld; meeting (Leg3Valley and"
             " Leg3Ceil) but not the general sentence: %lld]\n", nLeg3Diff, nLeg3Strict);
    totArms += nArms; totCrit += nCrit; totBad += nBad;
    if (nBad) badWalks++;
  }
  printf("\ntotal: arms %lld, meeting the criterion %lld, counterexamples %lld"
         " (walks with a counterexample: %d of %d)\n", totArms, totCrit, totBad, badWalks, nf);
  return 0;
}
