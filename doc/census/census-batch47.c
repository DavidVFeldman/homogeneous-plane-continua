/* Census for batch 47 (a) -- is every faithful pair a shaving of a thin one?
 *
 * Ranges over the GENERAL model.  Generator: *exhaustive enumeration* of all
 * pairs (rho, sigma) of a given length n with rho in [0, H] and
 * rho <= sigma <= rho + 1; every candidate is then verified against the
 * definition `IsCrookedIvF` of HPC/Fold/Faithful.lean (le, width, adj, and the
 * crookedness clause read with "near" tolerance one and a link meeting every
 * level between its rho and its sigma).  Generation is never trusted.
 *
 * For each faithful pair it asks the commission's first question:
 *
 *   (1) is the RAISE (sigma, sigma) -- rho lifted to sigma at every non-thin
 *       link -- again a faithful pair?  (necessary for the pair to be a
 *       shaving of a thin sequence: shaving lowers rho and leaves sigma)
 *   (2) is every non-thin link a strict local maximum of sigma?  (the second
 *       half of "is a multi-shaving of the thin sequence sigma")
 *
 * It reports the number of faithful pairs, the fraction of non-thin links, and
 * the first counterexample to (1) and to (2) at each length.
 *
 * Usage: census-batch47 [nmax] [H]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXLEV 32
#define MAXN 64

static int meetTab[MAXLEV][MAXN + 1];

/* Verify IsCrookedIvF (rho, sigma); if `why` is non-null, record the clause. */
static int crookedGen(const int *rho, const int *sig, int n, const char **why) {
  if (why) *why = "ok";
  if (n <= 0 || n > MAXN) { if (why) *why = "size"; return 0; }
  for (int t = 0; t < n; t++) {
    if (rho[t] > sig[t]) { if (why) *why = "le"; return 0; }
    if (sig[t] > rho[t] + 1) { if (why) *why = "width"; return 0; }
  }
  for (int t = 0; t + 1 < n; t++) {
    int mx = sig[t] > sig[t+1] ? sig[t] : sig[t+1];
    int mn = rho[t] < rho[t+1] ? rho[t] : rho[t+1];
    if (mx > mn + 1) { if (why) *why = "adj"; return 0; }
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
        int seen = 0;
        for (int q = 0; q < nh; q++) if (hs[q] == l) seen = 1;
        if (!seen) hs[nh++] = l;
      }
    }
    for (int t = s + 1; t < n; t++) {
      int ks[8], nk = 0;
      for (int e = -1; e <= 1; e++) {
        int u = t + e; if (u < 0 || u >= n) continue;
        for (int l = rho[u]; l <= sig[u]; l++) {
          int seen = 0;
          for (int q = 0; q < nk; q++) if (ks[q] == l) seen = 1;
          if (!seen) ks[nk++] = l;
        }
      }
      for (int a = 0; a < nh; a++) for (int b = 0; b < nk; b++) {
        int h = hs[a], k = ks[b];
        int diff = h - k; if (diff < 0) diff = -diff;
        if (diff < 3) continue;
        int r1, r2;
        if (h < k) { r1 = k - 1; r2 = h + 1; } else { r1 = k + 1; r2 = h - 1; }
        if (r1 < 0 || r1 >= MAXLEV || r2 < 0 || r2 >= MAXLEV) { if (why) *why = "range"; return 0; }
        int p1 = meetTab[r1][s + 1];
        if (p1 >= t) { if (why) *why = "crooked"; return 0; }
        int p2 = meetTab[r2][p1 + 1];
        if (p2 >= t) { if (why) *why = "crooked"; return 0; }
      }
    }
  }
  return 1;
}

static int rho[MAXN], sig[MAXN];
static int N, H;

static long long nFaithful, nNonThinPairs, nLinks, nNonThinLinks;
static long long nRaiseFail, nNotShaving;
static int printedRaise, printedShave;

static void report(void) {
  const char *why;
  if (!crookedGen(rho, sig, N, &why)) return;
  nFaithful++;
  int nonthin = 0;
  for (int t = 0; t < N; t++) if (sig[t] > rho[t]) nonthin++;
  nLinks += N;
  nNonThinLinks += nonthin;
  if (nonthin) nNonThinPairs++;
  /* (1) the raise */
  int raiseOK = crookedGen(sig, sig, N, &why);
  if (!raiseOK) {
    nRaiseFail++;
    if (!printedRaise) {
      printedRaise = 1;
      printf("  RAISE FAILS (%s) at n=%d:\n    rho =", why, N);
      for (int t = 0; t < N; t++) printf(" %d", rho[t]);
      printf("\n    sig =");
      for (int t = 0; t < N; t++) printf(" %d", sig[t]);
      printf("\n");
    }
  }
  /* (2) every non-thin link a strict local maximum of sigma */
  int shaving = raiseOK;
  for (int t = 0; t < N && shaving; t++) {
    if (sig[t] > rho[t]) {
      if (t > 0 && sig[t-1] >= sig[t]) shaving = 0;
      if (t + 1 < N && sig[t+1] >= sig[t]) shaving = 0;
    }
  }
  if (!shaving) {
    nNotShaving++;
    if (!printedShave && raiseOK) {
      printedShave = 1;
      printf("  NOT A SHAVING (raise faithful, non-thin link not a strict peak) at n=%d:\n"
             "    rho =", N);
      for (int t = 0; t < N; t++) printf(" %d", rho[t]);
      printf("\n    sig =");
      for (int t = 0; t < N; t++) printf(" %d", sig[t]);
      printf("\n");
    }
  }
}

/* depth-first over (rho t, sigma t), pruning on le/width/adj */
static void rec(int t) {
  if (t == N) { report(); return; }
  for (int r = 0; r <= H; r++) {
    for (int w = 0; w <= 1; w++) {
      int s = r + w;
      if (t > 0) {
        int mx = sig[t-1] > s ? sig[t-1] : s;
        int mn = rho[t-1] < r ? rho[t-1] : r;
        if (mx > mn + 1) continue;
      }
      rho[t] = r; sig[t] = s;
      rec(t + 1);
    }
  }
}

int main(int argc, char **argv) {
  int nmax = (argc > 1) ? atoi(argv[1]) : 12;
  H = (argc > 2) ? atoi(argv[2]) : 4;
  printf("census-batch47: exhaustive enumeration of the GENERAL model,\n");
  printf("  all pairs (rho, sigma) with rho in [0,%d], rho <= sigma <= rho+1,\n", H);
  printf("  each verified against IsCrookedIvF; raise = (sigma, sigma).\n\n");
  for (N = 1; N <= nmax; N++) {
    nFaithful = nNonThinPairs = nLinks = nNonThinLinks = 0;
    nRaiseFail = nNotShaving = 0;
    printedRaise = printedShave = 0;
    rec(0);
    printf("n=%2d: faithful %lld, of them non-thin %lld; non-thin links %lld/%lld (%.3f); "
           "raise fails %lld; not a shaving %lld\n",
           N, nFaithful, nNonThinPairs, nNonThinLinks, nLinks,
           nLinks ? (double)nNonThinLinks / (double)nLinks : 0.0,
           nRaiseFail, nNotShaving);
    fflush(stdout);
  }
  return 0;
}
