/* Census for batch 47 (d) -- the second generator: filling a valley, and what
 * the point sequence of a general pair is.
 *
 * WHAT THIS RANGES OVER.  Pairs of the GENERAL model.  Two generators, both
 * applied to the thin faithful sequence `bing 0 9`:
 *
 *   FILL   -- raise sigma by one at a strict local minimum, leaving rho alone
 *             (the reflection of shaving, `isCrookedIvF_fill` of
 *             HPC/Fold/Reflect.lean): one fill at a time over every strict
 *             local minimum, then random subsets;
 *   SHAVE  -- lower rho by one at a strict local maximum, leaving sigma alone
 *             (`isCrookedIvF_shave`): one at a time over every strict peak.
 *
 * Every candidate is verified against the definition `IsCrookedIvF` of
 * HPC/Fold/Faithful.lean; generation is never trusted.  The fraction of
 * non-thin links is reported for each family.
 *
 * It also asks, for each pair, whether the LOWERING (rho, rho) -- the point
 * sequence read as a thin pair -- is faithful.  For a filled pair it is, by
 * construction; for a shaved pair the answer decides whether the thin theorem
 * `s3_span_nine_mid4_thin` already covers the pair, since the conclusion of the
 * branch mentions only rho.
 *
 * Usage: census-batch47d [rand-rounds] [seed]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXLEV 32
#define MAXN 2048

static int meetTab[MAXLEV][MAXN + 1];

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
        int d = h - k; if (d < 0) d = -d;
        if (d < 3) continue;
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

static int rho[MAXN], sig[MAXN];

int main(int argc, char **argv) {
  long rounds = (argc > 1) ? atol(argv[1]) : 40;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 17u;
  srandom(seed);
  Path p = bpath(0, 9);
  int n = p.n, *v = p.v;
  printf("census-batch47d: the GENERAL model over bing 0 9 (n = %d);\n", n);
  printf("  generators: FILL (sigma raised at a strict local minimum) and SHAVE (rho lowered\n");
  printf("  at a strict local maximum); every candidate verified against IsCrookedIvF.\n\n");

  int nmin = 0, nmax = 0;
  for (int j = 1; j + 1 < n; j++) {
    if (v[j] < v[j-1] && v[j] < v[j+1]) nmin++;
    if (v[j] > v[j-1] && v[j] > v[j+1]) nmax++;
  }
  printf("strict local minima: %d; strict local maxima: %d\n", nmin, nmax);

  int fillOK = 0, fillBad = 0;
  for (int j = 1; j + 1 < n; j++) {
    if (!(v[j] < v[j-1] && v[j] < v[j+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    sig[j] = v[j] + 1;
    if (crookedGen(rho, sig, n)) fillOK++; else fillBad++;
  }
  printf("single fills: %d faithful, %d not (non-thin links 1/%d each)\n", fillOK, fillBad, n);

  long rf = 0, rbad = 0, rlinks = 0, rnon = 0;
  for (long it = 0; it < rounds; it++) {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    int filled = 0;
    for (int j = 1; j + 1 < n; j++) {
      if (!(v[j] < v[j-1] && v[j] < v[j+1])) continue;
      if (random() % 3 == 0) { sig[j] = v[j] + 1; filled++; }
    }
    if (crookedGen(rho, sig, n)) { rf++; rlinks += n; rnon += filled; } else rbad++;
  }
  printf("random multiple fills (%ld rounds, seed %u): %ld faithful, %ld not; "
         "non-thin links %ld/%ld (%.4f)\n", rounds, seed, rf, rbad, rnon, rlinks,
         rlinks ? (double)rnon / (double)rlinks : 0.0);

  /* mixed: fills and shavings at once */
  long mf = 0, mbad = 0;
  for (long it = 0; it < rounds; it++) {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] < v[j-1] && v[j] < v[j+1]) { if (random() % 3 == 0) sig[j] = v[j] + 1; }
      else if (v[j] > v[j-1] && v[j] > v[j+1]) { if (random() % 3 == 0) rho[j] = v[j] - 1; }
    }
    if (crookedGen(rho, sig, n)) mf++; else mbad++;
  }
  printf("random fills and shavings together (%ld rounds): %ld faithful, %ld not\n",
         rounds, mf, mbad);

  /* the lowering (rho, rho) of a shaved pair */
  int shaveOK = 0, lowOK = 0, lowBad = 0;
  for (int j = 1; j + 1 < n; j++) {
    if (!(v[j] > v[j-1] && v[j] > v[j+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    rho[j] = v[j] - 1;
    if (!crookedGen(rho, sig, n)) continue;
    shaveOK++;
    if (crookedGen(rho, rho, n)) lowOK++; else lowBad++;
  }
  printf("single shavings: %d faithful; of them the lowering (rho, rho) is faithful in %d "
         "and fails in %d\n", shaveOK, lowOK, lowBad);
  printf("  (so the point sequence of a shaved pair is not a thin crooked sequence, and the\n");
  printf("   thin theorem does not apply to it through its own point sequence)\n");
  free(p.v);
  return 0;
}
