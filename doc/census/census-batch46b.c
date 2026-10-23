/* Census for batch 46 (b) -- which contractions of `bing 0 9` are faithful?
 *
 * Diagnostic companion of census-batch46.c.  It asks the prior question: does
 * the general model admit a pair with sigma != rho at all, at span nine?  It
 * tries every single merge of two consecutive links of Bing's 986-link chain
 * `bing 0 9` -- rho the least of the two levels, sigma the greatest -- and
 * verifies each candidate against the definition `IsCrookedIvF`, exactly as in
 * HPC/Fold/Faithful.lean (le, width, adj, and the crookedness clause with
 * "near" tolerance one, a link meeting every level between rho and sigma).
 * It then hill-climbs: repeatedly adds a further merge that keeps the pair
 * faithful, and reports how wide the resulting pairs get.
 *
 * Usage: census-batch46b [rounds] [seed]
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

#define MAXLEV 32
#define MAXN   2048

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
static char merged[MAXN];      /* merged[j] = 1 : links j, j+1 of the chain are one block */

/* build (rho, sig) from the merge marks; returns the number of blocks */
static int build(const int *v, int n, int *m_out) {
  int m = 0;
  for (int j = 0; j < n; ) {
    if (merged[j]) {
      rho[m] = v[j] < v[j+1] ? v[j] : v[j+1];
      sig[m] = v[j] > v[j+1] ? v[j] : v[j+1];
      j += 2;
    } else { rho[m] = v[j]; sig[m] = v[j]; j += 1; }
    m++;
  }
  *m_out = m;
  return m;
}

int main(int argc, char **argv) {
  long rounds = (argc > 1) ? atol(argv[1]) : 4000;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 7u;
  srandom(seed);

  Path p = bpath(0, 9);
  int n = p.n, *v = p.v;
  int m;
  memset(merged, 0, sizeof(merged));
  build(v, n, &m);
  const char *why;
  printf("bing 0 9: n = %d; thin pair verifies: %d\n", n, crookedGen(rho, sig, m, &why));

  /* 1. every single merge, one at a time */
  long single_ok = 0;
  int first_ok = -1;
  long why_adj = 0, why_cr = 0;
  for (int j = 0; j + 1 < n; j++) {
    memset(merged, 0, sizeof(merged));
    merged[j] = 1;
    build(v, n, &m);
    int r = crookedGen(rho, sig, m, &why);
    if (r) { single_ok++; if (first_ok < 0) first_ok = j; }
    else if (!strcmp(why, "adj")) why_adj++;
    else if (!strcmp(why, "crooked")) why_cr++;
  }
  printf("single merges: %ld of %d keep the pair faithful", single_ok, n - 1);
  printf("  (failures: adj %ld, crookedness %ld)\n", why_adj, why_cr);
  if (first_ok >= 0) printf("  first such merge: links %d, %d at levels %d, %d\n",
                            first_ok, first_ok + 1, v[first_ok], v[first_ok + 1]);

  /* 2. hill-climb: add merges greedily while the pair stays faithful */
  if (single_ok > 0) {
    memset(merged, 0, sizeof(merged));
    long added = 0;
    for (long r = 0; r < rounds; r++) {
      int j = (int)(random() % (n - 1));
      if (merged[j]) continue;
      if (j > 0 && merged[j-1]) continue;
      if (j + 1 < n - 1 && merged[j+1]) continue;
      merged[j] = 1;
      build(v, n, &m);
      if (crookedGen(rho, sig, m, &why)) added++;
      else merged[j] = 0;
    }
    build(v, n, &m);
    int wide = 0, lo = 99, hi = -99;
    for (int t = 0; t < m; t++) {
      if (sig[t] > rho[t]) wide++;
      if (rho[t] < lo) lo = rho[t];
      if (rho[t] > hi) hi = rho[t];
    }
    printf("hill-climb: %ld merges accepted; %d links, %d wide; rho band [%d, %d]\n",
           added, m, wide, lo, hi);
    printf("faithful: %d\n", crookedGen(rho, sig, m, &why));
    FILE *f = fopen("/tmp/pair46.txt", "w");
    if (f) {
      fprintf(f, "%d\n", m);
      for (int t = 0; t < m; t++) fprintf(f, "%d %d\n", rho[t], sig[t]);
      fclose(f);
      printf("pair written to /tmp/pair46.txt\n");
    }
  }
  free(p.v);
  return 0;
}
