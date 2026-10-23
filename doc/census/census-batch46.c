/* Census for batch 46 -- pairs of the GENERAL model, sigma != rho.
 *
 * WHAT THIS RANGES OVER.  Faithful crooked *pairs* (rho, sigma) with sigma
 * strictly above rho somewhere, obtained by CONTRACTING Bing's 986-link chain
 * `bing 0 9`: a partition of its index set into consecutive blocks of one or
 * two links, with rho[t] the least level of the block and sigma[t] the
 * greatest.  Nothing is assumed about the result: every generated pair is
 * verified against the definition `IsCrookedIvF` (le, width, adj and the
 * crookedness clause, the clause read exactly as in HPC/Fold/Faithful.lean,
 * with "near" tolerance one and levels met by a link being rho and sigma).
 * Contraction is only a source of candidates; the verifier decides.
 *
 * WHAT IS CHECKED.  For each verified pair of span nine with both ends
 * attained, at every basepoint i with rho[i] = L+4 whose two arms (of rho) are
 * HighAt (L+1) (L+8) -- the open branch of span nine -- we decide the two
 * canonical folds exactly by the dynamic program over `FoldsOnto`, and, when
 * neither canonical walk folds both arms, we check
 *    - the ceiling announcement CeilAnn   (the work item `unserved_ceiling`),
 *    - the valley announcement            (the work item `unserved_valley`),
 * both read on the rho-arms, exactly as the Lean statements read them, and we
 * search for a walk of at most three legs folding both arms.
 *
 * Usage: census-batch46 [trials] [seed]
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

/* meetTab[l][j] = least index j' >= j whose link meets level l (n if none) */
static int meetTab[MAXLEV][MAXN + 1];

/* Verify IsCrookedIvF (rho, sigma) exactly.  Levels are assumed in [0, MAXLEV). */
static int crookedGen(const int *rho, const int *sig, int n) {
  if (n <= 0 || n > MAXN) return 0;
  for (int t = 0; t < n; t++) {
    if (rho[t] > sig[t]) return 0;                 /* le */
    if (sig[t] > rho[t] + 1) return 0;             /* width */
    if (rho[t] < 0 || sig[t] >= MAXLEV) return 0;
  }
  for (int t = 0; t + 1 < n; t++) {                /* adj */
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
        if (r1 < 0 || r1 >= MAXLEV || r2 < 0 || r2 >= MAXLEV) return 0;
        int p1 = meetTab[r1][s + 1];
        if (p1 >= t) return 0;
        int p2 = meetTab[r2][p1 + 1];
        if (p2 >= t) return 0;
      }
    }
  }
  return 1;
}

#define MAXW 96

static int folds(const int *f, int m, const int *w, int wl) {
  static char cur[MAXW], nxt[MAXW];
  if (wl <= 0) return 0;
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

static int highAt1(const int *f, int m) {          /* HighAt f (L+1) (L+8) */
  int sawLe2 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !sawLe2) return 0;
    if (f[d] <= 2) sawLe2 = 1;
  }
  return 1;
}
static int ceilAnn(const int *f, int m) {
  int sawLe0 = 0, sawGe7 = 0, b2 = 0, sawLe1 = 0, mid = 0, b3 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !(sawLe0 || b2 || b3)) return 0;
    if (f[d] <= 0) sawLe0 = 1;
    if (sawGe7 && f[d] <= 2) b2 = 1;
    if (mid && f[d] <= 2) b3 = 1;
    if (sawLe1 && f[d] >= 6) mid = 1;
    if (f[d] >= 7) sawGe7 = 1;
    if (f[d] <= 1) sawLe1 = 1;
  }
  return 1;
}
static int valleyAnn(const int *f, int m) {
  int sawGe6 = 0, sawLe1 = 0, pat = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= 1 && !(sawGe6 || pat)) return 0;
    if (sawLe1 && f[d] >= 5) pat = 1;
    if (f[d] >= 6) sawGe6 = 1;
    if (f[d] <= 1) sawLe1 = 1;
  }
  return 1;
}

static const int wLam[13] = {3,4,5,6,7,8,7,6,5,4,3,2,1};
static const int wVee[12] = {5,4,3,2,1,2,3,4,5,6,7,8};

/* build the walk start -> a -> b -> c (legs; -1 for "stop") */
static int buildWalk(int *w, int start, int a, int b, int c) {
  int len = 0, cur = start;
  w[len++] = cur;
  int tgt[3] = {a, b, c};
  for (int q = 0; q < 3; q++) {
    if (tgt[q] < 0) break;
    int s = tgt[q] > cur ? 1 : -1;
    if (tgt[q] == cur) return -1;
    while (cur != tgt[q]) { cur += s; if (len >= MAXW) return -1; w[len++] = cur; }
  }
  return len;
}

static int rho[MAXN], sig[MAXN];
static int armG[MAXN], armT[MAXN];

/* search a walk of at most three legs folding both arms; returns 1 and fills out */
static int searchWalk(const int *g, int mg, const int *t, int mt, int *out, int *outlen) {
  int w[MAXW];
  for (int start = 3; start <= 5; start++)
    for (int a = 0; a <= 9; a++)
      for (int b = -1; b <= 9; b++)
        for (int c = -1; c <= 9; c++) {
          if (b < 0 && c >= 0) continue;
          int wl = buildWalk(w, start, a, b, c);
          if (wl < 0) continue;
          if (folds(g, mg, w, wl) && folds(t, mt, w, wl)) {
            memcpy(out, w, sizeof(int) * wl); *outlen = wl; return 1;
          }
        }
  return 0;
}

int main(int argc, char **argv) {
  long trials = (argc > 1) ? atol(argv[1]) : 200;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 12345u;
  srandom(seed);

  Path p = bpath(0, 9);
  int n = p.n, *v = p.v;
  printf("bing 0 9: n = %d\n", n);
  /* self-test: the thin pair (v, v) must verify; a monotone run must not */
  for (int j = 0; j < n; j++) { rho[j] = v[j]; sig[j] = v[j]; }
  printf("self-test  thin bing 0 9 verifies: %d (expect 1)\n", crookedGen(rho, sig, n));
  { int mono[6] = {0,1,2,3,4,5};
    printf("self-test  monotone run verifies: %d (expect 0)\n", crookedGen(mono, mono, 6)); }

  long ok = 0, nonthin = 0, span9 = 0, branch = 0, unserved = 0;
  long ceilFail = 0, valFail = 0, noWalk3 = 0;
  int shownCe = 0, shownNo = 0, shownPair = 0;

  for (long trial = 0; trial < trials; trial++) {
    /* random contraction: blocks of one or two consecutive links */
    int m = 0, j = 0, pmerge = 1 + (int)(random() % 40); /* percent */
    while (j < n) {
      if (j + 1 < n && (random() % 100) < (unsigned)pmerge) {
        rho[m] = v[j] < v[j+1] ? v[j] : v[j+1];
        sig[m] = v[j] > v[j+1] ? v[j] : v[j+1];
        j += 2;
      } else { rho[m] = v[j]; sig[m] = v[j]; j += 1; }
      m++;
    }
    int thin = 1;
    for (int t = 0; t < m; t++) if (sig[t] != rho[t]) thin = 0;
    if (!crookedGen(rho, sig, m)) continue;
    ok++;
    if (!thin) nonthin++;
    int lo = 99, hi = -99, atL = 0, atH = 0;
    for (int t = 0; t < m; t++) { if (rho[t] < lo) lo = rho[t]; if (rho[t] > hi) hi = rho[t]; }
    for (int t = 0; t < m; t++) { if (rho[t] == 0) atL = 1; if (rho[t] == 9) atH = 1; }
    if (!(lo == 0 && hi == 9 && atL && atH)) continue;
    span9++;
    if (!thin && shownPair < 3) {
      shownPair++;
      int wide = 0;
      for (int t = 0; t < m; t++) if (sig[t] > rho[t]) wide++;
      printf("  verified NON-THIN pair: %d links, %d of them wide (sigma = rho + 1)\n", m, wide);
    }
    for (int i = 0; i < m; i++) {
      if (rho[i] != 4) continue;
      int mg = m - i, mt = i + 1;
      for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
      for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
      if (!highAt1(armG, mg) || !highAt1(armT, mt)) continue;
      branch++;
      int fLamG = folds(armG, mg, wLam, 13), fLamT = folds(armT, mt, wLam, 13);
      int fVeeG = folds(armG, mg, wVee, 12), fVeeT = folds(armT, mt, wVee, 12);
      if ((fLamG && fLamT) || (fVeeG && fVeeT)) continue;
      unserved++;
      int cA = ceilAnn(armG, mg) && ceilAnn(armT, mt);
      int vA = valleyAnn(armG, mg) && valleyAnn(armT, mt);
      if (!cA) ceilFail++;
      if (!vA) valFail++;
      if ((!cA || !vA) && shownCe < 4) {
        shownCe++;
        printf("\n  *** work item FAILS on a verified pair: trial %ld, basepoint %d of %d links\n",
               trial, i, m);
        printf("      thin: %d; ceiling announcement: %d; valley announcement: %d\n",
               thin, cA, vA);
        printf("      folds: Lambda (G,T) = (%d,%d); V (G,T) = (%d,%d)\n",
               fLamG, fLamT, fVeeG, fVeeT);
      }
      int w[MAXW], wl = 0;
      if (!searchWalk(armG, mg, armT, mt, w, &wl)) {
        noWalk3++;
        if (shownNo < 3) {
          shownNo++;
          printf("\n  *** NO WALK OF AT MOST THREE LEGS at trial %ld, basepoint %d of %d links"
                 " (thin %d)\n", trial, i, m, thin);
        }
      }
    }
  }

  printf("\ntrials: %ld\n", trials);
  printf("  contractions verifying IsCrookedIvF: %ld (non-thin: %ld)\n", ok, nonthin);
  printf("  of those, span nine with both ends attained: %ld\n", span9);
  printf("  basepoints of the open branch: %ld\n", branch);
  printf("    folding onto neither canonical walk: %ld\n", unserved);
  printf("      failing the ceiling announcement (unserved_ceiling): %ld\n", ceilFail);
  printf("      failing the valley announcement  (unserved_valley):  %ld\n", valFail);
  printf("      served by no walk of at most three legs: %ld\n", noWalk3);
  free(p.v);
  return 0;
}
