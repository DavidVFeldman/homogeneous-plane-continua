/* Census for batch 46 (d) -- shaved peaks: pairs of the GENERAL model whose
 * point sequence rho is one level short of its own crookedness witnesses.
 *
 * WHAT THIS RANGES OVER.  Faithful crooked pairs (rho, sigma) obtained from
 * Bing's 986-link chain `bing 0 9` by SHAVING peaks: at a link j whose level is
 * a local maximum, the pair is changed from [v_j, v_j] to [v_j - 1, v_j], so
 * that the link still meets the level v_j while its rho stands one level lower.
 * The length of the sequence is unchanged; only rho moves.  Nothing is assumed:
 * every candidate is verified against the definition `IsCrookedIvF` exactly as
 * in HPC/Fold/Faithful.lean (le, width, adj, and the crookedness clause with
 * "near" tolerance one, a link meeting every level between rho and sigma).
 *
 * WHAT IS CHECKED.  For each verified pair of span nine with both ends of the
 * band attained by rho, at every basepoint i with rho[i] = L+4 whose two
 * rho-arms are HighAt (L+1) (L+8) -- the open branch of span nine -- the two
 * canonical folds are decided exactly by the dynamic program over `FoldsOnto`,
 * and, when neither canonical walk folds both arms:
 *    - the ceiling announcement CeilAnn   (the work item `unserved_ceiling`),
 *    - the valley announcement            (the work item `unserved_valley`),
 * read on the rho-arms exactly as the Lean statements read them; and a search
 * for a walk of at most three legs folding both arms.
 *
 * Usage: census-batch46d [mode] [seed] [trials]
 *   mode 0: shave every peak at level 7 that can be shaved, one at a time
 *   mode 1: shave every peak (any level), one at a time
 *   mode 2: random subsets of shavable peaks, `trials` of them
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

static int crookedGen(const int *rho, const int *sig, int n, const char **why) {
  if (why) *why = "ok";
  if (n <= 0 || n > MAXN) { if (why) *why = "size"; return 0; }
  for (int t = 0; t < n; t++)
    if (rho[t] > sig[t] || sig[t] > rho[t] + 1) { if (why) *why = "width"; return 0; }
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

static int highAt1(const int *f, int m) {
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

static int rho[MAXN], sig[MAXN];
static int armG[MAXN], armT[MAXN];
static int shaved[MAXN];

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

static long branch = 0, unserved = 0, ceilFail = 0, valFail = 0, noWalk3 = 0;
static int shownCe = 0, shownNo = 0;

static void analyse(int m, int tag) {
  int lo = 99, hi = -99;
  for (int t = 0; t < m; t++) { if (rho[t] < lo) lo = rho[t]; if (rho[t] > hi) hi = rho[t]; }
  if (lo != 0 || hi != 9) return;
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
    if ((!cA || !vA) && shownCe < 5) {
      shownCe++;
      printf("\n  *** WORK ITEM FAILS on a verified general pair (tag %d), basepoint %d\n",
             tag, i);
      printf("      ceiling announcement: %d; valley announcement: %d\n", cA, vA);
      printf("      folds: Lambda (G,T) = (%d,%d); V (G,T) = (%d,%d)\n",
             fLamG, fLamT, fVeeG, fVeeT);
    }
    int w[MAXW], wl = 0;
    if (!searchWalk(armG, mg, armT, mt, w, &wl)) {
      noWalk3++;
      if (shownNo < 3) {
        shownNo++;
        printf("\n  *** NO WALK OF AT MOST THREE LEGS (tag %d), basepoint %d of %d links\n",
               tag, i, m);
      }
    }
  }
}

int main(int argc, char **argv) {
  int mode = (argc > 1) ? atoi(argv[1]) : 0;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 11u;
  long trials = (argc > 3) ? atol(argv[3]) : 50;
  srandom(seed);

  Path p = bpath(0, 9);
  int n = p.n, *v = p.v;
  const char *why;
  for (int j = 0; j < n; j++) { rho[j] = v[j]; sig[j] = v[j]; }
  printf("bing 0 9: n = %d; thin pair verifies: %d\n", n, crookedGen(rho, sig, n, &why));

  /* the peaks */
  int peaks[MAXN], np = 0;
  for (int j = 1; j + 1 < n; j++)
    if (v[j] > v[j-1] && v[j] > v[j+1]) peaks[np++] = j;
  printf("local maxima: %d", np);
  { int cnt7 = 0; for (int q = 0; q < np; q++) if (v[peaks[q]] == 7) cnt7++;
    printf(" (of them at level 7: %d)\n", cnt7); }

  if (mode == 0 || mode == 1) {
    long ok = 0, tried = 0;
    for (int q = 0; q < np; q++) {
      int j = peaks[q];
      if (mode == 0 && v[j] != 7) continue;
      tried++;
      for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
      rho[j] = v[j] - 1; sig[j] = v[j];
      if (crookedGen(rho, sig, n, &why)) { ok++; analyse(n, j); }
    }
    printf("single shavings tried: %ld; faithful: %ld\n", tried, ok);
  } else {
    long ok = 0;
    for (long tr = 0; tr < trials; tr++) {
      for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; shaved[u] = 0; }
      for (int q = 0; q < np; q++)
        if ((random() % 100) < 30) { int j = peaks[q]; rho[j] = v[j] - 1; shaved[j] = 1; }
      if (crookedGen(rho, sig, n, &why)) { ok++; analyse(n, (int)tr); }
    }
    printf("random shavings: %ld of %ld faithful\n", ok, trials);
  }

  printf("\nbasepoints of the open branch met: %ld\n", branch);
  printf("  folding onto neither canonical walk: %ld\n", unserved);
  printf("    failing the ceiling announcement (unserved_ceiling): %ld\n", ceilFail);
  printf("    failing the valley announcement  (unserved_valley):  %ld\n", valFail);
  printf("    served by no walk of at most three legs: %ld\n", noWalk3);
  free(p.v);
  return 0;
}
