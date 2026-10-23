/* Census for batch 46 (f) -- which walks serve the two refuting basepoints?
 *
 * WHAT THIS RANGES OVER.  The two verified general pairs of census-batch46e.c:
 * `bing 0 9` with the peak at index 128 shaved (basepoint 138, the valley
 * counterexample) and with the peak at index 309 shaved (basepoint 336, the
 * ceiling counterexample).  Each pair is verified against the definition
 * `IsCrookedIvF` before it is used.  At each of the two basepoints every walk
 * of at most three legs starting within one of the basepoint is enumerated and
 * the fold of each arm is decided exactly, by the dynamic program over the
 * definition `FoldsOnto`; the walks folding both arms are listed.  This is the
 * starting point the report asks for: which walk serves a pair that the two
 * refuted announcements no longer reach.
 *
 * Usage: census-batch46f
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
#define MAXW   96

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

static int rho[MAXN], sig[MAXN], armG[MAXN], armT[MAXN];

static void serve(const int *v, int n, int peak, int base, const char *what) {
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  rho[peak] = v[peak] - 1;
  printf("\n=== %s: peak %d shaved (%d -> %d), basepoint %d ===\n",
         what, peak, v[peak], rho[peak], base);
  printf("  the pair verifies IsCrookedIvF: %d\n", crookedGen(rho, sig, n));
  int mg = n - base, mt = base + 1;
  for (int d = 0; d < mg; d++) armG[d] = rho[base + d];
  for (int d = 0; d < mt; d++) armT[d] = rho[base - d];
  int w[MAXW], found = 0, shown = 0;
  for (int start = 3; start <= 5; start++)
    for (int a = 0; a <= 9; a++)
      for (int b = -1; b <= 9; b++)
        for (int c = -1; c <= 9; c++) {
          if (b < 0 && c >= 0) continue;
          int wl = buildWalk(w, start, a, b, c);
          if (wl < 0) continue;
          if (folds(armG, mg, w, wl) && folds(armT, mt, w, wl)) {
            found++;
            if (shown < 12) {
              shown++;
              printf("    serves: L+%d", start);
              printf(" -> L+%d", a);
              if (b >= 0) printf(" -> L+%d", b);
              if (c >= 0) printf(" -> L+%d", c);
              printf("   (%d links)\n", wl);
            }
          }
        }
  printf("  walks of at most three legs serving both arms: %d\n", found);
}

int main(void) {
  Path p = bpath(0, 9);
  serve(p.v, p.n, 128, 138, "the valley counterexample");
  serve(p.v, p.n, 309, 336, "the ceiling counterexample");
  free(p.v);
  return 0;
}
