/* Census for batch 46 (e) -- the two witnesses, in the exact form the Lean
 * files need.
 *
 * WHAT THIS RANGES OVER.  The same pairs as census-batch46d.c: Bing's 986-link
 * chain `bing 0 9` with one peak shaved -- at a strict local maximum j the link
 * becomes [v_j - 1, v_j], so rho stands one level below the level the link
 * still meets -- each candidate verified against the definition `IsCrookedIvF`
 * of HPC/Fold/Faithful.lean.  Here, for the first basepoint at which a work
 * item of HPC/Fold/Mixed.lean fails, every fact a Lean proof needs is printed:
 * the shaved peak, the basepoint, the two arms' fold status with the index
 * witnessing each failure, and the window that refutes the announcement.
 *
 * Usage: census-batch46e
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

static int highAt1(const int *f, int m) {
  int sawLe2 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !sawLe2) return 0;
    if (f[d] <= 2) sawLe2 = 1;
  }
  return 1;
}
static int ceilAnnFail(const int *f, int m) {     /* index of a failure, or -1 */
  int sawLe0 = 0, sawGe7 = 0, b2 = 0, sawLe1 = 0, mid = 0, b3 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !(sawLe0 || b2 || b3)) return d;
    if (f[d] <= 0) sawLe0 = 1;
    if (sawGe7 && f[d] <= 2) b2 = 1;
    if (mid && f[d] <= 2) b3 = 1;
    if (sawLe1 && f[d] >= 6) mid = 1;
    if (f[d] >= 7) sawGe7 = 1;
    if (f[d] <= 1) sawLe1 = 1;
  }
  return -1;
}
static int valleyAnnFail(const int *f, int m) {   /* index of a failure, or -1 */
  int sawGe6 = 0, sawLe1 = 0, pat = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= 1 && !(sawGe6 || pat)) return d;
    if (sawLe1 && f[d] >= 5) pat = 1;
    if (f[d] >= 6) sawGe6 = 1;
    if (f[d] <= 1) sawLe1 = 1;
  }
  return -1;
}

static const int wLam[13] = {3,4,5,6,7,8,7,6,5,4,3,2,1};
static const int wVee[12] = {5,4,3,2,1,2,3,4,5,6,7,8};

static int rho[MAXN], sig[MAXN], armG[MAXN], armT[MAXN];

static void report_arm(const char *name, const int *f, int m) {
  int first8 = -1, firstLe2 = -1, firstLe1 = -1, first7 = -1, mx = -99, mn = 99;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && first8 < 0) first8 = d;
    if (f[d] <= 2 && firstLe2 < 0) firstLe2 = d;
    if (f[d] <= 1 && firstLe1 < 0) firstLe1 = d;
    if (f[d] >= 7 && first7 < 0) first7 = d;
    if (f[d] > mx) mx = f[d];
    if (f[d] < mn) mn = f[d];
  }
  printf("    %s: %d links, levels [%d,%d]; first >=8 at %d, first >=7 at %d,"
         " first <=2 at %d, first <=1 at %d\n",
         name, m, mn, mx, first8, first7, firstLe2, firstLe1);
}

/* window facts before index d */
static void window(const int *f, int d) {
  int mn = 99, mx = -99;
  for (int j = 0; j < d; j++) { if (f[j] < mn) mn = f[j]; if (f[j] > mx) mx = f[j]; }
  printf("      before step %d the arm stays in [%d, %d]\n", d, mn, mx);
}

static void detail(int j, int i, int m, int which) {
  int mg = m - i, mt = i + 1;
  for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
  for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
  int fLamG = folds(armG, mg, wLam, 13), fLamT = folds(armT, mt, wLam, 13);
  int fVeeG = folds(armG, mg, wVee, 12), fVeeT = folds(armT, mt, wVee, 12);
  printf("\n=== %s counterexample: peak %d shaved, basepoint %d ===\n",
         which == 0 ? "CEILING" : "VALLEY", j, i);
  printf("    rho[%d] = %d (the shaved link meets %d); rho[i] = %d\n",
         j, rho[j], sig[j], rho[i]);
  printf("    folds: Lambda (G,T) = (%d,%d); V (G,T) = (%d,%d)\n", fLamG, fLamT, fVeeG, fVeeT);
  report_arm("forward arm ", armG, mg);
  report_arm("backward arm", armT, mt);
  /* the Lambda failure and the V failure, with their witnesses */
  for (int side = 0; side < 2; side++) {
    const int *f = side ? armT : armG;
    int mm = side ? mt : mg;
    const char *nm = side ? "backward" : "forward";
    if (!(side ? fLamT : fLamG)) {
      int d = -1;
      for (int q = 0; q < mm; q++) if (f[q] <= 1) { d = q; break; }
      if (d >= 0) { printf("    Lambda fails on the %s arm: first descent to <=1 at step %d\n",
                           nm, d); window(f, d); }
    }
    if (!(side ? fVeeT : fVeeG)) {
      int e = -1;
      for (int q = 0; q < mm; q++) if (f[q] >= 7) { e = q; break; }
      if (e >= 0) {
        int mn = 99;
        for (int q = 4; q < e; q++) if (f[q] < mn) mn = f[q];
        printf("    V fails on the %s arm: first ascent to >=7 at step %d;"
               " from step 4 to it the arm stays >= %d\n", nm, e, mn);
      }
    }
  }
  for (int side = 0; side < 2; side++) {
    const int *f = side ? armT : armG;
    int mm = side ? mt : mg;
    const char *nm = side ? "backward" : "forward";
    if (which == 0) {
      int d0 = ceilAnnFail(f, mm);
      if (d0 >= 0) {
        printf("    CEILING ANNOUNCEMENT FAILS on the %s arm at step %d (level %d)\n",
               nm, d0, f[d0]);
        window(f, d0);
        int p7 = -1;
        for (int q = 0; q < d0; q++) if (f[q] >= 7) { p7 = q; break; }
        if (p7 >= 0) {
          int mn = 99;
          for (int q = p7 + 1; q < d0; q++) if (f[q] < mn) mn = f[q];
          printf("      first step at >=7 before it: %d; from there to step %d the arm stays"
                 " >= %d\n", p7, d0, mn);
        } else printf("      the arm never stands at >=7 before step %d\n", d0);
        printf("      arm around the failure:");
        for (int q = (d0 > 12 ? d0 - 12 : 0); q <= d0; q++) printf("%d", f[q]);
        printf("\n");
      }
    } else {
      int d0 = valleyAnnFail(f, mm);
      if (d0 >= 0) {
        printf("    VALLEY ANNOUNCEMENT FAILS on the %s arm at step %d (level %d)\n",
               nm, d0, f[d0]);
        window(f, d0);
        printf("      arm up to the failure:");
        for (int q = (d0 > 40 ? d0 - 40 : 0); q <= d0; q++) printf("%d", f[q]);
        printf("\n");
      }
    }
  }
}

int main(void) {
  Path p = bpath(0, 9);
  int n = p.n, *v = p.v;
  printf("bing 0 9: n = %d\n", n);

  int peaks[MAXN], np = 0;
  for (int jj = 1; jj + 1 < n; jj++)
    if (v[jj] > v[jj-1] && v[jj] > v[jj+1]) peaks[np++] = jj;
  printf("strict local maxima: %d\n", np);

  int doneCeil = 0, doneVal = 0;
  for (int q = 0; q < np && !(doneCeil && doneVal); q++) {
    int j = peaks[q];
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    rho[j] = v[j] - 1;
    if (!crookedGen(rho, sig, n)) { printf("  peak %d: NOT faithful\n", j); continue; }
    for (int i = 0; i < n && !(doneCeil && doneVal); i++) {
      if (rho[i] != 4) continue;
      int mg = n - i, mt = i + 1;
      for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
      for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
      if (!highAt1(armG, mg) || !highAt1(armT, mt)) continue;
      int fLamG = folds(armG, mg, wLam, 13), fLamT = folds(armT, mt, wLam, 13);
      int fVeeG = folds(armG, mg, wVee, 12), fVeeT = folds(armT, mt, wVee, 12);
      if ((fLamG && fLamT) || (fVeeG && fVeeT)) continue;
      int cfG = ceilAnnFail(armG, mg), cfT = ceilAnnFail(armT, mt);
      int vfG = valleyAnnFail(armG, mg), vfT = valleyAnnFail(armT, mt);
      if (!doneCeil && (cfG >= 0 || cfT >= 0)) { detail(j, i, n, 0); doneCeil = 1; }
      if (!doneVal && (vfG >= 0 || vfT >= 0)) { detail(j, i, n, 1); doneVal = 1; }
    }
  }
  free(p.v);
  return 0;
}
