/* Census for batch 45 (b) -- the counterexample to `unserved_high8`, exhibited
 * inside one sequence, and checked twice.
 *
 * WHAT THIS RANGES OVER.  One actual faithful crooked sequence in the thin form
 * sigma = rho: Bing's 986-link chain `bing 0 9`, whose span is exactly nine and
 * whose two ends are attained, so every hypothesis of `unserved_high8` about
 * the sequence holds on it.  Crookedness is verified against `IsCrookedIvF` by
 * the routine `crookedThin` of census-batch43.c (run first on paths whose
 * status is known).  Nothing here ranges over a one-arm class.
 *
 * WHAT IS CHECKED, TWICE.  For every basepoint i with v[i] = L+4 and both arms
 * HighAt (L+1) (L+8) -- the open branch -- the two canonical folds are decided
 *   (1) exactly, by the dynamic program over the definition `FoldsOnto`, and
 *   (2) by the exact criteria of HPC/Fold/Profile.lean, read with the index
 *       clauses that HPC/Fold/Timing.lean supplies:
 *         Lambda-walk based at L+3 : before every descent to L+1 the arm stands
 *                                    at L+7 or above at an index at least five;
 *         V-walk based at L+5      : before every ascent to L+7 the arm stands
 *                                    at L+2 or below at an index at least four.
 * The two answers are compared at every basepoint; a disagreement is reported.
 *
 * THE COUNTEREXAMPLE.  A basepoint is a counterexample to `unserved_high8` when
 * neither canonical walk folds both arms and some arm rises to L+8 with no
 * earlier time at L+1 or below.  The first ones found are printed with their
 * indices, the failing arm, the index of the unannounced ascent, and the least
 * level the arm reaches before it.  The weaker ceiling announcement that the
 * three-leg engine actually asks for is checked at the same basepoints.
 *
 * Usage: census-batch45b
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

#define MAXLEV 64
#define MAXN   40001

static int nxtTab[MAXLEV][MAXN];

static int crookedThin(const int *v, int n) {
  int lo = v[0], hi = v[0];
  for (int j = 0; j < n; j++) { if (v[j] < lo) lo = v[j]; if (v[j] > hi) hi = v[j]; }
  int nlev = hi - lo + 1;
  if (nlev > MAXLEV || n >= MAXN) return 0;
  for (int j = 0; j + 1 < n; j++) { int d = v[j+1] - v[j]; if (d > 1 || d < -1) return 0; }
  for (int l = 0; l < nlev; l++) nxtTab[l][n] = n;
  for (int j = n - 1; j >= 0; j--)
    for (int l = 0; l < nlev; l++)
      nxtTab[l][j] = (v[j] - lo == l) ? j : nxtTab[l][j + 1];
  for (int s = 0; s < n; s++) {
    int hs[3], nh = 0;
    for (int e = -1; e <= 1; e++) {
      int u = s + e; if (u < 0 || u >= n) continue;
      int seen = 0;
      for (int q = 0; q < nh; q++) if (hs[q] == v[u]) seen = 1;
      if (!seen) hs[nh++] = v[u];
    }
    for (int t = s + 1; t < n; t++) {
      int ks[3], nk = 0;
      for (int e = -1; e <= 1; e++) {
        int u = t + e; if (u < 0 || u >= n) continue;
        int seen = 0;
        for (int q = 0; q < nk; q++) if (ks[q] == v[u]) seen = 1;
        if (!seen) ks[nk++] = v[u];
      }
      for (int a = 0; a < nh; a++) for (int b = 0; b < nk; b++) {
        int h = hs[a], k = ks[b];
        int diff = h - k; if (diff < 0) diff = -diff;
        if (diff < 3) continue;
        int r1, r2;
        if (h < k) { r1 = k - 1; r2 = h + 1; } else { r1 = k + 1; r2 = h - 1; }
        if (r1 - lo < 0 || r1 - lo >= nlev || r2 - lo < 0 || r2 - lo >= nlev) return 0;
        int p1 = nxtTab[r1 - lo][s + 1];
        if (p1 >= t) return 0;
        int p2 = nxtTab[r2 - lo][p1 + 1];
        if (p2 >= t) return 0;
      }
    }
  }
  return 1;
}

#define MAXW 80

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

/* the exact criteria, with the index clauses of HPC/Fold/Timing.lean */
static int lamCrit(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] > 1) continue;
    int ok = 0;
    for (int j = 0; j < d; j++) if (j >= 5 && f[j] >= 7) { ok = 1; break; }
    if (!ok) return 0;
  }
  return 1;
}
static int veeCrit(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] < 7) continue;
    int ok = 0;
    for (int j = 0; j < d; j++) if (j >= 4 && f[j] <= 2) { ok = 1; break; }
    if (!ok) return 0;
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
/* HighAt f L (L+8); returns -1 when it holds, else the first offending index */
static int high8Fail(const int *f, int m) {
  int sawLe1 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !sawLe1) return d;
    if (f[d] <= 1) sawLe1 = 1;
  }
  return -1;
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

static int armG[MAXN], armT[MAXN];

int main(void) {
  { Path q = bpath(0, 8);
    printf("check bing 0 8 (n=%d) crooked: %d\n", q.n, crookedThin(q.v, q.n)); free(q.v); }
  { int mono[6] = {0,1,2,3,4,5}; printf("check monotone run crooked: %d\n", crookedThin(mono, 6)); }

  Path p = bpath(0, 9);
  int n = p.n, *v = p.v;
  printf("bing 0 9: n = %d, crooked = %d\n", n, crookedThin(v, n));
  int lo = v[0], hi = v[0];
  for (int j = 0; j < n; j++) { if (v[j] < lo) lo = v[j]; if (v[j] > hi) hi = v[j]; }
  printf("levels attained: [%d, %d]; v[0] = %d, v[n-1] = %d\n", lo, hi, v[0], v[n-1]);

  long long branch = 0, unserved = 0, ce = 0, disagree = 0, ceilFail = 0, valFail = 0;
  int shown = 0;
  for (int i = 0; i < n; i++) {
    if (v[i] != 4) continue;
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armG[d] = v[i + d];
    for (int d = 0; d < mt; d++) armT[d] = v[i - d];
    if (!highAt1(armG, mg) || !highAt1(armT, mt)) continue;
    branch++;
    int fLamG = folds(armG, mg, wLam, 13), fLamT = folds(armT, mt, wLam, 13);
    int fVeeG = folds(armG, mg, wVee, 12), fVeeT = folds(armT, mt, wVee, 12);
    if (fLamG != lamCrit(armG, mg) || fLamT != lamCrit(armT, mt) ||
        fVeeG != veeCrit(armG, mg) || fVeeT != veeCrit(armT, mt)) {
      disagree++;
      printf("  !!! the fold and its criterion disagree at basepoint %d\n", i);
    }
    if ((fLamG && fLamT) || (fVeeG && fVeeT)) continue;
    unserved++;
    int hg = high8Fail(armG, mg), ht = high8Fail(armT, mt);
    if (!(ceilAnn(armG, mg) && ceilAnn(armT, mt))) ceilFail++;
    if (!(valleyAnn(armG, mg) && valleyAnn(armT, mt))) valFail++;
    if (hg < 0 && ht < 0) continue;
    ce++;
    if (shown < 4) {
      shown++;
      int d0 = hg >= 0 ? hg : ht;
      const int *a = hg >= 0 ? armG : armT;
      int mn = 99, mx = -99;
      for (int d = 0; d < d0; d++) { if (a[d] < mn) mn = a[d]; if (a[d] > mx) mx = a[d]; }
      printf("\n  *** COUNTEREXAMPLE to unserved_high8 at basepoint i = %d of bing 0 9\n", i);
      printf("      arms: forward %d links, backward %d links; v[i] = %d\n", mg, mt, v[i]);
      printf("      folds: Lambda (G,T) = (%d,%d); V (G,T) = (%d,%d)\n",
             fLamG, fLamT, fVeeG, fVeeT);
      printf("      the %s arm stands at L+%d at its step %d with no earlier time at L+1;\n",
             hg >= 0 ? "forward" : "backward", a[d0], d0);
      printf("      before that step it stays in [L+%d, L+%d]\n", mn, mx);
      printf("      ceiling announcement on that arm: %d (valley: %d)\n",
             ceilAnn(a, hg >= 0 ? mg : mt), valleyAnn(a, hg >= 0 ? mg : mt));
      printf("      the arm up to the failure:");
      for (int d = 0; d <= d0; d++) printf("%d", a[d]);
      printf("\n");
    }
  }
  printf("\nbasepoints of the open branch in bing 0 9: %lld\n", branch);
  printf("  folding onto neither canonical walk: %lld\n", unserved);
  printf("  of those, COUNTEREXAMPLES to unserved_high8: %lld\n", ce);
  printf("  of those, failing the ceiling announcement: %lld\n", ceilFail);
  printf("  of those, failing the valley announcement:  %lld\n", valFail);
  printf("fold/criterion disagreements: %lld\n", disagree);
  free(p.v);
  return 0;
}
