/* min-batch71.c -- batch 71, question 2.4: the smallest counterexample.
 *
 * break-batch71.c constructs faithful pairs with a high-run crossing whose
 * nearest time at L+2 or below is far beyond the 67 steps the reading of
 * NearLowT needs, and stores the most extreme one whole in witness-batch71.txt.
 * This program trims that pair -- binary search at each end, then a greedy pass
 * -- to the shortest window that is still a faithful pair with the same
 * basepoint, still a high-run crossing of the trichotomy, and still without a
 * time at L+2 or below within 67 steps before the basepoint.  Every predicate is
 * re-evaluated by its own definition at every trim, nothing is inherited.
 *
 * Usage: min-batch71 [witness file]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

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
#define MAXN   4096
/* the corpus generators keep batch 70's length bound, so the corpus is the same;
   the larger MAXN is only room for the edited pairs of the construction attempt */
#define MAXBASE 2400

static int meetTab[MAXLEV][MAXN + 1];

/* IsCrookedIvF (rho, sig), exactly as HPC/Fold/Faithful.lean states it.
   Copied unchanged from census-batch69.c. */
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

static int rho[MAXN], sig[MAXN], armG[MAXN], armT[MAXN], gG[MAXN], gT[MAXN];

/* LowAt f (L+1) (L+8) at L = 0, copied from census-batch69.c */
static int lowAt(const int *f, int m) {
  int seenHigh8 = 0, seenLow2 = 0, seenLow2High6 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= 1 && !seenHigh8 && !seenLow2High6) return 0;
    if (f[d] >= 8) seenHigh8 = 1;
    if (f[d] >= 6 && seenLow2) seenLow2High6 = 1;
    if (f[d] <= 2) seenLow2 = 1;
  }
  return 1;
}

static void reflArm(const int *f, int m, int *g) { for (int d = 0; d < m; d++) g[d] = 9 - f[d]; }

/* ---- the dynamic program of HPC/Fold/Decide.lean, and the four-leg family --
 *
 * folds decides FoldsOnto f len c by reachability, exactly as foldsB does; the
 * family is leg4Walk 0 9 K M P of HPC/Fold/Leg4Wide.lean over its window of
 * parameter sets, together with the reflection of each.  Both are copied
 * unchanged from census-batch69.c. */

#define MAXW 96

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

static int buildWalk4(int *w, int start, int a, int b, int c, int e) {
  int len = 0, cur = start;
  w[len++] = cur;
  int tgt[4] = {a, b, c, e};
  for (int q = 0; q < 4; q++) {
    if (tgt[q] < 0) break;
    if (tgt[q] == cur) return -1;
    int s = tgt[q] > cur ? 1 : -1;
    while (cur != tgt[q]) { cur += s; if (len >= MAXW) return -1; w[len++] = cur; }
  }
  return len;
}

#define MAXFAM 64
typedef struct { int P, K, M, refl, st, a, b, c, e, len; } Fam;
static Fam fam[MAXFAM];
static int famN = 0;

static void buildFamily(void) {
  for (int P = 2; P <= 6; P++)
    for (int K = P; K <= 8; K++)
      for (int M = 1; M <= P - 2; M++) {
        if (M + 3 > K) continue;
        int st = P - 1, a = K, b = M, c = 8, e = 1;
        int w[MAXW]; int wl = buildWalk4(w, st, a, b, c, e);
        if (wl < 0 || famN >= MAXFAM) continue;
        fam[famN].P = P; fam[famN].K = K; fam[famN].M = M; fam[famN].refl = 0;
        fam[famN].st = st; fam[famN].a = a; fam[famN].b = b; fam[famN].c = c; fam[famN].e = e;
        fam[famN].len = wl; famN++;
        int rst = 9 - st, ra = 9 - a, rb = 9 - b, rc = 9 - c, re = 9 - e;
        int w2[MAXW]; int wl2 = buildWalk4(w2, rst, ra, rb, rc, re);
        if (wl2 < 0 || famN >= MAXFAM) continue;
        fam[famN].P = P; fam[famN].K = K; fam[famN].M = M; fam[famN].refl = 1;
        fam[famN].st = rst; fam[famN].a = ra; fam[famN].b = rb; fam[famN].c = rc;
        fam[famN].e = re; fam[famN].len = wl2; famN++;
      }
}

static int famFoldsBoth(int q, const int *g, int mg, const int *t, int mt) {
  int w[MAXW];
  int wl = buildWalk4(w, fam[q].st, fam[q].a, fam[q].b, fam[q].c, fam[q].e);
  if (wl < 0) return 0;
  return folds(g, mg, w, wl) && folds(t, mt, w, wl);
}

/* Leg4Land of HPC/Fold/Leg4Land.lean at H = 9, L = 0, read greedily.
   Copied unchanged from census-batch69.c. */
static int landLeg4(const int *f, int m, int K, int M, int P) {
  const int H = 9;
  int A = K - P + 1;
  if (f[0] < P - 2 || f[0] > P) return 0;
  int t1 = -1, t2 = -1, t3 = -1;
  for (int j = A; j < m; j++) if (f[j] >= K - 1) { t1 = j; break; }
  if (t1 >= 0) for (int k = t1 + (K - M); k < m; k++) if (f[k] <= M + 1) { t2 = k; break; }
  if (t2 >= 0) for (int l = t2 + (H - 1 - M); l < m; l++) if (f[l] >= H - 2) { t3 = l; break; }
  for (int d = 0; d < m; d++) {
    if (f[d] <= P - 3 && (t1 < 0 || t1 + (K - 1 - f[d]) > d)) return 0;
    if (f[d] <= M - 2 && (t3 < 0 || t3 + (H - 2 - f[d]) > d)) return 0;
    if (f[d] >= K + 2 && (t2 < 0 || t2 + (f[d] - M - 1) > d)) return 0;
  }
  return 1;
}

/* DeepFirst2 of HPC/Fold/Ceil68.lean at L = 0 */
static int deepFirst2(const int *f, int m) {
  for (int e = 0; e < m; e++) {
    if (f[e] < 9) continue;
    int ok = 0;
    for (int d = 0; d < e && !ok; d++) if (f[d] <= 2) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* Ceil72: the third clause of Leg4Land at (9,7,2,5), existentials searched */
static int ceil72Clause(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] < 9) continue;
    int ok = 0;
    for (int j = 3; j < m && !ok; j++) {
      if (f[j] < 6) continue;
      for (int k = j + 5; k < m && !ok; k++) {
        if (f[k] > 3) continue;
        if (k + (f[d] - 3) <= d) ok = 1;
      }
    }
    if (!ok) return 0;
  }
  return 1;
}

/* Deep72: the second clause of the same, existentials searched */
static int deep72Clause(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] > 0) continue;
    int ok = 0;
    for (int j = 3; j < m && !ok; j++) {
      if (f[j] < 6) continue;
      for (int k = j + 5; k < m && !ok; k++) {
        if (f[k] > 3) continue;
        for (int l = k + 6; l < m && !ok; l++) {
          if (f[l] < 7) continue;
          if (l + (7 - f[d]) <= d) ok = 1;
        }
      }
    }
    if (!ok) return 0;
  }
  return 1;
}

/* Mid2Floor of HPC/Fold/CrossPartner64.lean at L = 0 */
static int mid2Floor(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] != 2) continue;
    int ok = 0;
    for (int j = 3; j + 4 <= d && !ok; j++) if (f[j] >= 6) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

static int reachesNine(const int *f, int m) {
  for (int d = 0; d < m; d++) if (f[d] >= 9) return 1;
  return 0;
}
static int touchesZero(const int *f, int m) {
  for (int d = 0; d < m; d++) if (f[d] <= 0) return 1;
  return 0;
}
static int firstNine(const int *f, int m) {
  for (int d = 0; d < m; d++) if (f[d] >= 9) return d;
  return -1;
}
/* NineBeforeDeep of HPC/Fold/Ceil69.lean at L = 0 */
static int nineBeforeDeep(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] > 0) continue;
    int ok = 0;
    for (int e = 0; e < d && !ok; e++) if (f[e] >= 9) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}


/* ------------------------------------------------------------- the trim ---- */

static int wRho[MAXN], wSig[MAXN], wN, wI, wSide;
static int tRho[MAXN], tSig[MAXN];

/* is the pair in rho/sig, of length n, faithful, with a high-run crossing at the
   basepoint i whose nearest time at L+2 or below on the partner's side is more
   than 67 steps before the basepoint?  Every predicate by its own definition. */
static int breaksAt(int n, int i, int *pnear2, int *pside) {
  if (i <= 0 || i >= n) return 0;
  if (!crookedGen(rho, sig, n)) return 0;
  if (rho[i] != 5) return 0;
  int mg = n - i, mt = i + 1;
  for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
  for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
  if (!(lowAt(armG, mg) && lowAt(armT, mt))) return 0;
  reflArm(armG, mg, gG);
  reflArm(armT, mt, gT);
  int tG = 0, tT = 0;
  if (landLeg4(gG, mg, 6, 2, 4)) tG |= 1;
  if (landLeg4(armG, mg, 8, 1, 5)) tG |= 2;
  if (landLeg4(gG, mg, 6, 1, 4)) tG |= 4;
  if (landLeg4(gT, mt, 6, 2, 4)) tT |= 1;
  if (landLeg4(armT, mt, 8, 1, 5)) tT |= 2;
  if (landLeg4(gT, mt, 6, 1, 4)) tT |= 4;
  if (tG & tT) return 0;
  int gHas8 = (tG & 2) != 0, tHas8 = (tT & 2) != 0;
  if (gHas8 == tHas8) return 0;
  int *Y; int mY;
  if (gHas8) { if (deepFirst2(armG, mg)) return 0; Y = armT; mY = mt; }
  else { if (deepFirst2(armT, mt)) return 0; Y = armG; mY = mg; }
  int near2 = -1;
  for (int s = 1; s < mY; s++) if (Y[s] <= 2) { near2 = s; break; }
  int v = (near2 < 0) ? (1 << 20) : near2;
  if (v <= 67) return 0;
  if (pnear2) *pnear2 = near2;
  if (pside) *pside = gHas8;
  return 1;
}

/* load the window [a, b] of the witness into rho/sig */
static void window(int a, int b) {
  for (int t = a; t <= b; t++) { rho[t - a] = wRho[t]; sig[t - a] = wSig[t]; }
}

int main(int argc, char **argv) {
  const char *path = (argc > 1) ? argv[1] : "witness-batch71.txt";
  FILE *fp = fopen(path, "r");
  if (!fp) { printf("cannot open %s\n", path); return 1; }
  if (fscanf(fp, "%d %d %d", &wN, &wI, &wSide) != 3) return 1;
  for (int t = 0; t < wN; t++) if (fscanf(fp, "%d", &wRho[t]) != 1) return 1;
  for (int t = 0; t < wN; t++) if (fscanf(fp, "%d", &wSig[t]) != 1) return 1;
  fclose(fp);
  printf("min-batch71: the smallest window of the batch-71 counterexample.\n");
  printf("  the witness read: %d links, basepoint %d, the w8 side is the %s arm\n",
         wN, wI, wSide ? "forward" : "backward");
  int near2 = -1, side = -1;
  window(0, wN - 1);
  if (!breaksAt(wN, wI, &near2, &side)) {
    printf("  the stored pair does not break the distance statement: nothing to do\n");
    return 1;
  }
  printf("  it breaks the distance statement: the nearest time at L+2 or below is %d"
         " steps\n  before the basepoint, against the bound 67\n", near2);

  int a = 0, b = wN - 1;
  /* trim the right end (the running arm) as far as the break survives */
  {
    int lo = wI + 1, hi = b;                 /* the last link kept */
    while (lo < hi) {
      int mid = (lo + hi) / 2;
      window(a, mid);
      if (breaksAt(mid - a + 1, wI - a, NULL, NULL)) hi = mid; else lo = mid + 1;
    }
    b = lo;
  }
  /* trim the left end (the partner's arm) as far as the break survives */
  {
    int lo = 0, hi = wI - 1;                 /* the first link kept */
    while (lo < hi) {
      int mid = (lo + hi + 1) / 2;
      window(mid, b);
      if (breaksAt(b - mid + 1, wI - mid, NULL, NULL)) lo = mid; else hi = mid - 1;
    }
    a = lo;
  }
  /* a final greedy pass at both ends */
  for (int pass = 0; pass < 4; pass++) {
    while (b > wI + 1) {
      window(a, b - 1);
      if (!breaksAt(b - a, wI - a, NULL, NULL)) break;
      b--;
    }
    while (a < wI - 1) {
      window(a + 1, b);
      if (!breaksAt(b - a, wI - a - 1, NULL, NULL)) break;
      a++;
    }
  }
  window(a, b);
  int n = b - a + 1, i = wI - a;
  if (!breaksAt(n, i, &near2, &side)) { printf("  the trim lost the break\n"); return 1; }
  printf("  the smallest window found: links [%d, %d] of the witness -- %d links,"
         " basepoint %d,\n  the w8 side is the %s arm, the nearest time at L+2 or below"
         " %d steps before it\n", a, b, n, i, side ? "forward" : "backward", near2);
  FILE *out = fopen("witness-batch71-min.txt", "w");
  if (out) {
    fprintf(out, "%d %d %d\n", n, i, side);
    for (int t = 0; t < n; t++) fprintf(out, "%d%c", rho[t], t + 1 == n ? '\n' : ' ');
    for (int t = 0; t < n; t++) fprintf(out, "%d%c", sig[t], t + 1 == n ? '\n' : ' ');
    fclose(out);
    printf("  written to witness-batch71-min.txt\n");
  }
  printf("  the level sequence:\n   ");
  for (int t = 0; t < n; t++) printf(" %d", rho[t]);
  printf("\n  the upper ends:\n   ");
  for (int t = 0; t < n; t++) printf(" %d", sig[t]);
  printf("\n");
  return 0;
}
