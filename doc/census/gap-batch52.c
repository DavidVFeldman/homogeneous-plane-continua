/* gap-batch52.c -- the shortest arm of the model witnessing the failure of the
 * reflected dichotomies.
 *
 * census-batch52.c reports that the reflected dichotomy floor3R_or_vee -- an arm
 * of the branch L+5 failing Floor3R folds onto the V-walk based at L+6 -- fails
 * on arms of the general model, which is what one expects once the reflected
 * crookedness clause CrookUpR is known to fail there too.  This program takes
 * the same generators and looks for the *shortest* witness, by truncating each
 * failing arm to the shortest prefix that still fails the clause and still fails
 * to fold: both properties are inherited by prefixes containing the offending
 * step, and CrookUp and CrookDown are inherited by every prefix.  The witness is
 * then small enough to be checked in the Lean kernel.
 *
 * Usage: gap-batch52 [rounds] [seed]
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

/* IsCrookedIvF (rho, sig), exactly as HPC/Fold/Crook.lean states it. */
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

/* the dynamic program of HPC/Fold/Decide.lean */
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

/* HighAt f (L+1) (L+8) */
static int highAt(const int *f, int m) {
  int seenLow = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !seenLow) return 0;
    if (f[d] <= 2) seenLow = 1;
  }
  return 1;
}

/* Leg3Valley f L */
static int leg3Valley(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j + 5 <= d && !ok; j++) if (a[j] >= 5) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* Leg3Ceil f L */
static int leg3Ceil(const int *a, int m) {
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

/* Valley4 f L: the valley clause common to the three walks -- before every time
 * at L+1 or below, a time at L+5 or above at a step >= 3, at least 4 earlier. */
static int valley4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j + 4 <= d && !ok; j++) if (a[j] >= 5) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* BottomW4 f L: the floor clause of w4 -- before every time at L or below, a
 * time at L+3 or below at a step >= 1, then a time at L+7 or above at least 6
 * steps later, and the descent at least 7 steps after that. */
static int bottomW4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 0) continue;
    int ok = 0;
    for (int j = 1; j + 13 <= d && !ok; j++) {
      if (a[j] > 3) continue;
      for (int k = j + 6; k + 7 <= d && !ok; k++) if (a[k] >= 7) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

/* TopW5 f L: the ceiling clause of w5 -- before every time at L+9, a time at
 * L+6 or above at a step >= 4, then a time at L+2 or below at least 6 steps
 * later, and the ascent at least 7 steps after that. */
static int topW5(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 9) continue;
    int ok = 0;
    for (int j = 4; j + 13 <= d && !ok; j++) {
      if (a[j] < 6) continue;
      for (int k = j + 6; k + 7 <= d && !ok; k++) if (a[k] <= 2) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

/* Valley5 f L: the valley clause of w5 -- a time at L+6 or above at a step >= 4,
 * at least 5 steps earlier (deepValley_of_foldsOnto_leg3deep). */
static int valley5(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 4; j + 5 <= d && !ok; j++) if (a[j] >= 6) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* MidW4 f L: the trough clause of w4 -- before every time at L+5 or above, a
 * time at L+3 or below at a step >= 1, at least 2 steps earlier. */
static int midW4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 5) continue;
    int ok = 0;
    for (int j = 1; j + 2 <= d && !ok; j++) if (a[j] <= 3) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* CeilW4 f L: the ceiling clause of w4 -- before every time at L+8 or above, a
 * time at L+3 or below at a step >= 1, at least 5 steps earlier. */
static int ceilW4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 8) continue;
    int ok = 0;
    for (int j = 1; j + 5 <= d && !ok; j++) if (a[j] <= 3) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

static int foldsLam(const int *f, int m) {   /* Lambda based at L+3: 3 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 3, 8, 1, -1);
  return folds(f, m, w, wl);
}
static int foldsVee(const int *f, int m) {   /* V based at L+5: 5 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 5, 1, 8, -1);
  return folds(f, m, w, wl);
}
static int foldsW3(const int *f, int m) {    /* 3 -> 6 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 3, 6, 1, 8);
  return folds(f, m, w, wl);
}
static int foldsW4(const int *f, int m) {    /* 3 -> 2 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 3, 2, 8, 1);
  return folds(f, m, w, wl);
}
static int foldsW5(const int *f, int m) {    /* 3 -> 7 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 3, 7, 1, 8);
  return folds(f, m, w, wl);
}

/* The configuration the case analysis of REPORT-batch49.md 2.2 leaves open for
 * `cross_valley_profile`: an arm whose low times before its first ascent to
 * L+7 all occur at its step two or three -- so that the clause applied across
 * the basepoint returns a low link at i-3 or i-2 and the V-criterion, which
 * wants index four or later, is not reached.  Returns 1 if the arm realises it. */
static int residualValleyCase(const int *a, int m) {
  int e = -1;
  for (int d = 0; d < m; d++) if (a[d] >= 7) { e = d; break; }
  if (e < 0) return 0;
  int any = 0, mx = -1, mn = 1 << 30;
  for (int j = 0; j < e; j++) if (a[j] <= 2) { any = 1; if (j > mx) mx = j; if (j < mn) mn = j; }
  return any && mn >= 2 && mx <= 3;
}

/* the shortest zigzag walk with at most three turns serving both arms */
static void findWalk(const int *g, int mg, const int *t, int mt) {
  int best = 1 << 30, bs = -1, ba = -1, bb = -1, bc = -1;
  for (int st = 2; st <= 6; st++)
    for (int a = 0; a <= 9; a++) {
      if (a == st) continue;
      for (int b = -1; b <= 9; b++) {
        if (b == a) continue;
        for (int c = -1; c <= 9; c++) {
          if (c == b) continue;
          if (b < 0 && c >= 0) continue;
          int w[MAXW]; int wl = buildWalk(w, st, a, b, c);
          if (wl < 0 || wl >= best) continue;
          if (folds(g, mg, w, wl) && folds(t, mt, w, wl)) {
            best = wl; bs = st; ba = a; bb = b; bc = c;
          }
        }
      }
    }
  if (bs < 0) printf("      NO walk of at most three turns serves this pair\n");
  else printf("      shortest serving walk (%d times): %d -> %d -> %d -> %d\n",
              best, bs, ba, bb, bc);
}

/* ---- the branch L+5: LowAt, reflection, the reflected crook clauses ------ */

/* LowAt f (L+1) (L+8), as HPC/Fold/Leaf.lean states it. */
static int lowAt(const int *f, int m) {
  int seenHigh8 = 0, seenLow2 = 0, seenLow2High6 = 0;  /* over the indices seen so far */
  for (int d = 0; d < m; d++) {
    if (f[d] <= 1 && !seenHigh8 && !seenLow2High6) return 0;
    if (f[d] >= 8) seenHigh8 = 1;
    if (f[d] >= 6 && seenLow2) seenLow2High6 = 1;
    if (f[d] <= 2) seenLow2 = 1;
  }
  return 1;
}

/* the reflection of an arm in the band [0,9] */
static void reflArm(const int *f, int m, int *g) { for (int d = 0; d < m; d++) g[d] = 9 - f[d]; }

/* CrookUp f, as HPC/Fold/Crook.lean states it */
static int crookUpArm(const int *f, int m) {
  static int nxt[10][MAXN + 1];
  for (int l = 0; l < 10; l++) nxt[l][m] = m;
  for (int j = m - 1; j >= 0; j--)
    for (int l = 0; l < 10; l++) nxt[l][j] = (f[j] == l) ? j : nxt[l][j + 1];
  for (int s = 0; s < m; s++)
    for (int t = s + 1; t < m; t++) {
      if (f[s] + 3 > f[t]) continue;
      int u = m;
      for (int l = f[t] - 2; l <= f[t] - 1; l++)
        if (l >= 0 && l <= 9 && nxt[l][s + 1] < u) u = nxt[l][s + 1];
      if (u >= t) return 0;
      int up = m;
      for (int l = f[s]; l <= f[s] + 1; l++)
        if (l >= 0 && l <= 9 && nxt[l][u + 1] < up) up = nxt[l][u + 1];
      if (up >= t) return 0;
    }
  return 1;
}

/* CrookDown f */
static int crookDownArm(const int *f, int m) {
  static int nxt[10][MAXN + 1];
  for (int l = 0; l < 10; l++) nxt[l][m] = m;
  for (int j = m - 1; j >= 0; j--)
    for (int l = 0; l < 10; l++) nxt[l][j] = (f[j] == l) ? j : nxt[l][j + 1];
  for (int s = 0; s < m; s++)
    for (int t = s + 1; t < m; t++) {
      if (f[t] + 3 > f[s]) continue;
      int u = m;
      for (int l = f[t]; l <= f[t] + 1; l++)
        if (l >= 0 && l <= 9 && nxt[l][s + 1] < u) u = nxt[l][s + 1];
      if (u >= t) return 0;
      int up = m;
      for (int l = f[s] - 2; l <= f[s] - 1; l++)
        if (l >= 0 && l <= 9 && nxt[l][u + 1] < up) up = nxt[l][u + 1];
      if (up >= t) return 0;
    }
  return 1;
}

/* CrookUpR f = CrookDown (9 - f), CrookDownR f = CrookUp (9 - f) */
static int crookUpR(const int *f, int m) {
  static int g[MAXN]; reflArm(f, m, g); return crookDownArm(g, m);
}
static int crookDownR(const int *f, int m) {
  static int g[MAXN]; reflArm(f, m, g); return crookUpArm(g, m);
}

/* the reflected walks, read on the arm itself */
static int foldsLamR(const int *f, int m) {  /* V based at L+6: 6 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 6, 1, 8, -1); return folds(f, m, w, wl);
}
static int foldsVeeR(const int *f, int m) {  /* Lambda based at L+4: 4 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 4, 8, 1, -1); return folds(f, m, w, wl);
}
static int foldsW3R(const int *f, int m) {   /* 6 -> 3 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 6, 3, 8, 1); return folds(f, m, w, wl);
}
static int foldsW4R(const int *f, int m) {   /* 6 -> 7 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 6, 7, 1, 8); return folds(f, m, w, wl);
}
static int foldsW5R(const int *f, int m) {   /* 6 -> 2 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 6, 2, 8, 1); return folds(f, m, w, wl);
}
/* two further candidates for the branch L+5, of the unreflected family: the
 * shortest walks the census finds serving the pairs the three reflections miss */
static int foldsW6(const int *f, int m) {    /* 5 -> 7 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 5, 7, 1, 8); return folds(f, m, w, wl);
}
static int foldsW7(const int *f, int m) {    /* 4 -> 7 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 4, 7, 1, 8); return folds(f, m, w, wl);
}



/* ---- the pair-level miss: the shortest truncation at which the three
 * reflected walks miss a pair of the branch L+5 ---------------------------- */

static int bestP = 1 << 30, bestG[MAXN], bestT[MAXN];

static void considerPair(const int *g, int mg, const int *t, int mt) {
  int lim = mg < mt ? mg : mt;
  if (lim > 120) lim = 120;
  for (int p = 8; p <= lim; p++) {
    if (p >= bestP) return;
    int lam = foldsVeeR(g, p) && foldsVeeR(t, p);      /* Lambda-walk at L+4 */
    int vee = foldsLamR(g, p) && foldsLamR(t, p);      /* V-walk at L+6 */
    if (lam || vee) continue;
    int s3 = foldsW3R(g, p) && foldsW3R(t, p);
    int s4 = foldsW4R(g, p) && foldsW4R(t, p);
    int s5 = foldsW5R(g, p) && foldsW5R(t, p);
    if (s3 || s4 || s5) continue;
    bestP = p; memcpy(bestG, g, sizeof(int) * p); memcpy(bestT, t, sizeof(int) * p);
    return;
  }
}

static void scanPairs(int n) {
  for (int i = 0; i < n; i++) {
    if (rho[i] != 5) continue;
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
    for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
    if (!lowAt(armG, mg) || !lowAt(armT, mt)) continue;
    considerPair(armG, mg, armT, mt);
  }
}

/* ---- the search ---------------------------------------------------------- */

static int bestLen = 1 << 30, bestArm[MAXN], bestKind = -1;
static int bestLen2 = 1 << 30, bestArm2[MAXN];

/* Floor3R read on the arm itself */
static int floor3R(const int *f, int m) { static int g[MAXN]; reflArm(f, m, g); return leg3Ceil(g, m); }
/* Ceil4R read on the arm itself */
static int ceil4R(const int *f, int m) { static int g[MAXN]; reflArm(f, m, g); return valley4(g, m); }

static void consider(const int *a, int m) {
  /* floor3R_or_vee: fails Floor3R and does not fold onto 6 -> 1 -> 8 */
  if (!floor3R(a, m) && !foldsLamR(a, m)) {
    for (int p = 4; p <= m; p++)
      if (!floor3R(a, p) && !foldsLamR(a, p)) {
        if (p < bestLen) { bestLen = p; memcpy(bestArm, a, sizeof(int) * p); bestKind = 3; }
        break;
      }
  }
  /* ceil4R_or_lam: fails Ceil4R and does not fold onto 4 -> 8 -> 1 */
  if (!ceil4R(a, m) && !foldsVeeR(a, m)) {
    for (int p = 4; p <= m; p++)
      if (!ceil4R(a, p) && !foldsVeeR(a, p)) {
        if (p < bestLen2) { bestLen2 = p; memcpy(bestArm2, a, sizeof(int) * p); }
        break;
      }
  }
}

static void scanGap(int n) {
  for (int i = 0; i < n; i++) {
    if (rho[i] != 5) continue;
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
    for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
    if (!lowAt(armG, mg) || !lowAt(armT, mt)) continue;
    consider(armG, mg);
    consider(armT, mt);
  }
}

static void runChainGap(int n, const int *v, long rounds) {
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  if (crookedGen(rho, sig, n)) { scanGap(n); scanPairs(n); }
  for (int pk = 1; pk + 1 < n; pk++) {
    if (!(v[pk] > v[pk-1] && v[pk] > v[pk+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    rho[pk] = v[pk] - 1;
    if (crookedGen(rho, sig, n)) { scanGap(n); scanPairs(n); }
  }
  for (int vl = 1; vl + 1 < n; vl++) {
    if (!(v[vl] < v[vl-1] && v[vl] < v[vl+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    sig[vl] = v[vl] + 1;
    if (crookedGen(rho, sig, n)) { scanGap(n); scanPairs(n); }
  }
  for (long it = 0; it < rounds; it++) {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) { if (random() % 2 == 0) rho[j] = v[j] - 1; }
      else if (v[j] < v[j-1] && v[j] < v[j+1]) { if (random() % 2 == 0) sig[j] = v[j] + 1; }
    }
    if (crookedGen(rho, sig, n)) { scanGap(n); scanPairs(n); }
  }
  {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) rho[j] = v[j] - 1;
      else if (v[j] < v[j-1] && v[j] < v[j+1]) sig[j] = v[j] + 1;
    }
    if (crookedGen(rho, sig, n)) { scanGap(n); scanPairs(n); }
  }
}

static void show(const char *what, const int *a, int m) {
  if (m > 1000) { printf("%s: none found\n", what); return; }
  printf("%s: length %d\n  levels:", what, m);
  for (int d = 0; d < m; d++) printf(" %d", a[d]);
  printf("\n  nat16: 0x");
  for (int d = m - 1; d >= 0; d--) printf("%X", a[d]);
  printf("\n  CrookUp=%d CrookDown=%d CrookUpR=%d CrookDownR=%d Ceil4R=%d Floor3R=%d "
         "foldsLamL4=%d foldsVeeL6=%d w3R=%d w4R=%d w5R=%d\n",
         crookUpArm(a, m), crookDownArm(a, m), !crookDownArm(a, m) ? 0 : crookUpR(a, m),
         crookDownR(a, m), ceil4R(a, m), floor3R(a, m), foldsVeeR(a, m), foldsLamR(a, m),
         foldsW3R(a, m), foldsW4R(a, m), foldsW5R(a, m));
}

int main(int argc, char **argv) {
  long rounds = (argc > 1) ? atol(argv[1]) : 200;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 52u;
  srandom(seed);
  setvbuf(stdout, NULL, _IOLBF, 0);
  Path p = bpath(0, 9);
  runChainGap(p.n, p.v, rounds);
  Path q = bpath(9, 0);
  runChainGap(q.n, q.v, rounds);
  printf("gap-batch52: rounds=%ld seed=%u\n", rounds, seed);
  if (bestKind == 3) show("shortest witness against floor3R_or_vee", bestArm, bestLen);
  else printf("no witness against floor3R_or_vee\n");
  if (bestLen2 < (1 << 30)) show("shortest witness against ceil4R_or_lam", bestArm2, bestLen2);
  else printf("no witness against ceil4R_or_lam\n");
  if (bestP < (1 << 30)) {
    printf("\nshortest truncation at which the three reflected walks miss a pair: %d steps\n",
           bestP);
    show("  forward arm", bestG, bestP);
    show("  backward arm", bestT, bestP);
  } else printf("\nno pair of the branch L+5 missed by the three reflected walks\n");
  free(p.v); free(q.v);
  return 0;
}
