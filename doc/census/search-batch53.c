/* census-batch53.c -- batch 53.  The ceiling crossing, the list of walks at the
 * branch L+5, and the valley residue.
 *
 * Carried over from census-batch52.c: the generators, the faithfulness test
 * (IsCrookedIvF), the dynamic program over FoldsOnto (HPC/Fold/Decide.lean),
 * the predicates of the walks and the exactness audit.
 *
 * New in this batch.
 *
 *   A. The target `cross_ceil_sentence` (commission 1, question 2), over a
 *      wider corpus: at every branch basepoint (rho i = L+4, both arms
 *      HighAt (L+1) (L+8)) at which some arm fails Leg3Ceil and the pair does
 *      not fold onto the Lambda-walk, does the pair satisfy the sentence of w4
 *      on both arms or the sentence of w5 on both arms?
 *
 *   B. The valley residue (commission 2, question 3).  Three predicates are
 *      separated, in increasing strength of the exclusion they would give:
 *        - ValleyResidual, exactly as HPC/Fold/CrossValley.lean states it:
 *          rho stands at L+2 two or three steps to one side of the basepoint;
 *        - the *narrow* residue: such a time u at which no level at or below
 *          L+1 is met by the interval [rho, sig] at u-1, u or u+1, so that the
 *          faithfulness clause anchored within one of u cannot return a time at
 *          L+2 or below (this is the configuration the sharpened dichotomy of
 *          HPC/Fold/CrossValleyNear.lean leaves);
 *        - the narrow residue *together with* an arm failing Leg3Valley, which
 *          is the only configuration in which the dichotomy is called on.
 *      Each is counted, and the conclusion of the work item is checked there.
 *
 *   C. The list of walks at the branch L+5 (commission question 1).  For every
 *      unserved pair of the branch that none of the three reflected walks
 *      serves, the shortest walk of at most three turns based within one of
 *      L+5 that serves it is computed, and a histogram of those walks is
 *      printed; then every missed pair is tested against the whole list, so
 *      the census states a covering list rather than a single miss count.
 *      Alongside: the sigma-route.  The reflection of the general model sends
 *      (rho, sig) to (9 - sig, 9 - rho), so the branch L+5 of rho is the branch
 *      L+4 of tau = 9 - sig; the census asks whether the three walks of L+4,
 *      read on the arms of tau, serve every pair of the branch.
 *
 *   D. A generator outside Bing's family: a randomised recursive chain
 *      (rpath), whose splitting points are chosen at random and which is kept
 *      only when the thin pair is faithful.
 *
 * Usage: census-batch53 [rand-rounds] [seed] [walk-steps] [crook-cap]
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

/* a recursive chain whose splitting levels are one further in than Bing's: the
 * consolidation goes back to `b - back` and forward to `a + fwd`, which for
 * (back, fwd) = (1, 1) is Bing's own chain and otherwise is not. */
static Path vpath(int a, int b, int back, int fwd) {
  Path p;
  int d = a < b ? b - a : a - b;
  if (d <= 2) {
    p.n = d + 1;
    p.v = (int *)malloc(sizeof(int) * p.n);
    int s = (a <= b) ? 1 : -1;
    for (int u = 0; u < p.n; u++) p.v[u] = a + s * u;
    return p;
  }
  int up = (a < b);
  int mid = up ? b - back : b + back;
  int c = up ? a + fwd : a - fwd;
  if (up && (mid <= a || c >= b || mid <= c)) { mid = b - 1; c = a + 1; }
  if (!up && (mid >= a || c <= b || mid >= c)) { mid = b + 1; c = a - 1; }
  Path p1 = vpath(a, mid, back, fwd), p2 = vpath(mid, c, back, fwd),
       p3 = vpath(c, b, back, fwd);
  p.n = p1.n + p2.n - 1 + p3.n - 1;
  p.v = (int *)malloc(sizeof(int) * p.n);
  memcpy(p.v, p1.v, sizeof(int) * p1.n);
  memcpy(p.v + p1.n, p2.v + 1, sizeof(int) * (p2.n - 1));
  memcpy(p.v + p1.n + p2.n - 1, p3.v + 1, sizeof(int) * (p3.n - 1));
  free(p1.v); free(p2.v); free(p3.v);
  return p;
}

/* the concatenation of two chains, the common endpoint kept once */
static Path cat(Path x, Path y) {
  Path p;
  p.n = x.n + y.n - 1;
  p.v = (int *)malloc(sizeof(int) * p.n);
  memcpy(p.v, x.v, sizeof(int) * x.n);
  memcpy(p.v + x.n, y.v + 1, sizeof(int) * (y.n - 1));
  return p;
}

#define MAXLEV 32
#define MAXN   4096
#define MAXW   96

static int meetTab[MAXLEV][MAXN + 1];

/* IsCrookedIvF (rho, sig), exactly as HPC/Fold/Faithful.lean states it. */
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

/* Valley4 f L */
static int valley4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j + 4 <= d && !ok; j++) if (a[j] >= 5) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* BottomW4 f L */
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

/* TopW5 f L */
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

/* Valley5 f L */
static int valley5(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 4; j + 5 <= d && !ok; j++) if (a[j] >= 6) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* MidW4 f L */
static int midW4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 5) continue;
    int ok = 0;
    for (int j = 1; j + 2 <= d && !ok; j++) if (a[j] <= 3) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* CeilW4 f L */
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

/* LowAt f (L+1) (L+8) */
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

/* the reflected walks, read on the arm itself */
static int foldsLamR(const int *f, int m) {  /* V at L+6: 6 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 6, 1, 8, -1); return folds(f, m, w, wl);
}
static int foldsVeeR(const int *f, int m) {  /* Lambda at L+4: 4 -> 8 -> 1 */
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

/* ---------------- the walk list at the branch L+5 ------------------------ */

/* a walk of at most three turns based within one of 5 */
typedef struct { int st, a, b, c, len; } Walk;

#define MAXLIST 64
static Walk wlist[MAXLIST];
static long wlistHits[MAXLIST];
static int wlistN = 0;

static int walkEq(const Walk *x, int st, int a, int b, int c) {
  return x->st == st && x->a == a && x->b == b && x->c == c;
}

static int noteWalk(int st, int a, int b, int c, int len) {
  for (int q = 0; q < wlistN; q++)
    if (walkEq(&wlist[q], st, a, b, c)) { wlistHits[q]++; return q; }
  if (wlistN >= MAXLIST) return -1;
  wlist[wlistN].st = st; wlist[wlistN].a = a; wlist[wlistN].b = b; wlist[wlistN].c = c;
  wlist[wlistN].len = len; wlistHits[wlistN] = 1;
  return wlistN++;
}

/* the shortest walk of at most three turns, based in [lo, hi], serving both arms */
static int findWalk(const int *g, int mg, const int *t, int mt, int lo, int hi,
                    int *bst, int *ba, int *bb, int *bc) {
  int best = 1 << 30;
  *bst = -1;
  for (int st = lo; st <= hi; st++)
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
            best = wl; *bst = st; *ba = a; *bb = b; *bc = c;
          }
        }
      }
    }
  return (*bst < 0) ? -1 : best;
}

/* the shortest walk of at most four turns, based in [lo, hi], serving both arms */
static int findWalk4(const int *g, int mg, const int *t, int mt, int lo, int hi,
                     int *bst, int *ba, int *bb, int *bc, int *be) {
  int best = 1 << 30;
  *bst = -1;
  for (int st = lo; st <= hi; st++)
    for (int a = 0; a <= 9; a++) {
      if (a == st) continue;
      for (int b = -1; b <= 9; b++) {
        if (b == a) continue;
        for (int c = -1; c <= 9; c++) {
          if (c == b) continue;
          if (b < 0 && c >= 0) continue;
          for (int e = -1; e <= 9; e++) {
            if (e == c) continue;
            if (c < 0 && e >= 0) continue;
            int w[MAXW]; int wl = buildWalk4(w, st, a, b, c, e);
            if (wl < 0 || wl >= best) continue;
            if (folds(g, mg, w, wl) && folds(t, mt, w, wl)) {
              best = wl; *bst = st; *ba = a; *bb = b; *bc = c; *be = e;
            }
          }
        }
      }
    }
  return (*bst < 0) ? -1 : best;
}


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

/* ---- the search: the shortest prefixes of a pair of the branch L+5 that no
 * walk of at most three turns based within one of L+5 serves ---------------- */

static int servedBy3(const int *g, int mg, const int *t, int mt) {
  int st, a, b, c;
  return findWalk(g, mg, t, mt, 4, 6, &st, &a, &b, &c) >= 0;
}

static int bestLen = 1 << 30;

static void tryPair(const int *g0, int mg0, const int *t0, int mt0, const char *tag, int gen,
                    int bp) {
  static int g[MAXN], t[MAXN];
  int mg = mg0 < 1200 ? mg0 : 1200, mt = mt0 < 1200 ? mt0 : 1200;
  for (int d = 0; d < mg; d++) g[d] = g0[d];
  for (int d = 0; d < mt; d++) t[d] = t0[d];
  if (servedBy3(g, mg, t, mt)) return;             /* the truncation is already served */
  /* shrink greedily */
  int changed = 1;
  while (changed) {
    changed = 0;
    while (mg > 1 && !servedBy3(g, mg - 1, t, mt)) { mg--; changed = 1; }
    while (mt > 1 && !servedBy3(g, mg, t, mt - 1)) { mt--; changed = 1; }
  }
  if (mg + mt >= bestLen) return;
  bestLen = mg + mt;
  printf("\n[%s %d] basepoint %d: prefixes %d/%d, no walk of at most three turns serves them\n",
         tag, gen, bp, mg, mt);
  printf("  forward :");  for (int d = 0; d < mg; d++) printf(" %d", g[d]);
  printf("\n  nat16   : 0x"); for (int d = mg - 1; d >= 0; d--) printf("%X", g[d]);
  printf("\n  backward:"); for (int d = 0; d < mt; d++) printf(" %d", t[d]);
  printf("\n  nat16   : 0x"); for (int d = mt - 1; d >= 0; d--) printf("%X", t[d]);
  printf("\n  lowAt G=%d T=%d  crookUp G=%d T=%d  crookDown G=%d T=%d\n",
         lowAt(g, mg), lowAt(t, mt), crookUpArm(g, mg), crookUpArm(t, mt),
         crookDownArm(g, mg), crookDownArm(t, mt));
  { int st, a, b, c, e;
    int l4 = findWalk4(g, mg, t, mt, 4, 6, &st, &a, &b, &c, &e);
    if (l4 < 0) printf("  no walk of at most four turns serves them either\n");
    else printf("  shortest four-turn walk (%d times): %d -> %d -> %d -> %d -> %d\n",
                l4, st, a, b, c, e); }
}

static void scanPairs(int n, const char *tag, int gen) {
  for (int i = 0; i < n; i++) {
    if (rho[i] != 5) continue;
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
    for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
    if (!lowAt(armG, mg) || !lowAt(armT, mt)) continue;
    if ((foldsLamR(armG, mg) && foldsLamR(armT, mt)) ||
        (foldsVeeR(armG, mg) && foldsVeeR(armT, mt))) continue;
    if (foldsW3R(armG, mg) && foldsW3R(armT, mt)) continue;
    if (foldsW4R(armG, mg) && foldsW4R(armT, mt)) continue;
    if (foldsW5R(armG, mg) && foldsW5R(armT, mt)) continue;
    if (servedBy3(armG, mg, armT, mt)) continue;
    tryPair(armG, mg, armT, mt, tag, gen, i);
  }
}

static void runChain(int n, const int *v, long rounds, long walkSteps) {
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  if (crookedGen(rho, sig, n)) scanPairs(n, "thin", 0);

  for (int pk = 1; pk + 1 < n; pk++) {
    if (!(v[pk] > v[pk-1] && v[pk] > v[pk+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    rho[pk] = v[pk] - 1;
    if (!crookedGen(rho, sig, n)) continue;
    scanPairs(n, "shave", pk);
  }
  for (int vl = 1; vl + 1 < n; vl++) {
    if (!(v[vl] < v[vl-1] && v[vl] < v[vl+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    sig[vl] = v[vl] + 1;
    if (!crookedGen(rho, sig, n)) continue;
    scanPairs(n, "fill", vl);
  }
  for (long it = 0; it < rounds; it++) {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) { if (random() % 3 == 0) rho[j] = v[j] - 1; }
      else if (v[j] < v[j-1] && v[j] < v[j+1]) { if (random() % 3 == 0) sig[j] = v[j] + 1; }
    }
    if (!crookedGen(rho, sig, n)) continue;
    scanPairs(n, "mix", (int)it);
  }
  for (long it = 0; it < rounds; it++) {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) { if (random() % 2 == 0) rho[j] = v[j] - 1; }
      else if (v[j] < v[j-1] && v[j] < v[j+1]) { if (random() % 2 == 0) sig[j] = v[j] + 1; }
    }
    if (!crookedGen(rho, sig, n)) continue;
    scanPairs(n, "heavy", (int)it);
  }
  {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) rho[j] = v[j] - 1;
      else if (v[j] < v[j-1] && v[j] < v[j+1]) sig[j] = v[j] + 1;
    }
    if (crookedGen(rho, sig, n)) scanPairs(n, "total", -1);
  }
  {
    static int crho[MAXN], csig[MAXN];
    for (int u = 0; u < n; u++) { crho[u] = v[u]; csig[u] = v[u]; }
    long accepted = 0;
    for (long it = 0; it < walkSteps; it++) {
      int j = 1 + (int)(random() % (n - 2));
      int which = (int)(random() % 2), delta = (random() % 2) ? 1 : -1;
      for (int u = 0; u < n; u++) { rho[u] = crho[u]; sig[u] = csig[u]; }
      if (which == 0) rho[j] += delta; else sig[j] += delta;
      if (rho[j] > sig[j] || sig[j] > rho[j] + 1) continue;
      if (rho[j] < 0 || sig[j] > 9) continue;
      if (!crookedGen(rho, sig, n)) continue;
      accepted++;
      for (int u = 0; u < n; u++) { crho[u] = rho[u]; csig[u] = sig[u]; }
      scanPairs(n, "walk", (int)accepted);
    }
  }
}

int main(int argc, char **argv) {
  long rounds = (argc > 1) ? atol(argv[1]) : 12;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 53u;
  srandom(seed);
  printf("search-batch53: the shortest pair of the branch L+5 that no walk of at most three "
         "turns serves.\nrounds=%ld seed=%u\n", rounds, seed);
  Path p = bpath(0, 9);
  runChain(p.n, p.v, rounds, 80);
  Path q = bpath(9, 0);
  runChain(q.n, q.v, rounds, 80);
  { Path x = bpath(0, 9), y = bpath(9, 0);
    Path r = cat(x, y);
    for (int u = 0; u < r.n; u++) { rho[u] = r.v[u]; sig[u] = r.v[u]; }
    if (crookedGen(rho, sig, r.n)) scanPairs(r.n, "cat-thin", 0);
    free(x.v); free(y.v); free(r.v); }
  free(p.v); free(q.v);
  return 0;
}
