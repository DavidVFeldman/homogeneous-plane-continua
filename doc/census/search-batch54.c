/* search-batch54.c -- batch 54.  A counterexample hunt over the general model,
 * with generators that are not chains of Bing's family.
 *
 * Every census of this repository so far has drawn its faithful pairs from
 * Bing's recursive chain `bing a b` and its shavings, fills and mixtures.  The
 * work items of HPC/Fold/Mixed.lean and HPC/Fold/CrossCeil.lean, however,
 * quantify over *every* pair (rho, sig) with IsCrookedIvF, the band, the
 * basepoint and the branch hypothesis -- and by the realization theorem of
 * HPC/Fold/Faithful.lean every such pair is the (minIdx, maxIdx) pair of an
 * actual crooked chain.  So a pair produced by any generator whatever, as long
 * as it satisfies IsCrookedIvF, decides the items.
 *
 * Three generators are tried.
 *
 *   A. Random concatenations of Bing blocks: levels a0, a1, ..., ak drawn
 *      uniformly from 0..9 and the blocks `bing a_j a_{j+1}` laid end to end,
 *      the common endpoint kept once.  About one in six of these is faithful,
 *      and the faithful ones are chains no census of this repository has seen:
 *      they are not `bing a b` for any a, b, and their level profile is
 *      whatever the draw produced.
 *
 *   B. Random recursive chains: the consolidation levels of the recursion are
 *      drawn per call rather than fixed at `b - 1` and `a + 1`.
 *
 *   C. A free depth-first random walk that extends (rho, sig) one link at a
 *      time and rejects any extension violating the model.  The clause is
 *      checked incrementally and exactly: appending a link can only create
 *      violations of pairs (s, t) with t among the last two indices, because
 *      the trigger levels of t are read at t-1, t, t+1 and the two witnesses
 *      are required strictly between s and t; a violated pair is never
 *      repaired later.
 *
 * On top of every faithful thin sequence the program also runs the single
 * shavings, the single fills, the total mixture and a random faithful
 * perturbation walk, so the corpus contains non-thin pairs as well.
 *
 * Every pair is scanned at every basepoint, exactly as the Lean statements
 * read -- every predicate named in a statement is evaluated by its own
 * definition, none by a proxy -- for a counterexample to
 *
 *   T1  cross_ceil_sentence     (HPC/Fold/CrossCeil.lean)
 *   T2  cross_valley_profile    (HPC/Fold/Mixed.lean)
 *   T3  unserved_three_walks    (HPC/Fold/Mixed.lean)
 *
 * and, at every basepoint of the branch L + 5, for a pair served by none of
 * the three reflected walks.  A hit is printed in full.
 *
 * Usage: search-batch54 [rounds] [seed] [walk-steps]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 4096
#define MAXW 96
#define MAXLEV 32

static int rho[MAXN], sig[MAXN];
static int meetTab[MAXLEV][MAXN + 1];

/* ---------------- the model, exactly as IsCrookedIvF reads it ------------- */

static int trigLevels(int t, int n, int *out) {
  int nh = 0;
  for (int e = -1; e <= 1; e++) {
    int u = t + e;
    if (u < 0 || u >= n) continue;
    for (int l = rho[u]; l <= sig[u]; l++) {
      int seen = 0;
      for (int q = 0; q < nh; q++) if (out[q] == l) seen = 1;
      if (!seen) out[nh++] = l;
    }
  }
  return nh;
}

static int meetFrom(int l, int from, int n) {
  if (l < 0 || l >= MAXLEV) return n;
  for (int j = from; j < n; j++) if (rho[j] <= l && l <= sig[j]) return j;
  return n;
}

static int crookedPair(int s, int t, int n) {
  int hs[8], ks[8];
  int nh = trigLevels(s, n, hs), nk = trigLevels(t, n, ks);
  for (int a = 0; a < nh; a++)
    for (int b = 0; b < nk; b++) {
      int h = hs[a], k = ks[b];
      int diff = h - k; if (diff < 0) diff = -diff;
      if (diff < 3) continue;
      int r1 = (h < k) ? k - 1 : k + 1, r2 = (h < k) ? h + 1 : h - 1;
      int p1 = meetFrom(r1, s + 1, n);
      if (p1 >= t) return 0;
      int p2 = meetFrom(r2, p1 + 1, n);
      if (p2 >= t) return 0;
    }
  return 1;
}

/* the whole model, with the meeting table -- the test of census-batch53.c */
static int faithful(int n) {
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
    int hs[8]; int nh = trigLevels(s, n, hs);
    for (int t = s + 1; t < n; t++) {
      int ks[8]; int nk = trigLevels(t, n, ks);
      for (int a = 0; a < nh; a++) for (int b = 0; b < nk; b++) {
        int h = hs[a], k = ks[b];
        int diff = h - k; if (diff < 0) diff = -diff;
        if (diff < 3) continue;
        int r1 = (h < k) ? k - 1 : k + 1, r2 = (h < k) ? h + 1 : h - 1;
        if (r1 < 0 || r1 >= MAXLEV || r2 < 0 || r2 >= MAXLEV) continue;
        int p1 = meetTab[r1][s + 1];
        if (p1 >= t) return 0;
        int p2 = meetTab[r2][p1 + 1];
        if (p2 >= t) return 0;
      }
    }
  }
  return 1;
}

/* ---------------- the generators ----------------------------------------- */

/* Bing's block a -> b, built with malloc as in census-batch53.c */
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

static int bingBlock(int *v, int a, int b) {
  Path p = bpath(a, b);
  int n = p.n;
  memcpy(v, p.v, sizeof(int) * n);
  free(p.v);
  return n;
}

/* a recursive block whose consolidation levels are drawn per call */
static int randBlock(int *v, int a, int b) {
  int d = a < b ? b - a : a - b;
  if (d <= 2) {
    int s = (a <= b) ? 1 : -1;
    for (int u = 0; u <= d; u++) v[u] = a + s * u;
    return d + 1;
  }
  int up = (a < b);
  int back = 1 + (int)(random() % 2), fwd = 1 + (int)(random() % 2);
  int mid = up ? b - back : b + back;
  int c = up ? a + fwd : a - fwd;
  if (up && (mid <= a || c >= b || mid <= c)) { mid = b - 1; c = a + 1; }
  if (!up && (mid >= a || c <= b || mid >= c)) { mid = b + 1; c = a - 1; }
  int t1[MAXN], t2[MAXN], t3[MAXN];
  int n1 = randBlock(t1, a, mid), n2 = randBlock(t2, mid, c), n3 = randBlock(t3, c, b);
  memcpy(v, t1, sizeof(int) * n1);
  memcpy(v + n1, t2 + 1, sizeof(int) * (n2 - 1));
  memcpy(v + n1 + n2 - 1, t3 + 1, sizeof(int) * (n3 - 1));
  return n1 + n2 - 1 + n3 - 1;
}

/* generator C: a free depth-first random walk over the model */
typedef struct { int r, s; } Cand;
static int freeWalk(int n, int fillPct, long budget) {
  static Cand cand[MAXN][6];
  static int ncand[MAXN], next[MAXN];
  int m = 1;
  rho[0] = random() % 10; sig[0] = rho[0];
  ncand[0] = 0; next[0] = 0;
  long steps = 0;
  while (m < n) {
    if (steps++ > budget) return 0;
    if (next[m] >= ncand[m]) {
      if (ncand[m] == 0) {
        int k = 0, base = rho[m-1];
        int order[3] = {-1, 0, 1};
        for (int q = 2; q > 0; q--) { int j = random() % (q + 1);
          int tmp = order[q]; order[q] = order[j]; order[j] = tmp; }
        for (int q = 0; q < 3; q++) {
          int r = base + order[q];
          if (r < 0 || r > 9) continue;
          int wide = ((random() % 100) < fillPct);
          for (int w = 0; w < 2; w++) {
            int s = (w == 0) ? (wide ? r + 1 : r) : (wide ? r : r + 1);
            if (s > 9) continue;
            int mx = sig[m-1] > s ? sig[m-1] : s;
            int mn = rho[m-1] < r ? rho[m-1] : r;
            if (mx > mn + 1) continue;
            cand[m][k].r = r; cand[m][k].s = s; k++;
          }
        }
        ncand[m] = k; next[m] = 0;
      }
      if (next[m] >= ncand[m]) {
        ncand[m] = 0; next[m] = 0;
        m--;
        if (m < 1) return 0;
        continue;
      }
    }
    int q = next[m]++;
    rho[m] = cand[m][q].r; sig[m] = cand[m][q].s;
    int ok = 1;
    for (int t = m; t >= m - 1 && t >= 1 && ok; t--)
      for (int s = 0; s < t && ok; s++)
        if (!crookedPair(s, t, m + 1)) ok = 0;
    if (!ok) continue;
    m++;
    ncand[m] = 0; next[m] = 0;
  }
  return 1;
}

/* ---------------- the predicates, as the Lean definitions read them ------- */

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

static int armG[MAXN], armT[MAXN];

static int highAt(const int *f, int m) {
  int seenLow = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !seenLow) return 0;
    if (f[d] <= 2) seenLow = 1;
  }
  return 1;
}
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
static int leg3Valley(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j + 5 <= d && !ok; j++) if (a[j] >= 5) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}
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
static int valley5(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 4; j + 5 <= d && !ok; j++) if (a[j] >= 6) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}
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
static int midW4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 5) continue;
    int ok = 0;
    for (int j = 1; j + 2 <= d && !ok; j++) if (a[j] <= 3) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}
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

static int foldsLam(const int *f, int m) { int w[MAXW]; int l = buildWalk(w, 3, 8, 1, -1); return folds(f, m, w, l); }
static int foldsVee(const int *f, int m) { int w[MAXW]; int l = buildWalk(w, 5, 1, 8, -1); return folds(f, m, w, l); }
static int foldsW3 (const int *f, int m) { int w[MAXW]; int l = buildWalk(w, 3, 6, 1, 8);  return folds(f, m, w, l); }
static int foldsW4 (const int *f, int m) { int w[MAXW]; int l = buildWalk(w, 3, 2, 8, 1);  return folds(f, m, w, l); }
static int foldsW5 (const int *f, int m) { int w[MAXW]; int l = buildWalk(w, 3, 7, 1, 8);  return folds(f, m, w, l); }
static int foldsLamR(const int *f, int m){ int w[MAXW]; int l = buildWalk(w, 6, 1, 8, -1); return folds(f, m, w, l); }
static int foldsVeeR(const int *f, int m){ int w[MAXW]; int l = buildWalk(w, 4, 8, 1, -1); return folds(f, m, w, l); }
static int foldsW3R(const int *f, int m) { int w[MAXW]; int l = buildWalk(w, 6, 3, 8, 1);  return folds(f, m, w, l); }
static int foldsW4R(const int *f, int m) { int w[MAXW]; int l = buildWalk(w, 6, 7, 1, 8);  return folds(f, m, w, l); }
static int foldsW5R(const int *f, int m) { int w[MAXW]; int l = buildWalk(w, 6, 2, 8, 1);  return folds(f, m, w, l); }

/* ---------------- the scan ----------------------------------------------- */

static long nPairs, nLinks, nNonThin, nSkipEnds;
static long nBase4, nBase5, nUnserved4, nUnserved5;
static long hitT1, hitT2, hitT3, hitT5;
static long resValley, resCeilPeak, resCeilHigh, ceilCase, ceilLamFree;
static FILE *out;

static void dump(const char *what, int n, int i) {
  if (!out) return;
  fprintf(out, "%s at basepoint %d of a faithful pair of %d links\n", what, i, n);
  fprintf(out, "  rho:");
  for (int u = 0; u < n; u++) fprintf(out, " %d", rho[u]);
  fprintf(out, "\n  sig:");
  for (int u = 0; u < n; u++) fprintf(out, " %d", sig[u]);
  fprintf(out, "\n");
  fflush(out);
}

static void scan(int n) {
  int attains0 = 0, attains9 = 0;
  nPairs++; nLinks += n;
  for (int u = 0; u < n; u++) {
    if (sig[u] != rho[u]) nNonThin++;
    if (rho[u] == 0) attains0 = 1;
    if (rho[u] == 9) attains9 = 1;
  }
  if (!attains0 || !attains9) { nSkipEnds++; return; }   /* hLat and hHat */
  for (int i = 0; i < n; i++) {
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
    for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
    if (rho[i] == 4) {
      if (!highAt(armG, mg) || !highAt(armT, mt)) continue;
      nBase4++;
      int vG = leg3Valley(armG, mg), vT = leg3Valley(armT, mt);
      int cG = leg3Ceil(armG, mg), cT = leg3Ceil(armT, mt);
      int flG = foldsLam(armG, mg), flT = foldsLam(armT, mt);
      int fvG = foldsVee(armG, mg), fvT = foldsVee(armT, mt);
      int lam = flG && flT, vee = fvG && fvT;
      {
        int off[4] = {-3, -2, 2, 3};
        for (int q = 0; q < 4; q++) {
          int u = i + off[q]; if (u < 0 || u >= n) continue;
          if (rho[u] == 2) { resValley++; break; }
        }
        for (int q = 0; q < 4; q++) {
          int u = i + off[q]; if (u < 0 || u >= n) continue;
          if (rho[u] >= 6) { resCeilPeak++; break; }
        }
        int off2[2] = {-4, 4};
        for (int q = 0; q < 2; q++) {
          int u = i + off2[q]; if (u < 0 || u >= n) continue;
          if (rho[u] >= 7) { resCeilHigh++; break; }
        }
      }
      if ((!vG || !vT) && !vee) {
        hitT2++;
        printf("  *** cross_valley_profile FAILS: basepoint %d (Leg3Valley G=%d T=%d; "
               "vee G=%d T=%d)\n", i, vG, vT, fvG, fvT);
        dump("T2 cross_valley_profile", n, i);
      }
      if (!cG || !cT) {
        ceilCase++;
        if (!lam) {
          ceilLamFree++;
          int m4 = midW4(armG, mg) && bottomW4(armG, mg) && midW4(armT, mt) && bottomW4(armT, mt);
          int t5 = valley5(armG, mg) && topW5(armG, mg) && valley5(armT, mt) && topW5(armT, mt);
          if (!m4 && !t5) {
            hitT1++;
            printf("  *** cross_ceil_sentence FAILS: basepoint %d (Leg3Ceil G=%d T=%d; "
                   "lam G=%d T=%d)\n", i, cG, cT, flG, flT);
            dump("T1 cross_ceil_sentence", n, i);
          }
        }
      }
      if (!lam && !vee) {
        nUnserved4++;
        int s3 = foldsW3(armG, mg) && foldsW3(armT, mt);
        int s4 = foldsW4(armG, mg) && foldsW4(armT, mt);
        int s5 = foldsW5(armG, mg) && foldsW5(armT, mt);
        if (!s3 && !s4 && !s5) {
          hitT3++;
          printf("  *** unserved_three_walks FAILS: basepoint %d\n", i);
          dump("T3 unserved_three_walks", n, i);
        }
      }
    } else if (rho[i] == 5) {
      if (!lowAt(armG, mg) || !lowAt(armT, mt)) continue;
      nBase5++;
      int lam = foldsLamR(armG, mg) && foldsLamR(armT, mt);
      int vee = foldsVeeR(armG, mg) && foldsVeeR(armT, mt);
      if (lam || vee) continue;
      nUnserved5++;
      int s3 = foldsW3R(armG, mg) && foldsW3R(armT, mt);
      int s4 = foldsW4R(armG, mg) && foldsW4R(armT, mt);
      int s5 = foldsW5R(armG, mg) && foldsW5R(armT, mt);
      if (!s3 && !s4 && !s5) {
        hitT5++;
        if (hitT5 <= 10) {
          printf("  *** the branch L+5: no reflected walk serves basepoint %d\n", i);
          dump("L+5 unserved by the three reflected walks", n, i);
        }
      }
    }
  }
}

/* the thin sequence in v of n links, and the non-thin pairs over it */
static void runSeq(int n, const int *v, long walkSteps) {
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  if (!faithful(n)) return;
  scan(n);
  for (int pk = 1; pk + 1 < n; pk++) {
    if (!(v[pk] > v[pk-1] && v[pk] > v[pk+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    rho[pk] = v[pk] - 1;
    if (faithful(n)) scan(n);
  }
  for (int vl = 1; vl + 1 < n; vl++) {
    if (!(v[vl] < v[vl-1] && v[vl] < v[vl+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    sig[vl] = v[vl] + 1;
    if (faithful(n)) scan(n);
  }
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  for (int j = 1; j + 1 < n; j++) {
    if (v[j] > v[j-1] && v[j] > v[j+1]) rho[j] = v[j] - 1;
    else if (v[j] < v[j-1] && v[j] < v[j+1]) sig[j] = v[j] + 1;
  }
  if (faithful(n)) scan(n);
  {
    static int crho[MAXN], csig[MAXN];
    for (int u = 0; u < n; u++) { crho[u] = v[u]; csig[u] = v[u]; }
    for (long it = 0; it < walkSteps; it++) {
      int j = 1 + (int)(random() % (n - 2));
      int which = (int)(random() % 2), delta = (random() % 2) ? 1 : -1;
      for (int u = 0; u < n; u++) { rho[u] = crho[u]; sig[u] = csig[u]; }
      if (which == 0) rho[j] += delta; else sig[j] += delta;
      if (rho[j] > sig[j] || sig[j] > rho[j] + 1) continue;
      if (rho[j] < 0 || sig[j] > 9) continue;
      if (!faithful(n)) continue;
      for (int u = 0; u < n; u++) { crho[u] = rho[u]; csig[u] = sig[u]; }
      scan(n);
    }
  }
}

int main(int argc, char **argv) {
  long rounds = (argc > 1) ? atol(argv[1]) : 60;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 54u;
  long walkSteps = (argc > 3) ? atol(argv[3]) : 60;
  srandom(seed);
  out = fopen("search-batch54-hits.txt", "w");
  printf("search-batch54: a counterexample hunt over faithful pairs outside Bing's family.\n");
  printf("rounds=%ld seed=%u walk-steps=%ld\n\n", rounds, seed, walkSteps);

  /* generator A: random concatenations of Bing blocks */
  long triedA = 0, madeA = 0;
  {
    static int v[MAXN], blk[MAXN];
    for (long it = 0; it < rounds; it++) {
      int nb = 2 + (int)(random() % 4), n = 0, cur = (int)(random() % 10), first = 1;
      for (int b = 0; b < nb; b++) {
        int nx; do { nx = (int)(random() % 10); } while (nx == cur);
        int ln = bingBlock(blk, cur, nx);
        if (n + ln >= 1200) break;
        if (first) { memcpy(v, blk, sizeof(int) * ln); n = ln; first = 0; }
        else { memcpy(v + n, blk + 1, sizeof(int) * (ln - 1)); n += ln - 1; }
        cur = nx;
      }
      if (n < 20) continue;
      triedA++;
      for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
      if (!faithful(n)) continue;
      madeA++;
      runSeq(n, v, walkSteps);
    }
  }
  printf("generator A (random concatenations of Bing blocks): %ld faithful of %ld drawn\n",
         madeA, triedA);

  /* generator B: random recursive chains */
  long triedB = 0, madeB = 0;
  {
    static int v[MAXN];
    for (long it = 0; it < rounds; it++) {
      int a = (int)(random() % 10), b; do { b = (int)(random() % 10); } while (b == a);
      int n = randBlock(v, a, b);
      if (n < 20 || n >= 1200) continue;
      triedB++;
      for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
      if (!faithful(n)) continue;
      madeB++;
      runSeq(n, v, walkSteps);
    }
  }
  printf("generator B (random recursive chains): %ld faithful of %ld drawn\n", madeB, triedB);

  /* generator C: the free depth-first walk */
  long triedC = 0, madeC = 0; int minLev = 99, maxLev = -1;
  {
    for (long it = 0; it < rounds; it++) {
      triedC++;
      if (!freeWalk(200, 8, 400000L)) continue;
      if (!faithful(200)) continue;
      madeC++;
      for (int u = 0; u < 200; u++) {
        if (rho[u] < minLev) minLev = rho[u];
        if (sig[u] > maxLev) maxLev = sig[u];
      }
      scan(200);
    }
  }
  printf("generator C (free depth-first walks of 200 links): %ld produced of %ld tried; "
         "levels visited %d..%d\n", madeC, triedC, minLev, maxLev);

  printf("\nfaithful pairs scanned: %ld; links %ld, non-thin %ld (%.5f); pairs skipped for not "
         "attaining both ends: %ld\n", nPairs, nLinks, nNonThin,
         nLinks ? (double)nNonThin / (double)nLinks : 0.0, nSkipEnds);
  printf("branch L+4: basepoints %ld, unserved %ld; branch L+5: basepoints %ld, unserved %ld\n",
         nBase4, nUnserved4, nBase5, nUnserved5);
  printf("the ceiling configuration: an arm fails Leg3Ceil %ld times, of those the pair misses "
         "the Lambda-walk %ld times\n", ceilCase, ceilLamFree);
  printf("residues seen at branch basepoints: ValleyResidual %ld, CeilPeakResidual %ld, "
         "CeilHighResidual %ld\n", resValley, resCeilPeak, resCeilHigh);
  printf("COUNTEREXAMPLES: cross_ceil_sentence %ld, cross_valley_profile %ld, "
         "unserved_three_walks %ld; branch L+5 served by none of the three reflected walks %ld\n",
         hitT1, hitT2, hitT3, hitT5);
  if (out) fclose(out);
  return 0;
}
