/* Census for batch 42 -- random long members of the faithful model.
 *
 * Same model and same crookedness clause as census-batch42.c, but with an
 * O(1) witness test (per value, the sorted list of indices whose interval
 * contains it, searched by bisection), so sequences of a thousand links can be
 * grown.  A sequence is grown left to right, admissible continuations tried in
 * random order, backtracking on a crookedness violation.  These sequences are
 * arbitrary members of the model, not windows of a Bing chain.
 *
 * For every sequence of span exactly nine and every basepoint of it the two
 * open branches of `s3_span_nine_except` are tested,
 *   branch 4: rho i = L+4, both arms HighAt (L+1) (L+8)
 *   branch 5: rho i = L+5, both arms LowAt  (L+1) (L+8)
 * and each hit is resolved exactly: the least number of turning targets of a
 * zigzag walk onto which both arms fold, and whether the single walk that
 * served the Bing corpus (base L+3, turns L+8, L+1 resp. base L+6, turns L+1,
 * L+8) serves it.
 *
 * Usage: census-batch42c length trials [seed]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef unsigned __int128 u128;

#define LMIN 0
#define HMAX 9
#define MAXN 4000
#define NVAL 12

static int N;
static int rho[MAXN], sig[MAXN];
static int lst[NVAL][MAXN], lcnt[NVAL];     /* indices whose interval holds v */

static void push_index(int j) {
  for (int v = rho[j]; v <= sig[j]; v++) lst[v][lcnt[v]++] = j;
}
static void pop_index(int j) {
  for (int v = rho[j]; v <= sig[j]; v++) lcnt[v]--;
}

/* least index in lst[v] that is > s, or -1 */
static inline int first_after(int v, int s) {
  int lo = 0, hi = lcnt[v];
  while (lo < hi) { int mid = (lo + hi) / 2; if (lst[v][mid] > s) hi = mid; else lo = mid + 1; }
  return lo < lcnt[v] ? lst[v][lo] : -1;
}

/* every crookedness clause with second index t, indices 0..len-1 fixed */
static int crooked_pairs_at(int t, int len) {
  int lo_t = t > 0 ? t - 1 : 0, hi_t = t + 1 < len ? t + 1 : len - 1;
  for (int s = 0; s + 1 < t; s++) {
    int lo_s = s > 0 ? s - 1 : 0, hi_s = s + 1 < len ? s + 1 : len - 1;
    for (int u = lo_s; u <= hi_s; u++)
      for (int h = rho[u]; h <= sig[u]; h++)
        for (int v = lo_t; v <= hi_t; v++)
          for (int k = rho[v]; k <= sig[v]; k++) {
            int d = h - k; if (d < 0) d = -d;
            if (d < 3) continue;
            int a, b;
            if (h < k) { a = k - 1; b = h + 1; } else { a = k + 1; b = h - 1; }
            if (a < 0 || a >= NVAL || b < 0 || b >= NVAL) return 0;
            int r = first_after(a, s);
            if (r < 0 || r >= t) return 0;
            int rp = first_after(b, r);
            if (rp < 0 || rp >= t) return 0;
          }
  }
  return 1;
}

/* ------------------------------------------------------------- conditions */

static int highAt(const int *f, int m, int tl, int th) {
  int seen = 0;
  for (int j = 0; j < m; j++) {
    if (f[j] >= th && !seen) return 0;
    if (f[j] <= tl + 1) seen = 1;
  }
  return 1;
}

static int lowAt(const int *f, int m, int tl, int th) {
  int seenLo = 0, seenHi = 0, seenPair = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= tl && !(seenHi || seenPair)) return 0;
    if (f[d] >= th) seenHi = 1;
    if (seenLo && f[d] >= th - 2) seenPair = 1;
    if (f[d] <= tl + 1) seenLo = 1;
  }
  return 1;
}

/* ---------------------------------------------------------------- folding */

#define MAXW 120
typedef struct { int c[MAXW + 4]; int len; } Walk;

static int build_walk(const int *ts, int k, Walk *w) {
  w->len = 0;
  w->c[w->len++] = ts[0];
  int cur = ts[0];
  for (int j = 1; j <= k; j++) {
    int tgt = ts[j];
    while (cur != tgt) {
      if (w->len >= MAXW) return 0;
      cur += (tgt > cur) ? 1 : -1; w->c[w->len++] = cur;
    }
  }
  return 1;
}

static int folds(const int *f, int m, const Walk *w) {
  u128 one = 1, mask;
  if (abs(f[0] - w->c[0]) > 1) return 0;
  mask = one;
  for (int j = 1; j < m; j++) {
    u128 spread = mask | (mask << 1) | (mask >> 1), nm = 0;
    for (int u = 0; u < w->len; u++) {
      if (!((spread >> u) & 1)) continue;
      if (abs(f[j] - w->c[u]) > 1) continue;
      nm |= one << u;
    }
    mask = nm;
    if (!mask) return 0;
  }
  return 1;
}

static int least_turns(const int *g, int mg, const int *t_, int mt, int kmax, int *out) {
  int ts[8];
  for (int k = 0; k <= kmax; k++)
    for (ts[0] = LMIN; ts[0] <= HMAX; ts[0]++) {
      int lo = LMIN + 1, hi = HMAX - 1, span = hi - lo + 1;
      long total = 1; for (int j = 1; j <= k; j++) total *= span;
      for (long code = 0; code < total; code++) {
        long c = code; int bad = 0;
        for (int j = 1; j <= k; j++) { ts[j] = lo + (int)(c % span); c /= span; }
        for (int j = 1; j <= k && !bad; j++) {
          if (ts[j] == ts[j-1]) bad = 1;
          if (j >= 2 && ((ts[j] > ts[j-1]) == (ts[j-1] > ts[j-2]))) bad = 1;
        }
        if (bad) continue;
        Walk w;
        if (!build_walk(ts, k, &w)) continue;
        if (folds(g, mg, &w) && folds(t_, mt, &w)) {
          if (out) for (int j = 0; j <= k; j++) out[j] = ts[j];
          return k;
        }
      }
    }
  return -1;
}

static int serves_fixed(const int *g, int mg, const int *t_, int mt, const int *ts, int k) {
  Walk w;
  if (!build_walk(ts, k, &w)) return 0;
  return folds(g, mg, &w) && folds(t_, mt, &w);
}

/* ------------------------------------------------------------- statistics */

static long long span9, hits[2], unserved[2], fixedok[2], turnhist[2][8];
static int printed[2];

static void examine(int len) {
  int mn = 99, mx = -1;
  for (int j = 0; j < len; j++) { if (rho[j] < mn) mn = rho[j]; if (rho[j] > mx) mx = rho[j]; }
  if (mx - mn != 9) return;
  span9++;
  int L = mn;
  static int g[MAXN], t_[MAXN];
  for (int i = 0; i < len; i++) {
    int mg = len - i, mt = i + 1;
    for (int j = 0; j < mg; j++) g[j] = rho[i + j];
    for (int j = 0; j < mt; j++) t_[j] = rho[i - j];
    for (int which = 0; which < 2; which++) {
      int hit;
      if (which == 0)
        hit = (rho[i] == L + 4) && highAt(g, mg, L + 1, L + 8) && highAt(t_, mt, L + 1, L + 8);
      else
        hit = (rho[i] == L + 5) && lowAt(g, mg, L + 1, L + 8) && lowAt(t_, mt, L + 1, L + 8);
      if (!hit) continue;
      hits[which]++;
      int fixed4[3] = {L + 3, L + 8, L + 1}, fixed5[3] = {L + 6, L + 1, L + 8};
      if (serves_fixed(g, mg, t_, mt, which ? fixed5 : fixed4, 2)) fixedok[which]++;
      int ts[8];
      int k = least_turns(g, mg, t_, mt, 5, ts);
      if (k < 0) {
        unserved[which]++;
        printf("UNSERVED branch %d len %d base %d:", which ? 5 : 4, len, i);
        for (int j = 0; j < len; j++) printf(" %d", rho[j]);
        printf("\n"); fflush(stdout);
      } else {
        turnhist[which][k]++;
        if (printed[which] < 2) {
          printed[which]++;
          printf("branch %d hit: len %d base %d turns %d walk", which ? 5 : 4, len, i, k);
          for (int j = 0; j <= k; j++) printf(" %d", ts[j]);
          printf("\n"); fflush(stdout);
        }
      }
    }
  }
}

/* ------------------------------------------------------------- the search */

static long long nodes;

static int rgrow(int len) {
  if (++nodes > 200000000LL) return 0;
  if (len >= 3 && !crooked_pairs_at(len - 2, len)) return 0;
  if (len == N) return crooked_pairs_at(len - 1, len);
  int cand[8][2], nc = 0;
  int r0 = rho[len - 1], s0 = sig[len - 1];
  for (int r = r0 - 1; r <= r0 + 1; r++) {
    if (r < LMIN || r > HMAX) continue;
    for (int s = r; s <= r + 1; s++) {
      int mx = s0 > s ? s0 : s, mn = r0 < r ? r0 : r;
      if (mx > mn + 1) continue;
      cand[nc][0] = r; cand[nc][1] = s; nc++;
    }
  }
  for (int a = nc - 1; a > 0; a--) {
    int b = rand() % (a + 1);
    int x = cand[a][0], y = cand[a][1];
    cand[a][0] = cand[b][0]; cand[a][1] = cand[b][1];
    cand[b][0] = x; cand[b][1] = y;
  }
  for (int a = 0; a < nc; a++) {
    rho[len] = cand[a][0]; sig[len] = cand[a][1];
    push_index(len);
    if (rgrow(len + 1)) return 1;
    pop_index(len);
  }
  return 0;
}

int main(int argc, char **argv) {
  N = argc > 1 ? atoi(argv[1]) : 200;
  int trials = argc > 2 ? atoi(argv[2]) : 20;
  unsigned seed = argc > 3 ? (unsigned)atoi(argv[3]) : 1u;
  srand(seed);
  long long made = 0;
  for (int it = 0; it < trials; it++) {
    for (int v = 0; v < NVAL; v++) lcnt[v] = 0;
    nodes = 0;
    rho[0] = rand() % (HMAX + 1); sig[0] = rho[0] + (rand() % 2);
    push_index(0);
    if (rgrow(1)) { made++; examine(N); }
  }
  printf("length %d, trials %d, sequences built: %lld, span nine: %lld\n",
         N, trials, made, span9);
  for (int w = 0; w < 2; w++) {
    printf("branch %d: hits %lld, unserved %lld, served by the fixed walk %lld, histogram:",
           w ? 5 : 4, hits[w], unserved[w], fixedok[w]);
    for (int k = 0; k < 8; k++) if (turnhist[w][k]) printf(" k=%d:%lld", k, turnhist[w][k]);
    printf("\n");
  }
  return 0;
}
