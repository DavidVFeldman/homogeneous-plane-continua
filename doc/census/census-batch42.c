/* Census for batch 42 -- actual crooked sequences at span nine.
 *
 * The corpus is not a chain and not a random sample: it is EVERY sequence of
 * the faithful interval model `IsCrookedIvF` of HPC/Fold/Faithful.lean with
 * rho-values in [0, 9], up to a length given on the command line.  A pair
 * (rho, sigma) is in the model when
 *
 *    rho t <= sigma t <= rho t + 1                                  (width)
 *    max (sigma t, sigma t') <= min (rho t, rho t') + 1   (t' = t+1, adj)
 *
 * and, for every s < t, every h in the union of the intervals of the
 * neighbours of s, every k in the union of the intervals of the neighbours of
 * t with |h - k| >= 3, there are s < r < r' < t with
 *
 *    h < k:  k-1 in I_r  and  h+1 in I_r'
 *    k < h:  k+1 in I_r  and  h-1 in I_r'                     (crookedness)
 *
 * By `realization` (batch 22) every such sequence is the (minIdx, maxIdx)
 * pair of an actual crooked chain, so this corpus is exactly the class of
 * pairs `S3` quantifies over, truncated by length only.
 *
 * Mode 0 (count): how many sequences of each length, and how many have span
 * exactly nine.
 *
 * Mode 1 (branches): among the sequences of span exactly nine, are the two
 * open branches of `s3_span_nine_except` inhabited by an actual basepoint,
 *   L+4 with both arms HighAt (L+1) (L+8),
 *   L+5 with both arms LowAt  (L+1) (L+8),
 * and, when they are, is the basepoint served -- do the two arms fold onto one
 * common zigzag walk -- and with how few turning targets?
 *
 * Usage: census-batch42 mode maxlen
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define LMIN 0
#define HMAX 9
#define MAXN 40

static int N;            /* target length */
static int mode;
static int rho[MAXN], sig[MAXN];

/* ------------------------------------------------------------ crookedness */

/* value v lies in interval of index u */
static inline int inI(int u, int v) { return rho[u] <= v && v <= sig[u]; }

/* check every crookedness clause with second index exactly t, given that
 * indices 0..len-1 are fixed and t+1 <= len-1 (so reach(t) is known). */
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
            int a, b;                    /* need I_r ni a, then I_r' ni b */
            if (h < k) { a = k - 1; b = h + 1; }
            else       { a = k + 1; b = h - 1; }
            int ok = 0;
            for (int r = s + 1; r < t && !ok; r++) {
              if (!inI(r, a)) continue;
              for (int rp = r + 1; rp < t; rp++)
                if (inI(rp, b)) { ok = 1; break; }
            }
            if (!ok) return 0;
          }
  }
  return 1;
}

/* ------------------------------------------------------------ arm folding */

/* zigzag walk: base centre ts[0], then k turning targets, one level per step */
typedef struct { int c[128]; int len; } Walk;

static void build_walk(const int *ts, int k, Walk *w) {
  w->len = 0;
  w->c[w->len++] = ts[0];
  int cur = ts[0];
  for (int j = 1; j <= k; j++) {
    int tgt = ts[j];
    while (cur != tgt) { cur += (tgt > cur) ? 1 : -1; w->c[w->len++] = cur; }
  }
}

/* reachable set of walk-times for folding f[0..m-1] starting at time 0.
 * returns 1 if some assignment exists */
static int folds(const int *f, int m, const Walk *w) {
  uint64_t mask[2] = {0, 0};
  if (w->len > 128) return 0;
  /* time 0 must be assigned to walk time 0 */
  if (abs(f[0] - w->c[0]) > 1) return 0;
  mask[0] = 1;
  for (int j = 1; j < m; j++) {
    uint64_t nm[2] = {0, 0};
    for (int u = 0; u < w->len; u++) {
      int bit = (u < 64) ? ((mask[0] >> u) & 1) : ((mask[1] >> (u - 64)) & 1);
      if (!bit) continue;
      for (int d = -1; d <= 1; d++) {
        int u2 = u + d;
        if (u2 < 0 || u2 >= w->len) continue;
        if (abs(f[j] - w->c[u2]) > 1) continue;
        if (u2 < 64) nm[0] |= (uint64_t)1 << u2; else nm[1] |= (uint64_t)1 << (u2 - 64);
      }
    }
    mask[0] = nm[0]; mask[1] = nm[1];
    if (!mask[0] && !mask[1]) return 0;
  }
  return 1;
}

/* least number of turning targets of a zigzag walk serving both arms; -1 if
 * none up to kmax turning targets. */
static int least_turns(const int *g, int mg, const int *t_, int mt, int kmax) {
  int ts[8];
  for (int k = 0; k <= kmax; k++) {
    /* ts[0] in [LMIN, HMAX], turning targets alternate direction */
    for (ts[0] = LMIN; ts[0] <= HMAX; ts[0]++) {
      int idx[8]; for (int j = 0; j <= k; j++) idx[j] = 0;
      /* enumerate turning targets in [LMIN+1, HMAX-1] with alternation */
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
        Walk w; build_walk(ts, k, &w);
        if (w.len > 128) continue;
        if (folds(g, mg, &w) && folds(t_, mt, &w)) return k;
      }
      (void)idx;
    }
  }
  return -1;
}

/* ------------------------------------------------------------- conditions */

/* HighAt f tl th : every time f reaches >= th, some earlier time has f <= tl+1 */
static int highAt(const int *f, int m, int tl, int th) {
  int seen = 0;
  for (int j = 0; j < m; j++) {
    if (f[j] >= th && !seen) return 0;
    if (f[j] <= tl + 1) seen = 1;
  }
  return 1;
}

/* LowAt f tl th : every time f drops to <= tl, either an earlier time has
 * f >= th, or two earlier times j < j' with f j <= tl+1 and f j' >= th-2. */
static int lowAt(const int *f, int m, int tl, int th) {
  for (int d = 0; d < m; d++) {
    if (f[d] > tl) continue;
    int ok = 0;
    for (int j = 0; j < d && !ok; j++) if (f[j] >= th) ok = 1;
    for (int j = 0; j < d && !ok; j++) {
      if (f[j] > tl + 1) continue;
      for (int jp = j + 1; jp < d; jp++) if (f[jp] >= th - 2) { ok = 1; break; }
    }
    if (!ok) return 0;
  }
  return 1;
}

/* ------------------------------------------------------------- statistics */

static long long count_len[MAXN + 1];
static long long count_span9;
static long long hits4, hits5, unserved;
static long long turnhist[8];
static int printed4, printed5;

static void report_hit(int len, int i, int which) {
  int g[MAXN], t_[MAXN];
  int mg = len - i, mt = i + 1;
  for (int j = 0; j < mg; j++) g[j] = rho[i + j];
  for (int j = 0; j < mt; j++) t_[j] = rho[i - j];
  int k = least_turns(g, mg, t_, mt, 5);
  if (k < 0) { unserved++;
    printf("UNSERVED branch %d len %d base %d:", which, len, i);
    for (int j = 0; j < len; j++) printf(" %d%s", rho[j], sig[j] > rho[j] ? "+" : "");
    printf("\n"); fflush(stdout);
  } else {
    if (k < 8) turnhist[k]++;
    int *pr = which == 4 ? &printed4 : &printed5;
    if (*pr < 3) {
      (*pr)++;
      printf("branch %d inhabited, len %d base %d turns %d:", which, len, i, k);
      for (int j = 0; j < len; j++) printf(" %d%s", rho[j], sig[j] > rho[j] ? "+" : "");
      printf("\n"); fflush(stdout);
    }
  }
}

static void examine(int len) {
  int mn = 99, mx = -1;
  for (int j = 0; j < len; j++) { if (rho[j] < mn) mn = rho[j]; if (rho[j] > mx) mx = rho[j]; }
  if (mx - mn != 9) return;
  count_span9++;
  if (mode == 0) return;
  int L = mn;
  for (int i = 0; i < len; i++) {
    int g[MAXN], t_[MAXN];
    int mg = len - i, mt = i + 1;
    for (int j = 0; j < mg; j++) g[j] = rho[i + j];
    for (int j = 0; j < mt; j++) t_[j] = rho[i - j];
    if (rho[i] == L + 4 && highAt(g, mg, L + 1, L + 8) && highAt(t_, mt, L + 1, L + 8)) {
      hits4++; report_hit(len, i, 4);
    }
    if (rho[i] == L + 5 && lowAt(g, mg, L + 1, L + 8) && lowAt(t_, mt, L + 1, L + 8)) {
      hits5++; report_hit(len, i, 5);
    }
  }
}

/* --------------------------------------------------------------- the search */

static void dfs(int len) {
  count_len[len]++;
  if (len >= 3) { /* pairs with second index len-2 are now determined */
    if (!crooked_pairs_at(len - 2, len)) return;
  }
  /* a complete sequence: check the last pair too */
  if (len >= 2 && crooked_pairs_at(len - 1, len)) examine(len);
  if (len == N) return;
  int r0 = rho[len - 1], s0 = sig[len - 1];
  for (int r = r0 - 1; r <= r0 + 1; r++) {
    if (r < LMIN || r > HMAX) continue;
    for (int s = r; s <= r + 1; s++) {
      int mx = s0 > s ? s0 : s, mn = r0 < r ? r0 : r;
      if (mx > mn + 1) continue;
      rho[len] = r; sig[len] = s;
      dfs(len + 1);
    }
  }
}

/* --------------------------------------------- mode 2: randomised sampling
 *
 * A random faithful crooked sequence of length N is grown left to right: at
 * each step the admissible continuations are tried in random order, and the
 * crookedness prune is the same one the exhaustive search uses.  On a dead end
 * the search backtracks.  The sequences produced are not subchains of a Bing
 * chain; they are arbitrary members of the model.
 */

static int rgrow(int len) {
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
    int t0 = cand[a][0], t1 = cand[a][1];
    cand[a][0] = cand[b][0]; cand[a][1] = cand[b][1];
    cand[b][0] = t0; cand[b][1] = t1;
  }
  for (int a = 0; a < nc; a++) {
    rho[len] = cand[a][0]; sig[len] = cand[a][1];
    if (rgrow(len + 1)) return 1;
  }
  return 0;
}

int main(int argc, char **argv) {
  mode = argc > 1 ? atoi(argv[1]) : 0;
  N = argc > 2 ? atoi(argv[2]) : 16;
  if (mode == 2) {
    int trials = argc > 3 ? atoi(argv[3]) : 1000;
    unsigned seed = argc > 4 ? (unsigned)atoi(argv[4]) : 1u;
    srand(seed);
    long long made = 0;
    for (int it = 0; it < trials; it++) {
      rho[0] = rand() % (HMAX + 1); sig[0] = rho[0] + (rand() % 2);
      if (sig[0] > HMAX + 1) sig[0] = rho[0];
      if (rgrow(1)) { made++; examine(N); }
    }
    printf("random sequences of length %d built: %lld\n", N, made);
    printf("span-nine among them: %lld\n", count_span9);
    printf("branch L+4 inhabited: %lld\n", hits4);
    printf("branch L+5 inhabited: %lld\n", hits5);
    printf("unserved (no zigzag walk with <= 5 turning targets): %lld\n", unserved);
    printf("least-turn histogram:");
    for (int k = 0; k < 8; k++) if (turnhist[k]) printf(" k=%d:%lld", k, turnhist[k]);
    printf("\n");
    return 0;
  }
  for (int r = LMIN; r <= HMAX; r++)
    for (int s = r; s <= r + 1; s++) {
      rho[0] = r; sig[0] = s;
      dfs(1);
    }
  printf("== counts by length (prefixes surviving the crookedness prune) ==\n");
  for (int n = 1; n <= N; n++) if (count_len[n]) printf("  len %2d : %lld\n", n, count_len[n]);
  printf("span-nine complete sequences examined: %lld\n", count_span9);
  if (mode) {
    printf("branch L+4 (both arms HighAt (L+1) (L+8)) inhabited: %lld times\n", hits4);
    printf("branch L+5 (both arms LowAt  (L+1) (L+8)) inhabited: %lld times\n", hits5);
    printf("unserved (no zigzag walk with <= 5 turning targets): %lld\n", unserved);
    printf("least-turn histogram:");
    for (int k = 0; k < 8; k++) if (turnhist[k]) printf(" k=%d:%lld", k, turnhist[k]);
    printf("\n");
  }
  return 0;
}
