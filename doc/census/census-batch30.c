/* census-batch30.c — Bing 1948 Theorem 7 (minimality), batch 30.
 *
 * Three questions.
 *
 * 1. Minimality, exhaustively at small span.  Over *all* faithful crooked sequences
 *    (rho, sig) in the model of HPC/Fold/Faithful.lean — sig t in {rho t, rho t + 1},
 *    the adjacency clause max(sig t, sig t') <= min(rho t, rho t') + 1 for neighbours,
 *    and the crookedness clause with forced-meeting witnesses — with rho confined to
 *    [0, span] and both ends attained, find the shortest one, by iterative deepening.
 *    Predicted: z 3 = 6, z 4 = 13, z 5 = 30.
 *
 * 2. The timing bound on Bing's own chains: on bingPath(0, n) for n = 4..8, and on
 *    random contiguous subchains of them, every pair of indices at level distance
 *    d >= 3 is at least z d - 1 apart.
 *
 * 3. isCrookedIvF_restrict: every contiguous stretch of a faithful crooked sequence
 *    is itself faithful and crooked (checked on bingPath(0, n) stretches and on the
 *    witnesses found by the search of part 1).
 *
 * Build: cc -O2 -o census-batch30 census-batch30.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 4096

/* ---------- the decidable form of IsCrookedIvF on a concrete sequence ---------- */

static int RHO[MAXN], SIG[MAXN];

static inline int cov(const int *rho, const int *sig, int r, int x) {
  return rho[r] <= x && x <= sig[r];
}

/* width and adjacency */
static int thin_ok(const int *rho, const int *sig, int m) {
  for (int t = 0; t < m; t++)
    if (!(rho[t] <= sig[t] && sig[t] <= rho[t] + 1)) return 0;
  for (int t = 0; t + 1 < m; t++) {
    int a = sig[t] > sig[t + 1] ? sig[t] : sig[t + 1];
    int b = rho[t] < rho[t + 1] ? rho[t] : rho[t + 1];
    if (a > b + 1) return 0;
  }
  return 1;
}

/* the crookedness clause, over every pair s < t of the m available indices, with
 * forced-meeting witnesses u within one of s and v within one of t.  Exact when the
 * sequence has length m; a sound prune when it is a prefix of a longer sequence. */
static int crooked_ok(const int *rho, const int *sig, int m) {
  for (int s = 0; s < m; s++)
    for (int t = s + 1; t < m; t++)
      for (int u = (s > 0 ? s - 1 : 0); u <= s + 1 && u < m; u++)
        for (int v = (t > 0 ? t - 1 : 0); v <= t + 1 && v < m; v++)
          for (int bh = 0; bh < 2; bh++)
            for (int bk = 0; bk < 2; bk++) {
              int h = bh ? sig[u] : rho[u];
              int k = bk ? sig[v] : rho[v];
              int diff = h - k < 0 ? k - h : h - k;
              if (diff < 3) continue;
              int ok = 0;
              for (int r = s + 1; r < t && !ok; r++)
                for (int rp = r + 1; rp < t && !ok; rp++) {
                  if (h < k) {
                    if (cov(rho, sig, r, k - 1) && cov(rho, sig, rp, h + 1)) ok = 1;
                  } else {
                    if (cov(rho, sig, r, k + 1) && cov(rho, sig, rp, h - 1)) ok = 1;
                  }
                }
              if (!ok) return 0;
            }
  return 1;
}

static int faithful_ok(const int *rho, const int *sig, int m) {
  return thin_ok(rho, sig, m) && crooked_ok(rho, sig, m);
}

/* ---------- Bing's recurrence ---------- */

static long long zval[64];
static void init_z(void) {
  zval[0] = 1; zval[1] = 2; zval[2] = 3;
  for (int i = 3; i < 64; i++) zval[i] = 2 * zval[i - 1] + zval[i - 2] - 2;
}

/* ---------- part 1: iterative deepening for the shortest faithful crooked span-d ---------- */

static int SPAN, DEPTH_CAP, BEST;
static int BESTR[MAXN], BESTS[MAXN];
static long long NODES, BUDGET;
static int EXHAUSTED;

static void dfs(int m) {
  if (NODES >= BUDGET) { EXHAUSTED = 0; return; }
  NODES++;
  if (!crooked_ok(RHO, SIG, m)) return;
  if (m > 0) {
    int mn = RHO[0], mx = RHO[0];
    for (int i = 1; i < m; i++) { if (RHO[i] < mn) mn = RHO[i]; if (RHO[i] > mx) mx = RHO[i]; }
    if (mx - mn == SPAN) {
      if (m < BEST) { BEST = m; memcpy(BESTR, RHO, sizeof(int) * m); memcpy(BESTS, SIG, sizeof(int) * m); }
      return;                    /* no proper extension can be shorter */
    }
  }
  if (m + 1 >= BEST || m + 1 > DEPTH_CAP) return;
  for (int nr = 0; nr <= SPAN; nr++) {
    if (m > 0) { int d = nr - RHO[m - 1]; if (d < -1 || d > 1) continue; }
    for (int ns = nr; ns <= nr + 1; ns++) {
      if (m > 0) {
        int a = SIG[m - 1] > ns ? SIG[m - 1] : ns;
        int b = RHO[m - 1] < nr ? RHO[m - 1] : nr;
        if (a > b + 1) continue;
      }
      RHO[m] = nr; SIG[m] = ns;
      dfs(m + 1);
    }
  }
}

static void shortest_budget(int span, int cap, long long budget) {
  SPAN = span; DEPTH_CAP = cap; BEST = cap + 1; NODES = 0; BUDGET = budget; EXHAUSTED = 1;
  dfs(0);
  if (BEST <= cap) {
    printf("span %d: shortest faithful crooked sequence has %d terms (z %d = %lld)%s\n",
           span, BEST, span, zval[span], (long long)BEST == zval[span] ? "  [matches]" : "  [MISMATCH]");
    printf("        rho ="); for (int i = 0; i < BEST; i++) printf(" %d", BESTR[i]);
    printf("\n        sig ="); for (int i = 0; i < BEST; i++) printf(" %d", BESTS[i]);
    printf("\n        nodes %lld\n", NODES);
    if ((long long)BEST < zval[span])
      printf("  *** COUNTEREXAMPLE to Minimality at span %d ***\n", span);
    /* part 3: every contiguous stretch of the witness is faithful and crooked */
    int bad = 0;
    for (int a = 0; a < BEST; a++)
      for (int b = a; b < BEST; b++)
        if (!faithful_ok(BESTR + a, BESTS + a, b - a + 1)) bad++;
    printf("        stretches of the witness failing faithfulness: %d\n", bad);
  } else {
    printf("span %d: no faithful crooked sequence with at most %d terms (z %d = %lld), nodes %lld%s\n",
           span, cap, span, zval[span], NODES,
           EXHAUSTED ? "  [exhaustive]" : "  [truncated at the node budget]");
    if (zval[span] > cap) printf("        consistent with Minimality (its bound is not reached)\n");
  }
  fflush(stdout);
}

static void shortest(int span, int cap) { shortest_budget(span, cap, (long long)1 << 62); }

/* ---------- part 2: Bing's chains ---------- */

static int PATH[MAXN], PLEN;

static void bing_path(int a, int b, int *out, int *len) {
  int d = a < b ? b - a : a - b;
  if (d <= 2) {
    *len = 0;
    if (a <= b) for (int u = 0; u <= b - a; u++) out[(*len)++] = a + u;
    else        for (int u = 0; u <= a - b; u++) out[(*len)++] = a - u;
    return;
  }
  int t1[MAXN], t2[MAXN], t3[MAXN], l1, l2, l3;
  if (a < b) { bing_path(a, b - 1, t1, &l1); bing_path(b - 1, a + 1, t2, &l2); bing_path(a + 1, b, t3, &l3); }
  else       { bing_path(a, b + 1, t1, &l1); bing_path(b + 1, a - 1, t2, &l2); bing_path(a - 1, b, t3, &l3); }
  *len = 0;
  for (int i = 0; i < l1; i++) out[(*len)++] = t1[i];
  for (int i = 1; i < l2; i++) out[(*len)++] = t2[i];
  for (int i = 1; i < l3; i++) out[(*len)++] = t3[i];
}

static unsigned long long rng_state = 88172645463325252ULL;
static unsigned long long rnd(void) {
  rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17;
  return rng_state;
}

static void gaps(const int *rho, int m, const char *tag, int *viol, int *pairs) {
  for (int i = 0; i < m; i++)
    for (int j = i + 1; j < m; j++) {
      int d = rho[j] - rho[i]; if (d < 0) d = -d;
      if (d < 3) continue;
      (*pairs)++;
      if ((long long)(j - i + 1) < zval[d]) {
        (*viol)++;
        if (*viol < 5) printf("  violation on %s: i=%d j=%d d=%d gap=%d z=%lld\n",
                              tag, i, j, d, j - i + 1, zval[d]);
      }
    }
}

int main(void) {
  init_z();
  printf("z: "); for (int i = 0; i <= 8; i++) printf("z %d = %lld  ", i, zval[i]); printf("\n\n");

  printf("== part 2: Bing's chains, index gap vs z ==\n");
  for (int n = 3; n <= 8; n++) {
    bing_path(0, n, PATH, &PLEN);
    int viol = 0, pairs = 0;
    char tag[32]; snprintf(tag, sizeof tag, "bing 0 %d", n);
    gaps(PATH, PLEN, tag, &viol, &pairs);
    int sig[MAXN]; for (int i = 0; i < PLEN; i++) sig[i] = PATH[i];
    int f = faithful_ok(PATH, sig, PLEN);
    printf("bing 0 %d: length %d (z %d = %lld), faithful crooked: %s, pairs d>=3: %d, violations: %d\n",
           n, PLEN, n, zval[n], f ? "yes" : "NO", pairs, viol);
    fflush(stdout);
  }
  printf("\n");

  printf("== part 3: random contiguous subchains (restriction + gap bound) ==\n");
  for (int n = 4; n <= 8; n++) {
    bing_path(0, n, PATH, &PLEN);
    int sig[MAXN]; for (int i = 0; i < PLEN; i++) sig[i] = PATH[i];
    int viol = 0, pairs = 0, notfaithful = 0, trials = 800;
    for (int it = 0; it < trials; it++) {
      int a = (int)(rnd() % (unsigned)PLEN), b = (int)(rnd() % (unsigned)PLEN);
      if (a > b) { int t = a; a = b; b = t; }
      int m = b - a + 1;
      if (m > 60) { a = b - 60; m = 61; }      /* keep the O(m^4) check affordable */
      if (!faithful_ok(PATH + a, sig + a, m)) notfaithful++;
      gaps(PATH + a, m, "subchain", &viol, &pairs);
    }
    printf("bing 0 %d: %d subchains, non-faithful stretches: %d, pairs d>=3: %d, violations: %d\n",
           n, trials, notfaithful, pairs, viol);
    fflush(stdout);
  }
  printf("\n== part 1: shortest faithful crooked sequence of each span ==\n");
  shortest(1, 4);
  shortest(2, 6);
  shortest(3, 13);
  shortest(4, 13);
  /* z 5 = 30: a hit below 30 terms would refute Minimality.  Exhaustion to depth 29 is out of
     reach, so this leg runs to a node budget and reports how far it got. */
  shortest_budget(5, 20, 120000000LL);
  return 0;
}
