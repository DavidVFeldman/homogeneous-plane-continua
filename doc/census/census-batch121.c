/* Batch 121 census in the faithful model: Q2 and Q3 of COMMISSION-batch121.md.
 *
 * Enumerator and Bing chains: census-batch87-common.h (unchanged).  A fold is a block map beta
 * (|beta(t+1) - beta(t)| <= 1, values 0..Q-1 all used) with beta i = 0.  Block width W: every
 * block has max rho - min sig <= W - 1 (the intervals [rho, sig] of its members meet a common
 * window of W consecutive coarse links; exactly "the block lies in W consecutive links of D" for
 * a realized chain, and for a general chain through its (minIdx, maxIdx)).
 *
 * End clause of width EW, for the end links t = 0 and t = n - 1:
 *   if t meets coarse level 0, every member of its block has rho <= EW - 1;
 *   if t meets coarse level K - 1, every member of its block has sig >= K - EW.
 * "Meets" is read in one of two ways:
 *   forced   -- some u with |u - t| <= 1 has rho u <= level <= sig u (the meeting table of the
 *               realized chain, linkRect_meet_strip_iff; the reading of batches 86-87);
 *   possible -- sig t <= 1 (for level 0), rho t >= K - 2 (for level K - 1): the meetings that
 *               ANY chain with these (minIdx, maxIdx) can have, since a link inside D_{sig t}
 *               can only meet D_0 if D_{sig t} does (Q2; Lean: Recon121.theorem3_end_of_model).
 *
 * Classes (each at every basepoint i):
 *   T3END   W = 3, EW = 3, forced     (batch 87's T3END, re-run as a cross-check)
 *   T3ENDP  W = 3, EW = 3, possible   (Q2: sufficient for theorem3_end on general chains)
 *   S2      W = 2, no end clause      (Q3(a): Bing's main clause)
 *   LIT     W = 2, EW = 2, forced     (Q3(b): Theorem3Literal on realized chains)
 *   LITP    W = 2, EW = 2, possible   (Q3(b): sufficient for Theorem3Literal minus the
 *                                      "only the first link" clause on general chains)
 *   T3E2    W = 3, EW = 2, forced     (Theorem3EndTwo on realized chains)
 *   T3E2P   W = 3, EW = 2, possible
 *   LITM    W = 2, EW = 2, forced + S, for every admissible S (below)
 *   T3ENDM  W = 3, EW = 3, forced + S, for every admissible S
 * An admissible S is a set of extra meetings of the end links with the extreme levels 0, K-1,
 * each possible and unforced, such that the sequence is still crooked (1948 clause) when the
 * meeting table is enlarged by S.  This is the exact class of meeting hypotheses a general chain
 * with these (minIdx, maxIdx) can present to the end clause, up to realizability of S.
 * The "only the first link" clause of Theorem3Literal holds automatically in a realized chain
 * (Lean: Recon121.linkChain_only).
 *
 * The search is exact (exhaustive DFS); a node limit makes it give up (undecided), after which it
 * is retried once with the other arm swept first.
 *
 * Usage: c121 enum N K SHARD NSHARDS   |   c121 bing KK
 * Environment: CLASSES (comma list, default all), LIMIT (node limit per search).
 */
#include "census-batch87-common.h"

static int beta[MAXN], order_[MAXN], prevof[MAXN];
static int bmaxr[MAXN + 2], bmins[MAXN + 2], lowT[MAXN + 2], highT[MAXN + 2];
static int endLow[MAXN], endHigh[MAXN];
static long nodes, LIMIT = 20000000;
static int W = 3, EW = 3;

static int dfs(int pos) {
  if (pos == n) return 1;
  if (++nodes > LIMIT) return -1;
  int t = order_[pos];
  int lo, hi;
  if (pos == 0) { lo = hi = 0; } else { lo = beta[prevof[t]] - 1; hi = beta[prevof[t]] + 1; if (lo < 0) lo = 0; }
  for (int u = lo; u <= hi; u++) {
    beta[t] = u;
    int or_ = bmaxr[u], os = bmins[u];
    if (rho[t] > bmaxr[u]) bmaxr[u] = rho[t];
    if (sig[t] < bmins[u]) bmins[u] = sig[t];
    lowT[u] += endLow[t]; highT[u] += endHigh[t];
    int good = bmaxr[u] - (W - 1) <= bmins[u];
    if (lowT[u] && bmaxr[u] > EW - 1) good = 0;
    if (highT[u] && bmins[u] < K - EW) good = 0;
    if (good) {
      int r = dfs(pos + 1);
      if (r != 0) return r;
    }
    lowT[u] -= endLow[t]; highT[u] -= endHigh[t];
    bmaxr[u] = or_; bmins[u] = os;
  }
  return 0;
}

static int LEFTFIRST = 0;
static int MODE = 0; /* 0: no end clause, 1: forced, 2: possible, 3: forced + the extra set S */
/* MODE 3: extra (unforced but possible) meetings of the end links with the extreme levels.
   bit 0: link 0 meets level 0; bit 1: link 0 meets level K-1; bit 2: link n-1 meets level 0;
   bit 3: link n-1 meets level K-1. */
static int SMASK = 0;
static int inS(int t, int j) {
  if (t == 0 && j == 0 && (SMASK & 1)) return 1;
  if (t == 0 && j == K - 1 && (SMASK & 2)) return 1;
  if (t == n - 1 && j == 0 && (SMASK & 4)) return 1;
  if (t == n - 1 && j == K - 1 && (SMASK & 8)) return 1;
  return 0;
}
static int meetsx(int t, int j) { return meets(t, j) || inS(t, j); }
/* crookedness with the extended meeting table; only pairs with an end link can change */
static int crooked_pair_x(int s, int t) {
  for (int h = 0; h < K; h++) {
    if (!meetsx(s, h)) continue;
    for (int k = 0; k < K; k++) {
      if (abs(h - k) < 3) continue;
      if (!meetsx(t, k)) continue;
      int need1 = h < k ? k - 1 : k + 1, need2 = h < k ? h + 1 : h - 1;
      int r = -1, r2 = -1;
      for (int x = s + 1; x < t; x++) if (rho[x] <= need1 && need1 <= sig[x]) { r = x; break; }
      for (int x = t - 1; x > s; x--) if (rho[x] <= need2 && need2 <= sig[x]) { r2 = x; break; }
      if (r < 0 || r2 < 0 || !(r < r2)) return 0;
    }
  }
  return 1;
}
static int admissibleS(void) {
  /* each extra meeting must be possible (sig t <= 1 for level 0, rho t >= K-2 for level K-1)
     and unforced; and the sequence must stay crooked */
  for (int b = 0; b < 4; b++) if (SMASK & (1 << b)) {
    int t = b < 2 ? 0 : n - 1, j = (b & 1) ? K - 1 : 0;
    if (meets(t, j)) return 0;
    if (j == 0 && sig[t] > 1) return 0;
    if (j == K - 1 && rho[t] < K - 2) return 0;
  }
  if (n == 1 && (SMASK & 12)) return 0;
  for (int t = 1; t < n; t++) if (!crooked_pair_x(0, t)) return 0;
  for (int s = 0; s < n - 1; s++) if (!crooked_pair_x(s, n - 1)) return 0;
  return 1;
}
static void reset(int start) {
  for (int u = 0; u <= n + 1; u++) { bmaxr[u] = -100; bmins[u] = 100; lowT[u] = highT[u] = 0; }
  for (int t = 0; t < n; t++) endLow[t] = endHigh[t] = 0;
  if (MODE) {
    int e[2] = {0, n - 1};
    for (int a = 0; a < 2; a++) {
      int t = e[a];
      int lo = MODE == 1 ? meets(t, 0) : MODE == 2 ? sig[t] <= 1 : meetsx(t, 0);
      int hi = MODE == 1 ? meets(t, K - 1) : MODE == 2 ? rho[t] >= K - 2 : meetsx(t, K - 1);
      if (lo) endLow[t] = 1;
      if (hi) endHigh[t] = 1;
    }
  }
  int p = 0;
  order_[p++] = start; prevof[start] = -1;
  if (!LEFTFIRST) {
    for (int t = start + 1; t < n; t++) { order_[p++] = t; prevof[t] = t - 1; }
    for (int t = start - 1; t >= 0; t--) { order_[p++] = t; prevof[t] = t + 1; }
  } else {
    for (int t = start - 1; t >= 0; t--) { order_[p++] = t; prevof[t] = t + 1; }
    for (int t = start + 1; t < n; t++) { order_[p++] = t; prevof[t] = t - 1; }
  }
  nodes = 0;
}
static int solve2(int start) {
  LEFTFIRST = 0; reset(start); int r = dfs(0);
  if (r < 0) { LEFTFIRST = 1; reset(start); r = dfs(0); LEFTFIRST = 0; }
  return r;
}

static void dump(const char *tag, int i) {
  printf("%s n=%d K=%d i=%d S=%d rho=", tag, n, K, i, SMASK);
  for (int t = 0; t < n; t++) printf("%d%s", rho[t], t + 1 < n ? "," : "");
  printf(" sig=");
  for (int t = 0; t < n; t++) printf("%d%s", sig[t], t + 1 < n ? "," : "");
  printf("\n"); fflush(stdout);
}

#define NCL 9
static const char *cname[NCL] = {"T3END", "T3ENDP", "S2", "LIT", "LITP", "T3E2", "T3E2P", "LITM", "T3ENDM"};
static const int cW[NCL] = {3, 3, 2, 2, 2, 3, 3, 2, 3};
static const int cEW[NCL] = {3, 3, 0, 2, 2, 2, 2, 2, 3};
static const int cMODE[NCL] = {1, 2, 0, 1, 2, 1, 2, 3, 3};
static int on[NCL];
static long inst[NCL], fail[NCL], unk[NCL], seqs, failseqs[NCL], fail4[NCL];

static int INTERIOR = 0;
static void visit(void) {
  seqs++;
  for (int c = 0; c < NCL; c++) {
    if (!on[c]) continue;
    W = cW[c]; EW = cEW[c]; MODE = cMODE[c];
    int any = 0;
    int masks[16], nm = 0;
    if (MODE == 3) { for (SMASK = 0; SMASK < 16; SMASK++) if (admissibleS()) masks[nm++] = SMASK; }
    else { masks[nm++] = 0; }
    for (int mi = 0; mi < nm; mi++)
    for (int i = INTERIOR ? 1 : 0; i < (INTERIOR ? n - 1 : n); i++) {
      SMASK = masks[mi];
      inst[c]++;
      int r = solve2(i);
      if (r == 0) { fail[c]++; if (K >= 4) { fail4[c]++; if (fail4[c] <= 8) { char tg[40]; sprintf(tg, "%s-FAIL-K>=4", cname[c]); dump(tg, i); } } any = 1; if (fail[c] <= 8) { char tg[40]; sprintf(tg, "%s-FAIL", cname[c]); dump(tg, i); } }
      if (r < 0) { unk[c]++; if (unk[c] <= 8) { char tg[40]; sprintf(tg, "%s-UNDEC", cname[c]); dump(tg, i); } }
    }
    if (any) failseqs[c]++;
  }
}

static long shard_ctr; static int SHARD = 0, NSH = 1;
static void gen_rec2(int t) {
  if (t >= 2) {
    int tt = t - 2; int save = n; n = t;
    for (int s = 0; s < tt; s++) if (!crooked_pair(s, tt)) { n = save; return; }
    n = save;
  }
  if (t == 4) { if ((shard_ctr++ % NSH) != SHARD) return; }
  if (t == NFULL) {
    n = NFULL;
    for (int s = 0; s < n - 1; s++) if (!crooked_pair(s, n - 1)) return;
    int mn = 100, mx = -100;
    for (int a = 0; a < n; a++) { if (rho[a] < mn) mn = rho[a]; if (sig[a] > mx) mx = sig[a]; }
    if (mn != 0 || mx != K - 1) return;
    VISIT();
    return;
  }
  for (int r = 0; r < K; r++)
    for (int w = 0; w < 2; w++) {
      int s = r + w;
      if (s >= K) continue;
      if (t > 0) {
        int mx = s > sig[t - 1] ? s : sig[t - 1];
        int mn = r < rho[t - 1] ? r : rho[t - 1];
        if (mx > mn + 1) continue;
      }
      rho[t] = r; sig[t] = s;
      gen_rec2(t + 1);
    }
}

static void summary(const char *what) {
  printf("%s sequences=%ld\n", what, seqs);
  for (int c = 0; c < NCL; c++) if (on[c])
    printf("  %s instances=%ld fails=%ld (in %ld sequences; %ld fails with K >= 4) undecided=%ld\n", cname[c], inst[c], fail[c], failseqs[c], fail4[c], unk[c]);
  fflush(stdout);
}

int main(int argc, char **argv) {
  if (getenv("LIMIT")) LIMIT = atol(getenv("LIMIT"));
  for (int c = 0; c < NCL; c++) on[c] = 1;
  if (getenv("CLASSES")) {
    const char *s = getenv("CLASSES");
    for (int c = 0; c < NCL; c++) {
      on[c] = 0;
      const char *p = s; size_t L = strlen(cname[c]);
      while ((p = strstr(p, cname[c]))) {
        if ((p == s || p[-1] == ',') && (p[L] == 0 || p[L] == ',')) { on[c] = 1; break; }
        p += L;
      }
    }
  }
  if (argc >= 6 && !strcmp(argv[1], "enum")) {
    int N = atoi(argv[2]), KK = atoi(argv[3]); SHARD = atoi(argv[4]); NSH = atoi(argv[5]);
    NFULL = N; K = KK; VISIT = visit; gen_rec2(0);
    char w[128]; sprintf(w, "enum n=%d K=%d shard %d/%d limit=%ld", N, KK, SHARD, NSH, LIMIT);
    summary(w);
  } else if (argc >= 3 && !strcmp(argv[1], "bing")) {
    int KK = atoi(argv[2]);
    Path P = bpath(0, KK - 1);
    for (int l = 0; l < P.n; l++)
      for (int r = l + 2; r < P.n; r++) {
        if (getenv("BINGWHOLE") && !(l == 0 && r == P.n - 1)) continue;
        n = r - l + 1; int mn = 100, mx = -1;
        for (int t = 0; t < n; t++) { rho[t] = sig[t] = P.v[l + t]; if (rho[t] < mn) mn = rho[t]; if (sig[t] > mx) mx = sig[t]; }
        for (int t = 0; t < n; t++) { rho[t] -= mn; sig[t] -= mn; }
        K = mx - mn + 1;
        if (!crooked_all()) { printf("NOT CROOKED?! l=%d r=%d\n", l, r); continue; }
        visit();
      }
    char w[128]; sprintf(w, "bing KK=%d len=%d limit=%ld", KK, P.n, LIMIT);
    summary(w);
  } else { fprintf(stderr, "usage\n"); return 1; }
  return 0;
}
