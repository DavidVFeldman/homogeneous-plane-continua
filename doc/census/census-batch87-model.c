/* Batch 87 census in the faithful model: items 2, 3 and 4 of COMMISSION-batch87.md.
 *
 * One enumeration of faithful sequences (census-batch87-common.h), three decided statements.
 * All folds are block maps beta (|beta(t+1) - beta(t)| <= 1, values 0..Q-1) with every block in
 * three consecutive coarse links (max rho - min sig <= 2 on each block).
 *
 * FOLD3 (item 2, ModelCoveringFold3 of HPC/PseudoArc/Recon87Model.lean).  For all a != c
 *   (P' in link a, R in link c) and q (Q' in link q), with I the largest index interval
 *   containing a and c, not containing q, whose members all satisfy the window property
 *   (share a coarse level with some link between a and c), q outside I:  there is a fold with
 *   beta a = 0, beta q = max beta, beta t <= beta c for t in I.  The fold condition is antitone
 *   in I and the window property is memberwise, so the largest admissible I is the hardest.
 *   Separation hypotheses (true at deep levels; two points of links at most two apart are within
 *   3 eps_m): S1 = the coarse intervals of a and c at distance >= 3 (P' != R);
 *   S2 = the coarse interval of q at distance >= 3 from that of every member of I (Q' not in W).
 *   Counters are kept for: no separation (F0), S1 (F1), S2 (F2), S1 and S2 (F3).
 *   F0 and F1 are only run when the flag "all" is given (n^3 instances per sequence).
 *
 * END (item 3, ModelEndTime of HPC/Fold/Recon87End.lean).  The whole sequence is [0, c]
 *   (c = n - 1), R in link 0, basepoint p with 0 < p < c:  there is a fold with beta p = 0 and
 *   beta 0 = beta c = max beta (both arm ends at the maximal time).  Counters for: no further
 *   hypothesis (E0); window (EW: every link shares a coarse level with a link of [0, p]);
 *   window and S (EWS: coarse intervals of links 0 and p at distance >= 3); X (EX: each arm
 *   [0, p] and [p, c] has a link with rho = 0 and a link with sig = K - 1, the hypothesis of
 *   Theorem 4 on each arm); window, S and X (EWSX); C (EC: the coarse intervals of links 0 and c
 *   meet a common window [j, j+2] -- necessary, since both ends lie in the last block);
 *   window, S and C (EWSC); C and X (ECX); window, S, C and X (EWSCX).
 *
 * T3END (item 4, theorem3_end, as in census-batch86-exhaustive.c).  For every basepoint i:
 *   there is a fold with beta i = 0 and the end-link clause: if link 0 (resp. n - 1) meets
 *   coarse level 0, every member of its block has rho <= 2; if it meets level K - 1, every
 *   member has sig >= K - 3.  (Meeting is by forced meetings: some neighbour's interval contains
 *   the level.)  Also re-checks theorem3 itself (without the clause).
 *
 * Usage: model enum N K SHARD NSHARDS [all]   |   model bing KK [all]
 * Environment: CHECKS (subset of "fet", default all), LIMIT (node limit per search; on hitting
 * it the search is retried once with the other sweep order), BINGWHOLE (bing: whole chain only).
 */
#include "census-batch87-common.h"

static int beta[MAXN], order_[MAXN], prevof[MAXN], posof[MAXN];
static int bmaxr[MAXN + 2], bmins[MAXN + 2], lowT[MAXN + 2], highT[MAXN + 2];
static int endLow[MAXN], endHigh[MAXN];
static int isI[MAXN], isMax[MAXN], C_ = -1;
static int dirOf[MAXN]; /* +1 right sweep, -1 left sweep */
static long nodes, LIMIT = 20000000;

static int dfs(int pos, int maxval) {
  if (pos == n) return 1;
  if (++nodes > LIMIT) return -1;
  int t = order_[pos];
  int lo, hi;
  if (pos == 0) { lo = hi = 0; } else { lo = beta[prevof[t]] - 1; hi = beta[prevof[t]] + 1; if (lo < 0) lo = 0; }
  for (int u = lo; u <= hi; u++) {
    beta[t] = u;
    int ok = 1;
    /* the R-time: members of I at most beta c */
    if (C_ >= 0) {
      if (t == C_) {
        for (int p = 0; p < pos && ok; p++) { int s = order_[p]; if (isI[s] && beta[s] > u) ok = 0; }
      } else if (isI[t] && posof[C_] < pos && u > beta[C_]) ok = 0;
    }
    /* the maximal time */
    int nm = maxval;
    if (ok) {
      if (isMax[t]) {
        if (maxval >= 0) { if (u != maxval) ok = 0; }
        else { for (int p = 0; p < pos && ok; p++) if (beta[order_[p]] > u) ok = 0; nm = u; }
      } else if (maxval >= 0 && u > maxval) ok = 0;
    }
    /* a later max-link in the current sweep must still be able to climb to the maximum */
    if (ok && nm >= 0) {
      for (int l = t + dirOf[t]; l >= 0 && l < n; l += dirOf[t])
        if (isMax[l] && u + abs(l - t) < nm) { ok = 0; break; }
    }
    if (!ok) continue;
    int or_ = bmaxr[u], os = bmins[u];
    if (rho[t] > bmaxr[u]) bmaxr[u] = rho[t];
    if (sig[t] < bmins[u]) bmins[u] = sig[t];
    lowT[u] += endLow[t]; highT[u] += endHigh[t];
    int good = bmaxr[u] - 2 <= bmins[u];
    if (lowT[u] && bmaxr[u] > 2) good = 0;
    if (highT[u] && bmins[u] < K - 3) good = 0;
    if (good) {
      int r = dfs(pos + 1, nm);
      if (r != 0) return r;
    }
    lowT[u] -= endLow[t]; highT[u] -= endHigh[t];
    bmaxr[u] = or_; bmins[u] = os;
  }
  return 0;
}

static int LEFTFIRST = 0; /* sweep the left arm first (used to retry undecided cases) */
static void reset(int start);
/* run the prepared search; on hitting the node limit, retry with the other sweep order */
typedef void (*setup_fn)(void);
static int solve2(int start, setup_fn setup) {
  LEFTFIRST = 0; reset(start); setup(); int r = dfs(0, -1);
  if (r < 0) { LEFTFIRST = 1; reset(start); setup(); r = dfs(0, -1); LEFTFIRST = 0; }
  return r;
}
static void reset(int start) {
  for (int u = 0; u <= n + 1; u++) { bmaxr[u] = -100; bmins[u] = 100; lowT[u] = highT[u] = 0; }
  for (int t = 0; t < n; t++) { isI[t] = isMax[t] = endLow[t] = endHigh[t] = 0; }
  C_ = -1;
  int p = 0;
  order_[p++] = start; prevof[start] = -1; dirOf[start] = 1;
  if (!LEFTFIRST) {
    for (int t = start + 1; t < n; t++) { order_[p++] = t; prevof[t] = t - 1; dirOf[t] = 1; }
    for (int t = start - 1; t >= 0; t--) { order_[p++] = t; prevof[t] = t + 1; dirOf[t] = -1; }
  } else {
    for (int t = start - 1; t >= 0; t--) { order_[p++] = t; prevof[t] = t + 1; dirOf[t] = -1; }
    for (int t = start + 1; t < n; t++) { order_[p++] = t; prevof[t] = t - 1; dirOf[t] = 1; }
  }
  for (int q = 0; q < n; q++) posof[order_[q]] = q;
  nodes = 0;
}

static int window_ok(int u, int lo, int hi) {
  for (int v = lo; v <= hi; v++) {
    int L = rho[u] > rho[v] ? rho[u] : rho[v];
    int H = sig[u] < sig[v] ? sig[u] : sig[v];
    if (L <= H) return 1;
  }
  return 0;
}
static int lvdist(int u, int v) {
  if (sig[u] < rho[v]) return rho[v] - sig[u];
  if (sig[v] < rho[u]) return rho[u] - sig[v];
  return 0;
}

static void dump(const char *tag, int x, int y, int z, int lo, int hi) {
  printf("%s n=%d K=%d %d %d %d [%d,%d] rho=", tag, n, K, x, y, z, lo, hi);
  for (int t = 0; t < n; t++) printf("%d%s", rho[t], t + 1 < n ? "," : "");
  printf(" sig=");
  for (int t = 0; t < n; t++) printf("%d%s", sig[t], t + 1 < n ? "," : "");
  printf("\n"); fflush(stdout);
}

static int ALL = 0;
static long seqs;
static long f3inst[4], f3fail[4], f3unk[4];
static long einst[9], efail[9], eunk[9];
static long tinst, tfail, tunk, t3fail, t3unk;

static int g_lo, g_hi, g_c, g_q;
static int lMaxS[MAXN], lMinR[MAXN], hMaxS[MAXN], hMinR[MAXN];
static unsigned long long lvmask(int v) {
  unsigned long long m = 0;
  for (int j = rho[v]; j <= sig[v]; j++) m |= 1ULL << j;
  return m;
}
static void setup_fold3(void) { for (int t = g_lo; t <= g_hi; t++) isI[t] = 1; C_ = g_c; isMax[g_q] = 1; }
static void setup_end(void) { isMax[0] = isMax[n - 1] = 1; }
static void setup_t3end(void) {
  int e[2] = {0, n - 1};
  for (int a = 0; a < 2; a++) { int t = e[a]; if (meets(t, 0)) endLow[t] = 1; if (meets(t, K - 1)) endHigh[t] = 1; }
}
static void setup_none(void) {}
static void do_fold3(void) {
  for (int a = 0; a < n; a++)
    for (int c = 0; c < n; c++) {
      if (a == c) continue;
      int mn = a < c ? a : c, mx = a < c ? c : a;
      int s1 = lvdist(a, c) >= 3;
      /* the largest window interval around [mn, mx]; cutting it at q gives the largest
         admissible I for that q.  Window test by bitmask of the coarse levels met by [mn, mx]. */
      unsigned long long mask = 0;
      for (int v = mn; v <= mx; v++) mask |= lvmask(v);
      int L0 = mn, H0 = mx;
      while (L0 - 1 >= 0 && (lvmask(L0 - 1) & mask)) L0--;
      while (H0 + 1 < n && (lvmask(H0 + 1) & mask)) H0++;
      /* running extremes of the levels of I, from [mn, mx] outwards */
      int coreMaxS = -1000, coreMinR = 1000;
      for (int v = mn; v <= mx; v++) { if (sig[v] > coreMaxS) coreMaxS = sig[v]; if (rho[v] < coreMinR) coreMinR = rho[v]; }
      for (int x = mn, mS = coreMaxS, mR = coreMinR; x >= L0; x--) { if (sig[x] > mS) mS = sig[x]; if (rho[x] < mR) mR = rho[x]; lMaxS[x] = mS; lMinR[x] = mR; }
      for (int x = mx, mS = coreMaxS, mR = coreMinR; x <= H0; x++) { if (sig[x] > mS) mS = sig[x]; if (rho[x] < mR) mR = rho[x]; hMaxS[x] = mS; hMinR[x] = mR; }
      for (int q = 0; q < n; q++) {
        if (mn <= q && q <= mx) continue;
        int lo = L0, hi = H0;
        if (q < mn && q >= lo) lo = q + 1;
        if (q > mx && q <= hi) hi = q - 1;
        /* S2: every member of I at coarse gap >= 3 from q.  I is connected and its levels move by
           at most one per step, so it lies on one side of q's levels:  S2 iff
           max sig(I) <= rho q - 3  or  min rho(I) >= sig q + 3. */
        int IMaxS = lMaxS[lo] > hMaxS[hi] ? lMaxS[lo] : hMaxS[hi];
        int IMinR = lMinR[lo] < hMinR[hi] ? lMinR[lo] : hMinR[hi];
        int s2 = (IMaxS <= rho[q] - 3) || (IMinR >= sig[q] + 3);
        if (!ALL && !s2) continue;
        g_lo = lo; g_hi = hi; g_c = c; g_q = q;
        int r = solve2(a, setup_fold3);
        for (int cls = 0; cls < 4; cls++) {
          if ((cls & 1) && !s1) continue;
          if ((cls & 2) && !s2) continue;
          if (!ALL && !(cls & 2)) continue;
          f3inst[cls]++;
          if (r == 0) { f3fail[cls]++; if (f3fail[cls] <= 5) { char tg[32]; sprintf(tg, "FOLD3-FAIL-S%d", cls); dump(tg, a, c, q, lo, hi); } }
          if (r < 0) { f3unk[cls]++; if (f3unk[cls] <= 5) { char tg[32]; sprintf(tg, "FOLD3-UNDEC-S%d", cls); dump(tg, a, c, q, lo, hi); } }
        }
      }
    }
}

static void do_end(void) {
  int c = n - 1;
  for (int p = 1; p < c; p++) {
    int w = 1;
    for (int u = 0; u <= c; u++) if (!window_ok(u, 0, p)) { w = 0; break; }
    int s = lvdist(0, p) >= 3;
    int r = solve2(p, setup_end);
    /* X(arm): the arm meets both extreme coarse levels 0 and K - 1 */
    int x1lo = 0, x1hi = 0, x2lo = 0, x2hi = 0;
    for (int u = 0; u <= p; u++) { if (rho[u] == 0) x1lo = 1; if (sig[u] == K - 1) x1hi = 1; }
    for (int u = p; u <= c; u++) { if (rho[u] == 0) x2lo = 1; if (sig[u] == K - 1) x2hi = 1; }
    int x = x1lo && x1hi && x2lo && x2hi;
    /* C: links 0 and c fit in one three-link window (necessary: they share the last block) */
    int cc = (rho[0] > rho[c] ? rho[0] : rho[c]) - 2 <= (sig[0] < sig[c] ? sig[0] : sig[c]);
    int cl[9] = {1, w, w && s, x, w && s && x, cc, w && s && cc, cc && x, w && s && cc && x};
    for (int k = 0; k < 9; k++) {
      if (!cl[k]) continue;
      einst[k]++;
      if (r == 0) { efail[k]++; if (efail[k] <= 5) { char tg[32]; sprintf(tg, "END-FAIL-%s", k == 0 ? "E0" : k == 1 ? "EW" : k == 2 ? "EWS" : k == 3 ? "EX" : k == 4 ? "EWSX" : k == 5 ? "EC" : k == 6 ? "EWSC" : k == 7 ? "ECX" : "EWSCX"); dump(tg, p, 0, c, 0, c); } }
      if (r < 0) { eunk[k]++; if (eunk[k] <= 5) { char tg[32]; sprintf(tg, "END-UNDEC-C%d", k); dump(tg, p, 0, c, 0, c); } }
    }
  }
}

static void do_t3end(int interior_only) {
  for (int i = interior_only ? 1 : 0; i < (interior_only ? n - 1 : n); i++) {
    tinst++;
    int r = solve2(i, setup_t3end);
    if (r == 0) {
      /* re-check theorem3 without the clause */
      int r3 = solve2(i, setup_none);
      if (r3 == 0) { t3fail++; dump("THM3-FAIL", i, 0, 0, 0, 0); }
      else if (r3 < 0) t3unk++;
      tfail++; if (tfail <= 10) dump("T3END-FAIL", i, 0, 0, 0, 0);
    }
    if (r < 0) { tunk++; if (tunk <= 10) dump("T3END-UNDEC", i, 0, 0, 0, 0); }
  }
}

static int DOF3 = 1, DOEND = 1, DOT3 = 1;
static void visit(void) {
  seqs++;
  if (DOF3) do_fold3();
  if (DOEND) do_end();
  if (DOT3) do_t3end(0);
}

static long shard_ctr; static int SHARD = 0, NSH = 1;
static void gen_shard(int t);
static void summary(const char *what) {
  printf("%s sequences=%ld\n", what, seqs);
  const char *nm[4] = {"none", "S1", "S2", "S1+S2"};
  if (DOF3) for (int k = 0; k < 4; k++) if (ALL || (k & 2))
    printf("  FOLD3[%s] instances=%ld fails=%ld undecided=%ld\n", nm[k], f3inst[k], f3fail[k], f3unk[k]);
  const char *en[9] = {"none", "window", "window+S", "X", "window+S+X", "C", "window+S+C", "C+X", "window+S+C+X"};
  if (DOEND) for (int k = 0; k < 9; k++)
    printf("  END[%s] instances=%ld fails=%ld undecided=%ld\n", en[k], einst[k], efail[k], eunk[k]);
  if (DOT3) printf("  T3END instances=%ld fails=%ld undecided=%ld thm3fails=%ld thm3undecided=%ld\n", tinst, tfail, tunk, t3fail, t3unk);
}

/* sharded enumeration: split the search tree at depth 4 */
static void gen_rec2(int t);
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

int main(int argc, char **argv) {
  if (getenv("LIMIT")) LIMIT = atol(getenv("LIMIT"));
  if (getenv("CHECKS")) { const char *c = getenv("CHECKS"); DOF3 = !!strchr(c, 'f'); DOEND = !!strchr(c, 'e'); DOT3 = !!strchr(c, 't'); }
  if (argc >= 6 && !strcmp(argv[1], "enum")) {
    int N = atoi(argv[2]), KK = atoi(argv[3]); SHARD = atoi(argv[4]); NSH = atoi(argv[5]);
    if (argc >= 7 && !strcmp(argv[6], "all")) ALL = 1;
    NFULL = N; K = KK; VISIT = visit; gen_rec2(0);
    char w[128]; sprintf(w, "enum n=%d K=%d shard %d/%d limit=%ld all=%d", N, KK, SHARD, NSH, LIMIT, ALL);
    summary(w);
  } else if (argc >= 3 && !strcmp(argv[1], "bing")) {
    int KK = atoi(argv[2]);
    if (argc >= 4 && !strcmp(argv[3], "all")) ALL = 1;
    Path P = bpath(0, KK - 1);
    for (int l = 0; l < P.n; l++)
      for (int r = l + 2; r < P.n; r++) {
        if (getenv("BINGWHOLE") && !(l == 0 && r == P.n - 1)) continue;
        n = r - l + 1; int mn = 100, mx = -1;
        for (int t = 0; t < n; t++) { rho[t] = sig[t] = P.v[l + t]; if (rho[t] < mn) mn = rho[t]; if (sig[t] > mx) mx = sig[t]; }
        for (int t = 0; t < n; t++) { rho[t] -= mn; sig[t] -= mn; }
        K = mx - mn + 1;
        if (!crooked_all()) { printf("NOT CROOKED?! l=%d r=%d\n", l, r); continue; }
        seqs++;
        if (DOF3) do_fold3();
        if (DOEND) do_end();
        if (DOT3 && K >= 5 && (meets(0, 0) || meets(0, K - 1) || meets(n - 1, 0) || meets(n - 1, K - 1))) do_t3end(1);
      }
    char w[128]; sprintf(w, "bing KK=%d len=%d limit=%ld all=%d", KK, P.n, LIMIT, ALL);
    summary(w);
  } else { fprintf(stderr, "usage\n"); return 1; }
  return 0;
}
