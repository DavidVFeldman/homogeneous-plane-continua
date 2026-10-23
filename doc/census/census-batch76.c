/* census-batch76.c -- batch 76: the extension law, decided exactly, and what an
 * induction through it would have to carry (commission sections 2.2, 2.3, 2.4, 2.5).
 *
 * Built on census-batch75.c: the same corpus builder (same seeds, same caps), the
 * same definitions of IsCrookedIvF, armG, armT and FoldsOnto, the same
 * de-duplication of basepoints by their pair of whole arms, and the same sample
 * (at most 250 basepoints per level and per least leg count k >= 3).  What is new
 * is what is measured at the sampled basepoints.
 *
 * ExtendsSubBand rho i L H k (HPC/Fold/Target76.lean), with L = 0, H = S:
 *   there are L <= L' <= p <= H' <= H with H' - L' <= H - L - 3, a walk w'
 *   (start s, a list of k - 1 targets, all in [L', H']) folding both arms
 *   truncated at their first exit from [L', H'], and e in {L+1, H-1}, e different
 *   from the last level of w', such that w = w' followed by one leg to e folds
 *   both whole arms.
 *
 * It is decided here EXACTLY, by the following reduction, each step of which is
 * a fact about the definitions:
 *   - a target list may be normalised (repeated targets dropped, monotone runs
 *     merged) without changing the walk, so w' ranges over alternating walks of
 *     at most k - 1 legs, and w = w' + e is either a walk with one more leg, or
 *     (when e continues w''s last leg) w' with its last target moved to e;
 *   - a fold of an arm restricts to a fold of every prefix, so among the bands
 *     containing w''s levels and p the minimal one is the easiest, and it is the
 *     only one that needs testing;
 *   - hence: enumerate every alternating walk w of at most k legs, targets in
 *     [0, S], based within one of p, whose last target is 1 or S - 1 and which
 *     folds both whole arms; for each, form every w' with w = w' + e; accept when
 *     the minimal band of w' and p has span <= S - 3 and w' folds both arms
 *     truncated at that band.
 *
 * FoldsOnto is decided by two independent procedures (a 128-bit mask
 * propagation and an array propagation) and compared on every suffix test of
 * every canonical witness and on a sample of the other calls.
 *
 * Usage: as census-batch75: census-batch76 [S] [windows] [mixtures] [seed] [kmax]
 *        [max-pair-length] [hard-sample-per-level] [shave-cap] [windows-on] [deep-cap]
 *        [q5-cap-per-level-and-k]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef unsigned __int128 u128;

static time_t T0;

/* ------------------------------------------------------------ Bing chains */

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

#define MAXLEV 40
#define MAXN   90000

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

/* ------------------------------------------------------------- the walks */

#define MAXWALK 120
#define MAXKLEG 10

static int SPAN = 10;                    /* H = SPAN, L = 0 */

#define MASKLEV 17                       /* levels 0 .. 16; the band is [0, SPAN], SPAN <= 15 */

typedef struct {
  int len;                               /* number of times of the walk */
  int legs;                              /* number of turning targets */
  int start;
  int lo, hi;                            /* the levels the walk visits */
  int tgt[MAXKLEG];
  u128 mask[MASKLEV];                    /* mask[v] : the times u with |v - c u| <= 1 */
} Walk;

#define MAXWALKS 2000000
static Walk *walks;
static long nWalks = 0;
static long widx[MAXLEV][MAXKLEG + 1], wcnt[MAXLEV][MAXKLEG + 1];

static int buildTimes(int start, const int *tgt, int legs, int *out) {
  int len = 0, cur = start;
  out[len++] = cur;
  for (int q = 0; q < legs; q++) {
    int t = tgt[q];
    if (t == cur) return -1;
    int s = t > cur ? 1 : -1;
    while (cur != t) { cur += s; if (len >= MAXWALK) return -1; out[len++] = cur; }
  }
  return len;
}

static void fillWalk(Walk *w, int start, const int *tgt, int legs, const int *times, int len) {
  w->len = len; w->legs = legs; w->start = start;
  for (int q = 0; q < legs; q++) w->tgt[q] = tgt[q];
  w->lo = times[0]; w->hi = times[0];
  for (int v = 0; v < MASKLEV; v++) w->mask[v] = 0;
  for (int u = 0; u < len; u++) {
    if (times[u] < w->lo) w->lo = times[u];
    if (times[u] > w->hi) w->hi = times[u];
    for (int d = -1; d <= 1; d++) {
      int v = times[u] + d;
      if (v >= 0 && v < MASKLEV) w->mask[v] |= ((u128)1) << u;
    }
  }
}

static void addWalk(int start, const int *tgt, int legs) {
  int times[MAXWALK];
  int len = buildTimes(start, tgt, legs, times);
  if (len < 0 || len > 120 || nWalks >= MAXWALKS) return;
  fillWalk(&walks[nWalks++], start, tgt, legs, times, len);
}

static int curTgt[MAXKLEG];

static void genAlt(int start, int legs, int depth, int last, int dir) {
  if (depth == legs) { addWalk(start, curTgt, legs); return; }
  for (int d = -1; d <= 1; d += 2) {
    if (dir != 0 && d != dir) continue;
    if (d > 0) {
      for (int t = last + 1; t <= SPAN - 1; t++) {
        curTgt[depth] = t; genAlt(start, legs, depth + 1, t, -1);
      }
    } else {
      for (int t = 1; t <= last - 1; t++) {
        curTgt[depth] = t; genAlt(start, legs, depth + 1, t, +1);
      }
    }
  }
}

static int KMAX = 5;

static void buildAllWalks(void) {
  for (int st = 0; st <= SPAN; st++)
    for (int k = 0; k <= KMAX; k++) {
      widx[st][k] = nWalks;
      genAlt(st, k, 0, st, 0);
      wcnt[st][k] = nWalks - widx[st][k];
    }
}

/* FoldsOnto f m c, decided exactly: the reachable set of walk times, forward. */
static int foldsMask(const int *f, int m, const Walk *w) {
  u128 r = w->mask[f[0]] & (u128)1;
  if (!r) return 0;
  for (int j = 1; j < m; j++) {
    r = (r | (r << 1) | (r >> 1)) & w->mask[f[j]];
    if (!r) return 0;
  }
  return 1;
}

/* the same, returning the set of arrival times (0 when the fold fails) */
static u128 foldsArrive(const int *f, int m, const Walk *w) {
  u128 r = w->mask[f[0]] & (u128)1;
  if (!r) return 0;
  for (int j = 1; j < m; j++) {
    r = (r | (r << 1) | (r >> 1)) & w->mask[f[j]];
    if (!r) return 0;
  }
  return r;
}

/* the same fold, decided by an independent array propagation */
static int foldsBrute(const int *f, int m, const Walk *w) {
  static char cur[MAXWALK], nxt[MAXWALK];
  int times[MAXWALK];
  int len = buildTimes(w->start, w->tgt, w->legs, times);
  if (len < 0) return 0;
  for (int u = 0; u < len; u++) cur[u] = 0;
  if (f[0] - times[0] > 1 || times[0] - f[0] > 1) return 0;
  cur[0] = 1;
  for (int j = 1; j < m; j++) {
    int any = 0;
    for (int u = 0; u < len; u++) nxt[u] = 0;
    for (int u = 0; u < len; u++) {
      if (!cur[u]) continue;
      for (int e = -1; e <= 1; e++) {
        int u2 = u + e;
        if (u2 < 0 || u2 >= len) continue;
        int d = f[j] - times[u2];
        if (d <= 1 && d >= -1) { nxt[u2] = 1; any = 1; }
      }
    }
    if (!any) return 0;
    memcpy(cur, nxt, sizeof(char) * len);
  }
  return 1;
}

/* ------------------------------------------------------------- the counters */

static int rho[MAXN], sig[MAXN], armG[MAXN], armT[MAXN];
static int curThin = 1;

static long nPairs = 0, nDistinctPairs = 0, nLinks = 0, nNonThin = 0, nSourceKinds = 0;
static long variantsTried = 0, variantsFaithful = 0;
static long nBase = 0, nBaseDistinct = 0, nBaseThin = 0;
static long kCount[MAXKLEG + 2], kCountThin[MAXKLEG + 2];
static long kNone = 0, kNoneThin = 0;
static long kByLevel[MAXLEV][MAXKLEG + 2];
static long kByLevelThin[MAXLEV][MAXKLEG + 2];
static long kNoneByLevel[MAXLEV];
static long armMin = 1 << 30, armMax = -1;
static long bruteSamples = 0, bruteBad = 0;
static long shownFail = 0, shownFive = 0, shownMax = 0;
static int maxLegsSeen = -1;
static long maxLegsByLevel[MAXLEV];
static int witnessWritten[MAXKLEG + 2];
static int DOWINDOWS = 1;
static long DEEPCAP = 20, deepDone = 0, deepFound[MAXKLEG + 4];

/* ---- section 2.1 counters ---- */
static long HARDPERLEVEL = 250;
static long hardSeen[MAXLEV], hardDone[MAXLEV][MAXKLEG + 2];
static long s21Examined = 0, s21NoLeastWalkFound = 0;
static long s21Success = 0, s21Fail = 0;
static long s21ByBandSpan[MAXLEV];       /* successes whose best sub-band has this span */
static long s21SuccessDeep = 0;          /* success with both truncated arms >= 10 links */
static long s21ExaminedDeepable = 0;
static long s21AppendTop = 0, s21AppendBottom = 0, s21AppendOther = 0, s21AppendNone = 0;
static long s21Prepend = 0;
static long s21LegsAppended[MAXKLEG + 2];
static long s21ByK[MAXKLEG + 2], s21SuccessByK[MAXKLEG + 2];
static long s21ArmTrunc[8];              /* histogram of min(truncated arm lengths) */
static long s21ShownFail = 0;
static long s21SpanMinus1 = 0, s21SpanMinus2 = 0;

/* ---- section 2.2 counters ---- */
static long s22Examined = 0;
static long s22SplitG = 0, s22SplitT = 0, s22SplitBoth = 0;
static long s22CommonPrefixBand = 0, s22PrefixWalk = 0, s22PrefixMeet = 0;
static long s22SuffixBothNine = 0;
static long s22Shown = 0;

/* distinctness */
#define HASHCAP (1 << 25)
static uint64_t *hashTab;
static long hashN = 0, hashOverflow = 0;
static uint64_t fnv(const void *p, size_t len, uint64_t h) {
  const unsigned char *q = (const unsigned char *)p;
  for (size_t u = 0; u < len; u++) { h ^= q[u]; h *= 1099511628211ULL; }
  return h;
}
static int hashNew(uint64_t key) {
  if (key == 0) key = 1;
  if (hashN > (HASHCAP / 10) * 6) { hashOverflow++; return 1; }
  uint64_t idx = key & (HASHCAP - 1);
  while (hashTab[idx]) {
    if (hashTab[idx] == key) return 0;
    idx = (idx + 1) & (HASHCAP - 1);
  }
  hashTab[idx] = key; hashN++;
  return 1;
}

/* ------------------------------------------------------------- the sweep */

static int leastLegs(const int *G, int mg, const int *T, int mt, int p, int *bestW) {
  for (int k = 0; k <= KMAX; k++) {
    for (int st = p - 1; st <= p + 1; st++) {
      if (st < 0 || st > SPAN) continue;
      long a = widx[st][k], c = wcnt[st][k];
      for (long q = a; q < a + c; q++) {
        if (!foldsMask(G, mg, &walks[q])) continue;
        if (!foldsMask(T, mt, &walks[q])) continue;
        if (bestW) *bestW = (int)q;
        return k;
      }
    }
  }
  return -1;
}

/* ---- the deep search: walks of more legs than the stored family, on the fly ----
   Used only at the basepoints that no stored walk serves, so that the maximum
   least leg count is reported and not merely bounded below by KMAX + 1. */
static const int *dsG, *dsT; static int dsMG, dsMT, dsLegs; static long dsTried;
static int dsTgt[MAXKLEG + 4]; static Walk dsFound; static int dsHit;

static void deepRec(int start, int depth, int last, int dir) {
  if (dsHit) return;
  if (depth == dsLegs) {
    int times[MAXWALK];
    int len = buildTimes(start, dsTgt, dsLegs, times);
    if (len < 0) return;
    Walk w;
    fillWalk(&w, start, dsTgt, dsLegs, times, len);
    dsTried++;
    if (!foldsMask(dsMG < dsMT ? dsG : dsT, dsMG < dsMT ? dsMG : dsMT, &w)) return;
    if (!foldsMask(dsMG < dsMT ? dsT : dsG, dsMG < dsMT ? dsMT : dsMG, &w)) return;
    dsFound = w; dsHit = 1;
    return;
  }
  for (int d = -1; d <= 1; d += 2) {
    if (dir != 0 && d != dir) continue;
    if (d > 0) {
      for (int t = last + 1; t <= SPAN - 1 && !dsHit; t++) {
        dsTgt[depth] = t; deepRec(start, depth + 1, t, -1);
      }
    } else {
      for (int t = 1; t <= last - 1 && !dsHit; t++) {
        dsTgt[depth] = t; deepRec(start, depth + 1, t, +1);
      }
    }
  }
}

/* the least leg count above KMAX, searched up to KMAX + 3 legs; -1 if none */
static int deepLeast(const int *G, int mg, const int *T, int mt, int p, Walk *out, long *tried) {
  dsG = G; dsT = T; dsMG = mg; dsMT = mt; dsTried = 0;
  for (int k = KMAX + 1; k <= KMAX + 3 && k <= MAXKLEG + 3; k++) {
    dsLegs = k;
    for (int st = p - 1; st <= p + 1; st++) {
      if (st < 0 || st > SPAN) continue;
      dsHit = 0;
      deepRec(st, 0, st, 0);
      if (dsHit) { if (out) *out = dsFound; if (tried) *tried = dsTried; return k; }
    }
  }
  if (tried) *tried = dsTried;
  return -1;
}

static void printWalk(const Walk *w) {
  printf("%d", w->start);
  for (int q = 0; q < w->legs; q++) printf(" -> %d", w->tgt[q]);
}
static void fprintWalk(FILE *fp, const Walk *w) {
  fprintf(fp, "%d", w->start);
  for (int q = 0; q < w->legs; q++) fprintf(fp, " -> %d", w->tgt[q]);
}

/* the maximal stretch of the arm whose levels stay inside [lo, hi] */
static int restrictLen(const int *f, int m, int lo, int hi) {
  int u = 0;
  while (u < m && f[u] >= lo && f[u] <= hi) u++;
  return u;
}


/* =====================================================================
 * Batch 76: the extension law, decided exactly, and what it carries.
 * ===================================================================== */

/* A walk built on the fly: start, targets (any levels of [0, S], directions
   alternating, every leg of positive length), its times and its masks. */
typedef struct {
  int start, legs;
  int tgt[MAXKLEG + 2];
  int len;
  int times[128];
  int lo, hi;
  u128 mask[MASKLEV];
} W;

static int mkW(W *w, int start, const int *tgt, int legs) {
  w->start = start; w->legs = legs;
  int len = 0, cur = start;
  w->times[len++] = cur;
  for (int q = 0; q < legs; q++) {
    int t = tgt[q];
    w->tgt[q] = t;
    if (t == cur) return 0;
    int s = t > cur ? 1 : -1;
    while (cur != t) { cur += s; if (len >= 128) return 0; w->times[len++] = cur; }
  }
  w->len = len;
  w->lo = w->hi = start;
  for (int v = 0; v < MASKLEV; v++) w->mask[v] = 0;
  for (int u = 0; u < len; u++) {
    int c = w->times[u];
    if (c < w->lo) w->lo = c;
    if (c > w->hi) w->hi = c;
    for (int d = -1; d <= 1; d++) {
      int v = c + d;
      if (v >= 0 && v < MASKLEV) w->mask[v] |= ((u128)1) << u;
    }
  }
  return 1;
}

/* Decider 1 (masks).  The set of walk times reachable at the last index of
   f[0 .. m-1], started from the set `init` at index 0 (init is intersected
   with the times serving f[0]).  0 when the fold fails. */
static u128 propM(const int *f, int m, const W *w, u128 init) {
  u128 r = init & w->mask[f[0]];
  if (!r) return 0;
  for (int j = 1; j < m; j++) {
    r = (r | (r << 1) | (r >> 1)) & w->mask[f[j]];
    if (!r) return 0;
  }
  return r;
}

/* Decider 2 (arrays), sharing nothing with decider 1 but the walk's times. */
static u128 propA(const int *f, int m, const W *w, u128 init) {
  static char cur[128], nxt[128];
  int any = 0;
  for (int u = 0; u < w->len; u++) {
    int d = f[0] - w->times[u];
    cur[u] = ((init >> u) & 1) && d >= -1 && d <= 1;
    if (cur[u]) any = 1;
  }
  if (!any) return 0;
  for (int j = 1; j < m; j++) {
    any = 0;
    for (int u = 0; u < w->len; u++) nxt[u] = 0;
    for (int u = 0; u < w->len; u++) {
      if (!cur[u]) continue;
      for (int e = -1; e <= 1; e++) {
        int u2 = u + e;
        if (u2 < 0 || u2 >= w->len) continue;
        int d = f[j] - w->times[u2];
        if (d >= -1 && d <= 1) { nxt[u2] = 1; any = 1; }
      }
    }
    if (!any) return 0;
    memcpy(cur, nxt, (size_t)w->len);
  }
  u128 r = 0;
  for (int u = 0; u < w->len; u++) if (cur[u]) r |= ((u128)1) << u;
  return r;
}

static long auditCalls = 0, auditBad = 0;
static u128 propAudit(const int *f, int m, const W *w, u128 init, int force) {
  u128 a = propM(f, m, w, init);
  if (force || (auditCalls < 200000 && m < 20000)) {
    auditCalls++;
    if (propA(f, m, w, init) != a) auditBad++;
  }
  return a;
}

static int topBit(u128 x) { int b = -1; for (int u = 0; u < 128; u++) if ((x >> u) & 1) b = u; return b; }
static int lowBit(u128 x) { for (int u = 0; u < 128; u++) if ((x >> u) & 1) return u; return -1; }

/* one success of ExtendsSubBand: w' (start, targets), e, the sub-band, the
   truncated arm lengths and the two arrival sets */
typedef struct {
  int start, legs, tgt[MAXKLEG + 2];
  int e, wLegs, merged;      /* merged: e continues w''s last leg (w has w'.legs legs) */
  int lo, hi, mgR, mtR;
  u128 AG, AT;
  int fam;                   /* every target of w in [L+1, H-1] (the batch-75 family) */
} Succ;

#define MAXSUCC 4096
static Succ succ[MAXSUCC];
static int nSucc; static long nSuccAll;

/* ---- the enumeration of w: legs <= kw_max, targets in [0,S], alternating,
   last target in {1, S-1}; for each w folding both whole arms, every w' with
   w = w' + one leg to e is produced and classified. ---- */
static const int *eG, *eT; static int eMG, eMT, eP, eK;
static int eTg[MAXKLEG + 4];

/* statistics of the "why S-3" question, over every (w', w) with w folding */
static int q5MaxSpanByLegs[MAXKLEG + 4];     /* the widest minimal band of a w' folding its truncated arms, by legs of w */
static int q5ExactS1ByLegs[MAXKLEG + 4], q5ExactS2ByLegs[MAXKLEG + 4];
static int q5MaxSpanFamByLegs[MAXKLEG + 4];  /* the same, over w whose targets all lie in [L+1, H-1] */

static void consider(const W *w) {
  /* w folds both whole arms; its last target is e */
  int kw = w->legs;
  int e = w->tgt[kw - 1];
  int prev = kw >= 2 ? w->tgt[kw - 2] : w->start;
  int fam = 1;
  for (int q = 0; q < kw; q++) if (w->tgt[q] < 1 || w->tgt[q] > SPAN - 1) fam = 0;
  for (int mode = 0; mode < 2; mode++) {
    /* mode 0: w' = w without its last target;  mode 1: the last target replaced by t strictly between */
    int tlo, thi;
    if (mode == 0) { tlo = 0; thi = 0; }
    else {
      if (kw < 1) continue;
      tlo = (prev < e ? prev : e) + 1; thi = (prev < e ? e : prev) - 1;
      if (tlo > thi) continue;
    }
    for (int t = tlo; t <= thi; t++) {
      int tg[MAXKLEG + 4], lg;
      for (int q = 0; q < kw - 1; q++) tg[q] = w->tgt[q];
      if (mode == 0) lg = kw - 1; else { tg[kw - 1] = t; lg = kw; }
      W wp;
      if (!mkW(&wp, w->start, tg, lg)) continue;
      int lo = wp.lo < eP ? wp.lo : eP, hi = wp.hi > eP ? wp.hi : eP;
      int span = hi - lo;
      int mgR = restrictLen(eG, eMG, lo, hi), mtR = restrictLen(eT, eMT, lo, hi);
      u128 AG = propAudit(eG, mgR, &wp, 1, 0);
      if (!AG) continue;
      u128 AT = propAudit(eT, mtR, &wp, 1, 0);
      if (!AT) continue;
      /* w' serves the basepoint in its minimal band */
      int wl = (mode == 0) ? kw : kw;   /* legs of w */
      if (span < SPAN) {
        if (span > q5MaxSpanByLegs[wl]) q5MaxSpanByLegs[wl] = span;
        if (fam && span > q5MaxSpanFamByLegs[wl]) q5MaxSpanFamByLegs[wl] = span;
        /* exact bands of span S-1 and S-2 containing [lo, hi] */
        for (int d = 1; d <= 2; d++) {
          int bs = SPAN - d;
          if (span > bs) continue;
          for (int a = 0; a + bs <= SPAN; a++) {
            int b = a + bs;
            if (a > lo || b < hi) continue;
            int g = restrictLen(eG, eMG, a, b), h = restrictLen(eT, eMT, a, b);
            if (!propM(eG, g, &wp, 1)) continue;
            if (!propM(eT, h, &wp, 1)) continue;
            if (d == 1) q5ExactS1ByLegs[wl] = 1; else q5ExactS2ByLegs[wl] = 1;
            break;
          }
        }
      }
      /* ExtendsSubBand at k = eK: w' has at most k-1 legs, span <= S-3 */
      if (lg <= eK - 1 && span <= SPAN - 3) {
        nSuccAll++;
        if (nSucc < MAXSUCC) {
          Succ *s = &succ[nSucc++];
          s->start = w->start; s->legs = lg;
          for (int q = 0; q < lg; q++) s->tgt[q] = tg[q];
          s->e = e; s->wLegs = kw; s->merged = mode;
          s->lo = lo; s->hi = hi; s->mgR = mgR; s->mtR = mtR; s->AG = AG; s->AT = AT;
          s->fam = fam;
        }
      }
    }
  }
}

static long enumTried;
static void enumRec(int start, int depth, int maxLegs, int last, int dir) {
  /* a complete walk whenever the last target is an extreme-neighbour */
  if (depth >= 1 && (eTg[depth - 1] == 1 || eTg[depth - 1] == SPAN - 1)) {
    W w;
    if (mkW(&w, start, eTg, depth)) {
      enumTried++;
      const int *f1 = eMG < eMT ? eG : eT, *f2 = eMG < eMT ? eT : eG;
      int m1 = eMG < eMT ? eMG : eMT, m2 = eMG < eMT ? eMT : eMG;
      if (propM(f1, m1, &w, 1) && propM(f2, m2, &w, 1)) consider(&w);
    }
  }
  if (depth == maxLegs) return;
  for (int d = -1; d <= 1; d += 2) {
    if (dir != 0 && d != dir) continue;
    if (d > 0) for (int t = last + 1; t <= SPAN; t++) { eTg[depth] = t; enumRec(start, depth + 1, maxLegs, t, -1); }
    else for (int t = 0; t <= last - 1; t++) { eTg[depth] = t; enumRec(start, depth + 1, maxLegs, t, +1); }
  }
}

/* Q5 (A): the least number of legs of a walk confined to [a, b], based within
   one of p, folding both arms truncated at their first exit from [a, b]. */
static int q5Found; static int q5a, q5b, q5g, q5h;
static void q5Rec(int start, int depth, int legs, int last, int dir) {
  if (q5Found) return;
  if (depth == legs) {
    W w;
    if (!mkW(&w, start, eTg, legs)) return;
    if (propM(eG, q5g, &w, 1) && propM(eT, q5h, &w, 1)) q5Found = 1;
    return;
  }
  for (int d = -1; d <= 1 && !q5Found; d += 2) {
    if (dir != 0 && d != dir) continue;
    if (d > 0) for (int t = last + 1; t <= q5b && !q5Found; t++) { eTg[depth] = t; q5Rec(start, depth + 1, legs, t, -1); }
    else for (int t = q5a; t <= last - 1 && !q5Found; t++) { eTg[depth] = t; q5Rec(start, depth + 1, legs, t, +1); }
  }
}
static int q5Least(int a, int b, int maxLegs) {
  q5a = a; q5b = b;
  q5g = restrictLen(eG, eMG, a, b); q5h = restrictLen(eT, eMT, a, b);
  for (int legs = 0; legs <= maxLegs; legs++)
    for (int st = eP - 1; st <= eP + 1; st++) {
      if (st < a || st > b) continue;
      q5Found = 0;
      q5Rec(st, 0, legs, st, 0);
      if (q5Found) return legs;
    }
  return -1;
}

/* ---- counters of batch 76 ---- */
static long x76Examined = 0, x76ByK[MAXKLEG + 2], x76OkByK[MAXKLEG + 2];
static long x76Fail = 0, x76Merged = 0, x76SpanHist[MAXLEV];
static long x76SpanS1 = 0, x76SpanS2 = 0;   /* successes at minimal span S-1, S-2: impossible by definition (<= S-3); kept as a check */
static long x76SuccCount = 0;
/* Q2 */
static long q2BothMax = 0, q2BothMin = 0, q2BothAny = 0, q2AnyPair = 0, q2None = 0;
static long q2ArmMaxOk[2], q2ArmMinOk[2], q2ArmAnyOk[2], q2ArmUntrunc[2], q2Arms = 0;
static long q2Shown = 0;
static long q2PairsTried = 0, q2PairsAllOk = 0;
/* Q4 */
static long q4Dir[2];                            /* 0 = down (to L+1), 1 = up (to H-1) */
static long q4First[2][4];                       /* first exit: 0 D, 1 U, 2 none, 3 tie-mixed */
static long q4Sides[2][3][3];                    /* G side x T side: 0 D, 1 U, 2 none */
static long q4Mid[2][3];                         /* p below / at / above the middle of the sub-band */
static long q4Last[2][3];                        /* last level of w': 0 bottom of sub-band, 1 top, 2 inner */
static long q4LastLeg[2][3];                     /* last leg of w': 0 descent, 1 ascent, 2 none */
static long q4BothDirs = 0;
static long q4Merged[2];
static long q4WideSpan[MAXLEV], q4WideEnds[2][4], q4WideFirst[2][4], q4Cover[2][4];
/* Q5 */
static long q5Examined = 0;
static long q5A_S1 = 0, q5A_S2 = 0, q5A_S1least[MAXKLEG + 3], q5A_S2least[MAXKLEG + 3];
static long q5A_S1none = 0, q5A_S2none = 0;
static long q5B_legsK_S1 = 0, q5B_legsK_S2 = 0, q5B_legsK1_S1 = 0, q5B_legsK1_S2 = 0;
static long q5B_maxSpanFam[MAXLEV], q5B_noneFam = 0;
static long q5B_maxSpanK[MAXLEV], q5B_maxSpanK1[MAXLEV], q5B_noneK1 = 0;
static long q5CAP = 1000000;
static long q5Done[MAXLEV][MAXKLEG + 2];

static void fprintArr(FILE *fp, const int *a, int m) {
  for (int u = 0; u < m; u++) fprintf(fp, "%d%c", a[u], u + 1 == m ? '\n' : ' ');
}

static int sideOf(const int *f, int m, int mR, int lo, int hi) {
  if (mR >= m) return 2;
  return f[mR] > hi ? 1 : 0;
  (void)lo;
}

static void section76(const int *G, int mg, const int *T, int mt, int p, int k,
                      int n, int i, const char *tag) {
  eG = G; eT = T; eMG = mg; eMT = mt; eP = p; eK = k;
  nSucc = 0; nSuccAll = 0; enumTried = 0;
  for (int u = 0; u < MAXKLEG + 4; u++) { q5MaxSpanByLegs[u] = -1; q5MaxSpanFamByLegs[u] = -1; q5ExactS1ByLegs[u] = 0; q5ExactS2ByLegs[u] = 0; }
  /* one enumeration over walks of at most k + 1 legs serves the extension law
     (w of at most k legs) and the "why S-3" question (at most k + 1) */
  int doQ5 = q5Done[p][k] < q5CAP;
  int maxLegs = doQ5 ? k + 1 : k;
  for (int st = p - 1; st <= p + 1; st++) {
    if (st < 0 || st > SPAN) continue;
    enumRec(st, 0, maxLegs, st, 0);
  }
  x76Examined++; x76ByK[k]++;
  if (nSucc == 0) {
    x76Fail++;
    printf("  EXTENDSSUBBAND FAILS [%ld] %-16s n=%5d i=%5d level=%d k=%d |G|=%5d |T|=%5d\n",
           x76Fail, tag, n, i, p, k, mg, mt);
    if (x76Fail <= 4) {
      char fn[80];
      snprintf(fn, sizeof(fn), "witness-batch76-ext-span%d-%ld.txt", SPAN, x76Fail);
      FILE *fp = fopen(fn, "w");
      if (fp) { fprintf(fp, "%d %d %d\n", n, i, k); fprintArr(fp, rho, n); fprintArr(fp, sig, n); fclose(fp); }
    }
  } else {
    x76OkByK[k]++;
    x76SuccCount += nSuccAll;
    /* canonical success: widest sub-band, then longest shorter truncated arm, then first */
    int best = 0;
    for (int s = 1; s < nSucc; s++) {
      int sb = succ[best].hi - succ[best].lo, ss = succ[s].hi - succ[s].lo;
      int tb = succ[best].mgR < succ[best].mtR ? succ[best].mgR : succ[best].mtR;
      int ts = succ[s].mgR < succ[s].mtR ? succ[s].mgR : succ[s].mtR;
      if (succ[s].fam != succ[best].fam) { if (succ[s].fam) best = s; continue; }
      if (ss > sb || (ss == sb && ts > tb)) best = s;
    }
    Succ *c = &succ[best];
    int span = c->hi - c->lo;
    x76SpanHist[span]++;
    if (span == SPAN - 1) x76SpanS1++;
    if (span == SPAN - 2) x76SpanS2++;
    if (c->merged) x76Merged++;

    /* ---------------- Q2: the suffixes ---------------- */
    int anyPair = 0;
    int canonMax = 1, canonMin = 1, canonAny = 1;
    for (int s = 0; s < nSucc; s++) {
      Succ *x = &succ[s];
      int tg[MAXKLEG + 4];
      for (int q = 0; q < x->legs; q++) tg[q] = x->tgt[q];
      tg[x->legs] = x->e;
      W w;
      if (!mkW(&w, x->start, tg, x->legs + 1)) {
        /* merged: w' + e continues the last leg; build w with the last target replaced */
        tg[x->legs - 1] = x->e;
        mkW(&w, x->start, tg, x->legs);
      }
      int okAll = 1;
      for (int arm = 0; arm < 2; arm++) {
        const int *f = arm ? T : G; int m = arm ? mt : mg; int mR = arm ? x->mtR : x->mgR;
        u128 A = arm ? x->AT : x->AG;
        int okMax, okMin, okAny;
        if (mR >= m) { okMax = okMin = okAny = 1; }
        else {
          int sidx = mR - 1;       /* the last index of the truncated arm: the split index */
          okMax = propAudit(f + sidx, m - sidx, &w, ((u128)1) << topBit(A), s == best) != 0;
          okMin = propAudit(f + sidx, m - sidx, &w, ((u128)1) << lowBit(A), s == best) != 0;
          okAny = propAudit(f + sidx, m - sidx, &w, A, s == best) != 0;
        }
        if (s == best) {
          q2Arms++;
          if (mR >= m) q2ArmUntrunc[arm]++;
          if (okMax) q2ArmMaxOk[arm]++;
          if (okMin) q2ArmMinOk[arm]++;
          if (okAny) q2ArmAnyOk[arm]++;
          if (!okMax) canonMax = 0;
          if (!okMin) canonMin = 0;
          if (!okAny) canonAny = 0;
        }
        if (!okAny) okAll = 0;
      }
      q2PairsTried++;
      if (okAll) { anyPair = 1; q2PairsAllOk++; }
    }
    if (canonMax) q2BothMax++;
    if (canonMin) q2BothMin++;
    if (canonAny) q2BothAny++;
    if (anyPair) q2AnyPair++;
    else {
      q2None++;
      if (q2Shown < 6) {
        q2Shown++;
        printf("  Q2 NO SUFFIX REPAIR [%ld] %-16s n=%5d i=%5d level=%d k=%d |G|=%5d |T|=%5d"
               "  w' = %d", q2Shown, tag, n, i, p, k, mg, mt, c->start);
        for (int q = 0; q < c->legs; q++) printf(" -> %d", c->tgt[q]);
        printf("  e = %d  band [%d,%d]  truncated %d, %d\n", c->e, c->lo, c->hi, c->mgR, c->mtR);
        char fn[80];
        snprintf(fn, sizeof(fn), "witness-batch76-q2-span%d-%ld.txt", SPAN, q2Shown);
        FILE *fp = fopen(fn, "w");
        if (fp) {
          fprintf(fp, "%d %d %d\n", n, i, k); fprintArr(fp, rho, n); fprintArr(fp, sig, n);
          fprintf(fp, "wprime %d %d %d", c->lo, c->hi, c->start);
          for (int q = 0; q < c->legs; q++) fprintf(fp, " %d", c->tgt[q]);
          fprintf(fp, "\nappend %d\n", c->e);
          fclose(fp);
        }
      }
    }

    /* ---------------- Q4: which extreme ---------------- */
    {
      int dir = (c->e == SPAN - 1) ? 1 : 0;
      q4Dir[dir]++;
      if (c->merged) q4Merged[dir]++;
      int sg = sideOf(G, mg, c->mgR, c->lo, c->hi), sT = sideOf(T, mt, c->mtR, c->lo, c->hi);
      q4Sides[dir][sg][sT]++;
      int first;
      if (sg == 2 && sT == 2) first = 2;
      else if (sg == 2) first = sT;
      else if (sT == 2) first = sg;
      else if (c->mgR < c->mtR) first = sg;
      else if (c->mtR < c->mgR) first = sT;
      else first = (sg == sT) ? sg : 3;
      q4First[dir][first]++;
      int twice = 2 * p, mid = c->lo + c->hi;
      q4Mid[dir][twice < mid ? 0 : twice == mid ? 1 : 2]++;
      int last = c->legs ? c->tgt[c->legs - 1] : c->start;
      q4Last[dir][last == c->lo ? 0 : last == c->hi ? 1 : 2]++;
      int prevl = c->legs >= 2 ? c->tgt[c->legs - 2] : c->start;
      q4LastLeg[dir][c->legs == 0 ? 2 : (last > prevl ? 1 : 0)]++;
      /* the widest band [a, b] containing w''s levels and p at which w' still folds both truncated arms */
      W wc;
      { int tg2[MAXKLEG + 4]; for (int q = 0; q < c->legs; q++) tg2[q] = c->tgt[q]; mkW(&wc, c->start, tg2, c->legs); }
      int ba = c->lo, bb = c->hi;
      for (int a = 0; a <= c->lo; a++) for (int b = c->hi; b <= SPAN; b++) {
        if (b - a <= bb - ba) continue;
        int g = restrictLen(G, mg, a, b), h = restrictLen(T, mt, a, b);
        if (!propM(G, g, &wc, 1) || !propM(T, h, &wc, 1)) continue;
        ba = a; bb = b;
      }
      q4WideSpan[bb - ba]++;
      q4WideEnds[dir][(ba == 0 ? 1 : 0) + (bb == SPAN ? 2 : 0)]++;
      { int g = restrictLen(G, mg, ba, bb), h = restrictLen(T, mt, ba, bb);
        int s1 = sideOf(G, mg, g, ba, bb), s2 = sideOf(T, mt, h, ba, bb);
        int f2;
        if (s1 == 2 && s2 == 2) f2 = 2; else if (s1 == 2) f2 = s2; else if (s2 == 2) f2 = s1;
        else if (g < h) f2 = s1; else if (h < g) f2 = s2; else f2 = (s1 == s2) ? s1 : 3;
        q4WideFirst[dir][f2]++; }
      q4Cover[dir][(c->lo <= 1 ? 1 : 0) + (c->hi >= SPAN - 1 ? 2 : 0)]++;
      int has[2] = {0, 0};
      for (int s = 0; s < nSucc; s++) has[succ[s].e == SPAN - 1 ? 1 : 0] = 1;
      if (has[0] && has[1]) q4BothDirs++;
    }
  }

  /* ---------------- Q5: why S-3 ---------------- */
  if (doQ5) {
    q5Done[p][k]++;
    q5Examined++;
    /* (A) the arms: some walk of a band of span S-1 / S-2 folds its truncated arms */
    int bestS1 = -1, bestS2 = -1;
    for (int d = 1; d <= 2; d++) {
      int bs = SPAN - d;
      for (int a = 0; a + bs <= SPAN; a++) {
        int b = a + bs;
        if (p < a || p > b) continue;
        int l = q5Least(a, b, k + 1);
        if (l < 0) continue;
        if (d == 1) { if (bestS1 < 0 || l < bestS1) bestS1 = l; }
        else { if (bestS2 < 0 || l < bestS2) bestS2 = l; }
      }
    }
    if (bestS1 >= 0) { q5A_S1++; q5A_S1least[bestS1]++; } else q5A_S1none++;
    if (bestS2 >= 0) { q5A_S2++; q5A_S2least[bestS2]++; } else q5A_S2none++;
    /* (B) least walks: a one-leg extension from a band of span S-1 / S-2, with k or k+1 legs */
    if (q5ExactS1ByLegs[k]) q5B_legsK_S1++;
    if (q5ExactS2ByLegs[k]) q5B_legsK_S2++;
    if (q5ExactS1ByLegs[k + 1]) q5B_legsK1_S1++;
    if (q5ExactS2ByLegs[k + 1]) q5B_legsK1_S2++;
    int mk = -1;
    for (int u = 0; u <= k; u++) if (q5MaxSpanByLegs[u] > mk) mk = q5MaxSpanByLegs[u];
    if (mk >= 0) q5B_maxSpanK[mk]++;
    { int mf = -1; for (int u = 0; u <= k; u++) if (q5MaxSpanFamByLegs[u] > mf) mf = q5MaxSpanFamByLegs[u];
      if (mf >= 0) q5B_maxSpanFam[mf]++; else q5B_noneFam++; }
    if (q5MaxSpanByLegs[k + 1] >= 0) q5B_maxSpanK1[q5MaxSpanByLegs[k + 1]]++; else q5B_noneK1++;
  }
}

static void report76(void) {
  printf("\n======== B76 S2.3  ExtendsSubBand at the least leg count, decided exactly ========\n");
  printf("  sampled basepoints of least leg count k >= 3: %ld\n", x76Examined);
  for (int k = 3; k <= KMAX; k++) printf("    k=%d: %ld of %ld satisfy ExtendsSubBand\n", k, x76OkByK[k], x76ByK[k]);
  printf("  basepoints at which ExtendsSubBand FAILS: %ld\n", x76Fail);
  printf("  (w', w) pairs witnessing it, over all satisfied basepoints: %ld\n", x76SuccCount);
  printf("  canonical witness (widest sub-band, then longest truncated arms): minimal sub-band span:\n");
  for (int s = 0; s < MAXLEV; s++) if (x76SpanHist[s]) printf("     span %2d (S-%d): %ld\n", s, SPAN - s, x76SpanHist[s]);
  printf("  canonical witnesses whose appended leg continues w''s last leg (w has k-1 legs): %ld\n", x76Merged);

  printf("\n======== B76 S2.2  the suffixes ========\n");
  printf("  basepoints: %ld (those satisfying ExtendsSubBand)\n", x76Examined - x76Fail);
  printf("  canonical witness, both suffixes fold from the LATEST arrival time of the truncated fold: %ld\n", q2BothMax);
  printf("  canonical witness, both suffixes fold from the EARLIEST arrival time: %ld\n", q2BothMin);
  printf("  canonical witness, each suffix folds from SOME arrival time of its own arm: %ld\n", q2BothAny);
  printf("  some witness (w', w) at which each suffix folds from some arrival time of its own arm: %ld\n", q2AnyPair);
  printf("  basepoints at which no witness and no arrival time serves: %ld\n", q2None);
  for (int arm = 0; arm < 2; arm++)
    printf("  arm %s (canonical witness): not truncated %ld; latest ok %ld; earliest ok %ld; some ok %ld\n",
           arm ? "T" : "G", q2ArmUntrunc[arm], q2ArmMaxOk[arm], q2ArmMinOk[arm], q2ArmAnyOk[arm]);
  printf("  over all witnesses: %ld pairs tried, %ld with both suffixes folding from some own arrival time\n",
         q2PairsTried, q2PairsAllOk);

  printf("\n======== B76 S2.4  which extreme ========\n");
  printf("  appended leg to L+1 (down): %ld;  to H-1 (up): %ld;  basepoints admitting both: %ld\n",
         q4Dir[0], q4Dir[1], q4BothDirs);
  printf("  merged (continuing w''s last leg): down %ld, up %ld\n", q4Merged[0], q4Merged[1]);
  const char *sd[4] = {"D", "U", "none", "tie-mixed"};
  printf("  (a) side of the FIRST exit from the sub-band (by arm index):\n");
  for (int dir = 0; dir < 2; dir++) {
    printf("     appended %s:", dir ? "up  " : "down");
    for (int u = 0; u < 4; u++) printf("  %s %ld", sd[u], q4First[dir][u]);
    printf("\n");
  }
  printf("  (a') exit side of G x exit side of T:\n");
  for (int dir = 0; dir < 2; dir++) {
    printf("     appended %s:", dir ? "up  " : "down");
    for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) if (q4Sides[dir][a][b])
      printf("  G%s/T%s %ld", sd[a], sd[b], q4Sides[dir][a][b]);
    printf("\n");
  }
  printf("  (b) the basepoint's level against the middle of the sub-band:\n");
  for (int dir = 0; dir < 2; dir++)
    printf("     appended %s:  below %ld  middle %ld  above %ld\n", dir ? "up  " : "down",
           q4Mid[dir][0], q4Mid[dir][1], q4Mid[dir][2]);
  printf("  (c) the last target of w' (its last level) in the sub-band, and w''s last leg:\n");
  for (int dir = 0; dir < 2; dir++)
    printf("     appended %s:  at the sub-band's bottom %ld  top %ld  inner %ld | last leg descent %ld ascent %ld none %ld\n",
           dir ? "up  " : "down", q4Last[dir][0], q4Last[dir][1], q4Last[dir][2],
           q4LastLeg[dir][0], q4LastLeg[dir][1], q4LastLeg[dir][2]);

  printf("  (d) the widest band [a,b] containing w''s levels and p at which the canonical w' still folds both\n"
         "      truncated arms -- the band of the ARMS, against the minimal band of the WALK's levels:\n");
  for (int s = 0; s < MAXLEV; s++) if (q4WideSpan[s]) printf("     span %2d (S-%d): %ld\n", s, SPAN - s, q4WideSpan[s]);
  const char *en[4] = {"neither end", "a = L", "b = H", "a = L and b = H"};
  for (int dir = 0; dir < 2; dir++) {
    printf("     appended %s:", dir ? "up  " : "down");
    for (int u = 0; u < 4; u++) printf("  %s %ld", en[u], q4WideEnds[dir][u]);
    printf("\n");
  }
  printf("  (e) the side of the first exit from that widest band:\n");
  for (int dir = 0; dir < 2; dir++) {
    printf("     appended %s:", dir ? "up  " : "down");
    for (int u = 0; u < 4; u++) printf("  %s %ld", sd[u], q4WideFirst[dir][u]);
    printf("\n");
  }
  const char *cv[4] = {"covers neither extreme", "covers L only", "covers H only", "covers both"};
  printf("  (f) whether w' comes within one of L (lowest level <= L+1) or of H (highest >= H-1):\n");
  for (int dir = 0; dir < 2; dir++) {
    printf("     appended %s:", dir ? "up  " : "down");
    for (int u = 0; u < 4; u++) printf("  %s %ld", cv[u], q4Cover[dir][u]);
    printf("\n");
  }

  printf("\n======== B76 S2.5  why S-3 ========\n");
  printf("  basepoints examined: %ld\n", q5Examined);
  printf("  (A) some walk confined to a band of span S-1 folds that band's truncated arms: %ld (none within k+1 legs: %ld)\n",
         q5A_S1, q5A_S1none);
  printf("      least legs:"); for (int u = 0; u <= MAXKLEG + 2; u++) if (q5A_S1least[u]) printf("  %d: %ld", u, q5A_S1least[u]); printf("\n");
  printf("  (A) some walk confined to a band of span S-2 folds that band's truncated arms: %ld (none within k+1 legs: %ld)\n",
         q5A_S2, q5A_S2none);
  printf("      least legs:"); for (int u = 0; u <= MAXKLEG + 2; u++) if (q5A_S2least[u]) printf("  %d: %ld", u, q5A_S2least[u]); printf("\n");
  printf("  (B) a walk of k legs (least) that is a one-leg extension of a w' folding the truncated arms\n"
         "      of a band of span exactly S-1: %ld;  of span exactly S-2: %ld\n", q5B_legsK_S1, q5B_legsK_S2);
  printf("  (B) the same with k+1 legs (not least): span S-1: %ld;  span S-2: %ld\n", q5B_legsK1_S1, q5B_legsK1_S2);
  printf("  (B) the widest minimal band of such a w', over extensions of at most k legs:\n");
  for (int s = 0; s < MAXLEV; s++) if (q5B_maxSpanK[s]) printf("     span %2d (S-%d): %ld\n", s, SPAN - s, q5B_maxSpanK[s]);
  printf("  (B) the same, over extensions w whose targets all lie in [L+1, H-1] (the batch-75 family):\n");
  for (int s = 0; s < MAXLEV; s++) if (q5B_maxSpanFam[s]) printf("     span %2d (S-%d): %ld\n", s, SPAN - s, q5B_maxSpanFam[s]);
  printf("     none in the family: %ld\n", q5B_noneFam);
  printf("  (B) the widest minimal band of such a w', over extensions of exactly k+1 legs:\n");
  for (int s = 0; s < MAXLEV; s++) if (q5B_maxSpanK1[s]) printf("     span %2d (S-%d): %ld\n", s, SPAN - s, q5B_maxSpanK1[s]);
  printf("     none with k+1 legs: %ld\n", q5B_noneK1);
  printf("\n  audit: the fold decided by masks against arrays on %ld calls (every canonical-witness\n"
         "  suffix, and a sample of the rest): %ld disagreements\n", auditCalls, auditBad);
}
/* ------------------------------------------------------------- scanPair */

static void scanPair(int n, const char *tag) {
  nPairs++;
  for (int u = 0; u < n; u++) { nLinks++; if (sig[u] != rho[u]) nNonThin++; }
  {
    uint64_t h = fnv(rho, sizeof(int) * (size_t)n, 14695981039346656037ULL);
    h = fnv(sig, sizeof(int) * (size_t)n, h);
    if (hashNew(h ^ 0xabcdef01ULL)) nDistinctPairs++;
  }
  for (int i = 0; i < n; i++) {
    int p = rho[i];
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
    for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
    nBase++;
    if (mg < armMin) armMin = mg;
    if (mt < armMin) armMin = mt;
    if (mg > armMax) armMax = mg;
    if (mt > armMax) armMax = mt;
    uint64_t h = fnv(armG, sizeof(int) * (size_t)mg, 14695981039346656037ULL);
    h = fnv(armT, sizeof(int) * (size_t)mt, h);
    int fresh = hashNew(h ^ 0x5eed1234ULL);
    if (!fresh) continue;
    nBaseDistinct++;
    if (curThin) nBaseThin++;

    int bw = -1;
    int k = leastLegs(armG, mg, armT, mt, p, &bw);
    if (k < 0) {
      kNone++; kNoneByLevel[p]++;
      if (curThin) kNoneThin++;
      if (deepDone < DEEPCAP) {
        deepDone++;
        Walk dw; long tried = 0;
        int dk = deepLeast(armG, mg, armT, mt, p, &dw, &tried);
        printf("  NO WALK OF AT MOST %d LEGS [%ld] %-16s n=%5d i=%5d level=%d |G|=%5d |T|=%5d\n",
               KMAX, deepDone, tag, n, i, p, mg, mt);
        if (dk > 0) {
          deepFound[dk]++;
          printf("      the deep search (walks of more legs, enumerated on the fly, %ld tried)"
                 " finds a walk of %d legs: ", tried, dk);
          printWalk(&dw);
          printf("\n");
          if (dk > maxLegsSeen) {
            maxLegsSeen = dk;
            for (int l = 0; l < MAXLEV; l++) maxLegsByLevel[l] = 0;
          }
          if (dk == maxLegsSeen) maxLegsByLevel[p]++;
          if (!witnessWritten[dk <= MAXKLEG + 1 ? dk : MAXKLEG + 1]) {
            witnessWritten[dk <= MAXKLEG + 1 ? dk : MAXKLEG + 1] = 1;
            char fn[64];
            snprintf(fn, sizeof(fn), "witness-batch76-span%d-k%d.txt", SPAN, dk);
            FILE *fp = fopen(fn, "w");
            if (fp) {
              fprintf(fp, "%d %d %d\n", n, i, dk);
              for (int t = 0; t < n; t++) fprintf(fp, "%d%c", rho[t], t + 1 == n ? '\n' : ' ');
              for (int t = 0; t < n; t++) fprintf(fp, "%d%c", sig[t], t + 1 == n ? '\n' : ' ');
              fprintf(fp, "walk ");
              fprintWalk(fp, &dw);
              fprintf(fp, "\n");
              fclose(fp);
            }
          }
        } else {
          deepFound[0]++;
          printf("      the deep search finds none of at most %d legs either (%ld tried)\n",
                 KMAX + 3, tried);
        }
      }
    } else {
      kCount[k]++; kByLevel[p][k]++;
      if (curThin) { kCountThin[k]++; kByLevelThin[p][k]++; }
      if (k > maxLegsSeen) {
        maxLegsSeen = k;
        for (int l = 0; l < MAXLEV; l++) maxLegsByLevel[l] = 0;
      }
      if (k == maxLegsSeen) maxLegsByLevel[p]++;
      if (k >= 5 && shownFive < 8) {
        shownFive++;
        printf("  least %d legs [%ld] %-16s n=%4d i=%4d level=%d |G|=%4d |T|=%4d  walk ",
               k, shownFive, tag, n, i, p, mg, mt);
        printWalk(&walks[bw]);
        printf("  (%s)\n", curThin ? "thin" : "general");
      }
      /* the first basepoint attaining each leg count from four up, written out in full */
      if (k >= 4 && !witnessWritten[k]) {
        witnessWritten[k] = 1; shownMax++;
        char fn[64];
        snprintf(fn, sizeof(fn), "witness-batch76-span%d-k%d.txt", SPAN, k);
        FILE *fp = fopen(fn, "w");
        if (fp) {
          fprintf(fp, "%d %d %d\n", n, i, k);
          for (int t = 0; t < n; t++) fprintf(fp, "%d%c", rho[t], t + 1 == n ? '\n' : ' ');
          for (int t = 0; t < n; t++) fprintf(fp, "%d%c", sig[t], t + 1 == n ? '\n' : ' ');
          fprintf(fp, "walk ");
          fprintWalk(fp, &walks[bw]);
          fprintf(fp, "\n");
          fclose(fp);
        }
      }
      /* the sample of batch 75 section 2.1: the basepoints of least leg count at least three */
      if (k >= 3) {
        hardSeen[p]++;
        if (hardDone[p][k] < HARDPERLEVEL) {
          hardDone[p][k]++;
          section76(armG, mg, armT, mt, p, k, n, i, tag);
        }
      }
    }
    /* the audit sample: the bitmask fold against the array fold */
    /* long arms are sampled too, but fewer of them: the array propagation is
       O(arm length x walk length) and the arms here run to tens of thousands */
    if (bruteSamples < ((mg < 6000 && mt < 6000) ? 3000 : 400)) {
      long q0 = widx[p][2];
      for (long q = q0; q < q0 + wcnt[p][2] && q < q0 + 6; q++) {
        bruteSamples++;
        if (foldsMask(armG, mg, &walks[q]) != foldsBrute(armG, mg, &walks[q])) bruteBad++;
        if (foldsMask(armT, mt, &walks[q]) != foldsBrute(armT, mt, &walks[q])) bruteBad++;
      }
    }
  }
}

/* ------------------------------------------------- the corpus of pairs ---- */

static long shaveCap = 12, fillCap = 12;
static long MAXPAIRLEN = 3000;

static void runBase(const int *v, int n, const char *tag, long mixes) {
  if (n < 30 || n >= MAXN || n > MAXPAIRLEN) return;
  {
    int lo = v[0], hi = v[0];
    for (int u = 0; u < n; u++) { if (v[u] < lo) lo = v[u]; if (v[u] > hi) hi = v[u]; }
    if (lo != 0 || hi != SPAN) return;
  }
  nSourceKinds++;
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  variantsTried++;
  curThin = 1;
  if (crookedGen(rho, sig, n)) { variantsFaithful++; scanPair(n, tag); }
  else return;
  curThin = 0;

  long done = 0;
  for (int pk = 1; pk + 1 < n && done < shaveCap; pk++) {
    if (!(v[pk] > v[pk-1] && v[pk] > v[pk+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    rho[pk] = v[pk] - 1;
    variantsTried++;
    if (!crookedGen(rho, sig, n)) continue;
    variantsFaithful++; done++;
    scanPair(n, tag);
  }
  done = 0;
  for (int vl = 1; vl + 1 < n && done < fillCap; vl++) {
    if (!(v[vl] < v[vl-1] && v[vl] < v[vl+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    sig[vl] = v[vl] + 1;
    variantsTried++;
    if (!crookedGen(rho, sig, n)) continue;
    variantsFaithful++; done++;
    scanPair(n, tag);
  }
  for (long it = 0; it < mixes; it++) {
    int rate = (it % 2) ? 2 : 3;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) { if (random() % rate == 0) rho[j] = v[j] - 1; }
      else if (v[j] < v[j-1] && v[j] < v[j+1]) { if (random() % rate == 0) sig[j] = v[j] + 1; }
    }
    variantsTried++;
    if (!crookedGen(rho, sig, n)) continue;
    variantsFaithful++;
    scanPair(n, tag);
  }
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  for (int j = 1; j + 1 < n; j++) {
    if (v[j] > v[j-1] && v[j] > v[j+1]) rho[j] = v[j] - 1;
    else if (v[j] < v[j-1] && v[j] < v[j+1]) sig[j] = v[j] + 1;
  }
  variantsTried++;
  if (crookedGen(rho, sig, n)) { variantsFaithful++; scanPair(n, tag); }
  printf("    [%-16s n=%4d] pairs so far %ld, distinct basepoints %ld, %lds\n",
         tag, n, nPairs, nBaseDistinct, (long)(time(NULL) - T0));
}

static int windowSpanS(const int *v, int n, int a, int b, int *out) {
  if (a < 0 || b >= n || b - a + 1 < 30) return 0;
  if (b - a + 1 > MAXPAIRLEN) b = a + (int)MAXPAIRLEN - 1;
  if (b - a + 1 >= MAXN) return 0;
  int lo = v[a], hi = v[a];
  for (int t = a; t <= b; t++) { if (v[t] < lo) lo = v[t]; if (v[t] > hi) hi = v[t]; }
  if (hi - lo != SPAN) return 0;
  for (int t = a; t <= b; t++) out[t - a] = v[t] - lo;
  return b - a + 1;
}

static int wbuf[MAXN];

int main(int argc, char **argv) {
  SPAN = (argc > 1) ? atoi(argv[1]) : 10;
  long windows = (argc > 2) ? atol(argv[2]) : 24;
  long mixes = (argc > 3) ? atol(argv[3]) : 4;
  unsigned seed = (argc > 4) ? (unsigned)atoi(argv[4]) : 75u;
  KMAX = (argc > 5) ? atoi(argv[5]) : 5;
  MAXPAIRLEN = (argc > 6) ? atol(argv[6]) : 3000;
  HARDPERLEVEL = (argc > 7) ? atol(argv[7]) : 250;
  if (argc > 8) { shaveCap = atol(argv[8]); fillCap = shaveCap; }
  DOWINDOWS = (argc > 9) ? atoi(argv[9]) : 1;
  DEEPCAP = (argc > 10) ? atol(argv[10]) : 20;
  q5CAP = (argc > 11) ? atol(argv[11]) : 1000000;
  srandom(seed);
  setvbuf(stdout, NULL, _IOLBF, 0);
  T0 = time(NULL);

  walks = (Walk *)malloc(sizeof(Walk) * MAXWALKS);
  hashTab = (uint64_t *)calloc(HASHCAP, sizeof(uint64_t));
  if (!walks || !hashTab) { printf("out of memory\n"); return 1; }

  buildAllWalks();

  printf("census-batch76: the fold at span %d.  L = 0, H = %d.\n", SPAN, SPAN);
  printf("seed=%u windows-per-chain=%ld mixtures-per-chain=%ld kmax=%d max-pair-length=%ld"
         " hard-sample-per-level-and-leg-count=%ld shave/fill-cap=%ld windows=%d\n",
         seed, windows, mixes, KMAX, MAXPAIRLEN, HARDPERLEVEL, shaveCap, DOWINDOWS);
  printf("walks of at most %d legs, based within one of a level: %ld in all\n", KMAX, nWalks);
  for (int k = 0; k <= KMAX; k++) {
    long tot = 0;
    for (int st = 0; st <= SPAN; st++) tot += wcnt[st][k];
    printf("   %d legs: %ld walks\n", k, tot);
  }
  printf("\n---- the corpus, chain by chain ----\n");

  {
    Path p = bpath(0, SPAN);
    printf("  bing 0 %d: %d links\n", SPAN, p.n);
    runBase(p.v, p.n, "bing", mixes);
    free(p.v);
    Path q = bpath(SPAN, 0);
    printf("  bing %d 0: %d links\n", SPAN, q.n);
    runBase(q.v, q.n, "bing-rev", mixes);
    free(q.v);
  }

  for (int N = SPAN + 1; N <= SPAN + 4 && DOWINDOWS; N++) {
    Path p = bpath(0, N);
    printf("  bing 0 %d: %d links\n", N, p.n);
    long gridMade = 0, randMade = 0;
    char name[64];
    int stride = 149;
    for (int a = 0; a + 120 < p.n && gridMade < windows; a += stride) {
      int lo = p.v[a], hi = p.v[a], b = -1;
      for (int t = a; t < p.n; t++) {
        if (p.v[t] < lo) lo = p.v[t];
        if (p.v[t] > hi) hi = p.v[t];
        if (hi - lo == SPAN) { b = t; break; }
        if (hi - lo > SPAN) break;
      }
      if (b < 0) continue;
      int e = b;
      while (e + 1 < p.n && p.v[e+1] >= lo && p.v[e+1] <= hi) e++;
      int m = windowSpanS(p.v, p.n, a, e, wbuf);
      if (!m) continue;
      snprintf(name, sizeof(name), "bing0%d-grid", N);
      gridMade++;
      runBase(wbuf, m, name, mixes);
    }
    for (long it = 0; it < windows * 3 && randMade < windows; it++) {
      int a = (int)(random() % (unsigned)(p.n - 60));
      int lo = p.v[a], hi = p.v[a], b = -1;
      for (int t = a; t < p.n; t++) {
        if (p.v[t] < lo) lo = p.v[t];
        if (p.v[t] > hi) hi = p.v[t];
        if (hi - lo == SPAN) { b = t; break; }
        if (hi - lo > SPAN) break;
      }
      if (b < 0) continue;
      int e = b;
      while (e + 1 < p.n && p.v[e+1] >= lo && p.v[e+1] <= hi) e++;
      int m = windowSpanS(p.v, p.n, a, e, wbuf);
      if (!m) continue;
      snprintf(name, sizeof(name), "bing0%d-rand", N);
      randMade++;
      runBase(wbuf, m, name, mixes);
    }
    printf("  -> windows of span %d: %ld at grid offsets, %ld at random offsets\n",
           SPAN, gridMade, randMade);
    free(p.v);
  }

  {
    int bk[4] = {1, 2, 2, 1}, fw[4] = {2, 1, 2, 3};
    for (int q = 0; q < 4; q++) {
      Path r = vpath(0, SPAN, bk[q], fw[q]);
      char name[64];
      snprintf(name, sizeof(name), "vpath(%d,%d)", bk[q], fw[q]);
      printf("  vpath 0 %d (%d,%d): %d links\n", SPAN, bk[q], fw[q], r.n);
      runBase(r.v, r.n, name, mixes);
      free(r.v);
      Path s = vpath(SPAN, 0, bk[q], fw[q]);
      snprintf(name, sizeof(name), "vpath-rev(%d,%d)", bk[q], fw[q]);
      printf("  vpath %d 0 (%d,%d): %d links\n", SPAN, bk[q], fw[q], s.n);
      runBase(s.v, s.n, name, mixes);
      free(s.v);
    }
  }

  {
    static int v[MAXN * 2];
    long made = 0;
    for (long it = 0; it < windows * 2 && DOWINDOWS; it++) {
      int nb = 2 + (int)(random() % 3), n = 0, cur = (int)(random() % (SPAN + 1)), first = 1;
      for (int b = 0; b < nb; b++) {
        int nx; do { nx = (int)(random() % (SPAN + 1)); } while (nx == cur);
        Path blk = bpath(cur, nx);
        if (n + blk.n >= MAXN * 2 - 4) { free(blk.v); break; }
        if (first) { memcpy(v, blk.v, sizeof(int) * blk.n); n = blk.n; first = 0; }
        else { memcpy(v + n, blk.v + 1, sizeof(int) * (blk.n - 1)); n += blk.n - 1; }
        cur = nx; free(blk.v);
      }
      if (n < 200) continue;
      if (n < MAXN) {
        int lo = v[0], hi = v[0];
        for (int u = 0; u < n; u++) { if (v[u] < lo) lo = v[u]; if (v[u] > hi) hi = v[u]; }
        if (hi - lo == SPAN) {
          static int sh[MAXN];
          for (int u = 0; u < n; u++) sh[u] = v[u] - lo;
          made++;
          runBase(sh, n, "concat", mixes);
          continue;
        }
      }
      int a = (int)(random() % (unsigned)(n - 40));
      int lo = v[a], hi = v[a], b = -1;
      for (int t = a; t < n; t++) {
        if (v[t] < lo) lo = v[t];
        if (v[t] > hi) hi = v[t];
        if (hi - lo == SPAN) { b = t; break; }
        if (hi - lo > SPAN) break;
      }
      if (b < 0) continue;
      int e = b;
      while (e + 1 < n && v[e+1] >= lo && v[e+1] <= hi) e++;
      int m = windowSpanS(v, n, a, e, wbuf);
      if (!m) continue;
      made++;
      runBase(wbuf, m, "concat-window", mixes);
    }
    printf("  random concatenations of Bing blocks: %ld used\n", made);
  }

  printf("\n================ the corpus at span %d ================\n", SPAN);
  printf("  base level sequences of band [0,%d] swept: %ld\n", SPAN, nSourceKinds);
  printf("  pairs tried: %ld;  faithful: %ld;  scanned: %ld (%ld distinct)\n",
         variantsTried, variantsFaithful, nPairs, nDistinctPairs);
  printf("  links: %ld, of which not thin: %ld\n", nLinks, nNonThin);
  printf("  basepoints of the band: %ld (%ld distinct by their pair of whole arms;\n"
         "  it is the distinct ones that are scored), of which thin: %ld\n",
         nBase, nBaseDistinct, nBaseThin);
  printf("  arm lengths seen: %ld to %ld  (whole arms; no arm-length bound)\n", armMin, armMax);
  printf("  keys in the distinctness table: %ld; past capacity: %ld\n", hashN, hashOverflow);

  printf("\n======== S2.3  the least number of legs, over the distinct basepoints ========\n");
  for (int k = 0; k <= KMAX; k++)
    printf("  least %d legs: %8ld basepoints   (thin pairs alone: %8ld)\n",
           k, kCount[k], kCountThin[k]);
  printf("  no walk of at most %d legs: %ld  (thin: %ld)\n", KMAX, kNone, kNoneThin);
  if (kNone) {
    printf("  of those, %ld were searched further, walks enumerated on the fly:", deepDone);
    for (int k = 0; k <= MAXKLEG + 3; k++)
      if (deepFound[k]) printf("  %s: %ld", k ? "served by that many legs" : "served by none", deepFound[k]);
    printf("  (leg counts:");
    for (int k = 1; k <= MAXKLEG + 3; k++) if (deepFound[k]) printf(" %d", k);
    printf(")\n");
  }
  printf("  the maximum least leg count at span %d is %d\n", SPAN, maxLegsSeen);
  printf("  the levels at which it is attained:");
  for (int p = 0; p <= SPAN; p++) if (maxLegsByLevel[p]) printf("  L+%d (%ld)", p, maxLegsByLevel[p]);
  printf("\n");

  printf("\n  by level (columns: least 0,1,...,%d legs, then none):\n", KMAX);
  for (int p = 0; p <= SPAN; p++) {
    long tot = kNoneByLevel[p];
    for (int k = 0; k <= KMAX; k++) tot += kByLevel[p][k];
    if (tot == 0) continue;
    printf("   level %2d:", p);
    for (int k = 0; k <= KMAX; k++) printf(" %8ld", kByLevel[p][k]);
    printf("  | none %ld\n", kNoneByLevel[p]);
  }

  printf("\n======== S2.5  the thin pairs alone (sigma = rho) ========\n");
  {
    int maxThin = -1;
    for (int k = 0; k <= KMAX; k++) if (kCountThin[k]) maxThin = k;
    printf("  distinct basepoints of thin pairs: %ld\n", nBaseThin);
    printf("  the maximum least leg count over thin pairs alone: %d"
           "  (over all pairs: %d)\n", maxThin, maxLegsSeen);
    printf("  by level (thin only):\n");
    for (int p = 0; p <= SPAN; p++) {
      long tot = 0;
      for (int k = 0; k <= KMAX; k++) tot += kByLevelThin[p][k];
      if (tot == 0) continue;
      printf("   level %2d:", p);
      for (int k = 0; k <= KMAX; k++) printf(" %8ld", kByLevelThin[p][k]);
      printf("\n");
    }
  }
  report76();
  printf("\n---- the audit sample ----\n");
  printf("  the fold decided by the bitmask propagation against the same fold decided by an\n"
         "  array propagation (stored walks, whole arms): %ld samples, %ld disagreements\n", bruteSamples, bruteBad);
  printf("  every predicate of this census is evaluated by its own definition: IsCrookedIvF,\n"
         "  armG, armT, FoldsOnto (twice, independently).\n");
  return 0;
}
