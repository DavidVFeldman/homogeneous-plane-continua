/* census-batch75.c -- batch 75, the reconnaissance censuses of sections 2.1,
 * 2.2, 2.3 and 2.5.
 *
 * Built on census-batch74.c: the same corpus builder, the same definitions, the
 * same two independent deciders for `FoldsOnto`, the same de-duplication of
 * basepoints by their pair of whole arms.  What is new is what is measured.
 *
 *   S2.1  Does the least walk at span S extend a least walk at a lower span?
 *         At a basepoint whose least leg count is k >= 3, is some least walk
 *         obtained from a walk that serves the same basepoint *read in a
 *         sub-band* -- the pair restricted to a band [L', H'] of smaller span
 *         containing the basepoint's level, which is faithful and crooked in
 *         its own right by `isCrookedIvF_restrict` -- by appending legs at the
 *         ends?  Reported as a fraction, with the shape of the appended legs.
 *
 *   S2.2  What the split lemma sees.  At the five-leg basepoints: is there a
 *         split index on each arm at which the prefix lies in a sub-band of
 *         span <= 9 and the suffix likewise, and do the two prefix folds meet
 *         at a common walk time?
 *
 *   S2.3  The growth of the least leg count, extended to spans 13 and 14: the
 *         maximum least leg count and the levels at which it is attained.
 *
 *   S2.5  What the general model adds: the same least-leg-count census over the
 *         *thin* pairs alone (sigma = rho), reported beside the general one.
 *
 * ------------------------------------------------------------ what a walk is
 *
 * A *walk with k legs* based at a basepoint of level p is a start
 * c0 in {p-1, p, p+1} cap [L, H] followed by k turning targets in [L+1, H-1],
 * the directions alternating, each leg a run of unit steps -- the itinerary of
 * census-batch26.py, and exactly the shape `FoldsOnto` consumes.  The number of
 * legs is the number of turning targets.
 *
 * ------------------------------------------------- what "read in a sub-band" is
 *
 * Fix a basepoint at index i, of level p, in a pair of band [L, H] = [0, S].
 * For a band [L', H'] with L <= L' <= p <= H' <= H and H' - L' < S, the *pair
 * read in the sub-band* is the maximal contiguous stretch of indices containing
 * i all of whose levels lie in [L', H'].  By `isCrookedIvF_restrict` that
 * stretch is again a faithful crooked pair, and its band is contained in
 * [L', H'], of strictly smaller span.  Its two arms are the whole arms of the
 * basepoint truncated at the first index, forwards and backwards, whose level
 * leaves [L', H'].  A walk *serves the basepoint in the sub-band* when all its
 * levels lie in [L', H'], its start is within one of p, and it folds both of
 * those truncated arms.
 *
 * A walk w with k legs *is obtained from w' by appending legs at the ends* when
 * w' is a leg-aligned contiguous sub-walk of w: for some 0 <= j1 < j2 <= k, the
 * legs j1 .. j2-1 of w, started at w's target j1-1 (or at w's own start when
 * j1 = 0).  j1 legs are then prepended and k - j2 appended.
 *
 * For each basepoint the sub-band is taken as the *minimal* band containing the
 * sub-walk's levels and p -- the most generous choice, since a smaller band
 * truncates the arms sooner and makes the test easier.  The census therefore
 * also reports how long the truncated arms are, so that a success on an arm of
 * two or three links is not read as a success on a real sub-band problem, and
 * separately reports successes at sub-bands of span S-1 and S-2 (one and two
 * levels dropped), which is what a "one leg per two levels of span" law would
 * require.
 *
 * ------------------------------------------------------------ definition audit
 *
 * Every predicate is evaluated by its own definition, none by a proxy.
 *   crookedGen   IsCrookedIvF of HPC/Fold/Faithful.lean (le, width, adj and the
 *                crookedness clause with interval triggers), unchanged from
 *                census-batch70.c / census-batch74.c.
 *   foldsMask    FoldsOnto of HPC/Fold/Faithful.lean, decided exactly by
 *                reachability of walk times, as a 128-bit mask.
 *   foldsBrute   the same, decided again by an independent array propagation;
 *                the two are compared on a sample and the disagreements counted.
 *   armG, armT   as HPC/Fold/Faithful.lean defines them, over whole arms.
 * No criterion of the four-leg engine and no landmark sentence is used.
 *
 * Usage: census-batch75 [S] [windows] [mixtures] [seed] [kmax] [cover-cap]
 *                       [max-pair-length] [hard-sample-per-level]
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

/* ---------------------------------------------------- section 2.1, one basepoint */

#define MAXLEAST 16

static void section21(const int *G, int mg, const int *T, int mt, int p, int k,
                      int n, int i, const char *tag) {
  /* all least walks, up to MAXLEAST of them */
  int least[MAXLEAST]; int nLeast = 0;
  for (int st = p - 1; st <= p + 1 && nLeast < MAXLEAST; st++) {
    if (st < 0 || st > SPAN) continue;
    long a = widx[st][k], c = wcnt[st][k];
    for (long q = a; q < a + c && nLeast < MAXLEAST; q++) {
      if (!foldsMask(G, mg, &walks[q])) continue;
      if (!foldsMask(T, mt, &walks[q])) continue;
      least[nLeast++] = (int)q;
    }
  }
  s21Examined++; s21ByK[k]++;
  if (nLeast == 0) { s21NoLeastWalkFound++; return; }

  int best = 0, bestSpan = -1, bestTrunc = -1, bestLegs = -1;
  int bestAppendTop = 0, bestAppendBottom = 0, bestAppendOther = 0;
  int bestPrepend = 0, bestAppended = 0;
  int bestW = -1, bestJ1 = 0, bestJ2 = 0;
  for (int q = 0; q < nLeast; q++) {
    const Walk *w = &walks[least[q]];
    for (int j1 = 0; j1 < k; j1++)
      for (int j2 = j1 + 1; j2 <= k; j2++) {
        if (j2 - j1 >= k) continue;                  /* strictly fewer legs */
        int st = (j1 == 0) ? w->start : w->tgt[j1 - 1];
        if (st < p - 1 || st > p + 1) continue;      /* must serve this basepoint */
        int tg[MAXKLEG];
        for (int u = j1; u < j2; u++) tg[u - j1] = w->tgt[u];
        int times[MAXWALK];
        int len = buildTimes(st, tg, j2 - j1, times);
        if (len < 0) continue;
        Walk sub;
        fillWalk(&sub, st, tg, j2 - j1, times, len);
        int lo = sub.lo < p ? sub.lo : p;
        int hi = sub.hi > p ? sub.hi : p;
        if (hi - lo >= SPAN) continue;               /* the sub-band must be smaller */
        int mgR = restrictLen(G, mg, lo, hi);
        int mtR = restrictLen(T, mt, lo, hi);
        if (mgR < 1 || mtR < 1) continue;
        if (!foldsMask(G, mgR, &sub)) continue;
        if (!foldsMask(T, mtR, &sub)) continue;
        int trunc = mgR < mtR ? mgR : mtR;
        int bandSpan = hi - lo;
        /* the best success: widest sub-band first, then longest truncated arms */
        if (bandSpan > bestSpan || (bandSpan == bestSpan && trunc > bestTrunc)) {
          best = 1; bestSpan = bandSpan; bestTrunc = trunc; bestLegs = j2 - j1;
          bestPrepend = j1; bestAppended = k - j2;
          bestW = least[q]; bestJ1 = j1; bestJ2 = j2;
          bestAppendTop = bestAppendBottom = bestAppendOther = 0;
          if (k - j2 > 0) {
            int lastTgt = w->tgt[k - 1];
            if (lastTgt == SPAN - 1) bestAppendTop = 1;
            else if (lastTgt == 1) bestAppendBottom = 1;
            else bestAppendOther = 1;
          }
        }
      }
  }
  if (!best) {
    s21Fail++;
    if (s21ShownFail < 8) {
      s21ShownFail++;
      printf("  S2.1 NO SUB-BAND ANCESTOR [%ld] %-16s n=%4d i=%4d level=%d k=%d"
             " |G|=%4d |T|=%4d  least walk ", s21ShownFail, tag, n, i, p, k, mg, mt);
      printWalk(&walks[least[0]]);
      printf("\n");
      if (s21ShownFail == 1) {
        char fn[64];
        snprintf(fn, sizeof(fn), "witness-batch75-s21-span%d.txt", SPAN);
        FILE *fp = fopen(fn, "w");
        if (fp) {
          fprintf(fp, "%d %d %d\n", n, i, k);
          for (int t = 0; t < n; t++) fprintf(fp, "%d%c", rho[t], t + 1 == n ? '\n' : ' ');
          for (int t = 0; t < n; t++) fprintf(fp, "%d%c", sig[t], t + 1 == n ? '\n' : ' ');
          fclose(fp);
        }
      }
    }
    return;
  }
  s21Success++; s21SuccessByK[k]++;
  if (bestSpan >= 0 && bestSpan < MAXLEV) s21ByBandSpan[bestSpan]++;
  if (bestSpan == SPAN - 1) s21SpanMinus1++;
  if (bestSpan == SPAN - 2) s21SpanMinus2++;
  if (bestTrunc >= 10) s21SuccessDeep++;
  s21ExaminedDeepable++;
  { int b = bestTrunc; int idx = b >= 100 ? 5 : b >= 40 ? 4 : b >= 10 ? 3 : b >= 4 ? 2 : b >= 2 ? 1 : 0;
    s21ArmTrunc[idx]++; }
  if (bestAppended == 0) s21AppendNone++;
  else if (bestAppendTop) s21AppendTop++;
  else if (bestAppendBottom) s21AppendBottom++;
  else s21AppendOther++;
  if (bestPrepend) s21Prepend++;
  if (bestAppended >= 0 && bestAppended <= MAXKLEG) s21LegsAppended[bestAppended]++;
  if (k >= 5 && s22Shown < 6) {
    printf("  S2.1 example k=%d: least walk ", k);
    printWalk(&walks[bestW]);
    printf("   sub-walk legs [%d,%d) of it, sub-band span %d, truncated arms >= %d,"
           " %d prepended, %d appended (legs kept %d)\n",
           bestJ1, bestJ2, bestSpan, bestTrunc, bestPrepend, bestAppended, bestLegs);
  }
}

/* ---------------------------------------------------- section 2.2, one basepoint */

static void section22(const int *G, int mg, const int *T, int mt, int p, int k,
                      int n, int i, const char *tag) {
  s22Examined++;
  /* (a) split indices on each arm with prefix and suffix each of span <= 9 */
  long splitG = 0, splitT = 0;
  for (int arm = 0; arm < 2; arm++) {
    const int *f = arm ? T : G;
    int m = arm ? mt : mg;
    /* suffix ranges */
    static int sufLo[MAXN], sufHi[MAXN];
    sufLo[m - 1] = f[m - 1]; sufHi[m - 1] = f[m - 1];
    for (int u = m - 2; u >= 0; u--) {
      sufLo[u] = f[u] < sufLo[u + 1] ? f[u] : sufLo[u + 1];
      sufHi[u] = f[u] > sufHi[u + 1] ? f[u] : sufHi[u + 1];
    }
    int preLo = f[0], preHi = f[0];
    long cnt = 0;
    for (int s = 0; s < m; s++) {
      if (f[s] < preLo) preLo = f[s];
      if (f[s] > preHi) preHi = f[s];
      if (preHi - preLo <= 9 && sufHi[s] - sufLo[s] <= 9) cnt++;
    }
    if (arm) splitT = cnt; else splitG = cnt;
  }
  if (splitG) s22SplitG++;
  if (splitT) s22SplitT++;
  if (splitG && splitT) s22SplitBoth++;

  /* (b) a common sub-band of span <= 9 containing a prefix of each arm: take the
     band maximising the shorter truncated arm */
  int bLo = -1, bHi = -1; int bestMin = -1, bestG = 0, bestT = 0;
  for (int lo = 0; lo <= p; lo++)
    for (int hi = p; hi <= SPAN; hi++) {
      if (hi - lo > 9) continue;
      int mgR = restrictLen(G, mg, lo, hi);
      int mtR = restrictLen(T, mt, lo, hi);
      int mn = mgR < mtR ? mgR : mtR;
      if (mn > bestMin) { bestMin = mn; bLo = lo; bHi = hi; bestG = mgR; bestT = mtR; }
    }
  if (bestMin <= 0) return;
  s22CommonPrefixBand++;

  /* (c) a single walk of the sub-band folding both prefixes, and whether the two
     arrival-time sets meet */
  int found = -1; u128 aG = 0, aT = 0;
  for (int kk = 0; kk <= KMAX && found < 0; kk++)
    for (int st = p - 1; st <= p + 1 && found < 0; st++) {
      if (st < bLo || st > bHi) continue;
      for (long q = widx[st][kk]; q < widx[st][kk] + wcnt[st][kk]; q++) {
        const Walk *w = &walks[q];
        if (w->lo < bLo || w->hi > bHi) continue;
        u128 rG = foldsArrive(G, bestG, w);
        if (!rG) continue;
        u128 rT = foldsArrive(T, bestT, w);
        if (!rT) continue;
        found = (int)q; aG = rG; aT = rT; break;
      }
    }
  if (found >= 0) {
    s22PrefixWalk++;
    if (aG & aT) s22PrefixMeet++;
  }

  /* (d) do the suffixes after that split each lie in a band of span <= 9? */
  int sgLo = G[bestG - 1], sgHi = G[bestG - 1];
  for (int u = bestG - 1; u < mg; u++) { if (G[u] < sgLo) sgLo = G[u]; if (G[u] > sgHi) sgHi = G[u]; }
  int stLo = T[bestT - 1], stHi = T[bestT - 1];
  for (int u = bestT - 1; u < mt; u++) { if (T[u] < stLo) stLo = T[u]; if (T[u] > stHi) stHi = T[u]; }
  int sufOK = (sgHi - sgLo <= 9) && (stHi - stLo <= 9);
  if (sufOK) s22SuffixBothNine++;

  if (s22Shown < 8) {
    s22Shown++;
    printf("  S2.2 [%ld] %-16s n=%4d i=%4d level=%d k=%d: split indices with both sides"
           " of span <= 9: %ld on G, %ld on T\n", s22Shown, tag, n, i, p, k, splitG, splitT);
    printf("       widest common prefix band [%d,%d] (span %d): prefixes %d and %d links;"
           " suffix spans %d and %d\n", bLo, bHi, bHi - bLo, bestG, bestT,
           sgHi - sgLo, stHi - stLo);
    if (found >= 0) {
      printf("       a walk of that band folding both prefixes: ");
      printWalk(&walks[found]);
      printf("   arrival sets meet: %s\n", (aG & aT) ? "yes" : "NO");
    } else {
      printf("       no walk of at most %d legs confined to that band folds both prefixes\n", KMAX);
    }
  }
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
            snprintf(fn, sizeof(fn), "witness-batch75-span%d-k%d.txt", SPAN, dk);
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
        snprintf(fn, sizeof(fn), "witness-batch75-span%d-k%d.txt", SPAN, k);
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
      /* section 2.1: a sample of the basepoints of least leg count at least three */
      if (k >= 3) {
        hardSeen[p]++;
        if (hardDone[p][k] < HARDPERLEVEL) {
          hardDone[p][k]++;
          section21(armG, mg, armT, mt, p, k, n, i, tag);
        }
      }
      /* section 2.2: every five-leg basepoint, up to a cap */
      if (k >= 5 && s22Examined < 400)
        section22(armG, mg, armT, mt, p, k, n, i, tag);
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
  srandom(seed);
  setvbuf(stdout, NULL, _IOLBF, 0);
  T0 = time(NULL);

  walks = (Walk *)malloc(sizeof(Walk) * MAXWALKS);
  hashTab = (uint64_t *)calloc(HASHCAP, sizeof(uint64_t));
  if (!walks || !hashTab) { printf("out of memory\n"); return 1; }

  buildAllWalks();

  printf("census-batch75: the fold at span %d.  L = 0, H = %d.\n", SPAN, SPAN);
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

  printf("\n======== S2.1  does a least walk extend a walk of a sub-band? ========\n");
  printf("  sampled basepoints of least leg count k >= 3: %ld"
         "  (at most %ld per level and leg count; seen:", s21Examined, HARDPERLEVEL);
  for (int p = 0; p <= SPAN; p++) if (hardSeen[p]) printf(" L+%d:%ld", p, hardSeen[p]);
  printf(")\n");
  printf("  of these, some least walk is an extension of a walk serving the basepoint in a\n"
         "  sub-band of smaller span: %ld;  none is: %ld"
         "  (least walk not found within the cap: %ld)\n",
         s21Success, s21Fail, s21NoLeastWalkFound);
  printf("  by least leg count k:  ");
  for (int k = 3; k <= KMAX; k++)
    printf("k=%d: %ld of %ld;  ", k, s21SuccessByK[k], s21ByK[k]);
  printf("\n");
  printf("  the widest sub-band at which a success is found, by its span:\n");
  for (int s = 0; s < MAXLEV; s++) if (s21ByBandSpan[s])
    printf("     span %2d: %ld\n", s, s21ByBandSpan[s]);
  printf("  successes at a sub-band of span S-1: %ld;  of span S-2: %ld\n",
         s21SpanMinus1, s21SpanMinus2);
  printf("  the length of the shorter truncated arm at the success"
         "  (1 | 2-3 | 4-9 | 10-39 | 40-99 | >=100):");
  for (int u = 0; u < 6; u++) printf(" %ld", s21ArmTrunc[u]);
  printf("\n  successes whose truncated arms are both at least ten links: %ld of %ld\n",
         s21SuccessDeep, s21ExaminedDeepable);
  printf("  legs appended at the end of the sub-walk:");
  for (int u = 0; u <= MAXKLEG; u++) if (s21LegsAppended[u]) printf("  %d legs: %ld", u, s21LegsAppended[u]);
  printf("\n  the shape of the last appended leg: an ascent to H-1: %ld;  a descent to L+1: %ld;"
         "  neither: %ld;  nothing appended (legs only prepended): %ld\n",
         s21AppendTop, s21AppendBottom, s21AppendOther, s21AppendNone);
  printf("  successes that also prepend legs at the start: %ld\n", s21Prepend);

  printf("\n======== S2.2  what the split lemma sees ========\n");
  printf("  five-leg basepoints examined: %ld\n", s22Examined);
  printf("  with a split index on the forward arm at which prefix and suffix each lie in a\n"
         "  band of span at most nine: %ld;  on the backward arm: %ld;  on both: %ld\n",
         s22SplitG, s22SplitT, s22SplitBoth);
  printf("  with a common band of span at most nine holding a prefix of both arms: %ld\n",
         s22CommonPrefixBand);
  printf("  of those, a single walk confined to that band folding both prefixes: %ld\n",
         s22PrefixWalk);
  printf("  of those, the two arms' sets of arrival times on that walk meet: %ld\n",
         s22PrefixMeet);
  printf("  and the two suffixes after that split each lie in a band of span at most nine: %ld\n",
         s22SuffixBothNine);

  printf("\n---- the audit sample ----\n");
  printf("  the fold decided by the bitmask propagation against the same fold decided by an\n"
         "  array propagation: %ld samples, %ld disagreements\n", bruteSamples, bruteBad);
  printf("  every predicate of this census is evaluated by its own definition: IsCrookedIvF,\n"
         "  armG, armT, FoldsOnto (twice, independently).  No criterion of the four-leg engine\n"
         "  and no landmark sentence is used.\n");
  return 0;
}
