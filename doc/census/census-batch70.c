/* census-batch70.c -- batch 70.  The widened corpus of span-nine crossings.
 *
 * The commission of batch 70 section 2.1 asks, before any Lean is attempted,
 * that the corpus of crossings of the branch L+5 be widened beyond the windows
 * of the single 986-link pair the batch-69 census swept, and that the three
 * statements the branch owes be re-measured on it:
 *
 *   1. the distance  -- a time of the pair at L+2 or below within 67 steps
 *      across the basepoint (NearLowT / NearLowG of HPC/Fold/Ceil69.lean);
 *   2. the partner's deep-floor clause Deep72 where the band reaches the floor;
 *   3. BothNineL5 -- the partner stops below L+9.
 *
 * and that the count of distinct configurations be reported alongside the count
 * of crossings.  Three further measurements the commission's questions ask for
 * are made in the same sweep:
 *
 *   4. (question 2.2) the nearest time of the pair at L+1 or below and at the
 *      floor L across the basepoint, against the bounds 166 and 405 -- the
 *      bounds the same pairing gives when it is read from a lower time (the
 *      timing law's z 7 = 170 and z 8 = 409 in place of z 6 = 71);
 *   5. (question 2.3) whether the crookedness clause read between the partner's
 *      floor descent and the running arm's link carrying L+9 returns the two
 *      landmarks Deep72 misses *as times of the partner's arm*, and whether the
 *      partner's arm reaches the floor at all (if it does not, its deep-floor
 *      clause is vacuous by deep72_of_off_floor);
 *   6. (question 2.4) whether both arms of a crossing ever reach L+9.
 *
 * ---------------------------------------------------------------- the corpus
 *
 * A pair of the corpus is a faithful pair (rho, sig) -- IsCrookedIvF, tested by
 * crookedGen below, which is the Lean definition written out -- whose levels lie
 * in the band [0, 9], so that L = 0 and the band is the span-nine band of the
 * targets.  The generators are
 *
 *   (a) the Bing chains bpath a b for every a, b in [0, 9] with |a - b| = 9,
 *       and the chains bpath a b of smaller span embedded in the band;
 *   (b) windows of span exactly nine, at grid offsets and at random offsets, of
 *       the larger Bing chains bing 0 N for N = 10, 11, 12, 13 -- the "bing 0 N
 *       for larger N; subchains at other offsets" and "the random and grid
 *       subchains of batch 29" the commission names;
 *   (c) the recursive chains vpath a b back fwd whose splitting levels are not
 *       Bing's, and windows of span nine of them;
 *   (d) random concatenations of Bing blocks, and windows of span nine of them;
 *   (e) for every base chain of (a)-(d): the thin pair (sig = rho), every single
 *       shaving of a peak, every single filling of a valley (capped), random
 *       mixtures of shavings and fillings at rates 1/3 and 1/2, and the total
 *       mixture -- the "shaved and filled pairs where the general model differs
 *       from the thin one".
 *
 * A window of a chain is a genuine faithful pair in its own right (crookedness
 * is inherited by sub-intervals, and crookedGen is run on every window anyway),
 * so this is a census over pairs and over whole arms of those pairs, not a
 * census over truncated arms: no arm-length bound applies, and the arm lengths
 * actually seen are reported.
 *
 * ------------------------------------------------------------ definition audit
 *
 * Every predicate is evaluated by its own definition, none by a proxy.
 *
 *   crookedGen      IsCrookedIvF of HPC/Fold/Faithful.lean (le, width, adj, and
 *                   the crookedness clause with interval triggers), copied
 *                   unchanged from census-batch69.c.
 *   lowAt           LowAt f (L+1) (L+8) of HPC/Fold/Leaf.lean, at L = 0.
 *   landLeg4        Leg4Land of HPC/Fold/Leg4Land.lean at H = 9, L = 0, with the
 *                   existential chains read greedily; landLeg4Brute evaluates
 *                   the existentials literally and the two are compared on a
 *                   sample, which is reported.
 *   the trichotomy  w8 = landLeg4 (arm) 8 1 5, wb = landLeg4 (reflected arm)
 *                   6 2 4, w3 = landLeg4 (reflected arm) 6 1 4, exactly as
 *                   TriCrossL5 of HPC/Fold/CrossMid2Fail65.lean names them; a
 *                   crossing is a basepoint at which no one of the three serves
 *                   both arms.
 *   deepFirst2      DeepFirst2 of HPC/Fold/Ceil68.lean at L = 0.
 *   ceil72Clause    the third clause of Leg4Land at (H,K,M,P) = (9,7,2,5),
 *                   written out at L = 0 with its existentials searched
 *                   literally (Ceil72 of HPC/Fold/Ceil68.lean).
 *   deep72Clause    the second clause of the same, i.e. Deep72 of
 *                   HPC/Fold/CrossPartner64.lean, existentials searched
 *                   literally.
 *   the pairing      read exactly as crooked_peak_valley_high9_mid of
 *                   HPC/Fold/Ceil68.lean reads it: between a time a with
 *                   rho a <= 2 and a link b with rho b <= 9 <= sig b, a link r
 *                   with rho r <= 8 <= sig r and, after it, a link r' with
 *                   rho r' <= rho a + 1 <= sig r'.
 *
 * No criterion of the four-leg engine is used anywhere in this census.
 *
 * Usage: census-batch70 [seed] [windows-per-chain] [mixtures-per-chain]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

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

/* the recursive chain whose splitting levels are one further in than Bing's */
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

#define MAXLEV 32
#define MAXN   2400

static int meetTab[MAXLEV][MAXN + 1];

/* IsCrookedIvF (rho, sig), exactly as HPC/Fold/Faithful.lean states it.
   Copied unchanged from census-batch69.c. */
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

static int rho[MAXN], sig[MAXN], armG[MAXN], armT[MAXN], gG[MAXN], gT[MAXN];

/* LowAt f (L+1) (L+8) at L = 0, copied from census-batch69.c */
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

/* ---- the dynamic program of HPC/Fold/Decide.lean, and the four-leg family --
 *
 * folds decides FoldsOnto f len c by reachability, exactly as foldsB does; the
 * family is leg4Walk 0 9 K M P of HPC/Fold/Leg4Wide.lean over its window of
 * parameter sets, together with the reflection of each.  Both are copied
 * unchanged from census-batch69.c. */

#define MAXW 96

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

#define MAXFAM 64
typedef struct { int P, K, M, refl, st, a, b, c, e, len; } Fam;
static Fam fam[MAXFAM];
static int famN = 0;

static void buildFamily(void) {
  for (int P = 2; P <= 6; P++)
    for (int K = P; K <= 8; K++)
      for (int M = 1; M <= P - 2; M++) {
        if (M + 3 > K) continue;
        int st = P - 1, a = K, b = M, c = 8, e = 1;
        int w[MAXW]; int wl = buildWalk4(w, st, a, b, c, e);
        if (wl < 0 || famN >= MAXFAM) continue;
        fam[famN].P = P; fam[famN].K = K; fam[famN].M = M; fam[famN].refl = 0;
        fam[famN].st = st; fam[famN].a = a; fam[famN].b = b; fam[famN].c = c; fam[famN].e = e;
        fam[famN].len = wl; famN++;
        int rst = 9 - st, ra = 9 - a, rb = 9 - b, rc = 9 - c, re = 9 - e;
        int w2[MAXW]; int wl2 = buildWalk4(w2, rst, ra, rb, rc, re);
        if (wl2 < 0 || famN >= MAXFAM) continue;
        fam[famN].P = P; fam[famN].K = K; fam[famN].M = M; fam[famN].refl = 1;
        fam[famN].st = rst; fam[famN].a = ra; fam[famN].b = rb; fam[famN].c = rc;
        fam[famN].e = re; fam[famN].len = wl2; famN++;
      }
}

static int famFoldsBoth(int q, const int *g, int mg, const int *t, int mt) {
  int w[MAXW];
  int wl = buildWalk4(w, fam[q].st, fam[q].a, fam[q].b, fam[q].c, fam[q].e);
  if (wl < 0) return 0;
  return folds(g, mg, w, wl) && folds(t, mt, w, wl);
}

/* Leg4Land of HPC/Fold/Leg4Land.lean at H = 9, L = 0, read greedily.
   Copied unchanged from census-batch69.c. */
static int landLeg4(const int *f, int m, int K, int M, int P) {
  const int H = 9;
  int A = K - P + 1;
  if (f[0] < P - 2 || f[0] > P) return 0;
  int t1 = -1, t2 = -1, t3 = -1;
  for (int j = A; j < m; j++) if (f[j] >= K - 1) { t1 = j; break; }
  if (t1 >= 0) for (int k = t1 + (K - M); k < m; k++) if (f[k] <= M + 1) { t2 = k; break; }
  if (t2 >= 0) for (int l = t2 + (H - 1 - M); l < m; l++) if (f[l] >= H - 2) { t3 = l; break; }
  for (int d = 0; d < m; d++) {
    if (f[d] <= P - 3 && (t1 < 0 || t1 + (K - 1 - f[d]) > d)) return 0;
    if (f[d] <= M - 2 && (t3 < 0 || t3 + (H - 2 - f[d]) > d)) return 0;
    if (f[d] >= K + 2 && (t2 < 0 || t2 + (f[d] - M - 1) > d)) return 0;
  }
  return 1;
}

/* the same sentence with its existentials searched literally (quadratic) */
static int landLeg4Brute(const int *f, int m, int K, int M, int P) {
  const int H = 9;
  int A = K - P + 1;
  if (f[0] < P - 2 || f[0] > P) return 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= P - 3) {
      int ok = 0;
      for (int j = A; j < m && !ok; j++)
        if (f[j] >= K - 1 && j + (K - 1 - f[d]) <= d) ok = 1;
      if (!ok) return 0;
    }
    if (f[d] <= M - 2) {
      int ok = 0;
      for (int j = A; j < m && !ok; j++) {
        if (f[j] < K - 1) continue;
        for (int k = j + (K - M); k < m && !ok; k++) {
          if (f[k] > M + 1) continue;
          for (int l = k + (H - 1 - M); l < m && !ok; l++)
            if (f[l] >= H - 2 && l + (H - 2 - f[d]) <= d) ok = 1;
        }
      }
      if (!ok) return 0;
    }
    if (f[d] >= K + 2) {
      int ok = 0;
      for (int j = A; j < m && !ok; j++) {
        if (f[j] < K - 1) continue;
        for (int k = j + (K - M); k < m && !ok; k++)
          if (f[k] <= M + 1 && k + (f[d] - M - 1) <= d) ok = 1;
      }
      if (!ok) return 0;
    }
  }
  return 1;
}

/* DeepFirst2 of HPC/Fold/Ceil68.lean at L = 0 */
static int deepFirst2(const int *f, int m) {
  for (int e = 0; e < m; e++) {
    if (f[e] < 9) continue;
    int ok = 0;
    for (int d = 0; d < e && !ok; d++) if (f[d] <= 2) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* Ceil72: the third clause of Leg4Land at (9,7,2,5), existentials searched */
static int ceil72Clause(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] < 9) continue;
    int ok = 0;
    for (int j = 3; j < m && !ok; j++) {
      if (f[j] < 6) continue;
      for (int k = j + 5; k < m && !ok; k++) {
        if (f[k] > 3) continue;
        if (k + (f[d] - 3) <= d) ok = 1;
      }
    }
    if (!ok) return 0;
  }
  return 1;
}

/* Deep72: the second clause of the same, existentials searched */
static int deep72Clause(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] > 0) continue;
    int ok = 0;
    for (int j = 3; j < m && !ok; j++) {
      if (f[j] < 6) continue;
      for (int k = j + 5; k < m && !ok; k++) {
        if (f[k] > 3) continue;
        for (int l = k + 6; l < m && !ok; l++) {
          if (f[l] < 7) continue;
          if (l + (7 - f[d]) <= d) ok = 1;
        }
      }
    }
    if (!ok) return 0;
  }
  return 1;
}

/* Mid2Floor of HPC/Fold/CrossPartner64.lean at L = 0 */
static int mid2Floor(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] != 2) continue;
    int ok = 0;
    for (int j = 3; j + 4 <= d && !ok; j++) if (f[j] >= 6) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

static int reachesNine(const int *f, int m) {
  for (int d = 0; d < m; d++) if (f[d] >= 9) return 1;
  return 0;
}
static int touchesZero(const int *f, int m) {
  for (int d = 0; d < m; d++) if (f[d] <= 0) return 1;
  return 0;
}
static int firstNine(const int *f, int m) {
  for (int d = 0; d < m; d++) if (f[d] >= 9) return d;
  return -1;
}
/* NineBeforeDeep of HPC/Fold/Ceil69.lean at L = 0 */
static int nineBeforeDeep(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] > 0) continue;
    int ok = 0;
    for (int e = 0; e < d && !ok; e++) if (f[e] >= 9) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* Ceil72's witness at the ascent d, taken with k as late as possible */
static int ceil72WitnessAt(const int *f, int m, int d, int *pj, int *pk) {
  for (int k = d - (f[d] - 3); k >= 0; k--) {
    if (k >= m) continue;
    if (f[k] > 3) continue;
    for (int j = k - 5; j >= 3; j--)
      if (f[j] >= 6) { *pj = j; *pk = k; return 1; }
  }
  return 0;
}

/* ----------------------------------------------------- distinctness tables */

#define HASHCAP (1 << 20)
static uint64_t hashTab[HASHCAP];
static long hashN = 0;

static uint64_t fnv(const void *p, size_t len, uint64_t h) {
  const unsigned char *q = (const unsigned char *)p;
  for (size_t u = 0; u < len; u++) { h ^= q[u]; h *= 1099511628211ULL; }
  return h;
}
/* returns 1 if the key is new (and inserts it), 0 if it was already present */
static int hashNew(uint64_t key) {
  if (key == 0) key = 1;
  uint64_t idx = key & (HASHCAP - 1);
  while (hashTab[idx]) {
    if (hashTab[idx] == key) return 0;
    idx = (idx + 1) & (HASHCAP - 1);
  }
  hashTab[idx] = key; hashN++;
  return 1;
}

/* ------------------------------------------------------------- the counters */

static long nPairs = 0, nLinks = 0, nNonThin = 0, nBase5 = 0, nCross = 0;
static long nDistinctPairs = 0, nDistinctCross = 0;
static long nHighRun = 0, nHighRunDistinct = 0;
static long nConfig = 0;                 /* distinct configuration tuples */
static long nSourceKinds = 0;

/* statement 1: the distance */
static long s1Hold = 0, s1Fail = 0, s1None = 0;
static long s1Min = 1 << 30, s1Max = -1;
static long near1Hold = 0, near1Fail = 0, near1None = 0, near1Min = 1 << 30, near1Max = -1;
static long near0Hold = 0, near0Fail = 0, near0None = 0, near0Min = 1 << 30, near0Max = -1;
static long sAnyHold = 0, sAnyFail = 0;

/* the clause itself */
static long cCeil72All = 0, cCeil72Wit = 0;
static long witLevel[12], distMin = 1 << 30, distMax = -1;
static long peakMin = 1 << 30, peakMax = -1, peakLevMin = 99, peakLevMax = -1;

/* statement 2: the partner's deep-floor clause */
static long s2ArmFloor = 0, s2ArmNoFloor = 0, s2Hold = 0, s2Fail = 0;
static long s2BandFloor = 0;
static long s2RunFloor = 0, s2RunHold = 0, s2RunFail = 0, s2RunNine = 0;
/* question 2.3: the reading of the pairing at the partner's floor descent */
static long q23Cases = 0, q23Reading = 0, q23NoReading = 0, q23Carry9 = 0;

/* statement 3: both arms at L+9 */
static long s3BothNine = 0, s3BothNineAllCross = 0, s3BothNineBase = 0;
static long s3CrossAll = 0;

/* arm lengths */
static long armMin = 1 << 30, armMax = -1;

/* the brute-force audit of landLeg4 */
static long bruteSamples = 0, bruteBad = 0;

static long nMid2Both = 0;
static long bnServed = 0, bnNone = 0, bnW72Both = 0, bnShown = 0;
static long bnPartnerDeep2 = 0, bnPartnerRun = 0, bnPartnerNear = 0, bnPartnerFar = 0;
static long bnPartnerCeil = 0;
static long bnArmMin = 1 << 30;
static long q23Escape = 0;
static long showN = 0;
static const char *curTag = "";
static int curN = 0;

/* ------------------------------------------------------------- the sweep */

static void measureHighRun(int n, int i, const int *X, int mX, const int *Y, int mY,
                           int gSide) {
  /* gSide = 1 when the running (w8) arm is the forward arm */
  nHighRun++;
  if (mid2Floor(X, mX) && mid2Floor(Y, mY)) nMid2Both++;
  uint64_t h = fnv(X, sizeof(int) * (size_t)mX, 1469598103934665603ULL);
  h = fnv(Y, sizeof(int) * (size_t)mY, h);
  int fresh = hashNew(h ^ 0x9e3779b97f4a7c15ULL);
  if (fresh) nHighRunDistinct++;
  if (mX < armMin) armMin = mX;
  if (mX > armMax) armMax = mX;
  if (mY < armMin) armMin = mY;
  if (mY > armMax) armMax = mY;

  int d = firstNine(X, mX);
  int j = -1, k = -1;
  int ok = (d >= 0) ? ceil72WitnessAt(X, mX, d, &j, &k) : 0;
  if (ok) {
    cCeil72Wit++;
    if (X[k] >= 0 && X[k] < 12) witLevel[X[k]]++;
    if (d - k < distMin) distMin = d - k;
    if (d - k > distMax) distMax = d - k;
    if (j < peakMin) peakMin = j;
    if (j > peakMax) peakMax = j;
    if (X[j] < peakLevMin) peakLevMin = X[j];
    if (X[j] > peakLevMax) peakLevMax = X[j];
  }
  if (ceil72Clause(X, mX)) cCeil72All++;

  /* ---- statement 1 and question 2.2: the nearest low times on the partner's
     side of the basepoint, at the levels 2, 1 and 0 */
  int near2 = -1, near1 = -1, near0 = -1;
  for (int s = 1; s < mY; s++) {
    int lv = Y[s];
    if (near2 < 0 && lv <= 2) near2 = s;
    if (near1 < 0 && lv <= 1) near1 = s;
    if (near0 < 0 && lv <= 0) near0 = s;
    if (near2 >= 0 && near1 >= 0 && near0 >= 0) break;
  }
  if (near2 < 0) s1None++;
  else {
    if (near2 < s1Min) s1Min = near2;
    if (near2 > s1Max) s1Max = near2;
    if (near2 <= 67) s1Hold++; else s1Fail++;
  }
  if (near1 < 0) near1None++;
  else {
    if (near1 < near1Min) near1Min = near1;
    if (near1 > near1Max) near1Max = near1;
    if (near1 <= 166) near1Hold++; else near1Fail++;
  }
  if (near0 < 0) near0None++;
  else {
    if (near0 < near0Min) near0Min = near0;
    if (near0 > near0Max) near0Max = near0;
    if (near0 <= 405) near0Hold++; else near0Fail++;
  }
  int anyRead = (near2 >= 0 && near2 <= 67) || (near1 >= 0 && near1 <= 166) ||
                (near0 >= 0 && near0 <= 405);
  if (anyRead) sAnyHold++; else sAnyFail++;

  /* ---- statement 2: the partner's deep-floor clause */
  int partnerFloor = touchesZero(Y, mY);
  int dY = deep72Clause(Y, mY);
  if (partnerFloor) {
    s2ArmFloor++;
    if (dY) s2Hold++; else s2Fail++;
  } else s2ArmNoFloor++;
  {
    int bandFloor = 0;
    for (int t = 0; t < n; t++) if (rho[t] <= 0) { bandFloor = 1; break; }
    if (bandFloor) s2BandFloor++;
  }
  if (touchesZero(X, mX)) {
    s2RunFloor++;
    if (deep72Clause(X, mX)) s2RunHold++; else s2RunFail++;
    if (nineBeforeDeep(X, mX)) s2RunNine++;
  }

  /* ---- question 2.3: the pairing read at the partner's floor descent against
     the running arm's link carrying 9.  The landmarks Deep72 misses are a link
     r with rho r <= 8 <= sig r (a time at 7 or above) and, after it, a link r'
     with rho r' <= rho c + 1 <= sig r'; the question is whether they can be
     placed as times of the *partner's* arm, i.e. between the floor descent and
     the basepoint, with the index constraints Deep72 asks and with a third
     landmark at 6 or above between the valley and the basepoint. */
  if (partnerFloor) {
    q23Cases++;
    int carry9 = 0;
    for (int s = 0; s < mY; s++) {
      int t = gSide ? (i - s) : (i + s);
      if (t < 0 || t >= n) break;
      if (rho[t] <= 9 && sig[t] >= 9) { carry9 = 1; break; }
    }
    if (carry9) q23Carry9++;
    /* the partner's first floor descent, in chain coordinates */
    int dFloor = -1;
    for (int s = 0; s < mY; s++) if (Y[s] <= 0) { dFloor = s; break; }
    int found = 0;
    if (dFloor > 0) {
      /* chain indices between the floor descent and the basepoint, in the
         partner's arm order: arm index s means chain index i - dirX*s */
      for (int sl = dFloor - 7; sl >= 6 && !found; sl--) {           /* the L+7 landmark */
        int tl = gSide ? (i - sl) : (i + sl);
        if (tl < 0 || tl >= n) continue;
        if (!(rho[tl] <= 8 && sig[tl] >= 8)) continue;
        for (int sk = sl - 6; sk >= 3 && !found; sk--) {             /* the valley */
          int tk = gSide ? (i - sk) : (i + sk);
          if (tk < 0 || tk >= n) continue;
          if (!(rho[tk] <= 1 && sig[tk] >= 1)) continue;
          for (int sj = sk - 5; sj >= 3 && !found; sj--) {           /* the L+6 landmark */
            int tj = gSide ? (i - sj) : (i + sj);
            if (tj < 0 || tj >= n) continue;
            if (rho[tj] >= 6) found = 1;
          }
        }
      }
    }
    if (found) q23Reading++; else q23NoReading++;
    /* does the same clause admit a pair of landmarks *past* the basepoint, on the
       running arm?  If it does, nothing in the pairing places its landmarks on
       the partner's arm. */
    if (dFloor > 0 && d >= 0) {
      int cChain = gSide ? (i - dFloor) : (i + dFloor);
      int bChain = gSide ? (i + d) : (i - d);
      int lo = cChain < bChain ? cChain : bChain, hi = cChain < bChain ? bChain : cChain;
      int esc = 0;
      for (int r = lo + 1; r < hi && !esc; r++) {
        if (!(rho[r] <= 8 && sig[r] >= 8)) continue;
        for (int r2 = r + 1; r2 < hi && !esc; r2++) {
          if (!(rho[r2] <= 1 && sig[r2] >= 1)) continue;
          int onRunning = gSide ? (r2 > i) : (r2 < i);
          if (onRunning) esc = 1;
        }
      }
      if (esc) q23Escape++;
    }
  }

  /* ---- statement 3: both arms at 9 */
  int bothNine = reachesNine(X, mX) && reachesNine(Y, mY);
  if (bothNine) {
    s3BothNine++;
    if (mX + mY < bnArmMin) bnArmMin = mX + mY;
    int served = -1;
    for (int q = 0; q < famN && served < 0; q++)
      if (famFoldsBoth(q, X, mX, Y, mY)) served = q;
    if (served >= 0) bnServed++; else bnNone++;
    if (landLeg4(X, mX, 7, 2, 5) && landLeg4(Y, mY, 7, 2, 5)) bnW72Both++;
    /* which route gives the partner its own ceiling clause? */
    if (deepFirst2(Y, mY)) bnPartnerDeep2++;
    else {
      bnPartnerRun++;
      /* the mirror distance: a time at 2 or below on the running arm's side of
         the basepoint, within 67 steps of it */
      int near = -1;
      for (int s = 1; s < mX; s++) if (X[s] <= 2) { near = s; break; }
      if (near >= 0 && near <= 67) bnPartnerNear++; else bnPartnerFar++;
    }
    if (ceil72Clause(Y, mY)) bnPartnerCeil++;
    if (bnShown == 0 && fresh) {
      /* dump the first such crossing in full, for the independent re-check of
         check70.py: the pair, the basepoint, and the two arms */
      FILE *fp = fopen("witness-batch70.txt", "w");
      if (fp) {
        fprintf(fp, "%d %d %d\n", n, i, gSide);
        for (int t = 0; t < n; t++) fprintf(fp, "%d%c", rho[t], t + 1 == n ? '\n' : ' ');
        for (int t = 0; t < n; t++) fprintf(fp, "%d%c", sig[t], t + 1 == n ? '\n' : ' ');
        fclose(fp);
      }
    }
    if (bnShown < 8 && fresh) {
      bnShown++;
      printf("  BOTH ARMS REACH 9 [%ld] %-14s n=%4d i=%4d running side=%c |X|=%d |Y|=%d\n",
             bnShown, curTag, n, i, gSide ? 'G' : 'T', mX, mY);
      printf("    first ascent of the running arm at arm index %d; of the partner at %d\n",
             firstNine(X, mX), firstNine(Y, mY));
      if (served >= 0)
        printf("    served by the four-leg walk %s P=%d K=%d M=%d : %d -> %d -> %d -> %d -> %d\n",
               fam[served].refl ? "reflected" : "direct", fam[served].P, fam[served].K,
               fam[served].M, fam[served].st, fam[served].a, fam[served].b, fam[served].c,
               fam[served].e);
      else printf("    NO WALK OF THE FOUR-LEG FAMILY SERVES BOTH ARMS\n");
      printf("    the running arm:");
      for (int u = 0; u < mX && u < 130; u++) printf(" %d", X[u]);
      printf("\n    the partner   :");
      for (int u = 0; u < mY && u < 130; u++) printf(" %d", Y[u]);
      printf("\n");
    }
  }

  /* ---- the configuration signature */
  {
    int sigv[10];
    sigv[0] = ok ? X[k] : -1;
    sigv[1] = ok ? d - k : -1;
    sigv[2] = ok ? X[j] : -1;
    sigv[3] = near2; sigv[4] = near1; sigv[5] = near0;
    sigv[6] = partnerFloor ? (dY ? 2 : 1) : 0;
    sigv[7] = bothNine;
    sigv[8] = touchesZero(X, mX) ? 1 : 0;
    sigv[9] = ok ? j : -1;
    uint64_t hc = fnv(sigv, sizeof(sigv), 14695981039346656037ULL);
    if (hashNew(hc ^ 0x51a7f00dULL)) nConfig++;
  }

  if (showN < 60 && fresh) {
    showN++;
    printf("  [%3ld] %-14s n=%4d i=%4d side=%c |X|=%4d |Y|=%4d ascent=%3d",
           showN, curTag, n, i, gSide ? 'G' : 'T', mX, mY, d);
    if (ok) printf("  witness k=%3d lev=%d (d-k=%3d) peak j=%3d lev=%d",
                   k, X[k], d - k, j, X[j]);
    else printf("  NO Ceil72 witness at the first ascent");
    printf("  near(2,1,0)=(%d,%d,%d) partnerFloor=%d deep72Y=%d bothNine=%d\n",
           near2, near1, near0, partnerFloor, dY, bothNine);
  }
}

static void scanPair(int n, const char *tag) {
  nPairs++;
  curTag = tag; curN = n;
  for (int u = 0; u < n; u++) { nLinks++; if (sig[u] != rho[u]) nNonThin++; }
  {
    uint64_t h = fnv(rho, sizeof(int) * (size_t)n, 14695981039346656037ULL);
    h = fnv(sig, sizeof(int) * (size_t)n, h);
    if (hashNew(h ^ 0xabcdef01ULL)) nDistinctPairs++;
  }
  for (int i = 0; i < n; i++) {
    if (rho[i] != 5) continue;
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
    for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
    if (!(lowAt(armG, mg) && lowAt(armT, mt))) continue;
    nBase5++;
    reflArm(armG, mg, gG);
    reflArm(armT, mt, gT);
    int tG = 0, tT = 0;
    if (landLeg4(gG, mg, 6, 2, 4)) tG |= 1;
    if (landLeg4(armG, mg, 8, 1, 5)) tG |= 2;
    if (landLeg4(gG, mg, 6, 1, 4)) tG |= 4;
    if (landLeg4(gT, mt, 6, 2, 4)) tT |= 1;
    if (landLeg4(armT, mt, 8, 1, 5)) tT |= 2;
    if (landLeg4(gT, mt, 6, 1, 4)) tT |= 4;
    if (reachesNine(armG, mg) && reachesNine(armT, mt)) s3BothNineBase++;
    if (tG & tT) continue;                       /* not a crossing */
    nCross++;
    s3CrossAll++;
    if (reachesNine(armG, mg) && reachesNine(armT, mt)) s3BothNineAllCross++;
    {
      uint64_t h = fnv(armG, sizeof(int) * (size_t)mg, 14695981039346656037ULL);
      h = fnv(armT, sizeof(int) * (size_t)mt, h);
      if (hashNew(h ^ 0x1234abcdULL)) nDistinctCross++;
    }
    /* the audit sample: the greedy reading against the literal one */
    if (bruteSamples < 4000 && mg < 400) {
      bruteSamples++;
      if (landLeg4(armG, mg, 8, 1, 5) != landLeg4Brute(armG, mg, 8, 1, 5)) bruteBad++;
      if (landLeg4(gG, mg, 6, 2, 4) != landLeg4Brute(gG, mg, 6, 2, 4)) bruteBad++;
    }
    int gHas8 = (tG & 2) != 0, tHas8 = (tT & 2) != 0;
    if (gHas8 == tHas8) continue;                /* not exactly one w8 side */
    if (gHas8) {
      if (deepFirst2(armG, mg)) continue;        /* not a high run */
      measureHighRun(n, i, armG, mg, armT, mt, 1);
    } else {
      if (deepFirst2(armT, mt)) continue;
      measureHighRun(n, i, armT, mt, armG, mg, 0);
    }
  }
}

/* ------------------------------------------------- the corpus of pairs ---- */

static long variantsTried = 0, variantsFaithful = 0;
static long shaveCap = 60, fillCap = 60;

/* run the thin pair, the shavings, the fillings, the mixtures and the total
   mixture of one base level sequence */
static void runBase(const int *v, int n, const char *tag, long mixes) {
  if (n < 30 || n >= MAXN) return;
  {
    int lo = v[0], hi = v[0];
    for (int u = 0; u < n; u++) { if (v[u] < lo) lo = v[u]; if (v[u] > hi) hi = v[u]; }
    if (lo != 0 || hi != 9) return;             /* the band must be exactly [0,9] */
  }
  nSourceKinds++;
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  variantsTried++;
  if (crookedGen(rho, sig, n)) { variantsFaithful++; scanPair(n, tag); }
  else return;                                   /* an unfaithful base: skip it */

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
}

/* a window of a longer chain, shifted so that its band is [0, 9] */
static int windowSpan9(const int *v, int n, int a, int b, int *out) {
  if (a < 0 || b >= n || b - a + 1 < 30 || b - a + 1 >= MAXN) return 0;
  int lo = v[a], hi = v[a];
  for (int t = a; t <= b; t++) { if (v[t] < lo) lo = v[t]; if (v[t] > hi) hi = v[t]; }
  if (hi - lo != 9) return 0;
  for (int t = a; t <= b; t++) out[t - a] = v[t] - lo;
  return b - a + 1;
}

static int wbuf[MAXN];

int main(int argc, char **argv) {
  unsigned seed = (argc > 1) ? (unsigned)atoi(argv[1]) : 70u;
  long windows = (argc > 2) ? atol(argv[2]) : 40;
  long mixes = (argc > 3) ? atol(argv[3]) : 6;
  srandom(seed);
  memset(witLevel, 0, sizeof(witLevel));
  buildFamily();
  printf("census-batch70: the widened corpus of span-nine crossings of the branch L+5.\n");
  printf("seed=%u windows-per-chain=%ld mixtures-per-chain=%ld\n", seed, windows, mixes);
  printf("the four-leg family: %d walks (%d parameter sets and their reflections)\n",
         famN, famN / 2);
  printf("\n---- the corpus, chain by chain ----\n");

  /* (a) the Bing chains of span nine inside the band */
  {
    Path p = bpath(0, 9);
    printf("  bing 0 9: %d links\n", p.n);
    runBase(p.v, p.n, "bing 0 9", mixes);
    free(p.v);
    Path q = bpath(9, 0);
    printf("  bing 9 0: %d links\n", q.n);
    runBase(q.v, q.n, "bing 9 0", mixes);
    free(q.v);
  }

  /* (b) windows of span nine of the larger Bing chains, at grid offsets and at
     random offsets */
  for (int N = 10; N <= 13; N++) {
    Path p = bpath(0, N);
    printf("  bing 0 %d: %d links", N, p.n);
    long gridMade = 0, randMade = 0;
    if (p.n < MAXN * 4) {
      char name[64];
      /* grid offsets: a stride that is coprime with the chain's own periods */
      int stride = 149;
      for (int a = 0; a + 120 < p.n && gridMade < windows; a += stride) {
        /* the shortest window from a whose span is nine */
        int lo = p.v[a], hi = p.v[a], b = -1;
        for (int t = a; t < p.n; t++) {
          if (p.v[t] < lo) lo = p.v[t];
          if (p.v[t] > hi) hi = p.v[t];
          if (hi - lo == 9) { b = t; break; }
          if (hi - lo > 9) break;
        }
        if (b < 0) continue;
        /* extend the window while the band stays [lo, hi] */
        int e = b;
        while (e + 1 < p.n && p.v[e+1] >= lo && p.v[e+1] <= hi) e++;
        int m = windowSpan9(p.v, p.n, a, e, wbuf);
        if (!m) continue;
        snprintf(name, sizeof(name), "bing0%d-grid", N);
        gridMade++;
        runBase(wbuf, m, name, mixes);
      }
      for (long it = 0; it < windows && randMade < windows; it++) {
        int a = (int)(random() % (unsigned)(p.n - 60));
        int lo = p.v[a], hi = p.v[a], b = -1;
        for (int t = a; t < p.n; t++) {
          if (p.v[t] < lo) lo = p.v[t];
          if (p.v[t] > hi) hi = p.v[t];
          if (hi - lo == 9) { b = t; break; }
          if (hi - lo > 9) break;
        }
        if (b < 0) continue;
        int e = b;
        while (e + 1 < p.n && p.v[e+1] >= lo && p.v[e+1] <= hi) e++;
        int m = windowSpan9(p.v, p.n, a, e, wbuf);
        if (!m) continue;
        snprintf(name, sizeof(name), "bing0%d-rand", N);
        randMade++;
        runBase(wbuf, m, name, mixes);
      }
    }
    printf("  -> windows of span nine: %ld at grid offsets, %ld at random offsets\n",
           gridMade, randMade);
    free(p.v);
  }

  /* (c) the chains outside Bing's family */
  {
    int bk[4] = {1, 2, 2, 1}, fw[4] = {2, 1, 2, 3};
    for (int q = 0; q < 4; q++) {
      Path r = vpath(0, 9, bk[q], fw[q]);
      char name[64];
      snprintf(name, sizeof(name), "vpath 0 9 (%d,%d)", bk[q], fw[q]);
      printf("  %s: %d links\n", name, r.n);
      runBase(r.v, r.n, name, mixes);
      free(r.v);
      Path s = vpath(9, 0, bk[q], fw[q]);
      snprintf(name, sizeof(name), "vpath 9 0 (%d,%d)", bk[q], fw[q]);
      printf("  %s: %d links\n", name, s.n);
      runBase(s.v, s.n, name, mixes);
      free(s.v);
    }
  }

  /* (d) random concatenations of Bing blocks, and windows of span nine of them */
  {
    static int v[MAXN * 2];
    long made = 0;
    for (long it = 0; it < windows; it++) {
      int nb = 2 + (int)(random() % 3), n = 0, cur = (int)(random() % 10), first = 1;
      for (int b = 0; b < nb; b++) {
        int nx; do { nx = (int)(random() % 10); } while (nx == cur);
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
        if (hi - lo == 9) {
          static int sh[MAXN];
          for (int u = 0; u < n; u++) sh[u] = v[u] - lo;
          made++;
          runBase(sh, n, "concat", mixes);
          continue;
        }
      }
      /* otherwise take a window of span nine */
      int a = (int)(random() % (unsigned)(n - 40));
      int lo = v[a], hi = v[a], b = -1;
      for (int t = a; t < n; t++) {
        if (v[t] < lo) lo = v[t];
        if (v[t] > hi) hi = v[t];
        if (hi - lo == 9) { b = t; break; }
        if (hi - lo > 9) break;
      }
      if (b < 0) continue;
      int e = b;
      while (e + 1 < n && v[e+1] >= lo && v[e+1] <= hi) e++;
      int m = windowSpan9(v, n, a, e, wbuf);
      if (!m) continue;
      made++;
      runBase(wbuf, m, "concat-window", mixes);
    }
    printf("  random concatenations of Bing blocks: %ld used\n", made);
  }

  /* ------------------------------------------------------------- the report */
  printf("\n================ the corpus ================\n");
  printf("  base level sequences of band [0,9] swept: %ld\n", nSourceKinds);
  printf("  pairs tried: %ld;  faithful: %ld;  scanned: %ld (%ld distinct)\n",
         variantsTried, variantsFaithful, nPairs, nDistinctPairs);
  printf("  links: %ld, of which not thin: %ld\n", nLinks, nNonThin);
  printf("  basepoints of the branch L+5: %ld\n", nBase5);
  printf("  crossings of the trichotomy: %ld (%ld distinct by their pair of arms)\n",
         nCross, nDistinctCross);
  printf("  high-run crossings (exactly one w8 side, that side not deep first at 2):"
         " %ld (%ld distinct)\n", nHighRun, nHighRunDistinct);
  printf("  distinct configurations among the high-run crossings: %ld\n", nConfig);
  printf("  arm lengths at the high-run crossings: %ld to %ld\n", armMin, armMax);
  printf("  both arms satisfy Mid2Floor at %ld of the %ld high-run crossings\n",
         nMid2Both, nHighRun);

  printf("\n======== statement 1: the distance (NearLowT / NearLowG) ========\n");
  printf("  a time of the pair at 2 or below within 67 steps across the basepoint:\n");
  printf("    holds at %ld, fails at %ld, no such time at all at %ld\n", s1Hold, s1Fail, s1None);
  printf("    the distance to the nearest such time ranges over [%ld, %ld]\n", s1Min, s1Max);
  printf("  at 1 or below within 166 steps (the reading from a link at L+1, z 7 = 170):\n");
  printf("    holds at %ld, fails at %ld, none at %ld; distance in [%ld, %ld]\n",
         near1Hold, near1Fail, near1None, near1Min, near1Max);
  printf("  at the floor 0 within 405 steps (the reading from a link at L, z 8 = 409):\n");
  printf("    holds at %ld, fails at %ld, none at %ld; distance in [%ld, %ld]\n",
         near0Hold, near0Fail, near0None, near0Min, near0Max);
  printf("  at least one of the three readings is available: %ld of %ld (fails at %ld)\n",
         sAnyHold, nHighRun, sAnyFail);
  printf("  Ceil72 holds at every ascent of the running arm at %ld of %ld;"
         " a witness at the first ascent at %ld\n", cCeil72All, nHighRun, cCeil72Wit);
  printf("  the level of the low landmark:");
  for (int u = 0; u < 12; u++) if (witLevel[u]) printf("  level %d : %ld", u, witLevel[u]);
  printf("\n  the distance from the ascent to the low landmark ranges over [%ld, %ld]\n",
         distMin, distMax);
  printf("  the peak index ranges over [%ld, %ld], its level over [%ld, %ld]\n",
         peakMin, peakMax, peakLevMin, peakLevMax);

  printf("\n======== statement 2: the partner's deep-floor clause ========\n");
  printf("  the band reaches the floor at %ld of the %ld high-run crossings\n",
         s2BandFloor, nHighRun);
  printf("  the partner's own arm reaches the floor at %ld; it does not at %ld"
         " (there Deep72 is vacuous)\n", s2ArmFloor, s2ArmNoFloor);
  printf("  where it does, the partner's Deep72 holds at %ld and fails at %ld\n", s2Hold, s2Fail);
  printf("  the running arm reaches the floor at %ld; there its Deep72 holds at %ld,"
         " fails at %ld,\n  and NineBeforeDeep holds at %ld\n",
         s2RunFloor, s2RunHold, s2RunFail, s2RunNine);
  printf("  question 2.3, the reading at the partner's floor descent: %ld cases;\n"
         "    the pairing's two landmarks, with a third at 6 or above, can be placed as\n"
         "    times of the partner's arm at %ld, and cannot at %ld;\n"
         "    the partner's arm carries 9 at some link at %ld\n",
         q23Cases, q23Reading, q23NoReading, q23Carry9);

  printf("\n  the same clause also admits landmarks past the basepoint, on the running\n"
         "  arm, at %ld of the %ld cases: the pairing by itself does not place them on\n"
         "  the partner's arm\n", q23Escape, q23Cases);

  printf("\n======== statement 3: BothNineL5 ========\n");
  printf("  both arms reach 9 at %ld of the %ld high-run crossings\n", s3BothNine, nHighRun);
  printf("  both arms reach 9 at %ld of the %ld crossings of the trichotomy\n",
         s3BothNineAllCross, s3CrossAll);
  printf("  both arms reach 9 at %ld of the %ld basepoints of the branch L+5\n",
         s3BothNineBase, nBase5);
  printf("  of the %ld high-run crossings with both arms at 9, the partner is deep first at 2\n"
         "  at %ld (its ceiling clause is then the batch-68 theorem) and runs high at %ld;\n"
         "  where it runs high, the mirror distance holds at %ld and fails at %ld;\n"
         "  the partner's ceiling clause Ceil72 holds at %ld of the %ld\n",
         s3BothNine, bnPartnerDeep2, bnPartnerRun, bnPartnerNear, bnPartnerFar,
         bnPartnerCeil, s3BothNine);
  printf("  of the %ld high-run crossings with both arms at 9: some walk of the four-leg\n"
         "  family serves both arms at %ld, none does at %ld, and both arms satisfy the\n"
         "  landmark sentence of w72 at %ld; the least |X| + |Y| seen is %ld\n",
         s3BothNine, bnServed, bnNone, bnW72Both, bnArmMin);

  printf("\n---- the audit sample ----\n");
  printf("  the landmark sentence read greedily against the same sentence with its\n"
         "  existentials searched literally: %ld samples, %ld disagreements\n",
         bruteSamples, bruteBad);
  printf("  every predicate of this census is evaluated by its own definition:\n"
         "    IsCrookedIvF, LowAt, Leg4Land (greedy and literal), DeepFirst2, Ceil72,\n"
         "    Deep72, Mid2Floor, NineBeforeDeep, and the crookedness clause read as\n"
         "    crooked_peak_valley_high9_mid reads it.  No criterion of the engine is used.\n");
  return 0;
}
