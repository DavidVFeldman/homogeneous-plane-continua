/* census-batch72.c -- batch 72.  The valley at L + 3.
 *
 * The commission of batch 72 asks where Valley3BeforeNine -- the landmark pair
 * that batch 71 showed is equivalent to Ceil72 on an arm of the band -- is a
 * fact, and what reading places its valley:
 *
 *   2.1  at every basepoint of the branch whose arm runs high, does that arm
 *        satisfy Valley3BeforeNine?  At every basepoint of the band with LowAt
 *        on that arm?  Without LowAt?  The five classes are measured separately,
 *        so the answer places the statement.
 *   2.2  the reading: a link carrying L+5 on the running arm's own side and a
 *        link carrying L+2 later in chain order put a link carrying L+3 between
 *        them; is that reading available at each high-run crossing, does it name
 *        the Ceil72 valley, and where does the valley sit?
 *   2.4  BothHighRunL5 at a crossing, and the shape of a both-high-run basepoint.
 *
 * The corpus, the predicates and the audit protocol are those of
 * census-batch70.c / census-batch71.c, unchanged and re-run here.
 *
 * Usage: census-batch72 [seed] [windows-per-chain] [mixtures-per-chain]
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
#define MAXN   4096
/* the corpus generators keep batch 70's length bound, so the corpus is the same;
   the larger MAXN is only room for the edited pairs of the construction attempt */
#define MAXBASE 2400

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

/* --------------------------------------------- batch 71: the anatomy table */

#define MAXROW 4096

typedef struct {
  int n, i, gSide, mX, mY;
  int near2, lev2, sigLev2, near1, near0;
  int ascent, wj, wk, wjLev, wkLev;
  int minBetween, maxBetween, nThree, firstHigh, lastHigh;
  int roleValley, rolePeak, rsrc, rdst, rlevS, rlevT, rspan;
  int bothNine, partnerFloor, deepY, bothRun;
  char tag[16];
} Row;
static Row rows[MAXROW];
static long nRows = 0;



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
static long nBand5 = 0;                  /* basepoints of the band, LowAt not asked */
static long nDistinctPairs = 0, nDistinctCross = 0;
static long nHighRun = 0;
static long nSourceKinds = 0;
static long armMin = 1 << 30, armMax = -1;
static long bruteSamples = 0, bruteBad = 0;
static const char *curTag = "";

/* ---- question 2.1: Valley3BeforeNine on a running arm, by class ---------- *
 *
 * class 0: every arm of a basepoint of the band (rho i = 5) that runs high,
 *          LowAt asked of nothing;
 * class 1: the same, with LowAt (L+1) (L+8) on that arm alone;
 * class 2: the same, with LowAt on both arms -- a basepoint of the branch;
 * class 3: an arm that runs high at a crossing of the trichotomy;
 * class 4: the running arm of a high-run crossing (the 229 of batch 71).
 */
#define NCLASS 5
static const char *className[NCLASS] = {
  "the band, LowAt asked of nothing",
  "the band, LowAt on the running arm",
  "the branch (LowAt on both arms)",
  "a running arm at a crossing",
  "the running arm of a high-run crossing"
};
static long clsN[NCLASS], clsHold[NCLASS], clsFail[NCLASS];
static long clsEmin[NCLASS], clsEmax[NCLASS];
static long clsFailEmin[NCLASS], clsFailEmax[NCLASS];
static long clsFailNoLow[NCLASS], clsFailNoPeak[NCLASS];
static long clsArmMin[NCLASS], clsArmMax[NCLASS];

/* the histogram of the first ascent of a running arm, over class 0 */
static long eHist[64];
static long eHistBig = 0;

/* question 2.2: the reading that places the valley */
static long rdCases = 0, rdHaveFive = 0, rdHaveLow = 0, rdNames = 0, rdNamesBefore = 0;
static long rdGapMin = 1 << 30, rdGapMax = -1;   /* chain steps from the L+5 link to the landmark */
static long rdArmMin = 1 << 30, rdArmMax = -1;   /* the arm index of the landmark */
static long rdPastAscent = 0;

/* question 2.4: both arms running high */
static long q24Base = 0, q24Cross = 0, q24High = 0;
static long q24w8 = 0, q24w3 = 0, q24wb = 0, q24Both3 = 0, q24Bothb = 0, q24Neither = 0;

static long clsServed[NCLASS], clsUnserved[NCLASS], clsW72Both[NCLASS];
static long showFail[NCLASS];
static long witWritten[NCLASS];

static void initCounters(void) {
  for (int c = 0; c < NCLASS; c++) {
    clsN[c] = clsHold[c] = clsFail[c] = 0;
    clsEmin[c] = 1 << 30; clsEmax[c] = -1;
    clsFailEmin[c] = 1 << 30; clsFailEmax[c] = -1;
    clsFailNoLow[c] = clsFailNoPeak[c] = 0;
    clsArmMin[c] = 1 << 30; clsArmMax[c] = -1;
    showFail[c] = 0; witWritten[c] = 0;
    clsServed[c] = clsUnserved[c] = clsW72Both[c] = 0;
  }
}

/* HighRunG / HighRunT of HPC/Fold/Reading70.lean at L = 0, written out: the arm
   reaches 9 and has nothing at 2 or below strictly before its first such time. */
static int runsHigh(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] >= 9) return 1;
    if (f[d] <= 2) return 0;
  }
  return 0;
}

/* Valley3BeforeNine of HPC/Fold/Distance71.lean at L = 0, by its own definition:
   exists j k with 3 <= j, j + 5 <= k, f j >= 6, f k <= 3 and every d with
   f d >= 9 has k + 6 <= d.  Returns 1/0; on failure *why is 1 if no time at 3 or
   below lies early enough and 2 if such a time exists but no peak precedes it. */
static int valley3BeforeNine(const int *f, int m, int *why, int *pj, int *pk) {
  int e = -1;
  for (int d = 0; d < m; d++) if (f[d] >= 9) { e = d; break; }
  int lim = (e < 0) ? m - 1 : e - 6;             /* k must satisfy k + 6 <= e */
  int peak = -1, anyLow = 0;
  for (int k = 0; k <= lim && k < m; k++) {
    /* peaks at index >= 3 and at most k - 5 */
    for (int j = (peak < 0 ? 3 : peak + 1); j + 5 <= k; j++)
      if (j < m && f[j] >= 6) { if (peak < 0) peak = j; }
    if (f[k] <= 3) {
      anyLow = 1;
      if (peak >= 0 && peak + 5 <= k) { if (pj) *pj = peak; if (pk) *pk = k; return 1; }
    }
  }
  if (why) *why = anyLow ? 2 : 1;
  return 0;
}

static void dumpWitness(const char *name, int n, int i, int gSide) {
  FILE *fp = fopen(name, "w");
  if (!fp) return;
  fprintf(fp, "%d %d %d\n", n, i, gSide);
  for (int t = 0; t < n; t++) fprintf(fp, "%d%c", rho[t], t + 1 == n ? '\n' : ' ');
  for (int t = 0; t < n; t++) fprintf(fp, "%d%c", sig[t], t + 1 == n ? '\n' : ' ');
  fclose(fp);
}

/* record one running arm in one class.  X is the running arm, gSide = 1 when it
   is the forward arm. */
static int recordArm(int cls, int n, int i, const int *X, int mX,
                     const int *Y, int mY, int gSide, const char *what) {
  int why = 0, j = -1, k = -1;
  int e = -1;
  for (int d = 0; d < mX; d++) if (X[d] >= 9) { e = d; break; }
  int ok = valley3BeforeNine(X, mX, &why, &j, &k);
  clsN[cls]++;
  if (e >= 0) {
    if (e < clsEmin[cls]) clsEmin[cls] = e;
    if (e > clsEmax[cls]) clsEmax[cls] = e;
  }
  if (mX < clsArmMin[cls]) clsArmMin[cls] = mX;
  if (mX > clsArmMax[cls]) clsArmMax[cls] = mX;
  if (ok) clsHold[cls]++;
  else {
    clsFail[cls]++;
    if (why == 1) clsFailNoLow[cls]++; else clsFailNoPeak[cls]++;
    if (e >= 0) {
      if (e < clsFailEmin[cls]) clsFailEmin[cls] = e;
      if (e > clsFailEmax[cls]) clsFailEmax[cls] = e;
    }
    int served = -1;
    for (int q = 0; q < famN && served < 0; q++)
      if (famFoldsBoth(q, X, mX, Y, mY)) served = q;
    if (served >= 0) clsServed[cls]++; else clsUnserved[cls]++;
    if (landLeg4(X, mX, 7, 2, 5) && landLeg4(Y, mY, 7, 2, 5)) clsW72Both[cls]++;
    if (showFail[cls] < 6) {
      showFail[cls]++;
      printf("  VALLEY3 FAILS [%s] %-14s n=%4d i=%4d side=%c |X|=%4d ascent=%d"
             " (%s)\n", className[cls], curTag, n, i, gSide ? 'G' : 'T', mX, e,
             why == 1 ? "no time at 3 or below early enough"
                      : "a low time, but no peak five steps before it");
      printf("    a walk of the four-leg family serving both arms: %s;"
             " both arms satisfy the w72 sentence: %s\n",
             served >= 0 ? "yes" : "NONE",
             (landLeg4(X, mX, 7, 2, 5) && landLeg4(Y, mY, 7, 2, 5)) ? "yes" : "no");
      printf("    the running arm:");
      for (int u = 0; u < mX && u < 60; u++) printf(" %d", X[u]);
      printf("\n");
    }
    if (!witWritten[cls]) {
      char nm[64];
      snprintf(nm, sizeof(nm), "witness-batch72-c%d.txt", cls);
      dumpWitness(nm, n, i, gSide);
      witWritten[cls] = 1;
      printf("    stored as %s (%s)\n", nm, what);
    }
  }
  return ok;
}

/* the seeds of the construction of §2.3: whole pairs at a basepoint of the
   branch whose running arm fails Valley3BeforeNine, one per fresh pair */
#define MAXSEED 96
typedef struct { int n, i, gSide, tG, tT, e; } SeedHdr;
static SeedHdr seedHdr[MAXSEED];
static int seedRho[MAXSEED][MAXN], seedSig[MAXSEED][MAXN];
static long nSeeds = 0;

static long sharedHist[8];
static long nSeedCand = 0;

/* a reservoir sample of the failing basepoints, so the seeds are spread over the
   whole corpus and not over the variants of one chain */
static void storeSeed(int n, int i, int gSide, int tG, int tT, int e) {
  sharedHist[(tG & tT) & 7]++;
  if (n >= MAXBASE) return;
  nSeedCand++;
  static uint64_t rs = 88172645463325252ULL;    /* a stream of its own, so the corpus
                                                   generator's random() is untouched */
  rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
  long slot = -1;
  if (nSeeds < MAXSEED) slot = nSeeds++;
  else if ((long)(rs % (uint64_t)nSeedCand) < MAXSEED) slot = (long)(rs % MAXSEED);
  if (slot < 0) return;
  SeedHdr *S = &seedHdr[slot];
  S->n = n; S->i = i; S->gSide = gSide; S->tG = tG; S->tT = tT; S->e = e;
  memcpy(seedRho[slot], rho, sizeof(int) * (size_t)n);
  memcpy(seedSig[slot], sig, sizeof(int) * (size_t)n);
}

static void writeSeeds(void) {
  FILE *fp = fopen("seeds-batch72.txt", "w");
  if (!fp) return;
  fprintf(fp, "%ld\n", nSeeds);
  for (long q = 0; q < nSeeds; q++) {
    SeedHdr *S = &seedHdr[q];
    fprintf(fp, "%d %d %d %d %d %d\n", S->n, S->i, S->gSide, S->tG, S->tT, S->e);
    for (int t = 0; t < S->n; t++) fprintf(fp, "%d%c", seedRho[q][t], t + 1 == S->n ? '\n' : ' ');
    for (int t = 0; t < S->n; t++) fprintf(fp, "%d%c", seedSig[q][t], t + 1 == S->n ? '\n' : ' ');
  }
  fclose(fp);
}

/* question 2.2: the descending pairing that places the valley.  On the running
   arm's own side, a link carrying 5 or more at arm index a0 >= 1, and, later in
   chain order, a link carrying 2. */
static long rdNamesValley = 0, rdSpanMin = 1 << 30, rdSpanMax = -1;
static long rdLowDistMin = 1 << 30, rdLowDistMax = -1;
static long rdA0Min = 1 << 30, rdA0Max = -1, rdArmGapMin = 1 << 30, rdArmGapMax = -1;
static long rdAnyOnArm = 0;

/* question 2.2.  The reading that places the valley: a link carrying L+5 on the
   running arm's own side, at arm index a0, and a link carrying L+2 on the far
   side of the basepoint.  Crookedness puts a link carrying L+3 between them --
   the first one after the L+5 link when the running arm is the backward arm (the
   descending pairing 5 -> 2), the second one when it is the forward arm (the
   ascending pairing 2 -> 5).  Every L+5 link of the arm is tried, and the
   question asked of each reading is where its landmark sits: on the running arm
   before its first ascent, and is it the Ceil72 valley itself. */
static void reading(int n, int i, const int *X, int mX, int gSide, int e) {
  rdCases++;
  int dir = gSide ? 1 : -1;
  int vj = -1, vk = -1;
  int haveValley = (e >= 0) ? ceil72WitnessAt(X, mX, e, &vj, &vk) : 0;
  int haveFive = 0, haveLow = 0, anyRead = 0, anyOnArm = 0, namesValley = 0;
  int bestSpan = 1 << 30, bestLow = -1, bestA0 = -1, bestGap = -1;
  /* the nearest link carrying L+2 on the partner's side */
  int lowOff = -1;
  for (int b0 = 1; b0 <= 2500; b0++) {
    int t = i - dir * b0;
    if (t < 0 || t >= n) break;
    if (rho[t] <= 2 && 2 <= sig[t]) { lowOff = b0; break; }
  }
  if (lowOff > 0) haveLow = 1;
  for (int a0 = 1; a0 < mX && a0 <= 400 && lowOff > 0; a0++) {
    int s = i + dir * a0;
    if (s < 0 || s >= n) break;
    if (!(rho[s] <= 5 && 5 <= sig[s])) continue;
    haveFive = 1;
    int t = i - dir * lowOff;
    int land = -1;
    if (dir < 0) {
      int p1 = meetTab[3][s + 1];
      if (p1 < t) land = p1;
    } else {
      int p1 = meetTab[4][t + 1];
      if (p1 < s) { int p2 = meetTab[3][p1 + 1]; if (p2 < s) land = p2; }
    }
    if (land < 0) continue;
    anyRead = 1;
    int span = a0 + lowOff;
    int onArm = gSide ? (land >= i) : (land <= i);
    if (onArm) {
      int armIdx = gSide ? (land - i) : (i - land);
      if (e < 0 || armIdx <= e - 6) {
        anyOnArm = 1;
        if (armIdx < rdArmMin) rdArmMin = armIdx;
        if (armIdx > rdArmMax) rdArmMax = armIdx;
        if (a0 - armIdx < rdArmGapMin) rdArmGapMin = a0 - armIdx;
        if (a0 - armIdx > rdArmGapMax) rdArmGapMax = a0 - armIdx;
        if (a0 < rdA0Min) rdA0Min = a0;
        if (a0 > rdA0Max) rdA0Max = a0;
        if (haveValley && armIdx == vk) namesValley = 1;
        if (span < bestSpan) { bestSpan = span; bestLow = lowOff; bestA0 = a0; bestGap = a0 - armIdx; }
      } else if (e >= 0 && armIdx > e - 6) rdPastAscent++;
    }
  }
  if (haveFive) rdHaveFive++;
  if (haveLow) rdHaveLow++;
  if (anyRead) rdNames++;
  if (anyOnArm) { rdAnyOnArm++; rdNamesBefore++; }
  if (namesValley) rdNamesValley++;
  if (bestSpan < (1 << 30)) {
    if (bestSpan < rdSpanMin) rdSpanMin = bestSpan;
    if (bestSpan > rdSpanMax) rdSpanMax = bestSpan;
    if (bestLow < rdLowDistMin) rdLowDistMin = bestLow;
    if (bestLow > rdLowDistMax) rdLowDistMax = bestLow;
    if (bestGap < rdGapMin) rdGapMin = bestGap;
    if (bestGap > rdGapMax) rdGapMax = bestGap;
  }
}

static void scanPair(int n, const char *tag) {
  nPairs++;
  curTag = tag;
  for (int u = 0; u < n; u++) { nLinks++; if (sig[u] != rho[u]) nNonThin++; }
  {
    uint64_t h = fnv(rho, sizeof(int) * (size_t)n, 14695981039346656037ULL);
    h = fnv(sig, sizeof(int) * (size_t)n, h);
    if (hashNew(h ^ 0xabcdef01ULL)) nDistinctPairs++;
  }
  for (int i = 0; i < n; i++) {
    if (rho[i] != 5) continue;
    nBand5++;
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
    for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
    int runG = runsHigh(armG, mg), runT = runsHigh(armT, mt);
    int lowG = lowAt(armG, mg), lowT = lowAt(armT, mt);

    /* class 0: the band, LowAt asked of nothing */
    if (runG) recordArm(0, n, i, armG, mg, armT, mt, 1, "class 0, the band alone");
    if (runT) recordArm(0, n, i, armT, mt, armG, mg, 0, "class 0, the band alone");
    /* the histogram of the first ascent */
    if (runG) { int e = firstNine(armG, mg); if (e >= 0) { if (e < 64) eHist[e]++; else eHistBig++; } }
    if (runT) { int e = firstNine(armT, mt); if (e >= 0) { if (e < 64) eHist[e]++; else eHistBig++; } }
    /* class 1: LowAt on the running arm alone */
    if (runG && lowG) recordArm(1, n, i, armG, mg, armT, mt, 1, "class 1, LowAt on the arm");
    if (runT && lowT) recordArm(1, n, i, armT, mt, armG, mg, 0, "class 1, LowAt on the arm");
    if (!(lowG && lowT)) continue;
    nBase5++;
    /* class 2: a basepoint of the branch */
    int failG = runG && !recordArm(2, n, i, armG, mg, armT, mt, 1, "class 2, the branch");
    int failT = runT && !recordArm(2, n, i, armT, mt, armG, mg, 0, "class 2, the branch");
    if (runG && runT) q24Base++;

    reflArm(armG, mg, gG);
    reflArm(armT, mt, gT);
    int tG = 0, tT = 0;
    if (landLeg4(gG, mg, 6, 2, 4)) tG |= 1;      /* w3 */
    if (landLeg4(armG, mg, 8, 1, 5)) tG |= 2;    /* w8 */
    if (landLeg4(gG, mg, 6, 1, 4)) tG |= 4;      /* wb */
    if (landLeg4(gT, mt, 6, 2, 4)) tT |= 1;
    if (landLeg4(armT, mt, 8, 1, 5)) tT |= 2;
    if (landLeg4(gT, mt, 6, 1, 4)) tT |= 4;
    /* the audit sample: the greedy reading against the literal one */
    if (bruteSamples < 4000 && mg < 400) {
      bruteSamples++;
      if (landLeg4(armG, mg, 8, 1, 5) != landLeg4Brute(armG, mg, 8, 1, 5)) bruteBad++;
      if (landLeg4(gG, mg, 6, 2, 4) != landLeg4Brute(gG, mg, 6, 2, 4)) bruteBad++;
    }
    if (failG) storeSeed(n, i, 1, tG, tT, firstNine(armG, mg));
    if (failT) storeSeed(n, i, 0, tG, tT, firstNine(armT, mt));
    if (runG && runT) {
      /* question 2.4: the shape of a both-high-run basepoint */
      if ((tG & 2) || (tT & 2)) q24w8++;
      if ((tG & 1) && (tT & 1)) q24Both3++; else if ((tG & 1) || (tT & 1)) q24w3++;
      if ((tG & 4) && (tT & 4)) q24Bothb++; else if ((tG & 4) || (tT & 4)) q24wb++;
      if (!(tG & (1 | 4)) && !(tT & (1 | 4))) q24Neither++;
    }
    if (tG & tT) continue;                       /* not a crossing */
    nCross++;
    if (runG && runT) q24Cross++;
    {
      uint64_t h = fnv(armG, sizeof(int) * (size_t)mg, 14695981039346656037ULL);
      h = fnv(armT, sizeof(int) * (size_t)mt, h);
      if (hashNew(h ^ 0x1234abcdULL)) nDistinctCross++;
    }
    /* class 3: a running arm at a crossing */
    if (runG) recordArm(3, n, i, armG, mg, armT, mt, 1, "class 3, a crossing");
    if (runT) recordArm(3, n, i, armT, mt, armG, mg, 0, "class 3, a crossing");
    int gHas8 = (tG & 2) != 0, tHas8 = (tT & 2) != 0;
    if (gHas8 == tHas8) continue;                /* not exactly one w8 side */
    if (gHas8 && runG) {
      nHighRun++;
      if (mg < armMin) armMin = mg;
      if (mg > armMax) armMax = mg;
      if (mt < armMin) armMin = mt;
      if (mt > armMax) armMax = mt;
      if (runT) q24High++;
      recordArm(4, n, i, armG, mg, armT, mt, 1, "class 4, a high-run crossing");
      reading(n, i, armG, mg, 1, firstNine(armG, mg));
    } else if (tHas8 && runT) {
      nHighRun++;
      if (mg < armMin) armMin = mg;
      if (mg > armMax) armMax = mg;
      if (mt < armMin) armMin = mt;
      if (mt > armMax) armMax = mt;
      if (runG) q24High++;
      recordArm(4, n, i, armT, mt, armG, mg, 0, "class 4, a high-run crossing");
      reading(n, i, armT, mt, 0, firstNine(armT, mt));
    }
  }
}

/* ------------------------------------------------- the corpus of pairs ---- */

static long variantsTried = 0, variantsFaithful = 0;
static long shaveCap = 60, fillCap = 60;

/* run the thin pair, the shavings, the fillings, the mixtures and the total
   mixture of one base level sequence */
static void runBase(const int *v, int n, const char *tag, long mixes) {
  if (n < 30 || n >= MAXBASE) return;
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
  if (a < 0 || b >= n || b - a + 1 < 30 || b - a + 1 >= MAXBASE) return 0;
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
  initCounters();
  buildFamily();
  printf("census-batch72: the valley at L + 3 -- Valley3BeforeNine on a running arm.\n");
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
    if (p.n < MAXBASE * 4) {
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
    static int v[MAXBASE * 2];
    long made = 0;
    for (long it = 0; it < windows; it++) {
      int nb = 2 + (int)(random() % 3), n = 0, cur = (int)(random() % 10), first = 1;
      for (int b = 0; b < nb; b++) {
        int nx; do { nx = (int)(random() % 10); } while (nx == cur);
        Path blk = bpath(cur, nx);
        if (n + blk.n >= MAXBASE * 2 - 4) { free(blk.v); break; }
        if (first) { memcpy(v, blk.v, sizeof(int) * blk.n); n = blk.n; first = 0; }
        else { memcpy(v + n, blk.v + 1, sizeof(int) * (blk.n - 1)); n += blk.n - 1; }
        cur = nx; free(blk.v);
      }
      if (n < 200) continue;
      if (n < MAXBASE) {
        int lo = v[0], hi = v[0];
        for (int u = 0; u < n; u++) { if (v[u] < lo) lo = v[u]; if (v[u] > hi) hi = v[u]; }
        if (hi - lo == 9) {
          static int sh[MAXBASE];
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
  printf("  basepoints of the band (rho i = L+5, LowAt asked of nothing): %ld\n", nBand5);
  printf("  basepoints of the branch L+5 (LowAt on both arms): %ld\n", nBase5);
  printf("  crossings of the trichotomy: %ld (%ld distinct by their pair of arms)\n",
         nCross, nDistinctCross);
  printf("  high-run crossings: %ld; arm lengths there: %ld to %ld\n",
         nHighRun, armMin, armMax);

  printf("\n======== question 2.1: Valley3BeforeNine on a running arm ========\n");
  printf("  a running arm is an arm of a basepoint at L+5 that reaches L+9 with\n"
         "  nothing at L+2 or below before its first such time (HighRunG/HighRunT).\n"
         "  Valley3BeforeNine is read by its own definition: a peak at L+6 or above\n"
         "  at arm index three or more, a time at L+3 or below five steps later, and\n"
         "  every ascent to L+9 at least six steps after that.\n\n");
  printf("  class                                    arms   holds    fails  ascent range"
         "   arm lengths\n");
  for (int c = 0; c < NCLASS; c++) {
    printf("  %-38s %6ld %7ld %8ld  [%3ld,%4ld]  [%4ld,%5ld]\n", className[c], clsN[c],
           clsHold[c], clsFail[c], clsEmin[c] == (1 << 30) ? -1 : clsEmin[c], clsEmax[c],
           clsArmMin[c] == (1 << 30) ? -1 : clsArmMin[c], clsArmMax[c]);
  }
  printf("\n  where it fails:\n");
  for (int c = 0; c < NCLASS; c++) {
    if (!clsFail[c]) { printf("  %-38s never fails\n", className[c]); continue; }
    printf("  %-38s %ld failures: %ld with no time at L+3 or below early enough,\n"
           "      %ld with such a time but no peak five steps before it; the first ascent\n"
           "      of a failing arm ranges over [%ld, %ld]; a walk of the four-leg family\n"
           "      serves both arms at %ld of them and at none at %ld; both arms satisfy the\n"
           "      w72 sentence at %ld\n",
           className[c], clsFail[c], clsFailNoLow[c], clsFailNoPeak[c],
           clsFailEmin[c] == (1 << 30) ? -1 : clsFailEmin[c], clsFailEmax[c],
           clsServed[c], clsUnserved[c], clsW72Both[c]);
  }
  printf("\n  the histogram of the first ascent of a running arm (class 0):\n   ");
  for (int u = 0; u < 64; u++) if (eHist[u]) printf(" %d:%ld", u, eHist[u]);
  printf("  64+:%ld\n", eHistBig);
  printf("  (the timing law forbids an ascent before arm index 12, and\n"
         "   Valley3BeforeNine is unsatisfiable when the first ascent is at 13 or less:\n"
         "   it asks for a peak at index three or more and a valley five steps later,\n"
         "   six steps before the ascent.)\n");

  printf("\n======== question 2.2: the reading that places the valley ========\n");
  printf("  at each of the %ld high-run crossings, the descending pairing from a link\n"
         "  carrying L+5 on the running arm's own side to a link carrying L+2 later in\n"
         "  chain order; its first landmark carries L+3.\n", rdCases);
  printf("    a link carrying L+5 on the running arm's side within 400 steps: %ld\n", rdHaveFive);
  printf("    and a link carrying L+2 on the partner's side within 2500: %ld\n", rdHaveLow);
  printf("    a reading of that shape exists: %ld; some reading of that shape puts its\n"
         "    landmark on the running arm at an arm index the clause can use: %ld\n",
         rdNames, rdNamesBefore);
  printf("    the span of the reading ranges over [%ld, %ld]; the L+2 link lies %ld to %ld\n"
         "    steps past the basepoint; the chain gap from the L+5 link to the landmark\n"
         "    ranges over [%ld, %ld]\n",
         rdSpanMin == (1 << 30) ? -1 : rdSpanMin, rdSpanMax,
         rdLowDistMin == (1 << 30) ? -1 : rdLowDistMin, rdLowDistMax,
         rdGapMin == (1 << 30) ? -1 : rdGapMin, rdGapMax);
  printf("    and the landmark is exactly the Ceil72 valley of the running arm at %ld\n",
         rdNamesValley);
  printf("    where a landmark is on the running arm its arm index ranges over"
         " [%ld, %ld],\n    the L+5 link that names it sits at arm index [%ld, %ld], and the\n"
         "    landmark sits %ld to %ld steps past that link (in arm indices);\n"
         "    readings whose landmark lands past the point the clause can use: %ld\n",
         rdArmMin == (1 << 30) ? -1 : rdArmMin, rdArmMax,
         rdA0Min == (1 << 30) ? -1 : rdA0Min, rdA0Max,
         rdArmGapMin == (1 << 30) ? -1 : rdArmGapMin, rdArmGapMax, rdPastAscent);

  printf("\n======== question 2.4: both arms running high ========\n");
  printf("  BothHighRunL5 (both arms reach L+9 with nothing at L+2 or below before):\n");
  printf("    at %ld of the %ld basepoints of the branch\n", q24Base, nBase5);
  printf("    at %ld of the %ld crossings of the trichotomy\n", q24Cross, nCross);
  printf("    at %ld of the %ld high-run crossings\n", q24High, nHighRun);
  printf("  the shape of a both-high-run basepoint of the branch: at least one arm is a\n"
         "  w8 arm at %ld; both arms are w3 arms at %ld, exactly one at %ld; both are wb\n"
         "  arms at %ld, exactly one at %ld; neither arm is w3 or wb at %ld\n",
         q24w8, q24Both3, q24w3, q24Bothb, q24wb, q24Neither);

  printf("\n======== the seeds of the construction of 2.3 ========\n");
  writeSeeds();
  printf("  whole pairs at a basepoint of the branch whose running arm fails\n"
         "  Valley3BeforeNine, one per fresh pair: %ld, written to seeds-batch72.txt\n",
         nSeeds);
  printf("  the failing basepoints by the walks their two arms share: ");
  for (int u = 0; u < 8; u++) if (sharedHist[u])
    printf(" [%s%s%s]:%ld", (u & 1) ? "w3" : "", (u & 2) ? "w8" : "", (u & 4) ? "wb" : "",
           sharedHist[u]);
  printf("  (%ld candidates sampled to %ld seeds)\n", nSeedCand, nSeeds);
  printf("  seed  n     i  side  w3/w8/wb of the forward arm and of the backward arm"
         "  ascent\n");
  for (long q = 0; q < nSeeds && q < 24; q++) {
    SeedHdr *S = &seedHdr[q];
    printf("  %4ld %4d %5d   %c    G:%c%c%c  T:%c%c%c   shared:%s   %d\n", q, S->n, S->i,
           S->gSide ? 'G' : 'T',
           (S->tG & 1) ? '3' : '-', (S->tG & 2) ? '8' : '-', (S->tG & 4) ? 'b' : '-',
           (S->tT & 1) ? '3' : '-', (S->tT & 2) ? '8' : '-', (S->tT & 4) ? 'b' : '-',
           (S->tG & S->tT) ? ((S->tG & S->tT & 1) ? " w3" : ((S->tG & S->tT & 2) ? " w8" : " wb"))
                           : " NONE (a crossing)", S->e);
  }

  printf("\n---- the audit sample ----\n");
  printf("  the landmark sentence read greedily against the same sentence with its\n"
         "  existentials searched literally: %ld samples, %ld disagreements\n",
         bruteSamples, bruteBad);
  printf("  every predicate of this census is evaluated by its own definition:\n"
         "    IsCrookedIvF, LowAt, Leg4Land (greedy and literal), HighRunG/HighRunT,\n"
         "    Valley3BeforeNine, and FoldsOnto by the dynamic program of\n"
         "    HPC/Fold/Decide.lean.  No criterion of the engine is used.\n");
  printf("  this is a census over whole pairs and whole arms, so no arm-length bound\n"
         "  applies: the arms seen at a high-run crossing run from %ld to %ld times.\n",
         armMin, armMax);
  return 0;
}
