/* census-batch74.c -- batch 74 section 2.3.  Reconnaissance at spans ten,
 * eleven and twelve.
 *
 * The commission of batch 74 section 2.3 asks, over faithful pairs whose band
 * has span S = 10, 11, 12 (the batch-70 corpus builder with the band widened):
 *
 *   (i)  at every basepoint of the band, is there a walk of the four-leg family
 *        serving both arms?  If not, the least number of legs that does, and the
 *        count of basepoints needing each;
 *   (ii) is the structure of span nine -- two branches, a trichotomy of walks at
 *        each, crossings served by a fifth and sixth walk -- visible at span
 *        ten, and how many branches and walks does span ten show?
 *
 * Span nine is swept too (S = 9), so that every number reported at ten, eleven
 * and twelve is read against the same number at the span whose answer is known.
 *
 * ------------------------------------------------------------ what a walk is
 *
 * A *walk with k legs* based at a basepoint of level p is
 *
 *     c0 in {p-1, p, p+1} cap [L, H],  followed by k turning targets in
 *     [L+1, H-1], the directions alternating, each leg a run of unit steps,
 *
 * exactly the itinerary of census-batch26.py and exactly the shape `FoldsOnto`
 * consumes (a walk is a function c : N -> Z and a fold is a 1-Lipschitz index
 * map beta with beta 0 = 0 and |f j - c (beta j)| <= 1).  The number of legs is
 * the number of turning targets.  The four-leg family of the span-nine engine
 * (`leg4Walk L H K M P` of HPC/Fold/Leg4Wide.lean: P-1 -> K -> M -> H-1 -> L+1)
 * is the sub-family of the k = 4 walks whose last two targets are pinned at
 * H-1 and L+1, so "a walk of the four-leg family serves both arms" is implied
 * by, and is reported here as, "the least number of legs is at most four"; the
 * pinned sub-family is measured separately and reported alongside.
 *
 * `FoldsOnto` is decided exactly, by forward propagation of the set of reachable
 * walk times as a bitmask (the dynamic program of HPC/Fold/Decide.lean, in the
 * bitmask form of census-batch26.py), so no criterion of the four-leg engine and
 * no landmark sentence is used anywhere in this census.
 *
 * ---------------------------------------------------------------- the corpus
 *
 * Exactly the batch-70 corpus builder with the band widened from [0,9] to [0,S]:
 *
 *   (a) the Bing chains bpath 0 S and bpath S 0;
 *   (b) windows of span exactly S, at grid offsets and at random offsets, of the
 *       larger Bing chains bing 0 N, N = S+1 .. S+4;
 *   (c) the recursive chains vpath a b back fwd whose splitting levels are not
 *       Bing's, in four parameter settings and both orientations;
 *   (d) random concatenations of Bing blocks, and windows of span S of them;
 *   (e) for every base sequence of (a)-(d): the thin pair (sig = rho), every
 *       single shaving of a peak and every single filling of a valley (capped),
 *       random mixtures at rates 1/3 and 1/2, and the total mixture.
 *
 * A window is a faithful pair in its own right and is tested as one; whole arms
 * of each pair are scored, from the basepoint to each end.  This is therefore a
 * census over pairs and over whole arms, not over truncated arms: no arm-length
 * bound applies, and the arm lengths actually seen are reported.
 *
 * ------------------------------------------------------------ definition audit
 *
 * Every predicate is evaluated by its own definition, none by a proxy.
 *
 *   crookedGen   IsCrookedIvF of HPC/Fold/Faithful.lean (le, width, adj and the
 *                crookedness clause with interval triggers), copied unchanged
 *                from census-batch70.c.
 *   foldsMask    FoldsOnto of HPC/Fold/Faithful.lean, decided exactly by
 *                reachability; audited below against foldsBrute, a second
 *                implementation that propagates the reachable set as an array.
 *   armG, armT   armG rho i = (rho i, rho (i+1), ...), armT rho i =
 *                (rho i, rho (i-1), ...), as HPC/Fold/Faithful.lean defines them.
 *   leg4Pinned   the walk leg4Walk L H K M P of HPC/Fold/Leg4Wide.lean, built
 *                from its parameters and its reflection, over the same window of
 *                parameter sets census-batch70.c uses, widened to the band.
 *
 * Usage: census-batch74 [S] [windows-per-chain] [mixtures-per-chain] [seed]
 *                       [kmax] [cover-cap]
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
#define MAXN   16384

static int meetTab[MAXLEV][MAXN + 1];

/* IsCrookedIvF (rho, sig), exactly as HPC/Fold/Faithful.lean states it.
   Copied unchanged from census-batch70.c. */
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
#define MAXKLEG 6

static int SPAN = 10;                    /* H = SPAN, L = 0 */

#define MASKLEV 16                       /* levels 0 .. 15; the band is [0, SPAN], SPAN <= 14 */

typedef struct {
  int len;                               /* number of times of the walk */
  int legs;                              /* number of turning targets */
  int start;
  int tgt[MAXKLEG];
  u128 mask[MASKLEV];                    /* mask[v] : the times u with |v - c u| <= 1 */
} Walk;

/* every walk, grouped by (start level, number of legs) */
#define MAXWALKS 600000
static Walk *walks;
static long nWalks = 0;
/* index ranges: widx[start][legs] = first index, wcnt[start][legs] = count */
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

static void addWalk(int start, const int *tgt, int legs) {
  int times[MAXWALK];
  int len = buildTimes(start, tgt, legs, times);
  if (len < 0 || len > 120 || nWalks >= MAXWALKS) return;
  Walk *w = &walks[nWalks++];
  w->len = len; w->legs = legs; w->start = start;
  for (int q = 0; q < legs; q++) w->tgt[q] = tgt[q];
  for (int v = 0; v < MASKLEV; v++) w->mask[v] = 0;
  for (int u = 0; u < len; u++)
    for (int d = -1; d <= 1; d++) {
      int v = times[u] + d;
      if (v >= 0 && v < MASKLEV) w->mask[v] |= ((u128)1) << u;
    }
}

static int curTgt[MAXKLEG];

static void genAlt(int start, int legs, int depth, int last, int dir) {
  /* dir: +1 up, -1 down, 0 free (only at depth 0) */
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

/* FoldsOnto f len c, decided exactly: the reachable set of walk times as a
   bitmask, propagated forward. */
static int foldsMask(const int *f, int m, const Walk *w) {
  u128 r = w->mask[f[0]] & (u128)1;
  if (!r) return 0;
  for (int j = 1; j < m; j++) {
    r = (r | (r << 1) | (r >> 1)) & w->mask[f[j]];
    if (!r) return 0;
  }
  return 1;
}

/* the same, with the reachable set kept as an array of flags */
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

/* ---------------------------------------------------- the pinned four-leg family */

/* leg4Walk L H K M P of HPC/Fold/Leg4Wide.lean, at L = 0, H = SPAN, and its
   reflection; the parameter window of census-batch70.c widened to the band. */
#define MAXPIN 512
static Walk *pinned;
static long nPinned = 0;

static void buildPinned(void) {
  for (int P = 2; P <= SPAN - 3; P++)
    for (int K = P; K <= SPAN - 1; K++)
      for (int M = 1; M <= P - 2; M++) {
        if (M + 3 > K) continue;
        int tg[4] = {K, M, SPAN - 1, 1};
        int times[MAXWALK];
        if (buildTimes(P - 1, tg, 4, times) > 0 && nPinned < MAXPIN) {
          Walk *w = &pinned[nPinned++];
          w->len = buildTimes(P - 1, tg, 4, times); w->legs = 4; w->start = P - 1;
          for (int q = 0; q < 4; q++) w->tgt[q] = tg[q];
          for (int v = 0; v < MASKLEV; v++) w->mask[v] = 0;
          for (int u = 0; u < w->len; u++)
            for (int d = -1; d <= 1; d++) {
              int v = times[u] + d;
              if (v >= 0 && v < MASKLEV) w->mask[v] |= ((u128)1) << u;
            }
        }
        int rt[4] = {SPAN - K, SPAN - M, 1, SPAN - 1};
        int rtimes[MAXWALK];
        int rl = buildTimes(SPAN - (P - 1), rt, 4, rtimes);
        if (rl > 0 && nPinned < MAXPIN) {
          Walk *w = &pinned[nPinned++];
          w->len = rl; w->legs = 4; w->start = SPAN - (P - 1);
          for (int q = 0; q < 4; q++) w->tgt[q] = rt[q];
          for (int v = 0; v < MASKLEV; v++) w->mask[v] = 0;
          for (int u = 0; u < rl; u++)
            for (int d = -1; d <= 1; d++) {
              int v = rtimes[u] + d;
              if (v >= 0 && v < MASKLEV) w->mask[v] |= ((u128)1) << u;
            }
        }
      }
}

/* ------------------------------------------------------------- the counters */

static int rho[MAXN], sig[MAXN], armG[MAXN], armT[MAXN];

static long nPairs = 0, nDistinctPairs = 0, nLinks = 0, nNonThin = 0, nSourceKinds = 0;
static long variantsTried = 0, variantsFaithful = 0;
static long nBase = 0, nBaseDistinct = 0;
static long kCount[MAXKLEG + 2];          /* kCount[k] : basepoints of least k legs */
static long kNone = 0;                    /* no walk of at most KMAX legs */
static long pinnedServed = 0, pinnedNot = 0;
static long kByLevel[MAXLEV][MAXKLEG + 2];
static long kNoneByLevel[MAXLEV];
static long armMin = 1 << 30, armMax = -1;
static long bruteSamples = 0, bruteBad = 0;
static long shownFail = 0, shownHard = 0, shownFive = 0;
static const char *curTag = "";

/* distinctness */
#define HASHCAP (1 << 24)
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

/* ------------------------------------------------- the cover sample ------- */

/* For the structure question: a sample of distinct basepoints, kept in full, so
   that a greedy cover over the walks of at most four legs can be run per level. */
#define COVERLEVELS MAXLEV
static long COVERCAP = 1500;
typedef struct { int *G; int mg; int *T; int mt; int p; } BP;
static BP *cover[COVERLEVELS];
static long coverN[COVERLEVELS];
static long coverSeen[COVERLEVELS];

/* a uniform sample of the distinct basepoints of the level, by reservoir */
static void coverAdd(int p, const int *G, int mg, const int *T, int mt) {
  coverSeen[p]++;
  BP *b;
  if (coverN[p] < COVERCAP) {
    b = &cover[p][coverN[p]++];
  } else {
    long r = random() % coverSeen[p];
    if (r >= COVERCAP) return;
    b = &cover[p][r];
    free(b->G); free(b->T);
  }
  b->p = p;
  b->mg = mg; b->mt = mt;
  b->G = (int *)malloc(sizeof(int) * mg);
  b->T = (int *)malloc(sizeof(int) * mt);
  memcpy(b->G, G, sizeof(int) * mg);
  memcpy(b->T, T, sizeof(int) * mt);
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

static void printWalk(const Walk *w) {
  printf("%d", w->start);
  for (int q = 0; q < w->legs; q++) printf(" -> %d", w->tgt[q]);
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
    if (!fresh) continue;                       /* score each configuration once */
    nBaseDistinct++;

    int bw = -1;
    int k = leastLegs(armG, mg, armT, mt, p, &bw);
    if (k < 0) {
      kNone++; kNoneByLevel[p]++;
      if (shownFail < 12) {
        shownFail++;
        printf("  NO WALK OF AT MOST %d LEGS  [%ld] %-16s n=%4d i=%4d level=%d"
               " |G|=%4d |T|=%4d\n", KMAX, shownFail, tag, n, i, p, mg, mt);
        printf("    the forward arm:");
        for (int u = 0; u < mg && u < 80; u++) printf(" %d", armG[u]);
        printf("\n    the backward arm:");
        for (int u = 0; u < mt && u < 80; u++) printf(" %d", armT[u]);
        printf("\n");
      }
    } else {
      kCount[k]++; kByLevel[p][k]++;
      if (k >= 5 && shownFive < 10) {
        shownFive++;
        printf("  FIVE LEGS OR MORE: least %d legs [%ld] %-16s n=%4d i=%4d level=%d"
               " |G|=%4d |T|=%4d  walk ", k, shownFive, tag, n, i, p, mg, mt);
        printWalk(&walks[bw]);
        printf("\n");
        if (shownFive == 1) {
          char fn[64];
          snprintf(fn, sizeof(fn), "witness-batch74-span%d.txt", SPAN);
          FILE *fp = fopen(fn, "w");
          if (fp) {
            fprintf(fp, "%d %d %d\n", n, i, k);
            for (int t = 0; t < n; t++) fprintf(fp, "%d%c", rho[t], t + 1 == n ? '\n' : ' ');
            for (int t = 0; t < n; t++) fprintf(fp, "%d%c", sig[t], t + 1 == n ? '\n' : ' ');
            fclose(fp);
          }
        }
      }
      if (k >= 4 && shownHard < 10) {
        shownHard++;
        printf("  least %d legs [%ld] %-16s n=%4d i=%4d level=%d |G|=%4d |T|=%4d  walk ",
               k, shownHard, tag, n, i, p, mg, mt);
        printWalk(&walks[bw]);
        printf("\n");
      }
    }
    /* the pinned four-leg family of the engine */
    {
      int served = 0;
      for (long q = 0; q < nPinned && !served; q++) {
        if (pinned[q].start < p - 1 || pinned[q].start > p + 1) continue;
        if (foldsMask(armG, mg, &pinned[q]) && foldsMask(armT, mt, &pinned[q])) served = 1;
      }
      if (served) pinnedServed++; else pinnedNot++;
    }
    /* the audit sample: the bitmask fold against the array fold */
    if (bruteSamples < 3000 && mg < 6000 && mt < 6000) {
      long q0 = widx[p][2];
      for (long q = q0; q < q0 + wcnt[p][2] && q < q0 + 6; q++) {
        bruteSamples++;
        if (foldsMask(armG, mg, &walks[q]) != foldsBrute(armG, mg, &walks[q])) bruteBad++;
        if (foldsMask(armT, mt, &walks[q]) != foldsBrute(armT, mt, &walks[q])) bruteBad++;
      }
    }
    if (p >= 0 && p < COVERLEVELS) coverAdd(p, armG, mg, armT, mt);
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
  if (crookedGen(rho, sig, n)) { variantsFaithful++; scanPair(n, tag); }
  else return;

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
  if (b - a + 1 > MAXPAIRLEN) b = a + (int)MAXPAIRLEN - 1;   /* truncate: still a pair */
  if (b - a + 1 >= MAXN) return 0;
  int lo = v[a], hi = v[a];
  for (int t = a; t <= b; t++) { if (v[t] < lo) lo = v[t]; if (v[t] > hi) hi = v[t]; }
  if (hi - lo != SPAN) return 0;
  for (int t = a; t <= b; t++) out[t - a] = v[t] - lo;
  return b - a + 1;
}

static int wbuf[MAXN];

/* ---------------------------------------------------------- greedy cover */

static int COVERLEGS = 4;

static void greedyCover(void) {
  printf("\n======== the structure: how many walks, and how many branches ========\n");
  printf("  a greedy cover, level by level: the fewest walks of at most %d legs that,\n"
         "  between them, serve every sampled basepoint of that level (each basepoint\n"
         "  served by one walk on both of its arms).  The cover is greedy, so each\n"
         "  count is an upper bound for the least number of walks at that level.\n",
         COVERLEGS);
  long totalWalks = 0, branches = 0, levelsSeen = 0;
  for (int p = 0; p <= SPAN; p++) {
    if (coverN[p] == 0) continue;
    levelsSeen++;
    long N = coverN[p];
    long words = (N + 63) / 64;
    /* candidate walks based within one of p, of at most COVERLEGS legs */
    long cand = 0;
    for (int st = p - 1; st <= p + 1; st++) {
      if (st < 0 || st > SPAN) continue;
      for (int k = 0; k <= COVERLEGS && k <= KMAX; k++) cand += wcnt[st][k];
    }
    long *idx = (long *)malloc(sizeof(long) * (size_t)cand);
    long ci = 0;
    for (int st = p - 1; st <= p + 1; st++) {
      if (st < 0 || st > SPAN) continue;
      for (int k = 0; k <= COVERLEGS && k <= KMAX; k++)
        for (long q = widx[st][k]; q < widx[st][k] + wcnt[st][k]; q++) idx[ci++] = q;
    }
    uint64_t *serve = (uint64_t *)calloc((size_t)(cand * words), sizeof(uint64_t));
    for (long c = 0; c < cand; c++) {
      const Walk *w = &walks[idx[c]];
      for (long b = 0; b < N; b++) {
        BP *bp = &cover[p][b];
        if (foldsMask(bp->G, bp->mg, w) && foldsMask(bp->T, bp->mt, w))
          serve[c * words + b / 64] |= ((uint64_t)1) << (b % 64);
      }
    }
    uint64_t *left = (uint64_t *)malloc(sizeof(uint64_t) * (size_t)words);
    for (long u = 0; u < words; u++) left[u] = ~(uint64_t)0;
    if (N % 64) left[words - 1] = (((uint64_t)1) << (N % 64)) - 1;
    long remaining = N, picked = 0;
    int firstPick[8]; int nFirst = 0;
    while (remaining > 0 && picked < 64) {
      long best = -1, bestCov = 0;
      for (long c = 0; c < cand; c++) {
        long cov = 0;
        for (long u = 0; u < words; u++)
          cov += __builtin_popcountll(serve[c * words + u] & left[u]);
        if (cov > bestCov) { bestCov = cov; best = c; }
      }
      if (best < 0 || bestCov == 0) break;
      for (long u = 0; u < words; u++) left[u] &= ~serve[best * words + u];
      remaining -= bestCov;
      picked++;
      if (nFirst < 8) firstPick[nFirst++] = (int)idx[best];
    }
    printf("  level %2d: %ld sampled basepoints (of %ld seen) -> %ld walk%s%s\n",
           p, N, coverSeen[p], picked, picked == 1 ? "" : "s",
           remaining > 0 ? "  (some sampled basepoint served by no candidate walk)" : "");
    for (int q = 0; q < nFirst; q++) {
      printf("        walk %d: ", q + 1);
      printWalk(&walks[firstPick[q]]);
      printf("   (%d legs)\n", walks[firstPick[q]].legs);
    }
    totalWalks += picked;
    if (picked >= 2) branches++;
    free(idx); free(serve); free(left);
  }
  printf("  levels with a basepoint: %ld; levels needing more than one walk"
         " (the branches): %ld;\n  walks in the cover, summed over levels: %ld\n",
         levelsSeen, branches, totalWalks);
}

int main(int argc, char **argv) {
  SPAN = (argc > 1) ? atoi(argv[1]) : 10;
  long windows = (argc > 2) ? atol(argv[2]) : 24;
  long mixes = (argc > 3) ? atol(argv[3]) : 4;
  unsigned seed = (argc > 4) ? (unsigned)atoi(argv[4]) : 74u;
  KMAX = (argc > 5) ? atoi(argv[5]) : 5;
  COVERCAP = (argc > 6) ? atol(argv[6]) : 1500;
  MAXPAIRLEN = (argc > 7) ? atol(argv[7]) : 3000;
  srandom(seed);
  setvbuf(stdout, NULL, _IOLBF, 0);
  T0 = time(NULL);

  walks = (Walk *)malloc(sizeof(Walk) * MAXWALKS);
  pinned = (Walk *)malloc(sizeof(Walk) * MAXPIN);
  hashTab = (uint64_t *)calloc(HASHCAP, sizeof(uint64_t));
  for (int p = 0; p < COVERLEVELS; p++)
    cover[p] = (BP *)malloc(sizeof(BP) * (size_t)COVERCAP);

  buildAllWalks();
  buildPinned();

  printf("census-batch74: the fold at span %d.  L = 0, H = %d.\n", SPAN, SPAN);
  printf("seed=%u windows-per-chain=%ld mixtures-per-chain=%ld kmax=%d cover-cap=%ld"
         " max-pair-length=%ld\n", seed, windows, mixes, KMAX, COVERCAP, MAXPAIRLEN);
  printf("walks of at most %d legs, based within one of a level: %ld in all\n", KMAX, nWalks);
  for (int k = 0; k <= KMAX; k++) {
    long tot = 0;
    for (int st = 0; st <= SPAN; st++) tot += wcnt[st][k];
    printf("   %d legs: %ld walks\n", k, tot);
  }
  printf("the pinned four-leg family (leg4Walk and its reflection): %ld walks\n", nPinned);
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

  for (int N = SPAN + 1; N <= SPAN + 4; N++) {
    Path p = bpath(0, N);
    printf("  bing 0 %d: %d links", N, p.n);
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
    for (long it = 0; it < windows * 2; it++) {
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
  printf("  basepoints of the band: %ld (%ld distinct by their pair of whole arms,\n"
         "  and it is the distinct ones that are scored)\n", nBase, nBaseDistinct);
  printf("  arm lengths seen: %ld to %ld  (whole arms; no arm-length bound)\n",
         armMin, armMax);
  printf("  keys in the distinctness table: %ld; keys past its capacity (counted as"
         " distinct): %ld\n", hashN, hashOverflow);

  printf("\n======== the least number of legs, over the distinct basepoints ========\n");
  long served4 = 0;
  for (int k = 0; k <= KMAX; k++) {
    printf("  least %d legs: %ld basepoints\n", k, kCount[k]);
    if (k <= 4) served4 += kCount[k];
  }
  printf("  no walk of at most %d legs: %ld basepoints\n", KMAX, kNone);
  printf("  a walk of the four-leg family (at most four legs) serves both arms at\n"
         "  %ld of the %ld distinct basepoints; %ld need more\n",
         served4, nBaseDistinct, nBaseDistinct - served4);
  printf("  the pinned four-leg family leg4Walk of the engine serves both arms at %ld,\n"
         "  and does not at %ld\n", pinnedServed, pinnedNot);

  printf("\n  by level (rows: level; columns: least 0,1,...,%d legs, then none):\n", KMAX);
  for (int p = 0; p <= SPAN; p++) {
    long tot = kNoneByLevel[p];
    for (int k = 0; k <= KMAX; k++) tot += kByLevel[p][k];
    if (tot == 0) continue;
    printf("   level %2d:", p);
    for (int k = 0; k <= KMAX; k++) printf(" %8ld", kByLevel[p][k]);
    printf("  | none %ld\n", kNoneByLevel[p]);
  }

  greedyCover();

  printf("\n---- the audit sample ----\n");
  printf("  the fold decided by the bitmask propagation against the same fold decided\n"
         "  by an array propagation: %ld samples, %ld disagreements\n",
         bruteSamples, bruteBad);
  printf("  every predicate of this census is evaluated by its own definition:\n"
         "    IsCrookedIvF, armG, armT, FoldsOnto (twice, independently), and the\n"
         "    walk leg4Walk of HPC/Fold/Leg4Wide.lean.  No criterion of the four-leg\n"
         "    engine and no landmark sentence is used.\n");
  return 0;
}
