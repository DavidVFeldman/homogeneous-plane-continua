/* Census for batch 44 (b) -- what walk serves a pair of the open branch.
 *
 * WHAT THIS RANGES OVER.  Actual faithful crooked sequences in the thin form
 * sigma = rho, verified pair by pair against `IsCrookedIvF` by the same routine
 * `crookedThin` as census-batch43.c (run first on paths whose status is known).
 * The thin form is a subclass of the faithful model.
 *
 * WHAT IS TESTED.  Nothing here uses a criterion or an announcement: a pair is
 * served by a walk when BOTH arms fold onto it, and folding is decided exactly,
 * by the dynamic program over the definition `FoldsOnto` of
 * HPC/Fold/Itinerary.lean -- a time assignment beta with beta 0 = 0, steps of
 * at most one, and every level within one of its time's center.  So the answer
 * is the truth about the walk, not about any sufficient condition for it.
 *
 * THE WALKS.  Every walk of at most `maxLegs` monotone legs whose start is
 * within one of the basepoint level and whose turning levels lie in the band
 * [L, L+9].  The canonical three are among them:
 *    Lambda   3 4 5 6 7 8 7 6 5 4 3 2 1     (lamCenter, based at L+3)
 *    V        5 4 3 2 1 2 3 4 5 6 7 8       (veeCenter, based at L+5)
 *    four-leg 3 4 5 6 5 4 3 2 1 2 3 4 5 6 7 8 7 6 5 4 3 2 1   (L+3, L+6, L+1, L+8)
 *
 * WHAT IS ASKED.  For every basepoint of the open branch of `bing 0 9` and of
 * its windows of span nine: is the pair served by the Lambda-walk, by the
 * V-walk, by the four-leg walk of batch 43, by any walk at all of at most
 * `maxLegs` legs?  A pair served by no walk of the class is printed in full.
 *
 * Usage: census-batch44b [maxLegs] [maxWindows]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

#define MAXLEV 64
#define MAXN   40001

static int nxtTab[MAXLEV][MAXN];

static int crookedThin(const int *v, int n) {
  int lo = v[0], hi = v[0];
  for (int j = 0; j < n; j++) { if (v[j] < lo) lo = v[j]; if (v[j] > hi) hi = v[j]; }
  int nlev = hi - lo + 1;
  if (nlev > MAXLEV || n >= MAXN) return 0;
  for (int j = 0; j + 1 < n; j++) { int d = v[j+1] - v[j]; if (d > 1 || d < -1) return 0; }
  for (int l = 0; l < nlev; l++) nxtTab[l][n] = n;
  for (int j = n - 1; j >= 0; j--)
    for (int l = 0; l < nlev; l++)
      nxtTab[l][j] = (v[j] - lo == l) ? j : nxtTab[l][j + 1];
  for (int s = 0; s < n; s++) {
    int hs[3], nh = 0;
    for (int e = -1; e <= 1; e++) {
      int u = s + e; if (u < 0 || u >= n) continue;
      int seen = 0;
      for (int q = 0; q < nh; q++) if (hs[q] == v[u]) seen = 1;
      if (!seen) hs[nh++] = v[u];
    }
    for (int t = s + 1; t < n; t++) {
      int ks[3], nk = 0;
      for (int e = -1; e <= 1; e++) {
        int u = t + e; if (u < 0 || u >= n) continue;
        int seen = 0;
        for (int q = 0; q < nk; q++) if (ks[q] == v[u]) seen = 1;
        if (!seen) ks[nk++] = v[u];
      }
      for (int a = 0; a < nh; a++) for (int b = 0; b < nk; b++) {
        int h = hs[a], k = ks[b];
        int diff = h - k; if (diff < 0) diff = -diff;
        if (diff < 3) continue;
        int r1, r2;
        if (h < k) { r1 = k - 1; r2 = h + 1; } else { r1 = k + 1; r2 = h - 1; }
        if (r1 - lo < 0 || r1 - lo >= nlev || r2 - lo < 0 || r2 - lo >= nlev) return 0;
        int p1 = nxtTab[r1 - lo][s + 1];
        if (p1 >= t) return 0;
        int p2 = nxtTab[r2 - lo][p1 + 1];
        if (p2 >= t) return 0;
      }
    }
  }
  return 1;
}

/* ------------------------------------------------------ the fold, exactly */

#define MAXW 80

/* Does the arm f (length m, levels as offsets from L) fold onto the walk w
   (length wl)?  Exactly the definition FoldsOnto: beta 0 = 0, |beta step| <= 1,
   |f j - w (beta j)| <= 1.  Dynamic program over the reachable set of beta. */
static int folds(const int *f, int m, const int *w, int wl) {
  static char cur[MAXW], nxt[MAXW];
  if (wl <= 0) return 0;
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

/* ------------------------------------------------------- the walk family */

#define MAXWALKS 300000
static int walks[MAXWALKS][MAXW];
static int walkLen[MAXWALKS];
static int walkTurns[MAXWALKS];
static int nWalks = 0;

static void emit(const int *pts, int npts) {
  /* pts[0..npts-1] are the turning levels, starting with the start level */
  int w[MAXW], wl = 0;
  w[wl++] = pts[0];
  for (int q = 1; q < npts; q++) {
    int s = pts[q] > pts[q-1] ? 1 : -1;
    for (int v = pts[q-1] + s; ; v += s) {
      if (wl >= MAXW) return;
      w[wl++] = v;
      if (v == pts[q]) break;
    }
  }
  if (nWalks >= MAXWALKS) return;
  memcpy(walks[nWalks], w, sizeof(int) * wl);
  walkLen[nWalks] = wl;
  walkTurns[nWalks] = npts - 2 < 0 ? 0 : npts - 2;
  nWalks++;
}

static void genRec(int *pts, int npts, int maxLegs) {
  if (npts >= 2) emit(pts, npts);
  if (npts - 1 >= maxLegs) return;
  int last = pts[npts-1];
  int dirUp;               /* the next leg must reverse the previous one */
  if (npts == 1) {
    for (int t = 0; t <= 9; t++) {
      if (t == last) continue;
      pts[npts] = t;
      genRec(pts, npts + 1, maxLegs);
    }
    return;
  }
  dirUp = (pts[npts-1] > pts[npts-2]) ? 0 : 1;   /* reverse */
  for (int t = 0; t <= 9; t++) {
    if (dirUp && t <= last) continue;
    if (!dirUp && t >= last) continue;
    pts[npts] = t;
    genRec(pts, npts + 1, maxLegs);
  }
}

/* ----------------------------------------------------------- the branch */

static int armBufG[MAXN], armBufT[MAXN];

static int highAt(const int *f, int m) {          /* HighAt f (L+1) (L+8) */
  int sawLe2 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !sawLe2) return 0;
    if (f[d] <= 2) sawLe2 = 1;
  }
  return 1;
}
static int lowAt(const int *f, int m) {           /* LowAt f (L+1) (L+8), one-clause read */
  int sawGe7 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= 1 && !sawGe7) return 0;
    if (f[d] >= 7) sawGe7 = 1;
  }
  return 1;
}
static int lamAnn(const int *f, int m) {
  int sawGe7 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= 1 && !sawGe7) return 0;
    if (f[d] >= 7) sawGe7 = 1;
  }
  return 1;
}
static int veeAnn(const int *f, int m) {
  int sawLe1 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 7 && !sawLe1) return 0;
    if (f[d] <= 1) sawLe1 = 1;
  }
  return 1;
}

static const int wLam[13] = {3,4,5,6,7,8,7,6,5,4,3,2,1};
static const int wVee[12] = {5,4,3,2,1,2,3,4,5,6,7,8};
static const int w4[23]   = {3,4,5,6,5,4,3,2,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1};
/* the walks the four-leg engine of HPC/Fold/Leg4.lean can actually produce at
   P = L+4: its hypotheses force the valley M = P-2 = L+2, and then K = L+6, L+7
   or L+8 (H = L+9).  leg4Walk L H K M P = P-1 up to K, down to M, up to H-1,
   down to L+1. */
static const int wE6[21] = {3,4,5,6,5,4,3,2,3,4,5,6,7,8,7,6,5,4,3,2,1};
static const int wE7[23] = {3,4,5,6,7,6,5,4,3,2,3,4,5,6,7,8,7,6,5,4,3,2,1};
static const int wE8[25] = {3,4,5,6,7,8,7,6,5,4,3,2,3,4,5,6,7,8,7,6,5,4,3,2,1};
/* the walks the two profile engines can produce at this basepoint: the Lambda-walk
   and the V-walk based at L+3, L+4, L+5 (peak L+8, valley L+1). */
static const int wL3[13] = {3,4,5,6,7,8,7,6,5,4,3,2,1};
static const int wL4[12] = {4,5,6,7,8,7,6,5,4,3,2,1};
static const int wL5[11] = {5,6,7,8,7,6,5,4,3,2,1};
static const int wV3[10] = {3,2,1,2,3,4,5,6,7,8};
static const int wV4[11] = {4,3,2,1,2,3,4,5,6,7,8};
static const int wV5[12] = {5,4,3,2,1,2,3,4,5,6,7,8};

static long long nBranch = 0, nMixed = 0;
static long long servedLam = 0, servedVee = 0, served4 = 0;
static long long servedNone3 = 0, unservedAny = 0;
static long long mixServed4 = 0, mixUnserved4 = 0;
static long long missedPairs = 0, missedE6 = 0, missedE7 = 0, missedE8 = 0, missed4 = 0;
static long long engineServed = 0, engineMissed = 0;
static int minFirstLowMissed = 1<<30, minFirstHighMissed = 1<<30;
static long long missedLamValley = 0, missedArms = 0, missedCeil7 = 0;
static long long missedValley7 = 0, missedCeil6 = 0, missedReach8 = 0, missedReach9 = 0;
static long long cW[9] = {0,0,0,0,0,0,0,0,0};
static long long allArms = 0, allHigh8 = 0, allValley = 0;
static long long mixPairs2 = 0, mixLamHigh8Fail = 0, mixVeeValleyFail = 0;
static long long mixUnservedAny = 0;
static int printed = 0;

/* which walks serve every mixed pair: an intersection, maintained as a mask */
static char *mixMask = 0;
static long long mixMaskPairs = 0;
static char *allMask = 0;
static long long allMaskPairs = 0;

static void doBranchPair(const int *f, int mg, const int *g, int mt, int mixed, int maxLegs) {
  nBranch++;
  if (mixed) {
    mixPairs2++;
    for (int sarm = 0; sarm < 2; sarm++) {
      const int *a = sarm ? g : f; int ma = sarm ? mt : mg;
      int lam = 1, sawGe7x = 0;
      for (int d = 0; d < ma; d++) {
        if (a[d] <= 1 && !sawGe7x) { lam = 0; break; }
        if (a[d] >= 7) sawGe7x = 1;
      }
      if (lam) {
        int sawLe1 = 0, ok = 1;
        for (int d = 0; d < ma; d++) {
          if (a[d] >= 8 && !sawLe1) { ok = 0; break; }
          if (a[d] <= 1) sawLe1 = 1;
        }
        if (!ok) mixLamHigh8Fail++;
      } else {
        int sawGe6 = 0, sawLe1 = 0, pat = 0, ok = 1;
        for (int d = 0; d < ma; d++) {
          if (a[d] <= 1 && !(sawGe6 || pat)) { ok = 0; break; }
          if (sawLe1 && a[d] >= 5) pat = 1;
          if (a[d] >= 6) sawGe6 = 1;
          if (a[d] <= 1) sawLe1 = 1;
        }
        if (!ok) mixVeeValleyFail++;
      }
    }
  }

  int sL = folds(f, mg, wLam, 13) && folds(g, mt, wLam, 13);
  int sV = folds(f, mg, wVee, 12) && folds(g, mt, wVee, 12);
  int s4 = folds(f, mg, w4, 23) && folds(g, mt, w4, 23);
  /* over EVERY branch arm: the two conditions the third walk needs */
  for (int sarm = 0; sarm < 2; sarm++) {
    const int *a = sarm ? g : f; int ma = sarm ? mt : mg;
    allArms++;
    { int sawLe1 = 0, ok = 1;
      for (int d = 0; d < ma; d++) {
        if (a[d] >= 8 && !sawLe1) { ok = 0; break; }
        if (a[d] <= 1) sawLe1 = 1;
      }
      if (ok) allHigh8++; }
    { int sawGe6 = 0, sawLe1 = 0, pat = 0, ok = 1;
      for (int d = 0; d < ma; d++) {
        if (a[d] <= 1 && !(sawGe6 || pat)) { ok = 0; break; }
        if (sawLe1 && a[d] >= 5) pat = 1;
        if (a[d] >= 6) sawGe6 = 1;
        if (a[d] <= 1) sawLe1 = 1;
      }
      if (ok) allValley++; }
  }
  /* and, on a mixed pair, the two clauses of the work items of HPC/Fold/Mixed.lean */
  if (mixed) {
    mixPairs2++;
    for (int sarm = 0; sarm < 2; sarm++) {
      const int *a = sarm ? g : f; int ma = sarm ? mt : mg;
      int lam = 1, sawGe7x = 0;
      for (int d = 0; d < ma; d++) {
        if (a[d] <= 1 && !sawGe7x) { lam = 0; break; }
        if (a[d] >= 7) sawGe7x = 1;
      }
      if (lam) {
        int sawLe1 = 0, ok = 1;
        for (int d = 0; d < ma; d++) {
          if (a[d] >= 8 && !sawLe1) { ok = 0; break; }
          if (a[d] <= 1) sawLe1 = 1;
        }
        if (!ok) mixLamHigh8Fail++;
      } else {
        int sawGe6 = 0, sawLe1 = 0, pat = 0, ok = 1;
        for (int d = 0; d < ma; d++) {
          if (a[d] <= 1 && !(sawGe6 || pat)) { ok = 0; break; }
          if (sawLe1 && a[d] >= 5) pat = 1;
          if (a[d] >= 6) sawGe6 = 1;
          if (a[d] <= 1) sawLe1 = 1;
        }
        if (!ok) mixVeeValleyFail++;
      }
    }
  }
  { const int *ws[9] = {wL3, wL4, wL5, wV3, wV4, wV5, wE6, wE7, wE8};
    const int wls[9] = {13, 12, 11, 10, 11, 12, 21, 23, 25};
    int any = 0;
    for (int q = 0; q < 9; q++) {
      int ok = folds(f, mg, ws[q], wls[q]) && folds(g, mt, ws[q], wls[q]);
      if (ok) { cW[q]++; any = 1; }
    }
    if (any) engineServed++; else engineMissed++;
  }
  if (sL) servedLam++;
  if (sV) servedVee++;
  if (s4) served4++;
  if (mixed) {
    nMixed++;
    if (s4) mixServed4++; else mixUnserved4++;
  }
  if (!sL && !sV) {
    missedPairs++;
    for (int sarm = 0; sarm < 2; sarm++) {
      const int *a = sarm ? g : f; int ma = sarm ? mt : mg;
      int fl = 1<<30, fh = 1<<30;
      for (int d = 0; d < ma; d++) { if (a[d] <= 1) { fl = d; break; } }
      for (int d = 0; d < ma; d++) { if (a[d] >= 7) { fh = d; break; } }
      if (fl < minFirstLowMissed) minFirstLowMissed = fl;
      if (fh < minFirstHighMissed) minFirstHighMissed = fh;
      missedArms++;
      /* the valley announcement of foldsOnto_leg3_deep at K = L+6 */
      { int sawGe6 = 0, sawLe1 = 0, pat = 0, ok = 1;
        for (int d = 0; d < ma; d++) {
          if (a[d] <= 1 && !(sawGe6 || pat)) { ok = 0; break; }
          if (sawLe1 && a[d] >= 5) pat = 1;
          if (a[d] >= 6) sawGe6 = 1;
          if (a[d] <= 1) sawLe1 = 1;
        }
        if (ok) missedLamValley++; }
      /* the ceiling announcement of foldsOnto_leg3_deep at K = L+7 (ascents to L+9) */
      { int sawLe0 = 0, sawGe8 = 0, b2 = 0, sawLe1 = 0, mid = 0, b3 = 0, ok = 1;
        for (int d = 0; d < ma; d++) {
          if (a[d] >= 9 && !(sawLe0 || b2 || b3)) { ok = 0; break; }
          if (a[d] <= 0) sawLe0 = 1;
          if (sawGe8 && a[d] <= 2) b2 = 1;
          if (mid && a[d] <= 2) b3 = 1;
          if (sawLe1 && a[d] >= 7) mid = 1;
          if (a[d] >= 8) sawGe8 = 1;
          if (a[d] <= 1) sawLe1 = 1;
        }
        if (ok) missedCeil7++; }
      /* the valley announcement at K = L+7 */
      { int sawGe7 = 0, sawLe1 = 0, pat = 0, ok = 1;
        for (int d = 0; d < ma; d++) {
          if (a[d] <= 1 && !(sawGe7 || pat)) { ok = 0; break; }
          if (sawLe1 && a[d] >= 6) pat = 1;
          if (a[d] >= 7) sawGe7 = 1;
          if (a[d] <= 1) sawLe1 = 1;
        }
        if (ok) missedValley7++; }
      /* the ceiling announcement at K = L+6 (ascents to L+8) */
      { int sawLe0 = 0, sawGe7 = 0, b2 = 0, sawLe1 = 0, mid = 0, b3 = 0, ok = 1;
        for (int d = 0; d < ma; d++) {
          if (a[d] >= 8 && !(sawLe0 || b2 || b3)) { ok = 0; break; }
          if (a[d] <= 0) sawLe0 = 1;
          if (sawGe7 && a[d] <= 2) b2 = 1;
          if (mid && a[d] <= 2) b3 = 1;
          if (sawLe1 && a[d] >= 6) mid = 1;
          if (a[d] >= 7) sawGe7 = 1;
          if (a[d] <= 1) sawLe1 = 1;
        }
        if (ok) missedCeil6++; }
      { int r8 = 0, r9 = 0;
        for (int d = 0; d < ma; d++) { if (a[d] >= 8) r8 = 1; if (a[d] >= 9) r9 = 1; }
        missedReach8 += r8; missedReach9 += r9; }
    }
    if (s4) missed4++;
    if (folds(f, mg, wE6, 21) && folds(g, mt, wE6, 21)) missedE6++;
    if (folds(f, mg, wE7, 23) && folds(g, mt, wE7, 23)) missedE7++;
    if (folds(f, mg, wE8, 25) && folds(g, mt, wE8, 25)) missedE8++;
    /* intersect the set of serving walks over the pairs the two canonical walks miss */
    if (!mixMask) { mixMask = (char *)malloc(nWalks); memset(mixMask, 1, nWalks); }
    for (int q = 0; q < nWalks; q++)
      if (mixMask[q] &&
          !(folds(f, mg, walks[q], walkLen[q]) && folds(g, mt, walks[q], walkLen[q])))
        mixMask[q] = 0;
    mixMaskPairs++;
  }
  /* and over every branch pair, to see whether one walk serves the whole branch */
  if (!allMask) { allMask = (char *)malloc(nWalks); memset(allMask, 1, nWalks); }
  for (int q = 0; q < nWalks; q++)
    if (allMask[q] &&
        !(folds(f, mg, walks[q], walkLen[q]) && folds(g, mt, walks[q], walkLen[q])))
      allMask[q] = 0;
  allMaskPairs++;
  if (sL || sV || s4) return;
  servedNone3++;
  /* the full search */
  int found = -1;
  for (int q = 0; q < nWalks; q++) {
    if (folds(f, mg, walks[q], walkLen[q]) && folds(g, mt, walks[q], walkLen[q])) {
      found = q; break;
    }
  }
  if (found < 0) {
    unservedAny++;
    if (mixed) mixUnservedAny++;
    if (printed < 3) {
      printed++;
      printf("  *** PAIR SERVED BY NO WALK OF AT MOST %d LEGS (mixed=%d)\n", maxLegs, mixed);
      printf("      forward arm (%d):", mg);
      for (int d = 0; d < mg && d < 200; d++) printf("%d", f[d]);
      printf("\n      backward arm (%d):", mt);
      for (int d = 0; d < mt && d < 200; d++) printf("%d", g[d]);
      printf("\n");
    }
  } else if (printed < 6) {
    printed++;
    printf("  pair served by neither canonical walk; first serving walk (turns %d): ",
           walkTurns[found]);
    for (int u = 0; u < walkLen[found]; u++) printf("%d", walks[found][u]);
    printf("\n");
  }
  (void)mixed;
}

static void doWindow(const int *v, int n, int maxLegs) {
  int lo = v[0], hi = v[0];
  for (int j = 0; j < n; j++) { if (v[j] < lo) lo = v[j]; if (v[j] > hi) hi = v[j]; }
  if (hi - lo != 9) return;
  int L = lo;
  for (int i = 0; i < n; i++) {
    if (v[i] != L + 4) continue;
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armBufG[d] = v[i + d] - L;
    for (int d = 0; d < mt; d++) armBufT[d] = v[i - d] - L;
    if (!highAt(armBufG, mg) || !highAt(armBufT, mt)) continue;
    int lg = lamAnn(armBufG, mg), vg = veeAnn(armBufG, mg);
    int lt = lamAnn(armBufT, mt), vt = veeAnn(armBufT, mt);
    int mixed = ((lg && !vg) && (vt && !lt)) || ((vg && !lg) && (lt && !vt));
    doBranchPair(armBufG, mg, armBufT, mt, mixed, maxLegs);
  }
}

static int buf[MAXN];

/* families B and C: more actual crooked sequences, sampled */
static void scanPath(const int *v, int n, int stride, int maxLegs) {
  if (stride < 1) stride = 1;
  for (int a = 0; a < n; a += stride)
    for (int b = a + 1; b < n; b++) {
      int lo = v[a], hi = v[a];
      for (int j = a; j <= b; j++) { if (v[j] < lo) lo = v[j]; if (v[j] > hi) hi = v[j]; }
      if (hi - lo > 9) break;
      if (hi - lo < 9) continue;
      for (int j = a; j <= b; j++) buf[j - a] = v[j];
      doWindow(buf, b - a + 1, maxLegs);
      break;
    }
}

int main(int argc, char **argv) {
  int maxLegs = argc > 1 ? atoi(argv[1]) : 4;
  int maxWindows = argc > 2 ? atoi(argv[2]) : 200;

  { int pts[8]; pts[0] = 3; genRec(pts, 1, maxLegs);
    pts[0] = 4; genRec(pts, 1, maxLegs);
    pts[0] = 5; genRec(pts, 1, maxLegs); }
  printf("walks of at most %d legs, start within one of L+4: %d\n", maxLegs, nWalks);

  { Path p = bpath(0, 8); printf("check bing 0 8 (n=%d) crooked: %d\n", p.n, crookedThin(p.v, p.n));
    free(p.v); }
  { int mono[6] = {0,1,2,3,4,5}; printf("check monotone run crooked: %d\n", crookedThin(mono, 6)); }

  Path p = bpath(0, 9);
  printf("bing 0 9: n = %d, crooked = %d\n", p.n, crookedThin(p.v, p.n));
  doWindow(p.v, p.n, maxLegs);
  printf("after the whole chain: branch pairs %lld, mixed %lld\n", nBranch, nMixed);

  /* windows of bing 0 9 of span exactly nine */
  int done = 0;
  for (int a = 0; a < p.n && done < maxWindows; a++) {
    for (int b = a + 1; b < p.n; b++) {
      int lo = p.v[a], hi = p.v[a];
      for (int j = a; j <= b; j++) { if (p.v[j] < lo) lo = p.v[j]; if (p.v[j] > hi) hi = p.v[j]; }
      if (hi - lo > 9) break;
      if (hi - lo < 9) continue;
      for (int j = a; j <= b; j++) buf[j - a] = p.v[j];
      doWindow(buf, b - a + 1, maxLegs);
      done++;
      break;                       /* one window per start, the shortest of span nine */
    }
  }
  free(p.v);

  /* family B: bing a b with |a-b| >= 9 */
  for (int a = 0; a <= 12; a++) for (int b = 0; b <= 12; b++) {
    int d = a < b ? b - a : a - b;
    if (d < 9) continue;
    if (a == 0 && b == 9) continue;
    Path q = bpath(a, b);
    if (q.n >= MAXN || q.n > 4000) { free(q.v); continue; }
    if (crookedThin(q.v, q.n)) scanPath(q.v, q.n, q.n / 60 + 1, maxLegs);
    free(q.v);
  }
  /* family C: random concatenations of bing paths, kept when crooked */
  srand(4400u);
  { int used = 0;
    for (int r = 0; r < 40; r++) {
      int nt = 3 + rand() % 4;
      int t[8]; t[0] = rand() % 10;
      for (int qq = 1; qq <= nt; qq++) { do { t[qq] = rand() % 10; } while (t[qq] == t[qq-1]); }
      static int cat[MAXN]; int tot = 0;
      for (int qq = 0; qq < nt; qq++) {
        Path pp = bpath(t[qq], t[qq+1]);
        if (tot + pp.n >= MAXN || tot + pp.n > 6000) { free(pp.v); tot = 0; break; }
        if (tot == 0) { memcpy(cat, pp.v, sizeof(int) * pp.n); tot = pp.n; }
        else { memcpy(cat + tot, pp.v + 1, sizeof(int) * (pp.n - 1)); tot += pp.n - 1; }
        free(pp.v);
      }
      if (tot == 0) continue;
      if (!crookedThin(cat, tot)) continue;
      used++;
      scanPath(cat, tot, tot / 60 + 1, maxLegs);
    }
    printf("family C: %d concatenations crooked and used\n", used);
  }

  printf("\nbranch pairs (v = L+4, both arms HighAt (L+1) (L+8)): %lld, of them mixed %lld\n",
         nBranch, nMixed);
  printf("served by the Lambda-walk: %lld\n", servedLam);
  printf("served by the V-walk:      %lld\n", servedVee);
  printf("served by the four-leg walk L+3,L+6,L+1,L+8: %lld  (mixed: %lld served, %lld not)\n",
         served4, mixServed4, mixUnserved4);
  printf("served by none of the three: %lld\n", servedNone3);
  printf("pairs served by at least one walk of an engine already in the repository: %lld\n",
         engineServed);
  printf("pairs served by NO such walk: %lld\n", engineMissed);
  { const char *nm[9] = {"Lambda L+3","Lambda L+4","Lambda L+5","V L+3","V L+4","V L+5",
                         "Leg4 K=L+6","Leg4 K=L+7","Leg4 K=L+8"};
    for (int q = 0; q < 9; q++) printf("   %-12s %lld\n", nm[q], cW[q]); }
  printf("over EVERY branch arm (%lld): a time at L+1 before every ascent to L+8: %lld;"
         " descents to L+1 announced at K = L+6: %lld\n", allArms, allHigh8, allValley);
  printf("mixed pairs %lld: Lambda-only arms without a time at L+1 before some ascent to L+8:"
         " %lld; V-only arms failing the valley announcement: %lld\n",
         mixPairs2, mixLamHigh8Fail, mixVeeValleyFail);
  printf("over the arms of pairs missed by both canonical walks (%lld arms):\n", missedArms);
  printf("   least step at which an arm stands at L+1 or below: %d\n", minFirstLowMissed);
  printf("   least step at which an arm stands at L+7 or above: %d\n", minFirstHighMissed);
  printf("   arms announcing every descent to L+1 (K = L+6): %lld\n", missedLamValley);
  printf("   arms announcing every ascent to L+9 (K = L+7):  %lld\n", missedCeil7);
  printf("   arms announcing every descent to L+1 (K = L+7): %lld\n", missedValley7);
  printf("   arms announcing every ascent to L+8 (K = L+6):  %lld\n", missedCeil6);
  printf("   arms reaching L+8: %lld; reaching L+9: %lld\n", missedReach8, missedReach9);
  printf("pairs missed by both canonical walks: %lld; of them served by\n", missedPairs);
  printf("   L+3,L+6,L+1,L+8 (valley at the floor):   %lld\n", missed4);
  printf("   L+3,L+6,L+2,L+8 (the Leg4 engine, K=L+6): %lld\n", missedE6);
  printf("   L+3,L+7,L+2,L+8 (the Leg4 engine, K=L+7): %lld\n", missedE7);
  printf("   L+3,L+8,L+2,L+8 (the Leg4 engine, K=L+8): %lld\n", missedE8);
  printf("served by NO walk of at most %d legs: %lld (mixed: %lld)\n",
         maxLegs, unservedAny, mixUnservedAny);
  if (allMask) {
    int cnt = 0;
    for (int q = 0; q < nWalks; q++) if (allMask[q]) cnt++;
    printf("walks serving ALL %lld branch pairs met: %d\n", allMaskPairs, cnt);
    int shown = 0;
    for (int q = 0; q < nWalks && shown < 10; q++) if (allMask[q]) {
      printf("   turns %d: ", walkTurns[q]);
      for (int u = 0; u < walkLen[q]; u++) printf("%d", walks[q][u]);
      printf("\n");
      shown++;
    }
  }
  if (mixMask) {
    int cnt = 0;
    for (int q = 0; q < nWalks; q++) if (mixMask[q]) cnt++;
    printf("walks serving ALL %lld pairs missed by both canonical walks: %d\n", mixMaskPairs, cnt);
    int shown = 0;
    for (int q = 0; q < nWalks && shown < 10; q++) if (mixMask[q]) {
      printf("   turns %d: ", walkTurns[q]);
      for (int u = 0; u < walkLen[q]; u++) printf("%d", walks[q][u]);
      printf("\n");
      shown++;
    }
  }
  return 0;
}
