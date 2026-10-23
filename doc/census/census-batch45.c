/* Census for batch 45 -- the two work items of HPC/Fold/Mixed.lean, and the
 * cross-arm statements they reduce to.
 *
 * WHAT THIS RANGES OVER.  Actual faithful crooked sequences in the thin form
 * sigma = rho, each verified against `IsCrookedIvF` by the routine
 * `crookedThin` of census-batch43.c (run first on paths whose status is known).
 * The thin form is a subclass of the faithful model; nothing here ranges over a
 * one-arm class.
 *
 * WHAT IS TESTED.  Folding is decided exactly, by the dynamic program over the
 * definition `FoldsOnto`: no criterion and no announcement stands in for it.
 * For every basepoint of the open branch (v[i] = L+4, both arms
 * HighAt (L+1) (L+8)):
 *
 *   W1  unserved_high8 : if the pair folds onto neither canonical walk, does
 *       every arm have a time at L+1 or below before each of its ascents to
 *       L+8?
 *   W2  unserved_valley : if the pair folds onto neither canonical walk, does
 *       every arm announce its descents to L+1 (a time at L+6 or above before,
 *       or a time at L+1 or below followed by one at L+5 or above)?
 *
 *   CH  the cross statement behind W1: if ONE arm has an ascent to L+8 with no
 *       earlier time at L+1 or below, does the OTHER arm fold onto the
 *       Lambda-walk?
 *   CV  the cross statement behind W2: if ONE arm has a descent to L+1 with no
 *       earlier time at L+6 or above, does the OTHER arm fold onto the V-walk?
 *
 *   CH' , CV' : the same two, with the conclusion read as an announcement
 *       (LamAnn, VeeAnn) rather than as a fold.
 *
 * Usage: census-batch45 [maxWindows] [nRandom] [seed]
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

/* ------------------------------------------------- announcements on an arm */

static int highAt1(const int *f, int m) {          /* HighAt f (L+1) (L+8) */
  int sawLe2 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !sawLe2) return 0;
    if (f[d] <= 2) sawLe2 = 1;
  }
  return 1;
}
static int high8(const int *f, int m) {            /* HighAt f L (L+8) */
  int sawLe1 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !sawLe1) return 0;
    if (f[d] <= 1) sawLe1 = 1;
  }
  return 1;
}
static int valleyAnn(const int *f, int m) {        /* the valley announcement, K = L+6 */
  int sawGe6 = 0, sawLe1 = 0, pat = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= 1 && !(sawGe6 || pat)) return 0;
    if (sawLe1 && f[d] >= 5) pat = 1;
    if (f[d] >= 6) sawGe6 = 1;
    if (f[d] <= 1) sawLe1 = 1;
  }
  return 1;
}
/* the ceiling announcement the three-leg engine asks for at K = L+6: before an
   ascent to L+8 there is a time at L or below, or a time at L+7 or above
   followed by one at L+2 or below, or a time at L+1 or below followed by one at
   L+6 or above and then one at L+2 or below. */
static int ceilAnn(const int *f, int m) {
  int sawLe0 = 0, sawGe7 = 0, b2 = 0, sawLe1 = 0, mid = 0, b3 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !(sawLe0 || b2 || b3)) return 0;
    if (f[d] <= 0) sawLe0 = 1;
    if (sawGe7 && f[d] <= 2) b2 = 1;
    if (mid && f[d] <= 2) b3 = 1;
    if (sawLe1 && f[d] >= 6) mid = 1;
    if (f[d] >= 7) sawGe7 = 1;
    if (f[d] <= 1) sawLe1 = 1;
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

static int armBufG[MAXN], armBufT[MAXN];

static long long nBranch = 0;
static long long nUnserved = 0, w1Fail = 0, w2Fail = 0;
static long long chCases = 0, chFail = 0, chFailAnn = 0;
static long long cvCases = 0, cvFail = 0, cvFailAnn = 0;
static long long selfHigh8Fail = 0, selfValleyFail = 0;
static long long w1cFail = 0;
static long long ccCases = 0, ccFail = 0, ccSelfFail = 0;
static long long ccMinBefore[12], ccMaxBefore[12], ccOtherMax[12];
static long long ccNoLe2 = 0;
static int printed = 0;

static void report(const char *tag, const int *f, int mg, const int *g, int mt) {
  if (printed >= 8) return;
  printed++;
  printf("  *** %s\n      forward arm (%d):", tag, mg);
  for (int d = 0; d < mg && d < 240; d++) printf("%d", f[d]);
  printf("\n      backward arm (%d):", mt);
  for (int d = 0; d < mt && d < 240; d++) printf("%d", g[d]);
  printf("\n");
}

static void doBranchPair(const int *f, int mg, const int *g, int mt) {
  nBranch++;
  int fLamG = folds(f, mg, wLam, 13), fLamT = folds(g, mt, wLam, 13);
  int fVeeG = folds(f, mg, wVee, 12), fVeeT = folds(g, mt, wVee, 12);
  int h8G = high8(f, mg), h8T = high8(g, mt);
  int vaG = valleyAnn(f, mg), vaT = valleyAnn(g, mt);

  /* W1, W2 : the two work items, conditioned exactly as in Mixed.lean */
  if (!(fLamG && fLamT) && !(fVeeG && fVeeT)) {
    nUnserved++;
    if (!(h8G && h8T)) { w1Fail++; report("W1 (unserved_high8) FAILS", f, mg, g, mt); }
    if (!(vaG && vaT)) { w2Fail++; report("W2 (unserved_valley) FAILS", f, mg, g, mt); }
    if (!(ceilAnn(f, mg) && ceilAnn(g, mt))) {
      w1cFail++; report("W1' (unserved ceiling announcement) FAILS", f, mg, g, mt);
    }
  }

  /* CC : one arm fails the ceiling announcement ==> the other folds onto Lambda? */
  for (int s = 0; s < 2; s++) {
    const int *a = s ? g : f;   int ma = s ? mt : mg;
    const int *b = s ? f : g;   int mb = s ? mg : mt;
    int fLamb = s ? fLamG : fLamT;
    if (!ceilAnn(a, ma)) {
      ccCases++;
      if (!(s ? fLamT : fLamG)) ccSelfFail++;
      if (!fLamb) ccFail++;
      /* the first index at which the ceiling announcement fails */
      { int sawLe0 = 0, sawGe7 = 0, b2 = 0, sawLe1 = 0, mid = 0, b3 = 0, d0 = -1;
        for (int d = 0; d < ma; d++) {
          if (a[d] >= 8 && !(sawLe0 || b2 || b3)) { d0 = d; break; }
          if (a[d] <= 0) sawLe0 = 1;
          if (sawGe7 && a[d] <= 2) b2 = 1;
          if (mid && a[d] <= 2) b3 = 1;
          if (sawLe1 && a[d] >= 6) mid = 1;
          if (a[d] >= 7) sawGe7 = 1;
          if (a[d] <= 1) sawLe1 = 1;
        }
        if (d0 > 0) {
          int mn = 99, mx = -99;
          for (int d = 0; d < d0; d++) { if (a[d] < mn) mn = a[d]; if (a[d] > mx) mx = a[d]; }
          if (mn >= 0 && mn < 12) ccMinBefore[mn]++;
          if (mx >= 0 && mx < 12) ccMaxBefore[mx]++;
          if (mn >= 3) ccNoLe2++;
        }
        /* the other arm: the greatest level before its first descent to L+1 */
        { int fl = -1;
          for (int d = 0; d < mb; d++) if (b[d] <= 1) { fl = d; break; }
          if (fl > 0) {
            int mx = -99;
            for (int d = 0; d < fl; d++) if (b[d] > mx) mx = b[d];
            if (mx >= 0 && mx < 12) ccOtherMax[mx]++;
          } else if (fl < 0) ccOtherMax[11]++;   /* never descends */
        }
      }
    }
  }

  /* CH : one arm fails HighAt L (L+8)  ==>  the other folds onto the Lambda-walk */
  for (int s = 0; s < 2; s++) {
    const int *a = s ? g : f;   int ma = s ? mt : mg;
    const int *b = s ? f : g;   int mb = s ? mg : mt;
    int h8a = s ? h8T : h8G;
    int fLamb = s ? fLamG : fLamT;
    if (!h8a) {
      chCases++;
      if (!(s ? fLamT : fLamG)) selfHigh8Fail++;   /* the failing arm itself */
      if (!fLamb) { chFail++; report("CH FAILS (other arm does not fold Lambda)", f, mg, g, mt); }
      if (!lamAnn(b, mb)) chFailAnn++;
    }
    (void)a; (void)ma;
  }

  /* CV : one arm fails the valley announcement ==> the other folds onto the V-walk */
  for (int s = 0; s < 2; s++) {
    const int *b = s ? f : g;   int mb = s ? mg : mt;
    int vaa = s ? vaT : vaG;
    int fVeeb = s ? fVeeG : fVeeT;
    if (!vaa) {
      cvCases++;
      if (!(s ? fVeeT : fVeeG)) selfValleyFail++;  /* the failing arm itself */
      if (!fVeeb) { cvFail++; report("CV FAILS (other arm does not fold V)", f, mg, g, mt); }
      if (!veeAnn(b, mb)) cvFailAnn++;
    }
  }
}

static void doWindow(const int *v, int n) {
  int lo = v[0], hi = v[0];
  for (int j = 0; j < n; j++) { if (v[j] < lo) lo = v[j]; if (v[j] > hi) hi = v[j]; }
  if (hi - lo != 9) return;
  int L = lo;
  for (int i = 0; i < n; i++) {
    if (v[i] != L + 4) continue;
    int mg = n - i, mt = i + 1;
    if (mg >= MAXN || mt >= MAXN) continue;
    for (int d = 0; d < mg; d++) armBufG[d] = v[i + d] - L;
    for (int d = 0; d < mt; d++) armBufT[d] = v[i - d] - L;
    if (!highAt1(armBufG, mg) || !highAt1(armBufT, mt)) continue;
    doBranchPair(armBufG, mg, armBufT, mt);
  }
}

static int buf[MAXN];

static void scanPath(const int *v, int n, int stride) {
  if (stride < 1) stride = 1;
  for (int a = 0; a < n; a += stride)
    for (int b = a + 1; b < n; b++) {
      int lo = v[a], hi = v[a];
      for (int j = a; j <= b; j++) { if (v[j] < lo) lo = v[j]; if (v[j] > hi) hi = v[j]; }
      if (hi - lo > 9) break;
      if (hi - lo < 9) continue;
      for (int j = a; j <= b; j++) buf[j - a] = v[j];
      doWindow(buf, b - a + 1);
      break;
    }
}

int main(int argc, char **argv) {
  int maxWindows = argc > 1 ? atoi(argv[1]) : 400;
  int nRandom = argc > 2 ? atoi(argv[2]) : 60;
  unsigned seed = argc > 3 ? (unsigned)atoi(argv[3]) : 4500u;

  { Path p = bpath(0, 8); printf("check bing 0 8 (n=%d) crooked: %d\n", p.n, crookedThin(p.v, p.n));
    free(p.v); }
  { int mono[6] = {0,1,2,3,4,5}; printf("check monotone run crooked: %d\n", crookedThin(mono, 6)); }

  Path p = bpath(0, 9);
  printf("bing 0 9: n = %d, crooked = %d\n", p.n, crookedThin(p.v, p.n));
  doWindow(p.v, p.n);

  int done = 0;
  for (int a = 0; a < p.n && done < maxWindows; a++) {
    for (int b = a + 1; b < p.n; b++) {
      int lo = p.v[a], hi = p.v[a];
      for (int j = a; j <= b; j++) { if (p.v[j] < lo) lo = p.v[j]; if (p.v[j] > hi) hi = p.v[j]; }
      if (hi - lo > 9) break;
      if (hi - lo < 9) continue;
      for (int j = a; j <= b; j++) buf[j - a] = p.v[j];
      doWindow(buf, b - a + 1);
      done++;
      break;
    }
  }
  free(p.v);

  for (int a = 0; a <= 12; a++) for (int b = 0; b <= 12; b++) {
    int d = a < b ? b - a : a - b;
    if (d < 9) continue;
    if (a == 0 && b == 9) continue;
    Path q = bpath(a, b);
    if (q.n >= MAXN || q.n > 4000) { free(q.v); continue; }
    if (crookedThin(q.v, q.n)) scanPath(q.v, q.n, q.n / 60 + 1);
    free(q.v);
  }

  srand(seed);
  { int used = 0;
    for (int r = 0; r < nRandom; r++) {
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
      scanPath(cat, tot, tot / 60 + 1);
    }
    printf("family C: %d concatenations crooked and used\n", used);
  }

  printf("\nbranch pairs (v = L+4, both arms HighAt (L+1) (L+8)): %lld\n", nBranch);
  printf("pairs folding onto neither canonical walk: %lld\n", nUnserved);
  printf("  W1 unserved_high8  fails on: %lld\n", w1Fail);
  printf("  W2 unserved_valley fails on: %lld\n", w2Fail);
  printf("  W1' ceiling announcement fails on: %lld\n", w1cFail);
  printf("arms failing the ceiling announcement: %lld cases\n", ccCases);
  printf("  CC fails (other arm does not fold Lambda): %lld\n", ccFail);
  printf("  of the failing arms, not folding Lambda themselves: %lld\n", ccSelfFail);
  printf("  failing arms with no time at L+2 or below before the failure: %lld\n", ccNoLe2);
  printf("  least level before the failure   :");
  for (int q = 0; q < 12; q++) printf(" %d:%lld", q, ccMinBefore[q]);
  printf("\n  greatest level before the failure:");
  for (int q = 0; q < 12; q++) printf(" %d:%lld", q, ccMaxBefore[q]);
  printf("\n  other arm, greatest level before its first descent to L+1 (11 = never descends):");
  for (int q = 0; q < 12; q++) printf(" %d:%lld", q, ccOtherMax[q]);
  printf("\n");
  printf("arms failing HighAt L (L+8): %lld cases\n", chCases);
  printf("  CH  fails (other arm does not fold Lambda): %lld\n", chFail);
  printf("  CH' fails (other arm not LamAnn):           %lld\n", chFailAnn);
  printf("  of the failing arms, not folding Lambda themselves: %lld\n", selfHigh8Fail);
  printf("arms failing the valley announcement: %lld cases\n", cvCases);
  printf("  CV  fails (other arm does not fold V): %lld\n", cvFail);
  printf("  CV' fails (other arm not VeeAnn):      %lld\n", cvFailAnn);
  printf("  of the failing arms, not folding V themselves: %lld\n", selfValleyFail);
  return 0;
}
