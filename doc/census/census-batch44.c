/* Census for batch 44 -- the four-leg walk at span nine, and its announcements.
 *
 * WHAT THIS RANGES OVER.  Every sequence examined here is an *actual* faithful
 * crooked sequence in the thin form sigma = rho: it is checked, pair by pair,
 * against the definition `IsCrookedIvF` of HPC/Fold/Faithful.lean, exactly as
 * in census-batch43.c (the routine `crookedThin` is the same, and is run first
 * on paths whose status is known).  The thin form is a subclass of the faithful
 * model, so the pairs counted are actual and the class of all actual pairs is
 * larger (COMMISSION sec. 2.2).
 *
 * THE QUESTION.  Batch 43 found the mixed configuration inhabited and checked
 * that the four-leg walk L+3 -> L+6 -> L+1 -> L+8 serves every mixed pair met.
 * In the repository that walk is `leg4Walk L H K M P` with
 *     H = L+9,  K = L+6,  M = L+1,  P = L+4,
 * and the engine `foldsOnto_leg4` (HPC/Fold/Leg4.lean) folds an arm onto it as
 * soon as three announcements hold.  At these parameters the deep-floor
 * announcement is vacuous (it asks about levels below L) and the other two read
 *
 *   FLOOR    every time at L or below is preceded by a time at L+6 or above,
 *            or by two times, in order, at L+2 or below and at L+5 or above;
 *   CEILING  every time at L+8 or above is preceded by a time at L or below, or
 *            by two times, in order, at L+7 or above and at L+2 or below, or by
 *            three times, in order, at L+2 or below, at L+6 or above and at
 *            L+2 or below.
 *
 * This census asks whether those two announcements hold on the arms of the open
 * branch, and in particular on the mixed ones -- that is, whether the four-leg
 * engine as it stands can be driven by announcements, or whether an exact
 * criterion in the style of HPC/Fold/Profile.lean is needed.  It also records
 * the greedy fold onto the walk itself (`Val4`/`gstep4` of Leg4.lean, the same
 * recursion), so the two can be compared.
 *
 * ARM CLASSES (the two exact criteria, as in batch 43, in announcement form):
 *   lamAnn : before the arm ever drops to L+1 it stands at L+7.
 *            Sufficient for the Lambda-walk based at L+3, by
 *            `s3_span_nine_mid_low_of_lam` (HPC/Fold/Timing.lean).
 *   veeAnn : before the arm ever rises to L+7 it stands at L+1.
 *            Sufficient for the V-walk based at L+5, by
 *            `s3_span_nine_mid_low_of_floor` (HPC/Fold/Span9Profile.lean).
 * Every arm satisfies at least one of the two -- that is `arm_lam_or_vee` of
 * HPC/Fold/Mixed.lean, proved in this batch; the census records it as a check.
 * A pair is MIXED when one arm has only lamAnn and the other only veeAnn.
 *
 * Usage: census-batch44 [maxN] [nRandom] [seed]
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

/* ------------------------------------------------- exact crookedness test */

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

/* ------------------------------------------------------------- arm tests */

/* arm f of length m, band floor L; f[0] = L+4 assumed by the caller. */

static int highAt(const int *f, int m, int L) {      /* HighAt f (L+1) (L+8) */
  int sawLe2 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= L + 8 && !sawLe2) return 0;
    if (f[d] <= L + 2) sawLe2 = 1;
  }
  return 1;
}

static int lamAnn(const int *f, int m, int L) {      /* drop to L+1 preceded by L+7 */
  int sawGe7 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= L + 1 && !sawGe7) return 0;
    if (f[d] >= L + 7) sawGe7 = 1;
  }
  return 1;
}

static int veeAnn(const int *f, int m, int L) {      /* rise to L+7 preceded by L+1 */
  int sawLe1 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= L + 7 && !sawLe1) return 0;
    if (f[d] <= L + 1) sawLe1 = 1;
  }
  return 1;
}

/* the four-leg floor announcement at H=L+9, K=L+6, M=L+1, P=L+4 */
static int leg4Floor(const int *f, int m, int L, int *witness) {
  int A1 = 0;          /* seen level >= L+6            */
  int sawLe2 = 0;      /* seen level <= L+2            */
  int A2 = 0;          /* seen <= L+2 then >= L+5      */
  for (int d = 0; d < m; d++) {
    if (f[d] <= L && !(A1 || A2)) { if (witness) *witness = d; return 0; }
    if (f[d] >= L + 6) A1 = 1;
    if (sawLe2 && f[d] >= L + 5) A2 = 1;
    if (f[d] <= L + 2) sawLe2 = 1;
  }
  return 1;
}

/* the four-leg ceiling announcement at the same parameters */
static int leg4Ceil(const int *f, int m, int L, int *witness) {
  int B1 = 0;          /* seen <= L                             */
  int sawGe7 = 0;      /* seen >= L+7                           */
  int B2 = 0;          /* seen >= L+7 then <= L+2               */
  int sawLe2 = 0;      /* seen <= L+2                           */
  int mid = 0;         /* seen <= L+2 then >= L+6               */
  int B3 = 0;          /* seen <= L+2, >= L+6, <= L+2           */
  for (int d = 0; d < m; d++) {
    if (f[d] >= L + 8 && !(B1 || B2 || B3)) { if (witness) *witness = d; return 0; }
    if (f[d] <= L) B1 = 1;
    if (sawGe7 && f[d] <= L + 2) B2 = 1;
    if (mid && f[d] <= L + 2) B3 = 1;
    if (sawLe2 && f[d] >= L + 6) mid = 1;
    if (f[d] >= L + 7) sawGe7 = 1;
    if (f[d] <= L + 2) sawLe2 = 1;
  }
  return 1;
}

/* ------------------------------------------- the greedy fold onto leg4Walk */

/* Val4 L H K M P v u of HPC/Fold/Leg4.lean, specialised to
   H = L+9, K = L+6, M = L+1, P = L+4 (offsets from L; v is an offset too). */
static int val4(int v, int u) {
  if (0 <= u && u <= 3 && v - 4 <= u && u <= v - 2) return 1;
  if (3 <= u && u <= 8 && 8 - v <= u && u <= 10 - v) return 1;
  if (8 <= u && u <= 15 && v + 6 <= u && u <= v + 8) return 1;
  if (15 <= u && u <= 22 && 22 - v <= u && u <= 24 - v) return 1;
  return 0;
}

static int foldsLeg4(const int *f, int m, int L) {
  int q = 0;
  if (!val4(f[0] - L, 0)) return 0;
  for (int j = 1; j < m; j++) {
    int v = f[j] - L;
    if (val4(v, q + 1)) q = q + 1;
    else if (val4(v, q)) ;
    else q = q - 1;
    if (!val4(v, q)) return 0;
  }
  return 1;
}

/* ------------------------------------------------------------- the census */

static long long nWin = 0, nBranch = 0;
static long long cLam = 0, cVee = 0, cBoth = 0, cNeither = 0;
static long long cMixPair = 0, cLamPair = 0, cVeePair = 0;
static long long armFloorFail = 0, armCeilFail = 0, armFoldFail = 0;
static long long mixArmFloorFail = 0, mixArmCeilFail = 0, mixArmFoldFail = 0;
static long long mixPairFoldFail = 0, mixPairAnnFail = 0;
static int reported = 0;

static int armBufG[MAXN], armBufT[MAXN];

static void doWindow(const int *v, int n) {
  int lo = v[0], hi = v[0];
  for (int j = 0; j < n; j++) { if (v[j] < lo) lo = v[j]; if (v[j] > hi) hi = v[j]; }
  if (hi - lo != 9) return;
  int L = lo;
  nWin++;
  for (int i = 0; i < n; i++) {
    if (v[i] != L + 4) continue;
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armBufG[d] = v[i + d];
    for (int d = 0; d < mt; d++) armBufT[d] = v[i - d];
    if (!highAt(armBufG, mg, L) || !highAt(armBufT, mt, L)) continue;
    nBranch++;
    int lamG = lamAnn(armBufG, mg, L), veeG = veeAnn(armBufG, mg, L);
    int lamT = lamAnn(armBufT, mt, L), veeT = veeAnn(armBufT, mt, L);
    for (int s = 0; s < 2; s++) {
      const int *f = s ? armBufT : armBufG;
      int m = s ? mt : mg;
      int lam = s ? lamT : lamG, vee = s ? veeT : veeG;
      if (lam && vee) cBoth++; else if (lam) cLam++; else if (vee) cVee++; else cNeither++;
      int wf = -1, wc = -1;
      int okF = leg4Floor(f, m, L, &wf), okC = leg4Ceil(f, m, L, &wc);
      int okFold = foldsLeg4(f, m, L);
      int mixedArm = (lam && !vee) || (vee && !lam);
      if (!okF) { armFloorFail++; if (mixedArm) mixArmFloorFail++; }
      if (!okC) { armCeilFail++; if (mixedArm) mixArmCeilFail++; }
      if (!okFold) { armFoldFail++; if (mixedArm) mixArmFoldFail++; }
      if (!okFold && mixedArm && reported < 4) {
        reported++;
        printf("  unserved mixed arm (lam=%d vee=%d, len %d): ", lam, vee, m);
        for (int d = 0; d < m && d < 80; d++) printf("%d", f[d] - L);
        printf("\n");
      }
      if (!okFold && okF && okC && reported < 12) {
        reported++;
        printf("  ANNOUNCED BUT NOT FOLDED (lam=%d vee=%d len %d): ", lam, vee, m);
        for (int d = 0; d < m && d < 120; d++) printf("%d", f[d] - L);
        printf("\n");
      }
      if (okFold && (!okF || !okC) && reported < 8) {
        reported++;
        printf("  folds but announcement fails (lam=%d vee=%d floor=%d ceil=%d len %d): ",
               lam, vee, okF, okC, m);
        for (int d = 0; d < m && d < 80; d++) printf("%d", f[d] - L);
        printf("\n");
      }
    }
    int mixed = ((lamG && !veeG) && (veeT && !lamT)) || ((veeG && !lamG) && (lamT && !veeT));
    if (lamG && lamT) cLamPair++;
    else if (veeG && veeT) cVeePair++;
    if (mixed) {
      cMixPair++;
      int okPair = foldsLeg4(armBufG, mg, L) && foldsLeg4(armBufT, mt, L);
      int okAnn = leg4Floor(armBufG, mg, L, 0) && leg4Ceil(armBufG, mg, L, 0) &&
                  leg4Floor(armBufT, mt, L, 0) && leg4Ceil(armBufT, mt, L, 0);
      if (!okPair) mixPairFoldFail++;
      if (!okAnn) mixPairAnnFail++;
    }
  }
}

static int buf[MAXN];

static void scanPath(const int *v, int n, int stride) {
  if (stride < 1) stride = 1;
  for (int a = 0; a < n; a += stride)
    for (int b = a + 1; b < n; b++) {
      int len = b - a + 1;
      if (len > MAXN - 1) break;
      int lo = v[a], hi = v[a];
      for (int j = a; j <= b; j++) { if (v[j] < lo) lo = v[j]; if (v[j] > hi) hi = v[j]; }
      if (hi - lo > 9) break;
      if (hi - lo < 9) continue;
      for (int j = a; j <= b; j++) buf[j - a] = v[j];
      doWindow(buf, len);
    }
}

int main(int argc, char **argv) {
  int maxN = argc > 1 ? atoi(argv[1]) : 10;
  int nRandom = argc > 2 ? atoi(argv[2]) : 20;
  unsigned seed = argc > 3 ? (unsigned)atoi(argv[3]) : 20440u;
  srand(seed);

  /* the crookedness test, on paths whose status is known */
  { Path p = bpath(0, 8); printf("check bing 0 8 (n=%d) crooked: %d\n", p.n, crookedThin(p.v, p.n));
    free(p.v); }
  { int mono[6] = {0,1,2,3,4,5};
    printf("check monotone run crooked: %d\n", crookedThin(mono, 6)); }
  { int fold1[7] = {0,1,2,3,2,1,0};
    printf("check single fold crooked: %d\n", crookedThin(fold1, 7)); }

  /* A. bing 0 N */
  for (int N = 9; N <= maxN; N++) {
    Path p = bpath(0, N);
    if (p.n >= MAXN) { free(p.v); continue; }
    int ok = crookedThin(p.v, p.n);
    printf("family A: bing 0 %d, n = %d, crooked = %d\n", N, p.n, ok);
    if (ok) {
      if (N == 9) doWindow(p.v, p.n);            /* the whole 986-link chain */
      scanPath(p.v, p.n, p.n / 200 + 1);
    }
    free(p.v);
  }

  /* B. bing a b */
  for (int a = 0; a <= 12; a++) for (int b = 0; b <= 12; b++) {
    int d = a < b ? b - a : a - b;
    if (d < 9) continue;
    if (a == 0 && b <= maxN) continue;
    Path p = bpath(a, b);
    if (p.n >= MAXN || p.n > 4000) { free(p.v); continue; }
    if (crookedThin(p.v, p.n)) scanPath(p.v, p.n, p.n / 200 + 1);
    free(p.v);
  }

  /* C. random concatenations */
  int used = 0;
  for (int r = 0; r < nRandom; r++) {
    int nt = 3 + rand() % 4;
    int t[8]; t[0] = rand() % 10;
    for (int q = 1; q <= nt; q++) { do { t[q] = rand() % 10; } while (t[q] == t[q-1]); }
    int tot = 0; static int cat[MAXN];
    for (int q = 0; q < nt; q++) {
      Path p = bpath(t[q], t[q+1]);
      if (tot + p.n >= MAXN) { free(p.v); tot = 0; break; }
      if (tot == 0) { memcpy(cat, p.v, sizeof(int) * p.n); tot = p.n; }
      else { memcpy(cat + tot, p.v + 1, sizeof(int) * (p.n - 1)); tot += p.n - 1; }
      free(p.v);
    }
    if (tot == 0) continue;
    if (!crookedThin(cat, tot)) continue;
    used++;
    scanPath(cat, tot, tot / 200 + 1);
  }
  printf("family C: %d of %d concatenations crooked and used\n", used, nRandom);

  printf("\nwindows of span exactly nine: %lld\n", nWin);
  printf("branch basepoints (v = L+4, both arms HighAt (L+1) (L+8)): %lld\n", nBranch);
  printf("arms: lam only %lld, vee only %lld, both %lld, NEITHER %lld\n",
         cLam, cVee, cBoth, cNeither);
  printf("pairs: lam/lam %lld, vee/vee %lld, mixed %lld\n", cLamPair, cVeePair, cMixPair);
  printf("arms failing the four-leg FLOOR announcement:   %lld (mixed arms: %lld)\n",
         armFloorFail, mixArmFloorFail);
  printf("arms failing the four-leg CEILING announcement: %lld (mixed arms: %lld)\n",
         armCeilFail, mixArmCeilFail);
  printf("arms not folding onto the four-leg walk:        %lld (mixed arms: %lld)\n",
         armFoldFail, mixArmFoldFail);
  printf("mixed pairs unserved by the four-leg walk: %lld; mixed pairs whose announcements fail: %lld\n",
         mixPairFoldFail, mixPairAnnFail);
  return 0;
}
