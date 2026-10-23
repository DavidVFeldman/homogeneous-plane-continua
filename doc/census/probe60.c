/* probe60.c -- batch 60, question 1: the two ascent clauses of the branch's
 * best walk, as arm-only dichotomies.
 *
 * The best walk of the branch L+5 is the reflected parameter set
 * (P, K, M) = (4, 6, 2), i.e. L+6 -> L+3 -> L+7 -> L+1 -> L+8.  Read on the
 * reflection g = 9 - f of an arm f based at 5, the three clauses of its exact
 * criterion Leg4Land (HPC/Fold/Leg4Land.lean) are
 *
 *   floor   : the arm's ascents to L+8  (g d <= P-3 = 1)   -- the L+8 clause;
 *   deep    : the arm's ascents to L+9  (g d <= M-2 = 0)   -- the L+9 clause;
 *   ceiling : the arm's descents to L+1 (g d >= K+2 = 8)   -- the descent,
 *             which land_down1_of_lowAt_low derives from the branch hypothesis.
 *
 * The commission asks whether an arm of the branch that fails one of the two
 * ascent clauses folds, by itself, onto another walk of the four-leg family --
 * the pattern of the branch L+4, where a failing arm is never the problem.
 * With the exact criterion the question is decidable arm by arm, and this
 * program decides it by exhaustive enumeration: every 1-Lipschitz arm of the
 * band [0, 9] based at 5 of length at most `maxlen` satisfying the branch
 * hypothesis LowAt (L+1) (L+8) is enumerated, its clause mask computed, and,
 * when a clause fails, every other walk of the family is tried on the arm
 * alone (by its own landmark sentence, and by the fold itself as a check).
 *
 * Usage: probe60 [maxlen]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXW 128
#define MAXM 40

static int buildWalk4(int *w, int start, int a, int b, int c, int e) {
  int len = 0, cur = start;
  w[len++] = cur;
  int tgt[4] = {a, b, c, e};
  for (int q = 0; q < 4; q++) {
    if (tgt[q] == cur) return -1;
    int s = tgt[q] > cur ? 1 : -1;
    while (cur != tgt[q]) { cur += s; if (len >= MAXW) return -1; w[len++] = cur; }
  }
  return len;
}

/* the dynamic program of HPC/Fold/Decide.lean */
static int folds(const int *f, int m, const int *W, int WL) {
  char cur[MAXW], nxt[MAXW];
  for (int u = 0; u < WL; u++) cur[u] = 0;
  if (f[0] - W[0] > 1 || W[0] - f[0] > 1) return 0;
  cur[0] = 1;
  for (int j = 1; j < m; j++) {
    int any = 0;
    for (int u = 0; u < WL; u++) nxt[u] = 0;
    for (int u = 0; u < WL; u++) {
      if (!cur[u]) continue;
      for (int e = -1; e <= 1; e++) {
        int u2 = u + e;
        if (u2 < 0 || u2 >= WL) continue;
        int d = f[j] - W[u2];
        if (d <= 1 && d >= -1) { nxt[u2] = 1; any = 1; }
      }
    }
    if (!any) return 0;
    memcpy(cur, nxt, WL);
  }
  return 1;
}

/* Leg4Land, clause by clause: 1 base, 2 floor, 4 deep, 8 ceiling */
static int landMask(const int *f, int m, int K, int M, int P) {
  const int H = 9;
  int A = K - P + 1, bad = 0;
  if (f[0] < P - 2 || f[0] > P) bad |= 1;
  int t1 = -1, t2 = -1, t3 = -1;
  for (int j = A; j < m; j++) if (j >= 0 && f[j] >= K - 1) { t1 = j; break; }
  if (t1 >= 0) for (int k = t1 + (K - M); k < m; k++) if (f[k] <= M + 1) { t2 = k; break; }
  if (t2 >= 0) for (int l = t2 + (H - 1 - M); l < m; l++) if (f[l] >= H - 2) { t3 = l; break; }
  for (int d = 0; d < m; d++) {
    if (f[d] <= P - 3 && (t1 < 0 || t1 + (K - 1 - f[d]) > d)) bad |= 2;
    if (f[d] <= M - 2 && (t3 < 0 || t3 + (H - 2 - f[d]) > d)) bad |= 4;
    if (f[d] >= K + 2 && (t2 < 0 || t2 + (f[d] - M - 1) > d)) bad |= 8;
  }
  return bad;
}

/* LowAt f (L+1) (L+8), the branch hypothesis */
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

/* the family of the wide four-leg engine and its reflections */
#define MAXFAM 64
typedef struct { int P, K, M, refl, st, a, b, c, e, len; int w[MAXW]; } Fam;
static Fam fam[MAXFAM];
static int famN = 0;

static void buildFamily(void) {
  for (int P = 2; P <= 6; P++)
    for (int K = P; K <= 8; K++)
      for (int M = 1; M <= P - 2; M++) {
        if (M + 3 > K) continue;
        if (9 > K + 3) continue;
        int st = P - 1, a = K, b = M, c = 8, e = 1;
        int w[MAXW]; int wl = buildWalk4(w, st, a, b, c, e);
        if (wl < 0 || famN >= MAXFAM) continue;
        fam[famN].P = P; fam[famN].K = K; fam[famN].M = M; fam[famN].refl = 0;
        fam[famN].st = st; fam[famN].a = a; fam[famN].b = b; fam[famN].c = c; fam[famN].e = e;
        fam[famN].len = wl; memcpy(fam[famN].w, w, sizeof(w)); famN++;
        int rst = 9 - st, ra = 9 - a, rb = 9 - b, rc = 9 - c, re = 9 - e;
        int w2[MAXW]; int wl2 = buildWalk4(w2, rst, ra, rb, rc, re);
        if (wl2 < 0 || famN >= MAXFAM) continue;
        fam[famN].P = P; fam[famN].K = K; fam[famN].M = M; fam[famN].refl = 1;
        fam[famN].st = rst; fam[famN].a = ra; fam[famN].b = rb; fam[famN].c = rc;
        fam[famN].e = re; fam[famN].len = wl2; memcpy(fam[famN].w, w2, sizeof(w2)); famN++;
      }
}

/* every arm's serving mask, for a greedy cover of the arms by walks */
static unsigned long long *armMask = NULL;
static long armMaskN = 0, armMaskCap = 0;

static long armsSeen = 0, okBest = 0;
static long failFloor = 0, failDeep = 0, failCeil = 0, failBase = 0;
static long floorAlt = 0, floorNone = 0, deepAlt = 0, deepNone = 0;
static long landFoldBad = 0;
static long altHits[MAXFAM], floorHits[MAXFAM], deepHits[MAXFAM], ceilHits[MAXFAM];
static long failCeilNone = 0, failCeilAlt = 0;
static int shownFloor = 0, shownDeep = 0, shownBoth = 0;
static long bothFail = 0, bothHits[MAXFAM];
static long triFail = 0, triHits[MAXFAM]; static int shownTri = 0;

static void examine(const int *f, int m) {
  int g[MAXM];
  for (int d = 0; d < m; d++) g[d] = 9 - f[d];
  int bm = landMask(g, m, 6, 2, 4);
  armsSeen++;
  {
    unsigned long long all = 0;
    for (int q = 0; q < famN; q++) {
      const int *a = fam[q].refl ? g : f;
      if (landMask(a, m, fam[q].K, fam[q].M, fam[q].P) == 0) all |= 1ULL << q;
    }
    if (armMaskN == armMaskCap) {
      armMaskCap = armMaskCap ? armMaskCap * 2 : 1 << 20;
      armMask = realloc(armMask, armMaskCap * sizeof(unsigned long long));
    }
    armMask[armMaskN++] = all;
  }
  if (bm == 0) { okBest++; return; }
  if (bm & 1) failBase++;
  if (bm & 2) failFloor++;
  if (bm & 4) failDeep++;
  if (bm & 8) failCeil++;
  int served = 0;
  for (int q = 0; q < famN; q++) {
    if (fam[q].refl && fam[q].P == 4 && fam[q].K == 6 && fam[q].M == 2) continue;
    const int *a = fam[q].refl ? g : f;
    int la = (landMask(a, m, fam[q].K, fam[q].M, fam[q].P) == 0);
    /* the sentence of a reflected parameter set is read on the reflected arm, so
     * the fold to compare it with is the fold of that arm onto the direct walk */
    int wd[MAXW];
    int wdl = buildWalk4(wd, fam[q].P - 1, fam[q].K, fam[q].M, 8, 1);
    int fo = (wdl > 0) && folds(a, m, wd, wdl);
    if (la != fo) landFoldBad++;
    if (la) { served = 1; altHits[q]++;
      if (bm & 2) floorHits[q]++;
      if (bm & 4) deepHits[q]++;
      if (bm & 8) ceilHits[q]++; }
  }
  if (bm & 2) {
    if (served) floorAlt++;
    else {
      floorNone++;
      if (shownFloor < 3) {
        shownFloor++;
        printf("  an arm failing the L+8 clause and served by no other walk:");
        for (int d = 0; d < m; d++) printf(" %d", f[d]);
        printf("   (clause mask %d)\n", bm);
      }
    }
  }
  if (bm & 8) { if (served) failCeilAlt++; else failCeilNone++; }
  /* the arms failing the best walk and failing w8 = direct (P,K,M) = (5,8,1) too */
  if (landMask(f, m, 8, 1, 5) != 0) {
    bothFail++;
    for (int q = 0; q < famN; q++) {
      if (fam[q].refl && fam[q].P == 4 && fam[q].K == 6 && fam[q].M == 2) continue;
      if (!fam[q].refl && fam[q].P == 5 && fam[q].K == 8 && fam[q].M == 1) continue;
      const int *a = fam[q].refl ? g : f;
      if (landMask(a, m, fam[q].K, fam[q].M, fam[q].P) == 0) bothHits[q]++;
    }
    if (landMask(g, m, 8, 1, 6) != 0) {
      triFail++;
      for (int q = 0; q < famN; q++) {
        const int *a = fam[q].refl ? g : f;
        if (landMask(a, m, fam[q].K, fam[q].M, fam[q].P) == 0) triHits[q]++;
      }
      if (shownTri < 6) {
        shownTri++;
        printf("  an arm failing the best walk, w8 and wR (mask %d):", bm);
        for (int d = 0; d < m; d++) printf(" %d", f[d]);
        printf("\n");
      }
    }
    if (shownBoth < 6) {
      shownBoth++;
      printf("  an arm failing both the best walk and w8 (mask %d):", bm);
      for (int d = 0; d < m; d++) printf(" %d", f[d]);
      printf("\n");
    }
  }
  if (bm & 4) {
    if (served) deepAlt++;
    else {
      deepNone++;
      if (shownDeep < 3) {
        shownDeep++;
        printf("  an arm failing the L+9 clause and served by no other walk:");
        for (int d = 0; d < m; d++) printf(" %d", f[d]);
        printf("   (clause mask %d)\n", bm);
      }
    }
  }
}

static int f[MAXM];

static void rec(int m, int len) {
  if (m == len) {
    if (lowAt(f, m)) examine(f, m);
    return;
  }
  for (int e = -1; e <= 1; e++) {
    int v = f[m - 1] + e;
    if (v < 0 || v > 9) continue;
    f[m] = v;
    rec(m + 1, len);
  }
}

int main(int argc, char **argv) {
  int maxlen = (argc > 1) ? atoi(argv[1]) : 14;
  buildFamily();
  printf("probe60: the two ascent clauses of L+6 -> L+3 -> L+7 -> L+1 -> L+8 as arm-only\n"
         "dichotomies; exhaustive 1-Lipschitz arms of [0,9] based at 5 with LowAt (L+1) (L+8),\n"
         "length up to %d; family of %d walks\n", maxlen, famN);
  for (int len = 1; len <= maxlen; len++) {
    f[0] = 5;
    rec(1, len);
  }
  printf("\narms examined %ld; the best walk's sentence holds on %ld\n", armsSeen, okBest);
  printf("arms failing: base %ld, floor (L+8) %ld, deep (L+9) %ld, ceiling (descent) %ld\n",
         failBase, failFloor, failDeep, failCeil);
  printf("floor-failing arms: served by another walk %ld, by none %ld\n", floorAlt, floorNone);
  printf("deep-failing arms:  served by another walk %ld, by none %ld\n", deepAlt, deepNone);
  printf("the landmark sentence against the fold, on every arm x walk tried: %ld disagreements\n",
         landFoldBad);
  printf("ceiling-failing arms: served by another walk %ld, by none %ld\n",
         failCeilAlt, failCeilNone);
  printf("\narms failing both the best walk and w8 = direct (5,8,1): %ld; the walks serving them:\n",
         bothFail);
  for (int q = 0; q < famN; q++)
    if (bothHits[q])
      printf("  %s P=%d K=%d M=%d : %d -> %d -> %d -> %d -> %d  serves %ld%s\n",
             fam[q].refl ? "reflected" : "direct   ", fam[q].P, fam[q].K, fam[q].M,
             fam[q].st, fam[q].a, fam[q].b, fam[q].c, fam[q].e, bothHits[q],
             (bothHits[q] == bothFail) ? "   <- serves every one of them" : "");
  {
    char *done = calloc(armMaskN, 1);
    long left = armMaskN, picks = 0, none = 0;
    for (long t = 0; t < armMaskN; t++) if (armMask[t] == 0) { done[t] = 1; left--; none++; }
    printf("\ngreedy cover of all %ld arms by walks of the family (%ld served by no walk):\n",
           armMaskN, none);
    while (left > 0 && picks < 10) {
      int best = -1; long bestc = 0;
      for (int q = 0; q < famN; q++) {
        long cnt = 0;
        for (long t = 0; t < armMaskN; t++) if (!done[t] && (armMask[t] & (1ULL << q))) cnt++;
        if (cnt > bestc) { bestc = cnt; best = q; }
      }
      if (best < 0) break;
      for (long t = 0; t < armMaskN; t++)
        if (!done[t] && (armMask[t] & (1ULL << best))) { done[t] = 1; left--; }
      picks++;
      printf("  pick %ld: %s P=%d K=%d M=%d (%d -> %d -> %d -> %d -> %d) covers %ld, left %ld\n",
             picks, fam[best].refl ? "reflected" : "direct   ", fam[best].P, fam[best].K,
             fam[best].M, fam[best].st, fam[best].a, fam[best].b, fam[best].c, fam[best].e,
             bestc, left);
    }
    printf("  walks needed: %ld; arms left: %ld\n", picks, left);
    free(done);
  }

  printf("\narms failing the best walk, w8 and wR = reflected (6,8,1): %ld; the walks serving them:\n",
         triFail);
  for (int q = 0; q < famN; q++)
    if (triHits[q])
      printf("  %s P=%d K=%d M=%d : serves %ld%s\n",
             fam[q].refl ? "reflected" : "direct   ", fam[q].P, fam[q].K, fam[q].M, triHits[q],
             (triHits[q] == triFail) ? "   <- serves every one of them" : "");
  printf("\nwalks serving an arm that fails a clause of the best walk"
         " (all / floor-failing / deep-failing / ceiling-failing):\n");
  for (int q = 0; q < famN; q++)
    if (altHits[q])
      printf("  %s P=%d K=%d M=%d : %d -> %d -> %d -> %d -> %d  serves %ld / %ld / %ld / %ld%s\n",
             fam[q].refl ? "reflected" : "direct   ", fam[q].P, fam[q].K, fam[q].M,
             fam[q].st, fam[q].a, fam[q].b, fam[q].c, fam[q].e, altHits[q],
             floorHits[q], deepHits[q], ceilHits[q],
             (floorHits[q] == failFloor && failFloor > 0) ? "   <- serves every floor-failing arm"
                                                          : "");
  return 0;
}
