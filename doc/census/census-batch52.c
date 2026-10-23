/* census-batch52.c -- batch 52.  The crossing argument: the ceiling case at the
 * branch L+4, and the branch L+5 read as the reflection of the branch L+4.
 *
 * Carried over from census-batch51.c: the generators, the faithfulness test
 * (IsCrookedIvF), the dynamic program over FoldsOnto (HPC/Fold/Decide.lean),
 * the predicates of the three walks and their exactness audit.
 *
 * New in this batch:
 *
 *   A. Question 1, the ceiling case as a crossing.  At every branch basepoint
 *      (rho i = L+4, both arms HighAt (L+1) (L+8)) at which some arm fails
 *      Leg3Ceil -- so that arm folds onto the Lambda-walk by leg3Ceil_or_lam --
 *      the census asks whether the pair then satisfies
 *          MidW4 and BottomW4 on both arms   (the sentence of w4), or
 *          Valley5 and TopW5 on both arms    (the sentence of w5).
 *      By foldsOnto_w4_iff_landmark / foldsOnto_w5_iff_landmark that is exactly
 *      "the pair folds onto w4, or onto w5".
 *
 *   B. Question 3, the branch L+5 at the level of arms.  An arm is reflected by
 *      f |-> 9 - f (the band is [0,9]); by the transport theorems of
 *      HPC/Fold/ArmReflect.lean a fold of f onto a reflected walk is a fold of
 *      the reflected arm onto the walk itself.  The census
 *        - audits that transport directly: folds(f, reflected walk) is compared
 *          with folds(9-f, walk) for each of the five walks;
 *        - at every basepoint rho i = L+5 with both arms LowAt (L+1) (L+8) --
 *          the open branch -- runs the whole branch-L+4 battery on the
 *          reflected arms: the three criteria, the sentence, the work item;
 *        - tests the reflected crookedness clauses CrookUpR and CrookDownR on
 *          the arms of the model.  CrookUp and CrookDown are theorems about
 *          every arm; their reflections are the clauses the reflected
 *          dichotomies (ceil4R_or_lam, floor3R_or_vee) consume, and whether the
 *          model supplies them is the question;
 *        - tests the reflected dichotomies themselves as statements about the
 *          model: an arm of the branch L+5 failing Ceil4R -- that is, whose
 *          reflection fails Valley4 -- does it fold onto the Lambda-walk based
 *          at L+4?  And one failing Floor3R onto the V-walk based at L+6?
 *
 *   C. Question 2, ValleyResidual as a pair: basepoints at which one arm fails
 *      Leg3Valley and the other realises the residual configuration of
 *      cross_valley_profile, with the V-fold verdict of each arm.
 *
 * Usage: census-batch52 [rand-rounds] [seed] [walk-steps] [crook-cap]
 * The last argument caps the arm length on which the O(n^2) crook clauses are
 * tested (0 = no cap).
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

#define MAXLEV 32
#define MAXN   2048
#define MAXW   96

static int meetTab[MAXLEV][MAXN + 1];

/* IsCrookedIvF (rho, sig), exactly as HPC/Fold/Crook.lean states it. */
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

/* the dynamic program of HPC/Fold/Decide.lean */
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

static int buildWalk(int *w, int start, int a, int b, int c) {
  int len = 0, cur = start;
  w[len++] = cur;
  int tgt[3] = {a, b, c};
  for (int q = 0; q < 3; q++) {
    if (tgt[q] < 0) break;
    if (tgt[q] == cur) return -1;
    int s = tgt[q] > cur ? 1 : -1;
    while (cur != tgt[q]) { cur += s; if (len >= MAXW) return -1; w[len++] = cur; }
  }
  return len;
}

static int rho[MAXN], sig[MAXN], armG[MAXN], armT[MAXN];

/* HighAt f (L+1) (L+8) */
static int highAt(const int *f, int m) {
  int seenLow = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !seenLow) return 0;
    if (f[d] <= 2) seenLow = 1;
  }
  return 1;
}

/* Leg3Valley f L */
static int leg3Valley(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j + 5 <= d && !ok; j++) if (a[j] >= 5) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* Leg3Ceil f L */
static int leg3Ceil(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 8) continue;
    int ok = 0;
    for (int j = 3; j + 11 <= d && !ok; j++) {
      if (a[j] < 5) continue;
      for (int k = j + 5; k + 6 <= d && !ok; k++) if (a[k] <= 2) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

/* Valley4 f L: the valley clause common to the three walks -- before every time
 * at L+1 or below, a time at L+5 or above at a step >= 3, at least 4 earlier. */
static int valley4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j + 4 <= d && !ok; j++) if (a[j] >= 5) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* BottomW4 f L: the floor clause of w4 -- before every time at L or below, a
 * time at L+3 or below at a step >= 1, then a time at L+7 or above at least 6
 * steps later, and the descent at least 7 steps after that. */
static int bottomW4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 0) continue;
    int ok = 0;
    for (int j = 1; j + 13 <= d && !ok; j++) {
      if (a[j] > 3) continue;
      for (int k = j + 6; k + 7 <= d && !ok; k++) if (a[k] >= 7) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

/* TopW5 f L: the ceiling clause of w5 -- before every time at L+9, a time at
 * L+6 or above at a step >= 4, then a time at L+2 or below at least 6 steps
 * later, and the ascent at least 7 steps after that. */
static int topW5(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 9) continue;
    int ok = 0;
    for (int j = 4; j + 13 <= d && !ok; j++) {
      if (a[j] < 6) continue;
      for (int k = j + 6; k + 7 <= d && !ok; k++) if (a[k] <= 2) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

/* Valley5 f L: the valley clause of w5 -- a time at L+6 or above at a step >= 4,
 * at least 5 steps earlier (deepValley_of_foldsOnto_leg3deep). */
static int valley5(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 4; j + 5 <= d && !ok; j++) if (a[j] >= 6) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* MidW4 f L: the trough clause of w4 -- before every time at L+5 or above, a
 * time at L+3 or below at a step >= 1, at least 2 steps earlier. */
static int midW4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 5) continue;
    int ok = 0;
    for (int j = 1; j + 2 <= d && !ok; j++) if (a[j] <= 3) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* CeilW4 f L: the ceiling clause of w4 -- before every time at L+8 or above, a
 * time at L+3 or below at a step >= 1, at least 5 steps earlier. */
static int ceilW4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 8) continue;
    int ok = 0;
    for (int j = 1; j + 5 <= d && !ok; j++) if (a[j] <= 3) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

static int foldsLam(const int *f, int m) {   /* Lambda based at L+3: 3 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 3, 8, 1, -1);
  return folds(f, m, w, wl);
}
static int foldsVee(const int *f, int m) {   /* V based at L+5: 5 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 5, 1, 8, -1);
  return folds(f, m, w, wl);
}
static int foldsW3(const int *f, int m) {    /* 3 -> 6 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 3, 6, 1, 8);
  return folds(f, m, w, wl);
}
static int foldsW4(const int *f, int m) {    /* 3 -> 2 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 3, 2, 8, 1);
  return folds(f, m, w, wl);
}
static int foldsW5(const int *f, int m) {    /* 3 -> 7 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 3, 7, 1, 8);
  return folds(f, m, w, wl);
}

/* The configuration the case analysis of REPORT-batch49.md 2.2 leaves open for
 * `cross_valley_profile`: an arm whose low times before its first ascent to
 * L+7 all occur at its step two or three -- so that the clause applied across
 * the basepoint returns a low link at i-3 or i-2 and the V-criterion, which
 * wants index four or later, is not reached.  Returns 1 if the arm realises it. */
static int residualValleyCase(const int *a, int m) {
  int e = -1;
  for (int d = 0; d < m; d++) if (a[d] >= 7) { e = d; break; }
  if (e < 0) return 0;
  int any = 0, mx = -1, mn = 1 << 30;
  for (int j = 0; j < e; j++) if (a[j] <= 2) { any = 1; if (j > mx) mx = j; if (j < mn) mn = j; }
  return any && mn >= 2 && mx <= 3;
}

/* the shortest zigzag walk with at most three turns serving both arms */
static void findWalk(const int *g, int mg, const int *t, int mt) {
  int best = 1 << 30, bs = -1, ba = -1, bb = -1, bc = -1;
  for (int st = 2; st <= 6; st++)
    for (int a = 0; a <= 9; a++) {
      if (a == st) continue;
      for (int b = -1; b <= 9; b++) {
        if (b == a) continue;
        for (int c = -1; c <= 9; c++) {
          if (c == b) continue;
          if (b < 0 && c >= 0) continue;
          int w[MAXW]; int wl = buildWalk(w, st, a, b, c);
          if (wl < 0 || wl >= best) continue;
          if (folds(g, mg, w, wl) && folds(t, mt, w, wl)) {
            best = wl; bs = st; ba = a; bb = b; bc = c;
          }
        }
      }
    }
  if (bs < 0) printf("      NO walk of at most three turns serves this pair\n");
  else printf("      shortest serving walk (%d times): %d -> %d -> %d -> %d\n",
              best, bs, ba, bb, bc);
}

/* ---- the branch L+5: LowAt, reflection, the reflected crook clauses ------ */

/* LowAt f (L+1) (L+8), as HPC/Fold/Leaf.lean states it. */
static int lowAt(const int *f, int m) {
  int seenHigh8 = 0, seenLow2 = 0, seenLow2High6 = 0;  /* over the indices seen so far */
  for (int d = 0; d < m; d++) {
    if (f[d] <= 1 && !seenHigh8 && !seenLow2High6) return 0;
    if (f[d] >= 8) seenHigh8 = 1;
    if (f[d] >= 6 && seenLow2) seenLow2High6 = 1;
    if (f[d] <= 2) seenLow2 = 1;
  }
  return 1;
}

/* the reflection of an arm in the band [0,9] */
static void reflArm(const int *f, int m, int *g) { for (int d = 0; d < m; d++) g[d] = 9 - f[d]; }

/* CrookUp f, as HPC/Fold/Crook.lean states it */
static int crookUpArm(const int *f, int m) {
  static int nxt[10][MAXN + 1];
  for (int l = 0; l < 10; l++) nxt[l][m] = m;
  for (int j = m - 1; j >= 0; j--)
    for (int l = 0; l < 10; l++) nxt[l][j] = (f[j] == l) ? j : nxt[l][j + 1];
  for (int s = 0; s < m; s++)
    for (int t = s + 1; t < m; t++) {
      if (f[s] + 3 > f[t]) continue;
      int u = m;
      for (int l = f[t] - 2; l <= f[t] - 1; l++)
        if (l >= 0 && l <= 9 && nxt[l][s + 1] < u) u = nxt[l][s + 1];
      if (u >= t) return 0;
      int up = m;
      for (int l = f[s]; l <= f[s] + 1; l++)
        if (l >= 0 && l <= 9 && nxt[l][u + 1] < up) up = nxt[l][u + 1];
      if (up >= t) return 0;
    }
  return 1;
}

/* CrookDown f */
static int crookDownArm(const int *f, int m) {
  static int nxt[10][MAXN + 1];
  for (int l = 0; l < 10; l++) nxt[l][m] = m;
  for (int j = m - 1; j >= 0; j--)
    for (int l = 0; l < 10; l++) nxt[l][j] = (f[j] == l) ? j : nxt[l][j + 1];
  for (int s = 0; s < m; s++)
    for (int t = s + 1; t < m; t++) {
      if (f[t] + 3 > f[s]) continue;
      int u = m;
      for (int l = f[t]; l <= f[t] + 1; l++)
        if (l >= 0 && l <= 9 && nxt[l][s + 1] < u) u = nxt[l][s + 1];
      if (u >= t) return 0;
      int up = m;
      for (int l = f[s] - 2; l <= f[s] - 1; l++)
        if (l >= 0 && l <= 9 && nxt[l][u + 1] < up) up = nxt[l][u + 1];
      if (up >= t) return 0;
    }
  return 1;
}

/* CrookUpR f = CrookDown (9 - f), CrookDownR f = CrookUp (9 - f) */
static int crookUpR(const int *f, int m) {
  static int g[MAXN]; reflArm(f, m, g); return crookDownArm(g, m);
}
static int crookDownR(const int *f, int m) {
  static int g[MAXN]; reflArm(f, m, g); return crookUpArm(g, m);
}

/* the reflected walks, read on the arm itself */
static int foldsLamR(const int *f, int m) {  /* V based at L+6: 6 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 6, 1, 8, -1); return folds(f, m, w, wl);
}
static int foldsVeeR(const int *f, int m) {  /* Lambda based at L+4: 4 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 4, 8, 1, -1); return folds(f, m, w, wl);
}
static int foldsW3R(const int *f, int m) {   /* 6 -> 3 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 6, 3, 8, 1); return folds(f, m, w, wl);
}
static int foldsW4R(const int *f, int m) {   /* 6 -> 7 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 6, 7, 1, 8); return folds(f, m, w, wl);
}
static int foldsW5R(const int *f, int m) {   /* 6 -> 2 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 6, 2, 8, 1); return folds(f, m, w, wl);
}
/* two further candidates for the branch L+5, of the unreflected family: the
 * shortest walks the census finds serving the pairs the three reflections miss */
static int foldsW6(const int *f, int m) {    /* 5 -> 7 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 5, 7, 1, 8); return folds(f, m, w, wl);
}
static int foldsW7(const int *f, int m) {    /* 4 -> 7 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 4, 7, 1, 8); return folds(f, m, w, wl);
}

typedef struct {
  long pairs, links, nonthin;
  /* the branch L+4 */
  long base, unserved, w3, w4, w5, threeOK, threeBad, sentence, sentenceBad;
  long exact, exactBad;
  /* question 1: the ceiling case as a crossing */
  long ceilCase, ceilCaseW4, ceilCaseW5, ceilCaseEither, ceilCaseNeither;
  long ceilCaseUnserved, ceilCaseUnservedNeither;
  long ceilCaseLamFree, ceilCaseLamFreeNeither;
  /* question 2: ValleyResidual as a pair */
  long valleyCase, valleyCaseCross, valleyResidualPair, valleyResidualPairBad;
  /* question 3: the branch L+5 */
  long base5, unserved5, w3R, w4R, w5R, threeOK5, threeBad5, sentence5, sentenceBad5;
  long w6R, w7R, fiveOK5, fiveBad5;
  long reflAudit, reflAuditBad;
  long crookArms, crookUpBad, crookDownBad, crookUpRBad, crookDownRBad;
  long ceil4RFail, ceil4RLam, ceil4RLamBad, floor3RFail, floor3RVee, floor3RVeeBad;
  long exact5, exact5Bad;
} Cnt;

static void zero(Cnt *c) { memset(c, 0, sizeof(*c)); }

static int crookCap = 256;

/* ---- the audit sample: arms of the branch L+5 and their reflected verdicts -- */
static FILE *auditFile = NULL;
static int auditWant = 0, auditHave = 0;
static char auditSig[64][64];
static char auditTag[64][16];

static int auditTagCount(const char *tag) {
  int n = 0;
  for (int s = 0; s < auditHave; s++) if (!strcmp(auditTag[s], tag)) n++;
  return n;
}

/* the reflected predicates, read on the arm itself: Ceil4R f = Valley4 (9-f), etc. */
static void auditArm5(const int *a0, int m0, const char *tag, int gen, int bp, const char *which) {
  static int g[MAXN];
  if (!auditFile || auditHave >= auditWant || m0 < 4) return;
  const int *a = a0;
  int m = m0 < 64 ? m0 : 64;
  reflArm(a, m, g);
  char sig1[64];
  snprintf(sig1, sizeof sig1, "%d%d%d%d%d%d%d%d%d%d%d%d%d",
           lowAt(a, m), valley4(g, m), leg3Ceil(g, m), midW4(g, m), ceilW4(g, m), bottomW4(g, m),
           valley5(g, m), topW5(g, m), foldsLamR(a, m), foldsVeeR(a, m), foldsW3R(a, m),
           foldsW4R(a, m), foldsW5R(a, m));
  for (int s = 0; s < auditHave; s++) if (!strcmp(auditSig[s], sig1)) return;
  if (auditTagCount(tag) >= 3) return;
  strcpy(auditSig[auditHave], sig1);
  snprintf(auditTag[auditHave], sizeof auditTag[0], "%s", tag);
  auditHave++;
  fprintf(auditFile, "arm %s gen=%d basepoint=%d %s len=%d (of %d)\n", tag, gen, bp, which, m, m0);
  fprintf(auditFile, "  levels:");
  for (int d = 0; d < m; d++) fprintf(auditFile, " %d", a[d]);
  fprintf(auditFile, "\n  nat16: 0x");
  for (int d = m - 1; d >= 0; d--) fprintf(auditFile, "%X", a[d]);
  fprintf(auditFile,
          "\n  lowAt=%d Ceil4R=%d Floor3R=%d MidW4R=%d FloorW4R=%d TopW4R=%d Ceil5R=%d "
          "BottomW5R=%d\n  foldsVeeL6=%d foldsLamL4=%d foldsW3R=%d foldsW4R=%d foldsW5R=%d\n",
          lowAt(a, m), valley4(g, m), leg3Ceil(g, m), midW4(g, m), ceilW4(g, m), bottomW4(g, m),
          valley5(g, m), topW5(g, m), foldsLamR(a, m), foldsVeeR(a, m), foldsW3R(a, m),
          foldsW4R(a, m), foldsW5R(a, m));
}

static void scan(Cnt *c, int n, const char *tag, int gen) {
  static int gG[MAXN], gT[MAXN];
  c->pairs++; c->links += n;
  for (int u = 0; u < n; u++) if (sig[u] != rho[u]) c->nonthin++;
  for (int i = 0; i < n; i++) {
    int mg = n - i, mt = i + 1;
    if (rho[i] == 4) {
      for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
      for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
      if (!highAt(armG, mg) || !highAt(armT, mt)) continue;
      c->base++;
      int vG = leg3Valley(armG, mg), vT = leg3Valley(armT, mt);
      int cG = leg3Ceil(armG, mg), cT = leg3Ceil(armT, mt);
      int q4G = valley4(armG, mg), q4T = valley4(armT, mt);
      int q5G = valley5(armG, mg), q5T = valley5(armT, mt);
      int fvG = foldsVee(armG, mg), fvT = foldsVee(armT, mt);
      int flG = foldsLam(armG, mg), flT = foldsLam(armT, mt);
      int f3G = foldsW3(armG, mg), f3T = foldsW3(armT, mt);
      int f4G = foldsW4(armG, mg), f4T = foldsW4(armT, mt);
      int f5G = foldsW5(armG, mg), f5T = foldsW5(armT, mt);
      int m4G = midW4(armG, mg) && bottomW4(armG, mg);
      int m4T = midW4(armT, mt) && bottomW4(armT, mt);
      int t5G = q5G && topW5(armG, mg), t5T = q5T && topW5(armT, mt);
      int unserved = !((flG && flT) || (fvG && fvT));

      /* the exactness audit of batch 51, carried over */
      {
        const int *ar[2] = {armG, armT}; int ml[2] = {mg, mt};
        int f3[2] = {f3G, f3T}, f4[2] = {f4G, f4T}, f5[2] = {f5G, f5T};
        for (int s = 0; s < 2; s++) {
          int land = valley4(ar[s], ml[s]) && leg3Ceil(ar[s], ml[s]);
          int w4c = midW4(ar[s], ml[s]) && ceilW4(ar[s], ml[s]) && bottomW4(ar[s], ml[s]);
          int w5c = valley5(ar[s], ml[s]) && topW5(ar[s], ml[s]);
          c->exact += 3;
          if (land != f3[s] || w4c != f4[s] || w5c != f5[s]) { c->exactBad++;
            printf("  [%s %d] EXACTNESS fails at the branch L+4: basepoint %d arm %d\n",
                   tag, gen, i, s); }
        }
      }

      /* question 1: the ceiling case */
      if (!cG || !cT) {
        c->ceilCase++;
        if (m4G && m4T) c->ceilCaseW4++;
        if (t5G && t5T) c->ceilCaseW5++;
        if ((m4G && m4T) || (t5G && t5T)) c->ceilCaseEither++;
        else {
          c->ceilCaseNeither++;
          if (unserved) {
            c->ceilCaseUnservedNeither++;
            printf("  [%s %d] CEILING CROSSING fails at an unserved pair: basepoint %d "
                   "(leg3Ceil G=%d T=%d; w4 sentence G=%d T=%d; w5 sentence G=%d T=%d)\n",
                   tag, gen, i, cG, cT, m4G, m4T, t5G, t5T);
          }
        }
        if (unserved) c->ceilCaseUnserved++;
        /* the hypothesis of the commission's first question: the other arm does
         * not fold onto the Lambda-walk, so the pair is not served by it */
        if (!(flG && flT)) {
          c->ceilCaseLamFree++;
          if (!((m4G && m4T) || (t5G && t5T))) {
            c->ceilCaseLamFreeNeither++;
            printf("  [%s %d] CEILING CROSSING fails (Lambda-free pair): basepoint %d "
                   "(leg3Ceil G=%d T=%d; lam G=%d T=%d; w4 sentence G=%d T=%d; "
                   "w5 sentence G=%d T=%d; vee G=%d T=%d)\n",
                   tag, gen, i, cG, cT, flG, flT, m4G, m4T, t5G, t5T, fvG, fvT);
          }
        }
      }

      /* question 2: the valley case, and the residual configuration as a pair */
      if (!vG || !vT) {
        c->valleyCase++;
        if (fvG && fvT) c->valleyCaseCross++;
        int resG = residualValleyCase(armG, mg), resT = residualValleyCase(armT, mt);
        if ((!vG && resT) || (!vT && resG) || (!vG && resG) || (!vT && resT)) {
          c->valleyResidualPair++;
          if (!(fvG && fvT)) { c->valleyResidualPairBad++;
            printf("  [%s %d] VALLEY RESIDUAL as a pair: basepoint %d "
                   "(valley G=%d T=%d, residual G=%d T=%d, V-fold G=%d T=%d)\n",
                   tag, gen, i, vG, vT, resG, resT, fvG, fvT); }
        }
      }

      if (!unserved) continue;
      c->unserved++;
      {
        int s3 = f3G && f3T, s4 = f4G && f4T, s5 = f5G && f5T;
        if (s3) c->w3++;
        if (s4) c->w4++;
        if (s5) c->w5++;
        int sent = (q4G && cG && q4T && cT) || (m4G && m4T) || (t5G && t5T);
        if (sent) c->sentence++;
        if (sent != (s3 || s4 || s5)) { c->sentenceBad++;
          printf("  [%s %d] three_walks_iff_sentence FAILS: basepoint %d\n", tag, gen, i); }
        if (s3 || s4 || s5) c->threeOK++;
        else { c->threeBad++;
          printf("  [%s %d] WORK ITEM unserved_three_walks FAILS: basepoint %d\n", tag, gen, i);
          findWalk(armG, mg, armT, mt); }
      }
    } else if (rho[i] == 5) {
      for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
      for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
      if (!lowAt(armG, mg) || !lowAt(armT, mt)) continue;
      c->base5++;
      reflArm(armG, mg, gG);
      reflArm(armT, mt, gT);
      auditArm5(armG, mg, tag, gen, i, "forward");
      auditArm5(armT, mt, tag, gen, i, "backward");

      /* the transport audit: a fold onto a reflected walk is a fold of the
       * reflected arm (foldsOnto_armRefl, w3R_eq, w4R_eq, w5R_eq) */
      {
        const int *ar[2] = {armG, armT}; const int *gr[2] = {gG, gT}; int ml[2] = {mg, mt};
        for (int s = 0; s < 2; s++) {
          int a1 = foldsW3R(ar[s], ml[s]) == foldsW3(gr[s], ml[s]);
          int a2 = foldsW4R(ar[s], ml[s]) == foldsW4(gr[s], ml[s]);
          int a3 = foldsW5R(ar[s], ml[s]) == foldsW5(gr[s], ml[s]);
          int a4 = foldsLamR(ar[s], ml[s]) == foldsLam(gr[s], ml[s]);
          int a5 = foldsVeeR(ar[s], ml[s]) == foldsVee(gr[s], ml[s]);
          c->reflAudit += 5;
          if (!(a1 && a2 && a3 && a4 && a5)) { c->reflAuditBad++;
            printf("  [%s %d] REFLECTION TRANSPORT fails: basepoint %d arm %d\n",
                   tag, gen, i, s); }
        }
      }

      /* the exactness audit on the reflected arms */
      {
        const int *gr[2] = {gG, gT}; int ml[2] = {mg, mt};
        for (int s = 0; s < 2; s++) {
          int land = valley4(gr[s], ml[s]) && leg3Ceil(gr[s], ml[s]);
          int w4c = midW4(gr[s], ml[s]) && ceilW4(gr[s], ml[s]) && bottomW4(gr[s], ml[s]);
          int w5c = valley5(gr[s], ml[s]) && topW5(gr[s], ml[s]);
          c->exact5 += 3;
          if (land != foldsW3(gr[s], ml[s]) || w4c != foldsW4(gr[s], ml[s]) ||
              w5c != foldsW5(gr[s], ml[s])) { c->exact5Bad++;
            printf("  [%s %d] EXACTNESS fails at the branch L+5: basepoint %d arm %d\n",
                   tag, gen, i, s); }
        }
      }

      /* the crookedness clauses and their reflections */
      {
        const int *ar[2] = {armG, armT}; int ml[2] = {mg, mt};
        for (int s = 0; s < 2; s++) {
          int m0 = ml[s];
          if (crookCap && m0 > crookCap) continue;
          c->crookArms++;
          if (!crookUpArm(ar[s], m0)) c->crookUpBad++;
          if (!crookDownArm(ar[s], m0)) c->crookDownBad++;
          if (!crookUpR(ar[s], m0)) c->crookUpRBad++;
          if (!crookDownR(ar[s], m0)) c->crookDownRBad++;
        }
      }

      /* the reflected dichotomies, as statements about the model */
      {
        const int *ar[2] = {armG, armT}; const int *gr[2] = {gG, gT}; int ml[2] = {mg, mt};
        for (int s = 0; s < 2; s++) {
          if (!valley4(gr[s], ml[s])) {            /* Ceil4R fails on the arm */
            c->ceil4RFail++;
            if (foldsVeeR(ar[s], ml[s])) c->ceil4RLam++;
            else { c->ceil4RLamBad++;
              printf("  [%s %d] ceil4R_or_lam FAILS in the model: basepoint %d arm %d\n",
                     tag, gen, i, s); }
          }
          if (!leg3Ceil(gr[s], ml[s])) {           /* Floor3R fails on the arm */
            c->floor3RFail++;
            if (foldsLamR(ar[s], ml[s])) c->floor3RVee++;
            else { c->floor3RVeeBad++;
              printf("  [%s %d] floor3R_or_vee FAILS in the model: basepoint %d arm %d\n",
                     tag, gen, i, s); }
          }
        }
      }

      /* the work item of the branch L+5 */
      {
        int flG = foldsLamR(armG, mg), flT = foldsLamR(armT, mt);
        int fvG = foldsVeeR(armG, mg), fvT = foldsVeeR(armT, mt);
        if ((flG && flT) || (fvG && fvT)) continue;
        c->unserved5++;
        int s3 = foldsW3R(armG, mg) && foldsW3R(armT, mt);
        int s4 = foldsW4R(armG, mg) && foldsW4R(armT, mt);
        int s5 = foldsW5R(armG, mg) && foldsW5R(armT, mt);
        int s6 = foldsW6(armG, mg) && foldsW6(armT, mt);
        int s7 = foldsW7(armG, mg) && foldsW7(armT, mt);
        if (s3) c->w3R++;
        if (s4) c->w4R++;
        if (s5) c->w5R++;
        if (s6) c->w6R++;
        if (s7) c->w7R++;
        if (s3 || s4 || s5 || s6 || s7) c->fiveOK5++; else c->fiveBad5++;
        int sent3 = valley4(gG, mg) && leg3Ceil(gG, mg) && valley4(gT, mt) && leg3Ceil(gT, mt);
        int sent4 = midW4(gG, mg) && bottomW4(gG, mg) && midW4(gT, mt) && bottomW4(gT, mt);
        int sent5 = valley5(gG, mg) && topW5(gG, mg) && valley5(gT, mt) && topW5(gT, mt);
        int sent = sent3 || sent4 || sent5;
        if (sent) c->sentence5++;
        if (sent != (s3 || s4 || s5)) { c->sentenceBad5++;
          printf("  [%s %d] three_walks5_iff_sentence FAILS: basepoint %d\n", tag, gen, i); }
        if (s3 || s4 || s5) c->threeOK5++;
        else { c->threeBad5++;
          printf("  [%s %d] the three reflected walks MISS a pair of the branch L+5: "
                 "basepoint %d\n", tag, gen, i);
          findWalk(armG, mg, armT, mt);
          printf("      forward arm  (len %d):", mg);
          for (int d = 0; d < mg && d < 60; d++) printf(" %d", armG[d]);
          printf("\n      backward arm (len %d):", mt);
          for (int d = 0; d < mt && d < 60; d++) printf(" %d", armT[d]);
          printf("\n");
        }
      }
    }
  }
}

static void report(const char *name, const Cnt *c) {
  printf("\n-- %s --\n", name);
  printf("faithful pairs: %ld; non-thin links %ld/%ld (%.5f)\n", c->pairs, c->nonthin, c->links,
         c->links ? (double)c->nonthin / (double)c->links : 0.0);
  printf("branch L+4: basepoints %ld, unserved %ld; served by w3 %ld, w4 %ld, w5 %ld; "
         "by one of the three %ld; BY NONE %ld\n", c->base, c->unserved, c->w3, c->w4, c->w5,
         c->threeOK, c->threeBad);
  printf("  sentence holds at %ld unserved pairs; equivalence failures %ld; "
         "exactness checks %ld / failures %ld\n", c->sentence, c->sentenceBad, c->exact,
         c->exactBad);
  printf("QUESTION 1 (the ceiling case as a crossing): basepoints with an arm failing Leg3Ceil "
         "%ld, of which unserved %ld\n", c->ceilCase, c->ceilCaseUnserved);
  printf("  both arms satisfy the w4 sentence: %ld; the w5 sentence: %ld; one of the two: %ld; "
         "NEITHER: %ld (of which unserved: %ld)\n", c->ceilCaseW4, c->ceilCaseW5,
         c->ceilCaseEither, c->ceilCaseNeither, c->ceilCaseUnservedNeither);
  printf("  with the other arm missing the Lambda-walk too (the question's own hypothesis): "
         "%ld, of which NEITHER sentence: %ld\n", c->ceilCaseLamFree, c->ceilCaseLamFreeNeither);
  printf("QUESTION 2 (cross_valley_profile): basepoints with an arm failing Leg3Valley %ld, "
         "of which both arms fold onto the V-walk %ld\n", c->valleyCase, c->valleyCaseCross);
  printf("  pairs realising the residual configuration together with a failing arm: %ld, "
         "FAILURES %ld\n", c->valleyResidualPair, c->valleyResidualPairBad);
  printf("QUESTION 3 (the branch L+5): basepoints %ld, unserved %ld; served by the reflection "
         "of w3 %ld, of w4 %ld, of w5 %ld; by one of the three %ld; BY NONE %ld\n",
         c->base5, c->unserved5, c->w3R, c->w4R, c->w5R, c->threeOK5, c->threeBad5);
  printf("  adding the two unreflected walks 5->7->1->8 and 4->7->1->8: they serve %ld and %ld; "
         "one of the five serves %ld; BY NONE OF THE FIVE %ld\n", c->w6R, c->w7R, c->fiveOK5,
         c->fiveBad5);
  printf("  reflected sentence holds at %ld unserved pairs; equivalence failures %ld; "
         "exactness checks %ld / failures %ld\n", c->sentence5, c->sentenceBad5, c->exact5,
         c->exact5Bad);
  printf("  transport audit: %ld checks, %ld failures\n", c->reflAudit, c->reflAuditBad);
  printf("  crookedness on %ld arms of the branch: CrookUp fails %ld, CrookDown fails %ld, "
         "CrookUpR fails %ld, CrookDownR fails %ld\n", c->crookArms, c->crookUpBad,
         c->crookDownBad, c->crookUpRBad, c->crookDownRBad);
  printf("  reflected dichotomies in the model: arms failing Ceil4R %ld (fold onto the Lambda-walk "
         "at L+4: %ld, FAILURES %ld); arms failing Floor3R %ld (fold onto the V-walk at L+6: %ld, "
         "FAILURES %ld)\n", c->ceil4RFail, c->ceil4RLam, c->ceil4RLamBad, c->floor3RFail,
         c->floor3RVee, c->floor3RVeeBad);
}

static Cnt ct, cs, cf, cm, ch, cw;
static void runChain(int n, const int *v, long rounds, long walkSteps, const char *name) {
  printf("\n==== base chain %s (n = %d links); IsCrookedIvF: ", name, n);
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  printf("%d ====\n", crookedGen(rho, sig, n));

  /* (0) the thin chain */
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  if (crookedGen(rho, sig, n)) scan(&ct, n, "thin", 0);

  /* (a) single shavings */
  for (int pk = 1; pk + 1 < n; pk++) {
    if (!(v[pk] > v[pk-1] && v[pk] > v[pk+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    rho[pk] = v[pk] - 1;
    if (!crookedGen(rho, sig, n)) { printf("  shave %d: NOT faithful\n", pk); continue; }
    scan(&cs, n, "shave", pk);
  }

  /* (b) single fills */
  for (int vl = 1; vl + 1 < n; vl++) {
    if (!(v[vl] < v[vl-1] && v[vl] < v[vl+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    sig[vl] = v[vl] + 1;
    if (!crookedGen(rho, sig, n)) { printf("  fill %d: NOT faithful\n", vl); continue; }
    scan(&cf, n, "fill", vl);
  }

  /* (c) random mixtures at rate 1/3 */
  for (long it = 0; it < rounds; it++) {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) { if (random() % 3 == 0) rho[j] = v[j] - 1; }
      else if (v[j] < v[j-1] && v[j] < v[j+1]) { if (random() % 3 == 0) sig[j] = v[j] + 1; }
    }
    if (!crookedGen(rho, sig, n)) { printf("  mix round %ld: NOT faithful\n", it); continue; }
    scan(&cm, n, "mix", (int)it);
  }

  /* (d) heavy mixtures: rate 1/2, and the total mixture */
  for (long it = 0; it < rounds; it++) {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) { if (random() % 2 == 0) rho[j] = v[j] - 1; }
      else if (v[j] < v[j-1] && v[j] < v[j+1]) { if (random() % 2 == 0) sig[j] = v[j] + 1; }
    }
    if (!crookedGen(rho, sig, n)) { printf("  heavy round %ld: NOT faithful\n", it); continue; }
    scan(&ch, n, "heavy", (int)it);
  }
  {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) rho[j] = v[j] - 1;
      else if (v[j] < v[j-1] && v[j] < v[j+1]) sig[j] = v[j] + 1;
    }
    if (crookedGen(rho, sig, n)) { printf("  the total mixture is faithful\n");
      scan(&ch, n, "total", -1); }
    else printf("  the total mixture is NOT faithful\n");
  }

  /* (e) a random faithful perturbation walk: single-link changes of rho or sig,
   * kept when the pair stays faithful.  This leaves the shaving/filling family
   * altogether: nothing asks the change to sit at a local extremum. */
  {
    static int crho[MAXN], csig[MAXN];
    for (int u = 0; u < n; u++) { crho[u] = v[u]; csig[u] = v[u]; }
    long accepted = 0;
    for (long it = 0; it < walkSteps; it++) {
      int j = 1 + (int)(random() % (n - 2));
      int which = (int)(random() % 2), delta = (random() % 2) ? 1 : -1;
      for (int u = 0; u < n; u++) { rho[u] = crho[u]; sig[u] = csig[u]; }
      if (which == 0) rho[j] += delta; else sig[j] += delta;
      if (rho[j] > sig[j] || sig[j] > rho[j] + 1) continue;
      if (rho[j] < 0 || sig[j] > 9) continue;
      if (!crookedGen(rho, sig, n)) continue;
      accepted++;
      for (int u = 0; u < n; u++) { crho[u] = rho[u]; csig[u] = sig[u]; }
      scan(&cw, n, "walk", (int)accepted);
    }
    printf("  random perturbation walk: %ld steps tried, %ld accepted\n", walkSteps, accepted);
  }
}

int main(int argc, char **argv) {
  long rounds = (argc > 1) ? atol(argv[1]) : 40;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 50u;
  long walkSteps = (argc > 3) ? atol(argv[3]) : 200;
  if (argc > 4) crookCap = atoi(argv[4]);
  srandom(seed);
  auditFile = fopen("census-batch52-audit.txt", "w");
  auditWant = 14;
  printf("census-batch52: the crossing argument, and the branch L+5 by reflection of arms.\n");
  printf("rounds=%ld seed=%u walk-steps=%ld crook-cap=%d\n", rounds, seed, walkSteps, crookCap);
  zero(&ct); zero(&cs); zero(&cf); zero(&cm); zero(&ch); zero(&cw);

  Path p = bpath(0, 9);
  runChain(p.n, p.v, rounds, walkSteps, "bing 0 9");
  Path q = bpath(9, 0);
  runChain(q.n, q.v, rounds, walkSteps, "bing 9 0");

  printf("\n================ totals over both base chains ================\n");
  report("the thin chains", &ct);
  report("single shavings", &cs);
  report("single fills", &cf);
  report("random mixtures (rate 1/3)", &cm);
  report("heavy mixtures (rate 1/2, and the total mixture)", &ch);
  report("random faithful perturbation walks", &cw);

  {
    Cnt all; zero(&all);
    const Cnt *cc[6] = {&ct, &cs, &cf, &cm, &ch, &cw};
    long *dst = (long *)&all;
    for (int s = 0; s < 6; s++) {
      const long *src = (const long *)cc[s];
      for (unsigned u = 0; u < sizeof(Cnt) / sizeof(long); u++) dst[u] += src[u];
    }
    report("EVERYTHING", &all);
  }
  if (auditFile) fclose(auditFile);
  free(p.v); free(q.v);
  return 0;
}
