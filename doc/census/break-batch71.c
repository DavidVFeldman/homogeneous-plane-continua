/* break-batch71.c -- batch 71, question 2.4.  Break the distance.
 *
 * The corpus never leaves 56..65: at every one of the 229 high-run crossings of
 * census-batch71.c the nearest time of the pair at L+2 or below lies 56 to 65
 * steps before the basepoint, against the bound 67 the reading of NearLowT
 * needs.  The commission asks for the strongest test available -- a targeted
 * construction rather than more sampling: a faithful pair, in the general model,
 * with a high-run crossing whose nearest time at L+2 or below is more than 67
 * steps before the basepoint.
 *
 * The seeds are the pairs census-batch71.c stored, one per distinct
 * configuration of a high-run crossing (seeds-batch71.txt).  Three families of
 * edit are applied to each, all of them lengthening the partner's approach to
 * the basepoint or removing the low time that ends it:
 *
 *   raise    every local minimum at L+2 or below in the approach is lifted by
 *            one level (thin, and then with the link widened);
 *   splice   a detour that never descends below L+3 is spliced into the
 *            approach at a link carrying v: the Bing block bpath(v,hi) followed
 *            by bpath(hi,v), for hi = 6,7,8 (and, as the kind `band`, hi = 9 --
 *            a whole crooked chain of the sub-band, the longest addition that
 *            introduces no time at L+2 or below);
 *   stretch  a stretch of the approach that stays at L+3 or above is reflected
 *            and re-appended, doubling it.
 *
 * Every edited pair is re-tested for faithfulness by crookedGen -- IsCrookedIvF
 * of HPC/Fold/Faithful.lean written out -- and every basepoint of the edited
 * pair is then re-scanned from scratch for high-run crossings, with LowAt,
 * Leg4Land and DeepFirst2 read by their own definitions, exactly as in
 * census-batch71.c.  Nothing is inherited from the seed.
 *
 * At every high-run crossing of every faithful edit the program measures, by
 * their own definitions: the three distances of NearLowBandT (to the nearest
 * time at L+2 or below, at L+1 or below, and at the floor, on the partner's
 * side of the basepoint) against the bounds 67, 166 and 405; the ceiling clause
 * Ceil72 on both arms; the landmark sentence of w72 on both arms; and whether
 * some walk of the four-leg family serves both arms.  The extreme break -- the
 * one whose nearest low time is furthest from the basepoint -- is stored whole
 * in witness-batch71.txt for the independent re-check check71.py.
 *
 * Usage: break-batch71 [seeds file]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

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


/* ------------------------------------------------------------ the seeds ---- */

#define MAXSEED 64
typedef struct { int n, i, gSide; int rho[MAXN], sig[MAXN]; } Seed;
static Seed seeds[MAXSEED];
static long nSeeds = 0;

static void loadSeeds(const char *path) {
  FILE *fp = fopen(path, "r");
  if (!fp) { printf("  cannot open %s\n", path); return; }
  long k = 0;
  if (fscanf(fp, "%ld", &k) != 1) { fclose(fp); return; }
  for (long q = 0; q < k && q < MAXSEED; q++) {
    Seed *S = &seeds[nSeeds];
    if (fscanf(fp, "%d %d %d", &S->n, &S->i, &S->gSide) != 3) break;
    if (S->n >= MAXN) break;
    for (int t = 0; t < S->n; t++) if (fscanf(fp, "%d", &S->rho[t]) != 1) { fclose(fp); return; }
    for (int t = 0; t < S->n; t++) if (fscanf(fp, "%d", &S->sig[t]) != 1) { fclose(fp); return; }
    nSeeds++;
  }
  fclose(fp);
}

/* -------------------------------------------------------------- the scan ---- */

static long brkTried = 0, brkFaithful = 0, brkWithCross = 0, brkBest = -1, brkBreaks = 0;
static long kindTried[4], kindFaithful[4], kindCross[4], kindBest[4];
static const char *kindName[4] = {"raise", "splice", "stretch", "band"};
static long crookFail = 0, crossFail = 0;
/* what happens at a break */
static long bk2 = 0, bk1 = 0, bk0 = 0, bkBand = 0, bkCeilRun = 0, bkCeilPart = 0;
static long bkW72Both = 0, bkServed = 0, bkNone = 0, bkCases = 0;
static long bkNear1Min = 1 << 30, bkNear1Max = -1, bkNear0Min = 1 << 30, bkNear0Max = -1;
static int bestRho[MAXN], bestSig[MAXN], bestN = 0, bestI = -1, bestSide = 0;
static long bestNear2 = -1, bestNear1 = -1, bestNear0 = -1, bestKind = -1;

/* one high-run crossing of the pair now in rho/sig, measured whole */
static void measure(int n, int i, int gSide, int *X, int mX, int *Y, int mY, int kind) {
  int near2 = -1, near1 = -1, near0 = -1;
  for (int s = 1; s < mY; s++) {
    if (near2 < 0 && Y[s] <= 2) near2 = s;
    if (near1 < 0 && Y[s] <= 1) near1 = s;
    if (near0 < 0 && Y[s] <= 0) near0 = s;
    if (near2 >= 0 && near1 >= 0 && near0 >= 0) break;
  }
  long d2 = (near2 < 0) ? (1 << 20) : near2;
  if (d2 > brkBest) brkBest = d2;
  if (d2 > kindBest[kind]) kindBest[kind] = d2;
  if (d2 <= 67) return;                       /* the distance statement holds here */
  brkBreaks++; bkCases++;
  bk2++;
  if (near1 < 0 || near1 > 166) bk1++;
  if (near0 < 0 || near0 > 405) bk0++;
  if ((near2 >= 0 && near2 <= 67) || (near1 >= 0 && near1 <= 166) ||
      (near0 >= 0 && near0 <= 405)) bkBand++;
  if (near1 >= 0) {
    if (near1 < bkNear1Min) bkNear1Min = near1;
    if (near1 > bkNear1Max) bkNear1Max = near1;
  }
  if (near0 >= 0) {
    if (near0 < bkNear0Min) bkNear0Min = near0;
    if (near0 > bkNear0Max) bkNear0Max = near0;
  }
  if (ceil72Clause(X, mX)) bkCeilRun++;
  if (ceil72Clause(Y, mY)) bkCeilPart++;
  if (landLeg4(X, mX, 7, 2, 5) && landLeg4(Y, mY, 7, 2, 5)) bkW72Both++;
  int served = -1;
  for (int q = 0; q < famN && served < 0; q++)
    if (famFoldsBoth(q, X, mX, Y, mY)) served = q;
  if (served >= 0) bkServed++; else bkNone++;
  if (brkBreaks <= 6 || d2 > bestNear2)
    printf("  *** BREAK [%s] n=%4d i=%4d w8 side=%c  nearest at 2: %3d (bound 67),"
           " at 1: %4d (166), at 0: %4d (405);  Ceil72 running=%d partner=%d;"
           " w72 both=%d; a walk serves both=%d\n",
           kindName[kind], n, i, gSide ? 'G' : 'T', near2, near1, near0,
           ceil72Clause(X, mX), ceil72Clause(Y, mY),
           landLeg4(X, mX, 7, 2, 5) && landLeg4(Y, mY, 7, 2, 5), served >= 0);
  if (d2 > bestNear2) {
    bestNear2 = d2; bestNear1 = near1; bestNear0 = near0; bestKind = kind;
    bestN = n; bestI = i; bestSide = gSide;
    memcpy(bestRho, rho, sizeof(int) * (size_t)n);
    memcpy(bestSig, sig, sizeof(int) * (size_t)n);
  }
}

/* every high-run crossing of the pair now in rho/sig */
static int scanPairForBreaks(int n, int kind) {
  int any = 0;
  for (int i = 0; i < n; i++) {
    if (rho[i] != 5) continue;
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
    for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
    if (!(lowAt(armG, mg) && lowAt(armT, mt))) continue;
    reflArm(armG, mg, gG);
    reflArm(armT, mt, gT);
    int tG = 0, tT = 0;
    if (landLeg4(gG, mg, 6, 2, 4)) tG |= 1;
    if (landLeg4(armG, mg, 8, 1, 5)) tG |= 2;
    if (landLeg4(gG, mg, 6, 1, 4)) tG |= 4;
    if (landLeg4(gT, mt, 6, 2, 4)) tT |= 1;
    if (landLeg4(armT, mt, 8, 1, 5)) tT |= 2;
    if (landLeg4(gT, mt, 6, 1, 4)) tT |= 4;
    if (tG & tT) continue;
    int gHas8 = (tG & 2) != 0, tHas8 = (tT & 2) != 0;
    if (gHas8 == tHas8) continue;
    if (gHas8) {
      if (deepFirst2(armG, mg)) continue;
      any = 1;
      measure(n, i, 1, armG, mg, armT, mt, kind);
    } else {
      if (deepFirst2(armT, mt)) continue;
      any = 1;
      measure(n, i, 0, armT, mt, armG, mg, kind);
    }
  }
  return any;
}

static int brkRho[MAXN], brkSig[MAXN];

static void brkTry(int n, int kind) {
  if (n < 30 || n >= MAXN) return;
  brkTried++; kindTried[kind]++;
  for (int u = 0; u < n; u++) { rho[u] = brkRho[u]; sig[u] = brkSig[u]; }
  if (!crookedGen(rho, sig, n)) { crookFail++; return; }
  brkFaithful++; kindFaithful[kind]++;
  if (scanPairForBreaks(n, kind)) { brkWithCross++; kindCross[kind]++; }
  else crossFail++;
}

/* ----------------------------------------------------------- the edits ---- */

static void spliceAt(const Seed *S, int p, const int *D, int dl, int kind) {
  int n0 = S->n;
  if (n0 + dl - 1 >= MAXN) return;
  for (int u = 0; u <= p; u++) { brkRho[u] = S->rho[u]; brkSig[u] = S->sig[u]; }
  int at = p;
  for (int u = 1; u < dl; u++) { at++; brkRho[at] = D[u]; brkSig[at] = D[u]; }
  for (int u = p + 1; u < n0; u++) { at++; brkRho[at] = S->rho[u]; brkSig[at] = S->sig[u]; }
  brkTry(at + 1, kind);
}

static int detour[MAXN];

static int buildDetour(int v, int hi) {
  Path up = bpath(v, hi), dn = bpath(hi, v);
  int dl = 0;
  for (int u = 0; u < up.n; u++) detour[dl++] = up.v[u];
  for (int u = 1; u < dn.n; u++) detour[dl++] = dn.v[u];
  free(up.v); free(dn.v);
  return dl;
}

int main(int argc, char **argv) {
  const char *path = (argc > 1) ? argv[1] : "seeds-batch71.txt";
  buildFamily();
  printf("break-batch71: the construction attempt of batch 71, question 2.4.\n");
  loadSeeds(path);
  printf("  seeds read from %s: %ld\n", path, nSeeds);
  long lenMin = 1 << 30, lenMax = -1;
  for (long q = 0; q < nSeeds; q++) {
    if (seeds[q].n < lenMin) lenMin = seeds[q].n;
    if (seeds[q].n > lenMax) lenMax = seeds[q].n;
  }
  printf("  seed lengths: %ld to %ld links\n", lenMin, lenMax);
  printf("  the four-leg family: %d walks\n", famN);
  printf("  every edit is re-tested for faithfulness and re-scanned from scratch.\n\n");

  for (long q = 0; q < nSeeds; q++) {
    Seed *S = &seeds[q];
    int n0 = S->n, i0 = S->i, dir = S->gSide ? -1 : 1;
    for (int w = 1; w <= 400; w++) {                     /* raise */
      int p = i0 + dir * w;
      if (p <= 0 || p >= n0 - 1) break;
      if (S->rho[p] > 2) continue;
      if (!(S->rho[p] <= S->rho[p-1] && S->rho[p] <= S->rho[p+1])) continue;
      for (int u = 0; u < n0; u++) { brkRho[u] = S->rho[u]; brkSig[u] = S->sig[u]; }
      brkRho[p] = S->rho[p] + 1;
      if (brkSig[p] < brkRho[p]) brkSig[p] = brkRho[p];
      brkTry(n0, 0);
      brkSig[p] = brkRho[p] + 1;
      brkTry(n0, 0);
    }
    for (int hi = 6; hi <= 9; hi++) {                    /* splice and band */
      for (int w = 1; w <= 200; w += 5) {
        int p = i0 + dir * w;
        if (p <= 0 || p >= n0 - 1) break;
        int v = S->rho[p];
        if (v < 3 || v >= hi) continue;
        if (S->sig[p] != v) continue;
        int dl = buildDetour(v, hi);
        spliceAt(S, p, detour, dl, hi == 9 ? 3 : 1);
      }
    }
    for (int w = 4; w <= 200; w += 7) {                  /* stretch */
      int p = i0 + dir * w;
      int lo = (dir < 0) ? p : i0, hiE = (dir < 0) ? i0 : p;
      if (lo <= 0 || hiE >= n0 - 1) break;
      int ok = 1;
      for (int t = lo; t <= hiE; t++) if (S->rho[t] < 3) { ok = 0; break; }
      if (!ok) continue;
      int seg = hiE - lo;
      if (seg < 2 || n0 + 2 * seg >= MAXN) continue;
      for (int u = 0; u <= hiE; u++) { brkRho[u] = S->rho[u]; brkSig[u] = S->sig[u]; }
      int at = hiE;
      for (int u = hiE - 1; u >= lo; u--) { at++; brkRho[at] = S->rho[u]; brkSig[at] = S->sig[u]; }
      for (int u = lo + 1; u <= hiE; u++) { at++; brkRho[at] = S->rho[u]; brkSig[at] = S->sig[u]; }
      for (int u = hiE + 1; u < n0; u++) { at++; brkRho[at] = S->rho[u]; brkSig[at] = S->sig[u]; }
      brkTry(at + 1, 2);
    }
  }

  printf("\n================ the result ================\n");
  printf("  edits tried: %ld; faithful: %ld; with a high-run crossing: %ld\n",
         brkTried, brkFaithful, brkWithCross);
  printf("  edits that lost faithfulness: %ld; faithful edits with no high-run crossing"
         " left: %ld\n", crookFail, crossFail);
  for (int k = 0; k < 4; k++)
    printf("    %-8s tried %5ld  faithful %5ld  with a crossing %5ld  largest distance %ld\n",
           kindName[k], kindTried[k], kindFaithful[k], kindCross[k], kindBest[k]);
  printf("  the largest distance to the nearest time at L+2 or below, over every\n"
         "  high-run crossing of every faithful edit: %ld (the bound is 67)\n", brkBest);
  printf("\n  high-run crossings of faithful edits at which the distance statement FAILS:"
         " %ld\n", bkCases);
  if (bkCases) {
    printf("    of them, the L+1 reading also fails (no time at L+1 or below within 166):"
           " %ld\n", bk1);
    printf("    the floor reading also fails (none at the floor within 405): %ld\n", bk0);
    printf("    at least one of the three readings of NearLowBandT still available: %ld\n",
           bkBand);
    printf("    the nearest time at L+1 or below lies in [%ld, %ld]; at the floor in"
           " [%ld, %ld]\n", bkNear1Min, bkNear1Max, bkNear0Min, bkNear0Max);
    printf("    Ceil72 nevertheless holds on the running arm at %ld of %ld, and on the"
           " partner at %ld\n", bkCeilRun, bkCases, bkCeilPart);
    printf("    both arms satisfy the landmark sentence of w72 at %ld of %ld\n",
           bkW72Both, bkCases);
    printf("    some walk of the four-leg family serves both arms at %ld; none does at"
           " %ld\n", bkServed, bkNone);
    printf("\n  the extreme break: a %s edit, %d links, basepoint %d, the w8 side is the"
           " %s arm,\n  nearest time at L+2 or below %ld steps before the basepoint"
           " (at L+1: %ld, at the floor: %ld)\n",
           kindName[bestKind], bestN, bestI, bestSide ? "forward" : "backward",
           bestNear2, bestNear1, bestNear0);
    FILE *fp = fopen("witness-batch71.txt", "w");
    if (fp) {
      fprintf(fp, "%d %d %d\n", bestN, bestI, bestSide);
      for (int t = 0; t < bestN; t++)
        fprintf(fp, "%d%c", bestRho[t], t + 1 == bestN ? '\n' : ' ');
      for (int t = 0; t < bestN; t++)
        fprintf(fp, "%d%c", bestSig[t], t + 1 == bestN ? '\n' : ' ');
      fclose(fp);
      printf("  it is stored whole in witness-batch71.txt, for check71.py\n");
    }
  }
  return 0;
}
