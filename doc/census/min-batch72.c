/* min-batch72.c -- batch 72: the shortest window of the branch counterexample.
 *
 * census-batch72.c stores, in witness-batch72-c2.txt, a faithful pair with a
 * basepoint of the branch L+5 -- LowAt on both arms -- whose forward arm runs
 * high and fails Valley3BeforeNine, equivalently fails Ceil72.  This program
 * trims that pair to the shortest window ending at the same place that still
 * carries every hypothesis and still fails, so that the Lean kernel can check
 * the whole verdict.  The window is written to witness-batch72-min.txt.
 *
 * Usage: min-batch72
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXLEV 32
#define MAXN 6144

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

static int meetTab[MAXLEV][MAXN + 1];

/* IsCrookedIvF, copied unchanged from census-batch71.c */
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

/* ------------------------------------------------------- the predicates --- */

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

static int firstNine(const int *f, int m) {
  for (int d = 0; d < m; d++) if (f[d] >= 9) return d;
  return -1;
}

static int runsHigh(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] >= 9) return 1;
    if (f[d] <= 2) return 0;
  }
  return 0;
}

/* Valley3BeforeNine, by its own definition */
static int valley3BeforeNine(const int *f, int m, int *pj, int *pk) {
  int e = -1;
  for (int d = 0; d < m; d++) if (f[d] >= 9) { e = d; break; }
  int lim = (e < 0) ? m - 1 : e - 6;
  int peak = -1;
  for (int k = 0; k <= lim && k < m; k++) {
    for (int j = (peak < 0 ? 3 : peak + 1); j + 5 <= k; j++)
      if (j < m && f[j] >= 6) { if (peak < 0) peak = j; }
    if (f[k] <= 3 && peak >= 0 && peak + 5 <= k) {
      if (pj) *pj = peak; if (pk) *pk = k; return 1;
    }
  }
  return 0;
}

/* the four-leg family and the folding dynamic program, as in census-batch71.c */
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
typedef struct { int st, a, b, c, e; } Fam;
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
        fam[famN].st = st; fam[famN].a = a; fam[famN].b = b; fam[famN].c = c;
        fam[famN].e = e; famN++;
        int rst = 9 - st, ra = 9 - a, rb = 9 - b, rc = 9 - c, re = 9 - e;
        int w2[MAXW]; int wl2 = buildWalk4(w2, rst, ra, rb, rc, re);
        if (wl2 < 0 || famN >= MAXFAM) continue;
        fam[famN].st = rst; fam[famN].a = ra; fam[famN].b = rb; fam[famN].c = rc;
        fam[famN].e = re; famN++;
      }
}
static int famServes(const int *g, int mg, const int *t, int mt) {
  int w[MAXW];
  for (int q = 0; q < famN; q++) {
    int wl = buildWalk4(w, fam[q].st, fam[q].a, fam[q].b, fam[q].c, fam[q].e);
    if (wl < 0) continue;
    if (folds(g, mg, w, wl) && folds(t, mt, w, wl)) return q;
  }
  return -1;
}

/* --------------------------------------------------------------- the test - */

static int rho[MAXN], sig[MAXN];
static int armG[MAXN], armT[MAXN], gG[MAXN], gT[MAXN];

typedef struct {
  int ok;            /* the edited pair passed every structural test */
  int faithful, band, base, low, cross, high, valleyFails, served, w72Both;
  int e, n, i, gSide;
} Verdict;

static Verdict examine(int n, int i, int wantSide) {
  Verdict V; memset(&V, 0, sizeof V);
  V.n = n; V.i = i; V.gSide = wantSide;
  if (n < 30 || n >= MAXN) return V;
  if (i <= 0 || i >= n - 1) return V;
  if (!crookedGen(rho, sig, n)) return V;
  V.faithful = 1;
  int lo = rho[0], hi = rho[0];
  for (int t = 0; t < n; t++) { if (rho[t] < lo) lo = rho[t]; if (rho[t] > hi) hi = rho[t]; }
  if (lo != 0 || hi != 9) return V;
  V.band = 1;
  if (rho[i] != 5) return V;
  V.base = 1;
  int mg = n - i, mt = i + 1;
  for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
  for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
  if (!(lowAt(armG, mg) && lowAt(armT, mt))) return V;
  V.low = 1;
  reflArm(armG, mg, gG); reflArm(armT, mt, gT);
  int tG = 0, tT = 0;
  if (landLeg4(gG, mg, 6, 2, 4)) tG |= 1;
  if (landLeg4(armG, mg, 8, 1, 5)) tG |= 2;
  if (landLeg4(gG, mg, 6, 1, 4)) tG |= 4;
  if (landLeg4(gT, mt, 6, 2, 4)) tT |= 1;
  if (landLeg4(armT, mt, 8, 1, 5)) tT |= 2;
  if (landLeg4(gT, mt, 6, 1, 4)) tT |= 4;
  if (tG & tT) return V;
  V.cross = 1;
  const int *X = wantSide ? armG : armT;
  int mX = wantSide ? mg : mt;
  if (!runsHigh(X, mX)) return V;
  V.high = 1;
  V.e = firstNine(X, mX);
  if (!valley3BeforeNine(X, mX, NULL, NULL)) V.valleyFails = 1;
  V.served = famServes(armG, mg, armT, mt) >= 0;
  V.w72Both = landLeg4(armG, mg, 7, 2, 5) && landLeg4(armT, mt, 7, 2, 5);
  V.ok = 1;
  return V;
}

/* a weaker examination, for the B attack: how close the edit came */
static void note(const Verdict *V, long *cFaith, long *cBand, long *cBase, long *cLow,
                 long *cCross, long *cHigh, long *cWin) {
  if (V->faithful) (*cFaith)++;
  if (V->band) (*cBand)++;
  if (V->base) (*cBase)++;
  if (V->low) (*cLow)++;
  if (V->cross) (*cCross)++;
  if (V->high) (*cHigh)++;
  if (V->ok && V->valleyFails) (*cWin)++;
}


static int wRho[MAXN], wSig[MAXN];

int main(void) {
  buildFamily();
  FILE *fp = fopen("witness-batch72-c2.txt", "r");
  if (!fp) { printf("no witness-batch72-c2.txt\n"); return 1; }
  int n, i0, gSide;
  if (fscanf(fp, "%d %d %d", &n, &i0, &gSide) != 3) return 1;
  for (int t = 0; t < n; t++) if (fscanf(fp, "%d", &wRho[t]) != 1) return 1;
  for (int t = 0; t < n; t++) if (fscanf(fp, "%d", &wSig[t]) != 1) return 1;
  fclose(fp);
  printf("min-batch72: the stored pair has %d links, basepoint %d, running side %c\n",
         n, i0, gSide ? 'G' : 'T');
  int bestA = -1, bestB = -1;
  /* the running arm is the forward arm: its links are i0 .. n-1, so only the
     front of the chain may be trimmed; the tail is trimmed only past the arm's
     own end, which here is the end of the chain */
  for (int a = i0 - 1; a >= 0 && bestA < 0; a--) {
    int m = n - a, ii = i0 - a;
    for (int t = 0; t < m; t++) { rho[t] = wRho[a + t]; sig[t] = wSig[a + t]; }
    if (!crookedGen(rho, sig, m)) continue;
    int lo = rho[ii] - 5, hi = sig[0], mn = rho[0];
    for (int t = 0; t < m; t++) { if (rho[t] < mn) mn = rho[t]; if (sig[t] > hi) hi = sig[t]; }
    if (mn < lo || hi > lo + 9) continue;   /* the band [L, L+9] with L = rho i - 5 */
    int mg = m - ii, mt = ii + 1;
    for (int d = 0; d < mg; d++) armG[d] = rho[ii + d] - lo;
    for (int d = 0; d < mt; d++) armT[d] = rho[ii - d] - lo;
    if (!(lowAt(armG, mg) && lowAt(armT, mt))) continue;
    if (!runsHigh(armG, mg)) continue;
    if (valley3BeforeNine(armG, mg, NULL, NULL)) continue;
    bestA = a; bestB = n - 1;
    printf("  the shortest window: links %d..%d (%d links), basepoint %d, floor L = %d,\n"
           "  band [%d, %d]; the forward arm has %d times, its first ascent at %d\n",
           a, n - 1, m, ii, lo, lo, hi, mg, firstNine(armG, mg));
    printf("  Valley3BeforeNine on the running arm: FAILS;  LowAt on both arms: yes\n");
    int tG = 0, tT = 0;
    reflArm(armG, mg, gG); reflArm(armT, mt, gT);
    if (landLeg4(gG, mg, 6, 2, 4)) tG |= 1;
    if (landLeg4(armG, mg, 8, 1, 5)) tG |= 2;
    if (landLeg4(gG, mg, 6, 1, 4)) tG |= 4;
    if (landLeg4(gT, mt, 6, 2, 4)) tT |= 1;
    if (landLeg4(armT, mt, 8, 1, 5)) tT |= 2;
    if (landLeg4(gT, mt, 6, 1, 4)) tT |= 4;
    printf("  the trichotomy: forward %c%c%c, backward %c%c%c; shared: %s\n",
           (tG&1)?'3':'-', (tG&2)?'8':'-', (tG&4)?'b':'-',
           (tT&1)?'3':'-', (tT&2)?'8':'-', (tT&4)?'b':'-',
           (tG & tT) ? "yes -- NOT a crossing" : "none -- a crossing");
    printf("  a walk of the four-leg family serves both arms: %s\n",
           famServes(armG, mg, armT, mt) >= 0 ? "yes" : "no");
    FILE *out = fopen("witness-batch72-min.txt", "w");
    if (out) {
      fprintf(out, "%d %d %d\n", m, ii, 1);
      for (int t = 0; t < m; t++) fprintf(out, "%d%c", rho[t] - lo, t + 1 == m ? '\n' : ' ');
      for (int t = 0; t < m; t++) fprintf(out, "%d%c", sig[t] - lo, t + 1 == m ? '\n' : ' ');
      fclose(out);
      printf("  written to witness-batch72-min.txt (shifted so the floor is 0)\n");
    }
    printf("  rho:");
    for (int t = 0; t < m; t++) printf(" %d", rho[t] - lo);
    printf("\n  sig:");
    for (int t = 0; t < m; t++) printf(" %d", sig[t] - lo);
    printf("\n");
  }
  if (bestA < 0) printf("  no window of the stored pair carries the whole verdict\n");
  (void)bestB;
  return 0;
}
