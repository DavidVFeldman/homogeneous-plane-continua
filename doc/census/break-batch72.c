/* break-batch72.c -- batch 72 §2.3.  Break the valley.
 *
 * Batch 71's construction machinery, aimed at Valley3BeforeNine on the running
 * arm instead of at the distance.  Two attacks, from two families of seed:
 *
 *   A. from the 64 high-run crossings stored by census-batch71.c
 *      (seeds-batch71.txt): edit the *running arm's approach* -- the stretch
 *      between the basepoint and its first ascent to L+9 -- so as to remove
 *      every time at L+3 before the ascent, or to remove the peak, or to push
 *      the valley to within five steps of the ascent, while keeping the pair
 *      faithful, the band [L, L+9], LowAt on both arms, the crossing, and the
 *      high run.
 *
 *   B. from the 96 basepoints of the branch at which the running arm already
 *      fails Valley3BeforeNine (seeds-batch72.txt, sampled by census-batch72.c):
 *      edit the *partner* so that the basepoint becomes a crossing.  The census
 *      says every one of the 187 132 failing basepoints has both arms `w8`; a
 *      running arm is always a w8 arm (HPC/Fold/Valley72.lean), so the only way
 *      to a crossing is to take w8 (and wb, and w3) off the partner.
 *
 * The edits:
 *   cut     -- delete a there-and-back detour: two indices p < q of equal level,
 *              with the material between them removed.  This is the inverse of
 *              batch 71's surviving `stretch` edit, and is the one edit that can
 *              *remove* a level pattern without lifting a link out of the band.
 *   stretch -- batch 71's edit: reflect a stretch and re-append it.
 *   raise   -- batch 71's edit: lift a local minimum by one.
 *   splice  -- insert bpath(v, lo) followed by bpath(lo, v) at a link of level v:
 *              a whole crooked descent of the sub-band, the downward form of
 *              batch 71's `band` edit.
 *
 * Every edited pair is re-tested for IsCrookedIvF from scratch and re-scanned
 * from scratch for the band, the basepoint, LowAt, the trichotomy, the high run
 * and Valley3BeforeNine; nothing is inherited from the seed.
 *
 * Usage: break-batch72 [seed]
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

/* ------------------------------------------------------------- the seeds -- */

#define MAXSEED 128
typedef struct { int n, i, gSide; int rho[MAXN], sig[MAXN]; } Seed;
static Seed seeds[MAXSEED];
static int nSeeds = 0;

static int readSeeds(const char *name, int withMasks) {
  FILE *fp = fopen(name, "r");
  if (!fp) { printf("  (no %s)\n", name); return 0; }
  long cnt = 0;
  if (fscanf(fp, "%ld", &cnt) != 1) { fclose(fp); return 0; }
  int made = 0;
  for (long q = 0; q < cnt; q++) {
    int n, i, gs, a, b, c;
    if (withMasks) {
      if (fscanf(fp, "%d %d %d %d %d %d", &n, &i, &gs, &a, &b, &c) != 6) break;
    } else {
      if (fscanf(fp, "%d %d %d", &n, &i, &gs) != 3) break;
    }
    if (nSeeds >= MAXSEED || n >= MAXN) {
      for (int t = 0; t < 2 * n; t++) { int x; if (fscanf(fp, "%d", &x) != 1) break; }
      continue;
    }
    Seed *S = &seeds[nSeeds];
    S->n = n; S->i = i; S->gSide = gs;
    for (int t = 0; t < n; t++) if (fscanf(fp, "%d", &S->rho[t]) != 1) break;
    for (int t = 0; t < n; t++) if (fscanf(fp, "%d", &S->sig[t]) != 1) break;
    nSeeds++; made++;
  }
  fclose(fp);
  printf("  %s: %d seeds read\n", name, made);
  return made;
}

/* --------------------------------------------------------------- the edits */

static int eRho[MAXN], eSig[MAXN];

/* cut: delete the material strictly between p and q, which carry the same
   levels -- the inverse of batch 71's `stretch`.  Returns the new length. */
static int editCut(const Seed *S, int p, int q, int *newI) {
  if (!(p < q && q < S->n)) return 0;
  if (S->rho[p] != S->rho[q] || S->sig[p] != S->sig[q]) return 0;
  int m = 0;
  for (int t = 0; t <= p; t++) { eRho[m] = S->rho[t]; eSig[m] = S->sig[t]; m++; }
  for (int t = q + 1; t < S->n; t++) { eRho[m] = S->rho[t]; eSig[m] = S->sig[t]; m++; }
  int cutLen = q - p;
  *newI = (S->i <= p) ? S->i : ((S->i > q) ? S->i - cutLen : -1);
  return (*newI < 0) ? 0 : m;
}

/* stretch: reflect the stretch [p, q] and re-append it after q */
static int editStretch(const Seed *S, int p, int q, int *newI) {
  if (!(p < q && q < S->n)) return 0;
  int add = 2 * (q - p);
  if (S->n + add >= MAXN) return 0;
  int m = 0;
  for (int t = 0; t <= q; t++) { eRho[m] = S->rho[t]; eSig[m] = S->sig[t]; m++; }
  for (int t = q - 1; t >= p; t--) { eRho[m] = S->rho[t]; eSig[m] = S->sig[t]; m++; }
  for (int t = p + 1; t <= q; t++) { eRho[m] = S->rho[t]; eSig[m] = S->sig[t]; m++; }
  *newI = (S->i <= q) ? S->i : S->i + add;
  return m;
}

/* raise: lift a local minimum of rho by one */
static int editRaise(const Seed *S, int t, int *newI) {
  if (t <= 0 || t + 1 >= S->n) return 0;
  if (!(S->rho[t] < S->rho[t-1] && S->rho[t] < S->rho[t+1])) return 0;
  for (int u = 0; u < S->n; u++) { eRho[u] = S->rho[u]; eSig[u] = S->sig[u]; }
  eRho[t] = S->rho[t] + 1;
  if (eSig[t] < eRho[t]) eSig[t] = eRho[t];
  *newI = S->i;
  return S->n;
}

/* splice: at a thin link of level v, insert bpath(v, lo) followed by
   bpath(lo, v) -- a whole crooked descent of the sub-band */
static int editSplice(const Seed *S, int p, int lo, int *newI) {
  if (p <= 0 || p + 1 >= S->n) return 0;
  int v = S->rho[p];
  if (S->sig[p] != v) return 0;
  if (lo >= v) return 0;
  Path d = bpath(v, lo), u = bpath(lo, v);
  int add = (d.n - 1) + (u.n - 1);
  if (S->n + add >= MAXN) { free(d.v); free(u.v); return 0; }
  int m = 0;
  for (int t = 0; t <= p; t++) { eRho[m] = S->rho[t]; eSig[m] = S->sig[t]; m++; }
  for (int t = 1; t < d.n; t++) { eRho[m] = d.v[t]; eSig[m] = d.v[t]; m++; }
  for (int t = 1; t < u.n; t++) { eRho[m] = u.v[t]; eSig[m] = u.v[t]; m++; }
  for (int t = p + 1; t < S->n; t++) { eRho[m] = S->rho[t]; eSig[m] = S->sig[t]; m++; }
  free(d.v); free(u.v);
  *newI = (S->i <= p) ? S->i : S->i + add;
  return m;
}

/* --------------------------------------------------------------- the runs - */

static long triedA[4], faithA[4], crossA[4], highA[4], winA[4];
static long triedB[4], faithB[4], crossB[4], highB[4], winB[4];
static const char *editName[4] = { "cut", "stretch", "raise", "splice" };
static int hits = 0;

static void tally(int attack, int fam2, const Verdict *V) {
  long *tr = attack ? triedB : triedA, *fa = attack ? faithB : faithA;
  long *cr = attack ? crossB : crossA, *hi = attack ? highB : highA;
  long *wi = attack ? winB : winA;
  tr[fam2]++;
  if (V->faithful) fa[fam2]++;
  if (V->cross) cr[fam2]++;
  if (V->high) hi[fam2]++;
  if (V->ok && V->valleyFails) wi[fam2]++;
}

static void report(int attack, int fam2, const Verdict *V) {
  if (!(V->ok && V->valleyFails)) return;
  hits++;
  printf("\n  *** A CROSSING WHOSE RUNNING ARM FAILS Valley3BeforeNine ***\n");
  printf("      attack %c, edit %s, n=%d basepoint=%d running side=%c ascent=%d\n",
         attack ? 'B' : 'A', editName[fam2], V->n, V->i, V->gSide ? 'G' : 'T', V->e);
  printf("      a walk of the four-leg family serves both arms: %s;"
         " both arms satisfy w72: %s\n", V->served ? "yes" : "NO", V->w72Both ? "yes" : "no");
  if (hits == 1) {
    FILE *fp = fopen("witness-batch72-break.txt", "w");
    if (fp) {
      fprintf(fp, "%d %d %d\n", V->n, V->i, V->gSide);
      for (int t = 0; t < V->n; t++) fprintf(fp, "%d%c", rho[t], t + 1 == V->n ? '\n' : ' ');
      for (int t = 0; t < V->n; t++) fprintf(fp, "%d%c", sig[t], t + 1 == V->n ? '\n' : ' ');
      fclose(fp);
      printf("      stored as witness-batch72-break.txt\n");
    }
  }
}

static void tryEdited(int attack, int fam2, int m, int newI, int wantSide) {
  if (m <= 0) return;
  memcpy(rho, eRho, sizeof(int) * (size_t)m);
  memcpy(sig, eSig, sizeof(int) * (size_t)m);
  Verdict V = examine(m, newI, wantSide);
  tally(attack, fam2, &V);
  report(attack, fam2, &V);
}

int main(int argc, char **argv) {
  unsigned s = (argc > 1) ? (unsigned)atoi(argv[1]) : 72u;
  srandom(s);
  buildFamily();
  printf("break-batch72: break the valley at L + 3.  seed=%u\n", s);
  printf("the four-leg family: %d walks\n\n", famN);

  /* ---------------- attack A: the running arm's approach, at a crossing ---- */
  printf("---- attack A: edit the running arm's approach at a high-run crossing ----\n");
  printf("  the edits are aimed at the valley: cuts that bracket it, the raise of the\n"
         "  valley link itself and of its neighbours, splices and stretches placed just\n"
         "  before it and just after it.\n");
  nSeeds = 0;
  readSeeds("seeds-batch71.txt", 0);
  int nA = nSeeds;
  for (int q = 0; q < nA; q++) {
    Seed *S = &seeds[q];
    memcpy(rho, S->rho, sizeof(int) * (size_t)S->n);
    memcpy(sig, S->sig, sizeof(int) * (size_t)S->n);
    Verdict V0 = examine(S->n, S->i, S->gSide);
    if (!V0.ok) continue;
    int dir = S->gSide ? 1 : -1;
    int e = V0.e;
    int mX = S->gSide ? S->n - S->i : S->i + 1;
    int X[MAXN];
    for (int d = 0; d < mX; d++) X[d] = S->rho[S->i + dir * d];
    int vj = -1, vk = -1;
    if (!valley3BeforeNine(X, mX, &vj, &vk)) continue;   /* it already fails: not a seed */
    /* the valley in chain coordinates */
    int cV = S->i + dir * vk;
    /* cut: bracket the valley, in chain order */
    for (int a = 1; a <= 60; a++) {
      for (int b = 1; b <= 60; b++) {
        int p = (dir > 0) ? cV - a : cV - b;
        int r = (dir > 0) ? cV + b : cV + a;
        if (p < 0 || r >= S->n) continue;
        int newI, m = editCut(S, p, r, &newI);
        tryEdited(0, 0, m, newI, S->gSide);
      }
    }
    /* raise: the valley link and its neighbours */
    for (int d = -3; d <= 3; d++) {
      int newI, m = editRaise(S, cV + d, &newI);
      tryEdited(0, 2, m, newI, S->gSide);
    }
    /* stretch and splice, placed on either side of the valley */
    for (int d = -40; d <= 40; d += 8) {
      int p = cV + d;
      if (p <= 0 || p + 2 >= S->n) continue;
      for (int r = p + 4; r <= p + 40; r += 12) {
        int newI, m = editStretch(S, p, r, &newI);
        tryEdited(0, 1, m, newI, S->gSide);
      }
      for (int lv = 0; lv <= 3; lv++) {
        int newI, m = editSplice(S, p, lv, &newI);
        tryEdited(0, 3, m, newI, S->gSide);
      }
    }
  }

  /* ---------------- attack B: the partner, at a failing basepoint --------- */
  printf("\n---- attack B: edit the partner at a basepoint whose running arm already"
         " fails ----\n");
  printf("  the edits are aimed at the partner's w8 sentence, which is what a crossing\n"
         "  needs taken off it: cuts that remove its first high excursion, splices that\n"
         "  put a descent of the sub-band before that excursion, raises and stretches.\n");
  nSeeds = 0;
  readSeeds("seeds-batch72.txt", 1);
  int nB = nSeeds;
  for (int q = 0; q < nB; q++) {
    Seed *S = &seeds[q];
    int dir = S->gSide ? 1 : -1;               /* the running arm's direction */
    int pdir = -dir;                           /* the partner's */
    int mY = (pdir > 0) ? S->n - S->i : S->i + 1;
    if (mY < 12) continue;
    /* the partner's first time at 7 or above, at arm index four or more */
    int t1 = -1;
    for (int d = 4; d < mY; d++) {
      int c = S->i + pdir * d;
      if (c < 0 || c >= S->n) break;
      if (S->rho[c] >= 7) { t1 = d; break; }
    }
    int cT = (t1 >= 0) ? S->i + pdir * t1 : S->i + pdir * (mY / 2);
    /* cut: bracket the first high excursion */
    for (int a = 1; a <= 60; a++)
      for (int b = 1; b <= 60; b++) {
        int p = cT - a, r = cT + b;
        if (p < 0 || r >= S->n) continue;
        int newI, m = editCut(S, p, r, &newI);
        tryEdited(1, 0, m, newI, S->gSide);
      }
    /* splice a descent of the sub-band before the first high excursion, and
       stretch and raise around it */
    for (int d = -40; d <= 40; d += 8) {
      int p = cT + d;
      if (p <= 0 || p + 2 >= S->n) continue;
      for (int lv = 0; lv <= 3; lv++) {
        int newI, m = editSplice(S, p, lv, &newI);
        tryEdited(1, 3, m, newI, S->gSide);
      }
      for (int r = p + 4; r <= p + 40; r += 12) {
        int newI, m = editStretch(S, p, r, &newI);
        tryEdited(1, 1, m, newI, S->gSide);
      }
      int newI, m = editRaise(S, p, &newI);
      tryEdited(1, 2, m, newI, S->gSide);
    }
  }

  printf("\n================ the outcome ================\n");
  printf("  attack A (the running arm's approach at a high-run crossing)\n");
  printf("  edit      tried   faithful   still a crossing   still a high run   breaks it\n");
  for (int f = 0; f < 4; f++)
    printf("  %-8s %7ld %10ld %18ld %18ld %11ld\n", editName[f], triedA[f], faithA[f],
           crossA[f], highA[f], winA[f]);
  printf("\n  attack B (the partner at a basepoint whose running arm already fails)\n");
  printf("  edit      tried   faithful   still a crossing   still a high run   breaks it\n");
  for (int f = 0; f < 4; f++)
    printf("  %-8s %7ld %10ld %18ld %18ld %11ld\n", editName[f], triedB[f], faithB[f],
           crossB[f], highB[f], winB[f]);
  printf("\n  crossings whose running arm fails Valley3BeforeNine, found: %d\n", hits);
  printf("  (every edited pair is re-tested for IsCrookedIvF and re-scanned from scratch\n"
         "   for the band, the basepoint, LowAt, the trichotomy, the high run and\n"
         "   Valley3BeforeNine; nothing is inherited from the seed.)\n");
  return 0;
}
