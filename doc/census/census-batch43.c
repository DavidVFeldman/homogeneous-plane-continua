/* Census for batch 43 -- the mixed configuration at span nine.
 *
 * WHAT THIS RANGES OVER.  Every sequence examined here is an *actual* faithful
 * crooked sequence.  It is checked, pair by pair, against the definition
 * `IsCrookedIvF` of HPC/Fold/Faithful.lean in its thin form (sigma = rho, so
 * every link is a point; the adjacency clause is then exactly 1-Lipschitz and
 * the crookedness clause is decidable as written -- see `crookedThin`, which is
 * also run on paths whose status is known, as a check on itself).  No one-arm
 * clause such as CrookUp is used anywhere, and no announcement: the arms are
 * classified by the two exact profile criteria of HPC/Fold/Profile.lean.
 *
 * ON THE BATCH-42 CENSUS.  `census-batch42k.c` declared the mixed class empty
 * over the windows of `bing 0 N`.  It held its arms in buffers of 512 entries
 * and skipped every basepoint with a longer arm (`if (mg > 512 || mt > 512)
 * continue;`), so at N = 9 it saw ten of the 182 basepoints of the branch.  The
 * present program holds 4200 and does not skip.  The mixed class is NOT empty.
 *
 * THE CORPUS.  Three families, each sequence verified crooked before use:
 *   A. windows of `bing 0 N`, N = 9 .. maxN;
 *   B. windows of `bing a b`, 0 <= a, b <= 12, |a-b| >= 9, not already in A;
 *   C. concatenations `bing t0 t1 ++ bing t1 t2 ++ ...` over random turning
 *      sequences in [0, 9], kept only when the concatenation is crooked.
 *  In families A and B the window starts run on a stride of about one
 *  two-hundredth of the length of the source path; every end is then used.
 *
 * WHAT IS COUNTED.  For every window whose range is exactly nine and every
 * basepoint i with v[i] = L+4 or L+5:
 *   lamCrit : before the arm ever drops to L+1 it stands at L+7.  Exact
 *             criterion for the Lambda-walk based at L+3 (peak L+8): by
 *             foldsOnto_lam_iff_profile together with `armG_gap` /`armT_gap`
 *             of HPC/Fold/Timing.lean, which supply the index clause.
 *   veeCrit : before the arm ever rises to L+7 it stands at L+2 at an index at
 *             least four.  Exact criterion for the V-walk based at L+5.
 * At L+5 both are read through the reflection x |-> 2L+9-x.  A pair is MIXED
 * when one arm satisfies only lamCrit and the other only veeCrit: then neither
 * of the two walks serves the pair, and that is the configuration left open at
 * span nine (COMMISSION sec. 2.1).  Mixed pairs are counted over all basepoints
 * at those heights and, separately, over the OPEN BRANCH -- v[i] = L+4 with
 * both arms HighAt (L+1) (L+8), or v[i] = L+5 with both arms LowAt (L+1)(L+8) --
 * which is what `s3_span_nine_except` leaves unserved.
 *
 * WHAT ELSE IS ASKED.  Two further questions, both about what does serve the
 * mixed pairs.  Every branch pair met is tested against the single four-leg
 * walk `L+3, L+6, L+1, L+8` (read through the reflection at the branch L+5);
 * and the set of all walks of up to three turns is intersected, separately over
 * the branch pairs and over the mixed ones, to see what survives.
 *
 * Usage: census-batch43 [maxN] [nRandom] [seed]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef unsigned __int128 u128;
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
        int r = nxtTab[r1 - lo][s + 1];
        if (r >= t) return 0;
        int rp = nxtTab[r2 - lo][r + 1];
        if (rp >= t) return 0;
      }
    }
  }
  return 1;
}

/* ---------------------------------------------------------------- folding */

#define MAXW 127

typedef struct { int c[MAXW + 1]; int len; } Walk;

static void build_walk(const int *ts, int k, Walk *w) {
  w->len = 0;
  w->c[w->len++] = ts[0];
  int cur = ts[0];
  for (int j = 1; j <= k; j++) {
    int tgt = ts[j];
    while (cur != tgt && w->len < MAXW) { cur += (tgt > cur) ? 1 : -1; w->c[w->len++] = cur; }
  }
}

static int folds(const int *f, int m, const Walk *w) {
  u128 one = 1, mask;
  if (abs(f[0] - w->c[0]) > 1) return 0;
  mask = one;
  for (int j = 1; j < m; j++) {
    u128 nm = 0;
    u128 spread = mask | (mask << 1) | (mask >> 1);
    for (int u = 0; u < w->len; u++) {
      if (!((spread >> u) & 1)) continue;
      if (abs(f[j] - w->c[u]) > 1) continue;
      nm |= one << u;
    }
    mask = nm;
    if (!mask) return 0;
  }
  return 1;
}

/* the four-leg walk that serves the mixed pairs of `bing 0 9` */
static Walk w4leg;

/* ------------------------------------------------- the walks of <= 3 turns */

#define MAXCAND 6000

static int candTs[MAXCAND][4], candK[MAXCAND], candAlive[MAXCAND], candAliveMix[MAXCAND];
static Walk candW[MAXCAND];
static int nCand = 0;
static long long candUsedOn = 0, candUsedOnMix = 0;

static void build_candidates(int L, int H) {
  nCand = 0;
  for (int k = 0; k <= 3; k++) {
    int ts[4];
    for (ts[0] = L; ts[0] <= H; ts[0]++) {
      int lo = L + 1, hi = H - 1, span = hi - lo + 1;
      long total = 1; for (int j = 1; j <= k; j++) total *= span;
      for (long code = 0; code < total; code++) {
        long c = code; int bad = 0;
        for (int j = 1; j <= k; j++) { ts[j] = lo + (int)(c % span); c /= span; }
        for (int j = 1; j <= k && !bad; j++) {
          if (ts[j] == ts[j-1]) bad = 1;
          if (j >= 2 && ((ts[j] > ts[j-1]) == (ts[j-1] > ts[j-2]))) bad = 1;
        }
        if (bad || nCand >= MAXCAND) continue;
        candK[nCand] = k;
        for (int j = 0; j <= k; j++) candTs[nCand][j] = ts[j];
        build_walk(ts, k, &candW[nCand]);
        candAlive[nCand] = 1;
        candAliveMix[nCand] = 1;
        nCand++;
      }
    }
  }
}

/* keep only the candidates that serve this pair; returns the number alive */
static int intersect_candidates(const int *g, int mg, const int *t_, int mt) {
  int alive = 0;
  for (int c = 0; c < nCand; c++) {
    if (!candAlive[c]) continue;
    if (folds(g, mg, &candW[c]) && folds(t_, mt, &candW[c])) alive++;
    else candAlive[c] = 0;
  }
  candUsedOn++;
  return alive;
}

/* the same, over the mixed pairs only */
static int intersect_candidates_mix(const int *g, int mg, const int *t_, int mt) {
  int alive = 0;
  for (int c = 0; c < nCand; c++) {
    if (!candAliveMix[c]) continue;
    if (folds(g, mg, &candW[c]) && folds(t_, mt, &candW[c])) alive++;
    else candAliveMix[c] = 0;
  }
  candUsedOnMix++;
  return alive;
}

static int least_turns_of(const int *g, int mg, const int *t_, int mt) {
  int best = -1;
  for (int c = 0; c < nCand; c++)
    if (folds(g, mg, &candW[c]) && folds(t_, mt, &candW[c]))
      if (best < 0 || candK[c] < best) best = candK[c];
  return best;
}

/* ------------------------------------------------- first-occurrence tables */

#define NTH 6
/* 0: <= L+1   1: <= L+2   2: >= L+6   3: >= L+7   4: >= L+8   5: <= L+3 */

static int nxtT[NTH][4300], prvT[NTH][4300];

static int thr(int which, int x, int L) {
  switch (which) {
    case 0: return x <= L + 1;
    case 1: return x <= L + 2;
    case 2: return x >= L + 6;
    case 3: return x >= L + 7;
    case 4: return x >= L + 8;
    default: return x <= L + 3;
  }
}

static void build_tables(const int *v, int len, int L) {
  for (int w = 0; w < NTH; w++) {
    nxtT[w][len] = len;
    for (int j = len - 1; j >= 0; j--) nxtT[w][j] = thr(w, v[j], L) ? j : nxtT[w][j + 1];
    prvT[w][0] = thr(w, v[0], L) ? 0 : -1;
    for (int j = 1; j < len; j++) prvT[w][j] = thr(w, v[j], L) ? j : prvT[w][j - 1];
  }
}

#define INF (1 << 20)
static int fG(int w, int i, int len) { int p = nxtT[w][i]; return p >= len ? INF : p - i; }
static int fGfrom(int w, int i, int s, int len) {
  int st = i + s; if (st >= len) return INF;
  int p = nxtT[w][st]; return p >= len ? INF : p - i;
}
static int fT(int w, int i) { int p = prvT[w][i]; return p < 0 ? INF : i - p; }
static int fTfrom(int w, int i, int s) {
  int st = i - s; if (st < 0) return INF;
  int p = prvT[w][st]; return p < 0 ? INF : i - p;
}

typedef struct { int le1, le2, le3, ge6, ge7, ge8, le2from4; } Firsts;

/* lamCrit: the first index at <= L+1 comes after the first at >= L+7 (a later
 * drop inherits the witness, so the first one decides) */
static int c_lam(const Firsts *f) { return f->le1 > f->ge7; }
/* veeCrit: an index >= 4 at <= L+2 comes before the first at >= L+7 */
static int c_vee(const Firsts *f) { return f->le2from4 < f->ge7; }
/* HighAt (L+1) (L+8): an index at <= L+2 comes before the first at >= L+8 */
static int c_highAt(const Firsts *f) { return f->ge8 == INF || f->le2 < f->ge8; }
/* LowAt (L+1) (L+8): before the first index at <= L+1 the arm has been at
 * >= L+8, or at <= L+2 and later at >= L+6.  `ge6after` is the first index at
 * >= L+6 strictly after the first index at <= L+2. */
static int c_lowAt(const Firsts *f, int ge6after) {
  if (f->le1 == INF) return 1;
  if (f->ge8 < f->le1) return 1;
  return f->le2 < f->le1 && ge6after < f->le1;
}

/* ----------------------------------------------------------- statistics */

static long long windows, base4, base5;
static long long hits4, hits5;
static long long clsAll[4], clsBranch[4];
static long long mixedBranch4, mixedBranch5;
static long long checked, unserved3;
static long long tested4leg, failed4leg, tested4legMix, failed4legMix;
static int printedMixedBranch, printedUnserved;

static void show(const int *v, int len, int i, const char *tag, int which) {
  int a = i - 24, b = i + 24;
  if (a < 0) a = 0;
  if (b >= len) b = len - 1;
  printf("%s at L+%d, window length %d, basepoint %d, arms %d and %d; v[%d..%d]:",
         tag, which ? 5 : 4, len, i, len - i, i + 1, a, b);
  for (int j = a; j <= b; j++) printf("%s%d", j == i ? " [" : " ", v[j]);
  printf("\n");
}

static void examine(const int *v, int len, int L) {
  windows++;
  build_tables(v, len, L);
  for (int i = 0; i < len; i++) {
    int which;
    if (v[i] == L + 4) which = 0; else if (v[i] == L + 5) which = 1; else continue;
    if (which == 0) base4++; else base5++;

    Firsts G, T;
    G.le1 = fG(0, i, len); G.le2 = fG(1, i, len); G.le3 = fG(5, i, len);
    G.ge6 = fG(2, i, len); G.ge7 = fG(3, i, len); G.ge8 = fG(4, i, len);
    G.le2from4 = fGfrom(1, i, 4, len);
    T.le1 = fT(0, i); T.le2 = fT(1, i); T.le3 = fT(5, i);
    T.ge6 = fT(2, i); T.ge7 = fT(3, i); T.ge8 = fT(4, i);
    T.le2from4 = fTfrom(1, i, 4);

    Firsts RG, RT;                      /* the arms read upside down */
    RG.le1 = G.ge8; RG.le2 = G.ge7; RG.le3 = G.ge6;
    RG.ge6 = G.le3; RG.ge7 = G.le2; RG.ge8 = G.le1;
    RG.le2from4 = fGfrom(3, i, 4, len);
    RT.le1 = T.ge8; RT.le2 = T.ge7; RT.le3 = T.ge6;
    RT.ge6 = T.le3; RT.ge7 = T.le2; RT.ge8 = T.le1;
    RT.le2from4 = fTfrom(3, i, 4);

    const Firsts *FG = which ? &RG : &G, *FT = which ? &RT : &T;

    int lg = c_lam(FG), vg = c_vee(FG), lt = c_lam(FT), vt = c_vee(FT);
    int cls;
    if (lg && lt) cls = 0;
    else if (vg && vt) cls = 1;
    else if ((lg || vg) && (lt || vt)) cls = 2;
    else cls = 3;
    clsAll[cls]++;

    int inBranch;
    if (which == 0) inBranch = c_highAt(&G) && c_highAt(&T);
    else {
      int g6 = (G.le2 == INF) ? INF : fGfrom(2, i, G.le2 + 1, len);
      int t6 = (T.le2 == INF) ? INF : fTfrom(2, i, T.le2 + 1);
      inBranch = c_lowAt(&G, g6) && c_lowAt(&T, t6);
    }
    if (!inBranch) continue;
    if (which == 0) hits4++; else hits5++;
    clsBranch[cls]++;
    if (cls == 2) {
      if (which == 0) mixedBranch4++; else mixedBranch5++;
      if (printedMixedBranch < 8) { printedMixedBranch++; show(v, len, i, "MIXED", which); }
    }

    /* the four-leg walk L+3, L+6, L+1, L+8 (its reflection at L+5), on as many
     * branch pairs as time allows */
    if (tested4leg < 20000) {
      static int g4[4300], t4[4300];
      int mg = len - i, mt = i + 1;
      if (mg <= 4300 && mt <= 4300) {
        for (int j = 0; j < mg; j++) g4[j] = which ? 9 - v[i + j] : v[i + j];
        for (int j = 0; j < mt; j++) t4[j] = which ? 9 - v[i - j] : v[i - j];
        tested4leg++;
        if (cls == 2) tested4legMix++;
        if (!(folds(g4, mg, &w4leg) && folds(t4, mt, &w4leg))) {
          failed4leg++;
          if (cls == 2) {
            failed4legMix++;
            if (failed4legMix <= 3) show(v, len, i, "FOUR-LEG-FAILS-ON-MIXED", which);
          }
        }
      }
    }

    /* the first branch pairs met are used to cut down the candidate walks */
    if (candUsedOn < 400 || (cls == 2 && candUsedOnMix < 3000)) {
      static int g[4300], t_[4300];
      int mg = len - i, mt = i + 1;
      if (mg > 4300 || mt > 4300) continue;
      for (int j = 0; j < mg; j++) g[j] = which ? 9 - v[i + j] : v[i + j];
      for (int j = 0; j < mt; j++) t_[j] = which ? 9 - v[i - j] : v[i - j];
      checked++;
      if (candUsedOn < 400) intersect_candidates(g, mg, t_, mt);
      if (cls == 2) intersect_candidates_mix(g, mg, t_, mt);
      if (least_turns_of(g, mg, t_, mt) < 0) {
        unserved3++;
        if (printedUnserved < 4) { printedUnserved++; show(v, len, i, "UNSERVED", which); }
      }
    }
  }
}

/* the whole path as a single window: every basepoint, with the least-turn walk
 * printed for the first few mixed pairs of the open branch */
static void examine_whole(const int *v, int n) {
  int mn = v[0], mx = v[0];
  for (int j = 0; j < n; j++) { if (v[j] < mn) mn = v[j]; if (v[j] > mx) mx = v[j]; }
  printf("whole path: length %d, band [%d,%d], span %d\n", n, mn, mx, mx - mn);
  if (mx - mn != 9) { printf("  (not of span nine; skipped)\n"); return; }
  static int sub[4300], g[4300], t_[4300];
  for (int j = 0; j < n; j++) sub[j] = v[j] - mn;
  build_tables(sub, n, 0);
  long long b4 = 0, mix = 0, lamlam = 0, veevee = 0, nei = 0, mix4leg = 0;
  int shown = 0;
  for (int i = 0; i < n; i++) {
    if (sub[i] != 4) continue;
    Firsts G, T;
    G.le1 = fG(0, i, n); G.le2 = fG(1, i, n); G.le3 = fG(5, i, n);
    G.ge6 = fG(2, i, n); G.ge7 = fG(3, i, n); G.ge8 = fG(4, i, n);
    G.le2from4 = fGfrom(1, i, 4, n);
    T.le1 = fT(0, i); T.le2 = fT(1, i); T.le3 = fT(5, i);
    T.ge6 = fT(2, i); T.ge7 = fT(3, i); T.ge8 = fT(4, i);
    T.le2from4 = fTfrom(1, i, 4);
    if (!(c_highAt(&G) && c_highAt(&T))) continue;
    b4++;
    int lg = c_lam(&G), vg = c_vee(&G), lt = c_lam(&T), vt = c_vee(&T);
    if (lg && lt) { lamlam++; continue; }
    if (vg && vt) { veevee++; continue; }
    if (!((lg || vg) && (lt || vt))) { nei++; continue; }
    mix++;
    { int mg = n - i, mt = i + 1;
      for (int j = 0; j < mg; j++) g[j] = sub[i + j];
      for (int j = 0; j < mt; j++) t_[j] = sub[i - j];
      if (folds(g, mg, &w4leg) && folds(t_, mt, &w4leg)) mix4leg++; }
    if (shown < 6) {
      shown++;
      int mg = n - i, mt = i + 1;
      for (int j = 0; j < mg; j++) g[j] = sub[i + j];
      for (int j = 0; j < mt; j++) t_[j] = sub[i - j];
      int best = -1, bc = -1;
      for (int c = 0; c < nCand; c++)
        if (folds(g, mg, &candW[c]) && folds(t_, mt, &candW[c]))
          if (best < 0 || candK[c] < best) { best = candK[c]; bc = c; }
      printf("  MIXED basepoint %d (arms %d, %d): G lam %d vee %d, T lam %d vee %d; ",
             i, mg, mt, lg, vg, lt, vt);
      if (best < 0) printf("NO walk of <= 3 turns serves it\n");
      else {
        printf("least turns %d, walk", best);
        for (int j = 0; j <= candK[bc]; j++) printf(" L+%d", candTs[bc][j]);
        printf("\n");
      }
    }
  }
  printf("  basepoints of the open branch at L+4: %lld  (lam,lam %lld; vee,vee %lld; MIXED %lld; neither %lld)\n",
         b4, lamlam, veevee, mix, nei);
  printf("  of the MIXED ones, served by L+3,L+6,L+1,L+8 : %lld of %lld\n", mix4leg, mix);
}

static void examine_all_windows(const int *v, int n) {
  static int sub[4300];
  int stride = n / 200; if (stride < 1) stride = 1;
  for (int a = 0; a < n; a += stride) {
    int mn = v[a], mx = v[a];
    for (int b = a + 1; b < n; b++) {
      if (v[b] < mn) mn = v[b];
      if (v[b] > mx) mx = v[b];
      if (mx - mn > 9) break;
      if (mx - mn != 9) continue;
      int len = b - a + 1;
      if (len > 4300) break;
      for (int j = 0; j < len; j++) sub[j] = v[a + j] - mn;   /* floor at 0 */
      examine(sub, len, 0);
    }
  }
}

static unsigned long long rngstate = 88172645463325252ULL;
static unsigned long long rnd(void) {
  rngstate ^= rngstate << 13; rngstate ^= rngstate >> 7; rngstate ^= rngstate << 17;
  return rngstate;
}

int main(int argc, char **argv) {
  setvbuf(stdout, NULL, _IOLBF, 0);
  int maxN = argc > 1 ? atoi(argv[1]) : 10;
  int nRandom = argc > 2 ? atoi(argv[2]) : 40;
  if (argc > 3) rngstate = (unsigned long long)atoll(argv[3]) * 2654435761ULL + 1;

  printf("--- the crookedness test, on paths whose status is known ---\n");
  for (int N = 3; N <= 9; N++) {
    Path p = bpath(0, N);
    printf("bing 0 %d : length %4d, crooked %d (must be 1)\n", N, p.n, crookedThin(p.v, p.n));
    free(p.v);
  }
  { int bad[10]; for (int j = 0; j < 10; j++) bad[j] = j;
    printf("the monotone run 0..9   : crooked %d (must be 0)\n", crookedThin(bad, 10)); }
  { int bad[7] = {0,1,2,3,2,1,0};
    printf("the single fold 0..3..0 : crooked %d (must be 0)\n", crookedThin(bad, 7)); }

  /* all the windows below have floor 0 or more; the candidate walks are built
   * for the band [0,9] and translated by the examine() caller through L */
  build_candidates(0, 9);
  { int ts[4] = {3, 6, 1, 8}; build_walk(ts, 3, &w4leg); }
  printf("\ncandidate walks of up to three turns: %d\n", nCand);

  printf("\n--- the span-nine chains themselves, every basepoint ---\n");
  for (int N = 9; N <= 9; N++) {
    Path p = bpath(0, N);
    printf("bing 0 %d : crooked %d\n", N, crookedThin(p.v, p.n));
    examine_whole(p.v, p.n);
    free(p.v);
  }

  printf("\n--- family A: windows of bing 0 N, N = 9 .. %d ---\n", maxN);
  for (int N = 9; N <= maxN; N++) {
    Path p = bpath(0, N);
    if (p.n >= MAXN || !crookedThin(p.v, p.n)) { printf("bing 0 %d skipped\n", N); free(p.v); continue; }
    printf("bing 0 %d : length %d, crooked\n", N, p.n);
    examine_all_windows(p.v, p.n);
    free(p.v);
  }
  printf("after family A: windows %lld, branch pairs %lld, mixed in branch %lld\n",
         windows, hits4 + hits5, mixedBranch4 + mixedBranch5);

  printf("\n--- family B: windows of bing a b, |a-b| >= 9, a,b <= 12 ---\n");
  for (int a = 0; a <= 12; a++)
    for (int b = 0; b <= 12; b++) {
      if (abs(a - b) < 9) continue;
      if (a == 0 && b >= 9 && b <= maxN) continue;
      Path p = bpath(a, b);
      if (p.n > 4000) { free(p.v); continue; }
      if (!crookedThin(p.v, p.n)) { printf("bing %d %d : NOT crooked\n", a, b); free(p.v); continue; }
      printf("bing %d %d : length %d, crooked\n", a, b, p.n);
      examine_all_windows(p.v, p.n);
      free(p.v);
    }
  printf("after family B: windows %lld, branch pairs %lld, mixed in branch %lld\n",
         windows, hits4 + hits5, mixedBranch4 + mixedBranch5);

  printf("\n--- family C: random concatenations of Bing paths ---\n");
  long long tried = 0, accepted = 0;
  static int cat[MAXN];
  for (int trial = 0; trial < nRandom; trial++) {
    int nseg = 2 + (int)(rnd() % 3);
    int cur = (int)(rnd() % 10);
    int n = 0;
    cat[n++] = cur;
    int ok = 1;
    for (int s = 0; s < nseg; s++) {
      int tgt = (int)(rnd() % 10);
      if (tgt == cur) { s--; continue; }
      Path p = bpath(cur, tgt);
      if (n + p.n - 1 >= 4000) { ok = 0; free(p.v); break; }
      for (int j = 1; j < p.n; j++) cat[n++] = p.v[j];
      free(p.v);
      cur = tgt;
    }
    if (!ok) continue;
    tried++;
    if (!crookedThin(cat, n)) continue;
    accepted++;
    printf("concatenation %lld : length %d, crooked\n", accepted, n);
    examine_all_windows(cat, n);
  }
  printf("concatenations tried %lld, of them crooked %lld\n", tried, accepted);

  printf("\n=== totals ===\n");
  printf("windows of span exactly nine          : %lld\n", windows);
  printf("basepoints at L+4 / L+5               : %lld / %lld\n", base4, base5);
  printf("  both arms lamCrit                   : %lld\n", clsAll[0]);
  printf("  both arms veeCrit                   : %lld\n", clsAll[1]);
  printf("  MIXED                               : %lld\n", clsAll[2]);
  printf("  neither                             : %lld\n", clsAll[3]);
  printf("OPEN BRANCH pairs at L+4 / L+5        : %lld / %lld\n", hits4, hits5);
  printf("  both arms lamCrit                   : %lld\n", clsBranch[0]);
  printf("  both arms veeCrit                   : %lld\n", clsBranch[1]);
  printf("  MIXED (neither walk serves the pair): %lld  (L+4: %lld, L+5: %lld)\n",
         clsBranch[2], mixedBranch4, mixedBranch5);
  printf("  neither                             : %lld\n", clsBranch[3]);
  printf("branch pairs tested against L+3,L+6,L+1,L+8 : %lld\n", tested4leg);
  printf("  of them NOT served by that walk            : %lld\n", failed4leg);
  printf("  of the MIXED ones, %lld tested, %lld not served\n", tested4legMix, failed4legMix);
  printf("branch pairs run through the walk set : %lld\n", checked);
  printf("unserved by any walk of <= 3 turns    : %lld\n", unserved3);
  int alive = 0, aliveMix = 0;
  for (int c = 0; c < nCand; c++) { if (candAlive[c]) alive++; if (candAliveMix[c]) aliveMix++; }
  printf("walks of <= 3 turns serving ALL %lld branch pairs met : %d\n", candUsedOn, alive);
  for (int c = 0, shown = 0; c < nCand && shown < 20; c++) {
    if (!candAlive[c]) continue;
    shown++;
    printf("   walk %d turns:", candK[c]);
    for (int j = 0; j <= candK[c]; j++) printf(" L+%d", candTs[c][j]);
    printf("\n");
  }
  printf("walks of <= 3 turns serving ALL %lld MIXED pairs met  : %d\n", candUsedOnMix, aliveMix);
  for (int c = 0, shown = 0; c < nCand && shown < 20; c++) {
    if (!candAliveMix[c]) continue;
    shown++;
    printf("   walk %d turns:", candK[c]);
    for (int j = 0; j <= candK[c]; j++) printf(" L+%d", candTs[c][j]);
    printf("\n");
  }
  return 0;
}
