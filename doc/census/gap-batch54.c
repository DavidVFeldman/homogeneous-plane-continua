/* gap-batch54.c -- batch 54, commission question 3: the sigma-route's lost link.
 *
 * The reflection of the general model sends (rho, sig) to (9 - sig, 9 - rho), so
 * the branch L+5 of rho is the branch L+4 of tau = 9 - sig, and census-batch53.c
 * found that one of the five walks of the branch L+4 serves the tau-pair at every
 * basepoint of the branch L+5.  What the branch itself needs is a fold of the
 * arms of 9 - rho, and 9 - rho sits one level above tau wherever the link is
 * non-thin: |(9 - rho) - tau| = sig - rho, which is 0 or 1.
 *
 * This program measures the loss link by link.  At every basepoint of the branch
 * L+5 it computes, for each of the five walks,
 *
 *    served_tau   -- both arms of tau fold onto the walk, window one
 *    served_refl  -- both arms of 9 - rho fold onto the same walk, window one
 *
 * and counts the basepoints where some walk serves tau but that same walk does
 * not serve 9 - rho (the walk is lost), where no walk of the five serves
 * 9 - rho (the basepoint is lost), and where the pair is thin on both arms, in
 * which case tau and 9 - rho coincide and nothing can be lost.  For the lost
 * basepoints the shortest walk of at most three turns based within one of L+4
 * that serves 9 - rho is searched for as well.
 *
 * Generators: bing 0 9, bing 9 0, their single shavings, single fills and total
 * mixtures, and random concatenations of Bing blocks (levels drawn uniformly).
 * Faithfulness is IsCrookedIvF, exactly as HPC/Fold/Faithful.lean states it;
 * every predicate is evaluated by its own definition.
 *
 * Usage: gap-batch54 [concat-draws] [seed]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 4096
#define MAXW 96
#define MAXLEV 32

static int rho[MAXN], sig[MAXN];
static int meetTab[MAXLEV][MAXN + 1];

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
  int mid = (a < b) ? b - 1 : b + 1, c = (a < b) ? a + 1 : a - 1;
  Path p1 = bpath(a, mid), p2 = bpath(mid, c), p3 = bpath(c, b);
  p.n = p1.n + p2.n - 1 + p3.n - 1;
  p.v = (int *)malloc(sizeof(int) * p.n);
  memcpy(p.v, p1.v, sizeof(int) * p1.n);
  memcpy(p.v + p1.n, p2.v + 1, sizeof(int) * (p2.n - 1));
  memcpy(p.v + p1.n + p2.n - 1, p3.v + 1, sizeof(int) * (p3.n - 1));
  free(p1.v); free(p2.v); free(p3.v);
  return p;
}

static int trigLevels(int t, int n, int *out) {
  int nh = 0;
  for (int e = -1; e <= 1; e++) {
    int u = t + e;
    if (u < 0 || u >= n) continue;
    for (int l = rho[u]; l <= sig[u]; l++) {
      int seen = 0;
      for (int q = 0; q < nh; q++) if (out[q] == l) seen = 1;
      if (!seen) out[nh++] = l;
    }
  }
  return nh;
}

static int faithful(int n) {
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
    int hs[8]; int nh = trigLevels(s, n, hs);
    for (int t = s + 1; t < n; t++) {
      int ks[8]; int nk = trigLevels(t, n, ks);
      for (int a = 0; a < nh; a++) for (int b = 0; b < nk; b++) {
        int h = hs[a], k = ks[b];
        int diff = h - k; if (diff < 0) diff = -diff;
        if (diff < 3) continue;
        int r1 = (h < k) ? k - 1 : k + 1, r2 = (h < k) ? h + 1 : h - 1;
        if (r1 < 0 || r1 >= MAXLEV || r2 < 0 || r2 >= MAXLEV) continue;
        int p1 = meetTab[r1][s + 1];
        if (p1 >= t) return 0;
        int p2 = meetTab[r2][p1 + 1];
        if (p2 >= t) return 0;
      }
    }
  }
  return 1;
}

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

/* the five walks of the branch L+4 */
static const int wdef[5][4] = {
  {3, 8, 1, -1},   /* the Lambda-walk */
  {5, 1, 8, -1},   /* the V-walk */
  {3, 6, 1, 8},    /* w3 */
  {3, 2, 8, 1},    /* w4 */
  {3, 7, 1, 8},    /* w5 */
};
static const char *wname[5] = {"Lambda", "V", "w3", "w4", "w5"};

static int foldsK(int k, const int *f, int m) {
  int w[MAXW];
  int l = buildWalk(w, wdef[k][0], wdef[k][1], wdef[k][2], wdef[k][3]);
  return folds(f, m, w, l);
}

static int highAt(const int *f, int m) {
  int seenLow = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !seenLow) return 0;
    if (f[d] <= 2) seenLow = 1;
  }
  return 1;
}
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

/* the shortest walk of at most three turns based in [lo, hi] serving both arms */
static int findWalk(const int *g, int mg, const int *t, int mt, int lo, int hi,
                    int *bst, int *ba, int *bb, int *bc) {
  int best = 1 << 30;
  *bst = -1;
  for (int st = lo; st <= hi; st++)
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
            best = wl; *bst = st; *ba = a; *bb = b; *bc = c;
          }
        }
      }
    }
  return (*bst < 0) ? -1 : best;
}

static long base5, thinBoth, tauServed, reflServed, walkLost[5], walkKept[5];
static long baseLost, baseLostThin, baseLostFound, baseLostNone;
static long pairs, links, nonthin;

static int refG[MAXN], refT[MAXN], tauG[MAXN], tauT[MAXN];

static void scan(int n) {
  pairs++; links += n;
  for (int u = 0; u < n; u++) if (sig[u] != rho[u]) nonthin++;
  for (int i = 0; i < n; i++) {
    if (rho[i] != 5) continue;
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) { refG[d] = 9 - rho[i + d]; tauG[d] = 9 - sig[i + d]; }
    for (int d = 0; d < mt; d++) { refT[d] = 9 - rho[i - d]; tauT[d] = 9 - sig[i - d]; }
    if (!lowAt(refG, mg) && !lowAt(refT, mt)) { }
    /* the branch hypothesis, on the arms of rho, exactly as s3_span_nine_mid5 reads it */
    {
      static int armG[MAXN], armT[MAXN];
      for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
      for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
      if (!lowAt(armG, mg) || !lowAt(armT, mt)) continue;
    }
    base5++;
    int thin = 1;
    for (int d = 0; d < mg; d++) if (sig[i + d] != rho[i + d]) thin = 0;
    for (int d = 0; d < mt; d++) if (sig[i - d] != rho[i - d]) thin = 0;
    if (thin) thinBoth++;
    if (tauG[0] != 4 || !highAt(tauG, mg) || !highAt(tauT, mt)) continue;
    int anyTau = 0, anyRefl = 0;
    for (int k = 0; k < 5; k++) {
      int st = foldsK(k, tauG, mg) && foldsK(k, tauT, mt);
      int sr = foldsK(k, refG, mg) && foldsK(k, refT, mt);
      if (st) anyTau = 1;
      if (sr) anyRefl = 1;
      if (st && !sr) walkLost[k]++;
      if (st && sr) walkKept[k]++;
    }
    if (anyTau) tauServed++;
    if (anyRefl) reflServed++;
    if (anyTau && !anyRefl) {
      baseLost++;
      if (thin) baseLostThin++;
      int st, a, b, c;
      int len = findWalk(refG, mg, refT, mt, 3, 5, &st, &a, &b, &c);
      if (len < 0) baseLostNone++;
      else {
        baseLostFound++;
        if (baseLostFound <= 10)
          printf("  a basepoint where the sigma-route's walk is lost and another serves: "
                 "%d -> %d -> %d -> %d (%d links)\n", st, a, b, c, len);
      }
    }
  }
}

static void runSeq(int n, const int *v) {
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  if (!faithful(n)) return;
  scan(n);
  for (int pk = 1; pk + 1 < n; pk++) {
    if (!(v[pk] > v[pk-1] && v[pk] > v[pk+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    rho[pk] = v[pk] - 1;
    if (faithful(n)) scan(n);
  }
  for (int vl = 1; vl + 1 < n; vl++) {
    if (!(v[vl] < v[vl-1] && v[vl] < v[vl+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    sig[vl] = v[vl] + 1;
    if (faithful(n)) scan(n);
  }
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  for (int j = 1; j + 1 < n; j++) {
    if (v[j] > v[j-1] && v[j] > v[j+1]) rho[j] = v[j] - 1;
    else if (v[j] < v[j-1] && v[j] < v[j+1]) sig[j] = v[j] + 1;
  }
  if (faithful(n)) scan(n);
}

int main(int argc, char **argv) {
  long draws = (argc > 1) ? atol(argv[1]) : 30;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 54u;
  srandom(seed);
  printf("gap-batch54: the sigma-route's lost link at the branch L+5.\n");
  printf("concat-draws=%ld seed=%u\n\n", draws, seed);

  { Path p = bpath(0, 9); runSeq(p.n, p.v); free(p.v); }
  { Path p = bpath(9, 0); runSeq(p.n, p.v); free(p.v); }
  {
    static int v[MAXN];
    long tried = 0, made = 0;
    for (long it = 0; it < draws; it++) {
      int nb = 2 + (int)(random() % 4), n = 0, cur = (int)(random() % 10), first = 1;
      for (int b = 0; b < nb; b++) {
        int nx; do { nx = (int)(random() % 10); } while (nx == cur);
        Path blk = bpath(cur, nx);
        if (n + blk.n >= 1200) { free(blk.v); break; }
        if (first) { memcpy(v, blk.v, sizeof(int) * blk.n); n = blk.n; first = 0; }
        else { memcpy(v + n, blk.v + 1, sizeof(int) * (blk.n - 1)); n += blk.n - 1; }
        cur = nx; free(blk.v);
      }
      if (n < 20) continue;
      tried++;
      for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
      if (!faithful(n)) continue;
      made++;
      runSeq(n, v);
    }
    printf("random concatenations of Bing blocks: %ld faithful of %ld drawn\n\n", made, tried);
  }

  printf("faithful pairs %ld; links %ld, non-thin %ld (%.5f)\n", pairs, links, nonthin,
         links ? (double)nonthin / (double)links : 0.0);
  printf("branch L+5 basepoints %ld, of which both arms are thin %ld\n", base5, thinBoth);
  printf("the tau-pair is served by one of the five walks at %ld basepoints; the pair of "
         "9 - rho at %ld\n", tauServed, reflServed);
  for (int k = 0; k < 5; k++)
    printf("  walk %s: serves tau and 9 - rho %ld times; serves tau and NOT 9 - rho %ld times\n",
           wname[k], walkKept[k], walkLost[k]);
  printf("basepoints where the sigma-route serves tau but no walk of the five serves 9 - rho: "
         "%ld (of them thin on both arms: %ld); another walk of at most three turns serves "
         "9 - rho at %ld of them, none at %ld\n", baseLost, baseLostThin, baseLostFound,
         baseLostNone);
  return 0;
}
