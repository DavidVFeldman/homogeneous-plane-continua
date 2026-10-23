/* Census for batch 42 (continued) -- the mixed case at span nine.
 *
 * Corpus: the same as census-batch42b.c -- every contiguous window of
 * `bing 0 N`, N = 9 .. maxN, whose range of rho-values is exactly nine, and
 * every basepoint of every such window.  A window of a crooked sequence is a
 * crooked sequence, so each (window, basepoint) is an actual pair.
 *
 * Here each arm of a branch hit is classified by the two EXACT profile
 * criteria of HPC/Fold/Profile.lean rather than by an announcement:
 *
 *   lamCrit : before the arm ever drops to L+1 it stands at L+7 at an index
 *             at least five           (folds onto the Lambda-walk at base L+3)
 *   veeCrit : before the arm ever rises to L+7 it stands at L+2 or below at an
 *             index at least four     (folds onto the V-walk at base L+5)
 *
 * and, at the branch L+5, by the reflections of these (the arm is reflected
 * through the middle of the band and the same tests are applied).
 *
 * The four classes of a pair are: both arms lamCrit (the Lambda-walk serves),
 * both arms veeCrit (the V-walk serves), MIXED (one arm only lamCrit, the
 * other only veeCrit -- what is left open), and neither.  The mixed class is
 * split further by whether the two failures are vacuous, i.e. whether the
 * lamCrit arm never drops to L+1 and the veeCrit arm never rises to L+7:
 * that sub-case is what `s3_span_nine_no_vacuous_mix` of HPC/Fold/CrossArm.lean
 * excludes, and this run checks the exclusion against the corpus.
 *
 * Usage: census-batch42k [maxN]
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

/* ------------------------------------------------------------- conditions */

static int highAt(const int *f, int m, int tl, int th) {
  int seen = 0;
  for (int j = 0; j < m; j++) {
    if (f[j] >= th && !seen) return 0;
    if (f[j] <= tl + 1) seen = 1;
  }
  return 1;
}

static int lowAt(const int *f, int m, int tl, int th) {
  for (int d = 0; d < m; d++) {
    if (f[d] > tl) continue;
    int ok = 0;
    for (int j = 0; j < d && !ok; j++) if (f[j] >= th) ok = 1;
    for (int j = 0; j < d && !ok; j++) {
      if (f[j] > tl + 1) continue;
      for (int jp = j + 1; jp < d; jp++) if (f[jp] >= th - 2) { ok = 1; break; }
    }
    if (!ok) return 0;
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
  u128 one = 1, mask = 0;
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

static int LG, HG;            /* level window for walk targets */

static int least_turns(const int *g, int mg, const int *t_, int mt, int kmax, int *out) {
  int ts[8];
  for (int k = 0; k <= kmax; k++)
    for (ts[0] = LG; ts[0] <= HG; ts[0]++) {
      int lo = LG + 1, hi = HG - 1, span = hi - lo + 1;
      long total = 1; for (int j = 1; j <= k; j++) total *= span;
      for (long code = 0; code < total; code++) {
        long c = code; int bad = 0;
        for (int j = 1; j <= k; j++) { ts[j] = lo + (int)(c % span); c /= span; }
        for (int j = 1; j <= k && !bad; j++) {
          if (ts[j] == ts[j-1]) bad = 1;
          if (j >= 2 && ((ts[j] > ts[j-1]) == (ts[j-1] > ts[j-2]))) bad = 1;
        }
        if (bad) continue;
        Walk w; build_walk(ts, k, &w);
        if (folds(g, mg, &w) && folds(t_, mt, &w)) {
          if (out) for (int j = 0; j <= k; j++) out[j] = ts[j];
          return k;
        }
      }
    }
  return -1;
}

/* ------------------------------------------- the two exact profile criteria */

/* before the arm ever drops to <= L+1 it stands at >= L+7 at an index >= 5 */
static int lamCrit(const int *f, int m, int L) {
  for (int d = 0; d < m; d++) {
    if (f[d] > L + 1) continue;
    int ok = 0;
    for (int j = 5; j < d; j++) if (f[j] >= L + 7) { ok = 1; break; }
    if (!ok) return 0;
  }
  return 1;
}

/* before the arm ever rises to >= L+7 it stands at <= L+2 at an index >= 4 */
static int veeCrit(const int *f, int m, int L) {
  for (int d = 0; d < m; d++) {
    if (f[d] < L + 7) continue;
    int ok = 0;
    for (int j = 4; j < d; j++) if (f[j] <= L + 2) { ok = 1; break; }
    if (!ok) return 0;
  }
  return 1;
}

static int neverLow(const int *f, int m, int L) {         /* never drops to L+1 */
  for (int j = 0; j < m; j++) if (f[j] <= L + 1) return 0;
  return 1;
}

static int neverHigh(const int *f, int m, int L) {        /* never rises to L+7 */
  for (int j = 0; j < m; j++) if (f[j] >= L + 7) return 0;
  return 1;
}

/* ------------------------------------------------------------- statistics */

static long long windows, hits[2];
static long long cls[2][4];          /* both lam, both vee, mixed, neither */
static long long mixedVac[2];        /* mixed with both failures vacuous */
static long long vacLam[2], vacVee[2];  /* an arm off the floor / off the ceiling */
static long long unserved[2];
static int printedMixed[2];

static void examine(const int *v, int len) {
  int mn = 99, mx = -1;
  for (int j = 0; j < len; j++) { if (v[j] < mn) mn = v[j]; if (v[j] > mx) mx = v[j]; }
  if (mx - mn != 9) return;
  windows++;
  int L = mn;
  LG = mn; HG = mx;
  for (int i = 0; i < len; i++) {
    int g[512], t_[512], gr[512], tr[512];
    int mg = len - i, mt = i + 1;
    if (mg > 512 || mt > 512) continue;
    for (int j = 0; j < mg; j++) g[j] = v[i + j];
    for (int j = 0; j < mt; j++) t_[j] = v[i - j];
    /* reflection through the middle of the band */
    for (int j = 0; j < mg; j++) gr[j] = 2 * L + 9 - g[j];
    for (int j = 0; j < mt; j++) tr[j] = 2 * L + 9 - t_[j];
    for (int which = 0; which < 2; which++) {
      int hit;
      if (which == 0)
        hit = (v[i] == L + 4) && highAt(g, mg, L + 1, L + 8) && highAt(t_, mt, L + 1, L + 8);
      else
        hit = (v[i] == L + 5) && lowAt(g, mg, L + 1, L + 8) && lowAt(t_, mt, L + 1, L + 8);
      if (!hit) continue;
      hits[which]++;
      const int *G = which ? gr : g, *T = which ? tr : t_;
      int lg = lamCrit(G, mg, L), vg = veeCrit(G, mg, L);
      int lt = lamCrit(T, mt, L), vt = veeCrit(T, mt, L);
      if (lg && lt) cls[which][0]++;
      else if (vg && vt) cls[which][1]++;
      else if ((lg || vg) && (lt || vt)) {
        cls[which][2]++;
        int vac = (lg && neverLow(G, mg, L) && vt && neverHigh(T, mt, L)) ||
                  (lt && neverLow(T, mt, L) && vg && neverHigh(G, mg, L));
        if (vac) mixedVac[which]++;
        if (printedMixed[which] < 3) {
          printedMixed[which]++;
          printf("MIXED branch %d len %d base %d:", which ? 5 : 4, len, i);
          for (int j = 0; j < len; j++) printf("%s%d", j == i ? " [" : " ", v[j]);
          printf("\n");
        }
      } else cls[which][3]++;
      if (neverLow(G, mg, L) || neverLow(T, mt, L)) vacLam[which]++;
      if (neverHigh(G, mg, L) || neverHigh(T, mt, L)) vacVee[which]++;
      if (least_turns(g, mg, t_, mt, 5, 0) < 0) {
        unserved[which]++;
        printf("UNSERVED branch %d len %d base %d\n", which ? 5 : 4, len, i);
      }
    }
  }
}

int main(int argc, char **argv) {
  int maxN = argc > 1 ? atoi(argv[1]) : 11;
  for (int N = 9; N <= maxN; N++) {
    Path p = bpath(0, N);
    printf("bing 0 %d : length %d\n", N, p.n);
    static int sub[2048];
    for (int a = 0; a < p.n; a++)
      for (int b = a + 1; b < p.n; b++) {
        int len = b - a + 1;
        if (len > 2048) continue;
        for (int j = 0; j < len; j++) sub[j] = p.v[a + j];
        examine(sub, len);
      }
    free(p.v);
  }
  printf("windows of span exactly nine: %lld\n", windows);
  for (int w = 0; w < 2; w++) {
    printf("branch %d: inhabited %lld, unserved %lld\n", w ? 5 : 4, hits[w], unserved[w]);
    printf("    both arms lamCrit : %lld\n", cls[w][0]);
    printf("    both arms veeCrit : %lld\n", cls[w][1]);
    printf("    MIXED             : %lld  (of which both failures vacuous: %lld)\n",
           cls[w][2], mixedVac[w]);
    printf("    neither           : %lld\n", cls[w][3]);
    printf("    pairs with an arm that never meets the floor   : %lld\n", vacLam[w]);
    printf("    pairs with an arm that never meets the ceiling : %lld\n", vacVee[w]);
  }
  return 0;
}
