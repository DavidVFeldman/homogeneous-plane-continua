/* Census for batch 42 -- are the two open branches at span nine inhabited by
 * actual pairs, and are those pairs served?
 *
 * Corpus: every contiguous window of `bing 0 N` for N = 9 .. 13 whose range of
 * rho-values is exactly nine (min = L, max = L + 9).  A window of a crooked
 * sequence is a crooked sequence (`isCrookedIvF_restrict`, batch 30), so every
 * (window, basepoint) pair below is an actual pair of the faithful model.
 *
 * For each window and each basepoint i of it:
 *   branch 4: rho i = L + 4 and both arms HighAt (L+1) (L+8)
 *   branch 5: rho i = L + 5 and both arms LowAt  (L+1) (L+8)
 * and, for a hit, the least number of turning targets of a zigzag walk onto
 * which both arms fold (exact `FoldsOnto` by bitmask reachability).
 *
 * Usage: census-batch42b [maxN]
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

/* ------------------------------------- candidate properties of actual arms */

/* CritLam f p H (Itinerary.lean): the exact criterion for folding onto the
 * Lambda-walk based at p with peak kappa = max (H-1) p. */
static int critLam(const int *f, int m, int p, int H) {
  int kappa = H - 1 > p ? H - 1 : p;
  if (p >= kappa) return 1;
  for (int d = 0; d < m; d++) {
    if (f[d] > p - 2) continue;
    int ok = 0;
    for (int j = 0; j < d && !ok; j++) if (f[j] >= kappa) ok = 1;
    int cnt = 0;
    for (int j = 0; j < d && !ok; j++) if (f[j] >= kappa - 1) { cnt++; if (cnt >= 2) ok = 1; }
    for (int j = 0; j < d && !ok; j++) {
      if (f[j] < kappa - 1) continue;
      for (int t = 1; t < j; t++) if (f[t] <= f[t-1]) { ok = 1; break; }
    }
    if (!ok) return 0;
  }
  return 1;
}

/* R8: before the arm ever drops to `lo`, it has been at `hi`, or it has been
 * at `lo + 1` and after that at `hi - 1`. */
static int deepFloor(const int *f, int m, int lo, int hi) {
  int seenHi = 0, seenLo = 0, seenPair = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= lo && !(seenHi || seenPair)) return 0;
    if (f[d] >= hi) seenHi = 1;
    if (seenLo && f[d] >= hi - 1) seenPair = 1;
    if (f[d] <= lo + 1) seenLo = 1;
  }
  return 1;
}

static int reaches(const int *f, int m, int lo, int hi) {
  for (int j = 0; j < m; j++) if (f[j] >= lo && f[j] <= hi) return 1;
  return 0;
}

/* ------------------------------------------------------------------- main */

/* before ever dropping to <= lo, the arm has been at >= hi */
static int highBeforeFloor(const int *f, int m, int lo, int hi) {
  int seenHi = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= lo && !seenHi) return 0;
    if (f[d] >= hi) seenHi = 1;
  }
  return 1;
}

#define NPROP 9
static const char *propname[NPROP] = {
  "CritLam(base L+3,peak L+8)", "LowAt L (L+8)", "deepFloor(L,L+8)",
  "never at L", "HighAt (L+1) (L+7)", "CritLam(base L+4,peak L+8)",
  "deepFloor(L+1,L+8)", "high L+7 before floor L+1", "high L+8 before floor L+1" };
static long long propcnt[2][NPROP];
static long long fixedok[2];

static void props(const int *f, int m, int L, int *out) {
  out[0] = critLam(f, m, L + 3, L + 9);
  out[1] = lowAt(f, m, L, L + 8);
  out[2] = deepFloor(f, m, L, L + 8);
  out[3] = !reaches(f, m, L, L);
  out[4] = highAt(f, m, L + 1, L + 7);
  out[5] = critLam(f, m, L + 4, L + 9);
  out[6] = deepFloor(f, m, L + 1, L + 8);
  out[7] = highBeforeFloor(f, m, L + 1, L + 7);
  out[8] = highBeforeFloor(f, m, L + 1, L + 8);
}

/* the two announcements of HPC/Fold/Span9Profile.lean, at the branch L+4 */
static int annTop(const int *f, int m, int lo, int hi) {
  int seen = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= lo && !seen) return 0;
    if (f[d] >= hi) seen = 1;
  }
  return 1;
}
static int annFloor(const int *f, int m, int lo, int hi) {
  int seen = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= hi && !seen) return 0;
    if (f[d] <= lo) seen = 1;
  }
  return 1;
}

static long long combo[2][4];      /* both-top, both-floor, mixed, neither */

static long long hits[2], unserved[2], windows, turnhist[2][8];
static int printed[2];

static void examine(const int *v, int len) {
  int mn = 99, mx = -1;
  for (int j = 0; j < len; j++) { if (v[j] < mn) mn = v[j]; if (v[j] > mx) mx = v[j]; }
  if (mx - mn != 9) return;
  windows++;
  int L = mn;
  LG = mn; HG = mx;
  for (int i = 0; i < len; i++) {
    int g[512], t_[512];
    int mg = len - i, mt = i + 1;
    if (mg > 512 || mt > 512) continue;
    for (int j = 0; j < mg; j++) g[j] = v[i + j];
    for (int j = 0; j < mt; j++) t_[j] = v[i - j];
    for (int which = 0; which < 2; which++) {
      int hit;
      if (which == 0)
        hit = (v[i] == L + 4) && highAt(g, mg, L + 1, L + 8) && highAt(t_, mt, L + 1, L + 8);
      else
        hit = (v[i] == L + 5) && lowAt(g, mg, L + 1, L + 8) && lowAt(t_, mt, L + 1, L + 8);
      if (!hit) continue;
      hits[which]++;
      {
        int aG, aT, bG, bT;
        if (which == 0) {
          aG = annTop(g, mg, L + 1, L + 8); aT = annTop(t_, mt, L + 1, L + 8);
          bG = annFloor(g, mg, L + 1, L + 7); bT = annFloor(t_, mt, L + 1, L + 7);
        } else {
          aG = annFloor(g, mg, L + 1, L + 8); aT = annFloor(t_, mt, L + 1, L + 8);
          bG = annTop(g, mg, L + 2, L + 8); bT = annTop(t_, mt, L + 2, L + 8);
        }
        if (aG && aT) combo[which][0]++;
        else if (bG && bT) combo[which][1]++;
        else if ((aG || bG) && (aT || bT)) combo[which][2]++;
        else combo[which][3]++;
      }
      int pg[NPROP], pt[NPROP];
      props(g, mg, L, pg); props(t_, mt, L, pt);
      for (int q = 0; q < NPROP; q++) if (pg[q] && pt[q]) propcnt[which][q]++;
      int fixed4[3] = {L + 3, L + 8, L + 1}, fixed5[3] = {L + 6, L + 1, L + 8};
      {
        Walk w; build_walk(which ? fixed5 : fixed4, 2, &w);
        if (folds(g, mg, &w) && folds(t_, mt, &w)) fixedok[which]++;
      }
      int ts[8];
      int k = least_turns(g, mg, t_, mt, 5, ts);
      if (k < 0) {
        unserved[which]++;
        printf("UNSERVED branch %d len %d base %d:", which ? 5 : 4, len, i);
        for (int j = 0; j < len; j++) printf(" %d", v[j]);
        printf("\n");
      } else {
        turnhist[which][k]++;
        if (printed[which] < 4 && len <= 140) {
          printed[which]++;
          printf("branch %d inhabited: len %d base %d turns %d walk", which ? 5 : 4, len, i, k);
          for (int j = 0; j <= k; j++) printf(" %d", ts[j]);
          printf("  seq:");
          for (int j = 0; j < len; j++) printf("%s%d", j == i ? " [" : " ", v[j]);
          printf("\n");
        }
      }
    }
  }
}

int main(int argc, char **argv) {
  int maxN = argc > 1 ? atoi(argv[1]) : 12;
  for (int N = 9; N <= maxN; N++) {
    Path p = bpath(0, N);
    printf("bing 0 %d : length %d\n", N, p.n);
    int sub[2048];
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
    printf("branch %d: inhabited %lld, unserved %lld, served by the fixed walk %lld,"
           " least-turn histogram:", w ? 5 : 4, hits[w], unserved[w], fixedok[w]);
    for (int k = 0; k < 8; k++) if (turnhist[w][k]) printf(" k=%d:%lld", k, turnhist[w][k]);
    printf("\n");
    for (int q = 0; q < NPROP; q++)
      printf("    both arms %-28s : %lld / %lld\n", propname[q], propcnt[w][q], hits[w]);
    printf("    announcements: both ceiling-first %lld, both floor-first %lld,"
           " mixed %lld, an arm with neither %lld\n",
           combo[w][0], combo[w][1], combo[w][2], combo[w][3]);
  }
  return 0;
}
