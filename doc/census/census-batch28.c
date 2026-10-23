/* Census for batch 28 -- the gate of COMMISSION.md sec.1.
 *
 * Decides `S3Zig` exactly, by bitmask reachability, at every basepoint of a
 * chain: is there a turning sequence `ts` with
 *
 *   - every entry in [L+1, H-1],
 *   - length >= 3,
 *   - directions alternating,
 *   - amplitudes |t_{j+1} - t_j| strictly increasing,
 *   - the last two entries (L+1, H-1) or (H-1, L+1),
 *
 * such that both arms at i fold onto the walk through `ts` (one level per
 * step) from time 0?  `FoldsOnto f len c` is: a Lipschitz time assignment
 * beta with beta 0 = 0, beta j < len, |f j - c (beta j)| <= 1; at j = 0 this
 * forces |rho i - ts[0]| <= 1, which is the statement's base-centre clause,
 * so that clause is not an extra restriction and is enforced here as part of
 * the fold.
 *
 * The set of admissible time-slots is a bitmask over walk times (walks are
 * shorter than 64 steps for every span considered here), so one O(n) sweep
 * per walk resolves every basepoint of the chain at once:
 *
 *   G i = { u : rho[i..] folds onto the walk starting at time u }
 *   T i = { u : rho[i], rho[i-1], ..., rho[0] folds starting at time u }
 *
 * and basepoint i is served by the walk iff 0 is in G i and in T i and the
 * walk's first entry is within one of rho i.
 *
 * Two families are censused:
 *   variant 0 -- `IsZig` exactly as stated;
 *   variant 1 -- `IsZig` with the first amplitude exempt from the increase
 *                condition (|t1 - t0| unconstrained, |t2 - t1| < |t3 - t2| < ...).
 *
 * Failures are split into basepoints at an extreme level (rho i = L or H),
 * where variant 0 is impossible for a structural reason, and the rest.
 *
 * Usage: census-batch28 [seed]
 */

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned long long u64;

/* ------------------------------------------------------------ bing chains */

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

/* ------------------------------------------------- zig turning sequences  */

#define MAXW 400000
#define MAXTS 24

static signed char wbuf[MAXW][64];   /* the walk, one level per step */
static unsigned char wlenA[MAXW];
static signed char tsbuf_all[MAXW][MAXTS];
static unsigned char tslenA[MAXW];
static unsigned char wturns[MAXW];   /* number of turning targets = |ts| - 1 */
static int order[MAXW];
static int nw;

static int gL, gH, gVariant;
static int ts[MAXTS];

static void emit(int k) {
  assert(nw < MAXW);
  assert(k <= MAXTS);
  int w[64], len = 0;
  w[len++] = ts[0];
  for (int j = 1; j < k; j++) {
    int d = ts[j] > ts[j - 1] ? 1 : -1;
    for (int x = ts[j - 1] + d;; x += d) {
      assert(len < 64);
      w[len++] = x;
      if (x == ts[j]) break;
    }
  }
  for (int u = 0; u < len; u++) wbuf[nw][u] = (signed char)w[u];
  wlenA[nw] = (unsigned char)len;
  for (int j = 0; j < k; j++) tsbuf_all[nw][j] = (signed char)ts[j];
  tslenA[nw] = (unsigned char)k;
  wturns[nw] = (unsigned char)(k - 1);
  nw++;
}

/* k entries already placed in ts; lastamp/lastdir describe the step into ts[k-1].
   Under variant 1 the increase condition linking |t1 - t0| to |t2 - t1| is dropped,
   so the amplitude placing ts[2] is unconstrained. */
static void dfs(int k, int lastamp, int lastdir) {
  int cur = ts[k - 1];
  /* under variant 1 the step out of ts[0] may have any amplitude */
  int minamp = (gVariant == 1 && k == 2) ? 1 : lastamp + 1;
  for (int dir = -1; dir <= 1; dir += 2) {
    if (lastdir != 0 && dir == lastdir) continue;
    for (int amp = minamp;; amp++) {
      int nxt = cur + dir * amp;
      if (nxt < gL + 1 || nxt > gH - 1) break;
      ts[k] = nxt;
      int ends = (ts[k - 1] == gL + 1 && nxt == gH - 1) ||
                 (ts[k - 1] == gH - 1 && nxt == gL + 1);
      if (k + 1 >= 3 && ends) emit(k + 1);
      else if (k + 1 < MAXTS) dfs(k + 1, amp, dir);
    }
  }
}

static int cmp_order(const void *a, const void *b) {
  int x = *(const int *)a, y = *(const int *)b;
  if (wturns[x] != wturns[y]) return wturns[x] - wturns[y];
  if (wlenA[x] != wlenA[y]) return wlenA[x] - wlenA[y];
  return x - y;
}

/* all zig walks for the band [L, H], sorted by turn count then length */
static void build_walks(int L, int H, int variant) {
  gL = L; gH = H; gVariant = variant; nw = 0;
  for (int c = L + 1; c <= H - 1; c++) { ts[0] = c; dfs(1, 0, 0); }
  for (int i = 0; i < nw; i++) order[i] = i;
  qsort(order, nw, sizeof(int), cmp_order);
}

/* ------------------------------------------------------------- the sweep  */

#define MAXN 20000

static u64 Gm[MAXN], Tm[MAXN];
static int minturns[MAXN];

static inline u64 nbr(u64 m, u64 full) { return (m | (m << 1) | (m >> 1)) & full; }

/* Fill minturns[i] (-1 when no zig walk serves i) for the chain rho[0..n-1].
   Writes the number of unserved basepoints at an extreme level and elsewhere. */
static void census_chain(const int *rho, int n, int variant,
                         int *bad_extreme, int *bad_other, int *out_maxturns) {
  int L = rho[0], H = rho[0];
  for (int i = 1; i < n; i++) { if (rho[i] < L) L = rho[i]; if (rho[i] > H) H = rho[i]; }
  for (int i = 0; i < n; i++) minturns[i] = -1;
  *out_maxturns = -1; *bad_extreme = 0; *bad_other = 0;
  if (H - L < 3) { *bad_extreme = -1; return; }   /* hypothesis L + 3 <= H fails */
  build_walks(L, H, variant);
  int remaining = n;
  u64 allow[64];
  for (int wi = 0; wi < nw && remaining > 0; wi++) {
    int w = order[wi];
    int len = wlenA[w];
    u64 full = (len >= 64) ? ~0ULL : ((1ULL << len) - 1ULL);
    for (int v = L; v <= H; v++) {
      u64 m = 0;
      for (int u = 0; u < len; u++) {
        int d = v - wbuf[w][u];
        if (d <= 1 && d >= -1) m |= 1ULL << u;
      }
      allow[v - L] = m;
    }
    Gm[n - 1] = allow[rho[n - 1] - L];
    for (int i = n - 2; i >= 0; i--) Gm[i] = allow[rho[i] - L] & nbr(Gm[i + 1], full);
    Tm[0] = allow[rho[0] - L];
    for (int i = 1; i < n; i++) Tm[i] = allow[rho[i] - L] & nbr(Tm[i - 1], full);
    int c0 = wbuf[w][0];
    for (int i = 0; i < n; i++) {
      if (minturns[i] >= 0) continue;
      int d = rho[i] - c0;
      if (d > 1 || d < -1) continue;
      if ((Gm[i] & Tm[i] & 1ULL) != 0ULL) { minturns[i] = wturns[w]; remaining--; }
    }
  }
  int mx = -1;
  for (int i = 0; i < n; i++) {
    if (minturns[i] < 0) {
      if (rho[i] == L || rho[i] == H) (*bad_extreme)++; else (*bad_other)++;
    } else if (minturns[i] > mx) mx = minturns[i];
  }
  *out_maxturns = mx;
}

/* does walk `w` serve basepoint `i` of rho?  (single-walk re-check) */
static int walk_serves(const int *rho, int n, int L, int H, int w, int i) {
  int len = wlenA[w];
  u64 full = (len >= 64) ? ~0ULL : ((1ULL << len) - 1ULL);
  u64 allow[64];
  for (int v = L; v <= H; v++) {
    u64 m = 0;
    for (int u = 0; u < len; u++) {
      int d = v - wbuf[w][u];
      if (d <= 1 && d >= -1) m |= 1ULL << u;
    }
    allow[v - L] = m;
  }
  int d0 = rho[i] - wbuf[w][0];
  if (d0 > 1 || d0 < -1) return 0;
  u64 g = allow[rho[n - 1] - L];
  for (int t = n - 2; t >= i; t--) g = allow[rho[t] - L] & nbr(g, full);
  u64 h = allow[rho[0] - L];
  for (int t = 1; t <= i; t++) h = allow[rho[t] - L] & nbr(h, full);
  return (g & h & 1ULL) != 0ULL;
}

static void print_ts(int w) {
  printf("[");
  for (int j = 0; j < tslenA[w]; j++) printf("%s%d", j ? ", " : "", tsbuf_all[w][j]);
  printf("]");
}

/* Report every minimal turning sequence at basepoint i. */
static void report_basepoint(const int *rho, int n, int i, int variant) {
  int L = rho[0], H = rho[0];
  for (int t = 1; t < n; t++) { if (rho[t] < L) L = rho[t]; if (rho[t] > H) H = rho[t]; }
  build_walks(L, H, variant);
  int best = -1, cnt = 0;
  for (int wi = 0; wi < nw; wi++) {
    int w = order[wi];
    if (best >= 0 && wturns[w] > best) break;
    if (!walk_serves(rho, n, L, H, w, i)) continue;
    if (best < 0) best = wturns[w];
    if (wturns[w] == best) {
      if (cnt < 16) { printf("      "); print_ts(w); printf("\n"); }
      cnt++;
    }
  }
  printf("    basepoint %d (level %d): %d minimal itineraries with %d turning targets\n",
         i, rho[i], cnt, best);
}

/* ------------------------------------------------- faithfulness (for a hit) */

static int faithful(const int *rho, int n) {
  for (int t = 0; t + 1 < n; t++) {
    int d = rho[t + 1] - rho[t];
    if (d > 1 || d < -1) return 0;
  }
  for (int s = 0; s < n; s++)
    for (int t = s + 1; t < n; t++)
      for (int hs = -1; hs <= 1; hs++) {
        if (s + hs < 0 || s + hs >= n) continue;
        int h = rho[s + hs];
        for (int ks = -1; ks <= 1; ks++) {
          if (t + ks < 0 || t + ks >= n) continue;
          int k = rho[t + ks];
          int ad = h - k; if (ad < 0) ad = -ad;
          if (ad < 3) continue;
          int w1 = (h < k) ? k - 1 : k + 1;
          int w2 = (h < k) ? h + 1 : h - 1;
          int ok = 0;
          for (int r = s + 1; r < t && !ok; r++)
            if (rho[r] == w1)
              for (int r2 = r + 1; r2 < t; r2++)
                if (rho[r2] == w2) { ok = 1; break; }
          if (!ok) return 0;
        }
      }
  return 1;
}

/* ------------------------------------------------------------------ main  */

static unsigned long long rstate;
static unsigned long long rnd(void) {
  rstate ^= rstate << 13; rstate ^= rstate >> 7; rstate ^= rstate << 17;
  return rstate;
}

static int subbuf[MAXN];

static void base_levels(int L, int H, int variant) {
  build_walks(L, H, variant);
  int seen[64]; memset(seen, 0, sizeof(seen));
  for (int w = 0; w < nw; w++) seen[wbuf[w][0] - L] = 1;
  printf("  band [%d, %d] variant %d: %d zig sequences; base levels used:", L, H, variant, nw);
  for (int v = 0; v <= H - L; v++) if (seen[v]) printf(" %d", L + v);
  printf("\n");
}

int main(int argc, char **argv) {
  rstate = (argc > 1) ? (unsigned long long)atoll(argv[1]) : 28ULL;

  printf("=== which base levels a zig sequence can start from ===\n");
  for (int H = 4; H <= 12; H++) { base_levels(0, H, 0); base_levels(0, H, 1); }

  for (int variant = 0; variant <= 1; variant++) {
    printf("\n=== variant %d: whole chains ===\n", variant);
    for (int N = 4; N <= 12; N++) {
      Path p = bpath(0, N);
      if (p.n > MAXN) { printf("bing 0 %d: %d links -- too long\n", N, p.n); free(p.v); continue; }
      int mx, be, bo;
      census_chain(p.v, p.n, variant, &be, &bo, &mx);
      printf("bing 0 %2d: %6d links, span %2d ... unserved at extreme levels: %d ; "
             "unserved elsewhere: %d ; max minimal turning targets: %d\n",
             N, p.n, N, be, bo, mx);
      fflush(stdout);
      if (bo > 0) {
        printf("  NON-STRUCTURAL FAILURE at basepoints:");
        int shown = 0;
        for (int i = 0; i < p.n && shown < 20; i++)
          if (minturns[i] < 0 && p.v[i] != 0 && p.v[i] != N) { printf(" %d(level %d)", i, p.v[i]); shown++; }
        printf("\n");
      }
      free(p.v);
    }

    /* the hardest basepoints of spans 11 and 12 */
    for (int N = 11; N <= 12; N++) {
      Path p = bpath(0, N);
      int mx, be, bo;
      census_chain(p.v, p.n, variant, &be, &bo, &mx);
      int cnt = 0;
      for (int i = 0; i < p.n; i++) if (minturns[i] == mx) cnt++;
      printf("\nvariant %d, span %d: %d basepoints attain the maximum %d; first few, "
             "with all minimal itineraries:\n", variant, N, cnt, mx);
      int shown = 0;
      static int save[MAXN];
      for (int i = 0; i < p.n && shown < 2; i++)
        if (minturns[i] == mx) {
          memcpy(save, minturns, sizeof(int) * p.n);
          report_basepoint(p.v, p.n, i, variant);
          memcpy(minturns, save, sizeof(int) * p.n);
          shown++;
        }
      fflush(stdout);
      free(p.v);
    }

    /* subchains of bing 0 12 of span >= 9: random */
    {
      Path p = bpath(0, 12);
      int n = p.n;
      long tested = 0, badsub = 0, badpts = 0;
      long hist[32]; memset(hist, 0, sizeof(hist));
      int nsub = 4000;
      for (int it = 0; it < nsub; it++) {
        int a, b, L, H, tries = 0;
        do {
          a = (int)(rnd() % (unsigned)(n - 1));
          int rem = n - a, lenmax = rem < 4000 ? rem : 4000;
          b = a + 1 + (int)(rnd() % (unsigned)lenmax);
          if (b >= n) b = n - 1;
          L = H = p.v[a];
          for (int t = a; t <= b; t++) { if (p.v[t] < L) L = p.v[t]; if (p.v[t] > H) H = p.v[t]; }
          tries++;
        } while (H - L < 9 && tries < 200);
        if (H - L < 9) continue;
        int m = b - a + 1;
        memcpy(subbuf, p.v + a, sizeof(int) * m);
        int mx, be, bo;
        census_chain(subbuf, m, variant, &be, &bo, &mx);
        tested++;
        if (mx >= 0 && mx < 32) hist[mx]++;
        if (bo > 0) {
          badsub++; badpts += bo;
          printf("  SUBCHAIN NON-STRUCTURAL FAILURE [%d, %d] span %d: %d basepoints; faithful=%d\n",
                 a, b, H - L, bo, m <= 600 ? faithful(subbuf, m) : -1);
          for (int i = 0, s = 0; i < m && s < 6; i++)
            if (minturns[i] < 0 && subbuf[i] != L && subbuf[i] != H) {
              printf("    basepoint %d (level %d)\n", i, subbuf[i]); s++;
            }
          fflush(stdout);
        }
      }
      printf("variant %d, random subchains of bing 0 12 of span >= 9: tested %ld, "
             "subchains with a non-structural failure %ld (%ld basepoints)\n",
             variant, tested, badsub, badpts);
      printf("  max minimal turning targets, distribution:");
      for (int k = 0; k < 32; k++) if (hist[k]) printf(" %d:%ld", k, hist[k]);
      printf("\n");
      free(p.v);
    }

    /* subchains of bing 0 12 of span >= 9: grid */
    {
      Path p = bpath(0, 12);
      int n = p.n;
      long tested = 0, badsub = 0, badpts = 0;
      int stride = 97;
      for (int a = 0; a < n; a += stride)
        for (int b = a + 1; b < n; b += stride) {
          int L = p.v[a], H = p.v[a];
          for (int t = a; t <= b; t++) { if (p.v[t] < L) L = p.v[t]; if (p.v[t] > H) H = p.v[t]; }
          if (H - L < 9) continue;
          int m = b - a + 1;
          memcpy(subbuf, p.v + a, sizeof(int) * m);
          int mx, be, bo;
          census_chain(subbuf, m, variant, &be, &bo, &mx);
          tested++;
          if (bo > 0) {
            badsub++; badpts += bo;
            printf("  GRID SUBCHAIN NON-STRUCTURAL FAILURE [%d, %d] span %d: %d basepoints\n",
                   a, b, H - L, bo);
            fflush(stdout);
          }
        }
      printf("variant %d, grid subchains of bing 0 12 (stride %d) of span >= 9: tested %ld, "
             "subchains with a non-structural failure %ld (%ld basepoints)\n",
             variant, stride, tested, badsub, badpts);
      free(p.v);
    }
  }
  return 0;
}
