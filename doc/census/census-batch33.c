/* Census for batch 33 -- the pair of arms, and the outside-in trimming.
 *
 * Conventions are batches 28-32's.  An itinerary is a base centre ts[0]
 * followed by turning targets ts[1..k], all in [L+1, H-1], directions
 * alternating, amplitudes strictly increasing after the first (the free
 * family `IsZigFree`), the last two targets being the two extreme bands in
 * either order.  The walk is one level per step through those targets.  A
 * sequence f folds onto a walk iff there is a 1-Lipschitz time assignment
 * starting at time 0 with every level within one of its time's centre; that
 * is decided exactly by reachability over the walk's times (a bitmask sweep).
 *
 * Sections:
 *   1. the two stretches A (forward from index 57) and B (backward from
 *      index 13) of `bing 0 6`: that they are what COMMISSION-batch33 says,
 *      that each is 1-Lipschitz and faithful-crooked (the decidable form of
 *      `IsCrookedIvF` with sigma = rho), the whole free family of the band
 *      [0,6], which members serve A, which serve B, and that none serves
 *      both.  Folding is computed twice, by a forward and by a backward
 *      sweep, and the two are compared.
 *   2. all arms of `bing 0 6`: every pair of arms starting at a common level
 *      that is served by no common member of the family, and whether the two
 *      arms of any single basepoint form such a pair.
 *   3. the outside-in trimming of COMMISSION-batch33 section 3: for each
 *      basepoint of `bing 0 n`, n = 6..12, the maximal contiguous stretch
 *      containing it whose span is at most one less, iterated; how the span,
 *      the basepoint's level within the inner band and its position inside
 *      the stretch move at each step, and whether the trimming degenerates.
 *      Both greedy expansion orders (left first, right first) are computed
 *      and compared.
 *
 * Usage: census-batch33
 */

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 u128;

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

/* -------------------------------------------------- the faithful model */

/* The decidable form of `IsCrookedIvF` with sigma = rho: the width and
   adjacency clauses are the Lipschitz condition, and the crookedness clause
   quantifies over pairs of indices and the levels they meet. */
static int is_lip(const int *r, int n) {
  for (int i = 0; i + 1 < n; i++) {
    int d = r[i + 1] - r[i];
    if (d > 1 || d < -1) return 0;
  }
  return 1;
}

/* level h is met at index s: sigma = rho, so h is the level of s-1, s or s+1 */
static int meets(const int *r, int n, int s, int h) {
  if (r[s] == h) return 1;
  if (s > 0 && r[s - 1] == h) return 1;
  if (s + 1 < n && r[s + 1] == h) return 1;
  return 0;
}

static int is_crooked(const int *r, int n, int verbose) {
  int lo = r[0], hi = r[0];
  for (int i = 1; i < n; i++) { if (r[i] < lo) lo = r[i]; if (r[i] > hi) hi = r[i]; }
  for (int s = 0; s < n; s++)
    for (int t = s + 1; t < n; t++)
      for (int h = lo; h <= hi; h++) {
        if (!meets(r, n, s, h)) continue;
        for (int k = lo; k <= hi; k++) {
          if (!meets(r, n, t, k)) continue;
          int d = h - k; if (d < 0) d = -d;
          if (d < 3) continue;
          int want1 = (h < k) ? k - 1 : k + 1;
          int want2 = (h < k) ? h + 1 : h - 1;
          int ok = 0;
          for (int p = s + 1; p < t && !ok; p++) {
            if (r[p] != want1) continue;
            for (int q = p + 1; q < t; q++) if (r[q] == want2) { ok = 1; break; }
          }
          if (!ok) {
            if (verbose)
              printf("    crookedness fails at s=%d t=%d h=%d k=%d\n", s, t, h, k);
            return 0;
          }
        }
      }
  return 1;
}

/* ---------------------------------------------------------- the walks */

#define MAXW 160
#define MAXTS 24

typedef struct {
  int k;               /* number of turning targets after the base centre */
  int ts[MAXTS];
  int len;
  signed char w[MAXW];
} Walk;

static Walk *walks = NULL;
static int nwalks = 0, capwalks = 0;
static int ts[MAXTS];
static int bandL, bandH;

static void walk_of(int k, signed char *w, int *lenout) {
  int len = 0;
  w[len++] = (signed char)ts[0];
  for (int j = 1; j <= k; j++) {
    if (ts[j] == ts[j - 1]) continue;
    int d = ts[j] > ts[j - 1] ? 1 : -1;
    for (int x = ts[j - 1] + d;; x += d) {
      if (len >= MAXW) { fprintf(stderr, "walk overflow\n"); exit(1); }
      w[len++] = (signed char)x;
      if (x == ts[j]) break;
    }
  }
  *lenout = len;
}

static void push_walk(int k) {
  if (nwalks == capwalks) {
    capwalks = capwalks ? capwalks * 2 : 1024;
    walks = (Walk *)realloc(walks, sizeof(Walk) * capwalks);
  }
  Walk *W = &walks[nwalks++];
  W->k = k;
  for (int j = 0; j <= k; j++) W->ts[j] = ts[j];
  walk_of(k, W->w, &W->len);
}

static void dfs(int j, int k, int lastamp, int lastdir) {
  if (j == k) {
    int a = ts[j - 1], b = ts[j];
    if ((a == bandL + 1 && b == bandH - 1) || (a == bandH - 1 && b == bandL + 1))
      push_walk(k);
    return;
  }
  int cur = ts[j];
  int minamp = (j <= 1) ? 1 : lastamp + 1;
  for (int dir = -1; dir <= 1; dir += 2) {
    if (lastdir != 0 && dir == lastdir) continue;
    for (int amp = minamp;; amp++) {
      int nxt = cur + dir * amp;
      if (nxt < bandL + 1 || nxt > bandH - 1) break;
      ts[j + 1] = nxt;
      dfs(j + 1, k, amp, dir);
    }
  }
}

static void enumerate_family(int L, int H, int kmax) {
  bandL = L; bandH = H; nwalks = 0;
  for (int k = 2; k <= kmax; k++)
    for (int c = L + 1; c <= H - 1; c++) { ts[0] = c; dfs(0, k, 0, 0); }
}

static void print_ts(const Walk *W) {
  printf("[");
  for (int j = 0; j <= W->k; j++) printf("%s%d", j ? ", " : "", W->ts[j]);
  printf("]");
}

/* ------------------------------------------------------------- folding */

/* Forward reachability: R_0 = {0} inter allow(f_0), R_{j+1} = nbr(R_j) inter
   allow(f_{j+1}).  f folds onto w iff the last set is nonempty. */
static int folds_fwd(const signed char *w, int len, const int *f, int m) {
  u128 one = 1;
  u128 full = (len >= 128) ? ~(u128)0 : ((one << len) - 1);
  u128 R = 0;
  for (int u = 0; u < len; u++) { int d = f[0] - w[u]; if (d <= 1 && d >= -1) R |= one << u; }
  R &= one;
  for (int j = 1; j < m; j++) {
    u128 allow = 0;
    for (int u = 0; u < len; u++) { int d = f[j] - w[u]; if (d <= 1 && d >= -1) allow |= one << u; }
    R = ((R << 1) | R | (R >> 1)) & full & allow;
    if (!R) return 0;
  }
  return R != 0;
}

/* Backward reachability, the independent implementation: B_{m-1} = allow,
   B_j = allow(f_j) inter nbr(B_{j+1}); folds iff time 0 is in B_0. */
static int folds_bwd(const signed char *w, int len, const int *f, int m) {
  u128 one = 1;
  u128 full = (len >= 128) ? ~(u128)0 : ((one << len) - 1);
  u128 B = 0;
  for (int u = 0; u < len; u++) { int d = f[m - 1] - w[u]; if (d <= 1 && d >= -1) B |= one << u; }
  for (int j = m - 2; j >= 0; j--) {
    u128 allow = 0;
    for (int u = 0; u < len; u++) { int d = f[j] - w[u]; if (d <= 1 && d >= -1) allow |= one << u; }
    B = allow & ((B << 1) | B | (B >> 1)) & full;
    if (!B) return 0;
  }
  return (B & one) != 0;
}

/* ============================================================ section 1 */

static int A14[14], B14[14];

static void section1(void) {
  Path p = bpath(0, 6);
  printf("\n===== 1. the two stretches of bing 0 6 =====\n");
  printf("  bing 0 6 has %d links\n", p.n);
  printf("  rho =");
  for (int i = 0; i < p.n; i++) printf(" %d", p.v[i]);
  printf("\n");
  for (int i = 0; i < 14; i++) A14[i] = p.v[57 + i];
  for (int i = 0; i < 14; i++) B14[i] = p.v[13 - i];
  printf("  A (forward from 57) =");
  for (int i = 0; i < 14; i++) printf(" %d", A14[i]);
  printf("\n  B (backward from 13) =");
  for (int i = 0; i < 14; i++) printf(" %d", B14[i]);
  printf("\n");
  int cA[14] = {3, 2, 3, 4, 3, 4, 5, 4, 3, 4, 5, 4, 5, 6};
  int cB[14] = {3, 4, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 0};
  int okA = 1, okB = 1;
  for (int i = 0; i < 14; i++) { okA &= (A14[i] == cA[i]); okB &= (B14[i] == cB[i]); }
  printf("  A matches the commissioned list: %s\n", okA ? "yes" : "NO");
  printf("  B matches the commissioned list: %s\n", okB ? "yes" : "NO");
  printf("  B = 6 - A pointwise: ");
  { int ok = 1; for (int i = 0; i < 14; i++) ok &= (B14[i] == 6 - A14[i]);
    printf("%s\n", ok ? "yes" : "NO"); }
  printf("  A is 1-Lipschitz: %s;  faithful crooked (sigma = rho): %s\n",
         is_lip(A14, 14) ? "yes" : "NO", is_crooked(A14, 14, 1) ? "yes" : "NO");
  printf("  B is 1-Lipschitz: %s;  faithful crooked (sigma = rho): %s\n",
         is_lip(B14, 14) ? "yes" : "NO", is_crooked(B14, 14, 1) ? "yes" : "NO");
  printf("  bing 0 6 itself is 1-Lipschitz: %s;  faithful crooked: %s\n",
         is_lip(p.v, p.n) ? "yes" : "NO", is_crooked(p.v, p.n, 0) ? "yes" : "NO");

  enumerate_family(0, 6, 12);
  printf("\n  the free family of the band [0,6] has %d members\n", nwalks);
  int nA = 0, nB = 0, nboth = 0, disagree = 0;
  int firstA = -1, firstB = -1;
  for (int a = 0; a < nwalks; a++) {
    int fa = folds_fwd(walks[a].w, walks[a].len, A14, 14);
    int fb = folds_fwd(walks[a].w, walks[a].len, B14, 14);
    int ga = folds_bwd(walks[a].w, walks[a].len, A14, 14);
    int gb = folds_bwd(walks[a].w, walks[a].len, B14, 14);
    if (fa != ga || fb != gb) disagree++;
    nA += fa; nB += fb; nboth += (fa && fb);
    if (fa && firstA < 0) firstA = a;
    if (fb && firstB < 0) firstB = a;
  }
  printf("  forward and backward sweeps disagree on %d members\n", disagree);
  printf("  members serving A: %d;  serving B: %d;  serving both: %d\n", nA, nB, nboth);
  printf("  every member, with what it serves:\n");
  for (int a = 0; a < nwalks; a++) {
    int fa = folds_fwd(walks[a].w, walks[a].len, A14, 14);
    int fb = folds_fwd(walks[a].w, walks[a].len, B14, 14);
    printf("    %2d ", a);
    print_ts(&walks[a]);
    printf("  len %2d  A:%s B:%s\n", walks[a].len, fa ? "yes" : "no ", fb ? "yes" : "no ");
  }
  if (firstA >= 0) { printf("  shortest-found walk serving A: "); print_ts(&walks[firstA]); printf("\n"); }
  if (firstB >= 0) { printf("  shortest-found walk serving B: "); print_ts(&walks[firstB]); printf("\n"); }

  /* the two walks the batch uses in Lean, and the two the commission names */
  int probes[4][6] = {{2, 3, 5, 1, 0, 0}, {2, 3, 1, 5, 0, 0},
                      {4, 3, 2, 4, 1, 5}, {4, 3, 4, 2, 5, 1}};
  for (int q = 0; q < 4; q++) {
    int k = probes[q][0];
    for (int j = 0; j <= k; j++) ts[j] = probes[q][1 + j];
    signed char w[MAXW]; int len;
    walk_of(k, w, &len);
    printf("  probe [");
    for (int j = 0; j <= k; j++) printf("%s%d", j ? ", " : "", ts[j]);
    printf("]  walk");
    for (int u = 0; u < len; u++) printf(" %d", w[u]);
    printf("  A:%s B:%s\n", folds_fwd(w, len, A14, 14) ? "yes" : "no",
           folds_fwd(w, len, B14, 14) ? "yes" : "no");
  }
  free(p.v);
}

/* ============================================================ section 2 */

/* Every arm of bing 0 6: forward and backward from each index.  Which pairs
   of arms starting at a common level are served by no common member. */
static void section2(void) {
  Path p = bpath(0, 6);
  int n = p.n;
  enumerate_family(0, 6, 12);
  printf("\n===== 2. all arms of bing 0 6 against the family =====\n");
  int narms = 2 * n;
  int **arm = (int **)malloc(sizeof(int *) * narms);
  int *alen = (int *)malloc(sizeof(int) * narms);
  int *abase = (int *)malloc(sizeof(int) * narms);
  int *alevel = (int *)malloc(sizeof(int) * narms);
  for (int i = 0; i < n; i++) {
    int g = 2 * i, t = 2 * i + 1;
    alen[g] = n - i; arm[g] = (int *)malloc(sizeof(int) * alen[g]);
    for (int j = 0; j < alen[g]; j++) arm[g][j] = p.v[i + j];
    alen[t] = i + 1; arm[t] = (int *)malloc(sizeof(int) * alen[t]);
    for (int j = 0; j < alen[t]; j++) arm[t][j] = p.v[i - j];
    abase[g] = abase[t] = i; alevel[g] = alevel[t] = p.v[i];
  }
  unsigned char *tab = (unsigned char *)malloc((size_t)nwalks * narms);
  for (int a = 0; a < nwalks; a++)
    for (int s = 0; s < narms; s++)
      tab[(size_t)a * narms + s] = (unsigned char)folds_fwd(walks[a].w, walks[a].len, arm[s], alen[s]);
  int unserved_arms = 0;
  for (int s = 0; s < narms; s++) {
    int any = 0;
    for (int a = 0; a < nwalks && !any; a++) any = tab[(size_t)a * narms + s];
    if (!any) unserved_arms++;
  }
  printf("  arms: %d;  arms served by no member at all: %d\n", narms, unserved_arms);
  int basepoints_served = 0;
  for (int i = 0; i < n; i++) {
    int any = 0;
    for (int a = 0; a < nwalks && !any; a++)
      any = tab[(size_t)a * narms + 2 * i] && tab[(size_t)a * narms + 2 * i + 1];
    basepoints_served += any;
    if (!any) printf("    basepoint %d (level %d) served by no member\n", i, p.v[i]);
  }
  printf("  basepoints of bing 0 6 served by some member: %d of %d\n", basepoints_served, n);

  /* pairs of arms at a common level, each served alone, none in common */
  int npairs = 0, npairs_same_base = 0, npairs_distinct = 0;
  printf("  pairs of arms at a common level served by no common member:\n");
  for (int s = 0; s < narms; s++) {
    int anys = 0;
    for (int a = 0; a < nwalks && !anys; a++) anys = tab[(size_t)a * narms + s];
    if (!anys) continue;
    for (int t = s + 1; t < narms; t++) {
      if (alevel[s] != alevel[t]) continue;
      int anyt = 0;
      for (int a = 0; a < nwalks && !anyt; a++) anyt = tab[(size_t)a * narms + t];
      if (!anyt) continue;
      int both = 0;
      for (int a = 0; a < nwalks && !both; a++)
        both = tab[(size_t)a * narms + s] && tab[(size_t)a * narms + t];
      if (both) continue;
      npairs++;
      if (abase[s] == abase[t]) npairs_same_base++; else npairs_distinct++;
      if (npairs <= 40) {
        printf("    %s from %d  and  %s from %d   (level %d)\n",
               (s % 2) ? "backward" : "forward ", abase[s],
               (t % 2) ? "backward" : "forward ", abase[t], alevel[s]);
      }
    }
  }
  printf("  such pairs: %d  (from the same basepoint: %d;  from different basepoints: %d)\n",
         npairs, npairs_same_base, npairs_distinct);

  /* up to equality of the underlying sequences */
  printf("  distinct as sequences: ");
  {
    int cnt = 0;
    for (int s = 0; s < narms; s++)
      for (int t = s + 1; t < narms; t++) {
        if (alevel[s] != alevel[t]) continue;
        if (alen[s] == alen[t]) {
          int same = 1;
          for (int j = 0; j < alen[s]; j++) if (arm[s][j] != arm[t][j]) { same = 0; break; }
          if (same) continue;
        }
        int anys = 0, anyt = 0, both = 0;
        for (int a = 0; a < nwalks; a++) {
          anys |= tab[(size_t)a * narms + s];
          anyt |= tab[(size_t)a * narms + t];
          both |= tab[(size_t)a * narms + s] && tab[(size_t)a * narms + t];
        }
        if (anys && anyt && !both) cnt++;
      }
    printf("%d\n", cnt);
  }
  for (int s = 0; s < narms; s++) free(arm[s]);
  free(arm); free(alen); free(abase); free(alevel); free(tab); free(p.v);
}

/* ============================================================ section 3 */

/* The outside-in trimming: the maximal contiguous stretch [a,b] of [lo,hi]
   containing i whose span is at most `cap`.  Two greedy orders. */
static void trim(const int *r, int lo, int hi, int i, int cap, int leftfirst,
                 int *ao, int *bo) {
  int a = i, b = i, mn = r[i], mx = r[i];
  int grow = 1;
  while (grow) {
    grow = 0;
    for (int pass = 0; pass < 2; pass++) {
      int left = leftfirst ? (pass == 0) : (pass == 1);
      if (left) {
        while (a > lo) {
          int nm = mn < r[a - 1] ? mn : r[a - 1];
          int nx = mx > r[a - 1] ? mx : r[a - 1];
          if (nx - nm > cap) break;
          a--; mn = nm; mx = nx; grow = 1;
        }
      } else {
        while (b < hi) {
          int nm = mn < r[b + 1] ? mn : r[b + 1];
          int nx = mx > r[b + 1] ? mx : r[b + 1];
          if (nx - nm > cap) break;
          b++; mn = nm; mx = nx; grow = 1;
        }
      }
    }
    if (!leftfirst) break;
    break;
  }
  *ao = a; *bo = b;
}

static void section3(void) {
  printf("\n===== 3. the outside-in trimming =====\n");
  printf("  For each basepoint i of bing 0 n, the maximal contiguous stretch\n"
         "  containing i whose span is at most one less than the current one,\n"
         "  iterated until the span is at most 3.  Reported: how the span moves,\n"
         "  whether the basepoint stays strictly inside the stretch, and whether\n"
         "  its level is interior to the inner band.\n");
  for (int nn = 6; nn <= 12; nn++) {
    Path p = bpath(0, nn);
    int n = p.n;
    int maxsteps = 0, degen_end = 0, degen_extreme = 0, orders_differ = 0;
    int span_stuck = 0;
    long long totsteps = 0;
    int first_extreme_example = -1;
    for (int i = 0; i < n; i++) {
      int lo = 0, hi = n - 1, L = 0, H = nn;
      int steps = 0;
      int sawend = 0, sawextreme = 0;
      while (H - L > 3) {
        int a1, b1, a2, b2;
        trim(p.v, lo, hi, i, H - L - 1, 1, &a1, &b1);
        trim(p.v, lo, hi, i, H - L - 1, 0, &a2, &b2);
        if (a1 != a2 || b1 != b2) orders_differ++;
        int a = a1, b = b1;
        int mn = p.v[a], mx = p.v[a];
        for (int q = a; q <= b; q++) { if (p.v[q] < mn) mn = p.v[q]; if (p.v[q] > mx) mx = p.v[q]; }
        if (mx - mn >= H - L) { span_stuck++; break; }
        if (a == i || b == i) sawend = 1;
        if (p.v[i] == mn || p.v[i] == mx) {
          sawextreme = 1;
          if (first_extreme_example < 0) first_extreme_example = i;
        }
        lo = a; hi = b; L = mn; H = mx;
        steps++;
        if (steps > 100) { printf("    runaway at i=%d\n", i); break; }
      }
      totsteps += steps;
      if (steps > maxsteps) maxsteps = steps;
      degen_end += sawend;
      degen_extreme += sawextreme;
    }
    printf("  span %2d  links %5d :  steps max %d, mean %.2f;  span never stalls: %s;\n"
           "            basepoint becomes an endpoint of the stretch at %d of %d basepoints;\n"
           "            basepoint sits at an extreme level of an inner band at %d of %d;\n"
           "            the two greedy orders differ in %d steps\n",
           nn, n, maxsteps, (double)totsteps / n, span_stuck ? "NO" : "yes",
           degen_end, n, degen_extreme, n, orders_differ);
    free(p.v);
  }

  /* one trace, printed in full */
  printf("\n  a full trace, bing 0 8 at basepoint 57:\n");
  {
    Path p = bpath(0, 8);
    int i = 57, lo = 0, hi = p.n - 1, L = 0, H = 8, step = 0;
    printf("    step 0: stretch [%d,%d] band [%d,%d] span %d, level %d\n", lo, hi, L, H, H - L, p.v[i]);
    while (H - L > 3 && step < 20) {
      int a, b;
      trim(p.v, lo, hi, i, H - L - 1, 1, &a, &b);
      int mn = p.v[a], mx = p.v[a];
      for (int q = a; q <= b; q++) { if (p.v[q] < mn) mn = p.v[q]; if (p.v[q] > mx) mx = p.v[q]; }
      step++;
      printf("    step %d: stretch [%d,%d] (%d links) band [%d,%d] span %d, level %d%s%s\n",
             step, a, b, b - a + 1, mn, mx, mx - mn, p.v[i],
             (a == i || b == i) ? "  [basepoint at an end]" : "",
             (p.v[i] == mn || p.v[i] == mx) ? "  [basepoint at an extreme level]" : "");
      if (mx - mn >= H - L) { printf("    span stalled\n"); break; }
      lo = a; hi = b; L = mn; H = mx;
    }
    free(p.v);
  }
}

int main(void) {
  printf("census for batch 33\n");
  section1();
  section2();
  section3();
  printf("\ndone\n");
  return 0;
}
