/* Census for batch 32 -- the cover of a band by walks of the free family.
 *
 * Conventions are batches 28-31's.  An itinerary is a base centre ts[0]
 * followed by k turning targets ts[1..k], all in [L+1, H-1], directions
 * alternating, amplitudes strictly increasing after the first (the free
 * family `IsZigFree`), and ending at the two extreme bands in either order.
 * The walk is one level per step through those targets.  `FoldsOnto` of both
 * arms of a basepoint onto that walk is decided exactly by reachability over
 * the walk's times (bitmask sweep, one O(n) pass per walk resolving every
 * basepoint at once).
 *
 * Sections:
 *   1. enumerate the whole free family of a band and, for each span 6..12 of
 *      `bing 0 n`, compute a greedy minimum cover of all basepoints by walks:
 *      the walks and what each covers.
 *   2. the same restricted to interior basepoints (L+3 <= level <= H-3).
 *   3. lower bounds on the cover: the level-gap bound (two basepoints whose
 *      levels differ by 3 or more are served by no common walk, because
 *      `FoldsOnto` pins the walk's first value to within one of the
 *      basepoint's level), and a greedy independent set of basepoints with
 *      pairwise disjoint serving sets.
 *   4. exact minimum cover by branch and bound, under a node budget.
 *   5. the candidate rules: the backward-read targets of COMMISSION §1 and the
 *      outward alternation from the base, checked at every basepoint.
 *   6. the ordinary item: the smallest chain on which one walk does not serve
 *      every basepoint, with an explicit pair of basepoints served by no
 *      common walk and the two levels involved.
 *
 * Usage: census-batch32
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

/* -------------------------------------------------------------- the sweep */

#define MAXN 20000
#define MAXW 128
#define MAXTS 20

static u128 Gm[MAXN], Tm[MAXN];
static int chainN;
static const int *chainV;
static int chainL, chainH;

static inline u128 nbr(u128 m, u128 full) { return (m | (m << 1) | (m >> 1)) & full; }

static void set_band(const int *rho, int n) {
  chainV = rho; chainN = n;
  chainL = chainH = rho[0];
  for (int i = 1; i < n; i++) {
    if (rho[i] < chainL) chainL = rho[i];
    if (rho[i] > chainH) chainH = rho[i];
  }
}

/* served[i] = 1 iff both arms of basepoint i fold onto the walk w. */
static void sweep(const signed char *w, int len, unsigned char *served) {
  u128 one = (u128)1;
  u128 full = (len >= 128) ? ~(u128)0 : ((one << len) - 1);
  u128 allow[64];
  for (int v = chainL; v <= chainH; v++) {
    u128 m = 0;
    for (int u = 0; u < len; u++) {
      int d = v - w[u];
      if (d <= 1 && d >= -1) m |= one << u;
    }
    allow[v - chainL] = m;
  }
  int n = chainN;
  Gm[n - 1] = allow[chainV[n - 1] - chainL];
  for (int i = n - 2; i >= 0; i--) Gm[i] = allow[chainV[i] - chainL] & nbr(Gm[i + 1], full);
  Tm[0] = allow[chainV[0] - chainL];
  for (int i = 1; i < n; i++) Tm[i] = allow[chainV[i] - chainL] & nbr(Tm[i - 1], full);
  for (int i = 0; i < n; i++) served[i] = ((Gm[i] & Tm[i] & one) != 0);
}

/* -------------------------------------------------- itinerary enumeration */

typedef struct {
  int k;               /* number of turning targets                          */
  int ts[MAXTS];       /* base centre then targets                           */
  int len;             /* walk length                                        */
  signed char w[MAXW]; /* the walk                                           */
} Walk;

static Walk *walks = NULL;
static int nwalks = 0, capwalks = 0;
static int ts[MAXTS];

static void walk_of(int k, signed char *w, int *lenout) {
  int len = 0;
  w[len++] = (signed char)ts[0];
  for (int j = 1; j <= k; j++) {
    if (ts[j] == ts[j - 1]) continue;   /* stepRun a a = [] */
    int d = ts[j] > ts[j - 1] ? 1 : -1;
    for (int x = ts[j - 1] + d;; x += d) {
      if (len >= MAXW) { fprintf(stderr, "overflow k=%d ts:", k); for (int q = 0; q <= k; q++) fprintf(stderr, " %d", ts[q]); fprintf(stderr, "\n"); exit(1); }
      w[len++] = (signed char)x;
      if (x == ts[j]) break;
    }
  }
  *lenout = len;
}

/* Membership in the free family `IsZigFree`: entries in [L+1,H-1], at least
   three of them, directions alternating, amplitudes strictly increasing from
   the second on, last two entries the two extreme bands in either order. */
static int is_free_family(const int *t, int k) {
  if (k + 1 < 3) return 0;
  for (int j = 0; j <= k; j++) if (t[j] < chainL + 1 || t[j] > chainH - 1) return 0;
  for (int j = 0; j + 2 <= k; j++)
    if ((long)(t[j + 1] - t[j]) * (long)(t[j + 2] - t[j + 1]) >= 0) return 0;
  for (int j = 1; j + 2 <= k; j++) {
    int a1 = abs(t[j + 1] - t[j]), a2 = abs(t[j + 2] - t[j + 1]);
    if (!(a1 < a2)) return 0;
  }
  int a = t[k - 1], b = t[k];
  if (!((a == chainL + 1 && b == chainH - 1) || (a == chainH - 1 && b == chainL + 1))) return 0;
  return 1;
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

/* All free-family itineraries with k targets ending at the extreme bands. */
static void dfs(int j, int k, int lastamp, int lastdir) {
  if (j == k) {
    int a = ts[j - 1], b = ts[j];
    if ((a == chainL + 1 && b == chainH - 1) || (a == chainH - 1 && b == chainL + 1))
      push_walk(k);
    return;
  }
  int cur = ts[j];
  int minamp = (j <= 1) ? 1 : lastamp + 1;
  for (int dir = -1; dir <= 1; dir += 2) {
    if (lastdir != 0 && dir == lastdir) continue;
    for (int amp = minamp;; amp++) {
      int nxt = cur + dir * amp;
      if (nxt < chainL + 1 || nxt > chainH - 1) break;
      ts[j + 1] = nxt;
      dfs(j + 1, k, amp, dir);
    }
  }
}

static void enumerate_family(int kmax) {
  nwalks = 0;
  for (int k = 2; k <= kmax; k++)
    for (int c = chainL + 1; c <= chainH - 1; c++) { ts[0] = c; dfs(0, k, 0, 0); }
}

static void print_ts(const Walk *W) {
  printf("[");
  for (int j = 0; j <= W->k; j++) printf("%s%d", j ? ", " : "", W->ts[j]);
  printf("]");
}

/* ------------------------------------------------------------- the covers */

static unsigned char *servedTab = NULL; /* nwalks x n */

static void build_table(int n) {
  servedTab = (unsigned char *)realloc(servedTab, (size_t)nwalks * n);
  for (int a = 0; a < nwalks; a++) sweep(walks[a].w, walks[a].len, servedTab + (size_t)a * n);
}

/* Greedy cover of the basepoints selected by `sel` (NULL = all). */
static int greedy_cover(int n, const unsigned char *sel, int verbose) {
  unsigned char *need = (unsigned char *)malloc(n);
  int total = 0;
  for (int i = 0; i < n; i++) { need[i] = sel ? sel[i] : 1; total += need[i]; }
  int used = 0, covered = 0;
  while (covered < total) {
    int best = -1, bestc = 0;
    for (int a = 0; a < nwalks; a++) {
      const unsigned char *s = servedTab + (size_t)a * n;
      int c = 0;
      for (int i = 0; i < n; i++) c += (need[i] && s[i]);
      if (c > bestc) { bestc = c; best = a; }
    }
    if (best < 0) {
      int miss = 0;
      for (int i = 0; i < n; i++) miss += need[i];
      printf("    UNCOVERABLE: %d basepoints served by no walk at all\n", miss);
      for (int i = 0, shown = 0; i < n && shown < 5; i++)
        if (need[i]) { printf("      basepoint %d level %d\n", i, chainV[i]); shown++; }
      break;
    }
    const unsigned char *s = servedTab + (size_t)best * n;
    for (int i = 0; i < n; i++) if (need[i] && s[i]) { need[i] = 0; covered++; }
    used++;
    if (verbose) {
      printf("    walk %2d  ", used);
      print_ts(&walks[best]);
      printf("  covers %d more  (running %d of %d)\n", bestc, covered, total);
    }
  }
  free(need);
  return used;
}

/* ------------------------------------------- lower bounds and exact cover */

/* Greedy independent set: basepoints whose serving sets are pairwise
   disjoint.  Its size is a lower bound for the minimum cover. */
static int independent_bound(int n, const unsigned char *sel) {
  int *deg = (int *)malloc(sizeof(int) * n);
  for (int i = 0; i < n; i++) {
    deg[i] = 0;
    if (sel && !sel[i]) { deg[i] = 1 << 30; continue; }
    for (int a = 0; a < nwalks; a++) deg[i] += servedTab[(size_t)a * n + i];
  }
  unsigned char *blocked = (unsigned char *)calloc(nwalks, 1);
  int count = 0;
  for (;;) {
    int best = -1;
    for (int i = 0; i < n; i++) {
      if (deg[i] >= (1 << 30)) continue;
      int ok = 1;
      for (int a = 0; a < nwalks && ok; a++)
        if (servedTab[(size_t)a * n + i] && blocked[a]) ok = 0;
      if (!ok) { deg[i] = 1 << 30; continue; }
      if (best < 0 || deg[i] < deg[best]) best = i;
    }
    if (best < 0) break;
    count++;
    for (int a = 0; a < nwalks; a++) if (servedTab[(size_t)a * n + best]) blocked[a] = 1;
    deg[best] = 1 << 30;
  }
  free(deg); free(blocked);
  return count;
}

/* Branch and bound: is there a cover of size <= lim?  Branch on the uncovered
   basepoint with the fewest serving walks. */
static long bbnodes, bbbudget;
static int bbn;
static unsigned char *bbneed;

static int bb(int lim) {
  if (++bbnodes > bbbudget) return -1;
  int pick = -1, pickc = 1 << 30;
  for (int i = 0; i < bbn; i++) {
    if (!bbneed[i]) continue;
    int c = 0;
    for (int a = 0; a < nwalks; a++) c += servedTab[(size_t)a * bbn + i];
    if (c < pickc) { pickc = c; pick = i; }
  }
  if (pick < 0) return 1;
  if (lim == 0) return 0;
  int unknown = 0;
  for (int a = 0; a < nwalks; a++) {
    if (!servedTab[(size_t)a * bbn + pick]) continue;
    unsigned char *save = (unsigned char *)malloc(bbn);
    memcpy(save, bbneed, bbn);
    for (int i = 0; i < bbn; i++) if (servedTab[(size_t)a * bbn + i]) bbneed[i] = 0;
    int r = bb(lim - 1);
    memcpy(bbneed, save, bbn);
    free(save);
    if (r == 1) return 1;
    if (r < 0) unknown = 1;
  }
  return unknown ? -1 : 0;
}

/* Exact minimum cover, or -1 if the budget ran out. */
static int exact_cover(int n, int lo, int hi, long budget) {
  bbn = n;
  for (int lim = lo; lim <= hi; lim++) {
    bbneed = (unsigned char *)malloc(n);
    for (int i = 0; i < n; i++) bbneed[i] = 1;
    bbnodes = 0; bbbudget = budget;
    int r = bb(lim);
    free(bbneed);
    if (r == 1) return lim;
    if (r < 0) return -1;
  }
  return -2;
}

/* --------------------------------------------------------- candidate rules */

/* The backward-read targets of COMMISSION §1: H-1, L+1, H-3, L+2, H-5, ...
   stopped at floor(span/2) - 1 of them, read backwards; base free. */
static int rule_backward(int L, int H, int base, int *out) {
  int k = (H - L) / 2 - 1;
  if (k < 2) k = 2;
  int buf[MAXTS];
  for (int j = 0; j < k; j++) {
    if (j % 2 == 0) buf[j] = H - 1 - j;          /* H-1, H-3, H-5, ... */
    else buf[j] = L + 1 + (j - 1) / 2;           /* L+1, L+2, ...      */
  }
  out[0] = base;
  for (int j = 0; j < k; j++) out[1 + j] = buf[k - 1 - j];
  return k;
}

/* The outward alternation from the base with amplitudes increasing by one,
   continued until it would leave the band and then closed on the two extreme
   bands: base, base-1, base+2, base-3, ... (and its mirror). */
static int rule_outward(int L, int H, int base, int firstdown, int *out) {
  out[0] = base;
  int k = 0, cur = base, amp = 1, dir = firstdown ? -1 : 1;
  for (;;) {
    int nxt = cur + dir * amp;
    if (nxt < L + 1 || nxt > H - 1) break;
    if (k + 1 >= MAXTS - 2) break;
    out[++k] = nxt;
    cur = nxt; amp++; dir = -dir;
  }
  /* close on the extremes, keeping the alternation and never repeating */
  int lastdir = (k >= 1) ? ((out[k] > out[k - 1]) ? 1 : -1) : 0;
  if (out[k] == L + 1) out[++k] = H - 1;
  else if (out[k] == H - 1) out[++k] = L + 1;
  else {
    int a = (lastdir == 1) ? L + 1 : H - 1;
    out[++k] = a;
    out[++k] = (a == L + 1) ? H - 1 : L + 1;
  }
  return k;
}

/* An alternation from the base with amplitudes increasing by one, the first
   amplitude `a` free and the first direction `dir` free, closed on the two
   extreme bands: base, base+dir*a, base-dir*(a+1), base+dir*(a+2), ...  */
static int rule_alt(int L, int H, int base, int a, int dir, int *out) {
  out[0] = base;
  int k = 0, cur = base, amp = a, d = dir;
  for (;;) {
    int nxt = cur + d * amp;
    if (nxt < L + 1 || nxt > H - 1) break;
    if (k + 3 >= MAXTS) break;
    out[++k] = nxt;
    cur = nxt; amp++; d = -d;
  }
  int lastdir = (k >= 1) ? ((out[k] > out[k - 1]) ? 1 : -1) : 0;
  if (out[k] == L + 1) out[++k] = H - 1;
  else if (out[k] == H - 1) out[++k] = L + 1;
  else {
    int e = (lastdir == 1) ? L + 1 : H - 1;
    out[++k] = e;
    out[++k] = (e == L + 1) ? H - 1 : L + 1;
  }
  return k;
}

/* Does some member of the alternation family serve basepoint i? */
static int alt_family_serves(int n, int i, int p) {
  unsigned char *srv = (unsigned char *)malloc(n);
  int L = chainL, H = chainH, ok = 0;
  for (int db = -1; db <= 1 && !ok; db++) {
    int base = p + db;
    if (base < L + 1 || base > H - 1) continue;
    for (int a = 1; a <= H - L && !ok; a++)
      for (int dir = -1; dir <= 1 && !ok; dir += 2) {
        int cand[MAXTS];
        int k = rule_alt(L, H, base, a, dir, cand);
        if (!is_free_family(cand, k)) continue;
        for (int j = 0; j <= k; j++) ts[j] = cand[j];
        signed char w[MAXW];
        int len;
        walk_of(k, w, &len);
        sweep(w, len, srv);
        if (srv[i]) ok = 1;
      }
  }
  free(srv);
  return ok;
}

static int rule_covers(const int *rho, int n, int mode, int *failures, int interiorOnly) {
  int bad = 0;
  unsigned char *srv = (unsigned char *)malloc(n);
  int L = chainL, H = chainH;
  for (int i = 0; i < n; i++) {
    int p = rho[i];
    if (interiorOnly && (p < L + 3 || p > H - 3)) continue;
    int ok = 0;
    for (int db = -1; db <= 1 && !ok; db++) {
      int base = p + db;
      if (base < L + 1 || base > H - 1) continue;
      int cand[3][MAXTS], ck[3], nc = 0;
      if (mode == 0) { ck[nc] = rule_backward(L, H, base, cand[nc]); nc++; }
      else {
        ck[nc] = rule_outward(L, H, base, 1, cand[nc]); nc++;
        ck[nc] = rule_outward(L, H, base, 0, cand[nc]); nc++;
      }
      for (int c = 0; c < nc && !ok; c++) {
        signed char w[MAXW];
        int len;
        if (!is_free_family(cand[c], ck[c])) continue;
        for (int j = 0; j <= ck[c]; j++) ts[j] = cand[c][j];
        walk_of(ck[c], w, &len);
        sweep(w, len, srv);
        if (srv[i]) ok = 1;
      }
    }
    if (!ok) bad++;
  }
  free(srv);
  *failures = bad;
  return bad == 0;
}

/* ---------------------------------------------------------------- main */

int main(void) {
  setvbuf(stdout, NULL, _IONBF, 0);
  printf("== batch 32 census: covering a band by walks of the free family ==\n");
  printf("   walks: base in [L+1,H-1], alternating, amplitudes increasing after the first,\n");
  printf("   last two targets (L+1,H-1) or (H-1,L+1); FoldsOnto decided by reachability.\n\n");

  for (int nn = 6; nn <= 12; nn++) {
    Path p = bpath(0, nn);
    set_band(p.v, p.n);
    enumerate_family(MAXTS - 2);
    build_table(p.n);
    int interior = 0;
    unsigned char *sel = (unsigned char *)calloc(p.n, 1);
    for (int i = 0; i < p.n; i++)
      if (p.v[i] >= chainL + 3 && p.v[i] <= chainH - 3) { sel[i] = 1; interior++; }
    printf("-- bing 0 %d: %d links, band [%d,%d], %d walks in the family, %d interior\n",
           nn, p.n, chainL, chainH, nwalks, interior);
    printf("  greedy cover of ALL basepoints:\n");
    int gall = greedy_cover(p.n, NULL, 1);
    int gint = interior ? greedy_cover(p.n, sel, 0) : 0;
    int lbAll = independent_bound(p.n, NULL);
    int lbInt = interior ? independent_bound(p.n, sel) : 0;
    printf("  greedy: all %d, interior %d | disjoint-set lower bound: all %d, interior %d"
           " | level-gap bound %d\n",
           gall, gint, lbAll, lbInt, (nn + 1 + 2) / 3);
    if (nn <= 8) {
      int ex = exact_cover(p.n, lbAll, gall, 2000000L);
      if (ex >= 0) printf("  exact minimum cover of all basepoints: %d\n", ex);
      else printf("  exact minimum cover: not decided within the node budget\n");
    }
    int f0, f1;
    rule_covers(p.v, p.n, 0, &f0, 0);
    rule_covers(p.v, p.n, 1, &f1, 0);
    printf("  rule check: backward-read targets fail at %d of %d basepoints;"
           " outward alternation fails at %d of %d\n", f0, p.n, f1, p.n);
    {
      int fam = 0;
      for (int i = 0; i < p.n; i++) if (!alt_family_serves(p.n, i, p.v[i])) fam++;
      printf("  rule family (alternations from the base, first amplitude and direction free,"
             " amplitudes increasing by one): fails at %d of %d basepoints\n", fam, p.n);
    }
    free(sel);
    free(p.v);
  }

  printf("\n== the ordinary item: two basepoints served by no common walk ==\n");
  for (int nn = 4; nn <= 8; nn++) {
    Path p = bpath(0, nn);
    set_band(p.v, p.n);
    enumerate_family(MAXTS - 2);
    build_table(p.n);
    /* a pair with disjoint serving sets, preferring interior basepoints */
    int bi = -1, bj = -1, bii = -1, bjj = -1;
    for (int i = 0; i < p.n && bi < 0; i++)
      for (int j = i + 1; j < p.n; j++) {
        int common = 0;
        for (int a = 0; a < nwalks && !common; a++)
          common = servedTab[(size_t)a * p.n + i] && servedTab[(size_t)a * p.n + j];
        if (!common) { bi = i; bj = j; break; }
      }
    for (int i = 0; i < p.n && bii < 0; i++) {
      if (p.v[i] < chainL + 1 || p.v[i] > chainH - 1) continue;
      for (int j = i + 1; j < p.n; j++) {
        if (p.v[j] < chainL + 1 || p.v[j] > chainH - 1) continue;
        int common = 0;
        for (int a = 0; a < nwalks && !common; a++)
          common = servedTab[(size_t)a * p.n + i] && servedTab[(size_t)a * p.n + j];
        if (!common) { bii = i; bjj = j; break; }
      }
    }
    printf("  bing 0 %d (%d links, band [%d,%d]): ", nn, p.n, chainL, chainH);
    if (bi >= 0)
      printf("pair (%d,%d) at levels (%d,%d)", bi, bj, p.v[bi], p.v[bj]);
    else
      printf("one walk serves every basepoint");
    if (bii >= 0)
      printf(" | interior pair (%d,%d) at levels (%d,%d)\n", bii, bjj, p.v[bii], p.v[bjj]);
    else
      printf(" | no interior pair\n");
    free(p.v);
  }

  return 0;
}
