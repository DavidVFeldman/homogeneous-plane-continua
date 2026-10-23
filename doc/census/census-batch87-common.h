/* Batch 87 census: shared enumerator of the faithful model and a generic fold search.
 *
 * Faithful model (HPC/Fold/Faithful.lean, IsCrookedIvF): fine links t = 0..n-1 with coarse
 * interval [rho t, sig t], sig <= rho + 1, adjacency max(sig t, sig t+1) <= min(rho t, rho t+1)+1,
 * and the crookedness clause with forced meetings (meets(t, h): some u with |u - t| <= 1 has
 * rho u <= h <= sig u).  Sequences are normalised to span exactly K coarse links
 * (min rho = 0, max sig = K - 1).
 *
 * The enumerator prunes on prefixes: the crookedness clause for a pair s < t only reads links
 * s-1 .. t+1, so it is checked as soon as link t+1 (or the last link) is placed.  Its counts at
 * K = 4, n = 6..10 are compared against census-batch86-exhaustive.log (which checks whole
 * sequences only) as a cross-check.
 *
 * Fold search: a block map beta (|beta(t+1) - beta(t)| <= 1, values 0..q-1 all used) with every
 * block inside three consecutive coarse links, i.e. max rho - min sig <= 2 over the block
 * (the intervals [rho, sig] of its members meet a common window [j, j+2]).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXN 4096
int n, K;
int rho[MAXN], sig[MAXN];

static int meets(int t, int j) {
  for (int u = t - 1; u <= t + 1; u++) {
    if (u < 0 || u >= n) continue;
    if (rho[u] <= j && j <= sig[u]) return 1;
  }
  return 0;
}
static int crooked_pair(int s, int t) {
  /* for h < k: need r < r' in (s, t) with k - 1 in [rho r, sig r] and h + 1 in [rho r', sig r'];
     take r the first index after s containing the level k - 1 and r' the last index before t
     containing h + 1 (symmetrically for k < h). */
  for (int h = 0; h < K; h++) {
    if (!meets(s, h)) continue;
    for (int k = 0; k < K; k++) {
      if (abs(h - k) < 3) continue;
      if (!meets(t, k)) continue;
      int need1 = h < k ? k - 1 : k + 1, need2 = h < k ? h + 1 : h - 1;
      int r = -1, r2 = -1;
      for (int x = s + 1; x < t; x++) if (rho[x] <= need1 && need1 <= sig[x]) { r = x; break; }
      for (int x = t - 1; x > s; x--) if (rho[x] <= need2 && need2 <= sig[x]) { r2 = x; break; }
      if (r < 0 || r2 < 0 || !(r < r2)) return 0;
    }
  }
  return 1;
}
/* whole-sequence check (used on Bing chains and as an independent re-check) */
static int crooked_all(void) {
  for (int s = 0; s < n; s++)
    for (int t = s + 1; t < n; t++)
      if (!crooked_pair(s, t)) return 0;
  return 1;
}

/* ---------- enumeration with prefix pruning ---------- */
typedef void (*visit_fn)(void);
static visit_fn VISIT;
static int NFULL;
static void gen_rec(int t) {
  /* links 0..t-1 are placed; n is temporarily t for meets() */
  if (t >= 2) {
    int tt = t - 2; /* pairs (s, tt) are now determined: tt + 1 = t - 1 placed */
    int save = n; n = t;
    for (int s = 0; s < tt; s++) if (!crooked_pair(s, tt)) { n = save; return; }
    n = save;
  }
  if (t == NFULL) {
    n = NFULL;
    for (int s = 0; s < n - 1; s++) if (!crooked_pair(s, n - 1)) return;
    int mn = 100, mx = -100;
    for (int a = 0; a < n; a++) { if (rho[a] < mn) mn = rho[a]; if (sig[a] > mx) mx = sig[a]; }
    if (mn != 0 || mx != K - 1) return;
    VISIT();
    return;
  }
  for (int r = 0; r < K; r++)
    for (int w = 0; w < 2; w++) {
      int s = r + w;
      if (s >= K) continue;
      if (t > 0) {
        int mx = s > sig[t - 1] ? s : sig[t - 1];
        int mn = r < rho[t - 1] ? r : rho[t - 1];
        if (mx > mn + 1) continue;
      }
      rho[t] = r; sig[t] = s;
      gen_rec(t + 1);
    }
}
static void enumerate(int len, int KK, visit_fn f) { NFULL = len; K = KK; VISIT = f; gen_rec(0); n = len; }

/* ---------- Bing's chains: coarse levels of the standard crooked pattern ---------- */
typedef struct { int *v; int n; } Path;
static Path bpath(int a, int b) {
  Path p; int d = a < b ? b - a : a - b;
  if (d <= 2) {
    p.n = d + 1; p.v = malloc(sizeof(int) * p.n); int s = (a <= b) ? 1 : -1;
    for (int u = 0; u < p.n; u++) p.v[u] = a + s * u;
    return p;
  }
  int mid = (a < b) ? b - 1 : b + 1; int c = (a < b) ? a + 1 : a - 1;
  Path p1 = bpath(a, mid), p2 = bpath(mid, c), p3 = bpath(c, b);
  p.n = p1.n + p2.n - 1 + p3.n - 1; p.v = malloc(sizeof(int) * p.n);
  memcpy(p.v, p1.v, sizeof(int) * p1.n);
  memcpy(p.v + p1.n, p2.v + 1, sizeof(int) * (p2.n - 1));
  memcpy(p.v + p1.n + p2.n - 1, p3.v + 1, sizeof(int) * (p3.n - 1));
  return p;
}
