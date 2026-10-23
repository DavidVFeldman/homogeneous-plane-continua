/* search-batch50.c -- batch 50.  A targeted search for a counterexample to
 * `cross_valley_profile` (HPC/Fold/Mixed.lean).
 *
 * The item says: if either arm of a branch pair fails `Leg3Valley`, then BOTH
 * arms fold onto the V-walk based at L+5.  The arm that fails folds onto it by
 * `leg3Valley_or_vee` (a theorem), so a counterexample is a branch basepoint at
 * which one arm fails `Leg3Valley` and the OTHER arm does not fold onto the
 * V-walk.  The censuses find none; this program looks for one on purpose.
 *
 * The exact V-criterion (HPC/Fold/Profile.lean) says an arm folds onto the
 * V-walk iff before every time at L+7 or above it has a time at L+2 or below at
 * an index at least 4 and at least 5 steps earlier.  So for an arm B write
 *
 *     w(B) = min over ascents d (B[d] >= 7) of #{ j : 4 <= j, j+5 <= d, B[j] <= 2 },
 *
 * with w(B) = +infinity when B never reaches L+7.  B fails the criterion when
 * w(B) = 0.  The objective minimised here is
 *
 *     O(pair) = min over branch basepoints i with an arm failing Leg3Valley
 *               of w(the other arm),
 *
 * so O = 0 is a counterexample; the search reports one immediately, together
 * with the arm, and verifies it with the dynamic program over `FoldsOnto`.
 *
 * The moves are single-link changes of rho or sig at any index, kept only when
 * the pair is still faithful (IsCrookedIvF) -- the same generator family as the
 * perturbation walks of census-batch50.c, steered instead of random.
 *
 * Usage: search-batch50 [steps] [seed] [restarts]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

#define MAXLEV 32
#define MAXN   2048
#define MAXW   96
#define INF    (1 << 20)

static int meetTab[MAXLEV][MAXN + 1];

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

static int rho[MAXN], sig[MAXN], armG[MAXN], armT[MAXN];

static int highAt(const int *f, int m) {
  int seenLow = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !seenLow) return 0;
    if (f[d] <= 2) seenLow = 1;
  }
  return 1;
}

static int leg3Valley(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j + 5 <= d && !ok; j++) if (a[j] >= 5) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

static int foldsVee(const int *f, int m) {
  int w[MAXW]; int wl = buildWalk(w, 5, 1, 8, -1);
  return folds(f, m, w, wl);
}

/* w(B): the least number of low witnesses any ascent of B has */
static int veeSlack(const int *a, int m) {
  int best = INF;
  for (int d = 0; d < m; d++) {
    if (a[d] < 7) continue;
    int cnt = 0;
    for (int j = 4; j + 5 <= d; j++) if (a[j] <= 2) cnt++;
    if (cnt < best) best = cnt;
  }
  return best;
}

/* The objective: the least slack of an arm sitting opposite an arm that fails
 * `Leg3Valley`.  Zero is a counterexample.  `INF` when the configuration the
 * item speaks about does not occur in the pair at all. */
static int objective(int n, int *bpOut, int *sideOut) {
  int best = INF;
  for (int i = 0; i < n; i++) {
    if (rho[i] != 4) continue;
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
    for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
    if (!highAt(armG, mg) || !highAt(armT, mt)) continue;
    int vG = leg3Valley(armG, mg), vT = leg3Valley(armT, mt);
    if (!vG) {
      int s = veeSlack(armT, mt);
      if (s < best) { best = s; if (bpOut) *bpOut = i; if (sideOut) *sideOut = 1; }
    }
    if (!vT) {
      int s = veeSlack(armG, mg);
      if (s < best) { best = s; if (bpOut) *bpOut = i; if (sideOut) *sideOut = 0; }
    }
  }
  return best;
}

static int checkCounterexample(int n) {
  for (int i = 0; i < n; i++) {
    if (rho[i] != 4) continue;
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
    for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
    if (!highAt(armG, mg) || !highAt(armT, mt)) continue;
    int vG = leg3Valley(armG, mg), vT = leg3Valley(armT, mt);
    int fG = foldsVee(armG, mg), fT = foldsVee(armT, mt);
    if ((!vG || !vT) && !(fG && fT)) {
      printf("*** COUNTEREXAMPLE to cross_valley_profile at basepoint %d: "
             "valley G=%d T=%d, V-fold G=%d T=%d\n", i, vG, vT, fG, fT);
      printf("    rho:");
      for (int u = 0; u < n; u++) printf(" %d", rho[u]);
      printf("\n    sig:");
      for (int u = 0; u < n; u++) printf(" %d", sig[u]);
      printf("\n");
      return 1;
    }
  }
  return 0;
}

int main(int argc, char **argv) {
  long steps = (argc > 1) ? atol(argv[1]) : 4000;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 50u;
  long restarts = (argc > 3) ? atol(argv[3]) : 4;
  srandom(seed);
  printf("search-batch50: hill climbing for a counterexample to cross_valley_profile\n");
  printf("steps=%ld seed=%u restarts=%ld\n", steps, seed, restarts);

  Path chains[2];
  chains[0] = bpath(0, 9);
  chains[1] = bpath(9, 0);

  int globalBest = INF;
  for (long r = 0; r < restarts; r++) {
    Path p = chains[r % 2];
    int n = p.n;
    static int crho[MAXN], csig[MAXN];
    for (int u = 0; u < n; u++) { crho[u] = p.v[u]; csig[u] = p.v[u]; }
    /* a random start: a few accepted perturbations */
    for (int it = 0; it < 40; it++) {
      int j = 1 + (int)(random() % (n - 2));
      int which = (int)(random() % 2), delta = (random() % 2) ? 1 : -1;
      for (int u = 0; u < n; u++) { rho[u] = crho[u]; sig[u] = csig[u]; }
      if (which == 0) rho[j] += delta; else sig[j] += delta;
      if (rho[j] > sig[j] || sig[j] > rho[j] + 1) continue;
      if (rho[j] < 0 || sig[j] > 9) continue;
      if (!crookedGen(rho, sig, n)) continue;
      for (int u = 0; u < n; u++) { crho[u] = rho[u]; csig[u] = sig[u]; }
    }
    for (int u = 0; u < n; u++) { rho[u] = crho[u]; sig[u] = csig[u]; }
    int cur = objective(n, NULL, NULL);
    long accepted = 0, improved = 0;
    for (long it = 0; it < steps; it++) {
      int j = 1 + (int)(random() % (n - 2));
      int which = (int)(random() % 2), delta = (random() % 2) ? 1 : -1;
      for (int u = 0; u < n; u++) { rho[u] = crho[u]; sig[u] = csig[u]; }
      if (which == 0) rho[j] += delta; else sig[j] += delta;
      if (rho[j] > sig[j] || sig[j] > rho[j] + 1) continue;
      if (rho[j] < 0 || sig[j] > 9) continue;
      if (!crookedGen(rho, sig, n)) continue;
      int bp = -1, side = -1;
      int val = objective(n, &bp, &side);
      /* accept an improvement, or a plateau move one time in four */
      if (val < cur || (val == cur && (random() % 4 == 0))) {
        if (val < cur) improved++;
        cur = val;
        accepted++;
        for (int u = 0; u < n; u++) { crho[u] = rho[u]; csig[u] = sig[u]; }
        if (val == 0) {
          printf("objective 0 reached at step %ld (basepoint %d, side %d)\n", it, bp, side);
          if (checkCounterexample(n)) { printf("search: counterexample found\n"); return 0; }
          printf("  (the V-fold survives there all the same; objective 0 is necessary, "
                 "not sufficient)\n");
        }
      }
    }
    printf("restart %ld (chain of %d links): best objective %d, %ld accepted moves, "
           "%ld improvements\n", r, n, cur, accepted, improved);
    if (cur < globalBest) globalBest = cur;
  }
  printf("\nsearch-batch50: best objective over all restarts: %d "
         "(0 would be a counterexample)\n", globalBest);
  return 0;
}
