/* Census for batch 42 -- does the peak-window criterion still decide the fold
 * when the arm starts one level above the base of the walk?
 *
 * Lemma F1 (HPC/Fold/Itinerary.lean) says that an arm with f 0 = p folds onto
 * the Lambda-walk `lamCenter p H L` exactly when `CritLam f p H` holds.  The
 * walk that serves every actual pair of the open branch at L + 4 is the
 * Lambda-walk based at p = L + 3 while the arm starts at L + 4.  This program
 * tests, by exhaustive enumeration of arms, whether the same criterion decides
 * that case:
 *
 *   for every 1-Lipschitz f : [0, n) -> [L, H] with f 0 = p + 1 and n <= N,
 *      FoldsOnto f (lamLen p H L) (lamCenter p H L)  <->  CritLam f p H ?
 *
 * The fold is decided exactly, by reachability over the set of walk times.
 *
 * Usage: census-batch42f [N] [p] [L] [H]
 */

#include <stdio.h>
#include <stdlib.h>

#define MAXN 64

static int N, p, L, H, kappa, wlen;
static int walk[64];
static int f[MAXN];
static long long arms, bad_fold, bad_crit;

static void build(void) {
  kappa = (H - 1 > p) ? H - 1 : p;
  wlen = 0;
  for (int v = p; v <= kappa; v++) walk[wlen++] = v;
  for (int v = kappa - 1; v >= L + 1; v--) walk[wlen++] = v;
}

/* exact FoldsOnto by reachability */
static int folds(int len) {
  unsigned long long mask = 0;
  if (abs(f[0] - walk[0]) > 1) return 0;
  mask = 1;
  for (int j = 1; j < len; j++) {
    unsigned long long spread = mask | (mask << 1) | (mask >> 1), nm = 0;
    for (int u = 0; u < wlen; u++)
      if (((spread >> u) & 1) && abs(f[j] - walk[u]) <= 1) nm |= 1ULL << u;
    mask = nm;
    if (!mask) return 0;
  }
  return 1;
}

/* CritLam f p H on f[0..len-1] */
static int critLam(int len) {
  if (p >= kappa) return 1;
  for (int d = 0; d < len; d++) {
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

/* The ascent-profile criterion: for every d with f d <= p - 2 there is j < d
 * with kappa - p <= j and f k >= kappa - 1 - (j - k) for every k <= j. */
static int reach(int j) {
  if (j < kappa - p) return 0;
  for (int k = 0; k <= j; k++) if (f[k] < kappa - 1 - (j - k)) return 0;
  return 1;
}

static int profile(int len) {
  if (p >= kappa) return 1;
  for (int d = 0; d < len; d++) {
    if (f[d] > p - 2) continue;
    int ok = 0;
    for (int j = 0; j < d && !ok; j++) if (reach(j)) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

static long long bad_pf, bad_pc;

static void show(int len, const char *tag) {
  printf("%s:", tag);
  for (int j = 0; j < len; j++) printf(" %d", f[j]);
  printf("\n");
}

static void dfs(int len) {
  arms++;
  int fo = folds(len), cr = critLam(len);
  if (fo && !cr) { if (++bad_crit <= 5) show(len, "folds but criterion fails"); }
  if (!fo && cr) { if (++bad_fold <= 5) show(len, "criterion holds but no fold"); }
  int pf = profile(len);
  if (fo && !pf) { if (++bad_pf <= 5) show(len, "folds but profile fails"); }
  if (!fo && pf) { if (++bad_pc <= 5) show(len, "profile holds but no fold"); }
  if (len == N) return;
  for (int v = f[len-1] - 1; v <= f[len-1] + 1; v++) {
    if (v < L || v > H) continue;
    f[len] = v;
    dfs(len + 1);
  }
}

int main(int argc, char **argv) {
  N = argc > 1 ? atoi(argv[1]) : 13;
  p = argc > 2 ? atoi(argv[2]) : 3;
  L = argc > 3 ? atoi(argv[3]) : 0;
  H = argc > 4 ? atoi(argv[4]) : 9;
  build();
  f[0] = p + (argc > 5 ? atoi(argv[5]) : 1);
  dfs(1);
  printf("p=%d L=%d H=%d, arms of length <= %d from level %d: %lld\n", p, L, H, N, f[0], arms);
  printf("folds but criterion fails: %lld ; criterion holds but no fold: %lld\n",
         bad_crit, bad_fold);
  printf("folds but profile fails: %lld ; profile holds but no fold: %lld\n",
         bad_pf, bad_pc);
  return 0;
}
