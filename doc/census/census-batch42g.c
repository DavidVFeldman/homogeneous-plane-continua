/* Census for batch 42 -- how fast can a crooked arm climb?
 *
 * The fold of an arm onto a walk is limited by the index bound: the walk time
 * at index j is at most j.  So what matters about an arm is not which events
 * happen but how many steps it needs to get high, and crookedness limits that.
 *
 * This program computes, by exhaustive breadth-first search over 1-Lipschitz
 * arms in [L, H] starting at level P, and subject to `CrookUp` and `CrookDown`
 * (HPC/Fold/Crook.lean, tested exactly over all pairs of the prefix), the least
 * index at which an arm can stand at level P + t, for each t.
 *
 * Usage: census-batch42g [N] [P] [L] [H]
 */

#include <stdio.h>
#include <stdlib.h>

#define MAXN 64
static int N, P, L, H;
static int f[MAXN];
static int best[64];

static int crook_at(int d) {
  for (int s = 0; s < d; s++) {
    if (f[s] + 3 <= f[d]) {
      int ok = 0;
      for (int u = s + 1; u < d && !ok; u++) {
        if (!(f[d] - 2 <= f[u] && f[u] <= f[d] - 1)) continue;
        for (int up = u + 1; up < d; up++)
          if (f[s] <= f[up] && f[up] <= f[s] + 1) { ok = 1; break; }
      }
      if (!ok) return 0;
    }
    if (f[d] + 3 <= f[s]) {
      int ok = 0;
      for (int u = s + 1; u < d && !ok; u++) {
        if (!(f[d] <= f[u] && f[u] <= f[d] + 1)) continue;
        for (int up = u + 1; up < d; up++)
          if (f[s] - 2 <= f[up] && f[up] <= f[s] - 1) { ok = 1; break; }
      }
      if (!ok) return 0;
    }
  }
  return 1;
}

static void dfs(int len) {
  int d = len - 1;
  if (!crook_at(d)) return;
  int t = f[d] - P;
  if (t >= 0 && t < 64 && d < best[t]) best[t] = d;
  int td = P - f[d];
  if (td > 0 && td < 64 && d < best[32 + td]) best[32 + td] = d;
  if (len == N) return;
  for (int v = f[d] - 1; v <= f[d] + 1; v++) {
    if (v < L || v > H) continue;
    f[len] = v;
    dfs(len + 1);
  }
}

int main(int argc, char **argv) {
  N = argc > 1 ? atoi(argv[1]) : 18;
  P = argc > 2 ? atoi(argv[2]) : 4;
  L = argc > 3 ? atoi(argv[3]) : 0;
  H = argc > 4 ? atoi(argv[4]) : 9;
  for (int i = 0; i < 64; i++) best[i] = 1000;
  f[0] = P;
  dfs(1);
  printf("crooked arms from level %d in [%d,%d], length <= %d\n", P, L, H, N);
  for (int t = 0; t + P <= H; t++)
    if (best[t] < 1000) printf("  least index at level %d (= P + %d) : %d\n", P + t, t, best[t]);
  for (int t = 1; P - t >= L; t++)
    if (best[32 + t] < 1000) printf("  least index at level %d (= P - %d) : %d\n",
                                    P - t, t, best[32 + t]);
  return 0;
}
