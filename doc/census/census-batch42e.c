/* Census for batch 42 -- is the criterion forced by the branch?
 *
 * Exhaustive search over ARMS, not over arm classes: a 1-Lipschitz integer
 * sequence f of length <= N with values in [L, H] = [0, 9] and f 0 = 4, the
 * basepoint level of the open branch at L + 4.  The arm is required to satisfy
 *
 *   CrookUp, CrookDown   (HPC/Fold/Crook.lean, exactly, over all pairs)
 *   HighAt (L+1) (L+9)   (leaf)
 *   LowAt  L     (L+7)   (leaf)
 *   HighAt (L+1) (L+8)   (the open branch)
 *
 * and the search asks whether any such arm fails
 *
 *   CritLam f (L+3) H    (HPC/Fold/Itinerary.lean: the peak-window criterion
 *                         for the Lambda-walk based at L+3 with peak L+8)
 *
 * Every one of these conditions is backward-looking, so a violation at an
 * index is permanent and the search may prune on it; the enumeration is
 * therefore exhaustive for arms of length <= N.
 *
 * Usage: census-batch42e [N] [p]      (p = basepoint level, default 4)
 */

#include <stdio.h>
#include <stdlib.h>

#define L 0
#define H 9
#define MAXN 64

static int N, P0;
static int f[MAXN];
static long long arms, viol;

/* ---- the conditions, each evaluated on the prefix f[0..len-1] at d = len-1 */

/* CrookUp/CrookDown clauses with second index d */
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

/* HighAt tl th at index d: if f d >= th then some j < d has f j <= tl + 1 */
static int highAt_at(int d, int tl, int th) {
  if (f[d] < th) return 1;
  for (int j = 0; j < d; j++) if (f[j] <= tl + 1) return 1;
  return 0;
}

/* LowAt tl th at index d */
static int lowAt_at(int d, int tl, int th) {
  if (f[d] > tl) return 1;
  for (int j = 0; j < d; j++) if (f[j] >= th) return 1;
  for (int j = 0; j < d; j++) {
    if (f[j] > tl + 1) continue;
    for (int jp = j + 1; jp < d; jp++) if (f[jp] >= th - 2) return 1;
  }
  return 0;
}

/* CritLam f p H at index d, with kappa = max (H-1) p */
static int critLam_at(int d, int p) {
  int kappa = H - 1 > p ? H - 1 : p;
  if (p >= kappa) return 1;
  if (f[d] > p - 2) return 1;
  for (int j = 0; j < d; j++) if (f[j] >= kappa) return 1;
  int cnt = 0;
  for (int j = 0; j < d; j++) if (f[j] >= kappa - 1) { cnt++; if (cnt >= 2) return 1; }
  for (int j = 0; j < d; j++) {
    if (f[j] < kappa - 1) continue;
    for (int t = 1; t < j; t++) if (f[t] <= f[t-1]) return 1;
  }
  return 0;
}

static void show(int len, const char *tag) {
  printf("%s:", tag);
  for (int j = 0; j < len; j++) printf(" %d", f[j]);
  printf("\n");
  fflush(stdout);
}

static void dfs(int len) {
  int d = len - 1;
  if (!crook_at(d)) return;
  if (!highAt_at(d, L + 1, H)) return;
  if (!highAt_at(d, L + 1, H - 1)) return;
  if (!lowAt_at(d, L, P0 + 3)) return;
  arms++;
  if (!critLam_at(d, P0 - 1)) {
    viol++;
    if (viol <= 5) show(len, "CRITLAM FAILS");
    return;                    /* the violation is permanent */
  }
  if (len == N) return;
  for (int v = f[d] - 1; v <= f[d] + 1; v++) {
    if (v < L || v > H) continue;
    f[len] = v;
    dfs(len + 1);
  }
}

int main(int argc, char **argv) {
  N = argc > 1 ? atoi(argv[1]) : 16;
  P0 = argc > 2 ? atoi(argv[2]) : 4;
  f[0] = P0;
  dfs(1);
  printf("arms of length <= %d from level %d satisfying the branch: %lld\n", N, P0, arms);
  printf("of which CritLam (base %d, peak %d) fails: %lld\n", P0 - 1, H - 1, viol);
  return 0;
}
