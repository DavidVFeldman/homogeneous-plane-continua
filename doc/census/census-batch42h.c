/* Census for batch 42 -- one walk for the whole open branch, tested against
 * arms rather than against arm classes.
 *
 * Exhaustive over 1-Lipschitz arms f in [L, H] = [0, 9] of length <= N with
 * f 0 = P, subject to
 *
 *   CrookUp and CrookDown, exactly, over all pairs of the arm
 *   HighAt (L+1) (L+9), LowAt L (P+3)          (the leaf at the basepoint P)
 *   HighAt (L+1) (L+8)                         (the open branch at P = L+4)
 *
 * it reports the arms that do NOT fold onto the walk given on the command line
 * (a base centre followed by turning targets).  Unlike the automaton census of
 * batches 40-41 this quantifies over actual arms, with crookedness tested and
 * not approximated; it is exhaustive only up to the length N.
 *
 * Usage: census-batch42h N P base t1 t2 ...
 */

#include <stdio.h>
#include <stdlib.h>

#define L 0
#define H 9
#define MAXN 64

static int N, P0;
static int f[MAXN];
static int walk[256], wlen;
static long long arms, fails;

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

static int highAt_at(int d, int tl, int th) {
  if (f[d] < th) return 1;
  for (int j = 0; j < d; j++) if (f[j] <= tl + 1) return 1;
  return 0;
}

static int lowAt_at(int d, int tl, int th) {
  if (f[d] > tl) return 1;
  for (int j = 0; j < d; j++) if (f[j] >= th) return 1;
  for (int j = 0; j < d; j++) {
    if (f[j] > tl + 1) continue;
    for (int jp = j + 1; jp < d; jp++) if (f[jp] >= th - 2) return 1;
  }
  return 0;
}

/* exact fold of f[0..len-1] onto the walk, by reachability */
static int folds(int len) {
  unsigned long long mask;
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

static void dfs(int len) {
  int d = len - 1;
  if (!crook_at(d)) return;
  if (!highAt_at(d, L + 1, H)) return;
  if (!highAt_at(d, L + 1, H - 1)) return;
  if (!lowAt_at(d, L, P0 + 3)) return;
  arms++;
  if (!folds(len)) {
    fails++;
    if (fails <= 8) {
      printf("NO FOLD:");
      for (int j = 0; j < len; j++) printf(" %d", f[j]);
      printf("\n");
    }
    return;                       /* a failure is permanent */
  }
  if (len == N) return;
  for (int v = f[d] - 1; v <= f[d] + 1; v++) {
    if (v < L || v > H) continue;
    f[len] = v;
    dfs(len + 1);
  }
}

int main(int argc, char **argv) {
  N = argc > 1 ? atoi(argv[1]) : 14;
  P0 = argc > 2 ? atoi(argv[2]) : 4;
  wlen = 0;
  int cur = argc > 3 ? atoi(argv[3]) : P0 - 1;
  walk[wlen++] = cur;
  for (int a = 4; a < argc; a++) {
    int tgt = atoi(argv[a]);
    while (cur != tgt) { cur += (tgt > cur) ? 1 : -1; walk[wlen++] = cur; }
  }
  printf("walk (%d times):", wlen);
  for (int u = 0; u < wlen; u++) printf(" %d", walk[u]);
  printf("\n");
  f[0] = P0;
  dfs(1);
  printf("arms of length <= %d in the branch at P = %d : %lld, not folding: %lld\n",
         N, P0, arms, fails);
  return 0;
}
