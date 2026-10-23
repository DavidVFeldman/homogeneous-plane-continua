/* census-batch49.c — batch 49, question 1: can an arm fail `Leg3Ceil`?
 *
 * Arms alone (no pairs): exhaustive DFS over every 1-Lipschitz sequence
 * f : {0,...} -> [0,9] with f 0 = 4 that satisfies the two arm clauses
 * `CrookUp` and `CrookDown` of HPC/Fold/Crook.lean, searching for one that
 * satisfies `HighAt f 1 8` but fails `Leg3Ceil f 0`.
 *
 * Definitions, verbatim from the Lean (L = 0):
 *   CrookUp    : forall s<t, f s + 3 <= f t ->
 *                exists s<u<u'<t, f t - 2 <= f u <= f t - 1,
 *                               f s <= f u' <= f s + 1
 *   CrookDown  : forall s<t, f t + 3 <= f s ->
 *                exists s<u<u'<t, f t <= f u <= f t + 1,
 *                               f s - 2 <= f u' <= f s - 1
 *   HighAt f 1 8 : forall d, 8 <= f d -> exists j < d, f j <= 2
 *   Leg3Ceil f 0 : forall d, 8 <= f d ->
 *                exists j k, 3 <= j, j+5 <= k, k+6 <= d, 5 <= f j, f k <= 2
 *
 * Two observations make the search finite and cheap.
 *  - Both crookedness clauses at a pair (s,t) mention only indices <= t, so a
 *    prefix can be rejected as soon as its last index is placed.
 *  - The witnesses for `Leg3Ceil` at an index d also serve every later index,
 *    so it is enough to examine the FIRST index D at which f reaches 8: if the
 *    clause holds there it holds everywhere, and if it fails there the arm
 *    fails `Leg3Ceil`.  Hence every branch of the DFS terminates at its first 8.
 *
 * Usage: census-batch49 [maxdepth]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int MAXD = 40;
static int f[256];
static long long nodes = 0, hits8 = 0, fails = 0, deep = 0, prunedCrook = 0;
static long long failHighAt = 0, okCeil = 0, prunedLate = 0;

/* check the two crookedness clauses for every pair (s,t) with t = last */
static int crook_ok(int t)
{
    for (int s = 0; s < t; s++) {
        if (f[s] + 3 <= f[t]) {
            int found = 0;
            for (int u = s + 1; u < t && !found; u++) {
                if (f[t] - 2 <= f[u] && f[u] <= f[t] - 1)
                    for (int v = u + 1; v < t && !found; v++)
                        if (f[s] <= f[v] && f[v] <= f[s] + 1) found = 1;
            }
            if (!found) return 0;
        }
        if (f[t] + 3 <= f[s]) {
            int found = 0;
            for (int u = s + 1; u < t && !found; u++) {
                if (f[t] <= f[u] && f[u] <= f[t] + 1)
                    for (int v = u + 1; v < t && !found; v++)
                        if (f[s] - 2 <= f[v] && f[v] <= f[s] - 1) found = 1;
            }
            if (!found) return 0;
        }
    }
    return 1;
}

static void report(int D)
{
    printf("FAILING ARM, first 8 at index %d:", D);
    for (int i = 0; i <= D; i++) printf(" %d", f[i]);
    printf("\n");
}

/* first index >= 3 with f >= 5, or -1 */
static int jmin_of(int t)
{
    for (int j = 3; j <= t; j++) if (f[j] >= 5) return j;
    return -1;
}

static void dfs(int t)
{
    nodes++;
    if (f[t] >= 8) {
        hits8++;
        /* HighAt */
        int high = 0;
        for (int j = 0; j < t; j++) if (f[j] <= 2) high = 1;
        if (!high) { failHighAt++; return; }
        /* Leg3Ceil at the first 8 */
        int ok = 0;
        for (int j = 3; j <= t && !ok; j++)
            if (f[j] >= 5)
                for (int k = j + 5; k + 6 <= t && !ok; k++)
                    if (f[k] <= 2) ok = 1;
        if (ok) { okCeil++; return; }
        fails++;
        if (fails <= 20) report(t);
        return;
    }
    if (t >= MAXD) { deep++; return; }
    for (int dv = -1; dv <= 1; dv++) {
        int nv = f[t] + dv;
        if (nv < 0 || nv > 9) continue;
        f[t + 1] = nv;
        /* a low time late enough after a high time settles `Leg3Ceil` for every
         * later first-8 (the climb from 2 to 8 costs at least six steps), so the
         * branch cannot produce a failing arm */
        if (nv <= 2) {
            int jm = jmin_of(t);
            if (jm >= 0 && t + 1 >= jm + 5) { prunedLate++; continue; }
        }
        if (crook_ok(t + 1)) dfs(t + 1); else prunedCrook++;
    }
}

int main(int argc, char **argv)
{
    if (argc > 1) MAXD = atoi(argv[1]);
    f[0] = 4;
    dfs(0);
    printf("maxdepth %d: nodes %lld, prefixes rejected by crookedness %lld, "
           "rejected as settled %lld, depth cutoffs %lld\n",
           MAXD, nodes, prunedCrook, prunedLate, deep);
    printf("arms reaching 8: %lld; of those failing HighAt(1,8): %lld; "
           "meeting Leg3Ceil: %lld; FAILING Leg3Ceil with HighAt: %lld\n",
           hits8, failHighAt, okCeil, fails);
    return 0;
}
