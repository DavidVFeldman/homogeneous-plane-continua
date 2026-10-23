/* search-batch52.c -- shortest arms witnessing the gap of the arm reflection.
 *
 * The arm reflection f |-> 9 - f transports every statement whose hypotheses are
 * IsLip, the band, the basepoint and the landmark clauses.  It does not
 * transport the crookedness clauses: the reflection of CrookDown is CrookUpR,
 * whose two windows sit one level above those of CrookUp.  This program
 * searches for the shortest 1-Lipschitz arms of the band [0,9] that witness the
 * gap, by depth-first search over the arms that satisfy CrookUp and CrookDown
 * (both violations are final: a violating pair (s,t) stays violating under every
 * extension, so the search prunes).
 *
 *   goal 1: CrookUp and CrookDown but not CrookUpR
 *   goal 2: CrookUp and CrookDown but not CrookDownR
 *   goal 3: based at 5, CrookUp and CrookDown, fails Floor3R and does not fold
 *           onto the V-walk 6 -> 1 -> 8 (the reflection of the Lambda-walk at
 *           L+3): a counterexample to the reflected dichotomy floor3R_or_vee as
 *           a statement about the model's own clauses
 *   goal 4: based at 5, CrookUp and CrookDown, fails Ceil4R and does not fold
 *           onto the Lambda-walk 4 -> 8 -> 1: likewise for ceil4R_or_lam
 *
 * Usage: search-batch52 [maxlen]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXM 64
#define MAXW 96

static int f[MAXM];

/* does the pair (s,t) with t the last index violate the clause? */
static int violUp(int m) {           /* CrookUp */
  int t = m - 1;
  for (int s = 0; s < t; s++) {
    if (f[s] + 3 > f[t]) continue;
    int u = -1;
    for (int j = s + 1; j < t; j++)
      if (f[j] >= f[t] - 2 && f[j] <= f[t] - 1) { u = j; break; }
    if (u < 0) return 1;
    int ok = 0;
    for (int j = u + 1; j < t; j++) if (f[j] >= f[s] && f[j] <= f[s] + 1) { ok = 1; break; }
    if (!ok) return 1;
  }
  return 0;
}

static int violDown(int m) {         /* CrookDown */
  int t = m - 1;
  for (int s = 0; s < t; s++) {
    if (f[t] + 3 > f[s]) continue;
    int u = -1;
    for (int j = s + 1; j < t; j++)
      if (f[j] >= f[t] && f[j] <= f[t] + 1) { u = j; break; }
    if (u < 0) return 1;
    int ok = 0;
    for (int j = u + 1; j < t; j++) if (f[j] >= f[s] - 2 && f[j] <= f[s] - 1) { ok = 1; break; }
    if (!ok) return 1;
  }
  return 0;
}

/* CrookUpR: windows [f t - 1, f t] then [f s + 1, f s + 2] */
static int failUpR(int m) {
  for (int t = 1; t < m; t++)
    for (int s = 0; s < t; s++) {
      if (f[s] + 3 > f[t]) continue;
      int u = -1;
      for (int j = s + 1; j < t; j++)
        if (f[j] >= f[t] - 1 && f[j] <= f[t]) { u = j; break; }
      if (u < 0) return 1;
      int ok = 0;
      for (int j = u + 1; j < t; j++) if (f[j] >= f[s] + 1 && f[j] <= f[s] + 2) { ok = 1; break; }
      if (!ok) return 1;
    }
  return 0;
}

/* CrookDownR: windows [f t + 1, f t + 2] then [f s - 1, f s] */
static int failDownR(int m) {
  for (int t = 1; t < m; t++)
    for (int s = 0; s < t; s++) {
      if (f[t] + 3 > f[s]) continue;
      int u = -1;
      for (int j = s + 1; j < t; j++)
        if (f[j] >= f[t] + 1 && f[j] <= f[t] + 2) { u = j; break; }
      if (u < 0) return 1;
      int ok = 0;
      for (int j = u + 1; j < t; j++) if (f[j] >= f[s] - 1 && f[j] <= f[s]) { ok = 1; break; }
      if (!ok) return 1;
    }
  return 0;
}

/* Floor3R f: before every time at 1 or below, a time at 4 or below at a step
 * >= 3, then a time at 7 or above at least 5 steps later, the descent at least
 * 6 steps after that. */
static int failFloor3R(int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j + 11 <= d && !ok; j++) {
      if (f[j] > 4) continue;
      for (int k = j + 5; k + 6 <= d && !ok; k++) if (f[k] >= 7) ok = 1;
    }
    if (!ok) return 1;
  }
  return 0;
}

/* Ceil4R f: before every time at 8 or above, a time at 4 or below at a step
 * >= 3 and at least four steps earlier. */
static int failCeil4R(int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] < 8) continue;
    int ok = 0;
    for (int j = 3; j + 4 <= d && !ok; j++) if (f[j] <= 4) ok = 1;
    if (!ok) return 1;
  }
  return 0;
}

static int buildWalk(int *w, int start, int a, int b, int c) {
  int len = 0, cur = start;
  w[len++] = cur;
  int tgt[3] = {a, b, c};
  for (int q = 0; q < 3; q++) {
    if (tgt[q] < 0) break;
    int s = tgt[q] > cur ? 1 : -1;
    while (cur != tgt[q]) { cur += s; w[len++] = cur; }
  }
  return len;
}

static int folds(const int *a, int m, const int *w, int wl) {
  char cur[MAXW], nxt[MAXW];
  for (int u = 0; u < wl; u++) cur[u] = 0;
  if (a[0] - w[0] > 1 || w[0] - a[0] > 1) return 0;
  cur[0] = 1;
  for (int j = 1; j < m; j++) {
    int any = 0;
    for (int u = 0; u < wl; u++) nxt[u] = 0;
    for (int u = 0; u < wl; u++) {
      if (!cur[u]) continue;
      for (int e = -1; e <= 1; e++) {
        int u2 = u + e;
        if (u2 < 0 || u2 >= wl) continue;
        int d = a[j] - w[u2];
        if (d <= 1 && d >= -1) { nxt[u2] = 1; any = 1; }
      }
    }
    if (!any) return 0;
    memcpy(cur, nxt, sizeof(char) * wl);
  }
  return 1;
}

static int foldsVeeAt6(int m) { int w[MAXW]; return folds(f, m, w, buildWalk(w, 6, 1, 8, -1)); }
static int foldsLamAt4(int m) { int w[MAXW]; return folds(f, m, w, buildWalk(w, 4, 8, 1, -1)); }

static int maxlen = 26;
static int found[5];
static long nodes = 0;

static void show(int goal, int m, const char *what) {
  if (found[goal]) return;
  found[goal] = 1;
  printf("goal %d (%s): length %d\n  levels:", goal, what, m);
  for (int d = 0; d < m; d++) printf(" %d", f[d]);
  printf("\n  Lean list: ![");
  for (int d = 0; d < m; d++) printf("%s%d", d ? ", " : "", f[d]);
  printf("]\n");
}

static void dfs(int m, int base5) {
  nodes++;
  if (m >= 2) { if (violUp(m) || violDown(m)) return; }
  if (m >= 4) {
    if (failUpR(m)) show(1, m, "CrookUp and CrookDown but not CrookUpR");
    if (failDownR(m)) show(2, m, "CrookUp and CrookDown but not CrookDownR");
    if (base5) {
      if (failFloor3R(m) && !foldsVeeAt6(m))
        show(3, m, "fails Floor3R and does not fold onto the V-walk at L+6");
      if (failCeil4R(m) && !foldsLamAt4(m))
        show(4, m, "fails Ceil4R and does not fold onto the Lambda-walk at L+4");
    }
  }
  if (m >= maxlen) return;
  if (found[1] && found[2] && (!base5 || (found[3] && found[4]))) return;
  int last = f[m - 1];
  for (int e = -1; e <= 1; e++) {
    int v = last + e;
    if (v < 0 || v > 9) continue;
    f[m] = v;
    dfs(m + 1, base5);
  }
}

/* ---- randomised search for the longer witnesses (goals 3 and 4) ---------- */

static int bestLen3 = 1 << 30, best3[MAXM];
static int bestLen4 = 1 << 30, best4[MAXM];

static void rdfs(int m, int cap) {
  if (m >= 2 && (violUp(m) || violDown(m))) return;
  if (m >= 14) {
    if (failFloor3R(m) && !foldsVeeAt6(m) && m < bestLen3) {
      bestLen3 = m; memcpy(best3, f, sizeof(int) * m);
    }
    if (failCeil4R(m) && !foldsLamAt4(m) && m < bestLen4) {
      bestLen4 = m; memcpy(best4, f, sizeof(int) * m);
    }
  }
  if (m >= cap) return;
  int order[3] = {-1, 0, 1};
  for (int q = 2; q > 0; q--) { int r = random() % (q + 1), t = order[q]; order[q] = order[r]; order[r] = t; }
  for (int e = 0; e < 3; e++) {
    int v = f[m - 1] + order[e];
    if (v < 0 || v > 9) continue;
    f[m] = v;
    rdfs(m + 1, cap);
    if (random() % 100 < 70) return;      /* random restart: keep the search shallow and wide */
  }
}

static void randomSearch(long tries, int cap) {
  for (long it = 0; it < tries; it++) { f[0] = 5; rdfs(1, cap); }
  if (bestLen3 < (1 << 30)) {
    printf("goal 3 (fails Floor3R, no fold onto 6 -> 1 -> 8): length %d\n  levels:", bestLen3);
    for (int d = 0; d < bestLen3; d++) printf(" %d", best3[d]);
    printf("\n  Lean list: ![");
    for (int d = 0; d < bestLen3; d++) printf("%s%d", d ? ", " : "", best3[d]);
    printf("]\n");
  } else printf("goal 3: no witness found\n");
  if (bestLen4 < (1 << 30)) {
    printf("goal 4 (fails Ceil4R, no fold onto 4 -> 8 -> 1): length %d\n  levels:", bestLen4);
    for (int d = 0; d < bestLen4; d++) printf(" %d", best4[d]);
    printf("\n  Lean list: ![");
    for (int d = 0; d < bestLen4; d++) printf("%s%d", d ? ", " : "", best4[d]);
    printf("]\n");
  } else printf("goal 4: no witness found\n");
}

int main(int argc, char **argv) {
  if (argc > 1) maxlen = atoi(argv[1]);
  setvbuf(stdout, NULL, _IOLBF, 0);
  if (argc > 2 && !strcmp(argv[2], "random")) {
    long tries = (argc > 3) ? atol(argv[3]) : 100000;
    unsigned seed = (argc > 4) ? (unsigned)atoi(argv[4]) : 52u;
    srandom(seed);
    printf("search-batch52: randomised search, cap %d, %ld restarts, seed %u\n", maxlen, tries,
           seed);
    randomSearch(tries, maxlen);
    return 0;
  }
  printf("search-batch52: shortest witnesses, arms of the band [0,9], maxlen %d\n", maxlen);
  printf("\n-- arms based at 5 (the branch L+5) --\n");
  memset(found, 0, sizeof found);
  f[0] = 5;
  dfs(1, 1);
  printf("nodes %ld\n", nodes);
  for (int g = 1; g <= 4; g++) if (!found[g]) printf("goal %d: no witness of length <= %d\n", g, maxlen);
  printf("\n-- arms with an arbitrary start --\n");
  memset(found, 0, sizeof found);
  nodes = 0;
  for (int st = 0; st <= 9 && !(found[1] && found[2]); st++) { f[0] = st; dfs(1, 0); }
  printf("nodes %ld\n", nodes);
  for (int g = 1; g <= 2; g++) if (!found[g]) printf("goal %d: no witness of length <= %d\n", g, maxlen);
  return 0;
}
