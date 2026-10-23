/* probe59.c -- batch 59, question 1, first pass.
 *
 * The landmark sentence of a four-leg walk, tested against the fold by
 * exhaustive enumeration of every 1-Lipschitz arm of the band [0,9] up to a
 * given length.
 *
 * The walk is leg4Walk 0 9 K M P: from P-1 up to K, down to M, up to 8, down
 * to 1.  Its landmark positions are A (the peak K), B (the valley M) and C
 * (the top 8).  For a trigger step d of the arm, let q = qmin(f d) be the least
 * walk position serving the level f d; the landmark sentence asks, for each
 * landmark position s < q, for a step j_s of the arm with |f j_s - w s| <= 1
 * (two-sided form) or with the one-sided half of that inequality (one-sided
 * form), the steps increasing, each gap at least the walk's own, the first at
 * least A and the last at least (q - s_last) before d.
 *
 * foldsOnto_landmark1/2 (HPC/Fold/Landmark.lean) say the sentence is necessary.
 * This program asks whether it is sufficient.
 *
 * Usage: probe59 [maxlen]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXW 96
#define MAXM 32

static int W[MAXW], WL;
static int A, B, C;           /* landmark positions of the walk */

static int buildWalk4(int *w, int start, int a, int b, int c, int e) {
  int len = 0, cur = start;
  w[len++] = cur;
  int tgt[4] = {a, b, c, e};
  for (int q = 0; q < 4; q++) {
    if (tgt[q] == cur) return -1;
    int s = tgt[q] > cur ? 1 : -1;
    while (cur != tgt[q]) { cur += s; if (len >= MAXW) return -1; w[len++] = cur; }
  }
  return len;
}

/* the dynamic program of HPC/Fold/Decide.lean */
static int folds(const int *f, int m) {
  char cur[MAXW], nxt[MAXW];
  for (int u = 0; u < WL; u++) cur[u] = 0;
  if (f[0] - W[0] > 1 || W[0] - f[0] > 1) return 0;
  cur[0] = 1;
  for (int j = 1; j < m; j++) {
    int any = 0;
    for (int u = 0; u < WL; u++) nxt[u] = 0;
    for (int u = 0; u < WL; u++) {
      if (!cur[u]) continue;
      for (int e = -1; e <= 1; e++) {
        int u2 = u + e;
        if (u2 < 0 || u2 >= WL) continue;
        int d = f[j] - W[u2];
        if (d <= 1 && d >= -1) { nxt[u2] = 1; any = 1; }
      }
    }
    if (!any) return 0;
    memcpy(cur, nxt, sizeof(char) * WL);
  }
  return 1;
}

static int qmin(int v) {           /* least walk position serving the level v */
  for (int u = 0; u < WL; u++) { int d = v - W[u]; if (d <= 1 && d >= -1) return u; }
  return WL;                        /* not served at all */
}

/* the least final index of a landmark chain at the positions s[0..r-1].
 * `two` selects the two-sided reading |f j - W s| <= 1; otherwise only the
 * half of it that points away from the walk's interior is asked. */
static int chainEnd(const int *f, int m, const int *s, int r, int two) {
  int at = -1;                      /* index of the previous landmark */
  for (int t = 0; t < r; t++) {
    int lo = (t == 0) ? s[0] : at + (s[t] - s[t-1]);
    int found = -1;
    for (int j = lo; j < m; j++) {
      int ok;
      if (two) ok = (f[j] >= W[s[t]] - 1 && f[j] <= W[s[t]] + 1);
      else {
        /* the one-sided half: a peak landmark asks only for a high time, a
         * valley landmark only for a low one */
        int peak = (s[t] == A || s[t] == C);
        ok = peak ? (f[j] >= W[s[t]] - 1) : (f[j] <= W[s[t]] + 1);
      }
      if (ok) { found = j; break; }
    }
    if (found < 0) return -1;
    at = found;
  }
  return at;
}

/* the landmark sentence.  Returns 1 if it holds. */
static int land(const int *f, int m, int two) {
  if (f[0] - W[0] > 1 || W[0] - f[0] > 1) return 0;
  int ls[3]; int e1, e2, e3;
  ls[0] = A; e1 = chainEnd(f, m, ls, 1, two);
  ls[0] = A; ls[1] = B; e2 = chainEnd(f, m, ls, 2, two);
  ls[0] = A; ls[1] = B; ls[2] = C; e3 = chainEnd(f, m, ls, 3, two);
  for (int d = 0; d < m; d++) {
    int q = qmin(f[d]);
    if (q >= WL) return 0;          /* the level is on no position of the walk */
    int r = 0; int last = -1;
    if (A < q) { r = 1; last = A; }
    if (B < q) { r = 2; last = B; }
    if (C < q) { r = 3; last = C; }
    if (r == 0) continue;
    int e = (r == 1) ? e1 : (r == 2) ? e2 : e3;
    if (e < 0) return 0;
    if (e + (q - last) > d) return 0;
  }
  return 1;
}

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void randomMode(long rounds, int maxlen) {
  printf("\nrandom Lipschitz arms, %ld per parameter set, length <= %d\n\n", rounds, maxlen);
  printf("  P  K  M | fold | land2 | land2&!fold | land1&!fold | fold&!land2\n");
  for (int P = 2; P <= 6; P++)
    for (int K = P; K <= 8; K++)
      for (int M = 1; M <= P - 2; M++) {
        if (M + 3 > K) continue;
        WL = buildWalk4(W, P - 1, K, M, 8, 1);
        if (WL < 0) continue;
        A = K - P + 1; B = 2 * K - P + 1 - M; C = 2 * K - P + 9 - 2 * M;
        long nf = 0, nl = 0, bad2 = 0, bad1 = 0, nec = 0;
        int f[512];
        for (long r = 0; r < rounds; r++) {
          int m = 1 + (int)(rnd() % maxlen);
          f[0] = P - 2 + (int)(rnd() % 3);
          if (f[0] < 0) f[0] = 0;
          for (int t = 1; t < m; t++) {
            int e = (int)(rnd() % 3) - 1;
            int v = f[t-1] + e;
            if (v < 0 || v > 9) v = f[t-1];
            f[t] = v;
          }
          int fo = folds(f, m), l2 = land(f, m, 1), l1 = land(f, m, 0);
          if (fo) nf++;
          if (l2) nl++;
          if (l2 && !fo) { bad2++;
            if (bad2 <= 3) { printf("    land2 without fold at P%d K%d M%d:", P, K, M);
              for (int t = 0; t < m; t++) printf(" %d", f[t]); printf("\n"); } }
          if (l1 && !fo) { bad1++;
            if (bad1 <= 3) { printf("    land1 without fold at P%d K%d M%d:", P, K, M);
              for (int t = 0; t < m; t++) printf(" %d", f[t]); printf("\n"); } }
          if (fo && !l2) { nec++;
            if (nec <= 3) { printf("    fold without land2 at P%d K%d M%d:", P, K, M);
              for (int t = 0; t < m; t++) printf(" %d", f[t]); printf("\n"); } }
        }
        printf("  %d  %d  %d | %ld | %ld | %ld | %ld | %ld\n", P, K, M, nf, nl, bad2, bad1, nec);
        fflush(stdout);
      }
}

int main(int argc, char **argv) {
  int maxlen = (argc > 1) ? atoi(argv[1]) : 13;
  if (argc > 2 && argv[2][0] == 'r') {
    randomMode((argc > 3) ? atol(argv[3]) : 200000, maxlen);
    return 0;
  }
  printf("probe59: exhaustive Lipschitz arms of [0,9], length <= %d\n\n", maxlen);
  printf("  P  K  M  len |   arms  |  fold  | land2 | land2&!fold | land1 | land1&!fold | !land&fold\n");
  for (int P = 2; P <= 6; P++)
    for (int K = P; K <= 8; K++)
      for (int M = 1; M <= P - 2; M++) {
        if (M + 3 > K) continue;
        WL = buildWalk4(W, P - 1, K, M, 8, 1);
        if (WL < 0) continue;
        A = K - P + 1; B = 2 * K - P + 1 - M; C = 2 * K - P + 9 - 2 * M;
        if (W[A] != K || W[B] != M || W[C] != 8) { printf("BAD LANDMARKS P%d K%d M%d\n", P, K, M); continue; }
        long arms = 0, nf = 0, nl2 = 0, nl1 = 0, bad2 = 0, bad1 = 0, nec = 0;
        int f[MAXM];
        for (int m = 1; m <= maxlen; m++) {
          /* enumerate arms of length m with base in [P-2, P] */
          for (int b = P - 2; b <= P; b++) {
            if (b < 0 || b > 9) continue;
            f[0] = b;
            long total = 1; for (int t = 1; t < m; t++) total *= 3;
            for (long code = 0; code < total; code++) {
              long c2 = code; int ok = 1;
              for (int t = 1; t < m; t++) { int e = (int)(c2 % 3) - 1; c2 /= 3;
                f[t] = f[t-1] + e; if (f[t] < 0 || f[t] > 9) { ok = 0; break; } }
              if (!ok) continue;
              arms++;
              int fo = folds(f, m), l2 = land(f, m, 1), l1 = land(f, m, 0);
              if (fo) nf++;
              if (l2) nl2++;
              if (l1) nl1++;
              if (l2 && !fo) bad2++;
              if (l1 && !fo) bad1++;
              if (fo && !l2) nec++;
            }
          }
        }
        printf("  %d  %d  %d  %3d | %7ld | %6ld | %5ld | %11ld | %5ld | %11ld | %10ld\n",
               P, K, M, WL, arms, nf, nl2, bad2, nl1, bad1, nec);
        fflush(stdout);
      }
  return 0;
}
