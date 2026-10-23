/* probe59b.c -- batch 59, question 1, second pass: the invariant.
 *
 * The landmark sentence of a four-leg walk is (probe59) equivalent to the fold
 * on every arm tested.  This program tests the *proof* of the sufficiency half
 * before it is attempted in Lean: the greedy time sequence gseq4 of
 * HPC/Fold/Leg4.lean is run on arms satisfying the landmark sentence, and the
 * six bounds of the candidate invariant are checked at every step.
 *
 *   t1 = least j >= A            with u j >= K-1
 *   t2 = least k >= t1 + (B-A)   with u k <= M+1
 *   t3 = least l >= t2 + (C-B)   with u l >= H-2
 *
 *   (1)                q j >= min(j, u j - P + 2, A)
 *   (2)   j >= t1  ->  q j >= min(A + (j-t1), 2K-P+2 - u j, B)
 *   (2')  j >= t1  ->  q j >= 2K-P - u j
 *   (3)   j >= t2  ->  q j >= min(B + (j-t2), u j + 2K-P+2-2M, C)
 *   (3')  j >= t2  ->  q j >= u j + 2K-P-2M
 *   (4)   j >= t3  ->  q j >= 2K-P+2H-2M-2 - u j
 *
 * and Val4 (u j) (q j) at every step -- which is the fold.
 *
 * Usage: probe59b [maxlen] [rounds]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXW 128
#define MAXM 600

static int W[MAXW], WL;
static int A, B, C, Pp, Kk, Mm;
static const int L = 0;
static int H = 9;

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

/* Val4 L H K M P v u, verbatim from HPC/Fold/Leg4.lean */
static int Val4(int v, int u) {
  int P = Pp, K = Kk, M = Mm;
  if (0 <= u && u <= K - P + 1 && v - P <= u && u <= v - P + 2) return 1;
  if (K - P + 1 <= u && u <= 2*K - P + 1 - M && 2*K - P - v <= u && u <= 2*K - P + 2 - v) return 1;
  if (2*K - P + 1 - M <= u && u <= 2*K - P + H - 2*M &&
      v + 2*K - P - 2*M <= u && u <= v + 2*K - P + 2 - 2*M) return 1;
  if (2*K - P + H - 2*M <= u && u <= 2*K - P + 2*H - 2*M - L - 2 &&
      2*K - P + 2*H - 2*M - 2 - v <= u && u <= 2*K - P + 2*H - 2*M - v) return 1;
  return 0;
}

static int gstep4(int v, int q) {
  if (Val4(v, q + 1)) return q + 1;
  if (Val4(v, q)) return q;
  return q - 1;
}

static int mn(int a, int b) { return a < b ? a : b; }

/* the landmark sentence, one-sided reading (probe59) */
static int qmin(int v) {
  for (int u = 0; u < WL; u++) { int d = v - W[u]; if (d <= 1 && d >= -1) return u; }
  return WL;
}

static int T1, T2, T3;
static void chains(const int *f, int m) {
  T1 = T2 = T3 = 1 << 29;
  for (int j = A; j < m; j++) if (f[j] >= Kk - 1) { T1 = j; break; }
  if (T1 > m) return;
  for (int k = T1 + (B - A); k < m; k++) if (f[k] <= Mm + 1) { T2 = k; break; }
  if (T2 > m) return;
  for (int l = T2 + (C - B); l < m; l++) if (f[l] >= H - 2) { T3 = l; break; }
}

static int land(const int *f, int m) {
  if (f[0] - W[0] > 1 || W[0] - f[0] > 1) return 0;
  chains(f, m);
  for (int d = 0; d < m; d++) {
    int q = qmin(f[d]);
    if (q >= WL) return 0;
    int r = 0, last = -1;
    if (A < q) { r = 1; last = A; }
    if (B < q) { r = 2; last = B; }
    if (C < q) { r = 3; last = C; }
    if (r == 0) continue;
    int e = (r == 1) ? T1 : (r == 2) ? T2 : T3;
    if (e > m) return 0;
    if (e + (q - last) > d) return 0;
  }
  return 1;
}

static unsigned long long rs = 987654321123ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
  int maxlen = (argc > 1) ? atoi(argv[1]) : 40;
  long rounds = (argc > 2) ? atol(argv[2]) : 300000;
  if (argc > 3) rs = (unsigned long long)atol(argv[3]);
  long tested = 0, badVal = 0, badInv[6] = {0,0,0,0,0,0}, badFold = 0, greedyLoses = 0;
  int f[MAXM];
  for (int Hb = 5; Hb <= 12; Hb++) {
  H = Hb;
  for (int P = 2; P <= 6; P++)
    for (int K = P; K <= H - 1; K++)
      for (int M = 1; M <= P - 2; M++) {
        if (M + 3 > K) continue;
        if (H > K + 3) continue;
        WL = buildWalk4(W, P - 1, K, M, H - 1, 1);
        if (WL < 0) continue;
        Pp = P; Kk = K; Mm = M;
        A = K - P + 1; B = 2*K - P + 1 - M; C = 2*K - P + H - 2*M;
        for (long r = 0; r < rounds; r++) {
          int m = 1 + (int)(rnd() % maxlen);
          f[0] = P - 2 + (int)(rnd() % 3);
          if (f[0] < 0) f[0] = 0;
          if (f[0] > H) f[0] = H;
          for (int t = 1; t < m; t++) {
            int e = (int)(rnd() % 3) - 1;
            int v = f[t-1] + e;
            if (v < 0 || v > H) v = f[t-1];
            f[t] = v;
          }
          if (!land(f, m)) continue;
          tested++;
          if (!folds(f, m)) { badFold++; continue; }
          /* run the greedy and check the invariant */
          int q = 0, bad = 0;
          for (int j = 0; j < m; j++) {
            if (j > 0) q = gstep4(f[j], q);
            if (!Val4(f[j], q)) { badVal++; bad = 1; break; }
            if (q < mn(mn(j, f[j] - P + 2), A)) badInv[0]++;
            if (j >= T1) {
              if (q < mn(mn(A + (j - T1), 2*K - P + 2 - f[j]), B)) badInv[1]++;
              if (q < 2*K - P - f[j]) badInv[2]++;
            }
            if (j >= T2) {
              if (q < mn(mn(B + (j - T2), f[j] + 2*K - P + 2 - 2*M), C)) badInv[3]++;
              if (q < f[j] + 2*K - P - 2*M) badInv[4]++;
            }
            if (j >= T3) {
              if (q < 2*K - P + 2*H - 2*M - 2 - f[j]) badInv[5]++;
            }
          }
          if (bad) {
            greedyLoses++;
            if (greedyLoses <= 5) {
              printf("  greedy fails though the arm folds, P%d K%d M%d:", P, K, M);
              for (int t = 0; t < m; t++) printf(" %d", f[t]);
              printf("   (t1 %d t2 %d t3 %d)\n", T1, T2, T3);
            }
          }
        }
      }
  }
  printf("\narms satisfying the landmark sentence: %ld\n", tested);
  printf("  of which the dynamic program rejects: %ld\n", badFold);
  printf("  greedy loses legality:                %ld\n", badVal);
  printf("  invariant failures (1)(2)(2')(3)(3')(4): %ld %ld %ld %ld %ld %ld\n",
         badInv[0], badInv[1], badInv[2], badInv[3], badInv[4], badInv[5]);
  return 0;
}
