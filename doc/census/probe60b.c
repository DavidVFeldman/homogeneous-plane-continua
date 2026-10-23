/* probe60b.c -- batch 60, question 1, second pass: how many walks does the
 * *arm-only* half of exhaustiveness at the branch L+5 need?
 *
 * Every 1-Lipschitz arm of the band [0, 9] based at 5 with LowAt (L+1) (L+8),
 * exhaustively up to a given length, is tested against three named walks by
 * their exact criteria (Leg4Land, HPC/Fold/Leg4Land.lean):
 *
 *   wb  = reflected (P,K,M) = (4,6,2)   L+6 -> L+3 -> L+7 -> L+1 -> L+8
 *         (the best walk of the branch; its descent clause is the branch
 *          hypothesis, land_down1_of_lowAt_low)
 *   w8  = direct    (P,K,M) = (5,8,1)   L+4 -> L+8 -> L+1 -> L+8 -> L+1
 *   w3  = reflected (P,K,M) = (4,6,1)   L+6 -> L+3 -> L+8 -> L+1 -> L+8
 *
 * and the program reports the arms served by none of them, the arms served by
 * none of wb and w8, and -- the dichotomy of question 1 -- the arms that fail
 * the floor (L+8) clause of wb and are not served by w8, and the arms that fail
 * its deep (L+9) clause and are served by neither w8 nor w3.
 *
 * Usage: probe60b [maxlen]
 */

#include <stdio.h>
#include <stdlib.h>

#define MAXM 40

/* Leg4Land, clause by clause: 1 base, 2 floor, 4 deep, 8 ceiling */
static int landMask(const int *f, int m, int K, int M, int P) {
  const int H = 9;
  int A = K - P + 1, bad = 0;
  if (f[0] < P - 2 || f[0] > P) bad |= 1;
  int t1 = -1, t2 = -1, t3 = -1;
  for (int j = A; j < m; j++) if (j >= 0 && f[j] >= K - 1) { t1 = j; break; }
  if (t1 >= 0) for (int k = t1 + (K - M); k < m; k++) if (f[k] <= M + 1) { t2 = k; break; }
  if (t2 >= 0) for (int l = t2 + (H - 1 - M); l < m; l++) if (f[l] >= H - 2) { t3 = l; break; }
  for (int d = 0; d < m; d++) {
    if (f[d] <= P - 3 && (t1 < 0 || t1 + (K - 1 - f[d]) > d)) bad |= 2;
    if (f[d] <= M - 2 && (t3 < 0 || t3 + (H - 2 - f[d]) > d)) bad |= 4;
    if (f[d] >= K + 2 && (t2 < 0 || t2 + (f[d] - M - 1) > d)) bad |= 8;
  }
  return bad;
}

static int lowAt(const int *f, int m) {
  int h8 = 0, l2 = 0, l26 = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= 1 && !h8 && !l26) return 0;
    if (f[d] >= 8) h8 = 1;
    if (f[d] >= 6 && l2) l26 = 1;
    if (f[d] <= 2) l2 = 1;
  }
  return 1;
}

static long arms = 0, okB = 0, ok8 = 0, ok3 = 0;
static long noneOfThree = 0, noneOfTwo = 0, none83 = 0;
static long floorFail = 0, floorNo8 = 0, deepFail = 0, deepNo83 = 0;
static int shown = 0;
static long setCount[8];
static int f[MAXM];

static void examine(int m) {
  int g[MAXM];
  for (int d = 0; d < m; d++) g[d] = 9 - f[d];
  int mb = landMask(g, m, 6, 2, 4);
  int m8 = landMask(f, m, 8, 1, 5);
  int m3 = landMask(g, m, 6, 1, 4);
  arms++;
  setCount[(mb == 0 ? 1 : 0) | (m8 == 0 ? 2 : 0) | (m3 == 0 ? 4 : 0)]++;
  if (mb == 0) okB++;
  if (m8 == 0) ok8++;
  if (m3 == 0) ok3++;
  if (mb && m8 && m3) {
    noneOfThree++;
    if (shown < 8) {
      shown++;
      printf("  served by none of wb, w8, w3 (masks %d %d %d):", mb, m8, m3);
      for (int d = 0; d < m; d++) printf(" %d", f[d]);
      printf("\n");
    }
  }
  if (mb && m8) noneOfTwo++;
  if (m8 && m3) none83++;
  if (mb & 2) { floorFail++; if (m8) floorNo8++; }
  if (mb & 4) { deepFail++; if (m8 && m3) deepNo83++; }
}

static void rec(int at, int len) {
  if (at == len) { if (lowAt(f, len)) examine(len); return; }
  for (int e = -1; e <= 1; e++) {
    int v = f[at - 1] + e;
    if (v < 0 || v > 9) continue;
    f[at] = v;
    rec(at + 1, len);
  }
}

int main(int argc, char **argv) {
  int maxlen = (argc > 1) ? atoi(argv[1]) : 15;
  printf("probe60b: the arm-only half of exhaustiveness at the branch L+5, three named walks,\n"
         "exhaustive 1-Lipschitz arms of [0,9] based at 5 with LowAt (L+1) (L+8), length <= %d\n",
         maxlen);
  for (int len = 1; len <= maxlen; len++) { f[0] = 5; rec(1, len); }
  printf("\narms %ld; served by wb %ld, by w8 %ld, by w3 %ld\n", arms, okB, ok8, ok3);
  printf("served by neither wb nor w8: %ld; by none of the three: %ld\n", noneOfTwo, noneOfThree);
  printf("served by neither w8 nor w3: %ld\n", none83);
  printf("\nthe service sets (bit 1 = wb, bit 2 = w8, bit 4 = w3):\n");
  for (int t = 0; t < 8; t++)
    printf("  {%s%s%s} : %ld\n", (t & 1) ? "wb " : "", (t & 2) ? "w8 " : "",
           (t & 4) ? "w3" : "", setCount[t]);
  printf("arms failing the floor (L+8) clause of wb: %ld; of them not served by w8: %ld\n",
         floorFail, floorNo8);
  printf("arms failing the deep (L+9) clause of wb: %ld; of them served by neither w8 nor w3: "
         "%ld\n", deepFail, deepNo83);
  return 0;
}
