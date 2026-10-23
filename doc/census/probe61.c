/* probe61.c -- batch 61, question 1: the crossing at the branch L+5, read arm
 * by arm, with the walk the census picks out added to the list.
 *
 * The census of batch 61 finds that every five-walk crossing of the corpus is
 * served, on both arms, by
 *
 *   w71 = direct (P,K,M) = (5,7,1)      L+4 -> L+7 -> L+1 -> L+8 -> L+1
 *
 * This probe measures, exhaustively over every 1-Lipschitz arm of the band
 * [0, 9] based at 5 with LowAt (L+1) (L+8), the joint service sets of the four
 * walks
 *
 *   wb  = reflected (4,6,2)   L+6 -> L+3 -> L+7 -> L+1 -> L+8
 *   w8  = direct    (5,8,1)   L+4 -> L+8 -> L+1 -> L+8 -> L+1
 *   w3  = reflected (4,6,1)   L+6 -> L+3 -> L+8 -> L+1 -> L+8
 *   w71 = direct    (5,7,1)   L+4 -> L+7 -> L+1 -> L+8 -> L+1
 *
 * so that the implications a proof of the crossing might use -- "an arm served
 * only by w8 is served by w71", "an arm that fails w8 is served by w71", and so
 * on -- can be read off before they are attempted in Lean.  Arms only: no pair,
 * no faithfulness hypothesis beyond the band, the Lipschitz condition, the
 * basepoint L+5 and the branch hypothesis.
 *
 * Usage: probe61 [maxlen]
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

static long arms = 0;
static long setCount[16];
static long w71Fail = 0;
static int shownNo71 = 0, shownCross = 0;
static int f[MAXM];

/* the clauses of w71 that fail, on the arms that fail it */
static long w71Floor = 0, w71Ceil = 0;

static void examine(int m) {
  int g[MAXM];
  for (int d = 0; d < m; d++) g[d] = 9 - f[d];
  int mb = landMask(g, m, 6, 2, 4);
  int m8 = landMask(f, m, 8, 1, 5);
  int m3 = landMask(g, m, 6, 1, 4);
  int m71 = landMask(f, m, 7, 1, 5);
  arms++;
  int s = (mb == 0 ? 1 : 0) | (m8 == 0 ? 2 : 0) | (m3 == 0 ? 4 : 0) | (m71 == 0 ? 8 : 0);
  setCount[s]++;
  if (m71) {
    w71Fail++;
    if (m71 & 2) w71Floor++;
    if (m71 & 8) w71Ceil++;
    if (shownNo71 < 6) {
      shownNo71++;
      printf("  not served by w71 (mask %d; wb %d w8 %d w3 %d):", m71, mb == 0, m8 == 0, m3 == 0);
      for (int d = 0; d < m; d++) printf(" %d", f[d]);
      printf("\n");
    }
  }
  /* an arm that could be one half of a crossing: served by w8 alone, or by
   * neither w8 nor w71 */
  if (m8 == 0 && mb && m3 && m71 && shownCross < 6) {
    shownCross++;
    printf("  served by w8 alone and not by w71:");
    for (int d = 0; d < m; d++) printf(" %d", f[d]);
    printf("\n");
  }
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
  int maxlen = (argc > 1) ? atoi(argv[1]) : 16;
  printf("probe61: the four walks wb, w8, w3, w71 on every 1-Lipschitz arm of [0,9] based at 5\n"
         "with LowAt (L+1) (L+8), exhaustively to length %d\n", maxlen);
  for (int len = 1; len <= maxlen; len++) { f[0] = 5; rec(1, len); }
  printf("\narms %ld; arms not served by w71: %ld (floor clause fails at %ld, ceiling at %ld)\n",
         arms, w71Fail, w71Floor, w71Ceil);
  printf("\nthe service sets (bit 1 = wb, 2 = w8, 4 = w3, 8 = w71):\n");
  for (int t = 0; t < 16; t++)
    printf("  {%s%s%s%s} : %ld\n", (t & 1) ? "wb " : "", (t & 2) ? "w8 " : "",
           (t & 4) ? "w3 " : "", (t & 8) ? "w71" : "", setCount[t]);
  /* the implications a proof of the crossing might use */
  {
    long a = 0, b = 0, c = 0, d = 0, e = 0;
    for (int t = 0; t < 16; t++) {
      int wb = t & 1, w8 = t & 2, w3 = t & 4, w71 = t & 8;
      if (w8 && !wb && !w3 && !w71) a += setCount[t];   /* {w8} alone, no w71 */
      if (!w8 && !w71) b += setCount[t];                /* fails w8, no w71 */
      if (wb && !w8 && !w3 && !w71) c += setCount[t];   /* {wb} alone, no w71 */
      if (w3 && !w8 && !wb && !w71) d += setCount[t];   /* {w3} alone, no w71 */
      if (wb && w3 && !w8 && !w71) e += setCount[t];    /* {wb,w3}, no w71 */
    }
    printf("\nthe implications:\n");
    printf("  served by w8 alone and not by w71 : %ld\n", a);
    printf("  fails w8 and not served by w71    : %ld\n", b);
    printf("  served by wb alone, not by w71    : %ld\n", c);
    printf("  served by w3 alone, not by w71    : %ld\n", d);
    printf("  served by wb and w3, not by w71   : %ld\n", e);
  }
  return 0;
}
