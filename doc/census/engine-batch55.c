/* engine-batch55.c -- batch 55, COMMISSION.md section 2 question 3.
 *
 * Engines for four turns.  HPC/Fold/Leg4.lean carries a four-leg engine whose
 * walk is leg4Walk L H K M P -- from P-1 up to K, down to M, up to H-1, down to
 * L+1 -- proved under the window
 *
 *     L+2 <= P <= L+4,  P+1 <= K <= H-1,  L+1 <= M,  M = P-2,  M+3 <= K,
 *     H <= K+3,
 *
 * so the base is at most L+4 and the valley exactly two below the base.  The
 * two test walks of the commission, 5 -> 7 -> 3 -> 8 -> 1 and its mirror
 * 4 -> 3 -> 7 -> 1 -> 8, are outside that window: the first has P = L+6 and
 * M = P-3, the second is the reflection of a walk with P = L+6 and M = P-3.
 *
 * This program asks whether the engine's own argument survives the two
 * relaxations, before the argument is attempted in Lean.  Over every arm of the
 * corpus, at the parameters L=0, H=9, K=7, M=3, P=6, it
 *
 *   - evaluates the three announcements of foldsOnto_leg4 (floor, deep floor,
 *     ceiling) exactly as the Lean statement reads them;
 *   - runs the greedy time assignment gseq4 exactly as HPC/Fold/Leg4.lean
 *     defines it, and checks the window condition Val4 at every step -- that is
 *     the invariant the proof maintains;
 *   - checks, independently, whether the arm folds onto the walk at all, by the
 *     dynamic program of HPC/Fold/Decide.lean.
 *
 * A step at which Val4 fails on an arm that satisfies the announcements is a
 * counterexample to the generalised engine, and is printed with the arm.
 *
 * Usage: engine-batch55 [rand-rounds] [seed] [walk-steps]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { int *v; int n; } Path;

static Path bpath(int a, int b) {
  Path p;
  int d = a < b ? b - a : a - b;
  if (d <= 2) {
    p.n = d + 1;
    p.v = (int *)malloc(sizeof(int) * p.n);
    int s = (a <= b) ? 1 : -1;
    for (int u = 0; u < p.n; u++) p.v[u] = a + s * u;
    return p;
  }
  int mid = (a < b) ? b - 1 : b + 1;
  int c = (a < b) ? a + 1 : a - 1;
  Path p1 = bpath(a, mid), p2 = bpath(mid, c), p3 = bpath(c, b);
  p.n = p1.n + p2.n - 1 + p3.n - 1;
  p.v = (int *)malloc(sizeof(int) * p.n);
  memcpy(p.v, p1.v, sizeof(int) * p1.n);
  memcpy(p.v + p1.n, p2.v + 1, sizeof(int) * (p2.n - 1));
  memcpy(p.v + p1.n + p2.n - 1, p3.v + 1, sizeof(int) * (p3.n - 1));
  free(p1.v); free(p2.v); free(p3.v);
  return p;
}

/* a recursive chain whose splitting levels are one further in than Bing's: the
 * consolidation goes back to `b - back` and forward to `a + fwd`, which for
 * (back, fwd) = (1, 1) is Bing's own chain and otherwise is not. */
static Path vpath(int a, int b, int back, int fwd) {
  Path p;
  int d = a < b ? b - a : a - b;
  if (d <= 2) {
    p.n = d + 1;
    p.v = (int *)malloc(sizeof(int) * p.n);
    int s = (a <= b) ? 1 : -1;
    for (int u = 0; u < p.n; u++) p.v[u] = a + s * u;
    return p;
  }
  int up = (a < b);
  int mid = up ? b - back : b + back;
  int c = up ? a + fwd : a - fwd;
  if (up && (mid <= a || c >= b || mid <= c)) { mid = b - 1; c = a + 1; }
  if (!up && (mid >= a || c <= b || mid >= c)) { mid = b + 1; c = a - 1; }
  Path p1 = vpath(a, mid, back, fwd), p2 = vpath(mid, c, back, fwd),
       p3 = vpath(c, b, back, fwd);
  p.n = p1.n + p2.n - 1 + p3.n - 1;
  p.v = (int *)malloc(sizeof(int) * p.n);
  memcpy(p.v, p1.v, sizeof(int) * p1.n);
  memcpy(p.v + p1.n, p2.v + 1, sizeof(int) * (p2.n - 1));
  memcpy(p.v + p1.n + p2.n - 1, p3.v + 1, sizeof(int) * (p3.n - 1));
  free(p1.v); free(p2.v); free(p3.v);
  return p;
}

/* the concatenation of two chains, the common endpoint kept once */
static Path cat(Path x, Path y) {
  Path p;
  p.n = x.n + y.n - 1;
  p.v = (int *)malloc(sizeof(int) * p.n);
  memcpy(p.v, x.v, sizeof(int) * x.n);
  memcpy(p.v + x.n, y.v + 1, sizeof(int) * (y.n - 1));
  return p;
}

#define MAXLEV 32
#define MAXN   4096
#define MAXW   96

static int meetTab[MAXLEV][MAXN + 1];

/* IsCrookedIvF (rho, sig), exactly as HPC/Fold/Faithful.lean states it. */
static int crookedGen(const int *rho, const int *sig, int n) {
  for (int t = 0; t < n; t++) if (rho[t] > sig[t] || sig[t] > rho[t] + 1) return 0;
  for (int t = 0; t + 1 < n; t++) {
    int mx = sig[t] > sig[t+1] ? sig[t] : sig[t+1];
    int mn = rho[t] < rho[t+1] ? rho[t] : rho[t+1];
    if (mx > mn + 1) return 0;
  }
  for (int l = 0; l < MAXLEV; l++) meetTab[l][n] = n;
  for (int j = n - 1; j >= 0; j--)
    for (int l = 0; l < MAXLEV; l++)
      meetTab[l][j] = (rho[j] <= l && l <= sig[j]) ? j : meetTab[l][j + 1];
  for (int s = 0; s < n; s++) {
    int hs[8], nh = 0;
    for (int e = -1; e <= 1; e++) {
      int u = s + e; if (u < 0 || u >= n) continue;
      for (int l = rho[u]; l <= sig[u]; l++) {
        int seen = 0; for (int q = 0; q < nh; q++) if (hs[q] == l) seen = 1;
        if (!seen) hs[nh++] = l;
      }
    }
    for (int t = s + 1; t < n; t++) {
      int ks[8], nk = 0;
      for (int e = -1; e <= 1; e++) {
        int u = t + e; if (u < 0 || u >= n) continue;
        for (int l = rho[u]; l <= sig[u]; l++) {
          int seen = 0; for (int q = 0; q < nk; q++) if (ks[q] == l) seen = 1;
          if (!seen) ks[nk++] = l;
        }
      }
      for (int a = 0; a < nh; a++) for (int b = 0; b < nk; b++) {
        int h = hs[a], k = ks[b];
        int diff = h - k; if (diff < 0) diff = -diff;
        if (diff < 3) continue;
        int r1 = (h < k) ? k - 1 : k + 1, r2 = (h < k) ? h + 1 : h - 1;
        int p1 = meetTab[r1][s + 1];
        if (p1 >= t) return 0;
        int p2 = meetTab[r2][p1 + 1];
        if (p2 >= t) return 0;
      }
    }
  }
  return 1;
}

/* the dynamic program of HPC/Fold/Decide.lean */
static int folds(const int *f, int m, const int *w, int wl) {
  static char cur[MAXW], nxt[MAXW];
  for (int u = 0; u < wl; u++) cur[u] = 0;
  if (f[0] - w[0] > 1 || w[0] - f[0] > 1) return 0;
  cur[0] = 1;
  for (int j = 1; j < m; j++) {
    int any = 0;
    for (int u = 0; u < wl; u++) nxt[u] = 0;
    for (int u = 0; u < wl; u++) {
      if (!cur[u]) continue;
      for (int e = -1; e <= 1; e++) {
        int u2 = u + e;
        if (u2 < 0 || u2 >= wl) continue;
        int d = f[j] - w[u2];
        if (d <= 1 && d >= -1) { nxt[u2] = 1; any = 1; }
      }
    }
    if (!any) return 0;
    memcpy(cur, nxt, sizeof(char) * wl);
  }
  return 1;
}

static int buildWalk4(int *w, int start, int a, int b, int c, int e) {
  int len = 0, cur = start;
  w[len++] = cur;
  int tgt[4] = {a, b, c, e};
  for (int q = 0; q < 4; q++) {
    if (tgt[q] < 0) break;
    if (tgt[q] == cur) return -1;
    int s = tgt[q] > cur ? 1 : -1;
    while (cur != tgt[q]) { cur += s; if (len >= MAXW) return -1; w[len++] = cur; }
  }
  return len;
}

static int buildWalk(int *w, int start, int a, int b, int c) {
  int len = 0, cur = start;
  w[len++] = cur;
  int tgt[3] = {a, b, c};
  for (int q = 0; q < 3; q++) {
    if (tgt[q] < 0) break;
    if (tgt[q] == cur) return -1;
    int s = tgt[q] > cur ? 1 : -1;
    while (cur != tgt[q]) { cur += s; if (len >= MAXW) return -1; w[len++] = cur; }
  }
  return len;
}

static int rho[MAXN], sig[MAXN], armG[MAXN], armT[MAXN];

/* ---------------- the engine, at L=0, H=9, K=7, M=3, P=6 ----------------- */

static int EL = 0, EH = 9, EK = 7, EM = 3, EP = 6;

/* the thresholds of the three announcements; the engine of HPC/Fold/Leg4.lean
 * uses (M-1, M-2, K+2), and the variants below raise them one level at a time */
/* the announcement thresholds; pass 0 reads them as HPC/Fold/Leg4.lean does
 * (M-1 and M-2), pass 1 as HPC/Fold/Leg4Wide.lean does (P-3 and P-4) */
static int FLOORTH, DEEPTH, CEILTH;
static void setPass(int pass) {
  FLOORTH = pass ? EP - 3 : EM - 1;
  DEEPTH  = pass ? EP - 4 : EM - 2;
  CEILTH  = EK + 2;
}

/* Val4 L H K M P v u, exactly as HPC/Fold/Leg4.lean states it */
static int val4(long v, long u) {
  long L = EL, H = EH, K = EK, M = EM, P = EP;
  if (0 <= u && u <= K - P + 1 && v - P <= u && u <= v - P + 2) return 1;
  if (K - P + 1 <= u && u <= 2*K - P + 1 - M && 2*K - P - v <= u && u <= 2*K - P + 2 - v) return 1;
  if (2*K - P + 1 - M <= u && u <= 2*K - P + H - 2*M &&
      v + 2*K - P - 2*M <= u && u <= v + 2*K - P + 2 - 2*M) return 1;
  if (2*K - P + H - 2*M <= u && u <= 2*K - P + 2*H - 2*M - L - 2 &&
      2*K - P + 2*H - 2*M - 2 - v <= u && u <= 2*K - P + 2*H - 2*M - v) return 1;
  return 0;
}

/* gstep4 */
static long gstep4(long v, long q) {
  if (val4(v, q + 1)) return q + 1;
  if (val4(v, q)) return q;
  return q - 1;
}

/* the walk itself, as leg4Walk reads it */
static int engineWalk(int *w) {
  long L = EL, H = EH, K = EK, M = EM, P = EP;
  long len = 2*K - P + 2*H - 2*M - L - 1;
  for (long u = 0; u < len; u++) {
    long x;
    if (u <= K - P + 1) x = P - 1 + u;
    else if (u <= 2*K - P + 1 - M) x = 2*K - P + 1 - u;
    else if (u <= 2*K - P + H - 2*M) x = u - (2*K - P + 1) + 2*M;
    else x = 2*K - P + 2*H - 2*M - 1 - u;
    w[u] = (int)x;
  }
  return (int)len;
}

/* the three announcements of foldsOnto_leg4, read on the arm */
static int annFloor(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] > FLOORTH) continue;
    int ok = 0;
    for (int k = 0; k < d && !ok; k++) if (f[k] >= EK) ok = 1;
    for (int k = 0; k < d && !ok; k++) {
      if (f[k] > EP - 2) continue;
      for (int k2 = k + 1; k2 < d && !ok; k2++) if (f[k2] >= EK - 1) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

static int annDeep(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] > DEEPTH) continue;
    int ok = 0;
    for (int k = 0; k < d && !ok; k++) if (f[k] >= EK + 2) ok = 1;
    for (int k = 0; k < d && !ok; k++) {
      if (f[k] > EM - 1) continue;
      for (int k2 = k + 1; k2 < d && !ok; k2++) if (f[k2] >= EH - 2) ok = 1;
    }
    for (int k = 0; k < d && !ok; k++) {
      if (f[k] < EK + 1) continue;
      for (int k2 = k + 1; k2 < d && !ok; k2++) {
        if (f[k2] > EM) continue;
        for (int k3 = k2 + 1; k3 < d && !ok; k3++) if (f[k3] >= EH - 2) ok = 1;
      }
    }
    if (!ok) return 0;
  }
  return 1;
}

static int annCeil(const int *f, int m) {
  for (int d = 0; d < m; d++) {
    if (f[d] < CEILTH) continue;
    int ok = 0;
    for (int k = 0; k < d && !ok; k++) if (f[k] <= EM - 1) ok = 1;
    for (int k = 0; k < d && !ok; k++) {
      if (f[k] < EK + 1) continue;
      for (int k2 = k + 1; k2 < d && !ok; k2++) if (f[k2] <= EM + 1) ok = 1;
    }
    for (int k = 0; k < d && !ok; k++) {
      if (f[k] > EP - 2) continue;
      for (int k2 = k + 1; k2 < d && !ok; k2++) {
        if (f[k2] < EK) continue;
        for (int k3 = k2 + 1; k3 < d && !ok; k3++) if (f[k3] <= EM + 1) ok = 1;
      }
    }
    if (!ok) return 0;
  }
  return 1;
}

static long arms, armsBase, armsAnn, armsInvBad, armsFoldBad, armsFold;
static void zeroCounts(void);
static long byBase[3][4];  /* [f0 - (P-2)][ann, invBad, foldBad, fold] */
static int ewalk[MAXW], ewlen;

static void engineArm(const int *f, int m, const char *tag, int gen, int i, int which) {
  arms++;
  if (f[0] < EP - 2 || f[0] > EP) return;
  armsBase++;
  if (!annFloor(f, m) || !annDeep(f, m) || !annCeil(f, m)) return;
  armsAnn++;
  int bslot = f[0] - (EP - 2);
  byBase[bslot][0]++;
  /* the greedy, exactly as gseq4 defines it */
  long q = 0;
  int bad = -1;
  if (!val4(f[0], 0)) bad = 0;
  for (int d = 1; d < m && bad < 0; d++) {
    q = gstep4(f[d], q);
    if (!val4(f[d], q)) bad = d;
  }
  int fold = folds(f, m, ewalk, ewlen);
  if (fold) { armsFold++; byBase[bslot][3]++; }
  if (bad >= 0) {
    armsInvBad++; byBase[bslot][1]++;
    if (armsInvBad <= 8) {
      printf("  [%s %d] the greedy leaves Val4 at step %d (arm %d at basepoint %d, "
             "folds = %d):\n   ", tag, gen, bad, which, i, fold);
      for (int d = 0; d < m && d < 90; d++) printf(" %d", f[d]);
      printf("\n");
    }
  }
  if (!fold) {
    armsFoldBad++; byBase[bslot][2]++;
    if (armsFoldBad <= 8) {
      printf("  [%s %d] an arm with all three announcements does NOT fold onto "
             "5 -> 7 -> 3 -> 8 -> 1 (arm %d at basepoint %d):\n   ", tag, gen, which, i);
      for (int d = 0; d < m && d < 90; d++) printf(" %d", f[d]);
      printf("\n");
    }
  }
}


/* ---- the invariant of gseq4_inv, simulated with the features ------------
 *
 * The six features E, R, E2, S, S2, T of HPC/Fold/Leg4.lean are "has happened"
 * predicates of the arm's prefix; the invariant is Val4 together with one lower
 * bound on the greedy time per feature.  The three announcements enter the
 * induction only as the implications
 *
 *     u (j+1) <= FLOORTH -> R j,   u (j+1) <= DEEPTH -> T j,
 *     CEILTH <= u (j+1) -> S j,
 *
 * so the honest test of the generalised engine is: on every arm at which those
 * three implications hold at every step, does the invariant hold at every step?
 */

static long invArms, invEligible, invBadVal, invBadBound;

static void zeroCounts(void) {
  arms = armsBase = armsAnn = armsInvBad = armsFoldBad = armsFold = 0;
  invArms = invEligible = invBadVal = invBadBound = 0;
  for (int b = 0; b < 3; b++) for (int c = 0; c < 4; c++) byBase[b][c] = 0;
}

static long imin(long a, long b) { return a < b ? a : b; }

static void invariantArm(const int *f, int m, const char *tag, int gen, int i, int which) {
  long L = EL, H = EH, K = EK, M = EM, P = EP;
  invArms++;
  if (f[0] < EP - 2 || f[0] > EP) return;
  /* the features along the prefix */
  static int E[MAXN], R[MAXN], E2[MAXN], S[MAXN], S2[MAXN], T[MAXN];
  int e = 0, r = 0, e2 = 0, sS = 0, s2 = 0, tT = 0;
  int seenK1 = 0, lowP_K = 0, lowM1 = 0, K1_M = 0;
  for (int j = 0; j < m; j++) {
    long v = f[j];
    int ePrev = e, seenK1Prev = seenK1, lowP_KPrev = lowP_K, lowM1Prev = lowM1,
        K1_MPrev = K1_M;
    r  = r  || v >= K || (ePrev && v >= K - 1);
    e2 = e2 || v >= K + 1 || (ePrev && v >= K);
    sS = sS || v <= M - 1 || (seenK1Prev && v <= M + 1) || (lowP_KPrev && v <= M + 1);
    s2 = s2 || v <= M - 1 || (seenK1Prev && v <= M);
    tT = tT || v >= K + 2 || (lowM1Prev && v >= H - 2) || (K1_MPrev && v >= H - 2);
    lowP_K = lowP_K || (ePrev && v >= K);
    seenK1 = seenK1 || v >= K + 1;
    lowM1  = lowM1  || v <= M - 1;
    K1_M   = K1_M   || (seenK1Prev && v <= M);
    e = e || v <= P - 2;
    E[j] = e; R[j] = r; E2[j] = e2; S[j] = sS; S2[j] = s2; T[j] = tT;
  }
  /* the three implications, at the thresholds of this build */
  for (int j = 0; j + 1 < m; j++) {
    if (f[j + 1] <= FLOORTH && !R[j]) return;
    if (f[j + 1] <= DEEPTH && !T[j]) return;
    if (f[j + 1] >= CEILTH && !S[j]) return;
  }
  invEligible++;
  long q = 0;
  for (int j = 0; j < m; j++) {
    long v = f[j];
    if (j > 0) q = gstep4(v, q);
    if (!val4(v, q)) { invBadVal++;
      if (invBadVal <= 6) {
        printf("  [%s %d] the INVARIANT fails (Val4) at step %d, arm %d at basepoint %d:\n   ",
               tag, gen, j, which, i);
        for (int d = 0; d < m && d < 90; d++) printf(" %d", f[d]);
        printf("\n");
      }
      return; }
    int bad = 0;
    if (E[j]  && !(imin(v - P + 2, K - P + 1) <= q)) bad = 1;
    if (R[j]  && !(2*K - P - v <= q)) bad = 2;
    if (E2[j] && !(imin(2*K - P + 2 - v, 2*K - P + 1 - M) <= q)) bad = 3;
    if (S[j]  && !(v + 2*K - P - 2*M <= q)) bad = 4;
    if (S2[j] && !(imin(v + 2*K - P + 2 - 2*M, 2*K - P + H - 2*M) <= q)) bad = 5;
    if (T[j]  && !(2*K - P + 2*H - 2*M - 2 - v <= q)) bad = 6;
    if (bad) { invBadBound++;
      if (invBadBound <= 6) {
        printf("  [%s %d] the INVARIANT fails (bound %d) at step %d, arm %d at basepoint %d:\n   ",
               tag, gen, bad, j, which, i);
        for (int d = 0; d < m && d < 90; d++) printf(" %d", f[d]);
        printf("\n");
      }
      return; }
  }
}

static void scan(int n, const char *tag, int gen) {
  static int aG[MAXN], aT[MAXN];
  for (int i = 0; i < n; i++) {
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) aG[d] = rho[i + d];
    for (int d = 0; d < mt; d++) aT[d] = rho[i - d];
    engineArm(aG, mg, tag, gen, i, 0);
    engineArm(aT, mt, tag, gen, i, 1);
    invariantArm(aG, mg, tag, gen, i, 0);
    invariantArm(aT, mt, tag, gen, i, 1);
  }
}

/* -------------------------- the generators ------------------------------- */

static void runChain(int n, const int *v, long rounds, long walkSteps, const char *name) {
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  if (crookedGen(rho, sig, n)) scan(n, "thin", 0);
  for (int pk = 1; pk + 1 < n; pk++) {
    if (!(v[pk] > v[pk-1] && v[pk] > v[pk+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    rho[pk] = v[pk] - 1;
    if (crookedGen(rho, sig, n)) scan(n, "shave", pk);
  }
  for (int vl = 1; vl + 1 < n; vl++) {
    if (!(v[vl] < v[vl-1] && v[vl] < v[vl+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    sig[vl] = v[vl] + 1;
    if (crookedGen(rho, sig, n)) scan(n, "fill", vl);
  }
  for (long it = 0; it < rounds; it++) {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) { if (random() % 3 == 0) rho[j] = v[j] - 1; }
      else if (v[j] < v[j-1] && v[j] < v[j+1]) { if (random() % 3 == 0) sig[j] = v[j] + 1; }
    }
    if (crookedGen(rho, sig, n)) scan(n, "mix", (int)it);
  }
  {
    static int crho[MAXN], csig[MAXN];
    for (int u = 0; u < n; u++) { crho[u] = v[u]; csig[u] = v[u]; }
    long accepted = 0;
    for (long it = 0; it < walkSteps; it++) {
      int j = 1 + (int)(random() % (n - 2));
      int which = (int)(random() % 2), delta = (random() % 2) ? 1 : -1;
      for (int u = 0; u < n; u++) { rho[u] = crho[u]; sig[u] = csig[u]; }
      if (which == 0) rho[j] += delta; else sig[j] += delta;
      if (rho[j] > sig[j] || sig[j] > rho[j] + 1) continue;
      if (rho[j] < 0 || sig[j] > 9) continue;
      if (!crookedGen(rho, sig, n)) continue;
      accepted++;
      for (int u = 0; u < n; u++) { crho[u] = rho[u]; csig[u] = sig[u]; }
      scan(n, "walk", (int)accepted);
    }
  }
}

int main(int argc, char **argv) {
  long rounds = (argc > 1) ? atol(argv[1]) : 8;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 55u;
  long walkSteps = (argc > 3) ? atol(argv[3]) : 40;
  srandom(seed);
  printf("engine-batch55: the four-leg engine of HPC/Fold/Leg4.lean, with the two floor\n"
         "announcements read at P-3 and P-4 (which is what they are when M = P-2), swept over\n"
         "every parameter set L=0, H=9, L+2 <= P <= L+6, L+1 <= M <= P-2, M+3 <= K <= H-1,\n"
         "H <= K+3, P <= K.  For each set: the arms of the corpus based within two of P that\n"
         "satisfy the three announcements, the steps at which the greedy leaves Val4, the arms\n"
         "that do not fold onto the walk at all, and the invariant of gseq4_inv.\n\n");
  Path p = bpath(0, 9);
  Path q = bpath(9, 0);
  int nbad = 0, nsets = 0;
  for (EP = 2; EP <= 6; EP++)
    for (EM = 1; EM <= EP - 2; EM++)
      for (EK = (EM + 3 > EP ? EM + 3 : EP); EK <= 8; EK++) {
        if (EH > EK + 3) continue;
        nsets++;
        ewlen = engineWalk(ewalk);
        printf("---- L=%d H=%d K=%d M=%d P=%d (walk of %d times:", EL, EH, EK, EM, EP, ewlen);
        for (int u = 0; u < ewlen; u++) printf(" %d", ewalk[u]);
        printf(")\n");
        for (int pass = 0; pass < 2; pass++) {
          setPass(pass);
          zeroCounts();
          runChain(p.n, p.v, rounds, walkSteps, "bing 0 9");
          runChain(q.n, q.v, rounds, walkSteps, "bing 9 0");
          printf("  %s (floor %d, deep %d): announced arms %ld; the greedy leaves Val4 at %ld; "
                 "the arm does not fold at %ld; the invariant fails at %ld/%ld\n",
                 pass ? "Leg4Wide, at P-3 and P-4" : "Leg4, at M-1 and M-2",
                 FLOORTH, DEEPTH, armsAnn, armsInvBad, armsFoldBad, invBadVal, invBadBound);
          for (int b = 0; b < 3; b++)
            printf("    base %d: announced %ld, Val4 fails %ld, does not fold %ld\n",
                   EP - 2 + b, byBase[b][0], byBase[b][1], byBase[b][2]);
          if (armsInvBad || armsFoldBad || invBadVal || invBadBound) { if (pass) nbad++;
            printf("  *** this reading FAILS at this parameter set ***\n"); }
        }
      }
  printf("\n================ %d parameter sets; the reading of HPC/Fold/Leg4Wide.lean "
         "fails at %d of them ================\n", nsets, nbad);
  return 0;
}
