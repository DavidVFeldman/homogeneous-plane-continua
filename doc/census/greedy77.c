/* greedy77.c -- exploration (not a proof): the greedy jump-zigzag.
 *
 * For a basepoint i of a faithful pair (rho, sigma), arms G = rho[i..], T = rho[i..0], p = rho[i]:
 * the greedy builds turning levels p = T0, T1, T2, ... (directions alternating, first direction
 * given).  In an up phase from turn b (entered by each arm at its own time tau_X), each arm not yet
 * finished contributes M_X = its maximum before it first drops below b - 1; the next turn is
 * min_X M_X + 1 (capped at H + 1); symmetrically for down phases.  An arm is finished when from
 * tau_X on it never leaves the phase envelope ([b-1, target+1] up).  The greedy FAILS when a turn
 * would not expand (not beyond every earlier level on its side) or a first leg is shorter than 2
 * or a later one shorter than 3.
 *
 * Every successful walk (on a sample of basepoints) is re-decided exactly: the walk is
 * c = [p] ++ leg(T0,T1) ++ ..., leg(a,b) = [a+3d, ..., b] (or [b] if |b-a|<3), and FoldsOnto is
 * decided for both whole arms by propagation of the set of reachable walk times.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int SPAN = 10;
/* ------------------------------------------------------------ Bing chains */

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

#define MAXLEV 40
#define MAXN   20000

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

static int DOWINDOWS = 1;
static time_t T0;

static int rho[MAXN], sig[MAXN], armG[MAXN], armT[MAXN];
static long nPairs = 0, nBase = 0, nFailBoth = 0, nUpOnly = 0, nDownOnly = 0, nBoth = 0;
static long nChecked = 0, nCheckBad = 0, maxTurns = 0, shownFail = 0;
static long dbgShown = 0, topBy1k2 = 0;
static long turnHist[64], kindHist[16], topBy1 = 0, botBy1 = 0;

/* phase from time tau of arm f (length m), previous turn prev, direction up.
   returns extreme before first far-side violation, or sets *done if never violates far side AND
   ... (done is decided separately) */
static int phaseExt(const int *f, int m, int tau, int prev, int up, int *never) {
  int ext = f[tau];
  for (int j = tau; j < m; j++) {
    int x = f[j];
    if (up && x < prev - 1) { *never = 0; return ext; }
    if (!up && x > prev + 1) { *never = 0; return ext; }
    if (up ? x > ext : x < ext) ext = x;
  }
  *never = 1; return ext;
}
/* returns transfer time, -1 if done (never leaves envelope), -2 if violation */
static int phaseStep(const int *f, int m, int tau, int prev, int tgt) {
  int up = tgt > prev;
  int lo = up ? prev - 1 : tgt - 1, hi = up ? tgt + 1 : prev + 1;
  int inside = 1;
  for (int j = tau; j < m; j++) if (f[j] < lo || f[j] > hi) { inside = 0; break; }
  if (inside) return -1;
  for (int j = tau; j < m; j++) {
    int x = f[j];
    if (up) { if (x < prev - 1) return -2; if (x >= tgt - 1) return j; }
    else { if (x > prev + 1) return -2; if (x <= tgt + 1) return j; }
  }
  return -1;
}

static int turns[64];
static int greedy(const int *G, int mG, const int *T, int mT, int L, int H, int firstUp, int shift, int *nt) {
  int p = G[0];
  int k = 0; turns[k++] = p + (shift ? (firstUp ? -1 : 1) : 0);
  int tG = 0, tT = 0; /* -1 = done */
  int up = firstUp;
  int top = turns[0], bot = turns[0];
  while (!(tG == -1 && tT == -1)) {
    if (k >= 60) return 0;
    int last = turns[k - 1];
    int have = 0, best = 0;
    if (tG != -1) { int nv; int e = phaseExt(G, mG, tG, last, up, &nv); if (!nv) { best = e; have = 1; } }
    if (tT != -1) { int nv; int e = phaseExt(T, mT, tT, last, up, &nv);
      if (!nv) { if (!have) best = e; else best = up ? (e < best ? e : best) : (e > best ? e : best); have = 1; } }
    int tgt;
    if (up) {
      tgt = have ? best + 1 : H + 1; if (tgt > H + 1) tgt = H + 1;
      if ((k == 1 && tgt < p + 2) || (k > 1 && (tgt < last + 3 || tgt <= top))) { *nt = k; turns[k] = tgt; return 0; }
    } else {
      tgt = have ? best - 1 : L - 1; if (tgt < L - 1) tgt = L - 1;
      if ((k == 1 && tgt > p - 2) || (k > 1 && (tgt > last - 3 || tgt >= bot))) { *nt = k; turns[k] = tgt; return 0; }
    }
    if (tG != -1) { tG = phaseStep(G, mG, tG, last, tgt); if (tG == -2) { printf("internal G\n"); exit(1);} }
    if (tT != -1) { tT = phaseStep(T, mT, tT, last, tgt); if (tT == -2) { printf("internal T\n"); exit(1);} }
    if (shift && k > 1 && up && tgt == top + 1) { topBy1++; if (k == 2) topBy1k2++;
      if (dbgShown < 3) { dbgShown++;
        printf("  TOPBY1 i=%d turns:", mT - 1); for (int q = 0; q < k; q++) printf(" %d", turns[q]); printf(" -> %d\n", tgt);
        printf("    G:"); for (int q = 0; q < mG; q++) printf(" %d", G[q]); printf("\n    T:"); for (int q = 0; q < mT; q++) printf(" %d", T[q]);
        printf("\n    sigG:"); for (int q = 0; q < mG; q++) printf(" %d", sig[mT - 1 + q]); printf("\n    sigT:"); for (int q = 0; q < mT; q++) printf(" %d", sig[mT - 1 - q]); printf("\n"); } }
    if (shift && k > 1 && !up && tgt == bot - 1) botBy1++;
    turns[k++] = tgt;
    if (tgt > top) top = tgt;
    if (tgt < bot) bot = tgt;
    up = !up;
  }
  *nt = k; return 1;
}

static int cwalk[4096];
static int buildJump(int k) {
  int n = 0; cwalk[n++] = turns[0];
  for (int q = 0; q + 1 < k; q++) {
    int a = turns[q], b = turns[q + 1], d = b > a ? 1 : -1;
    int ad = b > a ? b - a : a - b;
    if (ad < 3) cwalk[n++] = b;
    else for (int x = a + 3 * d; x != b + d; x += d) cwalk[n++] = x;
  }
  return n;
}
static unsigned char R1[4096], R2[4096];
static int foldsExact(const int *f, int m, int len) {
  if (abs(f[0] - cwalk[0]) > 1) return 0;
  memset(R1, 0, len); R1[0] = 1;
  for (int j = 1; j < m; j++) {
    int any = 0;
    for (int u = 0; u < len; u++) {
      int ok = R1[u] || (u > 0 && R1[u-1]) || (u + 1 < len && R1[u+1]);
      R2[u] = ok && abs(f[j] - cwalk[u]) <= 1;
      any |= R2[u];
    }
    if (!any) return 0;
    memcpy(R1, R2, len);
  }
  return 1;
}

static void scanPair(int n, const char *tag) {
  nPairs++;
  int L = rho[0], H = rho[0];
  for (int t = 0; t < n; t++) { if (rho[t] < L) L = rho[t]; if (rho[t] > H) H = rho[t]; }
  for (int i = 0; i < n; i++) {
    int mG = n - i, mT = i + 1;
    for (int j = 0; j < mG; j++) armG[j] = rho[i + j];
    for (int j = 0; j < mT; j++) armT[j] = rho[i - j];
    nBase++;
    int ok = 0, k = 0, saveF[64], kF = 0, kinds = 0;
    for (int v = 0; v < 4; v++) {
      int nt;
      int r = greedy(armG, mG, armT, mT, L, H, v & 1, v >> 1, &nt);
      if (r) { kinds |= 1 << v; if (!ok) { ok = 1; k = nt; memcpy(saveF, turns, sizeof(saveF)); } }
      else if (v == 0) { kF = nt; }
    }
    kindHist[kinds]++;
    if (!ok) {
      nFailBoth++;
      if (shownFail < 20) {
        shownFail++;
        printf("  GREEDY FAILS ALL FOUR STARTS: %s n=%d i=%d level L+%d\n", tag, n, i, rho[i] - L);
        printf("    rho:"); for (int t = 0; t < n; t++) printf(" %d", rho[t]);
        printf("\n    sig:"); for (int t = 0; t < n; t++) printf(" %d", sig[t]);
        printf("\n");
      }
      continue;
    }
    memcpy(turns, saveF, sizeof(saveF));
    if (k - 1 > maxTurns) maxTurns = k - 1;
    turnHist[k - 1]++;
    if (i % 13 == 0) {
      int len = buildJump(k);
      nChecked++;
      if (!(foldsExact(armG, mG, len) && foldsExact(armT, mT, len))) {
        nCheckBad++;
        printf("  EXACT CHECK FAILS %s i=%d\n", tag, i);
      }
    }
  }
}
/* ------------------------------------------------- the corpus of pairs ---- */

static long shaveCap = 12, fillCap = 12;
static long MAXPAIRLEN = 3000;

static void runBase(const int *v, int n, const char *tag, long mixes) {
  if (n < 30 || n >= MAXN || n > MAXPAIRLEN) return;
  {
    int lo = v[0], hi = v[0];
    for (int u = 0; u < n; u++) { if (v[u] < lo) lo = v[u]; if (v[u] > hi) hi = v[u]; }
    if (lo != 0 || hi != SPAN) return;
  }
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  
  if (crookedGen(rho, sig, n)) {  scanPair(n, tag); }
  else return;

  long done = 0;
  for (int pk = 1; pk + 1 < n && done < shaveCap; pk++) {
    if (!(v[pk] > v[pk-1] && v[pk] > v[pk+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    rho[pk] = v[pk] - 1;
    
    if (!crookedGen(rho, sig, n)) continue;
     done++;
    scanPair(n, tag);
  }
  done = 0;
  for (int vl = 1; vl + 1 < n && done < fillCap; vl++) {
    if (!(v[vl] < v[vl-1] && v[vl] < v[vl+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    sig[vl] = v[vl] + 1;
    
    if (!crookedGen(rho, sig, n)) continue;
     done++;
    scanPair(n, tag);
  }
  for (long it = 0; it < mixes; it++) {
    int rate = (it % 2) ? 2 : 3;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) { if (random() % rate == 0) rho[j] = v[j] - 1; }
      else if (v[j] < v[j-1] && v[j] < v[j+1]) { if (random() % rate == 0) sig[j] = v[j] + 1; }
    }
    
    if (!crookedGen(rho, sig, n)) continue;
    
    scanPair(n, tag);
  }
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  for (int j = 1; j + 1 < n; j++) {
    if (v[j] > v[j-1] && v[j] > v[j+1]) rho[j] = v[j] - 1;
    else if (v[j] < v[j-1] && v[j] < v[j+1]) sig[j] = v[j] + 1;
  }
  
  if (crookedGen(rho, sig, n)) {  scanPair(n, tag); }

}

static int windowSpanS(const int *v, int n, int a, int b, int *out) {
  if (a < 0 || b >= n || b - a + 1 < 30) return 0;
  if (b - a + 1 > MAXPAIRLEN) b = a + (int)MAXPAIRLEN - 1;
  if (b - a + 1 >= MAXN) return 0;
  int lo = v[a], hi = v[a];
  for (int t = a; t <= b; t++) { if (v[t] < lo) lo = v[t]; if (v[t] > hi) hi = v[t]; }
  if (hi - lo != SPAN) return 0;
  for (int t = a; t <= b; t++) out[t - a] = v[t] - lo;
  return b - a + 1;
}

static int wbuf[MAXN];

int main(int argc, char **argv) {
  SPAN = (argc > 1) ? atoi(argv[1]) : 10;
  long windows = (argc > 2) ? atol(argv[2]) : 24;
  long mixes = (argc > 3) ? atol(argv[3]) : 4;
  unsigned seed = (argc > 4) ? (unsigned)atoi(argv[4]) : 75u;
  MAXPAIRLEN = (argc > 6) ? atol(argv[6]) : 3000;
  if (argc > 8) { shaveCap = atol(argv[8]); fillCap = shaveCap; }
  srandom(seed);
  setvbuf(stdout, NULL, _IOLBF, 0);
  T0 = time(NULL);


  printf("greedy77 at span %d, seed %u\n", SPAN, seed);
  printf("\n---- the corpus, chain by chain ----\n");

  {
    Path p = bpath(0, SPAN);
    printf("  bing 0 %d: %d links\n", SPAN, p.n);
    runBase(p.v, p.n, "bing", mixes);
    free(p.v);
    Path q = bpath(SPAN, 0);
    printf("  bing %d 0: %d links\n", SPAN, q.n);
    runBase(q.v, q.n, "bing-rev", mixes);
    free(q.v);
  }

  for (int N = SPAN + 1; N <= SPAN + 4 && DOWINDOWS; N++) {
    Path p = bpath(0, N);
    printf("  bing 0 %d: %d links\n", N, p.n);
    long gridMade = 0, randMade = 0;
    char name[64];
    int stride = 149;
    for (int a = 0; a + 120 < p.n && gridMade < windows; a += stride) {
      int lo = p.v[a], hi = p.v[a], b = -1;
      for (int t = a; t < p.n; t++) {
        if (p.v[t] < lo) lo = p.v[t];
        if (p.v[t] > hi) hi = p.v[t];
        if (hi - lo == SPAN) { b = t; break; }
        if (hi - lo > SPAN) break;
      }
      if (b < 0) continue;
      int e = b;
      while (e + 1 < p.n && p.v[e+1] >= lo && p.v[e+1] <= hi) e++;
      int m = windowSpanS(p.v, p.n, a, e, wbuf);
      if (!m) continue;
      snprintf(name, sizeof(name), "bing0%d-grid", N);
      gridMade++;
      runBase(wbuf, m, name, mixes);
    }
    for (long it = 0; it < windows * 3 && randMade < windows; it++) {
      int a = (int)(random() % (unsigned)(p.n - 60));
      int lo = p.v[a], hi = p.v[a], b = -1;
      for (int t = a; t < p.n; t++) {
        if (p.v[t] < lo) lo = p.v[t];
        if (p.v[t] > hi) hi = p.v[t];
        if (hi - lo == SPAN) { b = t; break; }
        if (hi - lo > SPAN) break;
      }
      if (b < 0) continue;
      int e = b;
      while (e + 1 < p.n && p.v[e+1] >= lo && p.v[e+1] <= hi) e++;
      int m = windowSpanS(p.v, p.n, a, e, wbuf);
      if (!m) continue;
      snprintf(name, sizeof(name), "bing0%d-rand", N);
      randMade++;
      runBase(wbuf, m, name, mixes);
    }
    printf("  -> windows of span %d: %ld at grid offsets, %ld at random offsets\n",
           SPAN, gridMade, randMade);
    free(p.v);
  }

  {
    int bk[4] = {1, 2, 2, 1}, fw[4] = {2, 1, 2, 3};
    for (int q = 0; q < 4; q++) {
      Path r = vpath(0, SPAN, bk[q], fw[q]);
      char name[64];
      snprintf(name, sizeof(name), "vpath(%d,%d)", bk[q], fw[q]);
      printf("  vpath 0 %d (%d,%d): %d links\n", SPAN, bk[q], fw[q], r.n);
      runBase(r.v, r.n, name, mixes);
      free(r.v);
      Path s = vpath(SPAN, 0, bk[q], fw[q]);
      snprintf(name, sizeof(name), "vpath-rev(%d,%d)", bk[q], fw[q]);
      printf("  vpath %d 0 (%d,%d): %d links\n", SPAN, bk[q], fw[q], s.n);
      runBase(s.v, s.n, name, mixes);
      free(s.v);
    }
  }

  {
    static int v[MAXN * 2];
    long made = 0;
    for (long it = 0; it < windows * 2 && DOWINDOWS; it++) {
      int nb = 2 + (int)(random() % 3), n = 0, cur = (int)(random() % (SPAN + 1)), first = 1;
      for (int b = 0; b < nb; b++) {
        int nx; do { nx = (int)(random() % (SPAN + 1)); } while (nx == cur);
        Path blk = bpath(cur, nx);
        if (n + blk.n >= MAXN * 2 - 4) { free(blk.v); break; }
        if (first) { memcpy(v, blk.v, sizeof(int) * blk.n); n = blk.n; first = 0; }
        else { memcpy(v + n, blk.v + 1, sizeof(int) * (blk.n - 1)); n += blk.n - 1; }
        cur = nx; free(blk.v);
      }
      if (n < 200) continue;
      if (n < MAXN) {
        int lo = v[0], hi = v[0];
        for (int u = 0; u < n; u++) { if (v[u] < lo) lo = v[u]; if (v[u] > hi) hi = v[u]; }
        if (hi - lo == SPAN) {
          static int sh[MAXN];
          for (int u = 0; u < n; u++) sh[u] = v[u] - lo;
          made++;
          runBase(sh, n, "concat", mixes);
          continue;
        }
      }
      int a = (int)(random() % (unsigned)(n - 40));
      int lo = v[a], hi = v[a], b = -1;
      for (int t = a; t < n; t++) {
        if (v[t] < lo) lo = v[t];
        if (v[t] > hi) hi = v[t];
        if (hi - lo == SPAN) { b = t; break; }
        if (hi - lo > SPAN) break;
      }
      if (b < 0) continue;
      int e = b;
      while (e + 1 < n && v[e+1] >= lo && v[e+1] <= hi) e++;
      int m = windowSpanS(v, n, a, e, wbuf);
      if (!m) continue;
      made++;
      runBase(wbuf, m, "concat-window", mixes);
    }
    printf("  random concatenations of Bing blocks: %ld used\n", made);
  }


  printf("\n==== greedy77, span %d ====\n", SPAN);
  printf("  pairs scanned %ld, basepoints %ld\n", nPairs, nBase);
  printf("  greedy FAILS at all four starts: %ld\n", nFailBoth);
  printf("  by the set of starts that succeed (bit0 up-from-p, bit1 down-from-p, bit2 up-from-p-1, bit3 down-from-p+1):\n   ");
  for (int q = 0; q < 16; q++) if (kindHist[q]) printf(" %d:%ld", q, kindHist[q]); printf("\n");
  printf("  expansions by exactly one (shifted starts): tops %ld (of which in the second phase %ld), bottoms %ld\n", topBy1, topBy1k2, botBy1);
  printf("  exact re-checks %ld, failures %ld;  max turns %ld\n", nChecked, nCheckBad, maxTurns);
  printf("  turns histogram:"); for (int q = 0; q <= maxTurns; q++) printf(" %d:%ld", q, turnHist[q]); printf("\n");
  return 0;
}
