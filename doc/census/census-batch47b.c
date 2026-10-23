/* Census for batch 47 (b) -- does a fold of the thin sequence transfer to the
 * shaved one, and is the unserved branch covered by one small family of walks?
 *
 * WHAT THIS RANGES OVER.  Pairs of the GENERAL model.  Generator: shavings of
 * `bing 0 9` -- the thin faithful sequence `bing 0 9` with one strict local
 * maximum lowered by one (single shavings, all 288 peaks), and, in the second
 * part, random subsets of peaks shaved at once.  Every pair is verified against
 * the definition `IsCrookedIvF` of HPC/Fold/Faithful.lean before it is used;
 * generation is never trusted.  The fraction of non-thin links is reported.
 * Folding is decided exactly, by the dynamic program over `FoldsOnto`.
 *
 * QUESTION 1 (commission 47, 2.1, second half).  At each branch basepoint
 * (rho i = L+4, both arms HighAt (L+1) (L+8)) of a shaved pair, compare the
 * walks of at most three legs that serve the *thin* sequence `bing 0 9` at the
 * same basepoint with those that serve the shaved pair.  Does a fold of the
 * thin sequence transfer?
 *
 * QUESTION 2 (commission 47, 2.3).  Among the unserved branch pairs -- those
 * folding onto neither canonical walk -- how many are served by the three-leg
 * walk `L+3 -> L+a -> L+1 -> L+8` for a = 5, 6, 7, i.e. by the engine of
 * HPC/Fold/Leg3Deep.lean with its middle peak at one of three heights?
 *
 * Usage: census-batch47b [rand-rounds] [seed]
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

#define MAXLEV 32
#define MAXN   2048
#define MAXW   96

static int meetTab[MAXLEV][MAXN + 1];

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
static int thin[MAXN];

/* HighAt f L (L+8): before every ascent to L+8 there is a time at L+1 or below */
static int highAt(const int *f, int m) {
  int seenLow = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !seenLow) return 0;
    if (f[d] <= 1) seenLow = 1;
  }
  return 1;
}

static int servedBy(const int *g, int mg, const int *t, int mt,
                    int start, int a, int b, int c) {
  int w[MAXW];
  int wl = buildWalk(w, start, a, b, c);
  if (wl < 0) return 0;
  return folds(g, mg, w, wl) && folds(t, mt, w, wl);
}

/* THE PROFILE CRITERION for the third walk (census-batch47c.c): the engine's two
 * announcements with the peak demand lowered from L+6 to L+5 and the index
 * clauses the walk forces.  Exhaustively sufficient for the fold over every
 * 1-Lipschitz arm of length at most sixteen. */
static int profileCrit(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j < d && !ok; j++) if (a[j] >= 5 && j + 5 <= d) ok = 1;
    if (!ok) return 0;
  }
  for (int d = 0; d < m; d++) {
    if (a[d] < 8) continue;
    int ok = 0;
    for (int j = 3; j < d && !ok; j++) {
      if (a[j] < 5) continue;
      for (int k = j + 5; k < d && !ok; k++) if (a[k] <= 2 && k + 6 <= d) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

/* the two canonical walks, as in HPC/Fold/Profile.lean: Lambda based at L+3
 * (up to L+8, down to L+1) and V based at L+5 (down to L+1, up to L+8) */
static int servedCanonical(const int *g, int mg, const int *t, int mt) {
  if (servedBy(g, mg, t, mt, 3, 8, 1, -1)) return 1;
  if (servedBy(g, mg, t, mt, 5, 1, 8, -1)) return 2;
  return 0;
}

int main(int argc, char **argv) {
  long rounds = (argc > 1) ? atol(argv[1]) : 40;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 11u;
  srandom(seed);

  Path p = bpath(0, 9);
  int n = p.n, *v = p.v;
  printf("census-batch47b: the GENERAL model; generator: shavings of bing 0 9 (n = %d).\n", n);
  for (int u = 0; u < n; u++) thin[u] = v[u];
  printf("  the thin sequence bing 0 9 verifies IsCrookedIvF: %d\n", crookedGen(thin, thin, n));

  /* ---- part 1: single shavings, all peaks ---------------------------- */
  long nPairs = 0, nBase = 0, nUnserved = 0;
  long nThinServed = 0, nTransfer = 0, nA[10];
  long nCoveredByFamily = 0, nCoveredAny3 = 0;
  long nThinWalk[4] = {0,0,0,0}, nLostWalk[4] = {0,0,0,0}, nGainWalk[4] = {0,0,0,0};
  long nProfile = 0, nProfileFail = 0;
  for (int a = 0; a < 10; a++) nA[a] = 0;
  long nLinks = 0, nNonThin = 0;

  for (int pk = 1; pk + 1 < n; pk++) {
    if (!(v[pk] > v[pk-1] && v[pk] > v[pk+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    rho[pk] = v[pk] - 1;
    if (!crookedGen(rho, sig, n)) { printf("  peak %d: NOT faithful\n", pk); continue; }
    nPairs++;
    nLinks += n; nNonThin += 1;
    for (int i = 0; i < n; i++) {
      if (rho[i] != 4) continue;
      int mg = n - i, mt = i + 1;
      for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
      for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
      if (!highAt(armG, mg) || !highAt(armT, mt)) continue;
      nBase++;
      {
        /* fold transfer: the same walk on the thin sequence and on the pair */
        static int tg0[MAXN], tt0[MAXN];
        for (int d = 0; d < mg; d++) tg0[d] = thin[i + d];
        for (int d = 0; d < mt; d++) tt0[d] = thin[i - d];
        int wk[4][4] = {{3,8,1,-1},{5,1,8,-1},{3,6,1,8},{3,7,1,8}};
        for (int q = 0; q < 4; q++) {
          int st = wk[q][0], a = wk[q][1], b = wk[q][2], c = wk[q][3];
          int thinS = servedBy(tg0, mg, tt0, mt, st, a, b, c);
          int shavS = servedBy(armG, mg, armT, mt, st, a, b, c);
          if (thinS) { nThinWalk[q]++; if (!shavS) nLostWalk[q]++; }
          if (shavS && !thinS) nGainWalk[q]++;
        }
      }
      if (servedCanonical(armG, mg, armT, mt)) continue;
      nUnserved++;
      /* the same basepoint on the thin sequence */
      static int tg[MAXN], tt[MAXN];
      for (int d = 0; d < mg; d++) tg[d] = thin[i + d];
      for (int d = 0; d < mt; d++) tt[d] = thin[i - d];
      int thinWalk = servedCanonical(tg, mg, tt, mt);
      if (thinWalk) {
        nThinServed++;
        /* does that same canonical walk serve the shaved pair?  (it cannot,
         * the pair is unserved -- recorded for completeness) */
        int same = (thinWalk == 1) ? servedBy(armG, mg, armT, mt, 3, 8, 1, -1)
                                   : servedBy(armG, mg, armT, mt, 5, 1, 8, -1);
        if (same) nTransfer++;
      }
      if (profileCrit(armG, mg) && profileCrit(armT, mt)) nProfile++;
      else nProfileFail++;
      /* the three-leg family `L+3 -> L+a -> L+1 -> L+8` */
      int covered = 0;
      for (int a = 5; a <= 7; a++)
        if (servedBy(armG, mg, armT, mt, 3, a, 1, 8)) { nA[a]++; covered = 1; }
      if (covered) nCoveredByFamily++;
      else {
        /* any walk of at most three legs? */
        int found = 0;
        for (int start = 3; start <= 5 && !found; start++)
          for (int a = 0; a <= 9 && !found; a++)
            for (int b = -1; b <= 9 && !found; b++)
              for (int c = -1; c <= 9 && !found; c++) {
                if (b < 0 && c >= 0) continue;
                if (servedBy(armG, mg, armT, mt, start, a, b, c)) found = 1;
              }
        if (found) nCoveredAny3++;
        else printf("  UNSERVED BY ANY THREE-LEG WALK: peak %d, basepoint %d\n", pk, i);
      }
    }
  }
  printf("\n-- single shavings --\n");
  printf("faithful shaved pairs: %ld (each with 1 non-thin link of %d)\n", nPairs, n);
  printf("branch basepoints: %ld; folding onto neither canonical walk: %ld\n", nBase, nUnserved);
  printf("of those, the thin sequence IS served at the same basepoint by a canonical walk: %ld"
         " (and that walk serves the shaved pair: %ld)\n", nThinServed, nTransfer);
  printf("covered by L+3 -> L+a -> L+1 -> L+8: %ld", nCoveredByFamily);
  for (int a = 5; a <= 7; a++) printf("   [a=%d: %ld]", a, nA[a]);
  printf("\nnot covered by that family but by some three-leg walk: %ld\n", nCoveredAny3);
  printf("unserved pairs whose two arms both meet the profile criterion of census-batch47c.c: "
         "%ld (failing: %ld)\n", nProfile, nProfileFail);
  {
    const char *nm[4] = {"L+3 -> L+8 -> L+1 (Lambda)", "L+5 -> L+1 -> L+8 (V)",
                         "L+3 -> L+6 -> L+1 -> L+8", "L+3 -> L+7 -> L+1 -> L+8"};
    printf("fold transfer, over all %ld branch basepoints:\n", nBase);
    for (int q = 0; q < 4; q++)
      printf("  %-28s thin serves %6ld, of which lost after shaving %6ld; gained %6ld\n",
             nm[q], nThinWalk[q], nLostWalk[q], nGainWalk[q]);
  }

  /* ---- part 2: random multi-shavings --------------------------------- */
  long rPairs = 0, rBase = 0, rUnserved = 0, rFamily = 0, rAny = 0, rNone = 0;
  long rLinks = 0, rNonThin = 0, rThinServed = 0, rTransfer = 0;
  for (long it = 0; it < rounds; it++) {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    int shaved = 0;
    for (int pk = 1; pk + 1 < n; pk++) {
      if (!(v[pk] > v[pk-1] && v[pk] > v[pk+1])) continue;
      if (random() % 3 == 0) { rho[pk] = v[pk] - 1; shaved++; }
    }
    if (!crookedGen(rho, sig, n)) { printf("  round %ld: NOT faithful\n", it); continue; }
    rPairs++; rLinks += n; rNonThin += shaved;
    for (int i = 0; i < n; i++) {
      if (rho[i] != 4) continue;
      int mg = n - i, mt = i + 1;
      for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
      for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
      if (!highAt(armG, mg) || !highAt(armT, mt)) continue;
      rBase++;
      if (servedCanonical(armG, mg, armT, mt)) continue;
      rUnserved++;
      static int tg[MAXN], tt[MAXN];
      for (int d = 0; d < mg; d++) tg[d] = thin[i + d];
      for (int d = 0; d < mt; d++) tt[d] = thin[i - d];
      int thinWalk = servedCanonical(tg, mg, tt, mt);
      if (thinWalk) {
        rThinServed++;
        int same = (thinWalk == 1) ? servedBy(armG, mg, armT, mt, 3, 8, 1, -1)
                                   : servedBy(armG, mg, armT, mt, 5, 1, 8, -1);
        if (same) rTransfer++;
      }
      int covered = 0;
      for (int a = 5; a <= 7; a++)
        if (servedBy(armG, mg, armT, mt, 3, a, 1, 8)) covered = 1;
      if (covered) { rFamily++; continue; }
      int found = 0;
      for (int start = 3; start <= 5 && !found; start++)
        for (int a = 0; a <= 9 && !found; a++)
          for (int b = -1; b <= 9 && !found; b++)
            for (int c = -1; c <= 9 && !found; c++) {
              if (b < 0 && c >= 0) continue;
              if (servedBy(armG, mg, armT, mt, start, a, b, c)) found = 1;
            }
      if (found) rAny++;
      else { rNone++; printf("  UNSERVED BY ANY THREE-LEG WALK (random round %ld, basepoint %d)\n",
                             it, i); }
    }
  }
  printf("\n-- random multi-shavings (%ld rounds, seed %u) --\n", rounds, seed);
  printf("faithful pairs: %ld; non-thin links %ld/%ld (%.4f)\n", rPairs, rNonThin, rLinks,
         rLinks ? (double)rNonThin / (double)rLinks : 0.0);
  printf("branch basepoints: %ld; unserved by a canonical walk: %ld\n", rBase, rUnserved);
  printf("of those, thin served at the same basepoint: %ld (same walk serves the pair: %ld)\n",
         rThinServed, rTransfer);
  printf("covered by L+3 -> L+a -> L+1 -> L+8 (a in 5..7): %ld; by some other three-leg walk: %ld;"
         " by none: %ld\n", rFamily, rAny, rNone);
  free(p.v);
  return 0;
}
