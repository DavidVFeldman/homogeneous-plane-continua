/* census-batch49c.c -- batch 49.  Which walk serves the unserved pairs?
 *
 * `not_unservedLeg3deep` (HPC/Fold/CrossWitness.lean) shows that the third walk
 * `L+3 -> L+6 -> L+1 -> L+8` does not serve every unserved pair of the branch
 * `L + 4`: at the basepoint 336 of the shaved chain bing9sB the forward arm
 * fails `Leg3Ceil`, which by `leg3Ceil_of_foldsOnto_leg3` it could not do if it
 * folded onto that walk.  This census asks what does serve those pairs, over
 * the corpus of census-batch49b.c (the same generators, the same reading of the
 * branch hypothesis), and in particular whether the FOURTH walk
 *
 *      L+3 -> L+2 -> L+8 -> L+1      (`leg3Walk''' L (L+9) (L+7) (L+2)`)
 *
 * -- the reflection of the third one -- takes up the slack.  Every fold is
 * decided exactly by the dynamic program over `FoldsOnto`.
 *
 * Usage: census-batch49c [rand-rounds] [seed]
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

/* A randomised Bing recursion: to link a to b with |a-b| >= 3 the chain runs
 * a -> mid -> c -> b with mid within two of b and c within two of a.  bpath is
 * the choice mid = b-1, c = a+1; the others give different chains of the same
 * span, and every one produced is verified against IsCrookedIvF before use. */
static Path rpath(int a, int b) {
  Path p;
  int d = a < b ? b - a : a - b;
  if (d <= 2) {
    p.n = d + 1;
    p.v = (int *)malloc(sizeof(int) * p.n);
    int s = (a <= b) ? 1 : -1;
    for (int u = 0; u < p.n; u++) p.v[u] = a + s * u;
    return p;
  }
  int up = (a < b) ? 1 : -1;
  int dm = (random() % 2) + 1;            /* mid = b - 1 or b - 2 (signed) */
  int dc = (random() % 2) + 1;            /* c   = a + 1 or a + 2 (signed) */
  int mid = b - up * dm;
  int c = a + up * dc;
  if ((up > 0 && (mid <= c)) || (up < 0 && (mid >= c))) { mid = b - up; c = a + up; }
  Path p1 = rpath(a, mid), p2 = rpath(mid, c), p3 = rpath(c, b);
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

/* HighAt f (L+1) (L+8), as the definition reads it: before every ascent to
 * L+8 there is a time at L+2 or below.  (The batch-48 census asked L+1.) */
static int highAt(const int *f, int m) {
  int seenLow = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !seenLow) return 0;
    if (f[d] <= 2) seenLow = 1;
  }
  return 1;
}

/* the stronger reading used by the batch-48 census, kept so that the two
 * corpora can be compared */
static int highAtStrong(const int *f, int m) {
  int seenLow = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !seenLow) return 0;
    if (f[d] <= 1) seenLow = 1;
  }
  return 1;
}

/* Leg3Valley f L */
static int leg3Valley(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j + 5 <= d && !ok; j++) if (a[j] >= 5) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* Leg3Ceil f L */
static int leg3Ceil(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 8) continue;
    int ok = 0;
    for (int j = 3; j + 11 <= d && !ok; j++) {
      if (a[j] < 5) continue;
      for (int k = j + 5; k + 6 <= d && !ok; k++) if (a[k] <= 2) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

/* the clauses in the form the proof of batch 48 consumes (Leg3ValleyMin, Leg3CeilMin) */
static int leg3ValleyMin(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j < d && !ok; j++) if (a[j] >= 5) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

static int leg3CeilMin(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 8) continue;
    int ok = 0;
    for (int j = 3; j + 5 < d && !ok; j++) {
      if (a[j] < 5) continue;
      for (int k = j + 5; k < d && !ok; k++) if (a[k] <= 2) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

static int foldsLam(const int *f, int m) {   /* Lambda based at L+3: 3 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 3, 8, 1, -1);
  return folds(f, m, w, wl);
}
static int foldsVee(const int *f, int m) {   /* V based at L+5: 5 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 5, 1, 8, -1);
  return folds(f, m, w, wl);
}
static int foldsLeg3(const int *f, int m) {  /* the third walk: 3 -> 6 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 3, 6, 1, 8);
  return folds(f, m, w, wl);
}
static int foldsLeg3R(const int *f, int m) { /* the fourth walk: 3 -> 2 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 3, 2, 8, 1);
  return folds(f, m, w, wl);
}
static int foldsLeg3P(const int *f, int m) { /* the deep walk: 3 -> 7 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 3, 7, 1, 8);
  return folds(f, m, w, wl);
}

/* For a pair that neither the third nor the fourth walk serves: the shortest
 * zigzag walk with at most three turns that does serve it, searched by brute
 * force over the start and the turning levels. */
static void findWalk(const int *g, int mg, const int *t, int mt) {
  int best = 1 << 30, bs = -1, ba = -1, bb = -1, bc = -1;
  for (int st = 2; st <= 6; st++)
    for (int a = 0; a <= 9; a++) {
      if (a == st) continue;
      for (int b = -1; b <= 9; b++) {
        if (b == a) continue;
        for (int c = -1; c <= 9; c++) {
          if (c == b) continue;
          if (b < 0 && c >= 0) continue;
          int w[MAXW]; int wl = buildWalk(w, st, a, b, c);
          if (wl < 0 || wl >= best) continue;
          if (folds(g, mg, w, wl) && folds(t, mt, w, wl)) {
            best = wl; bs = st; ba = a; bb = b; bc = c;
          }
        }
      }
    }
  if (bs < 0) printf("      no walk of at most three turns serves this pair\n");
  else printf("      shortest serving walk (%d times): %d -> %d -> %d -> %d\n",
              best, bs, ba, bb, bc);
}

/* counters, shared by the three generators */
typedef struct {
  long pairs, links, nonthin, base, baseStrong, unserved;
  long valleyFailG, valleyFailT, ceilFailG, ceilFailT;
  long armVeeOK, armLamOK;          /* leg3Valley_or_vee / leg3Ceil_or_lam checks */
  long armVeeBad, armLamBad;
  long crossValleyTested, crossValleyBad;
  long crossCeilTested, crossCeilBad;
  long unservedProfileOK, unservedProfileBad;
  long unservedOneBad;
  long minValleyFail, minCeilFail, unservedMinOK, unservedMinBad;
  long unservedLeg3, unservedLeg3R, unservedLeg3P, unservedEither, unservedNeither;
  long unservedNotP;
  long ceilFailServedR, ceilFailNotServedR;
} Cnt;

static void zero(Cnt *c) { memset(c, 0, sizeof(*c)); }

static void scan(Cnt *c, int n, const char *tag, int gen) {
  c->pairs++; c->links += n;
  for (int u = 0; u < n; u++) if (sig[u] != rho[u]) c->nonthin++;
  for (int i = 0; i < n; i++) {
    if (rho[i] != 4) continue;
    int mg = n - i, mt = i + 1;
    for (int d = 0; d < mg; d++) armG[d] = rho[i + d];
    for (int d = 0; d < mt; d++) armT[d] = rho[i - d];
    if (!highAt(armG, mg) || !highAt(armT, mt)) continue;
    c->base++;
    if (highAtStrong(armG, mg) && highAtStrong(armT, mt)) c->baseStrong++;
    int vG = leg3Valley(armG, mg), vT = leg3Valley(armT, mt);
    int cG = leg3Ceil(armG, mg), cT = leg3Ceil(armT, mt);
    int fvG = foldsVee(armG, mg), fvT = foldsVee(armT, mt);
    int flG = foldsLam(armG, mg), flT = foldsLam(armT, mt);
    if (!leg3ValleyMin(armG, mg)) c->minValleyFail++;
    if (!leg3ValleyMin(armT, mt)) c->minValleyFail++;
    if (!leg3CeilMin(armG, mg)) c->minCeilFail++;
    if (!leg3CeilMin(armT, mt)) c->minCeilFail++;
    if (!vG) c->valleyFailG++;
    if (!vT) c->valleyFailT++;
    if (!cG) { c->ceilFailG++;
      printf("  [%s %d] arm fails Leg3Ceil: basepoint %d, forward arm "
             "(Lambda-fold G=%d T=%d)\n", tag, gen, i, flG, flT); }
    if (!cT) { c->ceilFailT++;
      printf("  [%s %d] arm fails Leg3Ceil: basepoint %d, backward arm "
             "(Lambda-fold G=%d T=%d)\n", tag, gen, i, flG, flT); }
    /* 2. the two lemmas proved in batch 48 */
    if (!vG) { if (fvG) c->armVeeOK++; else { c->armVeeBad++;
      printf("  [%s %d] LEMMA leg3Valley_or_vee FAILS: basepoint %d, forward arm\n", tag, gen, i); } }
    if (!vT) { if (fvT) c->armVeeOK++; else { c->armVeeBad++;
      printf("  [%s %d] LEMMA leg3Valley_or_vee FAILS: basepoint %d, backward arm\n", tag, gen, i); } }
    if (!cG) { if (flG) c->armLamOK++; else { c->armLamBad++;
      printf("  [%s %d] LEMMA leg3Ceil_or_lam FAILS: basepoint %d, forward arm\n", tag, gen, i); } }
    if (!cT) { if (flT) c->armLamOK++; else { c->armLamBad++;
      printf("  [%s %d] LEMMA leg3Ceil_or_lam FAILS: basepoint %d, backward arm\n", tag, gen, i); } }
    /* 3. the two work items */
    if (!vG || !vT) {
      c->crossValleyTested++;
      if (!(fvG && fvT)) { c->crossValleyBad++;
        printf("  [%s %d] WORK ITEM cross_valley_profile FAILS: basepoint %d "
               "(valley G=%d T=%d, V-fold G=%d T=%d)\n", tag, gen, i, vG, vT, fvG, fvT); }
    }
    if (!cG || !cT) {
      c->crossCeilTested++;
      if (!(flG && flT)) { c->crossCeilBad++;
        printf("  [%s %d] WORK ITEM cross_ceil_profile FAILS: basepoint %d "
               "(ceil G=%d T=%d, Lambda-fold G=%d T=%d)\n", tag, gen, i, cG, cT, flG, flT); }
    }
    /* 4. the unserved basepoints */
    if ((flG && flT) || (fvG && fvT)) continue;
    c->unserved++;
    if (vG && vT && cG && cT) c->unservedProfileOK++;
    else { c->unservedProfileBad++;
      printf("  [%s %d] unserved_profile FAILS: basepoint %d (valley G=%d T=%d, ceil G=%d T=%d)\n",
             tag, gen, i, vG, vT, cG, cT); }
    if (leg3ValleyMin(armG, mg) && leg3ValleyMin(armT, mt) &&
        leg3CeilMin(armG, mg) && leg3CeilMin(armT, mt)) c->unservedMinOK++;
    else c->unservedMinBad++;
    if (!((vG || vT) && (cG || cT))) { c->unservedOneBad++;
      printf("  [%s %d] unserved_profile_one FAILS: basepoint %d\n", tag, gen, i); }
    /* 5. which walk serves the unserved pair: the third or the fourth? */
    {
      int f3 = foldsLeg3(armG, mg) && foldsLeg3(armT, mt);
      int f4 = foldsLeg3R(armG, mg) && foldsLeg3R(armT, mt);
      int f5 = foldsLeg3P(armG, mg) && foldsLeg3P(armT, mt);
      if (f5) c->unservedLeg3P++;
      else { c->unservedNotP++;
        printf("  [%s %d] the deep walk 3->7->1->8 does NOT serve: basepoint %d "
               "(third %d, fourth %d)\n", tag, gen, i, f3, f4); }
      if (f3) c->unservedLeg3++;
      if (f4) c->unservedLeg3R++;
      if (f3 || f4) c->unservedEither++;
      else { c->unservedNeither++;
        printf("  [%s %d] NEITHER third nor fourth walk serves: basepoint %d\n", tag, gen, i);
        findWalk(armG, mg, armT, mt); }
      if (!cG || !cT) { if (f4) c->ceilFailServedR++; else c->ceilFailNotServedR++; }
    }
  }
}

static void report(const char *name, const Cnt *c) {
  printf("\n-- %s --\n", name);
  printf("faithful pairs: %ld; non-thin links %ld/%ld (%.5f)\n", c->pairs, c->nonthin, c->links,
         c->links ? (double)c->nonthin / (double)c->links : 0.0);
  printf("branch basepoints (rho i = L+4, both arms HighAt (L+1) (L+8)): %ld "
         "(of which %ld also meet the stronger reading of batch 48); unserved: %ld\n",
         c->base, c->baseStrong, c->unserved);
  printf("arms failing Leg3Valley: forward %ld, backward %ld; failing Leg3Ceil: forward %ld, "
         "backward %ld\n", c->valleyFailG, c->valleyFailT, c->ceilFailG, c->ceilFailT);
  printf("leg3Valley_or_vee confirmed %ld times (failures %ld); "
         "leg3Ceil_or_lam confirmed %ld times (failures %ld)\n",
         c->armVeeOK, c->armVeeBad, c->armLamOK, c->armLamBad);
  printf("cross_valley_profile: tested %ld, failures %ld;  "
         "cross_ceil_profile: tested %ld, failures %ld\n",
         c->crossValleyTested, c->crossValleyBad, c->crossCeilTested, c->crossCeilBad);
  printf("arms failing the sharpened clauses: Leg3ValleyMin %ld, Leg3CeilMin %ld\n",
         c->minValleyFail, c->minCeilFail);
  printf("unserved pairs meeting the sharpened clauses on both arms: %ld (failing %ld)\n",
         c->unservedMinOK, c->unservedMinBad);
  printf("unserved_profile: holds %ld, fails %ld;  unserved_profile_one failures: %ld\n",
         c->unservedProfileOK, c->unservedProfileBad, c->unservedOneBad);
  printf("unserved pairs served by the deep walk 3->7->1->8: %ld; NOT served by it: %ld\n",
         c->unservedLeg3P, c->unservedNotP);
  printf("unserved pairs served by the third walk 3->6->1->8: %ld; by the fourth walk "
         "3->2->8->1: %ld; by one of the two: %ld; BY NEITHER: %ld\n",
         c->unservedLeg3, c->unservedLeg3R, c->unservedEither, c->unservedNeither);
  printf("unserved pairs with an arm failing Leg3Ceil: served by the fourth walk %ld, "
         "not served by it %ld\n", c->ceilFailServedR, c->ceilFailNotServedR);
}

static Cnt cs, cf, cm, ct;

static void runChain(int n, const int *v, long rounds, const char *name) {
  printf("\n==== base chain %s (n = %d links); verifies IsCrookedIvF: ", name, n);
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; thin[u] = v[u]; }
  printf("%d ====\n", crookedGen(rho, sig, n));

  /* ---- generator 0: the thin sequence itself -------------------------- */
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  if (crookedGen(rho, sig, n)) scan(&ct, n, "thin", 0);

  /* ---- generator (a): single shavings, every peak --------------------- */
  for (int pk = 1; pk + 1 < n; pk++) {
    if (!(v[pk] > v[pk-1] && v[pk] > v[pk+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    rho[pk] = v[pk] - 1;
    if (!crookedGen(rho, sig, n)) { printf("  shave %d: NOT faithful\n", pk); continue; }
    scan(&cs, n, "shave", pk);
  }

  /* ---- generator (b): single fills, every valley ---------------------- */
  for (int vl = 1; vl + 1 < n; vl++) {
    if (!(v[vl] < v[vl-1] && v[vl] < v[vl+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    sig[vl] = v[vl] + 1;
    if (!crookedGen(rho, sig, n)) { printf("  fill %d: NOT faithful\n", vl); continue; }
    scan(&cf, n, "fill", vl);
  }

  /* ---- generator (c): random mixtures --------------------------------- */
  for (long it = 0; it < rounds; it++) {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) { if (random() % 3 == 0) rho[j] = v[j] - 1; }
      else if (v[j] < v[j-1] && v[j] < v[j+1]) { if (random() % 3 == 0) sig[j] = v[j] + 1; }
    }
    if (!crookedGen(rho, sig, n)) { printf("  round %ld: NOT faithful\n", it); continue; }
    scan(&cm, n, "mix", (int)it);
  }
}

int main(int argc, char **argv) {
  long rounds = (argc > 1) ? atol(argv[1]) : 40;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 49u;
  srandom(seed);
  printf("census-batch49c: which walk serves the unserved pairs of the branch L+4.\n");
  zero(&cs); zero(&cf); zero(&cm); zero(&ct);

  Path p = bpath(0, 9);
  runChain(p.n, p.v, rounds, "bing 0 9");
  Path q = bpath(9, 0);
  runChain(q.n, q.v, rounds, "bing 9 0 (the chain run the other way)");

  /* (d) other chains of span nine, from the randomised Bing recursion */
  long tried = 0, used = 0;
  for (long it = 0; it < 12; it++) {
    Path r = rpath(0, 9);
    tried++;
    if (r.n <= MAXN) {
      for (int u = 0; u < r.n; u++) { rho[u] = r.v[u]; sig[u] = r.v[u]; }
      if (crookedGen(rho, sig, r.n)) {
        used++;
        char nm[64]; snprintf(nm, sizeof nm, "random Bing recursion #%ld", it);
        runChain(r.n, r.v, rounds / 4 + 1, nm);
      } else printf("\n  [random chain %ld of %d links: not faithful, skipped]\n", it, r.n);
    } else printf("\n  [random chain %ld of %d links: too long, skipped]\n", it, r.n);
    free(r.v);
  }
  printf("\nrandomised base chains: %ld tried, %ld faithful and used\n", tried, used);

  printf("\n================ totals over both base chains ================\n");
  report("the thin sequences themselves", &ct);
  report("single shavings (one peak lowered)", &cs);
  report("single fills (one valley link widened upwards)", &cf);
  printf("   [random mixtures: %ld rounds per chain, seed %u]\n", rounds, seed);
  report("random mixtures of shavings and fills", &cm);
  free(p.v); free(q.v);
  return 0;
}
