/* census-batch50.c -- batch 50.  The three walks, the valley crossing, and a
 * wider corpus of general pairs.
 *
 * Tests, at every branch basepoint (rho i = L+4, both arms HighAt (L+1) (L+8)
 * read as the definition reads it: a time at L+2 or below before every time at
 * L+8 or above):
 *
 *   1. `cross_valley_profile`  (HPC/Fold/Mixed.lean, work item)
 *   2. `unserved_three_walks`  (HPC/Fold/Mixed.lean, work item): an unserved
 *      pair folds onto one of
 *          w3 = 3 -> 6 -> 1 -> 8,  w4 = 3 -> 2 -> 8 -> 1,  w5 = 3 -> 7 -> 1 -> 8
 *      -- both arms onto the same one.
 *   3. the necessity theorems of HPC/Fold/Landmark.lean and their batch-50
 *      extensions, as an audit of the Lean statements against the program:
 *          fold onto w3 ==> Leg3Ceil and Valley4
 *          fold onto w4 ==> Valley4 and CeilW4
 *          fold onto w5 ==> Valley5 (and Valley4)
 *      where Valley4 f : before every time at L+1 or below there is a time at
 *      L+5 or above, at a step >= 3 and at least 4 steps earlier -- the clause
 *      common to all three walks (`valley4_of_foldsOnto_three`).
 *   4. `arm_valley4_or_vee`: an arm failing Valley4 folds onto the V-walk.
 *   5. the two theorems of batch 48 (leg3Valley_or_vee, leg3Ceil_or_lam) and
 *      unserved_profile_one, again, over the wider corpus.
 *
 * Every fold is decided by the dynamic program over `FoldsOnto`, which is the
 * program proved equivalent to the definition in HPC/Fold/Decide.lean
 * (`foldsB_iff`).  Every pair is verified against `IsCrookedIvF` before use.
 *
 * Generators (all over the two base chains bing 0 9 and bing 9 0):
 *   (0) the thin chains themselves
 *   (a) single shavings (one peak of rho lowered)
 *   (b) single fills (one valley of sig raised)
 *   (c) random mixtures at rate 1/3
 *   (d) random mixtures at rate 1/2 and the total mixture (every peak shaved
 *       and every valley filled)
 *   (e) random faithful perturbation walks: a random single-link change of rho
 *       or sig, kept if the pair is still faithful, iterated.
 *
 * A sample of the arms met is written to census-batch50-audit.txt in the form
 * the Lean audit file HPC/Fold/Audit50.lean reads: the arm as a base-sixteen
 * numeral, its length, and the program's verdict on each predicate.
 *
 * Usage: census-batch50 [rand-rounds] [seed] [walk-steps]
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

/* IsCrookedIvF (rho, sig), exactly as HPC/Fold/Crook.lean states it. */
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

/* HighAt f (L+1) (L+8) */
static int highAt(const int *f, int m) {
  int seenLow = 0;
  for (int d = 0; d < m; d++) {
    if (f[d] >= 8 && !seenLow) return 0;
    if (f[d] <= 2) seenLow = 1;
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

/* Valley4 f L: the valley clause common to the three walks -- before every time
 * at L+1 or below, a time at L+5 or above at a step >= 3, at least 4 earlier. */
static int valley4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 3; j + 4 <= d && !ok; j++) if (a[j] >= 5) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* BottomW4 f L: the floor clause of w4 -- before every time at L or below, a
 * time at L+3 or below at a step >= 1, then a time at L+7 or above at least 6
 * steps later, and the descent at least 7 steps after that. */
static int bottomW4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 0) continue;
    int ok = 0;
    for (int j = 1; j + 13 <= d && !ok; j++) {
      if (a[j] > 3) continue;
      for (int k = j + 6; k + 7 <= d && !ok; k++) if (a[k] >= 7) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

/* TopW5 f L: the ceiling clause of w5 -- before every time at L+9, a time at
 * L+6 or above at a step >= 4, then a time at L+2 or below at least 6 steps
 * later, and the ascent at least 7 steps after that. */
static int topW5(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 9) continue;
    int ok = 0;
    for (int j = 4; j + 13 <= d && !ok; j++) {
      if (a[j] < 6) continue;
      for (int k = j + 6; k + 7 <= d && !ok; k++) if (a[k] <= 2) ok = 1;
    }
    if (!ok) return 0;
  }
  return 1;
}

/* Valley5 f L: the valley clause of w5 -- a time at L+6 or above at a step >= 4,
 * at least 5 steps earlier (deepValley_of_foldsOnto_leg3deep). */
static int valley5(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] > 1) continue;
    int ok = 0;
    for (int j = 4; j + 5 <= d && !ok; j++) if (a[j] >= 6) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

/* CeilW4 f L: the ceiling clause of w4 -- before every time at L+8 or above, a
 * time at L+3 or below at a step >= 1, at least 5 steps earlier. */
static int ceilW4(const int *a, int m) {
  for (int d = 0; d < m; d++) {
    if (a[d] < 8) continue;
    int ok = 0;
    for (int j = 1; j + 5 <= d && !ok; j++) if (a[j] <= 3) ok = 1;
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
static int foldsW3(const int *f, int m) {    /* 3 -> 6 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 3, 6, 1, 8);
  return folds(f, m, w, wl);
}
static int foldsW4(const int *f, int m) {    /* 3 -> 2 -> 8 -> 1 */
  int w[MAXW]; int wl = buildWalk(w, 3, 2, 8, 1);
  return folds(f, m, w, wl);
}
static int foldsW5(const int *f, int m) {    /* 3 -> 7 -> 1 -> 8 */
  int w[MAXW]; int wl = buildWalk(w, 3, 7, 1, 8);
  return folds(f, m, w, wl);
}

/* The configuration the case analysis of REPORT-batch49.md 2.2 leaves open for
 * `cross_valley_profile`: an arm whose low times before its first ascent to
 * L+7 all occur at its step two or three -- so that the clause applied across
 * the basepoint returns a low link at i-3 or i-2 and the V-criterion, which
 * wants index four or later, is not reached.  Returns 1 if the arm realises it. */
static int residualValleyCase(const int *a, int m) {
  int e = -1;
  for (int d = 0; d < m; d++) if (a[d] >= 7) { e = d; break; }
  if (e < 0) return 0;
  int any = 0, mx = -1, mn = 1 << 30;
  for (int j = 0; j < e; j++) if (a[j] <= 2) { any = 1; if (j > mx) mx = j; if (j < mn) mn = j; }
  return any && mn >= 2 && mx <= 3;
}

/* the shortest zigzag walk with at most three turns serving both arms */
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
  if (bs < 0) printf("      NO walk of at most three turns serves this pair\n");
  else printf("      shortest serving walk (%d times): %d -> %d -> %d -> %d\n",
              best, bs, ba, bb, bc);
}

typedef struct {
  long pairs, links, nonthin, base, unserved;
  long valleyFailG, valleyFailT, ceilFail, valley4Fail, valley5Fail, ceilW4Fail;
  long bottomW4Fail, topW5Fail, instrument;
  long residual, residualVee;
  long armVeeOK, armVeeBad, armLamOK, armLamBad;
  long armV4VeeOK, armV4VeeBad;
  long crossValleyTested, crossValleyBad;
  long unservedProfileOK, unservedProfileBad, unservedOneBad;
  long w3, w4, w5, threeOK, threeBad;
  long auditW3, auditW3Bad, auditW4, auditW4Bad, auditW5, auditW5Bad;
} Cnt;

static void zero(Cnt *c) { memset(c, 0, sizeof(*c)); }

/* ---- the audit sample ------------------------------------------------- */
static FILE *auditFile = NULL;
static int auditWant = 0, auditHave = 0;

static char auditSig[64][64];
static char auditTag[64][16];

static int auditTagCount(const char *tag) {
  int n = 0;
  for (int s = 0; s < auditHave; s++) if (!strcmp(auditTag[s], tag)) n++;
  return n;
}

static void auditArm(const int *a0, int m0, const char *tag, int gen, int bp, const char *which) {
  if (!auditFile || auditHave >= auditWant || m0 < 4) return;
  /* the audit objects are the first 64 steps of the arm: the predicates are
   * predicates of an arbitrary sequence, and a truncation keeps the kernel
   * checks in Lean affordable (Leg3Ceil is a triple quantifier). */
  const int *a = a0;
  int m = m0 < 64 ? m0 : 64;
  /* one arm per verdict signature, so that the sample exercises the predicates
   * rather than repeating one configuration */
  char sig[64];
  snprintf(sig, sizeof sig, "%d%d%d%d%d%d%d%d%d%d%d%d%d",
           highAt(a, m), leg3Valley(a, m), leg3Ceil(a, m), valley4(a, m), valley5(a, m),
           ceilW4(a, m), bottomW4(a, m), topW5(a, m), foldsLam(a, m), foldsVee(a, m),
           foldsW3(a, m), foldsW4(a, m), foldsW5(a, m));
  for (int s = 0; s < auditHave; s++) if (!strcmp(auditSig[s], sig)) return;
  if (auditTagCount(tag) >= 3) return;          /* spread the sample over the generators */
  strcpy(auditSig[auditHave], sig);
  snprintf(auditTag[auditHave], sizeof auditTag[0], "%s", tag);
  auditHave++;
  fprintf(auditFile, "arm %s gen=%d basepoint=%d %s len=%d (of %d)\n", tag, gen, bp, which, m, m0);
  fprintf(auditFile, "  levels:");
  for (int d = 0; d < m; d++) fprintf(auditFile, " %d", a[d]);
  fprintf(auditFile, "\n  nat16: 0x");
  for (int d = m - 1; d >= 0; d--) fprintf(auditFile, "%X", a[d]);
  fprintf(auditFile,
          "\n  highAt=%d leg3Valley=%d leg3Ceil=%d valley4=%d valley5=%d ceilW4=%d bottomW4=%d "
          "topW5=%d\n  foldsLam=%d foldsVee=%d foldsW3=%d foldsW4=%d foldsW5=%d\n",
          highAt(a, m), leg3Valley(a, m), leg3Ceil(a, m), valley4(a, m), valley5(a, m),
          ceilW4(a, m), bottomW4(a, m), topW5(a, m), foldsLam(a, m), foldsVee(a, m),
          foldsW3(a, m), foldsW4(a, m), foldsW5(a, m));
}

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
    auditArm(armG, mg, tag, gen, i, "forward");
    auditArm(armT, mt, tag, gen, i, "backward");
    int vG = leg3Valley(armG, mg), vT = leg3Valley(armT, mt);
    int cG = leg3Ceil(armG, mg), cT = leg3Ceil(armT, mt);
    int q4G = valley4(armG, mg), q4T = valley4(armT, mt);
    int q5G = valley5(armG, mg), q5T = valley5(armT, mt);
    int c4G = ceilW4(armG, mg), c4T = ceilW4(armT, mt);
    int fvG = foldsVee(armG, mg), fvT = foldsVee(armT, mt);
    int flG = foldsLam(armG, mg), flT = foldsLam(armT, mt);
    int f3G = foldsW3(armG, mg), f3T = foldsW3(armT, mt);
    int f4G = foldsW4(armG, mg), f4T = foldsW4(armT, mt);
    int f5G = foldsW5(armG, mg), f5T = foldsW5(armT, mt);
    if (!vG) c->valleyFailG++;
    if (!vT) c->valleyFailT++;
    if (!cG) c->ceilFail++;
    if (!cT) c->ceilFail++;
    if (!q4G) c->valley4Fail++;
    if (!q4T) c->valley4Fail++;
    if (!q5G) c->valley5Fail++;
    if (!q5T) c->valley5Fail++;
    if (!c4G) c->ceilW4Fail++;
    if (!c4T) c->ceilW4Fail++;
    if (residualValleyCase(armG, mg)) { c->residual++; if (fvG) c->residualVee++; }
    if (residualValleyCase(armT, mt)) { c->residual++; if (fvT) c->residualVee++; }
    if (!bottomW4(armG, mg)) c->bottomW4Fail++;
    if (!bottomW4(armT, mt)) c->bottomW4Fail++;
    if (!topW5(armG, mg)) c->topW5Fail++;
    if (!topW5(armT, mt)) c->topW5Fail++;

    /* audit of the necessity theorems: a fold implies the clause */
    {
      const int *ar[2] = {armG, armT}; int ml[2] = {mg, mt};
      int f3[2] = {f3G, f3T}, f4[2] = {f4G, f4T}, f5[2] = {f5G, f5T};
      for (int s = 0; s < 2; s++) {
        if (f3[s]) { c->auditW3++;
          if (!(leg3Ceil(ar[s], ml[s]) && valley4(ar[s], ml[s]))) { c->auditW3Bad++;
            printf("  [%s %d] AUDIT leg3Ceil/valley4 necessity FAILS for w3: basepoint %d arm %d\n",
                   tag, gen, i, s); } }
        if (f4[s]) { c->auditW4++;
          if (!(ceilW4(ar[s], ml[s]) && bottomW4(ar[s], ml[s]))) { c->auditW4Bad++;
            printf("  [%s %d] AUDIT ceilW4/bottomW4 necessity FAILS for w4: basepoint %d arm %d\n",
                   tag, gen, i, s); } }
        if (f5[s]) { c->auditW5++;
          if (!(valley5(ar[s], ml[s]) && topW5(ar[s], ml[s]))) { c->auditW5Bad++;
            printf("  [%s %d] AUDIT valley5/topW5 necessity FAILS for w5: basepoint %d arm %d\n",
                   tag, gen, i, s); } }
      }
    }

    /* the batch-48 theorems, and the new Valley4 form */
    if (!vG) { if (fvG) c->armVeeOK++; else { c->armVeeBad++;
      printf("  [%s %d] LEMMA leg3Valley_or_vee FAILS: basepoint %d forward\n", tag, gen, i); } }
    if (!vT) { if (fvT) c->armVeeOK++; else { c->armVeeBad++;
      printf("  [%s %d] LEMMA leg3Valley_or_vee FAILS: basepoint %d backward\n", tag, gen, i); } }
    if (!cG) { if (flG) c->armLamOK++; else { c->armLamBad++;
      printf("  [%s %d] LEMMA leg3Ceil_or_lam FAILS: basepoint %d forward\n", tag, gen, i); } }
    if (!cT) { if (flT) c->armLamOK++; else { c->armLamBad++;
      printf("  [%s %d] LEMMA leg3Ceil_or_lam FAILS: basepoint %d backward\n", tag, gen, i); } }
    if (!q4G) { if (fvG) c->armV4VeeOK++; else { c->armV4VeeBad++;
      printf("  [%s %d] arm fails Valley4 and does NOT fold onto the V-walk: basepoint %d "
             "forward\n", tag, gen, i); } }
    if (!q4T) { if (fvT) c->armV4VeeOK++; else { c->armV4VeeBad++;
      printf("  [%s %d] arm fails Valley4 and does NOT fold onto the V-walk: basepoint %d "
             "backward\n", tag, gen, i); } }

    /* work item 1 */
    if (!vG || !vT) {
      c->crossValleyTested++;
      if (!(fvG && fvT)) { c->crossValleyBad++;
        printf("  [%s %d] WORK ITEM cross_valley_profile FAILS: basepoint %d "
               "(valley G=%d T=%d, V-fold G=%d T=%d)\n", tag, gen, i, vG, vT, fvG, fvT); }
    }

    /* the unserved pairs */
    if ((flG && flT) || (fvG && fvT)) continue;
    c->unserved++;
    if (vG && vT && cG && cT) c->unservedProfileOK++; else c->unservedProfileBad++;
    if (!((vG || vT) && (cG || cT))) { c->unservedOneBad++;
      printf("  [%s %d] unserved_profile_one FAILS: basepoint %d\n", tag, gen, i); }
    {
      int s3 = f3G && f3T, s4 = f4G && f4T, s5 = f5G && f5T;
      if (s3) c->w3++;
      if (s4) c->w4++;
      if (s5) c->w5++;
      /* the instrument of refutation: for each walk, does some arm fail that
       * walk's necessary clause?  (three_walks_necessary, HPC/Fold/LandmarkW) */
      if ((!cG || !cT) && (!c4G || !c4T) && (!q5G || !q5T)) c->instrument++;
      if (s3 || s4 || s5) c->threeOK++;
      else { c->threeBad++;
        printf("  [%s %d] WORK ITEM unserved_three_walks FAILS: basepoint %d "
               "(w3 G=%d T=%d, w4 G=%d T=%d, w5 G=%d T=%d; valley4 G=%d T=%d, "
               "leg3Ceil G=%d T=%d)\n", tag, gen, i, f3G, f3T, f4G, f4T, f5G, f5T,
               q4G, q4T, cG, cT);
        findWalk(armG, mg, armT, mt);
        printf("      forward arm  (len %d):", mg);
        for (int d = 0; d < mg && d < 60; d++) printf(" %d", armG[d]);
        printf("\n      backward arm (len %d):", mt);
        for (int d = 0; d < mt && d < 60; d++) printf(" %d", armT[d]);
        printf("\n");
      }
    }
  }
}

static void report(const char *name, const Cnt *c) {
  printf("\n-- %s --\n", name);
  printf("faithful pairs: %ld; non-thin links %ld/%ld (%.5f)\n", c->pairs, c->nonthin, c->links,
         c->links ? (double)c->nonthin / (double)c->links : 0.0);
  printf("branch basepoints: %ld; unserved by the two canonical walks: %ld\n", c->base,
         c->unserved);
  printf("arms failing: Leg3Valley %ld/%ld (fwd/bwd), Leg3Ceil %ld, Valley4 %ld, Valley5 %ld, "
         "CeilW4 %ld, BottomW4 %ld, TopW5 %ld\n", c->valleyFailG, c->valleyFailT, c->ceilFail,
         c->valley4Fail, c->valley5Fail, c->ceilW4Fail, c->bottomW4Fail, c->topW5Fail);
  printf("arms realising the residual case of cross_valley_profile (all low times before the \n"
         "  first ascent to L+7 at step two or three): %ld, of which %ld fold onto the V-walk\n",
         c->residual, c->residualVee);
  printf("unserved pairs at which the landmark instrument fires (each of the three clauses "
         "fails on some arm): %ld\n", c->instrument);
  printf("necessity audits: w3 %ld checks / %ld failures; w4 %ld / %ld; w5 %ld / %ld\n",
         c->auditW3, c->auditW3Bad, c->auditW4, c->auditW4Bad, c->auditW5, c->auditW5Bad);
  printf("leg3Valley_or_vee: %ld confirmations, %ld failures;  leg3Ceil_or_lam: %ld, %ld;  "
         "Valley4-or-vee: %ld, %ld\n", c->armVeeOK, c->armVeeBad, c->armLamOK, c->armLamBad,
         c->armV4VeeOK, c->armV4VeeBad);
  printf("cross_valley_profile: tested %ld, FAILURES %ld\n", c->crossValleyTested,
         c->crossValleyBad);
  printf("unserved_profile: holds %ld, fails %ld; unserved_profile_one failures %ld\n",
         c->unservedProfileOK, c->unservedProfileBad, c->unservedOneBad);
  printf("unserved_three_walks: served by w3 %ld, w4 %ld, w5 %ld; by one of the three %ld; "
         "BY NONE %ld\n", c->w3, c->w4, c->w5, c->threeOK, c->threeBad);
}

static Cnt ct, cs, cf, cm, ch, cw;

static void runChain(int n, const int *v, long rounds, long walkSteps, const char *name) {
  printf("\n==== base chain %s (n = %d links); IsCrookedIvF: ", name, n);
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  printf("%d ====\n", crookedGen(rho, sig, n));

  /* (0) the thin chain */
  for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
  if (crookedGen(rho, sig, n)) scan(&ct, n, "thin", 0);

  /* (a) single shavings */
  for (int pk = 1; pk + 1 < n; pk++) {
    if (!(v[pk] > v[pk-1] && v[pk] > v[pk+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    rho[pk] = v[pk] - 1;
    if (!crookedGen(rho, sig, n)) { printf("  shave %d: NOT faithful\n", pk); continue; }
    scan(&cs, n, "shave", pk);
  }

  /* (b) single fills */
  for (int vl = 1; vl + 1 < n; vl++) {
    if (!(v[vl] < v[vl-1] && v[vl] < v[vl+1])) continue;
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    sig[vl] = v[vl] + 1;
    if (!crookedGen(rho, sig, n)) { printf("  fill %d: NOT faithful\n", vl); continue; }
    scan(&cf, n, "fill", vl);
  }

  /* (c) random mixtures at rate 1/3 */
  for (long it = 0; it < rounds; it++) {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) { if (random() % 3 == 0) rho[j] = v[j] - 1; }
      else if (v[j] < v[j-1] && v[j] < v[j+1]) { if (random() % 3 == 0) sig[j] = v[j] + 1; }
    }
    if (!crookedGen(rho, sig, n)) { printf("  mix round %ld: NOT faithful\n", it); continue; }
    scan(&cm, n, "mix", (int)it);
  }

  /* (d) heavy mixtures: rate 1/2, and the total mixture */
  for (long it = 0; it < rounds; it++) {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) { if (random() % 2 == 0) rho[j] = v[j] - 1; }
      else if (v[j] < v[j-1] && v[j] < v[j+1]) { if (random() % 2 == 0) sig[j] = v[j] + 1; }
    }
    if (!crookedGen(rho, sig, n)) { printf("  heavy round %ld: NOT faithful\n", it); continue; }
    scan(&ch, n, "heavy", (int)it);
  }
  {
    for (int u = 0; u < n; u++) { rho[u] = v[u]; sig[u] = v[u]; }
    for (int j = 1; j + 1 < n; j++) {
      if (v[j] > v[j-1] && v[j] > v[j+1]) rho[j] = v[j] - 1;
      else if (v[j] < v[j-1] && v[j] < v[j+1]) sig[j] = v[j] + 1;
    }
    if (crookedGen(rho, sig, n)) { printf("  the total mixture is faithful\n");
      scan(&ch, n, "total", -1); }
    else printf("  the total mixture is NOT faithful\n");
  }

  /* (e) a random faithful perturbation walk: single-link changes of rho or sig,
   * kept when the pair stays faithful.  This leaves the shaving/filling family
   * altogether: nothing asks the change to sit at a local extremum. */
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
      scan(&cw, n, "walk", (int)accepted);
    }
    printf("  random perturbation walk: %ld steps tried, %ld accepted\n", walkSteps, accepted);
  }
}

int main(int argc, char **argv) {
  long rounds = (argc > 1) ? atol(argv[1]) : 40;
  unsigned seed = (argc > 2) ? (unsigned)atoi(argv[2]) : 50u;
  long walkSteps = (argc > 3) ? atol(argv[3]) : 200;
  srandom(seed);
  auditFile = fopen("census-batch50-audit.txt", "w");
  auditWant = 18;
  printf("census-batch50: the three walks, the valley crossing, and the necessity audits.\n");
  printf("rounds=%ld seed=%u walk-steps=%ld\n", rounds, seed, walkSteps);
  zero(&ct); zero(&cs); zero(&cf); zero(&cm); zero(&ch); zero(&cw);

  Path p = bpath(0, 9);
  runChain(p.n, p.v, rounds, walkSteps, "bing 0 9");
  Path q = bpath(9, 0);
  runChain(q.n, q.v, rounds, walkSteps, "bing 9 0");

  printf("\n================ totals over both base chains ================\n");
  report("the thin chains", &ct);
  report("single shavings", &cs);
  report("single fills", &cf);
  report("random mixtures (rate 1/3)", &cm);
  report("heavy mixtures (rate 1/2, and the total mixture)", &ch);
  report("random faithful perturbation walks", &cw);

  {
    Cnt all; zero(&all);
    const Cnt *cc[6] = {&ct, &cs, &cf, &cm, &ch, &cw};
    long *dst = (long *)&all;
    for (int s = 0; s < 6; s++) {
      const long *src = (const long *)cc[s];
      for (unsigned u = 0; u < sizeof(Cnt) / sizeof(long); u++) dst[u] += src[u];
    }
    report("EVERYTHING", &all);
  }
  if (auditFile) fclose(auditFile);
  free(p.v); free(q.v);
  return 0;
}
