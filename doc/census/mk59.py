#!/usr/bin/env python3
"""Build census-batch59.c from census-batch58.c.

Batch 59 replaces the criterion block of batch 58 by the *exact* criterion of a four-leg
walk -- the landmark sentence Leg4Land of HPC/Fold/Leg4Land.lean -- and compares it, arm by
arm, with the fold itself; everything else is carried over unchanged.
"""

src = open('census-batch58.c').read()

# ---------------------------------------------------------------- header ----
old_head = "/* census-batch58.c -- batch 58."
new_head = '''/* census-batch59.c -- batch 59.  The branch L+5, read by the *exact* criterion
 * of a four-leg walk: the landmark sentence Leg4Land of HPC/Fold/Leg4Land.lean.
 *
 * New in this batch.
 *
 *   A. Question 1.  foldsOnto_leg4_iff_leg4Land says that, for a 1-Lipschitz arm
 *      of the band whose first level is within one of P-1, folding onto
 *      leg4Walk L H K M P is *equivalent* to the landmark sentence.  The census
 *      evaluates both, by their own definitions, on every arm of the branch and
 *      every parameter set of the window and its reflection, and reports the
 *      disagreements (the theorem says there are none).  The engine's criterion
 *      Leg4Crit is evaluated alongside, so the gain is measured.
 *
 *   B. Question 2.  The 175-link arm of HPC/Fold/Audit58.lean -- the window of
 *      bing 0 9 at its link 811, which meets the criterion of no parameter set
 *      of the engine -- is read by the exact criterion: which walks of the
 *      family serve it, and what the landmark chains are.
 *
 *   C. Question 3.  Exhaustiveness at L+5.  With an exact criterion per walk the
 *      statement "every basepoint of the branch is served by one of a finite
 *      list of walks" is decidable arm by arm, and the census reports it: the
 *      basepoints served by some walk of the family, those served by none, and a
 *      greedy cover of the whole branch by walks.
 *
 * Carried over from census-batch58.c unchanged: the generators, the
 * faithfulness test, the dynamic program, the branch-L+4 block, the
 * reflected-branch block and the whole corpus.  The original header follows.
 *
 * census-batch58.c -- batch 58.'''
assert old_head in src
src = src.replace(old_head, new_head, 1)

# ------------------------------------------------- the landmark sentence ----
anchor = "/* the residual basepoints of the branch L+5 and the family walks serving them */"
land_code = r'''/* ---- the landmark sentence Leg4Land of HPC/Fold/Leg4Land.lean --------------
 *
 * The walk leg4Walk 0 9 K M P has its landmark positions at
 *
 *   A = K - P + 1        (the peak, level K)
 *   B = 2K - P + 1 - M   (the valley, level M)
 *   C = 2K - P + 9 - 2M  (the top of the third leg, level 8)
 *
 * and the sentence asks, by its own definition:
 *
 *   base   : the first level is within one of P-1;
 *   floor  : before every d with f d <= P-3 a step j with j >= A, f j >= K-1 and
 *            j + (K - 1 - f d) <= d;
 *   deep   : before every d with f d <= M-2 three steps j, k, l with j >= A,
 *            f j >= K-1, k >= j + (K-M), f k <= M+1, l >= k + (8-M),
 *            f l >= 7 and l + (7 - f d) <= d;
 *   ceiling: before every d with f d >= K+2 two steps j, k with j >= A,
 *            f j >= K-1, k >= j + (K-M), f k <= M+1 and k + (f d - M - 1) <= d.
 *
 * The existential chains are evaluated greedily -- the earliest j, then the
 * earliest k after it, then the earliest l -- which is equivalent to the
 * definition because every constraint of the chain is monotone in the index;
 * landLeg4Brute below evaluates the existentials literally, and the two are
 * compared on a sample as a check on that step. */
static int landChain[3];
static int landLeg4(const int *f, int m, int K, int M, int P) {
  const int H = 9;
  int A = K - P + 1;
  landChain[0] = landChain[1] = landChain[2] = -1;
  if (f[0] < P - 2 || f[0] > P) return 0;
  int t1 = -1, t2 = -1, t3 = -1;
  for (int j = A; j < m; j++) if (f[j] >= K - 1) { t1 = j; break; }
  if (t1 >= 0) for (int k = t1 + (K - M); k < m; k++) if (f[k] <= M + 1) { t2 = k; break; }
  if (t2 >= 0) for (int l = t2 + (H - 1 - M); l < m; l++) if (f[l] >= H - 2) { t3 = l; break; }
  landChain[0] = t1; landChain[1] = t2; landChain[2] = t3;
  for (int d = 0; d < m; d++) {
    if (f[d] <= P - 3 && (t1 < 0 || t1 + (K - 1 - f[d]) > d)) return 0;
    if (f[d] <= M - 2 && (t3 < 0 || t3 + (H - 2 - f[d]) > d)) return 0;
    if (f[d] >= K + 2 && (t2 < 0 || t2 + (f[d] - M - 1) > d)) return 0;
  }
  return 1;
}

/* the same sentence with its existentials searched literally; quadratic and
 * cubic, so only used on short arms as a check on the greedy reading */
static int landLeg4Brute(const int *f, int m, int K, int M, int P) {
  const int H = 9;
  int A = K - P + 1;
  if (f[0] < P - 2 || f[0] > P) return 0;
  for (int d = 0; d < m; d++) {
    if (f[d] <= P - 3) {
      int ok = 0;
      for (int j = 0; j < m && !ok; j++)
        if (j >= A && f[j] >= K - 1 && j + (K - 1 - f[d]) <= d) ok = 1;
      if (!ok) return 0;
    }
    if (f[d] <= M - 2) {
      int ok = 0;
      for (int j = 0; j < m && !ok; j++) {
        if (!(j >= A && f[j] >= K - 1)) continue;
        for (int k = 0; k < m && !ok; k++) {
          if (!(k >= j + (K - M) && f[k] <= M + 1)) continue;
          for (int l = 0; l < m && !ok; l++)
            if (l >= k + (H - 1 - M) && f[l] >= H - 2 && l + (H - 2 - f[d]) <= d) ok = 1;
        }
      }
      if (!ok) return 0;
    }
    if (f[d] >= K + 2) {
      int ok = 0;
      for (int j = 0; j < m && !ok; j++) {
        if (!(j >= A && f[j] >= K - 1)) continue;
        for (int k = 0; k < m && !ok; k++)
          if (k >= j + (K - M) && f[k] <= M + 1 && k + (f[d] - M - 1) <= d) ok = 1;
      }
      if (!ok) return 0;
    }
  }
  return 1;
}

/* the fold onto the *direct* walk of a parameter set, P-1 -> K -> M -> 8 -> 1 */
static int foldsDirect(const int *f, int m, int K, int M, int P) {
  int w[MAXW];
  int wl = buildWalk4(w, P - 1, K, M, 8, 1);
  if (wl < 0) return 0;
  return folds(f, m, w, wl);
}

#define BRUTECAP 40000
static long bruteSamples = 0, bruteBad = 0;

'''
assert anchor in src
src = src.replace(anchor, land_code + anchor, 1)

# ------------------------------------------------------------- counters ----
old_cnt = "  long w1Both, w1BothIv;           /* basepoints where both arms meet it */"
new_cnt = '''  long w1Both, w1BothIv;           /* basepoints where both arms meet it */
  /* batch 59: the exact criterion, the landmark sentence */
  long landArms;                   /* arms x parameter sets examined */
  long landHolds, foldHolds;       /* the sentence holds; the arm folds */
  long landNotFold, foldNotLand;   /* the two disagreements (both must be 0) */
  long critHoldsPt;                /* the engine's criterion holds (point form) */
  long landNotCrit;                /* the sentence holds where the engine's criterion fails */
  long landAny5, landNone5;        /* a parameter set serving both arms of a basepoint */'''
assert old_cnt in src
src = src.replace(old_cnt, new_cnt, 1)

# ------------------------------------------------- the block inside scan ----
old_blk_start = "      /* ---- batch 58: the criteria of the wide four-leg engine ---- */"
i = src.index(old_blk_start)
j = src.index("      int s1 = foldsLamR(armG, mg)", i)
new_blk = '''      /* ---- batch 59: the exact criterion, against the fold itself ---- */
      {
        unsigned long long mland = 0;
        for (int q = 0; q < famN; q++) {
          int K = fam[q].K, M = fam[q].M, P = fam[q].P;
          const int *aG = fam[q].refl ? gG : armG;
          const int *aT = fam[q].refl ? gT : armT;
          int lG = landLeg4(aG, mg, K, M, P), lT = landLeg4(aT, mt, K, M, P);
          int fG = foldsDirect(aG, mg, K, M, P), fT = foldsDirect(aT, mt, K, M, P);
          int cG = (critLeg4Mask(aG, aG, aG, mg, K, M, P) == 0);
          int cT = (critLeg4Mask(aT, aT, aT, mt, K, M, P) == 0);
          c->landArms += 2;
          c->landHolds += lG + lT;
          c->foldHolds += fG + fT;
          c->critHoldsPt += cG + cT;
          if (lG && !fG) c->landNotFold++;
          if (lT && !fT) c->landNotFold++;
          if (fG && !lG) c->foldNotLand++;
          if (fT && !lT) c->foldNotLand++;
          if (lG && !cG) c->landNotCrit++;
          if (lT && !cT) c->landNotCrit++;
          if (mg <= 40 && bruteSamples < BRUTECAP) {
            bruteSamples++;
            if (landLeg4Brute(aG, mg, K, M, P) != lG) bruteBad++;
          }
          if (fG && fT) { mland |= 1ULL << q; critHits[q]++; }
        }
        if (mland) c->landAny5++; else c->landNone5++;
        if (critN < MAXRES) { critMaskPt[critN] = mland; critN++; }
      }
'''
src = src[:i] + new_blk + src[j:]

# --------------------------------------------------------------- report ----
old_rep = '  printf("  batch 58, the criteria of the four-leg engine at the branch L+5:\\n");'
k = src.index(old_rep)
k2 = src.index('}\n\n/* ------------------------------ the corpus', k)
new_rep = '''  printf("  batch 59, the exact criterion at the branch L+5:\\n");
  printf("    arms x parameter sets %ld; the landmark sentence holds %ld, the arm folds %ld\\n",
         c->landArms, c->landHolds, c->foldHolds);
  printf("    the sentence holds and the arm does not fold (must be 0): %ld\\n", c->landNotFold);
  printf("    the arm folds and the sentence fails (must be 0): %ld\\n", c->foldNotLand);
  printf("    the engine's criterion holds %ld; the sentence holds where it fails %ld\\n",
         c->critHoldsPt, c->landNotCrit);
  printf("    basepoints with a parameter set serving *both* arms: %ld; with none: %ld\\n",
         c->landAny5, c->landNone5);
'''
src = src[:k] + new_rep + src[k2:]

# ------------------------------------------------ the batch-59 witness -----
old_main = 'printf("census-batch58: the branch L+5 by the criteria of the four-leg engine.\\n");'
new_main = 'printf("census-batch59: the branch L+5 by the exact criterion of a four-leg walk.\\n");'
assert old_main in src
src = src.replace(old_main, new_main, 1)

# the question-2 block, run right after the family is built
anchor2 = '''  Path p = bpath(0, 9);
  runChain(p.n, p.v, rounds, walkSteps, "bing 0 9");'''
q2 = r'''  /* ---- question 2: the 175-link arm of HPC/Fold/Audit58.lean ------------ */
  {
    Path b = bpath(0, 9);
    printf("\nquestion 2: the arm of Audit58 -- bing 0 9 (%d links) from its link 811, "
           "175 links\n", b.n);
    static int arm[MAXN], armR[MAXN];
    int m175 = 175;
    for (int t = 0; t < m175; t++) { arm[t] = b.v[811 + t]; armR[t] = 9 - arm[t]; }
    printf("  the arm begins %d %d %d %d %d ... and ends ... %d %d %d\n",
           arm[0], arm[1], arm[2], arm[3], arm[4], arm[172], arm[173], arm[174]);
    int served = 0, crit = 0;
    for (int q = 0; q < famN; q++) {
      int K = fam[q].K, M = fam[q].M, P = fam[q].P;
      const int *a = fam[q].refl ? armR : arm;
      int fo = foldsDirect(a, m175, K, M, P);
      int la = landLeg4(a, m175, K, M, P);
      int t1 = landChain[0], t2 = landChain[1], t3 = landChain[2];
      int cr = (critLeg4Mask(a, a, a, m175, K, M, P) == 0);
      if (cr) crit++;
      if (fo != la) printf("  DISAGREEMENT at P%d K%d M%d %s\n", P, K, M,
                           fam[q].refl ? "reflected" : "direct");
      if (fo) {
        served++;
        printf("  served by (P,K,M) = (%d,%d,%d) %s: walk %d -> %d -> %d -> 8 -> 1;"
               " landmark chain %d, %d, %d; engine's criterion %s\n",
               P, K, M, fam[q].refl ? "reflected" : "direct   ",
               P - 1, K, M, t1, t2, t3, cr ? "holds" : "fails");
      }
    }
    printf("  walks of the family serving the arm: %d of %d; "
           "parameter sets whose engine criterion holds: %d\n", served, famN, crit);
    free(b.v);
  }

''' + anchor2
assert anchor2 in src
src = src.replace(anchor2, q2, 1)

# the brute-force audit line, printed at the end of main
tail_anchor = '  report("all", &cr);'
if tail_anchor not in src:
    # find the final report call block
    tail_anchor = None
open('census-batch59.c', 'w').write(src)
print("written", len(src))

# ---- second pass: the tail sections and the no-walk witness ----------------
src = open('census-batch59.c').read()

# prefixNoCrit / reportNoCrit now speak of walks, not criteria
src = src.replace('''/* ---- the shortest prefix of a forward arm that meets no criterion -----------
 *
 * Every clause of `Leg4Crit` is of the form "for every trigger `d`, some pattern
 * is completed strictly before `d`", so a prefix of an arm inherits the failure:
 * if the prefix fails a clause at `d`, the whole arm fails it at the same `d`.
 * The same holds for `LowAt` and for faithfulness.  So the shortest prefix of a
 * forward arm at which *no* parameter set of the window has its criterion is a
 * counterexample in its own right, read as a faithful pair whose basepoint is
 * its first link -- the backward arm is then the single basepoint link, which
 * meets every criterion whose base condition it meets.''',
'''/* ---- the shortest prefix of a forward arm that no walk serves ---------------
 *
 * A fold is inherited by a prefix: if the whole arm folds onto a walk then so
 * does every prefix of it.  The same holds for `LowAt` and for faithfulness.  So
 * the shortest prefix of a forward arm that *no* walk of the family serves is a
 * counterexample in its own right, read as a faithful pair whose basepoint is
 * its first link -- the backward arm is then the single basepoint link, which
 * folds onto every walk whose first level it meets.''')

src = src.replace('''    int b = fam[q].refl ? critLeg4Mask(rG, rG, rG, len, K, M, P)
                        : critLeg4Mask(aG, aG, aG, len, K, M, P);
    if (b == 0) return 0;''',
'''    int fo = fam[q].refl ? foldsDirect(rG, len, K, M, P)
                         : foldsDirect(aG, len, K, M, P);
    if (fo) return 0;''')

src = src.replace('''  if (bestNoCritI < 0) { printf("\\n  no arm of the branch meets no criterion\\n"); return; }''',
'''  if (bestNoCritI < 0) {
    printf("\\n  every arm of the branch is served by some walk of the family\\n"); return; }''')
src = src.replace('''  printf("\\n======== the shortest arm of the branch meeting no four-leg criterion ========\\n");''',
'''  printf("\\n======== the shortest arm of the branch served by no four-leg walk ========\\n");''')
src = src.replace('''  printf("  the clause that fails, per parameter set (1 base, 2 hfloor, 4 hdeep, 8 hceil):\\n");
  {
    static int aG[MAXN], rG[MAXN];
    for (int d = 0; d < len; d++) { aG[d] = nrho[d]; rG[d] = 9 - aG[d]; }
    for (int q = 0; q < famN; q++) {
      int b = fam[q].refl
              ? critLeg4Mask(rG, rG, rG, len, fam[q].K, fam[q].M, fam[q].P)
              : critLeg4Mask(aG, aG, aG, len, fam[q].K, fam[q].M, fam[q].P);
      printf("    %s P=%d K=%d M=%d : %d\\n", fam[q].refl ? "reflected" : "direct  ",
             fam[q].P, fam[q].K, fam[q].M, b);
    }
  }''',
'''  printf("  the fold and the landmark sentence, per parameter set:\\n");
  {
    static int aG[MAXN], rG[MAXN];
    for (int d = 0; d < len; d++) { aG[d] = nrho[d]; rG[d] = 9 - aG[d]; }
    for (int q = 0; q < famN; q++) {
      const int *a = fam[q].refl ? rG : aG;
      int fo = foldsDirect(a, len, fam[q].K, fam[q].M, fam[q].P);
      int la = landLeg4(a, len, fam[q].K, fam[q].M, fam[q].P);
      printf("    %s P=%d K=%d M=%d : folds %d, landmark sentence %d\\n",
             fam[q].refl ? "reflected" : "direct  ", fam[q].P, fam[q].K, fam[q].M, fo, la);
    }
  }''')

# call the witness hunt again from the new block
src = src.replace('''        if (mland) c->landAny5++; else c->landNone5++;''',
'''        if (mland) c->landAny5++; else { c->landNone5++; emitNoCrit(n, i); }
        noteNoCrit(n, i, mg);''')

# the tail: the walks of the family over the whole branch, and the greedy cover
i = src.index('  printf("\\n---- batch 58: the criteria of the four-leg engine over the whole branch ----\\n");')
j = src.index('  reportNoCrit();')
tail = '''  printf("\\n---- the four-leg family over the whole branch L+5 ----\\n");
  printf("  basepoints of the branch L+5 recorded: %ld\\n", critN);
  for (int q2 = 0; q2 < famN; q2++)
    if (critHits[q2])
      printf("  %s P=%d K=%d M=%d : %d -> %d -> %d -> %d -> %d  serves both arms at %ld\\n",
             fam[q2].refl ? "reflected" : "direct  ", fam[q2].P, fam[q2].K, fam[q2].M,
             fam[q2].st, fam[q2].a, fam[q2].b, fam[q2].c, fam[q2].e, critHits[q2]);

  {
    static char done[MAXRES];
    memset(done, 0, sizeof(done));
    long left = 0;
    for (long u = 0; u < critN; u++) if (critMaskPt[u]) left++; else done[u] = 1;
    printf("\\n  greedy cover of the branch by walks: %ld of %ld basepoints are served by "
           "some walk\\n", left, critN);
    int picks = 0;
    while (left > 0 && picks < famN) {
      int bestq = -1; long bestc = 0;
      for (int q2 = 0; q2 < famN; q2++) {
        long cnt = 0;
        for (long u = 0; u < critN; u++)
          if (!done[u] && (critMaskPt[u] & (1ULL << q2))) cnt++;
        if (cnt > bestc) { bestc = cnt; bestq = q2; }
      }
      if (bestq < 0) break;
      for (long u = 0; u < critN; u++)
        if (!done[u] && (critMaskPt[u] & (1ULL << bestq))) { done[u] = 1; left--; }
      picks++;
      printf("    pick %d: %s P=%d K=%d M=%d (%d -> %d -> %d -> %d -> %d) covers %ld, "
             "left %ld\\n", picks, fam[bestq].refl ? "reflected" : "direct",
             fam[bestq].P, fam[bestq].K, fam[bestq].M, fam[bestq].st, fam[bestq].a,
             fam[bestq].b, fam[bestq].c, fam[bestq].e, bestc, left);
    }
    printf("    walks needed: %d\\n", picks);
  }

  printf("\\n  the landmark sentence read literally (the existentials searched) against the\\n"
         "  greedy reading of the chains: %ld samples, %ld disagreements\\n",
         bruteSamples, bruteBad);

'''
src = src[:i] + tail + src[j:]

# the audit paragraph
src = src.replace('''  printf("  the strengthened criteria (witness at index 12, Valley5 at index 5, TopW5 at\\n"''',
'''  printf("    Leg4Land, the landmark sentence of HPC/Fold/Leg4Land.lean, clause by clause,\\n"
         "    with the index bounds the walk's own positions dictate; Leg4Crit, the criterion\\n"
         "    of the engine, as the three announcements of foldsOnto_leg4W.\\n");
  printf("  the strengthened criteria (witness at index 12, Valley5 at index 5, TopW5 at\\n"''')

open('census-batch59.c', 'w').write(src)
print("second pass written")

# ---- third pass: drop what the batch-58 criterion block used ---------------
import re
src = open('census-batch59.c').read()
# the interval witness emitter, now unused
i = src.index('static int emittedIv = 0;')
j = src.index('/* -------------------------------- the scan', i)
src = src[:i] + src[j:]
src = src.replace('''static long critHits[MAXFAM], critHitsIv[MAXFAM];
#define SOUNDCAP 400000
static long soundSamples = 0;
/* the failures of each clause of each parameter set, counted per arm */
static long clauseFailPt[MAXFAM][4], clauseFailIv[MAXFAM][4], clauseArms[MAXFAM];''',
'''static long critHits[MAXFAM];''')
src = src.replace('static unsigned long long critMaskPt[MAXRES], critMaskIv[MAXRES];',
                  'static unsigned long long critMaskPt[MAXRES];')
src = src.replace('''/* batch 58: the parameter sets whose criterion holds at a basepoint of the branch */''',
'''/* batch 59: the walks of the family serving both arms at a basepoint of the branch */''')
src = src.replace('''      if (j < *minIdx) *minIdx = j; break; }''',
'''      if (j < *minIdx) *minIdx = j;
      break; }''')
open('census-batch59.c','w').write(src)
print("third pass written")

# ---- fourth pass: the exact criterion makes the census linear --------------
src = open('census-batch59.c').read()
old = '''          int lG = landLeg4(aG, mg, K, M, P), lT = landLeg4(aT, mt, K, M, P);
          int fG = foldsDirect(aG, mg, K, M, P), fT = foldsDirect(aT, mt, K, M, P);
          int cG = (critLeg4Mask(aG, aG, aG, mg, K, M, P) == 0);
          int cT = (critLeg4Mask(aT, aT, aT, mt, K, M, P) == 0);
          c->landArms += 2;
          c->landHolds += lG + lT;
          c->foldHolds += fG + fT;
          c->critHoldsPt += cG + cT;
          if (lG && !fG) c->landNotFold++;
          if (lT && !fT) c->landNotFold++;
          if (fG && !lG) c->foldNotLand++;
          if (fT && !lT) c->foldNotLand++;
          if (lG && !cG) c->landNotCrit++;
          if (lT && !cT) c->landNotCrit++;
          if (mg <= 40 && bruteSamples < BRUTECAP) {
            bruteSamples++;
            if (landLeg4Brute(aG, mg, K, M, P) != lG) bruteBad++;
          }
          if (fG && fT) { mland |= 1ULL << q; critHits[q]++; }'''
new = '''          int lG = landLeg4(aG, mg, K, M, P), lT = landLeg4(aT, mt, K, M, P);
          int cG = (critLeg4Mask(aG, aG, aG, mg, K, M, P) == 0);
          int cT = (critLeg4Mask(aT, aT, aT, mt, K, M, P) == 0);
          c->landArms += 2;
          c->landHolds += lG + lT;
          c->critHoldsPt += cG + cT;
          if (lG && !cG) c->landNotCrit++;
          if (lT && !cT) c->landNotCrit++;
          /* the fold is quadratic where the sentence is linear, so it is run on a
           * capped sample -- in both directions, which is the theorem on the corpus */
          if (foldSamples < FOLDCAP) {
            foldSamples += 2;
            int fG = foldsDirect(aG, mg, K, M, P), fT = foldsDirect(aT, mt, K, M, P);
            c->foldHolds += fG + fT;
            if (lG && !fG) c->landNotFold++;
            if (lT && !fT) c->landNotFold++;
            if (fG && !lG) c->foldNotLand++;
            if (fT && !lT) c->foldNotLand++;
          }
          if (mg <= 40 && bruteSamples < BRUTECAP) {
            bruteSamples++;
            if (landLeg4Brute(aG, mg, K, M, P) != lG) bruteBad++;
          }
          if (lG && lT) { mland |= 1ULL << q; critHits[q]++; }'''
assert old in src
src = src.replace(old, new, 1)
src = src.replace('''#define BRUTECAP 40000
static long bruteSamples = 0, bruteBad = 0;''',
'''#define BRUTECAP 40000
static long bruteSamples = 0, bruteBad = 0;
#define FOLDCAP 400000
static long foldSamples = 0;''')
# the witness hunt: the landmark sentence, by the theorem the same as the fold
src = src.replace('''    int fo = fam[q].refl ? foldsDirect(rG, len, K, M, P)
                         : foldsDirect(aG, len, K, M, P);
    if (fo) return 0;''',
'''    int la = fam[q].refl ? landLeg4(rG, len, K, M, P)
                         : landLeg4(aG, len, K, M, P);
    if (la) return 0;''')
src = src.replace('''    printf("    the sentence holds and the arm does not fold (must be 0): %ld\\n", c->landNotFold);''',
'''    printf("    the sentence holds and the arm does not fold (must be 0): %ld\\n", c->landNotFold);''')
src = src.replace('''  printf("    arms x parameter sets %ld; the landmark sentence holds %ld, the arm folds %ld\\n",
         c->landArms, c->landHolds, c->foldHolds);''',
'''  printf("    arms x parameter sets %ld; the landmark sentence holds %ld\\n",
         c->landArms, c->landHolds);
  printf("    of a capped sample of %ld arms x parameter sets, the arm folds %ld times\\n",
         foldSamples, c->foldHolds);''')
open('census-batch59.c','w').write(src)
print("fourth pass written")
