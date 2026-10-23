/* probe64.c -- batch 64, question 4.
 *
 * The same search as probe63.c, restricted to the walks the corrected statement
 * `LandWalkPSuffices` (HPC/Fold/LandWalkFail.lean) is about -- those with **no
 * unit leg**, `NoUnitLeg s ts` -- and run over a wider range of walks.  A hit is
 * a counterexample to `LandWalkPSuffices`; the batch-63 refutation
 * `not_landWalkP_suffices_without_noUnitLeg` shows there are hits as soon as the
 * restriction is dropped.
 *
 * usage: probe64 [maxTurns] [maxLevel] [maxArm] [minLeg]
 *
 * ---- the header of probe63.c follows ----
 *
 * probe63.c -- batch 63, question 4.
 *
 * Is `LandWalkSuffices` (HPC/Fold/LandWalkSuff.lean) true as stated -- for a
 * walk of *any* shape?  The statement is
 *
 *   for every m > 0, every 1-Lipschitz arm f : Fin m -> Z with |f 0 - s| <= 1
 *   every one of whose levels some time of walkList s ts serves,
 *      LandWalk f s ts  ->  FoldsOnto f (walkLen s ts) (walkList s ts).
 *
 * This program enumerates small walks and all arms over them and tests the
 * implication, with every predicate evaluated *by its own definition*:
 *
 *   walkList / walkLen / walkStop / walkLevel  -- the recursions of LandList.lean;
 *   LandWalk   -- for every turn r and every time d of the arm whose level is
 *                 served only by the walk's times walkStop r and later, the
 *                 existence of a landmark chain j 0 <= ... <= j r = d with
 *                 j (u+1) >= j u + (walkStop (u+1) - walkStop u) and
 *                 |f (j u) - walkLevel u| <= 1 for u < r.  Existence is decided
 *                 by the backwards greedy, which is optimal: taking each
 *                 landmark as late as possible is best for all earlier ones.
 *   FoldsOnto  -- reachability over the positions of the walk: beta 0 = 0,
 *                 |beta (j+1) - beta j| <= 1, beta j < walkLen,
 *                 |f j - walkList (beta j)| <= 1.
 *
 * A hit is a counterexample to LandWalkSuffices.
 *
 * usage: probe63 [maxTurns] [maxLevel] [maxArm]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXW 64      /* times of the walk            */
#define MAXT 8       /* turning levels               */
#define MAXM 256     /* times of the arm (raised for the deep descents of batch 65) */

/* ---- the walk ------------------------------------------------------- */

typedef struct {
  int s;
  int nt;
  int t[MAXT];
  int len;            /* walkLen                      */
  int lv[MAXW];       /* walkList p, p < len          */
  int stop[MAXT + 2]; /* walkStop k, k <= nt          */
  int level[MAXT + 2];/* walkLevel k, k <= nt         */
} Walk;

static int build_walk(Walk *w, int s, int nt, const int *t) {
  int cur = s, i, p = 0;
  w->s = s; w->nt = nt;
  for (i = 0; i < nt; i++) w->t[i] = t[i];
  w->lv[p++] = cur;
  w->stop[0] = 0; w->level[0] = s;
  for (i = 0; i < nt; i++) {
    int tgt = t[i];
    while (cur != tgt) {
      cur += (tgt > cur) ? 1 : -1;
      if (p >= MAXW) return 0;
      w->lv[p++] = cur;
    }
    w->stop[i + 1] = p - 1;
    w->level[i + 1] = cur;
  }
  w->len = p;             /* walkLen = sum |diffs| + 1 */
  return 1;
}

/* ---- the arm -------------------------------------------------------- */

static int served_by(const Walk *w, int v, int p) {
  int d = v - w->lv[p];
  return (d <= 1 && d >= -1);
}

/* every level of the arm is served by some time of the walk */
static int band_ok(const Walk *w, const int *f, int m) {
  int j, p, ok;
  for (j = 0; j < m; j++) {
    ok = 0;
    for (p = 0; p < w->len; p++) if (served_by(w, f[j], p)) { ok = 1; break; }
    if (!ok) return 0;
  }
  return 1;
}

/* FoldsOnto f (walkLen s ts) (walkList s ts) */
static int folds(const Walk *w, const int *f, int m) {
  static char reach[2][MAXW];
  int cur = 0, j, p, q, any;
  memset(reach[0], 0, sizeof(reach[0]));
  if (!served_by(w, f[0], 0)) return 0;
  reach[0][0] = 1;
  for (j = 1; j < m; j++) {
    memset(reach[1 - cur], 0, MAXW);
    any = 0;
    for (p = 0; p < w->len; p++) {
      if (!reach[cur][p]) continue;
      for (q = p - 1; q <= p + 1; q++) {
        if (q < 0 || q >= w->len) continue;
        if (!served_by(w, f[j], q)) continue;
        reach[1 - cur][q] = 1; any = 1;
      }
    }
    if (!any) return 0;
    cur = 1 - cur;
  }
  return 1;
}

/* the trigger of clause r at the time d: every time of the walk that serves
   f d is walkStop r or later */
static int trigger(const Walk *w, const int *f, int d, int r) {
  int p;
  for (p = 0; p < w->len; p++)
    if (served_by(w, f[d], p) && p < w->stop[r]) return 0;
  return 1;
}

/* existence of the landmark chain of clause r ending at d, by the backwards
   greedy */
static int chain(const Walk *w, const int *f, int d, int r) {
  int cur = d, u, gap, j, found;
  for (u = r - 1; u >= 0; u--) {
    gap = w->stop[u + 1] - w->stop[u];
    found = -1;
    for (j = cur - gap; j >= 0; j--) {
      int diff = f[j] - w->level[u];
      if (diff <= 1 && diff >= -1) { found = j; break; }
    }
    if (found < 0) return 0;
    cur = found;
  }
  return (cur >= w->stop[0]);
}

static int landwalk(const Walk *w, const int *f, int m) {
  int r, d;
  for (r = 0; r <= w->nt; r++)
    for (d = 0; d < m; d++)
      if (trigger(w, f, d, r) && !chain(w, f, d, r)) return 0;
  return 1;
}

/* ---- the corrected sentence ----------------------------------------
 * The trigger is read at the *level*: P is the earliest time of the walk that
 * serves f d, and the last gap of the chain is P - walkStop r, the walk's own
 * distance from its r-th turn to that time.  The landmark at index r is a time
 * of the arm at walkLevel r, not d itself.  This is `foldsOnto_landmarkN`
 * applied to the chain walkStop 0 <= ... <= walkStop r <= P, so it is still
 * necessary for folding.
 */

static int min_serve(const Walk *w, const int *f, int d) {
  int p;
  for (p = 0; p < w->len; p++) if (served_by(w, f[d], p)) return p;
  return -1;
}

static int chainP(const Walk *w, const int *f, int d, int r, int P) {
  int cur, u, gap, j, found;
  /* the r-th landmark: at walkLevel r, at least P - walkStop r before d */
  cur = -1;
  for (j = d - (P - w->stop[r]); j >= 0; j--) {
    int diff = f[j] - w->level[r];
    if (diff <= 1 && diff >= -1) { cur = j; break; }
  }
  if (cur < 0) return 0;
  for (u = r - 1; u >= 0; u--) {
    gap = w->stop[u + 1] - w->stop[u];
    found = -1;
    for (j = cur - gap; j >= 0; j--) {
      int diff = f[j] - w->level[u];
      if (diff <= 1 && diff >= -1) { found = j; break; }
    }
    if (found < 0) return 0;
    cur = found;
  }
  return 1;
}

static int landwalkP(const Walk *w, const int *f, int m) {
  int r, d, P;
  for (d = 0; d < m; d++) {
    P = min_serve(w, f, d);
    if (P < 0) return 0;
    for (r = 0; r <= w->nt; r++)
      if (w->stop[r] <= P && !chainP(w, f, d, r, P)) return 0;
  }
  return 1;
}

/* ---- the search ----------------------------------------------------- */

static long long tested = 0, hits = 0;
static int found_this_walk = 0;
static long long walks_bad[MAXW];   /* walks with a counterexample, by min leg */
static long long walks_all[MAXW];

static int min_leg(const Walk *w) {
  int i, mn = 1 << 20;
  for (i = 0; i < w->nt; i++) {
    int g = w->stop[i + 1] - w->stop[i];
    if (g < mn) mn = g;
  }
  return mn;
}

static void report(const Walk *w, const int *f, int m) {
  int i;
  hits++;
  printf("COUNTEREXAMPLE  minleg=%d  s=%d  ts=[", min_leg(w), w->s);
  for (i = 0; i < w->nt; i++) printf("%d%s", w->t[i], i + 1 < w->nt ? "," : "");
  printf("]  walkLen=%d  walk=", w->len);
  for (i = 0; i < w->len; i++) printf("%d", w->lv[i]);
  printf("  m=%d  arm=", m);
  for (i = 0; i < m; i++) printf("%d", f[i]);
  printf("\n");
  fflush(stdout);
}

/* ---- batch 65: a randomised deep search ------------------------------
 *
 * The exhaustive search of probe64 reaches arms of fourteen times; the rule
 * of the batch-65 commission asks, before a sufficiency statement is written,
 * for a probe covering arms of at least twice the walk's length, which for a
 * walk of four turns with levels in [0,6] is about fifty times -- out of reach
 * of an exhaustive sweep (3^50 arms).  This probe therefore searches deep
 * rather than wide: for each walk whose shortest leg is at least the given
 * bound it runs randomised depth-first descents to the given arm length, with
 * the two prefix-monotone prunings the exhaustive search uses --
 *
 *   band_ok   : every level of the arm is served by the walk somewhere;
 *   landwalkP : a trigger unmet at a time d stays unmet, since the chain the
 *               sentence asks for lies entirely before d.
 *
 * so a prefix that fails either can be abandoned.  It reports, for each walk,
 * how deep the descents actually reached, and any counterexample found.
 *
 * It is a sample and not a sweep, and is reported as such. */

static long long rtested = 0, rhits = 0;
static int deepest = 0;

static int rrec(const Walk *w, int *f, int m, int maxm, long long *budget) {
  int ord[3], k, i;
  if (*budget <= 0) return 0;
  (*budget)--;
  if (m > deepest) deepest = m;
  if (m >= 1) {
    rtested++;
    if (!band_ok(w, f, m)) return 0;
    if (!landwalkP(w, f, m)) return 0;
    if (!folds(w, f, m)) {
      rhits++;
      report(w, f, m);
      return 1;
    }
  }
  if (m == maxm) return 0;
  ord[0] = -1; ord[1] = 0; ord[2] = 1;
  for (i = 2; i > 0; i--) { k = random() % (i + 1); int tmp = ord[i]; ord[i] = ord[k]; ord[k] = tmp; }
  for (i = 0; i < 3; i++) {
    f[m] = f[m - 1] + ord[i];
    if (rrec(w, f, m + 1, maxm, budget)) return 1;
  }
  return 0;
}

int main(int argc, char **argv) {
  int maxTurns = (argc > 1) ? atoi(argv[1]) : 4;
  int maxLevel = (argc > 2) ? atoi(argv[2]) : 6;
  int maxArm   = (argc > 3) ? atoi(argv[3]) : 30;
  int minLeg   = (argc > 4) ? atoi(argv[4]) : 3;
  long long bud = (argc > 5) ? atoll(argv[5]) : 2000000;
  unsigned seed = (argc > 6) ? (unsigned)atoi(argv[6]) : 65u;
  int nt, code, i, v0, s;
  int t[MAXT], f[MAXM];
  Walk w;
  long long nwalks = 0;
  srandom(seed);

  printf("probe65b: the corrected sentence (level-aware trigger), randomised deep descents.\n");
  printf("  walks of up to %d turns, levels in [0,%d], shortest leg at least %d;\n"
         "  arms of up to %d times; %lld nodes per walk; seed %u\n",
         maxTurns, maxLevel, minLeg, maxArm, bud, seed);

  for (s = 0; s <= maxLevel; s++)
  for (nt = 1; nt <= maxTurns; nt++) {
    long long total = 1;
    for (i = 0; i < nt; i++) total *= (maxLevel + 1);
    for (code = 0; code < total; code++) {
      long long c = code;
      int prev = s, bad = 0;
      for (i = 0; i < nt; i++) { t[i] = (int)(c % (maxLevel + 1)); c /= (maxLevel + 1); }
      for (i = 0; i < nt; i++) {
        if (t[i] == prev) { bad = 1; break; }
        if (i >= 1 && ((t[i] > t[i-1]) == (t[i-1] > (i >= 2 ? t[i-2] : s)))) { bad = 1; break; }
        prev = t[i];
      }
      if (bad) continue;
      if (!build_walk(&w, s, nt, t)) continue;
      if (min_leg(&w) < minLeg) continue;
      nwalks++;
      long long budget = bud;
      for (v0 = s - 1; v0 <= s + 1; v0++) {
        f[0] = v0;
        if (rrec(&w, f, 1, maxArm, &budget)) break;
      }
    }
  }
  printf("walks %lld   arms tested %lld   counterexamples %lld   deepest prefix reached %d\n",
         nwalks, rtested, rhits, deepest);
  return 0;
}
