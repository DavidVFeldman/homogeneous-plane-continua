/* Census for batch 34 -- the outside-in induction step (COMMISSION-batch34 section 1).
 *
 * Conventions are batches 28-33's.  An itinerary is a base centre ts[0]
 * followed by turning targets ts[1..k], all in [L+1, H-1], directions
 * alternating, amplitudes strictly increasing after the first (the free
 * family `IsZigFree`), the last two targets being the two extreme bands in
 * either order.  The walk is one level per step through those targets.  A
 * sequence f folds onto a walk iff there is a 1-Lipschitz time assignment
 * starting at time 0 with every level within one of its time's centre; that
 * is decided exactly by reachability over the walk's times (a bitmask sweep).
 *
 * The gate.  For each basepoint i of `bing 0 n` whose level is interior
 * (L+3 <= rho i <= H-3) we take trimmed stretches [a,b] containing i, with
 * their own band [L',H'], and ask:
 *
 *    (existence) some member of the free family of [L',H'] folds both arms
 *                of the stretch at i;
 *    (every)     every such member extends -- by appending the two outer
 *                legs L+1, H-1 in one order or the other -- to a walk
 *                folding both arms of the whole chain at i.
 *
 * Three trims are measured:
 *    G1  the greedy left-first maximal stretch of span <= H-L-1 (batch 33's),
 *    G2  the greedy right-first one,
 *    IN  the maximal stretch containing i that avoids both extreme levels,
 *        whose band therefore lies inside [L+1, H-1].
 *
 * and two forms of the extension test:
 *    EITHER    some order of the two appended legs folds the whole arms
 *              (the form COMMISSION-batch34 section 1 states);
 *    ORIENTED  the order dictated by the inner member's last target folds
 *              them -- append (L+1, H-1) if the inner member ends high and
 *              (H-1, L+1) if it ends low.  This is the only order that can
 *              make the extension a member of the free family of [L,H]
 *              (`isZigFree_append_outer`), so it is the one the induction
 *              needs; the program also checks the extension's membership
 *              directly.
 *
 * Sections:
 *   1. the gate at spans 6..12.
 *   2. the greedy-trim question: which trims work, and whether the choice
 *      between the two greedy orders is ever needed.
 *   3. a worked trace.
 *
 * Usage: census-batch34 [maxspan]
 */

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 u128;

/* ------------------------------------------------------------ bing chains */

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

/* ---------------------------------------------------------- the walks */

#define MAXW 120
#define MAXTS 32

typedef struct {
  int k;               /* number of turning targets after the base centre */
  int ts[MAXTS];
  int len;
  signed char w[MAXW];
} Walk;

static Walk *walks = NULL;
static int nwalks = 0, capwalks = 0;
static int ts[MAXTS];
static int bandL, bandH;

static void walk_of(const int *t, int k, signed char *w, int *lenout) {
  int len = 0;
  w[len++] = (signed char)t[0];
  for (int j = 1; j <= k; j++) {
    if (t[j] == t[j - 1]) continue;
    int d = t[j] > t[j - 1] ? 1 : -1;
    for (int x = t[j - 1] + d;; x += d) {
      if (len >= MAXW) { fprintf(stderr, "walk overflow\n"); exit(1); }
      w[len++] = (signed char)x;
      if (x == t[j]) break;
    }
  }
  *lenout = len;
}

static void push_walk(int k) {
  if (nwalks == capwalks) {
    capwalks = capwalks ? capwalks * 2 : 1024;
    walks = (Walk *)realloc(walks, sizeof(Walk) * capwalks);
  }
  Walk *W = &walks[nwalks++];
  W->k = k;
  for (int j = 0; j <= k; j++) W->ts[j] = ts[j];
  walk_of(W->ts, k, W->w, &W->len);
}

static void dfs(int j, int k, int lastamp, int lastdir) {
  if (j == k) {
    int a = ts[j - 1], b = ts[j];
    if ((a == bandL + 1 && b == bandH - 1) || (a == bandH - 1 && b == bandL + 1))
      push_walk(k);
    return;
  }
  int cur = ts[j];
  int minamp = (j <= 1) ? 1 : lastamp + 1;
  for (int dir = -1; dir <= 1; dir += 2) {
    if (lastdir != 0 && dir == lastdir) continue;
    for (int amp = minamp;; amp++) {
      int nxt = cur + dir * amp;
      if (nxt < bandL + 1 || nxt > bandH - 1) break;
      ts[j + 1] = nxt;
      dfs(j + 1, k, amp, dir);
    }
  }
}

/* the whole free family of the band [L,H] */
static void enumerate_family(int L, int H, int kmax) {
  bandL = L; bandH = H; nwalks = 0;
  if (H - L < 3) return;
  for (int k = 2; k <= kmax; k++)
    for (int c = L + 1; c <= H - 1; c++) { ts[0] = c; dfs(0, k, 0, 0); }
}

/* is the target list t[0..k] a member of the free family of [L,H]? */
static int is_zigfree(const int *t, int k, int L, int H) {
  if (k + 1 < 3) return 0;
  for (int j = 0; j <= k; j++) if (t[j] < L + 1 || t[j] > H - 1) return 0;
  for (int j = 0; j + 2 <= k; j++) {
    long d1 = t[j + 1] - t[j], d2 = t[j + 2] - t[j + 1];
    if (d1 * d2 >= 0) return 0;
    if (j >= 1) {
      long a1 = d1 < 0 ? -d1 : d1, a2 = d2 < 0 ? -d2 : d2;
      if (!(a1 < a2)) return 0;
    }
  }
  int p = t[k - 1], q = t[k];
  if (!((p == L + 1 && q == H - 1) || (p == H - 1 && q == L + 1))) return 0;
  return 1;
}

/* ------------------------------------------------------------- folding */

/* allow[v] = the set of times whose centre is within one of level v,
   for v in [vlo, vhi]; the table is indexed by v - vlo. */
static void allow_table(const signed char *w, int len, int vlo, int vhi, u128 *tab) {
  u128 one = 1;
  for (int v = vlo; v <= vhi; v++) {
    u128 m = 0;
    for (int u = 0; u < len; u++) { int d = v - w[u]; if (d <= 1 && d >= -1) m |= one << u; }
    tab[v - vlo] = m;
  }
}

/* Backward sweep over r[lo..hi]: out[k] = 1 iff the forward arm from k
   (that is r[k], r[k+1], ..., r[hi]) folds onto the walk, its first link
   pinned to time 0. */
static void sweep_fwdarm(const int *r, int lo, int hi, int len, int vlo,
                         const u128 *tab, unsigned char *out) {
  u128 one = 1;
  u128 full = (len >= 128) ? ~(u128)0 : ((one << len) - 1);
  u128 B = tab[r[hi] - vlo];
  out[hi] = (B & one) != 0;
  for (int k = hi - 1; k >= lo; k--) {
    B = tab[r[k] - vlo] & (((B << 1) | B | (B >> 1)) & full);
    out[k] = (B & one) != 0;
  }
}

/* Forward sweep over r[lo..hi]: out[k] = 1 iff the backward arm from k
   (that is r[k], r[k-1], ..., r[lo]) folds onto the walk. */
static void sweep_bwdarm(const int *r, int lo, int hi, int len, int vlo,
                         const u128 *tab, unsigned char *out) {
  u128 one = 1;
  u128 full = (len >= 128) ? ~(u128)0 : ((one << len) - 1);
  u128 F = tab[r[lo] - vlo];
  out[lo] = (F & one) != 0;
  for (int k = lo + 1; k <= hi; k++) {
    F = tab[r[k] - vlo] & (((F << 1) | F | (F >> 1)) & full);
    out[k] = (F & one) != 0;
  }
}

/* --------------------------------------------------------------- trims */

/* greedy maximal stretch containing i of span at most cap; two orders */
static void trim_greedy(const int *r, int lo, int hi, int i, int cap, int leftfirst,
                        int *ao, int *bo) {
  int a = i, b = i, mn = r[i], mx = r[i];
  for (int pass = 0; pass < 2; pass++) {
    int left = leftfirst ? (pass == 0) : (pass == 1);
    if (left) {
      while (a > lo) {
        int nm = mn < r[a - 1] ? mn : r[a - 1];
        int nx = mx > r[a - 1] ? mx : r[a - 1];
        if (nx - nm > cap) break;
        a--; mn = nm; mx = nx;
      }
    } else {
      while (b < hi) {
        int nm = mn < r[b + 1] ? mn : r[b + 1];
        int nx = mx > r[b + 1] ? mx : r[b + 1];
        if (nx - nm > cap) break;
        b++; mn = nm; mx = nx;
      }
    }
  }
  *ao = a; *bo = b;
}

/* the maximal stretch containing i that avoids the levels L and H */
static void trim_inner(const int *r, int lo, int hi, int i, int L, int H,
                       int *ao, int *bo) {
  int a = i, b = i;
  if (r[i] == L || r[i] == H) { *ao = i; *bo = i; return; }
  while (a > lo && r[a - 1] != L && r[a - 1] != H) a--;
  while (b < hi && r[b + 1] != L && r[b + 1] != H) b++;
  *ao = a; *bo = b;
}

static void band_of(const int *r, int a, int b, int *L, int *H) {
  int mn = r[a], mx = r[a];
  for (int q = a; q <= b; q++) { if (r[q] < mn) mn = r[q]; if (r[q] > mx) mx = r[q]; }
  *L = mn; *H = mx;
}

/* ------------------------------------------------- the gate, one trim */

typedef struct {
  int nserved;      /* basepoints with at least one inner-serving member */
  int okeither;     /* basepoints passing the EITHER form */
  int okoriented;   /* basepoints passing the ORIENTED form */
  int firstfail;    /* a basepoint failing the ORIENTED form, or -1 */
  int firstfailw;   /* the index of an inner member that does not extend */
} TrimStat;

/* Work buffers, sized to the chain. */
static unsigned char *bufIG, *bufIT, *bufEG[2], *bufET[2];
static int *cntServe, *cntBadE, *cntBadO, *badW;

/* Run the gate for the single trim [a,b] and report, for every basepoint i
   in [a,b] with pred[i], whether the trim passes.  Results are accumulated
   into cntServe / cntBadE / cntBadO, which the caller must clear. */
static void gate_trim(const int *r, int n, int a, int b, int L, int H,
                      int Lp, int Hp, int *nmembers, int *notzf) {
  int vlo = L - 2, vhi = H + 2;
  static u128 tab[64];
  enumerate_family(Lp, Hp, MAXTS - 2);
  *nmembers = nwalks;
  *notzf = 0;
  for (int wi = 0; wi < nwalks; wi++) {
    Walk *W = &walks[wi];
    allow_table(W->w, W->len, vlo, vhi, tab);
    sweep_fwdarm(r, a, b, W->len, vlo, tab, bufIG);
    sweep_bwdarm(r, a, b, W->len, vlo, tab, bufIT);
    /* does this member serve any basepoint of the stretch? */
    int any = 0;
    for (int i = a; i <= b; i++) if (bufIG[i] && bufIT[i]) { any = 1; break; }
    if (!any) continue;
    /* the two extensions */
    int t2[MAXTS + 2];
    int ext[2][MAXTS + 2], extk[2];
    for (int j = 0; j <= W->k; j++) t2[j] = W->ts[j];
    for (int e = 0; e < 2; e++) {
      for (int j = 0; j <= W->k; j++) ext[e][j] = t2[j];
      ext[e][W->k + 1] = e == 0 ? L + 1 : H - 1;
      ext[e][W->k + 2] = e == 0 ? H - 1 : L + 1;
      extk[e] = W->k + 2;
    }
    int oriented = (W->ts[W->k] == Hp - 1) ? 0 : 1;
    if (!is_zigfree(ext[0], extk[0], L, H) && !is_zigfree(ext[1], extk[1], L, H)) (*notzf)++;
    for (int e = 0; e < 2; e++) {
      signed char ww[MAXW]; int llen;
      walk_of(ext[e], extk[e], ww, &llen);
      allow_table(ww, llen, vlo, vhi, tab);
      sweep_fwdarm(r, 0, n - 1, llen, vlo, tab, bufEG[e]);
      sweep_bwdarm(r, 0, n - 1, llen, vlo, tab, bufET[e]);
    }
    for (int i = a; i <= b; i++) {
      if (!(bufIG[i] && bufIT[i])) continue;
      cntServe[i]++;
      int o1 = bufEG[0][i] && bufET[0][i];
      int o2 = bufEG[1][i] && bufET[1][i];
      int oo = oriented == 0 ? o1 : o2;
      if (!(o1 || o2)) cntBadE[i]++;
      if (!oo) { if (!cntBadO[i]) badW[i] = wi; cntBadO[i]++; }
    }
  }
}

/* ============================================================ section 1 */

static void print_ts_list(const int *t, int k) {
  printf("[");
  for (int j = 0; j <= k; j++) printf("%s%d", j ? ", " : "", t[j]);
  printf("]");
}

static void section1(int maxspan) {
  printf("\n===== 1. the gate: ExtendStep at every interior basepoint =====\n");
  printf("  trims: G1 greedy left-first (span <= H-L-1), G2 greedy right-first,\n"
         "         IN the maximal stretch avoiding both extreme levels.\n"
         "  forms: E some order of the appended legs folds the whole arms,\n"
         "         O the order dictated by the inner member's end does.\n");
  for (int nn = 6; nn <= maxspan; nn++) {
    Path p = bpath(0, nn);
    int n = p.n, L = 0, H = nn;
    bufIG = (unsigned char *)calloc(n, 1);
    bufIT = (unsigned char *)calloc(n, 1);
    for (int e = 0; e < 2; e++) {
      bufEG[e] = (unsigned char *)calloc(n, 1);
      bufET[e] = (unsigned char *)calloc(n, 1);
    }
    cntServe = (int *)calloc(n, sizeof(int));
    cntBadE = (int *)calloc(n, sizeof(int));
    cntBadO = (int *)calloc(n, sizeof(int));
    badW = (int *)calloc(n, sizeof(int));

    /* the distinct trims, and which basepoints use each */
    typedef struct { int a, b, Lp, Hp; } Tr;
    Tr trs[3 * 8];
    int ntr = 0;
    int *use[3];
    for (int g = 0; g < 3; g++) use[g] = (int *)malloc(sizeof(int) * n);
    int ninterior = 0;
    for (int i = 0; i < n; i++) {
      for (int g = 0; g < 3; g++) use[g][i] = -1;
      if (!(p.v[i] >= L + 3 && p.v[i] <= H - 3)) continue;
      ninterior++;
      for (int g = 0; g < 3; g++) {
        int a, b;
        if (g == 0) trim_greedy(p.v, 0, n - 1, i, H - L - 1, 1, &a, &b);
        else if (g == 1) trim_greedy(p.v, 0, n - 1, i, H - L - 1, 0, &a, &b);
        else trim_inner(p.v, 0, n - 1, i, L, H, &a, &b);
        int Lp, Hp; band_of(p.v, a, b, &Lp, &Hp);
        int f = -1;
        for (int q = 0; q < ntr; q++) if (trs[q].a == a && trs[q].b == b) { f = q; break; }
        if (f < 0) {
          if (ntr >= 24) { fprintf(stderr, "too many trims\n"); exit(1); }
          trs[ntr].a = a; trs[ntr].b = b; trs[ntr].Lp = Lp; trs[ntr].Hp = Hp;
          f = ntr++;
        }
        use[g][i] = f;
      }
    }
    /* run the gate once per distinct trim */
    int passE[24], passO[24], servedT[24], members[24], notzf[24];
    int *failbp = (int *)malloc(sizeof(int) * 24);
    int *failw = (int *)malloc(sizeof(int) * 24);
    unsigned char **okE = (unsigned char **)malloc(sizeof(void *) * ntr);
    unsigned char **okO = (unsigned char **)malloc(sizeof(void *) * ntr);
    for (int q = 0; q < ntr; q++) {
      okE[q] = (unsigned char *)calloc(n, 1);
      okO[q] = (unsigned char *)calloc(n, 1);
      memset(cntServe, 0, sizeof(int) * n);
      memset(cntBadE, 0, sizeof(int) * n);
      memset(cntBadO, 0, sizeof(int) * n);
      gate_trim(p.v, n, trs[q].a, trs[q].b, L, H, trs[q].Lp, trs[q].Hp,
                &members[q], &notzf[q]);
      passE[q] = passO[q] = servedT[q] = 0;
      failbp[q] = failw[q] = -1;
      for (int i = trs[q].a; i <= trs[q].b; i++) {
        if (!(p.v[i] >= L + 3 && p.v[i] <= H - 3)) continue;
        if (cntServe[i] > 0) servedT[q]++;
        okE[q][i] = (cntServe[i] > 0 && cntBadE[i] == 0);
        okO[q][i] = (cntServe[i] > 0 && cntBadO[i] == 0);
        passE[q] += okE[q][i];
        passO[q] += okO[q][i];
        if (!okO[q][i] && failbp[q] < 0 && cntServe[i] > 0) {
          failbp[q] = i; failw[q] = badW[i];
        }
      }
    }
    /* per basepoint: does some trim pass? */
    int failE = 0, failO = 0, firstfailE = -1, firstfailO = -1;
    int g1E = 0, g1O = 0, g2E = 0, g2O = 0, inE = 0, inO = 0, needchoice = 0;
    int g12E = 0, g12O = 0;
    for (int i = 0; i < n; i++) {
      if (!(p.v[i] >= L + 3 && p.v[i] <= H - 3)) continue;
      int e = 0, o = 0;
      int eg[3], og[3];
      for (int g = 0; g < 3; g++) {
        int q = use[g][i];
        eg[g] = okE[q][i]; og[g] = okO[q][i];
        e |= eg[g]; o |= og[g];
      }
      g1E += eg[0]; g1O += og[0];
      g2E += eg[1]; g2O += og[1];
      inE += eg[2]; inO += og[2];
      if (eg[0] != eg[1] || og[0] != og[1]) needchoice++;
      g12E += (eg[0] || eg[1]); g12O += (og[0] || og[1]);
      if (!e) { failE++; if (firstfailE < 0) firstfailE = i; }
      if (!o) { failO++; if (firstfailO < 0) firstfailO = i; }
    }
    printf("\n  span %2d: %d links, %d interior basepoints, %d distinct trims\n",
           nn, n, ninterior, ntr);
    for (int q = 0; q < ntr; q++)
      printf("    trim [%d,%d] band [%d,%d] span %d: %d family members, "
             "%d interior basepoints served, E ok %d, O ok %d%s\n",
             trs[q].a, trs[q].b, trs[q].Lp, trs[q].Hp, trs[q].Hp - trs[q].Lp,
             members[q], servedT[q], passE[q], passO[q],
             notzf[q] ? "  [NO extension of any used member is a family member of [L,H]]" : "");
    printf("    passing with G1 only: E %d/%d, O %d/%d\n", g1E, ninterior, g1O, ninterior);
    printf("    passing with G2 only: E %d/%d, O %d/%d\n", g2E, ninterior, g2O, ninterior);
    printf("    passing with IN only: E %d/%d, O %d/%d\n", inE, ninterior, inO, ninterior);
    printf("    passing with G1 or G2: E %d/%d, O %d/%d\n", g12E, ninterior, g12O, ninterior);
    printf("    the two greedy orders give different verdicts at %d basepoints\n", needchoice);
    printf("    FAILURES of the gate (some trim must pass): E %d, O %d\n", failE, failO);
    if (firstfailE >= 0) printf("    first EITHER failure at basepoint %d (level %d)\n",
                                firstfailE, p.v[firstfailE]);
    if (firstfailO >= 0) {
      int i = firstfailO;
      printf("    first ORIENTED failure at basepoint %d (level %d)\n", i, p.v[i]);
      for (int g = 0; g < 3; g++) {
        int q = use[g][i];
        printf("      trim %s = [%d,%d] band [%d,%d]\n", g == 0 ? "G1" : g == 1 ? "G2" : "IN",
               trs[q].a, trs[q].b, trs[q].Lp, trs[q].Hp);
      }
    }
    for (int q = 0; q < ntr; q++)
      if (failbp[q] >= 0 && failw[q] >= 0) {
        printf("    trim [%d,%d]: basepoint %d has an inner member that does not extend: ",
               trs[q].a, trs[q].b, failbp[q]);
        /* re-enumerate to name the member */
        enumerate_family(trs[q].Lp, trs[q].Hp, MAXTS - 2);
        if (failw[q] < nwalks) print_ts_list(walks[failw[q]].ts, walks[failw[q]].k);
        printf("\n");
      }
    for (int q = 0; q < ntr; q++) { free(okE[q]); free(okO[q]); }
    free(okE); free(okO); free(failbp); free(failw);
    for (int g = 0; g < 3; g++) free(use[g]);
    free(bufIG); free(bufIT);
    for (int e = 0; e < 2; e++) { free(bufEG[e]); free(bufET[e]); }
    free(cntServe); free(cntBadE); free(cntBadO); free(badW);
    free(p.v);
    fflush(stdout);
  }
}

/* ========================================================== section 1b */

/* The gate in the form the induction needs: the trim's band must lie inside
   [L+1, H-1] -- only then is the oriented extension a member of the free
   family of [L,H] -- and the trim may be any maximal stretch of any such
   band, not only the one avoiding the two extreme levels.  For every such
   band we take the maximal stretches (runs) whose band is exactly it. */
static void section1b(int maxspan) {
  printf("\n===== 1b. the gate over all inner trims (band inside [L+1,H-1]) =====\n");
  printf("  For each basepoint: is there a band [L',H'] with L+1 <= L', H' <= H-1\n"
         "  and a maximal stretch of that band containing the basepoint, such that\n"
         "  some member of the band's free family folds both inner arms and every\n"
         "  such member's oriented extension folds both whole arms?\n");
  for (int nn = 6; nn <= maxspan; nn++) {
    Path p = bpath(0, nn);
    int n = p.n, L = 0, H = nn;
    unsigned char *okall = (unsigned char *)calloc(n, 1);
    unsigned char *oksome = (unsigned char *)calloc(n, 1);
    unsigned char *okin = (unsigned char *)calloc(n, 1);
    int *nbands = (int *)calloc(n, sizeof(int));
    int *firstL = (int *)calloc(n, sizeof(int));
    int *firstH = (int *)calloc(n, sizeof(int));
    int *cntS = (int *)calloc(n, sizeof(int));
    int *cntB = (int *)calloc(n, sizeof(int));
    int *cntG = (int *)calloc(n, sizeof(int));
    int *badw = (int *)calloc(n, sizeof(int));
    int exL = -1, exH = -1, exW = -1, exBP = -1;
    unsigned char *iG = (unsigned char *)calloc(n, 1);
    unsigned char *iT = (unsigned char *)calloc(n, 1);
    unsigned char *eG = (unsigned char *)calloc(n, 1);
    unsigned char *eT = (unsigned char *)calloc(n, 1);
    int ninterior = 0, notzf = 0;
    long long totmembers = 0;
    for (int i = 0; i < n; i++)
      if (p.v[i] >= L + 3 && p.v[i] <= H - 3) ninterior++;
    static u128 tabI[64], tabE[64];
    int vlo = L - 2, vhi = H + 2;
    for (int Lp = L + 1; Lp + 3 <= H - 1; Lp++)
      for (int Hp = Lp + 3; Hp <= H - 1; Hp++) {
        /* the maximal stretches whose band is exactly [Lp,Hp] */
        int nruns = 0;
        static int ra[4096], rb[4096];
        int k = 0;
        while (k < n) {
          if (p.v[k] < Lp || p.v[k] > Hp) { k++; continue; }
          int a = k;
          while (k < n && p.v[k] >= Lp && p.v[k] <= Hp) k++;
          int b = k - 1, mn, mx;
          band_of(p.v, a, b, &mn, &mx);
          if (mn == Lp && mx == Hp) {
            if (nruns >= 4096) { fprintf(stderr, "too many runs\n"); exit(1); }
            ra[nruns] = a; rb[nruns] = b; nruns++;
          }
        }
        if (!nruns) continue;
        enumerate_family(Lp, Hp, MAXTS - 2);
        totmembers += nwalks;
        memset(cntS, 0, sizeof(int) * n);
        memset(cntB, 0, sizeof(int) * n);
        memset(cntG, 0, sizeof(int) * n);
        for (int wi = 0; wi < nwalks; wi++) {
          Walk *W = &walks[wi];
          allow_table(W->w, W->len, vlo, vhi, tabI);
          int any = 0;
          for (int q = 0; q < nruns && !any; q++) {
            sweep_fwdarm(p.v, ra[q], rb[q], W->len, vlo, tabI, iG);
            sweep_bwdarm(p.v, ra[q], rb[q], W->len, vlo, tabI, iT);
            for (int i = ra[q]; i <= rb[q]; i++) if (iG[i] && iT[i]) { any = 1; break; }
          }
          if (!any) continue;
          int ext[MAXTS + 2], extk = W->k + 2;
          for (int j = 0; j <= W->k; j++) ext[j] = W->ts[j];
          if (W->ts[W->k] == Hp - 1) { ext[W->k + 1] = L + 1; ext[W->k + 2] = H - 1; }
          else { ext[W->k + 1] = H - 1; ext[W->k + 2] = L + 1; }
          if (!is_zigfree(ext, extk, L, H)) notzf++;
          signed char ww[MAXW]; int llen;
          walk_of(ext, extk, ww, &llen);
          allow_table(ww, llen, vlo, vhi, tabE);
          sweep_fwdarm(p.v, 0, n - 1, llen, vlo, tabE, eG);
          sweep_bwdarm(p.v, 0, n - 1, llen, vlo, tabE, eT);
          for (int q = 0; q < nruns; q++) {
            sweep_fwdarm(p.v, ra[q], rb[q], W->len, vlo, tabI, iG);
            sweep_bwdarm(p.v, ra[q], rb[q], W->len, vlo, tabI, iT);
            for (int i = ra[q]; i <= rb[q]; i++) {
              if (!(iG[i] && iT[i])) continue;
              cntS[i]++;
              if (eG[i] && eT[i]) cntG[i]++;
              else { if (!cntB[i]) badw[i] = wi; cntB[i]++; }
            }
          }
        }
        for (int i = 0; i < n; i++) {
          if (!(p.v[i] >= L + 3 && p.v[i] <= H - 3)) continue;
          if (cntG[i] > 0) oksome[i] = 1;
          if (cntS[i] > 0 && cntB[i] == 0) {
            if (!okall[i]) { firstL[i] = Lp; firstH[i] = Hp; }
            okall[i] = 1;
            nbands[i]++;
            if (Lp == L + 1 && Hp == H - 1) okin[i] = 1;
          } else if (cntS[i] > 0 && exBP < 0 && Lp == L + 1 && Hp == H - 1) {
            exBP = i; exL = Lp; exH = Hp; exW = badw[i];
          }
        }
      }
    int pass = 0, passin = 0, passsome = 0, minb = 1 << 30, firstfail = -1, firstfails = -1;
    for (int i = 0; i < n; i++) {
      if (!(p.v[i] >= L + 3 && p.v[i] <= H - 3)) continue;
      pass += okall[i]; passin += okin[i]; passsome += oksome[i];
      if (!oksome[i] && firstfails < 0) firstfails = i;
      if (okall[i] && nbands[i] < minb) minb = nbands[i];
      if (!okall[i] && firstfail < 0) firstfail = i;
    }
    printf("  span %2d: %d links, %d interior basepoints, %lld family members swept\n",
           nn, n, ninterior, totmembers);
    printf("           EVERY form, passing with some inner trim: %d/%d   FAILURES %d\n",
           pass, ninterior, ninterior - pass);
    printf("           SOME  form, passing with some inner trim: %d/%d   FAILURES %d\n",
           passsome, ninterior, ninterior - passsome);
    if (firstfails >= 0)
      printf("           FIRST BASEPOINT FAILING THE SOME FORM: %d (level %d)\n",
             firstfails, p.v[firstfails]);
    printf("           passing with the full inner band [L+1,H-1]: %d/%d\n", passin, ninterior);
    printf("           least number of working bands at a passing basepoint: %d\n",
           pass ? minb : 0);
    printf("           oriented extensions that are not members of the free family of [L,H]: %d\n",
           notzf);
    if (firstfail >= 0)
      printf("           FIRST BASEPOINT FAILING THE EVERY FORM: %d (level %d)\n",
             firstfail, p.v[firstfail]);
    if (exBP >= 0) {
      enumerate_family(exL, exH, MAXTS - 2);
      printf("           witness: at basepoint %d (level %d), band [%d,%d], the member ",
             exBP, p.v[exBP], exL, exH);
      if (exW < nwalks) print_ts_list(walks[exW].ts, walks[exW].k);
      printf(" serves both inner arms but its oriented extension does not serve both whole arms\n");
    }
    fflush(stdout);
    free(okall); free(oksome); free(okin); free(nbands); free(firstL); free(firstH);
    free(cntS); free(cntB); free(cntG); free(badw); free(iG); free(iT); free(eG); free(eT);
    free(p.v);
  }
}

/* ============================================================ section 2 */

static void section2(void) {
  printf("\n===== 2. the trims themselves =====\n");
  for (int nn = 6; nn <= 12; nn++) {
    Path p = bpath(0, nn);
    int n = p.n, L = 0, H = nn;
    int differ = 0, innerdiff = 0, innerspan2 = 0, innernotstrict = 0;
    for (int i = 0; i < n; i++) {
      if (!(p.v[i] >= L + 3 && p.v[i] <= H - 3)) continue;
      int a1, b1, a2, b2, a3, b3, L1, H1, L2, H2, L3, H3;
      trim_greedy(p.v, 0, n - 1, i, H - L - 1, 1, &a1, &b1);
      trim_greedy(p.v, 0, n - 1, i, H - L - 1, 0, &a2, &b2);
      trim_inner(p.v, 0, n - 1, i, L, H, &a3, &b3);
      band_of(p.v, a1, b1, &L1, &H1);
      band_of(p.v, a2, b2, &L2, &H2);
      band_of(p.v, a3, b3, &L3, &H3);
      if (a1 != a2 || b1 != b2) differ++;
      if ((a3 != a1 || b3 != b1) && (a3 != a2 || b3 != b2)) innerdiff++;
      if (H3 - L3 != H - L - 2) innerspan2++;
      if (!(L3 == L + 1 && H3 == H - 1)) innernotstrict++;
    }
    printf("  span %2d: %d links; greedy orders differ at %d interior basepoints;\n"
           "           IN differs from both greedy trims at %d; IN has span != span-2 at %d;\n"
           "           IN's band is not exactly [L+1,H-1] at %d\n",
           nn, n, differ, innerdiff, innerspan2, innernotstrict);
    free(p.v);
  }
}

/* ============================================================ section 3 */

static void section3(void) {
  printf("\n===== 3. a trace: bing 0 8, basepoint 57, the IN trim iterated =====\n");
  Path p = bpath(0, 8);
  int lo = 0, hi = p.n - 1, L = 0, H = 8, step = 0;
  printf("  step 0: stretch [%d,%d] band [%d,%d] span %d, level %d\n", lo, hi, L, H, H - L, p.v[57]);
  while (H - L > 3 && step < 20) {
    int a, b, Lp, Hp;
    trim_inner(p.v, lo, hi, 57, L, H, &a, &b);
    band_of(p.v, a, b, &Lp, &Hp);
    step++;
    printf("  step %d: stretch [%d,%d] (%d links) band [%d,%d] span %d, level %d%s%s\n",
           step, a, b, b - a + 1, Lp, Hp, Hp - Lp, p.v[57],
           (a == 57 || b == 57) ? "  [basepoint at an end]" : "",
           (p.v[57] == Lp || p.v[57] == Hp) ? "  [basepoint at an extreme level]" : "");
    if (Hp - Lp >= H - L) { printf("  span stalled\n"); break; }
    lo = a; hi = b; L = Lp; H = Hp;
  }
  free(p.v);
}

/* ============================================================ section 4 */

/* The witness in full: bing 0 6, basepoint 5, the inner band [1,5]. */
static void section4(void) {
  printf("\n===== 4. the witness in full: bing 0 6, basepoint 5 =====\n");
  Path p = bpath(0, 6);
  int n = p.n, L = 0, H = 6, i0 = 5;
  printf("  rho =");
  for (int k = 0; k < n; k++) printf(" %d", p.v[k]);
  printf("\n  basepoint %d has level %d\n", i0, p.v[i0]);
  static u128 tabI[64], tabE[64];
  int vlo = L - 2, vhi = H + 2;
  unsigned char *iG = (unsigned char *)calloc(n, 1), *iT = (unsigned char *)calloc(n, 1);
  unsigned char *eG = (unsigned char *)calloc(n, 1), *eT = (unsigned char *)calloc(n, 1);
  for (int Lp = L + 1; Lp + 3 <= H - 1; Lp++)
    for (int Hp = Lp + 3; Hp <= H - 1; Hp++) {
      /* the maximal stretch of the band [Lp,Hp] containing i0 */
      if (p.v[i0] < Lp || p.v[i0] > Hp) continue;
      int a = i0, b = i0;
      while (a > 0 && p.v[a - 1] >= Lp && p.v[a - 1] <= Hp) a--;
      while (b < n - 1 && p.v[b + 1] >= Lp && p.v[b + 1] <= Hp) b++;
      int mn, mx; band_of(p.v, a, b, &mn, &mx);
      printf("  band [%d,%d]: stretch [%d,%d] (%d links), actual band [%d,%d]%s\n",
             Lp, Hp, a, b, b - a + 1, mn, mx,
             (mn == Lp && mx == Hp) ? "" : "  [extremes not attained: not a trim]");
      if (!(mn == Lp && mx == Hp)) continue;
      enumerate_family(Lp, Hp, MAXTS - 2);
      for (int wi = 0; wi < nwalks; wi++) {
        Walk *W = &walks[wi];
        allow_table(W->w, W->len, vlo, vhi, tabI);
        sweep_fwdarm(p.v, a, b, W->len, vlo, tabI, iG);
        sweep_bwdarm(p.v, a, b, W->len, vlo, tabI, iT);
        int ext[MAXTS + 2], extk = W->k + 2;
        for (int j = 0; j <= W->k; j++) ext[j] = W->ts[j];
        if (W->ts[W->k] == Hp - 1) { ext[W->k + 1] = L + 1; ext[W->k + 2] = H - 1; }
        else { ext[W->k + 1] = H - 1; ext[W->k + 2] = L + 1; }
        signed char ww[MAXW]; int llen;
        walk_of(ext, extk, ww, &llen);
        allow_table(ww, llen, vlo, vhi, tabE);
        sweep_fwdarm(p.v, 0, n - 1, llen, vlo, tabE, eG);
        sweep_bwdarm(p.v, 0, n - 1, llen, vlo, tabE, eT);
        printf("    member ");
        print_ts_list(W->ts, W->k);
        printf("  inner G:%s T:%s   extension ", iG[i0] ? "yes" : "no ", iT[i0] ? "yes" : "no ");
        print_ts_list(ext, extk);
        printf(" member of [%d,%d]:%s  whole G:%s T:%s\n", L, H,
               is_zigfree(ext, extk, L, H) ? "yes" : "NO ",
               eG[i0] ? "yes" : "no ", eT[i0] ? "yes" : "no ");
      }
    }
  free(iG); free(iT); free(eG); free(eT); free(p.v);
}

int main(int argc, char **argv) {
  int maxspan = argc > 1 ? atoi(argv[1]) : 12;
  printf("census for batch 34 (max span %d)\n", maxspan);
  section1(maxspan);
  section1b(maxspan);
  section2();
  section3();
  section4();
  printf("\ndone\n");
  return 0;
}
