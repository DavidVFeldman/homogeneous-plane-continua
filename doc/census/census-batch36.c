/* Census for batch 36 -- shortest serving walks (COMMISSION-batch36 section 1).
 *
 * Conventions are batches 28-35's.  A member of the free family `IsZigFree`
 * of a band [L',H'] is a base centre ts[0] followed by turning targets
 * ts[1..k], all in [L'+1, H'-1], directions alternating, amplitudes strictly
 * increasing after the first, the last two targets being the two extreme
 * bands H'-1, L'+1 in either order.  Its walk is one level per step through
 * those targets; its *length* is the number of levels, 1 + the total
 * amplitude.  A sequence f folds onto a walk iff there is a 1-Lipschitz time
 * assignment starting at time 0 with every level within one of its time's
 * centre; that is decided exactly by reachability over the walk's times (a
 * bitmask sweep).
 *
 * The gate: `ExtendStepMin` at every interior basepoint (L+3 <= rho i <= H-3)
 * of `bing 0 n`.  An inner trim is a band [L',H'] with L+1 <= L',
 * H' <= H-1, L'+3 <= H', together with a maximal stretch of that band whose
 * band is exactly [L',H'] (batch 34's inner trims, the ones
 * `zigFree_append_forces_inner` shows are the only appendable ones).  For a
 * basepoint i in such a stretch, a member *serves* if it folds both arms of
 * the stretch at i, and *extends* if the oriented extension -- append
 * (L+1, H-1) if the member ends high and (H-1, L+1) if it ends low -- is a
 * member of the free family of [L,H] and folds both arms of the whole chain
 * at i.  The gate asks:
 *
 *   MIN    is there a trim at which some member serves and *every serving
 *          member of least walk length* extends?
 *   SOME   is there a trim at which some serving member of least walk length
 *          extends?
 *   EVERY  (batch 34's form, recomputed for comparison) is there a trim at
 *          which some member serves and every serving member extends?
 *
 * The uniqueness question of COMMISSION-batch36 section 1 is the gap between
 * MIN and SOME: a basepoint passing SOME but not MIN is one where, at every
 * trim, some shortest serving walk extends and another does not.  The
 * program also counts the trims at which the shortest serving members split.
 *
 * Section 2 re-runs the gate restricted to the trims of the full inner band
 * [L+1, H-1], and section 3 traces one basepoint in full.
 *
 * Usage: census-batch36 [maxspan]
 */

#include <limits.h>
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

#define MAXW 128
#define MAXTS 32

typedef struct {
  int k;               /* number of turning targets after the base centre */
  int ts[MAXTS];
  int len;             /* the walk's length: 1 + the total amplitude */
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
      if (len > MAXW) { fprintf(stderr, "walk overflow\n"); exit(1); }
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

static void allow_table(const signed char *w, int len, int vlo, int vhi, u128 *tab) {
  u128 one = 1;
  for (int v = vlo; v <= vhi; v++) {
    u128 m = 0;
    for (int u = 0; u < len; u++) { int d = v - w[u]; if (d <= 1 && d >= -1) m |= one << u; }
    tab[v - vlo] = m;
  }
}

/* out[k] = 1 iff the forward arm from k folds onto the walk, pinned at time 0 */
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

/* out[k] = 1 iff the backward arm from k folds onto the walk */
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

static void band_of(const int *r, int a, int b, int *L, int *H) {
  int mn = r[a], mx = r[a];
  for (int q = a; q <= b; q++) { if (r[q] < mn) mn = r[q]; if (r[q] > mx) mx = r[q]; }
  *L = mn; *H = mx;
}

static void print_ts_list(const int *t, int k) {
  printf("[");
  for (int j = 0; j <= k; j++) printf("%s%d", j ? ", " : "", t[j]);
  printf("]");
}

/* ============================================================ the gate */

/* per-basepoint state, over one chain */
typedef struct {
  unsigned char okmin;    /* some trim: every shortest serving member extends */
  unsigned char oksome;   /* some trim: some shortest serving member extends */
  unsigned char okevery;  /* some trim: every serving member extends */
  unsigned char split;    /* some trim: the shortest serving members split */
  int wL, wH, wa, wb;     /* a trim witnessing okmin */
  int wlen;               /* the least serving length there */
} BP;

/* scratch, sized to the chain */
static int *minlen, *cntMin, *cntMinGood, *cntServe, *cntGood;
static int *badW, *goodW;
static unsigned char *iG, *iT, *eG, *eT;

static void run_gate(int nn, int maxspan_unused, int onlyfullband, int verbose) {
  (void)maxspan_unused;
  Path p = bpath(0, nn);
  int n = p.n, L = 0, H = nn;
  BP *bp = (BP *)calloc(n, sizeof(BP));
  minlen = (int *)malloc(sizeof(int) * n);
  cntMin = (int *)malloc(sizeof(int) * n);
  cntMinGood = (int *)malloc(sizeof(int) * n);
  cntServe = (int *)malloc(sizeof(int) * n);
  cntGood = (int *)malloc(sizeof(int) * n);
  badW = (int *)malloc(sizeof(int) * n);
  goodW = (int *)malloc(sizeof(int) * n);
  iG = (unsigned char *)calloc(n, 1);
  iT = (unsigned char *)calloc(n, 1);
  eG = (unsigned char *)calloc(n, 1);
  eT = (unsigned char *)calloc(n, 1);
  static u128 tabI[64], tabE[64];
  int vlo = L - 2, vhi = H + 2;
  int ninterior = 0;
  for (int i = 0; i < n; i++) if (p.v[i] >= L + 3 && p.v[i] <= H - 3) ninterior++;
  long long totmembers = 0, notzf = 0, ntrims = 0, nsplit = 0;
  /* the witness of a MIN failure, if any */
  int exBP = -1, exL = 0, exH = 0, exA = 0, exB = 0, exW = -1, exLen = 0;

  int *ra = (int *)malloc(sizeof(int) * n), *rb = (int *)malloc(sizeof(int) * n);
  for (int Lp = L + 1; Lp + 3 <= H - 1; Lp++)
    for (int Hp = Lp + 3; Hp <= H - 1; Hp++) {
      if (onlyfullband && !(Lp == L + 1 && Hp == H - 1)) continue;
      int nruns = 0, k = 0;
      while (k < n) {
        if (p.v[k] < Lp || p.v[k] > Hp) { k++; continue; }
        int a = k;
        while (k < n && p.v[k] >= Lp && p.v[k] <= Hp) k++;
        int b = k - 1, mn, mx;
        band_of(p.v, a, b, &mn, &mx);
        if (mn == Lp && mx == Hp) { ra[nruns] = a; rb[nruns] = b; nruns++; }
      }
      if (!nruns) continue;
      ntrims += nruns;
      enumerate_family(Lp, Hp, MAXTS - 2);
      totmembers += nwalks;
      for (int i = 0; i < n; i++) {
        minlen[i] = INT_MAX; cntMin[i] = 0; cntMinGood[i] = 0;
        cntServe[i] = 0; cntGood[i] = 0; badW[i] = -1; goodW[i] = -1;
      }
      for (int wi = 0; wi < nwalks; wi++) {
        Walk *W = &walks[wi];
        allow_table(W->w, W->len, vlo, vhi, tabI);
        int any = 0;
        for (int q = 0; q < nruns; q++) {
          sweep_fwdarm(p.v, ra[q], rb[q], W->len, vlo, tabI, iG);
          sweep_bwdarm(p.v, ra[q], rb[q], W->len, vlo, tabI, iT);
          for (int i = ra[q]; i <= rb[q]; i++) if (iG[i] && iT[i]) { any = 1; break; }
        }
        if (!any) continue;
        int ext[MAXTS + 2], extk = W->k + 2;
        for (int j = 0; j <= W->k; j++) ext[j] = W->ts[j];
        if (W->ts[W->k] == Hp - 1) { ext[W->k + 1] = L + 1; ext[W->k + 2] = H - 1; }
        else { ext[W->k + 1] = H - 1; ext[W->k + 2] = L + 1; }
        int zf = is_zigfree(ext, extk, L, H);
        if (!zf) notzf++;
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
            int good = zf && eG[i] && eT[i];
            cntServe[i]++;
            if (good) cntGood[i]++;
            if (W->len < minlen[i]) {
              minlen[i] = W->len; cntMin[i] = 1; cntMinGood[i] = good ? 1 : 0;
              badW[i] = good ? -1 : wi; goodW[i] = good ? wi : -1;
            } else if (W->len == minlen[i]) {
              cntMin[i]++;
              if (good) { cntMinGood[i]++; if (goodW[i] < 0) goodW[i] = wi; }
              else if (badW[i] < 0) badW[i] = wi;
            }
          }
        }
      }
      /* fold the trim's verdict into the per-basepoint state */
      for (int q = 0; q < nruns; q++)
        for (int i = ra[q]; i <= rb[q]; i++) {
          if (!(p.v[i] >= L + 3 && p.v[i] <= H - 3)) continue;
          if (cntServe[i] == 0) continue;
          if (cntMinGood[i] == cntMin[i]) {
            if (!bp[i].okmin) {
              bp[i].wL = Lp; bp[i].wH = Hp; bp[i].wa = ra[q]; bp[i].wb = rb[q];
              bp[i].wlen = minlen[i];
            }
            bp[i].okmin = 1;
          } else if (exBP < 0 || (exBP == i && 0)) {
            if (exBP < 0) {
              exBP = i; exL = Lp; exH = Hp; exA = ra[q]; exB = rb[q];
              exW = badW[i]; exLen = minlen[i];
            }
          }
          if (cntMinGood[i] > 0) bp[i].oksome = 1;
          if (cntMinGood[i] > 0 && cntMinGood[i] < cntMin[i]) { bp[i].split = 1; nsplit++; }
          if (cntGood[i] == cntServe[i]) bp[i].okevery = 1;
        }
    }
  free(ra); free(rb);

  int passmin = 0, passsome = 0, passevery = 0, splitbp = 0;
  int firstfailmin = -1, firstfailsome = -1;
  int gapbp = 0, firstgap = -1;
  for (int i = 0; i < n; i++) {
    if (!(p.v[i] >= L + 3 && p.v[i] <= H - 3)) continue;
    passmin += bp[i].okmin; passsome += bp[i].oksome; passevery += bp[i].okevery;
    splitbp += bp[i].split;
    if (!bp[i].okmin && firstfailmin < 0) firstfailmin = i;
    if (!bp[i].oksome && firstfailsome < 0) firstfailsome = i;
    if (!bp[i].okmin && bp[i].oksome) { gapbp++; if (firstgap < 0) firstgap = i; }
  }
  printf("  span %2d: %d links, %d interior basepoints, %lld inner trims, "
         "%lld family members swept\n", nn, n, ninterior, ntrims, totmembers);
  printf("           MIN   (every shortest serving member extends, at some trim): %d/%d"
         "   FAILURES %d\n", passmin, ninterior, ninterior - passmin);
  printf("           SOME  (some  shortest serving member extends, at some trim): %d/%d"
         "   FAILURES %d\n", passsome, ninterior, ninterior - passsome);
  printf("           EVERY (every serving member extends, at some trim): %d/%d"
         "   FAILURES %d\n", passevery, ninterior, ninterior - passevery);
  printf("           basepoints passing SOME but not MIN (uniqueness needed): %d\n", gapbp);
  printf("           basepoints with a trim whose shortest serving members split: %d\n",
         splitbp);
  printf("           trims whose shortest serving members split: %lld\n", nsplit);
  printf("           oriented extensions that are not members of the free family of [L,H]: "
         "%lld\n", notzf);
  if (firstfailmin >= 0) {
    printf("           FIRST BASEPOINT FAILING THE MIN FORM: %d (level %d)\n",
           firstfailmin, p.v[firstfailmin]);
    if (exBP >= 0) {
      enumerate_family(exL, exH, MAXTS - 2);
      printf("           witness: basepoint %d, band [%d,%d], stretch [%d,%d], least serving "
             "length %d, the member ", exBP, exL, exH, exA, exB, exLen);
      if (exW >= 0 && exW < nwalks) print_ts_list(walks[exW].ts, walks[exW].k);
      printf(" serves and does not extend\n");
    }
  }
  if (firstfailsome >= 0) {
    printf("           BASEPOINTS FAILING THE SOME FORM:");
    int shown = 0;
    for (int i = 0; i < n && shown < 40; i++) {
      if (!(p.v[i] >= L + 3 && p.v[i] <= H - 3)) continue;
      if (bp[i].oksome) continue;
      printf(" %d(level %d)", i, p.v[i]);
      shown++;
    }
    printf("\n");
  }
  if (verbose && passmin == ninterior) {
    /* a couple of witnessing trims, for the record */
    int shown = 0;
    for (int i = 0; i < n && shown < 3; i++) {
      if (!(p.v[i] >= L + 3 && p.v[i] <= H - 3)) continue;
      printf("           e.g. basepoint %d (level %d): band [%d,%d], stretch [%d,%d], "
             "least serving length %d\n", i, p.v[i], bp[i].wL, bp[i].wH, bp[i].wa, bp[i].wb,
             bp[i].wlen);
      shown++;
    }
  }
  fflush(stdout);
  free(bp); free(minlen); free(cntMin); free(cntMinGood); free(cntServe); free(cntGood);
  free(badW); free(goodW); free(iG); free(iT); free(eG); free(eT); free(p.v);
}

/* ============================================================ section 1 */

static void section1(int maxspan) {
  printf("\n===== 1. the gate: ExtendStepMin at every interior basepoint =====\n");
  printf("  trims: every band [L',H'] with L+1 <= L', H' <= H-1, L'+3 <= H', and every\n"
         "         maximal stretch whose band is exactly [L',H'].\n"
         "  serving: the member folds both arms of the stretch at the basepoint.\n"
         "  extending: the oriented extension is a member of the free family of [L,H]\n"
         "         and folds both arms of the whole chain at the basepoint.\n");
  for (int nn = 6; nn <= maxspan; nn++) run_gate(nn, maxspan, 0, 1);
}

/* ============================================================ section 2 */

static void section2(int maxspan) {
  printf("\n===== 2. the same, restricted to the full inner band [L+1,H-1] =====\n");
  for (int nn = 6; nn <= maxspan; nn++) run_gate(nn, maxspan, 1, 0);
}

/* =========================================================== section 1c */

/* The gate over *every* inner trim, not only the maximal stretches: for each
   band [Lp,Hp] with L+1 <= Lp, Hp <= H-1, Lp+3 <= Hp, every stretch [a,b]
   inside a maximal run of that band, containing the basepoint, attaining both
   Lp and Hp.  That is exactly the family `IsInnerTrim` allows.  Exhaustive, so
   run only at the small spans. */
static void section1c(int maxspan) {
  printf("\n===== 1c. the gate over EVERY inner trim (all stretches, not only maximal) =====\n");
  for (int nn = 6; nn <= maxspan; nn++) {
    Path p = bpath(0, nn);
    int n = p.n, L = 0, H = nn;
    unsigned char *okmin = (unsigned char *)calloc(n, 1);
    unsigned char *oksome = (unsigned char *)calloc(n, 1);
    int *wL = (int *)calloc(n, sizeof(int)), *wH = (int *)calloc(n, sizeof(int));
    int *wa = (int *)calloc(n, sizeof(int)), *wb = (int *)calloc(n, sizeof(int));
    unsigned char *uG = (unsigned char *)calloc(n, 1), *uT = (unsigned char *)calloc(n, 1);
    static u128 tabI[64], tabE[64];
    int vlo = L - 2, vhi = H + 2;
    int ninterior = 0;
    for (int i = 0; i < n; i++) if (p.v[i] >= L + 3 && p.v[i] <= H - 3) ninterior++;
    long long ntrims = 0;
    for (int Lp = L + 1; Lp + 3 <= H - 1; Lp++)
      for (int Hp = Lp + 3; Hp <= H - 1; Hp++) {
        int nruns = 0, k = 0;
        int *ra = (int *)malloc(sizeof(int) * n), *rb = (int *)malloc(sizeof(int) * n);
        while (k < n) {
          if (p.v[k] < Lp || p.v[k] > Hp) { k++; continue; }
          int a = k;
          while (k < n && p.v[k] >= Lp && p.v[k] <= Hp) k++;
          int b = k - 1, mn, mx;
          band_of(p.v, a, b, &mn, &mx);
          if (mn == Lp && mx == Hp) { ra[nruns] = a; rb[nruns] = b; nruns++; }
        }
        if (!nruns) { free(ra); free(rb); continue; }
        enumerate_family(Lp, Hp, MAXTS - 2);
        int nw = nwalks;
        int *mlen = (int *)malloc(sizeof(int) * (nw ? nw : 1));
        unsigned char *mgood = (unsigned char *)malloc(nw ? (size_t)nw * n : 1);
        int *Farr = (int *)malloc(sizeof(int) * (nw ? (size_t)nw * n : 1));
        int *Garr = (int *)malloc(sizeof(int) * (nw ? (size_t)nw * n : 1));
        for (int wi = 0; wi < nw; wi++) {
          Walk *W = &walks[wi];
          mlen[wi] = W->len;
          int ext[MAXTS + 2], extk = W->k + 2;
          for (int j = 0; j <= W->k; j++) ext[j] = W->ts[j];
          if (W->ts[W->k] == Hp - 1) { ext[W->k + 1] = L + 1; ext[W->k + 2] = H - 1; }
          else { ext[W->k + 1] = H - 1; ext[W->k + 2] = L + 1; }
          int zf = is_zigfree(ext, extk, L, H);
          signed char ww[MAXW]; int llen;
          walk_of(ext, extk, ww, &llen);
          allow_table(ww, llen, vlo, vhi, tabE);
          sweep_fwdarm(p.v, 0, n - 1, llen, vlo, tabE, uG);
          sweep_bwdarm(p.v, 0, n - 1, llen, vlo, tabE, uT);
          for (int i = 0; i < n; i++)
            mgood[(size_t)wi * n + i] = (unsigned char)(zf && uG[i] && uT[i]);
          /* the extents of the member's fold from each basepoint, inside each run */
          allow_table(W->w, W->len, vlo, vhi, tabI);
          u128 one = 1;
          u128 full = (W->len >= 128) ? ~(u128)0 : ((one << W->len) - 1);
          for (int q = 0; q < nruns; q++)
            for (int i = ra[q]; i <= rb[q]; i++) {
              u128 S = tabI[p.v[i] - vlo] & one;   /* the arm's first link at time 0 */
              int b = i;
              if (S) {
                while (b + 1 <= rb[q]) {
                  u128 T = tabI[p.v[b + 1] - vlo] & (((S << 1) | S | (S >> 1)) & full);
                  if (!T) break;
                  S = T; b++;
                }
              } else b = i - 1;
              Farr[(size_t)wi * n + i] = b;
              S = tabI[p.v[i] - vlo] & one;
              int a = i;
              if (S) {
                while (a - 1 >= ra[q]) {
                  u128 T = tabI[p.v[a - 1] - vlo] & (((S << 1) | S | (S >> 1)) & full);
                  if (!T) break;
                  S = T; a--;
                }
              } else a = i + 1;
              Garr[(size_t)wi * n + i] = a;
            }
        }
        for (int q = 0; q < nruns; q++)
          for (int i = ra[q]; i <= rb[q]; i++) {
            if (!(p.v[i] >= L + 3 && p.v[i] <= H - 3)) continue;
            if (okmin[i]) continue;
            int mnA = p.v[i], mxA = p.v[i];
            for (int a = i; a >= ra[q]; a--) {
              if (p.v[a] < mnA) mnA = p.v[a];
              if (p.v[a] > mxA) mxA = p.v[a];
              int mn = mnA, mx = mxA;
              for (int b = i; b <= rb[q]; b++) {
                if (p.v[b] < mn) mn = p.v[b];
                if (p.v[b] > mx) mx = p.v[b];
                if (!(mn == Lp && mx == Hp)) continue;
                ntrims++;
                int best = INT_MAX, allgood = 1, anygood = 0;
                for (int wi = 0; wi < nw; wi++) {
                  if (Garr[(size_t)wi * n + i] > a) continue;
                  if (Farr[(size_t)wi * n + i] < b) continue;
                  int g = mgood[(size_t)wi * n + i];
                  if (mlen[wi] < best) { best = mlen[wi]; allgood = g; anygood = g; }
                  else if (mlen[wi] == best) { allgood &= g; anygood |= g; }
                }
                if (best == INT_MAX) continue;
                if (anygood) oksome[i] = 1;
                if (allgood) {
                  if (!okmin[i]) { wL[i] = Lp; wH[i] = Hp; wa[i] = a; wb[i] = b; }
                  okmin[i] = 1;
                }
              }
              if (okmin[i]) break;
            }
          }
        free(mlen); free(mgood); free(Farr); free(Garr); free(ra); free(rb);
      }
    int passmin = 0, passsome = 0, firstfail = -1;
    for (int i = 0; i < n; i++) {
      if (!(p.v[i] >= L + 3 && p.v[i] <= H - 3)) continue;
      passmin += okmin[i]; passsome += oksome[i];
      if (!okmin[i] && firstfail < 0) firstfail = i;
    }
    printf("  span %2d: %d links, %d interior basepoints, %lld trims examined\n",
           nn, n, ninterior, ntrims);
    printf("           MIN over all inner trims: %d/%d   FAILURES %d\n",
           passmin, ninterior, ninterior - passmin);
    printf("           SOME over all inner trims (lower bound, search stops at a MIN pass): "
           "%d/%d\n", passsome, ninterior);
    if (firstfail >= 0)
      printf("           FIRST BASEPOINT FAILING THE MIN FORM OVER EVERY INNER TRIM: %d "
             "(level %d)\n", firstfail, p.v[firstfail]);
    else
      printf("           e.g. basepoint %d: band [%d,%d], stretch [%d,%d]\n",
             5, wL[5], wH[5], wa[5], wb[5]);
    fflush(stdout);
    free(okmin); free(oksome); free(wL); free(wH); free(wa); free(wb); free(uG); free(uT);
    free(p.v);
  }
}

/* ============================================================ section 3 */

/* The trace: bing 0 6, basepoint 5 -- batch 34's first EVERY failure -- with
   every inner trim, its serving members, their lengths and their extensions. */
static void section3(void) {
  printf("\n===== 3. a trace: bing 0 6, basepoint 5 (batch 34's first EVERY failure) =====\n");
  Path p = bpath(0, 6);
  int n = p.n, L = 0, H = 6, i0 = 5;
  printf("  rho =");
  for (int k = 0; k < n; k++) printf(" %d", p.v[k]);
  printf("\n  basepoint %d has level %d\n", i0, p.v[i0]);
  static u128 tabI[64], tabE[64];
  int vlo = L - 2, vhi = H + 2;
  unsigned char *aG = (unsigned char *)calloc(n, 1), *aT = (unsigned char *)calloc(n, 1);
  unsigned char *bG = (unsigned char *)calloc(n, 1), *bT = (unsigned char *)calloc(n, 1);
  for (int Lp = L + 1; Lp + 3 <= H - 1; Lp++)
    for (int Hp = Lp + 3; Hp <= H - 1; Hp++) {
      if (p.v[i0] < Lp || p.v[i0] > Hp) continue;
      int a = i0, b = i0;
      while (a > 0 && p.v[a - 1] >= Lp && p.v[a - 1] <= Hp) a--;
      while (b < n - 1 && p.v[b + 1] >= Lp && p.v[b + 1] <= Hp) b++;
      int mn, mx; band_of(p.v, a, b, &mn, &mx);
      if (!(mn == Lp && mx == Hp)) {
        printf("  band [%d,%d]: stretch [%d,%d] has band [%d,%d]: not a trim\n",
               Lp, Hp, a, b, mn, mx);
        continue;
      }
      printf("  band [%d,%d]: stretch [%d,%d] (%d links)\n", Lp, Hp, a, b, b - a + 1);
      enumerate_family(Lp, Hp, MAXTS - 2);
      int best = INT_MAX;
      for (int wi = 0; wi < nwalks; wi++) {
        Walk *W = &walks[wi];
        allow_table(W->w, W->len, vlo, vhi, tabI);
        sweep_fwdarm(p.v, a, b, W->len, vlo, tabI, aG);
        sweep_bwdarm(p.v, a, b, W->len, vlo, tabI, aT);
        if (aG[i0] && aT[i0] && W->len < best) best = W->len;
      }
      for (int wi = 0; wi < nwalks; wi++) {
        Walk *W = &walks[wi];
        allow_table(W->w, W->len, vlo, vhi, tabI);
        sweep_fwdarm(p.v, a, b, W->len, vlo, tabI, aG);
        sweep_bwdarm(p.v, a, b, W->len, vlo, tabI, aT);
        if (!(aG[i0] && aT[i0])) continue;
        int ext[MAXTS + 2], extk = W->k + 2;
        for (int j = 0; j <= W->k; j++) ext[j] = W->ts[j];
        if (W->ts[W->k] == Hp - 1) { ext[W->k + 1] = L + 1; ext[W->k + 2] = H - 1; }
        else { ext[W->k + 1] = H - 1; ext[W->k + 2] = L + 1; }
        signed char ww[MAXW]; int llen;
        walk_of(ext, extk, ww, &llen);
        allow_table(ww, llen, vlo, vhi, tabE);
        sweep_fwdarm(p.v, 0, n - 1, llen, vlo, tabE, bG);
        sweep_bwdarm(p.v, 0, n - 1, llen, vlo, tabE, bT);
        printf("    serving member ");
        print_ts_list(W->ts, W->k);
        printf(" length %d%s   extension ", W->len, W->len == best ? " [shortest]" : "");
        print_ts_list(ext, extk);
        printf(" member:%s folds whole arms:%s\n",
               is_zigfree(ext, extk, L, H) ? "yes" : "NO ",
               (bG[i0] && bT[i0]) ? "yes" : "no");
      }
    }
  free(aG); free(aT); free(bG); free(bT); free(p.v);
}

int main(int argc, char **argv) {
  int maxspan = argc > 1 ? atoi(argv[1]) : 12;
  printf("census for batch 36 -- shortest serving walks; spans 6 .. %d\n", maxspan);
  section1(maxspan);
  section1c(maxspan < 8 ? maxspan : 8);
  section2(maxspan);
  section3();
  printf("\ndone\n");
  return 0;
}
