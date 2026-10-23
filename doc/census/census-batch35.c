/* Census for batch 35 -- the cut route (COMMISSION-batch35.md sections 1-3).
 *
 * Conventions are batches 28-34's.  An itinerary is a base centre ts[0]
 * followed by turning targets ts[1..k], all in [L+1, H-1], directions
 * alternating, amplitudes strictly increasing after the first (the free
 * family `IsZigFree`), the last two targets being the two extreme bands in
 * either order.  The walk is one level per step through those targets.  A
 * sequence folds onto a walk iff there is a 1-Lipschitz time assignment
 * starting at time 0 with every level within one of its time's centre; that
 * is decided exactly by reachability over the walk's times (a bitmask sweep).
 *
 * Sections:
 *
 *   1. the commissioned cut data `CutData` is empty.  Exhaustively, over
 *      every quadruple a < r < r' < b of `bing 0 n`: how many meet the
 *      crossing clauses (bot, top, atR, atR'), and how many of those also
 *      meet the two band clauses (bandA, bandB).  The answer to the second
 *      is 0 at every span, and the reason is local: bandA covers its own
 *      right endpoint r, where atR demands a level at least H-1 and bandA
 *      a level at most H-2; bandB covers r', where atR' demands at most
 *      L+1 and bandB at least L+2.
 *
 *   2. the corrected cut `CutData'` -- what `crookedIvF_cut_first` gives.
 *      For each pair (a, b) with rho a = L and a later rho b = H, the first
 *      crossings r (first index after a with level >= H-2) and r' (first
 *      index after r with level <= L+1).  Measured: the level at r, the
 *      level at r', and the bands of the two stretches, both closed and
 *      with the endpoints dropped.  The point at issue is whether either
 *      stretch's band lies strictly inside [L, H] at BOTH ends, which is
 *      what `isZigFree_append_outer'` requires.
 *
 *   3. the gate.  For every interior basepoint i of `bing 0 n` take the
 *      enclosing cut -- a the last bottom index at or before i, b the first
 *      top index at or after i -- with its first crossings r, r'; the
 *      stretch of the cut containing i; and the core of that stretch, the
 *      maximal subinterval containing i whose levels avoid L and H (so that
 *      its band is strictly inside and the append lemma applies).  Then, as
 *      in batch 34: does some member of the core's free family fold both
 *      core arms at i (existence), does some such member's extension by the
 *      two outer legs fold both whole arms (SOME), and do all of them
 *      (EVERY)?  Also: is the oriented extension a member of the free
 *      family of [L, H]?
 *
 * Usage: census-batch35 [maxspan]
 */

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

#define MAXW 160
#define MAXTS 32

typedef struct {
  int k;
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

static void allow_table(const signed char *w, int len, int vlo, int vhi, u128 *tab) {
  u128 one = 1;
  for (int v = vlo; v <= vhi; v++) {
    u128 m = 0;
    for (int u = 0; u < len; u++) { int d = v - w[u]; if (d <= 1 && d >= -1) m |= one << u; }
    tab[v - vlo] = m;
  }
}

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

/* ============================================================ section 1 */

/* The commissioned `CutData`, exhaustively.  For each quadruple
   a < r < r' < b with rho a = L, rho b = H, rho r >= H-1, rho r' <= L+1
   (the crossing clauses), test the two band clauses.  bandA runs over
   [a, r] inclusive and bandB over [r, r'] inclusive, exactly as
   commissioned. */
static void section1(int maxspan) {
  printf("\n===== 1. the commissioned CutData is empty =====\n");
  printf("  Every contiguous subchain [lo,hi] of bing 0 n of span >= 3 is taken as an\n"
         "  ambient, with L,H its own band; a runs over its bottom indices and b over\n"
         "  the later top indices; r over (a,b) with rho r >= H-1 (atR) and r' over\n"
         "  (r,b) with rho r' <= L+1 (atR').  Counted: those quadruples, and how many\n"
         "  of them satisfy bandA (rho <= H-2 on [a,r]) and bandB (rho >= L+2 on\n"
         "  [r,r']).\n");
  for (int nn = 6; nn <= maxspan && nn <= 8; nn++) {
    Path p = bpath(0, nn);
    int n = p.n;
    long ambients = 0, quads = 0, withA = 0, withB = 0, both = 0;
    for (int lo = 0; lo < n; lo++) {
      int mn = p.v[lo], mx = p.v[lo];
      for (int hi = lo + 1; hi < n; hi++) {
        if (p.v[hi] < mn) mn = p.v[hi];
        if (p.v[hi] > mx) mx = p.v[hi];
        int L = mn, H = mx;
        if (H - L < 3) continue;
        ambients++;
        for (int a = lo; a <= hi; a++) {
          if (p.v[a] != L) continue;
          int mxA = p.v[a];
          for (int r = a + 1; r <= hi; r++) {
            mxA = mxA > p.v[r] ? mxA : p.v[r];
            if (p.v[r] < H - 1) continue;
            int okA = (mxA <= H - 2);
            int mnB = p.v[r];
            for (int rp = r + 1; rp <= hi; rp++) {
              mnB = mnB < p.v[rp] ? mnB : p.v[rp];
              if (p.v[rp] > L + 1) continue;
              int okB = (mnB >= L + 2);
              long nb = 0;
              for (int b = rp + 1; b <= hi; b++) if (p.v[b] == H) nb++;
              if (!nb) continue;
              quads += nb;
              if (okA) withA += nb;
              if (okB) withB += nb;
              if (okA && okB) both += nb;
            }
          }
        }
      }
    }
    printf("  span %2d (%d links): %ld ambients, %ld crossing quadruples;"
           " with bandA %ld; with bandB %ld; CutData %ld\n",
           nn, n, ambients, quads, withA, withB, both);
    free(p.v);
    fflush(stdout);
  }
  printf("  (the clash is local: at r, atR asks for >= H-1 and bandA for <= H-2;\n"
         "   at r', atR' asks for <= L+1 and bandB for >= L+2.  Hence `not_cutData`.)\n");
}

/* ============================================================ section 2 */

/* first index after a with level >= H-2, then first after that with <= L+1 */
static int first_cross(const int *v, int n, int from, int lo, int hi, int up) {
  for (int j = from + 1; j < n; j++) {
    if (up ? (v[j] >= hi) : (v[j] <= lo)) return j;
  }
  return -1;
}

static void section2(int maxspan) {
  printf("\n===== 2. the corrected cut CutData' =====\n");
  printf("  Every contiguous subchain [lo,hi] of span >= 3 is an ambient with its own\n"
         "  band [L,H]; a is a bottom index of it and b a later top index; r is the\n"
         "  first index after a at level >= H-2 and r' the first after r at level\n"
         "  <= L+1.  Measured: whether the level at r is exactly H-2 (the corrected\n"
         "  atR) and at r' at most L+1, whether the order a < r < r' < b holds, and\n"
         "  whether the two stretches are strictly inside [L,H] at both ends.\n");
  for (int nn = 6; nn <= maxspan && nn <= 10; nn++) {
    Path p = bpath(0, nn);
    int n = p.n;
    long ncut = 0, rEq = 0, rHigh = 0, rPrimeLow = 0, badorder = 0;
    long AstrictLow = 0, AopenStrictLow = 0, AstrictHigh = 0;
    long BstrictHigh = 0, BopenStrictHigh = 0, BstrictLow = 0, Bboth = 0, Aboth = 0;
    for (int lo = 0; lo < n; lo++) {
      int mn = p.v[lo], mx = p.v[lo];
      for (int hi = lo + 1; hi < n; hi++) {
        if (p.v[hi] < mn) mn = p.v[hi];
        if (p.v[hi] > mx) mx = p.v[hi];
        int L = mn, H = mx;
        if (H - L < 3) continue;
        for (int a = lo; a <= hi; a++) {
          if (p.v[a] != L) continue;
          int r = -1, rp = -1, b = -1;
          for (int j = a + 1; j <= hi; j++) if (p.v[j] >= H - 2) { r = j; break; }
          if (r < 0) break;
          for (int j = r + 1; j <= hi; j++) if (p.v[j] <= L + 1) { rp = j; break; }
          if (rp < 0) break;
          for (int j = rp + 1; j <= hi; j++) if (p.v[j] == H) { b = j; break; }
          if (b < 0) break;
          ncut++;
          if (p.v[r] == H - 2) rEq++;
          if (p.v[r] >= H - 1) rHigh++;
          if (p.v[rp] <= L + 1) rPrimeLow++;
          if (!(a < r && r < rp && rp < b)) badorder++;
          int mnA, mxA, mnAo, mxAo, mnB, mxB, mnBo, mxBo;
          band_of(p.v, a, r, &mnA, &mxA);
          band_of(p.v, a + 1, r, &mnAo, &mxAo);
          band_of(p.v, r, rp, &mnB, &mxB);
          band_of(p.v, r + 1, (rp - 1 >= r + 1) ? rp - 1 : r + 1, &mnBo, &mxBo);
          if (mnA >= L + 1) AstrictLow++;
          if (mnAo >= L + 1) AopenStrictLow++;
          if (mxA <= H - 1) AstrictHigh++;
          if (mnA >= L + 1 && mxA <= H - 1) Aboth++;
          if (mxB <= H - 1) BstrictHigh++;
          if (mxBo <= H - 1) BopenStrictHigh++;
          if (mnB >= L + 1) BstrictLow++;
          if (mxB <= H - 1 && mnB >= L + 1) Bboth++;
          break;                  /* one cut per (ambient, first bottom index) */
        }
      }
    }
    printf("  span %2d (%d links): %ld cuts; rho r = H-2 in %ld, >= H-1 in %ld;"
           " rho r' <= L+1 in %ld; order wrong in %ld\n",
           nn, n, ncut, rEq, rHigh, rPrimeLow, badorder);
    printf("            [a,r]  above L: %ld   below H: %ld   both: %ld   (a,r] above L: %ld\n",
           AstrictLow, AstrictHigh, Aboth, AopenStrictLow);
    printf("            [r,r'] above L: %ld   below H: %ld   both: %ld   (r,r') below H: %ld\n",
           BstrictLow, BstrictHigh, Bboth, BopenStrictHigh);
    free(p.v);
    fflush(stdout);
  }
  printf("  [a,r] contains a, whose level is L exactly, so its band is never strictly\n"
         "  inside [L,H]; the append lemma does not apply to it\n"
         "  (`cut_stretchA_no_extension`).\n");
}

/* ============================================================ section 3 */

static unsigned char *bufIG, *bufIT, *bufEG[2], *bufET[2];
static int *cntServe, *cntBadE, *cntBadO, *badW, *notFam;

/* the gate on the stretch [a,b] with band [Lp,Hp], over the basepoints of
   [a,b]; the counters must be cleared by the caller */
static void gate_trim(const int *r, int n, int a, int b, int L, int H,
                      int Lp, int Hp, int *nmembers, int *notzf) {
  int vlo = L - 2, vhi = H + 2;
  static u128 tab[96];
  enumerate_family(Lp, Hp, MAXTS - 2);
  *nmembers = nwalks;
  *notzf = 0;
  for (int wi = 0; wi < nwalks; wi++) {
    Walk *W = &walks[wi];
    allow_table(W->w, W->len, vlo, vhi, tab);
    sweep_fwdarm(r, a, b, W->len, vlo, tab, bufIG);
    sweep_bwdarm(r, a, b, W->len, vlo, tab, bufIT);
    int any = 0;
    for (int i = a; i <= b; i++) if (bufIG[i] && bufIT[i]) { any = 1; break; }
    if (!any) continue;
    int ext[2][MAXTS + 2], extk[2];
    for (int e = 0; e < 2; e++) {
      for (int j = 0; j <= W->k; j++) ext[e][j] = W->ts[j];
      ext[e][W->k + 1] = e == 0 ? L + 1 : H - 1;
      ext[e][W->k + 2] = e == 0 ? H - 1 : L + 1;
      extk[e] = W->k + 2;
    }
    int oriented = (W->ts[W->k] == Hp - 1) ? 0 : 1;
    int famok = is_zigfree(ext[oriented], extk[oriented], L, H);
    if (!famok) (*notzf)++;
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
      if (!(oo && famok)) { if (!cntBadO[i]) badW[i] = wi; cntBadO[i]++; }
      if (!famok) notFam[i]++;
    }
  }
}

static void print_ts_list(const int *t, int k) {
  printf("[");
  for (int j = 0; j <= k; j++) printf("%s%d", j ? ", " : "", t[j]);
  printf("]");
}

static void section3(int maxspan) {
  printf("\n===== 3. the gate: a walk built from the cut, at every interior basepoint =====\n");
  printf("  a = last bottom index at or before i, b = first top index at or after i;\n"
         "  r, r' the first crossings; S the stretch of the cut containing i; C the\n"
         "  core of S (maximal subinterval containing i avoiding the levels L and H).\n"
         "  existence: some member of C's free family folds both C-arms at i.\n"
         "  SOME / EVERY: some / every such member's extension by the two outer legs\n"
         "  folds both whole arms at i (EVERY also demands the oriented extension be\n"
         "  a member of the free family of [L,H]).\n");
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
    notFam = (int *)calloc(n, sizeof(int));

    /* last bottom at or before each index, first top at or after each index */
    int *lastL = (int *)malloc(sizeof(int) * n);
    int *firstH = (int *)malloc(sizeof(int) * n);
    int cur = -1;
    for (int j = 0; j < n; j++) { if (p.v[j] == L) cur = j; lastL[j] = cur; }
    cur = -1;
    for (int j = n - 1; j >= 0; j--) { if (p.v[j] == H) cur = j; firstH[j] = cur; }

    /* the core stretch of each interior basepoint, deduplicated */
    typedef struct { int a, b, Lp, Hp; } Tr;
    Tr *trs = (Tr *)malloc(sizeof(Tr) * n);
    int ntr = 0;
    int *use = (int *)malloc(sizeof(int) * n);
    int ninterior = 0, nocut = 0, narrow = 0;
    int inA = 0, inB = 0, inC = 0;
    long spansum = 0;
    for (int i = 0; i < n; i++) {
      use[i] = -1;
      if (!(p.v[i] >= L + 3 && p.v[i] <= H - 3)) continue;
      ninterior++;
      int a = lastL[i], b = firstH[i];
      if (a < 0 || b < 0 || a >= b) { nocut++; continue; }
      int r = first_cross(p.v, n, a, L + 1, H - 2, 1);
      int rp = r < 0 ? -1 : first_cross(p.v, n, r, L + 1, H - 2, 0);
      if (r < 0 || rp < 0 || !(a < r && r < rp && rp < b)) { nocut++; continue; }
      int slo, shi;
      if (i <= r) { slo = a; shi = r; inA++; }
      else if (i <= rp) { slo = r; shi = rp; inB++; }
      else { slo = rp; shi = b; inC++; }
      /* the core: maximal subinterval of [slo,shi] containing i whose levels
         avoid L and H */
      int clo = i, chi = i;
      while (clo > slo && p.v[clo - 1] != L && p.v[clo - 1] != H) clo--;
      while (chi < shi && p.v[chi + 1] != L && p.v[chi + 1] != H) chi++;
      int Lp, Hp; band_of(p.v, clo, chi, &Lp, &Hp);
      if (Hp - Lp < 3) { narrow++; continue; }
      spansum += Hp - Lp;
      int f = -1;
      for (int q = 0; q < ntr; q++) if (trs[q].a == clo && trs[q].b == chi) { f = q; break; }
      if (f < 0) {
        trs[ntr].a = clo; trs[ntr].b = chi; trs[ntr].Lp = Lp; trs[ntr].Hp = Hp;
        f = ntr++;
      }
      use[i] = f;
    }

    int passE = 0, passO = 0, served = 0, unserved = 0;
    int firstfail = -1, firstfailw = -1, firstfailtr = -1;
    int firstsome = -1, firstsometr = -1;
    int anyNotFam = 0;
    unsigned char *okE = (unsigned char *)calloc(n, 1);
    unsigned char *okO = (unsigned char *)calloc(n, 1);
    for (int q = 0; q < ntr; q++) {
      memset(cntServe, 0, sizeof(int) * n);
      memset(cntBadE, 0, sizeof(int) * n);
      memset(cntBadO, 0, sizeof(int) * n);
      memset(notFam, 0, sizeof(int) * n);
      int members, notzf;
      gate_trim(p.v, n, trs[q].a, trs[q].b, L, H, trs[q].Lp, trs[q].Hp, &members, &notzf);
      anyNotFam += notzf;
      for (int i = trs[q].a; i <= trs[q].b; i++) {
        if (use[i] != q) continue;
        if (cntServe[i] > 0) served++; else unserved++;
        okE[i] = (cntServe[i] > 0 && cntBadE[i] == 0);
        okO[i] = (cntServe[i] > 0 && cntBadO[i] == 0);
        int some = (cntServe[i] > 0 && cntBadE[i] < cntServe[i]);
        passE += some;
        passO += okO[i];
        if (!okO[i] && cntServe[i] > 0 && firstfail < 0) {
          firstfail = i; firstfailw = badW[i]; firstfailtr = q;
        }
        if (!some && cntServe[i] > 0 && firstsome < 0) { firstsome = i; firstsometr = q; }
      }
    }
    printf("\n  span %2d: %d links, %d interior basepoints, %d distinct cores\n",
           nn, n, ninterior, ntr);
    printf("    the basepoint lies in stretch [a,r] %d times, [r,r'] %d, [r',b] %d;"
           " no usable cut %d; core too narrow %d\n", inA, inB, inC, nocut, narrow);
    if (ntr) printf("    mean core span %.2f\n", (double)spansum / (double)(inA + inB + inC - narrow));
    printf("    existence (some member folds both core arms): %d served, %d unserved\n",
           served, unserved);
    printf("    SOME  (a serving member extends to fold both whole arms): %d/%d\n",
           passE, served);
    printf("    EVERY (all serving members extend, oriented, in the family): %d/%d\n",
           passO, served);
    printf("    serving members whose oriented extension is NOT in the family of [L,H]: %d\n",
           anyNotFam);
    if (firstsome >= 0)
      printf("    first SOME failure at basepoint %d (level %d), core [%d,%d] band [%d,%d]:"
             " no member of the core's family extends to fold both whole arms\n",
             firstsome, p.v[firstsome], trs[firstsometr].a, trs[firstsometr].b,
             trs[firstsometr].Lp, trs[firstsometr].Hp);
    if (firstfail >= 0) {
      printf("    first EVERY failure at basepoint %d (level %d), core [%d,%d] band [%d,%d]: ",
             firstfail, p.v[firstfail], trs[firstfailtr].a, trs[firstfailtr].b,
             trs[firstfailtr].Lp, trs[firstfailtr].Hp);
      enumerate_family(trs[firstfailtr].Lp, trs[firstfailtr].Hp, MAXTS - 2);
      if (firstfailw >= 0 && firstfailw < nwalks)
        print_ts_list(walks[firstfailw].ts, walks[firstfailw].k);
      printf("\n");
    }
    free(okE); free(okO); free(trs); free(use); free(lastL); free(firstH);
    free(bufIG); free(bufIT);
    for (int e = 0; e < 2; e++) { free(bufEG[e]); free(bufET[e]); }
    free(cntServe); free(cntBadE); free(cntBadO); free(badW); free(notFam);
    free(p.v);
    fflush(stdout);
  }
}

int main(int argc, char **argv) {
  int maxspan = argc > 1 ? atoi(argv[1]) : 12;
  printf("census for batch 35 -- the cut route; spans 6 .. %d\n", maxspan);
  section1(maxspan);
  section2(maxspan);
  section3(maxspan);
  return 0;
}
