/* Census for batch 31 -- the interior case of `S3ZigFree`.
 *
 * Conventions are batch 29's: an itinerary is a base centre ts[0] followed by
 * k turning targets ts[1..k], all in [L+1, H-1], directions alternating, one
 * level per step, and `FoldsOnto` is decided exactly by reachability over the
 * walk's times.  Three regimes as before; only regime 2 (`IsZigFree`) is used
 * here.
 *
 * What is new in this batch is the pair of one-turn walks based at the
 * basepoint's own level,
 *
 *     veeAt(p) = [p, L+1, H-1]      lamAt(p) = [p, H-1, L+1],
 *
 * and the tracking folds onto them (`foldsOnto_veeAt`, `foldsOnto_lamAt`).
 * The fold hypothesis, for the vee, is
 *
 *     the arm stays at or below p+1 until it first reaches L+1,
 *
 * and for the lam its mirror image.  Sections 1 and 2 measure how far that
 * carries: section 1 checks the hypothesis literally on both arms, section 2
 * checks by reachability whether the walk serves the basepoint at all (which
 * is weaker: the hypothesis is sufficient, not necessary).  Section 3 is the
 * minimal-turn table over interior basepoints, which says how many legs the
 * remaining basepoints really need, and re-checks that no basepoint fails.
 * Section 4 repeats 1-3 on random subchains of bing 0 12.
 *
 * Usage: census-batch31 [seed]
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

/* -------------------------------------------------------------- the sweep */

#define MAXN 20000
#define MAXW 128

static u128 Gm[MAXN], Tm[MAXN];
static int minturns[MAXN];
static int chainN;
static const int *chainV;
static int chainL, chainH;
static int remaining;
static int curk;

static inline u128 nbr(u128 m, u128 full) { return (m | (m << 1) | (m >> 1)) & full; }

static void set_band(const int *rho, int n) {
  chainV = rho; chainN = n;
  chainL = chainH = rho[0];
  for (int i = 1; i < n; i++) {
    if (rho[i] < chainL) chainL = rho[i];
    if (rho[i] > chainH) chainH = rho[i];
  }
}

/* Does the single walk `w` serve basepoint `i`? */
static int walk_serves(const signed char *w, int len, int i) {
  u128 one = (u128)1;
  u128 full = (len >= 128) ? ~(u128)0 : ((one << len) - 1);
  u128 allow[64];
  for (int v = chainL; v <= chainH; v++) {
    u128 m = 0;
    for (int u = 0; u < len; u++) {
      int d = v - w[u];
      if (d <= 1 && d >= -1) m |= one << u;
    }
    allow[v - chainL] = m;
  }
  int n = chainN;
  u128 g = allow[chainV[n - 1] - chainL];
  for (int t = n - 2; t >= i; t--) g = allow[chainV[t] - chainL] & nbr(g, full);
  u128 h = allow[chainV[0] - chainL];
  for (int t = 1; t <= i; t++) h = allow[chainV[t] - chainL] & nbr(h, full);
  return (g & h & one) != 0;
}

static void sweep(const signed char *w, int len) {
  u128 one = (u128)1;
  u128 full = (len >= 128) ? ~(u128)0 : ((one << len) - 1);
  u128 allow[64];
  for (int v = chainL; v <= chainH; v++) {
    u128 m = 0;
    for (int u = 0; u < len; u++) {
      int d = v - w[u];
      if (d <= 1 && d >= -1) m |= one << u;
    }
    allow[v - chainL] = m;
  }
  int n = chainN;
  Gm[n - 1] = allow[chainV[n - 1] - chainL];
  for (int i = n - 2; i >= 0; i--) Gm[i] = allow[chainV[i] - chainL] & nbr(Gm[i + 1], full);
  Tm[0] = allow[chainV[0] - chainL];
  for (int i = 1; i < n; i++) Tm[i] = allow[chainV[i] - chainL] & nbr(Tm[i - 1], full);
  for (int i = 0; i < n; i++) {
    if (minturns[i] >= 0) continue;
    if ((Gm[i] & Tm[i] & one) != 0) { minturns[i] = curk; remaining--; }
  }
}

/* -------------------------------------------------- itinerary enumeration */

#define MAXTS 16

static int ts[MAXTS];
static int gRegime, gTargetK, gSweeping;

static void walk_of(int k, signed char *w, int *lenout) {
  int len = 0;
  w[len++] = (signed char)ts[0];
  for (int j = 1; j <= k; j++) {
    int d = ts[j] > ts[j - 1] ? 1 : -1;
    for (int x = ts[j - 1] + d;; x += d) {
      assert(len < MAXW);
      w[len++] = (signed char)x;
      if (x == ts[j]) break;
    }
  }
  *lenout = len;
}

static void dfs(int j, int lastamp, int lastdir, void (*visit)(int)) {
  if (gSweeping && remaining <= 0) return;
  if (j == gTargetK) {
    if (gRegime != 0) {
      int a = ts[j - 1], b = ts[j];
      if (!((a == chainL + 1 && b == chainH - 1) || (a == chainH - 1 && b == chainL + 1)))
        return;
    }
    visit(j);
    return;
  }
  int cur = ts[j];
  int minamp = 1;
  if (gRegime == 1) minamp = lastamp + 1;
  if (gRegime == 2) minamp = (j == 1) ? 1 : lastamp + 1;
  for (int dir = -1; dir <= 1; dir += 2) {
    if (lastdir != 0 && dir == lastdir) continue;
    for (int amp = minamp;; amp++) {
      int nxt = cur + dir * amp;
      if (nxt < chainL + 1 || nxt > chainH - 1) break;
      ts[j + 1] = nxt;
      dfs(j + 1, amp, dir, visit);
    }
  }
}

static void visit_sweep(int k) {
  signed char w[MAXW];
  int len;
  walk_of(k, w, &len);
  sweep(w, len);
}

static void sweep_all_with_k(int k) {
  gTargetK = k;
  gSweeping = 1;
  if (gRegime != 0 && k < 2) return;
  for (int c = chainL + 1; c <= chainH - 1 && remaining > 0; c++) {
    ts[0] = c;
    dfs(0, 0, 0, visit_sweep);
    if (remaining <= 0) return;
  }
}

/* minturns[i] = least turn count serving basepoint i, or -1 if none found. */
static void census_chain(const int *rho, int n, int regime, int kmax) {
  set_band(rho, n);
  gRegime = regime;
  for (int i = 0; i < n; i++) minturns[i] = -1;
  remaining = n;
  if (chainH - chainL < 3) return;
  for (int k = 1; k <= kmax && remaining > 0; k++) { curk = k; sweep_all_with_k(k); }
}

/* ------------------------------------------- the one-turn walks at a level */

/* The fold hypothesis of `foldsOnto_veeAt`, on the arm `f` of length m with
   f[0] = p: the arm stays at or below p+1 until it first reaches L+1. */
static int vee_hyp(const int *f, int m, int L) {
  int p = f[0];
  for (int j = 0; j < m; j++) {
    if (f[j] <= L + 1) return 1;
    if (f[j] > p + 1) return 0;
  }
  return 1;
}

/* The fold hypothesis of `foldsOnto_lamAt`. */
static int lam_hyp(const int *f, int m, int H) {
  int p = f[0];
  for (int j = 0; j < m; j++) {
    if (f[j] >= H - 1) return 1;
    if (f[j] < p - 1) return 0;
  }
  return 1;
}

static int armG_buf[MAXN], armT_buf[MAXN];

static void arms(const int *rho, int n, int i, int *mg, int *mt) {
  *mg = n - i;
  for (int j = 0; j < *mg; j++) armG_buf[j] = rho[i + j];
  *mt = i + 1;
  for (int j = 0; j < *mt; j++) armT_buf[j] = rho[i - j];
}

/* Section 1 and 2 on one chain.  Counts are over interior basepoints, i.e.
   those with L+3 <= rho[i] <= H-3. */
typedef struct {
  int interior;      /* interior basepoints                                  */
  int hypVee;        /* both arms satisfy the vee hypothesis                 */
  int hypLam;        /* both arms satisfy the lam hypothesis                 */
  int hypEither;     /* one of the two                                       */
  int servedVee;     /* veeAt(p) serves the basepoint (reachability)         */
  int servedLam;     /* lamAt(p) serves the basepoint                        */
  int servedEither;  /* one of the two, with base p                          */
  int servedNbr;     /* one of the two with base p-1, p or p+1               */
  int opposite;      /* the hypothesis of `not_oneTurn_of_opposite` holds    */
                     /* at every admissible base p-1, p, p+1                */
} Cover;

/* The hypothesis of `not_oneTurn_of_opposite` on one arm: some index at or
   above b+2 before any index at or below L+2. */
static int rises_early(const int *f, int m, int b, int L) {
  for (int j = 0; j < m; j++) {
    if (f[j] >= b + 2) return 1;
    if (f[j] <= L + 2) return 0;
  }
  return 0;
}

/* Its mirror: some index at or below b-2 before any index at or above H-2. */
static int falls_early(const int *f, int m, int b, int H) {
  for (int j = 0; j < m; j++) {
    if (f[j] <= b - 2) return 1;
    if (f[j] >= H - 2) return 0;
  }
  return 0;
}

static void cover_chain(const int *rho, int n, Cover *c) {
  set_band(rho, n);
  memset(c, 0, sizeof(*c));
  if (chainH - chainL < 6) return;
  for (int i = 0; i < n; i++) {
    int p = rho[i];
    if (p < chainL + 3 || p > chainH - 3) continue;
    c->interior++;
    int mg, mt;
    arms(rho, n, i, &mg, &mt);
    int hv = vee_hyp(armG_buf, mg, chainL) && vee_hyp(armT_buf, mt, chainL);
    int hl = lam_hyp(armG_buf, mg, chainH) && lam_hyp(armT_buf, mt, chainH);
    c->hypVee += hv;
    c->hypLam += hl;
    c->hypEither += (hv || hl);
    int sv = 0, sl = 0, snbr = 0;
    for (int db = -1; db <= 1; db++) {
      int b = p + db;
      if (b < chainL + 1 || b > chainH - 1) continue;
      signed char w[MAXW];
      int len, s1 = 0, s2 = 0;
      if (b >= chainL + 2) {
        ts[0] = b; ts[1] = chainL + 1; ts[2] = chainH - 1;
        walk_of(2, w, &len);
        s1 = walk_serves(w, len, i);
      }
      if (b <= chainH - 2) {
        ts[0] = b; ts[1] = chainH - 1; ts[2] = chainL + 1;
        walk_of(2, w, &len);
        s2 = walk_serves(w, len, i);
      }
      if (db == 0) { sv = s1; sl = s2; }
      if (s1 || s2) snbr = 1;
    }
    c->servedVee += sv;
    c->servedLam += sl;
    c->servedEither += (sv || sl);
    c->servedNbr += snbr;
    /* the obstruction hypothesis, at every admissible base */
    int opp = 1;
    for (int db = -1; db <= 1; db++) {
      int b = p + db;
      if (b < chainL + 2 || b > chainH - 2) continue;
      int o1 = rises_early(armG_buf, mg, b, chainL) && falls_early(armT_buf, mt, b, chainH);
      int o2 = falls_early(armG_buf, mg, b, chainH) && rises_early(armT_buf, mt, b, chainL);
      if (!(o1 || o2)) { opp = 0; break; }
    }
    c->opposite += opp;
  }
}

static void print_cover(const char *tag, const Cover *c) {
  printf("  %-14s interior %6d | vee-hyp %6d  lam-hyp %6d  either %6d"
         " | vee %6d  lam %6d  either %6d  +-1 %6d | unserved %6d  opposite %6d\n",
         tag, c->interior, c->hypVee, c->hypLam, c->hypEither,
         c->servedVee, c->servedLam, c->servedEither, c->servedNbr,
         c->interior - c->servedNbr, c->opposite);
}

/* ------------------------------------------------------------ subchains */

static unsigned long rngstate = 12345;
static unsigned long rnd(void) {
  rngstate = rngstate * 6364136223846793005UL + 1442695040888963407UL;
  return rngstate >> 17;
}

/* ---------------------------------------------------------------- main */

int main(int argc, char **argv) {
  if (argc > 1) rngstate = strtoul(argv[1], NULL, 10);

  printf("== section 1-2: the one-turn walks at the basepoint's level, bing 0 n ==\n");
  printf("  (counts are over interior basepoints, L+3 <= level <= H-3)\n");
  for (int nn = 6; nn <= 12; nn++) {
    Path p = bpath(0, nn);
    Cover c;
    cover_chain(p.v, p.n, &c);
    char tag[32];
    snprintf(tag, sizeof(tag), "bing 0 %d", nn);
    print_cover(tag, &c);
    free(p.v);
  }

  printf("\n== section 3: least number of turning targets, IsZigFree, bing 0 n ==\n");
  for (int nn = 4; nn <= 12; nn++) {
    Path p = bpath(0, nn);
    census_chain(p.v, p.n, 2, 8);
    int unserved = 0, maxk = 0, maxkint = 0, interior = 0;
    int besti = -1;
    for (int i = 0; i < p.n; i++) {
      if (minturns[i] < 0) { unserved++; continue; }
      if (minturns[i] > maxk) maxk = minturns[i];
      if (p.v[i] >= chainL + 3 && p.v[i] <= chainH - 3) {
        interior++;
        if (minturns[i] > maxkint) { maxkint = minturns[i]; besti = i; }
      }
    }
    printf("  bing 0 %-2d  links %6d  span %2d  unserved %d  max turns %d"
           "  interior %6d  max turns (interior) %d  first at %d\n",
           nn, p.n, chainH - chainL, unserved, maxk, interior, maxkint, besti);
    free(p.v);
  }

  printf("\n== section 4: random subchains of bing 0 12, span >= 6 ==\n");
  {
    Path p = bpath(0, 12);
    Cover tot;
    memset(&tot, 0, sizeof(tot));
    int trials = 0, unservedTotal = 0, maxk = 0;
    for (int t = 0; t < 400; t++) {
      int a = (int)(rnd() % (unsigned long)p.n);
      int b = (int)(rnd() % (unsigned long)p.n);
      if (a > b) { int s = a; a = b; b = s; }
      int m = b - a + 1;
      if (m < 20 || m > 3000) continue;
      int lo = p.v[a], hi = p.v[a];
      for (int u = a; u <= b; u++) { if (p.v[u] < lo) lo = p.v[u]; if (p.v[u] > hi) hi = p.v[u]; }
      if (hi - lo < 6) continue;
      trials++;
      Cover c;
      cover_chain(p.v + a, m, &c);
      tot.interior += c.interior;
      tot.hypVee += c.hypVee;
      tot.hypLam += c.hypLam;
      tot.hypEither += c.hypEither;
      tot.servedVee += c.servedVee;
      tot.servedLam += c.servedLam;
      tot.servedEither += c.servedEither;
      tot.servedNbr += c.servedNbr;
      tot.opposite += c.opposite;
      if (m <= 600) {
        census_chain(p.v + a, m, 2, 8);
        for (int i = 0; i < m; i++) {
          if (minturns[i] < 0) {
            unservedTotal++;
            printf("    UNSERVED subchain [%d,%d] basepoint %d level %d\n", a, b, i, p.v[a + i]);
          } else if (minturns[i] > maxk) maxk = minturns[i];
        }
      }
    }
    printf("  subchains tested %d\n", trials);
    print_cover("subchains", &tot);
    printf("  unserved basepoints %d, max turns over swept subchains %d\n", unservedTotal, maxk);
    free(p.v);
  }

  return 0;
}
