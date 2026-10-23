// Batch 124, item 1 (Q1): census for the pair form of Bing's Theorem 3 (Theorem3Pair) in the model
// of batch 122, for longer fine chains than the Python census of batch 123.
//
// Model (BHyp): fine links t < n with coarse interval [rho t, sigma t] (width <= 1, adjacent links
// compatible), meeting table T = forced meetings (own interval and the neighbours' intervals);
// at the two end links any subset of the possible unforced meetings may be added (interior extra
// meetings only add crookedness obligations and do not enter the conclusion, so the forced table
// is the most general there).  Crookedness (1948) read with T.
// Question: for every adjacent pair (i, i+1) lying in a common coarse link, is there a time function
// beta with beta(i) = beta(i+1) = 0, moving by at most one, every fibre in a window {j, j+1}
// (j <= sigma, rho <= j+1), and Bing's end clause ("or" reading)?
// Usage: recon-batch124-pair N K [pair|only] [special]   (special: only instances whose interior
// links do not meet levels 0 and K-1 while link 0 meets 0 and link n-1 meets K-1 -- Bing's special
// case).  Mode `only`: for every link that can be covered by its neighbours (necessary conditions
// in `coverable`), is there a solution with beta(i) = 0 for which the only-clause holds, i.e. not
// both neighbours in one block other than that of i (interior), resp. the neighbour in the block
// of the end link?  Mode `thm4`: Theorem 4 as printed (outside the degenerate case K = 3, r = s):
// for all r <= s with D(r, s) meeting levels 0 and K-1, beta with beta(r) = 0, beta(s) maximal,
// windows, and the only-clauses at r and s (as in mode `only`).
// Not Lean-checked.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
using namespace std;

int N, K, SPECIAL, MODE;  // MODE 0: pair form; 1: only-clause at covered links (see below)
int ONLYI = -1;  // MODE 1: the basepoint whose neighbours are checked at the end
int T4R = -1, T4S = -1;  // MODE 2: Theorem 4, the links r <= s
int R[64], S[64];
unsigned T[64];   // bitmask of coarse links met
long long inst = 0, pairs = 0, fails = 0, seqcount = 0;

unsigned own(int t) { unsigned m = 0; for (int j = R[t]; j <= S[t]; j++) m |= 1u << j; return m; }
unsigned possm(int t) { unsigned m = 0; for (int j = 0; j < K; j++) if (S[t] <= j + 1 && j <= R[t] + 1) m |= 1u << j; return m; }

// crookedness for the pair (s,t), s<t, witnesses in (s,t)
bool crkpair(int s, int t) {
  for (int a = 0; a < K; a++) if (T[s] >> a & 1)
    for (int b = 0; b < K; b++) if (T[t] >> b & 1) {
      if (a + 3 <= b) {
        bool ok = false;
        for (int r = s + 1; r < t && !ok; r++) if (R[r] <= b - 1 && b - 1 <= S[r])
          for (int r2 = r + 1; r2 < t; r2++) if (R[r2] <= a + 1 && a + 1 <= S[r2]) { ok = true; break; }
        if (!ok) return false;
      }
      if (b + 3 <= a) {
        bool ok = false;
        for (int r = s + 1; r < t && !ok; r++) if (R[r] <= b + 1 && b + 1 <= S[r])
          for (int r2 = r + 1; r2 < t; r2++) if (R[r2] <= a - 1 && a - 1 <= S[r2]) { ok = true; break; }
        if (!ok) return false;
      }
    }
  return true;
}

// ---- beta search ----
int B[64];
unsigned Wb[128];  // window mask of each block value
unsigned win(int t) { unsigned m = 0; for (int j = 0; j + 1 < K; j++) if (j <= S[t] && R[t] <= j + 1) m |= 1u << j; return m; }
unsigned WIN[64];
int order[64]; int pi;

bool coverable(int i);
bool onlyok(int i) {
  // the only-clause at i can fail only if i is coverable and its neighbours sit in another block
  if (!coverable(i)) return true;
  if (i > 0 && i + 1 < N) return !(B[i - 1] == B[i + 1] && B[i - 1] != B[i]);
  if (i == 0) return N == 1 || B[1] == B[0];
  return B[N - 2] == B[N - 1];
}
bool endok() {
  if (T4R >= 0) {
    int mx = 0; for (int t = 0; t < N; t++) if (B[t] > mx) mx = B[t];
    if (B[T4S] != mx) return false;
    if (!onlyok(T4R) || !onlyok(T4S)) return false;
    return true;  // Theorem 4 has no end clause
  }
  if (ONLYI >= 0) {
    int i = ONLYI;
    if (i > 0 && i + 1 < N && B[i - 1] == B[i + 1] && B[i - 1] != B[i]) return false;
    if (i == 0 && B[1] != B[0]) return false;
    if (i == N - 1 && B[N - 2] != B[N - 1]) return false;
  }
  for (int e : {0, N - 1}) {
    if (!((T[e] & 1u) || (T[e] >> (K - 1) & 1u))) continue;
    bool lo = true, hi = true;
    for (int t = 0; t < N; t++) if (B[t] == B[e]) { if (R[t] > 1) lo = false; if (S[t] < K - 2) hi = false; }
    if (!lo && !hi) return false;
  }
  return true;
}

bool solve(int i) {
  pi = i;
  for (int v = 0; v < 128; v++) Wb[v] = ~0u;
  unsigned w = WIN[i] & WIN[i + 1];
  if (!w) return false;
  Wb[0] = w; B[i] = 0; B[i + 1] = 0;
  int idx = 0;
  for (int t = i + 2; t < N; t++) order[idx++] = t;
  for (int t = i - 1; t >= 0; t--) order[idx++] = t;
  struct L { static bool run(int k, int tot) {
    if (k == tot) {
      return endok();
    }
    int t = order[k];
    int nb = (t > pi) ? B[t - 1] : B[t + 1];
    for (int d = -1; d <= 1; d++) {
      int v = nb + d; if (v < 0) continue;
      unsigned w2 = Wb[v] & WIN[t]; if (!w2) continue;
      unsigned old = Wb[v]; Wb[v] = w2; B[t] = v;
      if (run(k + 1, tot)) { Wb[v] = old; return true; }
      Wb[v] = old;
    }
    return false; } };
  return L::run(0, idx);
}

bool solveOnly(int i) {
  pi = i; ONLYI = i;
  for (int v = 0; v < 128; v++) Wb[v] = ~0u;
  Wb[0] = WIN[i]; B[i] = 0;
  int idx = 0;
  for (int t = i + 1; t < N; t++) order[idx++] = t;
  for (int t = i - 1; t >= 0; t--) order[idx++] = t;
  struct L { static bool run(int k, int tot) {
    if (k == tot) return endok();
    int t = order[k];
    int nb = (t > pi) ? B[t - 1] : B[t + 1];
    for (int d = -1; d <= 1; d++) {
      int v = nb + d; if (v < 0) continue;
      unsigned w2 = Wb[v] & WIN[t]; if (!w2) continue;
      unsigned old = Wb[v]; Wb[v] = w2; B[t] = v;
      if (run(k + 1, tot)) { Wb[v] = old; return true; }
      Wb[v] = old;
    }
    return false; } };
  bool r = L::run(0, idx);
  ONLYI = -1;
  return r;
}

// MODE 1: can link i be covered by its neighbours in a chain?  Necessary conditions used:
// interior i: T(i) within T(i-1) u T(i+1), and every coarse link containing both neighbours
// contains link i; end link 0: link 0 inside link 1, so [rho 1, sigma 1] within [rho 0, sigma 0]
// and T(0) within T(1) (symmetrically at n-1).
bool coverable(int i) {
  if (i > 0 && i + 1 < N) {
    if (T[i] & ~(T[i - 1] | T[i + 1])) return false;
    unsigned both = own(i - 1) & own(i + 1);
    if (both & ~own(i)) return false;
    return true;
  }
  int j = (i == 0) ? 1 : N - 2;
  if (own(j) & ~own(i)) return false;
  if (T[i] & ~T[j]) return false;
  return true;
}

bool solveT4(int r, int sx) {
  pi = r; T4R = r; T4S = sx;
  for (int v = 0; v < 128; v++) Wb[v] = ~0u;
  Wb[0] = WIN[r]; B[r] = 0;
  int idx = 0;
  for (int t = r + 1; t < N; t++) order[idx++] = t;
  for (int t = r - 1; t >= 0; t--) order[idx++] = t;
  struct L { static bool run(int k, int tot) {
    if (k == tot) return endok();
    int t = order[k];
    int nb = (t > pi) ? B[t - 1] : B[t + 1];
    for (int d = -1; d <= 1; d++) {
      int v = nb + d; if (v < 0) continue;
      unsigned w2 = Wb[v] & WIN[t]; if (!w2) continue;
      unsigned old = Wb[v]; Wb[v] = w2; B[t] = v;
      if (run(k + 1, tot)) { Wb[v] = old; return true; }
      Wb[v] = old;
    }
    return false; } };
  bool res = L::run(0, idx);
  T4R = T4S = -1;
  return res;
}

void report(int i) {
  printf("FAIL i=%d :", i);
  for (int t = 0; t < N; t++) printf(" (%d,%d)", R[t], S[t]);
  printf("  T:");
  for (int t = 0; t < N; t++) printf(" %x", T[t]);
  printf("\n");
  fflush(stdout);
}

void full() {
  seqcount++;
  // forced tables
  unsigned base[64];
  for (int t = 0; t < N; t++) {
    unsigned m = own(t);
    if (t > 0) m |= own(t - 1);
    if (t + 1 < N) m |= own(t + 1);
    base[t] = m;
  }
  unsigned x0 = possm(0) & ~base[0], x1 = possm(N - 1) & ~base[N - 1];
  // enumerate subsets of extras at the ends
  for (unsigned s0 = x0;; s0 = (s0 - 1) & x0) {
    for (unsigned s1 = x1;; s1 = (s1 - 1) & x1) {
      for (int t = 0; t < N; t++) T[t] = base[t];
      T[0] |= s0; T[N - 1] |= s1;
      bool ok = true;
      for (int s = 0; s < N && ok; s++) for (int t = s + 1; t < N && ok; t++) ok = crkpair(s, t);
      if (ok && SPECIAL) {
        if (!(T[0] & 1u) || !(T[N - 1] >> (K - 1) & 1u)) ok = false;
        for (int t = 1; t + 1 < N && ok; t++) if ((T[t] & 1u) || (T[t] >> (K - 1) & 1u)) ok = false;
      }
      if (ok) {
        inst++;
        for (int t = 0; t < N; t++) WIN[t] = win(t);
        if (MODE == 0) {
          for (int i = 0; i + 1 < N; i++) {
            if (!(own(i) & own(i + 1))) continue;
            pairs++;
            if (!solve(i)) { fails++; report(i); }
          }
        } else if (MODE == 2) {
          for (int r = 0; r < N; r++) for (int sx = r; sx < N; sx++) {
            bool m0 = false, m1 = false;
            for (int t = r; t <= sx; t++) { if (T[t] & 1u) m0 = true; if (T[t] >> (K - 1) & 1u) m1 = true; }
            if (!m0 || !m1) continue;
            if (r == sx && K == 3) continue;
            pairs++;
            if (!solveT4(r, sx)) { fails++; printf("T4 r=%d s=%d ", r, sx); report(r); }
          }
        } else {
          for (int i = 0; i < N; i++) {
            if (!coverable(i)) continue;
            pairs++;
            if (!solveOnly(i)) { fails++; report(i); }
          }
        }
      }
      if (s1 == 0) break;
    }
    if (s0 == 0) break;
  }
}

// generate sequences, pruning by crookedness of completed pairs with forced tables
void gen(int t) {
  if (t == N) { full(); return; }
  for (int r = 0; r < K; r++) for (int s = r; s <= r + 1 && s < K; s++) {
    if (t > 0 && !(S[t - 1] <= r + 1 && s <= R[t - 1] + 1)) continue;
    if (SPECIAL && t > 0) {
      // interior links (t >= 1, and t-1 >= 1 interior once t+... ) must not lie in levels 0 / K-1
      if (r == 0 && t >= 1) { /* link t would meet 0: allowed only if t == N-1 is impossible (needs K-1) */ continue; }
    }
    R[t] = r; S[t] = s;
    // prune: link t-1's forced table is now complete (except end extras); check pairs (s', t-1)
    bool ok = true;
    if (t >= 1) {
      for (int u = 0; u <= t - 1; u++) {
        unsigned m = own(u);
        if (u > 0) m |= own(u - 1);
        m |= own(u + 1);
        T[u] = m;
      }
      int u = t - 1;
      for (int s2 = 0; s2 < u && ok; s2++) ok = crkpair(s2, u);
    }
    if (ok) gen(t + 1);
  }
}

int main(int argc, char** argv) {
  N = atoi(argv[1]); K = atoi(argv[2]);
  MODE = (argc > 3 && argv[3][0] == 'o') ? 1 : (argc > 3 && argv[3][0] == 't') ? 2 : 0;
  SPECIAL = (argc > 4 && argv[4][0] == 's') || (argc > 3 && argv[3][0] == 's');
  gen(0);
  printf("mode=%s ", MODE == 1 ? "only" : MODE == 2 ? "thm4" : "pair");
  printf("N=%d K=%d special=%d sequences=%lld instances=%lld pairs=%lld failures=%lld\n", N, K,
         SPECIAL, seqcount, inst, pairs, fails);
}
