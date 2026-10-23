/* Census for batch 42 -- does the greedy three-leg engine survive at the
 * basepoint P = L + 4?
 *
 * `Val3`, `gstep3` and the greedy sequence are transcribed from
 * HPC/Fold/Leg3.lean.  The engine is proved there for L + 2 <= P <= L + 3.
 * Here the greedy is run as a finite automaton over
 *
 *      (level v, greedy time q, monotone flags about the arm's past)
 *
 * for arbitrary 1-Lipschitz arms in [L, H] starting at P, subject to a guard
 * that says when the arm is allowed to step to the floor.  The automaton is
 * exact: the flags are monotone functions of the past, so the reachable set is
 * exactly the set of (level, time, history) triples realised by some arm.  If
 * no reachable state violates `Val3`, the engine works for that P and that
 * guard, for every arm obeying the guard, of any length.
 *
 * Guards tested (K = H - 1, so the ceiling announcement is vacuous):
 *   0 : no guard at all
 *   1 : the repository's R -- the arm has been at K, or at L+1 and then at K-1
 *   2 : before the arm ever drops to L + 1 it has been at K - 1
 *   3 : before the arm ever drops to L + 1 it has been at K
 *
 * Usage: census-batch42d L H K P guard
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int L, H, K, P;

static int Val3(int v, int u) {
  return (0 <= u && u <= K - P + 1 && v - P <= u && u <= v - P + 2) ||
         (K - P + 1 <= u && u <= 2*K - P - L && 2*K - P - v <= u && u <= 2*K - P + 2 - v) ||
         (2*K - P - L <= u && u <= 2*K - P - 2*L + H - 2 &&
          v - 2*L - P + 2*K - 2 <= u && u <= v - 2*L - P + 2*K);
}

static int gstep3(int v, int q) {
  if (Val3(v, q + 1)) return q + 1;
  if (Val3(v, q)) return q;
  return q - 1;
}

/* flags, all monotone in time:
 *   bit 0 : the arm has been at K - 1 or above
 *   bit 1 : the arm has been at K or above
 *   bit 2 : the arm has been at L + 1 or below
 *   bit 3 : the arm has been at L + 1 or below and after that at K - 1 or above
 *   bit 4 : the arm has been at L + 1 or below and after that at K or above
 */
#define NF 32

static int flag_update(int fl, int v) {
  int nf = fl;
  if (v >= K - 1) { nf |= 1; if (fl & 4) nf |= 8; }
  if (v >= K)     { nf |= 2; if (fl & 4) nf |= 16; }
  if (v <= L + 1) nf |= 4;
  return nf;
}

static int guard_ok(int guard, int fl, int v2) {
  switch (guard) {
    case 0: return 1;
    case 1: return (v2 > L) || (fl & 2) || (fl & 8);
    case 2: return (v2 > L + 1) || (fl & 1);
    case 3: return (v2 > L + 1) || (fl & 2);
  }
  return 1;
}

int main(int argc, char **argv) {
  L = argc > 1 ? atoi(argv[1]) : 0;
  H = argc > 2 ? atoi(argv[2]) : 9;
  K = argc > 3 ? atoi(argv[3]) : 8;
  P = argc > 4 ? atoi(argv[4]) : 4;
  int guard = argc > 5 ? atoi(argv[5]) : 0;
  int QMAX = 2*K - P - 2*L + H;          /* q stays in [-2, leg3Len] */
  int QOFF = 4;
  int nq = QMAX + QOFF + 4;
  int nv = H - L + 1;
  static char seen[64][256][NF];
  memset(seen, 0, sizeof seen);
  int stack[64*256*NF][3], sp = 0;
  int q0 = 0;
  if (!Val3(P, q0)) { printf("start not valid\n"); return 1; }
  int f0 = flag_update(0, P);
  seen[P - L][q0 + QOFF][f0] = 1;
  stack[sp][0] = P; stack[sp][1] = q0; stack[sp][2] = f0; sp++;
  long long states = 0, bad = 0;
  while (sp > 0) {
    sp--;
    int v = stack[sp][0], q = stack[sp][1], fl = stack[sp][2];
    states++;
    for (int d = -1; d <= 1; d++) {
      int v2 = v + d;
      if (v2 < L || v2 > H) continue;
      if (!guard_ok(guard, fl, v2)) continue;
      if (v2 >= K + 2) continue;               /* vacuous when K = H - 1 */
      int q2 = gstep3(v2, q);
      int fl2 = flag_update(fl, v2);
      if (!Val3(v2, q2)) {
        bad++;
        if (bad <= 5)
          printf("VIOLATION: level %d -> %d, time %d -> %d, flags %d\n", v, v2, q, q2, fl);
        continue;
      }
      if (q2 + QOFF < 0 || q2 + QOFF >= nq) { printf("q out of range %d\n", q2); continue; }
      if (v2 - L >= nv) continue;
      if (seen[v2 - L][q2 + QOFF][fl2]) continue;
      seen[v2 - L][q2 + QOFF][fl2] = 1;
      stack[sp][0] = v2; stack[sp][1] = q2; stack[sp][2] = fl2; sp++;
    }
  }
  printf("L=%d H=%d K=%d P=%d guard=%d : reachable states %lld, violations %lld\n",
         L, H, K, P, guard, states, bad);
  return 0;
}
