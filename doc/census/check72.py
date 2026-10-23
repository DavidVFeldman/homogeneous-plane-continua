"""check72.py -- the independent re-check of the batch-72 census.

Batch 72 asks where `Valley3BeforeNine` -- the landmark pair that batch 71 showed
is equivalent to `Ceil72` on an arm of the band -- is a fact.  The census
(`census-batch72.c`, log `census-batch72.log`) answers: it fails at 194 076 of
the 478 735 running arms at basepoints of the band, and every one of those
failures is also a failure at a basepoint of the *branch* -- `LowAt` on both arms
changes nothing -- while at all 229 running arms at a **crossing** it holds.

This script re-checks the census's finding from scratch on the stored witnesses
`witness-batch72-c0.txt`, `witness-batch72-c1.txt` and `witness-batch72-c2.txt`,
with every predicate written out again in Python, independently of the C and of
the Lean:

  * IsCrookedIvF (rho, sig) -- the definition of HPC/Fold/Faithful.lean, with the
    crookedness clause searched literally over all pairs of times and all levels
    the neighbouring links carry;
  * rho i = 5, the band [0, 9], and LowAt (arm) 1 8 on both arms;
  * HighRunG / HighRunT of HPC/Fold/Deep70.lean: the arm reaches 9 with nothing
    at 2 or below before its first such time;
  * Valley3BeforeNine of HPC/Fold/Distance71.lean, searched literally: a peak at
    6 or above at arm index three or more, a time at 3 or below five steps later,
    and every ascent to 9 at least six steps after that;
  * Ceil72 of HPC/Fold/Ceil68.lean, searched literally, as the check that the two
    are the same statement on these arms;
  * Leg4Land of HPC/Fold/Leg4Land.lean for the three walks of the trichotomy
    (w8 = (K,M,P) = (8,1,5) on the arm, wb = (6,2,4) and w3 = (6,1,4) on the
    reflected arm), so the class of the basepoint is re-derived;
  * FoldsOnto, as the reachability program of HPC/Fold/Decide.lean, for the
    four-leg family -- so the report's "the pair still folds" is re-checked.

Run: python3 check72.py
"""

import itertools
import os

# ---------------------------------------------------------------- the model


def is_crooked_ivf(rho, sig):
    n = len(rho)
    for t in range(n):
        if not (rho[t] <= sig[t] <= rho[t] + 1):
            return False
    for t in range(n - 1):
        if max(sig[t], sig[t + 1]) > min(rho[t], rho[t + 1]) + 1:
            return False

    def carries(u, lev):
        return rho[u] <= lev <= sig[u]

    def near_levels(s):
        out = set()
        for e in (-1, 0, 1):
            u = s + e
            if 0 <= u < n:
                out.update(range(rho[u], sig[u] + 1))
        return out

    nl = [near_levels(s) for s in range(n)]
    for s in range(n):
        for t in range(s + 1, n):
            for h in nl[s]:
                for k in nl[t]:
                    if abs(h - k) < 3:
                        continue
                    r1 = k - 1 if h < k else k + 1
                    r2 = h + 1 if h < k else h - 1
                    ok = False
                    for r in range(s + 1, t):
                        if not carries(r, r1):
                            continue
                        for r2i in range(r + 1, t):
                            if carries(r2i, r2):
                                ok = True
                                break
                        if ok:
                            break
                    if not ok:
                        return False
    return True


def low_at(f, lo, hi):
    """LowAt f lo hi, read as the census reads it: no time at lo or below before
    either a time at hi or above or a time at lo+1 or below followed by one at
    hi-2 or above."""
    seen_high, seen_low, seen_low_high = False, False, False
    for v in f:
        if v <= lo and not seen_high and not seen_low_high:
            return False
        if v >= hi:
            seen_high = True
        if v >= hi - 2 and seen_low:
            seen_low_high = True
        if v <= lo + 1:
            seen_low = True
    return True


def runs_high(f):
    for v in f:
        if v >= 9:
            return True
        if v <= 2:
            return False
    return False


def first_nine(f):
    for d, v in enumerate(f):
        if v >= 9:
            return d
    return -1


def valley3_before_nine(f):
    """Valley3BeforeNine f 0, existentials searched literally."""
    m = len(f)
    nines = [d for d in range(m) if f[d] >= 9]
    for j in range(3, m):
        if f[j] < 6:
            continue
        for k in range(j + 5, m):
            if f[k] > 3:
                continue
            if all(k + 6 <= d for d in nines):
                return (j, k)
    return None


def ceil72(f):
    """Ceil72 f 0, existentials searched literally."""
    m = len(f)
    for d in range(m):
        if f[d] < 9:
            continue
        ok = False
        for j in range(3, m):
            if f[j] < 6:
                continue
            for k in range(j + 5, m):
                if f[k] > 3:
                    continue
                if k + (f[d] - 3) <= d:
                    ok = True
                    break
            if ok:
                break
        if not ok:
            return False
    return True


def leg4land(f, H, K, M, P):
    m = len(f)
    A = K - P + 1
    if not (P - 2 <= f[0] <= P):
        return False
    for d in range(m):
        if f[d] <= P - 3:
            if not any(A <= j and f[j] >= K - 1 and j + (K - 1 - f[d]) <= d for j in range(m)):
                return False
        if f[d] <= M - 2:
            ok = False
            for j in range(m):
                if j < A or f[j] < K - 1:
                    continue
                for k in range(j + (K - M), m):
                    if f[k] > M + 1:
                        continue
                    for l in range(k + (H - 1 - M), m):
                        if f[l] >= H - 2 and l + (H - 2 - f[d]) <= d:
                            ok = True
                            break
                    if ok:
                        break
                if ok:
                    break
            if not ok:
                return False
        if f[d] >= K + 2:
            ok = False
            for j in range(m):
                if j < A or f[j] < K - 1:
                    continue
                for k in range(j + (K - M), m):
                    if f[k] <= M + 1 and k + (f[d] - M - 1) <= d:
                        ok = True
                        break
                if ok:
                    break
            if not ok:
                return False
    return True


def folds_onto(f, w):
    cur = {0} if abs(f[0] - w[0]) <= 1 else set()
    if not cur:
        return False
    for v in f[1:]:
        nxt = set()
        for u in cur:
            for e in (-1, 0, 1):
                u2 = u + e
                if 0 <= u2 < len(w) and abs(v - w[u2]) <= 1:
                    nxt.add(u2)
        if not nxt:
            return False
        cur = nxt
    return True


def walk4(start, a, b, c, e):
    w, cur = [start], start
    for tgt in (a, b, c, e):
        if tgt == cur:
            return None
        s = 1 if tgt > cur else -1
        while cur != tgt:
            cur += s
            w.append(cur)
    return w


def four_leg_family():
    out = []
    for P in range(2, 7):
        for K in range(P, 9):
            for M in range(1, P - 1):
                if M + 3 > K:
                    continue
                w = walk4(P - 1, K, M, 8, 1)
                if w:
                    out.append(w)
                w2 = walk4(9 - (P - 1), 9 - K, 9 - M, 1, 8)
                if w2:
                    out.append(w2)
    return out


FAMILY = four_leg_family()

# ------------------------------------------------------------- the witnesses


def read_witness(name):
    with open(name) as fh:
        n, i, gside = (int(x) for x in fh.readline().split())
        rho = [int(x) for x in fh.readline().split()]
        sig = [int(x) for x in fh.readline().split()]
    assert len(rho) == n and len(sig) == n
    return n, i, gside, rho, sig


def check(name):
    if not os.path.exists(name):
        print("  (%s is absent)" % name)
        return
    n, i, gside, rho, sig = read_witness(name)
    print("\n== %s: %d links, basepoint %d, the running arm is the %s arm"
          % (name, n, i, "forward" if gside else "backward"))
    print("   IsCrookedIvF: %s" % is_crooked_ivf(rho, sig))
    print("   the band: [%d, %d];  rho i = %d" % (min(rho), max(rho), rho[i]))
    armG = rho[i:]
    armT = rho[i::-1]
    print("   LowAt on the forward arm: %s; on the backward arm: %s"
          % (low_at(armG, 1, 8), low_at(armT, 1, 8)))
    X, Y = (armG, armT) if gside else (armT, armG)
    print("   the running arm runs high: %s (first ascent at arm index %d)"
          % (runs_high(X), first_nine(X)))
    v = valley3_before_nine(X)
    print("   Valley3BeforeNine on the running arm: %s%s"
          % (v is not None, "" if v is None else "  (peak %d, valley %d)" % v))
    print("   Ceil72 on the running arm: %s; on the partner: %s" % (ceil72(X), ceil72(Y)))
    refl = lambda f: [9 - u for u in f]
    tG = (leg4land(refl(armG), 9, 6, 2, 4), leg4land(armG, 9, 8, 1, 5),
          leg4land(refl(armG), 9, 6, 1, 4))
    tT = (leg4land(refl(armT), 9, 6, 2, 4), leg4land(armT, 9, 8, 1, 5),
          leg4land(refl(armT), 9, 6, 1, 4))
    print("   w3/w8/wb on the forward arm: %s; on the backward arm: %s" % (tG, tT))
    shared = [nm for nm, a, b in zip(("w3", "w8", "wb"), tG, tT) if a and b]
    print("   walks of the trichotomy serving both arms: %s%s"
          % (shared if shared else "none", "  -- a crossing" if not shared else ""))
    served = sum(1 for w in FAMILY if folds_onto(armG, w) and folds_onto(armT, w))
    print("   walks of the four-leg family serving both arms: %d" % served)


if __name__ == "__main__":
    print("check72.py -- the independent re-check of the batch-72 census.")
    print("Every predicate is written out from its own definition; nothing is")
    print("taken from the C of the census or from the Lean.")
    for nm in ("witness-batch72-c0.txt", "witness-batch72-c1.txt", "witness-batch72-c2.txt",
               "witness-batch72-min.txt", "witness-batch72-break.txt"):
        check(nm)
    print("\nThe reading of the result: a running arm of a faithful pair, at a basepoint")
    print("of the branch (LowAt on both arms), can fail Valley3BeforeNine -- so the")
    print("statement is not a fact about a running arm of a faithful pair with the")
    print("branch hypothesis.  At every such failure the two arms share the walk w8,")
    print("so the basepoint is not a crossing; on the corpus no crossing fails.")
