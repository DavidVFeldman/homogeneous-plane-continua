"""check70.py -- the independent re-check of the batch-70 finding.

The finding of batch 70 is that `BothNineL5` is inhabited: there are crossings of
the trichotomy at the branch `L + 5`, in faithful pairs of span nine, at which
*both* arms reach `L + 9`.  `census-batch70.c` writes the first one it stores to
`witness-batch70.txt` (the whole pair, the basepoint, and which side carries the
`w8` sentence), and this script re-checks it from scratch, with every predicate
written out again independently of the census's C:

  * IsCrookedIvF (rho, sig) -- the definition of HPC/Fold/Faithful.lean, with the
    crookedness clause searched literally over all pairs of times and all levels
    the neighbouring links carry;
  * rho i = 5, and LowAt (arm) 1 8 on both arms -- HPC/Fold/Leaf.lean;
  * Leg4Land, written out literally from HPC/Fold/Leg4Land.lean (no greedy
    reading), for the three walks of the trichotomy: w8 = (K,M,P) = (8,1,5) on
    the arm, wb = (6,2,4) and w3 = (6,1,4) on the reflected arm; the basepoint is
    a crossing exactly when no one of the three serves both arms;
  * both arms reach 9;
  * FoldsOnto, as the reachability dynamic program of HPC/Fold/Decide.lean, for
    the walks of the four-leg family leg4Walk 0 9 K M P and their reflections --
    to see which walk, if any, serves the crossing.

Usage: python3 check70.py [witness-batch70.txt]
"""

import sys


def faithful(rho, sig):
    n = len(rho)
    for t in range(n):
        if not (rho[t] <= sig[t] <= rho[t] + 1):
            return False, "width at %d" % t
    for t in range(n - 1):
        if max(sig[t], sig[t + 1]) > min(rho[t], rho[t + 1]) + 1:
            return False, "adjacency at %d" % t
    # the crookedness clause, searched literally
    def carries(u, lev):
        return 0 <= u < n and rho[u] <= lev <= sig[u]

    def levels_near(t):
        out = set()
        for u in (t - 1, t, t + 1):
            if 0 <= u < n:
                out.update(range(rho[u], sig[u] + 1))
        return out

    # first(lev, j) = least r >= j carrying lev, or n
    maxlev = max(sig) + 2
    first = [[n] * (n + 1) for _ in range(maxlev + 2)]
    for lev in range(maxlev + 2):
        for j in range(n - 1, -1, -1):
            first[lev][j] = j if carries(j, lev) else first[lev][j + 1]
    for s in range(n):
        hs = levels_near(s)
        for t in range(s + 1, n):
            ks = levels_near(t)
            for h in hs:
                for k in ks:
                    if abs(h - k) < 3:
                        continue
                    r1 = k - 1 if h < k else k + 1
                    r2 = h + 1 if h < k else h - 1
                    p1 = first[r1][s + 1]
                    if p1 >= t:
                        return False, "crookedness at (%d,%d,%d,%d)" % (s, t, h, k)
                    p2 = first[r2][p1 + 1]
                    if p2 >= t:
                        return False, "crookedness at (%d,%d,%d,%d)" % (s, t, h, k)
    return True, "faithful"


def low_at(f, tl=1, th=8):
    """LowAt f tl th of HPC/Fold/Leaf.lean, searched literally."""
    m = len(f)
    for d in range(m):
        if f[d] > tl:
            continue
        ok = any(f[j] >= th for j in range(d))
        if not ok:
            ok = any(f[j] <= tl + 1 and f[jp] >= th - 2
                     for j in range(d) for jp in range(j + 1, d))
        if not ok:
            return False
    return True


def leg4land(f, K, M, P, H=9):
    """Leg4Land f H K M P at L = 0, existentials searched literally."""
    m = len(f)
    A = K - P + 1
    if not (P - 2 <= f[0] <= P):
        return False
    for d in range(m):
        if f[d] <= P - 3:
            if not any(j >= A and f[j] >= K - 1 and j + (K - 1 - f[d]) <= d
                       for j in range(m)):
                return False
        if f[d] <= M - 2:
            ok = False
            for j in range(A, m):
                if f[j] < K - 1:
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
            for j in range(A, m):
                if f[j] < K - 1:
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


def walk_of(levels):
    w = [levels[0]]
    for t in levels[1:]:
        s = 1 if t > w[-1] else -1
        while w[-1] != t:
            w.append(w[-1] + s)
    return w


def folds(f, w):
    """FoldsOnto f (len w) w, by the reachability dynamic program."""
    cur = set()
    if abs(f[0] - w[0]) <= 1:
        cur.add(0)
    for x in f[1:]:
        nxt = set()
        for u in cur:
            for u2 in (u - 1, u, u + 1):
                if 0 <= u2 < len(w) and abs(x - w[u2]) <= 1:
                    nxt.add(u2)
        cur = nxt
        if not cur:
            return False
    return bool(cur)


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "witness-batch70.txt"
    with open(path) as fp:
        head = fp.readline().split()
        n, i, gside = int(head[0]), int(head[1]), int(head[2])
        rho = [int(x) for x in fp.readline().split()]
        sig = [int(x) for x in fp.readline().split()]
    assert len(rho) == n and len(sig) == n
    print("the witness: %d links, basepoint %d, the w8 side is the %s arm"
          % (n, i, "forward" if gside else "backward"))
    print("  levels run from %d to %d" % (min(rho), max(sig)))
    ok, why = faithful(rho, sig)
    print("  IsCrookedIvF: %s (%s)" % (ok, why))
    print("  rho i = %d" % rho[i])
    armG = rho[i:]
    armT = rho[i::-1]
    reflG = [9 - x for x in armG]
    reflT = [9 - x for x in armT]
    print("  arm lengths: forward %d, backward %d" % (len(armG), len(armT)))
    print("  LowAt on the forward arm: %s; on the backward arm: %s"
          % (low_at(armG), low_at(armT)))
    print("  the forward arm reaches 9: %s (first at arm index %s)"
          % (9 in armG, armG.index(9) if 9 in armG else None))
    print("  the backward arm reaches 9: %s (first at arm index %s)"
          % (9 in armT, armT.index(9) if 9 in armT else None))
    tags = {}
    tags["w8"] = (leg4land(armG, 8, 1, 5), leg4land(armT, 8, 1, 5))
    tags["wb"] = (leg4land(reflG, 6, 2, 4), leg4land(reflT, 6, 2, 4))
    tags["w3"] = (leg4land(reflG, 6, 1, 4), leg4land(reflT, 6, 1, 4))
    for name, (a, b) in tags.items():
        print("  %s: forward %s, backward %s" % (name, a, b))
    crossing = not any(a and b for a, b in tags.values())
    print("  a crossing of the trichotomy (no one of the three serves both arms): %s" % crossing)
    print("  w72 = (7,2,5) on the forward arm: %s; on the backward arm: %s"
          % (leg4land(armG, 7, 2, 5), leg4land(armT, 7, 2, 5)))
    served = []
    for P in range(2, 7):
        for K in range(P, 9):
            for M in range(1, P - 1):
                if M + 3 > K:
                    continue
                for refl in (0, 1):
                    lv = [P - 1, K, M, 8, 1]
                    if refl:
                        lv = [9 - x for x in lv]
                    if len(set(zip(lv, lv[1:]))) != len(lv) - 1 or any(
                            lv[q] == lv[q + 1] for q in range(len(lv) - 1)):
                        continue
                    w = walk_of(lv)
                    if folds(armG, w) and folds(armT, w):
                        served.append((("reflected" if refl else "direct"), P, K, M, tuple(lv)))
    print("  walks of the four-leg family serving both arms: %d" % len(served))
    for s in served[:6]:
        print("    %s P=%d K=%d M=%d : %s" % s)


if __name__ == "__main__":
    main()
