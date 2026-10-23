#!/usr/bin/env python3
"""Census for batch 23: the three conjectures over the faithful model.

Implements `IsCrookedIvF` (geometric adjacency + forced-meeting crookedness) and the
conclusions of `ExitReachF`, `HighExitValleyF`, `LowExitPeakF` exactly as they are stated in
HPC/Fold/ClosureF.lean, with H and L the attained maximum and minimum of rho (the statements
force this, since they demand `L <= rho <= H` together with attainment).

Usage:
  python3 census-batch23.py exhaustive LEN LEVELS
  python3 census-batch23.py random LEN LEVELS TRIALS [SEED]
"""

import sys, random


# ---------------------------------------------------------------- the model

def meets(rho, sig, s):
    """The levels a link forced to meet near index s: the union of the intervals of s-1,s,s+1."""
    n = len(rho)
    out = set()
    for u in range(max(0, s - 1), min(n, s + 2)):
        for h in range(rho[u], sig[u] + 1):
            out.add(h)
    return sorted(out)


def crooked_ok(rho, sig, s, t):
    """The crookedness clause of IsCrookedIvF for the pair (s, t)."""
    for h in meets(rho, sig, s):
        for k in meets(rho, sig, t):
            if abs(h - k) < 3:
                continue
            found = False
            if h < k:
                a, b = k - 1, h + 1
            else:
                a, b = k + 1, h - 1
            for r in range(s + 1, t):
                if not (rho[r] <= a <= sig[r]):
                    continue
                for r2 in range(r + 1, t):
                    if rho[r2] <= b <= sig[r2]:
                        found = True
                        break
                if found:
                    break
            if not found:
                return False
    return True


def is_faithful(rho, sig):
    n = len(rho)
    for t in range(n):
        if not (rho[t] <= sig[t] <= rho[t] + 1):
            return False
    for t in range(n - 1):
        if max(sig[t], sig[t + 1]) > min(rho[t], rho[t + 1]) + 1:
            return False
    for s in range(n):
        for t in range(s + 1, n):
            if not crooked_ok(rho, sig, s, t):
                return False
    return True


# ------------------------------------------------- the arms and the statements

def phase_list(A):
    out = []
    seen = False
    for j in range(len(A)):
        if j >= 1 and A[j] <= A[j - 1]:
            seen = True
        out.append(1 if seen else 0)
    return out


def prefix_ok(A, p):
    """prefix_ok[j] = every j' <= j has A j' >= p - 1."""
    out = []
    ok = True
    for j in range(len(A)):
        if A[j] < p - 1:
            ok = False
        out.append(ok)
    return out


def hStarArm(A, p):
    pk = prefix_ok(A, p)
    return max(A[j] for j in range(len(A)) if pk[j])


def lStarArm(A, p):
    return -hStarArm([-a for a in A], -p)


def hReach(A, p):
    pk = prefix_ok(A, p)
    ph = phase_list(A)
    return max(A[j] + ph[j] for j in range(len(A)) if pk[j])


def drops_below(A, p):
    return any(a <= p - 2 for a in A)


def okLam(A, p, h):
    return (not drops_below(A, p)) or h <= hReach(A, p)


def okVee(A, p, l):
    return okLam([-a for a in A], -p, -l)


def hStar(rho, i, H, L):
    G = rho[i:]
    T = rho[: i + 1][::-1]
    p = rho[i]
    return min(max(max(hStarArm(G, p), hStarArm(T, p)), max(p, L + 1)), max(H - 1, p))


def lStar(rho, i, H, L):
    G = rho[i:]
    T = rho[: i + 1][::-1]
    p = rho[i]
    return max(min(min(lStarArm(G, p), lStarArm(T, p)), min(p, H - 1)), min(L + 1, p))


def valley_before(A, L, h, s):
    for u in range(s, len(A)):
        if A[u] > h + 1:
            if not any(A[j] <= L + 1 for j in range(s, u)):
                return False
    return True


def valley_all_s(A, L, h):
    """The universally quantified `s` clause of HighExitValleyF for one arm."""
    ph = phase_list(A)
    m = len(A)
    s = 0
    while True:
        # hypothesis: every j < s in the arm has A j + phase j < h
        if s > m:
            return True
        if not all(A[j] + ph[j] < h for j in range(min(s, m))):
            return True  # and for every larger s too
        if not valley_before(A, L, h, s):
            return False
        s += 1


def check_point(rho, i):
    """Returns the list of failing conjecture names at basepoint i (H, L attained extremes)."""
    H, L = max(rho), min(rho)
    if L + 3 > H:
        return []
    p = rho[i]
    G = rho[i:]
    T = rho[: i + 1][::-1]
    hs = hStar(rho, i, H, L)
    ls = lStar(rho, i, H, L)
    bad = []
    if not ((okLam(G, p, hs) and okLam(T, p, hs)) or (okVee(G, p, ls) and okVee(T, p, ls))):
        bad.append("ExitReachF")
    if not (valley_all_s(G, L, hs) and valley_all_s(T, L, hs)):
        bad.append("HighExitValleyF")
    nG = [-a for a in G]
    nT = [-a for a in T]
    if not (valley_all_s(nG, -H, -ls) and valley_all_s(nT, -H, -ls)):
        bad.append("LowExitPeakF")
    return bad


def check_seq(rho, sig, report):
    n = len(rho)
    for i in range(n):
        for name in check_point(rho, i):
            report.setdefault(name, []).append((list(rho), list(sig), i))


# ------------------------------------------------------------- enumeration

def enumerate_faithful(n, levels, cb):
    """DFS over rho (normalized to start at 0, values in range(levels)) and sig."""
    rho = [0] * n
    sig = [0] * n
    count = 0

    def partial_ok(m):
        """Everything decidable from the prefix of length m."""
        if m >= 2:
            t = m - 2
            if max(sig[t], sig[t + 1]) > min(rho[t], rho[t + 1]) + 1:
                return False
        # crookedness clauses for pairs (s, t) with t + 1 <= m - 1, i.e. t <= m - 2
        t = m - 2
        if t >= 1:
            for s in range(t):
                if not crooked_ok(rho[:m], sig[:m], s, t):
                    return False
        return True

    def rec(m):
        nonlocal count
        if m == n:
            # the remaining clauses: pairs with t = n - 1
            for s in range(n - 1):
                if not crooked_ok(rho, sig, s, n - 1):
                    return
            count += 1
            cb(rho, sig)
            return
        lo = 0 if m == 0 else max(0, rho[m - 1] - 1)
        hi = 0 if m == 0 else min(levels - 1, rho[m - 1] + 1)
        for v in range(lo, hi + 1):
            rho[m] = v
            for w in (v, v + 1):
                if w > levels - 1:
                    continue
                sig[m] = w
                if partial_ok(m + 1):
                    rec(m + 1)
        return

    rec(0)
    return count


# ----------------------------------------------------------------- random

def random_faithful(n, levels, rng, tries=400):
    """Rejection-sample a faithful pair by greedy extension with backtracking."""
    for _ in range(tries):
        rho = [rng.randrange(levels)]
        sig = [rho[0] if rng.random() < 0.5 or rho[0] + 1 >= levels else rho[0] + 1]
        ok = True
        for m in range(1, n):
            cands = []
            for v in range(max(0, rho[-1] - 1), min(levels - 1, rho[-1] + 1) + 1):
                for w in (v, v + 1):
                    if w > levels - 1:
                        continue
                    if max(sig[-1], w) > min(rho[-1], v) + 1:
                        continue
                    r2, s2 = rho + [v], sig + [w]
                    good = True
                    t = m - 1
                    if t >= 1:
                        for s in range(t):
                            if not crooked_ok(r2, s2, s, t):
                                good = False
                                break
                    if good:
                        cands.append((v, w))
            if not cands:
                ok = False
                break
            v, w = rng.choice(cands)
            rho.append(v)
            sig.append(w)
        if ok and is_faithful(rho, sig):
            return rho, sig
    return None


def main():
    mode = sys.argv[1]
    report = {}
    if mode == "exhaustive":
        n = int(sys.argv[2])
        levels = int(sys.argv[3])
        pts = [0]

        def cb(rho, sig):
            pts[0] += sum(1 for _ in range(len(rho)))
            check_seq(rho, sig, report)

        c = enumerate_faithful(n, levels, cb)
        print(f"length {n}, {levels} levels: {c} faithful pairs, {pts[0]} basepoints")
    elif mode == "random":
        n = int(sys.argv[2])
        levels = int(sys.argv[3])
        trials = int(sys.argv[4])
        seed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
        rng = random.Random(seed)
        got = 0
        for _ in range(trials):
            r = random_faithful(n, levels, rng)
            if r is None:
                continue
            got += 1
            check_seq(r[0], r[1], report)
        print(f"random length {n}, {levels} levels: {got} faithful pairs")
    else:
        print(__doc__)
        return
    if not report:
        print("  no failure of ExitReachF, HighExitValleyF, LowExitPeakF")
    for k, v in report.items():
        print(f"  {k}: {len(v)} failures, first {v[0]}")


if __name__ == "__main__":
    main()
