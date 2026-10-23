#!/usr/bin/env python3
"""Directed counterexample search for batch 23: hill-climbing over the faithful model.

Moves (insert / delete / re-level / re-width) are applied to a faithful pair and rejected
unless the result is again faithful; the objective is a soft margin measuring how close a
basepoint is to breaking `ExitReachF`, `HighExitValleyF` or `LowExitPeakF`.

  python3 anneal-batch23.py TARGET ROUNDS STEPS LEVELS [SEED] [START]
     TARGET in {exit, high, low}; START in {flat, crooked} (default crooked)
"""

import sys, random
from bisect import bisect_left, bisect_right

from importlib.machinery import SourceFileLoader

C = SourceFileLoader("census23", "/workspace/request-project/census-batch23.py").load_module()
S = SourceFileLoader("search23", "/workspace/request-project/search-batch23.py").load_module()

BIG = 10 ** 6


# ------------------------------------------------------------- fast model check

def faithful(rho, sig):
    n = len(rho)
    for t in range(n):
        if not (rho[t] <= sig[t] <= rho[t] + 1):
            return False
    for t in range(n - 1):
        if max(sig[t], sig[t + 1]) > min(rho[t], rho[t + 1]) + 1:
            return False
    occ = {}
    for t in range(n):
        for a in range(rho[t], sig[t] + 1):
            occ.setdefault(a, []).append(t)
    meet = []
    for s in range(n):
        out = set()
        for u in range(max(0, s - 1), min(n, s + 2)):
            out.update(range(rho[u], sig[u] + 1))
        meet.append(sorted(out))

    def first_after(a, s):
        lst = occ.get(a)
        if not lst:
            return None
        i = bisect_right(lst, s)
        return lst[i] if i < len(lst) else None

    def last_before(b, t):
        lst = occ.get(b)
        if not lst:
            return None
        i = bisect_left(lst, t)
        return lst[i - 1] if i > 0 else None

    for s in range(n):
        for t in range(s + 1, n):
            for h in meet[s]:
                for k in meet[t]:
                    if abs(h - k) < 3:
                        continue
                    a, b = (k - 1, h + 1) if h < k else (k + 1, h - 1)
                    r = first_after(a, s)
                    if r is None or r >= t:
                        return False
                    r2 = last_before(b, t)
                    if r2 is None or r2 <= r:
                        return False
    return True


# ------------------------------------------------------------------- objectives

def arm_data(A, p):
    ph = C.phase_list(A)
    pk = C.prefix_ok(A, p)
    hre = max(A[j] + ph[j] for j in range(len(A)) if pk[j])
    return hre, any(a <= p - 2 for a in A)


def valley_margin(A, L, h):
    """Soft margin for the failure of the `ValleyBefore` clause on one arm: `>= 1` iff it
    fails, and otherwise a measure of how far the arm is from failing."""
    ph = C.phase_list(A)
    m = len(A)
    best = -BIG
    s = 0
    while s <= m:
        if not all(A[j] + ph[j] < h for j in range(min(s, m))):
            break
        for u in range(s, m):
            lo = min(A[j] for j in range(s, u)) if u > s else BIG
            best = max(best, min(A[u] - h - 1, lo - L - 1))
        s += 1
    return best


def margins(rho, i):
    """(exit, high, low) soft margins at basepoint i; `>= 1` means the statement fails."""
    H, L = max(rho), min(rho)
    if L + 3 > H:
        return (-BIG, -BIG, -BIG)
    p = rho[i]
    G = rho[i:]
    T = rho[: i + 1][::-1]
    hs = C.hStar(rho, i, H, L)
    ls = C.lStar(rho, i, H, L)
    fl = -BIG
    for A in (G, T):
        hre, _ = arm_data(A, p)
        short = max(0, min(A) - (p - 2))      # how far the arm is from dropping at all
        fl = max(fl, min(hs - hre, 1 - short) if short else hs - hre)
    fv = -BIG
    for A in (G, T):
        B = [-a for a in A]
        hre, _ = arm_data(B, -p)
        short = max(0, min(B) - (-p - 2))
        fv = max(fv, min((-ls) - hre, 1 - short) if short else (-ls) - hre)
    exitm = min(fl, fv)
    highm = max(valley_margin(G, L, hs), valley_margin(T, L, hs))
    nG = [-a for a in G]
    nT = [-a for a in T]
    lowm = max(valley_margin(nG, -H, -ls), valley_margin(nT, -H, -ls))
    return (exitm, highm, lowm)


def score(rho, target):
    H, L = max(rho), min(rho)
    if L + 3 > H:
        return (H - L) - 100
    best = -BIG
    for i in range(len(rho)):
        e, h, l = margins(rho, i)
        v = {"exit": e, "high": h, "low": l}[target]
        best = max(best, v)
    return best


# ---------------------------------------------------------------------- search

def mutate(rho, sig, levels, rng):
    n = len(rho)
    r, s = list(rho), list(sig)
    kind = rng.random()
    if kind < 0.3 and n > 4:
        d = rng.randrange(n)
        del r[d]
        del s[d]
    elif kind < 0.65 and n < 90:
        d = rng.randrange(n)
        v = r[d]
        w = rng.choice([v, v + 1])
        if w >= levels:
            w = v
        r.insert(d, v)
        s.insert(d, w)
    elif kind < 0.85:
        d = rng.randrange(n)
        v = r[d] + rng.choice([-1, 1])
        if not (0 <= v < levels):
            return None
        r[d] = v
        s[d] = rng.choice([v, v + 1]) if v + 1 < levels else v
    else:
        d = rng.randrange(n)
        s[d] = r[d] if s[d] > r[d] else (r[d] + 1 if r[d] + 1 < levels else r[d])
    return r, s


def main():
    target = sys.argv[1]
    rounds = int(sys.argv[2])
    steps = int(sys.argv[3])
    levels = int(sys.argv[4])
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    start = sys.argv[6] if len(sys.argv) > 6 else "crooked"
    rng = random.Random(seed)
    best_overall = (-BIG, None)
    for rd in range(rounds):
        if start == "crooked":
            c = None
            while c is None:
                c = S.random_crooked_chain(rng, levels=levels, maxlen=110)
            rho, sig = c
        else:
            rho = [0, 1, 1, 2, 1, 2, 2, 3]
            sig = list(rho)
        cur = score(rho, target)
        for _ in range(steps):
            m = mutate(rho, sig, levels, rng)
            if m is None:
                continue
            r, s = m
            if not faithful(r, s):
                continue
            v = score(r, target)
            if v >= cur:
                rho, sig, cur = r, s, v
            if cur >= 1:
                break
        if cur > best_overall[0]:
            best_overall = (cur, (list(rho), list(sig)))
        if cur >= 1:
            print(f"FAILURE of {target} found in round {rd}")
            print("rho =", rho)
            print("sig =", sig)
            print("faithful:", faithful(rho, sig))
            print("checks:", [(i, C.check_point(rho, i)) for i in range(len(rho))
                              if C.check_point(rho, i)])
            return
    print(f"no failure of {target}; best margin {best_overall[0]}")
    if best_overall[1] is not None:
        print("best rho =", best_overall[1][0])
        print("best sig =", best_overall[1][1])


if __name__ == "__main__":
    main()
