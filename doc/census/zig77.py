#!/usr/bin/env python3
"""zig77.py -- exploration: do both arms fold onto a common *jump* zigzag?

A walk in `FoldsOnto` is an arbitrary `c : N -> Z`; nothing asks consecutive centers to differ by
one.  The walk used here, for turning levels p = T0, T1, ..., TK (directions alternating), is

    c = [p] ++ leg(T0,T1) ++ leg(T1,T2) ++ ...,   leg(a,b) = [a+2d, a+3d, ..., b]  (d = sign(b-a))

i.e. every leg skips the two levels next to its starting turn.  The fold is decided EXACTLY by forward
propagation of the set of reachable walk times.  The search over turning lists is a DP whose
pruning uses the greedy phase condition; every accepted walk is re-decided exactly.
"""
import sys, functools, random

sys.setrecursionlimit(100000)


@functools.lru_cache(maxsize=None)
def bing_path(a, b):
    if abs(b - a) <= 2:
        return tuple(range(a, b + 1)) if a <= b else tuple(range(a, b - 1, -1))
    if a < b:
        return bing_path(a, b - 1) + bing_path(b - 1, a + 1)[1:] + bing_path(a + 1, b)[1:]
    return bing_path(a, b + 1) + bing_path(b + 1, a - 1)[1:] + bing_path(a - 1, b)[1:]


def jump_walk(turns):
    c = [turns[0]]
    for a, b in zip(turns, turns[1:]):
        d = 1 if b > a else -1
        if abs(b - a) < 3:
            c.append(b)
        else:
            c.extend(range(a + 3 * d, b + d, d))
    return c


def folds(f, c):
    if abs(f[0] - c[0]) > 1:
        return False
    R = {0}
    n = len(c)
    for x in f[1:]:
        R2 = set()
        for u in R:
            for v in (u - 1, u, u + 1):
                if 0 <= v < n and abs(x - c[v]) <= 1:
                    R2.add(v)
        if not R2:
            return False
        R = R2
    return True


def phase_step(f, tau, prev, target):
    """Greedy phase from time tau: leg from turn `prev` to `target`.
    Returns new tau (transfer time), or 'done' if the arm ends inside the envelope, or None."""
    up = target > prev
    lo, hi = (prev - 1, target + 1) if up else (target - 1, prev + 1)
    if all(lo <= x <= hi for x in f[tau:]):
        return 'done'
    for j in range(tau, len(f)):
        x = f[j]
        if up:
            if x < prev - 1:
                return None
            if x >= target - 1:
                return j
        else:
            if x > prev + 1:
                return None
            if x <= target + 1:
                return j
    return 'done'


def search(G, T, L, H, maxturns=14):
    p = G[0]
    from collections import deque
    q = deque([((p,), 0, 0)])
    seen = set()
    while q:
        turns, tG, tT = q.popleft()
        if tG == 'done' and tT == 'done':
            return list(turns)
        if len(turns) > maxturns:
            continue
        last = turns[-1]
        hi = max(turns); lo = min(turns)
        key = (last, hi, lo, tG, tT)
        if key in seen:
            continue
        seen.add(key)
        if len(turns) == 1:
            cands = [t for t in range(L - 1, H + 2) if abs(t - last) >= 2]
        elif last == hi:   # go down, strictly below every earlier level
            cands = list(range(L - 1, lo))
        else:
            cands = list(range(hi + 1, H + 2))
        for t in cands:
            nG = tG if tG == 'done' else phase_step(G, tG, last, t)
            if nG is None:
                continue
            nT = tT if tT == 'done' else phase_step(T, tT, last, t)
            if nT is None:
                continue
            q.append((turns + (t,), nG, nT))
    return None


def arms(rho, i):
    return rho[i:], rho[i::-1]


def run_bing(S):
    rho = list(bing_path(0, S))
    n = len(rho)
    bad = 0
    maxt = 0
    for i in range(n):
        G, T = arms(rho, i)
        w = search(G, T, 0, S)
        if w is None:
            bad += 1
            if bad <= 5:
                print("  unserved by DP: span", S, "i", i, "level", rho[i])
            continue
        c = jump_walk(w)
        if not (folds(G, c) and folds(T, c)):
            bad += 1
            print("  DP walk fails exact check", S, i, w)
        maxt = max(maxt, len(w) - 1)
    print("span", S, "n", n, "unserved", bad, "max turns", maxt)


if __name__ == "__main__":
    for S in range(3, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 10):
        run_bing(S)


def phase_max(f, tau, prev, up):
    """For a phase starting at tau from turn `prev` in direction up/down: the extreme level the arm
    reaches (max if up, min if down) before it first leaves the envelope on the far side
    (below prev-1 if up, above prev+1 if down).  None if it never leaves (the arm is done)."""
    ext = f[tau]
    for j in range(tau, len(f)):
        x = f[j]
        if up and x < prev - 1:
            return ext
        if (not up) and x > prev + 1:
            return ext
        ext = max(ext, x) if up else min(ext, x)
    return None


def greedy(G, T, L, H, first_up):
    p = G[0]
    turns = [p]
    tG, tT = 0, 0
    up = first_up
    while not (tG == 'done' and tT == 'done'):
        last = turns[-1]
        exts = []
        for f, t in ((G, tG), (T, tT)):
            if t != 'done':
                e = phase_max(f, t, last, up)
                if e is not None:
                    exts.append(e)
        if up:
            tgt = min(exts) + 1 if exts else H + 1
            tgt = min(tgt, H + 1)
            prevtop = max(turns)
            if tgt < last + (2 if len(turns) == 1 else 3) or (len(turns) > 1 and tgt <= prevtop):
                return None, turns + [tgt]
        else:
            tgt = max(exts) - 1 if exts else L - 1
            tgt = max(tgt, L - 1)
            prevbot = min(turns)
            if tgt > last - (2 if len(turns) == 1 else 3) or (len(turns) > 1 and tgt >= prevbot):
                return None, turns + [tgt]
        tG = tG if tG == 'done' else phase_step(G, tG, last, tgt)
        tT = tT if tT == 'done' else phase_step(T, tT, last, tgt)
        assert tG is not None and tT is not None
        turns.append(tgt)
        up = not up
    return turns, None


def run_greedy(rho, label):
    n = len(rho)
    L, H = min(rho), max(rho)
    bad = []
    for i in range(n):
        G, T = arms(rho, i)
        ok = False
        for fu in (True, False):
            w, fail = greedy(G, T, L, H, fu)
            if w is not None:
                c = jump_walk(w)
                assert folds(G, c) and folds(T, c), (i, w)
                ok = True
                break
        if not ok:
            bad.append(i)
    print(label, "n", n, "greedy fails at", len(bad), bad[:10])
    return bad
