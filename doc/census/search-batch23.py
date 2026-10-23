#!/usr/bin/env python3
"""Counterexample search for batch 23, over the faithful model `IsCrookedIvF`.

Random long faithful chains (the method that produced the batch-20 witnesses), scored against
the conclusions of `ExitReachF`, `HighExitValleyF`, `LowExitPeakF` with H, L the attained
extremes, plus a shrinker for any failure found.

  python3 search-batch23.py random  TRIALS LEN LEVELS [SEED]   -- random walks in the model
  python3 search-batch23.py crooked TRIALS MAXLEN LEVELS [SEED] -- chains from Bing's pattern
"""

import sys, random
from bisect import bisect_left, bisect_right

from importlib.machinery import SourceFileLoader

census = SourceFileLoader("census23", __file__.replace("search-", "census-")).load_module()
check_point = census.check_point
is_faithful = census.is_faithful


# ------------------------------------------------ fast incremental faithfulness

class Builder:
    """Incrementally built faithful pair. `rho[m]`, `sig[m]` appended with `try_push`."""

    def __init__(self):
        self.rho = []
        self.sig = []
        self.occ = {}           # level -> sorted list of indices whose interval contains it

    def _add_occ(self, m):
        for a in range(self.rho[m], self.sig[m] + 1):
            self.occ.setdefault(a, []).append(m)

    def _del_occ(self, m):
        for a in range(self.rho[m], self.sig[m] + 1):
            self.occ[a].pop()

    def meets(self, s):
        n = len(self.rho)
        out = set()
        for u in range(max(0, s - 1), min(n, s + 2)):
            out.update(range(self.rho[u], self.sig[u] + 1))
        return sorted(out)

    def first_after(self, a, s):
        """least index r with s < r and a in [rho r, sig r], or None."""
        lst = self.occ.get(a)
        if not lst:
            return None
        i = bisect_right(lst, s)
        return lst[i] if i < len(lst) else None

    def last_before(self, b, t):
        lst = self.occ.get(b)
        if not lst:
            return None
        i = bisect_left(lst, t)
        return lst[i - 1] if i > 0 else None

    def pair_ok(self, s, t):
        for h in self.meets(s):
            for k in self.meets(t):
                if abs(h - k) < 3:
                    continue
                a, b = (k - 1, h + 1) if h < k else (k + 1, h - 1)
                r = self.first_after(a, s)
                if r is None or r >= t:
                    return False
                r2 = self.last_before(b, t)
                if r2 is None or r2 <= r:
                    return False
        return True

    def try_push(self, v, w):
        """Append (v, w) and check everything that has become decidable; undo on failure."""
        m = len(self.rho)
        if not (v <= w <= v + 1):
            return False
        if m > 0 and max(self.sig[m - 1], w) > min(self.rho[m - 1], v) + 1:
            return False
        self.rho.append(v)
        self.sig.append(w)
        self._add_occ(m)
        t = m - 1
        if t >= 1:
            for s in range(t):
                if not self.pair_ok(s, t):
                    self.pop()
                    return False
        return True

    def pop(self):
        m = len(self.rho) - 1
        self._del_occ(m)
        self.rho.pop()
        self.sig.pop()

    def close(self):
        """The clauses with t the last index, which have no right neighbour to wait for."""
        t = len(self.rho) - 1
        for s in range(t):
            if not self.pair_ok(s, t):
                return False
        return True


def random_chain(n, levels, rng):
    b = Builder()
    guard = 0
    while len(b.rho) < n:
        guard += 1
        if guard > 40 * n:
            return None
        m = len(b.rho)
        if m == 0:
            cands = [(v, w) for v in range(levels) for w in (v, v + 1) if w < levels]
        else:
            prev = b.rho[-1]
            cands = [(v, w) for v in range(max(0, prev - 1), min(levels - 1, prev + 1) + 1)
                     for w in (v, v + 1) if w < levels]
        rng.shuffle(cands)
        placed = False
        for v, w in cands:
            if b.try_push(v, w):
                placed = True
                break
        if not placed:
            if len(b.rho) == 0:
                return None
            b.pop()          # backtrack one step
    if not b.close():
        return None
    return list(b.rho), list(b.sig)


# ------------------------------------------- chains built from Bing's crooked pattern

def crook(a, b):
    """Bing's crooked path from level `a` to level `b`: `a -> b-1 -> a+1 -> b`, recursively."""
    if abs(a - b) <= 1:
        return [a, b]
    d = 1 if b > a else -1
    return crook(a, b - d) + crook(b - d, a + d)[1:] + crook(a + d, b)[1:]


def sigma_dfs(rho, limit=400000):
    """Search for a `sigma` making `(rho, sigma)` faithful; `None` if there is none."""
    b = Builder()
    n = len(rho)
    cnt = [0]

    def rec(m):
        cnt[0] += 1
        if cnt[0] > limit:
            return None
        if m == n:
            return (list(b.rho), list(b.sig)) if b.close() else None
        for w in (rho[m], rho[m] + 1):
            if b.try_push(rho[m], w):
                r = rec(m + 1)
                if r is not None:
                    return r
                b.pop()
        return None

    return rec(0)


def random_crooked_chain(rng, levels=6, waypoints=3, plateau=0.08, maxlen=130):
    """A faithful chain with genuine range: concatenated crooked paths between random
    waypoints, with random plateaus, carried by a `sigma` found by search."""
    k = rng.randrange(1, waypoints + 1)
    pts = [rng.randrange(0, levels)]
    for _ in range(k):
        v = rng.randrange(0, levels)
        while v == pts[-1]:
            v = rng.randrange(0, levels)
        pts.append(v)
    seq = [pts[0]]
    for i in range(len(pts) - 1):
        seq += crook(pts[i], pts[i + 1])[1:]
    out = []
    for v in seq:
        out.append(v)
        if rng.random() < plateau:
            out.append(v)
    if len(out) > maxlen:
        return None
    return sigma_dfs(out)


def failures(rho, sig):
    out = []
    for i in range(len(rho)):
        for name in check_point(rho, i):
            out.append((name, i))
    return out


def shrink(rho, sig, name, verbose=True):
    """Greedy shrink keeping a failure of `name` and faithfulness."""
    def bad(r, s):
        if not is_faithful(r, s):
            return False
        return any(nm == name for nm, _ in failures(r, s))

    changed = True
    while changed:
        changed = False
        n = len(rho)
        for d in range(n):
            r2 = rho[:d] + rho[d + 1:]
            s2 = sig[:d] + sig[d + 1:]
            if len(r2) >= 2 and bad(r2, s2):
                rho, sig = r2, s2
                changed = True
                break
        if changed:
            continue
        for d in range(len(rho)):
            if sig[d] > rho[d]:
                s2 = list(sig)
                s2[d] = rho[d]
                if bad(rho, s2):
                    sig = s2
                    changed = True
                    break
    return rho, sig


def main():
    mode = sys.argv[1]
    if mode not in ("random", "crooked"):
        print(__doc__)
        return
    trials = int(sys.argv[2])
    n = int(sys.argv[3])
    levels = int(sys.argv[4])
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    rng = random.Random(seed)
    got = 0
    insts = 0
    found = {}
    for _ in range(trials):
        c = (random_chain(n, levels, rng) if mode == "random"
             else random_crooked_chain(rng, levels=levels, maxlen=n))
        if c is None:
            continue
        rho, sig = c
        got += 1
        H, L = max(rho), min(rho)
        if L + 3 <= H:
            insts += len(rho)
        for name, i in failures(rho, sig):
            found.setdefault(name, []).append((rho, sig, i))
    print(f"{got} faithful chains of length {n} on {levels} levels, {insts} instances")
    if not found:
        print("  no failure")
    for name, lst in found.items():
        rho, sig, i = lst[0]
        print(f"  {name}: {len(lst)} failures")
        r2, s2 = shrink(rho, sig, name)
        print(f"    shrunk rho = {r2}")
        print(f"    shrunk sig = {s2}")
        print(f"    faithful: {is_faithful(r2, s2)}  failures: {failures(r2, s2)}")


if __name__ == "__main__":
    main()
