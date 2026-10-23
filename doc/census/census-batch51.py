#!/usr/bin/env python3
"""census-batch51.py — the landmark sentence of `w₄` against the fold, over arms alone.

Exhaustive over 1-Lipschitz arms `f` in the band `[0, 9]` based at `4`, of every length up to
`NMAX`, and random over longer ones.  For each arm the census compares

* the verdict of the dynamic program of `HPC/Fold/Decide.lean` on the walk
  `w₄ = 3 → 2 → 8 → 1` (levels 3,2,3,4,5,6,7,8,7,6,5,4,3,2,1 above the floor);
* the landmark sentence `CeilW4 ∧ BottomW4` of `HPC/Fold/LandmarkW.lean`, which is a theorem
  *necessary* for the fold, and the same sentence in the *minimal* form a sufficiency engine
  would consume (only the index bounds a greedy argument spends).

This is a census over arms alone: no crooked pair is generated here.
"""
import random
import sys

W4 = [3, 2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, 1]


def folds(f, walk=W4):
    reach = {0} if abs(f[0] - walk[0]) <= 1 else set()
    for v in f[1:]:
        nxt = set()
        for p in range(len(walk)):
            if abs(v - walk[p]) <= 1 and any(abs(p - q) <= 1 for q in reach):
                nxt.add(p)
        reach = nxt
        if not reach:
            return False
    return bool(reach)


def ceilW4(f):
    for d, v in enumerate(f):
        if v >= 8:
            if not any(f[j] <= 3 for j in range(1, max(0, d - 4))):
                return False
    return True


def bottomW4(f):
    for d, v in enumerate(f):
        if v <= 0:
            ok = False
            for j in range(1, len(f)):
                if f[j] > 3:
                    continue
                for k in range(j + 6, d - 6):
                    if f[k] >= 7:
                        ok = True
                        break
                if ok:
                    break
            if not ok:
                return False
    return True


def midW4(f):
    """Every ascent to `L + 5` is preceded by a time at `L + 3` or below, at a step at least `1`
    and at least two steps earlier — the walk's trough at its position `1`."""
    for d, v in enumerate(f):
        if v >= 5:
            if not any(f[j] <= 3 for j in range(1, max(0, d - 1))):
                return False
    return True


def midW4min(f):
    for d, v in enumerate(f):
        if v >= 5:
            if not any(f[j] <= 3 for j in range(1, d)):
                return False
    return True


def ceilW4min(f):
    """`CeilW4` with only `1 ≤ j` and `j < d` — the form a greedy engine consumes."""
    for d, v in enumerate(f):
        if v >= 8:
            if not any(f[j] <= 3 for j in range(1, d)):
                return False
    return True


def bottomW4min(f):
    """`BottomW4` with only `1 ≤ j`, `j + 6 ≤ k`, `k < d`."""
    for d, v in enumerate(f):
        if v <= 0:
            ok = False
            for j in range(1, len(f)):
                if f[j] > 3:
                    continue
                for k in range(j + 6, d):
                    if f[k] >= 7:
                        ok = True
                        break
                if ok:
                    break
            if not ok:
                return False
    return True


def report(tag, n, bad_nec, bad_suf, bad_sufmin):
    print(f"{tag}: {n} arms; necessity failures {bad_nec}; "
          f"sufficiency failures (commissioned form) {bad_suf}; "
          f"sufficiency failures (minimal form) {bad_sufmin}")


def check(f, counters, examples):
    fo = folds(f)
    nec = ceilW4(f) and bottomW4(f) and midW4(f)
    necmin = ceilW4min(f) and bottomW4min(f) and midW4min(f)
    if fo and not nec:
        counters[0] += 1
        examples.setdefault("necessity", f)
    if nec and not fo:
        counters[1] += 1
        examples.setdefault("sufficiency", f)
    if necmin and not fo:
        counters[2] += 1
        examples.setdefault("sufficiency-min", f)


def exhaustive(nmax):
    counters = [0, 0, 0]
    examples = {}
    total = 0
    for n in range(1, nmax + 1):
        stack = [[4]]
        while stack:
            f = stack.pop()
            if len(f) == n:
                total += 1
                check(f, counters, examples)
                continue
            for dv in (-1, 0, 1):
                v = f[-1] + dv
                if 0 <= v <= 9:
                    stack.append(f + [v])
    report(f"exhaustive, lengths 1..{nmax}", total, *counters)
    for k, v in examples.items():
        print("   ", k, v)


def randomised(count, nmin, nmax, seed=51):
    rng = random.Random(seed)
    counters = [0, 0, 0]
    examples = {}
    for _ in range(count):
        n = rng.randint(nmin, nmax)
        f = [4]
        while len(f) < n:
            v = f[-1] + rng.choice((-1, 0, 1))
            if 0 <= v <= 9:
                f.append(v)
            else:
                f.append(f[-1])
        check(f, counters, examples)
    report(f"random, lengths {nmin}..{nmax}", count, *counters)
    for k, v in examples.items():
        print("   ", k, v)


def buildWalk(start, targets):
    w, cur = [start], start
    for t in targets:
        if t is None:
            break
        if t == cur:
            return None
        s = 1 if t > cur else -1
        while cur != t:
            cur += s
            w.append(cur)
    return w


FIVE = {"lam": buildWalk(3, [8, 1, None]), "vee": buildWalk(5, [1, 8, None]),
        "w3": buildWalk(3, [6, 1, 8]), "w4": W4, "w5": buildWalk(3, [7, 1, 8])}


def relaxed(f):
    """The relaxed valley clause of batch 50: before every ascent to `L + 7` a time at `L + 3` or
    below, at a step at least four."""
    for e, v in enumerate(f):
        if v >= 7 and not any(f[j] <= 3 for j in range(4, e)):
            return False
    return True


def relaxed_search(nmax):
    """Question 3 of the commission: is the relaxed clause enough for a fold onto some walk?"""
    arms = []
    for n in range(1, nmax + 1):
        stack = [[4]]
        while stack:
            f = stack.pop()
            if len(f) == n:
                if relaxed(f):
                    arms.append(f)
                continue
            for dv in (-1, 0, 1):
                v = f[-1] + dv
                if 0 <= v <= 9:
                    stack.append(f + [v])
    print(f"arms satisfying the relaxed clause, lengths 1..{nmax}: {len(arms)}")
    served = []
    for st in (3, 4, 5):
        for a in range(10):
            if a == st:
                continue
            for b in list(range(10)) + [None]:
                if b == a:
                    continue
                cs = (list(range(10)) + [None]) if b is not None else [None]
                for c in cs:
                    if b is not None and c == b:
                        continue
                    w = buildWalk(st, [a, b, c])
                    if w is None:
                        continue
                    if all(folds(f, w) for f in arms):
                        served.append((len(w), st, a, b, c))
    print("walks of at most three turns serving every such arm:", served)
    none5 = [f for f in arms if not any(folds(f, w) for w in FIVE.values())]
    print(f"such arms folding onto none of the five walks of the development: {len(none5)}",
          none5[:3])


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    exhaustive(nmax)
    randomised(200000, 14, 40)
    relaxed_search(min(nmax, 11))
