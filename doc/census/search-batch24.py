#!/usr/bin/env python3
"""Adversarial search for a counterexample to `F2PrimeOff`.

Reuses the model and the fold test of census-batch24.py. Two modes:

  python3 search-batch24.py pool N          # subchains of `bing 0 N`: the hardest basepoints
  python3 search-batch24.py climb N ITERS [SEED]
                                            # hill-climbing from subchains of `bing 0 N`,
                                            # minimising the number of itineraries that work

The score of a chain is the least, over its admissible basepoints, of the number of members of
the off-center family onto which both arms fold; score 0 is a counterexample.
"""

import sys, random, importlib.util

spec = importlib.util.spec_from_file_location("c24", "census-batch24.py")
c24 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c24)

bing_path = c24.bing_path
is_faithful = c24.is_faithful
folds_onto = c24.folds_onto
off_lam = c24.off_lam
off_vee = c24.off_vee


def options_at(rho, i):
    """How many members of the family both arms fold onto, at basepoint i."""
    H, L = max(rho), min(rho)
    if L + 3 > H:
        return None
    p = rho[i]
    G = rho[i:]
    T = rho[: i + 1][::-1]
    cnt = 0
    for c0 in (p - 1, p, p + 1):
        if not (L + 1 <= c0 <= H - 1):
            continue
        for h in range(c0, H):
            _, walk = off_lam(c0, h, L, H)
            if folds_onto(G, walk) and folds_onto(T, walk):
                cnt += 1
        for l in range(L + 1, c0 + 1):
            _, walk = off_vee(c0, l, L, H)
            if folds_onto(G, walk) and folds_onto(T, walk):
                cnt += 1
    return cnt


def score(rho):
    """Least number of working itineraries over admissible basepoints (None if vacuous)."""
    best = None
    arg = None
    for i in range(len(rho)):
        o = options_at(rho, i)
        if o is None:
            continue
        if best is None or o < best:
            best, arg = o, i
    return best, arg


def subchains(n, minlen=9, minspan=5):
    full = bing_path(0, n)
    out = []
    for a in range(len(full)):
        for b in range(a + minlen, len(full) + 1):
            rho = full[a:b]
            if max(rho) - min(rho) >= minspan:
                out.append(rho)
    return out


def mutate(rho, rng):
    """A 1-Lipschitz-preserving local change: shift one value, or delete/duplicate a link."""
    r = list(rho)
    k = rng.randrange(4)
    j = rng.randrange(len(r))
    if k == 0 and len(r) > 9:
        del r[j]
    elif k == 1:
        r.insert(j, r[j])
    elif k == 2:
        r[j] += 1
    else:
        r[j] -= 1
    for t in range(len(r) - 1):
        if abs(r[t + 1] - r[t]) > 1:
            return None
    return r


def main():
    mode = sys.argv[1]
    if mode == "pool":
        n = int(sys.argv[2])
        subs = subchains(n)
        best = None
        for rho in subs:
            s, i = score(rho)
            if s is None:
                continue
            if best is None or s < best[0]:
                best = (s, i, rho)
        print(f"bing 0 {n}: {len(subs)} subchains; hardest basepoint has {best[0]} working "
              f"itineraries")
        print(f"  at index {best[1]} of {best[2]}")
    elif mode == "climb":
        n = int(sys.argv[2])
        iters = int(sys.argv[3])
        seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
        rng = random.Random(seed)
        pool = subchains(n)
        rng.shuffle(pool)
        overall = None
        for start in pool[:40]:
            cur = list(start)
            cs, _ = score(cur)
            if cs is None:
                continue
            for _ in range(iters):
                cand = mutate(cur, rng)
                if cand is None or not is_faithful(cand, cand):
                    continue
                s, i = score(cand)
                if s is None:
                    continue
                if s <= cs:
                    cur, cs = cand, s
                if s == 0:
                    print("COUNTEREXAMPLE", cand, "basepoint", i)
                    return
            if overall is None or cs < overall[0]:
                overall = (cs, cur)
        print(f"climb: best score {overall[0]}")
        print(f"  {overall[1]}")
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
