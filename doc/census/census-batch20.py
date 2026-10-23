#!/usr/bin/env python3
"""Census for batch 20 — the interval model.

Exploratory computation, not a Lean-checked claim by itself.  The statement
checkers are imported from `census-batch19.py`, so the four `…Iv` statements are
scored by exactly the code that scored their sequence-model namesakes; what
changes here is the *domain*: sequences `rho` that carry an interval structure
`sigma` making the pair crooked in the sense of `IsCrookedIv`, rather than
sequences satisfying the necessary-only down form `IsCrookedSeq`.

    python3 census-batch20.py iv [maxlen] [levels]
        exhaustive depth-first over crooked interval chains (rho, sigma), pruning
        on the interval crookedness condition; every basepoint scored.

    python3 census-batch20.py random [samples] [len] [levels] [seed]
        randomised dives to a target length, many levels.

    python3 census-batch20.py tree SEQ
        for a named witness (`badSeq`, `fpSeq`), the first interval-crookedness
        instance that fails, for every one of the 2^n patterns of `sigma`.

    python3 census-batch20.py greedy SEQ
        a smallest set of instances `(s, t, h, k)` killing every pattern — the
        decision tree used by the two non-realizability proofs in Lean.

    python3 census-batch20.py witness
        the two sequence-model witnesses: crooked in the down form, 1-Lipschitz,
        and carried by no interval structure.
"""

import importlib.util
import os
import random
import sys
from itertools import product

_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("census19",
                                               os.path.join(_here, "census-batch19.py"))
b19 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(b19)

badSeq = [1, 2, 3, 2, 3, 4, 3, 4, 5]
fpSeq = [5, 4, 3, 3, 2, 3, 2, 1, 2, 3, 2, 1, 1, 0]
SEQS = {"badSeq": badSeq, "fpSeq": fpSeq}

NAMES = ("ExitReachIv", "HighExitValleyIv", "LowExitPeakIv", "F2PrimeIv")


# --- the interval model -----------------------------------------------------

def iv_witness(rho, sigma, s, t, h, k):
    """Is there `s < r < r' < t` witnessing interval crookedness for `(s,t,h,k)`?"""
    for r in range(s + 1, t):
        for rp in range(r + 1, t):
            if h < k:
                if rho[r] <= k - 1 <= sigma[r] and rho[rp] <= h + 1 <= sigma[rp]:
                    return True
            else:
                if rho[r] <= k + 1 <= sigma[r] and rho[rp] <= h - 1 <= sigma[rp]:
                    return True
    return False


def iv_crooked_last(rho, sigma):
    """The interval crookedness clause for every pair whose second index is the last."""
    t = len(rho) - 1
    for s in range(t):
        for h in range(rho[s], sigma[s] + 1):
            for k in range(rho[t], sigma[t] + 1):
                if abs(h - k) >= 3 and not iv_witness(rho, sigma, s, t, h, k):
                    return False
    return True


def iv_crooked(rho, sigma):
    return all(iv_crooked_last(rho[:t + 1], sigma[:t + 1]) for t in range(1, len(rho)))


def adj_ok(rho, sigma):
    return all(rho[t + 1] <= sigma[t] + 1 and rho[t] <= sigma[t + 1] + 1
               for t in range(len(rho) - 1))


# --- the four statements ----------------------------------------------------

def check_iv(rho, i, H, L):
    """The `…Iv` statements that FAIL at this instance.

    The bodies of the four statements are those of the batch-19 tight forms, so the
    batch-19 checker scores them; only the names change.
    """
    rename = {"ExitReachTight": "ExitReachIv", "HighExitValleyTight": "HighExitValleyIv",
              "LowExitPeakTight": "LowExitPeakIv", "F2PrimeTight": "F2PrimeIv"}
    return [rename[b] for b in b19.check(rho, i, H, L) if b in rename]


def report(bad):
    for name in NAMES:
        if name in bad:
            rho, sigma, i, H, L = bad[name]
            print(f"  {name}: FAILS at rho={rho}, sigma={sigma}, i={i}, H={H}, L={L}")
        else:
            print(f"  {name}: no failure")


# --- exhaustive census over interval chains ---------------------------------

def iv_census(maxlen, levels):
    state = {"pairs": 0, "rhos": set(), "basepoints": 0, "instances": 0, "bad": {}}

    def visit(rho, sigma):
        state["pairs"] += 1
        state["rhos"].add(tuple(rho))
        state["basepoints"] += len(rho)
        H, L = max(rho), min(rho)
        if L + 3 > H:
            return
        for i in range(len(rho)):
            state["instances"] += 1
            for name in check_iv(rho, i, H, L):
                state["bad"].setdefault(name, (list(rho), list(sigma), i, H, L))

    def dfs(rho, sigma):
        visit(rho, sigma)
        if len(rho) == maxlen:
            return
        for d in (-1, 0, 1):
            v = rho[-1] + d
            if not 0 <= v < levels:
                continue
            for e in (0, 1):
                rho.append(v)
                sigma.append(v + e)
                if iv_crooked_last(rho, sigma):
                    dfs(rho, sigma)
                rho.pop()
                sigma.pop()

    for start in range(levels):
        for e in (0, 1):
            dfs([start], [start + e])
    print(f"interval census: {levels} levels, length <= {maxlen}, 1-Lipschitz rho")
    print(f"  crooked interval chains (rho, sigma): {state['pairs']},"
          f" distinct rho: {len(state['rhos'])}")
    print(f"  basepoints: {state['basepoints']},"
          f" instances with L + 3 <= H: {state['instances']}")
    report(state["bad"])
    return state


# --- randomised dives -------------------------------------------------------

def random_dive(target, levels, rng):
    rho = [rng.randrange(levels)]
    sigma = [rho[0] + rng.randrange(2)]
    stack = [[(d, e) for d in (-1, 0, 1) for e in (0, 1)]]
    rng.shuffle(stack[0])
    while len(rho) < target:
        if not stack[-1]:
            if len(rho) == 1:
                return None
            rho.pop()
            sigma.pop()
            stack.pop()
            continue
        d, e = stack[-1].pop()
        v = rho[-1] + d
        if not 0 <= v < levels:
            continue
        rho.append(v)
        sigma.append(v + e)
        if not iv_crooked_last(rho, sigma):
            rho.pop()
            sigma.pop()
            continue
        nxt = [(d2, e2) for d2 in (-1, 0, 1) for e2 in (0, 1)]
        rng.shuffle(nxt)
        stack.append(nxt)
    return rho, sigma


def random_census(samples, target, levels, seed):
    rng = random.Random(seed)
    bad = {}
    chains = inst = 0
    for _ in range(samples):
        got = random_dive(target, levels, rng)
        if got is None:
            continue
        rho, sigma = got
        chains += 1
        H, L = max(rho), min(rho)
        if L + 3 > H:
            continue
        for i in range(len(rho)):
            inst += 1
            for name in check_iv(rho, i, H, L):
                bad.setdefault(name, (list(rho), list(sigma), i, H, L))
    print(f"random interval census: {chains} crooked interval chains of length {target}"
          f" on {levels} levels, seed {seed}; {inst} instances")
    report(bad)


# --- non-realizability of the two sequence-model witnesses ------------------

def first_failure(rho, sigma):
    n = len(rho)
    for s in range(n):
        for t in range(s + 1, n):
            for h in range(rho[s], sigma[s] + 1):
                for k in range(rho[t], sigma[t] + 1):
                    if abs(h - k) >= 3 and not iv_witness(rho, sigma, s, t, h, k):
                        return (s, t, h, k)
    return None


def tree(rho):
    n = len(rho)
    stats = {}
    good = []
    for bits in product([0, 1], repeat=n):
        sigma = [rho[i] + bits[i] for i in range(n)]
        if not adj_ok(rho, sigma):
            stats[("adj",)] = stats.get(("adj",), 0) + 1
            continue
        f = first_failure(rho, sigma)
        if f is None:
            good.append(bits)
        else:
            stats[f] = stats.get(f, 0) + 1
    print(f"patterns: {2 ** n}")
    for key, v in sorted(stats.items(), key=lambda kv: -kv[1]):
        print("  first failing instance (s,t,h,k)", key, ":", v, "patterns")
    print("patterns carrying the sequence as a crooked interval chain:", len(good))
    for g in good:
        print("   ", g)
    return good


def all_instances(rho):
    n = len(rho)
    return [(s, t, h, k)
            for s in range(n) for t in range(s + 1, n)
            for h in range(rho[s], rho[s] + 2) for k in range(rho[t], rho[t] + 2)
            if abs(h - k) >= 3]


def pair_cover(rho, pairs):
    """The patterns killed by none of the given instances."""
    n = len(rho)
    uncovered = []
    for bits in product([0, 1], repeat=n):
        sigma = [rho[i] + bits[i] for i in range(n)]
        if not adj_ok(rho, sigma):
            continue
        if not any(rho[s] <= h <= sigma[s] and rho[t] <= k <= sigma[t]
                   and not iv_witness(rho, sigma, s, t, h, k)
                   for (s, t, h, k) in pairs):
            uncovered.append(bits)
    return uncovered


def greedy(rho):
    n = len(rho)
    pats = [[rho[i] + b[i] for i in range(n)] for b in product([0, 1], repeat=n)]
    pats = [s for s in pats if adj_ok(rho, s)]
    cands = all_instances(rho)
    kill = {c: {idx for idx, sigma in enumerate(pats)
                if rho[c[0]] <= c[2] <= sigma[c[0]] and rho[c[1]] <= c[3] <= sigma[c[1]]
                and not iv_witness(rho, sigma, c[0], c[1], c[2], c[3])}
            for c in cands}
    chosen, remaining = [], set(range(len(pats)))
    while remaining:
        best = max(cands, key=lambda c: len(kill[c] & remaining))
        if not (kill[best] & remaining):
            print("  STUCK; uncovered patterns:", [pats[i] for i in list(remaining)[:5]])
            break
        chosen.append((best, len(kill[best] & remaining)))
        remaining -= kill[best]
    print(f"patterns consistent with the width and adjacency clauses: {len(pats)}")
    for c, cnt in chosen:
        print(f"  instance (s,t,h,k) = {c} kills {cnt}")
    return chosen


def witness_report():
    for name, rho in SEQS.items():
        lip = all(abs(rho[k + 1] - rho[k]) <= 1 for k in range(len(rho) - 1))
        down = all(b19.crooked_last(rho[:t + 1]) for t in range(len(rho)))
        realizable = [b for b in product([0, 1], repeat=len(rho))
                      if iv_crooked(rho, [rho[i] + b[i] for i in range(len(rho))])]
        print(f"{name} = {rho}")
        print(f"  1-Lipschitz={lip}, IsCrookedSeq={down},"
              f" interval structures making it crooked: {len(realizable)}"
              f" of {2 ** len(rho)}")
        print("  decision tree:")
        greedy(rho)


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "iv"
    a = sys.argv[2:]
    if mode == "iv":
        iv_census(int(a[0]) if a else 8, int(a[1]) if len(a) > 1 else 6)
    elif mode == "random":
        random_census(int(a[0]) if a else 200, int(a[1]) if len(a) > 1 else 30,
                      int(a[2]) if len(a) > 2 else 9, int(a[3]) if len(a) > 3 else 0)
    elif mode == "tree":
        tree(SEQS[a[0] if a else "badSeq"])
    elif mode == "greedy":
        greedy(SEQS[a[0] if a else "badSeq"])
    elif mode == "witness":
        witness_report()
    else:
        print(__doc__)


if __name__ == "__main__":
    main()


# --- shrinking a failing interval chain -------------------------------------

def shrink(rho, sigma, i, target):
    """Cut ends off a failing interval chain while the named statement still fails.

    Truncation preserves `IsCrookedIv` (the witnesses of a pair lie strictly between
    its endpoints), but it moves `H` and `L`, so the failure is rechecked each time.
    """
    rho, sigma = list(rho), list(sigma)
    changed = True
    while changed:
        changed = False
        for cut_front in (True, False):
            if len(rho) <= 2:
                break
            if cut_front:
                if i == 0:
                    continue
                r2, s2, i2 = rho[1:], sigma[1:], i - 1
            else:
                if i == len(rho) - 1:
                    continue
                r2, s2, i2 = rho[:-1], sigma[:-1], i
            H, L = max(r2), min(r2)
            if L + 3 > H:
                continue
            if target in check_iv(r2, i2, H, L) and iv_crooked(r2, s2):
                rho, sigma, i = r2, s2, i2
                changed = True
    return rho, sigma, i


def verify(rho, sigma, i):
    H, L = max(rho), min(rho)
    print(f"  rho   = {rho}")
    print(f"  sigma = {sigma}")
    print(f"  i = {i}, H = {H}, L = {L}, p = {rho[i]}")
    print(f"  1-Lipschitz: {all(abs(rho[k+1]-rho[k]) <= 1 for k in range(len(rho)-1))}")
    print(f"  width/le: {all(rho[t] <= sigma[t] <= rho[t]+1 for t in range(len(rho)))}")
    print(f"  adj: {adj_ok(rho, sigma)}")
    print(f"  IsCrookedIv: {iv_crooked(rho, sigma)}")
    print(f"  IsCrookedSeq (down form): "
          f"{all(b19.crooked_last(rho[:t+1]) for t in range(len(rho)))}")
    print(f"  fails: {check_iv(rho, i, H, L)}")


def shrink_hard(rho, sigma, i, target, passes=6):
    """Aggressive shrinking: end cuts, interior deletions, and `sigma` simplification."""
    rho, sigma, i = shrink(rho, sigma, i, target)

    def fails(r2, s2, i2):
        if len(r2) < 3 or not 0 <= i2 < len(r2):
            return False
        if any(abs(r2[k + 1] - r2[k]) > 1 for k in range(len(r2) - 1)):
            return False
        H, L = max(r2), min(r2)
        if L + 3 > H:
            return False
        return target in check_iv(r2, i2, H, L) and iv_crooked(r2, s2)

    for _ in range(passes):
        progress = False
        u = 0
        while u < len(rho):
            r2 = rho[:u] + rho[u + 1:]
            s2 = sigma[:u] + sigma[u + 1:]
            i2 = i - 1 if u < i else i
            if u != i and fails(r2, s2, i2):
                rho, sigma, i = r2, s2, i2
                progress = True
            else:
                u += 1
        for u in range(len(rho)):
            if sigma[u] != rho[u]:
                s2 = list(sigma)
                s2[u] = rho[u]
                if fails(rho, s2, i):
                    sigma = s2
                    progress = True
        rho, sigma, i = shrink(rho, sigma, i, target)
        if not progress:
            break
    return rho, sigma, i
