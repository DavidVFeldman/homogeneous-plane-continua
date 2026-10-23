#!/usr/bin/env python3
"""Census for batch 26: `S3`, the folding statement with the itinerary existentially
quantified, and a re-score of `F2PrimeOff` at span ten.

An *itinerary* here is a zigzag walk of unit steps: a base centre `c0` in `{p-1, p, p+1}`
followed by `k` turning targets in `[L+1, H-1]`, directions alternating.  `k` is the number of
turning targets; the one-bump family `offLam`/`offVee` of batch 24 is the case `k = 3`.
`FoldsOnto` is decided exactly, by forward propagation of the set of reachable times (here as
a bitmask, so that a 2 379-link chain costs one big-integer operation per link).

Scoring a basepoint means computing the least `k` for which some itinerary works, or reporting
that none works up to the search bound.  `S3` at a basepoint is implied by any success; a
failure of the search is evidence only, since only zigzags are searched.

Modes:
  python3 census-batch26.py f2off N                 # F2PrimeOff at every basepoint of bing 0 N
  python3 census-batch26.py kmax N KMAX             # least k at every basepoint of bing 0 N
  python3 census-batch26.py kmaxsub N MINLEN MINSPAN KMAX   # ... of subchains of bing 0 N
  python3 census-batch26.py subrand N MINLEN MINSPAN KMAX TRIALS [SEED]  # random subchains
  python3 census-batch26.py ex LEN LEVELS KMAX      # exhaustive faithful corpus
  python3 census-batch26.py rand LEN LEVELS TRIALS KMAX [SEED]
  python3 census-batch26.py at N I KMAX             # one basepoint of bing 0 N, verbose
  python3 census-batch26.py seq V1,V2,... KMAX      # one explicit sequence (sigma = rho)
"""

import sys, random, importlib.util

spec = importlib.util.spec_from_file_location("c24", "census-batch24.py")
c24 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c24)

bing_path = c24.bing_path
is_faithful = c24.is_faithful
folds_onto = c24.folds_onto
f2primeoff_at = c24.f2primeoff_at
witness_at = c24.witness_at
enumerate_faithful = c24.enumerate_faithful
random_faithful = c24.random_faithful


# ------------------------------------------------------------ fast fold test

def level_masks(walk, lo, hi):
    """masks[v - lo] has bit u set iff |v - walk[u]| <= 1."""
    masks = [0] * (hi - lo + 1)
    for u, w in enumerate(walk):
        for v in (w - 1, w, w + 1):
            if lo <= v <= hi:
                masks[v - lo] |= 1 << u
    return masks


def folds_fast(f, masks, lo, full):
    """FoldsOnto f (len walk) walk, by reachability with the set of times as a bitmask."""
    if not f:
        return True
    r = 1 & masks[f[0] - lo]
    if r == 0:
        return False
    for v in f[1:]:
        r = (r | (r << 1) | (r >> 1)) & masks[v - lo]
        if r == 0:
            return False
    return True


def walk_of(c0, turns):
    w = [c0]
    cur = c0
    for t in turns:
        step = 1 if t > cur else -1
        while cur != t:
            cur += step
            w.append(cur)
    return w


def alternating(L, H, k, last, up):
    """All alternating turning-target tuples of length k, in [L+1, H-1], first step in the
    direction `up` (None = free), starting from level `last`."""
    if k == 0:
        yield ()
        return
    dirs = (True, False) if up is None else (up,)
    for d in dirs:
        rng = range(last + 1, H) if d else range(L + 1, last)
        for t in rng:
            for rest in alternating(L, H, k - 1, t, not d):
                yield (t,) + rest


def min_k_at(rho, i, kmax, want_witness=False):
    """Least number of turning targets of a working itinerary at basepoint i, or None."""
    H, L = max(rho), min(rho)
    if L + 3 > H:
        return ("degenerate", None) if want_witness else -1
    p = rho[i]
    G = rho[i:]
    T = rho[: i + 1][::-1]
    for k in range(0, kmax + 1):
        for c0 in (p - 1, p, p + 1):
            if not (L <= c0 <= H):
                continue
            for turns in alternating(L, H, k, c0, None):
                walk = walk_of(c0, turns)
                masks = level_masks(walk, L, H)
                full = (1 << len(walk)) - 1
                if folds_fast(G, masks, L, full) and folds_fast(T, masks, L, full):
                    return (k, (c0,) + turns) if want_witness else k
    return (None, None) if want_witness else None


# ------------------------------------------------------------------- corpora

def score_seq(rho, kmax, report, stats, tag=""):
    H, L = max(rho), min(rho)
    span = H - L
    for i in range(len(rho)):
        k = min_k_at(rho, i, kmax)
        if k == -1:
            continue
        stats["basepoints"] = stats.get("basepoints", 0) + 1
        if k is None:
            report.setdefault("S3 search failed", []).append((tag, list(rho), i))
        else:
            cur = stats.setdefault("maxk", {})
            if k > cur.get(span, -1):
                cur[span] = k
                stats.setdefault("argmax", {})[span] = (tag, i, len(rho))


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return
    mode = sys.argv[1]
    report, stats = {}, {}

    if mode == "f2off":
        n = int(sys.argv[2])
        rho = bing_path(0, n)
        bad = [i for i in range(len(rho)) if not f2primeoff_at(rho, i)]
        print(f"bing 0 {n}: {len(rho)} links, span {max(rho) - min(rho)}")
        print(f"F2PrimeOff fails at {len(bad)} basepoints: {bad}")
        for i in bad:
            print(f"  basepoint {i}: level {rho[i]}, "
                  f"forward {len(rho) - i} links (max {max(rho[i:])}, min {min(rho[i:])}), "
                  f"backward {i + 1} links (max {max(rho[:i+1])}, min {min(rho[:i+1])})")
        return

    if mode == "at":
        n, i, kmax = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        rho = bing_path(0, n)
        k, w = min_k_at(rho, i, kmax, want_witness=True)
        print(f"bing 0 {n}, basepoint {i}, level {rho[i]}: least k = {k}, itinerary {w}")
        print(f"  F2PrimeOff here: {f2primeoff_at(rho, i)} ({witness_at(rho, i)})")
        return

    if mode == "kmax":
        n, kmax = int(sys.argv[2]), int(sys.argv[3])
        rho = bing_path(0, n)
        score_seq(rho, kmax, report, stats, tag=f"bing0{n}")
    elif mode == "kmaxsub":
        n, minlen, minspan, kmax = (int(sys.argv[2]), int(sys.argv[3]),
                                    int(sys.argv[4]), int(sys.argv[5]))
        base = bing_path(0, n)
        for a in range(len(base)):
            for b in range(a + minlen, len(base) + 1):
                sub = base[a:b]
                if max(sub) - min(sub) < minspan:
                    continue
                score_seq(sub, kmax, report, stats, tag=f"sub{a}:{b}")
    elif mode == "subrand":
        n, minlen, minspan, kmax, trials = (int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]),
                                            int(sys.argv[5]), int(sys.argv[6]))
        seed = int(sys.argv[7]) if len(sys.argv) > 7 else 0
        rng = random.Random(seed)
        base = bing_path(0, n)
        for _ in range(trials):
            a = rng.randrange(0, len(base) - minlen)
            b = rng.randrange(a + minlen, len(base) + 1)
            sub = base[a:b]
            if max(sub) - min(sub) < minspan:
                continue
            score_seq(sub, kmax, report, stats, tag=f"sub{a}:{b}")
    elif mode == "ex":
        ln, levels, kmax = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        total = enumerate_faithful(ln, levels,
                                   lambda r, s: score_seq(list(r), kmax, report, stats,
                                                          tag="ex"))
        print(f"faithful members of length {ln} on {levels} levels: {total}")
    elif mode == "rand":
        ln, levels, trials, kmax = (int(sys.argv[2]), int(sys.argv[3]),
                                    int(sys.argv[4]), int(sys.argv[5]))
        seed = int(sys.argv[6]) if len(sys.argv) > 6 else 0
        rng = random.Random(seed)
        for _ in range(trials):
            out = random_faithful(ln, levels, rng)
            if out is None:
                continue
            rho, sig = out
            score_seq(list(rho), kmax, report, stats, tag="rand")
    elif mode == "seq":
        rho = [int(v) for v in sys.argv[2].split(",")]
        kmax = int(sys.argv[3])
        score_seq(rho, kmax, report, stats, tag="seq")
    else:
        print(__doc__)
        return

    print(f"basepoints scored: {stats.get('basepoints', 0)}")
    for span in sorted(stats.get("maxk", {})):
        print(f"  span {span}: max k = {stats['maxk'][span]} "
              f"at {stats.get('argmax', {}).get(span)}")
    if report:
        for key, items in report.items():
            print(f"{key}: {len(items)}")
            for it in items[:5]:
                print(f"   {it}")
    else:
        print("no search failure")


if __name__ == "__main__":
    main()
