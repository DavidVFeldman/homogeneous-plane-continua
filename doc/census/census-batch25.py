#!/usr/bin/env python3
"""Census and adversarial search for batch 25: `OffDichotomy`.

Reuses the faithful model, the two ladder walks, the fold test and `BottomOnTime` /
`TopOnTime` of census-batch24.py (which implement HPC/Fold/Faithful.lean and
HPC/Fold/OffCenter.lean verbatim).

Modes:
  python3 census-batch25.py bing N                     # every basepoint of bing 0 N
  python3 census-batch25.py bingsub N MINLEN MINSPAN   # contiguous subchains of bing 0 N
  python3 census-batch25.py ex LEN LEVELS              # exhaustive faithful corpus
  python3 census-batch25.py rand LEN LEVELS TRIALS [SEED]
  python3 census-batch25.py seq V1,V2,...              # one explicit sequence (sigma = rho)
  python3 census-batch25.py climb N ITERS [SEED]       # hill-climbing for a counterexample

A basepoint is scored by the number of the (at most six) pairs (c0, side) for which both arms
satisfy the corresponding on-time criterion; score 0 at an admissible basepoint is a
counterexample to `OffDichotomy`.
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
bottom_on_time = c24.bottom_on_time
top_on_time = c24.top_on_time
enumerate_faithful = c24.enumerate_faithful
random_faithful = c24.random_faithful


def score_at(rho, i):
    """Number of working (c0, side) options at basepoint i; None if the basepoint is not
    admissible (span < 3)."""
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
        if bottom_on_time(G, c0, L) and bottom_on_time(T, c0, L):
            cnt += 1
        if top_on_time(G, c0, H) and top_on_time(T, c0, H):
            cnt += 1
    return cnt


def soundness_at(rho, i, report):
    """Each criterion really must give a fold onto the corresponding self-ladder."""
    H, L = max(rho), min(rho)
    if L + 3 > H:
        return
    p = rho[i]
    G = rho[i:]
    T = rho[: i + 1][::-1]
    for c0 in (p - 1, p, p + 1):
        if not (L + 1 <= c0 <= H - 1):
            continue
        _, wl = off_lam(c0, c0, L, H)
        _, wv = off_vee(c0, c0, L, H)
        for f in (G, T):
            if bottom_on_time(f, c0, L) and not folds_onto(f, wl):
                report.setdefault("BottomOnTime unsound", []).append((list(rho), i, c0))
            if top_on_time(f, c0, H) and not folds_onto(f, wv):
                report.setdefault("TopOnTime unsound", []).append((list(rho), i, c0))


def check_seq(rho, report, counts, sound=True):
    for i in range(len(rho)):
        s = score_at(rho, i)
        if s is None:
            continue
        counts[0] += 1
        counts[1] = min(counts[1], s)
        if s == 0:
            report.setdefault("OffDichotomy", []).append((list(rho), i))
        if sound:
            soundness_at(rho, i, report)


def worst(rho):
    """Least score over admissible basepoints; None if none."""
    best = None
    for i in range(len(rho)):
        s = score_at(rho, i)
        if s is None:
            continue
        best = s if best is None else min(best, s)
    return best


def climb(n, iters, rng):
    """Hill-climbing over faithful sequences, minimising the worst basepoint score."""
    full = bing_path(0, n)
    pool = []
    for a in range(len(full)):
        for b in range(a + 9, len(full) + 1):
            sub = full[a:b]
            if max(sub) - min(sub) >= 4:
                pool.append(sub)
    cur = list(rng.choice(pool))
    cur_s = worst(cur)
    best, best_s = list(cur), cur_s
    for _ in range(iters):
        cand = list(cur)
        move = rng.randrange(3)
        if move == 0 and len(cand) > 9:
            del cand[rng.randrange(len(cand))]
        elif move == 1:
            j = rng.randrange(len(cand))
            cand.insert(j, cand[j])
        else:
            j = rng.randrange(len(cand))
            cand[j] += rng.choice((-1, 1))
        if not is_faithful(cand, list(cand)):
            continue
        s = worst(cand)
        if s is None:
            continue
        if s <= cur_s:
            cur, cur_s = cand, s
        if s < best_s:
            best, best_s = list(cand), s
            if s == 0:
                return best, 0
    return best, best_s


# ------------------------------------------- linear-time criteria, for the long chains

def bot_fast(f, c0, L):
    """`BottomOnTime f c0 L`, in one pass."""
    b = max(c0 - L - 2, 0) + 1
    thr = min(L + 2, c0)
    for j, v in enumerate(f):
        if v > c0 + 1:
            return False
        if j >= b and v <= thr:
            return True
    return True


def top_fast(f, c0, H):
    """`TopOnTime f c0 H`, in one pass."""
    b = max(H - c0 - 2, 0) + 1
    thr = max(H - 2, c0)
    for j, v in enumerate(f):
        if v < c0 - 1:
            return False
        if j >= b and v >= thr:
            return True
    return True


def deep_scan(rho, lo=None, hi=None, verbose=True):
    """Scores the dichotomy at every basepoint of a long chain, in linear time per basepoint.
    `lo`/`hi` restrict the basepoint level."""
    H, L = max(rho), min(rho)
    n = len(rho)
    worst_score = 99
    fails = []
    seen = 0
    for i in range(n):
        p = rho[i]
        if L + 3 > H:
            continue
        if lo is not None and p < lo:
            continue
        if hi is not None and p > hi:
            continue
        seen += 1
        G = rho[i:]
        T = rho[: i + 1][::-1]
        cnt = 0
        for c0 in (p - 1, p, p + 1):
            if not (L + 1 <= c0 <= H - 1):
                continue
            if bot_fast(G, c0, L) and bot_fast(T, c0, L):
                cnt += 1
            if top_fast(G, c0, H) and top_fast(T, c0, H):
                cnt += 1
        worst_score = min(worst_score, cnt)
        if cnt == 0:
            fails.append(i)
    if verbose:
        print(f"  {seen} basepoints scanned, least score {worst_score}, {len(fails)} failures")
        if fails:
            print(f"  first failing basepoint {fails[0]}, level {rho[fails[0]]}")
    return worst_score, fails


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return
    mode = sys.argv[1]
    report = {}
    counts = [0, 99]
    if mode == "bing":
        n = int(sys.argv[2])
        rho = bing_path(0, n)
        print(f"bing 0 {n}: {len(rho)} links, faithful={is_faithful(rho, list(rho))}")
        check_seq(rho, report, counts)
    elif mode == "bingsub":
        n = int(sys.argv[2])
        minlen = int(sys.argv[3])
        minspan = int(sys.argv[4])
        full = bing_path(0, n)
        subs = 0
        for a in range(len(full)):
            for b in range(a + minlen, len(full) + 1):
                rho = full[a:b]
                if max(rho) - min(rho) < minspan:
                    continue
                subs += 1
                check_seq(rho, report, counts, sound=False)
        print(f"bing 0 {n}: {subs} subchains of length >= {minlen}, span >= {minspan}")
    elif mode == "ex":
        n = int(sys.argv[2])
        levels = int(sys.argv[3])
        c = enumerate_faithful(n, levels, lambda rho, sig: check_seq(rho, report, counts))
        print(f"length {n}, {levels} levels: {c} faithful pairs")
    elif mode == "rand":
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
            check_seq(r[0], report, counts, sound=False)
        print(f"random length {n}, {levels} levels: {got} faithful sequences")
    elif mode == "seq":
        rho = [int(x) for x in sys.argv[2].split(",")]
        print(f"length {len(rho)}, faithful={is_faithful(rho, list(rho))}")
        check_seq(rho, report, counts)
        for i in range(len(rho)):
            print(f"  basepoint {i} (level {rho[i]}): score {score_at(rho, i)}")
    elif mode == "deep":
        n = int(sys.argv[2])
        rho = bing_path(0, n)
        print(f"bing 0 {n}: {len(rho)} links, span {max(rho) - min(rho)}")
        deep_scan(rho)
        return
    elif mode == "agree":
        # the one-pass criteria must agree with the definitions, everywhere
        n = int(sys.argv[2])
        levels = int(sys.argv[3])
        bad = [0]

        def cb(rho, sig):
            H, L = max(rho), min(rho)
            for i in range(len(rho)):
                for f in (rho[i:], rho[: i + 1][::-1]):
                    for c0 in range(L, H + 1):
                        if bot_fast(f, c0, L) != bottom_on_time(f, c0, L):
                            bad[0] += 1
                        if top_fast(f, c0, H) != top_on_time(f, c0, H):
                            bad[0] += 1

        c = enumerate_faithful(n, levels, cb)
        print(f"length {n}, {levels} levels: {c} faithful pairs, {bad[0]} disagreements")
        return
    elif mode == "climb":
        n = int(sys.argv[2])
        iters = int(sys.argv[3])
        seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
        rng = random.Random(seed)
        b, s = climb(n, iters, rng)
        print(f"climb from bing 0 {n}: best worst-score {s}")
        print(f"  {b}")
        return
    else:
        print(__doc__)
        return
    print(f"  {counts[0]} admissible basepoints, least score {counts[1]}")
    if not report:
        print("  no failure of OffDichotomy, and both criteria give folds throughout")
    for k, v in report.items():
        print(f"  {k}: {len(v)} failures, first {v[0]}")


if __name__ == "__main__":
    main()
