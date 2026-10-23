#!/usr/bin/env python3
"""Adversarial search for short counterexamples to `OffDichotomy`.

Reuses the model of census-batch24.py and the one-pass criteria of census-batch25.py, plus a
fast faithfulness test (`fast_faithful`) for chains with `sigma = rho`, validated against the
definitional `is_faithful` of census-batch24.py on every chain short enough to check.

Modes:
  python3 search-batch25.py check N             # faithfulness of bing 0 N, fast test
  python3 search-batch25.py validate LEN LEVELS # fast test vs. the definitional one
  python3 search-batch25.py windows N SPAN      # maximal windows of bing 0 N of given span
  python3 search-batch25.py shrink N ITERS [SEED]   # try to shorten the bing 0 N counterexample
  python3 search-batch25.py anneal N ITERS [SEED]   # mutate faithful chains, minimising score
"""

import sys, random, importlib.util

spec = importlib.util.spec_from_file_location("c25", "census-batch25.py")
c25 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c25)

bing_path = c25.bing_path
is_faithful = c25.is_faithful
bot_fast = c25.bot_fast
top_fast = c25.top_fast
enumerate_faithful = c25.enumerate_faithful


def fast_faithful(rho):
    """`IsCrookedIvF rho rho`, in O(n^2) with next-occurrence tables.

    With `sigma = rho` every interval is a point, so the geometric clauses reduce to the
    1-Lipschitz condition and the meeting sets at `s` are the levels of `s − 1, s, s + 1`.
    The crookedness clause then asks, for levels `h` at `s` and `k` at `t` at distance at
    least three, for an index in `(s, t)` at the level adjacent to `k` on the side of `h`,
    followed by one at the level adjacent to `h` on the side of `k`."""
    n = len(rho)
    for t in range(n - 1):
        if abs(rho[t + 1] - rho[t]) > 1:
            return False
    lo, hi = min(rho), max(rho)
    nxt = {}
    for v in range(lo, hi + 1):
        arr = [n] * (n + 1)
        for i in range(n - 1, -1, -1):
            arr[i] = i if rho[i] == v else arr[i + 1]
        nxt[v] = arr
    def meets(s):
        return {rho[u] for u in range(max(0, s - 1), min(n, s + 2))}
    msets = [meets(s) for s in range(n)]
    for s in range(n):
        ms = msets[s]
        for t in range(s + 1, n):
            for h in ms:
                for k in msets[t]:
                    if abs(h - k) < 3:
                        continue
                    a, b = (k - 1, h + 1) if h < k else (k + 1, h - 1)
                    if not (lo <= a <= hi and lo <= b <= hi):
                        return False
                    r = nxt[a][s + 1]
                    if r >= t:
                        return False
                    if nxt[b][r + 1] >= t:
                        return False
    return True


def fails_at(rho, i):
    """The dichotomy fails at basepoint `i` of `rho`."""
    H, L = max(rho), min(rho)
    if L + 3 > H:
        return False
    p = rho[i]
    G = rho[i:]
    T = rho[: i + 1][::-1]
    for c0 in (p - 1, p, p + 1):
        if not (L + 1 <= c0 <= H - 1):
            continue
        if bot_fast(G, c0, L) and bot_fast(T, c0, L):
            return False
        if top_fast(G, c0, H) and top_fast(T, c0, H):
            return False
    return True


def worst_score(rho):
    H, L = max(rho), min(rho)
    if L + 3 > H:
        return None
    best = 99
    for i in range(len(rho)):
        p = rho[i]
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
        best = min(best, cnt)
        if best == 0:
            return 0
    return best


def any_failure(rho):
    return any(fails_at(rho, i) for i in range(len(rho)))


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return
    mode = sys.argv[1]
    if mode == "check":
        n = int(sys.argv[2])
        rho = bing_path(0, n)
        print(f"bing 0 {n}: {len(rho)} links, fast_faithful={fast_faithful(rho)}")
    elif mode == "validate":
        n = int(sys.argv[2])
        levels = int(sys.argv[3])
        bad = [0]
        tot = [0]

        def cb(rho, sig):
            tot[0] += 1
            if sig == rho and fast_faithful(rho) != is_faithful(rho, sig):
                bad[0] += 1

        enumerate_faithful(n, levels, cb)
        # and the negative side: perturbations of faithful chains
        rng = random.Random(0)
        for _ in range(2000):
            rho = bing_path(0, 5)
            j = rng.randrange(len(rho))
            rho = rho[:j] + rho[j + 1:]
            if fast_faithful(rho) != is_faithful(rho, list(rho)):
                bad[0] += 1
        print(f"length {n}, {levels} levels: {tot[0]} pairs tested, {bad[0]} disagreements")
    elif mode == "windows":
        n = int(sys.argv[2])
        span = int(sys.argv[3])
        full = bing_path(0, n)
        found = []
        for a in range(len(full)):
            b = a + 1
            while b < len(full) and max(full[a:b + 1]) - min(full[a:b + 1]) <= span:
                b += 1
            win = full[a:b]
            if max(win) - min(win) < 3 or len(win) < 9:
                continue
            for i in range(len(win)):
                if fails_at(win, i):
                    found.append((a, b, i, len(win)))
                    break
        print(f"bing 0 {n}, maximal windows of span <= {span}: {len(found)} with a failure")
        if found:
            best = min(found, key=lambda z: z[3])
            print(f"  shortest {best[3]} links, window [{best[0]},{best[1]}), basepoint {best[2]}")
            print(f"  {full[best[0]:best[1]]}")
    elif mode == "shrink":
        n = int(sys.argv[2])
        iters = int(sys.argv[3])
        seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
        rng = random.Random(seed)
        cur = bing_path(0, n)
        assert any_failure(cur)
        for _ in range(iters):
            j = rng.randrange(len(cur))
            ln = rng.choice((1, 1, 2, 4))
            cand = cur[:j] + cur[j + ln:]
            if len(cand) < 12:
                continue
            if not fast_faithful(cand):
                continue
            if any_failure(cand):
                cur = cand
                print(f"  shrunk to {len(cur)}")
        print(f"final length {len(cur)}")
        print(cur)
    elif mode == "anneal":
        n = int(sys.argv[2])
        iters = int(sys.argv[3])
        seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
        rng = random.Random(seed)
        cur = bing_path(0, n)
        cur_s = worst_score(cur)
        best, best_s = list(cur), cur_s
        for _ in range(iters):
            cand = list(cur)
            mv = rng.randrange(3)
            j = rng.randrange(len(cand))
            if mv == 0 and len(cand) > 12:
                del cand[j]
            elif mv == 1:
                cand.insert(j, cand[j])
            else:
                cand[j] += rng.choice((-1, 1))
            if not fast_faithful(cand):
                continue
            s = worst_score(cand)
            if s is None:
                continue
            if s <= cur_s:
                cur, cur_s = cand, s
            if (s, len(cand)) < (best_s, len(best)):
                best, best_s = list(cand), s
        print(f"anneal from bing 0 {n}: best score {best_s}, length {len(best)}")
        print(best)
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
