#!/usr/bin/env python3
"""Census for batch 27.

Part 1 — the obstruction.  `cutSeq` = `bingPath 0 8` restricted to [355, 391]:
checks the numeral, the Lipschitz condition, the bounds, the attainment, the
faithful model (`IsCrookedIvF` with rho = sigma), and the obstruction (no pair of
cut points gives three pieces of span <= 3, and every pair has a piece of full
span).  All of these are proved in Lean in HPC/Fold/Cut.lean; this is the
out-of-Lean check on the same data.

Part 2 — `LexCutExists`.  Over contiguous subchains of `bing 0 8` and `bing 0 10`
of span at least four, look for a `LexCut`: outer pieces of strictly smaller span,
every piece spanning at least two levels.  Also in the crookedness-witness form
(rho r >= H-2 and rho r' <= L+2), and with the threshold raised to three.

Part 3 — `Tracking` at a three-point window.  `s3_of_tracking` instantiates
`Tracking` at a window [a, a+2] with a one-time walk whose value is v; the
conclusion asked of `Tracking` there is that the suffix from a+2 and the reversed
prefix up to a both fold from time 0 of a walk whose value at time 0 is v.  This
part checks, by bitmask reachability over walks built from zigzag itineraries
through v, that such a pair of folds exists for every window of the corpora --
i.e. looks for a counterexample to that instance of `Tracking`.
"""

import random
import sys
from collections import Counter

sys.setrecursionlimit(100000)


# ---------------------------------------------------------------- Bing chains

def bing_path(a, b):
    if abs(b - a) <= 2:
        if a <= b:
            return [a + u for u in range(b - a + 1)]
        return [a - u for u in range(a - b + 1)]
    if a < b:
        return bing_path(a, b - 1) + bing_path(b - 1, a + 1)[1:] + bing_path(a + 1, b)[1:]
    return bing_path(a, b + 1) + bing_path(b + 1, a - 1)[1:] + bing_path(a - 1, b)[1:]


P8 = bing_path(0, 8)
P10 = bing_path(0, 10)
CUT = P8[355:392]


# ------------------------------------------------- part 1: the obstruction

def faithful(rho):
    """IsCrookedIvF rho rho, checked directly."""
    n = len(rho)
    for t in range(n - 1):
        if abs(rho[t + 1] - rho[t]) > 1:
            return (False, ("adj", t))
    for s in range(n):
        hs = {rho[u] for u in (s - 1, s, s + 1) if 0 <= u < n}
        for t in range(s + 1, n):
            ks = {rho[u] for u in (t - 1, t, t + 1) if 0 <= u < n}
            for h in hs:
                for k in ks:
                    if abs(h - k) < 3:
                        continue
                    want1, want2 = (k - 1, h + 1) if h < k else (k + 1, h - 1)
                    ok = False
                    for r in range(s + 1, t):
                        if rho[r] == want1:
                            for r2 in range(r + 1, t):
                                if rho[r2] == want2:
                                    ok = True
                                    break
                        if ok:
                            break
                    if not ok:
                        return (False, (s, t, h, k))
    return (True, None)


def span_on(rho, a, b):
    seg = rho[a:b + 1]
    return max(seg) - min(seg)


def part1():
    print("len bing 0 8 =", len(P8), " len bing 0 10 =", len(P10))
    print("cutSeq =", CUT)
    print("length", len(CUT), "min", min(CUT), "max", max(CUT))
    print("argmin", [i for i, v in enumerate(CUT) if v == min(CUT)],
          "argmax", [i for i, v in enumerate(CUT) if v == max(CUT)])
    print("lipschitz:", all(abs(CUT[i + 1] - CUT[i]) <= 1 for i in range(len(CUT) - 1)))
    print("faithful:", faithful(CUT))
    n = len(CUT)
    sols = [(r, r2) for r in range(1, n - 1) for r2 in range(r + 1, n - 1)
            if span_on(CUT, 0, r) <= 3 and span_on(CUT, r, r2) <= 3
            and span_on(CUT, r2, n - 1) <= 3]
    npairs = sum(1 for r in range(1, n - 1) for _ in range(r + 1, n - 1))
    print("pairs (r,r') with 0<r<r'<36:", npairs)
    print("three-cut solutions for cutSeq:", sols)
    cert = {}
    for r in range(1, n - 1):
        for r2 in range(r + 1, n - 1):
            for (a, b, name) in ((0, r, "first"), (r, r2, "middle"), (r2, n - 1, "last")):
                seg = CUT[a:b + 1]
                if min(seg) == 3 and max(seg) == 7:
                    cert[(r, r2)] = name
                    break
            else:
                cert[(r, r2)] = None
    print("pairs with no full-span piece:", [k for k, v in cert.items() if v is None])
    print("which piece carries both extremes:", Counter(cert.values()))


# ------------------------------------------------- part 2: LexCutExists

class RangeSpan:
    """O(1) range min/max by sparse tables."""

    def __init__(self, xs):
        self.n = len(xs)
        k = max(1, self.n.bit_length())
        self.mx = [list(xs)]
        self.mn = [list(xs)]
        j = 1
        while (1 << j) <= self.n:
            prevx, prevn = self.mx[-1], self.mn[-1]
            half = 1 << (j - 1)
            cur_x = [max(prevx[i], prevx[i + half]) for i in range(self.n - (1 << j) + 1)]
            cur_n = [min(prevn[i], prevn[i + half]) for i in range(self.n - (1 << j) + 1)]
            self.mx.append(cur_x)
            self.mn.append(cur_n)
            j += 1

    def span(self, a, b):
        j = (b - a + 1).bit_length() - 1
        hi = max(self.mx[j][a], self.mx[j][b - (1 << j) + 1])
        lo = min(self.mn[j][a], self.mn[j][b - (1 << j) + 1])
        return hi - lo


def has_lex_cut(seg, witness=False, threshold=2):
    n = len(seg)
    if n < 4:
        return False
    rs = RangeSpan(seg)
    L, H = min(seg), max(seg)
    S = H - L
    for r in range(1, n - 1):
        s1 = rs.span(0, r)
        if s1 > S - 1 or s1 < threshold:
            continue
        if witness and not seg[r] >= H - 2:
            continue
        for r2 in range(r + 1, n - 1):
            if witness and not seg[r2] <= L + 2:
                continue
            s3 = rs.span(r2, n - 1)
            if s3 > S - 1 or s3 < threshold:
                continue
            if rs.span(r, r2) < threshold:
                continue
            return True
    return False


def part2(subs):
    total = 0
    fp, fw, f3 = [], [], 0
    for tag, seg in subs:
        if max(seg) - min(seg) < 4:
            continue
        total += 1
        if not has_lex_cut(seg):
            fp.append((tag, len(seg)))
        if not has_lex_cut(seg, witness=True):
            fw.append((tag, len(seg)))
        if not has_lex_cut(seg, threshold=3):
            f3 += 1
    print("LexCut census: subchains of span >= 4 tested:", total)
    print("  failures (plain):", len(fp), fp[:5])
    print("  failures (crookedness-witness form):", len(fw), fw[:5])
    print("  failures (every piece of span >= 3):", f3,
          "= %.2f%%" % (100.0 * f3 / max(total, 1)))


# ------------------- part 3: Tracking at a three-point window

def folds_from(seq, walk, start):
    """Is there a Lipschitz time-assignment of `seq` onto `walk`, beginning at
    time `start`?  Bitmask reachability over times."""
    n = len(walk)
    cur = 0
    if abs(seq[0] - walk[start]) <= 1:
        cur = 1 << start
    if cur == 0:
        return False
    for x in seq[1:]:
        nxt = (cur | (cur << 1) | (cur >> 1)) & ((1 << n) - 1)
        allowed = 0
        for u in range(n):
            if abs(x - walk[u]) <= 1:
                allowed |= 1 << u
        cur = nxt & allowed
        if cur == 0:
            return False
    return True


def zigzags(v, lo, hi, depth):
    """Walks of the shape v -> t1 -> t2 -> ... with `depth` turning targets,
    all turning targets in [lo, hi]; each leg is a unit-step run."""
    out = []

    def run(a, b):
        if a <= b:
            return list(range(a, b + 1))
        return list(range(a, b - 1, -1))

    def rec(walk, last, d):
        out.append(list(walk))
        if d == 0:
            return
        for t in range(lo, hi + 1):
            if t == last:
                continue
            rec(walk + run(last, t)[1:], t, d - 1)

    rec([v], v, depth)
    return out


def window_tracking_ok(rho, a, max_turns=4):
    """The instance of `Tracking` that `s3_of_tracking` uses at the window
    [a, a+2]: with v the window's centre, is there a walk beginning at v onto
    which the suffix from a+2 and the reversed prefix up to a both fold from
    time 0?"""
    n = len(rho)
    L, H = min(rho), max(rho)
    m = min(rho[a], rho[a + 1], rho[a + 2])
    v = min(H - 1, m + 1)
    suffix = rho[a + 2:]
    prefix = rho[a::-1]
    for depth in range(0, max_turns + 1):
        for walk in zigzags(v, L + 1, H - 1, depth):
            if folds_from(suffix, walk, 0) and folds_from(prefix, walk, 0):
                return True, depth
    return False, None


def part3(chains, max_turns=4):
    bad = []
    tested = 0
    depths = Counter()
    for tag, seq in chains:
        n = len(seq)
        if max(seq) - min(seq) < 3:
            continue
        for a in range(0, n - 3):
            tested += 1
            ok, d = window_tracking_ok(seq, a, max_turns)
            if ok:
                depths[d] += 1
            else:
                bad.append((tag, a))
    print("Tracking at three-point windows: windows tested:", tested)
    print("  turning targets needed:", sorted(depths.items()))
    print("  failures (no walk found within the search):", len(bad), bad[:10])


# ---------------------------------------------------------------- driver

if __name__ == "__main__":
    part1()
    print()
    random.seed(27)
    subs = []
    n8 = len(P8)
    for a in range(0, n8, 5):
        for b in range(a + 1, n8, 5):
            subs.append(("b8", P8[a:b + 1]))
    n10 = len(P10)
    for _ in range(4000):
        a = random.randrange(n10 - 1)
        b = random.randrange(a + 1, min(a + 260, n10))
        subs.append(("b10", P10[a:b + 1]))
    part2(subs)
    print()
    corpus = [("bing 0 4", bing_path(0, 4)), ("bing 0 5", bing_path(0, 5)),
              ("bing 0 6", bing_path(0, 6)), ("bing 0 7", bing_path(0, 7)),
              ("bing 0 8", P8), ("cutSeq", CUT)]
    for _ in range(60):
        a = random.randrange(n10 - 40)
        b = random.randrange(a + 40, min(a + 200, n10))
        seg = P10[a:b + 1]
        corpus.append(("b10 sub", seg))
    part3(corpus)
