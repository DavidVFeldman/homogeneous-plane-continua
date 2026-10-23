"""Does a single walk serve every internally crooked arm of a leaf class?  Exact, all lengths.

Reachability over the product (crookedness state, class-predicate state, fold mask).
The walk serves the class iff no reachable state has an empty mask.
"""

import importlib.util
import itertools
import sys
from collections import deque


def load(name, path):
    s = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m)
    return m


ea = load("ea", "/workspace/request-project/explore-auto.py")
cs = load("cs", "/workspace/request-project/census-batch38.py")
L, H = 0, 7
NEG, POS = ea.NEG, ea.POS


def crook_start(p):
    return (p, p <= 1, tuple((NEG, POS, NEG, POS) if a == p else None for a in range(L, H + 1)))


def serves(walk, p, choices, cap=4_000_000):
    """exact: does every internally crooked arm of the class fold onto `walk`?"""
    preds = [cs.pred_low(tl, th) if c == 'L' else cs.pred_high(tl, th) for (c, tl, th) in choices]
    pred = cs.product_pred(preds)
    lw = len(walk)
    full = (1 << lw) - 1
    amask = {}
    for x in range(L, H + 1):
        m = 0
        for u in range(lw):
            if abs(walk[u] - x) <= 1:
                m |= 1 << u
        amask[x] = m
    ps0 = pred(tuple(0 for _ in preds), p)
    if ps0 is None:
        return True, 0, None
    m0 = 1 if abs(walk[0] - p) <= 1 else 0
    if not m0:
        return False, 0, [p]
    start = (crook_start(p), ps0, m0)
    par = {start: None}
    q = deque([start])
    while q:
        st = q.popleft()
        cur = st[0][0]
        for y in (cur - 1, cur, cur + 1):
            if not (L <= y <= H):
                continue
            ps = pred(st[1], y)
            if ps is None:
                continue
            ck = ea.step(st[0], y)
            if ck is None:
                continue
            m = st[2]
            m = (m | (m << 1) | (m >> 1)) & amask[y] & full
            nx = (ck, ps, m)
            if nx in par:
                continue
            par[nx] = st
            if m == 0:
                out = []
                z = nx
                while z is not None:
                    out.append(z[0][0])
                    z = par[z]
                return False, len(par), out[::-1]
            q.append(nx)
            if len(par) > cap:
                return None, len(par), None
    return True, len(par), None


def walks(maxlen, starts):
    for c0 in starts:
        for ln in range(1, maxlen + 1):
            for steps in itertools.product((-1, 1), repeat=ln - 1):
                w = [c0]
                ok = True
                for s in steps:
                    w.append(w[-1] + s)
                    if not (L - 1 <= w[-1] <= H + 1):
                        ok = False
                        break
                if ok:
                    yield w


if __name__ == "__main__":
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    base = [('H', 0, 7), ('L', 0, 6), ('L', 0, 5), ('L', 0, 4), ('L', 1, 4)]
    p = 3
    for a in 'LH':
        for b in 'LH':
            choices = base + [(a, 1, 5), (b, 1, 6)]
            tag = " & ".join(f"{c}({tl},{th})" for (c, tl, th) in choices)
            print("  " + tag)
            found = []
            for w in walks(maxlen, (p - 1, p, p + 1)):
                r, n, bad = serves(w, p, choices)
                if r:
                    found.append(w)
                    print(f"    serves: {w}  (states {n})")
                    sys.stdout.flush()
            if not found:
                print(f"    no walk of length <= {maxlen} serves the class")
            sys.stdout.flush()
