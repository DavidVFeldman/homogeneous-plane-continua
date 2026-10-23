"""Which crookedness clauses does the span-seven fold at p = 3 actually need?

Same exact product reachability as `explore-auto3.py`, but the crookedness automaton only
enforces the clauses selected by `rise` / `fall` filters.
"""

import importlib.util
from collections import deque

L, H = 0, 7
NEG, POS = -99, 99


def load(name, path):
    s = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m)
    return m


cs = load("cs", "/workspace/request-project/census-batch38.py")


def make_step(rise, fall):
    def step(state, y):
        val, lev = state
        for a in range(L, H + 1):
            e = lev[a]
            if e is None:
                continue
            M, m, Q, D = e
            if a <= y - 3 and rise(a, y) and not (Q >= y - 2):
                return None
            if a >= y + 3 and fall(a, y) and not (D <= y + 1):
                return None
        out = []
        for a in range(L, H + 1):
            e = lev[a]
            if e is None:
                out.append(None)
                continue
            M, m, Q, D = e
            if y <= a + 1:
                Q = max(Q, M)
            if y >= a - 2:
                D = min(D, m)
            out.append((max(M, y), min(m, y), Q, D))
        out[y] = (NEG, POS, NEG, POS)
        return (y, tuple(out))
    return step


def serves(walk, p, choices, rise, fall):
    step = make_step(rise, fall)
    preds = [cs.pred_low(tl, th) if c == 'L' else cs.pred_high(tl, th) for (c, tl, th) in choices]
    pred = cs.product_pred(preds)
    lw = len(walk)
    full = (1 << lw) - 1
    amask = {x: sum(1 << u for u in range(lw) if abs(walk[u] - x) <= 1) for x in range(L, H + 1)}
    ck0 = (p, tuple((NEG, POS, NEG, POS) if a == p else None for a in range(L, H + 1)))
    start = (ck0, pred(tuple(0 for _ in preds), p), 1 if abs(walk[0] - p) <= 1 else 0)
    par = {start: None}
    q = deque([start])
    while q:
        st = q.popleft()
        for y in (st[0][0] - 1, st[0][0], st[0][0] + 1):
            if not (L <= y <= H):
                continue
            ps = pred(st[1], y)
            if ps is None:
                continue
            ck = step(st[0], y)
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
    return True, len(par), None


if __name__ == "__main__":
    w3 = [2, 3, 4, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6]
    ch3 = [('H', 0, 7), ('L', 0, 6)]
    no = lambda a, y: False
    tests = {
        "none": (no, no),
        "rise a<=1, y=7": (lambda a, y: a <= 1 and y == 7, no),
        "rise a<=1": (lambda a, y: a <= 1, no),
        "rise y=7": (lambda a, y: y == 7, no),
        "rise y>=6": (lambda a, y: y >= 6, no),
        "rise all": (lambda a, y: True, no),
        "fall all": (no, lambda a, y: True),
        "rise a<=1,y=7 + fall a=7": (lambda a, y: a <= 1 and y == 7, lambda a, y: a == 7),
        "all": (lambda a, y: True, lambda a, y: True),
    }
    for tag, (r, f) in tests.items():
        ok, n, bad = serves(w3, 3, ch3, r, f)
        print(f"  {tag}: serves={ok} states={n}" + ("" if ok else f" bad={bad}"))
