"""Product of the crookedness automaton with the leaf class predicates: exact, all lengths."""

import importlib.util
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


def search(p, choices, target):
    preds = [cs.pred_low(tl, th) if c == 'L' else cs.pred_high(tl, th) for (c, tl, th) in choices]
    pred = cs.product_pred(preds)
    s0 = tuple(0 for _ in preds)
    ps0 = pred(s0, p)
    if ps0 is None:
        return "class empty at basepoint", 0
    start = (crook_start(p), ps0)
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
            nx = (ck, ps)
            if nx in par:
                continue
            par[nx] = st
            if y == target:
                out = []
                z = nx
                while z is not None:
                    out.append(z[0][0])
                    z = par[z]
                return out[::-1], len(par)
            q.append(nx)
    return None, len(par)


if __name__ == "__main__":
    base = [('H', 0, 7), ('L', 0, 6), ('L', 0, 5), ('L', 0, 4), ('L', 1, 4)]
    print("== leaf classes at p = 3, exact over all lengths ==")
    for a in 'LH':
        for b in 'LH':
            choices = base + [(a, 1, 5), (b, 1, 6)]
            tag = " & ".join(f"{c}({tl},{th})" for (c, tl, th) in choices)
            print("  " + tag)
            for tgt in (H, L):
                r, n = search(3, choices, tgt)
                print(f"    states {n}; reaches {tgt}: {r}")
                sys.stdout.flush()
    print()
    print("== single conditions at p = 3 ==")
    for choices in ([('H', 0, 7)], [('H', 0, 7), ('L', 1, 4)], [('H', 0, 7), ('L', 0, 4)]):
        tag = " & ".join(f"{c}({tl},{th})" for (c, tl, th) in choices)
        r, n = search(3, choices, H)
        print(f"  {tag}: states {n}; reaches {H}: {r}")
