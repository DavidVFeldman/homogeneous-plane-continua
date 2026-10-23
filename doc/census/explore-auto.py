"""Exact automaton for internally crooked 1-Lipschitz arms in [L,H].

State (Myhill-Nerode): the current value, and for every level a that has already
occurred, four numbers computed over the window strictly after the *last* occurrence
of a: the max M_a, the min m_a, the largest value that is followed (inside the window)
by a value <= a+1, and the smallest value that is followed by a value >= a-2.

Appending y at time t is legal iff, for every level a that has occurred,
  a <= y-3  ->  Q_a >= y-2     (the rise clause for the pair (last a, t))
  a >= y+3  ->  D_a <= y+1     (the fall clause)
This is exact: the last occurrence of a is the binding one for level a.
"""

import sys
from collections import deque

L, H = 0, 7
NEG, POS = -99, 99


def step(state, y):
    val, flag, lev = state
    lev = list(lev)
    for a in range(L, H + 1):
        e = lev[a]
        if e is None:
            continue
        M, m, Q, D = e
        if a <= y - 3 and not (Q >= y - 2):
            return None
        if a >= y + 3 and not (D <= y + 1):
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
        M = max(M, y)
        m = min(m, y)
        out.append((M, m, Q, D))
    out[y] = (NEG, POS, NEG, POS)
    return (y, flag or y <= 1, tuple(out))


def bfs(p, highat=True, limit=20_000_000):
    start = (p, p <= 1, tuple((NEG, POS, NEG, POS) if a == p else None
                              for a in range(L, H + 1)))
    seen = {start}
    q = deque([start])
    reached = None
    while q:
        st = q.popleft()
        for y in (st[0] - 1, st[0], st[0] + 1):
            if not (L <= y <= H):
                continue
            if highat and y >= H and not st[1]:
                continue
            nx = step(st, y)
            if nx is None or nx in seen:
                continue
            if y >= H:
                reached = nx
            seen.add(nx)
            q.append(nx)
            if len(seen) > limit:
                return None, len(seen), "limit"
    return reached, len(seen), "closed"


if __name__ == "__main__":
    for p in (3, 4):
        for ha in (True, False):
            r, n, how = bfs(p, ha)
            print(f"p={p} highat={ha}: states {n} ({how}); reaches {H}: {r is not None}")
            sys.stdout.flush()


def witness(p, highat=True):
    start = (p, p <= 1, tuple((NEG, POS, NEG, POS) if a == p else None
                              for a in range(L, H + 1)))
    par = {start: None}
    q = deque([start])
    while q:
        st = q.popleft()
        for y in (st[0] - 1, st[0], st[0] + 1):
            if not (L <= y <= H):
                continue
            if highat and y >= H and not st[1]:
                continue
            nx = step(st, y)
            if nx is None or nx in par:
                continue
            par[nx] = st
            if y >= H:
                out = []
                cur = nx
                while cur is not None:
                    out.append(cur[0])
                    cur = par[cur]
                return out[::-1]
            q.append(nx)
    return None
