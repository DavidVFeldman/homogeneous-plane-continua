"""greedy-batch39.py — the greedy time assignment on a given walk, for a given arm class.

The Lean folds of batches 37-39 are built by the *greedy* time assignment: at each step the arm
is carried as far along the walk as the new level allows.  This program decides, for a walk and a
class of arms, whether the greedy assignment stays legal at every arm length, and computes the
data the Lean invariant needs: for each history flag, the least greedy time reachable with that
flag set, as a function of the level.

The arm class is described by
  * the band [0, N] and the basepoint p,
  * `conds`: the LowAt/HighAt conditions the dichotomy supplies on both arms,
  * the full crookedness clause family Cl(a,b), Dl(a,b) for a + 3 <= b, which holds on every arm.

Run: python3 greedy-batch39.py
"""

N = 8
L = 0
H = N

# ---------------------------------------------------------------- the walk


def win(walk, v, q):
    return 0 <= q < len(walk) and abs(v - walk[q]) <= 1


def gstep(walk, v, q):
    if win(walk, v, q + 1):
        return q + 1
    if win(walk, v, q):
        return q
    return q - 1


# ---------------------------------------------------------------- conditions

# a condition is ('H', tl, th) = HighAt(tl,th) or ('L', tl, th) = LowAt(tl,th)


def clause_list(N):
    cl = []
    for a in range(0, N - 2):
        for b in range(a + 3, N + 1):
            cl.append(('C', a, b))
            cl.append(('D', a, b))
    return cl


class Flags:
    """history flags: condition flags, crookedness clause states, extra named flags"""

    __slots__ = ('cond', 'cls', 'seen')

    def __init__(self, cond, cls, seen):
        self.cond = cond      # tuple of ints, per condition
        self.cls = cls        # tuple of (state, reset_seen) per clause
        self.seen = seen      # tuple of bools: extra monotone level flags

    def key(self):
        return (self.cond, self.cls, self.seen)


def update(conds, clauses, extra, F, v):
    cond = []
    for c, s in zip(conds, F.cond):
        kind, tl, th = c
        if kind == 'H':
            if v <= tl + 1:
                s |= 1
        else:
            if (s & 2) and v >= th - 2:
                s |= 4
            if v >= th:
                s |= 1
            if v <= tl + 1:
                s |= 2
        cond.append(s)
    cls = []
    for c, (s, sr) in zip(clauses, F.cls):
        kind, a, b = c
        if kind == 'C':
            if v <= a:
                s, sr = 0, 1
            else:
                if s >= 1 and v <= a + 1:
                    s = 2
                elif v >= b - 2 and s == 0:
                    s = 1
        else:
            if v >= b:
                s, sr = 0, 1
            else:
                if s >= 1 and v >= b - 2:
                    s = 2
                elif v <= a + 1 and s == 0:
                    s = 1
        cls.append((s, sr))
    seen = []
    for (name, test), old in zip(extra, F.seen):
        seen.append(old or test(v))
    return Flags(tuple(cond), tuple(cls), tuple(seen))


def admissible(conds, clauses, F, v):
    for c, s in zip(conds, F.cond):
        kind, tl, th = c
        if kind == 'H':
            if v >= th and not (s & 1):
                return False
        else:
            if v <= tl and not ((s & 1) or (s & 4)):
                return False
    for c, (s, sr) in zip(clauses, F.cls):
        kind, a, b = c
        if not sr:
            continue
        if kind == 'C':
            if v >= b and s != 2:
                return False
        else:
            if v <= a and s != 2:
                return False
    return True


def analyse(walk, p, conds, extra=(), verbose=True):
    clauses = clause_list(N)
    F0 = Flags(tuple(0 for _ in conds), tuple((0, 0) for _ in clauses),
               tuple(False for _ in extra))
    F0 = update(conds, clauses, extra, F0, p)
    if not win(walk, p, 0):
        return None, 'walk does not start within one of the basepoint'
    start = (F0.key(), p, 0)
    seen = {start}
    stack = [(F0, p, 0)]
    reach = {}
    reach.setdefault((p, 0), set()).add(F0.key())
    bad = None
    while stack:
        F, v, q = stack.pop()
        for v2 in (v - 1, v, v + 1):
            if v2 < 0 or v2 > N:
                continue
            if not admissible(conds, clauses, F, v2):
                continue
            q2 = gstep(walk, v2, q)
            if not win(walk, v2, q2):
                bad = (v, q, v2, q2)
                return None, 'greedy fails: level %d time %d -> level %d time %d' % bad
            F2 = update(conds, clauses, extra, F, v2)
            st = (F2.key(), v2, q2)
            if st not in seen:
                seen.add(st)
                stack.append((F2, v2, q2))
    # bounds
    info = {}
    for (fk, v, q) in seen:
        info.setdefault(v, []).append((fk, q))
    return seen, info


def report(name, walk, p, conds, flagnames=None):
    print('=== %s : walk %s, p = %d, conds %s ===' % (name, walk, p, conds))
    res, info = analyse(walk, p, conds)
    if res is None:
        print('   FAILS:', info)
        return False
    print('   greedy stays legal at every length (%d states)' % len(res))
    # unconditional minimum time per level
    mins = {}
    for (fk, v, q) in res:
        mins[v] = min(mins.get(v, 99), q)
    print('   min greedy time per level:', dict(sorted(mins.items())))
    return True


if __name__ == '__main__':
    print('# span eight leaf branches: does the greedy assignment work on the chosen walks?')
    # p = 3, split at (0,7)
    leaf3 = [('H', 0, 8), ('L', 0, 6)]
    report('p=3 LowAt(0,7)', [2, 3, 4, 5, 6, 5, 4, 3, 2, 1], 3, leaf3 + [('L', 0, 7)])
    report('p=3 HighAt(0,7)', [2, 3, 4, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6], 3, leaf3 + [('H', 0, 7)])
    # p = 4, split at (0,8) then (1,7)
    leaf4 = [('H', 1, 8), ('L', 0, 7)]
    report('p=4 LowAt(0,8), LowAt(1,7)', [3, 4, 5, 6, 5, 4, 3, 2, 3, 4, 5, 6, 7], 4,
           leaf4 + [('L', 0, 8), ('L', 1, 7)])
    report('p=4 LowAt(0,8), HighAt(1,7)', [5, 4, 3, 2, 3, 4, 5, 6, 7], 4,
           leaf4 + [('L', 0, 8), ('H', 1, 7)])
    report('p=4 HighAt(0,8), LowAt(1,7)', [3, 4, 5, 6, 5, 4, 3, 2, 1], 4,
           leaf4 + [('H', 0, 8), ('L', 1, 7)])
    report('p=4 HighAt(0,8), HighAt(1,7)', [5, 4, 3, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1], 4,
           leaf4 + [('H', 0, 8), ('H', 1, 7)])
    # p = 5, split at (1,8)
    leaf5 = [('H', 2, 8), ('L', 0, 8)]
    report('p=5 LowAt(1,8)', [6, 5, 4, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2], 5, leaf5 + [('L', 1, 8)])
    report('p=5 HighAt(1,8)', [6, 5, 4, 3, 2, 3, 4, 5, 6, 7], 5, leaf5 + [('H', 1, 8)])
