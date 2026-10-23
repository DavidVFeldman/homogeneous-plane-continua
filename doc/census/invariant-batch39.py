"""invariant-batch39.py — the data the Lean span-eight folds need.

For a walk, a basepoint and a class of arms (the leaf conditions, the branch condition of one
`dichotomy_at` split, and one crookedness clause read monotonically), this computes

  * whether the greedy time assignment stays legal at every arm length,
  * for each history feature and each polarity, the least greedy time reachable — the bounds of
    the Lean invariant,
  * and it checks that the resulting invariant is closed under one greedy step, which is exactly
    the `prog` lemma of the Lean proof.

Features are monotone: `('ge', c)` = a level >= c has occurred, `('le', c)` = a level <= c has
occurred, `('then', i, test)` = feature i has held and later the level satisfied `test`.

Run: python3 invariant-batch39.py
"""

from itertools import product

N = 8


def feat_step(flags, holds, v):
    out = []
    for i, f in enumerate(flags):
        if f[0] == 'ge':
            out.append(holds[i] or v >= f[1])
        elif f[0] == 'le':
            out.append(holds[i] or v <= f[1])
        else:
            _, j, test = f
            fire = holds[j] and (v >= test[1] if test[0] == 'ge' else v <= test[1])
            out.append(holds[i] or fire)
    return tuple(out)


def feat_init(flags, p):
    return feat_step(flags, tuple(False for _ in flags), p)


def win(walk, v, q):
    return 0 <= q < len(walk) and abs(v - walk[q]) <= 1


def gstep(walk, v, q):
    if win(walk, v, q + 1):
        return q + 1
    if win(walk, v, q):
        return q
    return q - 1


def guard_ok(guards, holds, v):
    """guards: (level-test, alternatives); an alternative is i (feature i holds) or ('not', i)"""
    for (test, alts) in guards:
        fires = v >= test[1] if test[0] == 'ge' else v <= test[1]
        if not fires:
            continue
        ok = False
        for alt in alts:
            if isinstance(alt, tuple):
                if not holds[alt[1]]:
                    ok = True
            elif holds[alt]:
                ok = True
        if not ok:
            return False
    return True


def reachable(walk, p, flags, guards):
    st0 = feat_init(flags, p)
    if not win(walk, p, 0):
        return 'the walk does not start within one of the basepoint'
    seen = {(st0, p, 0)}
    stack = [(st0, p, 0)]
    while stack:
        st, v, q = stack.pop()
        for v2 in (v - 1, v, v + 1):
            if v2 < 0 or v2 > N:
                continue
            if not guard_ok(guards, st, v2):
                continue
            q2 = gstep(walk, v2, q)
            if not win(walk, v2, q2):
                return 'greedy fails at level %d time %d -> level %d time %d' % (v, q, v2, q2)
            st2 = feat_step(flags, st, v2)
            key = (st2, v2, q2)
            if key not in seen:
                seen.add(key)
                stack.append(key)
    return seen


def bound_tables(flags, reach):
    nf = len(flags)
    bnd = [[dict(), dict()] for _ in range(nf)]     # [feature][polarity][level] = least time
    for (st, v, q) in reach:
        for i in range(nf):
            d = bnd[i][1 if st[i] else 0]
            d[v] = min(d.get(v, 99), q)
    return bnd


def closure(walk, p, flags, guards, bnd):
    """all abstract (assignment, level, time) satisfying the bounds are closed under a step"""
    nf = len(flags)
    bad = []
    for holds in product([False, True], repeat=nf):
        for v in range(N + 1):
            if any(v not in bnd[i][1 if holds[i] else 0] for i in range(nf)):
                continue                       # this assignment is unreachable at this level
            lo = max(bnd[i][1 if holds[i] else 0][v] for i in range(nf))
            for q in range(lo, len(walk)):
                if not win(walk, v, q):
                    continue
                for v2 in (v - 1, v, v + 1):
                    if v2 < 0 or v2 > N:
                        continue
                    if not guard_ok(guards, holds, v2):
                        continue
                    q2 = gstep(walk, v2, q)
                    if not win(walk, v2, q2):
                        bad.append(('window', holds, v, q, v2, q2))
                        continue
                    h2 = feat_step(flags, holds, v2)
                    for i in range(nf):
                        d = bnd[i][1 if h2[i] else 0]
                        if v2 not in d:
                            bad.append(('unreachable', i, holds, v, q, v2, q2))
                        elif q2 < d[v2]:
                            bad.append(('bound', i, holds, v, q, v2, q2, d[v2]))
    return bad


def show(name, walk, p, flags, guards):
    print('=== %s ===' % name)
    print('   walk %s, basepoint %d, length %d' % (walk, p, len(walk)))
    reach = reachable(walk, p, flags, guards)
    if isinstance(reach, str):
        print('   ' + reach)
        return None
    bnd = bound_tables(flags, reach)
    print('   greedy legal at every length (%d abstract states)' % len(reach))
    for i, f in enumerate(flags):
        print('   feature %-22s holds: %s' % (str(f), dict(sorted(bnd[i][1].items()))))
        print('   %-30s fails: %s' % ('', dict(sorted(bnd[i][0].items()))))
    bad = closure(walk, p, flags, guards, bnd)
    print('   closure failures: %d' % len(bad))
    for b in bad[:8]:
        print('      ', b)
    return bnd


if __name__ == '__main__':
    # ---------- p = 3, the branch HighAt(0,7) ----------
    # 0: seen <= 1        (HighAt(0,8) and HighAt(0,7) trigger; Cl(1,7) trigger level)
    # 1: seen >= 6        (LowAt(0,6) first clause)
    # 2: (0) then >= 4    (LowAt(0,6) second clause)
    # 3: seen >= 5        (Cl(1,7) first witness)
    # 4: (3) then <= 2    (Cl(1,7) pattern)
    flags3H = [('le', 1), ('ge', 6), ('then', 0, ('ge', 4)), ('ge', 5),
               ('then', 3, ('le', 2))]
    guards3H = [(('ge', 8), [0]),
                (('le', 0), [1, 2]),
                (('ge', 7), [0]),
                (('ge', 7), [('not', 0), 4])]
    show('p=3, HighAt(0,7)', [2, 3, 4, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7], 3, flags3H, guards3H)

    # ---------- p = 3, the branch LowAt(0,7) ----------
    # 0: seen <= 1, 1: seen >= 6, 2: (0) then >= 4, 3: seen >= 7, 4: (0) then >= 5,
    # 5: (1) then <= 2   (Cl(1,8) pattern)
    flags3L = [('le', 1), ('ge', 6), ('then', 0, ('ge', 4)), ('ge', 7),
               ('then', 0, ('ge', 5)), ('then', 1, ('le', 2))]
    guards3L = [(('ge', 8), [0]),
                (('le', 0), [1, 2]),
                (('le', 0), [3, 4]),
                (('ge', 8), [('not', 0), 5])]
    show('p=3, LowAt(0,7)', [2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7], 3, flags3L,
         guards3L)
