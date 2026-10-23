"""Census for batch 38 -- span seven.

Conventions.  An arm is a 1-Lipschitz integer sequence with values in [L, H], based at its
first entry.  A walk is a 1-Lipschitz sequence of centres; an arm f folds onto a walk c iff
there is a 1-Lipschitz time assignment beta with beta 0 = 0 and |f j - c (beta j)| <= 1 for
every j, decided exactly by reachability over the walk's times (a bitmask sweep).  Throughout
L = 0, H = 7, and the interior basepoints are p = 3 and p = 4.

The conditions of the Lean file, at a pair of levels (tl, th) with tl + 3 <= th:

    LowAt  f tl th : for every d with f d <= tl, either f reaches th before d,
                     or f reaches tl+1 and afterwards th-2, both before d.
    HighAt f tl th : for every d with f d >= th, f reaches tl+1 before d.

The folding half needs only the switch condition at the basepoint p:

    Switch f p    : before f first falls to p-3 there is a time s >= H - p with f s >= H - 2.

and `bumpWalk p H` is  p-1, p, ..., H-1, H-2, ..., L+1  (peak index A = H - p).

Sections.

  1  The dichotomy at arbitrary levels, on the corpus of stretches of Bing's chains: at every
     interior basepoint of every stretch of `bing 0 d` whose band is exactly seven wide, and at
     every admissible level pair, either both arms are LowAt or both arms are HighAt.  (This is
     what `dichotomy_at` proves from the crookedness clause; the census is the independent check.)

  2  The bridge and the explicit fold, exhaustively: for every 1-Lipschitz arm of length at most
     fourteen satisfying `LowAt (p-3) H` or `LowAt (p-2) H`, the switch condition holds, and the
     greedy assignment that `foldsOnto_bumpWalk_of_switch` constructs is a fold onto `bumpWalk`.

  3  The same statement for arms of *every* length, exactly, by reachability over the product of
     (level, DP mask, predicate state): no arm satisfying the switch condition fails `bumpWalk`.

  4  What is left of span seven.  For every admissible level pair, whether a single walk of
     length at most twelve serves every arm of the corresponding class.  The servable classes are
     exactly the ones the Lean file uses; the leaf that survives every dichotomy is
     `HighAt(0,7) & LowAt(0,6) & ...`, and no walk of length at most thirteen serves it.

  6  At span six the batch-37 condition LowLate implies the switch condition, so the greedy
     assignment subsumes the phase device of batch 37.

  5  Why the leaf needs the arms' own crookedness.  The two arms that obstruct the leaf are
     exhibited; neither is internally crooked.  With internal crookedness imposed on the arms,
     walks serving the leaf reappear (evidence only: arms of length at most twelve).

Usage: python3 census-batch38.py
"""

import itertools
import sys
from collections import Counter, deque

L, H = 0, 7
INTERIOR = (3, 4)


# ---------------------------------------------------------------- Bing chains

def bpath(a, b):
    d = abs(a - b)
    if d <= 2:
        s = 1 if a <= b else -1
        return [a + s * u for u in range(d + 1)]
    mid = b - 1 if a < b else b + 1
    c = a + 1 if a < b else a - 1
    return bpath(a, mid) + bpath(mid, c)[1:] + bpath(c, b)[1:]


def stretches(rho, span):
    """all contiguous stretches whose level range is exactly `span`"""
    n = len(rho)
    out = []
    for a in range(n):
        lo = hi = rho[a]
        for b in range(a + 1, n):
            lo = min(lo, rho[b])
            hi = max(hi, rho[b])
            if hi - lo > span:
                break
            if hi - lo == span:
                out.append((a, b))
    return out


# ---------------------------------------------------------------- folding

def folds(f, c):
    lw = len(c)
    full = (1 << lw) - 1
    amask = {}
    for x in set(f):
        m = 0
        for u in range(lw):
            if abs(c[u] - x) <= 1:
                m |= 1 << u
        amask[x] = m
    cur = 1 if abs(f[0] - c[0]) <= 1 else 0
    if not cur:
        return False
    for j in range(1, len(f)):
        cur = (cur | (cur << 1) | (cur >> 1)) & amask[f[j]] & full
        if not cur:
            return False
    return True


def bump_walk(p):
    """p-1 up to H-1, then down to L+1"""
    up = [p - 1 + u for u in range(H - p + 1)]
    down = [H - 1 - v for v in range(1, H - 1 - L)]
    return up + down


# ---------------------------------------------------------------- predicates

def low_at(f, tl, th):
    for d, x in enumerate(f):
        if x > tl:
            continue
        if any(f[j] >= th for j in range(d)):
            continue
        if any(f[j] <= tl + 1 and any(f[k] >= th - 2 for k in range(j + 1, d))
               for j in range(d)):
            continue
        return False
    return True


def high_at(f, tl, th):
    for d, x in enumerate(f):
        if x < th:
            continue
        if any(f[j] <= tl + 1 for j in range(d)):
            continue
        return False
    return True


def switch(f, p):
    """before f first falls to p-3 there is a time s >= H - p with f s >= H - 2"""
    for d, x in enumerate(f):
        if x > p - 3:
            continue
        if any(s >= H - p and f[s] >= H - 2 for s in range(d)):
            continue
        return False
    return True


def pairs_admissible(p):
    """the level pairs the dichotomy can be applied at, at basepoint p"""
    out = []
    for tl in range(L, p - 1):
        for th in range(p + 1, H + 1):
            if th - tl >= 3:
                out.append((tl, th))
    return out


# ---------------------------------------------------------------- section 1

def section1():
    print("== 1. the dichotomy at arbitrary levels, on stretches of Bing's chains ==")
    tot = Counter()
    for d in (7, 8):
        rho = bpath(0, d)
        cnt = Counter()
        for (a, b) in stretches(rho, 7):
            seg = rho[a:b + 1]
            lo = min(seg)
            seg = [x - lo for x in seg]
            for i, x in enumerate(seg):
                if x not in INTERIOR:
                    continue
                g = seg[i:]
                t = seg[:i + 1][::-1]
                for (tl, th) in pairs_admissible(x):
                    cnt["instances"] += 1
                    lowpair = low_at(g, tl, th) and low_at(t, tl, th)
                    highpair = high_at(g, tl, th) and high_at(t, tl, th)
                    cnt["low"] += lowpair
                    cnt["high"] += highpair
                    if not (lowpair or highpair):
                        cnt["FAIL"] += 1
                        print("   FAILING INSTANCE", seg, i, tl, th)
        print(f"   bing 0 {d} ({len(rho)} links): " +
              ", ".join(f"{k} {v}" for k, v in sorted(cnt.items())))
        sys.stdout.flush()
        tot.update(cnt)
    print("   total: " + ", ".join(f"{k} {v}" for k, v in sorted(tot.items())))
    print(f"   dichotomy failures: {tot['FAIL']}")
    print()


# ---------------------------------------------------------------- section 2

def run_min(f):
    out = []
    cur = None
    for j, x in enumerate(f):
        v = x - j
        cur = v if cur is None else min(cur, v)
        out.append(cur)
    return out


def construct(f, p):
    """the assignment of `foldsOnto_bumpWalk_of_switch`: greedy ascent, then the descent"""
    A = H - p
    rm = run_min(f)
    a = [min(A, min(j, rm[j] + j - p + 2)) for j in range(len(f))]
    b = [A + max(H - 2 - f[j], 0) for j in range(len(f))]
    s = None
    for d in range(len(f)):
        if f[d] <= p - 3:
            for t in range(d):
                if t >= A and f[t] >= H - 2:
                    s = t
                    break
            break
    if s is None:
        return a
    return [a[j] if j < s else b[j] for j in range(len(f))]


def check_beta(f, beta, p):
    w = bump_walk(p)
    if beta[0] != 0:
        return "beta 0"
    for j in range(len(f)):
        if not (0 <= beta[j] < len(w)):
            return f"range at {j}"
        if abs(f[j] - w[beta[j]]) > 1:
            return f"window at {j}"
        if j and abs(beta[j] - beta[j - 1]) > 1:
            return f"Lipschitz at {j}"
    return None


def arms(p, maxlen):
    for ln in range(1, maxlen + 1):
        for steps in itertools.product((-1, 0, 1), repeat=ln - 1):
            f = [p]
            ok = True
            for st in steps:
                f.append(f[-1] + st)
                if not (L <= f[-1] <= H):
                    ok = False
                    break
            if ok:
                yield f


def section2(maxlen=14):
    print("== 2. the bridge and the greedy assignment, all arms of length <= %d ==" % maxlen)
    for p in INTERIOR:
        tested = bridged = bad = badbridge = 0
        for f in arms(p, maxlen):
            lowish = low_at(f, p - 3, H) or low_at(f, p - 2, H)
            if lowish:
                bridged += 1
                if not switch(f, p):
                    badbridge += 1
                    if badbridge < 4:
                        print("   BRIDGE FAIL", f)
            if not switch(f, p):
                continue
            tested += 1
            err = check_beta(f, construct(f, p), p)
            if err:
                bad += 1
                if bad < 4:
                    print("   FOLD FAIL", err, f)
        sys.stdout.flush()
        print(f"   p = {p}: walk {bump_walk(p)}")
        print(f"     LowAt arms {bridged}, bridge failures {badbridge}")
        print(f"     switch arms {tested}, fold failures {bad}")
    print()


# ---------------------------------------------------------------- section 3

def serves_all(w, p, pred, s0=0):
    """exact over arms of every length: does every arm satisfying `pred` fold onto `w`?"""
    lw = len(w)
    allowed = [0] * (H + 1)
    for x in range(H + 1):
        m = 0
        for u in range(lw):
            if abs(w[u] - x) <= 1:
                m |= 1 << u
        allowed[x] = m
    full = (1 << lw) - 1
    st0 = pred(s0, p)
    if st0 is None:
        return True, None
    m0 = 1 & allowed[p]
    if m0 == 0:
        return False, (p,)
    start = (m0, st0, p)
    seen = {start}
    dq = deque([(start, (p,))])
    while dq:
        (m, s, x), trace = dq.popleft()
        for y in (x - 1, x, x + 1):
            if not (L <= y <= H):
                continue
            s2 = pred(s, y)
            if s2 is None:
                continue
            m2 = (m | (m << 1) | (m >> 1)) & allowed[y] & full
            if m2 == 0:
                return False, trace + (y,)
            st = (m2, s2, y)
            if st not in seen:
                seen.add(st)
                dq.append((st, trace + (y,)))
    return True, None


def pred_switch(p):
    """states: (time capped at H-p, seen a good s).  None = the switch condition fails."""
    A = H - p

    def pred(s, y):
        if s == 'ok':
            return 'ok'
        j = s if isinstance(s, int) else 0
        if j >= A and y >= H - 2:
            return 'ok'
        if y <= p - 3:
            return None
        return min(j + 1, A)
    return pred


def pred_low(tl, th):
    def pred(s, y):
        if s == 2:
            return 2
        if y >= th:
            return 2
        if s == 1 and y >= th - 2:
            return 2
        if y <= tl:
            return None
        if y <= tl + 1:
            return 1
        return s
    return pred


def pred_high(tl, th):
    def pred(s, y):
        if s == 1:
            return 1
        if y <= tl + 1:
            return 1
        if y >= th:
            return None
        return 0
    return pred


def walks(maxlen, starts):
    for c0 in starts:
        for ln in range(1, maxlen + 1):
            for steps in itertools.product((-1, 1), repeat=ln - 1):
                w = [c0]
                ok = True
                for st in steps:
                    w.append(w[-1] + st)
                    if not (L - 1 <= w[-1] <= H + 1):
                        ok = False
                        break
                if ok:
                    yield w


def section3():
    print("== 3. the switch condition implies the fold, for arms of every length ==")
    for p in INTERIOR:
        w = bump_walk(p)
        ok, tr = serves_all(w, p, pred_switch(p), 0)
        print(f"   p = {p}: bumpWalk {w} serves every switch arm: {ok}" +
              ("" if ok else f" (witness {tr})"))
        good = [v for v in walks(len(w), (p - 1, p, p + 1))
                if serves_all(v, p, pred_switch(p), 0)[0]]
        print(f"     walks of length <= {len(w)} serving every switch arm: {len(good)}"
              f"; shortest {min(good, key=len) if good else None}")
    print()


# ---------------------------------------------------------------- section 4

def section4(maxlen=12):
    print("== 4. which classes have a walk, and what is left ==")
    for p in INTERIOR:
        print(f"   -- basepoint p = {p}")
        pool = list(walks(maxlen, (p - 1, p, p + 1)))
        leaf = []
        for (tl, th) in pairs_admissible(p):
            lw = [w for w in pool if serves_all(w, p, pred_low(tl, th))[0]]
            hw = [w for w in pool if serves_all(w, p, pred_high(tl, th))[0]]
            print(f"     ({tl},{th}): LowAt served by {len(lw)} walks"
                  f"{', e.g. ' + str(min(lw, key=len)) if lw else ''}"
                  f" | HighAt served by {len(hw)} walks"
                  f"{', e.g. ' + str(min(hw, key=len)) if hw else ''}")
            if not lw:
                leaf.append(('L', tl, th))
            if not hw:
                leaf.append(('H', tl, th))
        print(f"     classes with no walk of length <= {maxlen}: "
              + ", ".join(f"{c}({tl},{th})" for (c, tl, th) in leaf))
    print()


def product_pred(preds):
    def pred(s, y):
        out = []
        for pr, si in zip(preds, s):
            s2 = pr(si, y)
            if s2 is None:
                return None
            out.append(s2)
        return tuple(out)
    return pred


def section4b(maxlen=13):
    print("== 4b. the leaf that survives every dichotomy at p = 3 ==")
    p = 3
    choices = [('H', 0, 7), ('H', 1, 7), ('L', 0, 4), ('L', 0, 5), ('L', 0, 6), ('L', 1, 4),
               ('L', 1, 5), ('L', 1, 6)]
    preds = [pred_low(tl, th) if c == 'L' else pred_high(tl, th) for (c, tl, th) in choices]
    pred = product_pred(preds)
    s0 = tuple(0 for _ in preds)
    tag = " & ".join(f"{c}({tl},{th})" for (c, tl, th) in choices)
    good = [w for w in walks(maxlen, (p - 1, p, p + 1)) if serves_all(w, p, pred, s0)[0]]
    print(f"   {tag}")
    print(f"     walks of length <= {maxlen}: {len(good)}"
          f"{', e.g. ' + str(min(good, key=len)) if good else ''}")
    choices2 = choices[:-1] + [('H', 1, 6)]
    preds2 = [pred_low(tl, th) if c == 'L' else pred_high(tl, th) for (c, tl, th) in choices2]
    pred2 = product_pred(preds2)
    tag2 = " & ".join(f"{c}({tl},{th})" for (c, tl, th) in choices2)
    good2 = [w for w in walks(maxlen, (p - 1, p, p + 1)) if serves_all(w, p, pred2, s0)[0]]
    print(f"   {tag2}")
    print(f"     walks of length <= {maxlen}: {len(good2)}"
          f"{', e.g. ' + str(min(good2, key=len)) if good2 else ''}")
    print()


# ---------------------------------------------------------------- section 5

def crooked_new(f):
    """the crookedness clauses for the pairs (s, t) with t the last index"""
    t = len(f) - 1
    b = f[t]
    for s in range(t):
        a = f[s]
        if a >= b + 3:
            if not any(f[u] <= b + 1 and any(f[v] >= a - 2 for v in range(u + 1, t))
                       for u in range(s + 1, t)):
                return False
        if b >= a + 3:
            if not any(f[u] >= b - 2 and any(f[v] <= a + 1 for v in range(u + 1, t))
                       for u in range(s + 1, t)):
                return False
    return True


def crooked_arms(p, maxlen):
    out = []
    stack = [[p]]
    while stack:
        f = stack.pop()
        out.append(f)
        if len(f) == maxlen:
            continue
        for y in (f[-1] - 1, f[-1], f[-1] + 1):
            if not (L <= y <= H):
                continue
            g = f + [y]
            if crooked_new(g):
                stack.append(g)
    return out


def sat(f, pred, s0):
    s = s0
    for y in f:
        s = pred(s, y)
        if s is None:
            return False
    return True


def dfs_extreme(choices, maxlen, p):
    """depth-first search for an internally crooked arm of the class reaching L or H"""
    preds = [pred_low(tl, th) if c == 'L' else pred_high(tl, th) for (c, tl, th) in choices]
    pred = product_pred(preds)
    s0 = tuple(0 for _ in preds)
    stack = [([p], pred(s0, p))]
    cnt = 0
    while stack:
        f, st = stack.pop()
        cnt += 1
        if L in f or H in f:
            return f, cnt
        if len(f) == maxlen:
            continue
        for y in (f[-1] - 1, f[-1], f[-1] + 1):
            if not (L <= y <= H):
                continue
            st2 = pred(st, y)
            if st2 is None:
                continue
            g = f + [y]
            if crooked_new(g):
                stack.append((g, st2))
    return None, cnt


def section5(maxlen=16, walklen=13):
    print("== 5. the leaf, the arms' own crookedness, and the extremes ==")
    p = 3
    x = [3, 2, 3, 2, 1, 2, 3, 4, 5, 6, 7]
    y = [3, 2, 3, 2, 1, 2, 3, 4, 3, 2, 1, 0]
    print(f"   the two arms that obstruct the leaf: {x} and {y}")
    both = [w for w in walks(walklen, (p - 1, p, p + 1)) if folds(x, w) and folds(y, w)]
    print(f"     walks of length <= {walklen} taking both: {len(both)}")
    print(f"     internally crooked: {crooked_new_all(x)} and {crooked_new_all(y)}")
    print("   so the leaf can only be closed by using the arms' own crookedness.")
    print()
    print("   -- does a leaf class contain a crooked arm that reaches an extreme?")
    print("      (a class whose arms never reach one shrinks the band to [L+1, H-1], where")
    print("       both interior levels are near-extreme and `s3_near_extreme` settles them)")
    base = [('H', 0, 7), ('L', 0, 6), ('L', 0, 5), ('L', 0, 4), ('L', 1, 4)]
    for a in 'LH':
        for b in 'LH':
            choices = base + [(a, 1, 5), (b, 1, 6)]
            tag = " & ".join(f"{c}({tl},{th})" for (c, tl, th) in choices)
            r, cnt = dfs_extreme(choices, maxlen, p)
            print(f"     {tag}")
            print(f"       crooked arms of length <= {maxlen} searched: {cnt}; "
                  f"reaching an extreme: {r}")
            sys.stdout.flush()
    print()


def crooked_new_all(f):
    return all(crooked_new(f[:k + 1]) for k in range(len(f)))


def low_late6(f, L6, H6):
    """batch 37's LowLate, at the band [L6, H6]"""
    for d, x in enumerate(f):
        if x != L6:
            continue
        if any(f[j] >= H6 - 1 for j in range(d)):
            continue
        if any(f[j] <= L6 + 1 and any(f[k] >= H6 - 2 for k in range(j + 1, d))
               for j in range(d)):
            continue
        return False
    return True


def switch6(f, p, H6):
    for d, x in enumerate(f):
        if x > p - 3:
            continue
        if any(s >= H6 - p and f[s] >= H6 - 2 for s in range(d)):
            continue
        return False
    return True


def section6(maxlen=14):
    print("== 6. at span six the batch-37 condition implies the switch condition ==")
    L6, H6, p = 0, 6, 3
    tested = bad = 0
    for ln in range(1, maxlen + 1):
        for steps in itertools.product((-1, 0, 1), repeat=ln - 1):
            f = [p]
            ok = True
            for st in steps:
                f.append(f[-1] + st)
                if not (L6 <= f[-1] <= H6):
                    ok = False
                    break
            if not ok or not low_late6(f, L6, H6):
                continue
            tested += 1
            if not switch6(f, p, H6):
                bad += 1
                if bad < 4:
                    print("   FAIL", f)
    print(f"   LowLate arms of length <= {maxlen} in [0, 6] at p = 3: {tested}, "
          f"switch failures {bad}")
    print()


def dfs_target(choices, maxlen, p, tgt):
    """depth-first search for an internally crooked arm of the class reaching the level `tgt`"""
    preds = [pred_low(tl, th) if c == 'L' else pred_high(tl, th) for (c, tl, th) in choices]
    pred = product_pred(preds)
    s0 = tuple(0 for _ in preds)
    stack = [([p], pred(s0, p))]
    cnt = 0
    while stack:
        f, st = stack.pop()
        cnt += 1
        if tgt in f:
            return f, cnt
        if len(f) == maxlen:
            continue
        for y in (f[-1] - 1, f[-1], f[-1] + 1):
            if not (L <= y <= H):
                continue
            st2 = pred(st, y)
            if st2 is None:
                continue
            g = f + [y]
            if crooked_new(g):
                stack.append((g, st2))
    return None, cnt


def section7(maxlen=18):
    print("== 7. which extreme can a crooked arm of a leaf class reach? ==")
    print("   (an arm class that misses H lives in a band of width six, where `s3_span_six`")
    print("    settles the basepoint; one that misses both lives in a band of width five)")
    p = 3
    base = [('H', 0, 7), ('L', 0, 6), ('L', 0, 5), ('L', 0, 4), ('L', 1, 4)]
    for a in 'LH':
        for b in 'LH':
            choices = base + [(a, 1, 5), (b, 1, 6)]
            tag = " & ".join(f"{c}({tl},{th})" for (c, tl, th) in choices)
            print(f"     {tag}")
            for tgt in (H, L):
                r, cnt = dfs_target(choices, maxlen, p, tgt)
                print(f"       reaching {tgt}, arms of length <= {maxlen} searched {cnt}: {r}")
                sys.stdout.flush()
    print()



# ---------------------------------------------------------------- section 8

NEG, POS = -99, 99


def crook_step(state, y, rise=None, fall=None):
    """One letter of the exact automaton for *internal crookedness* of a 1-Lipschitz arm.

    State: the current value, and for every level `a` that has already occurred, four numbers
    read over the window strictly after the *last* occurrence of `a` -- the max `M`, the min
    `m`, the largest value `Q` that is followed inside the window by a value <= a+1, and the
    smallest value `D` that is followed by a value >= a-2.  Appending `y` is legal iff for
    every such level

        a <= y - 3  ->  Q >= y - 2      (the rise clause for the pair (last a, now))
        a >= y + 3  ->  D <= y + 1      (the fall clause)

    and this is exact, because for each level the last occurrence is the binding one.
    `rise` / `fall`, when given, restrict which clauses are enforced.
    """
    val, lev = state
    for a in range(L, H + 1):
        e = lev[a]
        if e is None:
            continue
        M, m, Q, D = e
        if a <= y - 3 and (rise is None or rise(a, y)) and not (Q >= y - 2):
            return None
        if a >= y + 3 and (fall is None or fall(a, y)) and not (D <= y + 1):
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


def crook_start(p):
    return (p, tuple((NEG, POS, NEG, POS) if a == p else None for a in range(L, H + 1)))


def crook_search(p, choices, target, rise=None, fall=None):
    """shortest internally crooked arm of the class that reaches `target`; exact, all lengths"""
    preds = [pred_low(tl, th) if c == 'L' else pred_high(tl, th) for (c, tl, th) in choices]
    pred = product_pred(preds)
    ps0 = pred(tuple(0 for _ in preds), p)
    if ps0 is None:
        return None, 0
    start = (crook_start(p), ps0)
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
            ck = crook_step(st[0], y, rise, fall)
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


def crook_search_seq(p, choices, targets, rise=None, fall=None):
    """shortest internally crooked arm of the class hitting `targets` in order; all lengths"""
    preds = [pred_low(tl, th) if c == 'L' else pred_high(tl, th) for (c, tl, th) in choices]
    pred = product_pred(preds)
    ps0 = pred(tuple(0 for _ in preds), p)
    if ps0 is None:
        return None, 0
    start = (crook_start(p), ps0, 0)
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
            ck = crook_step(st[0], y, rise, fall)
            if ck is None:
                continue
            k = st[2] + 1 if y == targets[st[2]] else st[2]
            nx = (ck, ps, k)
            if nx in par:
                continue
            par[nx] = st
            if k == len(targets):
                out = []
                z = nx
                while z is not None:
                    out.append(z[0][0])
                    z = par[z]
                return out[::-1], len(par)
            q.append(nx)
    return None, len(par)


def section8():
    print("== 8. do the arms of a leaf class stay away from an extreme?  (no: refuted) ==")
    print("   Batch 38's first route conjectured that internal crookedness plus the leaf")
    print("   conditions confine an arm to a band of width six.  The exact automaton above")
    print("   settles this over arms of every length, and the conjecture is false.")
    base = [('H', 0, 7), ('L', 0, 6), ('L', 0, 5), ('L', 0, 4), ('L', 1, 4)]
    p = 3
    for a in 'LH':
        for b in 'LH':
            choices = base + [(a, 1, 5), (b, 1, 6)]
            tag = " & ".join(f"{c}({tl},{th})" for (c, tl, th) in choices)
            print(f"   {tag}")
            for tgt in (H, L):
                r, n = crook_search(p, choices, tgt)
                chk = None if r is None else (crooked_new_all(r) and tgt in r)
                print(f"     states {n}; reaches {tgt}: {r}")
                print(f"       independently crooked (crooked_new_all): {chk}")
                sys.stdout.flush()
    print("   an arm of the first class attaining *both* extremes, in either order:")
    for targets in ((H, L), (L, H)):
        r, n = crook_search_seq(p, base + [('L', 1, 5), ('L', 1, 6)], targets)
        chk = None if r is None else (crooked_new_all(r) and L in r and H in r)
        print(f"     {targets[0]} then {targets[1]} (states {n}, length "
              f"{None if r is None else len(r)}): {r}")
        print(f"       independently crooked and attains both (crooked_new_all): {chk}")
        sys.stdout.flush()
    print("   -> a leaf-class arm can attain both 0 and 7; the band does not collapse.")
    print()


# ---------------------------------------------------------------- section 9

def walk7(p):
    return [2, 3, 4, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6] if p == 3 else \
           [5, 4, 3, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1]


def serves_crooked(walk, p, choices, rise=None, fall=None):
    """exact, over arms of every length: does every internally crooked arm of the class fold
    onto `walk`?  Reachability over (crookedness state, class state, fold mask)."""
    preds = [pred_low(tl, th) if c == 'L' else pred_high(tl, th) for (c, tl, th) in choices]
    pred = product_pred(preds)
    lw = len(walk)
    full = (1 << lw) - 1
    amask = {x: sum(1 << u for u in range(lw) if abs(walk[u] - x) <= 1) for x in range(L, H + 1)}
    ps0 = pred(tuple(0 for _ in preds), p)
    if ps0 is None:
        return True, 0, None
    if abs(walk[0] - p) > 1:
        return False, 0, [p]
    start = (crook_start(p), ps0, 1)
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
            ck = crook_step(st[0], y, rise, fall)
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


def section9(maxlen=11):
    print("== 9. the two leaf walks, and how little crookedness they need ==")
    no = lambda a, y: False
    yes = lambda a, y: True
    onerise = lambda a, y: a <= 1 and y == 7

    print("   -- p = 4, class HighAt(1,7) & LowAt(0,7), no crookedness assumed")
    w4 = walk7(4)
    ok, tr = serves_all(w4, 4, product_pred([pred_high(1, 7), pred_low(0, 7)]), (0, 0))
    print(f"      walk7' {w4}: serves every arm of the class: {ok}"
          + ("" if ok else f" (witness {tr})"))

    print("   -- p = 3, class HighAt(0,7) & LowAt(0,6)")
    w3 = walk7(3)
    ok, tr = serves_all(w3, 3, product_pred([pred_high(0, 7), pred_low(0, 6)]), (0, 0))
    print(f"      walk7 {w3} with no crookedness: serves {ok}"
          + ("" if ok else f" (witness {tr})"))
    tests = [("no clause", no, no),
             ("the single clause a <= 1, y = 7 (this is `Zig`)", onerise, no),
             ("every rise clause", yes, no),
             ("every fall clause", no, yes),
             ("full internal crookedness", None, None)]
    for tag, r, f in tests:
        ok, n, bad = serves_crooked(w3, 3, [('H', 0, 7), ('L', 0, 6)], r, f)
        print(f"      {tag}: serves={ok} states={n}" + ("" if ok else f" witness={bad}"))
        sys.stdout.flush()

    print(f"   -- no walk of length <= {maxlen} serves the p = 3 class, even with full")
    print("      internal crookedness assumed (so thirteen times is not extravagant)")
    found = []
    for w in walks(maxlen, (2, 3, 4)):
        ok, n, bad = serves_crooked(w, 3, [('H', 0, 7), ('L', 0, 6)], None, None)
        if ok:
            found.append(w)
    print(f"      walks of length <= {maxlen} that serve the class: {found}")
    print()


# ---------------------------------------------------------------- section 10

def val7(v, u):
    return ((0 <= u <= 3 and v - 3 <= u <= v - 1)
            or (3 <= u <= 7 and 7 - v <= u <= 9 - v)
            or (7 <= u <= 12 and v + 5 <= u <= v + 7))


def gstep7(v, q):
    if val7(v, q + 1):
        return q + 1
    if val7(v, q):
        return q
    return q - 1


def inv(v, q, E, E2, R, S):
    return (val7(v, q)
            and (not E or min(v - 1, 3) <= q)
            and (not E2 or min(9 - v, 7) <= q)
            and (not R or 7 - v <= q)
            and (not S or v + 5 <= q))


def section10():
    print("== 10. the greedy rule and its invariant: inductive, checked exhaustively ==")
    print("   The Lean fold assigns times greedily: at each step try q+1, else q, else q-1.")
    print("   The invariant carried is `Val7 v q` together with four progress clauses keyed to")
    print("   four monotone features of the arm:")
    print("      E  (the arm has been at <= 1)           ->  min(v-1, 3) <= q")
    print("      E2 (E, then >= 5;  or the arm >= 6)     ->  min(9-v, 7) <= q")
    print("      R  (>= 5;  or E, then >= 4)             ->  7 - v     <= q")
    print("      S  (E2, then <= 2;  or the arm <= 0)    ->  v + 5     <= q")
    print("   and the leaf conditions guarantee that a descent to 0 is preceded by R and an")
    print("   ascent to 7 by S.  Below: every transition allowed by those rules keeps the")
    print("   invariant, for every level, every legal time and every flag setting.")
    print(f"   base point: v = 3, q = 0, no flags -- invariant holds: {inv(3, 0, 0, 0, 0, 0)}")
    tested = bad = 0
    for v in range(L, H + 1):
        for q in range(-2, 15):
            for flags in itertools.product((0, 1), repeat=4):
                E, E2, R, S = flags
                if not inv(v, q, E, E2, R, S):
                    continue
                for v2 in (v - 1, v, v + 1):
                    if not (L <= v2 <= H):
                        continue
                    if v2 <= 0 and not R:
                        continue          # excluded by `hzero`
                    if v2 >= 7 and not S:
                        continue          # excluded by `hseven`
                    q2 = gstep7(v2, q)
                    # the strongest successor flags the update rules allow
                    E_ = E or v2 <= 1
                    E2_ = E2 or (E and v2 >= 5) or v2 >= 6
                    R_ = R or v2 >= 5 or (E and v2 >= 4)
                    S_ = S or (E2 and v2 <= 2) or v2 <= 0
                    tested += 1
                    if not inv(v2, q2, E_, E2_, R_, S_):
                        bad += 1
                        if bad < 5:
                            print(f"     FAIL v={v} q={q} flags={flags} -> v'={v2} q'={q2}")
    print(f"   transitions checked {tested}, invariant violations {bad}")
    print("   (this is exactly what `val7_gstep`, `prog7` and `gseq_inv` prove in Lean)")
    print()

if __name__ == "__main__":
    which = sys.argv[1:] or ["1", "2", "3", "4", "5", "6", "7", "8", "9", "10"]
    if "1" in which:
        section1()
    if "2" in which:
        section2()
    if "3" in which:
        section3()
    if "4" in which:
        section4()
        section4b()
    if "5" in which:
        section5()
    if "6" in which:
        section6()
    if "7" in which:
        section7()
    if "8" in which:
        section8()
    if "9" in which:
        section9()
    if "10" in which:
        section10()
