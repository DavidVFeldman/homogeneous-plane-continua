"""Census for batch 37 -- span six.

Conventions.  An arm is a 1-Lipschitz integer sequence with values in [L, H], based at its
first entry.  A walk is a 1-Lipschitz sequence of centres; an arm f folds onto a walk c iff
there is a 1-Lipschitz time assignment beta with beta 0 = 0 and |f j - c (beta j)| <= 1 for
every j, which is decided exactly by reachability over the walk's times (a bitmask sweep).
Throughout L = 0, H = 6, and the basepoint level is p = 3, the only interior level at span six.

    LowLate f   : for every d with f d = L, either f reaches H-1 before d,
                  or f reaches L+1 and afterwards H-2, both before d.
    HighLate f  : the reflection of LowLate (the two extremes exchanged).
    walk6       = [2, 3, 4, 5, 4, 3, 2, 1]        (peak H-1, base L+2, end L+1)
    walk6'      = [4, 3, 2, 1, 2, 3, 4, 5]        (its reflection)

Sections.

  1  The dichotomy, on the corpus of stretches of Bing's chains:  at every interior basepoint
     of every stretch of `bing 0 d`, d = 6, 7, 8, whose band is exactly six wide, either both
     arms are LowLate or both arms are HighLate.  (This is what `span6_dichotomy` proves from
     the crookedness clause; the census is the independent check.)

  2  The explicit fold, exhaustively:  for every 1-Lipschitz LowLate arm of length at most 14,
     the assignment that `foldsOnto_walk6_of_lowLate` constructs is a fold onto walk6.

  3  The same statement for arms of *every* length, exactly, by reachability over the product
     of (level, DP mask, predicate state):  no LowLate arm of any length fails walk6.

  4  The route that is closed.  The crookedness clause yields witnesses at levels >= H-2 and
     <= L+1 only, so the weaker conditions "reaches H-2 before L" and "reaches L+2 before H"
     are what a one-shot argument gives if one insists on the weaker threshold.  No walk of
     length at most 10 serves all arms satisfying them -- not even after imposing local
     crookedness in every window of size up to six.  This is why the span-six proof uses the
     two-clause LowLate and not the one-clause form.

  5  Two negative facts about the family of walks at span six:  no single walk of length at
     most 12 serves every interior basepoint of the corpus (so the walk cannot depend on the
     band alone), and neither arm folds, in general, onto the other arm's own trace.

Usage: python3 census-batch37.py
"""

import itertools
import sys
from collections import Counter, deque

L, H, P = 0, 6, 3
WALK6 = [2, 3, 4, 5, 4, 3, 2, 1]
WALK6M = [4, 3, 2, 1, 2, 3, 4, 5]


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


# ---------------------------------------------------------------- predicates

def low_late(f):
    for d, x in enumerate(f):
        if x != L:
            continue
        if any(f[j] >= H - 1 for j in range(d)):
            continue
        if any(f[j] <= L + 1 and any(f[k] >= H - 2 for k in range(j + 1, d))
               for j in range(d)):
            continue
        return False
    return True


def high_late(f):
    return low_late([2 * L + H - x for x in f])


# ---------------------------------------------------------------- section 1

def section1():
    print("== 1. the dichotomy on stretches of Bing's chains ==")
    tot = Counter()
    for d in (6, 7, 8):
        rho = bpath(0, d)
        cnt = Counter()
        for (a, b) in stretches(rho, 6):
            seg = rho[a:b + 1]
            lo = min(seg)
            seg = [x - lo for x in seg]
            for i, x in enumerate(seg):
                if x != P:
                    continue
                g = seg[i:]
                t = seg[:i + 1][::-1]
                lowpair = low_late(g) and low_late(t)
                highpair = high_late(g) and high_late(t)
                cnt["instances"] += 1
                cnt["low"] += lowpair
                cnt["high"] += highpair
                cnt["both"] += lowpair and highpair
                if not (lowpair or highpair):
                    cnt["FAIL"] += 1
                    print("   FAILING INSTANCE", seg, i)
        print(f"   bing 0 {d} ({len(rho)} links): " +
              ", ".join(f"{k} {v}" for k, v in sorted(cnt.items())))
        tot.update(cnt)
    print("   total: " + ", ".join(f"{k} {v}" for k, v in sorted(tot.items())))
    print(f"   dichotomy failures: {tot['FAIL']}")
    print()


# ---------------------------------------------------------------- section 2

def phase(f):
    out = []
    c = 0
    for j in range(len(f)):
        if j > 0 and f[j] <= f[j - 1]:
            c += 1
        out.append(min(2, c))
    return out


def construct(f):
    """the assignment of `foldsOnto_walk6_of_lowLate`"""
    ph = phase(f)
    a = [min(3, max(0, f[j] + ph[j] - (L + 3))) for j in range(len(f))]
    b = [3 + max(L + 4 - f[j], 0) for j in range(len(f))]
    s = None
    for j in range(1, len(f)):
        if f[j] >= L + 4 and a[j - 1] >= 2:
            s = j
            break
    if s is None:
        return a
    return [a[j] if j < s else b[j] for j in range(len(f))]


def check_beta(f, beta):
    if beta[0] != 0:
        return "beta 0"
    for j in range(len(f)):
        if not (0 <= beta[j] < len(WALK6)):
            return f"range at {j}"
        if abs(f[j] - WALK6[beta[j]]) > 1:
            return f"window at {j}"
        if j and abs(beta[j] - beta[j - 1]) > 1:
            return f"Lipschitz at {j}"
    return None


def section2(maxlen=14):
    print("== 2. the explicit assignment, all LowLate arms of length <= %d ==" % maxlen)
    tested = bad = 0
    for ln in range(1, maxlen + 1):
        for steps in itertools.product((-1, 0, 1), repeat=ln - 1):
            f = [P]
            ok = True
            for s in steps:
                f.append(f[-1] + s)
                if not (L <= f[-1] <= H):
                    ok = False
                    break
            if not ok:
                continue
            if not low_late(f):
                continue
            tested += 1
            err = check_beta(f, construct(f))
            if err:
                bad += 1
                if bad < 5:
                    print("   FAIL", err, f)
    print(f"   arms tested {tested}, failures {bad}")
    print()


# ---------------------------------------------------------------- sections 3,4

def serves_all(w, pred, window=None):
    """exact over arms of every length: does every arm satisfying `pred` fold onto `w`?

    `pred` is a transition on a finite state (None = the arm may be ignored);
    `window` imposes local crookedness on every window of that size."""
    lw = len(w)
    allowed = [0] * (H + 1)
    for x in range(H + 1):
        m = 0
        for u in range(lw):
            if abs(w[u] - x) <= 1:
                m |= 1 << u
        allowed[x] = m
    full = (1 << lw) - 1
    m0 = 1 & allowed[P]
    if m0 == 0:
        return False
    start = (m0, pred(0, P), (P,))
    seen = {start}
    dq = deque([start])
    while dq:
        m, s, hist = dq.popleft()
        x = hist[-1]
        for y in (x - 1, x, x + 1):
            if not (0 <= y <= H):
                continue
            h2 = (hist + (y,))[-window:] if window else (y,)
            if window and not loc_crooked(h2):
                continue
            s2 = pred(s, y)
            if s2 is None:
                continue
            m2 = (m | (m << 1) | (m >> 1)) & allowed[y] & full
            if m2 == 0:
                return False
            st = (m2, s2, h2)
            if st not in seen:
                seen.add(st)
                dq.append(st)
    return True


def loc_crooked(win):
    """a necessary condition on every window of a faithful crooked sequence"""
    k = len(win)
    for s in range(k):
        for t in range(s + 1, k):
            h, kk = win[s], win[t]
            if h >= kk + 3:
                if not any(win[r] <= kk + 1 and any(win[r2] >= h - 2 for r2 in range(r + 1, t))
                           for r in range(s + 1, t)):
                    return False
            if kk >= h + 3:
                if not any(win[r] >= kk - 1 and any(win[r2] <= h + 2 for r2 in range(r + 1, t))
                           for r in range(s + 1, t)):
                    return False
    return True


def pred_lowlate(s, y):
    """states: 0 nothing, 1 has been at <= L+1, 2 satisfied, None = not LowLate"""
    if s == 2:
        return 2
    if y >= H - 1:
        return 2
    if s == 1 and y >= H - 2:
        return 2
    if y == L:
        return None
    if y <= L + 1:
        return 1
    return s


def pred_highlate(s, y):
    if s == 2:
        return 2
    if y <= L + 1:
        return 2
    if s == 1 and y <= L + 2:
        return 2
    if y == H:
        return None
    if y >= H - 1:
        return 1
    return s


def pred_weak_low(s, y):
    """the one-clause form: reaches H-2 before L"""
    if s == 1:
        return 1
    if y >= H - 2:
        return 1
    if y == L:
        return None
    return 0


def pred_weak_high(s, y):
    if s == 1:
        return 1
    if y <= L + 2:
        return 1
    if y == H:
        return None
    return 0


def walks(maxlen, starts=(P - 1, P, P + 1)):
    for c0 in starts:
        for ln in range(1, maxlen + 1):
            for steps in itertools.product((-1, 1), repeat=ln - 1):
                w = [c0]
                ok = True
                for s in steps:
                    w.append(w[-1] + s)
                    if not (L <= w[-1] <= H):
                        ok = False
                        break
                if ok:
                    yield w


def section3():
    print("== 3. LowLate implies folding onto walk6, for arms of every length ==")
    print("   walk6  serves every LowLate  arm:", serves_all(WALK6, pred_lowlate))
    print("   walk6' serves every HighLate arm:", serves_all(WALK6M, pred_highlate))
    good = [w for w in walks(11) if serves_all(w, pred_lowlate)]
    print(f"   walks of length <= 11 serving every LowLate arm: {len(good)}")
    print(f"   shortest of them: {good[0] if good else None}")
    print()


def section4(maxlen=10):
    print("== 4. the one-clause form has no walk, even with local crookedness ==")
    for window in (None, 3, 4, 5, 6):
        for name, pred in (("reaches H-2 before L", pred_weak_low),
                           ("reaches L+2 before H", pred_weak_high)):
            good = [w for w in walks(maxlen) if serves_all(w, pred, window)]
            tag = "no window" if window is None else f"window {window}"
            print(f"   {tag}, {name}: {len(good)} serving walks of length <= {maxlen}")
    print()


# ---------------------------------------------------------------- section 5

def section5(maxlen=12):
    print("== 5. the walk cannot depend on the band alone; arms do not serve each other ==")
    pairs = set()
    for d in (6, 7):
        rho = bpath(0, d)
        for (a, b) in stretches(rho, 6):
            seg = rho[a:b + 1]
            lo = min(seg)
            seg = [x - lo for x in seg]
            for i, x in enumerate(seg):
                if x == P:
                    pairs.add((tuple(seg[i:]), tuple(seg[:i + 1][::-1])))
    pairs = sorted(pairs)
    print(f"   corpus: {len(pairs)} distinct arm pairs at level {P}, band [{L}, {H}]")
    universal = 0
    for w in walks(maxlen):
        ok = True
        for (g, t) in pairs:
            if not (folds(list(g), w) and folds(list(t), w)):
                ok = False
                break
        if ok:
            universal += 1
            print(f"   universal walk found: {w}")
    print(f"   walks of length <= {maxlen} serving every instance: {universal}")
    cw = sum(1 for (g, t) in pairs if folds(list(g), WALK6) and folds(list(t), WALK6))
    cm = sum(1 for (g, t) in pairs if folds(list(g), WALK6M) and folds(list(t), WALK6M))
    print(f"   walk6 alone serves {cw} of {len(pairs)}; walk6' alone serves {cm}")
    cov = sum(1 for (g, t) in pairs
              if (folds(list(g), WALK6) and folds(list(t), WALK6)) or
                 (folds(list(g), WALK6M) and folds(list(t), WALK6M)))
    print(f"   the pair (walk6, walk6') serves {cov} of {len(pairs)}")
    # arm traces
    bad = 0
    for (g, t) in pairs:
        if not (folds(list(t), list(g)) or folds(list(g), list(t))):
            bad += 1
    print(f"   instances where neither arm folds onto the other arm's trace: {bad}")
    print()


if __name__ == "__main__":
    which = sys.argv[1:] or ["1", "2", "3", "4", "5"]
    if "1" in which:
        section1()
    if "2" in which:
        section2()
    if "3" in which:
        section3()
    if "4" in which:
        section4()
    if "5" in which:
        section5()
