"""check71.py -- the independent re-check of the batch-71 counterexample.

The finding of batch 71 is that the **distance statement is false**: there are
faithful pairs of span nine with a high-run crossing of the trichotomy at the
branch `L + 5` whose nearest time at `L + 2` or below before the basepoint is far
beyond the 67 steps `NearLowT` asks for -- and beyond the 166 and 405 of the two
further readings of `NearLowBandT` as well.  `break-batch71.c` constructs them
from the stored crossings of `census-batch71.c`, and `min-batch71.c` trims the
most extreme one to the shortest window that still breaks the statement
(`witness-batch71-min.txt`).

This script re-checks that window from scratch, with every predicate written out
again independently of the C:

  * IsCrookedIvF (rho, sig) -- the definition of HPC/Fold/Faithful.lean, with the
    crookedness clause searched literally over all pairs of times and all levels
    the neighbouring links carry;
  * rho i = 5, the band [0, 9], and LowAt (arm) 1 8 on both arms;
  * Leg4Land, written out literally from HPC/Fold/Leg4Land.lean, for the three
    walks of the trichotomy: w8 = (K,M,P) = (8,1,5) on the arm, wb = (6,2,4) and
    w3 = (6,1,4) on the reflected arm; the basepoint is a crossing exactly when
    no one of the three serves both arms;
  * the high run -- the failure of DeepFirst2 on the w8 side: an ascent to 9 with
    nothing at 2 or below before it;
  * the three distances of NearLowBandT, on the partner's side of the basepoint,
    against the bounds 67, 166 and 405;
  * Ceil72 and Deep72 on both arms, and the landmark sentence of w72;
  * FoldsOnto, as the reachability program of HPC/Fold/Decide.lean, for the walks
    of the four-leg family -- to see whether the pair still folds.

Usage: python3 check71.py [witness-batch71-min.txt]
"""
import sys


def faithful(rho, sig):
    n = len(rho)
    for t in range(n):
        if not (rho[t] <= sig[t] <= rho[t] + 1):
            return False, "width at %d" % t
    for t in range(n - 1):
        if max(sig[t], sig[t + 1]) > min(rho[t], rho[t + 1]) + 1:
            return False, "adjacency at %d" % t
    # the crookedness clause, searched literally
    def carries(u, lev):
        return 0 <= u < n and rho[u] <= lev <= sig[u]

    def levels_near(t):
        out = set()
        for u in (t - 1, t, t + 1):
            if 0 <= u < n:
                out.update(range(rho[u], sig[u] + 1))
        return out

    # first(lev, j) = least r >= j carrying lev, or n
    maxlev = max(sig) + 2
    first = [[n] * (n + 1) for _ in range(maxlev + 2)]
    for lev in range(maxlev + 2):
        for j in range(n - 1, -1, -1):
            first[lev][j] = j if carries(j, lev) else first[lev][j + 1]
    for s in range(n):
        hs = levels_near(s)
        for t in range(s + 1, n):
            ks = levels_near(t)
            for h in hs:
                for k in ks:
                    if abs(h - k) < 3:
                        continue
                    r1 = k - 1 if h < k else k + 1
                    r2 = h + 1 if h < k else h - 1
                    p1 = first[r1][s + 1]
                    if p1 >= t:
                        return False, "crookedness at (%d,%d,%d,%d)" % (s, t, h, k)
                    p2 = first[r2][p1 + 1]
                    if p2 >= t:
                        return False, "crookedness at (%d,%d,%d,%d)" % (s, t, h, k)
    return True, "faithful"


def low_at(f, tl=1, th=8):
    """LowAt f tl th of HPC/Fold/Leaf.lean, searched literally."""
    m = len(f)
    for d in range(m):
        if f[d] > tl:
            continue
        ok = any(f[j] >= th for j in range(d))
        if not ok:
            ok = any(f[j] <= tl + 1 and f[jp] >= th - 2
                     for j in range(d) for jp in range(j + 1, d))
        if not ok:
            return False
    return True


def leg4land(f, K, M, P, H=9):
    """Leg4Land f H K M P at L = 0, existentials searched literally."""
    m = len(f)
    A = K - P + 1
    if not (P - 2 <= f[0] <= P):
        return False
    for d in range(m):
        if f[d] <= P - 3:
            if not any(j >= A and f[j] >= K - 1 and j + (K - 1 - f[d]) <= d
                       for j in range(m)):
                return False
        if f[d] <= M - 2:
            ok = False
            for j in range(A, m):
                if f[j] < K - 1:
                    continue
                for k in range(j + (K - M), m):
                    if f[k] > M + 1:
                        continue
                    for l in range(k + (H - 1 - M), m):
                        if f[l] >= H - 2 and l + (H - 2 - f[d]) <= d:
                            ok = True
                            break
                    if ok:
                        break
                if ok:
                    break
            if not ok:
                return False
        if f[d] >= K + 2:
            ok = False
            for j in range(A, m):
                if f[j] < K - 1:
                    continue
                for k in range(j + (K - M), m):
                    if f[k] <= M + 1 and k + (f[d] - M - 1) <= d:
                        ok = True
                        break
                if ok:
                    break
            if not ok:
                return False
    return True


def walk_of(levels):
    w = [levels[0]]
    for t in levels[1:]:
        s = 1 if t > w[-1] else -1
        while w[-1] != t:
            w.append(w[-1] + s)
    return w


def folds(f, w):
    """FoldsOnto f (len w) w, by the reachability dynamic program."""
    cur = set()
    if abs(f[0] - w[0]) <= 1:
        cur.add(0)
    for x in f[1:]:
        nxt = set()
        for u in cur:
            for u2 in (u - 1, u, u + 1):
                if 0 <= u2 < len(w) and abs(x - w[u2]) <= 1:
                    nxt.add(u2)
        cur = nxt
        if not cur:
            return False
    return bool(cur)




def ceil72(f):
    """Ceil72 f 0: the third clause of Leg4Land at (9,7,2,5), searched literally."""
    m = len(f)
    for d in range(m):
        if f[d] < 9:
            continue
        ok = False
        for j in range(3, m):
            if f[j] < 6:
                continue
            for k in range(j + 5, m):
                if f[k] <= 3 and k + (f[d] - 3) <= d:
                    ok = True
                    break
            if ok:
                break
        if not ok:
            return False
    return True


def deep72(f):
    """Deep72 f 0: the second clause of the same, searched literally."""
    m = len(f)
    for d in range(m):
        if f[d] > 0:
            continue
        ok = False
        for j in range(3, m):
            if f[j] < 6:
                continue
            for k in range(j + 5, m):
                if f[k] > 3:
                    continue
                for l in range(k + 6, m):
                    if f[l] >= 7 and l + (7 - f[d]) <= d:
                        ok = True
                        break
                if ok:
                    break
            if ok:
                break
        if not ok:
            return False
    return True


def deep_first2(f):
    """DeepFirst2 f 0: before every ascent to 9, a time at 2 or below."""
    for e in range(len(f)):
        if f[e] >= 9 and not any(f[d] <= 2 for d in range(e)):
            return False
    return True


def nearest(f, lev):
    """the least arm index (other than 0) at which the arm is at `lev` or below."""
    for s in range(1, len(f)):
        if f[s] <= lev:
            return s
    return None


def ceil72_witness(f):
    """the landmark pair (j, k) of Ceil72 at the arm's first ascent, k as late as
    possible: a peak at 6 or above at index >= 3 and, five steps later, a time at
    3 or below, six steps before the ascent."""
    m = len(f)
    if 9 not in f:
        return None
    d = f.index(9)
    for k in range(d - (f[d] - 3), -1, -1):
        if k >= m or f[k] > 3:
            continue
        for j in range(k - 5, 2, -1):
            if f[j] >= 6:
                return (j, k, d)
    return None


def reading_naming(rho, sig, target, span=600):
    """the crookedness reading of least span whose greedy witnesses name the link
    `target`: a pair of links (s, t) and levels (h, k) three or more apart, the
    first link after s carrying the level next to k, then the first after that
    carrying the level next to h."""
    n = len(rho)
    maxlev = max(sig) + 2

    def first(lev, j):
        while j < n:
            if rho[j] <= lev <= sig[j]:
                return j
            j += 1
        return n

    best = None
    lo, hi = max(0, target - span), min(n - 1, target + span)
    for s in range(lo, target):
        for t in range(target + 1, hi + 1):
            if best is not None and t - s >= best[0]:
                continue
            for h in range(rho[s], sig[s] + 1):
                for k in range(rho[t], sig[t] + 1):
                    if abs(h - k) < 3:
                        continue
                    r1lev = k - 1 if h < k else k + 1
                    r2lev = h + 1 if h < k else h - 1
                    if not (0 <= r1lev <= maxlev and 0 <= r2lev <= maxlev):
                        continue
                    p1 = first(r1lev, s + 1)
                    if p1 >= t:
                        continue
                    p2 = first(r2lev, p1 + 1)
                    if p2 >= t:
                        continue
                    if p1 == target or p2 == target:
                        role = ("peak" if (h < k) == (p1 == target) else "valley")
                        best = (t - s, s, t, h, k, role)
    return best


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "witness-batch71-min.txt"
    with open(path) as fp:
        head = fp.readline().split()
        n, i, gside = int(head[0]), int(head[1]), int(head[2])
        rho = [int(x) for x in fp.readline().split()]
        sig = [int(x) for x in fp.readline().split()]
    assert len(rho) == n and len(sig) == n
    print("the witness: %d links, basepoint %d, the w8 side is the %s arm"
          % (n, i, "forward" if gside else "backward"))
    print("  levels run from %d to %d" % (min(rho), max(sig)))
    ok, why = faithful(rho, sig)
    print("  IsCrookedIvF: %s (%s)" % (ok, why))
    print("  rho i = %d; the band is [%d, %d]" % (rho[i], min(rho), max(rho)))
    armG = rho[i:]
    armT = rho[i::-1]
    reflG = [9 - x for x in armG]
    reflT = [9 - x for x in armT]
    print("  arm lengths: forward %d, backward %d" % (len(armG), len(armT)))
    print("  LowAt on the forward arm: %s; on the backward arm: %s"
          % (low_at(armG), low_at(armT)))
    tags = {}
    tags["w8"] = (leg4land(armG, 8, 1, 5), leg4land(armT, 8, 1, 5))
    tags["wb"] = (leg4land(reflG, 6, 2, 4), leg4land(reflT, 6, 2, 4))
    tags["w3"] = (leg4land(reflG, 6, 1, 4), leg4land(reflT, 6, 1, 4))
    for name, (a, b) in tags.items():
        print("  %s: forward %s, backward %s" % (name, a, b))
    crossing = not any(a and b for a, b in tags.values())
    print("  a crossing of the trichotomy (no one of the three serves both arms): %s" % crossing)
    run, partner = (armG, armT) if gside else (armT, armG)
    print("  the w8 side is the %s arm; it is deep first at 2: %s (so it runs high: %s)"
          % ("forward" if gside else "backward", deep_first2(run), not deep_first2(run)))
    first9 = run.index(9) if 9 in run else None
    print("  its first ascent to 9 is at arm index %s, and it has nothing at 2 or below"
          " before it: %s" % (first9, first9 is not None
                              and all(x >= 3 for x in run[:first9])))
    d2, d1, d0 = nearest(partner, 2), nearest(partner, 1), nearest(partner, 0)
    print("  THE DISTANCE, on the partner's side of the basepoint:")
    print("    nearest time at 2 or below: %s steps (NearLowT asks for 67)  -> %s"
          % (d2, "HOLDS" if d2 is not None and d2 <= 67 else "FAILS"))
    print("    nearest time at 1 or below: %s steps (the second reading asks for 166) -> %s"
          % (d1, "HOLDS" if d1 is not None and d1 <= 166 else "FAILS"))
    print("    nearest time at the floor:  %s steps (the third reading asks for 405) -> %s"
          % (d0, "HOLDS" if d0 is not None and d0 <= 405 else "FAILS"))
    band = ((d2 is not None and d2 <= 67) or (d1 is not None and d1 <= 166)
            or (d0 is not None and d0 <= 405))
    print("    NearLowBandT (the disjunction of the three readings): %s" % band)
    print("  the conclusion the reading was for: Ceil72 on the running arm: %s;"
          " on the partner: %s" % (ceil72(run), ceil72(partner)))
    print("  Deep72 on the running arm: %s; on the partner: %s" % (deep72(run), deep72(partner)))
    print("  w72 = (7,2,5) on the forward arm: %s; on the backward arm: %s"
          % (leg4land(armG, 7, 2, 5), leg4land(armT, 7, 2, 5)))
    # what places the landmark the ceiling clause needs, now that no low time is near
    wit = ceil72_witness(run)
    if wit is not None:
        j, k, d = wit
        print("  the Ceil72 landmarks on the running arm: peak at arm index %d (level %d),"
              " valley at %d (level %d), ascent at %d"
              % (j, run[j], k, run[k], d))
        tk = i - k if not gside else i + k
        tj = i - j if not gside else i + j
        rd = reading_naming(rho, sig, tk)
        if rd is None:
            print("    no crookedness reading within 600 links names the valley")
        else:
            print("    the valley is the %s of the reading from level %d at %+d to level %d at %+d"
                  " (span %d)" % (rd[5], rd[3], rd[1] - i, rd[4], rd[2] - i, rd[0]))
        rd = reading_naming(rho, sig, tj)
        if rd is None:
            print("    no crookedness reading within 600 links names the peak")
        else:
            print("    the peak is the %s of the reading from level %d at %+d to level %d at %+d"
                  " (span %d)" % (rd[5], rd[3], rd[1] - i, rd[4], rd[2] - i, rd[0]))

    served = []
    for P in range(2, 7):
        for K in range(P, 9):
            for M in range(1, P - 1):
                if M + 3 > K:
                    continue
                for refl in (0, 1):
                    lv = [P - 1, K, M, 8, 1]
                    if refl:
                        lv = [9 - x for x in lv]
                    if any(lv[q] == lv[q + 1] for q in range(len(lv) - 1)):
                        continue
                    w = walk_of(lv)
                    if folds(armG, w) and folds(armT, w):
                        served.append((("reflected" if refl else "direct"), P, K, M, tuple(lv)))
    print("  walks of the four-leg family serving both arms: %d" % len(served))
    for s in served[:6]:
        print("    %s P=%d K=%d M=%d : %s" % s)


if __name__ == "__main__":
    main()
