#!/usr/bin/env python3
"""check75.py -- the independent re-check of the batch-75 witnesses.

`census-batch75.c` writes out, at each span it sweeps, the first distinct
basepoint it meets whose least leg count is four, five, ... , as
`witness-batch75-span<S>-k<k>.txt`: the pair (rho and sigma), the basepoint
index, the least number of legs the census claims, and the walk it found.

This script re-checks such a witness from scratch.  Nothing is taken from the
census: every predicate is written out again here, from its Lean definition, and
the fold is decided by a different procedure (forward propagation of the
reachable set of walk times as a Python set of integers, against the census's
128-bit mask).

  IsCrookedIvF (rho, sig)   HPC/Fold/Faithful.lean -- `le`, `width`, `adj` and
                            the crookedness clause with interval triggers.
  armG rho i, armT rho i    HPC/Fold/Faithful.lean.
  FoldsOnto f len c         HPC/Fold/Itinerary.lean.

What is checked:
  1. the pair is faithful (IsCrookedIvF) and its band is exactly [0, S];
  2. the basepoint's level, the whole arms and their lengths, thin or not;
  3. no walk of fewer than k legs, based within one of the level, folds both
     whole arms;
  4. some walk of k legs does (the census's walk is checked first);
  5. section 2.1 for this basepoint: whether some least walk is obtained, by
     appending legs at the ends, from a walk that serves the same basepoint read
     in a sub-band -- the pair restricted to a band [L', H'] of smaller span
     containing the basepoint's level, which is the maximal stretch of indices
     around the basepoint whose levels stay inside [L', H'].  The sub-band taken
     is the minimal one containing the sub-walk's levels and the basepoint's
     level; the truncated arms are printed, so that a success on a two-link arm
     is visible as such.

Usage: python3 check75.py witness-batch75-span11-k5.txt [...]
"""

import sys


def read_witness(path):
    lines = [l for l in open(path).read().split("\n")]
    n, i, k = (int(x) for x in lines[0].split())
    rho = [int(x) for x in lines[1].split()]
    sig = [int(x) for x in lines[2].split()]
    walk = None
    for l in lines[3:]:
        if l.startswith("walk "):
            walk = [int(x) for x in l[5:].replace("->", " ").split()]
    assert len(rho) == n and len(sig) == n
    return n, i, k, rho, sig, walk


# ------------------------------------------------------- IsCrookedIvF, again

def is_crooked_ivf(rho, sig):
    n = len(rho)
    for t in range(n):
        if not (rho[t] <= sig[t] <= rho[t] + 1):
            return False, ("width", t)
    for t in range(n - 1):
        if max(sig[t], sig[t + 1]) > min(rho[t], rho[t + 1]) + 1:
            return False, ("adj", t)
    lo, hi = min(rho), max(sig)
    meet = {}
    for l in range(lo - 1, hi + 2):
        col = [n] * (n + 1)
        for j in range(n - 1, -1, -1):
            col[j] = j if rho[j] <= l <= sig[j] else col[j + 1]
        meet[l] = col

    def levels_near(s):
        out = set()
        for u in (s - 1, s, s + 1):
            if 0 <= u < n:
                out.update(range(rho[u], sig[u] + 1))
        return out

    near = [levels_near(s) for s in range(n)]
    for s in range(n):
        for t in range(s + 1, n):
            for h in near[s]:
                for kk in near[t]:
                    if abs(h - kk) < 3:
                        continue
                    r1 = kk - 1 if h < kk else kk + 1
                    r2 = h + 1 if h < kk else h - 1
                    p1 = meet[r1][s + 1]
                    if p1 >= t:
                        return False, ("crooked", s, t, h, kk)
                    p2 = meet[r2][p1 + 1]
                    if p2 >= t:
                        return False, ("crooked2", s, t, h, kk)
    return True, None



def is_crooked_ivf_fast(rho, sig):
    """The same predicate, decided in linear time, as a second implementation.

    For fixed s, h and k the greedy witnesses p1 (the first index after s whose
    interval contains k-1, resp. k+1) and p2 (the first index after p1 whose
    interval contains h+1, resp. h-1) do not depend on t, and the clause at
    (s, t, h, k) holds exactly when p2 < t.  So the clause fails for some t
    precisely when the first index t > s at which k is a level near t satisfies
    t <= p2.  That is what is tested here, level by level, so no pair (s, t) is
    enumerated.  On every witness short enough for both, this is checked against
    the quadratic decision above.
    """
    n = len(rho)
    for t in range(n):
        if not (rho[t] <= sig[t] <= rho[t] + 1):
            return False, ("width", t)
    for t in range(n - 1):
        if max(sig[t], sig[t + 1]) > min(rho[t], rho[t + 1]) + 1:
            return False, ("adj", t)
    lo, hi = min(rho), max(sig)
    levels = list(range(lo - 1, hi + 2))
    meet = {}
    for l in levels:
        col = [n] * (n + 1)
        for j in range(n - 1, -1, -1):
            col[j] = j if rho[j] <= l <= sig[j] else col[j + 1]
        meet[l] = col
    nearnext = {}
    for l in levels:
        col = [n] * (n + 2)
        for j in range(n - 1, -1, -1):
            here = any(0 <= u < n and rho[u] <= l <= sig[u] for u in (j - 1, j, j + 1))
            col[j] = j if here else col[j + 1]
        nearnext[l] = col

    def levels_near(s):
        out = set()
        for u in (s - 1, s, s + 1):
            if 0 <= u < n:
                out.update(range(rho[u], sig[u] + 1))
        return out

    for s in range(n):
        for h in levels_near(s):
            for k in levels:
                if abs(h - k) < 3:
                    continue
                r1 = k - 1 if h < k else k + 1
                r2 = h + 1 if h < k else h - 1
                p1 = meet[r1][s + 1]
                p2 = meet[r2][p1 + 1] if p1 < n else n
                t = nearnext[k][s + 1]
                if t < n and t <= p2:
                    return False, ("crooked", s, t, h, k)
    return True, None


# ---------------------------------------------------------------- the folds

def walk_times(start, targets):
    w = [start]
    cur = start
    for t in targets:
        if t == cur:
            return None
        step = 1 if t > cur else -1
        while cur != t:
            cur += step
            w.append(cur)
    return w


def folds_onto(f, w):
    """FoldsOnto f (len w) w, by propagation of the reachable times as a set."""
    if abs(f[0] - w[0]) > 1:
        return False
    reach = {0}
    for v in f[1:]:
        nxt = set()
        for u in reach:
            for u2 in (u - 1, u, u + 1):
                if 0 <= u2 < len(w) and abs(v - w[u2]) <= 1:
                    nxt.add(u2)
        if not nxt:
            return False
        reach = nxt
    return True


def alternating(L, H, k, last, up):
    if k == 0:
        yield ()
        return
    dirs = (True, False) if up is None else (up,)
    for d in dirs:
        rng = range(last + 1, H) if d else range(L + 1, last)
        for t in rng:
            for rest in alternating(L, H, k - 1, t, not d):
                yield (t,) + rest


def all_walks(L, H, p, k):
    for c0 in (p - 1, p, p + 1):
        if not (L <= c0 <= H):
            continue
        for turns in alternating(L, H, k, c0, None):
            w = walk_times(c0, turns)
            if w is not None:
                yield (c0, turns, w)


def restrict(arm, lo, hi):
    u = 0
    while u < len(arm) and lo <= arm[u] <= hi:
        u += 1
    return arm[:u]


def check(path):
    n, i, kwit, rho, sig, cwalk = read_witness(path)
    L, H = min(rho), max(rho)
    p = rho[i]
    print("=" * 78)
    print("%s: %d links, basepoint %d, the census's least leg count %d, its walk %s"
          % (path, n, i, kwit, cwalk))
    print("  band [%d, %d], span %d; basepoint level %d; thin (sig = rho): %s"
          % (L, H, H - L, p, all(sig[t] == rho[t] for t in range(n))))

    okf, whyf = is_crooked_ivf_fast(rho, sig)
    print("  IsCrookedIvF (linear decision): %s%s"
          % (okf, "" if okf else "  (%s)" % (whyf,)))
    if n <= 6000:
        ok, why = is_crooked_ivf(rho, sig)
        print("  IsCrookedIvF (quadratic decision, over all index pairs): %s%s;"
              " the two agree: %s"
              % (ok, "" if ok else "  (%s)" % (why,), ok == okf))
    else:
        ok = okf
        print("  (the quadratic decision over all index pairs is not run at this length)")
    if not ok:
        return

    G = rho[i:]
    T = rho[: i + 1][::-1]
    print("  the whole arms: |armG| = %d, |armT| = %d" % (len(G), len(T)))

    # 3. no walk of fewer than kwit legs
    tried = 0
    served = None
    for k in range(0, kwit):
        for c0, turns, w in all_walks(L, H, p, k):
            tried += 1
            if folds_onto(T, w) and folds_onto(G, w):
                served = (k, (c0,) + turns)
                break
        if served:
            break
    print("  walks of fewer than %d legs tried: %d" % (kwit, tried))
    if served:
        print("  A WALK OF %d LEGS SERVES BOTH ARMS: %s -- the census's least leg"
              " count is NOT reproduced" % (served[0], served[1]))
        return
    print("  none of them serves both arms: the least leg count %d is reproduced" % kwit)

    # 4. the census's walk, and the least walks
    if cwalk is not None:
        w = walk_times(cwalk[0], cwalk[1:])
        print("  the census's walk %s folds both arms: %s"
              % (cwalk, w is not None and folds_onto(G, w) and folds_onto(T, w)))
    least = []
    for c0, turns, w in all_walks(L, H, p, kwit):
        if folds_onto(T, w) and folds_onto(G, w):
            least.append((c0, turns, w))
            if len(least) >= 16:
                break
    print("  least walks of %d legs found (up to 16): %s"
          % (kwit, [(c0,) + t for c0, t, _ in least]))

    # 5. section 2.1: a sub-band ancestor
    best = None
    for c0, turns, _ in least:
        for j1 in range(kwit):
            for j2 in range(j1 + 1, kwit + 1):
                if j2 - j1 >= kwit:
                    continue
                st = c0 if j1 == 0 else turns[j1 - 1]
                if abs(st - p) > 1:
                    continue
                sub = walk_times(st, turns[j1:j2])
                if sub is None:
                    continue
                lo, hi = min(min(sub), p), max(max(sub), p)
                if hi - lo >= H - L:
                    continue
                Gr, Tr = restrict(G, lo, hi), restrict(T, lo, hi)
                if not Gr or not Tr:
                    continue
                if folds_onto(Gr, sub) and folds_onto(Tr, sub):
                    cand = (hi - lo, min(len(Gr), len(Tr)), (st,) + turns[j1:j2],
                            (c0,) + turns, j1, kwit - j2, len(Gr), len(Tr))
                    if best is None or cand[:2] > best[:2]:
                        best = cand
    if best is None:
        print("  S2.1: NO sub-band ancestor: no least walk is an extension of a walk"
              " serving this basepoint in a smaller band")
    else:
        span, _, sub, full, pre, post, lg, lt = best
        print("  S2.1: the least walk %s extends the walk %s, which serves this basepoint"
              % (full, sub))
        print("        read in the sub-band of span %d (%d levels dropped); truncated arms"
              " %d and %d links; %d legs prepended, %d appended"
              % (span, (H - L) - span, lg, lt, pre, post))


def main():
    paths = sys.argv[1:]
    if not paths:
        print(__doc__)
        return
    for path in paths:
        check(path)


if __name__ == "__main__":
    main()
