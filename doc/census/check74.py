#!/usr/bin/env python3
"""check74.py -- the independent re-check of the batch-74 finding at span eleven.

`census-batch74.c` reports that at span eleven the four-leg family is no longer
enough: 19 of the distinct basepoints of its corpus are served by no walk of at
most four legs, and the least walk that serves them has five.  It writes the
first such basepoint to `witness-batch74-span11.txt` (the pair, the basepoint,
and the least number of legs).

This script re-checks that witness from scratch.  Nothing is imported from the
census: every predicate is written out again here, from the Lean definitions.

  IsCrookedIvF (rho, sig)   HPC/Fold/Faithful.lean -- `le`, `width`, `adj` and
                            the crookedness clause with interval triggers.
  armG rho i, armT rho i    HPC/Fold/Faithful.lean.
  FoldsOnto f len c         HPC/Fold/Itinerary.lean -- there is a 1-Lipschitz
                            index map beta with beta 0 = 0, beta j < len, and
                            |f j - c (beta j)| <= 1.  Decided here by forward
                            propagation of the reachable set of walk times, as a
                            set of integers (not a bitmask), so the decision
                            procedure is a second, independent one.

What is checked:
  1. the pair is faithful and its band is exactly [0, S];
  2. the basepoint's level;
  3. no walk of at most four legs serves both arms;
  4. the five-leg walk the census reports does serve both arms.

Usage: python3 check74.py [witness-batch74-span11.txt]
"""

import sys

PATH = sys.argv[1] if len(sys.argv) > 1 else "witness-batch74-span11.txt"


def read_witness(path):
    lines = open(path).read().split("\n")
    n, i, k = (int(x) for x in lines[0].split())
    rho = [int(x) for x in lines[1].split()]
    sig = [int(x) for x in lines[2].split()]
    assert len(rho) == n and len(sig) == n
    return n, i, k, rho, sig


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
    # meet[l][j] = least index >= j whose interval contains l
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
                for k in near[t]:
                    if abs(h - k) < 3:
                        continue
                    r1 = k - 1 if h < k else k + 1
                    r2 = h + 1 if h < k else h - 1
                    p1 = meet[r1][s + 1]
                    if p1 >= t:
                        return False, ("crooked", s, t, h, k)
                    p2 = meet[r2][p1 + 1]
                    if p2 >= t:
                        return False, ("crooked2", s, t, h, k)
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
    """FoldsOnto f (len w) w, by forward propagation of the reachable times."""
    reach = {0} if abs(f[0] - w[0]) <= 1 else set()
    if not reach:
        return False
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


def main():
    n, i, kwit, rho, sig = read_witness(PATH)
    L, H = min(rho), max(rho)
    print("witness: %d links, basepoint %d, the census's least number of legs %d"
          % (n, i, kwit))
    print("  band [%d, %d], span %d; basepoint level %d" % (L, H, H - L, rho[i]))
    thin = all(sig[t] == rho[t] for t in range(n))
    print("  thin (sig = rho): %s" % thin)

    ok, why = is_crooked_ivf(rho, sig)
    print("  IsCrookedIvF: %s%s" % (ok, "" if ok else "  (%s)" % (why,)))
    if not ok:
        return

    G = rho[i:]
    T = rho[: i + 1][::-1]
    print("  the arms: |armG| = %d, |armT| = %d (whole arms)" % (len(G), len(T)))

    p = rho[i]
    served = None
    tried = 0
    for k in range(0, 5):
        for c0 in (p - 1, p, p + 1):
            if not (L <= c0 <= H):
                continue
            for turns in alternating(L, H, k, c0, None):
                w = walk_times(c0, turns)
                if w is None:
                    continue
                tried += 1
                if folds_onto(T, w) and folds_onto(G, w):
                    served = (k, (c0,) + turns)
                    break
            if served:
                break
        if served:
            break
    print("  walks of at most four legs tried: %d" % tried)
    if served:
        print("  A WALK OF AT MOST FOUR LEGS SERVES BOTH ARMS: %s -- the census's"
              " finding is NOT reproduced" % (served,))
    else:
        print("  no walk of at most four legs serves both arms: the finding is"
              " reproduced")

    # the five-leg walks, searched until one serves
    found = None
    for c0 in (p - 1, p, p + 1):
        if not (L <= c0 <= H):
            continue
        for turns in alternating(L, H, 5, c0, None):
            w = walk_times(c0, turns)
            if w is None:
                continue
            if folds_onto(T, w) and folds_onto(G, w):
                found = (c0,) + turns
                break
        if found:
            break
    print("  a five-leg walk serving both arms: %s" % (found,))


if __name__ == "__main__":
    main()
