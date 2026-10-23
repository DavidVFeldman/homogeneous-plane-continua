"""Census for batch 18 — the three conjectures, and `F2Prime`, as they are *stated*.

Exploratory computation in the down form `IsCrookedSeq`.  Not a Lean-checked claim
by itself; the Lean-checked outcome is `HPC/Fold/Closure.lean`, where all four
statements are refuted and their tight forms are posed instead.

The point of this census is the distinction between

  * the **tight** reading, `H = max rho` and `L = min rho`, which is what every
    earlier batch enumerated, and
  * the **slack** reading, any `H >= max rho`, `L <= min rho` with `L + 3 <= H`,
    which is what the Lean statements actually quantify over.

Tight: no failure anywhere in the corpus, for any of the four statements.
Slack: all four fail, and the smallest witnesses found are the ones formalised
in `HPC/Fold/Closure.lean`:

    ExitReach, F2Prime      rho = 0,1,2,1,2,2,3,4        i = 2, H = 4, L = -1
    HighExitValley(Open)    rho = 2,1,0,1,2,1,2,2,3,4    i = 0, H = 4, L = -2
    LowExitPeak             rho = 0,1,2,1,2,2,3,4,3,2    i = 9, H = 6, L = 0

Neither attainment hypothesis can be dropped on its own: with `L` tight and `H`
slack, and with `H` tight and `L` slack, `F2Prime` still fails.

Usage:
    python3 census-batch18.py [maxlen] [levels] [slack]   both readings, by brute force
    python3 census-batch18.py tight [maxlen] [levels]     tight reading only, depth-first

The second mode prunes on crookedness as it extends a prefix — a crookedness
violation inside a prefix can never be repaired — which reaches seven levels and
length 13 in a few minutes.
"""

import sys
from itertools import product


def crooked(f):
    n = len(f)
    for s in range(n):
        for t in range(s + 1, n):
            if abs(f[t] - f[s]) >= 3:
                ok = False
                for r in range(s + 1, t):
                    for r2 in range(r + 1, t):
                        if f[s] < f[t]:
                            c = (f[t] - 2 <= f[r] <= f[t] - 1) and (f[s] <= f[r2] <= f[s] + 1)
                        else:
                            c = (f[t] <= f[r] <= f[t] + 1) and (f[s] - 2 <= f[r2] <= f[s] - 1)
                        if c:
                            ok = True
                            break
                    if ok:
                        break
                if not ok:
                    return False
    return True


def phases(A):
    """phase A j = 1 iff some 0 < t <= j has A t <= A (t-1)."""
    ph = [0] * len(A)
    cur = 0
    for j in range(len(A)):
        if j > 0 and A[j] <= A[j - 1]:
            cur = 1
        ph[j] = cur
    return ph


def hStarArm(A, p):
    best = None
    for j in range(len(A)):
        if all(A[k] >= p - 1 for k in range(j + 1)):
            best = A[j] if best is None else max(best, A[j])
    return best


def lStarArm(A, p):
    return -hStarArm([-a for a in A], -p)


def hReach(A, p):
    ph = phases(A)
    best = None
    for j in range(len(A)):
        if all(A[k] >= p - 1 for k in range(j + 1)):
            v = A[j] + ph[j]
            best = v if best is None else max(best, v)
    return best


def okLam(A, p, h):
    if all(a > p - 2 for a in A):
        return True
    return h <= hReach(A, p)


def okVee(A, p, l):
    return okLam([-a for a in A], -p, -l)


def hStar(rho, i, H, L):
    p = rho[i]
    G, T = rho[i:], rho[i::-1]
    return min(max(max(hStarArm(G, p), hStarArm(T, p)), max(p, L + 1)), max(H - 1, p))


def lStar(rho, i, H, L):
    p = rho[i]
    G, T = rho[i:], rho[i::-1]
    return max(min(min(lStarArm(G, p), lStarArm(T, p)), min(p, H - 1)), min(L + 1, p))


def valleyBefore(A, L, h, s):
    for u in range(s, len(A)):
        if A[u] > h + 1 and not any(A[j] <= L + 1 for j in range(s, u)):
            return False
    return True


def peakBefore(A, H, l, s):
    """`ValleyBefore` for the negated arm, read on the arm itself."""
    for u in range(s, len(A)):
        if A[u] < l - 1 and not any(A[j] >= H - 1 for j in range(s, u)):
            return False
    return True


def admissible_s_lam(A, h):
    ph = phases(A)
    return [s for s in range(len(A) + 1) if all(A[j] + ph[j] < h for j in range(s))]


def admissible_s_vee(A, l):
    nA = [-a for a in A]
    ph = phases(nA)
    return [s for s in range(len(A) + 1) if all(nA[j] + ph[j] < -l for j in range(s))]


def segLam(f, p, H, L, h):
    m = len(f)
    ph = phases(f)
    for s in range(m + 1):
        if not all(p - 1 <= f[j] <= h + 1 for j in range(s)):
            continue
        if s < m and not h <= f[s] + ph[s]:
            continue
        if not all(f[j] + ph[j] < h for j in range(s)):
            continue
        for t in range(s, m + 1):
            if not all(L <= f[j] <= h + 1 for j in range(s, t)):
                continue
            if t == m or (s < t and f[t - 1] <= L + 1):
                return True
    return False


def segVee(f, p, H, L, l):
    return segLam([-x for x in f], -p, -L, -H, -l)


def check(rho, i, H, L):
    """The statements that FAIL at this instance."""
    p = rho[i]
    G, T = list(rho[i:]), list(rho[i::-1])
    h, l = hStar(rho, i, H, L), lStar(rho, i, H, L)
    bad = []
    if not ((okLam(G, p, h) and okLam(T, p, h)) or (okVee(G, p, l) and okVee(T, p, l))):
        bad.append("ExitReach")
    openq = h < max(H - 1, p)
    for A in (G, T):
        if any(not valleyBefore(A, L, h, s) for s in admissible_s_lam(A, h)):
            bad.append("HighExitValley")
            if openq:
                bad.append("HighExitValleyOpen")
            break
    for A in (G, T):
        if any(not peakBefore(A, H, l, s) for s in admissible_s_vee(A, l)):
            bad.append("LowExitPeak")
            break
    if not ((segLam(G, p, H, L, h) and segLam(T, p, H, L, h)) or
            (segVee(G, p, H, L, l) and segVee(T, p, H, L, l))):
        bad.append("F2Prime")
    return bad


def sequences(maxlen, levels):
    for n in range(1, maxlen + 1):
        for start in range(levels):
            for steps in product((-1, 0, 1), repeat=n - 1):
                f = [start]
                ok = True
                for d in steps:
                    v = f[-1] + d
                    if not 0 <= v < levels:
                        ok = False
                        break
                    f.append(v)
                if ok and min(f) == 0:
                    yield f


NAMES = ("ExitReach", "HighExitValley", "HighExitValleyOpen", "LowExitPeak", "F2Prime")


def crooked_last(f):
    """Crookedness of the pairs `(s, t)` whose second index is the last one."""
    t = len(f) - 1
    for s in range(t):
        if abs(f[t] - f[s]) >= 3:
            found = False
            for r in range(s + 1, t):
                for r2 in range(r + 1, t):
                    if f[s] < f[t]:
                        c = (f[t] - 2 <= f[r] <= f[t] - 1) and (f[s] <= f[r2] <= f[s] + 1)
                    else:
                        c = (f[t] <= f[r] <= f[t] + 1) and (f[s] - 2 <= f[r2] <= f[s] - 1)
                    if c:
                        found = True
                        break
                if found:
                    break
            if not found:
                return False
    return True


def tight_census(maxlen, levels):
    """Depth-first over crooked prefixes; every sequence read at tight extremes."""
    state = {"seqs": 0, "basepoints": 0, "instances": 0, "bad": {}}

    def visit(f):
        state["seqs"] += 1
        state["basepoints"] += len(f)
        H, L = max(f), min(f)
        if L + 3 > H:
            return
        for i in range(len(f)):
            state["instances"] += 1
            for name in check(f, i, H, L):
                state["bad"].setdefault(name, (list(f), i, H, L))

    def dfs(f):
        visit(f)
        if len(f) == maxlen:
            return
        for d in (-1, 0, 1):
            f.append(f[-1] + d)
            if 0 <= f[-1] < levels and crooked_last(f):
                dfs(f)
            f.pop()

    for start in range(levels):
        dfs([start])
    print(f"tight census: {levels} levels, length <= {maxlen}")
    print(f"  crooked sequences: {state['seqs']}, basepoints: {state['basepoints']},"
          f" instances with L + 3 <= H: {state['instances']}")
    for name in NAMES:
        if name in state["bad"]:
            f, i, H, L = state["bad"][name]
            print(f"  {name}: FAILS at rho={f}, i={i}, H={H}, L={L}")
        else:
            print(f"  {name}: no failure")


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "tight":
        maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 12
        levels = int(sys.argv[3]) if len(sys.argv) > 3 else 6
        tight_census(maxlen, levels)
        return
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    levels = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    slack = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    seqs = basepoints = tight = slackn = 0
    tight_bad = {}
    slack_bad = {}
    for f in sequences(maxlen, levels):
        if not crooked(f):
            continue
        seqs += 1
        mx, mn = max(f), min(f)
        for i in range(len(f)):
            basepoints += 1
            for H in range(mx, mx + slack + 1):
                for L in range(mn - slack, mn + 1):
                    if L + 3 > H:
                        continue
                    isTight = (H == mx and L == mn)
                    if isTight:
                        tight += 1
                    else:
                        slackn += 1
                    for name in check(f, i, H, L):
                        tgt = tight_bad if isTight else slack_bad
                        key = (len(f), (H - mx) + (mn - L))
                        if name not in tgt or key < tgt[name][0]:
                            tgt[name] = (key, (list(f), i, H, L))
    print(f"crooked sequences: {seqs}, basepoints: {basepoints}")
    print(f"tight instances: {tight}, slack instances: {slackn}")
    print("tight reading (H = max rho, L = min rho):")
    for name in NAMES:
        if name in tight_bad:
            (_, (f, i, H, L)) = tight_bad[name]
            print(f"  {name}: FAILS at rho={f}, i={i}, H={H}, L={L}")
        else:
            print(f"  {name}: no failure")
    print("slack reading (smallest witness found: shortest, then least slack):")
    for name in NAMES:
        if name in slack_bad:
            (_, (f, i, H, L)) = slack_bad[name]
            print(f"  {name}: FAILS at rho={f}, i={i}, H={H}, L={L}")
        else:
            print(f"  {name}: no failure")


if __name__ == "__main__":
    main()
