"""Census for batch 19 — the three *tight* conjectures.

Exploratory computation in the down form `IsCrookedSeq`, always at the tight
reading `H = max rho`, `L = min rho` (both extremes attained, as the tight
statements require).  Not a Lean-checked claim by itself.

Three searches:

    python3 census-batch19.py tight  [maxlen] [levels]
        exhaustive depth-first over crooked prefixes, pruning on crookedness.

    python3 census-batch19.py random [samples] [len] [levels] [seed]
        randomised depth-first dives to a target length, many levels.

    python3 census-batch19.py witness
        the three witnesses formalised in HPC/Fold/ClosureTight.lean, rechecked.

    python3 census-batch19.py claim  [maxlen] [levels]
        the sub-claim of COMMISSION.md §3: in the open non-vacuous case, is `L`
        attained on the exceeding arm strictly before its exceeding index?

The checkers are those of `census-batch18.py`, restricted to the tight reading.
"""

import random
import sys

# --- basic predicates (shared with census-batch18.py) -----------------------


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


def phases(A):
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


NAMES = ("ExitReachTight", "HighExitValleyTight", "HighExitValleyOpenTight",
         "LowExitPeakTight", "F2PrimeTight", "F2PrimeFree")


def f2PrimeFree(rho, i, H, L):
    """Is there *any* one-bump fold at this basepoint?

    The free form: the bounds and the height (depth) are all quantified, over exactly
    the hypotheses of `exists_blocks_first_of_segLam` / `..._segVee`.  `SegLam` does not
    mention `H` and `SegVee` does not mention `L`, and the clauses are monotone in the
    remaining bound, so `L = min rho` is optimal on the L side and `H = max rho` on the
    V side; only the height and the depth have to be scanned, and outside the range
    below nothing changes.
    """
    p = rho[i]
    mx, mn = max(rho), min(rho)
    G, T = list(rho[i:]), list(rho[i::-1])
    for hb in range(p, mx + 3):
        if segLam(G, p, H, mn, hb) and segLam(T, p, H, mn, hb):
            return True
    for lb in range(mn - 2, p + 1):
        if lb + 1 <= mx and segVee(G, p, mx, L, lb) and segVee(T, p, mx, L, lb):
            return True
    return False


def check(rho, i, H, L):
    """The tight statements that FAIL at this instance."""
    p = rho[i]
    G, T = list(rho[i:]), list(rho[i::-1])
    h, l = hStar(rho, i, H, L), lStar(rho, i, H, L)
    bad = []
    if not ((okLam(G, p, h) and okLam(T, p, h)) or (okVee(G, p, l) and okVee(T, p, l))):
        bad.append("ExitReachTight")
    openq = h < max(H - 1, p)
    for A in (G, T):
        if any(not valleyBefore(A, L, h, s) for s in admissible_s_lam(A, h)):
            bad.append("HighExitValleyTight")
            if openq:
                bad.append("HighExitValleyOpenTight")
            break
    for A in (G, T):
        if any(not peakBefore(A, H, l, s) for s in admissible_s_vee(A, l)):
            bad.append("LowExitPeakTight")
            break
    if not ((segLam(G, p, H, L, h) and segLam(T, p, H, L, h)) or
            (segVee(G, p, H, L, l) and segVee(T, p, H, L, l))):
        bad.append("F2PrimeTight")
    if not f2PrimeFree(rho, i, H, L):
        bad.append("F2PrimeFree")
    return bad


# --- the sub-claim of COMMISSION.md §3 --------------------------------------

def claim_instances(rho, i):
    """Yield ('ok'|'FAIL', data) for each exceeding configuration on each arm.

    Configuration: an arm `A`, an admissible `s`, and `u >= s` with `A u > h+1`.
    The sub-claim: `min rho` is attained on `A` at some index `< u`.
    """
    H, L = max(rho), min(rho)
    if L + 3 > H:
        return
    p = rho[i]
    h = hStar(rho, i, H, L)
    if not h < max(H - 1, p):       # only the open case
        return
    for tag, A in (("G", list(rho[i:])), ("T", list(rho[i::-1]))):
        for s in admissible_s_lam(A, h):
            for u in range(s, len(A)):
                if A[u] > h + 1:
                    att = any(A[j] == L for j in range(u))
                    yield ("ok" if att else "FAIL"), (tag, s, u, h, H, L)


# --- drivers ----------------------------------------------------------------

def tight_census(maxlen, levels):
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
    report(state["bad"])


def report(bad):
    for name in NAMES:
        if name in bad:
            f, i, H, L = bad[name]
            print(f"  {name}: FAILS at rho={f}, i={i}, H={H}, L={L}")
        else:
            print(f"  {name}: no failure")


def random_dive(target, levels, rng):
    """One randomised depth-first dive to a crooked sequence of length `target`."""
    f = [rng.randrange(levels)]
    stack = [list((-1, 0, 1))]
    for s in stack:
        rng.shuffle(s)
    while len(f) < target:
        if not stack[-1]:
            if len(f) == 1:
                return None
            f.pop()
            stack.pop()
            continue
        d = stack[-1].pop()
        v = f[-1] + d
        if not 0 <= v < levels:
            continue
        f.append(v)
        if not crooked_last(f):
            f.pop()
            continue
        nxt = [-1, 0, 1]
        rng.shuffle(nxt)
        stack.append(nxt)
    return f


def random_census(samples, target, levels, seed):
    rng = random.Random(seed)
    bad = {}
    seqs = inst = 0
    for _ in range(samples):
        f = random_dive(target, levels, rng)
        if f is None:
            continue
        seqs += 1
        H, L = max(f), min(f)
        if L + 3 > H:
            continue
        for i in range(len(f)):
            inst += 1
            for name in check(f, i, H, L):
                bad.setdefault(name, (list(f), i, H, L))
    print(f"random census: {seqs} crooked sequences of length {target} on {levels} levels,"
          f" seed {seed}; {inst} instances")
    report(bad)


def claim_census(maxlen, levels):
    state = {"ok": 0, "fail": 0, "witness": None}

    def visit(f):
        for i in range(len(f)):
            for verdict, data in claim_instances(f, i):
                if verdict == "ok":
                    state["ok"] += 1
                else:
                    state["fail"] += 1
                    if state["witness"] is None:
                        state["witness"] = (list(f), i, data)

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
    print(f"sub-claim census: {levels} levels, length <= {maxlen}")
    print(f"  exceeding configurations in the open case: {state['ok'] + state['fail']}")
    print(f"  L attained on the arm before the exceeding index: {state['ok']}")
    print(f"  not attained: {state['fail']}")
    if state["witness"]:
        f, i, data = state["witness"]
        print(f"  first failure: rho={f}, i={i}, (arm,s,u,h,H,L)={data}")


WITNESSES = {
    "ExitReachTight / F2PrimeTight / F2PrimeFree":
        ([5, 4, 3, 3, 2, 3, 2, 1, 2, 3, 2, 1, 1, 0], 5),
    "LowExitPeakTight":
        ([3, 4, 4, 5, 6, 5, 4, 4, 3, 4, 3, 2, 3, 4, 3, 2, 2, 1], 2),
    "HighExitValleyOpenTight / HighExitValleyTight":
        ([6, 5, 4, 4, 3, 4, 3, 2, 3, 4, 3, 2, 2, 1, 2, 2, 3, 4, 3, 2, 2, 1, 2, 1, 0], 9),
}


def witness_report():
    """The three witnesses formalised in HPC/Fold/ClosureTight.lean."""
    for name, (f, i) in WITNESSES.items():
        H, L = max(f), min(f)
        ok = all(crooked_last(f[:t + 1]) for t in range(len(f)))
        lip = all(abs(f[k + 1] - f[k]) <= 1 for k in range(len(f) - 1))
        print(f"{name}:")
        print(f"  rho={f}, i={i}, H={H}, L={L}; crooked={ok}, 1-Lipschitz={lip}")
        print(f"  fails: {check(f, i, H, L)}")
        bad = [d for v, d in claim_instances(f, i) if v == "FAIL"]
        if bad:
            print(f"  sub-claim (L attained on the exceeding arm before u) FAILS at {bad}")


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "tight"
    a = sys.argv[2:]
    if mode == "tight":
        tight_census(int(a[0]) if a else 12, int(a[1]) if len(a) > 1 else 6)
    elif mode == "random":
        random_census(int(a[0]) if a else 200, int(a[1]) if len(a) > 1 else 60,
                      int(a[2]) if len(a) > 2 else 12, int(a[3]) if len(a) > 3 else 0)
    elif mode == "witness":
        witness_report()
    elif mode == "claim":
        claim_census(int(a[0]) if a else 12, int(a[1]) if len(a) > 1 else 6)
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
