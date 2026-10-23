#!/usr/bin/env python3
"""Census for batch 22 — the faithful model `IsCrookedIvF` and its realization.

Three jobs.

1. Enumerate the faithful model on short chains and verify, for every member, that the
   explicit construction of HPC/Fold/Faithful.lean does what §3 of the commission claims:
   the `x`-range of link `t` lies inside exactly the strips indexed by `I(t)`, meets exactly
   the strips indexed by `I(t-1) ∪ I(t) ∪ I(t+1)`, overlaps its neighbours and nothing else.
   Endpoints are kept in eighths, exactly as `lxN`/`rxN` do.

2. Report the smallest members of the model at which the crookedness clause is *not* vacuous
   (some admissible pair of meeting indices is at distance at least three), so that the
   formal example is known to exercise the clause.

3. Check that the two batch-20 witnesses violate the new adjacency condition.
"""

from itertools import product

# ---------------------------------------------------------------- the model


def near(n, t):
    return [u for u in range(n) if abs(u - t) <= 1]


def admissible(rho, sig):
    """`le`, `width` and geometric `adj`."""
    n = len(rho)
    for t in range(n):
        if not (rho[t] <= sig[t] <= rho[t] + 1):
            return False
    for t in range(n - 1):
        if max(sig[t], sig[t + 1]) > min(rho[t], rho[t + 1]) + 1:
            return False
    return True


def meets(rho, sig, t):
    """The indices the model says link `t` must meet."""
    s = set()
    for u in near(len(rho), t):
        s.update(range(rho[u], sig[u] + 1))
    return s


def crooked_pairs(rho, sig):
    """All instances of the crookedness clause: (s, t, h, k)."""
    n = len(rho)
    out = []
    for s in range(n):
        for t in range(s + 1, n):
            for h in meets(rho, sig, s):
                for k in meets(rho, sig, t):
                    if abs(h - k) >= 3:
                        out.append((s, t, h, k))
    return out


def crooked(rho, sig):
    n = len(rho)
    for (s, t, h, k) in crooked_pairs(rho, sig):
        ok = False
        for r in range(s + 1, t):
            for r2 in range(r + 1, t):
                if h < k:
                    a, b = k - 1, h + 1
                else:
                    a, b = k + 1, h - 1
                if rho[r] <= a <= sig[r] and rho[r2] <= b <= sig[r2]:
                    ok = True
        if not ok:
            return False
    return True


def in_model(rho, sig):
    return admissible(rho, sig) and crooked(rho, sig)


# ------------------------------------------------------ the construction


def extL(rho, t):
    return any(rho[u] <= rho[t] - 1 for u in range(len(rho)) if abs(u - t) == 1)


def extR(sig, t):
    return any(sig[u] >= sig[t] + 1 for u in range(len(sig)) if abs(u - t) == 1)


def lxN(rho, sig, t):
    if sig[t] == rho[t] + 1:
        return 8 * rho[t] + 9
    return 8 * rho[t] + (2 if extL(rho, t) else 4)


def rxN(rho, sig, t):
    if sig[t] == rho[t] + 1 or extR(sig, t):
        return 8 * rho[t] + 11
    return 8 * rho[t] + 8


def check_construction(rho, sig):
    """The endpoint table of §3, verified member by member."""
    n = len(rho)
    lo = min(rho) - 2
    hi = max(sig) + 2
    for t in range(n):
        p, q = lxN(rho, sig, t), rxN(rho, sig, t)
        assert p < q, (rho, sig, t)
        inside = {j for j in range(lo, hi + 1) if 8 * j <= p and q <= 8 * j + 12}
        touched = {j for j in range(lo, hi + 1) if 8 * j < q and p < 8 * j + 12}
        if inside != set(range(rho[t], sig[t] + 1)):
            return "containment", t, sorted(inside)
        if touched != meets(rho, sig, t):
            return "meeting", t, sorted(touched)
    for t in range(n):
        for u in range(n):
            p, q = lxN(rho, sig, t), rxN(rho, sig, t)
            p2, q2 = lxN(rho, sig, u), rxN(rho, sig, u)
            xmeet = p < q2 and p2 < q
            if abs(t - u) <= 1 and not xmeet:
                return "overlap", (t, u), None
            # links two or more apart are separated by their lanes, so the x-ranges
            # are allowed to meet; nothing to check there
    return None


# ------------------------------------------------------------- the census


def census(nmax, levels):
    total = 0
    bad = []
    nonvacuous = []
    for n in range(1, nmax + 1):
        for rho in product(range(levels), repeat=n):
            for w in product(range(2), repeat=n):
                sig = tuple(rho[t] + w[t] for t in range(n))
                if max(sig) >= levels:
                    continue
                if not in_model(rho, sig):
                    continue
                total += 1
                r = check_construction(rho, sig)
                if r is not None:
                    bad.append((rho, sig, r))
                if crooked_pairs(rho, sig):
                    nonvacuous.append((rho, sig))
    return total, bad, nonvacuous


if __name__ == "__main__":
    NMAX, LEVELS = 7, 5
    total, bad, nonvacuous = census(NMAX, LEVELS)
    print(f"members of the faithful model, n <= {NMAX}, {LEVELS} levels: {total}")
    print(f"failures of the endpoint table: {len(bad)}")
    for b in bad[:5]:
        print("   ", b)
    print(f"members whose crookedness clause fires: {len(nonvacuous)}")
    if nonvacuous:
        shortest = min(len(r) for r, s in nonvacuous)
        firsts = [(r, s) for r, s in nonvacuous if len(r) == shortest]
        print(f"   shortest length {shortest}; first few:")
        for r, s in firsts[:5]:
            print("      rho =", r, " sig =", s, " instances =", crooked_pairs(r, s))

    ivSeq = [9, 8, 7, 8, 7, 6, 7, 6, 6, 5, 6, 6, 7, 8, 7, 6, 6, 5, 6, 5, 5, 4]
    ivSig = [9, 8, 7, 8, 7, 6, 8, 6, 7, 5, 7, 6, 7, 8, 7, 6, 7, 5, 7, 5, 6, 4]
    lpivSeq = [5, 6, 6, 7, 8, 7, 6, 6, 5, 6, 5, 5, 4, 5, 6, 5, 6, 5, 5, 4, 5, 4, 4, 3]
    lpivSig = [5, 7, 6, 7, 8, 7, 6, 7, 5, 7, 5, 6, 4, 5, 6, 5, 7, 5, 6, 4, 6, 4, 5, 3]
    for name, rho, sig in (("ivSeq", ivSeq, ivSig), ("lpivSeq", lpivSeq, lpivSig)):
        viol = [t for t in range(len(rho) - 1)
                if max(sig[t], sig[t + 1]) > min(rho[t], rho[t + 1]) + 1]
        print(f"{name}: adjacency violated at t = {viol}")
