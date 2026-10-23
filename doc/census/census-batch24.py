#!/usr/bin/env python3
"""Census for batch 24: `F2PrimeOff` over the faithful model.

Implements `IsCrookedIvF` (geometric adjacency + forced-meeting crookedness) exactly as in
HPC/Fold/Faithful.lean, the two walks `offLam`/`offVee` exactly as in HPC/Fold/OffCenter.lean,
and `FoldsOnto` by reachability (the existential over the time-assignment beta is decided by
forward propagation of the set of reachable times).

Usage:
  python3 census-batch24.py exhaustive LEN LEVELS
  python3 census-batch24.py random LEN LEVELS TRIALS [SEED]
  python3 census-batch24.py bing N            # every basepoint of bing 0 N
  python3 census-batch24.py bingsub N MINLEN MINSPAN  # contiguous subchains of bing 0 N
  python3 census-batch24.py seq  V1,V2,...    # one explicit sequence (sigma = rho)
  python3 census-batch24.py dichotomy bing N          # OffDichotomy on bing 0 N
  python3 census-batch24.py dichotomy bingsub N MINLEN MINSPAN
  python3 census-batch24.py dichotomy ex LEN LEVELS   # OffDichotomy, exhaustive
"""

import sys, random


# ---------------------------------------------------------------- the model

def meets(rho, sig, s):
    n = len(rho)
    out = set()
    for u in range(max(0, s - 1), min(n, s + 2)):
        for h in range(rho[u], sig[u] + 1):
            out.add(h)
    return sorted(out)


def crooked_ok(rho, sig, s, t):
    for h in meets(rho, sig, s):
        for k in meets(rho, sig, t):
            if abs(h - k) < 3:
                continue
            found = False
            if h < k:
                a, b = k - 1, h + 1
            else:
                a, b = k + 1, h - 1
            for r in range(s + 1, t):
                if not (rho[r] <= a <= sig[r]):
                    continue
                for r2 in range(r + 1, t):
                    if rho[r2] <= b <= sig[r2]:
                        found = True
                        break
                if found:
                    break
            if not found:
                return False
    return True


def is_faithful(rho, sig):
    n = len(rho)
    for t in range(n):
        if not (rho[t] <= sig[t] <= rho[t] + 1):
            return False
    for t in range(n - 1):
        if max(sig[t], sig[t + 1]) > min(rho[t], rho[t + 1]) + 1:
            return False
    for s in range(n):
        for t in range(s + 1, n):
            if not crooked_ok(rho, sig, s, t):
                return False
    return True


# ------------------------------------------------------- the off-center family

def off_lam(c0, h, L, H):
    a = max(h - c0, 0) + 1
    b = max(h - 1 - (L + 1), 0) + 1
    d = max(H - 1 - (L + 2), 0) + 1
    length = a + b + d

    def c(u):
        if u < a:
            return c0 + u
        if u < a + b:
            return h - 1 - (u - a)
        return L + 2 + (u - a - b)

    return length, [c(u) for u in range(length)]


def off_vee(c0, l, L, H):
    a = max(c0 - l, 0) + 1
    b = max(H - 1 - (l + 1), 0) + 1
    d = max(H - 2 - (L + 1), 0) + 1
    length = a + b + d

    def c(u):
        if u < a:
            return c0 - u
        if u < a + b:
            return l + 1 + (u - a)
        return H - 2 - (u - a - b)

    return length, [c(u) for u in range(length)]


def folds_onto(f, walk):
    """Reachability decision of FoldsOnto f len walk (beta 0 = 0, 1-Lipschitz in time)."""
    length = len(walk)
    if not f:
        return True
    if abs(f[0] - walk[0]) > 1:
        return False
    cur = {0}
    for j in range(1, len(f)):
        nxt = set()
        for b in cur:
            for b2 in (b - 1, b, b + 1):
                if 0 <= b2 < length and abs(f[j] - walk[b2]) <= 1:
                    nxt.add(b2)
        if not nxt:
            return False
        cur = nxt
    return True


def f2primeoff_at(rho, i):
    """True iff the conclusion of F2PrimeOff holds at basepoint i (H, L attained extremes)."""
    H, L = max(rho), min(rho)
    if L + 3 > H:
        return True
    p = rho[i]
    G = rho[i:]
    T = rho[: i + 1][::-1]
    for c0 in (p - 1, p, p + 1):
        if not (L + 1 <= c0 <= H - 1):
            continue
        for h in range(c0, H):
            length, walk = off_lam(c0, h, L, H)
            if folds_onto(G, walk) and folds_onto(T, walk):
                return True
        for l in range(L + 1, c0 + 1):
            length, walk = off_vee(c0, l, L, H)
            if folds_onto(G, walk) and folds_onto(T, walk):
                return True
    return False


def witness_at(rho, i):
    """The (c0, kind, h/l) that works at basepoint i, or None."""
    H, L = max(rho), min(rho)
    if L + 3 > H:
        return ("degenerate",)
    p = rho[i]
    G = rho[i:]
    T = rho[: i + 1][::-1]
    for c0 in (p - 1, p, p + 1):
        if not (L + 1 <= c0 <= H - 1):
            continue
        for h in range(c0, H):
            _, walk = off_lam(c0, h, L, H)
            if folds_onto(G, walk) and folds_onto(T, walk):
                return (c0, "lam", h)
        for l in range(L + 1, c0 + 1):
            _, walk = off_vee(c0, l, L, H)
            if folds_onto(G, walk) and folds_onto(T, walk):
                return (c0, "vee", l)
    return None


def check_seq(rho, sig, report):
    for i in range(len(rho)):
        if not f2primeoff_at(rho, i):
            report.setdefault("F2PrimeOff", []).append((list(rho), list(sig), i))


# ------------------------------------------------- the dichotomy of OffCenter.lean

def bottom_on_time(f, c0, L):
    """`BottomOnTime` of HPC/Fold/OffCenter.lean, verbatim."""
    if all(v <= c0 + 1 for v in f):
        return True
    b = max(c0 - L - 2, 0) + 1
    thr = min(L + 2, c0)
    for j in range(b, len(f)):
        if all(f[k] <= c0 + 1 and f[k] <= thr + (j - k) for k in range(j + 1)):
            return True
    return False


def top_on_time(f, c0, H):
    """`TopOnTime`: the reflection of `BottomOnTime`."""
    return bottom_on_time([-v for v in f], -c0, -H)


def dichotomy_at(rho, i):
    """`OffDichotomy` at one basepoint: True, or the pair (False, witness data)."""
    H, L = max(rho), min(rho)
    if L + 3 > H:
        return True
    p = rho[i]
    G = rho[i:]
    T = rho[: i + 1][::-1]
    for c0 in (p - 1, p, p + 1):
        if not (L + 1 <= c0 <= H - 1):
            continue
        if bottom_on_time(G, c0, L) and bottom_on_time(T, c0, L):
            return True
        if top_on_time(G, c0, H) and top_on_time(T, c0, H):
            return True
    return False


def dichotomy_seq(rho, report):
    """Scores the dichotomy, and checks that each criterion really does give a fold."""
    H, L = max(rho), min(rho)
    if L + 3 > H:
        return
    for i in range(len(rho)):
        p = rho[i]
        G = rho[i:]
        T = rho[: i + 1][::-1]
        if not dichotomy_at(rho, i):
            report.setdefault("OffDichotomy", []).append((list(rho), i))
        for c0 in (p - 1, p, p + 1):
            if not (L + 1 <= c0 <= H - 1):
                continue
            _, wl = off_lam(c0, c0, L, H)
            _, wv = off_vee(c0, c0, L, H)
            for f in (G, T):
                if bottom_on_time(f, c0, L) and not folds_onto(f, wl):
                    report.setdefault("BottomOnTime unsound", []).append((list(rho), i, c0))
                if top_on_time(f, c0, H) and not folds_onto(f, wv):
                    report.setdefault("TopOnTime unsound", []).append((list(rho), i, c0))


# ------------------------------------------------------------- Bing's chains

def bing_path(a, b):
    if abs(b - a) <= 2:
        if a <= b:
            return list(range(a, b + 1))
        return list(range(a, b - 1, -1))
    if a < b:
        return bing_path(a, b - 1) + bing_path(b - 1, a + 1)[1:] + bing_path(a + 1, b)[1:]
    return bing_path(a, b + 1) + bing_path(b + 1, a - 1)[1:] + bing_path(a - 1, b)[1:]


# ------------------------------------------------------------- enumeration

def enumerate_faithful(n, levels, cb):
    rho = [0] * n
    sig = [0] * n
    count = 0

    def partial_ok(m):
        if m >= 2:
            t = m - 2
            if max(sig[t], sig[t + 1]) > min(rho[t], rho[t + 1]) + 1:
                return False
        t = m - 2
        if t >= 1:
            for s in range(t):
                if not crooked_ok(rho[:m], sig[:m], s, t):
                    return False
        return True

    def rec(m):
        nonlocal count
        if m == n:
            for s in range(n - 1):
                if not crooked_ok(rho, sig, s, n - 1):
                    return
            count += 1
            cb(rho, sig)
            return
        lo = 0 if m == 0 else max(0, rho[m - 1] - 1)
        hi = 0 if m == 0 else min(levels - 1, rho[m - 1] + 1)
        for v in range(lo, hi + 1):
            rho[m] = v
            for w in (v, v + 1):
                if w > levels - 1:
                    continue
                sig[m] = w
                if partial_ok(m + 1):
                    rec(m + 1)

    rec(0)
    return count


def random_faithful(n, levels, rng, tries=400):
    for _ in range(tries):
        rho = [rng.randrange(levels)]
        sig = [rho[0] if rng.random() < 0.5 or rho[0] + 1 >= levels else rho[0] + 1]
        ok = True
        for m in range(1, n):
            cands = []
            for v in range(max(0, rho[-1] - 1), min(levels - 1, rho[-1] + 1) + 1):
                for w in (v, v + 1):
                    if w > levels - 1:
                        continue
                    if max(sig[-1], w) > min(rho[-1], v) + 1:
                        continue
                    r2, s2 = rho + [v], sig + [w]
                    good = True
                    t = m - 1
                    if t >= 1:
                        for s in range(t):
                            if not crooked_ok(r2, s2, s, t):
                                good = False
                                break
                    if good:
                        cands.append((v, w))
            if not cands:
                ok = False
                break
            v, w = rng.choice(cands)
            rho.append(v)
            sig.append(w)
        if ok and is_faithful(rho, sig):
            return rho, sig
    return None


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return
    mode = sys.argv[1]
    report = {}
    if mode == "exhaustive":
        n = int(sys.argv[2])
        levels = int(sys.argv[3])
        pts = [0]

        def cb(rho, sig):
            pts[0] += len(rho)
            check_seq(rho, sig, report)

        c = enumerate_faithful(n, levels, cb)
        print(f"length {n}, {levels} levels: {c} faithful pairs, {pts[0]} basepoints")
    elif mode == "random":
        n = int(sys.argv[2])
        levels = int(sys.argv[3])
        trials = int(sys.argv[4])
        seed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
        rng = random.Random(seed)
        got = 0
        for _ in range(trials):
            r = random_faithful(n, levels, rng)
            if r is None:
                continue
            got += 1
            check_seq(r[0], r[1], report)
        print(f"random length {n}, {levels} levels: {got} faithful pairs")
    elif mode == "bing":
        n = int(sys.argv[2])
        rho = bing_path(0, n)
        sig = list(rho)
        print(f"bing 0 {n}: {len(rho)} links, faithful={is_faithful(rho, sig)}")
        check_seq(rho, sig, report)
    elif mode == "bingsub":
        n = int(sys.argv[2])
        minlen = int(sys.argv[3])
        minspan = int(sys.argv[4])
        full = bing_path(0, n)
        subs = 0
        pts = 0
        for a in range(len(full)):
            for b in range(a + minlen, len(full) + 1):
                rho = full[a:b]
                if max(rho) - min(rho) < minspan:
                    continue
                subs += 1
                pts += len(rho)
                check_seq(rho, list(rho), report)
        print(f"bing 0 {n}: {subs} subchains of length >= {minlen}, span >= {minspan}; "
              f"{pts} basepoints")
    elif mode == "dichotomy":
        what = sys.argv[2]
        if what == "bing":
            n = int(sys.argv[3])
            rho = bing_path(0, n)
            dichotomy_seq(rho, report)
            print(f"bing 0 {n}: {len(rho)} links")
        elif what == "bingsub":
            n = int(sys.argv[3])
            minlen = int(sys.argv[4])
            minspan = int(sys.argv[5])
            full = bing_path(0, n)
            subs = 0
            for a in range(len(full)):
                for b in range(a + minlen, len(full) + 1):
                    rho = full[a:b]
                    if max(rho) - min(rho) < minspan:
                        continue
                    subs += 1
                    dichotomy_seq(rho, report)
            print(f"bing 0 {n}: {subs} subchains")
        else:
            n = int(sys.argv[3])
            levels = int(sys.argv[4])
            c = enumerate_faithful(n, levels, lambda rho, sig: dichotomy_seq(rho, report))
            print(f"length {n}, {levels} levels: {c} faithful pairs")
        if not report:
            print("  no failure of OffDichotomy, and both criteria give folds throughout")
        for k, v in report.items():
            print(f"  {k}: {len(v)} failures, first {v[0]}")
        return
    elif mode == "seq":
        rho = [int(x) for x in sys.argv[2].split(",")]
        sig = list(rho)
        print(f"length {len(rho)}, faithful={is_faithful(rho, sig)}")
        check_seq(rho, sig, report)
    else:
        print(__doc__)
        return
    if not report:
        print("  no failure of F2PrimeOff")
    for k, v in report.items():
        print(f"  {k}: {len(v)} failures, first {v[0]}")


if __name__ == "__main__":
    main()
