#!/usr/bin/env python3
"""Batch 122, Q2/Q3: Bing's induction for Theorem 3 (1948), executed as a recursive algorithm with
the seams closed, and checked against the statement on a corpus.

Model.  Fine links t = 0..n-1 with coarse intervals [rho t, sig t] (the coarse links containing
the link; faithful model), coarse levels 0..K-1, and a meeting table T (T[t] = set of levels the
link t meets).  Requirements on T (they hold for the true meetings of any chain): every level of
[rho t, sig t] and of the intervals of the neighbours of t is in T[t] (forced meetings), and every
level in T[t] lies in [sig t - 1, rho t + 1].  The hypothesis is 1948 crookedness read with T.

Statement (Bing's Theorem 3 in the block reading, "or" end clause):  a time function beta with
beta(i) = 0, |beta(t+1) - beta(t)| <= 1, every fibre inside two adjacent coarse links (a common
level window [j, j+1] meets every interval of the fibre), and for each end link e meeting level 0
or K-1: its fibre has all rho <= 1 or all sig >= K-2.

The algorithm follows Bing's proof (notes: COMMISSION-batch121 transcription), with these repairs:
  * level groups of the special case: reading Cbot of REPORT-batch121 (bottom group rho <= 1,
    top group sig >= K-3 and rho >= 2, between by rho); of the general case: its mirror image
    anchored at the extreme that h_u meets (bottom group rho <= 1, top group sig >= K-2 and
    rho >= 2, between by rho);
  * the special case at r = 5 uses the base-case grouping for H, chosen so that the block of d_h
    has every rho >= K-3 (property P_s of Q1);
  * the special case with d_i strictly between d_h and d_k ("by a similar line of argument"):
    H is taken on D(h, k) inside E(2, r-1), and F is built from H as in the first branch, cut at
    the earlier of the blocks of d_h and d_k.
Every value returned is checked against the statement (check_stmt); a failure is printed.

Usage: recon-batch122-bing.py enum K nmin nmax   (all crooked faithful sequences, forced meetings
         plus every admissible set of extra end meetings, every basepoint)
       recon-batch122-bing.py bing KK              (all subchains of Bing's chain P(0, KK-1))
       recon-batch122-bing.py special K nmin nmax  (the special-case corpus of seam-batch121.py)
"""
import sys
import os
import importlib.util

sys.setrecursionlimit(10000)

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("seam121", os.path.join(here, "seam-batch121.py"))
S = importlib.util.module_from_spec(spec)
spec.loader.exec_module(S)

STATS = {}


def stat(key):
    STATS[key] = STATS.get(key, 0) + 1


# ---------------------------------------------------------------- the model

def forced_table(seq):
    n = len(seq)
    T = []
    for t in range(n):
        s = set()
        for u in (t - 1, t, t + 1):
            if 0 <= u < n:
                s.update(range(seq[u][0], seq[u][1] + 1))
        T.append(s)
    return T


def crooked_T(seq, K, T):
    n = len(seq)
    for s in range(n):
        for t in range(s + 1, n):
            for a in T[s]:
                for b in T[t]:
                    if abs(a - b) < 3:
                        continue
                    n1 = b - 1 if a < b else b + 1
                    n2 = a + 1 if a < b else a - 1
                    r = next((x for x in range(s + 1, t) if seq[x][0] <= n1 <= seq[x][1]), None)
                    r2 = next((x for x in range(t - 1, s, -1) if seq[x][0] <= n2 <= seq[x][1]), None)
                    if r is None or r2 is None or not r < r2:
                        return False
    return True


def check_stmt(seq, T, K, i, beta):
    n = len(seq)
    if beta is None or len(beta) != n:
        return "none"
    if beta[i] != 0 or min(beta) < 0:
        return "first"
    for t in range(n - 1):
        if abs(beta[t + 1] - beta[t]) > 1:
            return "lip"
    fib = {}
    for t in range(n):
        fib.setdefault(beta[t], []).append(t)
    for b, mem in fib.items():
        if max(seq[t][0] for t in mem) - 1 > min(seq[t][1] for t in mem):
            return "width"
    for e in {0, n - 1}:
        if 0 in T[e] or (K - 1) in T[e]:
            mem = fib[beta[e]]
            if not (all(seq[t][0] <= 1 for t in mem) or all(seq[t][1] >= K - 2 for t in mem)):
                return "end"
    return None


def flip(seq, T, K):
    """Mirror the coarse chain: level l -> K-1-l."""
    return [(K - 1 - s, K - 1 - r) for (r, s) in seq], [set(K - 1 - l for l in x) for x in T]


def rev(seq, T):
    return list(reversed(seq)), list(reversed(T))


def sub(seq, T, p, q, lo, hi):
    """Fine links p..q, coarse levels lo..hi (shifted to 0..hi-lo).  Requires every link of the
    subchain to lie in a level of lo..hi."""
    s2 = []
    for t in range(p, q + 1):
        r, s = seq[t]
        r2, s2_ = max(r, lo), min(s, hi)
        assert r2 <= s2_, "link not inside the sub-frame"
        # the interval of the link relative to the sub-frame: the levels of lo..hi containing it
        s2.append((r2 - lo, s2_ - lo))
    T2 = [set(l - lo for l in T[t] if lo <= l <= hi) for t in range(p, q + 1)]
    return s2, T2


# ---------------------------------------------------------------- the algorithm

def cbot_special(r, s, K):
    """Cbot group of the special case (coarse frame 0..K-1, groups 0..K-4, 0 = bottom)."""
    if r <= 1:
        return 0
    if s >= K - 3:
        return K - 4
    return r - 1


def cbot_general(r, s, K):
    """Group of the general case, bottom-anchored (groups 0..K-3, 0 = bottom e1+e2)."""
    if r <= 1:
        return 0
    if s >= K - 2:
        return K - 3
    return r - 1


def level_grouping(seq, K, i):
    """Bing's case d_i in e1+e2 (or, mirrored, in e_{m-1}+e_m), and the base case m <= 4."""
    n = len(seq)
    if K <= 4:
        thr = 1 if seq[i][0] <= 1 else None
        g = [0 if seq[t][0] <= 1 else 1 for t in range(n)]
        if g[i] == 1:
            g = [1 - x for x in g]
        return g
    if seq[i][0] <= 1:
        return [min(max(seq[t][0] - 1, 0), K - 3) for t in range(n)]
    if seq[i][1] >= K - 2:
        return [min(max(K - 2 - seq[t][1], 0), K - 3) for t in range(n)]
    return None


def bing(seq, T, K, i, depth=0):
    n = len(seq)
    if K <= 4 or seq[i][0] <= 1 or seq[i][1] >= K - 2:
        stat("level" if K > 4 else "base")
        return level_grouping(seq, K, i)
    ext = lambda t: 0 in T[t] or (K - 1) in T[t]
    h = max([t for t in range(i) if ext(t)], default=0)
    k = min([t for t in range(i + 1, n) if ext(t)], default=n - 1)
    low = any(0 in T[t] for t in range(h, k + 1))
    high = any((K - 1) in T[t] for t in range(h, k + 1))
    # H on D(h, k), satisfying the statement in E
    if not low:
        s2, T2 = sub(seq, T, h, k, 1, K - 1)
        H = bing(s2, T2, K - 1, i - h, depth + 1)
        stat("general/IH-low")
    elif not high:
        s2, T2 = sub(seq, T, h, k, 0, K - 2)
        H = bing(s2, T2, K - 1, i - h, depth + 1)
        stat("general/IH-high")
    else:
        s2, T2 = sub(seq, T, h, k, 0, K - 1)
        H = special(s2, T2, K, i - h, depth + 1)
        stat("general/special")
    if H is None:
        return None
    if h == 0 and k == n - 1:
        return H
    blocks_ext = [H[t - h] for t in range(h, k + 1) if ext(t)]
    u = min(blocks_ext)
    lowmeet = any(0 in T[t] for t in range(h, k + 1) if ext(t) and H[t - h] == u)
    if not lowmeet:
        sf, Tf = flip(seq, T, K)
        F = general_F(sf, Tf, K, h, k, H, u)
    else:
        F = general_F(seq, T, K, h, k, H, u)
    return F


def general_F(seq, T, K, h, k, H, u):
    n = len(seq)
    F = []
    for t in range(n):
        if h <= t <= k and H[t - h] < u:
            F.append(H[t - h])
        else:
            F.append(u + cbot_general(seq[t][0], seq[t][1], K))
    return F


def special(seq, T, K, i, depth=0):
    """Special case: only the end links meet the extreme levels, one meets 0 and the other K-1."""
    n = len(seq)
    if K <= 4 or seq[i][0] <= 1 or seq[i][1] >= K - 2:
        return level_grouping(seq, K, i)
    if not (0 in T[0]):
        # mirror so that link 0 meets level 0
        sf, Tf = flip(seq, T, K)
        return special(sf, Tf, K, i, depth)
    assert (K - 1) in T[n - 1]
    tops = [t for t in range(n) if seq[t][0] <= K - 2 <= seq[t][1]]
    bots = [t for t in range(n) if seq[t][0] <= 1 <= seq[t][1]]
    # branch 1: some h >= i inside e_{K-2} followed by some k inside e_1
    for h in tops:
        if h >= i:
            ks = [k for k in bots if k > h]
            if ks:
                stat("special/branch1")
                return special_branch1(seq, T, K, i, h, ks[0], depth)
    # branch 3 (mirror of branch 1): some k <= i inside e_1 preceded by some h inside e_{K-2}
    for k in reversed(bots):
        if k <= i:
            hs = [h for h in tops if h < k]
            if hs:
                stat("special/branch3")
                sr, Tr = rev(seq, T)
                sr, Tr = flip(sr, Tr, K)
                F = special_branch1(sr, Tr, K, n - 1 - i, n - 1 - k, n - 1 - hs[-1], depth)
                return None if F is None else list(reversed(F))
    # middle: h < i < k
    hs = [h for h in tops if h < i]
    ks = [k for k in bots if k > i]
    if not hs or not ks:
        print("  NO (h, k)?!", seq, i)
        return None
    stat("special/middle")
    return special_middle(seq, T, K, i, hs[-1], ks[0], depth)


def special_branch1(seq, T, K, i, h, k, depth):
    n = len(seq)
    # H on D(0, h) inside E(0, K-2), basepoint i; at K = 5 the base grouping with d_h's block
    # having rho >= K-3 = 2
    s2, T2 = sub(seq, T, 0, h, 0, K - 2)
    if K == 5:
        g = [0 if s2[t][0] <= 1 else 1 for t in range(h + 1)]
        if g[i] == 1:
            g = [1 - x for x in g]
        H = g
    else:
        H = bing(s2, T2, K - 1, i, depth + 1)
    if H is None:
        return None
    u = H[h]
    F = []
    for t in range(n):
        if t <= h and H[t] < u:
            F.append(H[t])
        elif t <= k:
            F.append(u + (K - 4) - cbot_special(seq[t][0], seq[t][1], K))
        else:
            F.append(u + (K - 4) + (t - k))
    return F


def special_middle(seq, T, K, i, h, k, depth):
    n = len(seq)
    s2, T2 = sub(seq, T, h, k, 1, K - 2)
    if K == 5:
        # E(1, 3): base grouping with the block of d_h having rho >= 2 and the block of d_k rho <= 1
        g = [0 if seq[t][0] <= 1 else 1 for t in range(h, k + 1)]
        if g[i - h] == 1:
            g = [1 - x for x in g]
        H = g
    else:
        H = bing(s2, T2, K - 2, i - h, depth + 1)
    if H is None:
        return None
    a, b = H[0], H[k - h]
    if a <= b:
        F = []
        for t in range(n):
            if h <= t <= k and H[t - h] < a:
                F.append(H[t - h])
            elif t <= k:
                F.append(a + (K - 4) - cbot_special(seq[t][0], seq[t][1], K))
            else:
                F.append(a + (K - 4) + (t - k))
        return F
    # b < a: reverse and flip, then the same with the roles of d_h, d_k exchanged
    sr, Tr = rev(seq, T)
    sr, Tr = flip(sr, Tr, K)
    Hr = list(reversed(H))
    h2, k2 = n - 1 - k, n - 1 - h
    a2 = Hr[0]
    F = []
    for t in range(n):
        if h2 <= t <= k2 and Hr[t - h2] < a2:
            F.append(Hr[t - h2])
        elif t <= k2:
            F.append(a2 + (K - 4) - cbot_special(sr[t][0], sr[t][1], K))
        else:
            F.append(a2 + (K - 4) + (t - k2))
    return list(reversed(F))


# ---------------------------------------------------------------- the corpora

FAILS = []


def test(seq, T, K, label=""):
    n = len(seq)
    bad = 0
    for i in range(n):
        F = bing(seq, T, K, i)
        r = check_stmt(seq, T, K, i, F)
        if r is not None:
            bad += 1
            stat("FAIL/" + r)
            if len(FAILS) < 20:
                FAILS.append((label, seq, [sorted(x) for x in T], K, i, F, r))
                print(f"  FAIL {label} K={K} rho={[c[0] for c in seq]} sig={[c[1] for c in seq]} "
                      f"T={[sorted(x) for x in T]} i={i} F={F} kind={r}")
                sys.stdout.flush()
    return bad


def admissible_extras(seq, K):
    """Every set of extra end meetings with the extreme levels (possible and unforced) keeping
    crookedness; yields the tables."""
    n = len(seq)
    base = forced_table(seq)
    cands = []
    for e in sorted({0, n - 1}):
        for L in (0, K - 1):
            if L not in base[e] and seq[e][1] - 1 <= L <= seq[e][0] + 1:
                cands.append((e, L))
    for mask in range(1 << len(cands)):
        T = [set(x) for x in base]
        for j, (e, L) in enumerate(cands):
            if mask >> j & 1:
                T[e].add(L)
        if mask == 0 or crooked_T(seq, K, T):
            yield T


def run_enum(K, nmin, nmax):
    import subprocess
    for n in range(nmin, nmax + 1):
        nseq = ninst = bad = 0
        for seq in enum_faithful(n, K):
            nseq += 1
            for T in admissible_extras(seq, K):
                ninst += n
                bad += test(seq, T, K, f"enum n={n}")
        print(f"K={K} n={n}: sequences={nseq} instances(table, basepoint)={ninst} failures={bad}")
        sys.stdout.flush()


def enum_faithful(n, K):
    """All crooked (forced meetings) faithful sequences of length n spanning exactly K levels,
    with prefix pruning (as census-batch87-common.h)."""
    cells = [(r, s) for r in range(K) for s in (r, r + 1) if s < K]
    seq = []

    def pair_ok(sq, s, t):
        T = forced_table(sq)
        for a in T[s]:
            for b in T[t]:
                if abs(a - b) < 3:
                    continue
                n1 = b - 1 if a < b else b + 1
                n2 = a + 1 if a < b else a - 1
                r = next((x for x in range(s + 1, t) if sq[x][0] <= n1 <= sq[x][1]), None)
                r2 = next((x for x in range(t - 1, s, -1) if sq[x][0] <= n2 <= sq[x][1]), None)
                if r is None or r2 is None or not r < r2:
                    return False
        return True

    def rec():
        L = len(seq)
        if L >= 2:
            tt = L - 2
            for s0 in range(0, tt):
                if not pair_ok(seq, s0, tt):
                    return
        if L == n:
            for s0 in range(0, n - 1):
                if not pair_ok(seq, s0, n - 1):
                    return
            if min(c[0] for c in seq) != 0 or max(c[1] for c in seq) != K - 1:
                return
            yield list(seq)
            return
        for c in cells:
            if seq:
                p = seq[-1]
                if max(p[1], c[1]) > min(p[0], c[0]) + 1:
                    continue
            seq.append(c)
            yield from rec()
            seq.pop()
    yield from rec()


def bing_path(a, b):
    d = abs(b - a)
    if d <= 2:
        s = 1 if a <= b else -1
        return [a + s * u for u in range(d + 1)]
    mid = b - 1 if a < b else b + 1
    c = a + 1 if a < b else a - 1
    p1, p2, p3 = bing_path(a, mid), bing_path(mid, c), bing_path(c, b)
    return p1 + p2[1:] + p3[1:]


def run_bing(KK, frames=False):
    """All subchains of Bing's chain P(0, KK-1), with the meeting table of the whole realized
    chain restricted (so the end links meet the levels of their outer neighbours), inside the
    frame of all KK levels and inside every sub-frame lo..hi containing the subchain."""
    P = bing_path(0, KK - 1)
    N = len(P)
    nsub = ninst = bad = 0
    for l in range(N):
        for r in range(l + 1, N):
            full = [(x, x) for x in P]
            Tfull = forced_table(full)
            seq = full[l:r + 1]
            T = Tfull[l:r + 1]
            lo0, hi0 = min(P[l:r + 1]), max(P[l:r + 1])
            fr = [(lo, hi) for lo in range(0, lo0 + 1) for hi in range(hi0, KK)] if frames else [(0, KK - 1)]
            for (lo, hi) in fr:
                s2, T2 = sub(seq, T, 0, len(seq) - 1, lo, hi)
                K = hi - lo + 1
                nsub += 1
                ninst += len(seq)
                bad += test(s2, T2, K, f"bing KK={KK} sub={l}..{r} frame={lo}..{hi}")
    print(f"bing KK={KK} (length {N}): subchain/frame pairs={nsub} instances={ninst} failures={bad}")


def run_special(K, nmin, nmax):
    for n in range(nmin, nmax + 1):
        nseq = ninst = bad = 0
        for inner in S.special_seqs(n, K):
            M = S.meets_table(inner, K, [(0, 0), (n - 1, K - 1)])
            if not S.crooked(inner, K, M):
                continue
            T = [set(j for j in range(K) if M[t][j]) for t in range(n)]
            nseq += 1
            ninst += n
            bad += test(inner, T, K, f"special n={n}")
        print(f"special K={K} n={n}: sequences={nseq} instances={ninst} failures={bad}")
        sys.stdout.flush()


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "enum":
        run_enum(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    elif mode == "bing":
        run_bing(int(sys.argv[2]), len(sys.argv) > 3 and sys.argv[3] == "frames")
    elif mode == "special":
        run_special(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    print("# branch statistics:", dict(sorted(STATS.items())))
