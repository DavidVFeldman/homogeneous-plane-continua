#!/usr/bin/env python3
"""Batch 121, Q4: Bing's special-case construction (Theorem 3, 1948, p. 732), executed literally.

Coordinates are 0-indexed.  Fine chain = Bing's D (links t = 0..n-1), coarse chain = Bing's E
(levels 0..K-1, K = Bing's r).  A fine link t lies in the coarse links rho t .. sig t (faithful
model).  Meetings: forced (some u with |u - t| <= 1 has rho u <= j <= sig u) plus the extra
meetings "link 0 meets level 0" and "link n-1 meets level K-1".

Special case.  No interior link meets level 0 or K-1; link 0 meets level 0, link n-1 meets level
K-1.  Forced meetings make the special case impossible in the realized model chain for n >= 3 (a
link inside level 0 forces its neighbour to meet level 0), so both end meetings are extra: every
link has 1 <= rho <= sig <= K-2, link 0 has [rho, sig] = [1, 1] ... [1, 2] (it lies in level 1 or
2 and must reach level 0, so sig 0 <= 1, i.e. rho 0 = sig 0 = 1), link n-1 likewise at K-2.
Crookedness is checked for the meeting table enlarged by the two extra meetings.

Crookedness gives 0 < h < k < n-1 with d_h inside level K-2 and d_k inside level 1.  For every such
(h, k), every basepoint i <= h, and every H satisfying the induction hypothesis on D(0, h) inside
E(0, K-2) -- a block map beta_H with beta_H i = 0, every block inside two consecutive levels, and
the end clause for the end links 0 and h of D(0, h) (meeting level 0, resp. K-2, its block lies in
levels 0..1, resp. K-3..K-2) -- the construction is:

  u      = beta_H h                               (the first, and only, block of H containing d_h)
  F-time = beta_H t                     for t <= h with beta_H t < u        (H(1, u-1))
         = u + (K-3) - g(t)             for t in D' (t <= h with beta_H t >= u, or h < t <= k),
                                        g(t) = max(rho t, 1) - 1           (level groups, top first)
         = u + (K-3) + (t - k)          for t > k                           (D(k+1, n))

F is a chain iff the F-time is 1-Lipschitz along the fine chain (block consolidation); it must also
have d_i in its first link (F-time of i = 0).  Its blocks are inside two consecutive levels and its
end clause holds by construction (checked anyway).

Output: for each K and n, the number of instances (sequence, h, k, i), the number for which SOME
admissible H makes F fail, and the number for which EVERY admissible H makes F fail; the failure
kind is recorded (seam at h_{u-1} = Lipschitz failure between H(1, u-1) and D'; u = 0 with d_i not
in the top group; other).
"""
import sys
from itertools import product


def faithful_seqs(n, lo, hi):
    """All adjacency-respecting interval sequences with levels in [lo, hi]."""
    cells = [(r, s) for r in range(lo, hi + 1) for s in (r, r + 1) if s <= hi]
    out = []

    def rec(seq):
        if len(seq) == n:
            out.append(list(seq))
            return
        for c in cells:
            if seq:
                p = seq[-1]
                if max(p[1], c[1]) > min(p[0], c[0]) + 1:
                    continue
            seq.append(c)
            rec(seq)
            seq.pop()
    rec([])
    return out


def meets_table(seq, K, extra):
    n = len(seq)
    M = [[False] * K for _ in range(n)]
    for t in range(n):
        for u in (t - 1, t, t + 1):
            if 0 <= u < n:
                for j in range(seq[u][0], seq[u][1] + 1):
                    M[t][j] = True
    for (t, j) in extra:
        M[t][j] = True
    return M


def crooked(seq, K, M):
    n = len(seq)
    for s in range(n):
        for t in range(s + 1, n):
            for a in range(K):
                if not M[s][a]:
                    continue
                for b in range(K):
                    if abs(a - b) < 3 or not M[t][b]:
                        continue
                    n1 = b - 1 if a < b else b + 1
                    n2 = a + 1 if a < b else a - 1
                    r = next((x for x in range(s + 1, t) if seq[x][0] <= n1 <= seq[x][1]), None)
                    r2 = next((x for x in range(t - 1, s, -1) if seq[x][0] <= n2 <= seq[x][1]), None)
                    if r is None or r2 is None or not r < r2:
                        return False
    return True


def all_H(seq, h, i, K, M):
    """All time functions on links 0..h satisfying the induction hypothesis inside levels
    0..K-2 (K-1 coarse links): beta i = 0, Lipschitz, blocks in two consecutive levels, end
    clause for links 0 and h."""
    top = K - 2
    endlow = {t for t in (0, h) if M[t][0]}
    endhigh = {t for t in (0, h) if M[t][top]}
    order = [i] + list(range(i + 1, h + 1)) + list(range(i - 1, -1, -1))
    prev = {i: None}
    for t in range(i + 1, h + 1):
        prev[t] = t - 1
    for t in range(i - 1, -1, -1):
        prev[t] = t + 1
    beta = {}
    blocks = {}
    res = []

    def ok_block(b):
        mem = blocks[b]
        mr = max(seq[t][0] for t in mem)
        ms = min(seq[t][1] for t in mem)
        if mr - 1 > ms:
            return False
        if any(t in endlow for t in mem) and mr > 1:
            return False
        if any(t in endhigh for t in mem) and ms < top - 1:
            return False
        return True

    def rec(p):
        if p == len(order):
            res.append(dict(beta))
            return
        t = order[p]
        cands = [0] if prev[t] is None else [v for v in (beta[prev[t]] - 1, beta[prev[t]], beta[prev[t]] + 1) if v >= 0]
        for v in cands:
            beta[t] = v
            blocks.setdefault(v, []).append(t)
            if ok_block(v):
                rec(p + 1)
            blocks[v].pop()
            del beta[t]
    rec(0)
    return res


GROUPING = "A"
PADDED = False


def construct_F(seq, K, h, k, H):
    """Reading A (bottom-anchored, by rho): groups "in e1+e2" (rho <= 1), "in e3 not e2" (rho = 2),
    ..., "in e_{r-1} not e_{r-2}" (rho = K-2), the last described by Bing as "in e_{r-2}+e_{r-1}".
    Reading B (top-anchored, by sig): the top group is every link of D' in e_{r-2}+e_{r-1}
    (sig >= K-3), then sig = K-4, ..., the bottom group sig <= 1.
    Readings Ctop / Cbot: bottom group "in e1+e2" (rho <= 1), top group "in e_{r-2}+e_{r-1}"
    (sig >= K-3), the groups between by rho; a link in both end groups goes to the top group
    (Ctop) or to the bottom group (Cbot)."""
    n = len(seq)
    u = H[h]
    F = []
    if GROUPING == "A":
        top = K - 3
        grp = lambda t: max(seq[t][0], 1) - 1
    elif GROUPING == "B":
        top = K - 4
        grp = lambda t: min(max(seq[t][1], 1), K - 3) - 1
    elif GROUPING == "Ctop":
        # the top group absorbs every link of D' in e_{r-2}+e_{r-1} (sig >= K-3), first
        top = K - 4
        grp = lambda t: top if seq[t][1] >= K - 3 else max(seq[t][0], 1) - 1
    else:  # "Cbot": the bottom group e1+e2 (rho <= 1) first, then the absorbing top group
        top = K - 4
        grp = lambda t: 0 if seq[t][0] <= 1 else (top if seq[t][1] >= K - 3 else seq[t][0] - 1)
    for t in range(n):
        if t <= h and H[t] < u:
            F.append(H[t])
        elif t <= k:
            F.append(u + top - grp(t))
        else:
            F.append(u + top + (t - k))
    return F, u


def check_F(seq, K, i, F, M):
    n = len(seq)
    if any(abs(F[t + 1] - F[t]) > 1 for t in range(n - 1)):
        return "lip"
    if F[i] != 0 or min(F) != 0:
        return "first"
    for b in set(F):
        mem = [t for t in range(n) if F[t] == b]
        mr = max(seq[t][0] for t in mem)
        ms = min(seq[t][1] for t in mem)
        if mr - 1 > ms:
            return "width"
        for t in (0, n - 1):
            if t in mem and M[t][0] and mr > 1:
                return "end"
            if t in mem and M[t][K - 1] and ms < K - 2:
                return "end"
    return None


def special_seqs(n, K):
    """Faithful sequences with levels in [1, K-2], first link (1, 1), last link (K-2, K-2), crooked
    for the forced meetings plus "link 0 meets level 0" (pruned on prefixes: the pair (s, t) only
    reads links s-1 .. t+1; the extra meeting of link n-1 is added at the end)."""
    lo, hi = 1, K - 2
    cells = [(r, s) for r in range(lo, hi + 1) for s in (r, r + 1) if s <= hi]
    out = []
    seq = [(1, 1)]

    def pair_ok(sq, s, t, M):
        a_list = [a for a in range(K) if M[s][a]]
        for a in a_list:
            for b in range(K):
                if abs(a - b) < 3 or not M[t][b]:
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
            M = meets_table(seq, K, [(0, 0)])
            for s0 in range(0, tt):
                if not pair_ok(seq, s0, tt, M):
                    return
        if L == n:
            if seq[-1] != (K - 2, K - 2):
                return
            out.append(list(seq))
            return
        for c in cells:
            p = seq[-1]
            if max(p[1], c[1]) > min(p[0], c[0]) + 1:
                continue
            seq.append(c)
            rec()
            seq.pop()
    rec()
    return out


def run(K, nmax, nmin=3, verbose=3):
    for n in range(nmin, nmax + 1):
        inst = some = every = 0
        kinds = {}
        shown = 0
        for inner in special_seqs(n, K):
            M = meets_table(inner, K, [(0, 0), (n - 1, K - 1)])
            if PADDED:
                # realizable inside the faithful model: the padded sequence (0,0) + inner + (K-1,K-1)
                # is crooked for its forced meetings, and the special-case chain is its subchain
                # 1..n (whose end links meet levels 0 and K-1 through the padding links)
                pad = [(0, 0)] + inner + [(K - 1, K - 1)]
                if not crooked(pad, K, meets_table(pad, K, [])):
                    continue
            # special case: no interior link meets level 0 or K-1 (automatic: all levels in 1..K-2
            # and the extra meetings are at the ends); crookedness with the extra meetings
            if not crooked(inner, K, M):
                continue
            for h in range(1, n - 1):
                if not (inner[h][0] <= K - 2 <= inner[h][1]):
                    continue
                for k in range(h + 1, n - 1):
                    if not (inner[k][0] <= 1 <= inner[k][1]):
                        continue
                    for i in range(0, h + 1):
                        Hs = all_H(inner, h, i, K, M)
                        if not Hs:
                            continue  # the induction hypothesis itself fails here: report
                        inst += 1
                        fails = []
                        for H in Hs:
                            F, u = construct_F(inner, K, h, k, H)
                            r = check_F(inner, K, i, F, M)
                            fails.append((r, H, F, u))
                        bad = [f for f in fails if f[0]]
                        if bad:
                            some += 1
                            for f in bad:
                                kinds[f[0]] = kinds.get(f[0], 0) + 1
                            if shown < verbose:
                                shown += 1
                                r, H, F, u = bad[0]
                                print(f"  SOME-FAIL K={K} n={n} rho={[c[0] for c in inner]} sig={[c[1] for c in inner]} "
                                      f"h={h} k={k} i={i} H={[H[t] for t in range(h + 1)]} u={u} F={F} kind={r}")
                        if len(bad) == len(fails):
                            every += 1
                            if every <= verbose: print(f"  EVERY-FAIL K={K} n={n} rho={[c[0] for c in inner]} sig={[c[1] for c in inner]} "
                                  f"h={h} k={k} i={i} (#H={len(fails)})")
        print(f"K={K} n={n}: instances={inst} some-H-fails={some} every-H-fails={every} kinds={kinds}")
        sys.stdout.flush()


if __name__ == "__main__":
    K = int(sys.argv[1])
    nmax = int(sys.argv[2])
    nmin = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    if len(sys.argv) > 4:
        GROUPING = sys.argv[4]
    if len(sys.argv) > 5:
        PADDED = sys.argv[5] == "padded"
    print(f"# padded (realized inside the faithful model): {PADDED}")
    print(f"# grouping reading {GROUPING}")
    run(K, nmax, nmin)
