#!/usr/bin/env python3
"""Batch 122, Q1: which H make Bing's special-case construction work, and which property P(H)
of the consolidation H separates them.

Coordinates and conventions as in seam-batch121.py (imported): fine links t = 0..n-1 (Bing's D),
coarse levels 0..K-1 (Bing's E, K = r), a fine link t lies in the coarse links rho t .. sig t.
Special-case instances (seq, h, k, i) with the basepoint i in D(0, h); the induction hypothesis
(IH) on D(0, h) inside E(0, K-2) is enumerated exhaustively (all_H of seam-batch121.py), and for
every IH-H the construction F is formed under reading Cbot (bingSpecialFCbot) and reading A
(bingSpecialF) and checked (check_F).

Candidate properties P(H) (0-indexed; u = H(h), the block of the end link d_h; "top" of
E(0, K-2) is the level K-2):
  a   d_h's block is the last block of H                         u = max H
  b   every link of h_{u-1} has sig >= K-4   (Bing: sigma >= r-3; vacuous if u = 0)
  c   a and b
  d   end-time form: for each end link e in {0, h} of D(0, h) meeting an extreme level L of
      E(0, K-2) (L = 0 for e = 0 by the extra meeting, L = K-2), H(e) is the largest time of a
      link of D(0, h) meeting L
  s   strict end clause for d_h: every link of h_u has rho >= K-3, i.e. no link of h_u lies in a
      coarse link below e_{K-3} (Bing: below e_{r-2})
  w   the exact working condition under Cbot, for reference: every link of D(0, h) at time u
      adjacent to a link at time u-1 is in the Cbot top group (rho >= 2 and sig >= K-3), and if
      u = 0 then d_i is in the top group

For each (K, n): instances; IH-H; and per candidate: #H with P, #H with P that fail under Cbot
("unsound"), #instances with no H with P ("unsat").  Also the corpus of special-case instances
inside Bing's chains P(0, KK-1) (all subchains, ends meeting the frame through their outer
neighbours).

Usage: recon-batch122-q1.py enum K nmin nmax   |   recon-batch122-q1.py bing KK
"""
import sys
import importlib.util
import os

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("seam121", os.path.join(here, "seam-batch121.py"))
S = importlib.util.module_from_spec(spec)
spec.loader.exec_module(S)

CANDS = ["a", "b", "c", "d", "s", "w"]


def prop(name, seq, K, h, i, H, M):
    u = H[h]
    times = [H[t] for t in range(h + 1)]
    if name == "a":
        return u == max(times)
    if name == "b":
        return u == 0 or all(seq[t][1] >= K - 4 for t in range(h + 1) if H[t] == u - 1)
    if name == "c":
        return prop("a", seq, K, h, i, H, M) and prop("b", seq, K, h, i, H, M)
    if name == "d":
        for (e, L) in ((0, 0), (h, K - 2), (0, K - 2), (h, 0)):
            if not M[e][L]:
                continue
            last = max(H[t] for t in range(h + 1) if M[t][L])
            if H[e] != last:
                return False
        return True
    if name == "s":
        return all(seq[t][0] >= K - 3 for t in range(h + 1) if H[t] == u)
    if name == "w":
        top = lambda t: seq[t][0] >= 2 and seq[t][1] >= K - 3
        for t in range(h + 1):
            if H[t] != u:
                continue
            for x in (t - 1, t + 1):
                if 0 <= x <= h and H[x] == u - 1 and not top(t):
                    return False
        if u == 0 and not top(i):
            return False
        return True
    raise ValueError(name)


def works(seq, K, h, k, i, H, M, grouping):
    S.GROUPING = grouping
    F, u = S.construct_F(seq, K, h, k, H)
    return S.check_F(seq, K, i, F, M) is None


class Tally:
    def __init__(self):
        self.inst = 0
        self.nH = 0
        self.workC = 0
        self.workA = 0
        self.inst_someC = 0
        self.inst_everyCfail = 0
        self.withP = {c: 0 for c in CANDS}
        self.unsound = {c: 0 for c in CANDS}
        self.unsat = {c: 0 for c in CANDS}
        self.first_unsound = {}
        self.first_unsat = {}

    def add(self, seq, K, h, k, i, Hs, M, listing=None):
        self.inst += 1
        self.nH += len(Hs)
        anyC = False
        haveP = {c: False for c in CANDS}
        rows = []
        for H in Hs:
            wc = works(seq, K, h, k, i, H, M, "Cbot")
            wa = works(seq, K, h, k, i, H, M, "A")
            self.workC += wc
            self.workA += wa
            anyC = anyC or wc
            ps = {}
            for c in CANDS:
                p = prop(c, seq, K, h, i, H, M)
                ps[c] = p
                if p:
                    self.withP[c] += 1
                    haveP[c] = True
                    if not wc:
                        self.unsound[c] += 1
                        self.first_unsound.setdefault(c, (seq, h, k, i, [H[t] for t in range(h + 1)]))
            rows.append(([H[t] for t in range(h + 1)], wc, wa, ps))
        self.inst_someC += anyC
        self.inst_everyCfail += (not anyC)
        for c in CANDS:
            if not haveP[c]:
                self.unsat[c] += 1
                self.first_unsat.setdefault(c, (seq, h, k, i))
        if listing is not None:
            listing.append((seq, h, k, i, rows))

    def report(self, label):
        print(f"{label}: instances={self.inst} IH-H={self.nH} working(Cbot)={self.workC} "
              f"working(A)={self.workA} inst-some-Cbot-works={self.inst_someC} "
              f"inst-every-Cbot-fails={self.inst_everyCfail}")
        for c in CANDS:
            print(f"   P={c}: H-with-P={self.withP[c]} unsound(H with P failing Cbot)={self.unsound[c]} "
                  f"unsat(instances with no H with P)={self.unsat[c]}")
            if c in self.first_unsound:
                seq, h, k, i, H = self.first_unsound[c]
                print(f"      e.g. unsound: rho={[x[0] for x in seq]} sig={[x[1] for x in seq]} h={h} k={k} i={i} H={H}")
            if c in self.first_unsat:
                seq, h, k, i = self.first_unsat[c]
                print(f"      e.g. unsat:   rho={[x[0] for x in seq]} sig={[x[1] for x in seq]} h={h} k={k} i={i}")
        sys.stdout.flush()


def instances_of(inner, K):
    """Special-case instances (h, k, i) with i in D(0, h), as in seam-batch121.run."""
    n = len(inner)
    M = S.meets_table(inner, K, [(0, 0), (n - 1, K - 1)])
    if not S.crooked(inner, K, M):
        return M, []
    out = []
    for h in range(1, n - 1):
        if not (inner[h][0] <= K - 2 <= inner[h][1]):
            continue
        for k in range(h + 1, n - 1):
            if not (inner[k][0] <= 1 <= inner[k][1]):
                continue
            for i in range(0, h + 1):
                out.append((h, k, i))
    return M, out


def run_enum(K, nmin, nmax, list_n=None):
    for n in range(nmin, nmax + 1):
        T = Tally()
        listing = [] if n == list_n else None
        nseq = 0
        for inner in S.special_seqs(n, K):
            M, insts = instances_of(inner, K)
            if insts:
                nseq += 1
            for (h, k, i) in insts:
                Hs = S.all_H(inner, h, i, K, M)
                if not Hs:
                    print(f"  IH FAILS?! rho={[c[0] for c in inner]} sig={[c[1] for c in inner]} h={h} i={i}")
                    continue
                T.add(inner, K, h, k, i, Hs, M, listing)
        T.report(f"K={K} n={n} (special-case sequences {nseq})")
        if listing is not None:
            print(f"# per-instance listing, K={K} n={n}: H (times of links 0..h), works under Cbot (C) / A (A), "
                  f"and the candidates holding")
            for (seq, h, k, i, rows) in listing:
                print(f"  rho={[x[0] for x in seq]} sig={[x[1] for x in seq]} h={h} k={k} i={i}: "
                      f"#H={len(rows)} withP(s)={sum(r[3]['s'] for r in rows)} working(C)={sum(r[1] for r in rows)}")
                for (H, wc, wa, ps) in rows:
                    print(f"      H={H} C={int(wc)} A={int(wa)} P={''.join(c for c in CANDS if ps[c])}")


def bing_path(a, b):
    d = abs(b - a)
    if d <= 2:
        s = 1 if a <= b else -1
        return [a + s * u for u in range(d + 1)]
    mid = b - 1 if a < b else b + 1
    c = a + 1 if a < b else a - 1
    p1, p2, p3 = bing_path(a, mid), bing_path(mid, c), bing_path(c, b)
    return p1 + p2[1:] + p3[1:]


def run_bing(KK):
    """Special-case instances inside Bing's chain P(0, KK-1): a subchain l..r and a frame [a, b]
    with P[l-1] = a, P[r+1] = b (or reversed), every link of the subchain in a+1..b-1 and no
    interior link adjacent to a link at level a or b.  Reversed instances are mirrored so that the
    first link meets the bottom level."""
    P = bing_path(0, KK - 1)
    N = len(P)
    tallies = {}
    nsub = 0
    for l in range(1, N - 1):
        for r in range(l + 2, N - 1):
            a0, b0 = P[l - 1], P[r + 1]
            if abs(a0 - b0) < 4:
                continue
            sub = P[l:r + 1]
            lo, hi = min(a0, b0), max(a0, b0)
            if min(sub) <= lo or max(sub) >= hi:
                continue
            # interior links must not meet lo or hi: no interior link adjacent to level lo/hi
            # (inside the subchain, links are in lo+1..hi-1, so only the outer neighbours matter)
            if a0 < b0:
                levels = [x - lo for x in sub]
            else:
                levels = [hi - x for x in sub]  # mirror so that link 0 meets level 0
            K = hi - lo + 1
            inner = [(x, x) for x in levels]
            if inner[0] != (1, 1) or inner[-1] != (K - 2, K - 2):
                continue
            M, insts = instances_of(inner, K)
            if not insts:
                continue
            nsub += 1
            T = tallies.setdefault((K, len(inner)), Tally())
            for (h, k, i) in insts:
                Hs = S.all_H(inner, h, i, K, M)
                if not Hs:
                    print(f"  IH FAILS?! levels={levels} h={h} i={i}")
                    continue
                T.add(inner, K, h, k, i, Hs, M)
    print(f"# Bing chain P(0, {KK - 1}), length {N}: special-case subchains {nsub}")
    for key in sorted(tallies):
        tallies[key].report(f"bing KK={KK} K={key[0]} n={key[1]}")


if __name__ == "__main__":
    if sys.argv[1] == "enum":
        K, nmin, nmax = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        list_n = int(sys.argv[5]) if len(sys.argv) > 5 else None
        run_enum(K, nmin, nmax, list_n)
    else:
        run_bing(int(sys.argv[2]))
