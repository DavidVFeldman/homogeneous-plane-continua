"""seam-batch56.py -- batch 56, COMMISSION.md section 2.3: Bing's seam under the
induction's own hypothesis.

Batch 55 ran the construction of p. 733 with `H` any width-two consolidation of
`D(h, k)` **with respect to `E`**, found by search, and the construction went
through at all 84 basepoints of `bing 0 4`, `bing 0 5`, `bing 0 6`: `F` a chain,
`d_i` in the first link only, seam width two.  The commission observes that this
is not what Bing's induction supplies.  His induction is on the number of links
of `E`, so the consolidation the hypothesis supplies is of a chain crooked in the
*shorter* chain `E(2, m-1) = [e_2, ..., e_{m-1}]`, and it consolidates only the
part of `D(h, k)` that lies in that shorter chain: the two end links of
`D(h, k)`, which meet `e_1` or `e_m`, are outside it and are attached at the
regroup.  A block of such an `H` lies in two adjacent links of `E(2, m-1)`, so
in terms of `E` it may reach from `e_2` to `e_3`; attaching the end link of
`D(h, k)`, which lies in `e_1`, then gives a block spanning `e_1`, `e_2`, `e_3`.

That is the prediction this program tests, now aimed at the right object:

    a seam of width three exactly when the block of `H` containing the inner end
    link reaches one link past the extreme.

Two passes, as the commission asks.

  (a) the thin model, on `bing 0 4`, `bing 0 5`, `bing 0 6`: `H` is a width-two
      consolidation of the interior `D(h+1, k-1)` with respect to `E(2, m-1)`
      -- every block inside two adjacent links of the shorter chain -- with
      `d_i` in the first block; the end links `h` and `k` are then attached to
      the blocks of their neighbours, and the regroup of p. 733 is carried out
      on the result.

  (b) the general model, on single shavings of `bing 0 6` and `bing 0 7` (the
      first six and the first three, the run being quadratic in the length): a
      link is an interval `[rho, sig]` of levels with `sig <= rho + 1`, so it may
      straddle two links of `E`.  Everything else is as in (a).

Reported per basepoint, as in batch 55: the blocks of `H` and their widths; `u`,
the first block of `F`'s head meeting `e_1` or `e_m`, and which end; whether `F`
is a chain; whether `d_i` lies in the first link of `F` only; the widths of the
blocks of `F`; and the width of the seam block -- the group that receives the
links of `h_u`.

Usage: python3 seam-batch56.py [maxblocks]
"""

import itertools
import sys


# ---------------------------------------------------------------- the chains

def bpath(a, b):
    """Bing's recursive pattern from level a to level b (the census's bpath)."""
    d = abs(a - b)
    if d <= 2:
        s = 1 if a <= b else -1
        return [a + s * u for u in range(d + 1)]
    mid = b - 1 if a < b else b + 1
    c = a + 1 if a < b else a - 1
    return bpath(a, mid) + bpath(mid, c)[1:] + bpath(c, b)[1:]


# --------------------------------------------- links, blocks, chains (general)
#
# A link j is the interval [rho[j], sig[j]] of levels of E, with sig <= rho + 1;
# the thin model is sig = rho.  Two links of D meet exactly when their indices
# differ by at most one.

def is_chain(blocks):
    """The block sequence is a chain: blocks p and q meet exactly when
    |p - q| <= 1, and every block is nonempty."""
    s = len(blocks)
    if any(len(B) == 0 for B in blocks):
        return False
    for p in range(s):
        for q in range(p, s):
            meet = any(abs(x - y) <= 1 for x in blocks[p] for y in blocks[q])
            if meet != (abs(p - q) <= 1):
                return False
    return True


def widths(blocks, rho, sig):
    return [max(sig[j] for j in B) - min(rho[j] for j in B) + 1 for B in blocks]


def meets_low(rho, sig, j):
    return rho[j] == 0


def meets_high(rho, sig, j, m):
    return sig[j] == m - 1


# ------------------- the inductive consolidation of the *inner* chain, by search

def fold_blocks(rho, sig, lo, hi, i, c, width=2):
    """Is there an assignment of the links lo..hi to blocks with d_i in block 0,
    at most one block of movement per link, and every block used?  Block p holds
    the levels c_p .. c_p+width-1, and a link is served by a block only if its
    whole interval fits in the block's window."""
    s = len(c)
    full = (1 << s) - 1

    def serve(j, p):
        return c[p] <= rho[j] and sig[j] <= c[p] + width - 1

    if not serve(i, 0):
        return None
    memo = {}

    def go(j, p, mask, d):
        key = (j, p, mask, d)
        if key in memo:
            return memo[key]
        res = None
        if d == 1 and j == hi:
            res = go(i, 0, mask, -1)
        elif d == -1 and j == lo:
            res = [] if mask == full else None
        else:
            nj = j + d
            for q in (p + 1, p, p - 1):
                if 0 <= q < s and serve(nj, q):
                    r = go(nj, q, mask | (1 << q), d)
                    if r is not None:
                        res = [(nj, q)] + r
                        break
        memo[key] = res
        return res

    path = go(i, 0, 1, 1) if i < hi else go(i, 0, 1, -1)
    if path is None:
        return None
    b = {i: 0}
    for (j, q) in path:
        b[j] = q
    blocks = [[] for _ in range(s)]
    for j in range(lo, hi + 1):
        blocks[b[j]].append(j)
    return blocks


def inner_consolidations(rho, sig, lo, hi, i, maxblocks, width=2):
    """All consolidations of the inner chain D(lo, hi) -- every link inside
    E(2, m-1), that is at levels 1 .. m-2 -- into blocks of width `width` with
    respect to that shorter chain, with d_i in the first block, of the least
    possible number of blocks."""
    m = max(sig) + 1
    # a block's window must lie inside the shorter chain E(2, m-1): levels 1..m-2
    wins = [c for c in range(1, m - width) if c + width - 1 <= m - 2]
    if not wins:
        return None, []
    for s in range(1, maxblocks + 1):
        found = []
        for c in itertools.product(wins, repeat=s):
            if any(abs(c[p + 1] - c[p]) > width for p in range(s - 1)):
                continue
            H = fold_blocks(rho, sig, lo, hi, i, c, width)
            if H is None:
                continue
            found.append((c, H))
        if found:
            return s, found
    return None, []


def attach_ends(H, h, k, lo, hi):
    """Attach the end links of D(h, k) -- the links h and k, which meet e_1 or
    e_m and so lie outside E(2, m-1) -- to the blocks of their neighbours, which
    is where the regroup puts them."""
    H = [list(B) for B in H]
    for (end, nb) in ((h, lo), (k, hi)):
        if end == nb:
            continue
        for B in H:
            if nb in B:
                B.append(end)
                break
    for B in H:
        B.sort()
    return H


# ------------------------------------------------------------ the seam step

def seam_from(rho, sig, i, H, keep_hu=False):
    """Bing's seam step, given the consolidation H of D(h, k)."""
    n = len(rho)
    m = max(sig) + 1
    out = {}
    out["Hwidths"] = widths(H, rho, sig)
    out["Hchain"] = is_chain(H)

    u = None
    for p, B in enumerate(H):
        if any(meets_low(rho, sig, j) or meets_high(rho, sig, j, m) for j in B):
            u = p
            break
    out["u"] = None if u is None else u + 1
    if u is None:
        return out
    metlow = any(meets_low(rho, sig, j) for j in H[u])
    out["end"] = "e_1" if metlow else "e_m"
    out["hu_levels"] = sorted({l for j in H[u] for l in range(rho[j], sig[j] + 1)})
    out["hu_ok"] = (max(out["hu_levels"]) <= 1) if metlow else (min(out["hu_levels"]) >= m - 2)

    head = [list(B) for B in H[:(u + 1 if keep_hu else u)]]
    used = {j for B in head for j in B}
    rest = [j for j in range(n) if j not in used]

    if metlow:
        groups = [[j for j in rest if sig[j] <= 1]]
        for l in range(2, m - 2):
            groups.append([j for j in rest if rho[j] <= l <= sig[j] and sig[j] <= l])
        groups.append([j for j in rest if rho[j] >= m - 2])
    else:
        groups = [[j for j in rest if rho[j] >= m - 2]]
        for l in range(m - 3, 1, -1):
            groups.append([j for j in rest if rho[j] <= l <= sig[j] and sig[j] <= l])
        groups.append([j for j in rest if sig[j] <= 1])
    placed = {j for g in groups for j in g}
    leftover = [j for j in rest if j not in placed]
    if leftover:
        # links straddling two links of E that no single level group receives:
        # they go with the lower of the two, as the regroup reads them
        for j in leftover:
            for g in groups:
                if any(abs(j - x) <= 1 for x in g):
                    g.append(j)
                    break
            else:
                groups.append([j])
    for g in groups:
        g.sort()

    groups = [g for g in groups if g]
    F = head + groups
    out["F"] = F
    out["Fwidths"] = widths(F, rho, sig)
    out["Fchain"] = is_chain(F)
    out["seam"] = len(head)
    out["seamwidth"] = out["Fwidths"][len(head)] if len(head) < len(F) else None
    out["di_first_only"] = (i in F[0]) and all(i not in B for B in F[1:])
    return out


def dhk(rho, sig, i):
    """D(h, k): the maximal interval around i with no interior link meeting e_1
    or e_m."""
    n = len(rho)
    m = max(sig) + 1
    h = 0
    for j in range(i, -1, -1):
        if meets_low(rho, sig, j) or meets_high(rho, sig, j, m):
            h = j
            break
    k = n - 1
    for j in range(i, n):
        if meets_low(rho, sig, j) or meets_high(rho, sig, j, m):
            k = j
            break
    return h, k


# ------------------------------------------------------------------- driver

def report_basepoint(rho, sig, i, maxblocks, width, w, verbose=False):
    h, k = dhk(rho, sig, i)
    lo, hi = h, k
    m = max(sig) + 1
    if meets_low(rho, sig, h) or meets_high(rho, sig, h, m):
        lo = h + 1
    if meets_low(rho, sig, k) or meets_high(rho, sig, k, m):
        hi = k - 1
    if not (lo <= i <= hi):
        w("  %3d %3d  [%2d,%2d]   -- the basepoint is an end link of D(h,k)\n"
          % (i, rho[i], h, k))
        return None
    s, fam = inner_consolidations(rho, sig, lo, hi, i, maxblocks, width)
    if s is None:
        w("  %3d %3d  [%2d,%2d]   -- no consolidation of the inner chain of width %d "
          "with at most %d blocks\n" % (i, rho[i], h, k, width, maxblocks))
        return None
    full = [(c, attach_ends(H, h, k, lo, hi)) for (c, H) in fam]
    res = [seam_from(rho, sig, i, H) for (_, H) in full]
    rep = [seam_from(rho, sig, i, H, keep_hu=True) for (_, H) in full]
    res = [r for r in res if r.get("u") is not None] or res
    r0, p0 = res[0], rep[0]
    r0["i"], r0["h"], r0["k"], r0["s"], r0["nH"] = i, h, k, s, len(fam)
    r0["H0"] = full[0][1]
    r0["c0"] = full[0][0]
    r0["seams_all"] = sorted({x["seamwidth"] for x in res if x.get("seamwidth") is not None})
    r0["allchain"] = all(x.get("Fchain") for x in res)
    r0["allgood_hu"] = all(x.get("hu_ok", False) for x in res)
    r0["maxw_all"] = max((max(x["Fwidths"]) for x in res if x.get("F")), default=0)
    r0["rep"] = p0
    good2 = [x for x in res if x.get("u") is not None and x["u"] >= 2 and x.get("F")]
    r0["has_u2"] = bool(good2)
    if good2:
        r0["u2_chain"] = all(x["Fchain"] for x in good2)
        r0["u2_any_chain"] = any(x["Fchain"] for x in good2)
        r0["u2_di"] = any(x["di_first_only"] for x in good2)
        r0["u2_seams"] = sorted({x["seamwidth"] for x in good2})
    if not r0.get("F"):
        w("  %3d %3d  [%2d,%2d] %3d  -- no block of H meets e_1 or e_m\n"
          % (i, rho[i], h, k, s))
        return r0
    w("  %3d %3d  [%2d,%2d] %3d  %-10s %4d %3d  %-4s %-8s %-4s %-6s %-6s %-16s %-6s %-9s %-6s %s\n"
      % (i, rho[i], h, k, s, "".join(str(x) for x in r0["Hwidths"]), len(fam),
         r0["u"], r0["end"], ",".join(str(l) for l in r0["hu_levels"]),
         "yes" if r0["hu_ok"] else "NO",
         "yes" if r0["Fchain"] else "NO",
         "yes" if r0["di_first_only"] else "NO",
         "".join(str(x) for x in r0["Fwidths"]), r0["seamwidth"],
         ",".join(str(x) for x in r0["seams_all"]),
         ("yes" if p0["Fchain"] else "NO") if p0.get("F") else "--",
         p0.get("seamwidth")))
    if verbose:
        w("      c = %s\n" % (r0["c0"],))
        w("      H (end links attached) = %s\n" % (r0["H0"],))
        w("      F = %s\n" % (r0["F"],))
        w("      F' (h_u kept in the head) = %s, widths %s, chain %s\n"
          % (p0.get("F"), p0.get("Fwidths"), p0.get("Fchain")))
    return r0


HDR = ("    i lev  D(h,k)    s  H widths    #H   u  end  h_u lev  h_u  F      d_i    "
       "F widths         seam   seam all  F' ch  F' seam\n")


def run(name, rho, sig, maxblocks, width, out, verbose_at=()):
    n = len(rho)
    m = max(sig) + 1
    w = out.write
    w("=" * 118 + "\n")
    w("%s, H a width-%d consolidation of the inner chain in E(2, m-1) : %d links, "
      "E has %d links\n" % (name, width, n, m))
    w("  rho %s\n" % (rho,))
    if sig != rho:
        w("  sig %s\n" % (sig,))
    bases = [i for i in range(n) if rho[i] >= 2 and sig[i] <= m - 3]
    if not bases:
        w("  no basepoint has d_i outside e_1 u e_2 and e_{m-1} u e_m\n\n")
        return []
    w("  %d basepoints (d_i outside e_1 u e_2 and outside e_{m-1} u e_m)\n\n" % len(bases))
    w(HDR)
    w("  " + "-" * 116 + "\n")
    rows = []
    for i in bases:
        r = report_basepoint(rho, sig, i, maxblocks, width, w, verbose=(i in verbose_at))
        rows.append(r if r is not None else {"i": i, "H": None})
    good = [r for r in rows if r and r.get("F")]
    w("\n  summary for %s: %d basepoints, %d with a consolidation of the inner chain.\n"
      % (name, len(bases), len(good)))
    if good:
        w("    h_u inside the two end links of E at %d of %d (at every least "
          "consolidation at %d);\n"
          % (sum(1 for r in good if r["hu_ok"]), len(good),
             sum(1 for r in good if r["allgood_hu"])))
        w("    F is a chain at %d of %d (at every least consolidation at %d);\n"
          % (sum(1 for r in good if r["Fchain"]), len(good),
             sum(1 for r in good if r["allchain"])))
        w("    d_i in the first link of F only at %d of %d;\n"
          % (sum(1 for r in good if r["di_first_only"]), len(good)))
        w("    widest block of F: %d; over all least consolidations: %d;\n"
          % (max(max(r["Fwidths"]) for r in good), max(r["maxw_all"] for r in good)))
        w("    seam widths: %s; over all least consolidations: %s;\n"
          % (sorted({r["seamwidth"] for r in good}),
             sorted({x for r in good for x in r["seams_all"]})))
        w("    of the seams of width three: %d of %d.\n"
          % (sum(1 for r in good if r["seamwidth"] == 3), len(good)))
        u2 = [r for r in good if r.get("has_u2")]
        w("    a least consolidation with a non-empty head (u >= 2) exists at %d of %d;\n"
          % (len(u2), len(good)))
        if u2:
            w("      of those: F a chain at some such %d, at all %d; d_i first only at some "
              "%d; seam widths %s.\n"
              % (sum(1 for r in u2 if r["u2_any_chain"]),
                 sum(1 for r in u2 if r["u2_chain"]),
                 sum(1 for r in u2 if r["u2_di"]),
                 sorted({x for r in u2 for x in r["u2_seams"]})))
    w("\n")
    return rows


def shavings(v):
    """The single shavings of a thin chain: one interior peak read one level
    lower, so that the link straddles two links of E."""
    out = []
    for pk in range(1, len(v) - 1):
        if v[pk] > v[pk - 1] and v[pk] > v[pk + 1]:
            rho = list(v)
            sig = list(v)
            rho[pk] = v[pk] - 1
            out.append((pk, rho, sig))
    return out


def main():
    maxblocks = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    sys.setrecursionlimit(100000)
    out = sys.stdout
    out.write("Bing's seam under the induction's own hypothesis (COMMISSION.md sec. 2.3); "
              "consolidations of at most %d blocks.\n" % maxblocks)
    out.write("H is a width-two consolidation of the inner chain D(h+1, k-1) with respect "
              "to E(2, m-1);\n")
    out.write("the end links of D(h, k), which meet e_1 or e_m, are attached to their "
              "neighbours' blocks at the regroup.\n\n")

    out.write("### (a) the thin model\n\n")
    thin = []
    for (a, b) in [(0, 4), (0, 5), (0, 6)]:
        v = bpath(a, b)
        thin += run("bing %d %d" % (a, b), v, list(v), maxblocks, 2, out,
                    verbose_at=((6,) if (a, b) == (0, 4) else ()))

    out.write("### (b) the general model: single shavings\n\n")
    gen = []
    for (a, b, howmany) in [(0, 6, 6), (0, 7, 3)]:
        v = bpath(a, b)
        for (pk, rho, sig) in shavings(v)[:howmany]:
            gen += run("bing %d %d shaved at %d" % (a, b, pk), rho, sig, maxblocks, 2, out)

    out.write("=" * 118 + "\n")
    for (nm, rows) in [("thin: bing 0 4, 0 5, 0 6", thin),
                       ("general: the first single shavings of bing 0 6 and bing 0 7", gen)]:
        good = [r for r in rows if r and r.get("F")]
        out.write("TOTAL, %s: %d basepoints, %d with a consolidation of the inner chain.\n"
                  % (nm, len(rows), len(good)))
        if not good:
            continue
        out.write("  h_u inside the two end links of E: %d; F a chain: %d; "
                  "d_i in the first link only: %d;\n"
                  % (sum(1 for r in good if r["hu_ok"]),
                     sum(1 for r in good if r["Fchain"]),
                     sum(1 for r in good if r["di_first_only"])))
        out.write("  blocks of F of width three or more: %d; seam widths: %s "
                  "(over all least consolidations: %s);\n"
                  % (sum(1 for r in good if max(r["Fwidths"]) >= 3),
                     sorted({r["seamwidth"] for r in good}),
                     sorted({x for r in good for x in r["seams_all"]})))
        out.write("  seams of width three: %d of %d; of width two: %d.\n"
                  % (sum(1 for r in good if r["seamwidth"] == 3), len(good),
                     sum(1 for r in good if r["seamwidth"] == 2)))
        out.write("  repaired F' (h_u kept a block of F): chain at %d of %d, "
                  "seam widths %s.\n"
                  % (sum(1 for r in good if r["rep"].get("Fchain")), len(good),
                     sorted({r["rep"].get("seamwidth") for r in good})))


if __name__ == "__main__":
    main()
