"""seam-batch55.py -- batch 55, COMMISSION.md section 3: Bing's seam.

The construction of p. 733, run in the thin model of this repository.

Model.  A chain D following a pattern in E = [e_1, ..., e_m] is the sequence rho
of its levels: the link d_j lies in e_{rho[j]+1} (levels are 0-based here, so
level l is Bing's e_{l+1}).  Two links of D meet exactly when their indices
differ by at most one.  `bing a b` is the pattern of Bing's recursive chain from
level a to level b -- the same `bpath` the censuses of this repository use.

A consolidation of D is a partition of its links into blocks whose sequence is
again a chain.  Because consecutive links of D meet, the block index b[j] moves
by at most one per link; because non-consecutive blocks must not meet, that is
also sufficient, provided every block is nonempty.  A block lies "in two
adjacent links of E" when the levels of its links span at most two consecutive
values; its *width* is that span, measured in links of E.

The construction, as COMMISSION.md sec. 3 quotes it:

    Let D be crooked in E = [e_1, ..., e_m], d_i a link of D, m > 4,
    d_i not in e_1 u e_2, d_i not in e_{m-1} u e_m.  Take D(h, k) maximal
    containing d_i with no interior link meeting e_1 or e_m.  By induction,
    H = [h_1, ..., h_s] is a consolidation of D(h, k) with d_i in h_1 only and
    every h_j in two adjacent links.  Let h_u be the first link of H meeting
    e_1 u e_m; say it meets e_1, so h_u is in e_1 u e_2.  Then F is H(1, u-1)
    followed by the remaining links of D grouped as: those in e_1 u e_2; those
    in e_3 not in e_2; ...; those in e_{m-1} u e_m.

The inductive consolidation H is supplied here by exhaustive search, which the
commission allows ("any correct source"): every block is given a pair of
adjacent levels {c_p, c_p+1}, and the program searches for an assignment of the
links of D(h, k) to blocks with d_i in the first block, moving by at most one
block per link and using every block.  Since consolidations are not unique, the
program takes the *fewest* blocks and then reports the whole family at that
size: the first one in the search order in detail, and the range of seam widths
over all of them.

Reported per basepoint:
  * whether H exists, the number of blocks and their widths;
  * u, the first block of H meeting e_1 or e_m, which end it meets, and the
    levels of h_u;
  * whether the assembled F is a chain;
  * whether d_i lies in the first link of F only;
  * the width in links of every block of F, and the width of the seam block --
    the group that receives the links of h_u.

Two sources of H are run, because the commission allows either.

  (a) width two, Bing's own inductive hypothesis: every h_j in two adjacent
      links of E.
  (b) width three, which is what a fold of this repository supplies: an
      itinerary onto a walk c puts the link at level l at a position with
      |l - c_p| <= 1, so a block spans three links of E.  Under (b) the first
      block of H meeting e_1 need not be inside e_1 u e_2, and the seam is
      where the prediction of the commission lives.  Both the construction as
      written (h_u's links fall into the level groups) and the repair that
      keeps h_u in the head, F' = H(1, u) followed by the groups, are assembled
      and checked.

Usage: python3 seam-batch55.py [maxblocks]
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


# ------------------------------------------------------- chains and blocks

def is_chain(blocks):
    """The block sequence is a chain: blocks p and q meet -- some link of one is
    equal or adjacent to a link of the other -- exactly when |p - q| <= 1, and
    every block is nonempty."""
    s = len(blocks)
    if any(len(B) == 0 for B in blocks):
        return False
    for p in range(s):
        for q in range(p, s):
            meet = any(abs(x - y) <= 1 for x in blocks[p] for y in blocks[q])
            if meet != (abs(p - q) <= 1):
                return False
    return True


def widths(blocks, rho):
    return [max(rho[j] for j in B) - min(rho[j] for j in B) + 1 for B in blocks]


# ------------------------------------- the inductive consolidation H, by search

def fold_blocks(rho, lo, hi, i, c, width=2):
    """Given the block levels c (block p holds the levels c_p .. c_p+width-1), is
    there an assignment of the links lo..hi to blocks with d_i in block 0, at
    most one block of movement per link, and every block used?  Returns the
    blocks."""
    s = len(c)
    full = (1 << s) - 1

    def serve(l, p):
        return c[p] <= l <= c[p] + width - 1

    if not serve(rho[i], 0):
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
                if 0 <= q < s and serve(rho[nj], q):
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


def first_end_block(rho, H):
    """u, 1-based: the first block of H meeting e_1 or e_m."""
    m = max(rho) + 1
    for p, B in enumerate(H):
        if any(rho[j] in (0, m - 1) for j in B):
            return p + 1
    return None


def all_consolidations(rho, lo, hi, i, maxblocks, width=2, minu=1):
    """All consolidations of D(lo,hi) of width at most `width` with d_i in the
    first block only and with u at least `minu`, of the least possible number of
    blocks.  (s, list)."""
    m = max(rho) + 1
    lev = max(1, m - width + 1)
    for s in range(1, maxblocks + 1):
        found = []
        for c in itertools.product(range(0, lev), repeat=s):
            # consecutive blocks meet, so their level windows are close
            if any(abs(c[p + 1] - c[p]) > width for p in range(s - 1)):
                continue
            H = fold_blocks(rho, lo, hi, i, c, width)
            if H is None:
                continue
            u = first_end_block(rho, H)
            if u is None or u < minu:
                continue
            found.append((c, H))
        if found:
            return s, found
    return None, []


# ------------------------------------------------------------ the seam step

def seam_from(rho, i, H, keep_hu=False):
    """Bing's seam step, given the inductive consolidation H of D(h, k).  With
    `keep_hu` the repaired variant is assembled instead: the head is H(1, u),
    so that h_u stays a block of F."""
    n = len(rho)
    m = max(rho) + 1
    out = {}
    out["Hwidths"] = widths(H, rho)
    out["Hchain"] = is_chain(H)

    u = None
    for p, B in enumerate(H):
        if any(rho[j] in (0, m - 1) for j in B):
            u = p
            break
    out["u"] = None if u is None else u + 1          # 1-based, as in the text
    if u is None:
        return out
    metlow = any(rho[j] == 0 for j in H[u])
    out["end"] = "e_1" if metlow else "e_m"
    out["hu_levels"] = sorted({rho[j] for j in H[u]})
    out["hu_ok"] = (max(out["hu_levels"]) <= 1) if metlow else (min(out["hu_levels"]) >= m - 2)

    head = [list(B) for B in H[:(u + 1 if keep_hu else u)]]
    used = {j for B in head for j in B}
    rest = [j for j in range(n) if j not in used]

    if metlow:
        groups = [[j for j in rest if rho[j] <= 1]]
        for l in range(2, m - 2):
            groups.append([j for j in rest if rho[j] == l])
        groups.append([j for j in rest if rho[j] >= m - 2])
    else:
        groups = [[j for j in rest if rho[j] >= m - 2]]
        for l in range(m - 3, 1, -1):
            groups.append([j for j in rest if rho[j] == l])
        groups.append([j for j in rest if rho[j] <= 1])

    groups = [g for g in groups if g]
    F = head + groups
    out["F"] = F
    out["Fwidths"] = widths(F, rho)
    out["Fchain"] = is_chain(F)
    out["seam"] = len(head)                           # 0-based index in F
    out["seamwidth"] = out["Fwidths"][len(head)] if len(head) < len(F) else None
    out["di_first_only"] = (i in F[0]) and all(i not in B for B in F[1:])
    return out


def dhk(rho, i):
    """D(h, k): the maximal interval around i with no interior link at e_1 or e_m."""
    n = len(rho)
    m = max(rho) + 1
    h = 0
    for j in range(i, -1, -1):
        if rho[j] == 0 or rho[j] == m - 1:
            h = j
            break
    k = n - 1
    for j in range(i, n):
        if rho[j] == 0 or rho[j] == m - 1:
            k = j
            break
    return h, k


# ------------------------------------------------------------------- driver

def report_basepoint(rho, i, maxblocks, width, w, verbose=False, minu=1):
    """One row of the table, for the given source of H."""
    h, k = dhk(rho, i)
    s, fam = all_consolidations(rho, h, k, i, maxblocks, width, minu)
    if s is None:
        w("  %3d %3d  [%2d,%2d]   -- no consolidation of width %d with at most %d blocks "
          "and u >= %d\n" % (i, rho[i], h, k, width, maxblocks, minu))
        return None
    res = [seam_from(rho, i, H) for (_, H) in fam]
    rep = [seam_from(rho, i, H, keep_hu=True) for (_, H) in fam]
    r0, p0 = res[0], rep[0]
    r0["i"], r0["h"], r0["k"], r0["s"], r0["nH"] = i, h, k, s, len(fam)
    r0["H0"] = fam[0][1]
    r0["c0"] = fam[0][0]
    r0["seams_all"] = sorted({x["seamwidth"] for x in res if x.get("seamwidth") is not None})
    r0["allchain"] = all(x.get("Fchain") for x in res)
    r0["anybad_hu"] = any(not x.get("hu_ok", True) for x in res)
    r0["allgood_hu"] = all(x.get("hu_ok", False) for x in res)
    r0["maxw_all"] = max(max(x["Fwidths"]) for x in res if x.get("F"))
    r0["rep"] = p0
    r0["rep_seams_all"] = sorted({x["seamwidth"] for x in rep if x.get("seamwidth") is not None})
    r0["rep_allchain"] = all(x.get("Fchain") for x in rep)
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
        w("      H = %s\n" % (r0["H0"],))
        w("      F = %s\n" % (r0["F"],))
        w("      F' (h_u kept in the head) = %s, widths %s, chain %s\n"
          % (p0.get("F"), p0.get("Fwidths"), p0.get("Fchain")))
    return r0


HDR = ("    i lev  D(h,k)    s  H widths    #H   u  end  h_u lev  h_u  F      d_i    "
       "F widths         seam   seam all  F' ch  F' seam\n")


def run(name, rho, maxblocks, width, out, verbose_at=(), minu=1):
    n = len(rho)
    m = max(rho) + 1
    w = out.write
    w("=" * 118 + "\n")
    w("%s, H of width %d, u >= %d : %d links, E has %d links\n"
      % (name, width, minu, n, m))
    w("  pattern %s\n" % (rho,))
    bases = [i for i in range(n) if rho[i] not in (0, 1, m - 2, m - 1)]
    if not bases:
        w("  no basepoint has d_i outside e_1 u e_2 and e_{m-1} u e_m\n\n")
        return []
    w("  %d basepoints (d_i outside e_1 u e_2 and outside e_{m-1} u e_m)\n\n" % len(bases))
    w(HDR)
    w("  " + "-" * 116 + "\n")
    rows = []
    for i in bases:
        r = report_basepoint(rho, i, maxblocks, width, w, verbose=(i in verbose_at), minu=minu)
        rows.append(r if r is not None else {"i": i, "H": None})
    good = [r for r in rows if r.get("F")]
    w("\n  summary for %s, H of width %d: %d basepoints, %d with a consolidation.\n"
      % (name, width, len(bases), len(good)))
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
        w("    repaired F' (h_u kept): chain at %d of %d, seam widths %s.\n"
          % (sum(1 for r in good if r["rep"].get("Fchain")), len(good),
             sorted({r["rep"].get("seamwidth") for r in good})))
    w("\n")
    return rows


def main():
    maxblocks = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    sys.setrecursionlimit(100000)
    out = sys.stdout
    out.write("Bing's seam (COMMISSION.md sec. 3), thin model; consolidations of at "
              "most %d blocks.\n" % maxblocks)
    out.write("Columns: s = blocks of H; #H = consolidations of that least size; "
              "u and h_u as in the text;\n")
    out.write("  'h_u' = is h_u inside e_1 u e_2 (resp. e_{m-1} u e_m); 'F' = is F a chain; "
              "'d_i' = d_i in the first link only;\n")
    out.write("  'seam' = width of the block of F that receives h_u's links; "
              "F' = the repair that keeps h_u a block of F.\n\n")
    passes = [(2, 1), (3, 1), (3, 2)]
    totals = {}
    for (width, minu) in passes:
        allrows = []
        for (a, b) in [(0, 4), (0, 5), (0, 6)]:
            allrows += run("bing %d %d" % (a, b), bpath(a, b), maxblocks, width, out,
                           verbose_at=((6,) if (a, b) == (0, 4) else ()), minu=minu)
        totals[(width, minu)] = allrows
    out.write("=" * 118 + "\n")
    for (width, minu) in passes:
        allrows = totals[(width, minu)]
        good = [r for r in allrows if r.get("F")]
        out.write("TOTAL, H of width %d, u >= %d: %d basepoints, %d with a consolidation.\n"
                  % (width, minu, len(allrows), len(good)))
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
        out.write("  repaired F': chain at %d of %d, seam widths %s.\n"
                  % (sum(1 for r in good if r["rep"].get("Fchain")), len(good),
                     sorted({r["rep"].get("seamwidth") for r in good})))


if __name__ == "__main__":
    main()
