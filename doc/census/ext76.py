#!/usr/bin/env python3
"""ext76.py -- ExtendsSubBand at the stored witnesses, and the independent
re-check of the batch-76 census's written-out basepoints.

Shares no code with census-batch76.c.  Every predicate is written again from its
Lean definition (HPC/Fold/Target76.lean, HPC/Fold/Itinerary.lean,
HPC/Fold/LandList.lean):

  walkList s ts, walkLen s ts   the walk through a list of turning levels.
  FoldsOnto f len c             decided by forward propagation of the set of
                                reachable walk times, as a Python set.
  truncArm f L' H'              the longest prefix of f whose levels lie in
                                [L', H'].
  ExtendsSubBand rho i L H k    there are L <= L' <= rho i <= H' <= H with
                                H' - L' <= H - L - 3, s in [L', H'], a list ts
                                of k - 1 levels of [L', H'], e in {L+1, H-1}
                                with e != last (s :: ts), such that walk s ts
                                folds both truncated arms and walk s (ts ++ [e])
                                folds both whole arms.

The search here is LITERAL in the band: every (L', H') is tried, and for each
every alternating target list of at most k - 1 legs in [L', H'] (a list of k - 1
levels differs from its normalisation -- repeats dropped, monotone runs merged --
by nothing the walk sees, and the normalised list is padded back to length
k - 1 with copies of its last level for the Lean statement).

Modes:
  python3 ext76.py least  FILE...    least leg count (walks with targets in
                                     [L+1, H-1], directions alternating) and an
                                     ExtendsSubBand witness at that count, in the
                                     form the Lean file consumes.
  python3 ext76.py q2 FILE...        re-check a written-out basepoint of the
                                     census's section 2.2 (the suffix test).
  python3 ext76.py q2all FILE...     the same over EVERY ExtendsSubBand witness at
                                     the file's k (literal: every sub-band, minimal
                                     or not) and every arrival time.
  python3 ext76.py extk FILE...      ExtendsSubBand at the k recorded in the file
                                     (no least-leg search).
"""

import sys


def read_pair(path):
    lines = open(path).read().split("\n")
    n, i, _ = (int(x) for x in lines[0].split()[:3])
    rho = [int(x) for x in lines[1].split()]
    sig = [int(x) for x in lines[2].split()]
    extra = lines[3:]
    assert len(rho) == n and len(sig) == n
    return n, i, rho, sig, extra


def walk_list(s, ts, p):
    # walkList : s, [] => s ; s, t :: ts, p => if p < |t - s| then s +- p else walkList t ts (p - |t - s|)
    for t in ts:
        d = abs(t - s)
        if p < d:
            return s + (p if s <= t else -p)
        p -= d
        s = t
    return s


def walk_len(s, ts):
    tot = 1
    for t in ts:
        tot += abs(t - s)
        s = t
    return tot


def centers(s, ts):
    ln = walk_len(s, ts)
    return [walk_list(s, ts, p) for p in range(ln)]


def reach(f, c, start_set):
    """The set of times reachable at the last index of f, from start_set at index 0."""
    ln = len(c)
    cur = {u for u in start_set if 0 <= u < ln and abs(f[0] - c[u]) <= 1}
    for j in range(1, len(f)):
        if not cur:
            return set()
        nxt = set()
        for u in cur:
            for v in (u - 1, u, u + 1):
                if 0 <= v < ln and abs(f[j] - c[v]) <= 1:
                    nxt.add(v)
        cur = nxt
    return cur


def folds(f, c):
    return len(f) == 0 or bool(reach(f, c, {0}))


def trunc(f, lo, hi):
    u = 0
    while u < len(f) and lo <= f[u] <= hi:
        u += 1
    return f[:u]


def alt_lists(lo, hi, start, legs):
    """Alternating target lists of exactly `legs` legs in [lo, hi] from start."""
    out = []

    def rec(cur, last, d, acc):
        if len(acc) == legs:
            out.append(list(acc))
            return
        for dd in ((1, -1) if d == 0 else (d,)):
            rng = range(last + 1, hi + 1) if dd > 0 else range(lo, last)
            for t in rng:
                acc.append(t)
                rec(t, t, -dd, acc)
                acc.pop()

    rec(start, start, 0, [])
    return out


def least_legs(G, T, p, L, H, kmax=7):
    for k in range(0, kmax + 1):
        for s in (p - 1, p, p + 1):
            if s < L or s > H:
                continue
            for ts in alt_lists(L + 1, H - 1, s, k):
                c = centers(s, ts)
                if folds(G, c) and folds(T, c):
                    return k, s, ts
    return None


def extends_sub_band(G, T, p, L, H, k, first=True):
    """All (or the first) witnesses of ExtendsSubBand, literal in (L', H')."""
    found = []
    # Every band and every leg count is tried; the order (widest bands first, most legs first)
    # only makes the first witness come sooner, and does not change the set searched.
    bands = [(Lp, Hp) for Lp in range(L, p + 1) for Hp in range(p, H + 1)
             if Hp - Lp <= H - L - 3]
    bands.sort(key=lambda b: -(b[1] - b[0]))
    for (Lp, Hp) in bands:
            Gt, Tt = trunc(G, Lp, Hp), trunc(T, Lp, Hp)
            for s in range(max(Lp, p - 1), min(Hp, p + 1) + 1):
                for legs in range(k - 1, -1, -1):
                    for ts in alt_lists(Lp, Hp, s, legs):
                        c1 = centers(s, ts)
                        if not (folds(Gt, c1) and folds(Tt, c1)):
                            continue
                        last = ts[-1] if ts else s
                        for e in (L + 1, H - 1):
                            if e == last:
                                continue
                            c = centers(s, ts + [e])
                            if folds(G, c) and folds(T, c):
                                found.append((Lp, Hp, s, ts, e))
                                if first:
                                    return found
    return found


def mode_least(paths):
    for path in paths:
        n, i, rho, sig, _ = read_pair(path)
        L, H = min(rho), max(rho)
        p = rho[i]
        G = rho[i:]
        T = [rho[i - j] for j in range(i + 1)]
        print(f"== {path}: n={n} i={i} band [{L},{H}] (span {H-L}) level {p} |G|={len(G)} |T|={len(T)}")
        ll = least_legs(G, T, p, L, H)
        if ll is None:
            print("   least leg count: none within the search")
            continue
        k, s0, ts0 = ll
        print(f"   least leg count k = {k}: walk {s0} -> {' -> '.join(map(str, ts0))}")
        if k < 1:
            print("   (k = 0: ExtendsSubBand at k = 0 asks for a list of -1 = 0 targets; tested anyway)")
        w = extends_sub_band(G, T, p, L, H, max(k, 1))
        if not w:
            print(f"   ExtendsSubBand at k = {k}: NO witness (literal search over every sub-band)")
            continue
        Lp, Hp, s, ts, e = w[0]
        pad = ts + [ts[-1] if ts else s] * (max(k, 1) - 1 - len(ts))
        Gt, Tt = trunc(G, Lp, Hp), trunc(T, Lp, Hp)
        print(f"   ExtendsSubBand at k = {k}: L'={Lp} H'={Hp} s={s} ts={pad} e={e}"
              f"  (w' = {s} -> {' -> '.join(map(str, ts))}; truncated arms {len(Gt)}, {len(Tt)} links;"
              f" len w' = {walk_len(s, pad)}, len w = {walk_len(s, pad + [e])})")
        print(f"   LEAN {path} {n} {i} {L} {H} {k} {Lp} {Hp} {s} {' '.join(map(str, pad))} | {e}")


def mode_q2(paths):
    """A written-out basepoint of section 2.2: w' and e given; for each arm, the
    truncated fold's arrival set, and whether the suffix folds from each time."""
    for path in paths:
        n, i, rho, sig, extra = read_pair(path)
        wl = [l for l in extra if l.startswith("wprime ")][0].split()[1:]
        lo, hi, s = int(wl[0]), int(wl[1]), int(wl[2])
        ts = [int(x) for x in wl[3:]]
        e = int([l for l in extra if l.startswith("append ")][0].split()[1])
        p = rho[i]
        G = rho[i:]
        T = [rho[i - j] for j in range(i + 1)]
        c1 = centers(s, ts)
        c = centers(s, ts + [e])
        print(f"== {path}: n={n} i={i} level {p}; w' = {s} -> {ts}, band [{lo},{hi}], e = {e}")
        print(f"   whole arms fold onto w: G {folds(G, c)}, T {folds(T, c)}")
        for name, f in (("G", G), ("T", T)):
            ft = trunc(f, lo, hi)
            A = reach(ft, c1, {0})
            if len(ft) == len(f):
                print(f"   arm {name}: not truncated")
                continue
            sidx = len(ft) - 1
            ok = sorted(u for u in A if reach(f[sidx:], c, {u}))
            print(f"   arm {name}: truncated at {len(ft)} of {len(f)} links; arrival times {sorted(A)};"
                  f" suffix folds from: {ok if ok else 'NONE'}")
            if not ok:
                # the same prefix folded onto the whole walk w (times of the appended leg allowed)
                Aw = reach(ft, c, {0})
                okw = sorted(u for u in Aw if reach(f[sidx:], c, {u}))
                print(f"      the prefix folded onto w instead (len w' = {len(c1)}, len w = {len(c)}):"
                      f" arrival times {sorted(Aw)}; the suffix folds from {okw}")


def mode_q2all(paths):
    """A written-out basepoint of section 2.2, re-checked over EVERY witness of
    ExtendsSubBand at the least leg count k given in the file (the literal search:
    every sub-band [L', H'], minimal or not, every start, every target list, every
    appended level), and for each arm EVERY arrival time of the truncated fold: is
    there a witness at which both suffixes fold, each from some arrival time of its
    own arm?  The census tests only the minimal sub-band of each w'; this is wider."""
    for path in paths:
        n, i, rho, sig, extra = read_pair(path)
        k = int(open(path).read().split()[2])
        L, H = min(rho), max(rho)
        p = rho[i]
        G = rho[i:]
        T = [rho[i - j] for j in range(i + 1)]
        ll = least_legs(G, T, p, L, H)
        wits = extends_sub_band(G, T, p, L, H, k, first=False)
        good = []
        for (Lp, Hp, s, ts, e) in wits:
            c1 = centers(s, ts)
            c = centers(s, ts + [e])
            ok = True
            for f in (G, T):
                ft = trunc(f, Lp, Hp)
                if len(ft) == len(f):
                    continue
                sidx = len(ft) - 1
                A = reach(ft, c1, {0})
                if not reach(f[sidx:], c, A):
                    ok = False
                    break
            if ok:
                good.append((Lp, Hp, s, ts, e))
        print(f"== {path}: n={n} i={i} band [{L},{H}] level {p}; least leg count (own search) "
              f"{ll[0] if ll else None}, file says {k}")
        print(f"   ExtendsSubBand witnesses at k = {k} (literal, every sub-band): {len(wits)}")
        print(f"   witnesses at which both suffixes fold from some own arrival time: {len(good)}"
              + (f"  e.g. {good[0]}" if good else "  -- NONE"))


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "least":
        mode_least(sys.argv[2:])
    elif mode == "q2":
        mode_q2(sys.argv[2:])
    elif mode == "q2all":
        mode_q2all(sys.argv[2:])
    elif mode == "extk":
        # ExtendsSubBand at the leg count k recorded in the file's first line (the least leg
        # count established by check75.py), without re-running the least-leg search.
        for path in sys.argv[2:]:
            n, i, rho, sig, _ = read_pair(path)
            k = int(open(path).read().split()[2])
            L, H = min(rho), max(rho)
            p = rho[i]
            G = rho[i:]
            T = [rho[i - j] for j in range(i + 1)]
            print(f"== {path}: n={n} i={i} band [{L},{H}] level {p}; k = {k} from the file")
            w = extends_sub_band(G, T, p, L, H, k)
            if not w:
                print(f"   ExtendsSubBand at k = {k}: NO witness")
                continue
            Lp, Hp, s, ts, e = w[0]
            pad = ts + [ts[-1] if ts else s] * (k - 1 - len(ts))
            print(f"   ExtendsSubBand at k = {k}: L'={Lp} H'={Hp} s={s} ts={pad} e={e}")
            print(f"   LEAN {path} {n} {i} {L} {H} {k} {Lp} {Hp} {s} {' '.join(map(str, pad))} | {e}")
