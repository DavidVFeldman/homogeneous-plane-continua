#!/usr/bin/env python3
"""parametric-batch74.py -- batch 74 section 2.4.  The parametric core.

A statement about the repository, not a proof.  It reads the two lists of
`inventory-batch73.md` (the declarations of the kernel dependency graph of
`HPC.Fold.s3_span_nine`, split by whether the statement pins a level by a literal
offset from the floor `L` or the ceiling `H` of the band), locates each
declaration in the sources, and measures three things:

  1. the engine:  which of the span-generic declarations are the timing law, the
     fold criteria, the pairing lemmas, the arm machinery, and which are local
     scaffolding -- grouped by the file they live in and by name family;
  2. the instances: which of the level-pinned declarations have a proof that is a
     *direct application* of a span-generic declaration -- the body, with the
     leading `by`/`:=` and whitespace removed, is a single term or a one-tactic
     proof (`exact`, `simpa using`, `simp only [...] ; exact`, ...) naming one or
     more span-generic declarations and nothing else of the project.  Those are
     the ones a parametric restatement would prove at once, since their proof
     already *is* the parametric proof read at a literal level;
  3. the mirror pairs: level-pinned declarations that come in armG/armT (or
     G/T, Lam/Vee) pairs, which a reflection lemma proves at once.

Usage: python3 parametric-batch74.py [inventory] [root]
"""

import os, re, sys, json
from collections import defaultdict

INV = sys.argv[1] if len(sys.argv) > 1 else "inventory-batch73.md"
ROOT = sys.argv[2] if len(sys.argv) > 2 else "HPC"

# ------------------------------------------------------------- the two lists

def read_lists(path):
    fixed, generic = [], []
    cur = None
    for line in open(path):
        if line.startswith("## Stated for nine alone"):
            cur = fixed; continue
        if line.startswith("## Span-generic"):
            cur = generic; continue
        m = re.match(r"\* `([^`]+)` — `([^`]+)`", line)
        if m and cur is not None:
            cur.append((m.group(1), m.group(2)))
    return fixed, generic


# --------------------------------------------------------- the declarations

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|inductive)\s+([A-Za-z_][^\s({:\[]*)")


KINDS = {}


def scan_sources(root):
    """name -> (file, header-lines, body-text)"""
    out = {}
    for dirpath, _, files in os.walk(root):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(dirpath, fn)
            lines = open(path).read().split("\n")
            starts = []
            for i, ln in enumerate(lines):
                m = DECL.match(ln)
                if m:
                    starts.append((i, m.group(2)))
            for idx, (i, name) in enumerate(starts):
                j = starts[idx + 1][0] if idx + 1 < len(starts) else len(lines)
                out[name] = (path, lines[i:j])
                KINDS[name] = DECL.match(lines[i]).group(1)
    return out


def split_body(chunk):
    """the statement and the proof body of a declaration, as text"""
    text = "\n".join(chunk)
    # the proof begins at the first top-level ":=" or ":= by"
    k = text.find(":=")
    if k < 0:
        return text, ""
    return text[:k], text[k + 2:]


TACTIC_WORDS = re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?]*")
NOISE = set("""by exact simpa using simp only rw intro fun le of from this at with
have refine apply omega rfl trivial constructor obtain rcases cases if then else
match do let show and or not fin nat int abs max min id show all_goals push_cast
linarith norm_num decide congr ext funext subst exacts left right""".split())


def main():
    fixed, generic = read_lists(INV)
    gnames = set(n for n, _ in generic)
    fnames = set(n for n, _ in fixed)
    src = scan_sources(ROOT)

    print("census of the inventory")
    print("  level-pinned declarations: %d" % len(fixed))
    print("  span-generic declarations: %d" % len(generic))
    print("  found in the sources: %d pinned, %d generic"
          % (sum(1 for n, _ in fixed if n in src), sum(1 for n, _ in generic if n in src)))

    missing = [n for n, _ in fixed if n not in src] + [n for n, _ in generic if n not in src]
    if missing:
        print("  named in the inventory but not found by the source scan: %s"
              % ", ".join(missing))

    # ------------------------------------------------ 1a. the engine, by family
    FAMILY = {
        "the timing law": ["z", "z_pos", "z_pos_aux", "z_mono", "z_mono_aux", "minGap",
                           "ivGap", "ivGap4", "ivGap5", "ivSep", "ivSep3", "ivSep4",
                           "ivSep5", "ArmSep", "armG_armSep", "armT_armSep",
                           "isLip_gap", "isLip_index_gap", "isLip_index_gap'"],
        "the exact fold criteria": ["foldsOnto_vee_iff_profile", "profile_of_foldsOnto_lam",
                                    "ascReach_iff_of_isLip", "critLamProfile_iff_of_isLip",
                                    "foldsOnto_landmark1", "foldsOnto_landmark2",
                                    "foldsOnto_walk7_of_val7", "foldsOnto_leg4W_refl",
                                    "foldsOnto_neg", "AscReach", "CritLamProfile",
                                    "CritVeeProfile", "beta_dist", "beta_hits",
                                    "beta_le_val"],
        "the crookedness pairing": ["CrookUp", "CrookDown", "CrookUp.levels", "crookUp_armG",
                                    "crookUp_armT", "crookDown_armG", "crookDown_armT",
                                    "crookUp_climb3", "crookUp_climb4", "crookUp_climb5",
                                    "crookDown_fall3", "crookDown_fall4",
                                    "IsCrookedIvF", "IsCrookedIvF.isLip", "IsCrookedIvF.near",
                                    "isCrookedIvF_restrict"],
        "the arms and the walks": ["armG", "armT", "armG_isLip", "armT_isLip", "armG_zero",
                                   "armT_zero", "armRefl", "armRefl_isLip", "FoldsOnto",
                                   "IsLip", "lamCenter", "lamCenter_asc", "lamCenter_desc",
                                   "veeCenter", "veeLen", "le_κ", "leg3Walk", "leg3Walk'",
                                   "leg4Walk'", "bumpWalk", "bumpWalk'", "bumpWalk_up",
                                   "bumpWalk_down", "offVee_self_walk", "offVee_self_len",
                                   "exists_least_index", "abs_sub_le_of_isLip"],
        "the announcements and the dichotomy": ["LowAt", "HighAt", "NonAscAt",
                                                "not_lowAt_highAt", "dichotomy_at",
                                                "lowAt_armG_of_not_highAt_armT",
                                                "lowAt_armT_of_not_highAt_armG",
                                                "highRunG_of_not_deepFirst2",
                                                "highRunT_of_not_deepFirst2",
                                                "nineBeforeDeep_of_highRunG",
                                                "nineBeforeDeep_of_highRunT",
                                                "highFirst_or_deepFirst",
                                                "BothHighRunL5", "CeilCrossGap",
                                                "topOnTime_of_ge", "bottomOnTime_of_le",
                                                "TopOnTime"],
    }
    print("\n---- 1a. the engine: the span-generic declarations by family ----")
    claimed = set()
    for fam, names in FAMILY.items():
        have = [n for n in names if n in gnames]
        claimed |= set(have)
        miss = [n for n in names if n not in gnames]
        print("  %-38s %2d   %s" % (fam, len(have), " ".join(have)))
        if miss:
            print("      (named here but not in the span-generic list: %s)" % " ".join(miss))
    rest = sorted(gnames - claimed)
    print("  %-38s %2d   %s" % ("the rest (local scaffolding)", len(rest), " ".join(rest)))

    # ---------------------------------------------------------- 1. the engine
    print("\n---- 1. the span-generic declarations, by file ----")
    byfile = defaultdict(list)
    for n, f in generic:
        byfile[f].append(n)
    for f in sorted(byfile, key=lambda f: -len(byfile[f])):
        print("  %-38s %2d   %s" % (f, len(byfile[f]), " ".join(sorted(byfile[f]))))

    # ------------------------------------------------- 2. the thin instances
    print("\n---- 2. level-pinned declarations whose proof is a direct application"
          " of span-generic ones ----")
    thin, sizes = [], []
    pinned_thms = set(n for n in fnames if KINDS.get(n) in ("theorem", "lemma"))
    only_generic = []
    for n, f in fixed:
        if n not in src:
            continue
        path, chunk = src[n]
        stmt, body = split_body(chunk)
        btxt = body.strip()
        if not btxt:
            continue
        nlines = len([l for l in btxt.split("\n") if l.strip()])
        sizes.append((nlines, n))
        words = set(TACTIC_WORDS.findall(btxt))
        used_generic = sorted(w for w in words if w in gnames)
        used_pinned_thm = sorted(w for w in words if w in pinned_thms and w != n)
        if used_generic and not used_pinned_thm:
            only_generic.append((n, f, nlines, used_generic))
            if nlines <= 6:
                thin.append((n, f, nlines, used_generic))
    print("  proofs whose only project-level *theorem* references are span-generic:"
          " %d of the %d" % (len(only_generic), len(fixed)))
    print("  of those, proofs of at most six lines (a direct instance): %d" % len(thin))
    for n, f, nl, g in thin:
        print("     %-44s %-34s %2d lines <- %s" % (n, f, nl, ", ".join(g[:6])))
    print("\n  the longer ones (only span-generic theorems, more than six lines):")
    for n, f, nl, g in only_generic:
        if nl > 6:
            print("     %-44s %-34s %3d lines" % (n, f, nl))
    sizes.sort()
    if sizes:
        tot = sum(s for s, _ in sizes)
        print("\n  proof sizes of the level-pinned declarations: %d bodies, %d lines in all,"
              " median %d, longest %d (%s)"
              % (len(sizes), tot, sizes[len(sizes) // 2][0], sizes[-1][0], sizes[-1][1]))

    # which generic lemmas are the ones being instantiated
    cnt = defaultdict(int)
    for _, _, _, g in thin:
        for x in g:
            cnt[x] += 1
    print("\n  the span-generic declarations they instantiate, by how often:")
    for x in sorted(cnt, key=lambda x: -cnt[x]):
        print("     %-38s %d" % (x, cnt[x]))

    # ------------------------------------------------------ 3. the mirror pairs
    print("\n---- 3. mirror pairs among the level-pinned declarations ----")
    pairs = []
    for n, f in fixed:
        if n.endswith("_armG"):
            m = n[:-5] + "_armT"
            if m in fnames:
                pairs.append((n, m))
        elif n.endswith("G") and not n.endswith("armG"):
            m = n[:-1] + "T"
            if m in fnames:
                pairs.append((n, m))
    print("  %d pairs (%d declarations) differ only by the arm they are read on"
          % (len(pairs), 2 * len(pairs)))
    for a, b in pairs:
        print("     %-44s %s" % (a, b))

    # -------------------------------------- 4. the pinned ones by file, for scale
    print("\n---- 4. the level-pinned declarations, by file ----")
    byfile = defaultdict(list)
    for n, f in fixed:
        byfile[f].append(n)
    for f in sorted(byfile, key=lambda f: -len(byfile[f])):
        print("  %-38s %2d" % (f, len(byfile[f])))


if __name__ == "__main__":
    main()
