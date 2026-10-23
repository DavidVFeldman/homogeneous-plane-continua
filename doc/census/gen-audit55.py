"""Generate HPC/Fold/Audit55.lean from census-batch55-sigma.txt.

The census writes, for each basepoint at which the sigma-route's implication
fails, the shrunk window of the pair and the four arms involved: the two arms of
tau = 9 - sig and the two arms of 9 - rho.  This script re-decides every verdict
independently, in Python, from the arms themselves, and writes the Lean file
that puts the same questions to the kernel.

Usage: python3 gen-audit55.py > HPC/Fold/Audit55.lean
"""

import sys

# the five walks of the branch L + 4, as levels above L
WALKS = {
    "Lam": [3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, 1],
    "Vee": [5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7, 8],
    "w3": [3, 4, 5, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7, 8],
    "w4": [3, 2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, 1],
    "w5": [3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7, 8],
}

LEANWALK = {
    "Lam": "(lamLen (0 + 3) (0 + 9) 0)\n      (lamCenter (0 + 3) (0 + 9) 0)",
    "Vee": "(veeLen (0 + 5) (0 + 9) 0)\n      (veeCenter (0 + 5) (0 + 9) 0)",
    "w3": "(leg3Len 0 (0 + 9) (0 + 6) (0 + 4))\n      (leg3Walk 0 (0 + 9) (0 + 6) (0 + 4))",
    "w4": "(leg3Len 0 (0 + 9) (0 + 7) (0 + 7))\n      (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2))",
    "w5": "(leg3Len 0 (0 + 9) (0 + 7) (0 + 4))\n      (leg3Walk 0 (0 + 9) (0 + 7) (0 + 4))",
}

WALKNAME = {"Lam": "the Λ-walk", "Vee": "the V-walk", "w3": "`w₃`", "w4": "`w₄`", "w5": "`w₅`"}


def folds(f, w):
    """the dynamic program of HPC/Fold/Decide.lean"""
    if abs(f[0] - w[0]) > 1:
        return False
    cur = {0}
    for v in f[1:]:
        nxt = set()
        for p in cur:
            for q in (p - 1, p, p + 1):
                if 0 <= q < len(w) and abs(v - w[q]) <= 1:
                    nxt.add(q)
        if not nxt:
            return False
        cur = nxt
    return True


def high_at(f):
    """HighAt f (L+1) (L+8), as the census reads it"""
    seen_low = False
    for v in f:
        if v >= 8 and not seen_low:
            return False
        if v <= 2:
            seen_low = True
    return True


def low_at(f):
    """LowAt f (L+1) (L+8), as the census reads it"""
    seen_high8 = seen_low2 = seen_low2_high6 = False
    for v in f:
        if v <= 1 and not seen_high8 and not seen_low2_high6:
            return False
        if v >= 8:
            seen_high8 = True
        if v >= 6 and seen_low2:
            seen_low2_high6 = True
        if v <= 2:
            seen_low2 = True
    return True


def numeral(levels):
    n = 0
    for i, v in enumerate(levels):
        n |= v << (4 * i)
    return n


def parse(path):
    out = []
    cur = None
    for line in open(path):
        if line.startswith("sigma-route counterexample"):
            cur = {"head": line.strip()}
            out.append(cur)
        elif cur is not None:
            for key, tag in [("  rho:", "rho"), ("  sig:", "sig")]:
                if line.startswith(key):
                    cur[tag] = [int(x) for x in line.split(":")[1].split()]
            if line.startswith("  tau forward"):
                cur["tauG"] = [int(x) for x in line.split(":")[1].split()]
            if line.startswith("  tau backward"):
                cur["tauT"] = [int(x) for x in line.split(":")[1].split()]
            if line.startswith("  9-rho forward"):
                cur["refG"] = [int(x) for x in line.split(":")[1].split()]
            if line.startswith("  9-rho backward"):
                cur["refT"] = [int(x) for x in line.split(":")[1].split()]
    return out


def wrap(levels):
    lines, cur = [], ""
    for tok in (str(x) for x in levels):
        if len(cur) + len(tok) + 1 > 96:
            lines.append(cur)
            cur = tok
        else:
            cur = cur + (" " if cur else "") + tok
    lines.append(cur)
    return lines


def main():
    cases = parse("census-batch55-sigma.txt")
    c = cases[0]
    rhoG = [9 - x for x in c["refG"]]
    rhoT = [9 - x for x in c["refT"]]
    arms = [("tG", c["tauG"], "the forward arm of `τ = 9 − σ`"),
            ("tT", c["tauT"], "the backward arm of `τ = 9 − σ`"),
            ("rG", c["refG"], "the forward arm of `9 − ρ`"),
            ("rT", c["refT"], "the backward arm of `9 − ρ`"),
            ("pG", rhoG, "the forward arm of `ρ`"),
            ("pT", rhoT, "the backward arm of `ρ`")]

    # the verdicts, recomputed here
    tau_ok = {k: folds(c["tauG"], w) and folds(c["tauT"], w) for k, w in WALKS.items()}
    ref_ok = {k: folds(c["refG"], w) and folds(c["refT"], w) for k, w in WALKS.items()}
    assert any(tau_ok.values()), "the tau-pair is not served: not a counterexample"
    assert not any(ref_ok.values()), "the pair of 9 - rho is served: not a counterexample"
    assert high_at(c["tauG"]) and high_at(c["tauT"])
    assert low_at(rhoG) and low_at(rhoT)
    served = [k for k in WALKS if tau_ok[k]]
    # for each walk, an arm of 9 - rho that fails
    failing = {}
    for k, w in WALKS.items():
        failing[k] = "rG" if not folds(c["refG"], w) else "rT"

    o = sys.stdout.write
    o('''import HPC.Fold.Decide
import HPC.Fold.ThreeWalks

/-!
# The σ-route loses the basepoint: a counterexample, decided by the kernel

The reflection of the general model sends `(ρ, σ)` to `(9 − σ, 9 − ρ)`, so the branch `L + 5` of
`ρ` is the branch `L + 4` of `τ = 9 − σ`, and the theorems of the branch `L + 4` apply to the
`τ`-pair. What the branch `L + 5` of `ρ` actually needs, however, is a fold of the arms of `9 − ρ`,
which sits one level above `τ` wherever the link is non-thin. COMMISSION.md §2 question 2 asks
whether a fold of the `τ`-pair onto one of the five walks of the branch `L + 4` always yields a
fold of the pair of `9 − ρ` onto *some* walk of that list — an implication batch 54 measured and
found to hold at every basepoint of its corpus.

It does not hold. This file carries one of the 501 basepoints of `census-batch55.c` at which it
fails, shrunk by the census to a window of %d links, and puts every verdict to the kernel:

* the `τ`-pair folds onto %s — both arms;
* the pair of `9 − ρ` folds onto **none** of the five: for each walk, one of its two arms is
  exhibited and the fold is refuted;
* the branch hypothesis holds where it is asked: both arms of `ρ` are `LowAt`, and both arms of
  `τ` are `HighAt`, with `τ` at `L + 4` at the basepoint.

So the σ-route cannot be repaired by allowing the walk to change: at this basepoint no walk of the
five serves `9 − ρ` at all. (The pair itself is faithful — `IsCrookedIvF` is not a decidable
predicate as stated, since it quantifies over all levels, and the census's own test is what
certifies it; everything below is about the arms, and is decided here.)

The arms are read off base-sixteen numerals by `armOf`, exactly as in the audits of batches 50–52.
-/

set_option maxRecDepth 40000000

namespace HPC.Fold

namespace Audit55

/-- The arm whose level at the step `i` is the `i`-th base-sixteen digit of `n`. -/
def armOf (n : ℕ) (m : ℕ) : Fin m → ℤ := fun i => (((n >>> (4 * i.val)) &&& 15 : ℕ) : ℤ)

instance (m : ℕ) (f : Fin m → ℤ) (tl th : ℤ) : Decidable (LowAt f tl th) := by
  unfold LowAt; infer_instance

instance (m : ℕ) (f : Fin m → ℤ) (tl th : ℤ) : Decidable (HighAt f tl th) := by
  unfold HighAt; infer_instance

''' % (len(c["rho"]), " and ".join(WALKNAME[k] for k in served)))

    o("/-! ## The pair\n\nThe window is `%s`.\n\n" % c["head"])
    o("`ρ`: `" + " ".join(str(x) for x in c["rho"]) + "`.\n\n")
    o("`σ`: `" + " ".join(str(x) for x in c["sig"]) + "`.\n\n")
    o("The basepoint is the index where `ρ` stands at `L + 5`; the arms below are read from it, "
      "outwards.\n-/\n\n")

    for name, lv, what in arms:
        o("/-- %s, %d steps.\n\nLevels: `%s`. -/\n"
          % (what, len(lv), "\n".join(wrap(lv))))
        o("def %s : Fin %d → ℤ :=\n  armOf 0x%X %d\n\n" % (name, len(lv), numeral(lv), len(lv)))

    o("/-! ## The hypotheses of the branch -/\n\n")
    o("theorem pG_lowAt : LowAt pG (0 + 1) (0 + 8) := by decide +kernel\n")
    o("theorem pT_lowAt : LowAt pT (0 + 1) (0 + 8) := by decide +kernel\n")
    o("theorem tG_highAt : HighAt tG (0 + 1) (0 + 8) := by decide +kernel\n")
    o("theorem tT_highAt : HighAt tT (0 + 1) (0 + 8) := by decide +kernel\n")
    o("theorem tG_base : tG ⟨0, by omega⟩ = 0 + 4 := by decide +kernel\n")
    o("theorem pG_base : pG ⟨0, by omega⟩ = 0 + 5 := by decide +kernel\n\n")

    o("/-! ## The `τ`-pair folds -/\n\n")
    for k in served:
        for arm in ("tG", "tT"):
            o("theorem %s_folds_%s :\n    FoldsOnto %s %s := by\n  decide +kernel\n"
              % (arm, k, arm, LEANWALK[k]))
    o("\n/-! ## The pair of `9 − ρ` folds onto none of the five -/\n\n")
    for k in WALKS:
        arm = failing[k]
        o("theorem %s_not_folds_%s :\n    ¬ (FoldsOnto %s %s) := by\n  decide +kernel\n"
          % (arm, k, arm, LEANWALK[k]))

    o('''
/-! ## The counterexample, assembled -/

/-- **The σ-route loses the basepoint.** At this basepoint the `τ`-pair folds onto %s, while no
walk of the five serves the pair of `9 − ρ`: for each of the five, one arm of `9 − ρ` refuses it.
-/
theorem sigma_route_walk_not_transported :
    (FoldsOnto tG %s ∧
      FoldsOnto tT %s) ∧
    ¬ (FoldsOnto %s %s) ∧
    ¬ (FoldsOnto %s %s) ∧
    ¬ (FoldsOnto %s %s) ∧
    ¬ (FoldsOnto %s %s) ∧
    ¬ (FoldsOnto %s %s) :=
  ⟨⟨tG_folds_%s, tT_folds_%s⟩, %s_not_folds_Lam, %s_not_folds_Vee, %s_not_folds_w3,
    %s_not_folds_w4, %s_not_folds_w5⟩

end Audit55

end HPC.Fold
''' % (WALKNAME[served[0]],
       LEANWALK[served[0]], LEANWALK[served[0]],
       failing["Lam"], LEANWALK["Lam"], failing["Vee"], LEANWALK["Vee"],
       failing["w3"], LEANWALK["w3"], failing["w4"], LEANWALK["w4"],
       failing["w5"], LEANWALK["w5"],
       served[0], served[0],
       failing["Lam"], failing["Vee"], failing["w3"], failing["w4"], failing["w5"]))


if __name__ == "__main__":
    main()
