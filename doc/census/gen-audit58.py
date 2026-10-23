"""Generate HPC/Fold/Audit58.lean.

Batch 58 asks whether the *criteria* of the wide four-leg engine
(`foldsOnto_leg4W`, `HPC/Fold/Leg4Wide.lean`) close the branch `L + 5` of span
nine.  `census-batch58.c` answers no, and hands back two witnesses:

  (a) a forward arm of the branch — the window of Bing's chain `bing 0 9`
      beginning at its link 811, cut to its shortest prefix with the property —
      at which *no* parameter set of the engine's window has its criterion;
  (b) a nine-link faithful arm which meets the criterion of one parameter set
      with the landmarks read on the *interval* and does not fold onto its walk.

This script recomputes both verdicts independently, in Python, from the arms
themselves, works out for each parameter set which clause of the criterion
fails and at which index, and writes the Lean file that puts the same questions
to the kernel.

Usage: python3 gen-audit58.py > HPC/Fold/Audit58.lean
"""

import sys

H = 9


def bpath(a, b):
    """Bing's chain from the level a to the level b."""
    d = abs(a - b)
    if d <= 2:
        s = 1 if a <= b else -1
        return [a + s * u for u in range(d + 1)]
    mid = b - 1 if a < b else b + 1
    c = a + 1 if a < b else a - 1
    return bpath(a, mid) + bpath(mid, c)[1:] + bpath(c, b)[1:]


def window():
    """the parameter sets (P, K, M) of the engine's window at L = 0, H = 9"""
    out = []
    for P in range(2, 7):
        for K in range(P, 9):
            for M in range(1, P - 1):
                if M + 3 > K or K + 3 < H:
                    continue
                out.append((P, K, M))
    return out


def clause_failures(p, lo, hi, K, M, P):
    """For each clause of Leg4Crit, the least index at which it fails."""
    m = len(p)
    res = {}
    if not (p[0] >= P - 1 and p[0] <= P and p[0] <= K - 1):
        res['base'] = 0
    fA = b1 = fB = 0
    for d in range(m):
        if p[d] <= P - 3 and not (fA or fB):
            res['floor'] = d
            break
        if hi[d] >= K:
            fA = 1
        if b1 and hi[d] >= K - 1:
            fB = 1
        if lo[d] <= P - 2:
            b1 = 1
    fA = b1 = fB = c1 = c2 = fC = 0
    for d in range(m):
        if p[d] <= P - 4 and not (fA or fB or fC):
            res['deep'] = d
            break
        if hi[d] >= K + 2:
            fA = 1
        if b1 and hi[d] >= H - 2:
            fB = 1
        if lo[d] <= M - 1:
            b1 = 1
        if c2 and hi[d] >= H - 2:
            fC = 1
        if c1 and lo[d] <= M:
            c2 = 1
        if hi[d] >= K + 1:
            c1 = 1
    fA = b1 = fB = c1 = c2 = fC = 0
    for d in range(m):
        if p[d] >= K + 2 and not (fA or fB or fC):
            res['ceil'] = d
            break
        if lo[d] <= M - 1:
            fA = 1
        if b1 and lo[d] <= M + 1:
            fB = 1
        if hi[d] >= K + 1:
            b1 = 1
        if c2 and lo[d] <= M + 1:
            fC = 1
        if c1 and hi[d] >= K:
            c2 = 1
        if lo[d] <= P - 2:
            c1 = 1
    return res


def folds(f, w):
    """the dynamic program of HPC/Fold/Decide.lean"""
    if abs(f[0] - w[0]) > 1:
        return False
    cur = {0}
    for v in f[1:]:
        nxt = set()
        for q in cur:
            for r in (q - 1, q, q + 1):
                if 0 <= r < len(w) and abs(v - w[r]) <= 1:
                    nxt.add(r)
        if not nxt:
            return False
        cur = nxt
    return True


def leg4walk(L, Hh, K, M, P):
    """leg4Walk L H K M P, as a list of levels"""
    out = []
    u = 0
    while True:
        if u <= K - P + 1:
            v = P - 1 + u
        elif u <= 2 * K - P + 1 - M:
            v = 2 * K - P + 1 - u
        elif u <= 2 * K - P + Hh - 2 * M:
            v = u - (2 * K - P + 1) + 2 * M
        else:
            v = 2 * K - P + 2 * Hh - 2 * M - 1 - u
        out.append(v)
        u += 1
        if u >= 2 * K - P + 2 * Hh - 2 * M - L - 1:
            return out


def numeral(xs):
    return '0x' + ''.join('%x' % x for x in reversed(xs))


# ---------------------------------------------------------------- witness (a)

CHAIN = bpath(0, 9)
START = 811
ARM = CHAIN[START:START + 175]
REFL = [9 - x for x in ARM]
assert ARM[0] == 5
assert len(ARM) == 175

ORDER = ['base', 'floor', 'ceil', 'deep']
PLAN = []
for (P, K, M) in window():
    for refl in (0, 1):
        s = REFL if refl else ARM
        res = clause_failures(s, s, s, K, M, P)
        assert res, (P, K, M, refl)
        for c in ORDER:
            if c in res:
                PLAN.append((P, K, M, refl, c, res[c]))
                break

# ---------------------------------------------------------------- witness (b)

IVRHO = [5, 4, 5, 5, 5, 4, 5, 4, 3]
IVSIG = [5, 4, 5, 6, 5, 4, 5, 4, 3]
IVP, IVK, IVM = 6, 7, 4
assert clause_failures(IVRHO, IVRHO, IVSIG, IVK, IVM, IVP) == {}
assert clause_failures(IVRHO, IVRHO, IVRHO, IVK, IVM, IVP) != {}
assert not folds(IVRHO, leg4walk(0, 9, IVK, IVM, IVP))

# ---------------------------------------------------------------------- output

CLAUSE_LEMMA = {
    'base': 'not_leg4CritG_of_base',
    'floor': 'not_leg4CritG_of_floor',
    'deep': 'not_leg4CritG_of_deep',
    'ceil': 'not_leg4CritG_of_ceil',
}
CLAUSE_ARGS = {'base': 1, 'floor': 2, 'deep': 3, 'ceil': 3}

out = sys.stdout.write

out('''import HPC.Fold.PairCheck
import HPC.Fold.Leg4Scan
import HPC.Fold.Decide
import HPC.Fold.ArmReflect
import HPC.Fold.Leaf

/-!
# The criteria of the four-leg engine do not close the branch `L + 5`

Batch 56 gave the branch `L + 5` of span nine a list of walks — the four-leg family of
`foldsOnto_leg4W` (`HPC/Fold/Leg4Wide.lean`) — every member of which comes with a *criterion*:
a base condition and three announcements about the arm, sufficient for the fold. Batch 57 refuted
the route through the reflected valley crossing and named, as the next candidate, the walk
`L+4 → L+7 → L+1 → L+8 → L+1`, whose floor announcement is met by exactly the pair of links the
crookedness clause returns. Question 1 of COMMISSION.md asks whether the branch hypothesis
`LowAt (L + 1) (L + 8)` and `ivSep` supply that walk's other two announcements; question 3 asks
whether the criteria may be read on the interval `[ρ, σ]` of a link rather than on its point `ρ`.

This file answers both with theorems, at two explicit faithful witnesses.

**Question 1: no, and not for any walk of the family.** `Leg4CritClosesL5` is the statement that
at every basepoint of the branch *some* parameter set of the engine's window has its criterion on
both arms, read either directly or through the reflection of each arm. It is false
(`not_leg4CritClosesL5`). The witness is the window of Bing's chain `bing 0 9` (986 links)
beginning at its link 811 and 175 links long, whose first link stands at `L + 5`: its forward arm
fails the criterion of **all twenty-nine** parameter sets of the window, in both orientations.
Its backward arm is the basepoint alone, so nothing is hidden there. In particular the walk
question 1 names fails too (`not_walk47181CritL5`), and the clause of it that fails at this arm
is the floor announcement, at the arm's index five.

**Question 3: the interval reading is not sufficient.** `Leg4CritIvSufficient` is the engine with
every landmark "at `l` or above" read on `σ` and every landmark "at `l` or below" read on `ρ`,
the triggers left on `ρ`. It is false (`not_leg4CritIvSufficient`), and the witness is small: the
nine-link faithful arm

```
ρ = 5 4 5 5 5 4 5 4 3        σ = 5 4 5 6 5 4 5 4 3
```

meets the interval criterion of the parameter set `(P, K, M) = (L + 6, L + 7, L + 4)` — its floor
announcement is served by the link at index three, whose interval reaches `L + 6` although its
`ρ` sits at `L + 5` — and does not fold onto the walk `L+5 → L+7 → L+4 → L+8 → L+1`. So the one
level the model reads from below is not bookkeeping: the engine consumes the point, not the
interval.

Every verdict is put to the kernel. Faithfulness is proved, not assumed, by the search of
`HPC/Fold/PairCheck.lean`; the twenty-nine refutations are the linear scans of
`HPC/Fold/Leg4Scan.lean`, which is what makes a 175-link arm affordable.
-/

set_option maxRecDepth 20000000

namespace HPC.Fold

/-- **The criteria of the wide four-leg engine, offered as a closure of the branch `L + 5`.**
At every basepoint of the branch some parameter set of the engine's window has its criterion on
both arms, read either on the arms or on their reflections in the level `L + (L + 9)`. Refuted by
`not_leg4CritClosesL5`. -/
def Leg4CritClosesL5 : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ), IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) → ρ i = L + 5 →
    LowAt (armG ρ i) (L + 1) (L + 8) → LowAt (armT ρ i) (L + 1) (L + 8) →
    ∃ K M P : ℤ, Leg4Window L (L + 9) K M P ∧
      ((Leg4Crit (armG ρ i) (L + 9) K M P ∧ Leg4Crit (armT ρ i) (L + 9) K M P) ∨
        (Leg4Crit (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) K M P ∧
          Leg4Crit (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) K M P))

/-- **The walk question 1 names**, `L+4 → L+7 → L+1 → L+8 → L+1`, which is the engine at
`(P, K, M) = (L + 5, L + 7, L + 1)`: its criterion holds on both arms at every basepoint of the
branch. Refuted by `not_walk47181CritL5`. -/
def Walk47181CritL5 : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ), IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) → ρ i = L + 5 →
    LowAt (armG ρ i) (L + 1) (L + 8) → LowAt (armT ρ i) (L + 1) (L + 8) →
    Leg4Crit (armG ρ i) (L + 9) (L + 7) (L + 1) (L + 5) ∧
      Leg4Crit (armT ρ i) (L + 9) (L + 7) (L + 1) (L + 5)

/-- **The engine, read on the interval.** The criterion with its high landmarks read on the upper
end `σ` of a link and its low landmarks on the lower end `ρ`, the triggers left on `ρ`, is still
sufficient for the fold. Refuted by `not_leg4CritIvSufficient`. -/
def Leg4CritIvSufficient : Prop :=
  ∀ (m : ℕ) (ρ σ : Fin m → ℤ) (L Hh K M P : ℤ), 0 < m → IsCrookedIvF ρ σ → IsLip ρ →
    Leg4Window L Hh K M P → (∀ j, L ≤ ρ j) → (∀ j, ρ j ≤ Hh) →
    Leg4CritG ρ ρ σ Hh K M P →
    FoldsOnto ρ (leg4Len L Hh K M P) (leg4Walk L Hh K M P)

''')

# ------------------------------------------------------------------- namespace A

out('''namespace Audit58

/-! ## The arm that meets no criterion

The window of Bing's chain `bing 0 9` beginning at its link %d, %d links long. The chain is thin,
so `σ = ρ`; both are carried as one natural number in base sixteen, the link `i` being the `i`-th
digit.

`ρ`: `%s`.
-/

/-- The %d links of the window, as a base-sixteen numeral. -/
def rhoNat : ℕ := %s

/-- Reading a link off the numeral. -/
def rhoD (i : ℕ) : ℕ := (rhoNat >>> (4 * i)) &&& 15

/-- The point sequence of the pair. -/
def rho175 : Fin %d → ℤ := PairCheck.rhoOf %d rhoD

/-- The pair is thin: the upper end of each link is its point. -/
def sig175 : Fin %d → ℤ := PairCheck.sigOf %d rhoD

/-- The basepoint: the first link, where `ρ` stands at `L + 5` with `L = 0`. -/
def basept : Fin %d := ⟨0, by omega⟩

/-- The forward arm at the basepoint: the whole window. -/
abbrev armF : Fin (%d - basept.val) → ℤ := armG rho175 basept

/-- Its reflection in the level `L + (L + 9)`. -/
abbrev armFR : Fin (%d - basept.val) → ℤ := armRefl (0 + (0 + 9)) (armG rho175 basept)

/-! ## The pair is faithful -/

/-- `IsCrookedIvF rho175 sig175`, by the search of `HPC/Fold/PairCheck.lean`. -/
theorem faithful : IsCrookedIvF rho175 sig175 :=
  PairCheck.isCrookedIvF_of_search (n := %d) (lev := 10) (rd := rhoD) (sd := rhoD)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

/-! ## The branch hypotheses -/

theorem band_lo : ∀ t, (0 : ℤ) ≤ rho175 t := by decide

theorem band_hi : ∀ t, rho175 t ≤ 0 + 9 := by decide

theorem base_level : rho175 basept = 0 + 5 := by decide

theorem lowAt_armG : LowAt (armG rho175 basept) (0 + 1) (0 + 8) := by unfold LowAt; decide

theorem lowAt_armT : LowAt (armT rho175 basept) (0 + 1) (0 + 8) := by unfold LowAt; decide

/-! ## No parameter set of the window has its criterion

For each of the twenty-nine parameter sets `(P, K, M)` of the window, and for each of the two
orientations, the clause of the criterion that fails is named, together with the index at which it
fails; the scans of `HPC/Fold/Leg4Scan.lean` do the rest. -/

''' % (START, len(ARM), ' '.join(str(x) for x in ARM), len(ARM), numeral(ARM),
       len(ARM), len(ARM), len(ARM), len(ARM), len(ARM), len(ARM), len(ARM), len(ARM)))

names = []
for (P, K, M, refl, cl, d) in PLAN:
    nm = 'no_%s_%d_%d_%d' % ('refl' if refl else 'dir', P, K, M)
    names.append((P, K, M, refl, nm))
    arm = 'armFR' if refl else 'armF'
    lemma = CLAUSE_LEMMA[cl]
    if cl == 'base':
        body = ('  %s ⟨%d, by decide⟩ rfl (by decide)' % (lemma, d))
    else:
        body = ('  %s ⟨%d, by decide⟩ (by decide)%s'
                % (lemma, d, ' (by decide)' * CLAUSE_ARGS[cl]))
    out('/-- `(P, K, M) = (%d, %d, %d)`%s: the %s clause fails at the index %d. -/\n'
        % (P, K, M, ', reflected' if refl else '', cl, d))
    out('theorem %s : ¬ Leg4Crit %s (0 + 9) %d %d %d :=\n%s\n\n' % (nm, arm, K, M, P, body))

# the two collecting lemmas
for refl in (0, 1):
    arm = 'armFR' if refl else 'armF'
    nm = 'no_crit_refl' if refl else 'no_crit_dir'
    out('/-- **No parameter set of the window** has its criterion on the %s arm. -/\n'
        % ('reflected' if refl else 'forward'))
    out('theorem %s (K M P : ℤ) (hw : Leg4Window 0 (0 + 9) K M P) :\n'
        '    ¬ Leg4Crit %s (0 + 9) K M P := by\n'
        '  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hw\n'
        '  interval_cases P <;> interval_cases K <;> interval_cases M <;>\n'
        '    first\n' % (nm, arm))
    out('      | omega\n')
    for (P, K, M, r, n2) in names:
        if r == refl:
            out('      | exact %s\n' % n2)
    out('\n')

out('''end Audit58

/-- **The criteria of the four-leg engine do not close the branch `L + 5`.** At the basepoint of
the 175-link faithful window of `Audit58` the forward arm fails the criterion of every parameter
set of the engine's window, in both orientations. -/
theorem not_leg4CritClosesL5 : ¬ Leg4CritClosesL5 := by
  intro h
  obtain ⟨K, M, P, hw, hc⟩ :=
    h 175 Audit58.rho175 Audit58.sig175 Audit58.basept 0 Audit58.faithful Audit58.band_lo
      Audit58.band_hi Audit58.base_level Audit58.lowAt_armG Audit58.lowAt_armT
  rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Audit58.no_crit_dir K M P hw h1
  · exact Audit58.no_crit_refl K M P hw h1

/-- **The walk question 1 names does not have a criterion the branch meets.** Its parameter set is
`(P, K, M) = (L + 5, L + 7, L + 1)`, and at the arm of `Audit58` its floor announcement already
fails. -/
theorem not_walk47181CritL5 : ¬ Walk47181CritL5 := by
  intro h
  exact Audit58.no_dir_5_7_1
    (h 175 Audit58.rho175 Audit58.sig175 Audit58.basept 0 Audit58.faithful Audit58.band_lo
      Audit58.band_hi Audit58.base_level Audit58.lowAt_armG Audit58.lowAt_armT).1

''')

# ------------------------------------------------------------------- namespace B

out('''namespace Audit58Iv

/-! ## The arm that meets the interval criterion and does not fold

`ρ`: `%s`; `σ`: `%s`. -/

/-- The nine links of `ρ`. -/
def rhoNat : ℕ := %s

/-- The nine links of `σ`. -/
def sigNat : ℕ := %s

def rhoD (i : ℕ) : ℕ := (rhoNat >>> (4 * i)) &&& 15

def sigD (i : ℕ) : ℕ := (sigNat >>> (4 * i)) &&& 15

/-- The point sequence. -/
def rho9 : Fin 9 → ℤ := PairCheck.rhoOf 9 rhoD

/-- The upper end of each link. -/
def sig9 : Fin 9 → ℤ := PairCheck.sigOf 9 sigD

theorem faithful : IsCrookedIvF rho9 sig9 :=
  PairCheck.isCrookedIvF_of_search (n := 9) (lev := 10) (rd := rhoD) (sd := sigD)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

theorem lip : IsLip rho9 := by unfold IsLip; decide

theorem band_lo : ∀ j, (0 : ℤ) ≤ rho9 j := by decide

theorem band_hi : ∀ j, rho9 j ≤ 9 := by decide

theorem window : Leg4Window 0 9 %d %d %d := by decide

/-- The criterion holds with the landmarks read on the interval. -/
theorem crit_interval : Leg4CritG rho9 rho9 sig9 9 %d %d %d := by decide

/-- It fails with the landmarks read on the point: the floor announcement asks for a link at
`L + 6`, and the arm never rises above `L + 5`. -/
theorem not_crit_point : ¬ Leg4Crit rho9 9 %d %d %d := by decide

/-- And the arm does not fold onto the walk. -/
theorem not_folds : ¬ FoldsOnto rho9 (leg4Len 0 9 %d %d %d) (leg4Walk 0 9 %d %d %d) :=
  not_foldsOnto_of_foldsB (by decide)

end Audit58Iv

/-- **The interval reading of the engine is not sufficient.** The nine-link faithful arm of
`Audit58Iv` meets the criterion of `(P, K, M) = (L + 6, L + 7, L + 4)` with its landmarks read on
the intervals of its links, and does not fold onto the walk that criterion is for. -/
theorem not_leg4CritIvSufficient : ¬ Leg4CritIvSufficient := fun h =>
  Audit58Iv.not_folds
    (h 9 Audit58Iv.rho9 Audit58Iv.sig9 0 9 %d %d %d (by omega) Audit58Iv.faithful Audit58Iv.lip
      Audit58Iv.window Audit58Iv.band_lo Audit58Iv.band_hi Audit58Iv.crit_interval)

end HPC.Fold
''' % (' '.join(map(str, IVRHO)), ' '.join(map(str, IVSIG)),
       numeral(IVRHO), numeral(IVSIG),
       IVK, IVM, IVP, IVK, IVM, IVP, IVK, IVM, IVP,
       IVK, IVM, IVP, IVK, IVM, IVP, IVK, IVM, IVP))
