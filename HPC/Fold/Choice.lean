import HPC.Fold.Interior
import HPC.Fold.DichotomyFaithful

/-!
# The choice rule

Batch 31 put one leg of the construction in place — `zigWalk_cons_length`,
`zigWalk_cons_val_tail`, `foldsOnto_prefixLeg`, with `isZigFree_cons` on the family side — and
proved the one-turn case in both orientations together with its limit,
`not_oneTurn_of_opposite`. What is missing is the rule that reads the two arms of a faithful
crooked sequence and chooses the turning targets.

This batch is gated on a census of the covers (`census-batch32.c`, output in
`census-batch32.log`, discussion in `REPORT-batch32.md`), and the census says the rule cannot be
tabulated:

* **A greedy cover of all the basepoints of `bing 0 n` by walks of the free family uses
  5, 7, 11, 16, 21, 30, 45 walks at spans 6 … 12** (the minimum is 4 at spans 6 and 7, by branch
  and bound; from span 8 on the exact value was not decided inside the node budget, and the
  best lower bound from basepoints with pairwise disjoint serving sets is 6, 8, 12, 14, 24).
  The count grows with the span, and the numbers reproduce the two the commission reports (7 at
  span 7, 11 at span 8).
* **No tabulated rule describes the cover.** The backward-read targets `H−1, L+1, H−3, L+2, …`
  fail at 9 of the 71 basepoints at span 6 and at 10 963 of 13 861 at span 12; an outward
  alternation from the base with amplitudes increasing by one fails at 43 of 71 and 13 797 of
  13 861; even the whole family of such alternations, with the first amplitude and the first
  direction free, fails at 4 of 71 and 11 671 of 13 861. So none is adopted.

What is proved here is the obstruction behind the growth, and it is sharper than "two
basepoints need two walks". `FoldsOnto` pins the walk's first value to within one of the
basepoint's level (`abs_sub_base_le_of_folds`, batch 28), so:

* `no_common_walk_of_level_gap`: **two basepoints whose levels differ by three or more are
  served by no common walk** — not by no common walk of the free family, by no walk at all;
* `notConstantOnBand`, the commissioned item, and `notConstantOnBandNonExtreme`, the same with
  both basepoints at non-extreme levels, on `cutSeq` and on `ceSeq` respectively;
* `cover_card_ge`: **a cover has at least as many walks as any set of basepoints with pairwise
  level gaps of three** — so any cover of the levels `L … H` of a chain needs at least
  `⌊(H − L)/3⌋ + 1` walks, and no family of bounded size can serve every band.
  `ceSeq_cover_card_ge_three` is the concrete instance: three walks at span eight, and
  `cover_card_ge_span` is the same bound read off the span of any Lipschitz chain that reaches
  both extremes, using the discrete intermediate-value property `exists_level`.

The proof is by the base-pinning lemma, so it needs no enumeration of the band's walks: neither
a `decide` over the family nor a reachability certificate (COMMISSION-batch32.md §2 offered
both). The census's pairs are sharper than the theorem's — at span four the two basepoints of
`bing 0 4` at levels 1 and 3, a gap of *two*, already have no common walk — but that sharper
fact is a statement about the finitely many walks of one band, while the level-gap obstruction
is uniform in the chain.

`s3ZigFreeInterior` is **not** proved here and no counterexample to it was found; it is kept,
commented out, at the end of the file, and nothing in the file depends on it.

English proofs: COMMISSION-batch32.md §2–§3.
-/

namespace HPC.Fold

/-! ## The level-gap obstruction -/

/-- **Two basepoints three levels apart are served by no common walk.** `FoldsOnto` pins the
walk's first value to within one of the basepoint's level, so a walk serving both puts their
levels within two of each other. -/
theorem no_common_walk_of_level_gap {n : ℕ} {ρ : Fin n → ℤ} {i j : Fin n} {ts : List ℤ}
    (hne : ts ≠ []) (hgap : 3 ≤ |ρ i - ρ j|)
    (hi : FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2)
    (hj : FoldsOnto (armG ρ j) (zigWalk ts).1 (zigWalk ts).2) : False := by
  have h1 := abs_sub_base_le_of_folds ρ i ts hne hi
  have h2 := abs_sub_base_le_of_folds ρ j ts hne hj
  have hb : |ρ i - ρ j| ≤ 2 := by
    rw [abs_le] at h1 h2 ⊢
    omega
  linarith

/-- The same with the walk given by a member of the free family: such a list is nonempty. -/
theorem no_common_free_walk_of_level_gap {n : ℕ} {ρ : Fin n → ℤ} {i j : Fin n} {L H : ℤ}
    {ts : List ℤ} (hts : IsZigFree L H ts) (hgap : 3 ≤ |ρ i - ρ j|)
    (hi : FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2)
    (hj : FoldsOnto (armG ρ j) (zigWalk ts).1 (zigWalk ts).2) : False := by
  refine no_common_walk_of_level_gap ?_ hgap hi hj
  intro h
  have := hts.len
  rw [h] at this
  simp at this

/-! ## The commissioned item -/

/-- **No walk serves a whole band.** There is a faithful crooked sequence and two basepoints of
it, both interior, served by no common member of the family — so the choice of walk must depend
on the basepoint and not only on `L` and `H`. -/
def NotConstantOnBand : Prop :=
  ∃ (n : ℕ) (ρ σ : Fin n → ℤ) (L H : ℤ) (i j : Fin n),
    IsCrookedIvF ρ σ ∧ (∀ t, L ≤ ρ t) ∧ (∀ t, ρ t ≤ H) ∧ L + 3 ≤ H ∧
    (∃ t, ρ t = L) ∧ (∃ t, ρ t = H) ∧
    ¬ ∃ ts : List ℤ, IsZigFree L H ts ∧
        FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
        FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
        FoldsOnto (armG ρ j) (zigWalk ts).1 (zigWalk ts).2 ∧
        FoldsOnto (armT ρ j) (zigWalk ts).1 (zigWalk ts).2

/-- **The commissioned item**, on the thirty-seven links of `cutSeq` (span four, levels
`3 … 7`): its basepoints `0` and `12`, at levels `3` and `7`, are served by no common walk. -/
theorem notConstantOnBand : NotConstantOnBand := by
  refine ⟨37, cutSeq, cutSeq, 3, 7, ⟨0, by norm_num⟩, ⟨12, by norm_num⟩, cutSeq_faithful,
    cutSeq_bounds.1, cutSeq_bounds.2, by norm_num, cutSeq_attains.1, cutSeq_attains.2, ?_⟩
  rintro ⟨ts, hts, hG, -, hG', -⟩
  refine no_common_free_walk_of_level_gap hts ?_ hG hG'
  have h1 : cutSeq ⟨0, by norm_num⟩ = 3 := rfl
  have h2 : cutSeq ⟨12, by norm_num⟩ = 7 := rfl
  rw [h1, h2]
  norm_num

/-- The same with both basepoints at non-extreme levels: `NotConstantOnBand` asks only for two
basepoints, and the two `cutSeq` supplies are at the extreme levels. At span four no two
non-extreme levels are three apart, so the witness is the 409-link chain `ceSeq`
(`bingPath 0 8`, levels `0 … 8`) at its basepoints `1` and `169`, of levels `1` and `7`. -/
def NotConstantOnBandNonExtreme : Prop :=
  ∃ (n : ℕ) (ρ σ : Fin n → ℤ) (L H : ℤ) (i j : Fin n),
    IsCrookedIvF ρ σ ∧ (∀ t, L ≤ ρ t) ∧ (∀ t, ρ t ≤ H) ∧ L + 3 ≤ H ∧
    (∃ t, ρ t = L) ∧ (∃ t, ρ t = H) ∧
    L + 1 ≤ ρ i ∧ ρ i ≤ H - 1 ∧ L + 1 ≤ ρ j ∧ ρ j ≤ H - 1 ∧
    ¬ ∃ ts : List ℤ, IsZigFree L H ts ∧
        FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
        FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
        FoldsOnto (armG ρ j) (zigWalk ts).1 (zigWalk ts).2 ∧
        FoldsOnto (armT ρ j) (zigWalk ts).1 (zigWalk ts).2

theorem notConstantOnBandNonExtreme : NotConstantOnBandNonExtreme := by
  have h1 : ceSeq ⟨1, by norm_num⟩ = 1 := rfl
  have h2 : ceSeq ⟨169, by norm_num⟩ = 7 := rfl
  refine ⟨409, ceSeq, ceSeq, 0, 8, ⟨1, by norm_num⟩, ⟨169, by norm_num⟩, ceSeq_faithful,
    ceSeq_lb, ceSeq_ub, by norm_num, ceSeq_attains_bot, ceSeq_attains_top,
    by rw [h1]; norm_num, by rw [h1]; norm_num, by rw [h2]; norm_num, by rw [h2]; norm_num, ?_⟩
  rintro ⟨ts, hts, hG, -, hG', -⟩
  refine no_common_free_walk_of_level_gap hts ?_ hG hG'
  rw [h1, h2]
  norm_num

/-! ## How many walks a cover needs -/

/-- **The cover bound.** If every basepoint in a family `b` is served by some walk of the list
`W`, and the levels of the `b`'s are pairwise three or more apart, then `W` has at least as
many walks as there are basepoints in the family. Applied to basepoints at the levels
`L, L + 3, L + 6, …`, it says a cover of a band of span `H − L` needs at least
`⌊(H − L)/3⌋ + 1` walks — so the size of a cover grows with the span, and no family of bounded
size serves every band. -/
theorem cover_card_ge {n m : ℕ} {ρ : Fin n → ℤ} (b : Fin m → Fin n) (W : List (List ℤ))
    (hW : ∀ ts ∈ W, ts ≠ [])
    (hgap : ∀ p q : Fin m, p ≠ q → 3 ≤ |ρ (b p) - ρ (b q)|)
    (hcov : ∀ p : Fin m, ∃ ts ∈ W,
      FoldsOnto (armG ρ (b p)) (zigWalk ts).1 (zigWalk ts).2) :
    m ≤ W.length := by
  classical
  choose F hFmem hFfold using hcov
  have hinj : Function.Injective F := by
    intro p q hpq
    by_contra hne
    exact no_common_walk_of_level_gap (hW _ (hFmem p)) (hgap p q hne) (hFfold p)
      (hpq ▸ hFfold q)
  have hcard : (Finset.univ : Finset (Fin m)).card ≤ W.toFinset.card :=
    Finset.card_le_card_of_injOn F (fun p _ => List.mem_toFinset.mpr (hFmem p))
      hinj.injOn
  simpa using hcard.trans (List.toFinset_card_le W)

/-- **Three walks at span eight.** Any list of walks serving every basepoint of `ceSeq` has at
least three members: its basepoints `0`, `5`, `70` are at levels `0`, `3`, `6`. (The census's
greedy cover of `ceSeq` uses eleven; this is the part of that count the level-gap obstruction
alone forces.) -/
theorem ceSeq_cover_card_ge_three (W : List (List ℤ)) (hW : ∀ ts ∈ W, ts ≠ [])
    (hcov : ∀ i : Fin 409, ∃ ts ∈ W,
      FoldsOnto (armG ceSeq i) (zigWalk ts).1 (zigWalk ts).2) :
    3 ≤ W.length := by
  have e0 : ceSeq ⟨0, by norm_num⟩ = 0 := rfl
  have e5 : ceSeq ⟨5, by norm_num⟩ = 3 := rfl
  have e70 : ceSeq ⟨70, by norm_num⟩ = 6 := rfl
  refine cover_card_ge
    (ρ := ceSeq)
    (![⟨0, by norm_num⟩, ⟨5, by norm_num⟩, ⟨70, by norm_num⟩] : Fin 3 → Fin 409) W hW ?_
    (fun p => hcov _)
  intro p q hpq
  fin_cases p <;> fin_cases q <;> simp_all

/-! ### From the bound to the span

To read `cover_card_ge` as a statement about the span one needs basepoints at the levels
`L, L + 3, L + 6, …`, and a Lipschitz sequence that reaches both `L` and `H` has a link at every
level between (the discrete intermediate-value property, `exists_level`). -/

/-- Auxiliary induction for `exists_level`: over a stretch of `d` steps, a Lipschitz sequence
takes every value between its two endpoints. -/
theorem exists_level_aux {n : ℕ} {ρ : Fin n → ℤ} (hlip : IsLip ρ) (v : ℤ) :
    ∀ (d : ℕ) (a b : Fin n), b.val = a.val + d →
      ((ρ a ≤ v ∧ v ≤ ρ b) ∨ (ρ b ≤ v ∧ v ≤ ρ a)) → ∃ t, ρ t = v := by
  intro d
  induction d with
  | zero =>
      intro a b hab h
      have hba : a = b := Fin.ext (by omega)
      subst hba
      exact ⟨a, by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega⟩
  | succ d ih =>
      intro a b hab h
      have hb := b.isLt
      have ha' : a.val + 1 < n := by omega
      by_cases hmid : (ρ ⟨a.val + 1, ha'⟩ ≤ v ∧ v ≤ ρ b) ∨ (ρ b ≤ v ∧ v ≤ ρ ⟨a.val + 1, ha'⟩)
      · exact ih ⟨a.val + 1, ha'⟩ b (by simp; omega) hmid
      · refine ⟨a, ?_⟩
        have hstep : |ρ ⟨a.val + 1, ha'⟩ - ρ a| ≤ 1 := hlip a ⟨a.val + 1, ha'⟩ rfl
        rw [abs_le] at hstep
        push_neg at hmid
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- **The discrete intermediate-value property.** A Lipschitz sequence that is at most `v`
somewhere and at least `v` somewhere is exactly `v` somewhere. -/
theorem exists_level {n : ℕ} {ρ : Fin n → ℤ} (hlip : IsLip ρ) {v : ℤ} {a b : Fin n}
    (h1 : ρ a ≤ v) (h2 : v ≤ ρ b) : ∃ t, ρ t = v := by
  rcases le_total a.val b.val with h | h
  · exact exists_level_aux hlip v (b.val - a.val) a b (by omega) (Or.inl ⟨h1, h2⟩)
  · exact exists_level_aux hlip v (a.val - b.val) b a (by omega) (Or.inr ⟨h1, h2⟩)

/-- **The cover grows with the span.** A cover of all the basepoints of a Lipschitz chain that
reaches both `L` and `H` has at least `⌊(H − L)/3⌋ + 1` walks. No hypothesis on the walks beyond
being nonempty: the bound holds for any walks at all, not only for the free family, and for any
chain, crooked or not. So no family of walks of bounded size serves every band, and the rule
that chooses the turning targets must read the chain. (The census measures the true growth:
greedily 5, 7, 11, 16, 21, 30, 45 walks at spans 6 … 12 for `bing 0 n`, against the 3, 3, 3, 4,
4, 4, 5 this bound gives.) -/
theorem cover_card_ge_span {n : ℕ} {ρ : Fin n → ℤ} {L H : ℤ} (hlip : IsLip ρ)
    (hL : ∃ t, ρ t = L) (hH : ∃ t, ρ t = H) (hLH : L ≤ H) (W : List (List ℤ))
    (hW : ∀ ts ∈ W, ts ≠ [])
    (hcov : ∀ i : Fin n, ∃ ts ∈ W, FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2) :
    ((H - L) / 3).toNat + 1 ≤ W.length := by
  classical
  obtain ⟨tL, htL⟩ := hL
  obtain ⟨tH, htH⟩ := hH
  have hex : ∀ p : Fin (((H - L) / 3).toNat + 1), ∃ t : Fin n, ρ t = L + 3 * (p.val : ℤ) := by
    intro p
    have hp : (p.val : ℤ) ≤ (H - L) / 3 := by
      have h := p.isLt
      omega
    refine exists_level hlip (a := tL) (b := tH) ?_ ?_
    · rw [htL]
      have : (0 : ℤ) ≤ (p.val : ℤ) := Int.natCast_nonneg _
      omega
    · rw [htH]; omega
  choose b hb using hex
  have key : ∀ x y : ℤ, x ≠ y → 3 ≤ |(L + 3 * x) - (L + 3 * y)| := by
    intro x y hxy
    rcases lt_or_gt_of_ne hxy with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  refine cover_card_ge b W hW ?_ (fun p => hcov (b p))
  intro p q hpq
  rw [hb p, hb q]
  exact key _ _ (by exact_mod_cast fun h => hpq (Fin.ext (by exact_mod_cast h)))

-- Commented-out statement `s3ZigFreeInterior`, `s3ZigFree`, `s3` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
