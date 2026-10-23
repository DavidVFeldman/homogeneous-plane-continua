import HPC.Fold.Bump
import HPC.Fold.Sync

/-!
# Theorem 3 reduced to a single open statement

Two branches. If the minimal-index sequence has range at most two, one block settles
everything. Otherwise the one-bump machinery applies, and what remains is a single
proposition, `F2Prime`, asserting that the explicit bump height `hStar` (or valley `lStar`)
satisfies the segmented condition of batch 8 for both arms.

Proved here: the range-at-most-two branch; that the arm attaining its own maximum satisfies
the first three clauses of `SegLam` at `hStar` (Lemma A); and that `F2Prime` implies Bing 1948
Theorem 3 in the block reading and three-link form.

Not proved here: `F2Prime`.

English proofs: COMMISSION-batch9.md §3. Delivered complete: no `sorry` remains.

Two remarks on the delivery, both anticipated by the commission:

* `hStarArm` is kept as the commissioned `sSup` over a set of integers; the set is a subset of
  the (finite) range of the arm, so `Int.csSup_mem` gives `hStarArm_mem` directly and no
  change of encoding was needed;
* batch 8 has no `SegVee` counterpart of `exists_blocks_first_of_segLam`, so one is added here
  (`exists_blocks_first_of_segVee`) by the two-line composition the commission describes.
-/

namespace HPC.Fold

open HPC.Chain

/-! ## The degenerate branch -/

/-- If every link of `E` lies in one of three consecutive links of `D`, the one-block
consolidation settles Theorem 3. -/
theorem exists_blocks_first_of_range_le_two {X : Type*} [MetricSpace X] {n k : ℕ}
    (_hn : 0 < n) {E : Chain X n} {D : Chain X k} (h : E.Refines D) (i : Fin n) (c : ℕ)
    (hrange : ∀ t, c ≤ (h.minIdx t).val ∧ (h.minIdx t).val ≤ c + 2) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  have hβ' : IsBlockMap (fun _ : Fin n => (⟨0, Nat.one_pos⟩ : Fin 1)) :=
    ⟨fun u => ⟨i, Subsingleton.elim _ _⟩, fun t t' _ => by simp⟩
  refine ⟨1, fun _ => ⟨0, Nat.one_pos⟩, hβ', rfl, fun u => ⟨c, ?_⟩⟩
  rw [ofBlocks_link]
  refine Set.iUnion₂_subset fun t _ => ?_
  refine (minIdx_subset h t).trans (D.link_subset_unionRange (h.minIdx t) (hrange t).1 ?_)
  have := (hrange t).2
  omega

/-! ## The explicit bump height -/

/-- The greatest level an arm attains strictly before its first drop to `p − 2`; the greatest
level of the whole arm if it never drops. -/
noncomputable def hStarArm {m : ℕ} (f : Fin m → ℤ) (p : ℤ) : ℤ :=
  sSup {v : ℤ | ∃ j : Fin m, f j = v ∧ ∀ j' : Fin m, j' ≤ j → p - 1 ≤ f j'}

noncomputable def lStarArm {m : ℕ} (f : Fin m → ℤ) (p : ℤ) : ℤ :=
  - hStarArm (fun j => - f j) (-p)

/-- The bump height: the larger of the two arms' demands, floored at `p` and `L + 1`, capped
at `max (H − 1) p`. -/
noncomputable def hStar {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ) : ℤ :=
  min (max (max (hStarArm (armG ρ i) (ρ i)) (hStarArm (armT ρ i) (ρ i))) (max (ρ i) (L + 1)))
      (max (H - 1) (ρ i))

noncomputable def lStar {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ) : ℤ :=
  max (min (min (lStarArm (armG ρ i) (ρ i)) (lStarArm (armT ρ i) (ρ i))) (min (ρ i) (H - 1)))
      (min (L + 1) (ρ i))

theorem hStarArm_mem {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (p : ℤ) (h0 : f ⟨0, hm⟩ = p) :
    ∃ j : Fin m, f j = hStarArm f p ∧ ∀ j' : Fin m, j' ≤ j → p - 1 ≤ f j' := by
  classical
  set S : Set ℤ := {v : ℤ | ∃ j : Fin m, f j = v ∧ ∀ j' : Fin m, j' ≤ j → p - 1 ≤ f j'}
  have hne : S.Nonempty := by
    refine ⟨p, ⟨0, hm⟩, h0, fun j' hj' => ?_⟩
    have hj'z : j'.val ≤ 0 := Fin.le_def.1 hj'
    have hj'0 : j' = ⟨0, hm⟩ := Fin.ext (show j'.val = 0 by omega)
    rw [hj'0, h0]
    omega
  have hsub : S ⊆ Set.range f := by
    rintro v ⟨j, rfl, -⟩
    exact ⟨j, rfl⟩
  have hbdd : BddAbove S := ((Set.finite_range f).subset hsub).bddAbove
  obtain ⟨j, hj, hj'⟩ := Int.csSup_mem hne hbdd
  exact ⟨j, hj, hj'⟩

theorem le_hStarArm {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (p : ℤ) (h0 : f ⟨0, hm⟩ = p) :
    p ≤ hStarArm f p := by
  classical
  set S : Set ℤ := {v : ℤ | ∃ j : Fin m, f j = v ∧ ∀ j' : Fin m, j' ≤ j → p - 1 ≤ f j'}
  have hmem : p ∈ S := by
    refine ⟨⟨0, hm⟩, h0, fun j' hj' => ?_⟩
    have hj'z : j'.val ≤ 0 := Fin.le_def.1 hj'
    have hj'0 : j' = ⟨0, hm⟩ := Fin.ext (show j'.val = 0 by omega)
    rw [hj'0, h0]
    omega
  have hsub : S ⊆ Set.range f := by
    rintro v ⟨j, rfl, -⟩
    exact ⟨j, rfl⟩
  have hbdd : BddAbove S := ((Set.finite_range f).subset hsub).bddAbove
  exact le_csSup hbdd hmem

/-- **Lemma A.** An arm satisfies the first three clauses of `SegLam` at its own `hStarArm`:
the least index at which the phase-adjusted level reaches the height exists, and every earlier
link lies in `[p − 1, h + 1]`. Stated as the existence of the index `s` that `SegLam` needs.

The Lipschitz hypothesis and `p ≤ h` turn out to be unnecessary and are kept as
commissioned. -/
theorem exists_peak_index {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (_hf : IsLip f) (p : ℤ)
    (h0 : f ⟨0, hm⟩ = p) (h : ℤ) (_hph : p ≤ h) (hle : h ≤ hStarArm f p) :
    ∃ s : ℕ, s < m ∧
      (∀ hs : s < m, h ≤ f ⟨s, hs⟩ + phase f ⟨s, hs⟩) ∧
      (∀ j : Fin m, j.val < s → f j + phase f j < h) ∧
      (∀ j : Fin m, j.val < s → p - 1 ≤ f j ∧ f j ≤ h + 1) := by
  classical
  obtain ⟨j₀, hj₀, hj₀'⟩ := hStarArm_mem hm f p h0
  have hP0 : h ≤ f j₀ + phase f j₀ := by
    rcases phase_zero_or_one f j₀ with e | e <;> omega
  obtain ⟨s, hs, hsmin⟩ := exists_least_index (fun j => h ≤ f j + phase f j) ⟨j₀, hP0⟩
  have hsj₀ : s.val ≤ j₀.val := by
    by_contra hc
    exact hsmin j₀ (by omega) hP0
  refine ⟨s.val, s.isLt, ?_, ?_, ?_⟩
  · intro hs'
    rwa [show (⟨s.val, hs'⟩ : Fin m) = s from Fin.ext rfl]
  · intro j hj
    exact lt_of_not_ge (hsmin j hj)
  · intro j hj
    have h1 : p - 1 ≤ f j := hj₀' j (Fin.le_def.2 (by omega))
    have h2 : ¬ (h ≤ f j + phase f j) := hsmin j hj
    rcases phase_zero_or_one f j with e | e <;> omega

/-! ## The open statement -/

/-- **F2′.** For a crooked, non-degenerate minimal-index sequence, the explicit bump height
serves both arms, or the explicit valley does.

This is the single remaining gap between the machinery of batches 1–8 and Bing 1948
Theorem 3. Checked on 2 926 738 basepoints — every crooked 1-Lipschitz sequence of length at
most 12 on six levels, and random crooked sequences to length 56 — with no exception once
constant sequences (range zero, handled by `exists_blocks_first_of_range_le_two`) are set
aside. -/
def F2Prime : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedSeq ρ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
      (SegLam (armG ρ i) (ρ i) H L (hStar ρ i H L) ∧
       SegLam (armT ρ i) (ρ i) H L (hStar ρ i H L)) ∨
      (SegVee (armG ρ i) (ρ i) H L (lStar ρ i H L) ∧
       SegVee (armT ρ i) (ρ i) H L (lStar ρ i H L))

/-! ## The `SegVee` bridge -/

/-- The valley counterpart of batch 8's `exists_blocks_first_of_segLam`: if both arms of the
minimal-index sequence satisfy the reflected segmented condition at a common valley, then `E`
has a block consolidation with every block inside three consecutive links of `D` and `d_i` in
the first block. -/
theorem exists_blocks_first_of_segVee {X : Type*} [MetricSpace X] {n k : ℕ}
    {E : Chain X n} {D : Chain X k} (h : E.Refines D) (i : Fin n) (p H L lb : ℤ)
    (hp : p = (h.minIdx i : ℤ))
    (hG : SegVee (armG (fun t => (h.minIdx t : ℤ)) i) p H L lb)
    (hT : SegVee (armT (fun t => (h.minIdx t : ℤ)) i) p H L lb)
    (hGlip : IsLip (armG (fun t => (h.minIdx t : ℤ)) i))
    (hTlip : IsLip (armT (fun t => (h.minIdx t : ℤ)) i))
    (hLf : ∀ t, L ≤ (h.minIdx t : ℤ)) (hHf : ∀ t, (h.minIdx t : ℤ) ≤ H)
    (hlp : lb ≤ p) (hLl : min (L + 1) p ≤ lb) (hpH : p ≤ H) (hlH : lb + 1 ≤ H) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  have hmG : 0 < n - i.val := by have := i.isLt; omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG (fun t => (h.minIdx t : ℤ)) i ⟨0, hmG⟩ = p := by
    simp only [armG]
    rw [hp]
    congr 2
  have hT0 : armT (fun t => (h.minIdx t : ℤ)) i ⟨0, hmT⟩ = p := by
    simp only [armT]
    rw [hp]
    congr 2
  have hfoldG := segVee_foldsOnto hmG _ hGlip p H L lb hG0
    (fun j => hLf _) (fun j => hHf _) hlp hLl hpH hlH hG
  have hfoldT := segVee_foldsOnto hmT _ hTlip p H L lb hT0
    (fun j => hLf _) (fun j => hHf _) hlp hLl hpH hlH hT
  exact exists_blocks_first_of_folds h i (veeBumpLen p H L lb) (veeBumpCenter p H L lb)
    hfoldG hfoldT

/-! ## Theorem 3, conditional on F2′ -/

/-- **Bing 1948, Theorem 3**, block reading, three-link form: if `E` is crooked in `D` then
for every link `d_i` there is a block consolidation of `E` with every block inside three
consecutive links of `D` and `d_i` in the first block.

Conditional on `F2Prime`; every other ingredient is proved. -/
theorem theorem3_of_F2Prime (hF2 : F2Prime) {X : Type*} [MetricSpace X] {n k : ℕ}
    (hn : 0 < n) {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  classical
  have href : E.Refines D := hcr.1
  set ρ : Fin n → ℤ := fun t => ((href.minIdx t : ℕ) : ℤ) with hρ
  obtain ⟨tL, -, htL⟩ := Finset.exists_min_image Finset.univ ρ ⟨i, Finset.mem_univ i⟩
  obtain ⟨tH, -, htH⟩ := Finset.exists_max_image Finset.univ ρ ⟨i, Finset.mem_univ i⟩
  set L : ℤ := ρ tL with hL
  set H : ℤ := ρ tH with hH
  have hLf : ∀ t, L ≤ ρ t := fun t => htL t (Finset.mem_univ t)
  have hHf : ∀ t, ρ t ≤ H := fun t => htH t (Finset.mem_univ t)
  by_cases hdeg : H ≤ L + 2
  · -- the degenerate branch
    refine exists_blocks_first_of_range_le_two hn href i (href.minIdx tL).val (fun t => ?_)
    have h1 := hLf t
    have h2 := hHf t
    simp only [hρ, hL, hH] at h1 h2 hdeg
    omega
  · -- the one-bump branch
    have hcase : L + 3 ≤ H := by omega
    have hlip : IsLip ρ := by
      intro t t' htt'
      have := minIdx_lip href t t' htt'
      simp only [hρ]
      rw [abs_le]
      omega
    have hcrook : IsCrookedSeq ρ := isCrookedSeq_minIdx hcr
    have hLi : L ≤ ρ i := hLf i
    have hiH : ρ i ≤ H := hHf i
    rcases hF2 n ρ i H L hlip hcrook hLf hHf hcase with ⟨hG, hT⟩ | ⟨hG, hT⟩
    · exact exists_blocks_first_of_segLam href i (ρ i) H L (hStar ρ i H L) rfl hG hT
        (armG_isLip hlip i) (armT_isLip hlip i) hLf hHf
        (by simp only [hStar]; omega) (by simp only [hStar]; omega) hLi
        (by simp only [hStar]; omega)
    · exact exists_blocks_first_of_segVee href i (ρ i) H L (lStar ρ i H L) rfl hG hT
        (armG_isLip hlip i) (armT_isLip hlip i) hLf hHf
        (by simp only [lStar]; omega) (by simp only [lStar]; omega) hiH
        (by simp only [lStar]; omega)

end HPC.Fold
