import HPC.HO16.HO16E
import HPC.HO16.NonVac196

/-!
# Batch 197, §6: non-vacuity

* `exists_ladder_example`: `exists_ladder` applied to a segment `G = [0, 1]`, `M = G × {½}` and
  the open strip `U = E × (¼, ¾)` (batch 196's `hoThm15_segment_hyps` for the separation).
* `ladder_example_alpha2`, `ladder_example_alpha3`: the end sets of `ladder_example`
  (commission 197 §6): `π(α₂) = {4/3, 3/2}`, `π(α₃) = {7/6}`, as computed by hand in the
  commission.
* Degenerate inputs of `IsLadder`: the empty decomposition of the empty set is a ladder
  (`isLadder_empty`; excluded in `ho16_stairwell_of_ladder` by `S.Nonempty`), and a list of even
  length is not allowed (`not_isLadder_even`).
-/

namespace HPC.HO16

open Set

/-- **Non-vacuity of `exists_ladder`**: a ladder over `[0, 1]` inside the strip `ℝ × (¼, ¾)`
around the separator `[0, 1] × {½}`. -/
theorem exists_ladder_example :
    ∃ (S : Finset (ℝ × ℝ)) (y : ℝ → List ℝ) (ev : ℝ × ℝ → Option (ℕ × ℝ × ℝ)),
      IsLadder (Icc (0 : ℝ) 1) S y ev ∧ S.Nonempty ∧
      ∀ i, ladderSheet S y ev i ⊆
        (univ ×ˢ Ioo (1 / 4 : ℝ) (3 / 4)) ∩ Icc (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  obtain ⟨hG, hc, hM, hsep, -, -⟩ := hoThm15_segment_hyps
  refine exists_ladder hG hc hM hsep (isOpen_univ.prod isOpen_Ioo) ?_
  rintro ⟨x, t⟩ ⟨-, ht⟩
  simp only [mem_singleton_iff] at ht
  exact ⟨mem_univ _, by rw [ht]; norm_num, by rw [ht]; norm_num⟩

/-- The empty decomposition of the empty set is a ladder (a degenerate input; excluded in
`ho16_stairwell_of_ladder` by `S.Nonempty`). -/
theorem isLadder_empty (y : ℝ → List ℝ) (ev : ℝ × ℝ → Option (ℕ × ℝ × ℝ)) :
    IsLadder (∅ : Set ℝ) ∅ y ev := by
  refine ⟨by simp, by simp, fun s hs => by simp at hs, by simp, by simp, by simp⟩

/-- Lists of even length are not allowed. -/
theorem not_isLadder_even :
    ¬ IsLadder (Icc (0 : ℝ) 1) {((0 : ℝ), (1 : ℝ))} (fun _ => []) (fun _ => none) := by
  intro h
  have := (h.2.2.2.1 ((0 : ℝ), (1 : ℝ)) (Finset.mem_singleton_self _)).1
  simp at this

section Example

/-- The data of `ladder_example`. -/
private noncomputable abbrev exS : Finset (ℝ × ℝ) := {((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (2 : ℝ))}
private noncomputable abbrev exY : ℝ → List ℝ := fun v => if v = 2 then [1 / 4, 1 / 2, 3 / 4] else [1 / 2]
private noncomputable abbrev exEv : ℝ × ℝ → Option (ℕ × ℝ × ℝ) :=
  fun s => if s = ((1 : ℝ), (2 : ℝ)) then some (1, 1 / 2, 3 / 8) else none

private theorem ex_alpha (i : ℕ) :
    Prod.fst '' ladderAlphaSet exS exY exEv i =
      AffineMap.lineMap (1 : ℝ) 2 '' wA 1 1 (1 / 2) i := by
  have h12 : (1 : ℝ) ≠ 2 := by norm_num
  have hne : ((0 : ℝ), (1 : ℝ)) ≠ ((1 : ℝ), (2 : ℝ)) := by intro h; simp at h
  rw [image_fst_ladderAlphaSet]
  simp only [exS, Finset.mem_insert, Finset.mem_singleton, iUnion_iUnion_eq_or_left,
    iUnion_iUnion_eq_left, exEv, if_neg hne, if_true, exY, if_neg h12]
  simp [eA]

private theorem lineMap_12 (μ : ℝ) : AffineMap.lineMap (1 : ℝ) 2 μ = 1 + μ := by
  rw [AffineMap.lineMap_apply_module]; simp; ring

/-- `π(α₂) = {4/3, 3/2}` for `ladder_example` (commission 197 §6). -/
theorem ladder_example_alpha2 :
    Prod.fst '' ladderAlphaSet {((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (2 : ℝ))}
      (fun v => if v = 2 then [1 / 4, 1 / 2, 3 / 4] else [1 / 2])
      (fun s => if s = ((1 : ℝ), (2 : ℝ)) then some (1, 1 / 2, 3 / 8) else none) 2 =
      {4 / 3, 3 / 2} := by
  rw [ex_alpha]
  simp only [wA, zzR, zzL]
  norm_num [lineMap_12, image_insert_eq, image_singleton]
  ext x
  simp only [mem_preimage, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (h | h)
    · right; linarith
    · left; linarith
  · rintro (h | h)
    · right; rw [h]; norm_num
    · left; rw [h]; norm_num

/-- `π(α₃) = {7/6}` for `ladder_example` (commission 197 §6). -/
theorem ladder_example_alpha3 :
    Prod.fst '' ladderAlphaSet {((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (2 : ℝ))}
      (fun v => if v = 2 then [1 / 4, 1 / 2, 3 / 4] else [1 / 2])
      (fun s => if s = ((1 : ℝ), (2 : ℝ)) then some (1, 1 / 2, 3 / 8) else none) 3 =
      {7 / 6} := by
  rw [ex_alpha]
  simp only [wA, zzR, zzL]
  norm_num [lineMap_12, image_insert_eq, image_singleton]

end Example

end HPC.HO16
