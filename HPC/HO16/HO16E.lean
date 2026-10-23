import HPC.HO16.HO16D
import HPC.HO16.LadderExists

/-!
# Batch 197 skeleton: Hoehn–Oversteegen Theorem 1, V — Theorem 15

The batch-197 skeleton (commission 197), split under `HPC/HO16/`: the definitions of §2
(`ladderY`, `IsLadder`, `zzL`, `zzR`, `zzLine`, `ladderPiece`, `ladderSheet`, `ladderHeight`) are
in `LadderDefs.lean`, verbatim; the proof of §3 is in `LadderParam.lean`, `LadderPiece.lean`,
`LadderStair.lean`, `LadderStair2.lean`. This file holds the skeleton's theorems.

Source: Hoehn–Oversteegen 2016 (`doc/sources/hoehn-oversteegen2016.pdf`), Theorem 15 and its proof
(pp. 194–198). The route replaces H–O's Claim 15.1 and their zig-zag construction by an explicit
one ("ladders", commission 197 §2). `π = Prod.fst`; `G⋆ = G ×ˢ Icc 0 1`. Route: commission 197.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

noncomputable section Ladder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **§3. A ladder has a stairwell structure of odd height** (the construction of H–O
pp. 196–198 in explicit form). The `α` is `ladderAlphaSet S y ev` (commission 197 §3, "The `α`"). -/
theorem ho16_stairwell_of_ladder {G : Set E} {S : Finset (E × E)} {y : E → List ℝ}
    {ev : E × E → Option (ℕ × ℝ × ℝ)} (hL : IsLadder G S y ev) (hS : S.Nonempty) :
    Odd (ladderHeight S y) ∧ ∃ α : ℕ → Set (E × ℝ),
      IsStairwellStr G (⋃ i ∈ Icc 1 (ladderHeight S y), ladderSheet S y ev i)
        (ladderHeight S y) (ladderSheet S y ev) α :=
  ⟨odd_ladderHeight hL hS, ladderAlphaSet S y ev, ladder_isStairwellStr hL hS⟩

/-- **§5 (stretch). Claim 15.1, replaced**: inside any open `U` containing a separator there is a
ladder. Proof: `LadderSep.lean` (a sign function `u` for the separator), `LadderSubdiv.lean`
(short edges), `LadderSign.lean` and `LadderExists.lean` (sign sequences at the levels `q / N`, one
flip per edge, the lists of midpoints of the sign changes; commission 197 §5, steps 1–4, with a
Lipschitz `u` in place of uniform continuity and the event of an edge read off its two lists).
Connectedness of `G` is used only for `G ≠ ∅`. -/
theorem exists_ladder {G : Set E} (hG : IsPLGraph G) (hconn : IsConnected G)
    {M : Set (E × ℝ)} (hM : M ⊆ G ×ˢ Ioo (0 : ℝ) 1)
    (hsep : SeparatesIn (G ×ˢ Icc (0 : ℝ) 1) M (G ×ˢ ({0} : Set ℝ)) (G ×ˢ ({1} : Set ℝ)))
    {U : Set (E × ℝ)} (hU : IsOpen U) (hMU : M ⊆ U) :
    ∃ (S : Finset (E × E)) (y : E → List ℝ) (ev : E × E → Option (ℕ × ℝ × ℝ)),
      IsLadder G S y ev ∧ S.Nonempty ∧ ∀ i, ladderSheet S y ev i ⊆ U ∩ G ×ˢ Ioo (0 : ℝ) 1 :=
  exists_ladder_aux hG hconn hM hsep hU hMU

end Ladder

/-! ## §5. Theorem 15, Theorem 20, the classification step (stretch) -/

/-- **H–O Theorem 15** for connected PL graphs. -/
theorem ho16_theorem15 : HOThm15 := by
  intro E _ _ G hG hconn M hM hsep U hU hMU
  obtain ⟨S, y, ev, hL, hS, hsub⟩ := exists_ladder hG hconn hM hsep hU hMU
  obtain ⟨hodd, α, hα⟩ := ho16_stairwell_of_ladder hL hS
  exact ⟨_, _, iUnion₂_subset fun i _ => hsub i, hodd, _, α, hα⟩

/-- **H–O Theorem 20, forward direction.** -/
theorem ho16_theorem20 : HOThm20 := ho16_theorem20_of_thm15 ho16_theorem15

/-- **H–O p. 180**: every indecomposable non-degenerate homogeneous plane continuum is a
pseudo-arc; no hypothesis. -/
theorem ho16_indec_homogeneous_pseudoArc (M : Set Pt) [CompactSpace M] [ConnectedSpace M]
    (hhom : IsHomogeneous M) (hind : ¬ IsDecomposableSpace M) (hnt : (univ : Set M).Nontrivial) :
    ∃ M₀ : Set Pt, IsPseudoArc M₀ ∧ Nonempty (M ≃ₜ M₀) :=
  homeomorph_pseudoArc_of_indec_homogeneous_of_thm15 ho16_theorem15 M hhom hind hnt

/-! ## §5. The converse, and both directions -/

/-- An indecomposable continuum `M` is, as a space, indecomposable as a subcontinuum of itself. -/
theorem isIndecomposable_univ_of_isIndecomposable {X : Type*} [MetricSpace X] {M : Set X}
    (hM : HPC.Fold.Q78.IsIndecomposable M) : HPC.Fold.Q78.IsIndecomposable (univ : Set M) := by
  have himg : ∀ A : Set M, HPC.Fold.Q78.IsContinuum A →
      HPC.Fold.Q78.IsContinuum (Subtype.val '' A) := fun A hA =>
    ⟨hA.1.image continuous_subtype_val, hA.2.image _ continuous_subtype_val.continuousOn⟩
  have hsub : ∀ A : Set M, Subtype.val '' A ⊆ M := fun A => by
    rintro _ ⟨z, -, rfl⟩; exact z.2
  have hval : ∀ A : Set M, Subtype.val '' A = M → A = univ := fun A hA =>
    eq_univ_of_forall fun z => by
      have : (z : X) ∈ Subtype.val '' A := by rw [hA]; exact z.2
      obtain ⟨w, hw, hwz⟩ := this
      rwa [← Subtype.ext hwz]
  haveI := isCompact_iff_compactSpace.1 hM.1.1
  haveI := isConnected_iff_connectedSpace.1 hM.1.2
  refine ⟨⟨isCompact_univ, isConnected_univ⟩, ?_⟩
  · intro A B hA hB _ _ hAB
    have hun : Subtype.val '' A ∪ Subtype.val '' B = M := by
      rw [← image_union, hAB, image_univ, Subtype.range_coe]
    rcases hM.2 _ _ (himg A hA) (himg B hB) (hsub A) (hsub B) hun with h | h
    · exact Or.inl (hval A h)
    · exact Or.inr (hval B h)

/-- A space whose underlying set is an indecomposable continuum is not decomposable. -/
theorem not_isDecomposableSpace_of_isIndecomposable_univ {X : Type*} [MetricSpace X]
    (h : HPC.Fold.Q78.IsIndecomposable (univ : Set X)) : ¬ IsDecomposableSpace X := by
  rintro ⟨H, K, hH, hK, hHu, hKu, hHK⟩
  rcases h.2 H K hH hK (subset_univ _) (subset_univ _) hHK with h' | h'
  · exact hHu h'
  · exact hKu h'

/-- **The converse** (not part of the stretch): a pseudo-arc is homogeneous (Bing;
`homogeneous_of_isPseudoArc`, batch 88) and indecomposable. -/
theorem ho16_pseudoArc_indec_homogeneous (M : Set Pt) [CompactSpace M] [ConnectedSpace M]
    (hPA : IsPseudoArc (univ : Set M)) : IsHomogeneous M ∧ ¬ IsDecomposableSpace M := by
  refine ⟨fun x z => ?_, not_isDecomposableSpace_of_isIndecomposable_univ
    (hPA.2.1 univ subset_rfl hPA.1.1)⟩
  obtain ⟨T, hT⟩ := homogeneous_of_isPseudoArc hPA x z (mem_univ x) (mem_univ z)
  refine ⟨(Homeomorph.Set.univ M).symm.trans (T.trans (Homeomorph.Set.univ M)), ?_⟩
  change ((T ⟨x, mem_univ x⟩ : (univ : Set M)) : M) = z
  rw [hT]

/-- **The indecomposable case of the classification, both directions** (stretch): a
non-degenerate plane continuum is homogeneous and indecomposable iff it is a pseudo-arc. -/
theorem ho16_indec_homogeneous_iff (M : Set Pt) [CompactSpace M] [ConnectedSpace M]
    (hnt : (univ : Set M).Nontrivial) :
    (IsHomogeneous M ∧ ¬ IsDecomposableSpace M) ↔ IsPseudoArc (univ : Set M) :=
  ⟨fun h => isPseudoArc_of_indec_homogeneous ho16_theorem20 M h.1 h.2 hnt,
    ho16_pseudoArc_indec_homogeneous M⟩

/-! ## §6. Non-vacuity -/

/-- The hypotheses of `ho16_indec_homogeneous_pseudoArc` are met: by the plane pseudo-arc
`M₀` (`isPseudoArc_plane`), homogeneous by `homogeneous_of_isPseudoArc` (pointwise for
`M₀ ⊆ Pt`), indecomposable as a hereditarily indecomposable continuum. -/
theorem exists_indec_homogeneous_plane : ∃ M : Set Pt, CompactSpace M ∧ ConnectedSpace M ∧
    IsHomogeneous M ∧ ¬ IsDecomposableSpace M ∧ (univ : Set M).Nontrivial := by
  obtain ⟨M₀, hM₀⟩ := isPseudoArc_plane
  obtain ⟨⟨⟨hc, hconn⟩, -⟩, hHI, hnt⟩ := id hM₀
  refine ⟨M₀, isCompact_iff_compactSpace.1 hc, isConnected_iff_connectedSpace.1 hconn,
    fun x z => ?_, not_isDecomposableSpace_of_isIndecomposable_univ
      (isIndecomposable_univ_of_isIndecomposable (hHI M₀ subset_rfl ⟨hc, hconn⟩)), ?_⟩
  · obtain ⟨T, hT⟩ := homogeneous_of_isPseudoArc hM₀ x z x.2 z.2
    exact ⟨T, hT⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := hnt
    exact ⟨⟨a, ha⟩, mem_univ _, ⟨b, hb⟩, mem_univ _, fun h => hab (congrArg Subtype.val h)⟩

/-- A ladder of height 3 on `[0, 2] ⊆ ℝ`: lists `[½]`, `[½]`, `[¼, ½, ¾]` at `0`, `1`, `2`; no
event on `(0, 1)`; a wedge at `2` at place `1` on `(1, 2)` (tip at parameter `½`, height `⅜`). -/
theorem ladder_example :
    IsLadder (Icc (0 : ℝ) 2) {((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (2 : ℝ))}
      (fun v => if v = 2 then [1 / 4, 1 / 2, 3 / 4] else [1 / 2])
      (fun s => if s = ((1 : ℝ), (2 : ℝ)) then some (1, 1 / 2, 3 / 8) else none) := by
  have h02 : (0 : ℝ) ≠ 2 := by norm_num
  have h12 : (1 : ℝ) ≠ 2 := by norm_num
  have hne : ((0 : ℝ), (1 : ℝ)) ≠ ((1 : ℝ), (2 : ℝ)) := by
    intro h; simp at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> norm_num
  · simp only [Finset.mem_insert, Finset.mem_singleton, iUnion_iUnion_eq_or_left,
      iUnion_iUnion_eq_left, segment_eq_Icc (zero_le_one' ℝ), segment_eq_Icc (one_le_two : (1:ℝ) ≤ 2)]
    rw [Icc_union_Icc_eq_Icc zero_le_one one_le_two]
  · intro s hs s' hs' hss
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs hs'
    rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl
    · exact absurd rfl hss
    · rintro z ⟨h1, h2⟩
      simp only [segment_eq_Icc (zero_le_one' ℝ), segment_eq_Icc (one_le_two : (1:ℝ) ≤ 2), mem_Icc] at h1 h2
      have : z = 1 := le_antisymm h1.2 h2.1
      subst this; simp
    · rintro z ⟨h1, h2⟩
      simp only [segment_eq_Icc (zero_le_one' ℝ), segment_eq_Icc (one_le_two : (1:ℝ) ≤ 2), mem_Icc] at h1 h2
      have : z = 1 := le_antisymm h2.2 h1.1
      subst this; simp
    · exact absurd rfl hss
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> simp [h02, h12, Nat.odd_iff] <;> norm_num
  · intro s hs he
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> simp [h02, h12, hne] at he ⊢
  · intro s hs m lam h he
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · simp [hne] at he
    · simp only [if_true, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      simp [h12]; norm_num

/-- The ladder of `ladder_example` has height 3. -/
theorem ladder_example_height :
    ladderHeight {((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (2 : ℝ))}
      (fun v => if v = 2 then [1 / 4, 1 / 2, 3 / 4] else [1 / 2]) = 3 := by
  have h02 : (0 : ℝ) ≠ 2 := by norm_num
  have h12 : (1 : ℝ) ≠ 2 := by norm_num
  simp [ladderHeight, h02, h12]

/-- `ho16_stairwell_of_ladder` applied to `ladder_example`: the union of its three sheets has a
stairwell structure of height 3. -/
theorem ladder_example_stairwell :
    HasStairwell (Icc (0 : ℝ) 2)
      (⋃ i ∈ Icc 1 3, ladderSheet {((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (2 : ℝ))}
        (fun v => if v = 2 then [1 / 4, 1 / 2, 3 / 4] else [1 / 2])
        (fun s => if s = ((1 : ℝ), (2 : ℝ)) then some (1, 1 / 2, 3 / 8) else none) i) 3 := by
  obtain ⟨-, α, hα⟩ := ho16_stairwell_of_ladder ladder_example (Finset.insert_nonempty _ _)
  rw [ladder_example_height] at hα
  exact ⟨_, α, hα⟩

end HPC.HO16
