import HPC.Hagopian.H84Bridge

/-!
# Batch 187, §5.2: the cover `𝔅` (reconnaissance, with a finite repair)

Commission 187 §5.2. Hagopian (p. 343): "Let `𝔅` be the collection of open sets
`{⋃Δ(𝒫)} ∪ {⋃Δ(𝒫(Z)): Z ∈ Ω(𝒫)∖Δ(𝒫)}`. Since `𝒫` is free and since `𝒫(Z)` is free and (3) holds
for each element `Z` of `Ω(𝒫)∖Δ(𝒫)`, it follows that `⋃𝔅` is a closed open subset of `M`. Hence `𝔅`
covers `M`."

The closedness of the union of the whole (uncountable) family is not argued. What the proof of
Theorem 1 uses afterwards is a finite subcover, and that can be obtained directly:
`C = Cl ⋃Δ(𝒫) ∖ ⋃Δ(𝒫)` is compact; each point of `C` lies in a member `Z` of `Ω(𝒫) ∖ Δ(𝒫)` (the
layer through it of its strand), hence in `⋃Δ(𝒫(Z))`; finitely many `⋃Δ(𝒫(Zᵢ))` cover `C`; then
`U = ⋃Δ(𝒫) ∪ ⋃ᵢ ⋃Δ(𝒫(Zᵢ))` is open and closed (`Cl ⋃Δ(𝒫(Zᵢ)) ⊆ ⋃𝒫(Zᵢ) ⊆ ⋃Δ(𝒫(Zᵢ)) ∪ ⋃Δ(𝒫)` by
freeness and (3)), so `U = M`.

* `isOpen_sUnion_delta5`: `⋃Δ(𝒫)` is open.
* `exists_finite_cover84_aux`: the finite cover, for any choice `Z ↦ 𝒫(Z)` of free regular chains
  with `Z ∈ Δ(𝒫(Z))` and (3).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Cover

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- `⋃Δ(𝒫) = ⋃𝒫 ∖ Cl(P 0 ∪ P 4)` is open. -/
theorem isOpen_sUnion_delta5 {P : Fin 5 → Set M} (hP : IsChain5 P) (hr : IsRegular5 P) :
    IsOpen (⋃₀ Delta5 P) := by
  rw [(delta5_partition hP hr).1]
  exact (isOpen_iUnion hP.isOpen).sdiff isClosed_closure

omit [CompactSpace M] [ConnectedSpace M] in
/-- `Cl ⋃Δ(Q) ⊆ ⋃Δ(Q) ∪ Cl(Q 0 ∪ Q 4)` for a free regular chain `Q`. -/
theorem closure_sUnion_delta5_subset {Q : Fin 5 → Set M} (hQ : IsChain5 Q) (hf : IsFree5 Q)
    (hr : IsRegular5 Q) : closure (⋃₀ Delta5 Q) ⊆ ⋃₀ Delta5 Q ∪ closure (Q 0 ∪ Q 4) := by
  intro y hy
  have hym := closure_delta_subset_mid hQ.isOpen hf hr hy
  by_cases hyc : y ∈ closure (Q 0 ∪ Q 4)
  · exact Or.inr hyc
  · left
    rw [(delta5_partition hQ hr).1]
    refine ⟨?_, hyc⟩
    rcases hym with (h | h) | h
    · exact mem_iUnion.2 ⟨1, h⟩
    · exact mem_iUnion.2 ⟨2, h⟩
    · exact mem_iUnion.2 ⟨3, h⟩

open Classical in
/-- **§5.2, the cover, finite form.** For a free normal regular chain `𝒫` and any choice
`Z ↦ Q Z` of free regular chains with `Z ∈ Δ(Q Z)` and `Cl(Q Z 0 ∪ Q Z 4) ⊆ ⋃Δ(𝒫)` (Hagopian's
(3)) for `Z ∈ Ω(𝒫) ∖ Δ(𝒫)`, finitely many `Zᵢ` give `M = ⋃Δ(𝒫) ∪ ⋃ᵢ ⋃Δ(Q Zᵢ)`. -/
theorem exists_finite_cover84_aux {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P)
    (hf : IsFree5 P) (hr : IsRegular5 P) (Q : Set M → Fin 5 → Set M)
    (hQ : ∀ Z ∈ Omega5 P, Z ∉ Delta5 P → IsChain5 (Q Z) ∧ IsFree5 (Q Z) ∧ IsRegular5 (Q Z) ∧
      Z ∈ Delta5 (Q Z) ∧ closure (Q Z 0 ∪ Q Z 4) ⊆ ⋃₀ Delta5 P) :
    ∃ S : Finset (Set M), (∀ Z ∈ S, Z ∈ Omega5 P ∧ Z ∉ Delta5 P) ∧
      ∀ y : M, y ∈ ⋃₀ Delta5 P ∨ ∃ Z ∈ S, y ∈ ⋃₀ Delta5 (Q Z) := by
  set O := ⋃₀ Delta5 P with hO
  have hOo : IsOpen O := isOpen_sUnion_delta5 hP hr
  set C := closure O \ O with hC
  have hCc : IsCompact C := (isClosed_closure.sdiff hOo).isCompact
  -- the index type
  let ι := {Z : Set M // Z ∈ Omega5 P ∧ Z ∉ Delta5 P}
  let U : ι → Set M := fun Z => ⋃₀ Delta5 (Q Z.1)
  have hUo : ∀ Z, IsOpen (U Z) := fun Z =>
    isOpen_sUnion_delta5 (hQ Z.1 Z.2.1 Z.2.2).1 (hQ Z.1 Z.2.1 Z.2.2).2.2.1
  -- each point of `C` lies in some `U Z`
  have hCU : C ⊆ ⋃ Z, U Z := by
    rintro q ⟨hqcl, hqO⟩
    have hqm : q ∈ midUnion P := closure_delta_subset_mid hP.isOpen hf hr hqcl
    obtain ⟨c, hc, -⟩ := hr q hqm
    have hqK : q ∈ closure (connectedComponentIn (midUnion P) q) :=
      subset_closure (mem_connectedComponentIn hqm)
    set Z := layer c (c ⟨q, hqK⟩) with hZ
    have hqZ : q ∈ Z := mem_layer_self84 c ⟨q, hqK⟩
    have hZΩ : Z ∈ Omega5 P := ⟨q, hqm, c, hc, _, rfl⟩
    have hZΔ : Z ∉ Delta5 P := fun h => hqO ⟨Z, h, hqZ⟩
    exact mem_iUnion.2 ⟨⟨Z, hZΩ, hZΔ⟩, Z, (hQ Z hZΩ hZΔ).2.2.2.1, hqZ⟩
  obtain ⟨t, ht⟩ := hCc.elim_finite_subcover U hUo hCU
  set V := O ∪ ⋃ i ∈ t, U i with hV
  have hVo : IsOpen V := hOo.union (isOpen_biUnion fun i _ => hUo i)
  have hVc : IsClosed V := by
    refine closure_subset_iff_isClosed.1 ?_
    rw [hV, closure_union, Finset.closure_biUnion]
    rintro y (hy | hy)
    · by_cases hyO : y ∈ O
      · exact Or.inl hyO
      · exact Or.inr (ht ⟨hy, hyO⟩)
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy
      obtain ⟨hQc, hQf, hQr, -, hQ3⟩ := hQ i.1 i.2.1 i.2.2
      rcases closure_sUnion_delta5_subset hQc hQf hQr hyi with h | h
      · exact Or.inr (mem_iUnion₂.2 ⟨i, hi, h⟩)
      · exact Or.inl (hQ3 h)
  -- `O` is nonempty
  have hOne : O.Nonempty := by
    obtain ⟨y, -, hy2⟩ := (hP.inter_iff 1 2).2 (by decide)
    refine ⟨y, ?_⟩
    rw [hO, (delta5_partition hP hr).1]
    exact ⟨mem_iUnion.2 ⟨2, hy2⟩, (closure_P2_subset hP hn hf (subset_closure hy2)).2⟩
  have hVu : V = univ := by
    rcases isClopen_iff.1 ⟨hVc, hVo⟩ with h | h
    · obtain ⟨y, hy⟩ := hOne
      exact absurd (h ▸ (Or.inl hy : y ∈ V)) (notMem_empty y)
    · exact h
  refine ⟨t.image Subtype.val, ?_, fun y => ?_⟩
  · intro Z hZ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hZ
    exact i.2
  · have hyV : y ∈ V := hVu ▸ mem_univ y
    rcases hyV with hy | hy
    · exact Or.inl hy
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy
      exact Or.inr ⟨i.1, Finset.mem_image_of_mem _ hi, hyi⟩

end Cover

end HPC.Hagopian
