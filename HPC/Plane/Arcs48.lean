import HPC.Plane.Thm5

/-!
# Batch 108: Bing 1948 (Amer. J. Math.), *Some characterizations of arcs and simple closed curves*,
# §2: Theorem 5 and Corollary 2; Duke 1951 Theorem 12 in Bing's generality

Saved from the uploaded skeleton as `HPC/Plane/Arcs48.lean`; `import HPC.Plane.Arcs48` is added at
the end of `HPC.lean`. Every item is proved, with no `sorry`.

Source: R. H. Bing, *Some characterizations of arcs and simple closed curves*, Amer. J. Math. 70
(1948) 497–506 — "the arcs paper", [4] of the Duke paper. Transcriptions in
COMMISSION-batch108.md §1. Everything is for a compact metric space `S` and continua `M ⊆ S`.

Shape changes from the skeleton (all recorded in `doc/batches/REPORT-batch108.md`):
* `Cuts` uses Bing's literal clause "`R` contains neither `A` nor `B`", i.e. `¬ A ⊆ R ∧ ¬ B ⊆ R`
  (p. 497), instead of disjointness. This makes `Cuts` weaker and Corollary 2 stronger; the proof
  of Corollary 2 does not use the clause at all, so it holds under either reading.
* `exists_irreducibleAbout` and `arcs_theorem5`: the hypothesis `IsClosed R` was not used and has
  been removed (Bing's Theorem 5 is stated for an arbitrary proper subset `R`).
* `condA_of_condB_general`, `theorem12_1951_general`: the hypothesis that `M` is a continuum was
  not used and has been removed.

The proof of Theorem 5 follows Bing's two cases. The second case is reorganised around
`Arcs48.exists_point_dense`: for a nonempty proper subcontinuum `N` of `M` there is `p ∈ M ∖ N`
such that the continua of `M ∖ {p}` containing `N` have dense union. Its proof is Bing's: the
sequence `N₁ ⊆ N₂ ⊆ …` (`Arcs48.tight_or_point`) either gives `p` directly, or its closure is a
proper subcontinuum not contained in the relative interior of any proper subcontinuum of `M`
(`Arcs48.Tight`); in the latter case Baire's theorem over the sets `E_i ∩ F_i` gives `p`
(`Arcs48.exists_point_of_tight`).
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **Bing's "cuts"** (p. 497): `R` *cuts `A` from `B` in `M`* if `M` contains a continuum
meeting both `A` and `B`, `R` contains neither `A` nor `B` (Bing's wording, read literally:
`A ⊄ R` and `B ⊄ R`), and `R` meets every continuum in `M` meeting both `A` and `B`. -/
def Cuts (M R A B : Set S) : Prop :=
  (∃ K : Set S, Fold.Q78.IsContinuum K ∧ K ⊆ M ∧ (K ∩ A).Nonempty ∧ (K ∩ B).Nonempty) ∧
    ¬ A ⊆ R ∧ ¬ B ⊆ R ∧
    ∀ K : Set S, Fold.Q78.IsContinuum K → K ⊆ M → (K ∩ A).Nonempty → (K ∩ B).Nonempty →
      (K ∩ R).Nonempty

/-- A continuum *irreducible about* `R`: contains `R`, and no proper subcontinuum does. -/
def IrreducibleAbout (N R : Set S) : Prop :=
  Fold.Q78.IsContinuum N ∧ R ⊆ N ∧ ∀ K : Set S, Fold.Q78.IsContinuum K → K ⊆ N → R ⊆ K → K = N

/-- Existence of a subcontinuum irreducible about a nonempty `R ⊆ M` (Zorn / Brouwer
reduction). The skeleton's hypothesis `IsClosed R` is not needed and has been removed. -/
theorem exists_irreducibleAbout {M R : Set S} (hM : Fold.Q78.IsContinuum M)
    (hRM : R ⊆ M) (hne : R.Nonempty) : ∃ N ⊆ M, IrreducibleAbout N R := by
  set 𝒮 : Set (Set S) := {W | W ⊆ M ∧ Fold.Q78.IsContinuum W ∧ R ⊆ W}
  obtain ⟨m, -, hm⟩ := zorn_superset_nonempty 𝒮 (fun c hcS hch hne' => by
    refine ⟨⋂₀ c, ⟨?_, ⟨?_, hne.mono ?_, ?_⟩, ?_⟩, fun W hW => sInter_subset_of_mem hW⟩
    · obtain ⟨W, hW⟩ := hne'
      exact (sInter_subset_of_mem hW).trans (hcS hW).1
    · exact (isClosed_sInter fun W hW => (hcS hW).2.1.1.isClosed).isCompact
    · exact subset_sInter fun W hW => (hcS hW).2.2
    · exact T14.isPreconnected_sInter_chain hne' hch (fun W hW => (hcS hW).2.1.1)
        (fun W hW => (hcS hW).2.1.2.isPreconnected)
    · exact subset_sInter fun W hW => (hcS hW).2.2) M ⟨subset_rfl, hM, hRM⟩
  obtain ⟨⟨hmM, hmc, hRm⟩, hmin⟩ := hm
  exact ⟨m, hmM, hmc, hRm, fun K hK hKm hRK =>
    Subset.antisymm hKm (hmin ⟨hKm.trans hmM, hK, hRK⟩ hKm)⟩

namespace Arcs48

omit [CompactSpace S] in
/-- A preconnected `M` which is not contained in the open set `O ∋ p` has a point of `O` other
than `p`. -/
theorem exists_other_point {M O : Set S} (hM : IsPreconnected M) (hO : IsOpen O) {p : S}
    (hpM : p ∈ M) (hpO : p ∈ O) (h : ¬ M ⊆ O) : ∃ x ∈ M, x ∈ O ∧ x ≠ p := by
  by_contra hcon
  push_neg at hcon
  have hcov : M ⊆ O ∪ {p}ᶜ := fun x _ => by
    by_cases hxp : x = p
    · exact Or.inl (hxp ▸ hpO)
    · exact Or.inr hxp
  have hdis : M ∩ (O ∩ {p}ᶜ) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff, mem_empty_iff_false, iff_false,
      not_and, not_not]
    exact fun hxM hxO => hcon x hxM hxO
  rcases isPreconnected_iff_subset_of_disjoint.mp hM O {p}ᶜ hO isClosed_singleton.isOpen_compl
    hcov hdis with h' | h'
  · exact h h'
  · exact h' hpM rfl

/-- `N` is *tight* in `M`: it lies in the relative interior of no proper subcontinuum of `M`. -/
def Tight (M N : Set S) : Prop :=
  ∀ K O : Set S, Fold.Q78.IsContinuum K → K ⊆ M → K ≠ M → IsOpen O → N ⊆ O → O ∩ M ⊆ K → False

/-- **Bing: "`F_i + N` is a continuum".** If `N ⊆ E ⊆ M` are continua and `N` is tight in `M`,
then `closure (M ∖ E) ∪ N` is preconnected. (A separation `X ∪ Y` with `N ⊆ X` makes `X ∪ E` a
proper subcontinuum of `M` containing the neighbourhood `M ∖ Y` of `N`.) -/
theorem isPreconnected_closure_diff_union {M N E : Set S} (hM : Fold.Q78.IsContinuum M)
    (hE : Fold.Q78.IsContinuum E) (hEM : E ⊆ M) (hN : Fold.Q78.IsContinuum N) (hNE : N ⊆ E)
    (ht : Tight M N) : IsPreconnected (closure (M \ E) ∪ N) := by
  set F := closure (M \ E) with hF_def
  set G := F ∪ N with hG_def
  have hFM : F ⊆ M := closure_minimal diff_subset hM.1.isClosed
  have hGM : G ⊆ M := union_subset hFM (hNE.trans hEM)
  have hGcl : IsClosed G := isClosed_closure.union hN.1.isClosed
  have key : ∀ u v : Set S, IsClosed u → IsClosed v → G ⊆ u ∪ v → Disjoint u v → N ⊆ u →
      G ⊆ u := by
    intro u v hu hv hGuv huv hNu
    by_contra hGu
    obtain ⟨y, hyG, hyu⟩ := not_subset.mp hGu
    have hyv : y ∈ v := (hGuv hyG).resolve_left hyu
    set Q := (G ∩ u) ∪ E with hQ_def
    have hQcl : IsClosed Q := (hGcl.inter hu).union hE.1.isClosed
    have hQM : Q ⊆ M := union_subset (inter_subset_left.trans hGM) hEM
    have main : ∀ a b : Set S, IsClosed a → IsClosed b → Q ⊆ a ∪ b → Disjoint a b → E ⊆ a →
        Q ⊆ a := by
      intro a b ha hb hQab hab hEa
      have hcov : M ⊆ (a ∪ (G ∩ v)) ∪ (Q ∩ b) := by
        intro x hxM
        by_cases hxQ : x ∈ Q
        · rcases hQab hxQ with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr ⟨hxQ, h⟩
        · have hxE : x ∉ E := fun h => hxQ (Or.inr h)
          have hxG : x ∈ G := Or.inl (subset_closure ⟨hxM, hxE⟩)
          rcases hGuv hxG with h | h
          · exact absurd (Or.inl ⟨hxG, h⟩) hxQ
          · exact Or.inl (Or.inr ⟨hxG, h⟩)
      have hdis : Disjoint (a ∪ (G ∩ v)) (Q ∩ b) := by
        rw [Set.disjoint_left]
        rintro z (hza | ⟨hzG, hzv⟩) ⟨hzQ, hzb⟩
        · exact disjoint_left.mp hab hza hzb
        · rcases hzQ with ⟨-, hzu⟩ | hzE
          · exact disjoint_left.mp huv hzu hzv
          · exact disjoint_left.mp hab (hEa hzE) hzb
      rcases (isPreconnected_iff_subset_of_fully_disjoint_closed hM.1.isClosed).mp
          hM.2.isPreconnected _ _ (ha.union (hGcl.inter hv)) (hQcl.inter hb) hcov hdis
        with h | h
      · intro z hzQ
        rcases hQab hzQ with hza | hzb
        · exact hza
        · rcases h (hQM hzQ) with hza | ⟨hzG, hzv⟩
          · exact hza
          · rcases hzQ with ⟨-, hzu⟩ | hzE
            · exact absurd hzv (disjoint_left.mp huv hzu)
            · exact hEa hzE
      · obtain ⟨e, he⟩ := hE.2.nonempty
        exact absurd (h (hEM he)).2 (disjoint_left.mp hab (hEa he))
    have hQconn : IsPreconnected Q := by
      rw [isPreconnected_iff_subset_of_fully_disjoint_closed hQcl]
      intro a b ha hb hQab hab
      rcases (isPreconnected_iff_subset_of_fully_disjoint_closed hE.1.isClosed).mp
          hE.2.isPreconnected a b ha hb (subset_union_right.trans hQab) hab with h | h
      · exact Or.inl (main a b ha hb hQab hab h)
      · exact Or.inr (main b a hb ha (by rwa [union_comm]) hab.symm h)
    have hQc : Fold.Q78.IsContinuum Q :=
      ⟨hQcl.isCompact, hE.2.nonempty.mono subset_union_right, hQconn⟩
    have hNO : N ⊆ vᶜ := fun x hx hxv => disjoint_left.mp huv (hNu hx) hxv
    have hOQ : vᶜ ∩ M ⊆ Q := by
      rintro x ⟨hxv, hxM⟩
      by_cases hxE : x ∈ E
      · exact Or.inr hxE
      · have hxG : x ∈ G := Or.inl (subset_closure ⟨hxM, hxE⟩)
        exact Or.inl ⟨hxG, (hGuv hxG).resolve_right hxv⟩
    have hQne : Q ≠ M := by
      obtain ⟨z, hzM, hzE, hzv⟩ : ∃ z ∈ M, z ∉ E ∧ z ∈ v := by
        by_contra hcon
        push_neg at hcon
        have hsub : M \ E ⊆ u := fun x ⟨hxM, hxE⟩ =>
          (hGuv (Or.inl (subset_closure ⟨hxM, hxE⟩))).resolve_right (hcon x hxM hxE)
        have hFu : F ⊆ u := closure_minimal hsub hu
        rcases hyG with h | h
        · exact hyu (hFu h)
        · exact hyu (hNu h)
      intro hQM'
      have hzQ : z ∈ Q := hQM'.symm ▸ hzM
      rcases hzQ with ⟨-, hzu⟩ | hzE'
      · exact disjoint_left.mp huv hzu hzv
      · exact hzE hzE'
    exact ht Q vᶜ hQc hQM hQne hv.isOpen_compl hNO hOQ
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hGcl]
  intro u v hu hv hGuv huv
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed hN.1.isClosed).mp
      hN.2.isPreconnected u v hu hv (subset_union_right.trans hGuv) huv with h | h
  · exact Or.inl (key u v hu hv hGuv huv h)
  · exact Or.inr (key v u hv hu (by rwa [union_comm]) huv.symm h)

/-- **One open set `D` of Bing's sequence, for tight `N`.** There is a closed set `Z` (Bing's
`E_i · F_i`) with empty relative interior in `M` such that every `p ∈ M ∖ (N ∪ Z)` misses a
continuum `G ⊆ M` containing `N` and meeting `closure D` (Bing's `G_i`: `E_i` or `F_i + N`). -/
theorem exists_nowhereDense_piece {M N D : Set S} (hM : Fold.Q78.IsContinuum M)
    (hN : Fold.Q78.IsContinuum N) (hNM : N ⊆ M) (ht : Tight M N) (hD : IsOpen D)
    (hDN : Disjoint D N) (hDM : (D ∩ M).Nonempty) :
    ∃ Z : Set S, IsClosed Z ∧ (∀ O : Set S, IsOpen O → O ∩ M ⊆ Z → O ∩ M = ∅) ∧
      ∀ p ∈ M, p ∉ N → p ∉ Z → ∃ G : Set S, Fold.Q78.IsContinuum G ∧ G ⊆ M ∧ N ⊆ G ∧
        p ∉ G ∧ (G ∩ closure D).Nonempty := by
  obtain ⟨n0, hn0⟩ := hN.2.nonempty
  have hFcl : IsClosed (M \ D) := hM.1.isClosed.sdiff hD
  have hFne : M \ D ≠ M := fun h => by
    obtain ⟨x, hxD, hxM⟩ := hDM
    have hx : x ∈ M \ D := h.symm ▸ hxM
    exact hx.2 hxD
  have hn0F : n0 ∈ M \ D := ⟨hNM hn0, fun h => disjoint_left.mp hDN h hn0⟩
  obtain ⟨K, hK, hKF, hn0K, hKb⟩ := exists_continuum_bump_closed hM hFcl diff_subset hFne hn0F
  set E := K ∪ N with hE_def
  have hE : Fold.Q78.IsContinuum E := isContinuum_union hK hN ⟨n0, hn0K, hn0⟩
  have hEMD : E ⊆ M \ D :=
    union_subset hKF (fun x hx => ⟨hNM hx, fun h => disjoint_left.mp hDN h hx⟩)
  have hEM : E ⊆ M := hEMD.trans diff_subset
  refine ⟨E ∩ closure (M \ E), hE.1.isClosed.inter isClosed_closure, ?_, ?_⟩
  · intro O hO hOZ
    by_contra hne
    obtain ⟨x, hxO, hxM⟩ := nonempty_iff_ne_empty.mpr hne
    obtain ⟨y, hyO, hyM, hyE⟩ := mem_closure_iff.mp (hOZ ⟨hxO, hxM⟩).2 O hO hxO
    exact hyE (hOZ ⟨hyO, hyM⟩).1
  · intro p hpM hpN hpZ
    by_cases hpE : p ∈ E
    · have hpF : p ∉ closure (M \ E) := fun h => hpZ ⟨hpE, h⟩
      refine ⟨closure (M \ E) ∪ N, ⟨(isClosed_closure.union hN.1.isClosed).isCompact,
        hN.2.nonempty.mono subset_union_right,
        isPreconnected_closure_diff_union hM hE hEM hN subset_union_right ht⟩,
        union_subset (closure_minimal diff_subset hM.1.isClosed) hNM, subset_union_right, ?_, ?_⟩
      · rintro (h | h)
        · exact hpF h
        · exact hpN h
      · obtain ⟨x, hxD, hxM⟩ := hDM
        exact ⟨x, Or.inl (subset_closure ⟨hxM, fun h => (hEMD h).2 hxD⟩), subset_closure hxD⟩
    · obtain ⟨x, hxK, hxcl⟩ := hKb
      refine ⟨E, hE, hEM, subset_union_right, hpE, x, Or.inl hxK, ?_⟩
      exact closure_mono (fun z hz => by_contra fun h => hz.2 ⟨hz.1, h⟩) hxcl

/-- **Bing's second case, for tight `N`** (the Baire argument). -/
theorem exists_point_of_tight {M N : Set S} (hM : Fold.Q78.IsContinuum M)
    (hN : Fold.Q78.IsContinuum N) (hNM : N ⊆ M) (hNne : N ≠ M) (ht : Tight M N) :
    ∃ p ∈ M, p ∉ N ∧ M ⊆ closure (⋃ K ∈ {K : Set S | Fold.Q78.IsContinuum K ∧ K ⊆ M ∧ p ∉ K ∧
      N ⊆ K}, K) := by
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis S
  have hZ : ∀ b : B, ∃ Z : Set S, IsClosed Z ∧
      (∀ O : Set S, IsOpen O → O ∩ M ⊆ Z → O ∩ M = ∅) ∧
      (Disjoint (b : Set S) N → ((b : Set S) ∩ M).Nonempty → ∀ p ∈ M, p ∉ N → p ∉ Z →
        ∃ G : Set S, Fold.Q78.IsContinuum G ∧ G ⊆ M ∧ N ⊆ G ∧ p ∉ G ∧
          (G ∩ closure (b : Set S)).Nonempty) := by
    intro b
    by_cases h : Disjoint (b : Set S) N ∧ ((b : Set S) ∩ M).Nonempty
    · obtain ⟨Z, h1, h2, h3⟩ := exists_nowhereDense_piece hM hN hNM ht (hB.isOpen b.2) h.1 h.2
      exact ⟨Z, h1, h2, fun _ _ => h3⟩
    · exact ⟨∅, isClosed_empty, fun O _ h => subset_empty_iff.mp h,
        fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Z hZcl hZnd hZG using hZ
  haveI : CompactSpace M := isCompact_iff_compactSpace.mp hM.1
  haveI : Countable B := hBc.to_subtype
  have hdense : Dense (⋂ b : B, {x : M | (x : S) ∉ Z b}) := by
    apply dense_iInter_of_isOpen
    · intro b
      exact (hZcl b).isOpen_compl.preimage continuous_subtype_val
    · intro b
      rw [dense_iff_inter_open]
      intro W hW hWne
      obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hW
      by_contra hcon
      rw [not_nonempty_iff_eq_empty] at hcon
      have hsub : O ∩ M ⊆ Z b := by
        rintro x ⟨hxO, hxM⟩
        by_contra hxZ
        have hx : (⟨x, hxM⟩ : M) ∈ (Subtype.val ⁻¹' O) ∩ {x : M | (x : S) ∉ Z b} := ⟨hxO, hxZ⟩
        rw [hcon] at hx
        exact hx
      obtain ⟨⟨x, hxM⟩, hxO⟩ := hWne
      have hx : x ∈ O ∩ M := ⟨hxO, hxM⟩
      rw [hZnd b O hO hsub] at hx
      exact hx
  have hopen : IsOpen {x : M | (x : S) ∉ N} :=
    hN.1.isClosed.isOpen_compl.preimage continuous_subtype_val
  have hne : ({x : M | (x : S) ∉ N}).Nonempty := by
    obtain ⟨x, hxM, hxN⟩ := not_subset.mp (fun h => hNne (Subset.antisymm hNM h))
    exact ⟨⟨x, hxM⟩, hxN⟩
  obtain ⟨⟨p, hpM⟩, hpN, hpZ⟩ := hdense.inter_open_nonempty _ hopen hne
  simp only [mem_iInter, mem_setOf_eq] at hpZ
  refine ⟨p, hpM, hpN, fun x hxM => ?_⟩
  by_cases hxN : x ∈ N
  · exact subset_closure (mem_biUnion (x := N) ⟨hN, hNM, hpN, subset_rfl⟩ hxN)
  rw [mem_closure_iff]
  intro O hO hxO
  obtain ⟨b, hbB, hxb, hbcl⟩ :=
    hB.exists_closure_subset ((hO.sdiff hN.1.isClosed).mem_nhds ⟨hxO, hxN⟩)
  have hbN : Disjoint b N :=
    disjoint_left.mpr fun y hyb hyN => (hbcl (subset_closure hyb)).2 hyN
  obtain ⟨G, hG, hGM, hNG, hpG, y, hyG, hycl⟩ :=
    hZG ⟨b, hbB⟩ hbN ⟨x, hxb, hxM⟩ p hpM hpN (hpZ ⟨b, hbB⟩)
  exact ⟨y, (hbcl hycl).1, mem_biUnion (x := G) ⟨hG, hGM, hpG, hNG⟩ hyG⟩

/-- **Bing's sequence `N₁ ⊆ N₂ ⊆ …`.** For a nonempty proper subcontinuum `N` of `M`: either the
required point exists outright (`⋃ N_i` dense, and then `⋃ N_i ≠ M` by compactness), or the
closure of `⋃ N_i` is a proper subcontinuum containing `N` which is tight in `M`. -/
theorem tight_or_point {M N : Set S} (hM : Fold.Q78.IsContinuum M)
    (hN : Fold.Q78.IsContinuum N) (hNM : N ⊆ M) (hNne : N ≠ M) :
    (∃ p ∈ M, p ∉ N ∧ M ⊆ closure (⋃ K ∈ {K : Set S | Fold.Q78.IsContinuum K ∧ K ⊆ M ∧ p ∉ K ∧
      N ⊆ K}, K)) ∨
    ∃ N' : Set S, Fold.Q78.IsContinuum N' ∧ N' ⊆ M ∧ N' ≠ M ∧ N ⊆ N' ∧ Tight M N' := by
  classical
  obtain ⟨n0, hn0⟩ := hN.2.nonempty
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis S
  have hBne : B.Nonempty := by
    have h : n0 ∈ ⋃₀ B := hB.sUnion_eq ▸ mem_univ n0
    obtain ⟨t, ht, -⟩ := h
    exact ⟨t, ht⟩
  obtain ⟨b, rfl⟩ := hBc.exists_eq_range hBne
  let P : Set S → ℕ → Set S → Prop := fun A j K => Fold.Q78.IsContinuum K ∧ K ⊆ M ∧ K ≠ M ∧
    ∃ O : Set S, IsOpen O ∧ A ∪ (b j ∩ M) ⊆ O ∧ O ∩ M ⊆ K
  let step : ℕ → Set S → Set S := fun j A => if h : ∃ K, P A j K then Classical.choose h else A
  let Ns : ℕ → Set S := fun n => Nat.rec N (fun j A => step j A) n
  have hNs_succ : ∀ j, Ns (j + 1) = step j (Ns j) := fun j => rfl
  have hbase : ∀ n, Fold.Q78.IsContinuum (Ns n) ∧ Ns n ⊆ M ∧ Ns n ≠ M := by
    intro n
    induction n with
    | zero => exact ⟨hN, hNM, hNne⟩
    | succ j ih =>
      rw [hNs_succ]
      simp only [step]
      split_ifs with h
      · have hs := Classical.choose_spec h
        exact ⟨hs.1, hs.2.1, hs.2.2.1⟩
      · exact ih
  have hchosen : ∀ j, (∃ K, P (Ns j) j K) → b j ∩ M ⊆ Ns (j + 1) ∧
      ∃ O : Set S, IsOpen O ∧ Ns j ⊆ O ∧ O ∩ M ⊆ Ns (j + 1) := by
    intro j h
    rw [hNs_succ]
    simp only [step, dif_pos h]
    obtain ⟨-, -, -, O, hO, hAO, hOK⟩ := Classical.choose_spec h
    exact ⟨fun x hx => hOK ⟨hAO (Or.inr hx), hx.2⟩, O, hO,
      fun x hx => hAO (Or.inl hx), hOK⟩
  have hnot : ∀ j, ¬ (∃ K, P (Ns j) j K) → Ns (j + 1) = Ns j := by
    intro j h
    rw [hNs_succ]
    simp only [step, dif_neg h]
  have hsucc : ∀ n, Ns n ⊆ Ns (n + 1) := by
    intro n
    by_cases h : ∃ K, P (Ns n) n K
    · obtain ⟨-, O, -, hO1, hO2⟩ := hchosen n h
      exact fun x hx => hO2 ⟨hO1 hx, (hbase n).2.1 hx⟩
    · rw [hnot n h]
  have hmono : Monotone Ns := monotone_nat_of_le_succ hsucc
  have hNsub : ∀ n, N ⊆ Ns n := fun n => hmono (Nat.zero_le n)
  set U := ⋃ n, Ns n with hU_def
  have hUM : U ⊆ M := iUnion_subset fun n => (hbase n).2.1
  have hNU : N ⊆ U := (hNsub 0).trans (subset_iUnion Ns 0)
  by_cases hcl : M ⊆ closure U
  · left
    have hUne : ¬ M ⊆ U := by
      intro hMU
      let W : ℕ → Set S := fun n => ⋃₀ {O : Set S | IsOpen O ∧ O ∩ M ⊆ Ns n}
      have hWo : ∀ n, IsOpen (W n) := fun n => isOpen_sUnion fun O hO => hO.1
      have hWM : ∀ n, W n ∩ M ⊆ Ns n := by
        rintro n x ⟨⟨O, hO, hxO⟩, hxM⟩
        exact hO.2 ⟨hxO, hxM⟩
      have hWmono : Monotone W := fun n m hnm => sUnion_subset_sUnion fun O hO =>
        ⟨hO.1, hO.2.trans (hmono hnm)⟩
      have hcov : M ⊆ ⋃ n, W n := by
        intro x hxM
        obtain ⟨i, hxi⟩ := mem_iUnion.mp (hMU hxM)
        obtain ⟨j, hij, hj⟩ : ∃ j, i ≤ j ∧ ∃ K, P (Ns j) j K := by
          by_contra hcon
          push_neg at hcon
          have hconst : ∀ k, Ns (i + k) = Ns i := by
            intro k
            induction k with
            | zero => rfl
            | succ k ih =>
              rw [← add_assoc, hnot (i + k) (fun ⟨K, hK⟩ => hcon (i + k) (Nat.le_add_right i k) K hK), ih]
          apply (hbase i).2.2
          refine Subset.antisymm (hbase i).2.1 fun y hyM => ?_
          obtain ⟨m, hym⟩ := mem_iUnion.mp (hMU hyM)
          rcases le_total m i with hmi | him
          · exact hmono hmi hym
          · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le him
            rwa [hconst k] at hym
        obtain ⟨-, O, hO, hO1, hO2⟩ := hchosen j hj
        exact mem_iUnion.mpr ⟨j + 1, ⟨O, ⟨hO, hO2⟩, hO1 (hmono hij hxi)⟩⟩
      obtain ⟨n, hn⟩ := hM.1.elim_directed_cover W hWo hcov hWmono.directed_le
      exact (hbase n).2.2 (Subset.antisymm (hbase n).2.1 fun x hx => hWM n ⟨hn hx, hx⟩)
    obtain ⟨p, hpM, hpU⟩ := not_subset.mp hUne
    refine ⟨p, hpM, fun h => hpU (hNU h), hcl.trans (closure_mono ?_)⟩
    exact iUnion_subset fun n y hy => mem_biUnion (x := Ns n)
      ⟨(hbase n).1, (hbase n).2.1, fun h => hpU (mem_iUnion.mpr ⟨n, h⟩), hNsub n⟩ hy
  · right
    have hUconn : IsPreconnected U :=
      isPreconnected_iUnion ⟨n0, mem_iInter.mpr fun n => hNsub n hn0⟩
        (fun n => (hbase n).1.2.2)
    refine ⟨closure U, ⟨isClosed_closure.isCompact, ⟨n0, subset_closure (hNU hn0)⟩,
      hUconn.closure⟩, closure_minimal hUM hM.1.isClosed, fun h => hcl h.ge,
      hNU.trans subset_closure, ?_⟩
    intro K O hK hKM hKne hO hN'O hOK
    obtain ⟨q, hqM, hqO, hqU⟩ : ∃ q ∈ M, q ∈ O ∧ q ∉ closure U := by
      by_contra hq
      push_neg at hq
      have hcov : M ⊆ O ∪ (closure U)ᶜ := fun x _ => by
        by_cases hx : x ∈ closure U
        · exact Or.inl (hN'O hx)
        · exact Or.inr hx
      have hdis : M ∩ (O ∩ (closure U)ᶜ) = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and,
          not_not]
        exact fun hxM hxO => hq x hxM hxO
      rcases isPreconnected_iff_subset_of_disjoint.mp hM.2.isPreconnected O (closure U)ᶜ hO
        isClosed_closure.isOpen_compl hcov hdis with h | h
      · exact hcl fun x hx => hq x hx (h hx)
      · exact h (hNM hn0) (subset_closure (hNU hn0))
    obtain ⟨_, ⟨j, rfl⟩, hqj, hjsub⟩ :=
      hB.exists_subset_of_mem_open (a := q) (u := O ∩ (closure U)ᶜ) ⟨hqO, hqU⟩
        (hO.inter isClosed_closure.isOpen_compl)
    have hPj : ∃ K', P (Ns j) j K' :=
      ⟨K, hK, hKM, hKne, O, hO,
        union_subset ((subset_iUnion Ns j).trans (subset_closure.trans hN'O))
          (inter_subset_left.trans (hjsub.trans inter_subset_left)), hOK⟩
    have hq := (hchosen j hPj).1 ⟨hqj, hqM⟩
    exact (hjsub hqj).2 (subset_closure (mem_iUnion.mpr ⟨j + 1, hq⟩))

/-- **The second case of Theorem 5, with `R` replaced by `N`.** For a nonempty proper
subcontinuum `N` of `M` there is `p ∈ M ∖ N` such that the union of the subcontinua of `M` which
contain `N` and miss `p` is dense in `M`. -/
theorem exists_point_dense {M N : Set S} (hM : Fold.Q78.IsContinuum M)
    (hN : Fold.Q78.IsContinuum N) (hNM : N ⊆ M) (hNne : N ≠ M) :
    ∃ p ∈ M, p ∉ N ∧ M ⊆ closure (⋃ K ∈ {K : Set S | Fold.Q78.IsContinuum K ∧ K ⊆ M ∧ p ∉ K ∧
      N ⊆ K}, K) := by
  rcases tight_or_point hM hN hNM hNne with h | ⟨N', hN', hN'M, hN'ne, hNN', ht⟩
  · exact h
  · obtain ⟨p, hpM, hpN', hd⟩ := exists_point_of_tight hM hN' hN'M hN'ne ht
    refine ⟨p, hpM, fun h => hpN' (hNN' h), hd.trans (closure_mono ?_)⟩
    exact biUnion_mono (fun K hK => ⟨hK.1, hK.2.1, hK.2.2.1, hNN'.trans hK.2.2.2⟩)
      (fun _ _ => subset_rfl)

end Arcs48

/-- **Arcs paper, Theorem 5.** For each proper subset `R` of the compact continuum `M`
(nonempty, so that the continua in question exist) there is `p ∈ M ∖ R` such that the union of all
continua lying in `M ∖ {p}` and meeting `R` is dense in `M`. The skeleton's hypothesis
`IsClosed R` is not needed and has been removed. -/
theorem arcs_theorem5 {M R : Set S} (hM : Fold.Q78.IsContinuum M) (hRM : R ⊆ M)
    (hne : R.Nonempty) (hRne : R ≠ M) :
    ∃ p ∈ M \ R, Dense
      ((↑) ⁻¹' (⋃ K ∈ {K : Set S | Fold.Q78.IsContinuum K ∧ K ⊆ M \ {p} ∧ (K ∩ R).Nonempty}, K) :
        Set M) := by
  suffices h : ∃ p ∈ M \ R, M ⊆ closure (⋃ K ∈ {K : Set S | Fold.Q78.IsContinuum K ∧
      K ⊆ M \ {p} ∧ (K ∩ R).Nonempty}, K) by
    obtain ⟨p, hp, hd⟩ := h
    refine ⟨p, hp, ?_⟩
    rw [Topology.IsInducing.subtypeVal.dense_iff]
    intro x
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr
      (iUnion₂_subset fun K hK => hK.2.1.trans diff_subset)]
    exact hd x.2
  obtain ⟨N, hNM, hN, hRN, hirr⟩ := exists_irreducibleAbout hM hRM hne
  by_cases hNeq : N = M
  · -- Bing's first case, `M = N`: any `p ∈ M ∖ R` works.
    obtain ⟨p, hpM, hpR⟩ := not_subset.mp (fun h : M ⊆ R => hRne (Subset.antisymm hRM h))
    refine ⟨p, ⟨hpM, hpR⟩, ?_⟩
    set V := ⋃ K ∈ {K : Set S | Fold.Q78.IsContinuum K ∧ K ⊆ M \ {p} ∧ (K ∩ R).Nonempty}, K
      with hV_def
    have hRV : R ⊆ V := fun r hr => mem_iUnion₂.mpr ⟨{r},
      ⟨isContinuum_singleton' r, singleton_subset_iff.mpr ⟨hRM hr, fun h => hpR (by
        rw [mem_singleton_iff] at h; exact h ▸ hr)⟩, ⟨r, rfl, hr⟩⟩, rfl⟩
    intro x hxM
    by_contra hx
    set O := (closure V)ᶜ with hO_def
    have hO : IsOpen O := isClosed_closure.isOpen_compl
    have hRO : ∀ r ∈ R, r ∉ O := fun r hr h => h (subset_closure (hRV hr))
    have hkey : ∀ K : Set S, Fold.Q78.IsContinuum K → K ⊆ M → (K ∩ R).Nonempty →
        (K ∩ O).Nonempty → p ∈ K := by
      rintro K hK hKM hKR ⟨y, hyK, hyO⟩
      by_contra hpK
      exact hyO (subset_closure (mem_biUnion (x := K) ⟨hK, fun z hz => ⟨hKM hz, fun h => hpK (by
        rw [mem_singleton_iff] at h; exact h ▸ hz)⟩, hKR⟩ hyK))
    have hMO : ¬ M ⊆ O := fun h => by
      obtain ⟨r, hr⟩ := hne
      exact hRO r hr (h (hRM hr))
    obtain ⟨x', hx'M, hx'O, hx'p⟩ : ∃ x' ∈ M, x' ∈ O ∧ x' ≠ p := by
      by_cases hxp : x = p
      · exact Arcs48.exists_other_point hM.2.isPreconnected hO (hxp ▸ hxM) (hxp ▸ hx) hMO
      · exact ⟨x, hxM, hx, hxp⟩
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO x' hx'O
    set δ := min (ε / 2) (dist x' p / 2) with hδ_def
    have hδ : 0 < δ := lt_min (half_pos hε) (half_pos (dist_pos.mpr hx'p))
    have hδε : δ ≤ ε / 2 := min_le_left _ _
    have hδp : δ ≤ dist x' p / 2 := min_le_right _ _
    set F := M \ Metric.ball x' δ with hF_def
    have hFcl : IsClosed F := hM.1.isClosed.sdiff Metric.isOpen_ball
    have hFne : F ≠ M := fun h => by
      have hx' : x' ∈ F := h ▸ hx'M
      exact hx'.2 (Metric.mem_ball_self hδ)
    have hpF : p ∈ F := ⟨hpM, fun h => by
      rw [Metric.mem_ball, dist_comm] at h
      have := dist_pos.mpr hx'p
      linarith⟩
    have hcl : closure (M \ F) ⊆ O := by
      have hsub : M \ F ⊆ Metric.closedBall x' δ := fun z hz => by
        have hz' : z ∈ Metric.ball x' δ := by
          by_contra h
          exact hz.2 ⟨hz.1, h⟩
        exact Metric.ball_subset_closedBall hz'
      refine (closure_minimal hsub Metric.isClosed_closedBall).trans fun z hz => hεO ?_
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hRF : R ⊆ F := fun r hr => ⟨hRM hr, fun h => hRO r hr
      (hεO (Metric.ball_subset_ball (hδε.trans (half_le_self hε.le)) h))⟩
    have hK : ∀ r ∈ R, ∃ K : Set S, Fold.Q78.IsContinuum K ∧ K ⊆ F ∧ r ∈ K ∧ p ∈ K := by
      intro r hr
      obtain ⟨K, hK, hKF, hrK, y, hyK, hycl⟩ :=
        exists_continuum_bump_closed hM hFcl diff_subset hFne (hRF hr)
      exact ⟨K, hK, hKF, hrK, hkey K hK (hKF.trans diff_subset) ⟨r, hrK, hr⟩ ⟨y, hyK, hcl hycl⟩⟩
    choose! K hKc hKF hrK hpK using hK
    set C := closure (⋃ r : ↥R, K r.1) with hC_def
    obtain ⟨r0, hr0⟩ := hne
    have hCc : Fold.Q78.IsContinuum C :=
      ⟨isClosed_closure.isCompact, ⟨r0, subset_closure (mem_iUnion.mpr ⟨⟨r0, hr0⟩, hrK r0 hr0⟩)⟩,
        (isPreconnected_iUnion (s := fun r : ↥R => K r.1) ⟨p, mem_iInter.mpr fun r => hpK r r.2⟩
          fun r => (hKc r r.2).2.2).closure⟩
    have hCF : C ⊆ F := closure_minimal (iUnion_subset fun r => hKF r r.2) hFcl
    have hRC : R ⊆ C := fun r hr => subset_closure (mem_iUnion.mpr ⟨⟨r, hr⟩, hrK r hr⟩)
    have hCN : C = N := hirr C hCc (hNeq ▸ hCF.trans diff_subset) hRC
    exact hFne (Subset.antisymm diff_subset (hNeq ▸ hCN ▸ hCF))
  · -- Bing's second case, `M ≠ N`.
    obtain ⟨p, hpM, hpN, hd⟩ := Arcs48.exists_point_dense hM hN hNM hNeq
    refine ⟨p, ⟨hpM, fun h => hpN (hRN h)⟩, hd.trans (closure_mono (biUnion_mono ?_
      fun _ _ => subset_rfl))⟩
    rintro K ⟨hK, hKM, hpK, hNK⟩
    obtain ⟨r, hr⟩ := hne
    exact ⟨hK, fun z hz => ⟨hKM hz, fun h => hpK (by
      rw [mem_singleton_iff] at h; exact h ▸ hz)⟩, ⟨r, hNK (hRN hr), hr⟩⟩

/-- The point case used by Duke Theorem 12: `R = {r}`, in the form "`M ⊆ closure (⋃ …)`". -/
theorem arcs_theorem5_point {M : Set S} (hM : Fold.Q78.IsContinuum M) (hnd : M.Nontrivial)
    {r : S} (hr : r ∈ M) :
    ∃ p ∈ M, p ≠ r ∧ M ⊆ closure (⋃ K ∈ {K : Set S | Fold.Q78.IsContinuum K ∧ K ⊆ M ∧ p ∉ K ∧ r ∈ K}, K) := by
  obtain ⟨p, hpM, hpr, hd⟩ := Arcs48.exists_point_dense hM (isContinuum_singleton' r)
    (singleton_subset_iff.mpr hr) (fun h => hnd.ne_singleton h.symm)
  exact ⟨p, hpM, fun h => hpr h, hd.trans (closure_mono (biUnion_mono
    (fun K hK => ⟨hK.1, hK.2.1, hK.2.2.1, hK.2.2.2 rfl⟩) fun _ _ => subset_rfl))⟩

/-- **Arcs paper, Corollary 2.** Each nondegenerate compact continuum contains two points neither
of which cuts between two open subsets of the continuum. (Theorem 5 with `R = {r}` applied twice:
first at any `r`, giving `p`, then at `r = p`, giving `q ≠ p`; a point `p` given by Theorem 5 cuts
no two nonempty open subsets, because two continua through `r` missing `p` reach them.) -/
theorem arcs_corollary2 {M : Set S} (hM : Fold.Q78.IsContinuum M) (hnd : M.Nontrivial) :
    ∃ p q : S, p ∈ M ∧ q ∈ M ∧ p ≠ q ∧
      (∀ D E : Set S, IsOpen D → IsOpen E → (D ∩ M).Nonempty → (E ∩ M).Nonempty →
        ¬ Cuts M {p} (D ∩ M) (E ∩ M)) ∧
      (∀ D E : Set S, IsOpen D → IsOpen E → (D ∩ M).Nonempty → (E ∩ M).Nonempty →
        ¬ Cuts M {q} (D ∩ M) (E ∩ M)) := by
  have key : ∀ r ∈ M, ∃ p ∈ M, p ≠ r ∧ ∀ D E : Set S, IsOpen D → IsOpen E →
      (D ∩ M).Nonempty → (E ∩ M).Nonempty → ¬ Cuts M {p} (D ∩ M) (E ∩ M) := by
    intro r hr
    obtain ⟨p, hpM, hpr, hd⟩ := arcs_theorem5_point hM hnd hr
    refine ⟨p, hpM, hpr, fun D E hD hE hDM hEM hcut => ?_⟩
    have hmeet : ∀ D : Set S, IsOpen D → (D ∩ M).Nonempty → ∃ K : Set S,
        Fold.Q78.IsContinuum K ∧ K ⊆ M ∧ p ∉ K ∧ r ∈ K ∧ (K ∩ (D ∩ M)).Nonempty := by
      rintro D hD ⟨x, hxD, hxM⟩
      obtain ⟨y, hyD, hyV⟩ := mem_closure_iff.mp (hd hxM) D hD hxD
      obtain ⟨K, ⟨hK, hKM, hpK, hrK⟩, hyK⟩ := mem_iUnion₂.mp hyV
      exact ⟨K, hK, hKM, hpK, hrK, y, hyK, hyD, hKM hyK⟩
    obtain ⟨K1, hK1, hK1M, hpK1, hrK1, hK1D⟩ := hmeet D hD hDM
    obtain ⟨K2, hK2, hK2M, hpK2, hrK2, hK2E⟩ := hmeet E hE hEM
    obtain ⟨z, hzK, hzp⟩ := hcut.2.2.2 (K1 ∪ K2) (isContinuum_union hK1 hK2 ⟨r, hrK1, hrK2⟩)
      (union_subset hK1M hK2M) (hK1D.mono (inter_subset_inter_left _ subset_union_left))
      (hK2E.mono (inter_subset_inter_left _ subset_union_right))
    rw [mem_singleton_iff] at hzp
    subst hzp
    rcases hzK with h | h
    · exact hpK1 h
    · exact hpK2 h
  obtain ⟨r, hr⟩ := hnd.nonempty
  obtain ⟨p, hpM, -, hp⟩ := key r hr
  obtain ⟨q, hqM, hqp, hq⟩ := key p hpM
  exact ⟨p, q, hpM, hqM, fun h => hqp h.symm, hp, hq⟩

/-- **Duke 1951, Theorem 12, B ⇒ A, in Bing's generality**, by his own proof: for a
nondegenerate subcontinuum `W ∋ p` of `M`, Theorem 5 gives `q ≠ p` with the continua in `W ∖ {q}`
through `p` dense in `W`; under condition B each of them lies in any subcontinuum `H ⊆ W`
through `p` and `q` (the alternative `H ⊆ K` is excluded by `q`), so `W ⊆ closure ⋃ ⊆ H`. The
skeleton's hypothesis that `M` is a continuum is not needed and has been removed. -/
theorem condA_of_condB_general {M : Set S} {p : S} (hp : CondB M p) : CondA M p := by
  refine ⟨hp.1, fun W hWM hW hnt hpW => ?_⟩
  obtain ⟨q, hqW, hqp, hd⟩ := arcs_theorem5_point hW hnt hpW
  refine ⟨q, hqp, hW, hpW, hqW, fun H hH hHW hpH hqH => Subset.antisymm hHW ?_⟩
  refine hd.trans (closure_minimal (iUnion₂_subset fun K hK => ?_) hH.1.isClosed)
  obtain ⟨hK, hKW, hqK, hpK⟩ := hK
  rcases hp.2 K H (hKW.trans hWM) (hHW.trans hWM) hK hH hpK hpH with h | h
  · exact h
  · exact absurd (h hqH) hqK

/-- **Duke 1951, Theorem 12** (both directions) for any `M` in a compact metric space; A ⇒ B is
batch 85's `condB_of_condA`. -/
theorem theorem12_1951_general {M : Set S} (p : S) : CondA M p ↔ CondB M p :=
  ⟨condB_of_condA, condA_of_condB_general⟩

end HPC.Plane
