import HPC.Hagopian.H84Delta

/-!
# Batch 186, §3.2: Lemma 12 of Hagopian 1984

Hagopian's construction (p. 339): `A = L 0 ∖ Cl L 1`, `B = L 4 ∖ Cl L 3`; Moore 1962 Theorem 44
(`exists_closed_split_of_no_connected`) in `K = M ∖ (A ∪ B)` separates `E ∖ (A ∪ B)` (inside a
closed `H`) from `M ∖ ⋃𝔏` (inside a closed `L'`), `H ∪ L' = K`, `H ∩ L' = ∅`; the refinement is
`P = (L 0, L 1 ∖ L', L 2 ∖ L', L 3 ∖ L', L 4)` (Hagopian's `C ∩ Lᵢ` with `C = M ∖ L'`).

* *No connected set meets both* (Hagopian: "Since `𝔏` is regular, `E∖(A ∪ B)` is an essential
  subcontinuum of `E`. Since `M` is atriodic, `E∖(A ∪ B)` is a component of `M∖(A ∪ B)`"): the
  closure of such a set is a continuum in `K` meeting `E` and missing both end layers of `E` (they
  lie in `A` and `B`), so it lies in `E` (`subset_of_meets_avoids`), but it meets `M ∖ ⋃𝔏`. The
  essential-subcontinuum step is not needed.
* *Running straight* transfers from `𝔏` to `𝒫` for a continuum whose points in `⋃𝔏′` miss `L'` and
  whose layers either miss `L'` or meet `A ∪ B` (`runsStraight_refine`); near a point off `L'` the
  links `Lᵢ ∖ L'` and `Lᵢ` have the same frontier.
* *Regularity*: each component of `⋃𝒫′` is a component of `⋃𝔏′` (components of `⋃𝔏′` lie in `H` or
  in `L'`), and its closure lies in `H`.
* *Freeness* as in commission 186 §3.2.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Lemma12

variable {M : Set Pt}

/-- Consecutive links of a chain meet along a connected set running from `L 0` to `L 4`. -/
theorem chain_consecutive_meet {L : Fin 5 → Set M} (hL : IsChain5 L) {S : Set M}
    (hS : IsPreconnected S) (hSL : S ⊆ ⋃ i, L i) (h0 : (S ∩ L 0).Nonempty)
    (h4 : (S ∩ L 4).Nonempty) (i : ℕ) (hi : i < 4) :
    (S ∩ L ⟨i, by omega⟩ ∩ L ⟨i + 1, by omega⟩).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  set U := ⋃ (j : Fin 5) (_ : (j : ℕ) ≤ i), L j with hU
  set V := ⋃ (j : Fin 5) (_ : i < (j : ℕ)), L j with hV
  have hUo : IsOpen U := isOpen_biUnion fun j _ => hL.isOpen j
  have hVo : IsOpen V := isOpen_biUnion fun j _ => hL.isOpen j
  have hcov : S ⊆ U ∪ V := by
    intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hSL hz)
    rcases le_or_gt (j : ℕ) i with h | h
    · exact Or.inl (mem_biUnion h hj)
    · exact Or.inr (mem_biUnion h hj)
  have key : ∀ z ∈ S, z ∈ U → z ∈ V → False := by
    intro z hz hzU hzV
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.1 hzU
    obtain ⟨j', hj', hzj'⟩ := mem_iUnion₂.1 hzV
    have hadj := (hL.inter_iff j j').1 ⟨z, hzj, hzj'⟩
    have e1 : j = ⟨i, by omega⟩ := Fin.ext (by simp only; omega)
    have e2 : j' = ⟨i + 1, by omega⟩ := Fin.ext (by simp only; omega)
    rw [e1] at hzj
    rw [e2] at hzj'
    exact (not_nonempty_iff_eq_empty.2 hne) ⟨z, ⟨hz, hzj⟩, hzj'⟩
  have hdisj : S ∩ (U ∩ V) = ∅ :=
    eq_empty_iff_forall_notMem.2 fun z ⟨hz, hzU, hzV⟩ => key z hz hzU hzV
  rcases isPreconnected_iff_subset_of_disjoint.1 hS U V hUo hVo hcov hdisj with h | h
  · obtain ⟨z, hz, hz4⟩ := h4
    exact key z hz (h hz) (mem_biUnion (show i < ((4 : Fin 5) : ℕ) by simp; omega) hz4)
  · obtain ⟨z, hz, hz0⟩ := h0
    exact key z hz (mem_biUnion (show ((0 : Fin 5) : ℕ) ≤ i by simp) hz0) (h hz)

/-- Off a closed set `L'`, the link `Lᵢ ∖ L'` has the frontier of `Lᵢ`. -/
theorem mem_frontier_diff_iff {S L' : Set M} (hL' : IsClosed L') {y : M} (hy : y ∉ L') :
    y ∈ frontier (S \ L') ↔ y ∈ frontier S := by
  have hO : IsOpen L'ᶜ := hL'.isOpen_compl
  have hcl : y ∈ closure (S \ L') ↔ y ∈ closure S := by
    refine ⟨fun h => closure_mono diff_subset h, fun h => ?_⟩
    have := hO.inter_closure ⟨hy, h⟩
    rw [inter_comm] at this
    exact this
  have hint : y ∈ interior (S \ L') ↔ y ∈ interior S := by
    rw [diff_eq, interior_inter, hO.interior_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩
  simp only [frontier, mem_diff, hcl, hint]

/-- The refined chain of Lemma 12. -/
def refineChain (L : Fin 5 → Set M) (L' : Set M) : Fin 5 → Set M :=
  ![L 0, L 1 \ L', L 2 \ L', L 3 \ L', L 4]

theorem refineChain_subset (L : Fin 5 → Set M) (L' : Set M) (i : Fin 5) :
    refineChain L L' i ⊆ L i := by
  fin_cases i <;> simp [refineChain, diff_subset]

theorem refineChain_mid (L : Fin 5 → Set M) (L' : Set M) :
    midUnion (refineChain L L') = midUnion L \ L' := by
  simp only [midUnion, refineChain, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [union_diff_distrib, union_diff_distrib]
  rfl

theorem mem_refineChain_of {L : Fin 5 → Set M} {L' : Set M} {i : Fin 5} {z : M} (hz : z ∈ L i)
    (hmid : z ∈ midUnion L → z ∉ L') : z ∈ refineChain L L' i := by
  fin_cases i
  · exact hz
  · exact ⟨hz, hmid (Or.inl (Or.inl hz))⟩
  · exact ⟨hz, hmid (Or.inl (Or.inr hz))⟩
  · exact ⟨hz, hmid (Or.inr hz)⟩
  · exact hz

/-- **Running straight transfers to the refinement.** -/
theorem runsStraight_refine {L : Fin 5 → Set M} (hL : IsChain5 L) (hn : IsNormal5 L) {L' : Set M}
    (hL' : IsClosed L') {G : Set M} {d : G → unitInterval} (hd : IsAdmissibleMap G d)
    (hs : RunsStraight d L)
    (ha : ∀ g ∈ G, g ∈ midUnion L → g ∉ L')
    (hb : ∀ r, layer d r ⊆ L'ᶜ ∨ (layer d r ∩ ((L 0 \ closure (L 1)) ∪ (L 4 \ closure (L 3)))).Nonempty) :
    RunsStraight d (refineChain L L') := by
  have hLo := hL.isOpen
  refine ⟨fun g hg => ?_, fun z hz => ?_, fun z hz => ?_, fun r i hri => ?_, fun r t i hrt hrti => ?_⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (hs.1 hg)
    exact mem_iUnion.2 ⟨i, mem_refineChain_of hi (ha g hg)⟩
  · exact ⟨(hs.2.1 hz).1, fun h => (hs.2.1 hz).2 (refineChain_subset L L' 1 h)⟩
  · exact ⟨(hs.2.2.1 hz).1, fun h => (hs.2.2.1 hz).2 (refineChain_subset L L' 3 h)⟩
  · -- condition (4)
    have hfr_sub : ∀ j : Fin 5, frontier (refineChain L L' j) ⊆ closure (L j) := fun j =>
      frontier_subset_closure.trans (closure_mono (refineChain_subset L L' j))
    -- a layer meeting `A ∪ B` misses the closures of the middle links
    have hmidmiss : (layer d r ∩ ((L 0 \ closure (L 1)) ∪ (L 4 \ closure (L 3)))).Nonempty →
        ∀ j : Fin 5, j ≠ 0 → j ≠ 4 → Disjoint (layer d r) (closure (L j)) := by
      rintro ⟨a, har, ha'⟩ j hj0 hj4
      refine layer_disjoint_closure_of_mem hd hLo hs har fun haj => ?_
      rcases ha' with ⟨haL, ha1⟩ | ⟨haL, ha3⟩
      · fin_cases j
        · exact hj0 rfl
        · exact ha1 haj
        · exact disjoint_left.1 (hn 0 2 (by decide)) (subset_closure haL) haj
        · exact disjoint_left.1 (hn 0 3 (by decide)) (subset_closure haL) haj
        · exact hj4 rfl
      · fin_cases j
        · exact hj0 rfl
        · exact disjoint_left.1 (hn 1 4 (by decide)) haj (subset_closure haL)
        · exact disjoint_left.1 (hn 2 4 (by decide)) haj (subset_closure haL)
        · exact ha3 haj
        · exact hj4 rfl
    have hmid_case : ∀ j : Fin 5, j ≠ 0 → j ≠ 4 → refineChain L L' j = L j \ L' := by
      intro j hj0 hj4
      fin_cases j <;> first | exact absurd rfl hj0 | exact absurd rfl hj4 | rfl
    by_cases hi0 : i = 0
    · subst hi0; exact hs.2.2.2.1 r 0 hri
    by_cases hi4 : i = 4
    · subst hi4; exact hs.2.2.2.1 r 4 hri
    rw [hmid_case i hi0 hi4] at hri ⊢
    rcases hb r with hoff | hmeet
    · obtain ⟨y, hyr, hyf⟩ := hri
      have hyf' := (mem_frontier_diff_iff hL' (hoff hyr)).1 hyf
      intro z hz
      exact (mem_frontier_diff_iff hL' (hoff hz)).2 (hs.2.2.2.1 r i ⟨y, hyr, hyf'⟩ hz)
    · obtain ⟨y, hyr, hyf⟩ := hri
      have := hfr_sub i
      rw [hmid_case i hi0 hi4] at this
      exact absurd (this hyf) (disjoint_left.1 (hmidmiss hmeet i hi0 hi4) hyr)
  · -- condition (5)
    have hsub := hs.2.2.2.2 r t i hrt
      (hrti.trans (refineChain_subset L L' i))
    intro z hz
    refine mem_refineChain_of (hsub hz) (ha z ?_)
    obtain ⟨w, -, rfl⟩ := hz
    exact w.2

variable [CompactSpace M] [ConnectedSpace M]

/-- **Lemma 12** (p. 339). Shape of the skeleton; the conclusion is strengthened by "every component
of `⋃𝒫′` is a component of `⋃𝔏′`" (allowed by the commission). -/
theorem hagopian84_lemma12_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {L : Fin 5 → Set M} (hL : IsChain5 L)
    (hn : IsNormal5 L) (hr : IsRegular5 L) (hs : RunsStraight k L)
    (h0 : layer k 0 ⊆ L 0 \ closure (L 1)) (h1 : layer k 1 ⊆ L 4 \ closure (L 3)) :
    ∃ P, IsOrderedRefinement5 P L ∧ IsFree5 P ∧ IsNormal5 P ∧ IsRegular5 P ∧ RunsStraight k P ∧
      ∀ x ∈ midUnion P, connectedComponentIn (midUnion P) x =
        connectedComponentIn (midUnion L) x := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  have hLo := hL.isOpen
  set A := L 0 \ closure (L 1) with hA
  set B := L 4 \ closure (L 3) with hB
  have hAo : IsOpen A := (hLo 0).sdiff isClosed_closure
  have hBo : IsOpen B := (hLo 4).sdiff isClosed_closure
  set K := (A ∪ B)ᶜ with hK
  have hKc : IsClosed K := (hAo.union hBo).isClosed_compl
  have hEc : IsCompact E := hE.isCompact
  have hEcont : Fold.Q78.IsContinuum E := hE.1.choose_spec.choose_spec.1
  -- the middle links lie in `K`
  have hmidK : midUnion L ⊆ K := by
    rintro z hz (⟨hz0, hz1⟩ | ⟨hz4, hz3⟩)
    · rcases hz with (h | h) | h
      · exact hz1 (subset_closure h)
      · exact disjoint_left.1 (chain5_disjoint hL 0 2 (by decide)) hz0 h
      · exact disjoint_left.1 (chain5_disjoint hL 0 3 (by decide)) hz0 h
    · rcases hz with (h | h) | h
      · exact disjoint_left.1 (chain5_disjoint hL 1 4 (by decide)) h hz4
      · exact disjoint_left.1 (chain5_disjoint hL 2 4 (by decide)) h hz4
      · exact hz3 (subset_closure h)
  -- Moore 1962, Theorem 44
  have hno : ∀ Z ⊆ K, IsPreconnected Z → (Z ∩ (E ∩ K)).Nonempty →
      (Z ∩ (⋃ i, L i)ᶜ).Nonempty → False := by
    rintro Z hZK hZ ⟨p, hpZ, hpE, -⟩ ⟨q, hqZ, hq⟩
    have hCc : Fold.Q78.IsContinuum (closure Z) :=
      ⟨isClosed_closure.isCompact, ⟨p, subset_closure hpZ⟩, hZ.closure⟩
    have hCK : closure Z ⊆ K := closure_minimal hZK hKc
    have hsub := subset_of_meets_avoids hHU hAT hEcont hE.2.1 hCc ⟨p, hpE, subset_closure hpZ⟩
      (by
        rw [disjoint_left]
        intro z hz hz'
        rcases hz' with hz' | hz'
        · exact hCK hz (Or.inl (h0 hz'))
        · exact hCK hz (Or.inr (h1 hz')))
    exact hq (hs.1 (hsub (subset_closure hqZ)))
  obtain ⟨H, L', hHc, hL'c, hHL, hHLd, hPH, hQL⟩ :=
    exists_closed_split_of_no_connected hKc.isCompact (hEc.isClosed.inter hKc)
      (isOpen_iUnion hLo).isClosed_compl inter_subset_right
      (fun z hz hzK => hz (by
        rcases hzK with ⟨h, -⟩ | ⟨h, -⟩
        · exact mem_iUnion.2 ⟨0, h⟩
        · exact mem_iUnion.2 ⟨4, h⟩)) hno
  have hHK : H ⊆ K := hHL ▸ subset_union_left
  have hHL' : ∀ z ∈ H, z ∉ L' := fun z hz hz' => disjoint_left.1 hHLd hz hz'
  have hHU' : H ⊆ ⋃ i, L i := fun z hz => by
    by_contra hc
    exact hHL' z hz (hQL hc)
  set P := refineChain L L' with hPdef
  have hPo : ∀ i, IsOpen (P i) := by
    intro i
    fin_cases i
    · exact hLo 0
    · exact (hLo 1).sdiff hL'c
    · exact (hLo 2).sdiff hL'c
    · exact (hLo 3).sdiff hL'c
    · exact hLo 4
  have hEmid : ∀ e ∈ E, e ∈ midUnion L → e ∉ L' := fun e he hm =>
    hHL' e (hPH ⟨he, hmidK hm⟩)
  have hEP : ∀ e ∈ E, ∀ i, e ∈ L i → e ∈ P i := fun e he i hei =>
    mem_refineChain_of hei (hEmid e he)
  -- consecutive links of `P` meet
  have hcons : ∀ (i : ℕ) (hi : i < 4), (P ⟨i, by omega⟩ ∩ P ⟨i + 1, by omega⟩).Nonempty := by
    intro i hi
    obtain ⟨z, layer_k0⟩ := layer_nonempty' hE.2.1 0
    obtain ⟨z', layer_k1⟩ := layer_nonempty' hE.2.1 1
    obtain ⟨e, ⟨heE, he1⟩, he2⟩ := chain_consecutive_meet hL hEcont.2.isPreconnected hs.1
      ⟨z, layer_subset_set k 0 layer_k0, (hs.2.1 layer_k0).1⟩
      ⟨z', layer_subset_set k 1 layer_k1, (hs.2.2.1 layer_k1).1⟩ i hi
    exact ⟨e, hEP e heE _ he1, hEP e heE _ he2⟩
  have hchain : IsChain5 P := by
    refine ⟨hPo, fun i j => ⟨fun h => ?_, fun h => ?_⟩⟩
    · obtain ⟨z, hzi, hzj⟩ := h
      exact (hL.inter_iff i j).1 ⟨z, refineChain_subset L L' i hzi, refineChain_subset L L' j hzj⟩
    · rcases Nat.lt_trichotomy (i : ℕ) j with hij | hij | hij
      · have hj : (j : ℕ) = i + 1 := by omega
        have := hcons i (by omega)
        have e1 : (⟨i, by omega⟩ : Fin 5) = i := Fin.ext rfl
        have e2 : (⟨(i : ℕ) + 1, by omega⟩ : Fin 5) = j := Fin.ext hj.symm
        rwa [e1, e2] at this
      · have hij' : i = j := Fin.ext hij
        subst hij'
        rcases Nat.lt_or_ge (i : ℕ) 4 with h4 | h4
        · obtain ⟨z, hz, -⟩ := hcons i h4
          have e1 : (⟨i, by omega⟩ : Fin 5) = i := Fin.ext rfl
          rw [e1] at hz
          exact ⟨z, hz, hz⟩
        · obtain ⟨z, -, hz⟩ := hcons 3 (by omega)
          have e1 : (⟨3 + 1, by omega⟩ : Fin 5) = i := Fin.ext (by have := i.isLt; simp; omega)
          rw [e1] at hz
          exact ⟨z, hz, hz⟩
      · have hi : (i : ℕ) = j + 1 := by omega
        have := hcons j (by omega)
        have e1 : (⟨j, by omega⟩ : Fin 5) = j := Fin.ext rfl
        have e2 : (⟨(j : ℕ) + 1, by omega⟩ : Fin 5) = i := Fin.ext hi.symm
        rw [e1, e2] at this
        obtain ⟨z, h1, h2⟩ := this
        exact ⟨z, h2, h1⟩
  -- components of `⋃𝒫′`
  have hcc : ∀ x ∈ midUnion P, connectedComponentIn (midUnion P) x =
      connectedComponentIn (midUnion L) x ∧ connectedComponentIn (midUnion L) x ⊆ H := by
    intro x hx
    rw [hPdef, refineChain_mid] at hx
    set C := connectedComponentIn (midUnion L) x
    have hCK : C ⊆ H ∪ L' := hHL ▸ (connectedComponentIn_subset _ _).trans hmidK
    have hCH : C ⊆ H := by
      rcases isPreconnected_iff_subset_of_disjoint_closed.1 isPreconnected_connectedComponentIn
          H L' hHc hL'c hCK (by
            rw [eq_empty_iff_forall_notMem]
            rintro z ⟨-, hzH, hzL⟩
            exact hHL' z hzH hzL) with h | h
      · exact h
      · exact absurd (h (mem_connectedComponentIn hx.1)) hx.2
    refine ⟨Subset.antisymm (connectedComponentIn_mono _ (by
      rw [hPdef, refineChain_mid]; exact diff_subset)) ?_, hCH⟩
    refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx.1) ?_
    rw [hPdef, refineChain_mid]
    exact fun z hz => ⟨connectedComponentIn_subset _ _ hz, hHL' z (hCH hz)⟩
  refine ⟨P, ⟨hchain, refineChain_subset L L'⟩, ?_, ?_, ?_, ?_, fun x hx => (hcc x hx).1⟩
  · -- free
    intro y hy
    have hUo : IsOpen (⋃ i, P i) := isOpen_iUnion hPo
    have hyU : y ∉ ⋃ i, P i := by
      have := hy.2; rwa [hUo.interior_eq] at this
    have hUeq : (⋃ i, P i) = (P 0 ∪ P 4) ∪ midUnion P := by
      ext z
      simp only [mem_iUnion, mem_union, midUnion]
      constructor
      · rintro ⟨i, hi⟩
        fin_cases i
        · exact Or.inl (Or.inl hi)
        · exact Or.inr (Or.inl (Or.inl hi))
        · exact Or.inr (Or.inl (Or.inr hi))
        · exact Or.inr (Or.inr hi)
        · exact Or.inl (Or.inr hi)
      · rintro ((h | h) | (h | h) | h)
        · exact ⟨0, h⟩
        · exact ⟨4, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, h⟩
        · exact ⟨3, h⟩
    have hmidH : midUnion P ⊆ H := by
      intro z hz
      exact (hcc z hz).2 (mem_connectedComponentIn (by
        have := hz; rw [hPdef, refineChain_mid] at this; exact this.1))
    have hyc : y ∉ closure (midUnion P) := by
      intro hyc
      have hyH : y ∈ H := closure_minimal hmidH hHc hyc
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hHU' hyH)
      apply hyU
      rw [hUeq]
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inr (Or.inl (Or.inl ⟨hi, hHL' y hyH⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨hi, hHL' y hyH⟩))
      · exact Or.inr (Or.inr ⟨hi, hHL' y hyH⟩)
      · exact Or.inl (Or.inr hi)
    refine ⟨⟨?_, ?_⟩, hyc⟩
    · have := hy.1
      rw [hUeq, closure_union] at this
      exact this.resolve_right hyc
    · rw [((hPo 0).union (hPo 4)).interior_eq]
      intro h
      exact hyU (hUeq ▸ Or.inl h)
  · -- normal
    intro i j hij
    exact (hn i j hij).mono (closure_mono (refineChain_subset L L' i))
      (closure_mono (refineChain_subset L L' j))
  · -- regular
    intro x hx
    obtain ⟨hceq, hcH⟩ := hcc x hx
    have hxL : x ∈ midUnion L := by
      have := hx; rw [hPdef, refineChain_mid] at this; exact this.1
    obtain ⟨d, hd, hds⟩ := hr x hxL
    rw [hceq]
    have hGH : closure (connectedComponentIn (midUnion L) x) ⊆ H := closure_minimal hcH hHc
    refine ⟨d, hd, runsStraight_refine hL hn hL'c hd.2.1 hds
      (fun g hg _ => hHL' g (hGH hg))
      (fun r => Or.inl fun z hz => hHL' z (hGH (layer_subset_set d r hz)))⟩
  · -- `E` runs straight through `P`
    refine runsStraight_refine hL hn hL'c hE.2.1 hs hEmid fun r => ?_
    by_cases hmeet : (layer k r ∩ (A ∪ B)).Nonempty
    · exact Or.inr hmeet
    · left
      intro z hz hzL
      refine hHL' z (hPH ⟨layer_subset_set k r hz, fun hAB => hmeet ⟨z, hz, hAB⟩⟩) hzL

end Lemma12

end HPC.Hagopian
