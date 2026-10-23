import HPC.Hagopian.H76Lemma3
import HPC.Plane.SorgenfreyDefs

/-!
# Batch 156, item H: Lemma 8 of Hagopian 1976

Let `G = {G₀, …, Gₙ}` be a chain in the plane following `E`.

* `connected_meets_links`: a connected set covered by a chain and meeting both end links meets every
  overlap `Gₘ ∩ Gₘ₊₁` (so `E` meets every link and every overlap).
* `component_of_caps` (**"Since `M` is atriodic, there exist open sets `A` and `B` in `G₁` and `Gₙ`,
  respectively, such that `E` is a component of `M − (A ∪ B)`"**). Take `A = G₀ ∖ E`, `B = Gₙ ∖ E`.
  A continuum `K ⊇ E` of `M` missing `A ∪ B` meets `G₀ ∪ Gₙ` only in `E`. If `x ∈ K ∖ E`, choose open
  `O₁ ⊇ X`, `O₂ ⊇ Z` with closures in `G₀`, `Gₙ`; boundary bumping in `K` gives a continuum
  `L ⊆ K ∖ (O₁ ∪ O₂)` through `x` meeting `cl (K ∩ (O₁ ∪ O₂)) ⊆ E`. `L` meets `E` and misses
  `X ∪ Z`, so `L ⊆ E` by the triod of `subset_of_meets_avoids` (atriodicity): a contradiction.
* Moore 1962, Theorem 44 (`exists_closed_split_of_no_connected`) then splits `M − (A ∪ B)` into
  disjoint closed sets `H ⊇ E` and `L ⊇ M − St G`; disjoint open `C ⊇ H`, `D ⊇ L` exist in the
  plane.
* `lemma8_aux`: `Lᵢ = Gᵢ` for `i = 0, n`, `Lᵢ = C ∩ Gᵢ` otherwise. It is a chain (the overlaps of
  `G` meet `E ⊆ C`), follows `E` (every point of `E` in `Gⱼ` is in `Lⱼ`), and is free: a point of
  `M ∩ Bd (St L)` is not in `A ∪ B ⊆ St L`; in `C` it would lie outside `St G`, hence in `D`; so it
  is in `D`, away from `C`, and so in `Cl (L₀ ∪ Lₙ) − (L₀ ∪ Lₙ)`.
* For `n = 0` or `n = 1` (one or two links) the definition gives `L = G`; `G` is then free by
  definition (`St G = G₀ ∪ Gₙ`), and the argument above is not needed (it still applies).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Lemma8

/-- A connected set covered by a chain, meeting both end links, meets every overlap. -/
theorem connected_meets_links {n : ℕ} {G : Fin (n + 1) → Set Pt} (hG : IsPlaneChain G)
    {S : Set Pt} (hS : IsPreconnected S) (hSG : S ⊆ ⋃ i, G i) (h0 : (S ∩ G 0).Nonempty)
    (hn : (S ∩ G (Fin.last n)).Nonempty) (m : ℕ) (hm : m < n) :
    (S ∩ (G ⟨m, by omega⟩ ∩ G ⟨m + 1, by omega⟩)).Nonempty := by
  set U₁ := ⋃ (i : Fin (n + 1)) (_ : (i : ℕ) ≤ m), G i
  set U₂ := ⋃ (i : Fin (n + 1)) (_ : m < (i : ℕ)), G i
  have hU₁ : IsOpen U₁ := isOpen_iUnion fun i => isOpen_iUnion fun _ => hG.isOpen i
  have hU₂ : IsOpen U₂ := isOpen_iUnion fun i => isOpen_iUnion fun _ => hG.isOpen i
  have hcov : S ⊆ U₁ ∪ U₂ := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hSG hx)
    by_cases him : (i : ℕ) ≤ m
    · exact Or.inl (mem_iUnion₂.2 ⟨i, him, hi⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨i, not_le.1 him, hi⟩)
  obtain ⟨x, hxS, hx1, hx2⟩ := hS U₁ U₂ hU₁ hU₂ hcov
    (by obtain ⟨y, hyS, hy⟩ := h0; exact ⟨y, hyS, mem_iUnion₂.2 ⟨0, Nat.zero_le _, hy⟩⟩)
    (by obtain ⟨y, hyS, hy⟩ := hn; exact ⟨y, hyS, mem_iUnion₂.2 ⟨Fin.last n, by simpa, hy⟩⟩)
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx1
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx2
  have hij := ((hG.meets i j).1 ⟨x, hxi, hxj⟩).2
  have hie : i = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
  have hje : j = ⟨m + 1, by omega⟩ := Fin.ext (by simp; omega)
  exact ⟨x, hxS, hie ▸ hxi, hje ▸ hxj⟩

variable {M : Set Pt} [CompactSpace M]

/-- **The caps.** A subcontinuum of `M` containing `E` and meeting `G₀ ∪ Gₙ` only in `E` is `E`. -/
theorem component_of_caps (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {G₁ Gₙ : Set M} (h₁ : IsOpen G₁) (hₙ : IsOpen Gₙ)
    (hX : layer k 0 ⊆ G₁) (hZ : layer k 1 ⊆ Gₙ) {K : Set M} (hK : Fold.Q78.IsContinuum K)
    (hEK : E ⊆ K) (hKG : K ∩ (G₁ ∪ Gₙ) ⊆ E) : K ⊆ E := by
  obtain ⟨⟨a, b, hab⟩, hk, hk0⟩ := hE
  have hEc := hab.1
  intro x hxK
  by_contra hxE
  have hXc := (isContinuum_layer hEc.1 hk 0).1
  have hZc := (isContinuum_layer hEc.1 hk 1).1
  obtain ⟨O₁, hO₁, hXO₁, hO₁G⟩ := normal_exists_closure_subset hXc.isClosed h₁ hX
  obtain ⟨O₂, hO₂, hZO₂, hO₂G⟩ := normal_exists_closure_subset hZc.isClosed hₙ hZ
  set F₀ := K \ (O₁ ∪ O₂)
  have hF₀ : IsClosed F₀ := hK.1.isClosed.inter (hO₁.union hO₂).isClosed_compl
  obtain ⟨x₀, hx₀⟩ := hk.2.1 0
  have hx₀O : (x₀ : M) ∈ O₁ := hXO₁ ⟨x₀, hx₀, rfl⟩
  have hxF₀ : x ∈ F₀ := by
    refine ⟨hxK, fun hx => hxE (hKG ⟨hxK, ?_⟩)⟩
    rcases hx with hx | hx
    · exact Or.inl (hO₁G (subset_closure hx))
    · exact Or.inr (hO₂G (subset_closure hx))
  obtain ⟨L, hL, hLF₀, hxL, hLcl⟩ := exists_continuum_bump_closed hK hF₀ diff_subset
    (fun h => (h ▸ (show (x₀ : M) ∉ F₀ from fun h' => h'.2 (Or.inl hx₀O)))
      (hEK x₀.2)) hxF₀
  have hclE : closure (K \ F₀) ⊆ E := by
    have : K \ F₀ ⊆ K ∩ (O₁ ∪ O₂) := by
      rintro y ⟨hyK, hyF⟩
      by_contra hy
      exact hyF ⟨hyK, fun h => hy ⟨hyK, h⟩⟩
    refine (closure_mono this).trans fun y hy => hKG ⟨closure_minimal inter_subset_left
      hK.1.isClosed hy, ?_⟩
    have := closure_mono (inter_subset_right (s := K) (t := O₁ ∪ O₂)) hy
    rw [closure_union] at this
    rcases this with h | h
    · exact Or.inl (hO₁G h)
    · exact Or.inr (hO₂G h)
  have hLE : L ⊆ E := subset_of_meets_avoids hHU hAT hEc hk hL
    (by obtain ⟨y, hyL, hy⟩ := hLcl; exact ⟨y, hclE hy, hyL⟩)
    (by
      rw [disjoint_left]
      intro y hyL hy
      have hyF := hLF₀ hyL
      rcases hy with hy | hy
      · exact hyF.2 (Or.inl (hXO₁ hy))
      · exact hyF.2 (Or.inr (hZO₂ hy)))
  exact hxE (hLE hxL)

omit [CompactSpace M] in
theorem toPt_mono {A B : Set M} (h : A ⊆ B) : toPt A ⊆ toPt B := image_mono h

omit [CompactSpace M] in
theorem mem_toPt {A : Set M} {x : M} : (x : Pt) ∈ toPt A ↔ x ∈ A :=
  Subtype.val_injective.mem_set_image

/-- **Lemma 8.** -/
theorem lemma8_aux (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {n : ℕ} (G : Fin (n + 1) → Set Pt) (hG : IsPlaneChain G)
    (hGE : Follows G k) :
    ∃ L : Fin (n + 1) → Set Pt, IsOrderedRefinement L G ∧ Follows L k ∧ IsFree M L := by
  classical
  obtain ⟨hEG, hXG, hZG, hlayG, hfolG⟩ := hGE
  have hE' := hE
  obtain ⟨⟨a, b, hab⟩, hk, hk0⟩ := hE'
  have hEc := hab.1
  set last := Fin.last n
  -- `E` as a plane set
  have hEcP : IsCompact (toPt E) := hEc.1.image continuous_subtype_val
  have hEpP : IsPreconnected (toPt E) := hEc.2.2.image _ continuous_subtype_val.continuousOn
  obtain ⟨x₀, hx₀⟩ := hk.2.1 0
  obtain ⟨x₁, hx₁⟩ := hk.2.1 1
  have hx₀G : ((x₀ : M) : Pt) ∈ G 0 := hXG ⟨x₀, ⟨x₀, hx₀, rfl⟩, rfl⟩
  have hx₁G : ((x₁ : M) : Pt) ∈ G last := hZG ⟨x₁, ⟨x₁, hx₁, rfl⟩, rfl⟩
  have hx₀E : ((x₀ : M) : Pt) ∈ toPt E := ⟨x₀, x₀.2, rfl⟩
  have hx₁E : ((x₁ : M) : Pt) ∈ toPt E := ⟨x₁, x₁.2, rfl⟩
  have hov := connected_meets_links hG hEpP hEG ⟨_, hx₀E, hx₀G⟩ ⟨_, hx₁E, hx₁G⟩
  -- `E` meets `Gᵢ ∩ Gⱼ` whenever `|i − j| ≤ 1`
  have hEmeet : ∀ i j : Fin (n + 1), (i : ℕ) ≤ j + 1 → (j : ℕ) ≤ i + 1 →
      (toPt E ∩ (G i ∩ G j)).Nonempty := by
    intro i j hij hji
    rcases Nat.lt_or_ge (i : ℕ) j with h | h
    · have hm : (i : ℕ) < n := by omega
      obtain ⟨x, hx, hx1, hx2⟩ := hov i hm
      have hie : (⟨(i : ℕ), by omega⟩ : Fin (n + 1)) = i := Fin.ext rfl
      have hje : (⟨(i : ℕ) + 1, by omega⟩ : Fin (n + 1)) = j := Fin.ext (by simp; omega)
      exact ⟨x, hx, hie ▸ hx1, hje ▸ hx2⟩
    rcases Nat.lt_or_ge (j : ℕ) i with h' | h'
    · have hm : (j : ℕ) < n := by omega
      obtain ⟨x, hx, hx1, hx2⟩ := hov j hm
      have hje : (⟨(j : ℕ), by omega⟩ : Fin (n + 1)) = j := Fin.ext rfl
      have hie : (⟨(j : ℕ) + 1, by omega⟩ : Fin (n + 1)) = i := Fin.ext (by simp; omega)
      exact ⟨x, hx, hie ▸ hx2, hje ▸ hx1⟩
    have hij' : i = j := Fin.ext (le_antisymm h' h)
    subst hij'
    rcases Nat.lt_or_ge (i : ℕ) n with hm | hm
    · obtain ⟨x, hx, hx1, -⟩ := hov i hm
      have hie : (⟨(i : ℕ), by omega⟩ : Fin (n + 1)) = i := Fin.ext rfl
      exact ⟨x, hx, hie ▸ hx1, hie ▸ hx1⟩
    · have hil : i = last := Fin.ext (by simp [last]; omega)
      subst hil
      exact ⟨_, hx₁E, hx₁G, hx₁G⟩
  -- the caps `A`, `B`
  set A := G 0 \ toPt E
  set B := G last \ toPt E
  have hA : IsOpen A := (hG.isOpen 0).sdiff hEcP.isClosed
  have hB : IsOpen B := (hG.isOpen last).sdiff hEcP.isClosed
  -- Moore 44
  set K₀ : Set M := (Subtype.val ⁻¹' (A ∪ B))ᶜ
  set Q : Set M := (Subtype.val ⁻¹' (⋃ i, G i))ᶜ
  have hK₀c : IsClosed K₀ :=
    ((hA.union hB).preimage continuous_subtype_val).isClosed_compl
  have hQc : IsClosed Q :=
    ((isOpen_iUnion hG.isOpen).preimage continuous_subtype_val).isClosed_compl
  have hEK₀ : E ⊆ K₀ := by
    intro x hx hxAB
    rcases hxAB with h | h
    · exact h.2 ⟨x, hx, rfl⟩
    · exact h.2 ⟨x, hx, rfl⟩
  have hQK₀ : Q ⊆ K₀ := by
    intro x hxQ hxAB
    apply hxQ
    rcases hxAB with h | h
    · exact mem_iUnion.2 ⟨0, h.1⟩
    · exact mem_iUnion.2 ⟨last, h.1⟩
  have hEQ : Disjoint E Q := by
    rw [disjoint_left]
    intro x hx hxQ
    exact hxQ (hEG ⟨x, hx, rfl⟩)
  have hno : ∀ Zs ⊆ K₀, IsPreconnected Zs → (Zs ∩ E).Nonempty → (Zs ∩ Q).Nonempty → False := by
    intro Zs hZK hZp hZE hZQ
    set K' := closure (E ∪ Zs)
    have hK'p : IsPreconnected (E ∪ Zs) := by
      obtain ⟨y, hyZ, hyE⟩ := hZE
      exact IsPreconnected.union y hyE hyZ hEc.2.2 hZp
    have hK' : Fold.Q78.IsContinuum K' :=
      ⟨isClosed_closure.isCompact, (hEc.2.1.mono subset_union_left).closure,
        hK'p.closure⟩
    have hK'K₀ : K' ⊆ K₀ := closure_minimal (union_subset hEK₀ hZK) hK₀c
    have hK'E : K' ⊆ E := by
      refine component_of_caps hHU hAT hE ((hG.isOpen 0).preimage continuous_subtype_val)
        ((hG.isOpen last).preimage continuous_subtype_val)
        (fun x hx => hXG ⟨x, hx, rfl⟩) (fun x hx => hZG ⟨x, hx, rfl⟩) hK'
        (subset_union_left.trans subset_closure) ?_
      rintro x ⟨hxK', hxG⟩
      by_contra hxE
      apply hK'K₀ hxK'
      rcases hxG with h | h
      · exact Or.inl ⟨h, fun h' => hxE (mem_toPt.1 h')⟩
      · exact Or.inr ⟨h, fun h' => hxE (mem_toPt.1 h')⟩
    obtain ⟨y, hyZ, hyQ⟩ := hZQ
    exact disjoint_left.1 hEQ (hK'E (subset_closure (Or.inr hyZ))) hyQ
  obtain ⟨H₀, L₀, hH₀, hL₀, hHL, hHLd, hEH, hQL⟩ :=
    exists_closed_split_of_no_connected hK₀c.isCompact hEc.1.isClosed hQc hEK₀ hQK₀ hno
  obtain ⟨C, D, hC, hD, hHC, hLD, hCD⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hH₀.isCompact.image continuous_subtype_val)
      (hL₀.isCompact.image continuous_subtype_val)
      ((disjoint_image_iff Subtype.val_injective).2 hHLd)
  have hEC : toPt E ⊆ C := (image_mono hEH).trans hHC
  have hMD : ∀ x : M, (x : Pt) ∉ ⋃ i, G i → (x : Pt) ∈ D := fun x hx =>
    hLD ⟨x, hQL hx, rfl⟩
  have hMCD : ∀ x : M, (x : Pt) ∉ A ∪ B → (x : Pt) ∈ C ∪ D := by
    intro x hx
    have hxK : x ∈ K₀ := hx
    rw [← hHL] at hxK
    rcases hxK with h | h
    · exact Or.inl (hHC ⟨x, h, rfl⟩)
    · exact Or.inr (hLD ⟨x, h, rfl⟩)
  -- the refinement
  set L : Fin (n + 1) → Set Pt := fun i => if i = 0 ∨ i = last then G i else C ∩ G i with hLdef
  have hL0 : L 0 = G 0 := by simp [L]
  have hLn : L last = G last := by simp [L]
  have hLG : ∀ i, L i ⊆ G i := by
    intro i
    by_cases h : i = 0 ∨ i = last
    · simp [L, h]
    · simp only [L, h, if_false]; exact inter_subset_right
  have hEL : ∀ i, toPt E ∩ G i ⊆ L i := by
    intro i x hx
    by_cases h : i = 0 ∨ i = last
    · simp only [L, h, if_true]; exact hx.2
    · simp only [L, h, if_false]; exact ⟨hEC hx.1, hx.2⟩
  have hLC : ∀ i, ¬ (i = 0 ∨ i = last) → L i ⊆ C := by
    intro i h
    simp only [L, h, if_false]; exact inter_subset_left
  have hLchain : IsPlaneChain L := by
    refine ⟨fun i => ?_, fun i j => ⟨fun h => ?_, fun h => ?_⟩⟩
    · by_cases h : i = 0 ∨ i = last
      · simp only [L, h, if_true]; exact hG.isOpen i
      · simp only [L, h, if_false]; exact hC.inter (hG.isOpen i)
    · obtain ⟨x, hx1, hx2⟩ := h
      exact (hG.meets i j).1 ⟨x, hLG i hx1, hLG j hx2⟩
    · obtain ⟨x, hxE, hxi, hxj⟩ := hEmeet i j h.1 h.2
      exact ⟨x, hEL i ⟨hxE, hxi⟩, hEL j ⟨hxE, hxj⟩⟩
  refine ⟨L, ⟨hLchain, hLG⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hEG hx)
    exact mem_iUnion.2 ⟨i, hEL i ⟨hx, hi⟩⟩
  · rw [hL0]; exact hXG
  · rw [hLn]; exact hZG
  · intro t
    obtain ⟨i, hi⟩ := hlayG t
    exact ⟨i, fun x hx => hEL i ⟨toPt_mono (img_subset _) hx, hi hx⟩⟩
  · intro r s hrs i hi x hx
    have hxG := hfolG r s hrs i (fun y hy => hLG i (hi hy)) hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hxG
    have hxE : x ∈ toPt E := toPt_mono (img_subset _) hx
    have hji := (hG.meets j i).1 hj
    refine mem_iUnion₂.2 ⟨j, ?_, hEL j ⟨hxE, hxj⟩⟩
    exact (hLchain.meets j i).2 hji
  · -- freeness
    rintro x ⟨hxM, hxfr⟩
    have hLo : IsOpen (⋃ i, L i) := isOpen_iUnion hLchain.isOpen
    rw [hLo.frontier_eq] at hxfr
    obtain ⟨hxcl, hxL⟩ := hxfr
    have hends : G 0 ∪ G last ⊆ ⋃ i, L i := union_subset
      (fun y hy => mem_iUnion.2 ⟨0, hL0 ▸ hy⟩) (fun y hy => mem_iUnion.2 ⟨last, hLn ▸ hy⟩)
    have hxAB : x ∉ A ∪ B := by
      rintro (h | h)
      · exact hxL (hends (Or.inl h.1))
      · exact hxL (hends (Or.inr h.1))
    have hxD : x ∈ D := by
      rcases hMCD ⟨x, hxM⟩ hxAB with h | h
      · exfalso
        have hxG : x ∉ ⋃ i, G i := by
          intro hxG
          obtain ⟨i, hi⟩ := mem_iUnion.1 hxG
          apply hxL
          refine mem_iUnion.2 ⟨i, ?_⟩
          by_cases hi' : i = 0 ∨ i = last
          · simp only [L, hi', if_true]; exact hi
          · simp only [L, hi', if_false]; exact ⟨h, hi⟩
        exact disjoint_left.1 hCD h (hMD ⟨x, hxM⟩ hxG)
      · exact h
    have hLD : (⋃ i, L i) ∩ D ⊆ G 0 ∪ G last := by
      rintro y ⟨hy, hyD⟩
      obtain ⟨i, hi⟩ := mem_iUnion.1 hy
      by_cases hi' : i = 0 ∨ i = last
      · rcases hi' with rfl | rfl
        · exact Or.inl (hL0 ▸ hi)
        · exact Or.inr (hLn ▸ hi)
      · exact absurd hyD (disjoint_left.1 hCD (hLC i hi' hi))
    have hxcl' : x ∈ closure (G 0 ∪ G last) :=
      closure_mono hLD (by rw [inter_comm]; exact hD.inter_closure ⟨hxD, hxcl⟩)
    have hGo : IsOpen (G 0 ∪ G last) := (hG.isOpen 0).union (hG.isOpen last)
    rw [hL0, hLn, hGo.frontier_eq]
    exact ⟨hxcl', fun h => hxL (hends h)⟩

end Lemma8

end HPC.Hagopian
