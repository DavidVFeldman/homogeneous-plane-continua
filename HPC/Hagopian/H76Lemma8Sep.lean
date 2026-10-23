import HPC.Hagopian.H76Lemma8Caps

/-!
# Batch 161, item T5: Lemma 8 with caps, exposing the separating open sets

`lemma8_caps_sep`: the proof of `lemma8_caps_aux` (batch 159, `H76Lemma8Caps.lean`), unchanged, with
a conclusion that also records the second open set `D` of Moore 1962, Theorem 44 (Hagopian p. 344:
"there exist disjoint open sets `C` and `D` in `R²` such that (1) `C ⊇ E`, (2) `D ⊇ M − St G`, and
(3) `C ∪ D ⊇ M − (A ∪ B)`"). Property 1 (p. 346) needs (3): a connected subset of `M` missing the
caps `A ∪ B` and meeting `C` lies in `C`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Lemma8Sep

variable {M : Set Pt} [CompactSpace M]

/-- **Lemma 8 with prescribed caps**, with the separating open sets `C ⊇ E` and `D` of Moore's
Theorem 44: `C ∩ D = ∅` and `M − (A ∪ B) ⊆ C ∪ D`, where `A = U − E`, `B = V − E`. -/
theorem lemma8_caps_sep (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {n : ℕ} (G : Fin (n + 1) → Set Pt) (hG : IsPlaneChain G)
    (hGE : Follows G k) {U V : Set Pt} (hU : IsOpen U) (hV : IsOpen V)
    (hXU : toPt (layer k 0) ⊆ U) (hZV : toPt (layer k 1) ⊆ V) (hUG : U ⊆ G 0)
    (hVG : V ⊆ G (Fin.last n)) :
    ∃ (L : Fin (n + 1) → Set Pt) (C D : Set Pt), IsOpen C ∧ IsOpen D ∧ Disjoint C D ∧
      (∀ x : M, (x : Pt) ∉ (U \ toPt E) ∪ (V \ toPt E) → (x : Pt) ∈ C ∪ D) ∧ toPt E ⊆ C ∧
      L 0 = G 0 ∧ L (Fin.last n) = G (Fin.last n) ∧
      (∀ i, i ≠ 0 → i ≠ Fin.last n → L i = C ∩ G i) ∧
      IsOrderedRefinement L G ∧ Follows L k ∧ IsFree M L := by
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
  set A := U \ toPt E
  set B := V \ toPt E
  have hA : IsOpen A := hU.sdiff hEcP.isClosed
  have hB : IsOpen B := hV.sdiff hEcP.isClosed
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
    · exact mem_iUnion.2 ⟨0, hUG h.1⟩
    · exact mem_iUnion.2 ⟨last, hVG h.1⟩
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
      refine component_of_caps hHU hAT hE (hU.preimage continuous_subtype_val)
        (hV.preimage continuous_subtype_val)
        (fun x hx => hXU ⟨x, hx, rfl⟩) (fun x hx => hZV ⟨x, hx, rfl⟩) hK'
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
  refine ⟨L, C, D, hC, hD, hCD, fun x hx => hMCD x hx, hEC, hL0, hLn,
    fun i h0 hn => by simp [L, h0, hn], ⟨hLchain, hLG⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
      · exact hxL (hends (Or.inl (hUG h.1)))
      · exact hxL (hends (Or.inr (hVG h.1)))
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

end Lemma8Sep

end HPC.Hagopian
