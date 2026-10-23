import HPC.Plane.SorgenfreyDefs

/-!
# Batch 102, part 1: Nadler 11.25–11.33

The statements of the skeleton for 11.25–11.33 (moved here from `HPC/Plane/Sorgenfrey.lean`),
with their proofs. Throughout, `X = Y ⊕ Z`, `U = X ∖ Z`, `V = X ∖ Y`, and `Ū`, `V̄` are closures.

Shape changes (recorded in `REPORT-batch102.md`):
* **11.28 as transcribed is false** when `H = Ū` (then `U ∖ H = ∅`, which is not connected);
  Nadler's proof assumes `U − H ≠ ∅` ("assuming for the purpose of proof"). The skeleton's
  statement is kept, commented out, with the counterexample `isConnected_diff_of_superset_false`
  (the arc `[0, 1] = [0, ½] ⊕ [½, 1]`); `isConnected_diff_of_superset'` adds `U ∖ H ≠ ∅`.
* **11.31**: the hypothesis `B ⊆ Ū` is not used and is dropped.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ## 11.25, 11.26 and the remark after 11.24 -/

/-- **11.25.** Every triod is a weak triod. -/
theorem isWeakTriod_of_isTriod {X : Set S} (h : IsTriod X) : IsWeakTriod X := by
  obtain ⟨hX, N, hN, hNX, A, B, C, hA, hB, hC, hcov, h1, h2, h3, h4, h5, h6⟩ := h
  have hnotN : ∀ x ∈ A ∪ B ∪ C, x ∉ N := fun x hx => by
    have : x ∈ X \ N := by rw [hcov]; exact hx
    exact this.2
  have hXA : Fold.Q78.IsContinuum (N ∪ A) :=
    isContinuum_union_piece (R := B ∪ C) hX hN hNX (by rw [hcov, union_assoc])
      (disjoint_union_right.mpr ⟨h1, h3⟩) (by rw [closure_union]; exact disjoint_union_right.mpr ⟨h2, h4⟩)
  have hXB : Fold.Q78.IsContinuum (N ∪ B) :=
    isContinuum_union_piece (R := A ∪ C) hX hN hNX
      (by rw [hcov]; ext x; simp only [mem_union]; tauto)
      (disjoint_union_right.mpr ⟨h2.symm, h5⟩)
      (by rw [closure_union]; exact disjoint_union_right.mpr ⟨h1.symm, h6⟩)
  have hXC : Fold.Q78.IsContinuum (N ∪ C) :=
    isContinuum_union_piece (R := A ∪ B) hX hN hNX
      (by rw [hcov]; ext x; simp only [mem_union]; tauto)
      (disjoint_union_right.mpr ⟨h4.symm, h6.symm⟩)
      (by rw [closure_union]; exact disjoint_union_right.mpr ⟨h3.symm, h5.symm⟩)
  have hXeq : X = N ∪ (A ∪ B ∪ C) := by rw [← hcov, union_diff_cancel hNX]
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  obtain ⟨c, hc⟩ := hC
  obtain ⟨n, hn⟩ := hN.2.nonempty
  refine isWeakTriod_of hXA hXB hXC (by rw [hXeq]; ext x; simp only [mem_union]; tauto) ?_ ?_ ?_
    ⟨n, Or.inl hn, Or.inl hn, Or.inl hn⟩
  · refine ⟨a, Or.inr ha, ?_, ?_⟩
    · rintro (h | h)
      · exact hnotN a (Or.inl (Or.inl ha)) h
      · exact Set.disjoint_left.mp h2 ha (subset_closure h)
    · rintro (h | h)
      · exact hnotN a (Or.inl (Or.inl ha)) h
      · exact Set.disjoint_left.mp h4 ha (subset_closure h)
  · refine ⟨b, Or.inr hb, ?_, ?_⟩
    · rintro (h | h)
      · exact hnotN b (Or.inl (Or.inr hb)) h
      · exact Set.disjoint_left.mp h1 (subset_closure h) hb
    · rintro (h | h)
      · exact hnotN b (Or.inl (Or.inr hb)) h
      · exact Set.disjoint_left.mp h6 hb (subset_closure h)
  · refine ⟨c, Or.inr hc, ?_, ?_⟩
    · rintro (h | h)
      · exact hnotN c (Or.inr hc) h
      · exact Set.disjoint_left.mp h3 (subset_closure h) hc
    · rintro (h | h)
      · exact hnotN c (Or.inr hc) h
      · exact Set.disjoint_left.mp h5 (subset_closure h) hc

/-- **11.26.** For a unicoherent continuum, triod ⇔ weak triod. -/
theorem isTriod_iff_isWeakTriod {X : Set S} (hX : Fold.Q78.IsContinuum X) (hu : IsUnicoherent X) :
    IsTriod X ↔ IsWeakTriod X := by
  refine ⟨isWeakTriod_of_isTriod, ?_⟩
  rintro ⟨X₁, X₂, X₃, ⟨-, h₁, h₂, h₃, hcov, e₁, e₂, e₃⟩, c, ⟨hc1, hc2⟩, hc3⟩
  have h23 : Fold.Q78.IsContinuum (X₂ ∪ X₃) := isContinuum_union h₂ h₃ ⟨c, hc2, hc3⟩
  have h13 : Fold.Q78.IsContinuum (X₁ ∪ X₃) := isContinuum_union h₁ h₃ ⟨c, hc1, hc3⟩
  have h12 : Fold.Q78.IsContinuum (X₁ ∪ X₂) := isContinuum_union h₁ h₂ ⟨c, hc1, hc2⟩
  have hZ₁ : Fold.Q78.IsContinuum (X₁ ∩ (X₂ ∪ X₃)) :=
    ⟨h₁.1.inter_right h23.1.isClosed, hu _ _ h₁ h23 (by rw [hcov, union_assoc])⟩
  have hZ₂ : Fold.Q78.IsContinuum (X₂ ∩ (X₁ ∪ X₃)) :=
    ⟨h₂.1.inter_right h13.1.isClosed, hu _ _ h₂ h13 (by rw [hcov]; ext x; simp only [mem_union]; tauto)⟩
  have hZ₃ : Fold.Q78.IsContinuum (X₃ ∩ (X₁ ∪ X₂)) :=
    ⟨h₃.1.inter_right h12.1.isClosed, hu _ _ h₃ h12 (by rw [hcov]; ext x; simp only [mem_union]; tauto)⟩
  have hN : Fold.Q78.IsContinuum (X₁ ∩ (X₂ ∪ X₃) ∪ X₂ ∩ (X₁ ∪ X₃) ∪ X₃ ∩ (X₁ ∪ X₂)) :=
    isContinuum_union (isContinuum_union hZ₁ hZ₂ ⟨c, ⟨hc1, Or.inl hc2⟩, hc2, Or.inl hc1⟩) hZ₃
      ⟨c, Or.inl ⟨hc1, Or.inl hc2⟩, hc3, Or.inl hc1⟩
  have hX₁ : IsClosed X₁ := h₁.1.isClosed
  have hX₂ : IsClosed X₂ := h₂.1.isClosed
  have hX₃ : IsClosed X₃ := h₃.1.isClosed
  subst hcov
  have cl₁ : closure ((X₁ ∪ X₂ ∪ X₃) \ (X₂ ∪ X₃)) ⊆ X₁ :=
    closure_minimal (fun x hx => by rcases hx.1 with (h | h) | h <;> simp_all) hX₁
  have cl₂ : closure ((X₁ ∪ X₂ ∪ X₃) \ (X₁ ∪ X₃)) ⊆ X₂ :=
    closure_minimal (fun x hx => by rcases hx.1 with (h | h) | h <;> simp_all) hX₂
  have cl₃ : closure ((X₁ ∪ X₂ ∪ X₃) \ (X₁ ∪ X₂)) ⊆ X₃ :=
    closure_minimal (fun x hx => by rcases hx.1 with (h | h) | h <;> simp_all) hX₃
  refine ⟨hX, _, hN, fun x hx => by
      rcases hx with (h | h) | h
      exacts [Or.inl (Or.inl h.1), Or.inl (Or.inr h.1), Or.inr h.1],
    (X₁ ∪ X₂ ∪ X₃) \ (X₂ ∪ X₃), (X₁ ∪ X₂ ∪ X₃) \ (X₁ ∪ X₃), (X₁ ∪ X₂ ∪ X₃) \ (X₁ ∪ X₂), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx, hx'⟩ := not_subset.mp e₁
    exact ⟨x, Or.inl (Or.inl hx), hx'⟩
  · obtain ⟨x, hx, hx'⟩ := not_subset.mp e₂
    exact ⟨x, Or.inl (Or.inr hx), hx'⟩
  · obtain ⟨x, hx, hx'⟩ := not_subset.mp e₃
    exact ⟨x, Or.inr hx, hx'⟩
  · ext x
    by_cases h1 : x ∈ X₁ <;> by_cases h2 : x ∈ X₂ <;> by_cases h3 : x ∈ X₃ <;> simp [h1, h2, h3]
  · exact Set.disjoint_left.mpr fun x hx hx' => hx'.2 (Or.inl (cl₁ hx))
  · exact Set.disjoint_left.mpr fun x hx hx' => hx.2 (Or.inl (cl₂ hx'))
  · exact Set.disjoint_left.mpr fun x hx hx' => hx'.2 (Or.inl (cl₁ hx))
  · exact Set.disjoint_left.mpr fun x hx hx' => hx.2 (Or.inr (cl₃ hx'))
  · exact Set.disjoint_left.mpr fun x hx hx' => hx'.2 (Or.inr (cl₂ hx))
  · exact Set.disjoint_left.mpr fun x hx hx' => hx.2 (Or.inr (cl₃ hx'))

omit [CompactSpace S] in
/-- A weak triod is not irreducible between any two points (Nadler, after 11.24, "using 11.5"). -/
theorem not_irreducible_of_isWeakTriod {X : Set S} (h : IsWeakTriod X) (p q : S) :
    ¬ IsIrreducibleBetween X p q := by
  intro hirr
  obtain ⟨X₁, X₂, X₃, ⟨-, h₁, h₂, h₃, hcov, e₁, e₂, e₃⟩, c, ⟨hc1, hc2⟩, hc3⟩ := h
  have k : ∀ W, Fold.Q78.IsContinuum W → W ⊆ X → p ∈ W → q ∈ W → ¬ X ⊆ W → False :=
    fun W hW hWX hp hq hne => hne (hirr.2.2.2 W hW hWX hp hq).symm.subset
  have c12 := isContinuum_union h₁ h₂ ⟨c, hc1, hc2⟩
  have c13 := isContinuum_union h₁ h₃ ⟨c, hc1, hc3⟩
  have c23 := isContinuum_union h₂ h₃ ⟨c, hc2, hc3⟩
  have s12 : X₁ ∪ X₂ ⊆ X := by rw [hcov]; exact subset_union_left
  have s13 : X₁ ∪ X₃ ⊆ X := by rw [hcov]; intro x hx; simp only [mem_union] at hx ⊢; tauto
  have s23 : X₂ ∪ X₃ ⊆ X := by rw [hcov]; intro x hx; simp only [mem_union] at hx ⊢; tauto
  have n12 : ¬ X ⊆ X₁ ∪ X₂ := fun hs => e₃ (by rw [hcov] at hs; exact fun x hx => hs (Or.inr hx))
  have n13 : ¬ X ⊆ X₁ ∪ X₃ := fun hs => e₂ (by
    rw [hcov] at hs; exact fun x hx => hs (Or.inl (Or.inr hx)))
  have n23 : ¬ X ⊆ X₂ ∪ X₃ := fun hs => e₁ (by
    rw [hcov] at hs; exact fun x hx => hs (Or.inl (Or.inl hx)))
  have hp : p ∈ X₁ ∪ X₂ ∪ X₃ := hcov ▸ hirr.2.1
  have hq : q ∈ X₁ ∪ X₂ ∪ X₃ := hcov ▸ hirr.2.2.1
  rcases hp with (hp | hp) | hp <;> rcases hq with (hq | hq) | hq <;>
    first
    | exact k _ c12 s12 (Or.inl hp) (Or.inl hq) n12
    | exact k _ c12 s12 (Or.inl hp) (Or.inr hq) n12
    | exact k _ c12 s12 (Or.inr hp) (Or.inl hq) n12
    | exact k _ c12 s12 (Or.inr hp) (Or.inr hq) n12
    | exact k _ c13 s13 (Or.inl hp) (Or.inl hq) n13
    | exact k _ c13 s13 (Or.inl hp) (Or.inr hq) n13
    | exact k _ c13 s13 (Or.inr hp) (Or.inl hq) n13
    | exact k _ c13 s13 (Or.inr hp) (Or.inr hq) n13
    | exact k _ c23 s23 (Or.inl hp) (Or.inl hq) n23
    | exact k _ c23 s23 (Or.inl hp) (Or.inr hq) n23
    | exact k _ c23 s23 (Or.inr hp) (Or.inl hq) n23

/-! ## 11.27 and 11.28 -/

/-- One half of 11.27: if `X = Y ⊕ Z` is not a weak triod, then `X ∖ Y` is connected. -/
theorem isConnected_diff_left_of_not_weakTriod {X Y Z : Set S} (h : IsEssentialSum₂ X Y Z)
    (hnt : ¬ IsWeakTriod X) : IsConnected (X \ Y) := by
  have hX := h.1
  have hY := h.2.1
  have hZ := h.2.2.1
  have hYsub : Y ⊆ X := h.left_subset
  have hZsub : Z ⊆ X := h.right_subset
  refine ⟨h.symm.diff_nonempty, ?_⟩
  have hdZ : X \ Y ⊆ Z := h.symm.diff_subset_left
  have hXeq : X = Y ∪ (X \ Y) := (union_diff_cancel hYsub).symm
  -- Step 1: each piece of a separation of `X ∖ Y` is preconnected.
  have step1 : ∀ P Q : Set S, Q.Nonempty → X \ Y = P ∪ Q → Disjoint (closure P) Q →
      Disjoint P (closure Q) → IsPreconnected P := by
    intro P Q hQ hPQ hs1 hs2
    by_contra hP
    obtain ⟨W₁, W₂, hW₁, hW₂, hPW, hw1, hw2⟩ := exists_separated_of_not_isPreconnected hP
    have hW₁P : W₁ ⊆ P := hPW ▸ subset_union_left
    have hW₂P : W₂ ⊆ P := hPW ▸ subset_union_right
    have hnY : ∀ x ∈ P ∪ Q, x ∉ Y := fun x hx => by
      have : x ∈ X \ Y := by rw [hPQ]; exact hx
      exact this.2
    have c1 : Fold.Q78.IsContinuum (Y ∪ W₁) :=
      isContinuum_union_piece (R := W₂ ∪ Q) hX hY hYsub
        (by rw [hPQ, hPW, union_assoc])
        (disjoint_union_right.mpr ⟨hw1, hs1.mono_left (closure_mono hW₁P)⟩)
        (by rw [closure_union]; exact disjoint_union_right.mpr ⟨hw2, hs2.mono_left hW₁P⟩)
    have c2 : Fold.Q78.IsContinuum (Y ∪ W₂) :=
      isContinuum_union_piece (R := W₁ ∪ Q) hX hY hYsub
        (by rw [hPQ, hPW]; ext x; simp only [mem_union]; tauto)
        (disjoint_union_right.mpr ⟨hw2.symm, hs1.mono_left (closure_mono hW₂P)⟩)
        (by rw [closure_union]; exact disjoint_union_right.mpr ⟨hw1.symm, hs2.mono_left hW₂P⟩)
    have c3 : Fold.Q78.IsContinuum (Y ∪ Q) :=
      isContinuum_union_piece (R := P) hX hY hYsub (by rw [hPQ, union_comm]) hs2.symm hs1.symm
    obtain ⟨a, ha⟩ := hW₁
    obtain ⟨b, hb⟩ := hW₂
    obtain ⟨d, hd⟩ := hQ
    obtain ⟨y, hy⟩ := hY.2.nonempty
    refine hnt (isWeakTriod_of c1 c2 c3 ?_ ?_ ?_ ?_ ⟨y, Or.inl hy, Or.inl hy, Or.inl hy⟩)
    · rw [hXeq, hPQ, hPW]; ext x; simp only [mem_union]; tauto
    · refine ⟨a, Or.inr ha, ?_, ?_⟩
      · rintro (h' | h')
        · exact hnY a (Or.inl (hW₁P ha)) h'
        · exact Set.disjoint_left.mp hw2 ha (subset_closure h')
      · rintro (h' | h')
        · exact hnY a (Or.inl (hW₁P ha)) h'
        · exact Set.disjoint_left.mp hs2 (hW₁P ha) (subset_closure h')
    · refine ⟨b, Or.inr hb, ?_, ?_⟩
      · rintro (h' | h')
        · exact hnY b (Or.inl (hW₂P hb)) h'
        · exact Set.disjoint_left.mp hw1 (subset_closure h') hb
      · rintro (h' | h')
        · exact hnY b (Or.inl (hW₂P hb)) h'
        · exact Set.disjoint_left.mp hs2 (hW₂P hb) (subset_closure h')
    · refine ⟨d, Or.inr hd, ?_, ?_⟩
      · rintro (h' | h')
        · exact hnY d (Or.inr hd) h'
        · exact Set.disjoint_left.mp hs1 (subset_closure (hW₁P h')) hd
      · rintro (h' | h')
        · exact hnY d (Or.inr hd) h'
        · exact Set.disjoint_left.mp hs1 (subset_closure (hW₂P h')) hd
  by_contra hcon
  obtain ⟨U, V, hU, hV, hUV, hs1, hs2⟩ := exists_separated_of_not_isPreconnected hcon
  have hUc : IsPreconnected U := step1 U V hV hUV hs1 hs2
  have hVc : IsPreconnected V := step1 V U hU (by rw [hUV, union_comm]) hs2.symm hs1.symm
  have hUsub : U ⊆ X \ Y := hUV ▸ subset_union_left
  have hVsub : V ⊆ X \ Y := hUV ▸ subset_union_right
  have hcU : Fold.Q78.IsContinuum (closure U) ∧ closure U ⊆ Z :=
    isContinuum_closure_of_subset hZ.1.isClosed (hUsub.trans hdZ) hUc hU
  have hcV : Fold.Q78.IsContinuum (closure V) ∧ closure V ⊆ Z :=
    isContinuum_closure_of_subset hZ.1.isClosed (hVsub.trans hdZ) hVc hV
  -- Step 2 (Moore 5.2): `Y ∩ Z` splits between `Ū` and `V̄`.
  have hYZ : IsCompact (Y ∩ Z) := hY.1.inter_right hZ.1.isClosed
  obtain ⟨H, L, hH, hL, hHL, hdHL, hPH, hQL⟩ := exists_closed_split_of_no_connected hYZ
    (isClosed_closure.inter hYZ.isClosed) (isClosed_closure.inter hYZ.isClosed)
    inter_subset_right inter_subset_right (P := closure U ∩ (Y ∩ Z)) (Q := closure V ∩ (Y ∩ Z))
    (by
      intro Z' hZ'K hZ'c ⟨u, huZ', huP⟩ ⟨v, hvZ', hvQ⟩
      obtain ⟨hK', hK'K⟩ := isContinuum_closure_of_subset hYZ.isClosed hZ'K hZ'c ⟨u, huZ'⟩
      have c1 := isContinuum_union hK' hcU.1 ⟨u, subset_closure huZ', huP.1⟩
      have c2 := isContinuum_union hK' hcV.1 ⟨v, subset_closure hvZ', hvQ.1⟩
      obtain ⟨a, ha⟩ := hU
      obtain ⟨b, hb⟩ := hV
      obtain ⟨y, hy⟩ := h.diff_nonempty
      have hyY : y ∈ Y := h.diff_subset_left hy
      refine hnt (isWeakTriod_of c1 c2 hY ?_ ?_ ?_ ?_
        ⟨u, Or.inl (subset_closure huZ'), Or.inl (subset_closure huZ'), (hZ'K huZ').1⟩)
      · apply Subset.antisymm
        · intro x hx
          by_cases hxY : x ∈ Y
          · exact Or.inr hxY
          · have : x ∈ U ∪ V := hUV ▸ ⟨hx, hxY⟩
            rcases this with h' | h'
            · exact Or.inl (Or.inl (Or.inr (subset_closure h')))
            · exact Or.inl (Or.inr (Or.inr (subset_closure h')))
        · refine union_subset (union_subset (union_subset ?_ ?_) (union_subset ?_ ?_)) hYsub
          · exact hK'K.trans (inter_subset_left.trans hYsub)
          · exact hcU.2.trans hZsub
          · exact hK'K.trans (inter_subset_left.trans hYsub)
          · exact hcV.2.trans hZsub
      · refine ⟨a, Or.inr (subset_closure ha), ?_, (hUsub ha).2⟩
        rintro (h' | h')
        · exact (hUsub ha).2 (hK'K h').1
        · exact Set.disjoint_left.mp hs2 ha h'
      · refine ⟨b, Or.inr (subset_closure hb), ?_, (hVsub hb).2⟩
        rintro (h' | h')
        · exact (hVsub hb).2 (hK'K h').1
        · exact Set.disjoint_left.mp hs1 h' hb
      · refine ⟨y, hyY, ?_, ?_⟩
        · rintro (h' | h')
          · exact hy.2 (hK'K h').2
          · exact hy.2 (hcU.2 h')
        · rintro (h' | h')
          · exact hy.2 (hK'K h').2
          · exact hy.2 (hcV.2 h'))
  -- Step 3: `Z = (H ∪ Ū) ∪ (L ∪ V̄)` is a separation of `Z`.
  have hcov : Z ⊆ (H ∪ closure U) ∪ (L ∪ closure V) := by
    intro z hz
    by_cases hzY : z ∈ Y
    · have : z ∈ H ∪ L := hHL ▸ ⟨hzY, hz⟩
      rcases this with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr (Or.inl h')
    · have : z ∈ U ∪ V := hUV ▸ ⟨hZsub hz, hzY⟩
      rcases this with h' | h'
      · exact Or.inl (Or.inr (subset_closure h'))
      · exact Or.inr (Or.inr (subset_closure h'))
  have hdisj : Z ∩ ((H ∪ closure U) ∩ (L ∪ closure V)) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_union, mem_empty_iff_false, iff_false, not_and]
    intro hxZ hx1 hx2
    have hHyz : ∀ {w}, w ∈ H → w ∈ Y ∩ Z := fun hw => hHL ▸ Or.inl hw
    have hLyz : ∀ {w}, w ∈ L → w ∈ Y ∩ Z := fun hw => hHL ▸ Or.inr hw
    rcases hx1 with h1 | h1 <;> rcases hx2 with h2 | h2
    · exact Set.disjoint_left.mp hdHL h1 h2
    · exact Set.disjoint_left.mp hdHL h1 (hQL ⟨h2, hHyz h1⟩)
    · exact Set.disjoint_left.mp hdHL (hPH ⟨h1, hLyz h2⟩) h2
    · by_cases hxY : x ∈ Y
      · exact Set.disjoint_left.mp hdHL (hPH ⟨h1, hxY, hxZ⟩) (hQL ⟨h2, hxY, hxZ⟩)
      · have : x ∈ U ∪ V := hUV ▸ ⟨hZsub hxZ, hxY⟩
        rcases this with h' | h'
        · exact Set.disjoint_left.mp hs2 h' h2
        · exact Set.disjoint_left.mp hs1 h1 h'
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hZ.2.isPreconnected _ _
    (hH.union isClosed_closure) (hL.union isClosed_closure) hcov hdisj with h' | h'
  · obtain ⟨b, hb⟩ := hV
    rcases h' (hdZ (hVsub hb)) with h'' | h''
    · exact (hVsub hb).2 (hHL ▸ Or.inl h'' : b ∈ Y ∩ Z).1
    · exact Set.disjoint_left.mp hs1 h'' hb
  · obtain ⟨a, ha⟩ := hU
    rcases h' (hdZ (hUsub ha)) with h'' | h''
    · exact (hUsub ha).2 (hHL ▸ Or.inr h'' : a ∈ Y ∩ Z).1
    · exact Set.disjoint_left.mp hs2 ha h''

/-- **11.27.** If `X = Y ⊕ Z` and `X` is not a weak triod, then `X ∖ Y` and `X ∖ Z` are connected. -/
theorem isConnected_diff_of_not_weakTriod {X Y Z : Set S} (h : IsEssentialSum₂ X Y Z)
    (hnt : ¬ IsWeakTriod X) : IsConnected (X \ Y) ∧ IsConnected (X \ Z) :=
  ⟨isConnected_diff_left_of_not_weakTriod h hnt, isConnected_diff_left_of_not_weakTriod h.symm hnt⟩

/-- `Ū` is a continuum (11.27). -/
theorem isContinuum_closure_diff {X Y Z : Set S} (h : IsEssentialSum₂ X Y Z)
    (hnt : ¬ IsWeakTriod X) : Fold.Q78.IsContinuum (closure (X \ Z)) :=
  ⟨isClosed_closure.isCompact, (isConnected_diff_of_not_weakTriod h hnt).2.closure⟩

-- Commented-out statement `isConnected_diff_of_superset` removed in batch 103; see `LEDGER.md`.

/-- **11.28 as transcribed is false**: the arc `[0, 1] = [0, ½] ⊕ [½, 1]` (not a weak triod, being
irreducible between `0` and `1`), with `H = Ū = [0, ½]`, has `U ∖ H = ∅`. -/
theorem isConnected_diff_of_superset_false :
    ¬ (∀ {X Y Z H : Set unitInterval}, IsEssentialSum₂ X Y Z → ¬ IsWeakTriod X →
      Fold.Q78.IsContinuum H → H ⊆ closure (X \ Z) → closure (X \ Z) ∩ Z ⊆ H →
      IsConnected ((X \ Z) \ H)) := by
  intro hall
  set m : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩ with hm
  have hess : IsEssentialSum₂ (univ : Set unitInterval) (Icc 0 m) (Icc m 1) := by
    refine ⟨⟨isCompact_univ, isConnected_univ⟩, ⟨isCompact_Icc, isConnected_Icc m.2.1⟩,
      ⟨isCompact_Icc, isConnected_Icc m.2.2⟩, ?_, ?_, ?_⟩
    · ext x
      simp only [mem_univ, mem_union, mem_Icc, true_iff]
      rcases le_total x m with h | h
      · exact Or.inl ⟨x.2.1, h⟩
      · exact Or.inr ⟨h, x.2.2⟩
    · intro he
      have := (he.symm ▸ mem_univ (1 : unitInterval) : (1 : unitInterval) ∈ Icc 0 m).2
      change (1 : ℝ) ≤ 1 / 2 at this
      norm_num at this
    · intro he
      have := (he.symm ▸ mem_univ (0 : unitInterval) : (0 : unitInterval) ∈ Icc m 1).1
      change (1 / 2 : ℝ) ≤ 0 at this
      norm_num at this
  have hnt : ¬ IsWeakTriod (univ : Set unitInterval) := fun hw =>
    not_irreducible_of_isWeakTriod hw 0 1 ⟨⟨isCompact_univ, isConnected_univ⟩, trivial, trivial,
      fun K hK _ h0 h1 => eq_univ_of_forall fun x =>
        hK.2.isPreconnected.Icc_subset h0 h1 ⟨x.2.1, x.2.2⟩⟩
  obtain ⟨x, hx⟩ := (hall hess hnt (isContinuum_closure_diff hess hnt) Subset.rfl
    inter_subset_left).nonempty
  exact hx.2 (subset_closure hx.1)

/-- **11.28, corrected.** With `U = X ∖ Z`: if `H` is a subcontinuum of `Ū` containing `Ū ∩ Z` and
`U ⊄ H`, then `U ∖ H` is connected. -/
theorem isConnected_diff_of_superset' {X Y Z H : Set S} (h : IsEssentialSum₂ X Y Z)
    (hnt : ¬ IsWeakTriod X) (hH : Fold.Q78.IsContinuum H) (hHU : H ⊆ closure (X \ Z))
    (hHZ : closure (X \ Z) ∩ Z ⊆ H) (hne : ((X \ Z) \ H).Nonempty) :
    IsConnected ((X \ Z) \ H) := by
  have hT := isContinuum_closure_diff h hnt
  obtain ⟨w, hw⟩ := h.closure_inter_nonempty
  have hZH : Fold.Q78.IsContinuum (Z ∪ H) := isContinuum_union h.2.2.1 hH ⟨w, hw.2, hHZ hw⟩
  have hess : IsEssentialSum₂ X (Z ∪ H) (closure (X \ Z)) := by
    refine ⟨h.1, hZH, hT, ?_, ?_, h.closure_diff_ne⟩
    · rw [union_comm, ← union_assoc, ← h.eq_closure_union, union_eq_left.mpr
        (hHU.trans h.closure_diff_subset)]
    · intro he
      obtain ⟨x, ⟨hxX, hxZ⟩, hxH⟩ := hne
      rw [← he] at hxX
      rcases hxX with h' | h'
      · exact hxZ h'
      · exact hxH h'
  have := isConnected_diff_left_of_not_weakTriod hess hnt
  rwa [← diff_diff] at this

/-! ## 11.30 -/

/-- **11.30.** For nonempty compact `A`, `B` in a continuum `X` there is a subcontinuum
`C = irr(A, B)` (Zorn / Brouwer reduction). -/
theorem exists_irrFromTo {X A B : Set S} (hX : Fold.Q78.IsContinuum X) (hA : IsCompact A)
    (hB : IsCompact B) (hAX : (A ∩ X).Nonempty) (hBX : (B ∩ X).Nonempty) :
    ∃ C ⊆ X, IrrFromTo C A B := by
  set 𝒮 : Set (Set S) :=
    {W | W ⊆ X ∧ Fold.Q78.IsContinuum W ∧ (W ∩ A).Nonempty ∧ (W ∩ B).Nonempty}
  have hmeet : ∀ c ⊆ 𝒮, IsChain (· ⊆ ·) c → c.Nonempty → ∀ D : Set S, IsCompact D →
      (∀ W ∈ c, (W ∩ D).Nonempty) → (⋂₀ c ∩ D).Nonempty := by
    intro c hc hch hne D hD hWD
    haveI : Nonempty c := hne.to_subtype
    have := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun W : c => (W : Set S) ∩ D) (fun W₁ W₂ => by
        rcases hch.total W₁.2 W₂.2 with h | h
        · exact ⟨W₁, Subset.rfl, inter_subset_inter_left _ h⟩
        · exact ⟨W₂, inter_subset_inter_left _ h, Subset.rfl⟩)
      (fun W => hWD W W.2) (fun W => ((hc W.2).2.1.1.inter_right hD.isClosed))
      (fun W => ((hc W.2).2.1.1.isClosed.inter hD.isClosed))
    obtain ⟨x, hx⟩ := this
    simp only [mem_iInter] at hx
    exact ⟨x, mem_sInter.mpr fun W hW => (hx ⟨W, hW⟩).1, (hx ⟨_, hne.some_mem⟩).2⟩
  obtain ⟨m, hmX, hm⟩ := zorn_superset_nonempty 𝒮 (fun c hcS hch hne => by
    refine ⟨⋂₀ c, ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩, fun W hW => sInter_subset_of_mem hW⟩
    · obtain ⟨W, hW⟩ := hne
      exact (sInter_subset_of_mem hW).trans (hcS hW).1
    · exact (isClosed_sInter fun W hW => (hcS hW).2.1.1.isClosed).isCompact
    · obtain ⟨x, hx, -⟩ := hmeet c hcS hch hne A hA fun W hW => (hcS hW).2.2.1
      exact ⟨x, hx⟩
    · exact isPreconnected_sInter_chain' hne hch (fun W hW => (hcS hW).2.1.1)
        (fun W hW => (hcS hW).2.1.2.isPreconnected)
    · exact hmeet c hcS hch hne A hA fun W hW => (hcS hW).2.2.1
    · exact hmeet c hcS hch hne B hB fun W hW => (hcS hW).2.2.2) X
    ⟨Subset.rfl, hX, by rwa [inter_comm], by rwa [inter_comm]⟩
  obtain ⟨⟨-, hmc, hAm, hBm⟩, hmin⟩ := hm
  exact ⟨m, hmX, hmc, hAm, hBm, fun K hK hKm hAK hBK =>
    Subset.antisymm hKm (hmin ⟨hKm.trans hmX, hK, hAK, hBK⟩ hKm)⟩

/-! ## 11.31–11.33 -/

/-- **11.31.** `X = Y ⊕ Z` not a weak triod, `U = X ∖ Z`; `A`, `B` subcontinua (`A ⊆ Ū`),
`p ∈ U ∖ A`, `A ⊇ Ū ∩ Z`, `B = irr(p, A)`, `A ∪ B ⊇ U`. Then `Ū = irr(p, Ū ∩ Z)`.
(Shape change: the hypothesis `B ⊆ Ū` of the skeleton is not used and is dropped.) -/
theorem nadler_11_31 {X Y Z A B : Set S} {p : S} (h : IsEssentialSum₂ X Y Z)
    (hnt : ¬ IsWeakTriod X) (hA : Fold.Q78.IsContinuum A) (hB : Fold.Q78.IsContinuum B)
    (hAU : A ⊆ closure (X \ Z)) (hp : p ∈ (X \ Z) \ A)
    (hAZ : closure (X \ Z) ∩ Z ⊆ A) (hBirr : IrrFromTo B {p} A) (hcov : X \ Z ⊆ A ∪ B) :
    IrrFromTo (closure (X \ Z)) {p} (closure (X \ Z) ∩ Z) := by
  have hT := isContinuum_closure_diff h hnt
  have hpT : p ∈ closure (X \ Z) := subset_closure hp.1
  refine ⟨hT, ⟨p, hpT, rfl⟩, by rw [← inter_assoc, inter_self]; exact h.closure_inter_nonempty,
    fun L hL hLT hpL hLZ => ?_⟩
  obtain ⟨p', hp'L, rfl⟩ := hpL
  obtain ⟨w, hwL, hwT, hwZ⟩ := hLZ
  -- (*) `B ⊆ L`
  have hBL : B ⊆ L := by
    obtain ⟨K, hK, hKL, hKcl, hpK, x, hxK, hxA⟩ := exists_continuum_bump_open hL
      hA.1.isClosed.isOpen_compl hp'L hp.2 (fun hs => hs hwL (hAZ ⟨hwT, hwZ⟩))
    have hsubB : L ∩ Aᶜ ⊆ B := fun y ⟨hyL, hyA⟩ => by
      by_cases hyZ : y ∈ Z
      · exact absurd (hAZ ⟨hLT hyL, hyZ⟩) hyA
      · exact (hcov ⟨h.closure_diff_subset (hLT hyL), hyZ⟩).resolve_left hyA
    have hKB : K ⊆ B := hKcl.trans (closure_minimal hsubB hB.1.isClosed)
    have := hBirr.2.2.2 K hK hKB ⟨p', hpK, rfl⟩ ⟨x, hxK, not_not.mp hxA⟩
    exact this ▸ hKL
  by_contra hLne
  have hUL : ¬ X \ Z ⊆ L := fun hs =>
    hLne (Subset.antisymm hLT (closure_minimal hs hL.1.isClosed))
  obtain ⟨x, hxU, hxL⟩ := not_subset.mp hUL
  have hxA : x ∈ A := (hcov hxU).resolve_right fun hxB => hxL (hBL hxB)
  obtain ⟨q, hqZ, hqY⟩ := h.right_diff_nonempty
  refine hnt (isWeakTriod_of hA hL h.2.2.1 ?_ ⟨x, hxA, hxL, hxU.2⟩ ⟨p', hp'L, hp.2, hp.1.2⟩
    ⟨q, hqZ, fun hqA => h.closure_diff_disjoint (hAU hqA) ⟨hqZ, hqY⟩,
      fun hqL => h.closure_diff_disjoint (hLT hqL) ⟨hqZ, hqY⟩⟩ ⟨w, hAZ ⟨hwT, hwZ⟩, hwL, hwZ⟩)
  apply Subset.antisymm
  · intro y hy
    by_cases hyZ : y ∈ Z
    · exact Or.inr hyZ
    · rcases hcov ⟨hy, hyZ⟩ with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inl (Or.inr (hBL h'))
  · exact union_subset (union_subset (hAU.trans h.closure_diff_subset)
      (hLT.trans h.closure_diff_subset)) h.right_subset

omit [CompactSpace S] in
/-- **11.32.** `X = Y ⊕ Z` unicoherent, not a weak triod, `U = X ∖ Z`, `A ⊊ Ū` a subcontinuum
with `A ⊇ Ū ∩ Z`, `W = U ∖ A`. If `W̄ = E ⊕ F` then exactly one of `E`, `F` misses `A`. -/
theorem nadler_11_32 {X Y Z A E F : Set S} (h : IsEssentialSum₂ X Y Z) (hu : IsUnicoherent X)
    (hnt : ¬ IsWeakTriod X) (hA : Fold.Q78.IsContinuum A) (hAU : A ⊆ closure (X \ Z))
    (hAZ : closure (X \ Z) ∩ Z ⊆ A)
    (hEF : IsEssentialSum₂ (closure ((X \ Z) \ A)) E F) :
    (E ∩ A = ∅ ∧ (F ∩ A).Nonempty) ∨ (F ∩ A = ∅ ∧ (E ∩ A).Nonempty) := by
  set W := (X \ Z) \ A with hW_def
  have hWT : closure W ⊆ closure (X \ Z) := closure_mono diff_subset
  have hWX : closure W ⊆ X := hWT.trans h.closure_diff_subset
  have hE : E ⊆ closure W := hEF.left_subset
  have hF : F ⊆ closure W := hEF.right_subset
  have hEFeq : closure W = E ∪ F := hEF.2.2.2.1
  obtain ⟨w, hw⟩ := h.closure_inter_nonempty
  have hZA : Fold.Q78.IsContinuum (Z ∪ A) := isContinuum_union h.2.2.1 hA ⟨w, hw.2, hAZ hw⟩
  have hXeq : X = closure W ∪ (Z ∪ A) := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxZA : x ∈ Z ∪ A
      · exact Or.inr hxZA
      · exact Or.inl (subset_closure ⟨⟨hx, fun h' => hxZA (Or.inl h')⟩, fun h' => hxZA (Or.inr h')⟩)
    · exact union_subset hWX (union_subset h.right_subset (hAU.trans h.closure_diff_subset))
  obtain ⟨q, hqZ, hqY⟩ := h.right_diff_nonempty
  have hqT : q ∉ closure (X \ Z) := fun hq => h.closure_diff_disjoint hq ⟨hqZ, hqY⟩
  -- a point of `W` outside a proper summand
  have hout : ∀ G : Set S, IsClosed G → G ≠ closure W → G ⊆ closure W → ∃ x ∈ W, x ∉ G :=
    fun G hG hne hsub => by
      by_contra hc
      push_neg at hc
      exact hne (Subset.antisymm hsub (closure_minimal hc hG))
  -- (*) `E ∩ F ∩ (Z ∪ A) = ∅`
  have hstar : ∀ x, x ∈ E → x ∈ F → x ∈ Z ∪ A → False := by
    intro c hcE hcF hcZA
    obtain ⟨x, hxW, hxF⟩ := hout F hEF.2.2.1.1.isClosed hEF.2.2.2.2.2 hF
    obtain ⟨y, hyW, hyE⟩ := hout E hEF.2.1.1.isClosed hEF.2.2.2.2.1 hE
    have hxE : x ∈ E := ((hEFeq ▸ subset_closure hxW : x ∈ E ∪ F)).resolve_right hxF
    have hyF : y ∈ F := ((hEFeq ▸ subset_closure hyW : y ∈ E ∪ F)).resolve_left hyE
    have hnZA : ∀ z ∈ W, z ∉ Z ∪ A := fun z hz h' => by
      rcases h' with h' | h'
      · exact hz.1.2 h'
      · exact hz.2 h'
    refine hnt (isWeakTriod_of hEF.2.1 hEF.2.2.1 hZA ?_ ⟨x, hxE, hxF, hnZA x hxW⟩
      ⟨y, hyF, hyE, hnZA y hyW⟩ ⟨q, Or.inl hqZ, fun h' => hqT (hWT (hE h')),
        fun h' => hqT (hWT (hF h'))⟩ ⟨c, hcE, hcF, hcZA⟩)
    rw [hXeq, hEFeq]
  -- unicoherence: `(Z ∪ A) ∩ W̄` is connected, hence lies in one of the two pieces
  have hconn := hu (closure W) (Z ∪ A) hEF.1 hZA hXeq.symm
  have hone : (E ∩ (Z ∪ A) = ∅) ∨ (F ∩ (Z ∪ A) = ∅) := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn.isPreconnected E F
      hEF.2.1.1.isClosed hEF.2.2.1.1.isClosed (fun x hx => hEFeq ▸ hx.1)
      (by
        ext x
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        rintro ⟨_, hxZA⟩ hxE hxF
        exact hstar x hxE hxF hxZA) with h' | h'
    · right
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hxF hxZA
      exact hstar x (h' ⟨hF hxF, hxZA⟩) hxF hxZA
    · left
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hxE hxZA
      exact hstar x hxE (h' ⟨hE hxE, hxZA⟩) hxZA
  have hEA : E ∩ (Z ∪ A) = ∅ → E ∩ A = ∅ := fun h' =>
    eq_empty_of_subset_empty (h' ▸ inter_subset_inter_right _ subset_union_right)
  have hFA : F ∩ (Z ∪ A) = ∅ → F ∩ A = ∅ := fun h' =>
    eq_empty_of_subset_empty (h' ▸ inter_subset_inter_right _ subset_union_right)
  -- not both
  have hnotboth : E ∩ A = ∅ → F ∩ A = ∅ → False := by
    intro hE' hF'
    have hWA : ∀ x ∈ closure W, x ∉ Z ∪ A := fun x hx hxZA => by
      have hxA : x ∈ A := by
        rcases hxZA with h' | h'
        · exact hAZ ⟨hWT hx, h'⟩
        · exact h'
      rcases hEFeq ▸ hx with h' | h'
      · exact (eq_empty_iff_forall_notMem.mp hE') x ⟨h', hxA⟩
      · exact (eq_empty_iff_forall_notMem.mp hF') x ⟨h', hxA⟩
    obtain ⟨x, hx1, hx2, hx3⟩ := isPreconnected_closed_iff.mp h.1.2.isPreconnected _ _
      isClosed_closure hZA.1.isClosed hXeq.subset
      (by obtain ⟨x, hx⟩ := hEF.1.2.nonempty; exact ⟨x, hWX hx, hx⟩)
      ⟨w, h.right_subset hw.2, Or.inl hw.2⟩
    exact hWA x hx2 hx3
  rcases hone with h' | h'
  · have hE' := hEA h'
    refine Or.inl ⟨hE', nonempty_iff_ne_empty.mpr fun hF' => hnotboth hE' hF'⟩
  · have hF' := hFA h'
    refine Or.inr ⟨hF', nonempty_iff_ne_empty.mpr fun hE' => hnotboth hE' hF'⟩

omit [CompactSpace S] in
/-- The first half of the proof of 11.33: a subcontinuum `K` containing `p ∈ U` and `q ∈ V`
contains `U`, when `Ū = irr(p, Ū ∩ Z)`. -/
theorem diff_subset_of_irr {X Y Z K : Set S} {p q : S} (h : IsEssentialSum₂ X Y Z)
    (hu : IsUnicoherent X) (hp : p ∈ X \ Z) (hq : q ∈ X \ Y)
    (hU : IrrFromTo (closure (X \ Z)) {p} (closure (X \ Z) ∩ Z)) (hK : Fold.Q78.IsContinuum K)
    (hKX : K ⊆ X) (hpK : p ∈ K) (hqK : q ∈ K) : X \ Z ⊆ K := by
  have hqZ : q ∈ Z := h.symm.diff_subset_left hq
  have hKZ : Fold.Q78.IsContinuum (K ∪ Z) := isContinuum_union hK h.2.2.1 ⟨q, hqK, hqZ⟩
  have hXeq : (K ∪ Z) ∪ closure (X \ Z) = X := by
    apply Subset.antisymm
    · exact union_subset (union_subset hKX h.right_subset) h.closure_diff_subset
    · intro x hx
      by_cases hxZ : x ∈ Z
      · exact Or.inl (Or.inr hxZ)
      · exact Or.inr (subset_closure ⟨hx, hxZ⟩)
  have hL := hu _ _ hKZ hU.1 hXeq
  have hLc : Fold.Q78.IsContinuum ((K ∪ Z) ∩ closure (X \ Z)) :=
    ⟨hKZ.1.inter_right isClosed_closure, hL⟩
  have hpT : p ∈ closure (X \ Z) := subset_closure hp
  have hLZ : (((K ∪ Z) ∩ closure (X \ Z)) ∩ (closure (X \ Z) ∩ Z)).Nonempty := by
    by_contra hc
    rw [not_nonempty_iff_eq_empty] at hc
    have hsplit : K ∪ Z ⊆ ((K ∪ Z) ∩ closure (X \ Z)) ∪ Z := by
      intro x hx
      by_cases hxZ : x ∈ Z
      · exact Or.inr hxZ
      · rcases hx with h' | h'
        · exact Or.inl ⟨Or.inl h', subset_closure ⟨hKX h', hxZ⟩⟩
        · exact absurd h' hxZ
    obtain ⟨x, -, hx1, hx2⟩ := isPreconnected_closed_iff.mp hKZ.2.isPreconnected _ _ hLc.1.isClosed
      h.2.2.1.1.isClosed hsplit ⟨p, Or.inl hpK, Or.inl hpK, hpT⟩ ⟨q, Or.inl hqK, hqZ⟩
    have : x ∈ ((K ∪ Z) ∩ closure (X \ Z)) ∩ (closure (X \ Z) ∩ Z) := ⟨hx1, hx1.2, hx2⟩
    rw [hc] at this
    exact this
  have heq := hU.2.2.2 _ hLc inter_subset_right ⟨p, ⟨Or.inl hpK, hpT⟩, rfl⟩ hLZ
  intro x hx
  have : x ∈ (K ∪ Z) ∩ closure (X \ Z) := by rw [heq]; exact subset_closure hx
  exact this.1.resolve_right hx.2

/-- **11.33.** `X = Y ⊕ Z` unicoherent, not a weak triod, `U = X ∖ Z`, `V = X ∖ Y`, `p ∈ U`,
`q ∈ V`. If `Ū = irr(p, Ū ∩ Z)` and `V̄ = irr(q, V̄ ∩ Y)` then `X` is irreducible between `p` and
`q`. -/
theorem nadler_11_33 {X Y Z : Set S} {p q : S} (h : IsEssentialSum₂ X Y Z) (hu : IsUnicoherent X)
    (hnt : ¬ IsWeakTriod X) (hp : p ∈ X \ Z) (hq : q ∈ X \ Y)
    (hU : IrrFromTo (closure (X \ Z)) {p} (closure (X \ Z) ∩ Z))
    (hV : IrrFromTo (closure (X \ Y)) {q} (closure (X \ Y) ∩ Y)) :
    IsIrreducibleBetween X p q := by
  refine ⟨h.1, hp.1, hq.1, fun K hK hKX hpK hqK => ?_⟩
  by_contra hKne
  have hUK := diff_subset_of_irr h hu hp hq hU hK hKX hpK hqK
  have hVK := diff_subset_of_irr h.symm hu hq hp hV hK hKX hqK hpK
  set T := closure (X \ Z) with hT_def
  have hTK : T ⊆ K := closure_minimal hUK hK.1.isClosed
  have hVbK : closure (X \ Y) ⊆ K := closure_minimal hVK hK.1.isClosed
  have hqT : q ∉ T := fun h' => hq.2 (h.closure_diff_subset_left h')
  obtain ⟨J₀, hJ₀, hJ₀K, hJ₀cl, hqJ₀, w, hwJ₀, hwT⟩ := exists_continuum_bump_open hK
    isClosed_closure.isOpen_compl hqK hqT (fun hs => hs hpK (subset_closure hp))
  rw [Set.notMem_compl_iff] at hwT
  have hJ₀U : ∀ x ∈ J₀, x ∉ X \ Z := fun x hx hxU => by
    obtain ⟨y, hyZ, hyK, hyT⟩ := mem_closure_iff.mp (hJ₀cl hx) _ h.2.2.1.1.isClosed.isOpen_compl
      hxU.2
    exact hyT (subset_closure ⟨hKX hyK, hyZ⟩)
  have hVb := isContinuum_closure_diff h.symm hnt
  have hJ : Fold.Q78.IsContinuum (J₀ ∪ closure (X \ Y)) :=
    isContinuum_union hJ₀ hVb ⟨q, hqJ₀, subset_closure hq⟩
  have hVbZ : closure (X \ Y) ⊆ Z := h.symm.closure_diff_subset_left
  have hJU : ∀ x ∈ J₀ ∪ closure (X \ Y), x ∉ X \ Z := fun x hx hxU => by
    rcases hx with h' | h'
    · exact hJ₀U x h' hxU
    · exact hxU.2 (hVbZ h')
  have hYZ : Fold.Q78.IsContinuum (Y ∩ Z) :=
    ⟨h.2.1.1.inter_right h.2.2.1.1.isClosed, hu Y Z h.2.1 h.2.2.1 h.2.2.2.1.symm⟩
  have hTY : T ⊆ Y := h.closure_diff_subset_left
  obtain ⟨x, hxX, hxK⟩ := not_subset.mp fun hs => hKne (Subset.antisymm hKX hs)
  have hxZ : x ∈ Z := by_contra fun h' => hxK (hUK ⟨hxX, h'⟩)
  have hxY : x ∈ Y := by_contra fun h' => hxK (hVK ⟨hxX, h'⟩)
  have hwX : w ∈ X := hKX (hJ₀K hwJ₀)
  have hwZ : w ∈ Z := by_contra fun h' => hJ₀U w hwJ₀ ⟨hwX, h'⟩
  refine hnt (isWeakTriod_of hJ (isContinuum_closure_diff h hnt) hYZ ?_
    ⟨q, Or.inr (subset_closure hq), hqT, fun h' => hq.2 h'.1⟩
    ⟨p, subset_closure hp, fun h' => hJU p h' hp, fun h' => hp.2 h'.2⟩
    ⟨x, ⟨hxY, hxZ⟩, fun h' => by
      rcases h' with h' | h'
      · exact hxK (hJ₀K h')
      · exact hxK (hVbK h'), fun h' => hxK (hTK h')⟩
    ⟨w, Or.inl hwJ₀, hwT, hTY hwT, hwZ⟩)
  apply Subset.antisymm
  · intro y hy
    by_cases hyZ : y ∈ Z
    · by_cases hyY : y ∈ Y
      · exact Or.inr ⟨hyY, hyZ⟩
      · exact Or.inl (Or.inl (Or.inr (subset_closure ⟨hy, hyY⟩)))
    · exact Or.inl (Or.inr (subset_closure ⟨hy, hyZ⟩))
  · refine union_subset (union_subset (union_subset (hJ₀K.trans hKX) (hVbK.trans hKX))
      h.closure_diff_subset) (inter_subset_left.trans h.left_subset)

end HPC.Plane
