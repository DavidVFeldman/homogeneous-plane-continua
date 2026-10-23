import HPC.Moore.Sec6Th24

/-!
# Moore, F.A. (1916), §6: Theorem 25, in the topological setting (batch 138)

**Theorem 25.** Under the hypothesis of Theorem 24, `R = AXB (open) + R₁ + R₂`.

Moore's proof (pp. 141–143), formalized step by step (`Gen.th25`):

1. Suppose `R` has a point `E` not in `AXB + R₁ + R₂`; let `Y = R − (AXB + R₁' + R₂')`, so that
   `R − AXB = R₁ + R₂ + Y` with `R₁`, `R₂`, `Y` open and disjoint (\"It is clear that no one of
   the three sets … contains a limit point of either of the other two\").
2. An arc from `E` to a point of `R₁` inside `R`; its first point `O` on `AXB`; `OE − O ⊆ Y`.
3. An arc `ED` (`D` on the open arc `ADB`) without `R₁` (Axiom 3, Theorem 16); its first point
   `L` on `ADB`; `EL − L ⊆ Y` (\"It easily follows that `EL − L` is a subset of `Y`\").
4. Points `H̄, H, O, K, K̄` on `AXB` in this order and arcs `H̄P₂K̄` through `R₂`, `HP₁K` through
   `R₁` (\"It can easily be shown that the point-set `FG + GA` contains as a subset an arc `FH`
   …\": `exists_cross`). Moore chooses `H` near `A`; there the first point of `FG + GA` on the
   boundary of `R₁` may lie on `ACB` rather than on `AXB`. Here the arcs are aimed at interior
   points of `AXB`, which avoids the issue.
5. The closed curve `J̄ = H̄P₂K̄ + K̄K + KP₁H + HH̄` and its interior `R̄ ⊆ R` (Theorem 21).
6. `O` is without `J̄` (it is joined to `L ∉ R` by `OE + EL`, which misses `J̄`); hence so is
   every point of `AXB` off `J̄`; so `R̄ ⊆ R₁ + R₂ + Y`, while `R̄` meets `R₁` and `R₂` (at
   `P₁`, `P₂`), against Axiom 2.
-/

namespace HPC.Moore

open Set Topology
open unitInterval (nonneg' le_one')

namespace Gen

variable {T : Type*} [TopologicalSpace T] [T2Space T] {reg : Set (Set T)}

/-- **Theorem 25**, topologically. -/
theorem th25 [LocallyConnectedSpace T] (hopen : ∀ R ∈ reg, IsOpen R)
    (hpc : ∀ R ∈ reg, IsPreconnected R) (h21 : Th21Prop reg) (harc : ArcConn T)
    (h8 : Ax8Prop reg) (hext : ∀ R ∈ reg, IsPreconnected (closure R)ᶜ)
    {J R : Set T} (hR : TInt reg J R) {A B : T} {C₁ C₂ : Set T} (hC₁ : TArc A B C₁)
    (hC₂ : TArc A B C₂) (hC12 : C₁ ∩ C₂ = {A, B}) (hCJ : C₁ ∪ C₂ = J)
    {Xa : Set T} (hX : TArc A B Xa) (hXR : Xa \ {A, B} ⊆ R) {R₁ R₂ : Set T}
    (hR₁ : TInt reg (Xa ∪ C₁) R₁) (hR₂ : TInt reg (Xa ∪ C₂) R₂) :
    R = Xa \ {A, B} ∪ R₁ ∪ R₂ := by
  have hRreg := hR.2.1
  have hRo := hopen R hRreg
  have hR₁o := hopen R₁ hR₁.2.1
  have hR₂o := hopen R₂ hR₂.2.1
  have hC₁J : C₁ ⊆ J := hCJ ▸ subset_union_left
  have hC₂J : C₂ ⊆ J := hCJ ▸ subset_union_right
  have hAJ : A ∈ J := hC₁J hC₁.left_mem
  have hBJ : B ∈ J := hC₁J hC₁.right_mem
  have hRJ' : ∀ x ∈ R, x ∉ J := fun x hx hxJ => notMem_of_mem_frontier hRo (hR.2.2 ▸ hxJ) hx
  have hR₁R : R₁ ⊆ R := th24_sub h21 hR hAJ hBJ hC₁J hXR hR₁
  have hR₂R : R₂ ⊆ R := th24_sub h21 hR hAJ hBJ hC₂J hXR hR₂
  have hC₂ext : C₂ \ {A, B} ⊆ (closure R₁)ᶜ := th24_ext hopen hR hC₂J hC12 hXR hR₁ hR₁R
  have hdis : Disjoint R₁ R₂ :=
    th24_disj hopen hpc hR hC₁J hR₁ hR₂ hR₂R hC₂ext hC₂.nonempty_diff
  have hXfr₁ : Xa ⊆ frontier R₁ := hR₁.2.2 ▸ subset_union_left
  have hXfr₂ : Xa ⊆ frontier R₂ := hR₂.2.2 ▸ subset_union_left
  have hXcl₁ : Xa ⊆ closure R₁ := hXfr₁.trans frontier_subset_closure
  have hXcl₂ : Xa ⊆ closure R₂ := hXfr₂.trans frontier_subset_closure
  have hXR' : ∀ x ∈ Xa, x ≠ A → x ≠ B → x ∈ R := fun x hx hA hB => hXR ⟨hx, by simp [hA, hB]⟩
  have hAR : A ∉ R := fun h => hRJ' A h hAJ
  have hBR : B ∉ R := fun h => hRJ' B h hBJ
  have hne_of_fr : ∀ W : Set T, A ∈ frontier W → W.Nonempty := by
    intro W hW
    rw [nonempty_iff_ne_empty]; rintro rfl; simp at hW
  apply subset_antisymm _ (union_subset (union_subset hXR hR₁R) hR₂R)
  intro E hER
  by_contra hE
  simp only [mem_union, not_or] at hE
  obtain ⟨⟨hEX', hER₁⟩, hER₂⟩ := hE
  have hEX : E ∉ Xa := fun h => hEX' ⟨h, by
    rintro (rfl | rfl)
    · exact hAR hER
    · exact hBR hER⟩
  -- Step 1: the set `Y`
  set Y := R ∩ (closure R₁)ᶜ ∩ (closure R₂)ᶜ with hY
  have hmemY : ∀ x ∈ R, x ∉ Xa → x ∉ R₁ → x ∉ R₂ → x ∈ Y := by
    intro x hx hxX hx1 hx2
    refine ⟨⟨hx, fun hcl => ?_⟩, fun hcl => ?_⟩
    · rw [closure_eq_union_frontier hR₁o, hR₁.2.2] at hcl
      rcases hcl with h | h | h
      exacts [hx1 h, hxX h, hRJ' x hx (hC₁J h)]
    · rw [closure_eq_union_frontier hR₂o, hR₂.2.2] at hcl
      rcases hcl with h | h | h
      exacts [hx2 h, hxX h, hRJ' x hx (hC₂J h)]
  have hEY := hmemY E hER hEX hER₁ hER₂
  have hYo : IsOpen Y :=
    (hRo.inter isClosed_closure.isOpen_compl).inter isClosed_closure.isOpen_compl
  have hdec : ∀ x ∈ R, x ∉ Xa → x ∈ R₁ ∨ x ∈ R₂ ∨ x ∈ Y := by
    intro x hx hxX
    by_cases h1 : x ∈ R₁
    · exact Or.inl h1
    by_cases h2 : x ∈ R₂
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hmemY x hx hxX h1 h2))
  have hfrR : ∀ Z : Set T, Z ⊆ R → (∀ x ∈ Z, x ∉ Xa) →
      Disjoint Z (frontier R₁) ∧ Disjoint Z (frontier R₂) := by
    intro Z hZR hZX
    refine ⟨?_, ?_⟩
    · rw [hR₁.2.2]
      refine disjoint_left.mpr fun x hxZ hx => ?_
      rcases hx with hx | hx
      exacts [hZX x hxZ hx, hRJ' x (hZR hxZ) (hC₁J hx)]
    · rw [hR₂.2.2]
      refine disjoint_left.mpr fun x hxZ hx => ?_
      rcases hx with hx | hx
      exacts [hZX x hxZ hx, hRJ' x (hZR hxZ) (hC₂J hx)]
  -- Step 2: the point `O`
  obtain ⟨F, hF⟩ := hne_of_fr R₁ (hXfr₁ hX.left_mem)
  have hEF : E ≠ F := fun h => hER₁ (h ▸ hF)
  obtain ⟨ε, hεR, hε⟩ := harc R hRo (hpc R hRreg) E hER F (hR₁R hF) hEF
  have hεX : (ε ∩ Xa).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hnX : ∀ x ∈ ε, x ∉ Xa := fun x hx hxX => (eq_empty_iff_forall_notMem.mp hne) x ⟨hx, hxX⟩
    have := conn_sub_ext_of_frontier hε.isPreconnected (hfrR ε hεR hnX).1
      ⟨E, hε.left_mem, hEY.1.2⟩
    exact this hε.right_mem (subset_closure hF)
  obtain ⟨O, hOX, Γ₁, hΓ₁ε, hΓ₁, hΓ₁X⟩ := hε.first_point hX.isClosed hεX hEX
  have hOR : O ∈ R := hεR (hΓ₁ε hΓ₁.right_mem)
  have hΓ₁Y : Γ₁ \ {O} ⊆ Y := by
    have hpre := hΓ₁.isPreconnected_diff_right
    have hsubR : Γ₁ \ {O} ⊆ R := fun x hx => hεR (hΓ₁ε hx.1)
    have hnX : ∀ x ∈ Γ₁ \ {O}, x ∉ Xa := fun x hx hxX =>
      hx.2 (by rw [← hΓ₁X]; exact ⟨hx.1, hxX⟩)
    have hEin : E ∈ Γ₁ \ {O} := ⟨hΓ₁.left_mem, fun h => hEX (h ▸ hOX)⟩
    obtain ⟨hfr₁, hfr₂⟩ := hfrR _ hsubR hnX
    have h1 := conn_sub_ext_of_frontier hpre hfr₁ ⟨E, hEin, hEY.1.2⟩
    have h2 := conn_sub_ext_of_frontier hpre hfr₂ ⟨E, hEin, hEY.2⟩
    exact fun x hx => ⟨⟨hsubR hx, h1 hx⟩, h2 hx⟩
  -- Step 3: the point `L`
  obtain ⟨D, hD⟩ := hC₂.nonempty_diff
  have hDext := hC₂ext hD
  have hED : E ≠ D := fun h => hRJ' E hER (h ▸ hC₂J hD.1)
  obtain ⟨δ, hδE, hδ⟩ := harc _ isClosed_closure.isOpen_compl (hext R₁ hR₁.2.1) E hEY.1.2 D
    hDext hED
  obtain ⟨L, hLC₂, Γ₂, hΓ₂δ, hΓ₂, hΓ₂C⟩ := hδ.first_point hC₂.isClosed
    ⟨D, hδ.right_mem, hD.1⟩ (fun h => hRJ' E hER (hC₂J h))
  have hLR : L ∉ R := fun h => hRJ' L h (hC₂J hLC₂)
  have hΓ₂Y : Γ₂ \ {L} ⊆ Y := by
    have hpre := hΓ₂.isPreconnected_diff_right
    have hEin : E ∈ Γ₂ \ {L} := ⟨hΓ₂.left_mem, fun h => hLR (h ▸ hER)⟩
    have hcl1 : Γ₂ \ {L} ⊆ (closure R₁)ᶜ := fun x hx => hδE (hΓ₂δ hx.1)
    have hnC₂ : ∀ x ∈ Γ₂ \ {L}, x ∉ C₂ := fun x hx hxC =>
      hx.2 (by rw [← hΓ₂C]; exact ⟨hx.1, hxC⟩)
    have hnC₁ : ∀ x ∈ Γ₂ \ {L}, x ∉ C₁ := fun x hx hxC =>
      hcl1 hx (frontier_subset_closure (hR₁.2.2 ▸ Or.inr hxC))
    have hnX : ∀ x ∈ Γ₂ \ {L}, x ∉ Xa := fun x hx hxX => hcl1 hx (hXcl₁ hxX)
    have hfrR' : Disjoint (Γ₂ \ {L}) (frontier R) := by
      rw [hR.2.2, ← hCJ]
      refine disjoint_left.mpr fun x hx hxJ => ?_
      rcases hxJ with h | h
      exacts [hnC₁ x hx h, hnC₂ x hx h]
    have hsubR := conn_sub_of_frontier hpre hfrR' ⟨E, hEin, hER⟩
    have hfr₂ : Disjoint (Γ₂ \ {L}) (frontier R₂) := (hfrR _ hsubR hnX).2
    have h2 := conn_sub_ext_of_frontier hpre hfr₂ ⟨E, hEin, hEY.2⟩
    exact fun x hx => ⟨⟨hsubR hx, hcl1 hx⟩, h2 hx⟩
  -- Step 4: parametrize `AXB`; the crossing arcs
  obtain ⟨f, hf, hfr, hf0, hf1⟩ := hX.2
  have hfX : ∀ u, f u ∈ Xa := fun u => hfr ▸ mem_range_self u
  have hinj := hf.injective
  obtain ⟨o, rfl⟩ : ∃ o, f o = O := by rw [← hfr] at hOX; exact hOX
  have ho0 : 0 < o := lt_of_le_of_ne nonneg' fun e => hAR (by rw [← hf0, e]; exact hOR)
  have ho1 : o < 1 := lt_of_le_of_ne le_one' fun e => hBR (by rw [← hf1, ← e]; exact hOR)
  have hfR : ∀ u, 0 < u → u < 1 → f u ∈ R := fun u h0 h1 =>
    hXR' (f u) (hfX u) (fun e => h0.ne' (hinj (e.trans hf0.symm)))
      (fun e => h1.ne (hinj (e.trans hf1.symm)))
  set N : unitInterval → unitInterval → Set T :=
    fun a b => (C₁ ∪ C₂ ∪ f '' Icc 0 a ∪ f '' Icc b 1)ᶜ with hN
  have hNo : ∀ a b, IsOpen (N a b) := fun a b =>
    (((hC₁.isClosed.union hC₂.isClosed).union (isCompact_Icc.image hf.continuous).isClosed).union
      (isCompact_Icc.image hf.continuous).isClosed).isOpen_compl
  have hNmem : ∀ a b q, a < q → q < b → f q ∈ N a b := by
    intro a b q haq hqb hmem
    have hq0 : 0 < q := lt_of_le_of_lt nonneg' haq
    have hq1 : q < 1 := lt_of_lt_of_le hqb le_one'
    rcases hmem with ((h | h) | h) | h
    · exact hRJ' _ (hfR q hq0 hq1) (hC₁J h)
    · exact hRJ' _ (hfR q hq0 hq1) (hC₂J h)
    · rw [hinj.mem_set_image] at h; exact absurd h.2 (not_le.mpr haq)
    · rw [hinj.mem_set_image] at h; exact absurd h.1 (not_le.mpr hqb)
  have hNpar : ∀ a b x, x ∈ Xa ∪ (C₁ ∪ C₂) → x ∈ N a b → ∃ u, a < u ∧ u < b ∧ f u = x := by
    intro a b x hx hxN
    simp only [hN, mem_compl_iff, mem_union, not_or] at hxN
    obtain ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩ := hxN
    rcases hx with hx | hx | hx
    · rw [← hfr] at hx
      obtain ⟨u, rfl⟩ := hx
      refine ⟨u, not_le.mp fun h => hx3 (mem_image_of_mem f ⟨nonneg', h⟩),
        not_le.mp fun h => hx4 (mem_image_of_mem f ⟨h, le_one'⟩), rfl⟩
    · exact absurd hx hx1
    · exact absurd hx hx2
  have hNdis : ∀ (W : Set T) a b c, frontier W ⊆ Xa ∪ (C₁ ∪ C₂) →
      Disjoint (frontier W ∩ N a b) (N b c) := by
    intro W a b c hW
    refine disjoint_left.mpr fun x ⟨hxW, hxN⟩ hxN' => ?_
    obtain ⟨u, -, hub, rfl⟩ := hNpar a b x (hW hxW) hxN
    exact hxN' (Or.inl (Or.inr (mem_image_of_mem f ⟨nonneg', hub.le⟩)))
  have hfrR₁ : frontier R₁ ⊆ Xa ∪ (C₁ ∪ C₂) := by
    rw [hR₁.2.2]; exact union_subset_union_right _ subset_union_left
  have hfrR₂ : frontier R₂ ⊆ Xa ∪ (C₁ ∪ C₂) := by
    rw [hR₂.2.2]; exact union_subset_union_right _ subset_union_right
  -- the arc `H̄P₂K̄` through `R₂`
  obtain ⟨q₁, hq₁0, hq₁o⟩ := exists_between ho0
  obtain ⟨q₂, hoq₂, hq₂1⟩ := exists_between ho1
  obtain ⟨Hb, ⟨hHbfr, hHbN⟩, Kb, ⟨hKbfr, hKbN⟩, β, hβ, hβR₂⟩ := exists_cross harc hR₂o
    (hpc R₂ hR₂.2.1) (hne_of_fr R₂ (hXfr₂ hX.left_mem)) (hXfr₂ (hfX q₁)) (hXfr₂ (hfX q₂))
    ((hNo 0 o).mem_nhds (hNmem 0 o q₁ hq₁0 hq₁o)) ((hNo o 1).mem_nhds (hNmem o 1 q₂ hoq₂ hq₂1))
    (hNdis R₂ 0 o 1 hfrR₂)
  obtain ⟨hb, -, hbo, rfl⟩ := hNpar 0 o Hb (hfrR₂ hHbfr) hHbN
  obtain ⟨kb, hokb, -, rfl⟩ := hNpar o 1 Kb (hfrR₂ hKbfr) hKbN
  -- the arc `HP₁K` through `R₁`
  obtain ⟨q₃, hbq₃, hq₃o⟩ := exists_between hbo
  obtain ⟨q₄, hoq₄, hq₄kb⟩ := exists_between hokb
  obtain ⟨Ha, ⟨hHafr, hHaN⟩, Ka, ⟨hKafr, hKaN⟩, α, hα, hαR₁⟩ := exists_cross harc hR₁o
    (hpc R₁ hR₁.2.1) ⟨F, hF⟩ (hXfr₁ (hfX q₃)) (hXfr₁ (hfX q₄))
    ((hNo hb o).mem_nhds (hNmem hb o q₃ hbq₃ hq₃o))
    ((hNo o kb).mem_nhds (hNmem o kb q₄ hoq₄ hq₄kb)) (hNdis R₁ hb o kb hfrR₁)
  obtain ⟨h, hbh, hho, rfl⟩ := hNpar hb o Ha (hfrR₁ hHafr) hHaN
  obtain ⟨k, hok, hkkb, rfl⟩ := hNpar o kb Ka (hfrR₁ hKafr) hKaN
  have hhk : h < k := hho.trans hok
  -- Step 5: the closed curve `J̄`
  have hαX : ∀ x ∈ α, x ∈ Xa → x = f h ∨ x = f k := by
    intro x hx hxX
    by_contra hne
    push_neg at hne
    exact notMem_of_mem_frontier hR₁o (hXfr₁ hxX) (hαR₁ ⟨hx, by simp [hne.1, hne.2]⟩)
  have hβX : ∀ x ∈ β, x ∈ Xa → x = f hb ∨ x = f kb := by
    intro x hx hxX
    by_contra hne
    push_neg at hne
    exact notMem_of_mem_frontier hR₂o (hXfr₂ hxX) (hβR₂ ⟨hx, by simp [hne.1, hne.2]⟩)
  have hαβ : Disjoint α β := by
    refine disjoint_left.mpr fun x hxα hxβ => ?_
    by_cases hxX : x ∈ Xa
    · rcases hαX x hxα hxX with rfl | rfl <;> rcases hβX _ hxβ hxX with e | e <;>
        have e' := hinj e
      · exact hbh.ne' e'
      · exact (hho.trans hokb).ne e'
      · exact (hbo.trans hok).ne' e'
      · exact hkkb.ne e'
    · have h1 : x ∈ R₁ := hαR₁ ⟨hxα, by
        rintro (rfl | rfl)
        · exact hxX (hfX h)
        · exact hxX (hfX k)⟩
      have h2 : x ∈ R₂ := hβR₂ ⟨hxβ, by
        rintro (rfl | rfl)
        · exact hxX (hfX hb)
        · exact hxX (hfX kb)⟩
      exact disjoint_left.mp hdis h1 h2
  have hA1 : TArc (f h) (f kb) (α ∪ f '' Icc k kb) := by
    refine hα.union (TArc.image_Icc hf hkkb) (subset_antisymm ?_ ?_)
    · rintro x ⟨hxα, v, hv, rfl⟩
      rcases hαX _ hxα (hfX v) with e | e
      · exact absurd (hinj e ▸ hv.1) (not_le.mpr hhk)
      · exact e
    · rintro x rfl; exact ⟨hα.right_mem, mem_image_of_mem f ⟨le_rfl, hkkb.le⟩⟩
  have hA2 : TArc (f h) (f kb) (f '' Icc hb h ∪ β) := by
    refine (TArc.image_Icc hf hbh).symm.union hβ (subset_antisymm ?_ ?_)
    · rintro x ⟨⟨v, hv, rfl⟩, hxβ⟩
      rcases hβX _ hxβ (hfX v) with e | e
      · exact e
      · exact absurd (hinj e ▸ hv.2) (not_le.mpr (hho.trans hokb))
    · rintro x rfl; exact ⟨mem_image_of_mem f ⟨le_rfl, hbh.le⟩, hβ.left_mem⟩
  set Jb := α ∪ f '' Icc k kb ∪ (f '' Icc hb h ∪ β) with hJbdef
  have hJb : TSCC Jb := by
    refine ⟨f h, f kb, _, _, hA1, hA2, subset_antisymm ?_ ?_, rfl⟩
    · rintro x ⟨hx1 | ⟨v, hv, rfl⟩, hx2 | hx2⟩
      · obtain ⟨v, hv, rfl⟩ := hx2
        rcases hαX _ hx1 (hfX v) with e | e
        · exact Or.inl e
        · exact absurd (hinj e ▸ hv.2) (not_le.mpr hhk)
      · exact absurd hx2 (disjoint_left.mp hαβ hx1)
      · obtain ⟨w, hw, e⟩ := hx2
        exact absurd (hinj e ▸ hw.2) (not_le.mpr (lt_of_lt_of_le hhk hv.1))
      · rcases hβX _ hx2 (hfX v) with e | e
        · exact absurd (hinj e ▸ hv.1) (not_le.mpr ((hbo.trans hok)))
        · exact Or.inr e
    · rintro x (rfl | rfl)
      · exact ⟨Or.inl hα.left_mem, Or.inl (mem_image_of_mem f ⟨hbh.le, le_rfl⟩)⟩
      · exact ⟨Or.inr (mem_image_of_mem f ⟨hkkb.le, le_rfl⟩), Or.inr hβ.right_mem⟩
  -- Step 6: the interior `R̄` of `J̄` lies in `R`
  obtain ⟨Rb, hRbreg, hRbJ⟩ := h8 Jb hJb
  have hRbo := hopen Rb hRbreg
  have hαsub : ∀ x ∈ α, x ∈ R₁ ∨ x = f h ∨ x = f k := by
    intro x hx
    by_cases hx' : x = f h ∨ x = f k
    · exact Or.inr hx'
    · push_neg at hx'
      exact Or.inl (hαR₁ ⟨hx, by simp [hx'.1, hx'.2]⟩)
  have hβsub : ∀ x ∈ β, x ∈ R₂ ∨ x = f hb ∨ x = f kb := by
    intro x hx
    by_cases hx' : x = f hb ∨ x = f kb
    · exact Or.inr hx'
    · push_neg at hx'
      exact Or.inl (hβR₂ ⟨hx, by simp [hx'.1, hx'.2]⟩)
  have hb0 : 0 < hb := lt_of_le_of_ne nonneg' fun e =>
    hHbN (Or.inl (Or.inl (Or.inl (by rw [← e, hf0]; exact hC₁.left_mem))))
  have hkb1 : kb < 1 := lt_of_le_of_ne le_one' fun e =>
    hKbN (Or.inl (Or.inl (Or.inl (by rw [e, hf1]; exact hC₁.right_mem))))
  have hJbcl : Jb ⊆ closure R₁ ∪ closure R₂ := by
    rintro x ((hx | ⟨v, -, rfl⟩) | (⟨v, -, rfl⟩ | hx))
    · rcases hαsub x hx with h' | rfl | rfl
      exacts [Or.inl (subset_closure h'), Or.inl (hXcl₁ (hfX _)), Or.inl (hXcl₁ (hfX _))]
    · exact Or.inl (hXcl₁ (hfX v))
    · exact Or.inl (hXcl₁ (hfX v))
    · rcases hβsub x hx with h' | rfl | rfl
      exacts [Or.inr (subset_closure h'), Or.inr (hXcl₂ (hfX _)), Or.inr (hXcl₂ (hfX _))]
  have hJbR : Jb ⊆ R := by
    rintro x ((hx | ⟨v, hv, rfl⟩) | (⟨v, hv, rfl⟩ | hx))
    · rcases hαsub x hx with h' | rfl | rfl
      · exact hR₁R h'
      · exact hfR h (hb0.trans hbh) (hho.trans ho1)
      · exact hfR k (ho0.trans hok) (hkkb.trans hkb1)
    · exact hfR v (ho0.trans (hok.trans_le hv.1)) (hv.2.trans_lt hkb1)
    · exact hfR v (hb0.trans_le hv.1) (hv.2.trans_lt (hho.trans ho1))
    · rcases hβsub x hx with h' | rfl | rfl
      · exact hR₂R h'
      · exact hfR hb hb0 (hbo.trans ho1)
      · exact hfR kb (ho0.trans hokb) hkb1
  have hRbR : Rb ⊆ R := h21 R hRreg Rb hRbreg (hRbJ ▸ hJbR.trans subset_closure)
  have hclRb : closure Rb ⊆ R := by
    rw [closure_eq_union_frontier hRbo, hRbJ]; exact union_subset hRbR hJbR
  -- Step 7: `O` is without `J̄`
  have hYJb : Disjoint Y Jb := disjoint_left.mpr fun x hxY hxJ =>
    (hJbcl hxJ).elim hxY.1.2 hxY.2
  have hOJb : f o ∉ Jb := by
    rintro ((hx | ⟨v, hv, e⟩) | (⟨v, hv, e⟩ | hx))
    · rcases hαX _ hx (hfX o) with e | e <;> have e' := hinj e
      exacts [hho.ne' e', hok.ne e']
    · exact absurd (hinj e ▸ hv.1) (not_le.mpr hok)
    · exact absurd (hinj e ▸ hv.2) (not_le.mpr hho)
    · rcases hβX _ hx (hfX o) with e | e <;> have e' := hinj e
      exacts [hbo.ne' e', hokb.ne e']
  have hΓ : IsPreconnected (Γ₁ ∪ Γ₂) :=
    hΓ₁.isPreconnected.union E hΓ₁.left_mem hΓ₂.left_mem hΓ₂.isPreconnected
  have hΓJb : Disjoint (Γ₁ ∪ Γ₂) (frontier Rb) := by
    rw [hRbJ]
    refine disjoint_left.mpr fun x hx hxJ => ?_
    rcases hx with hx | hx
    · by_cases hxO : x = f o
      · exact hOJb (hxO ▸ hxJ)
      · exact disjoint_left.mp hYJb (hΓ₁Y ⟨hx, hxO⟩) hxJ
    · by_cases hxL : x = L
      · exact hLR (hJbR (hxL ▸ hxJ))
      · exact disjoint_left.mp hYJb (hΓ₂Y ⟨hx, hxL⟩) hxJ
  have hΓext := conn_sub_ext_of_frontier hΓ hΓJb
    ⟨L, Or.inr hΓ₂.right_mem, fun h' => hLR (hclRb h')⟩
  have hOext : f o ∉ closure Rb := hΓext (Or.inl hΓ₁.right_mem)
  -- Step 8: `AXB` misses `R̄`
  have hJbf : ∀ v, f v ∈ Jb → v ∈ Icc hb h ∨ v ∈ Icc k kb := by
    rintro v ((hx | ⟨w, hw, e⟩) | (⟨w, hw, e⟩ | hx))
    · rcases hαX _ hx (hfX v) with e | e <;> have e' := hinj e <;> subst e'
      exacts [Or.inl ⟨hbh.le, le_rfl⟩, Or.inr ⟨le_rfl, hkkb.le⟩]
    · exact Or.inr (hinj e ▸ hw)
    · exact Or.inl (hinj e ▸ hw)
    · rcases hβX _ hx (hfX v) with e | e <;> have e' := hinj e <;> subst e'
      exacts [Or.inl ⟨le_rfl, hbh.le⟩, Or.inr ⟨hkkb.le, le_rfl⟩]
  have hpiece : ∀ s : Set unitInterval, IsPreconnected s →
      (∀ v ∈ s, v ∉ Icc hb h ∧ v ∉ Icc k kb) → (∃ v ∈ s, f v ∉ closure Rb) →
      ∀ v ∈ s, f v ∉ Rb := by
    intro s hs hsJ ⟨v₀, hv₀, hv₀c⟩ v hv hvRb
    have hpre : IsPreconnected (f '' s) := hs.image _ hf.continuous.continuousOn
    have hd : Disjoint (f '' s) (frontier Rb) := by
      rw [hRbJ]
      refine disjoint_left.mpr ?_
      rintro _ ⟨w, hw, rfl⟩ hwJ
      exact (hJbf w hwJ).elim (hsJ w hw).1 (hsJ w hw).2
    exact conn_sub_ext_of_frontier hpre hd ⟨f v₀, mem_image_of_mem f hv₀, hv₀c⟩
      (mem_image_of_mem f hv) (subset_closure hvRb)
  have hXRb : ∀ v, f v ∉ Rb := by
    intro v hv
    have hvJ : f v ∉ Jb := fun h' => notMem_of_mem_frontier hRbo (hRbJ ▸ h') hv
    rcases lt_or_ge v hb with h1 | h1
    · refine hpiece (Ico 0 hb) isPreconnected_Ico (fun w hw => ⟨fun h' => ?_, fun h' => ?_⟩)
        ⟨0, ⟨le_rfl, hb0⟩, fun h' => hAR (hf0 ▸ hclRb h')⟩ v ⟨nonneg', h1⟩ hv
      · exact absurd h'.1 (not_le.mpr hw.2)
      · exact absurd h'.1 (not_le.mpr (hw.2.trans (hbo.trans hok)))
    rcases le_or_gt v h with h2 | h2
    · exact hvJ (Or.inr (Or.inl (mem_image_of_mem f ⟨h1, h2⟩)))
    rcases lt_or_ge v k with h3 | h3
    · refine hpiece (Ioo h k) isPreconnected_Ioo (fun w hw => ⟨fun h' => ?_, fun h' => ?_⟩)
        ⟨o, ⟨hho, hok⟩, hOext⟩ v ⟨h2, h3⟩ hv
      · exact absurd h'.2 (not_le.mpr hw.1)
      · exact absurd h'.1 (not_le.mpr hw.2)
    rcases le_or_gt v kb with h4 | h4
    · exact hvJ (Or.inl (Or.inr (mem_image_of_mem f ⟨h3, h4⟩)))
    · refine hpiece (Ioc kb 1) isPreconnected_Ioc (fun w hw => ⟨fun h' => ?_, fun h' => ?_⟩)
        ⟨1, ⟨hkb1, le_rfl⟩, fun h' => hBR (hf1 ▸ hclRb h')⟩ v ⟨h4, le_one'⟩ hv
      · exact absurd h'.2 (not_le.mpr ((hho.trans hokb).trans hw.1))
      · exact absurd h'.2 (not_le.mpr hw.1)
  -- Step 9: `R̄` meets `R₁` and `R₂` but misses `AXB`: Axiom 2 fails
  obtain ⟨P₁, hP₁⟩ := hα.nonempty_diff
  obtain ⟨P₂, hP₂⟩ := hβ.nonempty_diff
  have hP₁cl : P₁ ∈ closure Rb := frontier_subset_closure (hRbJ ▸ Or.inl (Or.inl hP₁.1))
  have hP₂cl : P₂ ∈ closure Rb := frontier_subset_closure (hRbJ ▸ Or.inr (Or.inr hP₂.1))
  obtain ⟨y₁, hy₁R₁, hy₁Rb⟩ := mem_closure_iff_nhds.mp hP₁cl R₁ (hR₁o.mem_nhds (hαR₁ hP₁))
  obtain ⟨y₂, hy₂R₂, hy₂Rb⟩ := mem_closure_iff_nhds.mp hP₂cl R₂ (hR₂o.mem_nhds (hβR₂ hP₂))
  have hsub : Rb ⊆ R₁ ∪ (R₂ ∪ Y) := by
    intro x hx
    have hxX : x ∉ Xa := by rw [← hfr]; rintro ⟨v, rfl⟩; exact hXRb v hx
    rcases hdec x (hRbR hx) hxX with h' | h' | h'
    exacts [Or.inl h', Or.inr (Or.inl h'), Or.inr (Or.inr h')]
  have hdis' : Disjoint R₁ (R₂ ∪ Y) := disjoint_union_right.mpr
    ⟨hdis, disjoint_left.mpr fun x hx hxY => hxY.1.2 (subset_closure hx)⟩
  have := (hpc Rb hRbreg).subset_left_of_subset_union hR₁o (hR₂o.union hYo) hdis' hsub
    ⟨y₁, hy₁Rb, hy₁R₁⟩
  exact disjoint_left.mp hdis (this hy₂Rb) hy₂R₂

end Gen

end HPC.Moore
