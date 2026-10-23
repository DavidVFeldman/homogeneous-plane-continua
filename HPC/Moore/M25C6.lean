import HPC.Moore.M25C20

/-!
# Batch 147, item F: Axioms 6 and 7 for the restricted regions, proved directly

Moore (p. 425): \"With the aid of results established in my paper *Concerning a set of postulates
for plane analysis situs* and the fact that every region in the restricted sense is the interior of a
simple closed curve it easily follows that Axiom 6 and 7 also hold true\". As the commission asks,
they are proved here directly, for `R` the interior of a closed curve `J`, `R̄` a restricted region and
`P ∈ R̄` an element of `J`:

* **Cross-cuts near `P`** (`exists_crosscut`). For a Moore region `V₀` about `P` and `D` the interior
  (or the exterior) of `J`: elements `a`, `b` of `J` and the two arcs `X`, `Y` of `J` between them,
  with `P` inside `X ⊆ V₀`, and an arc `c` from `a` to `b` in `V₀` lying, except for `a`, `b`, in
  `D`. The ingredients:
  - the arcs `J₁`, `J₂` of `J` from `P` (Theorem 10), cut near `P` (the role of Theorem 7: sub-arcs
    of `J` about `P`), so that `C₂`, the rest of `J`, is a connected closed set missing `P`;
  - points `a`, `b` on either side of `P`, accessible from `D` inside a small region `W`
    (`exists_access`: an arc from an element of `D` near `J`, cut at its first element on `J`);
  - their access arcs are joined in `D ∩ V₀` by Janiszewski's theorem (`quot_janiszewski`) for `J` and
    `frontier V₀ + C₂`, whose common part is `C₂`, connected.
* **Axiom 6**: `K` is the interior of `X + c`; it lies in `R` by Theorem 15, and in `V₀ ⊆ R̄` by
  Theorem 12. `K̄` is a restricted region about `P` in `V₀ − Y` (Theorem 19), so `J ∩ K̄ ⊆ X`, part of
  the boundary of `K`.
* **Axiom 7**: `L` is the interior of `X + c` for an exterior cross-cut `c`. By Theorem 18, either
  `Y − a − b` is in the exterior of `X + c`, and then `L` misses `J`, lies in the exterior of `J`
  (since `c − a − b` does); or `Y − a − b` is in `L ⊆ V₀`, which is excluded by choosing `V₀` to
  miss an element of `J`.

So Moore's step through Moore 1919 (and, for Σ₂, through the unproved equivalence of F.A. p. 163) is
not needed.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane Gen

variable {r : Setoid Pt}

section General

variable {T : Type*} [TopologicalSpace T]

/-- An embedded arc stays in an open set near its start. -/
theorem exists_Icc_subset_of_isOpen {f : unitInterval → T} (hf : Continuous f) {U : Set T}
    (hU : IsOpen U) (h0 : f 0 ∈ U) {s₀ : unitInterval} (hs₀ : 0 < s₀) :
    ∃ s : unitInterval, 0 < s ∧ s < s₀ ∧ f '' Icc 0 s ⊆ U := by
  have hmem : f ⁻¹' U ∈ 𝓝 (0 : unitInterval) := (hU.preimage hf).mem_nhds h0
  obtain ⟨u, hu, hsub⟩ := exists_Ico_subset_of_mem_nhds' hmem hs₀
  obtain ⟨s, hs0, hsu⟩ := exists_between hu.1
  exact ⟨s, hs0, hsu.trans_le hu.2, by
    rintro _ ⟨v, hv, rfl⟩; exact hsub ⟨hv.1, hv.2.trans_lt hsu⟩⟩

end General

section M25C6

variable (hG : MooreDecomp r)
include hG

/-- **Accessible elements.** Near any element `y` of the boundary `J` of an open set `D` there is an
element `a` of `J` reached from an element of `D` by an arc meeting `J` only in `a`. -/
theorem exists_access {J D N : Set (Quotient r)} (hDo : IsOpen D) (hfr : frontier D = J)
    (hN : IsOpen N) {y : Quotient r} (hyJ : y ∈ J) (hyN : y ∈ N) :
    ∃ a ∈ J ∩ N, ∃ z ∈ D, ∃ α ⊆ N, TArc z a α ∧ α ∩ J = {a} ∧ α \ {a} ⊆ D := by
  haveI := t2Space_quot hG
  obtain ⟨M, hM, hyM, hMN⟩ := exists_region_subset hG (hN.mem_nhds hyN)
  have hy : y ∈ frontier D := hfr ▸ hyJ
  obtain ⟨z, hzM, hzD⟩ := mem_closure_iff_nhds.1 (frontier_subset_closure hy) M (hM.1.mem_nhds hyM)
  have hyD : y ∉ D := notMem_of_mem_frontier hDo hy
  have hzJ : z ∉ J := fun h => notMem_of_mem_frontier hDo (hfr ▸ h) hzD
  obtain ⟨Λ, hΛM, hΛ⟩ := arcConn_quot hG M hM.1 hM.2.1.isPreconnected z hzM y hyM
    (fun h => hyD (h ▸ hzD))
  have hJc : IsClosed J := hfr ▸ isClosed_frontier
  obtain ⟨a, haJ, α, hαΛ, hα, hαJ⟩ := hΛ.first_point hJc ⟨y, hΛ.right_mem, hyJ⟩ hzJ
  have hαN : α ⊆ N := hαΛ.trans (hΛM.trans hMN)
  refine ⟨a, ⟨haJ, hαN hα.right_mem⟩, z, hzD, α, hαN, hα, hαJ, ?_⟩
  refine conn_sub_of_frontier hα.isPreconnected_diff_right ?_ ⟨z, ⟨hα.left_mem, ?_⟩, hzD⟩
  · rw [hfr, disjoint_left]
    rintro x ⟨hx, hxa⟩ hxJ
    have : x ∈ α ∩ J := ⟨hx, hxJ⟩
    rw [hαJ] at this; exact hxa this
  · rintro rfl; exact hzJ haJ

omit hG in
/-- A point of an arc from `P` (parametrized by `f`), other than `P`, the other end, and the far
part, lies on the near part. -/
theorem mem_near_part {P : Quotient r} {J₁ J₂ : Set (Quotient r)} {f : unitInterval → Quotient r}
    (hfr : range f = J₁) (hf0 : f 0 = P) (hP₂ : P ∈ J₂) {s : unitInterval} {a : Quotient r} (ha₁ : a ∈ J₁) (ha₂ : a ∉ J₂)
    (has : a ∉ f '' Icc s 1) : ∃ σ : unitInterval, 0 < σ ∧ σ < s ∧ f σ = a := by
  rw [← hfr] at ha₁
  obtain ⟨σ, rfl⟩ := ha₁
  refine ⟨σ, lt_of_le_of_ne unitInterval.nonneg' fun e => ha₂ (by rw [← e, hf0]; exact hP₂),
    lt_of_not_ge fun h => has ⟨σ, ⟨h, unitInterval.le_one'⟩, rfl⟩, rfl⟩

/-- **Cross-cuts near an element of a closed curve.** -/
theorem exists_crosscut {J D V₀ : Set (Quotient r)} (hJ : IsSCCElt J) (hDo : IsOpen D)
    (hDc : IsPreconnected D) (hfr : frontier D = J) {P : Quotient r} (hP : P ∈ J)
    (hV₀ : mooreRegion V₀) (hPV : P ∈ V₀) :
    ∃ a b : Quotient r, ∃ X Y c : Set (Quotient r), IsArcElt a b X ∧ IsArcElt a b Y ∧
      X ∩ Y = {a, b} ∧ X ∪ Y = J ∧ P ∈ X ∧ P ≠ a ∧ P ≠ b ∧ X ⊆ V₀ ∧ IsArcElt a b c ∧
      c \ {a, b} ⊆ D ∧ c ⊆ V₀ := by
  haveI := t2Space_quot hG
  haveI := locallyConnectedSpace_quot hG
  have hJc : IsClosed J := hJ.1
  have hDJ : ∀ x ∈ D, x ∉ J := fun x hx hxJ => notMem_of_mem_frontier hDo (hfr ▸ hxJ) hx
  -- the arcs `J₁`, `J₂` of `J` from `P`, cut near `P`
  obtain ⟨y₀, hy₀J, hy₀P⟩ := hJ.2.2.1.exists_ne P
  obtain ⟨J₁, J₂, h₁, h₂, hu, hi⟩ := m25_theorem10 hG hJ hP hy₀J hy₀P.symm
  obtain ⟨-, f₁, hf₁, hf₁r, hf₁0, hf₁1⟩ := (isArcElt_iff_tarc hG).1 h₁
  obtain ⟨-, f₂, hf₂, hf₂r, hf₂0, hf₂1⟩ := (isArcElt_iff_tarc hG).1 h₂
  have hP₁ : P ∈ J₁ := hf₁r ▸ hf₁0 ▸ mem_range_self 0
  have hP₂ : P ∈ J₂ := hf₂r ▸ hf₂0 ▸ mem_range_self 0
  have hi' : J₂ ∩ J₁ = {P, y₀} := by rw [inter_comm, hi]
  obtain ⟨s₁, hs₁0, hs₁1, hs₁V⟩ := exists_Icc_subset_of_isOpen hf₁.continuous hV₀.1
    (hf₁0 ▸ hPV) (zero_lt_one' unitInterval)
  obtain ⟨s₂, hs₂0, hs₂1, hs₂V⟩ := exists_Icc_subset_of_isOpen hf₂.continuous hV₀.1
    (hf₂0 ▸ hPV) (zero_lt_one' unitInterval)
  set C₂ := f₁ '' Icc s₁ 1 ∪ f₂ '' Icc s₂ 1 with hC₂def
  have hC₂c : IsClosed C₂ := ((isCompact_Icc.image hf₁.continuous).union
    (isCompact_Icc.image hf₂.continuous)).isClosed
  have hPC₂ : P ∉ C₂ := by
    rintro (⟨v, hv, hve⟩ | ⟨v, hv, hve⟩)
    · rw [← hf₁0] at hve; have := hf₁.injective hve; subst this
      exact absurd hv.1 (not_le.2 hs₁0)
    · rw [← hf₂0] at hve; have := hf₂.injective hve; subst this
      exact absurd hv.1 (not_le.2 hs₂0)
  have hC₂J : C₂ ⊆ J := by
    rintro _ (⟨v, -, rfl⟩ | ⟨v, -, rfl⟩)
    · exact hu ▸ Or.inl (hf₁r ▸ mem_range_self v)
    · exact hu ▸ Or.inr (hf₂r ▸ mem_range_self v)
  have hC₂conn : IsConnected C₂ := by
    refine ((isConnected_Icc hs₁1.le).image _ hf₁.continuous.continuousOn).union ?_
      ((isConnected_Icc hs₂1.le).image _ hf₂.continuous.continuousOn)
    refine ⟨y₀, ⟨1, ⟨hs₁1.le, le_rfl⟩, hf₁1⟩, ⟨1, ⟨hs₂1.le, le_rfl⟩, hf₂1⟩⟩
  have hJC₂ : J ∩ (frontier V₀ ∪ C₂) = C₂ := by
    apply subset_antisymm
    · rintro z ⟨hzJ, hz | hz⟩
      · have hzV : z ∉ V₀ := notMem_of_mem_frontier hV₀.1 hz
        rw [← hu] at hzJ
        rcases hzJ with hz1 | hz2
        · rw [← hf₁r] at hz1
          obtain ⟨v, rfl⟩ := hz1
          rcases le_total v s₁ with h | h
          · exact absurd (hs₁V ⟨v, ⟨unitInterval.nonneg', h⟩, rfl⟩) hzV
          · exact Or.inl ⟨v, ⟨h, unitInterval.le_one'⟩, rfl⟩
        · rw [← hf₂r] at hz2
          obtain ⟨v, rfl⟩ := hz2
          rcases le_total v s₂ with h | h
          · exact absurd (hs₂V ⟨v, ⟨unitInterval.nonneg', h⟩, rfl⟩) hzV
          · exact Or.inr ⟨v, ⟨h, unitInterval.le_one'⟩, rfl⟩
      · exact hz
    · intro z hz; exact ⟨hC₂J hz, Or.inr hz⟩
  -- the small region `W` about `P`
  obtain ⟨W, hW, hPW, hWsub⟩ :=
    exists_region_subset hG ((hV₀.1.sdiff hC₂c).mem_nhds ⟨hPV, hPC₂⟩)
  have hWV : W ⊆ V₀ := fun x hx => (hWsub hx).1
  -- an accessible element `a` on the near part of `J₁`
  have side : ∀ {Ja Jb : Set (Quotient r)} {f : unitInterval → Quotient r} {s : unitInterval},
      IsEmbedding f → range f = Ja → f 0 = P → f 1 = y₀ → Ja ∩ Jb = {P, y₀} → P ∈ Jb →
      IsClosed Jb → 0 < s → Ja ⊆ J → J ⊆ Ja ∪ Jb →
      ∃ a ∈ J, ∃ z ∈ D ∩ W, ∃ α ⊆ W, TArc z a α ∧ α ∩ J = {a} ∧ α \ {a} ⊆ D ∧
        ∃ σ : unitInterval, 0 < σ ∧ σ < s ∧ f σ = a := by
    intro Ja Jb f s hf hfr' hf0 hf1 hiab hPb hJbc hs hJaJ hJab
    obtain ⟨τ, hτ0, hτs, hτW⟩ := exists_Icc_subset_of_isOpen hf.continuous hW.1 (hf0 ▸ hPW) hs
    have hyN : f τ ∈ W \ (Jb ∪ f '' Icc s 1) := by
      refine ⟨hτW ⟨τ, ⟨unitInterval.nonneg', le_rfl⟩, rfl⟩, ?_⟩
      rintro (h | ⟨v, hv, hve⟩)
      · have : f τ ∈ Ja ∩ Jb := ⟨hfr' ▸ mem_range_self τ, h⟩
        rw [hiab] at this
        rcases this with h' | h'
        · rw [← hf0] at h'; exact hτ0.ne' (hf.injective h')
        · rw [mem_singleton_iff, ← hf1] at h'
          exact (hτs.trans_le unitInterval.le_one').ne (hf.injective h')
      · have := hf.injective hve; subst this; exact absurd hv.1 (not_le.2 hτs)
    have hNo : IsOpen (W \ (Jb ∪ f '' Icc s 1)) :=
      hW.1.sdiff (hJbc.union (isCompact_Icc.image hf.continuous).isClosed)
    obtain ⟨a, ⟨haJ, haN⟩, z, hzD, α, hαN, hα, hαJ, hαD⟩ :=
      exists_access hG hDo hfr hNo (hJaJ (hfr' ▸ mem_range_self τ)) hyN
    have haJa : a ∈ Ja := (hJab haJ).resolve_right fun h => haN.2 (Or.inl h)
    obtain ⟨σ, hσ0, hσs, hσa⟩ := mem_near_part hfr' hf0 hPb haJa
      (fun h => haN.2 (Or.inl h)) (fun h => haN.2 (Or.inr h))
    have hzW : z ∈ W := by
      by_contra hzW
      exact hzW ((hαN hα.left_mem).1)
    exact ⟨a, haJ, z, ⟨hzD, hzW⟩, α, fun x hx => (hαN hx).1, hα, hαJ, hαD, σ, hσ0, hσs, hσa⟩
  obtain ⟨a, haJ, z₁, ⟨hz₁D, hz₁W⟩, α₁, hα₁W, hα₁, hα₁J, hα₁D, σ₁, hσ₁0, hσ₁s, hσ₁a⟩ :=
    side hf₁ hf₁r hf₁0 hf₁1 hi hP₂ h₂.2.1 hs₁0 (hu ▸ subset_union_left) hu.symm.subset
  obtain ⟨b, hbJ, z₂, ⟨hz₂D, hz₂W⟩, α₂, hα₂W, hα₂, hα₂J, hα₂D, σ₂, hσ₂0, hσ₂s, hσ₂b⟩ :=
    side hf₂ hf₂r hf₂0 hf₂1 hi' hP₁ h₁.2.1 hs₂0 (hu ▸ subset_union_right)
      (by rw [union_comm]; exact hu.symm.subset)
  subst hσ₁a hσ₂b
  have hab : f₁ σ₁ ≠ f₂ σ₂ := by
    intro h
    have : f₁ σ₁ ∈ J₁ ∩ J₂ := ⟨hf₁r ▸ mem_range_self _, h ▸ hf₂r ▸ mem_range_self _⟩
    rw [hi] at this
    rcases this with h' | h'
    · rw [← hf₁0] at h'; exact hσ₁0.ne' (hf₁.injective h')
    · rw [mem_singleton_iff, ← hf₁1] at h'; exact (hσ₁s.trans hs₁1).ne (hf₁.injective h')
  -- the arc `X` of `J` through `P`
  have hXa : TArc (f₁ σ₁) P (f₁ '' Icc 0 σ₁) := by
    have := (TArc.image_Icc hf₁ hσ₁0).symm; rwa [hf₁0] at this
  have hXb : TArc P (f₂ σ₂) (f₂ '' Icc 0 σ₂) := by
    have := TArc.image_Icc hf₂ hσ₂0; rwa [hf₂0] at this
  have hXint : f₁ '' Icc 0 σ₁ ∩ f₂ '' Icc 0 σ₂ = {P} := by
    apply subset_antisymm
    · rintro z ⟨⟨u, hu', rfl⟩, ⟨v, -, hve⟩⟩
      have : f₁ u ∈ J₁ ∩ J₂ := ⟨hf₁r ▸ mem_range_self u, hve ▸ hf₂r ▸ mem_range_self v⟩
      rw [hi] at this
      rcases this with h' | h'
      · exact h'
      · rw [mem_singleton_iff, ← hf₁1] at h'
        have := hf₁.injective h'; subst this
        exact absurd hu'.2 (not_le.2 (hσ₁s.trans hs₁1))
    · rintro z rfl
      exact ⟨⟨0, ⟨le_rfl, hσ₁0.le⟩, hf₁0⟩, ⟨0, ⟨le_rfl, hσ₂0.le⟩, hf₂0⟩⟩
  set X := f₁ '' Icc 0 σ₁ ∪ f₂ '' Icc 0 σ₂ with hXdef
  have hX : TArc (f₁ σ₁) (f₂ σ₂) X := hXa.union hXb hXint
  have hXV : X ⊆ V₀ := by
    rintro _ (⟨u, hu', rfl⟩ | ⟨u, hu', rfl⟩)
    · exact hs₁V ⟨u, ⟨hu'.1, hu'.2.trans hσ₁s.le⟩, rfl⟩
    · exact hs₂V ⟨u, ⟨hu'.1, hu'.2.trans hσ₂s.le⟩, rfl⟩
  have hXJ : X ⊆ J := by
    rintro _ (⟨u, -, rfl⟩ | ⟨u, -, rfl⟩)
    · exact hu ▸ Or.inl (hf₁r ▸ mem_range_self u)
    · exact hu ▸ Or.inr (hf₂r ▸ mem_range_self u)
  have hPX : P ∈ X := Or.inl ⟨0, ⟨le_rfl, hσ₁0.le⟩, hf₁0⟩
  have hPa : P ≠ f₁ σ₁ := fun h => hσ₁0.ne (hf₁.injective (hf₁0.trans h))
  have hPb : P ≠ f₂ σ₂ := fun h => hσ₂0.ne (hf₂.injective (hf₂0.trans h))
  -- the other arc `Y` (Theorem 10)
  obtain ⟨Y₁, Y₂, hY₁, hY₂, hYu, hYi⟩ := m25_theorem10 hG hJ haJ hbJ hab
  obtain ⟨Y, hY, hXYi, hXYu⟩ : ∃ Y, IsArcElt (f₁ σ₁) (f₂ σ₂) Y ∧
      X ∩ Y = {f₁ σ₁, f₂ σ₂} ∧ X ∪ Y = J := by
    rcases TArc.eq_of_subset_union ((isArcElt_iff_tarc hG).1 hY₁) ((isArcElt_iff_tarc hG).1 hY₂)
      hYi (hXJ.trans hYu.symm.subset) hX with h | h
    · exact ⟨Y₂, hY₂, h ▸ hYi, h ▸ hYu⟩
    · exact ⟨Y₁, hY₁, by rw [h, inter_comm, hYi], by rw [h, union_comm, hYu]⟩
  -- Janiszewski: the access arcs are joined in `D ∩ V₀`
  have hBc : IsClosed (frontier V₀ ∪ C₂) := isClosed_frontier.union hC₂c
  have hBb : Bornology.IsBounded (ptsOf r (frontier V₀ ∪ C₂)) :=
    (isBounded_ptsOf_frontier hG hV₀.2.2.1).union (hJ.2.2.2.1.subset (ptsOf_mono hC₂J))
  have hWB : ∀ x ∈ W, x ∉ frontier V₀ ∪ C₂ := by
    rintro x hx (h | h)
    · exact notMem_of_mem_frontier hV₀.1 h (hWV hx)
    · exact (hWsub hx).2 h
  have hz₂K := quot_janiszewski hG hJc hJ.2.2.2.1 hBc hBb (Or.inl (by rw [hJC₂]; exact hC₂conn))
    (hDJ z₁ hz₁D) (hWB z₁ hz₁W) (hDJ z₂ hz₂D) (hWB z₂ hz₂W)
    (hDc.subset_connectedComponentIn hz₁D (fun x hx => hDJ x hx) hz₂D)
    (hW.2.1.isPreconnected.subset_connectedComponentIn hz₁W (fun x hx => hWB x hx) hz₂W)
  set K := connectedComponentIn (J ∪ (frontier V₀ ∪ C₂))ᶜ z₁ with hKdef
  have hz₁c : z₁ ∈ (J ∪ (frontier V₀ ∪ C₂))ᶜ := fun h => h.elim (hDJ z₁ hz₁D) (hWB z₁ hz₁W)
  have hz₁K : z₁ ∈ K := mem_connectedComponentIn hz₁c
  have hKo : IsOpen K := isOpen_connectedComponentIn_quot hG (hJc.union hBc).isOpen_compl z₁
  have hKsub : K ⊆ (J ∪ (frontier V₀ ∪ C₂))ᶜ := connectedComponentIn_subset _ _
  have hKD : K ⊆ D := by
    refine conn_sub_of_frontier isPreconnected_connectedComponentIn ?_ ⟨z₁, hz₁K, hz₁D⟩
    rw [hfr]; exact disjoint_left.2 fun x hx hxJ => hKsub hx (Or.inl hxJ)
  have hKV : K ⊆ V₀ := by
    refine conn_sub_of_frontier isPreconnected_connectedComponentIn ?_ ⟨z₁, hz₁K, hWV hz₁W⟩
    exact disjoint_left.2 fun x hx hxF => hKsub hx (Or.inr (Or.inl hxF))
  have haz₂ : f₁ σ₁ ≠ z₂ := fun h => hDJ z₂ hz₂D (h ▸ haJ)
  obtain ⟨T₁, hT₁, hT₁a⟩ : ∃ T₁ ⊆ α₁ ∪ K, TArc (f₁ σ₁) z₂ T₁ := by
    by_cases hz : z₁ = z₂
    · subst hz; exact ⟨α₁, subset_union_left, hα₁.symm⟩
    · obtain ⟨α₃, hα₃K, hα₃⟩ := arcConn_quot hG K hKo isPreconnected_connectedComponentIn z₁ hz₁K
        z₂ hz₂K hz
      obtain ⟨γ, hγ, hγa⟩ := hα₁.symm.join hα₃.symm ⟨z₁, hα₁.left_mem, hα₃.left_mem⟩ haz₂
      exact ⟨γ, hγ.trans (union_subset_union_right _ hα₃K), hγa⟩
  obtain ⟨c, hc, hca⟩ := hT₁a.join hα₂.symm ⟨z₂, hT₁a.right_mem, hα₂.left_mem⟩ hab
  refine ⟨f₁ σ₁, f₂ σ₂, X, Y, c, (isArcElt_iff_tarc hG).2 hX, hY, hXYi, hXYu, hPX, hPa, hPb, hXV,
    (isArcElt_iff_tarc hG).2 hca, ?_, ?_⟩
  · rintro x ⟨hxc, hxab⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hxab
    rcases hc hxc with hxT | hx2
    · rcases hT₁ hxT with hx1 | hxK
      · exact hα₁D ⟨hx1, hxab.1⟩
      · exact hKD hxK
    · exact hα₂D ⟨hx2, hxab.2⟩
  · intro x hxc
    rcases hc hxc with hxT | hx2
    · rcases hT₁ hxT with hx1 | hxK
      · exact hWV (hα₁W hx1)
      · exact hKV hxK
    · exact hWV (hα₂W hx2)

/-- The common setting of Axioms 6 and 7: a Moore region `V₀ ⊆ R̄` about `P` missing an element `y₀`
of `J` other than `P`. -/
theorem exists_V₀ {J R' : Set (Quotient r)} (hJ : IsSCCElt J) (hR'o : IsOpen R') {P : Quotient r}
    (hPR' : P ∈ R') :
    ∃ y₀ ∈ J, ∃ V₀, mooreRegion V₀ ∧ P ∈ V₀ ∧ V₀ ⊆ R' ∧ y₀ ∉ V₀ := by
  haveI := t2Space_quot hG
  obtain ⟨y₀, hy₀J, hy₀P⟩ := hJ.2.2.1.exists_ne P
  obtain ⟨V₀, hV₀, hPV₀, hV₀sub⟩ := exists_region_subset hG
    ((hR'o.sdiff isClosed_singleton).mem_nhds ⟨hPR', fun h => hy₀P (mem_singleton_iff.1 h).symm⟩)
  exact ⟨y₀, hy₀J, V₀, hV₀, hPV₀, fun x hx => (hV₀sub hx).1, fun h => (hV₀sub h).2 rfl⟩

/-- **Axiom 6** for the restricted regions, proved directly. -/
theorem m25r_axiom6 : (spaceRestricted r).Axiom6 := by
  rintro R ⟨J, hJ, rfl⟩ R' hR' P hPR' hPb
  rw [bdry_restricted hG, (sccInterior_spec hG hJ).2.2.2.1] at hPb
  obtain ⟨hIo, hIc, -, hfrI, -⟩ := sccInterior_spec hG hJ
  obtain ⟨-, -, V₀, hV₀, hPV₀, hV₀R', -⟩ := exists_V₀ hG hJ (isOpen_restricted hG R' hR') hPR'
  obtain ⟨a, b, X, Y, c, hX, hY, hXY, hXYJ, hPX, hPa, hPb', hXV, hc, hcD, hcV⟩ :=
    exists_crosscut hG hJ hIo hIc.isPreconnected hfrI hPb hV₀ hPV₀
  have hcR : c \ {a, b} ⊆ sccInterior (X ∪ Y) := hXYJ ▸ hcD
  obtain ⟨-, -, -, hK, -⟩ := setting_int hG hX hY hc hXY fun z hz => (hcR hz).1
  obtain ⟨hKR, -, -⟩ := m25_theorem15 hG hX hY hc hXY hcR
  have hKV : sccInterior (X ∪ c) ⊆ V₀ :=
    sccInterior_subset_of_subset hG hV₀ hK (union_subset hXV hcV)
  have hPY : P ∉ Y := fun h => by
    have : P ∈ X ∩ Y := ⟨hPX, h⟩
    rw [hXY] at this
    rcases this with h' | h'
    · exact hPa h'
    · exact hPb' h'
  obtain ⟨K', hK', hPK', hK'V⟩ := exists_restricted_subset hG
    ((hV₀.1.sdiff hY.2.1).mem_nhds ⟨hPV₀, hPY⟩)
  refine ⟨sccInterior (X ∪ c), ⟨_, hK, rfl⟩, K', hK', hKV.trans hV₀R',
    fun x hx => hV₀R' (hK'V hx).1, hPK', hXYJ ▸ hKR, ?_⟩
  rw [bdry_restricted hG, bdry_restricted hG, (sccInterior_spec hG hJ).2.2.2.1,
    (sccInterior_spec hG hK).2.2.2.1]
  rintro z ⟨hzJ, hzK'⟩
  rw [← hXYJ] at hzJ
  exact Or.inl (hzJ.resolve_right (hK'V hzK').2)

/-- **Axiom 7** for the restricted regions, proved directly. -/
theorem m25r_axiom7 : (spaceRestricted r).Axiom7 := by
  rintro R ⟨J, hJ, rfl⟩ R' hR' P hPR' hPb
  rw [bdry_restricted hG, (sccInterior_spec hG hJ).2.2.2.1] at hPb
  obtain ⟨hIo, -, -, -, hEo, hEc, -, hfrE, hdisJ, huJ⟩ := sccInterior_spec hG hJ
  obtain ⟨y₀, hy₀J, V₀, hV₀, hPV₀, hV₀R', hy₀V⟩ :=
    exists_V₀ hG hJ (isOpen_restricted hG R' hR') hPR'
  obtain ⟨a, b, X, Y, c, hX, hY, hXY, hXYJ, hPX, hPa, hPb', hXV, hc, hcD, hcV⟩ :=
    exists_crosscut hG hJ hEo hEc.isPreconnected hfrE hPb hV₀ hPV₀
  have hcE : c \ {a, b} ⊆ sccExterior (X ∪ Y) := hXYJ ▸ hcD
  obtain ⟨-, -, -, hL, hYc⟩ := setting_int hG hX hY hc hXY fun z hz => (hcE hz).1
  have hLV : sccInterior (X ∪ c) ⊆ V₀ :=
    sccInterior_subset_of_subset hG hV₀ hL (union_subset hXV hcV)
  have hPY : P ∉ Y := fun h => by
    have : P ∈ X ∩ Y := ⟨hPX, h⟩
    rw [hXY] at this
    rcases this with h' | h'
    · exact hPa h'
    · exact hPb' h'
  have hab : a ∈ X ∧ b ∈ X := ⟨hX.2.2.2.2.1, hX.2.2.2.2.2.1⟩
  -- the interior `L` of `X + c` lies in the exterior of `J`
  have h18 := m25_theorem18 hG hX hY hc hXY hcE
  have hYE : Y \ {a, b} ⊆ sccExterior (X ∪ c) := by
    refine h18.1.resolve_right fun hXE => ?_
    have hYX : Y ∩ X = {a, b} := by rw [inter_comm, hXY]
    have hcE' : c \ {a, b} ⊆ sccExterior (Y ∪ X) := by rw [union_comm]; exact hcE
    have h := ((m25_theorem18 hG hY hX hc hYX hcE').2 hXE).1
    have hy₀X : y₀ ∉ X := fun h => hy₀V (hXV h)
    have hy₀Y : y₀ ∈ Y \ {a, b} := by
      refine ⟨(hXYJ ▸ hy₀J : y₀ ∈ X ∪ Y).resolve_left hy₀X, ?_⟩
      rintro (h | h)
      · exact hy₀X (h ▸ hab.1)
      · exact hy₀X ((mem_singleton_iff.1 h) ▸ hab.2)
    exact hy₀V (hLV (h hy₀Y))
  obtain ⟨hLo, hLc, -, hfrL, -⟩ := sccInterior_spec hG hL
  have hLJ : sccInterior (X ∪ c) ⊆ sccInterior J ∪ sccExterior J := by
    rw [huJ, ← hXYJ]
    rintro z hz (hzX | hzY)
    · exact notMem_of_mem_frontier hLo (by rw [hfrL]; exact Or.inl hzX) hz
    · by_cases hzab : z ∈ ({a, b} : Set (Quotient r))
      · rcases hzab with rfl | h
        · exact notMem_of_mem_frontier hLo (by rw [hfrL]; exact Or.inl hab.1) hz
        · rw [mem_singleton_iff] at h; subst h
          exact notMem_of_mem_frontier hLo (by rw [hfrL]; exact Or.inl hab.2) hz
      · exact disjoint_left.1 (sccInterior_spec hG hL).2.2.2.2.2.2.2.2.1 hz (hYE ⟨hzY, hzab⟩)
  have hLsub : sccInterior (X ∪ c) ⊆ sccExterior J := by
    rcases hLc.isPreconnected.subset_or_subset hIo hEo hdisJ hLJ with h | h
    · exfalso
      obtain ⟨z, hz⟩ := ((isArcElt_iff_tarc hG).1 hc).nonempty_diff
      have hzcl : z ∈ closure (sccInterior (X ∪ c)) :=
        frontier_subset_closure (by rw [hfrL]; exact Or.inr hz.1)
      have := closure_mono h hzcl
      rw [closure_sccInterior hG hJ] at this
      have hzE := hcD hz
      rcases this with h' | h'
      · exact disjoint_left.1 hdisJ h' hzE
      · exact hzE.1 h'
    · exact h
  obtain ⟨L', hL', hPL', hL'V⟩ := exists_restricted_subset hG
    ((hV₀.1.sdiff hY.2.1).mem_nhds ⟨hPV₀, hPY⟩)
  refine ⟨sccInterior (X ∪ c), ⟨_, hL, rfl⟩, L', hL', hLV.trans hV₀R',
    fun x hx => hV₀R' (hL'V hx).1, hPL', ?_, ?_⟩
  · rw [Space.ext, cl_eq_closure_restricted hG, compl_closure_sccInterior hG hJ]; exact hLsub
  · rw [bdry_restricted hG, bdry_restricted hG, (sccInterior_spec hG hJ).2.2.2.1,
      (sccInterior_spec hG hL).2.2.2.1]
    rintro z ⟨hzJ, hzL'⟩
    rw [← hXYJ] at hzJ
    exact Or.inl (hzJ.resolve_right (hL'V hzL').2)

end M25C6

end HPC.Moore
