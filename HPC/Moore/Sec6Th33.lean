import HPC.Moore.Sec6Th32

/-!
# Moore, F.A. (1916), §6: Theorems 33 and 34 (batch 138, item B)

**Theorem 33.** If `A` is on the boundary of a region `R`, `B` is in `R`, and `AB` is an arc with
`AB − A` in `R`, then `R − (AB − A)` is connected. (Printed \"`R − AB − A)`\".)

**Theorem 34.** If `J` is a closed curve and `AB` is an arc lying wholly in `R`, the interior of
`J`, then `R − AB` is connected. (Printed \"If `J` is a Jordan arc\".) The general form, for any
region `R`, is `fa_theorem34_region`.

Moore gives two proofs. The first (pp. 148–150, for regions bounded by closed curves) is not
needed: the second, \"a modification of a proof due to Mr. J. R. Kline\" (p. 150, for any region),
is formalized here, and gives the closed-curve case as a special case.

Kline's proof: for `C`, `D` in `R − AB`, an arc `CA` (here `CB`) in `R`; its first point `X` on `AB`;
\"By Theorems 31 and 32, some point `F` on `XA` can be joined to `A` by an arc `AF` such that
`AF − A` is a subset of `(R + B) − AB`\" (`reach_end`: the arc from `C` to `X` itself lies in the
component of `R − AB` that `accessible` reaches the end from); then the same for `D` and the arc
`CAB`. In Theorem 34 the first point of the arc from `D` on `CAB` may be `B`, an end of `CAB`
(Kline's argument does not cover this); then `C` and `D` are the ends of an arc
`C … A B … D` and are joined by `joinZ`.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-- From a point `P` of `O − AB`, an arc in `O` reaching `AB` but not `A`, and `AB − A ⊆ O`: an arc
from `P` to `B` in `O` meeting `AB` only in `B` (Kline's step, by Theorems 31 and 32).
*Axioms used: 1–8.* -/
theorem reach_end (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {f : unitInterval → S}
    (hf : @IsEmbedding _ _ _ σ.topology f) {O : Set S} (hO : @IsOpen S σ.topology O)
    (hfO : ∀ u ∈ Ioo 0 1, f u ∈ O) (hf1 : f 1 ∈ O) {P Y : S} (hP : P ∈ O \ range f)
    {Γ : Set S} (hΓ : @TArc S σ.topology P Y Γ) (hΓO : Γ ⊆ O) (hY : Y ∈ range f)
    (hf0 : f 0 ∉ Γ) :
    ∃ τ, @TArc S σ.topology P (f 1) τ ∧ τ ⊆ O ∧ τ ∩ range f = {f 1} := by
  letI := σ.topology
  haveI := t2Space h1
  have hKc : IsClosed (range f) := (isCompact_range hf.continuous).isClosed
  obtain ⟨X, hXK, Γ', hΓ'Γ, hΓ', hΓ'K⟩ := hΓ.first_point hKc ⟨Y, hΓ.right_mem, hY⟩ hP.2
  obtain ⟨w, rfl⟩ := hXK
  have hw0 : w ≠ 0 := by
    rintro rfl; exact hf0 (hΓ'Γ hΓ'.right_mem)
  by_cases hw1 : w = 1
  · subst hw1; exact ⟨Γ', hΓ', hΓ'Γ.trans hΓO, hΓ'K⟩
  have hw : w ∈ Ioo 0 1 := ⟨lt_of_le_of_ne nonneg' (Ne.symm hw0), lt_of_le_of_ne le_one' hw1⟩
  have hsub : Γ' \ {f w} ⊆ O \ range f := by
    intro x hx
    refine ⟨hΓO (hΓ'Γ hx.1), fun h => hx.2 ?_⟩
    have : x ∈ Γ' ∩ range f := ⟨hx.1, h⟩
    rwa [hΓ'K] at this
  have hPw : P ≠ f w := fun e => hP.2 (e ▸ mem_range_self w)
  have hQ : Γ' \ {f w} ⊆ connectedComponentIn (O \ range f) P :=
    hΓ'.isPreconnected_diff_right.subset_connectedComponentIn ⟨hΓ'.left_mem, hPw⟩ hsub
  obtain ⟨τ, hτ, hτQ⟩ := accessible h1 h2 h3 h4 h5 h6 h7 h8 hf hO (t₀ := 0) (zero_lt_one' _)
    hfO hP ⟨w, hw, closure_mono hQ hΓ'.mem_closure_diff_right⟩
  refine ⟨τ, hτ, fun x hx => ?_, ?_⟩
  · rcases hτQ hx with rfl | h
    · exact hf1
    · exact (connectedComponentIn_subset _ _ h).1
  · ext x
    constructor
    · rintro ⟨hx, hxK⟩
      rcases hτQ hx with rfl | h
      · rfl
      · exact absurd hxK (connectedComponentIn_subset _ _ h).2
    · rintro rfl
      exact ⟨hτ.right_mem, mem_range_self 1⟩

/-- `reach_end` with both ends of `AB` in `O`: an arc from `P` to one of the ends, meeting `AB` only
there. *Axioms used: 1–8.* -/
theorem reach_end' (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {f : unitInterval → S}
    (hf : @IsEmbedding _ _ _ σ.topology f) {O : Set S} (hO : @IsOpen S σ.topology O)
    (hfO : ∀ u ∈ Ioo 0 1, f u ∈ O) (hf1 : f 1 ∈ O) {P Y : S} (hP : P ∈ O \ range f)
    {Γ : Set S} (hΓ : @TArc S σ.topology P Y Γ) (hΓO : Γ ⊆ O) (hY : Y ∈ range f) :
    ∃ E τ, (E = f 0 ∨ E = f 1) ∧ @TArc S σ.topology P E τ ∧ τ ⊆ O ∧ τ ∩ range f = {E} := by
  letI := σ.topology
  haveI := t2Space h1
  have hKc : IsClosed (range f) := (isCompact_range hf.continuous).isClosed
  obtain ⟨X, hXK, Γ', hΓ'Γ, hΓ', hΓ'K⟩ := hΓ.first_point hKc ⟨Y, hΓ.right_mem, hY⟩ hP.2
  by_cases hX0 : X = f 0
  · exact ⟨X, Γ', Or.inl hX0, hΓ', hΓ'Γ.trans hΓO, hΓ'K⟩
  obtain ⟨τ, hτ, hτO, hτK⟩ := reach_end h1 h2 h3 h4 h5 h6 h7 h8 hf hO hfO hf1 hP hΓ'
    (hΓ'Γ.trans hΓO) hXK (fun h => hX0 (by
      have : f 0 ∈ Γ' ∩ range f := ⟨h, mem_range_self 0⟩
      rw [hΓ'K] at this; exact this.symm))
  exact ⟨f 1, τ, Or.inr rfl, hτ, hτO, hτK⟩

/-- If `M` is an arc in the open set `R` from `P` to `P' ∉ K`, containing `K`, and `P` is joined in
`R − K` to a point `Y` of `M` other than `P` and `P'`, then `P` and `P'` lie in a connected subset of
`R − K` (`sides` at `Y` and `accessible` towards `P'`). *Axioms used: 1–8.* -/
theorem joinZ (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {R : Set S}
    (hRo : @IsOpen S σ.topology R) {K M : Set S} {P P' Y : S} (hM : @TArc S σ.topology P P' M)
    (hMR : M ⊆ R) (hKM : K ⊆ M) (hP'K : P' ∉ K) (hY : Y ∈ M) (hYP : Y ≠ P) (hYP' : Y ≠ P')
    {Sy : Set S} (hSy : @IsPreconnected S σ.topology Sy) (hSyR : Sy ⊆ R \ K) (hPS : P ∈ Sy)
    (hYS : Y ∈ Sy) : ∃ T ⊆ R \ K, P ∈ T ∧ P' ∈ T ∧ @IsPreconnected S σ.topology T := by
  letI := σ.topology
  haveI := t2Space h1
  obtain ⟨-, m, hm, rfl, rfl, rfl⟩ := hM
  obtain ⟨y, rfl⟩ := hY
  have hy0 : 0 < y := lt_of_le_of_ne nonneg' fun e => hYP (by rw [← e])
  have hy1 : y < 1 := lt_of_le_of_ne le_one' fun e => hYP' (by rw [e])
  obtain ⟨e, s, hey, hys, N, I₁, I₂, -, hNR, -, -, hI₁N, -, -, -, hI₁c, -, hI₁K, -, hcl⟩ :=
    sides h1 h2 h3 h4 h5 h6 h7 h8 hm hy0 hy1 hRo (hMR (mem_range_self y))
  have hycl := (hcl y ⟨hey.le, hys.le⟩).1
  obtain ⟨x, -, hx⟩ := mem_closure_iff_nhds.mp hycl univ Filter.univ_mem
  have hI₁R : I₁ ⊆ R \ range m := fun z hz => ⟨hNR (hI₁N hz), disjoint_left.mp hI₁K hz⟩
  have hI₁Q : I₁ ⊆ connectedComponentIn (R \ range m) x :=
    hI₁c.subset_connectedComponentIn hx hI₁R
  obtain ⟨τ, hτ, hτQ⟩ := accessible h1 h2 h3 h4 h5 h6 h7 h8 hm hRo (t₀ := 0) (zero_lt_one' _)
    (fun u _ => hMR (mem_range_self u)) (hI₁R hx) ⟨y, ⟨hy0, hy1⟩, closure_mono hI₁Q hycl⟩
  have hA : IsPreconnected (insert (m y) I₁) :=
    hI₁c.subset_closure (subset_insert _ _) (insert_subset hycl subset_closure)
  refine ⟨Sy ∪ (insert (m y) I₁ ∪ τ), ?_, Or.inl hPS, Or.inr (Or.inr hτ.right_mem), ?_⟩
  · rintro z (hz | (hz | hz) | hz)
    · exact hSyR hz
    · rw [hz]; exact hSyR hYS
    · exact ⟨(hI₁R hz).1, fun h => (hI₁R hz).2 (hKM h)⟩
    · rcases hτQ hz with rfl | h
      · exact ⟨hMR (mem_range_self 1), hP'K⟩
      · have := connectedComponentIn_subset _ _ h
        exact ⟨this.1, fun h' => this.2 (hKM h')⟩
  · exact hSy.union (m y) hYS (Or.inl (mem_insert _ _))
      (hA.union x (mem_insert_of_mem _ hx) hτ.left_mem hτ.isPreconnected)

/-- **Theorem 33.** If `A` is on the boundary of a region `R`, `B ∈ R`, and `AB` is an arc with
`AB − A ⊆ R`, then `R − (AB − A)` is connected. *Axioms used: 1–8.* Kline's proof (Moore p. 150),
via Theorems 31 and 32 (`reach_end`). **Shape change:** the axioms are made explicit. -/
theorem fa_theorem33 (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {R : Set S}
    (hR : R ∈ σ.region) {A B : S} (hA : A ∈ σ.bdry R) (hB : B ∈ R) {K : Set S}
    (hK : σ.IsArc A B K) (hKR : K \ {A} ⊆ R) : σ.IsConn (R \ (K \ {A})) := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have hRo := isOpen_region hR
  have hRc := hpc_region h1 h2 R hR
  have harc := arcConn h1 h3 h4 h51 h2
  have hAR : A ∉ R := notMem_of_mem_frontier hRo (by rwa [← bdry_eq_frontier h1])
  have heq : R \ (K \ {A}) = R \ K := by
    ext x
    simp only [mem_diff, mem_singleton_iff, not_and, not_not]
    constructor
    · rintro ⟨hx, h⟩; exact ⟨hx, fun hxK => hAR (h hxK ▸ hx)⟩
    · rintro ⟨hx, h⟩; exact ⟨hx, fun hxK => absurd hxK h⟩
  rw [isConn_iff h1, heq]
  rw [isArc_iff_tarc h1 h3 h4 h51] at hK
  obtain ⟨hAB, g, hg, rfl, rfl, rfl⟩ := hK
  have hKarc : TArc (g 0) (g 1) (range g) := ⟨hAB, g, hg, rfl, rfl, rfl⟩
  have hgO : ∀ u ∈ Ioo 0 1, g u ∈ R := fun u hu =>
    hKR ⟨mem_range_self u, fun e => hu.1.ne' (hg.injective e)⟩
  have step1 : ∀ P ∈ R \ range g, ∃ Γ, TArc P (g 1) Γ ∧ Γ ⊆ R ∧ Γ ∩ range g = {g 1} := by
    intro P hP
    obtain ⟨Γ₀, hΓ₀R, hΓ₀⟩ := harc R hRo hRc P hP.1 (g 1) hB
      (fun e => hP.2 (e ▸ mem_range_self 1))
    exact reach_end h1 h2 h3 h4 h5 h6 h7 h8 hg hRo hgO hB hP hΓ₀ hΓ₀R (mem_range_self 1)
      (fun h => hAR (hΓ₀R h))
  refine isPreconnected_of_forall_pair fun P hP P' hP' => ?_
  obtain ⟨Γ, hΓ, hΓR, hΓK⟩ := step1 P hP
  have hPB : P ≠ g 1 := fun e => hP.2 (e ▸ mem_range_self 1)
  by_cases hP'Γ : P' ∈ Γ
  · refine ⟨Γ \ {g 1}, fun x hx => ⟨hΓR hx.1, fun h => hx.2 ?_⟩, ⟨hΓ.left_mem, hPB⟩,
      ⟨hP'Γ, fun e => hP'.2 (e ▸ mem_range_self 1)⟩, hΓ.isPreconnected_diff_right⟩
    have : x ∈ Γ ∩ range g := ⟨hx.1, h⟩
    rwa [hΓK] at this
  have hK'' : TArc P (g 0) (Γ ∪ range g) := hΓ.union hKarc.symm hΓK
  obtain ⟨-, φ, hφ, hφr, hφ0, hφ1⟩ := hK''.symm
  have hφO : ∀ u ∈ Ioo 0 1, φ u ∈ R := by
    intro u hu
    have hu' : φ u ∈ Γ ∪ range g := hφr ▸ mem_range_self u
    have hne : φ u ≠ g 0 := fun e => hu.1.ne' (hφ.injective (e.trans hφ0.symm))
    rcases hu' with h | h
    · exact hΓR h
    · exact hKR ⟨h, hne⟩
  have hP'φ : P' ∈ R \ range φ := ⟨hP'.1, by rw [hφr]; rintro (h | h); exacts [hP'Γ h, hP'.2 h]⟩
  have hPP' : P' ≠ P := fun e => hP'Γ (e ▸ hΓ.left_mem)
  obtain ⟨Γ₀, hΓ₀R, hΓ₀⟩ := harc R hRo hRc P' hP'.1 P hP.1 hPP'
  obtain ⟨τ, hτ, hτR, hτK⟩ := reach_end h1 h2 h3 h4 h5 h6 h7 h8 hφ hRo hφO (hφ1 ▸ hP.1) hP'φ
    hΓ₀ hΓ₀R (hφ1 ▸ mem_range_self 1) (by rw [hφ0]; exact fun h => hAR (hΓ₀R h))
  rw [hφ1] at hτ hτK
  refine ⟨τ, fun x hx => ⟨hτR hx, fun h => hP.2 ?_⟩, hτ.right_mem, hτ.left_mem, hτ.isPreconnected⟩
  have : x ∈ τ ∩ range φ := ⟨hx, hφr ▸ Or.inr h⟩
  rw [hτK] at this
  exact this ▸ h

/-- **Theorem 34, for any region** (the form of Moore's second proof): if `AB` is an arc in a region
`R`, then `R − AB` is connected. *Axioms used: 1–8.* Kline's proof (Moore p. 150), with the case
the first point of `DC` on `CAB` is `B` supplied (`joinZ`). -/
theorem fa_theorem34_region (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {R : Set S}
    (hR : R ∈ σ.region) {A B : S} {K : Set S} (hK : σ.IsArc A B K) (hKR : K ⊆ R) :
    σ.IsConn (R \ K) := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have hRo := isOpen_region hR
  have hRc := hpc_region h1 h2 R hR
  have harc := arcConn h1 h3 h4 h51 h2
  rw [isConn_iff h1]
  rw [isArc_iff_tarc h1 h3 h4 h51] at hK
  obtain ⟨hAB, g, hg, rfl, rfl, rfl⟩ := hK
  have hKarc : TArc (g 0) (g 1) (range g) := ⟨hAB, g, hg, rfl, rfl, rfl⟩
  have hgO : ∀ u ∈ Ioo 0 1, g u ∈ R := fun u _ => hKR (mem_range_self u)
  have step1 : ∀ P ∈ R \ range g, ∃ E Γ, (E = g 0 ∨ E = g 1) ∧ TArc P E Γ ∧ Γ ⊆ R ∧
      Γ ∩ range g = {E} := by
    intro P hP
    obtain ⟨Γ₀, hΓ₀R, hΓ₀⟩ := harc R hRo hRc P hP.1 (g 1) (hKR (mem_range_self 1))
      (fun e => hP.2 (e ▸ mem_range_self 1))
    exact reach_end' h1 h2 h3 h4 h5 h6 h7 h8 hg hRo hgO (hKR (mem_range_self 1)) hP hΓ₀ hΓ₀R
      (mem_range_self 1)
  refine isPreconnected_of_forall_pair fun P hP P' hP' => ?_
  obtain ⟨E, Γ, hE, hΓ, hΓR, hΓK⟩ := step1 P hP
  have hEK : E ∈ range g := by rcases hE with rfl | rfl <;> exact mem_range_self _
  have hPE : P ≠ E := fun e => hP.2 (e ▸ hEK)
  have hΓK' : Γ \ {E} ⊆ R \ range g := fun x hx => ⟨hΓR hx.1, fun h => hx.2 (by
    have : x ∈ Γ ∩ range g := ⟨hx.1, h⟩
    rwa [hΓK] at this)⟩
  by_cases hP'Γ : P' ∈ Γ
  · exact ⟨Γ \ {E}, hΓK', ⟨hΓ.left_mem, hPE⟩, ⟨hP'Γ, fun e => hP'.2 (e ▸ hEK)⟩,
      hΓ.isPreconnected_diff_right⟩
  obtain ⟨E', hKE⟩ : ∃ E', TArc E E' (range g) := by
    rcases hE with rfl | rfl
    · exact ⟨g 1, hKarc⟩
    · exact ⟨g 0, hKarc.symm⟩
  have hK'' : TArc P E' (Γ ∪ range g) := hΓ.union hKE hΓK
  obtain ⟨φ, hφ, hφr, hφ0, hφ1⟩ := hK''.2
  have hφR : range φ ⊆ R := hφr ▸ union_subset hΓR hKR
  have hP'φ : P' ∉ range φ := by rw [hφr]; rintro (h | h); exacts [hP'Γ h, hP'.2 h]
  have hPP' : P' ≠ P := fun e => hP'Γ (e ▸ hΓ.left_mem)
  obtain ⟨Γ₀, hΓ₀R, hΓ₀⟩ := harc R hRo hRc P' hP'.1 P hP.1 hPP'
  obtain ⟨E'', τ, hE'', hτ, hτR, hτK⟩ := reach_end' h1 h2 h3 h4 h5 h6 h7 h8 hφ hRo
    (fun u _ => hφR (mem_range_self u)) (hφR (mem_range_self 1)) ⟨hP'.1, hP'φ⟩ hΓ₀ hΓ₀R
    (hφ0 ▸ mem_range_self 0)
  have hgφ : range g ⊆ range φ := hφr ▸ subset_union_right
  rcases hE'' with rfl | rfl
  · -- the arc from `P'` reaches `P`
    rw [hφ0] at hτ hτK
    refine ⟨τ, fun x hx => ⟨hτR hx, fun h => hP.2 ?_⟩, hτ.right_mem, hτ.left_mem,
      hτ.isPreconnected⟩
    have : x ∈ τ ∩ range φ := ⟨hx, hgφ h⟩
    rw [hτK] at this
    exact this ▸ h
  · -- the arc from `P'` reaches `E'`: `P` and `P'` are the ends of an arc through `AB`
    rw [hφ1] at hτ hτK
    have hM : TArc P P' ((Γ ∪ range g) ∪ τ) := hK''.union hτ.symm (by
      rw [inter_comm, ← hφr]; exact hτK)
    obtain ⟨Y, hYΓ, hYPE⟩ := hΓ.nonempty_diff
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hYPE
    exact joinZ h1 h2 h3 h4 h5 h6 h7 h8 hRo (K := range g) hM
      (union_subset (union_subset hΓR hKR) hτR) (subset_union_right.trans subset_union_left)
      hP'.2 (Or.inl (Or.inl hYΓ)) hYPE.1 (fun e => hP'Γ (e ▸ hYΓ))
      hΓ.isPreconnected_diff_right hΓK' ⟨hΓ.left_mem, hPE⟩ ⟨hYΓ, hYPE.2⟩

/-- **Theorem 34.** If `J` is a closed curve and `AB` is an arc lying wholly in `R`, the interior of
`J`, then `R − AB` is connected. *Axioms used: 1–8.* **Check 6:** printed \"If `J` is a Jordan
arc\"; since `R` is \"the interior of `J`\", this is a misprint for closed curve. The statement is
the special case of `fa_theorem34_region` (the interior of `J` is a region); Moore's first proof
(for this case) is not needed. **Shape change:** the axioms are made explicit. -/
theorem fa_theorem34 (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {J R : Set S}
    (hR : σ.IsInteriorOf J R) {A B : S} {K : Set S} (hK : σ.IsArc A B K) (hKR : K ⊆ R) :
    σ.IsConn (R \ K) :=
  fa_theorem34_region h1 h2 h3 h4 h5 h6 h7 h8 hR.2.1 hK hKR

end HPC.Moore
