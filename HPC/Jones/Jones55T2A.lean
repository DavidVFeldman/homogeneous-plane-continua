import HPC.Jones.Jones55
import HPC.Moore.M25C

/-!
# Batch 148, items A–C: Jones 1949 Theorem 1 as a statement; the Jordan curve theorem; Borsuk
# invariance and countability

Part of the batch-148 skeleton (`doc/batches/skeletons/Jones55T2-batch148.lean`), split under
`HPC/Jones/`; the statements are verbatim. Collected in `HPC/Jones/Jones55T2.lean`.

* **A.** `Jones49Thm1` (with nondegeneracy) and `not_jones49_theorem1_point`: the printed form fails
  for a one-point continuum. Whyburn, *Analytic Topology* (1942), Ch. I §10, p. 15: "A compact
  connected set will be called a continuum", and §8, p. 13, makes a single point connected; so in
  Whyburn's convention (Jones's footnote 3) one-point sets are continua and the printed form is not
  harmless.
* **B.** `jordan_curve_theorem`: `m25_theorem11` for the decomposition into points (`ptSetoid`,
  batch 146), with `isSCCElt_iff_tscc` (batch 147) and the decomposition of `Circle` into two
  half-circles (`tscc_circle`).
* **C.** `separatesPlane_of_homeomorph` (from `borsuk_exists_log` and
  `no_log_pow_of_bounded_component`, batch 146) and `countable_of_pairwiseDisjoint_open`.
-/

namespace HPC.Jones

open Set Topology Metric HPC.Plane HPC.Moore

/-! ## Jones 1949 Theorem 1, as a statement -/

/-- **Jones 1949, Theorem 1** (p. 113): "If a compact, plane continuum `M` is both homogeneous and
aposyndetic, then `M` is a simple closed curve." With `M` nondegenerate (see
`not_jones49_theorem1_point`). -/
def Jones49Thm1 : Prop :=
  ∀ K : Set Pt, IsCompact K → IsConnected K → K.Nontrivial → IsHomogeneous K → IsAposyndetic K →
    Nonempty (K ≃ₜ Circle)

/-- A subsingleton space is homogeneous. -/
theorem isHomogeneous_of_subsingleton {Y : Type*} [TopologicalSpace Y] [Subsingleton Y] :
    IsHomogeneous Y := fun x y => ⟨Homeomorph.refl Y, Subsingleton.elim x y⟩

/-- A subsingleton metric space is (vacuously) aposyndetic. -/
theorem isAposyndetic_of_subsingleton {Y : Type*} [MetricSpace Y] [Subsingleton Y] :
    IsAposyndetic Y := fun x y hxy => absurd (Subsingleton.elim x y) hxy

/-- The circle is not homeomorphic to a subsingleton. -/
theorem not_homeomorph_circle_of_subsingleton {Y : Type*} [TopologicalSpace Y] [Subsingleton Y]
    (e : Y ≃ₜ Circle) : False := by
  have hne : Circle.exp Real.pi ≠ 1 := by
    rw [Ne, Circle.exp_eq_one]
    rintro ⟨n, hn⟩
    have h1 : (1 : ℝ) = 2 * n := by
      have := Real.pi_pos
      field_simp at hn
      linarith
    have h2 : (1 : ℤ) = 2 * n := by exact_mod_cast h1
    omega
  exact hne (e.symm.injective (Subsingleton.elim _ _))

/-- Jones 1949 Theorem 1 **as printed** is false for a one-point continuum (vacuously homogeneous and
aposyndetic, not a simple closed curve) — unless "continuum" excludes points in the convention of
the books Jones's footnote 3 refers to (Moore 1932, Whyburn 1942). Record the convention.

*Convention recorded:* Whyburn 1942, Ch. I §10 (p. 15): "A compact connected set will be called a
continuum"; by §8 (p. 13) a one-point set is connected. One-point sets are continua there, and the
printed form is false as stated. -/
theorem not_jones49_theorem1_point :
    ¬ ∀ K : Set Pt, IsCompact K → IsConnected K → IsHomogeneous K → IsAposyndetic K →
      Nonempty (K ≃ₜ Circle) := by
  intro h
  obtain ⟨e⟩ := h {0} isCompact_singleton isConnected_singleton isHomogeneous_of_subsingleton
    isAposyndetic_of_subsingleton
  exact not_homeomorph_circle_of_subsingleton e

/-! ## The circle is two arcs with common end points -/

/-- The half-circle `t ↦ exp (s π t)` (`s = ±1`). -/
noncomputable def halfC (s : ℝ) : unitInterval → Circle := fun t => Circle.exp (s * Real.pi * t)

theorem continuous_halfC (s : ℝ) : Continuous (halfC s) :=
  Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)

theorem halfC_eq_iff {s s' : ℝ} {t t' : unitInterval} :
    halfC s t = halfC s' t' ↔
      ∃ m : ℤ, s * Real.pi * t = s' * Real.pi * t' + m * (2 * Real.pi) :=
  Circle.exp_eq_exp

theorem int_eq_zero_of_abs_lt {m : ℤ} {x : ℝ} (h : x = m * (2 * Real.pi))
    (hx : |x| < 2 * Real.pi) : m = 0 := by
  have hpi := Real.pi_pos
  subst h
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hx
  have : |(m : ℝ)| < 1 := by
    by_contra hc; push_neg at hc; nlinarith
  have : |m| < 1 := by exact_mod_cast this
  rw [abs_lt] at this
  omega

theorem injective_halfC {s : ℝ} (hs : s = 1 ∨ s = -1) : Function.Injective (halfC s) := by
  intro t t' h
  obtain ⟨m, hm⟩ := halfC_eq_iff.1 h
  have hpi := Real.pi_pos
  have ht := t.2; have ht' := t'.2
  simp only [Set.mem_Icc] at ht ht'
  have h0 : m = 0 := by
    apply int_eq_zero_of_abs_lt (x := s * Real.pi * t - s * Real.pi * t') (by linarith)
    rw [abs_lt]
    rcases hs with rfl | rfl <;> constructor <;> nlinarith
  subst h0
  apply Subtype.ext
  simp at hm
  rcases hs with rfl | rfl
  · rcases hm with h | h
    · exact h
    · norm_num at h
  · rcases hm with h | h
    · exact h
    · norm_num at h

/-- `Circle` is a topological simple closed curve: the two half-circles from `1` to `-1`. -/
theorem tscc_circle : Gen.TSCC (univ : Set Circle) := by
  have hpi := Real.pi_pos
  have h1 := Gen.TArc.of_inj (continuous_halfC 1) (injective_halfC (Or.inl rfl))
  have h2 := Gen.TArc.of_inj (continuous_halfC (-1)) (injective_halfC (Or.inr rfl))
  have e0 : halfC (-1) 0 = halfC 1 0 := by simp [halfC]
  have e1 : halfC (-1) 1 = halfC 1 1 := by
    rw [halfC_eq_iff]; exact ⟨-1, by push_cast; ring⟩
  rw [e0, e1] at h2
  refine ⟨_, _, _, _, h1, h2, ?_, ?_⟩
  · ext z
    simp only [mem_inter_iff, mem_range, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨t, rfl⟩, ⟨t', ht'⟩⟩
      obtain ⟨m, hm⟩ := halfC_eq_iff.1 ht'
      have ht := t.2; have ht2 := t'.2
      simp only [Set.mem_Icc] at ht ht2
      have hm' : ((t' : ℝ) + t) = -2 * m := by nlinarith
      have hmr : (m : ℝ) ≤ 0 ∧ -1 ≤ (m : ℝ) := ⟨by linarith, by linarith⟩
      have : m = 0 ∨ m = -1 := by
        have a : m ≤ 0 := by exact_mod_cast hmr.1
        have b : -1 ≤ m := by exact_mod_cast hmr.2
        omega
      rcases this with rfl | rfl
      · left; congr 1; apply Subtype.ext; simp at hm'; show (t : ℝ) = 0; linarith
      · right; congr 1; apply Subtype.ext; simp at hm'; show (t : ℝ) = 1; linarith
    · rintro (rfl | rfl)
      · exact ⟨⟨0, rfl⟩, ⟨0, e0⟩⟩
      · exact ⟨⟨1, rfl⟩, ⟨1, e1⟩⟩
  · symm; refine eq_univ_of_forall fun z => ?_
    rw [← Circle.exp_arg z]
    have h1 := Complex.neg_pi_lt_arg (z : ℂ)
    have h2 := Complex.arg_le_pi (z : ℂ)
    by_cases h : 0 ≤ (z : ℂ).arg
    · left
      refine ⟨⟨(z : ℂ).arg / Real.pi, div_nonneg h hpi.le, (div_le_one hpi).2 h2⟩, ?_⟩
      simp only [halfC]; congr 1; field_simp
    · right
      push_neg at h
      refine ⟨⟨-(z : ℂ).arg / Real.pi, div_nonneg (by linarith) hpi.le,
        (div_le_one hpi).2 (by linarith)⟩, ?_⟩
      simp only [halfC]; congr 1; field_simp

/-- Topological arcs are carried to topological arcs by embeddings. -/
theorem tarc_image_embedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {g : X → Y} (hg : IsEmbedding g) {A B : X} {C : Set X} (h : Gen.TArc A B C) :
    Gen.TArc (g A) (g B) (g '' C) := by
  obtain ⟨hAB, f, hf, rfl, rfl, rfl⟩ := h
  exact ⟨fun e => hAB (hg.injective e), g ∘ f, hg.comp hf, range_comp g f, rfl, rfl⟩

/-- Topological simple closed curves are carried to topological simple closed curves by
embeddings. -/
theorem tscc_image_embedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {g : X → Y} (hg : IsEmbedding g) {J : Set X} (h : Gen.TSCC J) : Gen.TSCC (g '' J) := by
  obtain ⟨A, B, C₁, C₂, h₁, h₂, h12, rfl⟩ := h
  refine ⟨g A, g B, g '' C₁, g '' C₂, tarc_image_embedding hg h₁, tarc_image_embedding hg h₂, ?_,
    image_union g C₁ C₂⟩
  rw [← image_inter hg.injective, h12, image_pair]

/-! ## The Jordan curve theorem in the plane, from Moore 1925 Theorem 11 -/

/-- **The Jordan curve theorem**, from `m25_theorem11` for the decomposition into points and the
equivalence of `IsSCCElt` with topological circles (batch 147). Needed by Jones 1949 (Case 1, Case 2)
and convenient for the exposition.

*Import chain:* `m25_theorem11` (`HPC/Moore/M25B11.lean`, batch 146: Mullikin's Theorem 5 and
Moore 1925 Theorems 9, 10), `isSCCElt_iff_tscc` (`HPC/Moore/M25CInt.lean`, batch 147) and
`mooreDecomp_ptSetoid` (`HPC/Moore/M25BPts.lean`). Neither `m19_plane` nor `m25_theorem22` is
used. -/
theorem jordan_curve_theorem {J : Set Pt} (hJ : Nonempty (J ≃ₜ Circle)) :
    ∃ I E : Set Pt, IsOpen I ∧ IsConnected I ∧ IsOpen E ∧ IsConnected E ∧ Disjoint I E ∧
      I ∪ E = Jᶜ ∧ Bornology.IsBounded I ∧ ¬ Bornology.IsBounded E ∧ frontier I = J ∧
      frontier E = J := by
  obtain ⟨e⟩ := hJ
  have hG := mooreDecomp_ptSetoid
  set g : Circle → Quotient ptSetoid := fun z => ptHomeo (e.symm z : Pt) with hgdef
  have hg : IsEmbedding g :=
    ptHomeo.isEmbedding.comp (IsEmbedding.subtypeVal.comp e.symm.isEmbedding)
  have himg : g '' univ = ptHomeo '' J := by
    ext q
    simp only [mem_image, mem_univ, true_and, hgdef]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, (e.symm z).2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e ⟨x, hx⟩, by simp⟩
  have hscc : IsSCCElt (ptHomeo '' J) := by
    rw [isSCCElt_iff_tscc hG, ← himg]
    exact tscc_image_embedding hg tscc_circle
  obtain ⟨I, E, hIo, hIc, hEo, hEc, hIE, hIEu, hIb, hEb, hIf, hEf⟩ := m25_theorem11 hG hscc
  have hpre : ptHomeo ⁻¹' (ptHomeo '' J) = J := ptHomeo.preimage_image J
  refine ⟨ptHomeo ⁻¹' I, ptHomeo ⁻¹' E, hIo.preimage ptHomeo.continuous,
    (ptHomeo.isConnected_preimage).2 hIc, hEo.preimage ptHomeo.continuous,
    (ptHomeo.isConnected_preimage).2 hEc, hIE.preimage _, ?_, hIb, hEb, ?_, ?_⟩
  · rw [← preimage_union, hIEu, preimage_compl, hpre]
  · rw [← ptHomeo.preimage_frontier, hIf, hpre]
  · rw [← ptHomeo.preimage_frontier, hEf, hpre]

/-! ## Plane separation is a topological invariant of plane compacta -/

/-- **Borsuk-type invariance** ("Since each two elements of `G` are homeomorphic, it follows that if
one element of `G` were to separate `S`, then each of them would separate `S`"): for compact plane
sets, separating the plane depends only on the homeomorphism type.

*Proof:* if `A` separates, `z ↦ z − x` (with `x` in a bounded complementary component of `A`) has no
continuous logarithm on `A` (`no_log_pow_of_bounded_component`); transported to `B` it would have
one if `B` did not separate (`borsuk_exists_log`). -/
theorem separatesPlane_of_homeomorph {A B : Set Pt} (hA : IsCompact A) (hB : IsCompact B)
    (h : Nonempty (A ≃ₜ B)) (hsep : SeparatesPlane A) : SeparatesPlane B := by
  obtain ⟨φ⟩ := h
  intro hBc
  obtain ⟨x, hx, hb⟩ := exists_bounded_component_of_separates hA hsep
  classical
  set F : Pt → ℂ := fun z => if hz : z ∈ B then toCpx (φ.symm ⟨z, hz⟩ : Pt) - toCpx x else 1
    with hFdef
  have hF : ContinuousOn F B := by
    rw [continuousOn_iff_continuous_restrict]
    have : B.restrict F = fun z : B => toCpx (φ.symm z : Pt) - toCpx x := by
      ext ⟨z, hz⟩; simp [hFdef, hz]
    rw [this]
    exact (continuous_toCpx.comp (continuous_subtype_val.comp φ.symm.continuous)).sub
      continuous_const
  have hF0 : ∀ z ∈ B, F z ≠ 0 := by
    intro z hz
    simp only [hFdef, hz, dite_true]
    exact toCpx_sub_ne_zero (fun e => hx (e ▸ (φ.symm ⟨z, hz⟩).2))
  obtain ⟨g, hg, hge⟩ := borsuk_exists_log hB hBc hF hF0
  refine no_log_pow_of_bounded_component hA hx hb (a := 1) one_ne_zero (u := fun _ => 1)
    continuousOn_const (fun _ _ => one_ne_zero) ⟨fun z => if hz : z ∈ A then g (φ ⟨z, hz⟩) else 0,
    ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have : A.restrict (fun z => if hz : z ∈ A then g (φ ⟨z, hz⟩) else 0) =
        fun z : A => g (φ z : Pt) := by
      ext ⟨z, hz⟩; simp [hz]
    rw [this]
    exact hg.comp_continuous (continuous_subtype_val.comp φ.continuous) (fun z => (φ z).2)
  · intro z hz
    simp only [hz, dite_true, zpow_one, mul_one]
    rw [hge _ (φ ⟨z, hz⟩).2]
    simp [hFdef]

open Function in
/-- The plane does not contain uncountably many mutually exclusive nonempty open sets.

*Shape change:* `open Function in` is added before the statement, which is otherwise verbatim: the
notation `Disjoint on U` is not available without it (the skeleton's statement does not
elaborate). -/
theorem countable_of_pairwiseDisjoint_open {ι : Type*} {U : ι → Set Pt} (hU : ∀ i, IsOpen (U i))
    (hne : ∀ i, (U i).Nonempty) (hd : Pairwise (Disjoint on U)) : Countable ι := by
  have hpd : (univ : Set ι).PairwiseDisjoint U := fun i _ j _ hij => hd hij
  have : (univ : Set ι).Countable :=
    hpd.countable_of_isOpen (fun i _ => hU i) (fun i _ => hne i)
  exact countable_univ_iff.mp this

end HPC.Jones
