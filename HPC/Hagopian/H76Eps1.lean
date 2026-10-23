import HPC.Hagopian.Hagopian76E

/-!
# Batch 161, item T4: the elevenths of `E` and `ε₁`

Hagopian 1976, pp. 345–346: "Define `ε₁` to be one-third the minimum of the union of
`{ρ(Aᵢ, Bᵢ) : 1 ≤ i ≤ 5}`, `{ρ(E, π⁻¹(qᵢ)) : 1 ≤ i ≤ 5}`, `{ρ(k⁻¹(0) ∪ k⁻¹(1), k⁻¹[[1/11, 10/11]])}`"
and: "Note that if `h` is an `ε₁`-homeomorphism of `M` onto `M`, then the chain formed by taking
`ε₁`-neighborhoods in `R²` of the elements of `{k⁻¹[[(i − 1)/11, i/11]] : 1 ≤ i ≤ 11}` follows
`h[E]`."

* `piece k i` is the `i`-th eleventh `k⁻¹[[(i − 1)/11, i/11]]`, `middle k` is `k⁻¹[[1/11, 10/11]]`.
* `IsEps1 k ε₁` records the two families used by the later steps of this batch:
  * `sep`: non-adjacent elevenths are `4ε₁` apart. This family is **not** among Hagopian's four;
    it is what the chain sentence above needs (ledger check 161.2: the four printed families do not
    separate `k⁻¹[[0, 1/11]]` from `k⁻¹[[2/11, 3/11]]`);
  * `ends`: the third printed family, `ρ(k⁻¹(0) ∪ k⁻¹(1), k⁻¹[[1/11, 10/11]]) ≥ 3ε₁`.
  The families with `Aᵢ`, `qᵢ` live in the collar coordinates of T2–T8 and are not used here.
* `exists_isEps1`: such an `ε₁` exists (the elevenths are compact; finitely many pairs).
* `isEps1_thickening_disjoint`: the skeleton's form of T4.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Eps1

variable {M : Set Pt}

/-- The `i`-th eleventh of `E` (p. 345: `k⁻¹[[(i − 1)/11, i/11]]`). -/
def piece {E : Set M} (k : E → unitInterval) (i : ℕ) : Set M :=
  layerSet k {t | ((i : ℝ) - 1) / 11 ≤ (t : ℝ) ∧ (t : ℝ) ≤ (i : ℝ) / 11}

/-- The middle part `k⁻¹[[1/11, 10/11]]` of `E`. -/
def middle {E : Set M} (k : E → unitInterval) : Set M :=
  layerSet k {t | 1 / 11 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 10 / 11}

/-- **`ε₁`** (T4): the families of the minimum used in this batch (see the module docstring). -/
structure IsEps1 {E : Set M} (k : E → unitInterval) (ε₁ : ℝ) : Prop where
  pos : 0 < ε₁
  sep : ∀ i j : ℕ, i + 1 < j → j ≤ 11 → ∀ x ∈ piece k i, ∀ y ∈ piece k j, 4 * ε₁ ≤ dist x y
  ends : ∀ x ∈ layer k 0 ∪ layer k 1, ∀ y ∈ middle k, 3 * ε₁ ≤ dist x y

theorem isClosed_interval_set (a b : ℝ) :
    IsClosed {t : unitInterval | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b} :=
  (isClosed_le continuous_const continuous_subtype_val).inter
    (isClosed_le continuous_subtype_val continuous_const)

theorem isCompact_layerSet_interval {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) (a b : ℝ) :
    IsCompact (layerSet k {t : unitInterval | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b}) :=
  isCompact_img hE.isCompact hE.2.1.1 (isClosed_interval_set a b)

/-- A positive bound for finitely many conditions, each preserved by shrinking. -/
theorem exists_pos_forall_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) (P : ι → ℝ → Prop)
    (hmono : ∀ i a b, 0 < a → a ≤ b → P i b → P i a) (h : ∀ i ∈ s, ∃ δ > 0, P i δ) :
    ∃ δ > 0, ∀ i ∈ s, P i δ := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨δ, hδ, hs⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨δa, hδa, hPa⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨min δ δa, lt_min hδ hδa, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hmono _ _ _ (lt_min hδ hδa) (min_le_right _ _) hPa
    · exact hmono _ _ _ (lt_min hδ hδa) (min_le_left _ _) (hs i hi)

theorem piece_disjoint {E : Set M} (k : E → unitInterval) {i j : ℕ} (hij : i + 1 < j) :
    Disjoint (piece k i) (piece k j) := by
  rw [disjoint_left]
  rintro _ ⟨e, he, rfl⟩ ⟨e', he', hee'⟩
  have : e' = e := Subtype.val_injective hee'
  subst this
  have hc : (i : ℝ) + 2 ≤ j := by exact_mod_cast hij
  have h1 := he.2
  have h2 := he'.1
  have : ((j : ℝ) - 1) / 11 ≤ (i : ℝ) / 11 := h2.trans h1
  linarith [this]

theorem ends_middle_disjoint {E : Set M} (k : E → unitInterval) :
    Disjoint (layer k 0 ∪ layer k 1) (middle k) := by
  rw [disjoint_left]
  rintro _ hx ⟨e', he', hee'⟩
  rcases hx with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · have : e' = e := Subtype.val_injective hee'
    subst this
    have h0 : k e' = 0 := he
    have := he'.1
    rw [h0] at this
    norm_num at this
  · have : e' = e := Subtype.val_injective hee'
    subst this
    have h0 : k e' = 1 := he
    have := he'.2
    rw [h0] at this
    norm_num at this

/-- **T4**: `ε₁` exists. -/
theorem exists_isEps1 {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ ε₁, IsEps1 k ε₁ := by
  classical
  have hpc : ∀ i : ℕ, IsCompact (piece k i) := fun i => isCompact_layerSet_interval hE _ _
  set s : Finset (ℕ × ℕ) := ((Finset.range 12) ×ˢ (Finset.range 12)).filter
    fun p => p.1 + 1 < p.2
  obtain ⟨δ, hδ, hδs⟩ := exists_pos_forall_finset s
    (fun p δ => ∀ x ∈ piece k p.1, ∀ y ∈ piece k p.2, δ ≤ dist x y)
    (fun p a b _ hab hP x hx y hy => hab.trans (hP x hx y hy))
    (fun p hp => exists_pos_le_dist (hpc p.1) (hpc p.2).isClosed
      (piece_disjoint k (Finset.mem_filter.1 hp).2))
  have hendc : IsCompact (layer k 0 ∪ layer k 1) := by
    have hEc := hE.isCompact
    exact (isCompact_img hEc hE.2.1.1 isClosed_singleton).union
      (isCompact_img hEc hE.2.1.1 isClosed_singleton)
  obtain ⟨δ', hδ', hδ's⟩ := exists_pos_le_dist hendc
    (isCompact_layerSet_interval hE _ _).isClosed (ends_middle_disjoint k)
  refine ⟨min (δ / 4) (δ' / 3), lt_min (by positivity) (by positivity), ?_, ?_⟩
  · intro i j hij hj x hx y hy
    have hp : (i, j) ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, hij⟩
    have := hδs _ hp x hx y hy
    have : 4 * min (δ / 4) (δ' / 3) ≤ δ := by
      have := min_le_left (δ / 4) (δ' / 3); linarith
    linarith
  · intro x hx y hy
    have := hδ's x hx y hy
    have : 3 * min (δ / 4) (δ' / 3) ≤ δ' := by
      have := min_le_right (δ / 4) (δ' / 3); linarith
    linarith

/-- The `ε₁`-neighbourhoods of the images of non-adjacent elevenths under an `ε₁`-homeomorphism
are disjoint (the skeleton's form of T4). -/
theorem isEps1_thickening_disjoint {E : Set M} {k : E → unitInterval} {ε₁ : ℝ}
    (he : IsEps1 k ε₁) (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < ε₁) {i j : ℕ} (hij : i + 1 < j)
    (hj : j ≤ 11) :
    Disjoint (Metric.thickening ε₁ (toPt (h '' piece k i)))
      (Metric.thickening ε₁ (toPt (h '' piece k j))) := by
  rw [disjoint_left]
  intro z hz hz'
  obtain ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, hza⟩ := mem_thickening_iff.1 hz
  obtain ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, hzb⟩ := mem_thickening_iff.1 hz'
  have h1 := hh a
  have h2 := hh b
  have hsep := he.sep i j hij hj a ha b hb
  have htri : dist a b ≤ dist a (h a) + dist (z : Pt) ((h a : M) : Pt) +
      dist (z : Pt) ((h b : M) : Pt) + dist b (h b) := by
    rw [Subtype.dist_eq, Subtype.dist_eq, Subtype.dist_eq]
    have := dist_triangle4 (a : Pt) ((h a : M) : Pt) z (b : Pt)
    have h3 := dist_triangle (z : Pt) ((h b : M) : Pt) (b : Pt)
    rw [dist_comm ((h a : M) : Pt) z] at this
    rw [dist_comm ((h b : M) : Pt) (b : Pt)] at h3
    linarith
  linarith

end Eps1

end HPC.Hagopian
