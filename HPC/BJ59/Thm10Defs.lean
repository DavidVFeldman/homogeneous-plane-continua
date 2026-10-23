import HPC.BJ59.Zigzag
import HPC.BJ59.Step1b

/-!
# Batch 201, §§2–3: the conditions carried through the induction of Theorem 10, and the
# combinatorial tools

The skeleton's `HasPrivatePoints`, `IsFibreChainMap`, `EndCompat`, `IsFibreFine` (statements
verbatim), and the tools `exists_point_only_of_minimal`, `adjacent_of_properCover`,
`isFibreFine_of_isEpsChain`. Route: commission 201 §§2–3.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

/-! ## §2. The conditions carried through the induction -/

section Conditions

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Every link has a point outside the closures of the other links. -/
def HasPrivatePoints {n : ℕ} (D : Chain X n) : Prop :=
  ∀ j, ∃ p ∈ D.link j, ∀ j', j' ≠ j → p ∉ closure (D.link j')

/-- **Condition A of p. 188, in the form carried through the induction.** `H` is a chain map of
`D` onto `E`; a link meeting a fibre of `f` goes to a link meeting the fibre of `g` over the same
point; and a run of links of `D` that properly covers a fibre of `f` goes to links whose union
covers the fibre of `g` over the same point. -/
def IsFibreChainMap (f : X → unitInterval) (g : Y → unitInterval) {n m : ℕ} (D : Chain X n)
    (E : Chain Y m) (H : Fin n → Fin m) : Prop :=
  IsChainMap H ∧ Function.Surjective H ∧
    (∀ t j, (D.link j ∩ f ⁻¹' {t}).Nonempty → (E.link (H j) ∩ g ⁻¹' {t}).Nonempty) ∧
    ∀ t (u v : ℕ), (∀ j : Fin n, u ≤ j.val → j.val ≤ v → (D.link j ∩ f ⁻¹' {t}).Nonempty) →
      f ⁻¹' {t} ⊆ ⋃ (j : Fin n) (_ : u ≤ j.val ∧ j.val ≤ v), D.link j →
      g ⁻¹' {t} ⊆ ⋃ (j : Fin n) (_ : u ≤ j.val ∧ j.val ≤ v), E.link (H j)

/-- **Condition C of p. 188**: agreement with the given homeomorphisms of the end fibres. -/
def EndCompat (f : X → unitInterval) (g : Y → unitInterval) (h₀ : f ⁻¹' {0} ≃ₜ g ⁻¹' {0})
    (h₁ : f ⁻¹' {1} ≃ₜ g ⁻¹' {1}) {n m : ℕ} (D : Chain X n) (E : Chain Y m)
    (H : Fin n → Fin m) : Prop :=
  (∀ j (x : f ⁻¹' {0}), (x : X) ∈ D.link j → (h₀ x : Y) ∈ E.link (H j)) ∧
    ∀ j (x : f ⁻¹' {1}), (x : X) ∈ D.link j → (h₁ x : Y) ∈ E.link (H j)

/-- One link, or every run of links covering a fibre has at least three links. -/
def IsFibreFine (g : Y → unitInterval) {m : ℕ} (E : Chain Y m) : Prop :=
  m = 1 ∨ ∀ t (u v : ℕ), g ⁻¹' {t} ⊆ ⋃ (k : Fin m) (_ : u ≤ k.val ∧ k.val ≤ v), E.link k →
    u + 2 ≤ v

end Conditions

/-! ## §3. Tools -/

section Tools

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- In a run covering a preconnected set from which neither end link can be dropped, every link
contains a point of the set that lies in no other link of the run. -/
theorem exists_point_only_of_minimal {n : ℕ} (D : Chain X n) {C : Set X} (hC : IsPreconnected C)
    {w₁ w₂ : ℕ} (hw : w₁ ≤ w₂) (hw₂ : w₂ < n)
    (hcov : C ⊆ ⋃ (j : Fin n) (_ : w₁ ≤ j.val ∧ j.val ≤ w₂), D.link j)
    (hl : ¬ C ⊆ ⋃ (j : Fin n) (_ : w₁ + 1 ≤ j.val ∧ j.val ≤ w₂), D.link j)
    (hr : ¬ C ⊆ ⋃ (j : Fin n) (_ : w₁ ≤ j.val ∧ j.val + 1 ≤ w₂), D.link j)
    (j : Fin n) (hj₁ : w₁ ≤ j.val) (hj₂ : j.val ≤ w₂) :
    ∃ z ∈ C ∩ D.link j, ∀ j' : Fin n, w₁ ≤ j'.val → j'.val ≤ w₂ → j' ≠ j → z ∉ D.link j' := by
  by_contra hno
  push_neg at hno
  set U : Set X := ⋃ (k : Fin n) (_ : w₁ ≤ k.val ∧ k.val < j.val), D.link k with hU
  set V : Set X := ⋃ (k : Fin n) (_ : j.val < k.val ∧ k.val ≤ w₂), D.link k with hV
  have hUo : IsOpen U := isOpen_biUnion fun k _ => D.isOpen k
  have hVo : IsOpen V := isOpen_biUnion fun k _ => D.isOpen k
  have hUV : Disjoint U V := by
    rw [Set.disjoint_left]
    intro z hzU hzV
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 hzU
    obtain ⟨k', hk', hzk'⟩ := mem_iUnion₂.1 hzV
    have := (D.adjacent_iff k k').1 ⟨z, hzk, hzk'⟩
    by_cases hkk : k'.val = k.val + 1
    · omega
    · omega
  have hCUV : C ⊆ U ∪ V := by
    intro z hz
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 (hcov hz)
    have key : ∃ k' : Fin n, w₁ ≤ k'.val ∧ k'.val ≤ w₂ ∧ k' ≠ j ∧ z ∈ D.link k' := by
      by_cases hkj : k = j
      · subst hkj
        obtain ⟨k', h1, h2, h3, h4⟩ := hno z ⟨hz, hzk⟩
        exact ⟨k', h1, h2, h3, h4⟩
      · exact ⟨k, hk.1, hk.2, hkj, hzk⟩
    obtain ⟨k', h1, h2, h3, h4⟩ := key
    have h3' : k'.val ≠ j.val := fun h => h3 (Fin.ext h)
    rcases lt_or_gt_of_ne h3' with h | h
    · exact Or.inl (mem_iUnion₂.2 ⟨k', ⟨h1, h⟩, h4⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨k', ⟨h, h2⟩, h4⟩)
  rcases hC.subset_or_subset hUo hVo hUV hCUV with h | h
  · apply hr
    intro z hz
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 (h hz)
    exact mem_iUnion₂.2 ⟨k, ⟨hk.1, by omega⟩, hzk⟩
  · apply hl
    intro z hz
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 (h hz)
    exact mem_iUnion₂.2 ⟨k, ⟨by omega, hk.2⟩, hzk⟩

/-- Discrete intermediate values: an integer sequence with steps of at most two, at most `1` at
`p` and at least `-1` at `q ≥ p`, takes a value in `[-1, 1]` on `[p, q]`. -/
theorem exists_abs_le_one_of_steps (ψ : ℕ → ℤ) (hψ : ∀ k, |ψ (k + 1) - ψ k| ≤ 2) :
    ∀ (d p : ℕ), ψ p ≤ 1 → -1 ≤ ψ (p + d) → ∃ k, p ≤ k ∧ k ≤ p + d ∧ |ψ k| ≤ 1 := by
  intro d
  induction d with
  | zero =>
    intro p hp hq
    exact ⟨p, le_rfl, le_rfl, abs_le.2 ⟨by simpa using hq, hp⟩⟩
  | succ d ih =>
    intro p hp hq
    by_cases h : -1 ≤ ψ p
    · exact ⟨p, le_rfl, by omega, abs_le.2 ⟨h, hp⟩⟩
    · have h1 := hψ p
      rw [abs_le] at h1
      have hq' : -1 ≤ ψ (p + 1 + d) := by
        rw [show p + 1 + d = p + (d + 1) by omega]; exact hq
      obtain ⟨k, hk1, hk2, hk⟩ := ih (p + 1) (by omega) hq'
      exact ⟨k, by omega, by omega, hk⟩

/-- **Theorem 6 in the form Step 2(c) uses** (p. 185): two chain maps that carry a run onto
families of links each properly covering the same set agree up to adjacency somewhere on the
run. -/
theorem adjacent_of_properCover {N n : ℕ} (D : Chain X n) {C : Set X} {R R' : Fin N → Fin n}
    (hR : IsChainMap R) (hR' : IsChainMap R') {t u : ℕ} (htu : t ≤ u) (hu : u < N)
    (hRC : ∀ a : Fin N, t ≤ a.val → a.val ≤ u → (D.link (R a) ∩ C).Nonempty)
    (hR'C : ∀ a : Fin N, t ≤ a.val → a.val ≤ u → (D.link (R' a) ∩ C).Nonempty)
    (hCR : C ⊆ ⋃ (a : Fin N) (_ : t ≤ a.val ∧ a.val ≤ u), D.link (R a))
    (hCR' : C ⊆ ⋃ (a : Fin N) (_ : t ≤ a.val ∧ a.val ≤ u), D.link (R' a)) :
    ∃ a : Fin N, t ≤ a.val ∧ a.val ≤ u ∧ ((R a : ℤ) - R' a).natAbs ≤ 1 := by
  classical
  -- the run as a finset
  set S : Finset (Fin N) := Finset.univ.filter (fun a : Fin N => t ≤ a.val ∧ a.val ≤ u) with hS
  have hSne : S.Nonempty := ⟨⟨t, by omega⟩, by simp [hS, htu]⟩
  obtain ⟨a₀, ha₀S, ha₀⟩ := S.exists_min_image (fun a => (R a).val) hSne
  obtain ⟨b₀, hb₀S, hb₀⟩ := S.exists_min_image (fun a => (R' a).val) hSne
  simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at ha₀S hb₀S ha₀ hb₀
  -- `v ≥ v' - 1` and `v' ≥ v - 1`
  have hv : (R' b₀).val ≤ (R a₀).val + 1 := by
    obtain ⟨z, hz1, hz2⟩ := hRC a₀ ha₀S.1 ha₀S.2
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.1 (hCR' hz2)
    have := (D.adjacent_iff _ _).1 ⟨z, hz1, hza⟩
    have := hb₀ a ha
    omega
  have hv' : (R a₀).val ≤ (R' b₀).val + 1 := by
    obtain ⟨z, hz1, hz2⟩ := hR'C b₀ hb₀S.1 hb₀S.2
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.1 (hCR hz2)
    have := (D.adjacent_iff _ _).1 ⟨z, hz1, hza⟩
    have := ha₀ a ha
    omega
  -- `φ = R - R'` on the run, extended by zero
  set ψ : ℕ → ℤ := fun k => if hk : k < N then ((R ⟨k, hk⟩ : ℤ) - R' ⟨k, hk⟩) else 0 with hψ
  have hstep : ∀ k, t ≤ k → k + 1 ≤ u → |ψ (k + 1) - ψ k| ≤ 2 := by
    intro k hk1 hk2
    have h1 := hR ⟨k + 1, by omega⟩ ⟨k, by omega⟩ (by simp)
    have h2 := hR' ⟨k + 1, by omega⟩ ⟨k, by omega⟩ (by simp)
    simp only [hψ, dif_pos (show k + 1 < N by omega), dif_pos (show k < N by omega)]
    rw [abs_le]
    constructor <;> omega
  -- the sequence restricted to `[t, u]`
  set ψ' : ℕ → ℤ := fun k => ψ (max t (min k u)) with hψ'
  have hstep' : ∀ k, |ψ' (k + 1) - ψ' k| ≤ 2 := by
    intro k
    simp only [hψ']
    by_cases h1 : k + 1 ≤ t
    · rw [max_eq_left (by omega), max_eq_left (by omega)]; simp
    by_cases h2 : u ≤ k
    · rw [min_eq_right (by omega), min_eq_right (by omega)]; simp
    rw [min_eq_left (by omega), min_eq_left (by omega), max_eq_right (by omega),
      max_eq_right (by omega)]
    exact hstep k (by omega) (by omega)
  have hval : ∀ a : Fin N, t ≤ a.val → a.val ≤ u → ψ' a.val = (R a : ℤ) - R' a := by
    intro a h1 h2
    simp only [hψ', hψ]
    rw [min_eq_left h2, max_eq_right h1, dif_pos a.isLt]
  have hfin : ∀ k, t ≤ k → k ≤ u → |ψ' k| ≤ 1 →
      ∃ a : Fin N, t ≤ a.val ∧ a.val ≤ u ∧ ((R a : ℤ) - R' a).natAbs ≤ 1 := by
    intro k h1 h2 h3
    refine ⟨⟨k, by omega⟩, h1, h2, ?_⟩
    rw [hval ⟨k, by omega⟩ h1 h2] at h3
    rw [abs_le] at h3
    omega
  -- at `b₀`, `ψ ≥ -1`; at `a₀`, `ψ ≤ 1`
  have hb : -1 ≤ ψ' b₀.val := by
    rw [hval b₀ hb₀S.1 hb₀S.2]
    have := ha₀ b₀ hb₀S
    omega
  have ha : ψ' a₀.val ≤ 1 := by
    rw [hval a₀ ha₀S.1 ha₀S.2]
    have := hb₀ a₀ ha₀S
    omega
  rcases le_total a₀.val b₀.val with hab | hab
  · obtain ⟨k, hk1, hk2, hk⟩ := exists_abs_le_one_of_steps ψ' hstep' (b₀.val - a₀.val) a₀.val ha
      (by rw [show a₀.val + (b₀.val - a₀.val) = b₀.val by omega]; exact hb)
    exact hfin k (by omega) (by omega) hk
  · -- reverse direction: apply the lemma to `-ψ'`
    have hstep'' : ∀ k, |(-ψ') (k + 1) - (-ψ') k| ≤ 2 := by
      intro k
      have := hstep' k
      simp only [Pi.neg_apply]
      rw [show -ψ' (k + 1) - -ψ' k = -(ψ' (k + 1) - ψ' k) by ring, abs_neg]
      exact this
    obtain ⟨k, hk1, hk2, hk⟩ := exists_abs_le_one_of_steps (-ψ') hstep'' (a₀.val - b₀.val)
      b₀.val (by simp only [Pi.neg_apply]; omega)
      (by rw [show b₀.val + (a₀.val - b₀.val) = a₀.val by omega]; simp only [Pi.neg_apply]; omega)
    simp only [Pi.neg_apply, abs_neg] at hk
    exact hfin k (by omega) (by omega) hk

/-- Chains finer than a third of the spread of the fibres are fibre-fine. -/
theorem isFibreFine_of_isEpsChain {g : Y → unitInterval} {κ : ℝ}
    (hκ : ∀ t, ∃ p ∈ g ⁻¹' {t}, ∃ q ∈ g ⁻¹' {t}, κ ≤ dist p q) {m : ℕ} (E : Chain Y m)
    (hE : IsEpsChain E (κ / 3)) : IsFibreFine g E := by
  right
  intro t u v hcov
  by_contra huv
  obtain ⟨p, hp, q, hq, hpq⟩ := hκ t
  obtain ⟨a, ha, hpa⟩ := mem_iUnion₂.1 (hcov hp)
  obtain ⟨b, hb, hqb⟩ := mem_iUnion₂.1 (hcov hq)
  have hab : ((a : ℤ) - b).natAbs ≤ 1 := by omega
  have := dist_lt_of_adjacent hE hab hpa hqb
  have := dist_nonneg (x := p) (y := q)
  linarith

end Tools

end HPC.BJ59
