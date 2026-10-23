import HPC.BJ59.Thm10Defs
import HPC.BJ59.Private
import HPC.BJ59.BJChains

/-!
# Batch 201: small library for Theorem 10

Distances along an `ε`-chain, convexity of the set of links meeting a preconnected set, counting
a downward-closed set of indices.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Lib

variable {Y : Type*} [MetricSpace Y]

/-- Points of the closures of two links of an `ε`-chain `d` apart are less than `(d + 1) ε`
apart. -/
theorem dist_lt_of_mem_closure_link {N : ℕ} {F : Chain Y N} {ε : ℝ} (hF : IsEpsChain F ε) :
    ∀ (d : ℕ) (a b : Fin N), b.val = a.val + d → ∀ x ∈ closure (F.link a),
      ∀ y ∈ closure (F.link b), dist x y < (d + 1) * ε := by
  intro d
  induction d with
  | zero =>
    intro a b hab x hx y hy
    have : a = b := Fin.ext (by omega)
    subst this
    have h1 := dist_le_diam_of_mem (hF a).1.closure hx hy
    rw [Metric.diam_closure] at h1
    have := (hF a).2
    simp only [Nat.cast_zero, zero_add, one_mul]
    linarith
  | succ d ih =>
    intro a b hab x hx y hy
    set c : Fin N := ⟨a.val + d, by omega⟩
    obtain ⟨w, hwc, hwb⟩ := (F.adjacent c b).2 (by simp only [c]; omega)
    have h1 := ih a c rfl x hx w (subset_closure hwc)
    have h2 := dist_le_diam_of_mem (hF b).1.closure (subset_closure hwb) hy
    rw [Metric.diam_closure] at h2
    have := (hF b).2
    have := dist_triangle x w y
    push_cast
    linarith

/-- The symmetric form of `dist_lt_of_mem_closure_link`. -/
theorem dist_lt_of_mem_closure_link' {N : ℕ} {F : Chain Y N} {ε : ℝ} (hF : IsEpsChain F ε)
    (a b : Fin N) {x y : Y} (hx : x ∈ closure (F.link a)) (hy : y ∈ closure (F.link b)) :
    dist x y < (((a : ℤ) - b).natAbs + 1) * ε := by
  rcases le_total a.val b.val with h | h
  · have := dist_lt_of_mem_closure_link hF (b.val - a.val) a b (by omega) x hx y hy
    have he : (((a : ℤ) - b).natAbs : ℝ) = ((b.val - a.val : ℕ) : ℝ) := by
      congr 1; omega
    rw [he]; exact this
  · have := dist_lt_of_mem_closure_link hF (a.val - b.val) b a (by omega) y hy x hx
    have he : (((a : ℤ) - b).natAbs : ℝ) = ((a.val - b.val : ℕ) : ℝ) := by
      congr 1; omega
    rw [he, dist_comm]; exact this

/-- Counting a downward-closed property below `M`. -/
theorem card_filter_lt_iff_of_downward (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ w w', w' ≤ w → P w → P w') :
    ∀ (M w : ℕ), w < M → (P w ↔ w < ((Finset.range M).filter P).card) := by
  intro M
  induction M with
  | zero => intro w hw; omega
  | succ M ih =>
    intro w hw
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hM : P M
    · rw [if_pos hM, Finset.card_insert_of_notMem (by simp)]
      have hall : ∀ w', w' < M → P w' := fun w' hw' => hP M w' hw'.le hM
      have hc : ((Finset.range M).filter P).card = M := by
        rw [Finset.filter_true_of_mem (fun w' hw' => hall w' (Finset.mem_range.1 hw'))]
        simp
      rw [hc]
      exact ⟨fun _ => by omega, fun _ => hP M w (by omega) hM⟩
    · rw [if_neg hM]
      rcases Nat.lt_or_ge w M with h | h
      · exact ih w h
      · have : w = M := by omega
        subst this
        have := Finset.card_le_card (Finset.filter_subset P (Finset.range w))
        simp only [Finset.card_range] at this
        exact ⟨fun h' => absurd h' hM, fun h' => by omega⟩

theorem card_filter_le (P : ℕ → Prop) [DecidablePred P] (M : ℕ) :
    ((Finset.range M).filter P).card ≤ M := by
  have := Finset.card_le_card (Finset.filter_subset P (Finset.range M))
  simpa using this

end Lib

section Lib2

variable {Y : Type*} [MetricSpace Y]

/-- **Tube lemma** for a fibre: a compact set meeting the fibre over `c` inside an open set `V`
meets the fibres near `c` inside `V`. -/
theorem exists_tube {g : Y → unitInterval} (hg : Continuous g) {K V : Set Y} (hK : IsCompact K)
    (hV : IsOpen V) {c : unitInterval} (h : K ∩ g ⁻¹' {c} ⊆ V) :
    ∃ τ > 0, ∀ y ∈ K, |(g y : ℝ) - c| ≤ τ → y ∈ V := by
  by_cases hne : (K \ V).Nonempty
  · have hc : IsCompact (K \ V) := hK.diff hV
    have hcont : ContinuousOn (fun y => |(g y : ℝ) - c|) (K \ V) :=
      ((continuous_subtype_val.comp hg).sub continuous_const).abs.continuousOn
    obtain ⟨y₀, hy₀, hmin⟩ := hc.exists_isMinOn hne hcont
    have hpos : 0 < |(g y₀ : ℝ) - c| := by
      rw [abs_pos, sub_ne_zero]
      intro he
      exact hy₀.2 (h ⟨hy₀.1, by simp only [mem_preimage, mem_singleton_iff]; exact Subtype.ext he⟩)
    refine ⟨|(g y₀ : ℝ) - c| / 2, by linarith, fun y hy hyc => ?_⟩
    by_contra hyV
    have := hmin ⟨hy, hyV⟩
    simp only [mem_setOf_eq] at this
    linarith
  · refine ⟨1, one_pos, fun y hy _ => ?_⟩
    by_contra hyV
    exact hne ⟨y, hy, hyV⟩

/-- An open set meeting the fibre over `c` meets the fibres near `c` (for an open map). -/
theorem exists_meets_near {g : Y → unitInterval} (hgo : IsOpenMap g) {U : Set Y} (hU : IsOpen U)
    {c : unitInterval} (h : (U ∩ g ⁻¹' {c}).Nonempty) :
    ∃ τ > 0, ∀ x : unitInterval, |(x : ℝ) - c| ≤ τ → (U ∩ g ⁻¹' {x}).Nonempty := by
  obtain ⟨y, hyU, hyc⟩ := h
  have hc : c ∈ g '' U := ⟨y, hyU, hyc⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hgo U hU) c hc
  refine ⟨r / 2, by linarith, fun x hx => ?_⟩
  obtain ⟨z, hzU, hzx⟩ := hball (show x ∈ ball c r by
    rw [mem_ball, Subtype.dist_eq, Real.dist_eq]; linarith)
  exact ⟨z, hzU, hzx⟩

/-- Shrinking the links keeps an `ε`-chain. -/
theorem IsEpsChain.of_subset {n : ℕ} {D D' : Chain Y n} {ε : ℝ} (hD : IsEpsChain D ε)
    (h : ∀ i, D'.link i ⊆ D.link i) : IsEpsChain D' ε := fun i =>
  ⟨(hD i).1.subset (h i), lt_of_le_of_lt (Metric.diam_mono (h i) (hD i).1) (hD i).2⟩

/-- Fine chains in Bing–Jones's sense with private points cover a non-degenerate snake-like
space. -/
theorem exists_fine_bjChain_private (hSY : IsSnakeLike (univ : Set Y))
    (hnt : (univ : Set Y).Nontrivial) {μ : ℝ} (hμ : 0 < μ) :
    ∃ (N : ℕ) (G : Chain Y N), univ ⊆ G.union ∧ IsBJChain G ∧ IsEpsChain G μ ∧
      HasPrivatePoints G := by
  obtain ⟨N, G₀, hG₀, hcov⟩ := hSY.2 μ hμ
  obtain ⟨G₁, hG₁bj, hG₁cov, hG₁ne, hG₁sub⟩ := exists_bjChain_shrink hSY.1 G₀ hcov
    (fun i => by simpa using G₀.link_nonempty i) (fun _ => ∅)
    (fun _ => ⟨isCompact_empty, empty_subset _⟩)
  obtain ⟨G₂, hG₂bj, hG₂cov, hG₂sub, hG₂p⟩ := exists_privatePoint_shrink hSY.1 hnt G₁ hG₁bj
    hG₁cov hG₁ne
  refine ⟨N, G₂, hG₂cov, hG₂bj, IsEpsChain.of_subset hG₀ fun i => (hG₂sub i).trans
    ((subset_closure).trans (hG₁sub i).1), fun i => ?_⟩
  obtain ⟨p, hp, hpo⟩ := hG₂p i
  exact ⟨p, hp.2, hpo⟩

end Lib2

end HPC.BJ59
