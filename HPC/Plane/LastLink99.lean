import HPC.Plane.Organ98
import HPC.Plane.Recon91

/-!
# Batch 99: the last-link claim of Bing's Theorem 10 (Duke 1951), by Fugate's counting argument

See `REPORT-batch99.md`. Bing's orientation throughout: `p` in the first link of `F`, the claim
concerns the last link.
-/

namespace HPC.Plane

open Set Topology

variable {X : Type*} [MetricSpace X]

/-- A **Theorem-10 chain for `K` from `p` refining `D`**: covers `K`, refines `D`, and `p` lies
in the first link and in the closure of no other. -/
def IsT10Chain {m : ℕ} (D : Chain X m) (K : Set X) (p : X) {k : ℕ} (F : Chain X k) : Prop :=
  ∃ hk : 0 < k, K ⊆ F.union ∧ F.Refines D ∧ p ∈ F.link ⟨0, hk⟩ ∧
    ∀ j : Fin k, j.val ≠ 0 → p ∉ closure (F.link j)

/-! ### Index values extended to `ℕ` -/

/-- The `D`-indices `a i` of the links of `F`, extended to all of `ℕ` by repeating the last one. -/
def clampVal {k m : ℕ} (hk : 0 < k) (a : Fin k → Fin m) (i : ℕ) : ℤ :=
  ((a ⟨min i (k - 1), by omega⟩ : Fin m) : ℕ)

theorem clampVal_of_lt {k m : ℕ} (hk : 0 < k) (a : Fin k → Fin m) {i : ℕ} (hi : i < k) :
    clampVal hk a i = ((a ⟨i, hi⟩ : Fin m) : ℕ) := by
  simp only [clampVal, Nat.min_eq_left (show i ≤ k - 1 by omega)]

/-- Consecutive links of `F` meet, so their `D`-indices differ by at most one. -/
theorem clampVal_step {k m : ℕ} {D : Chain X m} {F : Chain X k} (hk : 0 < k) (a : Fin k → Fin m)
    (ha : ∀ i, F.link i ⊆ D.link (a i)) (i : ℕ) :
    |clampVal hk a (i + 1) - clampVal hk a i| ≤ 1 := by
  by_cases h : i + 1 < k
  · rw [clampVal_of_lt hk a h, clampVal_of_lt hk a (by omega : i < k)]
    obtain ⟨z, hz1, hz2⟩ := (F.adjacent_iff ⟨i, by omega⟩ ⟨i + 1, h⟩).mpr (by simp only []; omega)
    have := (D.adjacent_iff (a ⟨i, by omega⟩) (a ⟨i + 1, h⟩)).mp ⟨z, ha _ hz1, ha _ hz2⟩
    rw [abs_le]
    omega
  · have : clampVal hk a (i + 1) = clampVal hk a i := by
      simp only [clampVal, show min (i + 1) (k - 1) = k - 1 by omega,
        show min i (k - 1) = k - 1 by omega]
    rw [this]
    simp

/-- **Item 1. Discrete intermediate value for refinements.** If `F` refines `D` via the choice
`idx` (`F.link i ⊆ D.link (idx i)`), a run `F(u..v)` passes through every `D`-index between
`idx u` and `idx v`. -/
theorem exists_link_in_between {m k : ℕ} {D : Chain X m} {F : Chain X k}
    (idx : Fin k → Fin m) (hidx : ∀ i, F.link i ⊆ D.link (idx i))
    {u v : Fin k} (huv : u ≤ v) {r : Fin m} (hr : idx u ≤ r ∧ r ≤ idx v ∨ idx v ≤ r ∧ r ≤ idx u) :
    ∃ i : Fin k, u ≤ i ∧ i ≤ v ∧ idx i = r := by
  have hk : 0 < k := u.pos
  set C := clampVal hk idx with hC
  have hstep := clampVal_step hk idx hidx
  have hCu : C u = ((idx u : Fin m) : ℕ) := clampVal_of_lt hk idx u.isLt
  have hCv : C v = ((idx v : Fin m) : ℕ) := clampVal_of_lt hk idx v.isLt
  have huv' : u.val ≤ v.val := huv
  -- it suffices to find a natural index in `[u, v]` with value `r`
  suffices h : ∃ t : ℕ, u.val ≤ t ∧ t ≤ v.val ∧ C t = (r : ℕ) by
    obtain ⟨t, h1, h2, h3⟩ := h
    refine ⟨⟨t, by omega⟩, h1, h2, Fin.ext ?_⟩
    rw [hC, clampVal_of_lt hk idx (by omega)] at h3
    exact_mod_cast h3
  have hr' : (C u ≤ (r : ℕ) ∧ ((r : ℕ) : ℤ) ≤ C v) ∨ (C v ≤ (r : ℕ) ∧ ((r : ℕ) : ℤ) ≤ C u) := by
    rw [hCu, hCv]
    rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · right; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  by_cases hu : C u = (r : ℕ)
  · exact ⟨u, le_rfl, huv', hu⟩
  by_cases hv : C v = (r : ℕ)
  · exact ⟨v, huv', le_rfl, hv⟩
  rcases hr' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨t, ht1, ht2, hc⟩ := exists_adjacent_cross hstep (a := u.val) (b := v.val)
      (p := (r : ℕ)) h1 (show ((r : ℕ) : ℤ) + 1 ≤ C v.val by omega)
    rcases hc with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact ⟨t, by omega, by omega, e1⟩
    · exact ⟨t + 1, by omega, by omega, e2⟩
  · obtain ⟨t, ht1, ht2, hc⟩ := exists_adjacent_cross hstep (a := v.val) (b := u.val)
      (p := (r : ℕ)) h1 (show ((r : ℕ) : ℤ) + 1 ≤ C u.val by omega)
    rcases hc with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact ⟨t, by omega, by omega, e1⟩
    · exact ⟨t + 1, by omega, by omega, e2⟩

/-! ### The combinatorial core -/

/-- **A tail with an extreme first term and a repeated value.** Let `g` move by at most one per
step, and let `g N` lie between `g u` and `g v` with `u ≤ v < N`. Then some `j < N` has `g j`
extreme (minimum or maximum) among `g j, …, g N`, and the value `g N` is taken also at some
`i ∈ [j, N)`. -/
theorem exists_extreme_repeat {g : ℕ → ℤ} (hstep : ∀ i, |g (i + 1) - g i| ≤ 1) {u v N : ℕ}
    (huv : u ≤ v) (hvN : v < N)
    (hbet : (g u ≤ g N ∧ g N ≤ g v) ∨ (g v ≤ g N ∧ g N ≤ g u)) :
    ∃ j, j < N ∧ ((∀ i, j ≤ i → i ≤ N → g j ≤ g i) ∨ (∀ i, j ≤ i → i ≤ N → g i ≤ g j)) ∧
      ∃ i, j ≤ i ∧ i < N ∧ g i = g N := by
  classical
  obtain ⟨iL, hiL, hL⟩ := (Finset.Icc u N).exists_min_image g ⟨u, by simp; omega⟩
  obtain ⟨iH, hiH, hH⟩ := (Finset.Icc u N).exists_max_image g ⟨u, by simp; omega⟩
  simp only [Finset.mem_Icc] at hiL hiH
  have hL' : ∀ i, u ≤ i → i ≤ N → g iL ≤ g i := fun i h1 h2 => hL i (by simp; omega)
  have hH' : ∀ i, u ≤ i → i ≤ N → g i ≤ g iH := fun i h1 h2 => hH i (by simp; omega)
  have hLu := hL' u le_rfl (by omega)
  have hLv := hL' v huv (by omega)
  have hHu := hH' u le_rfl (by omega)
  have hHv := hH' v huv (by omega)
  have hLN := hL' N (by omega) le_rfl
  have hHN := hH' N (by omega) le_rfl
  by_cases h1 : g N = g iL
  · -- `g N` is the minimum; it is attained at `u` or at `v`
    have hw : ∃ w, w ≤ v ∧ u ≤ w ∧ g w = g iL := by
      rcases hbet with ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨u, huv, le_rfl, by omega⟩
      · exact ⟨v, le_rfl, huv, by omega⟩
    obtain ⟨w, hwv, hwu, hgw⟩ := hw
    refine ⟨w, by omega, Or.inl fun i hi hiN => ?_, w, le_rfl, by omega, by omega⟩
    rw [hgw]; exact hL' i (by omega) hiN
  by_cases h2 : g N = g iH
  · have hw : ∃ w, w ≤ v ∧ u ≤ w ∧ g w = g iH := by
      rcases hbet with ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨v, le_rfl, huv, by omega⟩
      · exact ⟨u, huv, le_rfl, by omega⟩
    obtain ⟨w, hwv, hwu, hgw⟩ := hw
    refine ⟨w, by omega, Or.inr fun i hi hiN => ?_, w, le_rfl, by omega, by omega⟩
    rw [hgw]; exact hH' i (by omega) hiN
  have hLN' : g iL < g N := lt_of_le_of_ne hLN (Ne.symm h1)
  have hNH' : g N < g iH := lt_of_le_of_ne hHN h2
  have hiLN : iL ≠ N := fun h => h1 (by rw [h])
  have hiHN : iH ≠ N := fun h => h2 (by rw [h])
  obtain ⟨t, ht1, ht2, hc⟩ := exists_adjacent_cross hstep (a := iL) (b := iH) (p := g N)
    hLN'.le (by omega)
  have hi : ∃ i, min iL iH ≤ i ∧ i ≤ max iL iH ∧ g i = g N := by
    rcases hc with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact ⟨t, ht1, by omega, e1⟩
    · exact ⟨t + 1, by omega, ht2, e2⟩
  obtain ⟨i, hi1, hi2, hgi⟩ := hi
  have hiN : i < N := by
    rcases le_total iL iH with h | h
    · rw [max_eq_right h] at hi2; omega
    · rw [max_eq_left h] at hi2; omega
  rcases le_total iL iH with h | h
  · rw [min_eq_left h] at hi1
    exact ⟨iL, by omega, Or.inl fun i' hi' hi'N => hL' i' (by omega) hi'N, i, hi1, hiN, hgi⟩
  · rw [min_eq_right h] at hi1
    exact ⟨iH, by omega, Or.inr fun i' hi' hi'N => hH' i' (by omega) hi'N, i, hi1, hiN, hgi⟩

/-! ### The shortening -/

/-- **Shortening a Theorem-10 chain.** Let `a` choose for each link of `F` a link of `D`
containing it, with values `C` on `ℕ`. If from some index `j` on the value `C j` is extreme among
`C j, …, C (k-1)` and some value repeats in that range, then the tail `F(j..k-1)` can be replaced
by the consolidation whose links are the unions of the tail links with a common `D`-index; the
result is a shorter Theorem-10 chain. -/
theorem exists_shorter_T10Chain {m k : ℕ} {D : Chain X m} {K : Set X} {p : X} {F : Chain X k}
    (hF : IsT10Chain D K p F) (a : Fin k → Fin m) (ha : ∀ i, F.link i ⊆ D.link (a i))
    {j : ℕ} (hjk : j < k) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hext : ∀ i, j ≤ i → i < k → 0 ≤ s * (clampVal hF.1 a i - clampVal hF.1 a j))
    {i₁ i₂ : ℕ} (h₁ : j ≤ i₁) (h₁₂ : i₁ < i₂) (h₂ : i₂ < k)
    (hrep : clampVal hF.1 a i₁ = clampVal hF.1 a i₂) :
    ∃ k' < k, ∃ G : Chain X k', IsT10Chain D K p G := by
  classical
  have hKF := hF.2.1
  have hp0 := hF.2.2.2.1
  have hpF := hF.2.2.2.2
  set C := clampVal hF.1 a with hC
  have hstep : ∀ i, |C (i + 1) - C i| ≤ 1 := clampVal_step hF.1 a ha
  set e : ℕ → ℕ := fun i => (s * (C i - C j)).toNat with he_def
  have he : ∀ i, j ≤ i → i < k → (e i : ℤ) = s * (C i - C j) := fun i h1 h2 =>
    Int.toNat_of_nonneg (hext i h1 h2)
  have hej : e j = 0 := by simp [he_def]
  -- the largest value of `e` on the tail
  obtain ⟨iM, hiM, hM⟩ := (Finset.Ico j k).exists_max_image e ⟨j, by simp; omega⟩
  simp only [Finset.mem_Ico] at hiM
  have hM' : ∀ i, j ≤ i → i < k → e i ≤ e iM := fun i h1 h2 => hM i (by simp; omega)
  set E := e iM with hE
  -- every value `0..E` is taken on the tail
  have hsurjE : ∀ c ≤ E, ∃ i, j ≤ i ∧ i ≤ iM ∧ e i = c := by
    intro c hc
    rcases eq_or_lt_of_le hc with h | h
    · exact ⟨iM, hiM.1, le_rfl, h.symm⟩
    set g : ℕ → ℤ := fun i => s * (C i - C j) with hg
    have hgstep : ∀ i, |g (i + 1) - g i| ≤ 1 := by
      intro i
      have := hstep i
      simp only [hg]
      rcases hs with rfl | rfl
      · simpa [abs_le] using this
      · rw [abs_le] at this ⊢; constructor <;> linarith [this.1, this.2]
    have hgj : g j = 0 := by simp [hg]
    have hgM : g iM = E := by rw [hE, he iM hiM.1 hiM.2]
    obtain ⟨t, ht1, ht2, hc'⟩ := exists_adjacent_cross hgstep (a := j) (b := iM)
      (p := (c : ℤ)) (by rw [hgj]; positivity) (by rw [hgM]; omega)
    rw [min_eq_left hiM.1] at ht1
    rw [max_eq_right hiM.1] at ht2
    rcases hc' with ⟨e1, -⟩ | ⟨-, e2⟩
    · refine ⟨t, ht1, by omega, ?_⟩
      have := he t ht1 (by omega)
      simp only [hg] at e1
      omega
    · refine ⟨t + 1, by omega, ht2, ?_⟩
      have := he (t + 1) (by omega) (by omega)
      simp only [hg] at e2
      omega
  -- counting: `E + 1 < k - j`
  have hcount : E + 1 + j < k := by
    have hsub : Finset.range (E + 1) ⊆ ((Finset.Ico j k).erase i₂).image e := by
      intro c hc
      rw [Finset.mem_range] at hc
      obtain ⟨i, hi1, hi2, hic⟩ := hsurjE c (by omega)
      rw [Finset.mem_image]
      by_cases hii : i = i₂
      · refine ⟨i₁, by simp; omega, ?_⟩
        rw [← hic, hii]
        simp only [he_def, hrep]
      · exact ⟨i, by simp; omega, hic⟩
    have := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_range, Finset.card_erase_of_mem (by simp; omega), Nat.card_Ico] at this
    omega
  -- the block map
  set k' := j + E + 1 with hk'
  have hβlt : ∀ i : Fin k, ¬ i.val < j → j + e i < k' := fun i hi => by
    have := hM' i (by omega) i.isLt; omega
  let β : Fin k → Fin k' := fun i =>
    if h : i.val < j then ⟨i.val, by omega⟩ else ⟨j + e i, hβlt i h⟩
  have hβval : ∀ i : Fin k, (β i).val = if i.val < j then i.val else j + e i := fun i => by
    by_cases h : i.val < j <;> simp [β, h]
  have hβ0 : ∀ i : Fin k, i.val = 0 → (β i).val = 0 := fun i hi => by
    rw [hβval]
    by_cases h : i.val < j
    · rw [if_pos h, hi]
    · have : (i : ℕ) = j := by omega
      rw [if_neg h, this, hej]
      omega
  have hβ : Chain.IsBlockMap β := by
    constructor
    · intro u
      by_cases hu : u.val < j
      · exact ⟨⟨u.val, by omega⟩, Fin.ext (by rw [hβval]; simp [hu])⟩
      · obtain ⟨i, hi1, hi2, hic⟩ := hsurjE (u.val - j) (by omega)
        refine ⟨⟨i, by omega⟩, Fin.ext ?_⟩
        rw [hβval]
        simp only [show ¬ i < j by omega, if_false]
        omega
    · intro t t' htt'
      rw [hβval, hβval]
      by_cases h1 : t'.val < j
      · simp only [h1, show t.val < j by omega, if_true]; omega
      by_cases h2 : t.val < j
      · have : t'.val = j := by omega
        simp only [h1, h2, if_true, if_false]
        rw [this, hej]; omega
      simp only [h1, h2, if_false]
      have e1 := he t (by omega) t.isLt
      have e2 := he t' (by omega) t'.isLt
      have hs1 := hstep t.val
      rw [← htt'] at hs1
      rw [abs_le] at hs1
      rcases hs with rfl | rfl <;> omega
  -- equal block, equal `D`-index
  have hfib : ∀ t t' : Fin k, β t = β t' → a t = a t' := by
    intro t t' htt
    have hv := congrArg Fin.val htt
    rw [hβval, hβval] at hv
    by_cases h1 : t.val < j <;> by_cases h2 : t'.val < j <;>
      simp only [h1, h2, if_true, if_false] at hv
    · exact congrArg a (Fin.ext hv)
    · omega
    · omega
    · have e1 := he t (by omega) t.isLt
      have e2 := he t' (by omega) t'.isLt
      have c1 := clampVal_of_lt hF.1 a t.isLt
      have c2 := clampVal_of_lt hF.1 a t'.isLt
      have hCC : C t = C t' := by
        have : (e t : ℤ) = e t' := by exact_mod_cast (show e t = e t' by omega)
        rcases hs with rfl | rfl <;> omega
      apply Fin.ext
      rw [hC] at hCC
      rw [c1, c2] at hCC
      exact_mod_cast hCC
  set G := F.ofBlocks β hβ with hG
  refine ⟨k', by omega, G, by omega, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hKF hx)
    refine mem_iUnion.mpr ⟨β i, ?_⟩
    rw [hG, Chain.ofBlocks_link]
    exact mem_iUnion₂.mpr ⟨i, rfl, hi⟩
  · intro u
    obtain ⟨t, ht⟩ := hβ.surj u
    refine ⟨a t, fun x hx => ?_⟩
    rw [hG, Chain.ofBlocks_link] at hx
    obtain ⟨t', ht', hx⟩ := mem_iUnion₂.mp hx
    have : a t' = a t := hfib t' t (by rw [ht]; exact ht')
    rw [← this]
    exact ha t' hx
  · rw [hG, Chain.ofBlocks_link]
    refine mem_iUnion₂.mpr ⟨⟨0, hF.1⟩, ?_, hp0⟩
    exact Fin.ext (hβ0 _ rfl)
  · intro u hu hcl
    rw [hG, Chain.ofBlocks_link, (Set.toFinite _).closure_biUnion] at hcl
    obtain ⟨t, ht, hcl⟩ := mem_iUnion₂.mp hcl
    have ht' : β t = u := ht
    refine hpF t (fun h0 => hu ?_) hcl
    rw [← ht']
    exact hβ0 t h0

/-- **The last-link claim** (Bing: "the last link of `F` intersects `M''·(d₁ + d_m)` or else a
chain with fewer links than `F` with the required properties covers `M''`"; Fugate, Lemma 1,
p. 462). Let `K` be a nondegenerate set meeting every link of `D` (`m ≥ 2`), and `F` a
Theorem-10 chain for `K` from `p` refining `D` **of least length** among such chains. Then the
last link of `F` meets `K ∩ (D_0 ∪ D_{m−1})` at a point other than `p`.

Shape change from the skeleton: the hypothesis `K.Nontrivial` is added (the skeleton's form is
false for `K = {p}`, see `lastLink_of_minimal_skeleton_false`); the hypotheses that `K` is a
continuum and contains `p` are not used and have been removed. -/
theorem lastLink_of_minimal {m : ℕ} (D : Chain X m) (hm : 2 ≤ m) {K : Set X}
    (hKnt : K.Nontrivial) (hmeet : ∀ i, (D.link i ∩ K).Nonempty) {p : X}
    {k : ℕ} (F : Chain X k) (hF : IsT10Chain D K p F)
    (hmin : ∀ (k' : ℕ) (F' : Chain X k'), IsT10Chain D K p F' → k ≤ k') :
    ∃ y ∈ K, y ≠ p ∧ y ∈ F.link ⟨k - 1, by have := hF.1; omega⟩ ∧
      (y ∈ D.link ⟨0, by omega⟩ ∨ y ∈ D.link ⟨m - 1, by omega⟩) := by
  classical
  have hF' := hF
  obtain ⟨hk, hKF, hFD, hp0, hpF⟩ := hF
  by_contra hno
  push_neg at hno
  obtain ⟨a, ha⟩ : ∃ a : Fin k → Fin m, ∀ i, F.link i ⊆ D.link (a i) :=
    ⟨fun i => (hFD i).choose, fun i => (hFD i).choose_spec⟩
  have hcov : ∀ x ∈ K, ∃ i, x ∈ F.link i := fun x hx => mem_iUnion.mp (hKF hx)
  -- a point `y ≠ p` of `K` in the last link
  have hy : ∃ y ∈ K, y ≠ p ∧ y ∈ F.link ⟨k - 1, by omega⟩ := by
    by_cases hk1 : k = 1
    · obtain ⟨x, hx, hxp⟩ := hKnt.exists_ne p
      obtain ⟨i, hi⟩ := hcov x hx
      have : i = ⟨k - 1, by omega⟩ := Fin.ext (by have := i.isLt; omega)
      exact ⟨x, hx, hxp, this ▸ hi⟩
    · by_contra hne
      push_neg at hne
      have hmiss : ∀ x ∈ K, x ∉ F.link ⟨k - 1, by omega⟩ := fun x hx hxl => by
        by_cases hxp : x = p
        · subst hxp
          exact hpF ⟨k - 1, by omega⟩ (by simp only []; omega) (subset_closure hxl)
        · exact hne x hx hxp hxl
      -- drop the last link
      have hle : (⟨0, by omega⟩ : Fin k) ≤ ⟨k - 2, by omega⟩ := Fin.mk_le_mk.mpr (Nat.zero_le _)
      set F' := F.sub ⟨0, by omega⟩ ⟨k - 2, by omega⟩ hle with hF'def
      have hT : IsT10Chain D K p F' := by
        refine ⟨by omega, fun x hx => ?_, fun t => ⟨a _, ha _⟩, ?_, fun t ht hcl => ?_⟩
        · obtain ⟨i, hi⟩ := hcov x hx
          have hik : i.val ≤ k - 2 := by
            by_contra h
            have : i = ⟨k - 1, by omega⟩ := Fin.ext (by have := i.isLt; show i.val = k - 1; omega)
            exact hmiss x hx (this ▸ hi)
          refine mem_iUnion.mpr ⟨⟨i.val, by simp only []; omega⟩, ?_⟩
          show x ∈ F.link ⟨0 + i.val, _⟩
          simpa using hi
        · show p ∈ F.link ⟨0 + 0, _⟩
          simpa using hp0
        · exact hpF ⟨0 + t.val, by omega⟩ (by simp only []; omega) hcl
      have : k ≤ k - 2 - 0 + 1 := hmin _ F' hT
      omega
  obtain ⟨y, hyK, hyp, hyl⟩ := hy
  set r := a ⟨k - 1, by omega⟩ with hr
  have hyr : y ∈ D.link r := ha _ hyl
  obtain ⟨hy0, hym⟩ := hno y hyK hyp hyl
  have hr0 : r.val ≠ 0 := fun h => hy0 (by convert hyr using 2; exact Fin.ext h.symm)
  have hrm : r.val ≠ m - 1 := fun h => hym (by convert hyr using 2; exact Fin.ext h.symm)
  have hrlt := r.isLt
  -- the two end links of `D` are disjoint
  have hdisj : ∀ z, z ∈ D.link ⟨0, by omega⟩ → z ∉ D.link ⟨m - 1, by omega⟩ := fun z h1 h2 => by
    have := (D.adjacent_iff ⟨0, by omega⟩ ⟨m - 1, by omega⟩).mp ⟨z, h1, h2⟩
    simp only [] at this
    omega
  obtain ⟨z0, hz0d, hz0K⟩ := hmeet ⟨0, by omega⟩
  obtain ⟨z1, hz1d, hz1K⟩ := hmeet ⟨m - 1, by omega⟩
  obtain ⟨i0, hi0⟩ := hcov z0 hz0K
  obtain ⟨i1, hi1⟩ := hcov z1 hz1K
  have hz01 : z0 ≠ z1 := fun h => hdisj z0 hz0d (h ▸ hz1d)
  -- `p` in the last link forces `k = 1`
  have hpl : p ∈ F.link ⟨k - 1, by omega⟩ → k = 1 := fun h => by
    by_contra hk1
    exact hpF ⟨k - 1, by omega⟩ (by simp only []; omega) (subset_closure h)
  have hlast : ∀ i : Fin k, i.val = k - 1 → F.link i = F.link ⟨k - 1, by omega⟩ := fun i hi => by
    rw [show i = ⟨k - 1, by omega⟩ from Fin.ext hi]
  have hi0l : i0.val ≠ k - 1 ∧ i1.val ≠ k - 1 := by
    by_contra hcon
    rw [not_and_or, not_not, not_not] at hcon
    rcases hcon with h | h
    · have hz0l : z0 ∈ F.link ⟨k - 1, by omega⟩ := hlast i0 h ▸ hi0
      by_cases hz0p : z0 = p
      · have hk1 := hpl (hz0p ▸ hz0l)
        have hz1l : z1 ∈ F.link ⟨k - 1, by omega⟩ := hlast i1 (by have := i1.isLt; omega) ▸ hi1
        exact (hno z1 hz1K (fun h => hz01 (hz0p.trans h.symm)) hz1l).2 hz1d
      · exact (hno z0 hz0K hz0p hz0l).1 hz0d
    · have hz1l : z1 ∈ F.link ⟨k - 1, by omega⟩ := hlast i1 h ▸ hi1
      by_cases hz1p : z1 = p
      · have hk1 := hpl (hz1p ▸ hz1l)
        have hz0l : z0 ∈ F.link ⟨k - 1, by omega⟩ := hlast i0 (by have := i0.isLt; omega) ▸ hi0
        exact (hno z0 hz0K (fun h => hz01 (h.trans hz1p.symm)) hz0l).1 hz0d
      · exact (hno z1 hz1K hz1p hz1l).2 hz1d
  -- the `D`-indices at the two points
  have ha0 : (a i0).val ≤ 1 := by
    have := (D.adjacent_iff (a i0) ⟨0, by omega⟩).mp ⟨z0, ha _ hi0, hz0d⟩
    simp only [] at this; omega
  have ha1 : m - 2 ≤ (a i1).val := by
    have := (D.adjacent_iff (a i1) ⟨m - 1, by omega⟩).mp ⟨z1, ha _ hi1, hz1d⟩
    simp only [] at this; omega
  set C := clampVal hk a with hC
  have hstep := clampVal_step hk a ha
  have hC0 : C i0 = (a i0 : ℕ) := clampVal_of_lt hk a i0.isLt
  have hC1 : C i1 = (a i1 : ℕ) := clampVal_of_lt hk a i1.isLt
  have hCN : C (k - 1) = (r : ℕ) := clampVal_of_lt hk a (by omega)
  have hi0k := i0.isLt
  have hi1k := i1.isLt
  have hbet : ∃ u v, u ≤ v ∧ v < k - 1 ∧
      ((C u ≤ C (k - 1) ∧ C (k - 1) ≤ C v) ∨ (C v ≤ C (k - 1) ∧ C (k - 1) ≤ C u)) := by
    rcases le_total i0.val i1.val with h | h
    · exact ⟨i0, i1, h, by omega, Or.inl ⟨by omega, by omega⟩⟩
    · exact ⟨i1, i0, h, by omega, Or.inr ⟨by omega, by omega⟩⟩
  obtain ⟨u, v, huv, hvN, hbet⟩ := hbet
  obtain ⟨j, hjN, hext, i, hji, hiN, hgi⟩ := exists_extreme_repeat hstep huv hvN hbet
  have hshort : ∃ k' < k, ∃ G : Chain X k', IsT10Chain D K p G := by
    rcases hext with hext | hext
    · exact exists_shorter_T10Chain hF' a ha (j := j) (by omega) (s := 1) (Or.inl rfl)
        (fun i' h1 h2 => by have := hext i' h1 (by omega); simp only [one_mul]; linarith)
        hji hiN (by omega) hgi
    · exact exists_shorter_T10Chain hF' a ha (j := j) (by omega) (s := -1) (Or.inr rfl)
        (fun i' h1 h2 => by have := hext i' h1 (by omega); linarith)
        hji hiN (by omega) hgi
  obtain ⟨k', hk', G, hG⟩ := hshort
  have := hmin k' G hG
  omega

/-- **Item 3.** A Theorem-10 chain of least length exists as soon as one exists. -/
theorem exists_minimal_T10Chain {m : ℕ} (D : Chain X m) (K : Set X) (p : X)
    (h : ∃ (k : ℕ) (F : Chain X k), IsT10Chain D K p F) :
    ∃ (k : ℕ) (F : Chain X k), IsT10Chain D K p F ∧
      ∀ (k' : ℕ) (F' : Chain X k'), IsT10Chain D K p F' → k ≤ k' := by
  classical
  obtain ⟨F, hF⟩ := Nat.find_spec h
  exact ⟨Nat.find h, F, hF, fun k' F' hF' => Nat.find_min' h ⟨F', hF'⟩⟩

/-! ### Assembly of Theorem 10 -/

/-- A nested intersection of compact preconnected sets is preconnected. (The batch-13 lemma
`T14.isPreconnected_sInter_chain` assumes a compact ambient space; this version does not.) -/
theorem isPreconnected_sInter_chain' {c : Set (Set X)} (hne : c.Nonempty)
    (hch : IsChain (· ⊆ ·) c) (hcpt : ∀ W ∈ c, IsCompact W) (hconn : ∀ W ∈ c, IsPreconnected W) :
    IsPreconnected (⋂₀ c) := by
  obtain ⟨W₀, hW₀⟩ := hne
  have hclosed : IsClosed (⋂₀ c) := isClosed_sInter fun W hW => (hcpt W hW).isClosed
  have hcK : IsCompact (⋂₀ c) := (hcpt W₀ hW₀).of_isClosed_subset hclosed (sInter_subset_of_mem hW₀)
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hclosed]
  intro u v hu hv hsub hdisj
  set u' := u ∩ ⋂₀ c with hu'_def
  set v' := v ∩ ⋂₀ c with hv'_def
  have hu' : IsCompact u' := hcK.inter_left hu
  have hv' : IsClosed v' := hv.inter hclosed
  have hdisj' : Disjoint u' v' := hdisj.mono inter_subset_left inter_subset_left
  have hsub' : ⋂₀ c ⊆ u' ∪ v' := fun x hx =>
    (hsub hx).imp (fun h => ⟨h, hx⟩) (fun h => ⟨h, hx⟩)
  obtain ⟨δ, hδ, hδd⟩ := hdisj'.exists_thickenings hu' hv'
  have hopen : IsOpen (Metric.thickening δ u' ∪ Metric.thickening δ v') :=
    Metric.isOpen_thickening.union Metric.isOpen_thickening
  haveI : Nonempty c := ⟨⟨W₀, hW₀⟩⟩
  obtain ⟨⟨W, hWc⟩, hW⟩ : ∃ i : c, (i : Set X) ⊆ Metric.thickening δ u' ∪ Metric.thickening δ v' := by
    refine exists_subset_nhds_of_isCompact' (V := fun i : c => (i : Set X)) ?_
      (fun i => hcpt _ i.2) (fun i => (hcpt _ i.2).isClosed) ?_
    · intro i j
      rcases hch.total i.2 j.2 with h | h
      · exact ⟨i, le_rfl, h⟩
      · exact ⟨j, h, le_rfl⟩
    · intro x hx
      refine hopen.mem_nhds ?_
      have hx' : x ∈ ⋂₀ c := by
        rw [sInter_eq_iInter]; simpa using hx
      rcases hsub' hx' with h | h
      · exact Or.inl (Metric.self_subset_thickening hδ _ h)
      · exact Or.inr (Metric.self_subset_thickening hδ _ h)
  have hLW : ⋂₀ c ⊆ W := sInter_subset_of_mem hWc
  rcases isPreconnected_iff_subset_of_disjoint.mp (hconn W hWc) _ _ Metric.isOpen_thickening
      Metric.isOpen_thickening hW (by
        rw [hδd.inter_eq]; exact inter_empty _) with h | h
  · left
    intro z hz
    rcases hsub' hz with h' | h'
    · exact h'.1
    · exact absurd ⟨h (hLW hz), Metric.self_subset_thickening hδ _ h'⟩ (fun h2 => hδd.le_bot h2)
  · right
    intro z hz
    rcases hsub' hz with h' | h'
    · exact absurd ⟨Metric.self_subset_thickening hδ _ h', h (hLW hz)⟩ (fun h2 => hδd.le_bot h2)
    · exact h'.1

/-- A set covered by the links `a..b` of `D` is covered by the subchain `D(a..b)`. -/
theorem subset_sub_union {m : ℕ} (D : Chain X m) {a b : Fin m} (hab : a ≤ b) {M : Set X}
    (h : ∀ x ∈ M, ∃ i : Fin m, a.val ≤ i.val ∧ i.val ≤ b.val ∧ x ∈ D.link i) :
    M ⊆ (D.sub a b hab).union := by
  intro x hx
  obtain ⟨i, h1, h2, hi⟩ := h x hx
  refine mem_iUnion.mpr ⟨⟨i.val - a.val, by omega⟩, ?_⟩
  show x ∈ D.link ⟨a.val + (i.val - a.val), _⟩
  convert hi using 2
  ext
  simp only []
  omega

/-- A refinement of a subchain of `D` refines `D`. -/
theorem refines_of_refines_sub {m n : ℕ} {D : Chain X m} {a b : Fin m} {hab : a ≤ b}
    {E : Chain X n} (h : E.Refines (D.sub a b hab)) : E.Refines D := fun i => by
  obtain ⟨j, hj⟩ := h i
  exact ⟨_, hj⟩

/-- **Theorem 10, the induction.** Strong induction on the length of `D`; inside, a minimal
counterexample `M'` (Zorn), which meets every link of `D` (else a shorter subchain covers it), is
nondegenerate, and contains a proper nondegenerate subcontinuum `K ∋ p` meeting every link; `K`
has a Theorem-10 chain by minimality, a least one has its last link through
`K ∩ (D_0 ∪ D_{m-1}) ∖ {p}` (`lastLink_of_minimal`), and Bing's surgery
(`theorem10_1951_of_lastLink`, batch 91) gives one for `M'`. -/
theorem theorem10_aux (p : X) : ∀ (m : ℕ) (D : Chain X m) (M : Set X), Fold.Q78.IsContinuum M →
    M ⊆ D.union → CondA M p → ∃ (n : ℕ) (E : Chain X n), IsT10Chain D M p E := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro D M hM hD hp
  by_contra hfail
  set S : Set (Set X) := {W | W ⊆ M ∧ Fold.Q78.IsContinuum W ∧ p ∈ W ∧
    ¬ ∃ (n : ℕ) (E : Chain X n), IsT10Chain D W p E} with hS
  obtain ⟨M', -, hM'min⟩ := zorn_superset_nonempty S (fun c hcS hch hne => by
    refine ⟨⋂₀ c, ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩, fun W hW => sInter_subset_of_mem hW⟩
    · obtain ⟨W, hW⟩ := hne
      exact (sInter_subset_of_mem hW).trans (hcS hW).1
    · obtain ⟨W, hW⟩ := hne
      exact (hcS hW).2.1.1.of_isClosed_subset
        (isClosed_sInter fun W hW => (hcS hW).2.1.1.isClosed) (sInter_subset_of_mem hW)
    · exact ⟨⟨p, mem_sInter.mpr fun W hW => (hcS hW).2.2.1⟩,
        isPreconnected_sInter_chain' hne hch (fun W hW => (hcS hW).2.1.1)
          (fun W hW => (hcS hW).2.1.2.isPreconnected)⟩
    · exact mem_sInter.mpr fun W hW => (hcS hW).2.2.1
    · rintro ⟨n, E, hn, hcov, hrest⟩
      haveI : Nonempty c := hne.to_subtype
      obtain ⟨⟨W, hWc⟩, hW⟩ := exists_subset_nhds_of_isCompact'
        (V := fun i : c => (i : Set X)) (U := E.union)
        (fun i j => by
          rcases hch.total i.2 j.2 with h | h
          · exact ⟨i, le_rfl, h⟩
          · exact ⟨j, h, le_rfl⟩)
        (fun i => (hcS i.2).2.1.1) (fun i => (hcS i.2).2.1.1.isClosed)
        (fun x hx => (isOpen_iUnion E.isOpen).mem_nhds
          (hcov (by rw [sInter_eq_iInter]; simpa using hx)))
      exact (hcS hWc).2.2.2 ⟨n, E, hn, hW, hrest⟩) M ⟨subset_rfl, hM, hp.1, hfail⟩
  obtain ⟨hM'M, hM'c, hpM', hM'fail⟩ := hM'min.1
  have hA' : CondA M' p := ⟨hpM', fun W hW => hp.2 W (hW.trans hM'M)⟩
  have hM'D : M' ⊆ D.union := hM'M.trans hD
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp (hM'D hpM')
  have hm0 : 0 < m := i₀.pos
  have hloc : ∀ x ∈ M', ∃ i : Fin m, x ∈ D.link i := fun x hx => mem_iUnion.mp (hM'D hx)
  -- `M'` meets the two end links of `D`
  have hend0 : (M' ∩ D.link ⟨0, hm0⟩).Nonempty := by
    by_contra h0
    rw [not_nonempty_iff_eq_empty] at h0
    have hm2 : 2 ≤ m := by
      by_contra hm2
      have : i₀ = ⟨0, hm0⟩ := Fin.ext (by have := i₀.isLt; omega)
      exact (eq_empty_iff_forall_notMem.mp h0) p ⟨hpM', this ▸ hi₀⟩
    have hle : (⟨1, by omega⟩ : Fin m) ≤ ⟨m - 1, by omega⟩ := Fin.mk_le_mk.mpr (by omega)
    obtain ⟨n, E, hn, hcovE, hED, hrest⟩ := IH _ (by simp only []; omega)
      (D.sub ⟨1, by omega⟩ ⟨m - 1, by omega⟩ hle) M' hM'c
      (subset_sub_union D hle fun x hx => by
        obtain ⟨i, hi⟩ := hloc x hx
        refine ⟨i, ?_, by simp only []; omega, hi⟩
        by_contra h
        have : i = ⟨0, hm0⟩ := Fin.ext (by simp only [] at h ⊢; omega)
        exact (eq_empty_iff_forall_notMem.mp h0) x ⟨hx, this ▸ hi⟩) hA'
    exact hM'fail ⟨n, E, hn, hcovE, refines_of_refines_sub hED, hrest⟩
  have hend1 : (M' ∩ D.link ⟨m - 1, by omega⟩).Nonempty := by
    by_contra h0
    rw [not_nonempty_iff_eq_empty] at h0
    have hm2 : 2 ≤ m := by
      by_contra hm2
      have : i₀ = ⟨m - 1, by omega⟩ := Fin.ext (by have := i₀.isLt; simp only []; omega)
      exact (eq_empty_iff_forall_notMem.mp h0) p ⟨hpM', this ▸ hi₀⟩
    have hle : (⟨0, by omega⟩ : Fin m) ≤ ⟨m - 2, by omega⟩ := Fin.mk_le_mk.mpr (by omega)
    obtain ⟨n, E, hn, hcovE, hED, hrest⟩ := IH _ (by simp only []; omega)
      (D.sub ⟨0, by omega⟩ ⟨m - 2, by omega⟩ hle) M' hM'c
      (subset_sub_union D hle fun x hx => by
        obtain ⟨i, hi⟩ := hloc x hx
        refine ⟨i, by simp only []; omega, ?_, hi⟩
        by_contra h
        have : i = ⟨m - 1, by omega⟩ := Fin.ext (by have := i.isLt; simp only [] at h ⊢; omega)
        exact (eq_empty_iff_forall_notMem.mp h0) x ⟨hx, this ▸ hi⟩) hA'
    exact hM'fail ⟨n, E, hn, hcovE, refines_of_refines_sub hED, hrest⟩
  -- hence every link
  have hmeet : ∀ i, (D.link i ∩ M').Nonempty := by
    intro i
    rw [inter_comm]
    by_cases hi0 : i.val = 0
    · rwa [show i = ⟨0, hm0⟩ from Fin.ext hi0]
    by_cases hi1 : i.val = m - 1
    · rwa [show i = ⟨m - 1, by omega⟩ from Fin.ext hi1]
    exact D.inter_link_nonempty_between hM'c.2.isPreconnected hM'D
      (show (⟨0, hm0⟩ : Fin m) < i from Fin.mk_lt_mk.mpr (by omega))
      (show i < ⟨m - 1, by omega⟩ from Fin.lt_def.mpr (by simp only []; omega)) hend0 hend1
  -- `m ≥ 2`: a one-link chain is its own Theorem-10 chain
  have hm2 : 2 ≤ m := by
    by_contra hm2
    refine hM'fail ⟨m, D, hm0, hM'D, fun i => ⟨i, subset_rfl⟩, ?_, fun j hj => ?_⟩
    · rwa [show i₀ = ⟨0, hm0⟩ from Fin.ext (by have := i₀.isLt; omega)] at hi₀
    · exact absurd (j.isLt) (by omega)
  -- `M'` is nondegenerate: `{p}` has the one-link chain `D(i₀..i₀)`
  have hnt : M'.Nontrivial := by
    by_contra hnt
    rw [not_nontrivial_iff] at hnt
    have hM'p : M' = {p} := hnt.eq_singleton_of_mem hpM'
    refine hM'fail ⟨_, D.sub i₀ i₀ le_rfl, by omega, ?_, refines_of_refines_sub
      (fun i => ⟨i, subset_rfl⟩), ?_, fun j hj => absurd j.isLt (by omega)⟩
    · rw [hM'p]
      refine singleton_subset_iff.mpr (mem_iUnion.mpr ⟨⟨0, by omega⟩, ?_⟩)
      show p ∈ D.link ⟨i₀.val + 0, _⟩
      simpa using hi₀
    · show p ∈ D.link ⟨i₀.val + 0, _⟩
      simpa using hi₀
  -- a proper nondegenerate subcontinuum through `p` meeting every link
  have hB : CondB M' p := condB_of_condA hA'
  obtain ⟨K₁, hK₁M, hK₁ne, hK₁c, hpK₁, hK₁meet⟩ := exists_proper_meeting_all_links hM'c hnt hA' D hmeet
  obtain ⟨K₂, hK₂M, hK₂ne, hK₂c, hpK₂, z, hzK₂, hzp⟩ := exists_proper_subcontinuum_meeting hM'c hnt
    hpM' (isOpen_compl_singleton (x := p))
    (by obtain ⟨x, hx, hxp⟩ := hnt.exists_ne p; exact ⟨x, hxp, hx⟩)
  have hK : ∃ K : Set X, K ⊆ M' ∧ K ≠ M' ∧ Fold.Q78.IsContinuum K ∧ p ∈ K ∧
      (∀ i, (D.link i ∩ K).Nonempty) ∧ K.Nontrivial := by
    rcases hB.2 K₁ K₂ hK₁M hK₂M hK₁c hK₂c hpK₁ hpK₂ with h | h
    · exact ⟨K₂, hK₂M, hK₂ne, hK₂c, hpK₂, fun i => (hK₁meet i).mono (inter_subset_inter_right _ h),
        ⟨z, hzK₂, p, hpK₂, hzp⟩⟩
    · exact ⟨K₁, hK₁M, hK₁ne, hK₁c, hpK₁, hK₁meet, ⟨z, h hzK₂, p, hpK₁, hzp⟩⟩
  obtain ⟨K, hKM, hKne, hKc, hpK, hKmeet, hKnt⟩ := hK
  -- `K` has a Theorem-10 chain, by minimality of `M'`
  have hKT : ∃ (n : ℕ) (E : Chain X n), IsT10Chain D K p E := by
    by_contra hKT
    exact hKne (Subset.antisymm hKM (hM'min.2 ⟨hKM.trans hM'M, hKc, hpK, hKT⟩ hKM))
  obtain ⟨k, F, hF, hmin⟩ := exists_minimal_T10Chain D K p hKT
  obtain ⟨y, hyK, hyp, hyF, hyD⟩ := lastLink_of_minimal D hm2 hKnt hKmeet F hF hmin
  obtain ⟨hk, hKF, hFD, hp0, hpF⟩ := hF
  rcases hyD with hyD | hyD
  · obtain ⟨n, E, hn, h⟩ := theorem10_1951_of_lastLink hM'c D hM'D hB hKM hKc hpK F hk hKF hFD
      hp0 hpF hm0 hyK hyF hyD hyp
    exact hM'fail ⟨n, E, hn, h⟩
  · obtain ⟨n, E, hn, h⟩ := theorem10_1951_of_lastLink' hM'c D hM'D hB hKM hKc hpK F hk hKF hFD
      hp0 hpF hm0 hyK hyF hyD hyp
    exact hM'fail ⟨n, E, hn, h⟩

/-- **Item 4. Theorem 10** (Bing 1951, p. 659). If `D` covers the continuum `M` and `p ∈ M`
satisfies condition A, some refinement `E` of `D` covers `M` with `p` in its first link and in
the closure of no other link. -/
theorem theorem10_1951 {M : Set X} (hM : Fold.Q78.IsContinuum M) {m : ℕ} (D : Chain X m)
    (hD : M ⊆ D.union) {p : X} (hp : CondA M p) :
    ∃ (n : ℕ) (E : Chain X n) (hn : 0 < n), M ⊆ E.union ∧ E.Refines D ∧
      p ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (E.link j) := by
  obtain ⟨n, E, hn, h⟩ := theorem10_aux p m D M hM hD hp
  exact ⟨n, E, hn, h⟩

@[inherit_doc theorem10_1951] alias theorem10_1951' := theorem10_1951

/-- **Theorem 13, sufficiency for condition A**: in a snake-like continuum a point satisfying
condition A is an end point (via Theorem 10). Batch 100 moved it here from `EndPoints51.lean`, which
cannot import this file (`Surgery91.lean`, used here, imports `EndPoints51.lean`). -/
theorem endPoint_of_condA {M : Set X} (hM : IsSnakeLike M) {p : X} (hp : CondA M p) :
    IsEndPoint M p := by
  refine ⟨hp.1, fun ε hε => ?_⟩
  obtain ⟨m, D, hDε, hMD⟩ := hM.2 ε hε
  obtain ⟨n, E, hn, hME, hED, hp0, hpj⟩ := theorem10_1951 hM.1 D hMD hp
  refine ⟨n, E, hn, fun i => ?_, hME, hp0, fun j hj h => hpj j hj (subset_closure h)⟩
  obtain ⟨k, hk⟩ := hED i
  exact ⟨(hDε k).1.subset hk, (Metric.diam_mono hk (hDε k).1).trans_lt (hDε k).2⟩

@[inherit_doc endPoint_of_condA] alias endPoint_of_condA' := endPoint_of_condA

/-! ### The skeleton's form of the last-link claim is false for `K = {p}` -/

/-- The chain of `n ≤ 2` links all equal to `ℝ`. -/
def univChainR (n : ℕ) (hn : n ≤ 2) : Chain ℝ n where
  link _ := univ
  isOpen _ := isOpen_univ
  adjacent i j := by
    simp only [inter_self, univ_nonempty, true_iff]
    have := i.isLt; have := j.isLt
    omega

/-- **Refutation of the skeleton's `lastLink_of_minimal`.** With `D = (ℝ, ℝ)`, `K = {0}`,
`p = 0` and `F = (ℝ)`, every hypothesis holds (`F` has the least possible length, one), but no
point of `K` differs from `p`. -/
theorem lastLink_of_minimal_skeleton_false :
    ¬ ∀ {m : ℕ} (D : Chain ℝ m) (hm : 2 ≤ m) {K : Set ℝ},
      Fold.Q78.IsContinuum K → (∀ i, (D.link i ∩ K).Nonempty) → ∀ {p : ℝ}, p ∈ K →
      ∀ {k : ℕ} (F : Chain ℝ k) (hF : IsT10Chain D K p F),
      (∀ (k' : ℕ) (F' : Chain ℝ k'), IsT10Chain D K p F' → k ≤ k') →
      ∃ y ∈ K, y ≠ p ∧ y ∈ F.link ⟨k - 1, by have := hF.1; omega⟩ ∧
        (y ∈ D.link ⟨0, by omega⟩ ∨ y ∈ D.link ⟨m - 1, by omega⟩) := by
  intro h
  have hT : IsT10Chain (univChainR 2 le_rfl) {0} 0 (univChainR 1 (by norm_num)) :=
    ⟨by norm_num, fun x _ => mem_iUnion.mpr ⟨0, trivial⟩, fun i => ⟨0, subset_rfl⟩, trivial,
      fun j hj => absurd (Fin.val_eq_zero j) hj⟩
  obtain ⟨y, hy, hyp, -⟩ := h (univChainR 2 le_rfl) le_rfl
    ⟨isCompact_singleton, isConnected_singleton⟩ (fun i => ⟨0, trivial, rfl⟩) rfl
    (univChainR 1 (by norm_num)) hT (fun k' F' hF' => hF'.1)
  exact hyp hy

end HPC.Plane
