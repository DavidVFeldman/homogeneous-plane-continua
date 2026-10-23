import HPC.Plane.Tree6Thread

/-!
# Batch 118, auxiliary: threading a closed chain of simple arcs through a circular chain

For connected open sets `D 0, …, D (m-1)` (`m ≥ 3`), consecutive ones (cyclically) meeting and no
three of them sharing a point, there are points `P i ∈ D (i-1) ∩ D i` and simple arcs
`A i ⊆ D i` from `P i` to `P (i+1)` (`P m = P 0`) forming a closed chain: consecutive arcs meet
only at their common end (`threaded_nat`).

Choose points `Q i ∈ D (i-1) ∩ D i` and simple arcs `G i ⊆ D i` from `Q i` to `Q (i+1)`; then
trim forward (`trim_chain`): cut the current arc at its first point on `G (i+1)`, and restart
along `G (i+1)` from there; finally close up (`trim_close`): cut the last arc at its first point
on the first one, and start the first one there.
-/

namespace HPC.Plane

open Set Metric

/-- A set that is a simple polygonal arc from `a` to `b` (vertex-function form). -/
def SArcSet (S : Set Pt) (a b : Pt) : Prop :=
  ∃ (v : ℕ → Pt) (n : ℕ), IsSArc v n ∧ v 0 = a ∧ v (n - 1) = b ∧ S = vpath v n

namespace SArcSet

variable {S : Set Pt} {a b : Pt}

theorem isClosed (h : SArcSet S a b) : IsClosed S := by
  obtain ⟨v, n, -, -, -, rfl⟩ := h; exact (isCompact_vpath v n).isClosed

theorem start_mem (h : SArcSet S a b) : a ∈ S := by
  obtain ⟨v, n, hv, rfl, -, rfl⟩ := h; exact hv.start_mem

theorem end_mem (h : SArcSet S a b) : b ∈ S := by
  obtain ⟨v, n, hv, -, rfl, rfl⟩ := h; exact hv.end_mem

theorem first_mem (h : SArcSet S a b) {K : Set Pt} (hK : IsClosed K) (hne : (S ∩ K).Nonempty)
    (ha : a ∉ K) : ∃ x ∈ S ∩ K, ∃ S', SArcSet S' a x ∧ S' ⊆ S ∧ S' ∩ K = {x} := by
  obtain ⟨v, n, hv, rfl, rfl, rfl⟩ := h
  obtain ⟨x, hx, u, k, hu, hu0, hu1, husub, huK⟩ := hv.exists_first_mem hK hne ha
  exact ⟨x, hx, vpath u k, ⟨u, k, hu, hu0, hu1, rfl⟩, husub, huK⟩

theorem suffix (h : SArcSet S a b) {x : Pt} (hx : x ∈ S) (hxb : x ≠ b) :
    ∃ S', SArcSet S' x b ∧ S' ⊆ S := by
  obtain ⟨v, n, hv, rfl, rfl, rfl⟩ := h
  obtain ⟨u, k, hu, hu0, hu1, husub⟩ := hv.exists_suffix hx hxb
  exact ⟨vpath u k, ⟨u, k, hu, hu0, hu1, rfl⟩, husub⟩

end SArcSet

/-- No point in three distinct sets of the family. -/
theorem not_mem_three {m : ℕ} {D : ℕ → Set Pt}
    (hNT : ∀ i j l, i < m → j < m → l < m → i ≠ j → j ≠ l → i ≠ l → D i ∩ D j ∩ D l = ∅)
    {i j l : ℕ} (hi : i < m) (hj : j < m) (hl : l < m) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    {y : Pt} (h1 : y ∈ D i) (h2 : y ∈ D j) (h3 : y ∈ D l) : False := by
  have := hNT i j l hi hj hl hij hjl hil
  exact (this ▸ (⟨⟨h1, h2⟩, h3⟩ : y ∈ D i ∩ D j ∩ D l) : y ∈ (∅ : Set Pt))

/-- The invariant of the forward trimming, after `k` arcs. -/
def TrimInv (D G : ℕ → Set Pt) (Q : ℕ → Pt) (k : ℕ) (A : ℕ → Set Pt) (P : ℕ → Pt)
    (δ : Set Pt) : Prop :=
  P 0 = Q 0 ∧ (∀ i < k, SArcSet (A i) (P i) (P (i + 1)) ∧ A i ⊆ D i) ∧
    (∀ i, i + 1 < k → A i ∩ A (i + 1) = {P (i + 1)}) ∧
    (1 ≤ k → A (k - 1) ∩ δ = {P k}) ∧ SArcSet δ (P k) (Q (k + 1)) ∧ δ ⊆ D k ∧ (G k).Nonempty

/-- **Forward trimming.** -/
theorem trim_chain {m : ℕ} (hm : 3 ≤ m) (D G : ℕ → Set Pt) (Q : ℕ → Pt)
    (hG : ∀ i < m, SArcSet (G i) (Q i) (Q (i + 1)) ∧ G i ⊆ D i) (hQ : Q m = Q 0)
    (hNT : ∀ i j l, i < m → j < m → l < m → i ≠ j → j ≠ l → i ≠ l → D i ∩ D j ∩ D l = ∅) :
    ∀ k, k < m → ∃ A P δ, TrimInv D G Q k A P δ := by
  intro k
  induction k with
  | zero =>
    intro hk
    exact ⟨fun _ => ∅, Q, G 0, rfl, fun i hi => absurd hi (by omega),
      fun i hi => absurd hi (by omega), fun h => absurd h (by omega), (hG 0 hk).1, (hG 0 hk).2,
      ⟨_, (hG 0 hk).1.start_mem⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨A, P, δ, hP0, hA, hcons, hlast, hδ, hδD, -⟩ := ih (by omega)
    obtain ⟨hGk, hGkD⟩ := hG (k + 1) hk
    -- `P k` lies in `D k` and in the previous set
    have hPk : P k ∈ D k := hδD hδ.start_mem
    have hPk' : P k ∈ D (if k = 0 then m - 1 else k - 1) := by
      split_ifs with h0
      · subst h0
        rw [hP0, ← hQ]
        exact (hG (m - 1) (by omega)).2 (by
          have := (hG (m - 1) (by omega)).1.end_mem
          rwa [show m - 1 + 1 = m by omega] at this)
      · have := (hA (k - 1) (by omega)).1.end_mem
        rw [show k - 1 + 1 = k by omega] at this
        exact (hA (k - 1) (by omega)).2 this
    have hPkK : P k ∉ G (k + 1) := by
      intro hmem
      split_ifs at hPk' with h0
      · subst h0
        exact not_mem_three hNT (i := m - 1) (j := 0) (l := 1) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) hPk' hPk (hGkD hmem)
      · exact not_mem_three hNT (i := k - 1) (j := k) (l := k + 1) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) hPk' hPk (hGkD hmem)
    obtain ⟨x, ⟨hxδ, hxG⟩, α, hα, hαδ, hαG⟩ :=
      hδ.first_mem hGk.isClosed ⟨Q (k + 1), hδ.end_mem, hGk.start_mem⟩ hPkK
    have hxQ : x ≠ Q (k + 1 + 1) := by
      intro hxq
      by_cases hk2 : k + 2 < m
      · have h3 : Q (k + 2) ∈ D (k + 2) := (hG (k + 2) hk2).2 (hG (k + 2) hk2).1.start_mem
        rw [← hxq] at h3
        exact not_mem_three hNT (i := k) (j := k + 1) (l := k + 2) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (hδD hxδ) (hGkD hxG) h3
      · have hkm : k + 2 = m := by omega
        have h3 : Q 0 ∈ D 0 := (hG 0 (by omega)).2 (hG 0 (by omega)).1.start_mem
        rw [← hQ, ← hkm, ← hxq] at h3
        exact not_mem_three hNT (i := k) (j := k + 1) (l := 0) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (hδD hxδ) (hGkD hxG) h3
    obtain ⟨δ', hδ', hδ'G⟩ := hGk.suffix hxG hxQ
    refine ⟨fun i => if i < k then A i else α, fun i => if i ≤ k then P i else x, δ', ?_, ?_, ?_,
      ?_, ?_, hδ'G.trans hGkD, ⟨_, hGk.start_mem⟩⟩
    · simp [hP0]
    · intro i hi
      by_cases hik : i < k
      · simp only [hik, if_true, show i ≤ k by omega, show i + 1 ≤ k by omega]
        exact hA i hik
      · have : i = k := by omega
        subst this
        simp only [lt_irrefl, if_false, le_refl, if_true, show ¬ (i + 1 ≤ i) by omega]
        exact ⟨hα, hαδ.trans hδD⟩
    · intro i hi
      by_cases hik : i + 1 < k
      · simp only [show i < k by omega, hik, if_true, show i + 1 ≤ k by omega]
        exact hcons i hik
      · have : i + 1 = k := by omega
        subst this
        simp only [show i < i + 1 by omega, if_true, lt_irrefl, if_false, le_refl]
        apply subset_antisymm
        · intro y hy
          have := hlast (by omega)
          rw [show i + 1 - 1 = i by omega] at this
          exact this ▸ (⟨hy.1, hαδ hy.2⟩ : y ∈ A i ∩ δ)
        · rintro y rfl
          exact ⟨(hA i (by omega)).1.end_mem, hα.start_mem⟩
    · intro _
      beta_reduce
      simp only [show k + 1 - 1 = k by omega, lt_irrefl, if_false, show ¬ (k + 1 ≤ k) by omega]
      apply subset_antisymm
      · intro y hy
        exact hαG ▸ (⟨hy.1, hδ'G hy.2⟩ : y ∈ α ∩ G (k + 1))
      · rintro y rfl
        exact ⟨hα.end_mem, hδ'.start_mem⟩
    · beta_reduce
      simp only [show ¬ (k + 1 ≤ k) by omega, if_false]
      exact hδ'

/-- **Closing up** after the forward trimming. -/
theorem trim_close {m : ℕ} (hm : 3 ≤ m) (D G : ℕ → Set Pt) (Q : ℕ → Pt) (hQ : Q m = Q 0)
    (hNT : ∀ i j l, i < m → j < m → l < m → i ≠ j → j ≠ l → i ≠ l → D i ∩ D j ∩ D l = ∅)
    {A : ℕ → Set Pt} {P : ℕ → Pt} {δ : Set Pt} (hinv : TrimInv D G Q (m - 1) A P δ) :
    ∃ (A' : ℕ → Set Pt) (P' : ℕ → Pt), P' m = P' 0 ∧
      (∀ i < m, SArcSet (A' i) (P' i) (P' (i + 1)) ∧ A' i ⊆ D i) ∧
      (∀ i, i + 1 < m → A' i ∩ A' (i + 1) = {P' (i + 1)}) ∧ A' (m - 1) ∩ A' 0 = {P' 0} := by
  obtain ⟨hP0, hA, hcons, hlast, hδ, hδD, -⟩ := hinv
  rw [show m - 1 + 1 = m by omega, hQ, ← hP0] at hδ
  have hlast := hlast (by omega)
  obtain ⟨hA0, hA0D⟩ := hA 0 (by omega)
  obtain ⟨hA1, hA1D⟩ := hA 1 (by omega)
  have hPm1 : P (m - 1) ∉ A 0 := by
    intro hmem
    have h1 := (hA (m - 2) (by omega)).1.end_mem
    rw [show m - 2 + 1 = m - 1 by omega] at h1
    exact not_mem_three hNT (i := m - 2) (j := m - 1) (l := 0) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) ((hA (m - 2) (by omega)).2 h1) (hδD hδ.start_mem)
      (hA0D hmem)
  obtain ⟨y, ⟨hyδ, hyA⟩, β, hβ, hβδ, hβA⟩ :=
    hδ.first_mem hA0.isClosed ⟨P 0, hδ.end_mem, hA0.start_mem⟩ hPm1
  have hyP1 : y ≠ P (0 + 1) := by
    intro hyp
    exact not_mem_three hNT (i := m - 1) (j := 0) (l := 1) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (hδD hyδ) (hA0D hyA) (hA1D (hyp ▸ hA1.start_mem))
  obtain ⟨α₀, hα₀, hα₀A⟩ := hA0.suffix hyA hyP1
  refine ⟨fun i => if i = 0 then α₀ else if i < m - 1 then A i else β,
    fun i => if i = 0 ∨ i = m then y else P i, by simp, ?_, ?_, ?_⟩
  · intro i hi
    by_cases h0 : i = 0
    · subst h0
      simp only [if_true, true_or, false_or, show 0 + 1 ≠ 0 by omega, show 0 + 1 ≠ m by omega, if_false]
      exact ⟨hα₀, hα₀A.trans hA0D⟩
    · by_cases hi1 : i < m - 1
      · simp only [h0, hi1, if_true, if_false, false_or, show i ≠ m by omega,
          false_or, show i + 1 ≠ m by omega]
        exact hA i hi1
      · have : i = m - 1 := by omega
        subst this
        simp only [h0, lt_irrefl, if_false, false_or, show m - 1 ≠ m by omega,
          show m - 1 + 1 = m by omega, or_true, if_true]
        exact ⟨hβ, hβδ.trans hδD⟩
  · intro i hi
    by_cases h0 : i = 0
    · subst h0
      simp only [if_true, show 0 + 1 < m - 1 by omega, if_false, false_or,
        show 0 + 1 ≠ 0 by omega, show 0 + 1 ≠ m by omega]
      apply subset_antisymm
      · intro z hz
        exact hcons 0 (by omega) ▸ (⟨hα₀A hz.1, hz.2⟩ : z ∈ A 0 ∩ A (0 + 1))
      · rintro z rfl
        exact ⟨hα₀.end_mem, hA1.start_mem⟩
    · by_cases hi1 : i + 1 < m - 1
      · simp only [h0, show i < m - 1 by omega, hi1, if_true, if_false, show i + 1 ≠ 0 by omega,
          false_or, show i + 1 ≠ m by omega]
        exact hcons i hi1
      · have : i = m - 2 := by omega
        subst this
        simp only [h0, show m - 2 < m - 1 by omega, if_true, if_false,
          show m - 2 + 1 ≠ 0 by omega, show ¬ (m - 2 + 1 < m - 1) by omega,
          false_or, show m - 2 + 1 ≠ m by omega]
        rw [show m - 2 + 1 = m - 1 by omega]
        apply subset_antisymm
        · intro z hz
          exact hlast ▸ (⟨by rw [show m - 1 - 1 = m - 2 by omega]; exact hz.1, hβδ hz.2⟩ :
            z ∈ A (m - 1 - 1) ∩ δ)
        · rintro z rfl
          have h1 := (hA (m - 2) (by omega)).1.end_mem
          rw [show m - 2 + 1 = m - 1 by omega] at h1
          exact ⟨h1, hβ.start_mem⟩
  · simp only [show m - 1 ≠ 0 by omega, lt_irrefl, if_false, if_true, true_or]
    apply subset_antisymm
    · intro z hz
      exact hβA ▸ (⟨hz.1, hα₀A hz.2⟩ : z ∈ β ∩ A 0)
    · rintro z rfl
      exact ⟨hβ.end_mem, hα₀.start_mem⟩

/-- Membership of the junction points in two consecutive sets. -/
theorem junction_mem {m : ℕ} (hm : 3 ≤ m) {D A : ℕ → Set Pt} {P : ℕ → Pt} (hPm : P m = P 0)
    (hA : ∀ i < m, SArcSet (A i) (P i) (P (i + 1)) ∧ A i ⊆ D i) {i : ℕ} (hi : i < m) :
    P i ∈ D i ∧ P i ∈ D (if i = 0 then m - 1 else i - 1) := by
  refine ⟨(hA i hi).2 (hA i hi).1.start_mem, ?_⟩
  split_ifs with h0
  · subst h0
    have := (hA (m - 1) (by omega)).1.end_mem
    rw [show m - 1 + 1 = m by omega, hPm] at this
    exact (hA (m - 1) (by omega)).2 this
  · have := (hA (i - 1) (by omega)).1.end_mem
    rw [show i - 1 + 1 = i by omega] at this
    exact (hA (i - 1) (by omega)).2 this

/-- **Threading, `ℕ`-indexed form**, under "no three sets share a point". -/
theorem threaded_nat {m : ℕ} (hm : 3 ≤ m) (D : ℕ → Set Pt) (hopen : ∀ i < m, IsOpen (D i))
    (hconn : ∀ i < m, IsConnected (D i))
    (hne : ∀ i < m, (D (if i = 0 then m - 1 else i - 1) ∩ D i).Nonempty)
    (hNT : ∀ i j l, i < m → j < m → l < m → i ≠ j → j ≠ l → i ≠ l → D i ∩ D j ∩ D l = ∅) :
    ∃ (A : ℕ → Set Pt) (P : ℕ → Pt), P m = P 0 ∧
      (∀ i < m, SArcSet (A i) (P i) (P (i + 1)) ∧ A i ⊆ D i) ∧
      (∀ i, i + 1 < m → A i ∩ A (i + 1) = {P (i + 1)}) ∧ A (m - 1) ∩ A 0 = {P 0} ∧
      (∀ i j, i < j → j < m → P i ≠ P j) := by
  classical
  set Q : ℕ → Pt := fun i => if h : i < m then (hne i h).choose else (hne 0 (by omega)).choose
    with hQdef
  have hQm : Q m = Q 0 := by simp [hQdef, show 0 < m by omega]
  have hQ : ∀ i < m, Q i ∈ D (if i = 0 then m - 1 else i - 1) ∧ Q i ∈ D i := by
    intro i hi
    simp only [hQdef, hi, dif_pos]
    exact (hne i hi).choose_spec
  have hQ1 : ∀ i < m, Q (i + 1) ∈ D i := by
    intro i hi
    by_cases h : i + 1 < m
    · have := (hQ (i + 1) h).1
      simpa using this
    · have := (hQ 0 (by omega)).1
      rw [show i + 1 = m by omega, hQm]
      simpa [show i = m - 1 by omega] using this
  have hG : ∀ i < m, ∃ G, SArcSet G (Q i) (Q (i + 1)) ∧ G ⊆ D i := by
    intro i hi
    have hne' : Q i ≠ Q (i + 1) := by
      intro heq
      have h1 := (hQ i hi).1
      have h2 := (hQ i hi).2
      by_cases h : i + 1 < m
      · have h3 := (hQ (i + 1) h).2
        rw [← heq] at h3
        split_ifs at h1 with h0
        · subst h0
          exact not_mem_three hNT (i := m - 1) (j := 0) (l := 1) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) h1 h2 h3
        · exact not_mem_three hNT (i := i - 1) (j := i) (l := i + 1) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) h1 h2 h3
      · have hi' : i = m - 1 := by omega
        have h3 := (hQ 0 (by omega)).2
        rw [← hQm, show m = i + 1 by omega, ← heq] at h3
        have h1' : Q i ∈ D (i - 1) := by
          simpa [show i ≠ 0 by omega] using h1
        exact not_mem_three hNT (i := i - 1) (j := i) (l := 0) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) h1' h2 h3
    obtain ⟨v, n, hv, h0, h1, hsub⟩ :=
      exists_sarc_in (hopen i hi) (hconn i hi) (hQ i hi).2 (hQ1 i hi) hne'
    exact ⟨vpath v n, ⟨v, n, hv, h0, h1, rfl⟩, hsub⟩
  choose! G hG using hG
  obtain ⟨A, P, δ, hinv⟩ := trim_chain hm D G Q hG hQm hNT (m - 1) (by omega)
  obtain ⟨A', P', hPm, hA, hcons, hwrap⟩ := trim_close hm D G Q hQm hNT hinv
  refine ⟨A', P', hPm, hA, hcons, hwrap, ?_⟩
  intro i j hij hj heq
  obtain ⟨hi1, hi2⟩ := junction_mem hm hPm hA (i := i) (by omega)
  obtain ⟨hj1, hj2⟩ := junction_mem hm hPm hA hj
  rw [← heq] at hj1 hj2
  rw [if_neg (by omega)] at hj2
  by_cases hji : j - 1 = i
  · split_ifs at hi2 with h0
    · subst h0
      exact not_mem_three hNT (i := m - 1) (j := 0) (l := j) (by omega) (by omega) hj
        (by omega) (by omega) (by omega) hi2 hi1 hj1
    · exact not_mem_three hNT (i := i - 1) (j := i) (l := j) (by omega) (by omega) hj
        (by omega) (by omega) (by omega) hi2 hi1 hj1
  · exact not_mem_three hNT (i := i) (j := j - 1) (l := j) (by omega) (by omega) hj
      (by omega) (by omega) (by omega) hi1 hj2 hj1

/-! ### A small triangle (the case of a common point of three sets, `m = 3`) -/

theorem mem_segment_prod {x y w : Pt} : w ∈ segment ℝ x y ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    w.1 = x.1 + t * (y.1 - x.1) ∧ w.2 = x.2 + t * (y.2 - x.2) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    exact ⟨t, h0, h1, by simp, by simp⟩
  · rintro ⟨t, h0, h1, e1, e2⟩
    exact ⟨t, ⟨h0, h1⟩, Prod.ext (by simp [e1]) (by simp [e2])⟩

theorem sArcSet_segment {x y : Pt} (hxy : x ≠ y) : SArcSet (segment ℝ x y) x y := by
  refine ⟨fun i => if i = 0 then x else y, 2, ⟨le_rfl, ?_, ?_, ?_⟩, by simp, by simp, ?_⟩
  · intro i j hij hj
    have hi : i = 0 := by omega
    have hj' : j = 1 := by omega
    subst hi hj'
    simpa using hxy
  · intro i hi; omega
  · intro i j hij hj; omega
  · simp [vpath]

theorem tri_ab_bc (z : Pt) {e : ℝ} (he : 0 < e) :
    segment ℝ z (z + (e, 0)) ∩ segment ℝ (z + (e, 0)) (z + (0, e)) = {z + (e, 0)} := by
  apply subset_antisymm
  · rintro w ⟨h1, h2⟩
    obtain ⟨t, t0, t1, a1, a2⟩ := mem_segment_prod.1 h1
    obtain ⟨s, s0, s1, b1, b2⟩ := mem_segment_prod.1 h2
    simp at a1 a2 b1 b2
    have hs : s = 0 := by nlinarith
    subst hs
    exact Prod.ext (by simp; linarith) (by simp; linarith)
  · rintro w rfl
    exact ⟨right_mem_segment _ _ _, left_mem_segment _ _ _⟩

theorem tri_bc_ca (z : Pt) {e : ℝ} (he : 0 < e) :
    segment ℝ (z + (e, 0)) (z + (0, e)) ∩ segment ℝ (z + (0, e)) z = {z + (0, e)} := by
  apply subset_antisymm
  · rintro w ⟨h1, h2⟩
    obtain ⟨t, t0, t1, a1, a2⟩ := mem_segment_prod.1 h1
    obtain ⟨s, s0, s1, b1, b2⟩ := mem_segment_prod.1 h2
    simp at a1 a2 b1 b2
    have ht : t = 1 := by nlinarith
    subst ht
    exact Prod.ext (by simp; linarith) (by simp; linarith)
  · rintro w rfl
    exact ⟨right_mem_segment _ _ _, left_mem_segment _ _ _⟩

theorem tri_ca_ab (z : Pt) {e : ℝ} (he : 0 < e) :
    segment ℝ (z + (0, e)) z ∩ segment ℝ z (z + (e, 0)) = {z} := by
  apply subset_antisymm
  · rintro w ⟨h1, h2⟩
    obtain ⟨t, t0, t1, a1, a2⟩ := mem_segment_prod.1 h1
    obtain ⟨s, s0, s1, b1, b2⟩ := mem_segment_prod.1 h2
    simp at a1 a2 b1 b2
    have hs : s = 0 := by nlinarith
    subst hs
    exact Prod.ext (by linarith) (by linarith)
  · rintro w rfl
    exact ⟨right_mem_segment _ _ _, left_mem_segment _ _ _⟩

/-- **Threading, `ℕ`-indexed form**, for a circular chain of connected open sets (non-adjacent
sets disjoint). Either no three of the sets share a point (`threaded_nat`), or `m = 3` and the
three sets share a point, around which a small triangle does. -/
theorem threaded_nat_chain {m : ℕ} (hm : 3 ≤ m) (D : ℕ → Set Pt)
    (hopen : ∀ i < m, IsOpen (D i)) (hconn : ∀ i < m, IsConnected (D i))
    (hne : ∀ i < m, (D (if i = 0 then m - 1 else i - 1) ∩ D i).Nonempty)
    (hfar : ∀ i j, i < m → j < m → (D i ∩ D j).Nonempty →
      i = j ∨ i + 1 = j ∨ j + 1 = i ∨ (i = 0 ∧ j = m - 1) ∨ (j = 0 ∧ i = m - 1)) :
    ∃ (A : ℕ → Set Pt) (P : ℕ → Pt), P m = P 0 ∧
      (∀ i < m, SArcSet (A i) (P i) (P (i + 1)) ∧ A i ⊆ D i) ∧
      (∀ i, i + 1 < m → A i ∩ A (i + 1) = {P (i + 1)}) ∧ A (m - 1) ∩ A 0 = {P 0} ∧
      (∀ i j, i < j → j < m → P i ≠ P j) := by
  by_cases hNT : ∀ i j l, i < m → j < m → l < m → i ≠ j → j ≠ l → i ≠ l → D i ∩ D j ∩ D l = ∅
  · exact threaded_nat hm D hopen hconn hne hNT
  push_neg at hNT
  obtain ⟨i, j, l, hi, hj, hl, hij, hjl, hil, hne3⟩ := hNT
  obtain ⟨y, ⟨hyi, hyj⟩, hyl⟩ := hne3
  have h1 := hfar i j hi hj ⟨y, hyi, hyj⟩
  have h2 := hfar j l hj hl ⟨y, hyj, hyl⟩
  have h3 := hfar i l hi hl ⟨y, hyi, hyl⟩
  have hm3 : m = 3 := by omega
  subst hm3
  have hy : ∀ k < 3, y ∈ D k := by
    intro k hk
    rcases (by omega : k = i ∨ k = j ∨ k = l) with rfl | rfl | rfl <;> assumption
  have hU : IsOpen (D 0 ∩ D 1 ∩ D 2) :=
    ((hopen 0 (by omega)).inter (hopen 1 (by omega))).inter (hopen 2 (by omega))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU y ⟨⟨hy 0 (by omega), hy 1 (by omega)⟩,
    hy 2 (by omega)⟩
  set e := ε / 2 with he
  have he0 : 0 < e := by positivity
  have hb : y + (e, 0) ∈ ball y ε := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Prod.norm_def]
    simp [abs_of_pos he0]; constructor <;> linarith
  have hc : y + (0, e) ∈ ball y ε := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Prod.norm_def]
    simp [abs_of_pos he0]; constructor <;> linarith
  have ha : y ∈ ball y ε := mem_ball_self hε
  have hsub : ∀ {u w : Pt}, u ∈ ball y ε → w ∈ ball y ε → ∀ k < 3, segment ℝ u w ⊆ D k := by
    intro u w hu hw k hk
    refine ((convex_ball y ε).segment_subset hu hw).trans (hball.trans ?_)
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exact fun x hx => hx.1.1
    · exact fun x hx => hx.1.2
    · exact fun x hx => hx.2
  have hab : y ≠ y + (e, 0) := by
    intro h; have := congrArg Prod.fst h; simp at this; linarith
  have hbc : y + (e, 0) ≠ y + (0, e) := by
    intro h; have := congrArg Prod.fst h; simp at this; linarith
  have hca : y + (0, e) ≠ y := by
    intro h; have := congrArg Prod.snd h; simp at this; linarith
  refine ⟨fun k => if k = 0 then segment ℝ y (y + (e, 0)) else if k = 1 then
      segment ℝ (y + (e, 0)) (y + (0, e)) else segment ℝ (y + (0, e)) y,
    fun k => if k = 1 then y + (e, 0) else if k = 2 then y + (0, e) else y, by simp, ?_, ?_, ?_,
    ?_⟩
  · intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exact ⟨by simpa using sArcSet_segment hab, by simpa using hsub ha hb 0 (by omega)⟩
    · exact ⟨by simpa using sArcSet_segment hbc, by simpa using hsub hb hc 1 (by omega)⟩
    · exact ⟨by simpa using sArcSet_segment hca, by simpa using hsub hc ha 2 (by omega)⟩
  · intro k hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · simpa using tri_ab_bc y he0
    · simpa using tri_bc_ca y he0
  · simpa using tri_ca_ab y he0
  · intro a b hab' hb'
    rcases (by omega : (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using hab
    · simpa using hca.symm
    · simpa using hbc

end HPC.Plane
