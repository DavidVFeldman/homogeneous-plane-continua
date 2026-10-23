import HPC.Plane.Snake51
import HPC.PseudoArc.Theorem14

/-!
# Batch 85: tools for the end-point theorems of Bing 1951, §5

* **Weak chains.** A finite family of open sets in which links two or more apart are disjoint,
  but adjacent links need not meet. `exists_chain_of_weak`: the links of a weak chain that meet
  a preconnected set `C` covered by it form a run of consecutive indices, and that run is a chain
  (`HPC.Chain`) covering `C`. Surgery on chains is done with weak chains and then trimmed.
* **Limits of finely chained sets inside a compact set** (`isPreconnected_limSup_of_compact`):
  the batch-81 lemma `HPC.T13.isPreconnected_limSup` without the compact-ambient-space
  hypothesis, the sets being assumed to lie in one compact set.
-/

namespace HPC.Plane

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

/-! ## Weak chains -/

/-- A splitting of a weak chain: if the links before `c₁` are disjoint from the links from `c₂`
on, a preconnected set covered by the two groups and meeting the first lies in the first. -/
theorem weak_split {n : ℕ} {L : ℕ → Set X} (hLo : ∀ i, IsOpen (L i)) {C : Set X}
    (hC : IsPreconnected C) {c₁ c₂ : ℕ}
    (hdisj : ∀ i j, i < c₁ → c₂ ≤ j → j < n → Disjoint (L i) (L j))
    (hcov : C ⊆ (⋃ i, ⋃ (_ : i < n ∧ i < c₁), L i) ∪ (⋃ j, ⋃ (_ : j < n ∧ c₂ ≤ j), L j))
    {a b : ℕ} (ha : a < n ∧ a < c₁) (hb : b < n ∧ c₂ ≤ b) (hCa : (L a ∩ C).Nonempty)
    (hCb : (L b ∩ C).Nonempty) : False := by
  have hU : IsOpen (⋃ i, ⋃ (_ : i < n ∧ i < c₁), L i) :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => hLo i
  have hV : IsOpen (⋃ j, ⋃ (_ : j < n ∧ c₂ ≤ j), L j) :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => hLo i
  have hUV : Disjoint (⋃ i, ⋃ (_ : i < n ∧ i < c₁), L i) (⋃ j, ⋃ (_ : j < n ∧ c₂ ≤ j), L j) := by
    rw [Set.disjoint_iUnion_left]; intro i; rw [Set.disjoint_iUnion_left]; intro hi
    rw [Set.disjoint_iUnion_right]; intro j; rw [Set.disjoint_iUnion_right]; intro hj
    exact hdisj i j hi.2 hj.2 hj.1
  obtain ⟨z, hzL, hzC⟩ := hCa
  have hsub := hC.subset_left_of_subset_union hU hV hUV hcov
    ⟨z, hzC, mem_iUnion₂.mpr ⟨a, ha, hzL⟩⟩
  obtain ⟨w, hwL, hwC⟩ := hCb
  exact Set.disjoint_left.mp hUV (hsub hwC) (mem_iUnion₂.mpr ⟨b, hb, hwL⟩)

/-- **Trimming a weak chain.** Let `L 0, …, L (n-1)` be open sets with `L i ∩ L j = ∅` whenever
`j ≥ i + 2`, covering a preconnected set `C`, and let `L i₀` meet `C`. The links meeting `C` are
exactly those with index in a run `[a, a + k)` containing `i₀`, and they form a chain covering
`C`. -/
theorem exists_chain_of_weak {n : ℕ} (L : ℕ → Set X) (hLo : ∀ i, IsOpen (L i))
    (hweak : ∀ i j, i + 2 ≤ j → j < n → Disjoint (L i) (L j)) {C : Set X} (hC : IsPreconnected C)
    (hcov : C ⊆ ⋃ i, ⋃ (_ : i < n), L i) {i₀ : ℕ} (hi₀ : i₀ < n) (hCi₀ : (L i₀ ∩ C).Nonempty) :
    ∃ (a k : ℕ) (E : Chain X k), a ≤ i₀ ∧ i₀ < a + k ∧ a + k ≤ n ∧
      (∀ t : Fin k, E.link t = L (a + t)) ∧ C ⊆ E.union ∧
      (∀ t : Fin k, (E.link t ∩ C).Nonempty) ∧
      (∀ i, i < n → (L i ∩ C).Nonempty → a ≤ i ∧ i < a + k) := by
  classical
  set S : Finset ℕ := (Finset.range n).filter (fun i => (L i ∩ C).Nonempty) with hS
  have hi₀S : i₀ ∈ S := by simp [hS, hi₀, hCi₀]
  have hSne : S.Nonempty := ⟨i₀, hi₀S⟩
  set a := S.min' hSne with ha
  set b := S.max' hSne with hb
  have haS : a ∈ S := S.min'_mem hSne
  have hbS : b ∈ S := S.max'_mem hSne
  have hmemS : ∀ {i}, i ∈ S ↔ i < n ∧ (L i ∩ C).Nonempty := by
    intro i; simp [hS]
  have hai₀ : a ≤ i₀ := S.min'_le _ hi₀S
  have hi₀b : i₀ ≤ b := S.le_max' _ hi₀S
  have hbn : b < n := (hmemS.mp hbS).1
  -- a covering statement split at thresholds
  have cov_split : ∀ c₁ c₂, c₁ ≤ c₂ → (∀ i, c₁ ≤ i → i < c₂ → i < n → L i ∩ C = ∅) →
      C ⊆ (⋃ i, ⋃ (_ : i < n ∧ i < c₁), L i) ∪ (⋃ j, ⋃ (_ : j < n ∧ c₂ ≤ j), L j) := by
    intro c₁ c₂ _ hgap z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcov hz)
    by_cases h1 : i < c₁
    · exact Or.inl (mem_iUnion₂.mpr ⟨i, ⟨hi, h1⟩, hzi⟩)
    by_cases h2 : c₂ ≤ i
    · exact Or.inr (mem_iUnion₂.mpr ⟨i, ⟨hi, h2⟩, hzi⟩)
    exfalso
    have := hgap i (by omega) (by omega) hi
    exact (this ▸ (⟨hzi, hz⟩ : z ∈ L i ∩ C) : z ∈ (∅ : Set X))
  -- every index between `a` and `b` meets `C`
  have hfill : ∀ i, a ≤ i → i ≤ b → (L i ∩ C).Nonempty := by
    intro i hai hib
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hai' : a < i := lt_of_le_of_ne hai (fun h => by
      have := (hmemS.mp haS).2; rw [h, hne] at this; exact Set.not_nonempty_empty this)
    have hib' : i < b := lt_of_le_of_ne hib (fun h => by
      have := (hmemS.mp hbS).2; rw [← h, hne] at this; exact Set.not_nonempty_empty this)
    exact weak_split hLo hC (c₁ := i) (c₂ := i + 1)
      (fun i' j hi' hj hjn => hweak i' j (by omega) hjn)
      (cov_split i (i + 1) (by omega) (fun i' h1 h2 _ => by
        rw [show i' = i by omega]; exact hne))
      ⟨by omega, hai'⟩ ⟨hbn, by omega⟩ (hmemS.mp haS).2 (hmemS.mp hbS).2
  refine ⟨a, b - a + 1, ⟨fun t => L (a + t), fun t => hLo _, ?_⟩, hai₀, by omega, by omega,
    fun t => rfl, ?_, ?_, ?_⟩
  · intro t u
    have ht := t.isLt
    have hu := u.isLt
    constructor
    · intro hne
      by_contra hfar
      rcases le_total (t : ℕ) u with h | h
      · exact (Set.nonempty_iff_ne_empty.mp hne)
          (Set.disjoint_iff_inter_eq_empty.mp (hweak (a + t) (a + u) (by omega) (by omega)))
      · have hne' : (L (a + u) ∩ L (a + t)).Nonempty := by
          rw [Set.inter_comm]; exact hne
        exact (Set.nonempty_iff_ne_empty.mp hne')
          (Set.disjoint_iff_inter_eq_empty.mp (hweak (a + u) (a + t) (by omega) (by omega)))
    · intro hclose
      -- adjacent links of the run meet
      have key : ∀ i, a ≤ i → i + 1 ≤ b → (L i ∩ L (i + 1)).Nonempty := by
        intro i hai hib
        by_contra hne
        rw [not_nonempty_iff_eq_empty] at hne
        refine weak_split hLo hC (c₁ := i + 1) (c₂ := i + 1) ?_
          (cov_split (i + 1) (i + 1) le_rfl (fun i' h1 h2 _ => by omega))
          ⟨by omega, by omega⟩ ⟨hbn, by omega⟩ (hmemS.mp haS).2 (hmemS.mp hbS).2
        intro i' j hi' hj hjn
        by_cases hij : i' + 2 ≤ j
        · exact hweak i' j hij hjn
        · rw [show i' = i by omega, show j = i + 1 by omega]
          exact Set.disjoint_iff_inter_eq_empty.mpr hne
      show (L (a + t) ∩ L (a + u)).Nonempty
      rcases lt_trichotomy (t : ℕ) u with h | h | h
      · have := key (a + t) (by omega) (by omega)
        rwa [show a + (u : ℕ) = a + t + 1 by omega]
      · rw [show u = t from Fin.ext h.symm]
        obtain ⟨z, hz, -⟩ := hfill (a + t) (by omega) (by omega)
        exact ⟨z, hz, hz⟩
      · have := key (a + u) (by omega) (by omega)
        rw [Set.inter_comm]
        rwa [show a + (t : ℕ) = a + u + 1 by omega]
  · intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcov hz)
    have hiS : i ∈ S := hmemS.mpr ⟨hi, ⟨z, hzi, hz⟩⟩
    have h1 : a ≤ i := S.min'_le _ hiS
    have h2 : i ≤ b := S.le_max' _ hiS
    exact mem_iUnion.mpr ⟨⟨i - a, by omega⟩, by
      show z ∈ L (a + (i - a)); rwa [show a + (i - a) = i by omega]⟩
  · intro t
    exact hfill (a + t) (by omega) (by have := t.isLt; omega)
  · intro i hi hne
    have hiS : i ∈ S := hmemS.mpr ⟨hi, hne⟩
    exact ⟨S.min'_le _ hiS, by have := S.le_max' _ hiS; omega⟩

/-! ## Links indexed by natural numbers -/

/-- The links of a chain indexed by `ℕ`, empty past the end. -/
def linkN {n : ℕ} (D : Chain X n) (i : ℕ) : Set X := if h : i < n then D.link ⟨i, h⟩ else ∅

theorem linkN_of_lt {n : ℕ} (D : Chain X n) {i : ℕ} (h : i < n) : linkN D i = D.link ⟨i, h⟩ :=
  dif_pos h

theorem linkN_fin {n : ℕ} (D : Chain X n) (i : Fin n) : linkN D i = D.link i :=
  dif_pos i.isLt

theorem isOpen_linkN {n : ℕ} (D : Chain X n) (i : ℕ) : IsOpen (linkN D i) := by
  unfold linkN; split_ifs
  · exact D.isOpen _
  · exact isOpen_empty

theorem mem_linkN {n : ℕ} (D : Chain X n) {i : ℕ} {x : X} :
    x ∈ linkN D i ↔ ∃ h : i < n, x ∈ D.link ⟨i, h⟩ := by
  unfold linkN; split_ifs with h
  · exact ⟨fun hx => ⟨h, hx⟩, fun ⟨_, hx⟩ => hx⟩
  · exact ⟨fun hx => hx.elim, fun ⟨h', _⟩ => (h h').elim⟩

theorem disjoint_linkN {n : ℕ} (D : Chain X n) {i j : ℕ} (hij : i + 2 ≤ j) :
    Disjoint (linkN D i) (linkN D j) := by
  rw [Set.disjoint_left]
  intro x hi hj
  obtain ⟨hi', hxi⟩ := (mem_linkN D).mp hi
  obtain ⟨hj', hxj⟩ := (mem_linkN D).mp hj
  have := (D.adjacent_iff ⟨i, hi'⟩ ⟨j, hj'⟩).mp ⟨x, hxi, hxj⟩
  simp only at this
  omega

theorem mem_union_iff_linkN {n : ℕ} (D : Chain X n) {x : X} :
    x ∈ D.union ↔ ∃ i, i < n ∧ x ∈ linkN D i := by
  simp only [Chain.union, mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, i.isLt, by rwa [linkN_fin]⟩
  · rintro ⟨i, hi, hx⟩; exact ⟨⟨i, hi⟩, by rwa [← linkN_of_lt D hi]⟩

theorem linkN_subset_of {n : ℕ} (D : Chain X n) {S : Set X} (h : ∀ i, D.link i ⊆ S) (i : ℕ) :
    linkN D i ⊆ S := fun x hx => by
  obtain ⟨hi, hx⟩ := (mem_linkN D).mp hx; exact h _ hx

/-- **Reverse and trim.** From a chain covering a preconnected set `C` with a point `q ∈ C` in its
first link only, a chain whose links are links of the given one, covering `C`, every link meeting
`C`, with `q` in its last link only. -/
theorem exists_chain_last_only {n : ℕ} (D : Chain X n) {C : Set X} (hC : IsPreconnected C)
    (hCD : C ⊆ D.union) {q : X} (hqC : q ∈ C) (hn : 0 < n) (hq0 : q ∈ D.link ⟨0, hn⟩)
    (hqj : ∀ j : Fin n, j.val ≠ 0 → q ∉ D.link j) :
    ∃ (k : ℕ) (D' : Chain X k) (hk : 0 < k), (∀ t, ∃ s, D'.link t = D.link s) ∧
      C ⊆ D'.union ∧ (∀ t, (D'.link t ∩ C).Nonempty) ∧ q ∈ D'.link ⟨k - 1, by omega⟩ ∧
      ∀ t : Fin k, q ∈ D'.link t → t.val = k - 1 := by
  set R := D.reverse
  have hrev : ∀ i (hi : i < n), linkN R i = D.link ⟨n - 1 - i, by omega⟩ := by
    intro i hi
    rw [linkN_of_lt R hi]
    simp only [R, Chain.reverse_link]
    congr 1; ext; simp [Fin.val_rev]; omega
  obtain ⟨a, k, D', ha, hk, hakn, hlink, hcov, hmeet, -⟩ := exists_chain_of_weak (n := n) (linkN R)
    (isOpen_linkN R) (fun i j hij _ => disjoint_linkN R hij) hC
    (fun x hx => by
      have hx' := hCD hx
      simp only [Chain.union, mem_iUnion] at hx'
      obtain ⟨i, hi⟩ := hx'
      have hi' : i.val < n := i.isLt
      refine mem_iUnion₂.mpr ⟨n - 1 - i, by omega, ?_⟩
      rw [hrev (n - 1 - i) (by omega)]
      have e : (⟨n - 1 - (n - 1 - i.val), by omega⟩ : Fin n) = i := Fin.ext (by simp only; omega)
      rw [e]; exact hi)
    (i₀ := n - 1) (by omega) ⟨q, by
      rw [hrev (n - 1) (by omega)]
      have e : (⟨n - 1 - (n - 1), by omega⟩ : Fin n) = ⟨0, hn⟩ := Fin.ext (by simp only; omega)
      rw [e]; exact hq0, hqC⟩
  have hak : a + k = n := by omega
  have hk0 : 0 < k := by omega
  refine ⟨k, D', hk0, fun t => ⟨⟨n - 1 - (a + t), by omega⟩,
    by rw [hlink t, hrev (a + t) (by omega)]⟩, hcov, hmeet, ?_, ?_⟩
  · rw [hlink, hrev (a + (k - 1)) (by omega)]
    have e : (⟨n - 1 - (a + (k - 1)), by omega⟩ : Fin n) = ⟨0, hn⟩ := Fin.ext (by simp only; omega)
    rw [e]; exact hq0
  · intro t ht
    rw [hlink, hrev (a + t) (by omega)] at ht
    by_contra hne
    exact hqj _ (by simp only; omega) ht

/-! ## Limits of finely chained sets inside a compact set -/

/-- `HPC.T13.limSup_subset_of_mem` with the sets inside a compact set `S` instead of a compact
ambient space. -/
theorem limSup_subset_of_mem_of_compact {S : Set X} (hS : IsCompact S) {I : Set ℕ}
    {A : ℕ → Set X} {ε : ℕ → ℝ} (hAS : ∀ k ∈ I, A k ⊆ S)
    (hε : Tendsto ε atTop (𝓝 0)) (hch : ∀ k ∈ I, T13.ChainedAt (A k) (ε k)) {R : X}
    (hR : ∀ k ∈ I, R ∈ A k) {u v : Set X} (hu : IsCompact u) (hv : IsClosed v)
    (hsub : T13.limSup I A ⊆ u ∪ v) (hdisj : Disjoint u v) (hRu : R ∈ u) :
    T13.limSup I A ⊆ u := by
  obtain ⟨δ, hδ, hδd⟩ := hdisj.exists_thickenings hu hv
  set U' := thickening (δ / 2) u
  set V' := thickening (δ / 2) v
  have hsep : ∀ x ∈ U', ∀ y ∈ V', δ / 2 ≤ dist x y := by
    intro x hx y hy
    by_contra hlt
    push_neg at hlt
    rw [mem_thickening_iff] at hx hy
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    have h1 : y ∈ thickening δ u :=
      mem_thickening_iff.mpr ⟨a, ha, by linarith [dist_triangle y x a, dist_comm x y]⟩
    have h2 : y ∈ thickening δ v := mem_thickening_iff.mpr ⟨b, hb, by linarith⟩
    exact (hδd.le_bot ⟨h1, h2⟩ : _)
  set C : ℕ → Set X := fun N => closure (⋃ k ∈ I, ⋃ (_ : N ≤ k), A k) with hC
  have hCanti : ∀ N N', N ≤ N' → C N' ⊆ C N := by
    intro N N' h
    refine closure_mono ?_
    intro z hz
    simp only [mem_iUnion] at hz ⊢
    obtain ⟨k, hk, hk', hz⟩ := hz
    exact ⟨k, hk, le_trans h hk', hz⟩
  have hCS : ∀ N, C N ⊆ S := fun N => closure_minimal
    (iUnion₂_subset fun k hk => iUnion_subset fun _ => hAS k hk) hS.isClosed
  have hopen : IsOpen (U' ∪ V') := isOpen_thickening.union isOpen_thickening
  obtain ⟨N1, hN1⟩ : ∃ N, C N ⊆ U' ∪ V' := by
    refine exists_subset_nhds_of_isCompact' (V := C) ?_
      (fun N => hS.of_isClosed_subset isClosed_closure (hCS N))
      (fun N => isClosed_closure) ?_
    · intro i j
      exact ⟨max i j, hCanti _ _ (le_max_left _ _), hCanti _ _ (le_max_right _ _)⟩
    · intro x hx
      refine hopen.mem_nhds ?_
      have : x ∈ T13.limSup I A := hx
      rcases hsub this with h | h
      · exact Or.inl (self_subset_thickening (by linarith) _ h)
      · exact Or.inr (self_subset_thickening (by linarith) _ h)
  obtain ⟨N2, hN2⟩ : ∃ N, ∀ k, N ≤ k → ε k < δ / 2 := by
    have := (hε.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 2 by linarith)))
    exact eventually_atTop.mp this
  have hAk : ∀ k ∈ I, max N1 N2 ≤ k → A k ⊆ U' := by
    intro k hk hNk
    have hAC : A k ⊆ U' ∪ V' := by
      refine subset_trans ?_ hN1
      intro z hz
      exact subset_closure (mem_iUnion₂.mpr ⟨k, hk, mem_iUnion.mpr ⟨le_of_max_le_left hNk, hz⟩⟩)
    rcases hch k hk U' V' hAC (fun x hx y hy =>
        lt_of_lt_of_le (hN2 k (le_of_max_le_right hNk)) (hsep x hx y hy)) with h | h
    · exact h
    · exfalso
      have hRU : R ∈ U' := self_subset_thickening (by linarith) _ hRu
      have := hsep R hRU R (h (hR k hk))
      simp at this
      linarith
  have hCN : C (max N1 N2) ⊆ thickening δ u := by
    refine subset_trans (closure_mono ?_) (subset_trans (closure_thickening_subset_cthickening (δ / 2) u)
      (cthickening_subset_thickening' hδ (by linarith) u))
    intro z hz
    simp only [mem_iUnion] at hz
    obtain ⟨k, hk, hk', hz⟩ := hz
    exact hAk k hk hk' hz
  intro z hz
  rcases hsub hz with h | h
  · exact h
  · exfalso
    have h1 : z ∈ thickening δ u := hCN (T13.limSup_subset_closure _ hz)
    have h2 : z ∈ thickening δ v := self_subset_thickening hδ _ h
    exact (hδd.le_bot ⟨h1, h2⟩ : _)

/-- The limit superior of sets lying in a compact set `S` is contained in `S`. -/
theorem limSup_subset_of_subset {S : Set X} (hS : IsClosed S) {I : Set ℕ} {A : ℕ → Set X}
    (hAS : ∀ k ∈ I, A k ⊆ S) : T13.limSup I A ⊆ S :=
  (T13.limSup_subset_closure 0).trans (closure_minimal
    (iUnion₂_subset fun k hk => iUnion_subset fun _ => hAS k hk) hS)

/-- **Limits of finely chained sets inside a compact set are connected.** -/
theorem isPreconnected_limSup_of_compact {S : Set X} (hS : IsCompact S) {I : Set ℕ}
    {A : ℕ → Set X} {ε : ℕ → ℝ} (hAS : ∀ k ∈ I, A k ⊆ S)
    (hε : Tendsto ε atTop (𝓝 0)) (hch : ∀ k ∈ I, T13.ChainedAt (A k) (ε k)) {R : X}
    (hR : ∀ k ∈ I, R ∈ A k) (hI : I.Infinite) : IsPreconnected (T13.limSup I A) := by
  have hLS := limSup_subset_of_subset hS.isClosed hAS
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed (T13.isClosed_limSup I A)]
  intro u v hu hv hsub hdisj
  have hRS : R ∈ S := hAS _ (hI.nonempty.some_mem) (hR _ hI.nonempty.some_mem)
  have hsub' : T13.limSup I A ⊆ (u ∩ S) ∪ (v ∩ S) := fun z hz => by
    rcases hsub hz with h | h
    · exact Or.inl ⟨h, hLS hz⟩
    · exact Or.inr ⟨h, hLS hz⟩
  have hdisj' : Disjoint (u ∩ S) (v ∩ S) :=
    hdisj.mono inter_subset_left inter_subset_left
  rcases hsub (T13.mem_limSup hI hR) with h | h
  · exact Or.inl ((limSup_subset_of_mem_of_compact hS hAS hε hch hR
      (hS.inter_left hu) (hv.inter hS.isClosed) hsub' hdisj' ⟨h, hRS⟩).trans inter_subset_left)
  · exact Or.inr ((limSup_subset_of_mem_of_compact hS hAS hε hch hR
      (hS.inter_left hv) (hu.inter hS.isClosed) (hsub'.trans (union_comm _ _).le) hdisj'.symm
      ⟨h, hRS⟩).trans inter_subset_left)

/-! ## Irreducibility and fine chains (Theorem 14's `δ`) -/

/-- The part of `M` in the links `0, …, l` of a chain of mesh `< δ` all of whose links up to `l`
meet `M` is `2δ`-chained. -/
theorem chainedAt_initial {M : Set X} {n : ℕ} (F : Chain X n) {δ : ℝ}
    (hF : ∀ i, Bornology.IsBounded (F.link i) ∧ diam (F.link i) < δ) {l : ℕ} (hl : l < n)
    (hmeet : ∀ i (hi : i < n), i ≤ l → (M ∩ F.link ⟨i, hi⟩).Nonempty) :
    T13.ChainedAt (M ∩ ⋃ i, ⋃ (hi : i < n), ⋃ (_ : i ≤ l), F.link ⟨i, hi⟩) (2 * δ) := by
  set A := M ∩ ⋃ i, ⋃ (hi : i < n), ⋃ (_ : i ≤ l), F.link ⟨i, hi⟩
  have hdist : ∀ i (y z : X), y ∈ F.link i → z ∈ F.link i → dist y z < δ := fun i y z hy hz =>
    (dist_le_diam_of_mem (hF i).1 hy hz).trans_lt (hF i).2
  obtain ⟨z₀, hz₀M, hz₀⟩ := hmeet 0 (by omega) (Nat.zero_le _)
  have side : ∀ W W' : Set X, A ⊆ W ∪ W' → (∀ x ∈ W, ∀ y ∈ W', 2 * δ < dist x y) → z₀ ∈ W →
      A ⊆ W := by
    intro W W' hcov hsep hz₀W
    have claim : ∀ i (hi : i < n), i ≤ l → ∀ y ∈ M ∩ F.link ⟨i, hi⟩, y ∈ W ∧
        ∃ z ∈ M ∩ F.link ⟨i, hi⟩, z ∈ W := by
      intro i
      induction i with
      | zero =>
        intro hi _ y hy
        have hyA : y ∈ A := ⟨hy.1, mem_iUnion₂.mpr ⟨0, hi, mem_iUnion.mpr ⟨Nat.zero_le _, hy.2⟩⟩⟩
        refine ⟨?_, z₀, ⟨hz₀M, hz₀⟩, hz₀W⟩
        rcases hcov hyA with h | h
        · exact h
        · have := hsep z₀ hz₀W y h
          have := hdist ⟨0, hi⟩ z₀ y hz₀ hy.2
          have : 0 < δ := lt_of_le_of_lt dist_nonneg this
          linarith
      | succ i ih =>
        intro hi hil y hy
        obtain ⟨z, hzM, hz⟩ := hmeet i (by omega) (by omega)
        have hzW := (ih (by omega) (by omega) z ⟨hzM, hz⟩).1
        obtain ⟨w, hw1, hw2⟩ := (F.adjacent_iff ⟨i, by omega⟩ ⟨i + 1, hi⟩).mpr (by simp only; omega)
        have hyA : y ∈ A := ⟨hy.1, mem_iUnion₂.mpr ⟨i + 1, hi, mem_iUnion.mpr ⟨hil, hy.2⟩⟩⟩
        have hyW : y ∈ W := by
          rcases hcov hyA with h | h
          · exact h
          · have h1 := hsep z hzW y h
            have h2 := hdist _ z w hz hw1
            have h3 := hdist _ w y hw2 hy.2
            have := dist_triangle z w y
            linarith
        exact ⟨hyW, y, hy, hyW⟩
    intro y hy
    obtain ⟨i, hi, hil, hyi⟩ : ∃ i, ∃ hi : i < n, i ≤ l ∧ y ∈ F.link ⟨i, hi⟩ := by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy.2
      obtain ⟨hi', hi⟩ := mem_iUnion.mp hi
      obtain ⟨hil, hi⟩ := mem_iUnion.mp hi
      exact ⟨i, hi', hil, hi⟩
    exact (claim i hi hil y ⟨hy.1, hyi⟩).1
  intro U V hcov hsep
  have hz₀A : z₀ ∈ A := ⟨hz₀M, mem_iUnion₂.mpr ⟨0, by omega, mem_iUnion.mpr ⟨Nat.zero_le _, hz₀⟩⟩⟩
  rcases hcov hz₀A with h | h
  · exact Or.inl (side U V hcov hsep h)
  · exact Or.inr (side V U (hcov.trans (union_comm U V).le)
      (fun x hx y hy => by rw [dist_comm]; exact hsep y hy x hx) h)

/-- **Bing's `δ` in Theorem 14.** Let `M` be a continuum irreducible from `p` to `q`, and `O` an
open set containing a point `x` of `M` other than `p` and `q`. There is `δ > 0` such that in every
`δ`-chain covering `M` with `p` in its first link, some link other than the first lies in `O` and
comes before every link containing `q`. -/
theorem exists_delta_link_between {M : Set X} (hM : Fold.Q78.IsContinuum M) {p q : X}
    (hirr : IsIrreducibleBetween M p q) {O : Set X} (hO : IsOpen O) {x : X} (hxM : x ∈ M)
    (hxO : x ∈ O) (hxp : x ≠ p) (hxq : x ≠ q) :
    ∃ δ > 0, ∀ (n : ℕ) (F : Chain X n) (hn : 0 < n),
      (∀ i, Bornology.IsBounded (F.link i) ∧ diam (F.link i) < δ) → M ⊆ F.union →
      p ∈ F.link ⟨0, hn⟩ → ∃ j : Fin n, 0 < j.val ∧ F.link j ⊆ O ∧ ∀ l : Fin n, q ∈ F.link l → j < l := by
  classical
  by_contra hcon
  push_neg at hcon
  choose n F hn hF hMF hpF hbad using fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity)
  have hqM : q ∈ M := hirr.2.2.1
  have hpM : p ∈ M := hirr.2.1
  have hex : ∀ k, ∃ i, ∃ hi : i < n k, q ∈ (F k).link ⟨i, hi⟩ := by
    intro k
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hMF k hqM)
    exact ⟨i.val, i.isLt, hi⟩
  set l : ℕ → ℕ := fun k => Nat.find (hex k) with hl
  have hlspec : ∀ k, ∃ hi : l k < n k, q ∈ (F k).link ⟨l k, hi⟩ := fun k => Nat.find_spec (hex k)
  have hlmin : ∀ k i (hi : i < n k), q ∈ (F k).link ⟨i, hi⟩ → l k ≤ i :=
    fun k i hi h => Nat.find_min' (hex k) ⟨hi, h⟩
  set A : ℕ → Set X := fun k => M ∩ ⋃ i, ⋃ (hi : i < n k), ⋃ (_ : i ≤ l k), (F k).link ⟨i, hi⟩
    with hA
  have hAM : ∀ k ∈ (univ : Set ℕ), A k ⊆ M := fun k _ => inter_subset_left
  have hpA : ∀ k ∈ (univ : Set ℕ), p ∈ A k := fun k _ =>
    ⟨hpM, mem_iUnion₂.mpr ⟨0, hn k, mem_iUnion.mpr ⟨Nat.zero_le _, hpF k⟩⟩⟩
  have hqA : ∀ k ∈ (univ : Set ℕ), q ∈ A k := fun k _ =>
    ⟨hqM, mem_iUnion₂.mpr ⟨l k, (hlspec k).1, mem_iUnion.mpr ⟨le_rfl, (hlspec k).2⟩⟩⟩
  have hch : ∀ k ∈ (univ : Set ℕ), T13.ChainedAt (A k) (2 * (1 / ((k : ℝ) + 1))) := by
    intro k _
    refine chainedAt_initial (F k) (hF k) (hlspec k).1 (fun i hi hil => ?_)
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; exact ⟨p, hpM, hpF k⟩
    rcases lt_or_eq_of_le hil with hlt | heq
    · obtain ⟨z, hz1, hz2⟩ := (F k).inter_link_nonempty_between hM.2.isPreconnected (hMF k)
        (a := ⟨0, hn k⟩) (b := ⟨i, hi⟩) (c := ⟨l k, (hlspec k).1⟩) (Fin.mk_lt_mk.mpr h0)
        (Fin.mk_lt_mk.mpr hlt) ⟨p, hpM, hpF k⟩ ⟨q, hqM, (hlspec k).2⟩
      exact ⟨z, hz1, hz2⟩
    · subst heq; exact ⟨q, hqM, (hlspec k).2⟩
  have hε : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ))
  set Lim := T13.limSup univ A
  have hLpre : IsPreconnected Lim :=
    isPreconnected_limSup_of_compact hM.1 hAM hε hch hpA infinite_univ
  have hLM : Lim ⊆ M := limSup_subset_of_subset hM.1.isClosed hAM
  have hpL : p ∈ Lim := T13.mem_limSup infinite_univ hpA
  have hqL : q ∈ Lim := T13.mem_limSup infinite_univ hqA
  have hLcont : Fold.Q78.IsContinuum Lim :=
    ⟨hM.1.of_isClosed_subset (T13.isClosed_limSup _ _) hLM, ⟨p, hpL⟩, hLpre⟩
  have hLeq : Lim = M := hirr.2.2.2 Lim hLcont hLM hpL hqL
  have hxL : x ∈ Lim := hLeq ▸ hxM
  obtain ⟨r₀, hr₀, hr₀O⟩ := Metric.isOpen_iff.mp hO x hxO
  have hdp : 0 < dist x p := dist_pos.mpr hxp
  have hdq : 0 < dist x q := dist_pos.mpr hxq
  set r := min (r₀ / 2) (min (dist x p) (dist x q) / 2) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by positivity)
  have hr1 : r ≤ r₀ / 2 := min_le_left _ _
  have hr2 : 2 * r ≤ dist x p := by
    have := min_le_right (r₀ / 2) (min (dist x p) (dist x q) / 2)
    have := min_le_left (dist x p) (dist x q); linarith
  have hr3 : 2 * r ≤ dist x q := by
    have := min_le_right (r₀ / 2) (min (dist x p) (dist x q) / 2)
    have := min_le_right (dist x p) (dist x q); linarith
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hr0
  have hxcl := T13.limSup_subset_closure N hxL
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hxcl r hr0
  obtain ⟨k, -, hNk, hyA⟩ : ∃ k, k ∈ (univ : Set ℕ) ∧ N ≤ k ∧ y ∈ A k := by
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    obtain ⟨hk', hk⟩ := mem_iUnion.mp hk
    obtain ⟨hNk, hk⟩ := mem_iUnion.mp hk
    exact ⟨k, hk', hNk, hk⟩
  have hδk : 1 / ((k : ℝ) + 1) < r := by
    refine lt_of_le_of_lt ?_ hN
    gcongr
  obtain ⟨hyM, hy'⟩ := hyA
  obtain ⟨i, hi, hil, hyi⟩ : ∃ i, ∃ hi : i < n k, i ≤ l k ∧ y ∈ (F k).link ⟨i, hi⟩ := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy'
    obtain ⟨hi', hi⟩ := mem_iUnion.mp hi
    obtain ⟨hil, hi⟩ := mem_iUnion.mp hi
    exact ⟨i, hi', hil, hi⟩
  have hsmall : ∀ (j : Fin (n k)) (a b : X), a ∈ (F k).link j → b ∈ (F k).link j →
      dist a b < r := fun j a b ha hb =>
    ((dist_le_diam_of_mem (hF k j).1 ha hb).trans_lt (hF k j).2).trans hδk
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    have := hsmall _ y p hyi (hpF k)
    have := dist_triangle x y p
    linarith
  rcases lt_or_eq_of_le hil with hlt | heq
  · have hsub : (F k).link ⟨i, hi⟩ ⊆ O := by
      intro z hz
      apply hr₀O
      rw [Metric.mem_ball]
      have := hsmall _ z y hz hyi
      have := dist_triangle z y x
      rw [dist_comm] at hxy
      linarith
    obtain ⟨l', hql', hl'i⟩ := hbad k ⟨i, hi⟩ h0 hsub
    have := hlmin k l'.val l'.isLt hql'
    have : l'.val ≤ i := hl'i
    omega
  · subst heq
    have := hsmall _ y q hyi (hlspec k).2
    have := dist_triangle x y q
    linarith

end HPC.Plane
