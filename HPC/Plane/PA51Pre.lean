import HPC.Plane.PA51Crook

/-!
# Batch 88: a description of a compact chainable hereditarily indecomposable space

The body of Bing's proof of Theorem 1 (*Concerning hereditarily indecomposable continua*, 1951),
carried out in a compact metric space `X` which is itself the continuum (`M = univ`); the general
case is reduced to this one in `PA51Lift.lean` by passing to the subspace `M`.

* `PreDesc X`: Bing's sequence `C_{n_1}, C_{n_2}, …` — chains covering `X`, each crooked (1948
  sense) in the previous one, closures of links nested, mesh at most `1/(i+1)`. Unlike a
  `Description`, the levels need not be chains from a fixed point to another.
* `exists_preDesc`: such a sequence exists when `X` is chainable and hereditarily indecomposable
  (`eventually_crookedIn`, iterated).
* `PreDesc.exists_description`: for `p`, `q` in different composants of `X`, a description from `p`
  to `q` with `Δ.M = univ` (Bing: "there is no loss of generality in supposing that each of the
  chains is from `p` to `q`"): the argument of Theorem 13 (`Description.exists_step`,
  `exists_description_from'`) with the pre-description in place of a description.
-/

namespace HPC.Plane

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

namespace PA51

/-- **Bing's sequence of mutually crooked chains** covering the space `X`. -/
structure PreDesc (X : Type*) [MetricSpace X] where
  n : ℕ → ℕ
  D : (i : ℕ) → Chain X (n i)
  cover : ∀ i (x : X), ∃ t, x ∈ (D i).link t
  crooked : ∀ i, (D (i + 1)).IsCrookedIn' (D i)
  closure_subset : ∀ i (t : Fin (n (i + 1))), ∃ s, closure ((D (i + 1)).link t) ⊆ (D i).link s
  bdd : ∀ i t, Bornology.IsBounded ((D i).link t)
  diam_le : ∀ i t, diam ((D i).link t) ≤ 1 / ((i : ℝ) + 1)

/-! ### Existence of a pre-description -/

/-- **One step**: a chain covering the compact hereditarily indecomposable chainable space has a
refinement covering the space, crooked in it, with closures of links in its links and mesh at most
`η`. -/
theorem exists_crooked_next [CompactSpace X]
    (hHI : ∀ K : Set X, Fold.Q78.IsContinuum K → Fold.Q78.IsIndecomposable K)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ univ ⊆ D.union)
    {n : ℕ} (C : Chain X n) (hcov : ∀ x : X, ∃ t, x ∈ C.link t) {η : ℝ} (hη : 0 < η) :
    ∃ (n' : ℕ) (C' : Chain X n'), (∀ x : X, ∃ t, x ∈ C'.link t) ∧ C'.IsCrookedIn' C ∧
      (∀ t, ∃ s, closure (C'.link t) ⊆ C.link s) ∧ (∀ t, Bornology.IsBounded (C'.link t)) ∧
      ∀ t, diam (C'.link t) ≤ η := by
  obtain ⟨lam, hlam, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun t => C.isOpen t) (fun x _ => mem_iUnion.mpr (hcov x))
  set η' : ℕ → ℝ := fun m => min (lam / 2) (1 / ((m : ℝ) + 1)) with hη'
  have hη'pos : ∀ m, 0 < η' m := fun m => lt_min (by linarith) (by positivity)
  choose N E hEε hEcov using fun m => hsnake (η' m) (hη'pos m)
  have hcl : ∀ m t, ∃ s, closure ((E m).link t) ⊆ C.link s := by
    intro m t
    obtain ⟨y, hy⟩ := (E m).link_nonempty t
    obtain ⟨s, hs⟩ := hleb y (mem_univ y)
    refine ⟨s, (closure_subset_closedBall_diam (hEε m t).1 hy).trans
      ((closedBall_subset_ball ?_).trans hs)⟩
    have := (hEε m t).2
    have := min_le_left (lam / 2) (1 / ((m : ℝ) + 1))
    linarith
  have href : ∀ m, (E m).Refines C := fun m t => by
    obtain ⟨s, hs⟩ := hcl m t
    exact ⟨s, subset_closure.trans hs⟩
  have hdiam : ∀ m t, diam ((E m).link t) ≤ 1 / ((m : ℝ) + 1) := fun m t =>
    ((hEε m t).2.trans_le (min_le_right _ _)).le
  have hev := eventually_crookedIn hHI C hcov E href (fun m => 1 / ((m : ℝ) + 1))
    (fun m => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat (fun m t => (hEε m t).1) hdiam
  obtain ⟨m, hcr, hm⟩ := (hev.and (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const
    hη)).exists
  exact ⟨N m, E m, fun x => mem_iUnion.mp (hEcov m (mem_univ x)), hcr, hcl m,
    fun t => (hEε m t).1, fun t => (hdiam m t).trans hm.le⟩

/-- A chain covering the space with bounded links. -/
structure CoverLevel (X : Type*) [MetricSpace X] where
  n : ℕ
  C : Chain X n
  cover : ∀ x : X, ∃ t, x ∈ C.link t
  bdd : ∀ t, Bornology.IsBounded (C.link t)

/-- **Bing's sequence exists** in a compact chainable hereditarily indecomposable space. -/
theorem exists_preDesc [CompactSpace X]
    (hHI : ∀ K : Set X, Fold.Q78.IsContinuum K → Fold.Q78.IsIndecomposable K)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ univ ⊆ D.union) :
    Nonempty (PreDesc X) := by
  obtain ⟨n₀, C₀, hC₀ε, hC₀cov⟩ := hsnake 1 one_pos
  let L₀ : CoverLevel X := ⟨n₀, C₀, fun x => mem_iUnion.mp (hC₀cov (mem_univ x)),
    fun t => (hC₀ε t).1⟩
  have step : ∀ (L : CoverLevel X) (i : ℕ), ∃ L' : CoverLevel X, L'.C.IsCrookedIn' L.C ∧
      (∀ t, ∃ s, closure (L'.C.link t) ⊆ L.C.link s) ∧
      ∀ t, diam (L'.C.link t) ≤ 1 / ((i : ℝ) + 2) := by
    intro L i
    obtain ⟨n', C', hcov, hcr, hcl, hbdd, hdiam⟩ :=
      exists_crooked_next hHI hsnake L.C L.cover (η := 1 / ((i : ℝ) + 2)) (by positivity)
    exact ⟨⟨n', C', hcov, hbdd⟩, hcr, hcl, hdiam⟩
  choose next hcr hcl hdiam using step
  let lev : ℕ → CoverLevel X := fun i => Nat.rec L₀ (fun i L => next L i) i
  have hlevs : ∀ i, lev (i + 1) = next (lev i) i := fun i => rfl
  refine ⟨{
    n := fun i => (lev i).n
    D := fun i => (lev i).C
    cover := fun i => (lev i).cover
    crooked := fun i => ?_
    closure_subset := fun i t => ?_
    bdd := fun i => (lev i).bdd
    diam_le := fun i t => ?_ }⟩
  · show (lev (i + 1)).C.IsCrookedIn' (lev i).C
    rw [hlevs]; exact hcr _ _
  · show ∃ s, closure ((lev (i + 1)).C.link t) ⊆ (lev i).C.link s
    exact hcl (lev i) i t
  · show diam ((lev i).C.link t) ≤ 1 / ((i : ℝ) + 1)
    cases i with
    | zero =>
      show diam (C₀.link t) ≤ 1 / (((0 : ℕ) : ℝ) + 1)
      simpa using (hC₀ε t).2.le
    | succ i =>
      refine (hdiam (lev i) i t).trans (le_of_eq ?_)
      push_cast; ring

/-! ### Properties of a pre-description -/

namespace PreDesc

variable (B : PreDesc X)

theorem refines_of_le {i j : ℕ} (hij : i ≤ j) : (B.D j).Refines (B.D i) := by
  induction j, hij using Nat.le_induction with
  | base => intro t; exact ⟨t, subset_rfl⟩
  | succ j hij ih =>
      intro t
      obtain ⟨s, hs⟩ := B.closure_subset j t
      obtain ⟨u, hu⟩ := ih s
      exact ⟨u, (subset_closure.trans hs).trans hu⟩

theorem crooked_of_lt {i j : ℕ} (hij : i < j) : (B.D j).IsCrookedIn' (B.D i) := by
  exact Chain.isCrookedIn'_of_refines (B.refines_of_le hij) (B.crooked i)

theorem mem_levelUnion (i : ℕ) (x : X) : x ∈ (B.D i).union := mem_iUnion.mpr (B.cover i x)

/-- Deep levels have at least five links when the space has two distinct points. -/
theorem eventually_five_le {p q : X} (hpq : p ≠ q) : ∀ᶠ m in atTop, 5 ≤ B.n m := by
  have hd : 0 < dist p q := dist_pos.mpr hpq
  have ht : Tendsto (fun i : ℕ => 10 * (1 / ((i : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (10 : ℝ)
  filter_upwards [ht.eventually_lt_const hd] with m hm
  by_contra hcon
  push_neg at hcon
  set e : ℝ := 1 / ((m : ℝ) + 1) with he
  have hepos : 0 < e := by positivity
  have hb : Bornology.IsBounded ({p, q} : Set X) := (Set.toFinite _).isBounded
  have h1 := Chain.diam_le_length_mul hb (B.D m) (fun x _ => B.mem_levelUnion m x)
    (2 * e) (B.bdd m) (fun t => by
      have := B.diam_le m t
      linarith)
  rw [Metric.diam_pair] at h1
  have h2 : (B.n m : ℝ) ≤ 4 := by exact_mod_cast (by omega : B.n m ≤ 4)
  have h3 : (B.n m : ℝ) * (2 * e) ≤ 4 * (2 * e) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  linarith

/-- **The limit step** (as `Description.false_of_disjoint_limit`). -/
theorem false_of_disjoint_limit [CompactSpace X] {R S : X}
    (hcomp : S ∉ composant (univ : Set X) R) {I : Set ℕ} (hI : I.Infinite) (A : ℕ → Set X)
    (hch : ∀ k ∈ I, T13.ChainedAt (A k) (1 / ((k : ℝ) + 1))) (hRA : ∀ k ∈ I, R ∈ A k)
    (hSA : ∀ k ∈ I, S ∈ A k) {O : Set X} (hO : IsOpen O) (hOne : O.Nonempty)
    (hdisj : ∀ k ∈ I, Disjoint (A k) O) : False := by
  set Z := T13.limSup I A
  have hZc : IsClosed Z := T13.isClosed_limSup I A
  have hZpc : IsPreconnected Z :=
    T13.isPreconnected_limSup tendsto_one_div_add_atTop_nhds_zero_nat hch hRA hI
  have hRZ : R ∈ Z := T13.mem_limSup hI hRA
  have hSZ : S ∈ Z := T13.mem_limSup hI hSA
  have hZne : Z ≠ univ := by
    obtain ⟨w, hwO⟩ := hOne
    intro heq
    have hwZ : w ∈ Z := heq ▸ mem_univ w
    have := T13.limSup_subset_closure 0 hwZ
    obtain ⟨y, hyO, hy⟩ := mem_closure_iff.mp this O hO hwO
    simp only [mem_iUnion] at hy
    obtain ⟨k, hk, -, hy⟩ := hy
    exact (hdisj k hk).le_bot ⟨hy, hyO⟩
  apply hcomp
  exact mem_sUnion.mpr ⟨Z, ⟨⟨hZc.isCompact, ⟨R, hRZ⟩, hZpc⟩, subset_univ _, hZne, hRZ⟩, hSZ⟩

/-- **Reaching both ends** (Bing: "the subchain of `C_{n_k}` from `p` to `q` has a link that
intersects the first link of `C_{n_j}` and has a link that intersects the last link"). -/
theorem exists_subchain_meets_ends [CompactSpace X] {R S : X} (hRS : R ≠ S)
    (hcomp : S ∉ composant (univ : Set X) R) (j : ℕ) (hj : 0 < B.n j) :
    ∃ k, j < k ∧ ∃ a b : Fin (B.n k), (B.D k).IsSubchainFrom a b R S ∧
      (∃ t : Fin (B.n k), a ≤ t ∧ t ≤ b ∧
        ((B.D k).link t ∩ (B.D j).link ⟨0, hj⟩).Nonempty) ∧
      (∃ t : Fin (B.n k), a ≤ t ∧ t ≤ b ∧
        ((B.D k).link t ∩ (B.D j).link ⟨B.n j - 1, by omega⟩).Nonempty) := by
  classical
  have hRS' : 0 < dist R S := dist_pos.mpr hRS
  obtain ⟨k0, hk0⟩ : ∃ k0, ∀ k : ℕ, k0 ≤ k → 1 / ((k : ℝ) + 1) < dist R S :=
    eventually_atTop.mp (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hRS'))
  by_contra hcon
  have hex : ∀ k, max k0 (j + 1) ≤ k → ∃ ab : Fin (B.n k) × Fin (B.n k),
      (B.D k).IsSubchainFrom ab.1 ab.2 R S := fun k hk => by
    obtain ⟨a, b, h⟩ := (B.D k).exists_isSubchainFrom (B.mem_levelUnion k R) (B.mem_levelUnion k S)
      (fun t hRt hSt => by
        have := dist_le_diam_of_mem (B.bdd k t) hRt hSt
        linarith [B.diam_le k t, hk0 k (le_of_max_le_left hk)])
    exact ⟨(a, b), h⟩
  let A : ℕ → Set X := fun k =>
    if h : max k0 (j + 1) ≤ k then (B.D k).span (hex k h).choose.1 (hex k h).choose.2 else ∅
  have hAspec : ∀ k (h : max k0 (j + 1) ≤ k), A k = (B.D k).span (hex k h).choose.1
      (hex k h).choose.2 := fun k h => by simp only [A, dif_pos h]
  set O₁ := (B.D j).link ⟨0, hj⟩
  set O₂ := (B.D j).link ⟨B.n j - 1, by omega⟩
  let I₁ := {k | max k0 (j + 1) ≤ k ∧ Disjoint (A k) O₁}
  let I₂ := {k | max k0 (j + 1) ≤ k ∧ Disjoint (A k) O₂}
  have hcov : Ici (max k0 (j + 1)) ⊆ I₁ ∪ I₂ := by
    intro k hk
    have hk' : max k0 (j + 1) ≤ k := hk
    by_contra hk2
    simp only [mem_union, mem_setOf_eq, not_or, not_and, I₁, I₂] at hk2
    have d1 := hk2.1 hk'
    have d2 := hk2.2 hk'
    rw [hAspec k hk', not_disjoint_iff] at d1 d2
    obtain ⟨x, hx, hx1⟩ := d1
    obtain ⟨y, hy, hy2⟩ := d2
    obtain ⟨t, ht1, ht2, hxt⟩ := Chain.mem_span.mp hx
    obtain ⟨u, hu1, hu2, hyu⟩ := Chain.mem_span.mp hy
    exact hcon ⟨k, by omega, _, _, (hex k hk').choose_spec, ⟨t, ht1, ht2, x, hxt, hx1⟩,
      ⟨u, hu1, hu2, y, hyu, hy2⟩⟩
  have main : ∀ I : Set ℕ, I ⊆ Ici (max k0 (j + 1)) → I.Infinite → ∀ O : Set X, IsOpen O →
      O.Nonempty → (∀ k ∈ I, Disjoint (A k) O) → False := by
    intro I hI hinf O hO hOne hdisj
    refine false_of_disjoint_limit hcomp hinf A (fun k hk => ?_) (fun k hk => ?_)
      (fun k hk => ?_) hO hOne hdisj
    · rw [hAspec k (hI hk)]
      exact Chain.chainedAt_span _ _ _ (B.bdd k) (B.diam_le k)
    · rw [hAspec k (hI hk)]
      exact ((hex k (hI hk)).choose_spec.mem_span).1
    · rw [hAspec k (hI hk)]
      exact ((hex k (hI hk)).choose_spec.mem_span).2
  rcases infinite_union.mp ((Ici_infinite _).mono hcov) with h | h
  · exact main I₁ (fun k hk => hk.1) h O₁ ((B.D j).isOpen _) ((B.D j).link_nonempty _)
      (fun k hk => hk.2)
  · exact main I₂ (fun k hk => hk.1) h O₂ ((B.D j).isOpen _) ((B.D j).link_nonempty _)
      (fun k hk => hk.2)

/-- **One step** (as `Description.exists_step`). -/
theorem exists_step [CompactSpace X] {R S : X} (hRS : R ≠ S)
    (hcomp : S ∉ composant (univ : Set X) R) (L : ℕ) :
    ∃ k, L < k ∧ ∃ N, ∃ F : Chain X N, F.IsFrom R S ∧ F.IsConsolidationOf (B.D k) ∧
      (∀ u, ∃ t, closure (F.link u) ⊆ (B.D L).link t) ∧
      (∀ u, diam (F.link u) ≤ 1 / ((L : ℝ) + 1)) := by
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun t => (B.D L).isOpen t) (fun x _ => B.mem_levelUnion L x)
  set η := min δ (1 / ((L : ℝ) + 1)) with hη
  have hηpos : 0 < η := lt_min hδ (by positivity)
  obtain ⟨m0, hm0⟩ : ∃ m0, ∀ m : ℕ, m0 ≤ m → 1 / ((m : ℝ) + 1) < η / 3 :=
    eventually_atTop.mp (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds (by linarith)))
  obtain ⟨m1, hm1⟩ : ∃ m1, ∀ m, m1 ≤ m → 5 ≤ B.n m :=
    eventually_atTop.mp (B.eventually_five_le hRS)
  set m := max (max m0 m1) (L + 1)
  have hLm : L + 1 ≤ m := le_max_right _ _
  have hm5 : 5 ≤ B.n m := hm1 m (by omega)
  have hεm : 1 / ((m : ℝ) + 1) < η / 3 := hm0 m (by omega)
  obtain ⟨k, hmk, a, b, hsubc, ⟨t₁, ht₁a, ht₁b, hm₁⟩, ⟨t₂, ht₂a, ht₂b, hm₂⟩⟩ :=
    B.exists_subchain_meets_ends hRS hcomp m (by omega)
  have hcr := B.crooked_of_lt hmk
  have final : ∀ (N : ℕ) (F : Chain X N),
      (∀ u, ∃ j, F.link u ⊆ (B.D m).unionRange j 3) →
      (∀ u, ∃ t, closure (F.link u) ⊆ (B.D L).link t) ∧
      (∀ u, diam (F.link u) ≤ 1 / ((L : ℝ) + 1)) := by
    intro N F hF3
    have hdist : ∀ u, ∀ x ∈ F.link u, ∀ y ∈ F.link u, dist x y ≤ 3 * (1 / ((m : ℝ) + 1)) := by
      intro u x hx y hy
      obtain ⟨j, hj⟩ := hF3 u
      exact Chain.dist_le_of_mem_unionRange (B.bdd m) (B.diam_le m) (hj hx) (hj hy)
    refine ⟨fun u => ?_, fun u => ?_⟩
    · obtain ⟨x0, hx0⟩ := F.link_nonempty u
      obtain ⟨t, ht⟩ := hleb x0 (mem_univ x0)
      refine ⟨t, subset_trans ?_ ht⟩
      have hsub : F.link u ⊆ closedBall x0 (3 * (1 / ((m : ℝ) + 1))) := fun y hy => by
        rw [mem_closedBall]; exact hdist u y hy x0 hx0
      refine subset_trans (isClosed_closedBall.closure_subset_iff.mpr hsub)
        (closedBall_subset_ball ?_)
      linarith [min_le_left δ (1 / ((L : ℝ) + 1))]
    · refine diam_le_of_forall_dist_le (by positivity) (fun x hx y hy => ?_)
      have := hdist u x hx y hy
      linarith [min_le_right δ (1 / ((L : ℝ) + 1))]
  obtain ⟨hab, hor | hor⟩ := hsubc
  · obtain ⟨q, β, hβ, hF, hF3⟩ := Chain.exists_blockChain hm5 hcr hab hor ⟨ht₁a, ht₁b⟩
      ⟨ht₂a, ht₂b⟩ hm₁ hm₂
    have hcons := Chain.ofBlocks_isConsolidationOf (B.D k) β hβ
    exact ⟨k, by omega, q, _, hF, hcons, final _ _ hF3⟩
  · obtain ⟨q, β, hβ, hF, hF3⟩ := Chain.exists_blockChain hm5 hcr hab hor ⟨ht₁a, ht₁b⟩
      ⟨ht₂a, ht₂b⟩ hm₁ hm₂
    have hcons := (Chain.ofBlocks_isConsolidationOf (B.D k) β hβ).reverse
    exact ⟨k, by omega, q, _, hF.reverse, hcons, final _ _ (fun u => hF3 (Fin.rev u))⟩

include B in
/-- **A description of the whole space from `R` to `S`** (Bing's sequence `D_1, D_2, …`), for
`R`, `S` in different composants. -/
theorem exists_description [CompactSpace X] {R S : X} (hRS : R ≠ S)
    (hcomp : S ∉ composant (univ : Set X) R) :
    ∃ Δ : Description X R S, Δ.M = univ := by
  choose K hK N F hF1 hF2 hF3 hF4 using B.exists_step hRS hcomp
  let lev : ℕ → ℕ := fun i => Nat.rec 0 (fun _ l => K l + 1) i
  have hlev0 : lev 0 = 0 := rfl
  have hlevs : ∀ i, lev (i + 1) = K (lev i) + 1 := fun i => rfl
  have hlevge : ∀ i, i ≤ lev i := by
    intro i
    induction i with
    | zero => simp [hlev0]
    | succ i ih => rw [hlevs]; have := hK (lev i); omega
  have hbdd : ∀ L (u : Fin (N L)), Bornology.IsBounded ((F L).link u) := by
    intro L u
    obtain ⟨t, ht⟩ := hF3 L u
    exact (B.bdd L t).subset (subset_closure.trans ht)
  refine ⟨{
    n := fun i => N (lev i)
    D := fun i => F (lev i)
    isFrom := fun i => hF1 (lev i)
    crooked := fun i => ?_
    closure_subset := fun i t => ?_
    ε := fun i => 1 / ((i : ℝ) + 1)
    ε_pos := fun i => by positivity
    ε_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
    bdd := fun i t => hbdd (lev i) t
    diam_le := fun i t => ?_ }, ?_⟩
  · show (F (lev (i + 1))).IsCrookedIn' (F (lev i))
    have href : (F (lev (i + 1))).Refines (B.D (K (lev i) + 1)) := by
      intro u
      obtain ⟨t, ht⟩ := hF3 (lev (i + 1)) u
      exact ⟨t, subset_closure.trans ht⟩
    exact Chain.isCrookedIn'_of_refines href
      (Chain.isCrookedIn'_of_isConsolidationOf (hF2 (lev i)) (B.crooked (K (lev i))))
  · show ∃ s, closure ((F (lev (i + 1))).link t) ⊆ (F (lev i)).link s
    obtain ⟨s1, hs1⟩ := hF3 (lev (i + 1)) t
    obtain ⟨s2, hs2⟩ := B.closure_subset (K (lev i)) s1
    obtain ⟨s3, hs3⟩ := (hF2 (lev i)).1 s2
    exact ⟨s3, hs1.trans (subset_closure.trans (hs2.trans hs3))⟩
  · show diam ((F (lev i)).link t) ≤ 1 / ((i : ℝ) + 1)
    refine (hF4 (lev i) t).trans ?_
    gcongr
    exact_mod_cast hlevge i
  · show (⋂ i, (F (lev i)).union) = univ
    refine eq_univ_of_forall fun z => mem_iInter.mpr fun i => ?_
    rw [(hF2 (lev i)).union_eq]
    exact B.mem_levelUnion _ z

end PreDesc

/-- **Bing 1951, Theorem 1, the body of the proof, for the whole space.** A compact chainable
hereditarily indecomposable metric space with points `p`, `q` in different composants admits a
description from `p` to `q` describing the whole space. -/
theorem exists_description_univ [CompactSpace X]
    (hHI : ∀ K : Set X, Fold.Q78.IsContinuum K → Fold.Q78.IsIndecomposable K)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ univ ⊆ D.union)
    {p q : X} (hpq : p ≠ q) (hcomp : q ∉ composant (univ : Set X) p) :
    ∃ Δ : Description X p q, Δ.M = univ := by
  obtain ⟨B⟩ := exists_preDesc hHI hsnake
  exact B.exists_description hpq hcomp

end PA51

end HPC.Plane
