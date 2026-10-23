import HPC.Jones.Basic

/-!
# Batch 135: Jones 1948, Theorem 6

Jones's nested construction: open sets `D = D₀ ⊇ D̄₁ ⊇ D₁ ⊇ D̄₂ ⊇ …` and closed sets
`M₀ ⊇ M₁ ⊇ M₂ ⊇ …` with `diam Mₙ → 0`, such that `X` is not aposyndetic at each point of `Dₙ` with
respect to some point of `Mₙ`, and `Dₙ₊₁` misses the component `Cₙ` of `z` in the complement of a
small neighbourhood `Vₙ` of `Mₙ₊₁`. Then `x₀ ∈ ⋂ Dₙ` and `y₀ ∈ ⋂ Mₙ`: a continuum from `x₀` to `z`
missing `y₀` misses some `Vₙ`, so lies in `Cₙ`, which does not contain `x₀`.

The one step of the construction is `theorem6_step`. The finite cover of `Kₙ` by closed sets of
small diameter and the choice of `Mₙ₊₁` with `L(Mₙ₊₁)` containing an open set are as in Jones (the
latter by Baire, `exists_ball_subset_of_closed_cover`); `Dₙ₊₁ ∩ Cₙ = ∅` is possible because the
continuum `Cₙ` cannot contain an open set containing a point of `L(Mₙ₊₁)`.

Jones's footnote 6 says `D` may meet `M₀`; the theorem is proved here, as stated in the skeleton,
with `D ∩ M₀ = ∅`, which is what gives `x₀ ≠ y₀`. The hypothesis \"`D` nonempty\" is necessary:
`not_theorem6_printed`.
-/

namespace HPC.Jones

open Set Topology Filter Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- The invariant of Jones's construction: `D` open nonempty, `M` closed, and `X` not aposyndetic
at each point of `D` with respect to some point of `M`. -/
def Thm6Inv (D M : Set X) : Prop :=
  IsOpen D ∧ D.Nonempty ∧ IsClosed M ∧ ∀ x ∈ D, ∃ y ∈ M, ¬ AposAt x y

omit [CompactSpace X] in
theorem Thm6Inv.nonempty_right {D M : Set X} (h : Thm6Inv D M) : M.Nonempty := by
  obtain ⟨-, ⟨x, hx⟩, -, h⟩ := h
  obtain ⟨y, hy, -⟩ := h x hx
  exact ⟨y, hy⟩

/-- **One step of Jones's construction for Theorem 6.** -/
theorem theorem6_step {D M : Set X} (h : Thm6Inv D M) {z : X} (hz : z ∉ M) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ D' M' : Set X, ∃ δ : ℝ, Thm6Inv D' M' ∧ closure D' ⊆ D ∧ M' ⊆ M ∧
      (∀ a ∈ M', ∀ b ∈ M', dist a b < ε) ∧ 0 < δ ∧ δ < ε ∧ z ∉ thickening δ M' ∧
      Disjoint D' (connectedComponentIn (thickening δ M')ᶜ z) := by
  obtain ⟨hD, hDne, hM, hinv⟩ := h
  obtain ⟨t, -, htfin, hcovM⟩ := finite_cover_balls_of_compact hM.isCompact
    (by positivity : (0 : ℝ) < ε / 3)
  haveI : Countable t := htfin.countable.to_subtype
  set g : t → Set X := fun m => M ∩ closedBall (m : X) (ε / 3) with hg
  have hgcl : ∀ m, IsClosed (g m) := fun m => hM.inter isClosed_closedBall
  have hLcl : ∀ m, IsClosed {x : X | ∃ y ∈ g m, ¬ AposAt x y} := fun m =>
    isClosed_exists_not_aposAt_right (hgcl m)
  have hcovD : D ⊆ ⋃ m, {x : X | ∃ y ∈ g m, ¬ AposAt x y} := by
    intro x hx
    obtain ⟨y, hyM, hxy⟩ := hinv x hx
    obtain ⟨m, hm, hym⟩ := mem_iUnion₂.mp (hcovM hyM)
    exact mem_iUnion.mpr ⟨⟨m, hm⟩, y, ⟨hyM, ball_subset_closedBall hym⟩, hxy⟩
  obtain ⟨m, w, r, hr, hball⟩ := exists_ball_subset_of_closed_cover hD hDne hLcl hcovD
  set M' := g m with hM'
  have hinv' : ∀ x ∈ ball w r, ∃ y ∈ M', ¬ AposAt x y := fun x hx => (hball hx).2
  have hM'ne : M'.Nonempty := by
    obtain ⟨y, hy, -⟩ := hinv' w (mem_ball_self hr)
    exact ⟨y, hy⟩
  have hzM' : z ∉ M' := fun h => hz h.1
  have hpos : 0 < infDist z M' := ((hgcl m).notMem_iff_infDist_pos hM'ne).mp hzM'
  set δ := min (ε / 2) (infDist z M' / 2) with hδdef
  have hδ : 0 < δ := lt_min (half_pos hε) (half_pos hpos)
  have hzT : z ∉ thickening δ M' := by
    rw [mem_thickening_iff_infDist_lt hM'ne, not_lt]
    exact (min_le_right _ _).trans (half_le_self hpos.le)
  set C := connectedComponentIn (thickening δ M')ᶜ z with hC
  have hCcl : IsClosed C := isClosed_connectedComponentIn' isOpen_thickening.isClosed_compl z
  have hCcont : Fold.Q78.IsContinuum C :=
    ⟨hCcl.isCompact, isConnected_connectedComponentIn_iff.mpr hzT⟩
  have hM'C : ∀ y ∈ M', y ∉ C := fun y hy hyC =>
    connectedComponentIn_subset _ _ hyC (self_subset_thickening hδ M' hy)
  have hex : ∃ w' ∈ ball w r, w' ∉ C := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨y, hy, hna⟩ := hinv' w (mem_ball_self hr)
    exact hna ⟨C, ball w r, hCcont, isOpen_ball, mem_ball_self hr, hcon, hM'C y hy⟩
  obtain ⟨w', hw'B, hw'C⟩ := hex
  have hO : IsOpen (ball w r ∩ Cᶜ) := isOpen_ball.inter hCcl.isOpen_compl
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hO w' ⟨hw'B, hw'C⟩
  have hsub : ball w' (ρ / 2) ⊆ ball w r ∩ Cᶜ :=
    (ball_subset_ball (half_le_self hρ.le)).trans hρsub
  refine ⟨ball w' (ρ / 2), M', δ, ⟨isOpen_ball, ⟨w', mem_ball_self (half_pos hρ)⟩, hgcl m,
    fun x hx => hinv' x (hsub hx).1⟩, ?_, inter_subset_left, ?_, hδ,
    (min_le_left _ _).trans_lt (half_lt_self hε), hzT, ?_⟩
  · refine (closure_ball_subset_closedBall).trans ?_
    refine (closedBall_subset_ball (half_lt_self hρ)).trans ?_
    exact fun x hx => (hball (hρsub hx).1).1
  · intro a ha b hb
    have h1 : dist a (m : X) ≤ ε / 3 := ha.2
    have h2 : dist b (m : X) ≤ ε / 3 := hb.2
    calc dist a b ≤ dist a (m : X) + dist (m : X) b := dist_triangle _ _ _
      _ = dist a (m : X) + dist b (m : X) := by rw [dist_comm (m : X) b]
      _ < ε := by linarith
  · rw [Set.disjoint_left]
    intro x hx hxC
    exact (hsub hx).2 hxC

/-- **Theorem 6.** Let `D` be open and nonempty, and `M₀` closed with `D ∩ M₀ = ∅`. Suppose that
for each `x ∈ D` there is `y ∈ M₀` such that `X` is not aposyndetic at `x` with respect to `y`.
Then for each `z ∉ M₀` there are `x₀ ∈ D` and `y₀ ∈ M₀` with `y₀` cutting `x₀` from `z`. -/
theorem theorem6 {D M₀ : Set X} (hD : IsOpen D) (hDne : D.Nonempty) (hM₀ : IsClosed M₀)
    (hDM : Disjoint D M₀) (h : ∀ x ∈ D, ∃ y ∈ M₀, ¬ AposAt x y) {z : X} (hz : z ∉ M₀) :
    ∃ x₀ ∈ D, ∃ y₀ ∈ M₀, CutsPts y₀ x₀ z := by
  have step : ∀ (p : Set X × Set X) (n : ℕ), Thm6Inv p.1 p.2 → z ∉ p.2 →
      ∃ q : Set X × Set X, ∃ δ : ℝ, Thm6Inv q.1 q.2 ∧ closure q.1 ⊆ p.1 ∧ q.2 ⊆ p.2 ∧
        (∀ a ∈ q.2, ∀ b ∈ q.2, dist a b < 1 / ((n : ℝ) + 1)) ∧ 0 < δ ∧
        δ < 1 / ((n : ℝ) + 1) ∧ z ∉ thickening δ q.2 ∧
        Disjoint q.1 (connectedComponentIn (thickening δ q.2)ᶜ z) := by
    intro p n hp hzp
    obtain ⟨D', M', δ, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      theorem6_step hp hzp (ε := 1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨(D', M'), δ, h1, h2, h3, h4, h5, h6, h7, h8⟩
  choose! F δ hF using step
  let seq : ℕ → Set X × Set X := fun n => Nat.rec (D, M₀) (fun k p => F p k) n
  have hseqS : ∀ n, seq (n + 1) = F (seq n) n := fun n => rfl
  have hgood : ∀ n, Thm6Inv (seq n).1 (seq n).2 ∧ z ∉ (seq n).2 := by
    intro n
    induction n with
    | zero => exact ⟨⟨hD, hDne, hM₀, h⟩, hz⟩
    | succ n ih =>
      rw [hseqS]
      obtain ⟨h1, -, h3, -⟩ := hF (seq n) n ih.1 ih.2
      exact ⟨h1, fun hzz => ih.2 (h3 hzz)⟩
  have hP := fun n => hF (seq n) n (hgood n).1 (hgood n).2
  simp only [← hseqS] at hP
  -- the point `x₀`
  obtain ⟨x₀, hx₀⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => closure (seq n).1) (fun n => (hP n).2.1.trans subset_closure)
    (fun n => (hgood n).1.2.1.closure) isClosed_closure.isCompact (fun n => isClosed_closure)
  have hx₀n : ∀ n, x₀ ∈ (seq n).1 := fun n => (hP n).2.1 (mem_iInter.mp hx₀ (n + 1))
  -- the point `y₀`
  obtain ⟨y₀, hy₀⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => (seq n).2) (fun n => (hP n).2.2.1) (fun n => (hgood n).1.nonempty_right)
    (hgood 0).1.2.2.1.isCompact (fun n => (hgood n).1.2.2.1)
  have hy₀n : ∀ n, y₀ ∈ (seq n).2 := fun n => mem_iInter.mp hy₀ n
  have hx₀D : x₀ ∈ D := hx₀n 0
  have hy₀M : y₀ ∈ M₀ := hy₀n 0
  refine ⟨x₀, hx₀D, y₀, hy₀M, fun he => Set.disjoint_left.mp hDM hx₀D (he ▸ hy₀M),
    fun he => hz (he ▸ hy₀M), fun he => ?_, fun K hK hx₀K hzK => ?_⟩
  · -- `x₀ ≠ z`
    obtain ⟨-, -, -, -, -, -, hzT, hdisj⟩ := hP 0
    have hzC : z ∈ connectedComponentIn (thickening (δ (seq 0) 0) (seq (0 + 1)).2)ᶜ z :=
      mem_connectedComponentIn (show z ∈ (thickening (δ (seq 0) 0) (seq (0 + 1)).2)ᶜ from hzT)
    have hz1 : z ∈ (seq 1).1 := he ▸ hx₀n 1
    exact Set.disjoint_left.mp hdisj hz1 hzC
  · by_contra hy₀K
    have hKne : K.Nonempty := ⟨z, hzK⟩
    have hη : 0 < infDist y₀ K := (hK.1.isClosed.notMem_iff_infDist_pos hKne).mp hy₀K
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hη)
    obtain ⟨-, -, -, hdiam, -, hδn, hzT, hdisj⟩ := hP n
    have hKT : K ⊆ (thickening (δ (seq n) n) (seq (n + 1)).2)ᶜ := by
      intro k hk hkT
      obtain ⟨m, hm, hkm⟩ := mem_thickening_iff.mp hkT
      have h1 := hdiam m hm y₀ (hy₀n (n + 1))
      have h2 : infDist y₀ K ≤ dist y₀ k := infDist_le_dist_of_mem hk
      have h3 : dist y₀ k ≤ dist k m + dist m y₀ := by
        rw [dist_comm y₀ k]; exact dist_triangle _ _ _
      linarith
    have hKC := hK.2.isPreconnected.subset_connectedComponentIn hzK hKT
    exact Set.disjoint_left.mp hdisj (hx₀n (n + 1)) (hKC hx₀K)

omit [CompactSpace X] in
/-- **Theorem 6 as printed (without \"`D` nonempty\") is false** in every nonempty space: with
`D = M₀ = ∅` the hypotheses hold vacuously and the conclusion asks for a point of `D`. -/
theorem not_theorem6_printed [Nonempty X] :
    ¬ ∀ (D M₀ : Set X), IsOpen D → IsClosed M₀ → Disjoint D M₀ →
      (∀ x ∈ D, ∃ y ∈ M₀, ¬ AposAt x y) → ∀ z : X, z ∉ M₀ →
        ∃ x₀ ∈ D, ∃ y₀ ∈ M₀, CutsPts y₀ x₀ z := by
  intro h
  obtain ⟨x₀, hx₀, -⟩ := h ∅ ∅ isOpen_empty isClosed_empty (disjoint_empty _)
    (fun x hx => absurd hx (notMem_empty x)) (Classical.arbitrary X) (notMem_empty _)
  exact notMem_empty x₀ hx₀

end HPC.Jones
