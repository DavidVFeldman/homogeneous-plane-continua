import HPC.PseudoArc.Description
import HPC.Covers.Matching

/-!
# Bing 1948, Theorem 12: two descriptions give a homeomorphism

Conditional on `Description.PatternFollowing` (Theorem 6), which is a hypothesis here and is
to be proved in a later batch. Everything else — the alternating construction, the mesh
bookkeeping, condition (4) of Theorem 11 from pattern following, and the tracking of `P`
and `Q` — is proved.

English proof: COMMISSION.md §3. All statements are proved; the file contains no `sorry`.
-/

namespace HPC

open Set Metric

variable {X₁ X₂ : Type*} [MetricSpace X₁] [MetricSpace X₂]

/-- **The matching lemma.** If `Y₁` follows the pattern `x` in `Z₁` and `Y₂` follows the same
pattern in `Z₂`, then whenever the `j`-th link of `Y₁` meets the `k`-th link of `Z₁`, the
`j`-th link of `Y₂` comes within `diam` of a link of `Z₂` of the `k`-th link of `Z₂`. This is
condition (4) of Theorem 11 with `ε` any bound exceeding the mesh of `Z₂`. -/
theorem Chain.pattern_matching {N m : ℕ}
    {Y₁ : Chain X₁ N} {Z₁ : Chain X₁ m} {Y₂ : Chain X₂ N} {Z₂ : Chain X₂ m}
    (x : Fin N → Fin m) (h₁ : Y₁.FollowsPattern x Z₁) (h₂ : Y₂.FollowsPattern x Z₂)
    {ε : ℝ} (hε : ∀ s, Metric.diam (Z₂.link s) < ε) (hb : ∀ s, Bornology.IsBounded (Z₂.link s))
    (j : Fin N) (k : Fin m) (hjk : (Y₁.link j ∩ Z₁.link k).Nonempty) :
    ∃ p ∈ Y₂.link j, ∃ q ∈ Z₂.link k, dist p q < ε := by
  obtain ⟨z, hz1, hz2⟩ := hjk
  have hadj : ((x j : ℤ) - (k : ℤ)).natAbs ≤ 1 := (Z₁.adjacent _ _).mp ⟨z, h₁ j hz1, hz2⟩
  obtain ⟨q, hq1, hq2⟩ := (Z₂.adjacent (x j) k).mpr hadj
  obtain ⟨p, hp⟩ := Y₂.link_nonempty j
  exact ⟨p, hp, q, hq2,
    lt_of_le_of_lt (Metric.dist_le_diam_of_mem (hb (x j)) (h₂ j hp) hq1) (hε (x j))⟩

/-- A chain following a pattern in `Z` has mesh at most the mesh of `Z`. -/
theorem Chain.diam_le_of_followsPattern {N m : ℕ} {Y : Chain X₁ N} {Z : Chain X₁ m}
    (x : Fin N → Fin m) (h : Y.FollowsPattern x Z) {ε : ℝ}
    (hZ : ∀ s, Metric.diam (Z.link s) ≤ ε) (hb : ∀ s, Bornology.IsBounded (Z.link s)) :
    ∀ t, Metric.diam (Y.link t) ≤ ε :=
  fun t => (Metric.diam_mono (h t) (hb (x t))).trans (hZ (x t))

/-- A refinement of `Z` has mesh at most the mesh of `Z`. -/
theorem Chain.diam_le_of_refines {N m : ℕ} {Y : Chain X₁ N} {Z : Chain X₁ m}
    (h : Y.Refines Z) {ε : ℝ}
    (hZ : ∀ s, Metric.diam (Z.link s) ≤ ε) (hb : ∀ s, Bornology.IsBounded (Z.link s)) :
    ∀ t, Metric.diam (Y.link t) ≤ ε :=
  Chain.diam_le_of_followsPattern (Chain.refineIdx h) (Chain.refineIdx_subset h) hZ hb

/-- A consolidation of a level, being a chain from `P` to `Q` refined by that level, is
followed in it by a pattern: the refinement map of the level into the consolidation is a
pattern. Conversely every refinement `Y.Refines Z` of chains from `P` to `Q` yields a pattern
`x` with `Y.FollowsPattern x Z`. -/
theorem Chain.exists_pattern_of_refines {N m : ℕ} {Y : Chain X₁ N} {Z : Chain X₁ m}
    {P Q : X₁} (hY : Y.IsFrom P Q) (hZ : Z.IsFrom P Q) (h : Y.Refines Z) :
    ∃ x : Fin N → Fin m, Description.IsPattern x ∧ Y.FollowsPattern x Z := by
  refine ⟨Chain.refineIdx h, ?_, Chain.refineIdx_subset h⟩
  obtain ⟨hN, hP, hQ, -, -⟩ := hY
  obtain ⟨hm, -, -, hPuZ, hQuZ⟩ := hZ
  refine ⟨hN, hm, hPuZ _ (Chain.refineIdx_subset h _ hP),
    hQuZ _ (Chain.refineIdx_subset h _ hQ), fun t t' ht => ?_⟩
  refine Chain.pattern_lipschitz (Chain.refineIdx_subset h) t' t ?_
  rw [Y.adjacent_iff]
  omega

/-! ### The alternating construction

Theorem 12 is proved by building, level by level, a pair of chains with the same number of
links, one in each space, following the same pattern in the pair one level up. The two sides
alternate roles: at each step the side that is currently a level of its description gets
refined by a deeper level, and the other side is made to follow the resulting pattern by
`PatternFollowing`. A `Rung` packages one level of this construction. -/

namespace Description

variable {X : Type*} [MetricSpace X]

/-- `Δ.CanFollow lv C`: every pattern in the chain `C` is followed by a consolidation of a
level of `Δ` deeper than `lv`. Under `Δ.PatternFollowing` this holds for `C = Δ.D lv`; it is
the property of a side of the construction that lets the *other* side be refined. -/
def CanFollow {P Q : X} (Δ : Description X P Q) (lv : ℕ) {N : ℕ} (C : Chain X N) : Prop :=
  ∀ (N' : ℕ) (x : Fin N' → Fin N), IsPattern x →
    ∃ a, lv < a ∧ ∃ E : Chain X N', E.IsFrom P Q ∧ E.IsConsolidationOf (Δ.D a) ∧
      E.FollowsPattern x C

theorem canFollow_level {P Q : X} {Δ : Description X P Q} (h : Δ.PatternFollowing) (i : ℕ) :
    Δ.CanFollow i (Δ.D i) := fun N' x hx => h i N' x hx

/-- A consolidation of a level covers `M`. -/
theorem M_subset_consolidation {P Q : X} (Δ : Description X P Q) {N lv : ℕ} {C : Chain X N}
    (h : C.IsConsolidationOf (Δ.D lv)) : Δ.M ⊆ ⋃ k, C.link k :=
  (Δ.M_subset_union lv).trans (Chain.union_subset_of_refines h.1)

/-- Every link of a consolidation of a level meets `M`. -/
theorem consolidation_link_inter_M_nonempty [CompactSpace X] {P Q : X} (Δ : Description X P Q)
    {N lv : ℕ} {C : Chain X N} (h : C.IsConsolidationOf (Δ.D lv)) (k : Fin N) :
    (C.link k ∩ Δ.M).Nonempty := by
  obtain ⟨S, hS⟩ := h.2 k
  obtain ⟨z, hz⟩ := C.link_nonempty k
  rw [hS] at hz
  simp only [Set.mem_iUnion, exists_prop] at hz
  obtain ⟨j, hjS, -⟩ := hz
  obtain ⟨w, hw1, hw2⟩ := Δ.link_inter_M_nonempty lv j
  refine ⟨w, ?_, hw2⟩
  rw [hS]
  exact Set.subset_biUnion_of_mem (u := fun i => (Δ.D lv).link i) hjS hw1

/-- **One half-step of the construction.** Side `B`, a consolidation of a level of `ΔB`, is
refined by a deeper level of `ΔB` of mesh at most `δ`; the refinement gives a pattern, and
side `A`, which can follow patterns, produces a partner following the same pattern. -/
theorem exists_half_step {XA XB : Type*} [MetricSpace XA] [MetricSpace XB]
    {PA QA : XA} {PB QB : XB} (ΔA : Description XA PA QA) (ΔB : Description XB PB QB)
    {N lvA lvB : ℕ} {CA : Chain XA N} {CB : Chain XB N}
    (hcanA : ΔA.CanFollow lvA CA)
    (hfromB : CB.IsFrom PB QB) (hconsB : CB.IsConsolidationOf (ΔB.D lvB))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c, lvB ≤ c ∧ ΔB.ε c ≤ δ ∧ ∃ lvA', lvA < lvA' ∧ ∃ CA' : Chain XA (ΔB.n c),
      CA'.IsFrom PA QA ∧ CA'.IsConsolidationOf (ΔA.D lvA') ∧
      ∃ x : Fin (ΔB.n c) → Fin N, (ΔB.D c).FollowsPattern x CB ∧ CA'.FollowsPattern x CA := by
  obtain ⟨c, hlvc, href, hεc⟩ := ΔB.exists_level_refining hconsB hδ
  obtain ⟨x, hpat, hfollow⟩ := Chain.exists_pattern_of_refines (ΔB.isFrom c) hfromB href
  obtain ⟨lvA', hlt, E, hE1, hE2, hE3⟩ := hcanA _ x hpat
  exact ⟨c, hlvc, hεc, lvA', hlt, E, hE1, hE2, x, hfollow, hE3⟩

end Description

/-- One level of the alternating construction: a pair of chains with the same number of links,
one in each space, each a chain from its `P` to its `Q` and a consolidation of a level of its
description, with a common mesh bound `mesh`, and such that at least one of the two sides can
follow patterns and has the sharper mesh bound `mfollow`. -/
structure Rung {P₁ Q₁ : X₁} {P₂ Q₂ : X₂}
    (Δ₁ : Description X₁ P₁ Q₁) (Δ₂ : Description X₂ P₂ Q₂) where
  /-- the common number of links -/
  N : ℕ
  C₁ : Chain X₁ N
  C₂ : Chain X₂ N
  isFrom₁ : C₁.IsFrom P₁ Q₁
  isFrom₂ : C₂.IsFrom P₂ Q₂
  lv₁ : ℕ
  lv₂ : ℕ
  cons₁ : C₁.IsConsolidationOf (Δ₁.D lv₁)
  cons₂ : C₂.IsConsolidationOf (Δ₂.D lv₂)
  /-- a bound on the mesh of both sides -/
  mesh : ℝ
  /-- a bound on the mesh of the side that can follow patterns -/
  mfollow : ℝ
  mesh_pos : 0 < mesh
  mfollow_pos : 0 < mfollow
  diam₁ : ∀ t, Metric.diam (C₁.link t) ≤ mesh
  diam₂ : ∀ t, Metric.diam (C₂.link t) ≤ mesh
  follow : (Δ₁.CanFollow lv₁ C₁ ∧ ∀ t, Metric.diam (C₁.link t) ≤ mfollow) ∨
           (Δ₂.CanFollow lv₂ C₂ ∧ ∀ t, Metric.diam (C₂.link t) ≤ mfollow)

namespace Rung

variable {P₁ Q₁ : X₁} {P₂ Q₂ : X₂}

/-- The first level of the construction: a level of `Δ₁` of mesh below `1/2` and below
`dist P₁ Q₁`, matched on side 2 by a consolidation of a level of `Δ₂` with the same number of
links. -/
theorem exists_base [CompactSpace X₂]
    (Δ₁ : Description X₁ P₁ Q₁) (Δ₂ : Description X₂ P₂ Q₂)
    (hpf₁ : Δ₁.PatternFollowing) (hPQ₁ : P₁ ≠ Q₁) (hPQ₂ : P₂ ≠ Q₂) :
    ∃ r : Rung Δ₁ Δ₂, r.mfollow = 1 / 2 := by
  have hd : (0 : ℝ) < dist P₁ Q₁ := dist_pos.mpr hPQ₁
  obtain ⟨a, ha1, ha2⟩ : ∃ a, Δ₁.ε a < 1 / 2 ∧ Δ₁.ε a < dist P₁ Q₁ :=
    ((Filter.Tendsto.eventually_lt_const (by norm_num) Δ₁.ε_tendsto).and
      (Filter.Tendsto.eventually_lt_const hd Δ₁.ε_tendsto)).exists
  have h2le : 2 ≤ Δ₁.n a := Δ₁.two_le_n_of_lt a ha2
  obtain ⟨b, hb⟩ : ∃ b, Δ₁.n a ≤ Δ₂.n b :=
    ((Δ₂.n_tendsto_atTop hPQ₂).eventually_ge_atTop (Δ₁.n a)).exists
  obtain ⟨F, hF1, hF2⟩ :=
    Chain.exists_consolidation_isFrom (Δ₂.D b) P₂ Q₂ (Δ₂.isFrom b) (Δ₁.n a) h2le hb
  have huniv : ∀ t, Metric.diam (F.link t) ≤ Metric.diam (Set.univ : Set X₂) + 1 := by
    intro t
    have := Metric.diam_mono (Set.subset_univ (F.link t)) isBounded_of_compactSpace
    linarith
  exact ⟨{ N := Δ₁.n a
           C₁ := Δ₁.D a
           C₂ := F
           isFrom₁ := Δ₁.isFrom a
           isFrom₂ := hF1
           lv₁ := a
           lv₂ := b
           cons₁ := Chain.isConsolidationOf_self _
           cons₂ := hF2
           mesh := max (1 / 2) (Metric.diam (Set.univ : Set X₂) + 1)
           mfollow := 1 / 2
           mesh_pos := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
           mfollow_pos := by norm_num
           diam₁ := fun t => ((Δ₁.diam_le a t).trans ha1.le).trans (le_max_left _ _)
           diam₂ := fun t => (huniv t).trans (le_max_right _ _)
           follow := Or.inl ⟨Description.canFollow_level hpf₁ a,
             fun t => (Δ₁.diam_le a t).trans ha1.le⟩ }, rfl⟩

/-- **The step of the construction.** The side that can follow patterns keeps its mesh bound
and loses that ability; the other side is refined by a level of mesh at most `δ`, and so
becomes a level, which can follow patterns. Both new chains follow the same pattern in the
two old ones. -/
theorem exists_next [CompactSpace X₁] [CompactSpace X₂]
    {Δ₁ : Description X₁ P₁ Q₁} {Δ₂ : Description X₂ P₂ Q₂}
    (hpf₁ : Δ₁.PatternFollowing) (hpf₂ : Δ₂.PatternFollowing)
    (r : Rung Δ₁ Δ₂) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r' : Rung Δ₁ Δ₂, r'.mfollow = δ ∧ r'.mesh = max δ r.mfollow ∧
      ∃ x : Fin r'.N → Fin r.N, r'.C₁.FollowsPattern x r.C₁ ∧ r'.C₂.FollowsPattern x r.C₂ := by
  have hmax : 0 < max δ r.mfollow := lt_of_lt_of_le hδ (le_max_left _ _)
  rcases r.follow with ⟨hcan, hdf⟩ | ⟨hcan, hdf⟩
  · obtain ⟨c, -, hεc, lv, -, CA, hCA1, hCA2, x, hfB, hfA⟩ :=
      Description.exists_half_step Δ₁ Δ₂ hcan r.isFrom₂ r.cons₂ hδ
    exact ⟨{ N := Δ₂.n c
             C₁ := CA
             C₂ := Δ₂.D c
             isFrom₁ := hCA1
             isFrom₂ := Δ₂.isFrom c
             lv₁ := lv
             lv₂ := c
             cons₁ := hCA2
             cons₂ := Chain.isConsolidationOf_self _
             mesh := max δ r.mfollow
             mfollow := δ
             mesh_pos := hmax
             mfollow_pos := hδ
             diam₁ := fun t => (Chain.diam_le_of_followsPattern x hfA hdf
               (fun _ => isBounded_of_compactSpace) t).trans (le_max_right _ _)
             diam₂ := fun t => ((Δ₂.diam_le c t).trans hεc).trans (le_max_left _ _)
             follow := Or.inr ⟨Description.canFollow_level hpf₂ c,
               fun t => (Δ₂.diam_le c t).trans hεc⟩ }, rfl, rfl, x, hfA, hfB⟩
  · obtain ⟨c, -, hεc, lv, -, CA, hCA1, hCA2, x, hfB, hfA⟩ :=
      Description.exists_half_step Δ₂ Δ₁ hcan r.isFrom₁ r.cons₁ hδ
    exact ⟨{ N := Δ₁.n c
             C₁ := Δ₁.D c
             C₂ := CA
             isFrom₁ := Δ₁.isFrom c
             isFrom₂ := hCA1
             lv₁ := c
             lv₂ := lv
             cons₁ := Chain.isConsolidationOf_self _
             cons₂ := hCA2
             mesh := max δ r.mfollow
             mfollow := δ
             mesh_pos := hmax
             mfollow_pos := hδ
             diam₁ := fun t => ((Δ₁.diam_le c t).trans hεc).trans (le_max_left _ _)
             diam₂ := fun t => (Chain.diam_le_of_followsPattern x hfA hdf
               (fun _ => isBounded_of_compactSpace) t).trans (le_max_right _ _)
             follow := Or.inl ⟨Description.canFollow_level hpf₁ c,
               fun t => (Δ₁.diam_le c t).trans hεc⟩ }, rfl, rfl, x, hfB, hfA⟩

end Rung

/-- **Bing 1948, Theorem 12**, conditional on pattern following. -/
theorem Description.exists_homeomorph [CompactSpace X₁] [CompactSpace X₂]
    {P₁ Q₁ : X₁} {P₂ Q₂ : X₂}
    (Δ₁ : Description X₁ P₁ Q₁) (Δ₂ : Description X₂ P₂ Q₂)
    (hPQ₁ : P₁ ≠ Q₁) (hPQ₂ : P₂ ≠ Q₂)
    (h₁ : Δ₁.PatternFollowing) (h₂ : Δ₂.PatternFollowing) :
    ∃ T : Δ₁.M ≃ₜ Δ₂.M,
      T ⟨P₁, Δ₁.P_mem_M⟩ = ⟨P₂, Δ₂.P_mem_M⟩ ∧ T ⟨Q₁, Δ₁.Q_mem_M⟩ = ⟨Q₂, Δ₂.Q_mem_M⟩ := by
  classical
  -- the alternating construction
  obtain ⟨r₀, hr₀⟩ := Rung.exists_base Δ₁ Δ₂ h₁ hPQ₁ hPQ₂
  have hnext : ∀ (k : ℕ) (r : Rung Δ₁ Δ₂), ∃ r' : Rung Δ₁ Δ₂,
      r'.mfollow = (1 / 2 : ℝ) ^ (k + 2) ∧ r'.mesh = max ((1 / 2 : ℝ) ^ (k + 2)) r.mfollow ∧
      ∃ x : Fin r'.N → Fin r.N, r'.C₁.FollowsPattern x r.C₁ ∧ r'.C₂.FollowsPattern x r.C₂ :=
    fun k r => Rung.exists_next h₁ h₂ r (by positivity)
  choose nxt hmf hmesh hlink using hnext
  set R : ℕ → Rung Δ₁ Δ₂ := fun k => Nat.rec r₀ (fun k r => nxt k r) k
  -- the mesh bookkeeping
  have hmfollow : ∀ k, (R k).mfollow = (1 / 2 : ℝ) ^ (k + 1) := by
    intro k
    cases k with
    | zero => simpa using hr₀
    | succ k => exact hmf k (R k)
  have hmeshk : ∀ k, (R (k + 1)).mesh = (1 / 2 : ℝ) ^ (k + 1) := by
    intro k
    rw [show (R (k + 1)).mesh = max ((1 / 2 : ℝ) ^ (k + 2)) (R k).mfollow from hmesh k (R k),
      hmfollow k]
    refine max_eq_right ?_
    have : (1 / 2 : ℝ) ^ (k + 2) = (1 / 2 : ℝ) ^ (k + 1) * (1 / 2) := by ring
    rw [this]
    nlinarith [pow_pos (show (0:ℝ) < 1/2 by norm_num) (k + 1)]
  have hεpos : ∀ i, 0 < 2 * (R i).mesh := fun i => by
    have := (R i).mesh_pos; linarith
  have hsum : Summable (fun i => 2 * (R i).mesh) := by
    rw [← summable_nat_add_iff 1]
    have hfun : (fun k => 2 * (R (k + 1)).mesh) = fun k => (1 / 2 : ℝ) ^ k := by
      funext k
      rw [hmeshk k]
      ring
    rw [hfun]
    exact summable_geometric_two
  -- the matching covers
  have hN : ∀ i, 0 < (R i).N := by
    intro i
    obtain ⟨hn, -, -, -, -⟩ := (R i).isFrom₁
    exact hn
  have hdiam₁ : ∀ i (k : Fin (R i).N), Metric.diam ((R i).C₁.link k) ≤ 2 * (R i).mesh := by
    intro i k
    have := (R i).diam₁ k
    have := (R i).mesh_pos
    linarith
  have hdiam₂ : ∀ i (k : Fin (R i).N), Metric.diam ((R i).C₂.link k) ≤ 2 * (R i).mesh := by
    intro i k
    have := (R i).diam₂ k
    have := (R i).mesh_pos
    linarith
  have hlt₁ : ∀ i (k : Fin (R i).N), Metric.diam ((R i).C₁.link k) < 2 * (R i).mesh := by
    intro i k
    have := (R i).diam₁ k
    have := (R i).mesh_pos
    linarith
  have hlt₂ : ∀ i (k : Fin (R i).N), Metric.diam ((R i).C₂.link k) < 2 * (R i).mesh := by
    intro i k
    have := (R i).diam₂ k
    have := (R i).mesh_pos
    linarith
  obtain ⟨T, hT⟩ := MatchingCovers.exists_homeomorph
    (M₁ := Δ₁.M) (M₂ := Δ₂.M) (ε := fun i => 2 * (R i).mesh)
    { N := fun i => (R i).N
      x₁ := fun i => (R i).C₁.link
      x₂ := fun i => (R i).C₂.link
      open₁ := fun i => (R i).C₁.isOpen
      open₂ := fun i => (R i).C₂.isOpen
      cover₁ := fun i => Δ₁.M_subset_consolidation (R i).cons₁
      cover₂ := fun i => Δ₂.M_subset_consolidation (R i).cons₂
      meet₁ := fun i => Δ₁.consolidation_link_inter_M_nonempty (R i).cons₁
      meet₂ := fun i => Δ₂.consolidation_link_inter_M_nonempty (R i).cons₂
      bdd₁ := fun _ _ => isBounded_of_compactSpace
      bdd₂ := fun _ _ => isBounded_of_compactSpace
      diam₁ := hdiam₁
      diam₂ := hdiam₂
      match₁ := by
        intro i j k hjk
        obtain ⟨x, hx₁, hx₂⟩ := hlink i (R i)
        exact Chain.pattern_matching x hx₁ hx₂ (hlt₂ i)
          (fun _ => isBounded_of_compactSpace) j k hjk
      match₂ := by
        intro i j k hjk
        obtain ⟨x, hx₁, hx₂⟩ := hlink i (R i)
        exact Chain.pattern_matching x hx₂ hx₁ (hlt₁ i)
          (fun _ => isBounded_of_compactSpace) j k hjk }
    Δ₁.isCompact_M Δ₂.isCompact_M hεpos hsum
  -- the two endpoints are tracked by the constant index sequences
  refine ⟨T, ?_, ?_⟩
  · refine hT (fun i => ⟨0, hN i⟩) _ _ (fun i => ?_) (fun i => ?_)
    · obtain ⟨hn, hP, -, -, -⟩ := (R i).isFrom₁
      exact hP
    · obtain ⟨hn, hP, -, -, -⟩ := (R i).isFrom₂
      exact hP
  · refine hT (fun i => ⟨(R i).N - 1, by show (R i).N - 1 < (R i).N; have := hN i; omega⟩)
      _ _ (fun i => ?_) (fun i => ?_)
    · obtain ⟨hn, -, hQ, -, -⟩ := (R i).isFrom₁
      exact hQ
    · obtain ⟨hn, -, hQ, -, -⟩ := (R i).isFrom₂
      exact hQ

end HPC
