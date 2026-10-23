import HPC.Jones.Defs
import HPC.PseudoArc.Statements79

/-!
# Batch 135: Jones 1948, §§1–2 — Theorems 0–5 and 7–10

Theorem 6 is in `HPC/Jones/Theorem6.lean`.

* Theorems 1 and 2 are consequences of `isOpen_setOf_aposAt` (the pairs of aposyndesis form an
  open subset of `X × X`). Theorem 1 holds without its hypotheses `x ≠ y` and `yᵢ ≠ xᵢ`.
* Theorem 3 (no proof printed): closedness as for Theorem 2; connectedness from
  `aposAt_of_frontier` (finite covers and boundary bumping).
* Theorem 0 (\"with the help of the Heine–Borel theorem\"): finite covers.
* Theorems 4 and 5: projections of closed subsets of `X × X`.
* Theorem 7: Jones's continuum `H₀ + M₁(c₂)`, with `H₀` a product of a closed ball and a factor.
* Theorems 8–10, and the refutation of Theorem 10 as printed (`theorem10_printed_iff`,
  `not_theorem10_printed_unitInterval`).
-/

namespace HPC.Jones

open Set Topology Filter Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-! ### The repository's notions -/

section Equivalences

variable [ConnectedSpace X]

theorem isContinuum_univ : Fold.Q78.IsContinuum (univ : Set X) :=
  ⟨isCompact_univ, isConnected_univ⟩

/-- `IsDecomposableSpace X` is the negation of `Fold.Q78.IsIndecomposable univ`. -/
theorem isDecomposableSpace_iff_not_isIndecomposable :
    IsDecomposableSpace X ↔ ¬ Fold.Q78.IsIndecomposable (univ : Set X) := by
  constructor
  · rintro ⟨H, K, hH, hK, hHu, hKu, hHK⟩ ⟨-, h⟩
    rcases h H K hH hK (subset_univ _) (subset_univ _) hHK with h | h
    · exact hHu h
    · exact hKu h
  · intro h
    by_contra hd
    apply h
    refine ⟨isContinuum_univ, fun A B hA hB _ _ hAB => ?_⟩
    by_contra hne
    push_neg at hne
    exact hd ⟨A, B, hA, hB, hne.1, hne.2, hAB⟩

omit [CompactSpace X] [ConnectedSpace X] in
/-- Jones's composant is the repository's `HPC.composant` of the whole space. -/
theorem composant_eq_composant_univ (x : X) : composant x = HPC.composant univ x := by
  ext y
  constructor
  · rintro ⟨K, hK, hKu, hxK, hyK⟩
    exact mem_sUnion.mpr ⟨K, ⟨hK, subset_univ _, hKu, hxK⟩, hyK⟩
  · intro hy
    obtain ⟨K, ⟨hK, -, hKu, hxK⟩, hyK⟩ := mem_sUnion.mp hy
    exact ⟨K, hK, hKu, hxK, hyK⟩

end Equivalences

/-! ### Theorems 1–5 -/

omit [CompactSpace X] in
/-- **Theorem 1.** Suppose `xᵢ → x` and `yᵢ → y`, and `X` is not aposyndetic at `xᵢ` with respect
to `yᵢ`. Then `X` is not aposyndetic at `x` with respect to `y`.

*Shape change:* the hypotheses `x ≠ y` and `yᵢ ≠ xᵢ` of the skeleton are not needed and are
dropped (`X` is never aposyndetic at a point with respect to itself). Compactness is not used. -/
theorem theorem1 {x y : X} (u v : ℕ → X) (hu : Tendsto u atTop (𝓝 x))
    (hv : Tendsto v atTop (𝓝 y)) (hna : ∀ i, ¬ AposAt (u i) (v i)) : ¬ AposAt x y := by
  have h := isClosed_setOf_not_aposAt.mem_of_tendsto (hu.prodMk_nhds hv)
    (Eventually.of_forall hna)
  exact h

omit [CompactSpace X] in
/-- The set of Theorem 2 is the set of all `y` with `X` not aposyndetic at `x` w.r.t. `y`. -/
theorem setOf_theorem2_eq (x : X) :
    {y | y ≠ x ∧ ¬ AposAt x y} ∪ {x} = {y | ¬ AposAt x y} := by
  ext y
  by_cases hy : y = x
  · subst hy; simp [not_aposAt_self]
  · simp [hy]

omit [CompactSpace X] in
/-- The set of Theorem 3 is the set of all `x` with `X` not aposyndetic at `x` w.r.t. `y`. -/
theorem setOf_theorem3_eq (y : X) :
    {x | x ≠ y ∧ ¬ AposAt x y} ∪ {y} = {x | ¬ AposAt x y} := by
  ext x
  by_cases hx : x = y
  · subst hx; simp [not_aposAt_self]
  · simp [hx]

omit [CompactSpace X] in
/-- **Theorem 2.** The set `K` of points `y ≠ x` such that `X` is not aposyndetic at `x` with
respect to `y`, together with `x`, is closed. (No proof printed.) -/
theorem theorem2 (x : X) : IsClosed ({y | y ≠ x ∧ ¬ AposAt x y} ∪ {x}) := by
  rw [setOf_theorem2_eq]; exact isClosed_not_aposAt_right x

/-- **Theorem 3.** The set `L` of points `x ≠ y` such that `X` is not aposyndetic at `x` with
respect to `y`, together with `y`, is a continuum. (No proof printed. This is Jones 1955's `L_y`.)

Proof: `L` is closed (`isClosed_not_aposAt_left`). If `L = A ∪ B` with `A ∋ y`, `B` disjoint
nonempty closed, take an open `V ⊇ B` with `closure V ∩ A = ∅`; the frontier of `V` misses `L`, so
by `aposAt_of_frontier` `X` is aposyndetic at the points of `B` with respect to `y`. -/
theorem theorem3 [ConnectedSpace X] (y : X) :
    Fold.Q78.IsContinuum ({x | x ≠ y ∧ ¬ AposAt x y} ∪ {y}) := by
  rw [setOf_theorem3_eq]
  set L := {x | ¬ AposAt x y} with hL
  have hLcl : IsClosed L := isClosed_not_aposAt_left y
  have hyL : y ∈ L := not_aposAt_self y
  refine ⟨hLcl.isCompact, ⟨y, hyL⟩, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  -- the key claim, for the piece containing `y`
  have key : ∀ u v : Set X, IsClosed u → IsClosed v → L ⊆ u ∪ v → L ∩ (u ∩ v) = ∅ → y ∈ u →
      L ⊆ u := by
    intro u v hu hv hLuv hLuv' hyu b hbL
    by_contra hbu
    have hbv : b ∈ v := (hLuv hbL).resolve_left hbu
    have hAcl : IsClosed (L ∩ u) := hLcl.inter hu
    have hBcl : IsClosed (L ∩ v) := hLcl.inter hv
    have hAB : L ∩ v ⊆ (L ∩ u)ᶜ := by
      rintro z ⟨hzL, hzv⟩ ⟨-, hzu⟩
      have : z ∈ L ∩ (u ∩ v) := ⟨hzL, hzu, hzv⟩
      rw [hLuv'] at this; exact this
    obtain ⟨V, hV, hBV, hVA⟩ := normal_exists_closure_subset hBcl hAcl.isOpen_compl hAB
    have hbV : b ∈ V := hBV ⟨hbL, hbv⟩
    have hyV : y ∉ closure V := fun h => hVA h ⟨hyL, hyu⟩
    have hfr : ∀ z ∈ frontier V, AposAt z y := by
      intro z hz
      by_contra hzna
      have hzL : z ∈ L := hzna
      rcases hLuv hzL with hzu | hzv
      · exact hVA hz.1 ⟨hzL, hzu⟩
      · exact hz.2 (by rw [hV.interior_eq]; exact hBV ⟨hzL, hzv⟩)
    exact hbL (aposAt_of_frontier hV hbV hyV hfr)
  intro u v hu hv hLuv hLuv'
  rcases hLuv hyL with hyu | hyv
  · exact Or.inl (key u v hu hv hLuv hLuv' hyu)
  · refine Or.inr (key v u hv hu (by rwa [union_comm]) ?_ hyv)
    rwa [inter_comm v u]

/-- **Theorem 4.** The set of points at which `X` is non-aposyndetic is an `F_σ`. -/
theorem theorem4 : ∃ F : ℕ → Set X, (∀ i, IsClosed (F i)) ∧
    {x : X | ¬ AposyndeticAt x} = ⋃ i, F i := by
  refine ⟨fun i => Prod.fst '' ({p : X × X | ¬ AposAt p.1 p.2} ∩
    {p : X × X | 1 / ((i : ℝ) + 1) ≤ dist p.1 p.2}), fun i => isClosed_fst_image
      (isClosed_setOf_not_aposAt.inter (isClosed_le continuous_const continuous_dist)), ?_⟩
  ext x
  simp only [AposyndeticAt, mem_setOf_eq, not_forall, mem_iUnion, mem_image, mem_inter_iff,
    Prod.exists, exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨y, hyx, hna⟩
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt (dist_pos.mpr (Ne.symm hyx))
    exact ⟨i, y, hna, hi.le⟩
  · rintro ⟨i, y, hna, hi⟩
    refine ⟨y, fun h => ?_, hna⟩
    subst h
    rw [dist_self] at hi
    have : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
    linarith

/-! ### Theorem 0 -/

/-- **Theorem 0.** `X` is semi-locally-connected at `p` iff it is aposyndetic at each point of
`X − p` with respect to `p`. (\"May be established with the help of the Heine–Borel theorem.\") -/
theorem theorem0 [ConnectedSpace X] (p : X) : SemiLocConnAt p ↔ ∀ x, x ≠ p → AposAt x p := by
  classical
  constructor
  · intro h x hxp
    set d := dist x p with hd
    have hdpos : 0 < d := dist_pos.mpr hxp
    obtain ⟨V, hV, hpV, hVU, F, hFV, hcov⟩ := h (ball p (d / 2)) isOpen_ball (mem_ball_self
      (half_pos hdpos))
    set O : Set X := (closedBall p (d / 2))ᶜ with hO
    have hOopen : IsOpen O := isClosed_closedBall.isOpen_compl
    have hxO : x ∈ O := by
      simp only [hO, mem_compl_iff, mem_closedBall, not_le]; linarith
    have hOU : O ⊆ (ball p (d / 2))ᶜ := compl_subset_compl.mpr ball_subset_closedBall
    obtain ⟨O', hO', hxO', hO'C⟩ := exists_open_subset_component hV.isClosed_compl F hOopen hxO
      (hOU.trans hcov)
    have hxV : x ∈ Vᶜ := by
      obtain ⟨c, -, hxc⟩ := mem_iUnion₂.mp (hcov (hOU hxO))
      exact connectedComponentIn_subset _ _ hxc
    refine ⟨connectedComponentIn Vᶜ x, O', ⟨(isClosed_connectedComponentIn'
      hV.isClosed_compl x).isCompact, isConnected_connectedComponentIn_iff.mpr hxV⟩, hO', hxO',
      hO'C, fun hp => ?_⟩
    exact connectedComponentIn_subset _ _ hp hpV
  · intro h U hU hpU
    obtain ⟨t, H, U', htH, hcov⟩ := exists_finite_apos_cover hU.isClosed_compl.isCompact
      (y := p) (fun x hx => h x fun hxp => hx (hxp ▸ hpU))
    have hHne : ∀ i ∈ t, (H i).Nonempty := fun i hi => (htH i hi).1.2.nonempty
    choose! c hc using hHne
    set V : Set X := U ∩ (⋃ i ∈ t, H i)ᶜ with hVdef
    have hVopen : IsOpen V :=
      hU.inter (isClosed_biUnion_finset fun i hi => (htH i hi).1.1.isClosed).isOpen_compl
    have hpV : p ∈ V := by
      refine ⟨hpU, fun hp => ?_⟩
      obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
      exact (htH i hi).2.2.2 hpi
    have hHV : ∀ i ∈ t, H i ⊆ Vᶜ := fun i hi z hz hzV =>
      hzV.2 (mem_iUnion₂.mpr ⟨i, hi, hz⟩)
    refine ⟨V, hVopen, hpV, inter_subset_left, t.image c, ?_, ?_⟩
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact hHV i hi (hc i hi)
    · intro z hz
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcov hz)
      refine mem_iUnion₂.mpr ⟨c i, Finset.mem_image_of_mem c hi, ?_⟩
      exact (htH i hi).1.2.isPreconnected.subset_connectedComponentIn (hc i hi) (hHV i hi)
        ((htH i hi).2.2.1 hzi)

/-- **Theorem 5.** The set of points at which `X` is not semi-locally-connected is an `F_σ`.
(\"Theorem 0 and an argument similar to that used for Theorem 4.\") -/
theorem theorem5 [ConnectedSpace X] : ∃ F : ℕ → Set X, (∀ i, IsClosed (F i)) ∧
    {x : X | ¬ SemiLocConnAt x} = ⋃ i, F i := by
  refine ⟨fun i => Prod.snd '' ({p : X × X | ¬ AposAt p.1 p.2} ∩
    {p : X × X | 1 / ((i : ℝ) + 1) ≤ dist p.1 p.2}), fun i => isClosed_snd_image
      (isClosed_setOf_not_aposAt.inter (isClosed_le continuous_const continuous_dist)), ?_⟩
  ext x
  simp only [theorem0, mem_setOf_eq, not_forall, mem_iUnion, mem_image, mem_inter_iff,
    Prod.exists, exists_eq_right]
  constructor
  · rintro ⟨z, hzx, hna⟩
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt (dist_pos.mpr hzx)
    exact ⟨i, z, hna, hi.le⟩
  · rintro ⟨i, z, hna, hi⟩
    refine ⟨z, fun h => ?_, hna⟩
    subst h
    rw [dist_self] at hi
    have : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
    linarith

/-! ### Theorem 7 -/

section Theorem7

variable {Y Z : Type*} [MetricSpace Y] [ConnectedSpace Y] [MetricSpace Z] [ConnectedSpace Z]

/-- The continuum of Jones's proof of Theorem 7: `(A × Z) ∪ (Y × {c})`, `A` closed. -/
theorem isContinuum_prod_cross [CompactSpace Y] [CompactSpace Z] {A : Set Y} (hA : IsClosed A)
    (hAne : A.Nonempty) (c : Z) :
    Fold.Q78.IsContinuum (A ×ˢ (univ : Set Z) ∪ (univ : Set Y) ×ˢ {c}) := by
  obtain ⟨a, ha⟩ := hAne
  refine ⟨((hA.prod isClosed_univ).union (isClosed_univ.prod isClosed_singleton)).isCompact,
    ⟨(a, c), Or.inr ⟨mem_univ _, rfl⟩⟩, ?_⟩
  have hrow : IsPreconnected ((univ : Set Y) ×ˢ ({c} : Set Z)) :=
    isPreconnected_univ.prod isPreconnected_singleton
  refine isPreconnected_of_forall (a, c) ?_
  rintro ⟨y₁, y₂⟩ (⟨hy₁, -⟩ | ⟨-, hy₂⟩)
  · refine ⟨({y₁} : Set Y) ×ˢ (univ : Set Z) ∪ (univ : Set Y) ×ˢ {c}, ?_, Or.inr ⟨mem_univ _,
      rfl⟩, Or.inl ⟨rfl, mem_univ _⟩, ?_⟩
    · exact union_subset_union_left _ (Set.prod_mono (singleton_subset_iff.mpr hy₁) Subset.rfl)
    · exact (isPreconnected_singleton.prod isPreconnected_univ).union (y₁, c)
        ⟨rfl, mem_univ _⟩ ⟨mem_univ _, rfl⟩ hrow
  · exact ⟨(univ : Set Y) ×ˢ {c}, subset_union_right, ⟨mem_univ _, rfl⟩, ⟨mem_univ _, hy₂⟩,
      hrow⟩

/-- Theorem 7, the case of distinct first coordinates. -/
theorem aposAt_prod_of_fst_ne [CompactSpace Y] [CompactSpace Z] [Nontrivial Z] {a b : Y × Z}
    (h : a.1 ≠ b.1) : AposAt a b := by
  set d := dist a.1 b.1 with hd
  have hdpos : 0 < d := dist_pos.mpr h
  obtain ⟨c, hc⟩ := exists_ne b.2
  refine ⟨closedBall a.1 (d / 2) ×ˢ (univ : Set Z) ∪ (univ : Set Y) ×ˢ {c},
    ball a.1 (d / 2) ×ˢ (univ : Set Z),
    isContinuum_prod_cross isClosed_closedBall ⟨a.1, mem_closedBall_self (half_pos hdpos).le⟩ c,
    isOpen_ball.prod isOpen_univ, ⟨mem_ball_self (half_pos hdpos), mem_univ _⟩,
    (Set.prod_mono ball_subset_closedBall Subset.rfl).trans subset_union_left, ?_⟩
  rintro (⟨hb, -⟩ | ⟨-, hb⟩)
  · rw [mem_closedBall, dist_comm] at hb; linarith
  · exact hc hb.symm

/-- Theorem 7, the case of distinct second coordinates. -/
theorem aposAt_prod_of_snd_ne [CompactSpace Y] [CompactSpace Z] [Nontrivial Y] {a b : Y × Z}
    (h : a.2 ≠ b.2) : AposAt a b := by
  set d := dist a.2 b.2 with hd
  have hdpos : 0 < d := dist_pos.mpr h
  obtain ⟨c, hc⟩ := exists_ne b.1
  have hcont : Fold.Q78.IsContinuum ((univ : Set Y) ×ˢ closedBall a.2 (d / 2) ∪
      ({c} : Set Y) ×ˢ (univ : Set Z)) := by
    have h0 := isContinuum_prod_cross (Y := Z) (Z := Y) isClosed_closedBall
      ⟨a.2, mem_closedBall_self (half_pos hdpos).le⟩ c
    have himg : (Prod.swap '' (closedBall a.2 (d / 2) ×ˢ (univ : Set Y) ∪
        (univ : Set Z) ×ˢ {c})) = (univ : Set Y) ×ˢ closedBall a.2 (d / 2) ∪
          ({c} : Set Y) ×ˢ (univ : Set Z) := by
      rw [image_union, image_swap_prod, image_swap_prod]
    rw [← himg]
    exact ⟨h0.1.image continuous_swap, h0.2.image _ continuous_swap.continuousOn⟩
  refine ⟨(univ : Set Y) ×ˢ closedBall a.2 (d / 2) ∪ ({c} : Set Y) ×ˢ (univ : Set Z),
    (univ : Set Y) ×ˢ ball a.2 (d / 2), hcont, isOpen_univ.prod isOpen_ball,
    ⟨mem_univ _, mem_ball_self (half_pos hdpos)⟩,
    (Set.prod_mono Subset.rfl ball_subset_closedBall).trans subset_union_left, ?_⟩
  rintro (⟨-, hb⟩ | ⟨hb, -⟩)
  · rw [mem_closedBall, dist_comm] at hb; linarith
  · exact hc hb.symm

end Theorem7

/-- **Theorem 7.** The product of two nondegenerate continua is aposyndetic at each of its
points. (Stated for two compact connected metric spaces, both nontrivial.) -/
theorem theorem7 (Y Z : Type*) [MetricSpace Y] [CompactSpace Y] [ConnectedSpace Y]
    [Nontrivial Y] [MetricSpace Z] [CompactSpace Z] [ConnectedSpace Z] [Nontrivial Z] :
    IsAposyndetic (Y × Z) := by
  intro a b hab
  by_cases h : a.1 = b.1
  · exact aposAt_prod_of_snd_ne fun h' => hab (Prod.ext h h')
  · exact aposAt_prod_of_fst_ne h

/-! ### §2: Theorems 8–10 -/

section Indecomposable

variable [ConnectedSpace X]

omit [CompactSpace X] [ConnectedSpace X] in
/-- In a decomposition `X = H ∪ K` into proper subcontinua, `X` is aposyndetic at each point of
`X − K` with respect to each point of `X − H`. -/
theorem aposAt_of_decomposition {H K : Set X} (hH : Fold.Q78.IsContinuum H) (hK : IsClosed K)
    (hHK : H ∪ K = univ) {x y : X} (hx : x ∉ K) (hy : y ∉ H) : AposAt x y := by
  refine ⟨H, Kᶜ, hH, hK.isOpen_compl, hx, fun z hz => ?_, hy⟩
  have : z ∈ H ∪ K := hHK ▸ mem_univ z
  exact this.resolve_right hz

/-- **Theorem 8.** `X` is decomposable iff there are distinct `x`, `y` with `X` aposyndetic at `x`
with respect to `y`. -/
theorem theorem8 : IsDecomposableSpace X ↔ ∃ x y : X, x ≠ y ∧ AposAt x y := by
  constructor
  · rintro ⟨H, K, hH, hK, hHu, hKu, hHK⟩
    obtain ⟨x, hx⟩ := (ne_univ_iff_exists_notMem K).mp hKu
    obtain ⟨y, hy⟩ := (ne_univ_iff_exists_notMem H).mp hHu
    have h := aposAt_of_decomposition hH hK.1.isClosed hHK hx hy
    exact ⟨x, y, h.ne, h⟩
  · rintro ⟨x, y, -, H, U, hH, hU, hxU, hUH, hyH⟩
    have hHu : H ≠ univ := fun h => hyH (h ▸ mem_univ y)
    by_cases hc : IsPreconnected Hᶜ
    · -- `X = H ∪ closure (X − H)`
      refine ⟨H, closure Hᶜ, hH, ⟨isClosed_closure.isCompact, ⟨y, subset_closure hyH⟩,
        hc.closure⟩, hHu, ?_, ?_⟩
      · intro h
        have hx : x ∈ closure Hᶜ := h ▸ mem_univ x
        obtain ⟨z, hzU, hzH⟩ := mem_closure_iff.mp hx U hU hxU
        exact hzH (hUH hzU)
      · exact eq_univ_of_forall fun z => by
          by_cases hz : z ∈ H
          · exact Or.inl hz
          · exact Or.inr (subset_closure hz)
    · obtain ⟨A, B, hA, hB, hcov, hAB, hBA⟩ := Plane.exists_separated_of_not_isPreconnected hc
      have hcov' : univ \ H = A ∪ B := by rw [← hcov]; ext; simp
      have hcov'' : univ \ H = B ∪ A := by rw [hcov', union_comm]
      have h1 := Plane.isContinuum_union_piece isContinuum_univ hH (subset_univ _) hcov' hAB hBA
      have h2 := Plane.isContinuum_union_piece isContinuum_univ hH (subset_univ _) hcov''
        hBA.symm hAB.symm
      have hAH : Disjoint A H := by
        rw [Set.disjoint_left]; intro z hz hzH
        have : z ∈ Hᶜ := hcov ▸ Or.inl hz
        exact this hzH
      have hBH : Disjoint B H := by
        rw [Set.disjoint_left]; intro z hz hzH
        have : z ∈ Hᶜ := hcov ▸ Or.inr hz
        exact this hzH
      refine ⟨H ∪ A, H ∪ B, h1, h2, ?_, ?_, ?_⟩
      · intro h
        obtain ⟨b, hb⟩ := hB
        have : b ∈ H ∪ A := h ▸ mem_univ b
        rcases this with h' | h'
        · exact Set.disjoint_left.mp hBH hb h'
        · exact Set.disjoint_left.mp hAB (subset_closure h') hb
      · intro h
        obtain ⟨a, ha⟩ := hA
        have : a ∈ H ∪ B := h ▸ mem_univ a
        rcases this with h' | h'
        · exact Set.disjoint_left.mp hAH ha h'
        · exact Set.disjoint_left.mp hAB (subset_closure ha) h'
      · refine eq_univ_of_forall fun z => ?_
        by_cases hz : z ∈ H
        · exact Or.inl (Or.inl hz)
        · have : z ∈ A ∪ B := hcov ▸ hz
          rcases this with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr (Or.inr h')

/-- **Theorem 9.** `X` is indecomposable iff there are no distinct `x`, `y` with `X` aposyndetic
at `x` with respect to `y`. -/
theorem theorem9 : ¬ IsDecomposableSpace X ↔ ∀ x y : X, x ≠ y → ¬ AposAt x y := by
  rw [theorem8]; push_neg; rfl

/-- **Theorem 10** (corrected: `D` nonempty). `X` is indecomposable iff it contains a nonempty open
set `D` such that `X` is not aposyndetic at any `x ∈ D` with respect to any `y ≠ x`.

*Shape change:* the skeleton's `[Nontrivial X]` is not needed and is dropped. As printed (without
\"nonempty\") the theorem is false for every decomposable continuum: `theorem10_printed_iff`. -/
theorem theorem10 :
    ¬ IsDecomposableSpace X ↔
      ∃ D : Set X, IsOpen D ∧ D.Nonempty ∧ ∀ x ∈ D, ∀ y, y ≠ x → ¬ AposAt x y := by
  constructor
  · intro h
    exact ⟨univ, isOpen_univ, univ_nonempty, fun x _ y hyx => theorem9.mp h x y (Ne.symm hyx)⟩
  · rintro ⟨D, hD, ⟨x, hxD⟩, hDna⟩ ⟨H, K, hH, hK, hHu, hKu, hHK⟩
    have hxK : x ∈ K := by
      by_contra hxK
      obtain ⟨y, hy⟩ := (ne_univ_iff_exists_notMem H).mp hHu
      have h := aposAt_of_decomposition hH hK.1.isClosed hHK hxK hy
      exact hDna x hxD y (Ne.symm h.ne) h
    have hDH : D ⊆ H := by
      intro z hzD
      by_contra hzH
      obtain ⟨y, hy⟩ := (ne_univ_iff_exists_notMem K).mp hKu
      have h := aposAt_of_decomposition hK hH.1.isClosed (by rw [union_comm]; exact hHK) hzH hy
      exact hDna z hzD y (Ne.symm h.ne) h
    obtain ⟨y, hy⟩ := (ne_univ_iff_exists_notMem H).mp hHu
    have h : AposAt x y := ⟨H, D, hH, hD, hxD, hDH, hy⟩
    exact hDna x hxD y (Ne.symm h.ne) h

omit [CompactSpace X] [ConnectedSpace X] in
/-- **Theorem 10 as printed** (without \"`D` nonempty\") says exactly that `X` is indecomposable:
its right-hand side always holds, with `D = ∅`. So the printed theorem fails for every
decomposable continuum. -/
theorem theorem10_printed_iff :
    (¬ IsDecomposableSpace X ↔ ∃ D : Set X, IsOpen D ∧ ∀ x ∈ D, ∀ y, y ≠ x → ¬ AposAt x y) ↔
      ¬ IsDecomposableSpace X := by
  have hrhs : ∃ D : Set X, IsOpen D ∧ ∀ x ∈ D, ∀ y, y ≠ x → ¬ AposAt x y :=
    ⟨∅, isOpen_empty, fun x hx => absurd hx (notMem_empty x)⟩
  exact ⟨fun h => h.mpr hrhs, fun h => iff_of_true h hrhs⟩

end Indecomposable

/-! ### The refutation of Theorem 10 as printed: an arc -/

/-- The unit interval is decomposable: `[0, 1/2] ∪ [1/2, 1]`. -/
theorem isDecomposableSpace_unitInterval : IsDecomposableSpace unitInterval := by
  have hcont : ∀ a b : ℝ, a ≤ b → 0 ≤ a → b ≤ 1 →
      Fold.Q78.IsContinuum {t : unitInterval | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b} := by
    intro a b hab ha hb
    have hset : {t : unitInterval | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b} =
        (Subtype.val : unitInterval → ℝ) ⁻¹' Icc a b := rfl
    have hcl : IsClosed {t : unitInterval | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b} := by
      rw [hset]; exact isClosed_Icc.preimage continuous_subtype_val
    refine ⟨hcl.isCompact, ⟨⟨a, ha, hab.trans hb⟩, le_refl a, hab⟩, ?_⟩
    rw [hset, ← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe]
    have : Icc (0 : ℝ) 1 ∩ Icc a b = Icc a b := by
      ext t; simp only [mem_inter_iff, mem_Icc]; constructor
      · exact fun h => h.2
      · exact fun h => ⟨⟨ha.trans h.1, h.2.trans hb⟩, h⟩
    rw [unitInterval, this]
    exact isPreconnected_Icc
  refine ⟨_, _, hcont 0 (1 / 2) (by norm_num) le_rfl (by norm_num),
    hcont (1 / 2) 1 (by norm_num) (by norm_num) le_rfl, ?_, ?_, ?_⟩
  · intro h
    have : (1 : unitInterval) ∈ {t : unitInterval | 0 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 / 2} :=
      h ▸ mem_univ _
    have h' := this.2
    simp at h'
    norm_num at h'
  · intro h
    have : (0 : unitInterval) ∈ {t : unitInterval | 1 / 2 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1} :=
      h ▸ mem_univ _
    have h' := this.1
    simp at h'
    norm_num at h'
  · refine eq_univ_of_forall fun t => ?_
    rcases le_total (t : ℝ) (1 / 2) with h | h
    · exact Or.inl ⟨t.2.1, h⟩
    · exact Or.inr ⟨h, t.2.2⟩

/-- **Theorem 10 as printed is false** (ledger entry): for the arc `[0, 1]` the printed
right-hand side holds (with `D = ∅`) but the arc is decomposable. -/
theorem not_theorem10_printed_unitInterval :
    ¬ (¬ IsDecomposableSpace unitInterval ↔
      ∃ D : Set unitInterval, IsOpen D ∧ ∀ x ∈ D, ∀ y, y ≠ x → ¬ AposAt x y) := by
  rw [theorem10_printed_iff]
  exact not_not.mpr isDecomposableSpace_unitInterval

end HPC.Jones
