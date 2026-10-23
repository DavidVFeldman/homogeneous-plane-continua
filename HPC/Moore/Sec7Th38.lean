import HPC.Moore.Sec7Th37

/-!
# Moore, F.A. (1916), §7: Theorem 38 (batch 139)

**Theorem 38** (p. 153, as printed). If `J` and `C` are closed curves, `O` is a point on `J` but
not on `C`, `A₁` and `A₂` are distinct points common to `C` and `J`, and `A₁XA₂` is an arc on `C`
such that the interior of the closed curve `A₁XA₂OA₁` is a subset of the exterior of `J`, then there
exist two points `O₁` and `O₂`, distinct from `O`, such that (1) on the interval `O₁OO₂` of the
curve `J`, `O` is between `O₁` and `A₂` and between `O₂` and `A₁`, (2) there is on the curve `C` an
arc `O₁YO₂` such that `O₁YO₂` and the interior of the closed curve `O₁YO₂OO₁` are subsets of the
exterior of `J`, (3) if the exterior of `J` contains `B₁ZB₂` and the interior of the closed curve
`B₁ZB₂OB₁` where `B₁` and `B₂` are points on that arc of `J` from `O₁` to `O₂` which does not
contain `O`, and `B₁ZB₂` is an arc of `C`, then `B₁ = O₁` and `B₂ = O₂`.

**Reading** (commission §2, \"record the reading\"):
* `A₁XA₂OA₁` is the closed curve formed by `A₁XA₂` and the arc `T` of `J` from `A₁` to `A₂`
  through `O` (there is exactly one such arc: `O` is not `A₁`, `A₂`). The open arc `A₁XA₂` is
  assumed to lie in the exterior of `J` (**added hypothesis** `hXE`; Moore's conclusion (2) states
  it for `O₁YO₂`, and Theorem 41's use, \"an interval `A_pXB_p` of `J₁` lying entirely without `J₂`
  except for its endpoints\", assumes it).
* (1): `O₁`, `O₂` lie on the arc `T'` of `J` from `A₁` to `A₂` not containing `O`, in the order
  `A₁, O₁, O₂, A₂`; the interval `O₁OO₂` is the arc `V` of `J` from `O₁` to `O₂` through `O`, and it
  contains `T`. \"`O` is between `O₁` and `A₂`\" is stated as: every arc of `V` from `O₁` to `A₂`
  contains `O` (and likewise for `O₂`, `A₁`).
* (3): as printed, `B₁`, `B₂` on the arc `V'` of `J` from `O₁` to `O₂` **not** containing `O`. So
  `O₁YO₂` is the *outermost* such arc of `C` (its pocket `O₁YO₂OO₁` is the largest), not the
  innermost as in Theorem 37. This is the form Theorem 41 uses (\"if `Z` and `W` are points on
  `A_pC` and `B_pC` …\"). The conclusion is stated as `{B₁, B₂} = {O₁, O₂}`: the statement does not
  say which of `B₁`, `B₂` is nearer `O₁`.

Proof (\"analogous\"; none printed): the chords here are the arcs of `C` from `T'` to `T'` whose open
part and pocket lie in the exterior of `J`. As in Theorem 37, all but `A₁XA₂` lie in the other arc
`K` of `C` from `A₁` to `A₂`, with disjoint open intervals in its parameter. They are finitely many:
otherwise chords would shrink to a point `y` of `J` (`param_chords_accumulate`), and the closed curve
formed by a small chord and the small arc of `J` between its ends would enclose `O` (Theorem 27)
while lying in a small region about `y` (Theorem 21). The outermost one is then chosen.
-/

namespace HPC.Moore

open Set Topology Gen Filter
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-- Two pairs of parameters whose open intervals contain no point of `k ⁻¹ Z` but whose ends do,
and which are not each other's reverse, have disjoint open intervals. -/
theorem param_disjoint {X : Type*} {k : unitInterval → X} {Z : Set X}
    {P : Set (unitInterval × unitInterval)}
    (hP : ∀ x ∈ P, x.1 ≠ x.2 ∧ k x.1 ∈ Z ∧ k x.2 ∈ Z ∧
      ∀ u, min x.1 x.2 < u → u < max x.1 x.2 → k u ∉ Z)
    (hswap : ∀ x ∈ P, ∀ y ∈ P, x.1 = y.2 → x.2 = y.1 → False) :
    ∀ x ∈ P, ∀ y ∈ P, x ≠ y → min x.1 x.2 ≤ min y.1 y.2 → max x.1 x.2 ≤ min y.1 y.2 := by
  have hmemZ : ∀ x ∈ P, k (min x.1 x.2) ∈ Z ∧ k (max x.1 x.2) ∈ Z := by
    intro x hx
    obtain ⟨-, h1, h2, -⟩ := hP x hx
    constructor
    · rcases min_choice x.1 x.2 with h | h <;> rw [h] <;> assumption
    · rcases max_choice x.1 x.2 with h | h <;> rw [h] <;> assumption
  have hpos : ∀ x ∈ P, min x.1 x.2 < max x.1 x.2 := fun x hx =>
    min_lt_max.mpr (hP x hx).1
  intro x hx y hy hxy hle
  by_contra hlt
  push_neg at hlt
  rcases lt_or_eq_of_le hle with hlt' | heq
  · exact (hP x hx).2.2.2 _ hlt' hlt (hmemZ y hy).1
  · have hMM : max x.1 x.2 = max y.1 y.2 := by
      rcases lt_trichotomy (max x.1 x.2) (max y.1 y.2) with h | h | h
      · exact absurd (hmemZ x hx).2 ((hP y hy).2.2.2 _ hlt h)
      · exact h
      · exact absurd (hmemZ y hy).2 ((hP x hx).2.2.2 _ (heq ▸ hpos y hy) h)
    rcases le_total x.1 x.2 with h1 | h1 <;> rcases le_total y.1 y.2 with h2 | h2
    · rw [min_eq_left h1, min_eq_left h2] at heq
      rw [max_eq_right h1, max_eq_right h2] at hMM
      exact hxy (Prod.ext heq hMM)
    · rw [min_eq_left h1, min_eq_right h2] at heq
      rw [max_eq_right h1, max_eq_left h2] at hMM
      exact hswap x hx y hy heq hMM
    · rw [min_eq_right h1, min_eq_left h2] at heq
      rw [max_eq_left h1, max_eq_right h2] at hMM
      exact hswap x hx y hy hMM heq
    · rw [min_eq_right h1, min_eq_right h2] at heq
      rw [max_eq_left h1, max_eq_left h2] at hMM
      exact hxy (Prod.ext hMM heq)

/-- Infinitely many such pairs accumulate: some sequence of them has both ends tending to the same
parameter. -/
theorem param_chords_accumulate {X : Type*} {k : unitInterval → X} {Z : Set X}
    {P : Set (unitInterval × unitInterval)}
    (hP : ∀ x ∈ P, x.1 ≠ x.2 ∧ k x.1 ∈ Z ∧ k x.2 ∈ Z ∧
      ∀ u, min x.1 x.2 < u → u < max x.1 x.2 → k u ∉ Z)
    (hswap : ∀ x ∈ P, ∀ y ∈ P, x.1 = y.2 → x.2 = y.1 → False) (hinf : P.Infinite) :
    ∃ c : unitInterval, ∃ x : ℕ → unitInterval × unitInterval, (∀ n, x n ∈ P) ∧
      Tendsto (fun n => (x n).1) atTop (𝓝 c) ∧ Tendsto (fun n => (x n).2) atTop (𝓝 c) := by
  set e := hinf.natEmbedding P
  set y : ℕ → unitInterval × unitInterval := fun n => (e n : unitInterval × unitInterval)
  have hyP : ∀ n, y n ∈ P := fun n => (e n).2
  have hyinj : Function.Injective y := fun a b h => e.injective (Subtype.ext h)
  obtain ⟨z, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq y
  have h1 : Tendsto (fun n => (y (φ n)).1) atTop (𝓝 z.1) := (continuous_fst.tendsto z).comp hlim
  have h2 : Tendsto (fun n => (y (φ n)).2) atTop (𝓝 z.2) := (continuous_snd.tendsto z).comp hlim
  have hz : z.1 = z.2 := by
    by_contra hne
    obtain ⟨m, hm1, hm2⟩ := exists_between (min_lt_max.mpr hne)
    have hmin : Tendsto (fun n => min (y (φ n)).1 (y (φ n)).2) atTop (𝓝 (min z.1 z.2)) :=
      h1.min h2
    have hmax : Tendsto (fun n => max (y (φ n)).1 (y (φ n)).2) atTop (𝓝 (max z.1 z.2)) :=
      h1.max h2
    have ev : ∀ᶠ n in atTop, min (y (φ n)).1 (y (φ n)).2 < m ∧ m < max (y (φ n)).1 (y (φ n)).2 :=
      (hmin.eventually (gt_mem_nhds hm1)).and (hmax.eventually (lt_mem_nhds hm2))
    obtain ⟨N, hN⟩ := eventually_atTop.mp ev
    have hA := hN N le_rfl
    have hB := hN (N + 1) (Nat.le_succ N)
    have hne' : y (φ N) ≠ y (φ (N + 1)) := fun h =>
      (hφ (Nat.lt_succ_self N)).ne (hyinj h)
    rcases le_total (min (y (φ N)).1 (y (φ N)).2) (min (y (φ (N + 1))).1 (y (φ (N + 1))).2)
      with h | h
    · have := param_disjoint hP hswap _ (hyP _) _ (hyP _) hne' h
      exact absurd (hB.1.trans (hA.2.trans_le this)) (lt_irrefl _)
    · have := param_disjoint hP hswap _ (hyP _) _ (hyP _) (Ne.symm hne') h
      exact absurd (hA.1.trans (hB.2.trans_le this)) (lt_irrefl _)
  exact ⟨z.1, fun n => y (φ n), fun n => hyP _, h1, hz ▸ h2⟩

/-- If `a n → c` and `b n → c` in `[0, 1]`, the intervals between them eventually lie in any
neighbourhood of `c`. -/
theorem eventually_uIcc_subset {c : unitInterval} {V : Set unitInterval} (hV : V ∈ 𝓝 c)
    {a b : ℕ → unitInterval} (ha : Tendsto a atTop (𝓝 c)) (hb : Tendsto b atTop (𝓝 c)) :
    ∀ᶠ n in atTop, uIcc (a n) (b n) ⊆ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  filter_upwards [ha.eventually (Metric.ball_mem_nhds c hε),
    hb.eventually (Metric.ball_mem_nhds c hε)] with n hna hnb
  intro u hu
  apply hball
  rw [Metric.mem_ball]
  rw [Subtype.dist_eq, Real.dist_eq] at hna hnb ⊢
  have hu1 : ((min (a n) (b n) : unitInterval) : ℝ) ≤ u := Subtype.coe_le_coe.mpr hu.1
  have hu2 : (u : ℝ) ≤ ((max (a n) (b n) : unitInterval) : ℝ) := Subtype.coe_le_coe.mpr hu.2
  rw [abs_lt] at hna hnb ⊢
  rcases le_total (a n) (b n) with h | h
  · rw [min_eq_left h] at hu1; rw [max_eq_right h] at hu2
    constructor <;> linarith [hna.1, hna.2, hnb.1, hnb.2]
  · rw [min_eq_right h] at hu1; rw [max_eq_left h] at hu2
    constructor <;> linarith [hna.1, hna.2, hnb.1, hnb.2]

/-- Two different arcs of a closed curve with the same ends are its two arcs between them.
*Axioms used: 1, 3, 4, 5₁.* -/
theorem two_arcs_eq (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S)) {J : Set S} (hJ : σ.IsSCC J) {u v : S} {U₁ U₂ : Set S}
    (hU₁ : σ.IsArc u v U₁) (hU₂ : σ.IsArc u v U₂) (hU₁J : U₁ ⊆ J) (hU₂J : U₂ ⊆ J)
    (hne : U₁ ≠ U₂) : U₁ ∩ U₂ = {u, v} ∧ U₁ ∪ U₂ = J := by
  obtain ⟨D₁, D₂, hD₁, hD₂, hDi, hDu, huniq⟩ :=
    fa_scc_two_arcs h1 h3 h4 h51 hJ (hU₁J hU₁.left_mem) (hU₁J hU₁.right_mem) hU₁.1
  rcases huniq U₁ hU₁J hU₁ with rfl | rfl <;> rcases huniq U₂ hU₂J hU₂ with rfl | rfl
  · exact absurd rfl hne
  · exact ⟨hDi, hDu⟩
  · exact ⟨by rw [inter_comm, hDi], by rw [union_comm, hDu]⟩
  · exact absurd rfl hne

section Th38

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h7 h8

/-- **Theorem 38** (reading recorded in the module docstring). *Axioms used: 1, 2, 3, 4, 5, 7, 8.*
**Shape changes:** the skeleton's placeholder `True` is replaced by this statement; the open arc
`A₁XA₂` is assumed to lie without `J` (`hXE`); the closed curve `A₁XA₂OA₁` is `X ∪ T` with `T`
the arc of `J` from `A₁` to `A₂` through `O`, and its interior is `W`; in (3) the conclusion is
`{B₁, B₂} = {O₁, O₂}`. -/
theorem fa_theorem38 {J C I : Set S} (hJ : σ.IsInteriorOf J I) (hC : σ.IsSCC C)
    {O A₁ A₂ : S} (hO : O ∈ J) (hOC : O ∉ C) (hA₁ : A₁ ∈ C ∩ J) (hA₂ : A₂ ∈ C ∩ J)
    (hA : A₁ ≠ A₂) {X : Set S} (hX : σ.IsArc A₁ A₂ X) (hXC : X ⊆ C)
    (hXE : openArc A₁ A₂ X ⊆ σ.ext I) {T W : Set S} (hT : σ.IsArc A₁ A₂ T) (hTJ : T ⊆ J)
    (hOT : O ∈ T) (hW : σ.IsInteriorOf (X ∪ T) W) (hWE : W ⊆ σ.ext I) :
    ∃ O₁ O₂ : S, ∃ V V' : Set S, O₁ ≠ O ∧ O₂ ≠ O ∧
      σ.IsArc O₁ O₂ V ∧ V ⊆ J ∧ O ∈ V ∧ σ.IsArc O₁ O₂ V' ∧ V' ⊆ J ∧ V ∩ V' = {O₁, O₂} ∧
      (T ⊆ V ∧ (∀ U, σ.IsArc O₁ A₂ U → U ⊆ V → O ∈ U) ∧
        (∀ U, σ.IsArc O₂ A₁ U → U ⊆ V → O ∈ U)) ∧
      (∃ Y W', σ.IsArc O₁ O₂ Y ∧ Y ⊆ C ∧ openArc O₁ O₂ Y ⊆ σ.ext I ∧
        σ.IsInteriorOf (Y ∪ V) W' ∧ W' ⊆ σ.ext I) ∧
      ∀ B₁ B₂ : S, ∀ Z V'' W'' : Set S, B₁ ∈ V' → B₂ ∈ V' → σ.IsArc B₁ B₂ Z → Z ⊆ C →
        openArc B₁ B₂ Z ⊆ σ.ext I → σ.IsArc B₁ B₂ V'' → V'' ⊆ J → O ∈ V'' →
        σ.IsInteriorOf (Z ∪ V'') W'' → W'' ⊆ σ.ext I → ({B₁, B₂} : Set S) = {O₁, O₂} := by
  classical
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  have harc := arcConn h1 h3 h4 h51 h2
  have hTI : TInt σ.region J I := (isInteriorOf_iff h1 h3 h4 h51).mp hJ
  obtain ⟨hIo, -, -, hfrI, hEo, -, -, hfrE, hcl, hdis, hEJ, -, hJcpt, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hJ
  rw [ext_eq_compl_closure h1] at hXE hWE ⊢
  set E := (closure I)ᶜ with hEdef
  have hEJ' : ∀ x ∈ E, x ∉ J := fun x hx hxJ => disjoint_left.mp hEJ hx hxJ
  have hJc : IsClosed J := hJcpt.isClosed
  have hAA : ∀ x ∈ ({A₁, A₂} : Set S), x ∈ J := by
    rintro x (rfl | rfl); exacts [hA₁.2, hA₂.2]
  have hOA₁ : O ≠ A₁ := fun h => hOC (h ▸ hA₁.1)
  have hOA₂ : O ≠ A₂ := fun h => hOC (h ▸ hA₂.1)
  -- the other arc `T'` of `J` from `A₁` to `A₂`, parametrized by `g`
  obtain ⟨D₁, D₂, hD₁, hD₂, hDi, hDu, hDuniq⟩ := fa_scc_two_arcs h1 h3 h4 h51 hJ.1 hA₁.2 hA₂.2 hA
  obtain ⟨T', hT', hTT', hTT'u⟩ : ∃ T', σ.IsArc A₁ A₂ T' ∧ T ∩ T' = {A₁, A₂} ∧ T ∪ T' = J := by
    rcases hDuniq T hTJ hT with rfl | rfl
    · exact ⟨D₂, hD₂, hDi, hDu⟩
    · exact ⟨D₁, hD₁, by rw [inter_comm, hDi], by rw [union_comm, hDu]⟩
  have hT'J : T' ⊆ J := hTT'u ▸ subset_union_right
  have hOT' : O ∉ T' := fun h => by
    have : O ∈ T ∩ T' := ⟨hOT, h⟩
    rw [hTT'] at this
    rcases this with h' | h'
    · exact hOA₁ h'
    · exact hOA₂ h'
  obtain ⟨-, g, hg, hgr, hg0, hg1⟩ := (isArc_iff_tarc h1 h3 h4 h51).mp hT'
  subst hg0 hg1
  have hgJ : range g ⊆ J := hgr ▸ hT'J
  have hOg : ∀ u, g u ≠ O := fun u h => hOT' (hgr ▸ h ▸ mem_range_self u)
  -- the chords
  set Good : unitInterval → unitInterval → Set S → Prop := fun s t Z =>
    s < t ∧ Z ⊆ C ∧ TArc (g s) (g t) Z ∧ Z \ {g s, g t} ⊆ E ∧
      ∃ V W', TArc (g s) (g t) V ∧ V ⊆ J ∧ O ∈ V ∧ TInt σ.region (Z ∪ V) W' ∧ W' ⊆ E
    with hGood
  have hXg : Good 0 1 X := ⟨zero_lt_one' _, hXC, (isArc_iff_tarc h1 h3 h4 h51).mp hX, hXE, T, W,
    (isArc_iff_tarc h1 h3 h4 h51).mp hT, hTJ, hOT, (isInteriorOf_iff h1 h3 h4 h51).mp hW, hWE⟩
  set Ch : Set (unitInterval × unitInterval) := {x | ∃ Z, Good x.1 x.2 Z} with hCh
  have hfin : Ch.Finite := by
    have hXa := (isArc_iff_tarc h1 h3 h4 h51).mp hX
    have hA₁C : g 0 ∈ C := hXC hXa.left_mem
    have hA₂C : g 1 ∈ C := hXC hXa.right_mem
    obtain ⟨C₁, C₂, hC₁, hC₂, hCi, hCu, huniq⟩ := fa_scc_two_arcs h1 h3 h4 h51 hC hA₁C hA₂C hA
    obtain ⟨K, hK, hXK, hXKu⟩ : ∃ K, σ.IsArc (g 0) (g 1) K ∧ X ∩ K = {g 0, g 1} ∧ X ∪ K = C := by
      rcases huniq X hXC hX with rfl | rfl
      · exact ⟨C₂, hC₂, hCi, hCu⟩
      · exact ⟨C₁, hC₁, by rw [inter_comm, hCi], by rw [union_comm, hCu]⟩
    rw [isArc_iff_tarc h1 h3 h4 h51] at hK
    have hXJ : ∀ x ∈ X \ {g 0, g 1}, x ∉ J := fun x hx => hEJ' x (hXE hx)
    have hclaim : ∀ s t Z, Good s t Z → (s = 0 ∧ t = 1) ∨ Z ⊆ K := by
      intro s t Z hZ
      obtain ⟨hst, hZC, hZa, hZE, -⟩ := hZ
      have hZJ : ∀ x ∈ Z \ {g s, g t}, x ∉ J := fun x hx => hEJ' x (hZE hx)
      have hcov : Z \ {g s, g t} ⊆ Kᶜ ∪ Xᶜ := by
        intro x hx
        by_contra h
        simp only [mem_union, mem_compl_iff, not_or, not_not] at h
        have : x ∈ X ∩ K := ⟨h.2, h.1⟩
        rw [hXK] at this
        exact hZJ x hx (hgJ (by rcases this with rfl | rfl <;> exact mem_range_self _))
      have hdisj : Z \ {g s, g t} ∩ (Kᶜ ∩ Xᶜ) = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
        intro hx hxK hxX
        rcases hXKu ▸ hZC hx.1 with h | h
        · exact hxX h
        · exact hxK h
      rcases isPreconnected_iff_subset_of_disjoint.mp hZa.isPreconnected_diff _ _
          hK.isClosed.isOpen_compl hXa.isClosed.isOpen_compl hcov hdisj with h | h
      · left
        have hZX : Z ⊆ X := by
          refine hZa.subset_closure_diff.trans (closure_minimal (fun x hx => ?_) hXa.isClosed)
          rcases hXKu ▸ hZC hx.1 with h' | h'
          · exact h'
          · exact absurd h' (h hx)
        have hend : ∀ u, g u ∈ X → u = 0 ∨ u = 1 := by
          intro u hu
          by_contra hne
          simp only [not_or] at hne
          refine hXJ (g u) ⟨hu, ?_⟩ (hgJ (mem_range_self u))
          simp only [mem_insert_iff, mem_singleton_iff, not_or]
          exact ⟨fun e => hne.1 (hg.injective e), fun e => hne.2 (hg.injective e)⟩
        refine ⟨(hend s (hZX hZa.left_mem)).resolve_right fun e => ?_,
          (hend t (hZX hZa.right_mem)).resolve_left fun e => ?_⟩
        · subst e; exact absurd hst (not_lt.mpr le_one')
        · subst e; exact absurd hst (not_lt.mpr nonneg')
      · right
        refine hZa.subset_closure_diff.trans (closure_minimal (fun x hx => ?_) hK.isClosed)
        rcases hXKu ▸ hZC hx.1 with h' | h'
        · exact absurd h' (h hx)
        · exact h'
    set ChK : Set (unitInterval × unitInterval) := {x | ∃ Z, Good x.1 x.2 Z ∧ Z ⊆ K} with hChK
    have hsub : Ch ⊆ insert (0, 1) ChK := by
      rintro ⟨s, t⟩ ⟨Z, hZ⟩
      rcases hclaim s t Z hZ with ⟨rfl, rfl⟩ | h
      · exact mem_insert _ _
      · exact mem_insert_of_mem _ ⟨Z, hZ, h⟩
    obtain ⟨-, k, hk, hkr, -, -⟩ := hK
    set F : unitInterval × unitInterval → unitInterval × unitInterval :=
      fun x => (Function.invFun k (g x.1), Function.invFun k (g x.2)) with hF
    have hmemK : ∀ x ∈ ChK, g x.1 ∈ range k ∧ g x.2 ∈ range k := by
      rintro x ⟨Z, hZ, hZK⟩
      obtain ⟨-, -, hZa, -⟩ := hZ
      exact ⟨hkr ▸ hZK hZa.left_mem, hkr ▸ hZK hZa.right_mem⟩
    have hinv : ∀ y ∈ range k, k (Function.invFun k y) = y := fun y hy =>
      Function.invFun_eq (f := k) hy
    have hinj : InjOn F ChK := by
      intro x hx y hy hxy
      simp only [hF, Prod.mk.injEq] at hxy
      have e1 : g x.1 = g y.1 := by
        rw [← hinv _ (hmemK x hx).1, ← hinv _ (hmemK y hy).1, hxy.1]
      have e2 : g x.2 = g y.2 := by
        rw [← hinv _ (hmemK x hx).2, ← hinv _ (hmemK y hy).2, hxy.2]
      exact Prod.ext (hg.injective e1) (hg.injective e2)
    have hFk : ∀ x ∈ ChK, k (F x).1 = g x.1 ∧ k (F x).2 = g x.2 := fun x hx =>
      ⟨hinv _ (hmemK x hx).1, hinv _ (hmemK x hx).2⟩
    have hZeq : ∀ x ∈ ChK, ∀ Z, Good x.1 x.2 Z → Z ⊆ K → Z = k '' uIcc (F x).1 (F x).2 := by
      intro x hx Z hZ hZK
      obtain ⟨-, -, hZa, -⟩ := hZ
      refine eq_image_uIcc_of_isArc_subset h1 h4 hk (hkr ▸ hZK) ?_
      rw [(hFk x hx).1, (hFk x hx).2]; exact (isArc_iff_tarc h1 h3 h4 h51).mpr hZa
    have hP : ∀ z ∈ F '' ChK, z.1 ≠ z.2 ∧ k z.1 ∈ J ∧ k z.2 ∈ J ∧
        ∀ u, min z.1 z.2 < u → u < max z.1 z.2 → k u ∉ J := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨Z, hZ, hZK⟩ := hx
      have hx' : x ∈ ChK := ⟨Z, hZ, hZK⟩
      obtain ⟨hst, -, hZa, hZE, -⟩ := id hZ
      refine ⟨fun e => hZa.ne (by rw [← (hFk x hx').1, ← (hFk x hx').2, e]),
        by rw [(hFk x hx').1]; exact hgJ (mem_range_self _),
        by rw [(hFk x hx').2]; exact hgJ (mem_range_self _), ?_⟩
      intro u hu1 hu2 huJ
      have hu : u ∈ uIcc (F x).1 (F x).2 := ⟨hu1.le, hu2.le⟩
      have hne : u ≠ (F x).1 ∧ u ≠ (F x).2 := by
        rcases le_total (F x).1 (F x).2 with h | h
        · rw [min_eq_left h] at hu1; rw [max_eq_right h] at hu2
          exact ⟨hu1.ne', hu2.ne⟩
        · rw [min_eq_right h] at hu1; rw [max_eq_left h] at hu2
          exact ⟨hu2.ne, hu1.ne'⟩
      refine hEJ' (k u) (hZE ⟨hZeq x hx' Z hZ hZK ▸ mem_image_of_mem _ hu, ?_⟩) huJ
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun e => hne.1 (hk.injective (e.trans (hFk x hx').1.symm)),
        fun e => hne.2 (hk.injective (e.trans (hFk x hx').2.symm))⟩
    have hswap : ∀ z ∈ F '' ChK, ∀ w ∈ F '' ChK, z.1 = w.2 → z.2 = w.1 → False := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ e1 e2
      have e1' : g x.1 = g y.2 := by rw [← (hFk x hx).1, ← (hFk y hy).2, e1]
      have e2' : g x.2 = g y.1 := by rw [← (hFk x hx).2, ← (hFk y hy).1, e2]
      obtain ⟨Z, ⟨hxlt, -⟩, -⟩ := hx
      obtain ⟨Z', ⟨hylt, -⟩, -⟩ := hy
      rw [hg.injective e1'] at hxlt
      rw [hg.injective e2'] at hxlt
      exact absurd (hxlt.trans hylt) (lt_irrefl _)
    have hPfin : (F '' ChK).Finite := by
      by_contra hinf
      obtain ⟨c, xs, hxsP, hc1, hc2⟩ := param_chords_accumulate hP hswap hinf
      have hex : ∀ n, ∃ st : unitInterval × unitInterval, st ∈ ChK ∧ F st = xs n :=
        fun n => hxsP n
      choose st hstK hFst using hex
      have hks : ∀ n, k (xs n).1 = g (st n).1 := fun n => by
        rw [← hFst n]; exact (hFk _ (hstK n)).1
      have hkt : ∀ n, k (xs n).2 = g (st n).2 := fun n => by
        rw [← hFst n]; exact (hFk _ (hstK n)).2
      have hk1 : Tendsto (fun n => k (xs n).1) atTop (𝓝 (k c)) :=
        (hk.continuous.tendsto c).comp hc1
      have hk2 : Tendsto (fun n => k (xs n).2) atTop (𝓝 (k c)) :=
        (hk.continuous.tendsto c).comp hc2
      have hyg : k c ∈ range g := (isCompact_range hg.continuous).isClosed.mem_of_tendsto hk1
        (Eventually.of_forall fun n => hks n ▸ mem_range_self _)
      obtain ⟨c', hc'⟩ := hyg
      have hyO : k c ≠ O := hc' ▸ hOg c'
      obtain ⟨N, hN, hyN, hNcl⟩ := exists_region_closure_subset h1 isOpen_compl_singleton
        (show k c ∈ ({O}ᶜ : Set S) from hyO)
      have hs_lim : Tendsto (fun n => (st n).1) atTop (𝓝 c') := by
        rw [hg.tendsto_nhds_iff, hc']
        have : (g ∘ fun n => (st n).1) = fun n => k (xs n).1 := funext fun n => (hks n).symm
        rw [this]; exact hk1
      have ht_lim : Tendsto (fun n => (st n).2) atTop (𝓝 c') := by
        rw [hg.tendsto_nhds_iff, hc']
        have : (g ∘ fun n => (st n).2) = fun n => k (xs n).2 := funext fun n => (hkt n).symm
        rw [this]; exact hk2
      have hNo := isOpen_region hN
      have ev1 := eventually_uIcc_subset (V := k ⁻¹' N)
        (hk.continuous.continuousAt.preimage_mem_nhds (hNo.mem_nhds hyN)) hc1 hc2
      have ev2 := eventually_uIcc_subset (V := g ⁻¹' N)
        (hg.continuous.continuousAt.preimage_mem_nhds (hNo.mem_nhds (hc' ▸ hyN))) hs_lim ht_lim
      obtain ⟨n, hn1, hn2⟩ := (ev1.and ev2).exists
      obtain ⟨Z, hZ, hZK⟩ := hstK n
      have hZeq' := hZeq _ (hstK n) Z hZ hZK
      rw [hFst n] at hZeq'
      obtain ⟨hst, -, hZa, hZE, V, W', hVa, hVJ, hOV, hW', hW'E⟩ := hZ
      have hZN : Z ⊆ N := hZeq' ▸ image_subset_iff.mpr hn1
      have hGN : g '' Icc (st n).1 (st n).2 ⊆ N := by
        rw [← uIcc_of_le hst.le]; exact image_subset_iff.mpr hn2
      have hGa : TArc (g (st n).1) (g (st n).2) (g '' Icc (st n).1 (st n).2) :=
        TArc.image_Icc hg hst
      have hGJ : g '' Icc (st n).1 (st n).2 ⊆ J := (image_subset_range _ _).trans hgJ
      have hZJ : ∀ x ∈ Z \ {g (st n).1, g (st n).2}, x ∉ J := fun x hx => hEJ' x (hZE hx)
      have hΓ := tscc_of_open_disjoint hGa hZa hGJ hZJ
      obtain ⟨R, hR, hRΓ⟩ := ax8Prop h1 h3 h4 h51 h8 _ hΓ
      have hRN : R ⊆ N := th21Prop h1 h3 h4 h5 h7 N hN R hR
        (by rw [hRΓ]; exact (union_subset hZN hGN).trans subset_closure)
      have hVne : V ≠ g '' Icc (st n).1 (st n).2 := fun h =>
        hOT' (hgr ▸ image_subset_range _ _ (h ▸ hOV))
      obtain ⟨hVG, hVGu⟩ := two_arcs_eq h1 h3 h4 h51 hJ.1 ((isArc_iff_tarc h1 h3 h4 h51).mpr hVa)
        ((isArc_iff_tarc h1 h3 h4 h51).mpr hGa) hVJ hGJ hVne
      obtain ⟨m, hsm, hmt⟩ := exists_between hst
      have hOV' : O ∈ V \ {g (st n).1, g (st n).2} := by
        refine ⟨hOV, ?_⟩
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨fun e => hOg _ e.symm, fun e => hOg _ e.symm⟩
      have hDm : g m ∈ g '' Icc (st n).1 (st n).2 \ {g (st n).1, g (st n).2} := by
        refine ⟨mem_image_of_mem _ ⟨hsm.le, hmt.le⟩, ?_⟩
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨fun e => hsm.ne' (hg.injective e), fun e => hmt.ne (hg.injective e)⟩
      have h27 := th27 hopen_region (hpc_region h1 h2) (th21Prop h1 h3 h4 h5 h7) harc
        (ax8Prop h1 h3 h4 h51 h8) (hext_region h1 h3)
        (fun R hR => isCompact_closure_region h1 h4 hR) (not_isCompact_univ h1 h5) hTI hVa hGa
        hVG hVGu hOV' hDm hZa hZE hW' ⟨hΓ, hR, hRΓ⟩
      have hDext : g m ∈ (closure W')ᶜ := by
        rw [closure_eq_union_frontier (isOpen_region hW'.2.1), hW'.2.2]
        rintro (h | h | h)
        · exact hEJ' _ (hW'E h) (hgJ (mem_range_self m))
        · exact hEJ' _ (hZE ⟨h, hDm.2⟩) (hgJ (mem_range_self m))
        · have : g m ∈ V ∩ g '' Icc (st n).1 (st n).2 := ⟨h, hDm.1⟩
          rw [hVG] at this; exact hDm.2 this
      exact hNcl (subset_closure (hRN (h27.2 hDext).1)) rfl
    exact ((Finite.of_finite_image hPfin hinj).insert _).subset hsub
  obtain ⟨x, hxCh, hxmax⟩ := Set.exists_max_image Ch Prod.fst hfin ⟨(0, 1), X, hXg⟩
  obtain ⟨y, ⟨hyCh, hy1⟩, hymin⟩ := Set.exists_min_image {y ∈ Ch | y.1 = x.1} Prod.snd
    (hfin.subset (sep_subset _ _)) ⟨x, hxCh, rfl⟩
  obtain ⟨Y, hY⟩ := hyCh
  have hmax : ∀ s t Z, Good s t Z → y.1 ≤ s → t ≤ y.2 → s = y.1 ∧ t = y.2 := by
    intro s t Z hZ hps htq
    have hs : s = y.1 := le_antisymm (hy1 ▸ hxmax (s, t) ⟨Z, hZ⟩) hps
    exact ⟨hs, le_antisymm htq (hymin (s, t) ⟨⟨Z, hZ⟩, hs.trans hy1⟩)⟩
  obtain ⟨hpq, hYC, hYa, hYE, V, W', hVa, hVJ, hOV, hW', hW'E⟩ := hY
  have toA : ∀ {u v : S} {U : Set S}, TArc u v U → σ.IsArc u v U := fun h =>
    (isArc_iff_tarc h1 h3 h4 h51).mpr h
  have hGa : TArc (g y.1) (g y.2) (g '' Icc y.1 y.2) := TArc.image_Icc hg hpq
  have hGJ : g '' Icc y.1 y.2 ⊆ J := (image_subset_range _ _).trans hgJ
  have hVne : V ≠ g '' Icc y.1 y.2 := fun h => hOT' (hgr ▸ image_subset_range _ _ (h ▸ hOV))
  obtain ⟨hVG, hVGu⟩ := two_arcs_eq h1 h3 h4 h51 hJ.1 (toA hVa) (toA hGa) hVJ hGJ hVne
  obtain ⟨m, hpm, hmq⟩ := exists_between hpq
  have hmV : g m ∉ V := fun h => by
    have : g m ∈ V ∩ g '' Icc y.1 y.2 := ⟨h, mem_image_of_mem _ ⟨hpm.le, hmq.le⟩⟩
    rw [hVG] at this
    rcases this with e | e
    · exact hpm.ne' (hg.injective e)
    · exact hmq.ne (hg.injective e)
  -- `O` lies on every arc of `V` from an end of `V'` to the far end of `T`
  have hthrough : ∀ {a b : unitInterval} {U : Set S}, a < b → m ∈ Icc a b →
      σ.IsArc (g a) (g b) U → U ⊆ V → O ∈ U := by
    intro a b U hab hm hU hUV
    have hGab := TArc.image_Icc hg hab
    have hne : U ≠ g '' Icc a b := fun h => hmV (hUV (h ▸ mem_image_of_mem _ hm))
    obtain ⟨-, hu⟩ := two_arcs_eq h1 h3 h4 h51 hJ.1 hU (toA hGab) (hUV.trans hVJ)
      ((image_subset_range _ _).trans hgJ) hne
    rcases (hu ▸ hO : O ∈ U ∪ g '' Icc a b) with h | ⟨w, -, hw⟩
    · exact h
    · exact absurd hw (hOg w)
  refine ⟨g y.1, g y.2, V, g '' Icc y.1 y.2, hOg _, hOg _, toA hVa, hVJ, hOV, toA hGa, hGJ, hVG,
    ⟨?_, ?_, ?_⟩, ⟨Y, W', toA hYa, hYC, hYE, (isInteriorOf_iff h1 h3 h4 h51).mpr hW', hW'E⟩, ?_⟩
  · intro x hx
    rcases (hVGu ▸ hTJ hx : x ∈ V ∪ g '' Icc y.1 y.2) with h | ⟨u, hu, rfl⟩
    · exact h
    · have : g u ∈ T ∩ T' := ⟨hx, hgr ▸ mem_range_self u⟩
      rw [hTT'] at this
      rcases this with e | e
      · have hu0 : u = 0 := hg.injective e
        have : y.1 = 0 := le_antisymm (hu0 ▸ hu.1) nonneg'
        rw [hu0, ← this]; exact hVa.left_mem
      · have hu1 : u = 1 := hg.injective e
        have : y.2 = 1 := le_antisymm le_one' (hu1 ▸ hu.2)
        rw [hu1, ← this]; exact hVa.right_mem
  · intro U hU hUV
    exact hthrough (hpq.trans_le le_one') ⟨hpm.le, le_one'⟩ hU hUV
  · intro U hU hUV
    exact hthrough (lt_of_le_of_lt nonneg' hpq) ⟨nonneg', hmq.le⟩ hU.symm hUV
  · intro B₁ B₂ Z V'' W'' hB₁ hB₂ hZ hZC hZE hV'' hV''J hOV'' hW'' hW''E
    obtain ⟨s, hs, rfl⟩ := hB₁
    obtain ⟨t, ht, rfl⟩ := hB₂
    have hst : s ≠ t := fun e => hZ.1 (e ▸ rfl)
    have hZa := (isArc_iff_tarc h1 h3 h4 h51).mp hZ
    have hV''a := (isArc_iff_tarc h1 h3 h4 h51).mp hV''
    have hW''t := (isInteriorOf_iff h1 h3 h4 h51).mp hW''
    rcases lt_or_gt_of_ne hst with hlt | hlt
    · obtain ⟨rfl, rfl⟩ := hmax s t Z ⟨hlt, hZC, hZa, hZE, V'', W'', hV''a, hV''J, hOV'', hW''t,
        hW''E⟩ hs.1 ht.2
      rfl
    · have hZE' : Z \ {g t, g s} ⊆ E := by rw [pair_comm]; exact hZE
      obtain ⟨rfl, rfl⟩ := hmax t s Z ⟨hlt, hZC, hZa.symm, hZE', V'', W'', hV''a.symm, hV''J,
        hOV'', hW''t, hW''E⟩ ht.1 hs.2
      exact pair_comm _ _

end Th38

end HPC.Moore
