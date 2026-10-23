import HPC.Moore.M41Replace
import HPC.Moore.M19A

/-!
# Theorem 41, Case II: the geometric lemmas (batch 140, item A)

Notation of the proof of `fa_theorem41` (`HPC/Moore/M41.lean`): `Eᵢ = S − Iᵢ'` is the exterior of
`Jᵢ`, `Ω = E₁ ∩ E₂`, and `V` is a component of `Ω` whose closure is not compact.

* `Gen.exists_unbounded_component`: such a component exists.
* `Gen.disjoint_of_unbounded`: `V` misses the interior of every closed curve that misses `V`.
* `chord_through`, `chord_subset`: a *chord* of `J₁` over a closed set `K` is an arc of `J₁` with
  its ends on `K` and its open arc off `K`; every point of `J₁ − K` lies on one, and two chords
  whose open arcs meet are equal.
* `chord_side`: if one point of the open arc of a chord of `J₁` over `J₂` (lying without `J₂`) is
  a limit point of `V`, every point of the chord is (batch 138's `side_propagate`).
* `pocket`: for such a chord `Z` from `p` to `q`, and the arc `C` of `J₂` from `p` to `q` not
  containing a given point `O` of `J₂` that is a limit point of `V`, no point of the open arc `C`
  is a limit point of `V` (Theorem 27 and `disjoint_of_unbounded`).
* `chords_null`: arcs of a closed curve with pairwise disjoint open arcs are a null family
  (Theorem A of 1919).
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

namespace Gen

variable {X : Type*} [TopologicalSpace X]

/-- A point of `F` in the closure of a component of `F` lies in that component. -/
theorem mem_connectedComponentIn_of_mem_closure {F : Set X} {x y : X}
    (hy : y ∈ closure (connectedComponentIn F x)) (hyF : y ∈ F) :
    y ∈ connectedComponentIn F x := by
  by_cases hx : x ∈ F
  · have hpc : IsPreconnected (insert y (connectedComponentIn F x)) :=
      isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
        (insert_subset hy subset_closure)
    exact hpc.subset_connectedComponentIn (Or.inr (mem_connectedComponentIn hx))
      (insert_subset hyF (connectedComponentIn_subset _ _)) (mem_insert _ _)
  · rw [connectedComponentIn_eq_empty hx, closure_empty] at hy
    exact hy.elim

variable [LocallyConnectedSpace X]

/-- The frontier of a component of the complement of a closed set `K` lies in `K`. -/
theorem frontier_connectedComponentIn_subset {K : Set X} (hK : IsClosed K) (x : X) :
    frontier (connectedComponentIn Kᶜ x) ⊆ K := by
  intro y hy
  by_contra hyK
  have h1 := mem_connectedComponentIn_of_mem_closure hy.1 hyK
  have h2 := hy.2
  rw [hK.isOpen_compl.connectedComponentIn.interior_eq] at h2
  exact h2 h1

variable [T2Space X]

/-- **An unbounded component.** If the closed set `K` lies in the interior of a compact set `N`,
and some connected set `E` has a noncompact closure meeting `K`, then some component of `Kᶜ` has a
noncompact closure. -/
theorem exists_unbounded_component {K N E : Set X} (hK : IsClosed K) (hN : IsCompact N)
    (hKN : K ⊆ interior N) (hE : IsPreconnected E) (hEc : ¬ IsCompact (closure E))
    (hEK : (closure E ∩ K).Nonempty) :
    ∃ x ∈ Kᶜ, ¬ IsCompact (closure (connectedComponentIn Kᶜ x)) := by
  by_contra hall
  push_neg at hall
  have hNc : IsClosed N := hN.isClosed
  have hfrc : IsCompact (frontier N) := hN.of_isClosed_subset isClosed_frontier
    (frontier_subset_closure.trans hNc.closure_subset)
  have hfrK : frontier N ⊆ Kᶜ := fun y hy hyK => hy.2 (hKN hyK)
  obtain ⟨t, ht⟩ := hfrc.elim_finite_subcover (fun y : frontier N => connectedComponentIn Kᶜ y)
    (fun y => hK.isOpen_compl.connectedComponentIn)
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, mem_connectedComponentIn (hfrK hy)⟩)
  set B := N ∪ ⋃ y ∈ t, closure (connectedComponentIn Kᶜ (y : X)) with hB
  have hBc : IsCompact B := hN.union (t.isCompact_biUnion fun y _ => hall y (hfrK y.2))
  have hEB : E ⊆ B := by
    intro q hq
    by_cases hqN : q ∈ N
    · exact Or.inl hqN
    have hqK : q ∈ Kᶜ := fun h => hqN (interior_subset (hKN h))
    set C := connectedComponentIn Kᶜ q with hC
    by_cases hCfr : (C ∩ frontier N).Nonempty
    · obtain ⟨y, hyC, hyfr⟩ := hCfr
      obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.mp (ht hyfr)
      have e1 : C = connectedComponentIn Kᶜ y := connectedComponentIn_eq hyC
      have e2 : connectedComponentIn Kᶜ (z : X) = connectedComponentIn Kᶜ y :=
        connectedComponentIn_eq hyz
      refine Or.inr (mem_iUnion₂.mpr ⟨z, hzt, subset_closure ?_⟩)
      rw [e2, ← e1]
      exact mem_connectedComponentIn hqK
    · exfalso
      rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hCfr
      have hCN : C ⊆ (closure N)ᶜ := conn_sub_ext_of_frontier isPreconnected_connectedComponentIn
        hCfr ⟨q, mem_connectedComponentIn hqK, by rwa [hNc.closure_eq]⟩
      have hCcl : IsClosed C := by
        refine isClosed_of_closure_subset fun y hy => ?_
        refine mem_connectedComponentIn_of_mem_closure hy fun hyK => ?_
        have h1 : y ∈ closure (closure N)ᶜ := closure_mono hCN hy
        rw [closure_compl] at h1
        exact h1 (interior_mono subset_closure (hKN hyK))
      have hEC : E ⊆ C := hE.subset_isClopen ⟨hCcl, hK.isOpen_compl.connectedComponentIn⟩
        ⟨q, hq, mem_connectedComponentIn hqK⟩
      obtain ⟨y, hyE, hyK⟩ := hEK
      exact (connectedComponentIn_subset _ _ (hCcl.closure_subset_iff.mpr hEC hyE)) hyK
  exact hEc (hBc.of_isClosed_subset isClosed_closure (hBc.isClosed.closure_subset_iff.mpr hEB))

omit [LocallyConnectedSpace X] [T2Space X] in
/-- A connected set `V` with noncompact closure misses the interior `R` of every closed curve `J`
that misses `V` (when closures of regions are compact). -/
theorem disjoint_of_unbounded {reg : Set (Set X)} (hcpt : ∀ R ∈ reg, IsCompact (closure R))
    {J R V : Set X} (hR : TInt reg J R) (hV : IsPreconnected V) (hVc : ¬ IsCompact (closure V))
    (hVJ : Disjoint V J) : Disjoint V R := by
  rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
  intro hne
  have hVR : V ⊆ R := conn_sub_of_frontier hV (hR.2.2 ▸ hVJ) hne
  exact hVc ((hcpt R hR.2.1).of_isClosed_subset isClosed_closure (closure_mono hVR))

end Gen

variable {S : Type*} {σ : Space S}

section Chords

variable (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h51 : Space.Axiom5₁ (S := S))
include h1 h3 h4 h51

/-- The other arc of a closed curve between the ends of one of its arcs. -/
theorem exists_other_arc {J : Set S} (hJ : σ.IsSCC J) {p q : S} {Z : Set S}
    (hZ : @TArc S σ.topology p q Z) (hZJ : Z ⊆ J) :
    ∃ W, @TArc S σ.topology p q W ∧ Z ∩ W = {p, q} ∧ Z ∪ W = J := by
  letI := σ.topology
  obtain ⟨C₁, C₂, hC₁, hC₂, hCi, hCu, huniq⟩ :=
    fa_scc_two_arcs h1 h3 h4 h51 hJ (hZJ hZ.left_mem) (hZJ hZ.right_mem) hZ.ne
  rcases huniq Z hZJ ((isArc_iff_tarc h1 h3 h4 h51).mpr hZ) with rfl | rfl
  · exact ⟨C₂, (isArc_iff_tarc h1 h3 h4 h51).mp hC₂, hCi, hCu⟩
  · exact ⟨C₁, (isArc_iff_tarc h1 h3 h4 h51).mp hC₁, by rw [inter_comm, hCi],
      by rw [union_comm, hCu]⟩

/-- **A chord through a point.** A point `x` of the closed curve `J₁` not on the closed set `K`,
where `J₁ ∩ K` has two points, lies on an arc of `J₁` with its ends on `K` and its open arc off
`K`. -/
theorem chord_through {J₁ K : Set S} (hJ₁ : σ.IsSCC J₁) (hK : @IsClosed S σ.topology K)
    {x : S} (hx : x ∈ J₁) (hxK : x ∉ K) {y y' : S} (hy : y ∈ J₁ ∩ K) (hy' : y' ∈ J₁ ∩ K)
    (hyy : y ≠ y') :
    ∃ p q Z, @TArc S σ.topology p q Z ∧ Z ⊆ J₁ ∧ p ∈ K ∧ q ∈ K ∧ x ∈ Z \ {p, q} ∧
      Disjoint (Z \ {p, q}) K := by
  letI := σ.topology
  haveI := t2Space h1
  have hxy : x ≠ y := fun e => hxK (e ▸ hy.2)
  obtain ⟨D₁, D₂, hD₁, hD₂, hDi, hDu⟩ := exists_two_arcs_of_isSCC h1 h3 h4 h51 hJ₁ hx hy.1 hxy
  rw [isArc_iff_tarc h1 h3 h4 h51] at hD₁ hD₂
  obtain ⟨p, hpK, D₁', hD₁'D, hD₁', hD₁'K⟩ := hD₁.first_point hK ⟨y, hD₁.right_mem, hy.2⟩ hxK
  obtain ⟨q, hqK, D₂', hD₂'D, hD₂', hD₂'K⟩ := hD₂.first_point hK ⟨y, hD₂.right_mem, hy.2⟩ hxK
  have whole : ∀ {D D' : Set S}, TArc x y D → D' ⊆ D → TArc x y D' → D' = D :=
    fun hD hD'D hD' => subset_antisymm hD'D fun z hz =>
      hD.mem_of_isPreconnected hz hD'.isPreconnected hD'D hD'.left_mem hD'.right_mem
  have hpq : p ≠ q := by
    rintro rfl
    have hpy : p = y := by
      have : p ∈ D₁ ∩ D₂ := ⟨hD₁'D hD₁'.right_mem, hD₂'D hD₂'.right_mem⟩
      rw [hDi] at this
      rcases this with h | h
      · exact absurd (h ▸ hpK) hxK
      · exact h
    subst hpy
    have e1 := whole hD₁ hD₁'D hD₁'
    have e2 := whole hD₂ hD₂'D hD₂'
    subst e1 e2
    have hy'D : y' ∈ D₁' ∪ D₂' := hDu ▸ hy'.1
    rcases hy'D with h | h
    · have : y' ∈ D₁' ∩ K := ⟨h, hy'.2⟩
      rw [hD₁'K] at this
      exact hyy this.symm
    · have : y' ∈ D₂' ∩ K := ⟨h, hy'.2⟩
      rw [hD₂'K] at this
      exact hyy this.symm
  have hint : D₁' ∩ D₂' = {x} := by
    apply subset_antisymm
    · rintro z ⟨hz1, hz2⟩
      have : z ∈ D₁ ∩ D₂ := ⟨hD₁'D hz1, hD₂'D hz2⟩
      rw [hDi] at this
      rcases this with h | h
      · exact h
      · exfalso
        have hzK : z ∈ K := (mem_singleton_iff.mp h) ▸ hy.2
        have e1 : z ∈ D₁' ∩ K := ⟨hz1, hzK⟩
        have e2 : z ∈ D₂' ∩ K := ⟨hz2, hzK⟩
        rw [hD₁'K] at e1
        rw [hD₂'K] at e2
        exact hpq ((mem_singleton_iff.mp e1).symm.trans (mem_singleton_iff.mp e2))
    · exact singleton_subset_iff.mpr ⟨hD₁'.left_mem, hD₂'.left_mem⟩
  have hJ₁D : D₁ ∪ D₂ ⊆ J₁ := hDu.subset
  refine ⟨p, q, D₁' ∪ D₂', hD₁'.symm.union hD₂' hint,
    union_subset (hD₁'D.trans (subset_union_left.trans hJ₁D))
      (hD₂'D.trans (subset_union_right.trans hJ₁D)), hpK, hqK, ⟨Or.inl hD₁'.left_mem, ?_⟩, ?_⟩
  · rintro (h | h)
    · exact hxK (h ▸ hpK)
    · exact hxK ((mem_singleton_iff.mp h) ▸ hqK)
  · rw [disjoint_left]
    rintro z ⟨hz, hzpq⟩ hzK
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzpq
    rcases hz with h | h
    · have : z ∈ D₁' ∩ K := ⟨h, hzK⟩
      rw [hD₁'K] at this
      exact hzpq.1 this
    · have : z ∈ D₂' ∩ K := ⟨h, hzK⟩
      rw [hD₂'K] at this
      exact hzpq.2 this

/-- **Two chords whose open arcs meet.** If `Z` is an arc of `J₁` with ends on `K`, and `Z'` an arc
of `J₁` whose open arc misses `K` and meets the open arc of `Z`, then `Z' ⊆ Z`. -/
theorem chord_subset {J₁ K : Set S} (hJ₁ : σ.IsSCC J₁) {p q p' q' : S} {Z Z' : Set S}
    (hZ : @TArc S σ.topology p q Z) (hZ' : @TArc S σ.topology p' q' Z') (hZJ : Z ⊆ J₁)
    (hZ'J : Z' ⊆ J₁) (hp : p ∈ K) (hq : q ∈ K) (hZ'K : Disjoint (Z' \ {p', q'}) K)
    (hmeet : ((Z \ {p, q}) ∩ (Z' \ {p', q'})).Nonempty) : Z' ⊆ Z := by
  letI := σ.topology
  haveI := t2Space h1
  obtain ⟨W, hW, hZW, hZWu⟩ := exists_other_arc h1 h3 h4 h51 hJ₁ hZ hZJ
  have hsub : Z' \ {p', q'} ⊆ Wᶜ ∪ Zᶜ := by
    intro z hz
    by_contra hc
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hc
    have : z ∈ Z ∩ W := ⟨hc.2, hc.1⟩
    rw [hZW] at this
    rcases this with h | h
    · exact disjoint_left.mp hZ'K hz (h ▸ hp)
    · exact disjoint_left.mp hZ'K hz ((mem_singleton_iff.mp h) ▸ hq)
  have hempty : (Z' \ {p', q'}) ∩ (Wᶜ ∩ Zᶜ) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and, mem_compl_iff]
    intro hz hzW hzZ
    have : z ∈ J₁ := hZ'J hz.1
    rw [← hZWu] at this
    rcases this with h | h
    exacts [hzZ h, hzW h]
  rcases (isPreconnected_iff_subset_of_disjoint.mp hZ'.isPreconnected_diff) _ _
    hW.isClosed.isOpen_compl hZ.isClosed.isOpen_compl hsub hempty with h | h
  · have hZ'Z : Z' \ {p', q'} ⊆ Z := fun z hz => by
      have : z ∈ J₁ := hZ'J hz.1
      rw [← hZWu] at this
      rcases this with h' | h'
      · exact h'
      · exact absurd h' (h hz)
    exact hZ'.subset_closure_diff.trans (hZ.isClosed.closure_subset_iff.mpr hZ'Z)
  · obtain ⟨z, hz, hz'⟩ := hmeet
    exact absurd hz.1 (h hz')

/-- **The chords of a closed curve form a null family** (Theorem A of 1919): arcs of a closed curve
`L` with pairwise disjoint open arcs; for every `ε > 0`, only finitely many reach distance `ε` from
their first end (for a metric of the space, batch 137's `metrizable`). -/
theorem chords_null {L : Set S} (hL : σ.IsSCC L) {ι : Type*} (a b : ι → S) (Z : ι → Set S)
    (hZ : ∀ i, @TArc S σ.topology (a i) (b i) (Z i)) (hZL : ∀ i, Z i ⊆ L)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Z i \ {a i, b i}) (Z j \ {a j, b j})) :
    letI := σ.topology
    haveI := metrizable h1 h3 h51
    letI := TopologicalSpace.metrizableSpaceMetric S
    ∀ ε > 0, {i | ∃ x ∈ Z i, ε ≤ dist x (a i)}.Finite := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := metrizable h1 h3 h51
  letI := TopologicalSpace.metrizableSpaceMetric S
  intro ε hε
  by_contra hinf
  have hG : {i | ∃ x ∈ Z i, ε ≤ dist x (a i)}.Infinite := hinf
  set e := hG.natEmbedding with he
  have hpt : ∀ n, ∃ x ∈ Z (e n), ε ≤ dist x (a (e n)) := fun n => (e n).2
  choose x hx hxd using hpt
  have hLc : IsCompact L := by
    obtain ⟨A, B, C₁, C₂, hC₁, hC₂, -, rfl⟩ := (isSCC_iff_tscc h1 h3 h4 h51).mp hL
    exact hC₁.isCompact.union hC₂.isCompact
  obtain ⟨c, -, φ, hφ, hxc⟩ := hLc.tendsto_subseq (x := x) fun n => hZL _ (hx n)
  obtain ⟨d, -, ψ, hψ, had⟩ :=
    hLc.tendsto_subseq (x := fun n => a (e (φ n))) fun n => hZL _ (hZ _).left_mem
  have hxc' : Filter.Tendsto (fun n => x (φ (ψ n))) Filter.atTop (𝓝 c) :=
    hxc.comp hψ.tendsto_atTop
  have hcd : ε ≤ dist c d :=
    ge_of_tendsto (hxc'.dist had) (Filter.Eventually.of_forall fun n => hxd _)
  have hε3 : 0 < ε / 3 := by positivity
  have hMN : Disjoint (Metric.closedBall c (ε / 3)) (Metric.closedBall d (ε / 3)) := by
    rw [disjoint_left]
    intro y hy1 hy2
    rw [Metric.mem_closedBall] at hy1 hy2
    have := dist_triangle_right c d y
    rw [dist_comm c y, dist_comm d y] at this
    linarith
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    ((hxc'.eventually (Metric.closedBall_mem_nhds c hε3)).and
      (had.eventually (Metric.closedBall_mem_nhds d hε3)))
  set k : ℕ → ι := fun n => (e (φ (ψ (n + n₀))) : ι) with hk
  have hkinj : Function.Injective k := by
    intro i j hij
    have := Subtype.ext hij
    have := e.injective this
    have := hφ.injective this
    have := hψ.injective this
    omega
  refine m19_theoremA h1 h3 h4 h51 hL ((isClosedM_iff h1).mpr Metric.isClosed_closedBall)
    ((isClosedM_iff h1).mpr Metric.isClosed_closedBall) hMN
    ⟨fun n => Z (k n), fun n => ⟨⟨a (k n), b (k n), (isArc_iff_tarc h1 h3 h4 h51).mpr (hZ _)⟩,
      hZL _, ⟨x (φ (ψ (n + n₀))), hx _, (hn₀ (n + n₀) (by omega)).1⟩,
      ⟨a (k n), (hZ _).left_mem, (hn₀ (n + n₀) (by omega)).2⟩⟩, ?_⟩
  rintro i j hij ⟨X', Y', T, hT, hTsub⟩
  have hkij : k i ≠ k j := hkinj.ne hij
  have hfin : (openArc X' Y' T).Finite := by
    refine (Set.toFinite ({a (k i), b (k i), a (k j), b (k j)} : Set S)).subset ?_
    intro z hz
    obtain ⟨hzi, hzj⟩ := hTsub hz
    by_cases h₁ : z ∈ ({a (k i), b (k i)} : Set S)
    · rcases h₁ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    by_cases h₂ : z ∈ ({a (k j), b (k j)} : Set S)
    · rcases h₂ with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    exact absurd (hdisj _ _ hkij) (not_disjoint_iff.mpr ⟨z, ⟨hzi, h₁⟩, ⟨hzj, h₂⟩⟩)
  obtain ⟨hXY, f, hf, rfl, rfl, rfl⟩ := (isArc_iff_tarc h1 h3 h4 h51).mp hT
  have hinf' : (openArc (f 0) (f 1) (range f)).Infinite := by
    rw [openArc, TArc.diff_eq hf]
    exact (Set.Ioo_infinite (zero_lt_one' unitInterval)).image hf.injective.injOn
  exact hinf' hfin

end Chords

end HPC.Moore
