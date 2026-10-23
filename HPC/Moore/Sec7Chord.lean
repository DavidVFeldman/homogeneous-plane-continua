import HPC.Moore.Sec7B

/-!
# Moore, F.A. (1916), §7: chords of a closed curve (batch 139)

The device behind Theorems 37 and 38. `J` and `C` are closed curves, `T` is an arc of `J`
(parametrized by an embedding `g`, from `A₁ = g 0` to `A₂ = g 1`) through `O = g o`, and `O` is not
on `C`. A *chord* is an arc of `C` from a point `g s` of `T` to a point `g t` (`s ≤ o ≤ t`) whose
open part misses `J`. Given any family of chords containing an arc `A₁XA₂` of `C`,
`exists_maximal_chord` gives a chord `g p … g q` in the family such that no other chord of the family
has its ends `g s`, `g t` on the intervals `g p … O` and `O … g q` of `T`.

The proof shows that the family has only finitely many pairs of ends (`param_chords_finite`):
except for `A₁XA₂` itself, every chord lies in the other arc `K` of `C` from `A₁` to `A₂`; in the
parameter of `K` distinct chords have disjoint open intervals (their ends are on `J`, their open
parts are not), and all have length at least some `λ > 0` (compactness, since their two ends lie in
the disjoint compact sets `C ∩ g[0, o]` and `C ∩ g[o, 1]`). This replaces Moore's limit-point
argument (the points `L₁`, `L₂`, `F`, `G` of p. 153) and makes his monotonicity statement
(\"in view of Theorem 29 …\") unnecessary.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-- A `λ`-separated set of points of `[0, 1]` is finite. -/
theorem finite_of_separated {α : Type*} {P : Set α} {l : ℝ} (hl : 0 < l) (m : α → ℝ)
    (hm01 : ∀ x ∈ P, 0 ≤ m x ∧ m x ≤ 1) (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → l ≤ |m x - m y|) :
    P.Finite := by
  classical
  refine Finite.of_finite_image (f := fun x => ⌊m x / l⌋₊) ?_ ?_
  · refine (finite_Iic ⌊1 / l⌋₊).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Nat.floor_le_floor (div_le_div_of_nonneg_right (hm01 x hx).2 hl.le)
  · intro x hx y hy hxy
    by_contra hne
    have h := hsep x hx y hy hne
    simp only at hxy
    have hx0 : 0 ≤ m x / l := div_nonneg (hm01 x hx).1 hl.le
    have hy0 : 0 ≤ m y / l := div_nonneg (hm01 y hy).1 hl.le
    have h1 := Nat.floor_le hx0
    have h2 := Nat.lt_floor_add_one (m x / l)
    have h3 := Nat.floor_le hy0
    have h4 := Nat.lt_floor_add_one (m y / l)
    rw [hxy] at h1 h2
    have : |m x / l - m y / l| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hl, div_lt_one hl] at this
    linarith

/-- Pairs of parameters `(a, b)` of a map `k` of `[0, 1]`, with `k a` in the closed set `G₁` and `k b`
in the closed set `G₂` (no point of `k` in both), with `k a`, `k b` in `Z` but no `k u` in `Z` for
`u` strictly between `a` and `b`: there are only finitely many. -/
theorem param_chords_finite {X : Type*} [TopologicalSpace X] {k : unitInterval → X}
    (hk : Continuous k) {G₁ G₂ Z : Set X} (hG₁ : IsClosed G₁) (hG₂ : IsClosed G₂)
    (hG : ∀ u, k u ∈ G₁ → k u ∈ G₂ → False) {P : Set (unitInterval × unitInterval)}
    (hP : ∀ x ∈ P, k x.1 ∈ G₁ ∧ k x.2 ∈ G₂ ∧ k x.1 ∈ Z ∧ k x.2 ∈ Z ∧
      ∀ u, min x.1 x.2 < u → u < max x.1 x.2 → k u ∉ Z) : P.Finite := by
  rcases P.eq_empty_or_nonempty with hPe | ⟨x₁, hx₁⟩
  · rw [hPe]; exact finite_empty
  set Q : Set (unitInterval × unitInterval) := {x | k x.1 ∈ G₁ ∧ k x.2 ∈ G₂} with hQ
  have hQc : IsClosed Q :=
    (hG₁.preimage (hk.comp continuous_fst)).inter (hG₂.preimage (hk.comp continuous_snd))
  have hPQ : P ⊆ Q := fun x hx => ⟨(hP x hx).1, (hP x hx).2.1⟩
  have hf : Continuous fun x : unitInterval × unitInterval => |((x.1 : ℝ) - x.2)| :=
    (continuous_subtype_val.comp continuous_fst |>.sub
      (continuous_subtype_val.comp continuous_snd)).abs
  obtain ⟨x₀, hx₀Q, hmin⟩ := hQc.isCompact.exists_isMinOn ⟨x₁, hPQ hx₁⟩ hf.continuousOn
  set l := |((x₀.1 : ℝ) - x₀.2)| with hl
  have hl0 : 0 < l := by
    rw [hl, abs_pos, sub_ne_zero]
    intro h
    have : x₀.1 = x₀.2 := Subtype.ext h
    exact hG x₀.1 hx₀Q.1 (this ▸ hx₀Q.2)
  have hlen : ∀ x ∈ P, l ≤ ((max x.1 x.2 : unitInterval) : ℝ) - (min x.1 x.2 : unitInterval) := by
    intro x hx
    have h := hmin (hPQ hx)
    simp only [mem_setOf_eq] at h
    rcases le_total x.1 x.2 with h' | h'
    · rw [max_eq_right h', min_eq_left h',
        ← abs_of_nonneg (sub_nonneg.mpr (Subtype.coe_le_coe.mpr h')), abs_sub_comm]
      exact h
    · rw [max_eq_left h', min_eq_right h',
        ← abs_of_nonneg (sub_nonneg.mpr (Subtype.coe_le_coe.mpr h'))]
      exact h
  have hmemZ : ∀ x ∈ P, k (min x.1 x.2) ∈ Z ∧ k (max x.1 x.2) ∈ Z := by
    intro x hx
    obtain ⟨-, -, h1, h2, -⟩ := hP x hx
    constructor
    · rcases min_choice x.1 x.2 with h | h <;> rw [h] <;> assumption
    · rcases max_choice x.1 x.2 with h | h <;> rw [h] <;> assumption
  have hpos : ∀ x ∈ P, min x.1 x.2 < max x.1 x.2 := by
    intro x hx
    have := hlen x hx
    exact Subtype.coe_lt_coe.mp (by linarith)
  have key : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → min x.1 x.2 ≤ min y.1 y.2 →
      max x.1 x.2 ≤ min y.1 y.2 := by
    intro x hx y hy hxy hle
    by_contra hlt
    push_neg at hlt
    rcases lt_or_eq_of_le hle with hlt' | heq
    · exact (hP x hx).2.2.2.2 _ hlt' hlt (hmemZ y hy).1
    · have hMM : max x.1 x.2 = max y.1 y.2 := by
        rcases lt_trichotomy (max x.1 x.2) (max y.1 y.2) with h | h | h
        · exact absurd (hmemZ x hx).2 ((hP y hy).2.2.2.2 _ hlt h)
        · exact h
        · exact absurd (hmemZ y hy).2 ((hP x hx).2.2.2.2 _ (heq ▸ hpos y hy) h)
      obtain ⟨hxG₁, -, -, -, -⟩ := hP x hx
      obtain ⟨-, hyG₂, -, -, -⟩ := hP y hy
      rcases le_total x.1 x.2 with h1 | h1 <;> rcases le_total y.1 y.2 with h2 | h2
      · rw [min_eq_left h1, min_eq_left h2] at heq
        rw [max_eq_right h1, max_eq_right h2] at hMM
        exact hxy (Prod.ext heq hMM)
      · rw [min_eq_left h1, min_eq_right h2] at heq
        exact hG x.1 hxG₁ (heq ▸ hyG₂)
      · rw [max_eq_left h1, max_eq_right h2] at hMM
        exact hG x.1 hxG₁ (hMM ▸ hyG₂)
      · rw [min_eq_right h1, min_eq_right h2] at heq
        rw [max_eq_left h1, max_eq_left h2] at hMM
        exact hxy (Prod.ext hMM heq)
  refine finite_of_separated hl0 (fun x => ((min x.1 x.2 : unitInterval) : ℝ))
    (fun x _ => ⟨(min x.1 x.2).2.1, (min x.1 x.2).2.2⟩) ?_
  intro x hx y hy hxy
  rcases le_total (min x.1 x.2) (min y.1 y.2) with h | h
  · have h1 := Subtype.coe_le_coe.mpr (key x hx y hy hxy h)
    have h2 := hlen x hx
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := Subtype.coe_le_coe.mpr (key y hy x hx (Ne.symm hxy) h)
    have h2 := hlen y hy
    rw [abs_of_nonneg (by linarith)]
    linarith

section Chord

variable (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h51 : Space.Axiom5₁ (S := S))
include h1 h3 h4 h51

/-- **Chords.** `T` (parametrized by `g`) is an arc of `J` through `O = g o`, `C` a closed curve
not containing `O`. `Good s t Z` is any property of arcs `Z` of `C` from `g s` to `g t`
(`s ≤ o ≤ t`) whose open part misses `J`, and `A₁XA₂` (`s = 0`, `t = 1`) has it. Then some
`Good` chord `g p … g q` is innermost: no `Good` chord has ends `g s`, `g t` with
`p ≤ s ≤ o ≤ t ≤ q` other than `s = p`, `t = q`. *Axioms used: 1, 3, 4, 5₁.* -/
theorem exists_maximal_chord {J C X : Set S} (hC : σ.IsSCC C) {g : unitInterval → S}
    (hg : @IsEmbedding _ _ _ σ.topology g) (hgJ : range g ⊆ J) {o : unitInterval}
    (hoC : g o ∉ C) (Good : unitInterval → unitInterval → Set S → Prop)
    (hGood : ∀ s t Z, Good s t Z → s ≤ o ∧ o ≤ t ∧ Z ⊆ C ∧ @TArc S σ.topology (g s) (g t) Z ∧
      ∀ x ∈ Z \ {g s, g t}, x ∉ J)
    (hX : Good 0 1 X) :
    ∃ p q Y, Good p q Y ∧ ∀ s t Z, Good s t Z → p ≤ s → t ≤ q → s = p ∧ t = q := by
  classical
  letI := σ.topology
  haveI := t2Space h1
  set Ch : Set (unitInterval × unitInterval) := {x | ∃ Z, Good x.1 x.2 Z} with hCh
  obtain ⟨-, -, hXC, hXa, hXJ⟩ := hGood 0 1 X hX
  have hA₁C : g 0 ∈ C := hXC hXa.left_mem
  have hA₂C : g 1 ∈ C := hXC hXa.right_mem
  have ho0 : o ≠ 0 := fun h => hoC (h ▸ hA₁C)
  have ho1 : o ≠ 1 := fun h => hoC (h ▸ hA₂C)
  obtain ⟨C₁, C₂, hC₁, hC₂, hCi, hCu, huniq⟩ :=
    fa_scc_two_arcs h1 h3 h4 h51 hC hA₁C hA₂C hXa.ne
  obtain ⟨K, hK, hXK, hXKu⟩ : ∃ K, σ.IsArc (g 0) (g 1) K ∧ X ∩ K = {g 0, g 1} ∧ X ∪ K = C := by
    rcases huniq X hXC ((isArc_iff_tarc h1 h3 h4 h51).mpr hXa) with rfl | rfl
    · exact ⟨C₂, hC₂, hCi, hCu⟩
    · exact ⟨C₁, hC₁, by rw [inter_comm, hCi], by rw [union_comm, hCu]⟩
  rw [isArc_iff_tarc h1 h3 h4 h51] at hK
  have hclaim : ∀ s t Z, Good s t Z → (s = 0 ∧ t = 1) ∨ Z ⊆ K := by
    intro s t Z hZ
    obtain ⟨hso, hot, hZC, hZa, hZJ⟩ := hGood s t Z hZ
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
      · subst e; exact ho1 (le_antisymm le_one' hso)
      · subst e; exact ho0 (le_antisymm hot nonneg')
    · right
      refine hZa.subset_closure_diff.trans (closure_minimal (fun x hx => ?_) hK.isClosed)
      rcases hXKu ▸ hZC hx.1 with h' | h'
      · exact absurd h' (h hx)
      · exact h'
  set ChK : Set (unitInterval × unitInterval) := {x | ∃ Z, Good x.1 x.2 Z ∧ Z ⊆ K}
    with hChK
  have hsub : Ch ⊆ insert (0, 1) ChK := by
    rintro ⟨s, t⟩ ⟨Z, hZ⟩
    rcases hclaim s t Z hZ with ⟨rfl, rfl⟩ | h
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨Z, hZ, h⟩
  obtain ⟨-, k, hk, hkr, hk0, hk1⟩ := hK
  set F : unitInterval × unitInterval → unitInterval × unitInterval :=
    fun x => (Function.invFun k (g x.1), Function.invFun k (g x.2)) with hF
  have hmemK : ∀ x ∈ ChK, g x.1 ∈ range k ∧ g x.2 ∈ range k := by
    rintro x ⟨Z, hZ, hZK⟩
    obtain ⟨-, -, -, hZa, -⟩ := hGood _ _ _ hZ
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
  have hfinF : (F '' ChK).Finite := by
    refine param_chords_finite hk.continuous (G₁ := g '' Icc 0 o) (G₂ := g '' Icc o 1) (Z := J)
      (isCompact_Icc.image hg.continuous).isClosed (isCompact_Icc.image hg.continuous).isClosed
      ?_ ?_
    · rintro u ⟨a, ha, hau⟩ ⟨b, hb, hbu⟩
      have hab : a = b := hg.injective (hau.trans hbu.symm)
      subst hab
      have hao : a = o := le_antisymm ha.2 hb.1
      subst hao
      exact hoC (hXKu ▸ Or.inr (hkr ▸ hau ▸ mem_range_self u))
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨Z, hZ, hZK⟩ := hx
      obtain ⟨hso, hot, -, hZa, hZJ⟩ := hGood _ _ _ hZ
      have ha := hinv _ (hmemK x ⟨Z, hZ, hZK⟩).1
      have hb := hinv _ (hmemK x ⟨Z, hZ, hZK⟩).2
      simp only [hF]
      refine ⟨by rw [ha]; exact mem_image_of_mem _ ⟨nonneg', hso⟩,
        by rw [hb]; exact mem_image_of_mem _ ⟨hot, le_one'⟩,
        by rw [ha]; exact hgJ (mem_range_self _), by rw [hb]; exact hgJ (mem_range_self _), ?_⟩
      intro u hu1 hu2 huJ
      have hZeq : Z = k '' uIcc (Function.invFun k (g x.1)) (Function.invFun k (g x.2)) := by
        refine eq_image_uIcc_of_isArc_subset h1 h4 hk (hkr ▸ hZK) ?_
        rw [ha, hb]; exact (isArc_iff_tarc h1 h3 h4 h51).mpr hZa
      have hu : u ∈ uIcc (Function.invFun k (g x.1)) (Function.invFun k (g x.2)) :=
        ⟨hu1.le, hu2.le⟩
      refine hZJ (k u) ⟨hZeq ▸ mem_image_of_mem _ hu, ?_⟩ huJ
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      have hne : ∀ {a b : unitInterval}, min a b < u → u < max a b → u ≠ a ∧ u ≠ b := by
        intro a b h₁ h₂
        rcases le_total a b with h | h
        · rw [min_eq_left h] at h₁; rw [max_eq_right h] at h₂
          exact ⟨h₁.ne', h₂.ne⟩
        · rw [min_eq_right h] at h₁; rw [max_eq_left h] at h₂
          exact ⟨h₂.ne, h₁.ne'⟩
      obtain ⟨hua, hub⟩ := hne hu1 hu2
      exact ⟨fun e => hua (hk.injective (e.trans ha.symm)),
        fun e => hub (hk.injective (e.trans hb.symm))⟩
  have hfinK : ChK.Finite := Finite.of_finite_image hfinF hinj
  have hfin : Ch.Finite := (hfinK.insert _).subset hsub
  obtain ⟨x, hxCh, hxmax⟩ := Set.exists_max_image Ch Prod.fst hfin ⟨(0, 1), X, hX⟩
  obtain ⟨y, ⟨hyCh, hy1⟩, hymin⟩ := Set.exists_min_image {y ∈ Ch | y.1 = x.1} Prod.snd
    (hfin.subset (sep_subset _ _)) ⟨x, hxCh, rfl⟩
  obtain ⟨Y, hY⟩ := hyCh
  refine ⟨y.1, y.2, Y, hY, fun s t Z hZ hps htq => ?_⟩
  have hs : s = y.1 := le_antisymm (hy1 ▸ hxmax (s, t) ⟨Z, hZ⟩) hps
  exact ⟨hs, le_antisymm htq (hymin (s, t) ⟨⟨Z, hZ⟩, hs.trans hy1⟩)⟩

end Chord

end HPC.Moore
