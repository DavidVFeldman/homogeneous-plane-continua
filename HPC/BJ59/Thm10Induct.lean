import HPC.BJ59.Thm10Defs
import HPC.BJ59.Thm8Cor

/-!
# Batch 201, §5: Theorem 10 from the step lemma

The skeleton's `BJStep` (statement verbatim) and `bjThm10_of_step`: alternate the step, starting
from one-link chains, and feed the sequences to `zigzag_homeomorph` and `zigzag_fibre`.
Route: commission 201 §5.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

/-- **One step of Bing–Jones's induction** (Steps 2, 3, 4, ⋯ of the proof of Theorem 10): from a
chain map `H` of `D` (on `X`) onto `E` (on `Y`) with Conditions A and C, a fine chain `E′` on `Y`
and a chain map `K` of `E′` onto `D` with Conditions A′, B′ and C′. Applied with `X` and `Y`
exchanged it gives Conditions A, B and C. -/
def BJStep : Prop :=
  ∀ (X Y : Type) [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y]
    (f : X → unitInterval) (g : Y → unitInterval), IsContArcPA f → IsContArcPA g →
    IsSnakeLike (univ : Set X) → IsSnakeLike (univ : Set Y) →
    ∀ (h₀ : f ⁻¹' {0} ≃ₜ g ⁻¹' {0}) (h₁ : f ⁻¹' {1} ≃ₜ g ⁻¹' {1}) (n m : ℕ) (D : Chain X n)
      (E : Chain Y m) (H : Fin n → Fin m), univ ⊆ D.union → univ ⊆ E.union →
      HasPrivatePoints D → IsFibreFine g E → IsFibreChainMap f g D E H →
      EndCompat f g h₀ h₁ D E H → ∀ δ : ℝ, 0 < δ →
      ∃ (N : ℕ) (E' : Chain Y N) (K : Fin N → Fin n), univ ⊆ E'.union ∧ IsBJChain E' ∧
        IsEpsChain E' δ ∧ HasPrivatePoints E' ∧ IsFibreChainMap g f E' D K ∧
        EndCompat g f h₀.symm h₁.symm E' D K ∧ ∀ k, E'.link k ⊆ E.link (H (K k))

section Induction

variable {X Y : Type} [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y]

theorem IsEpsChain.mono' {Z : Type*} [MetricSpace Z] {n : ℕ} {D : Chain Z n} {ε ε' : ℝ}
    (hD : IsEpsChain D ε) (h : ε ≤ ε') : IsEpsChain D ε' :=
  fun i => ⟨(hD i).1, lt_of_lt_of_le (hD i).2 h⟩

/-- A stage of the induction: chains `D` on `X`, `E` on `Y`, and a chain map `H` of `D` onto
`E`. -/
structure BJStage (X Y : Type) [MetricSpace X] [MetricSpace Y] where
  n : ℕ
  m : ℕ
  D : Chain X n
  E : Chain Y m
  H : Fin n → Fin m

/-- The properties carried by a stage (commission 201 §5), with mesh `< ε`. -/
def BJStage.Good (f : X → unitInterval) (g : Y → unitInterval) (h₀ : f ⁻¹' {0} ≃ₜ g ⁻¹' {0})
    (h₁ : f ⁻¹' {1} ≃ₜ g ⁻¹' {1}) (s : BJStage X Y) (ε : ℝ) : Prop :=
  univ ⊆ s.D.union ∧ univ ⊆ s.E.union ∧ IsBJChain s.D ∧ IsBJChain s.E ∧
    HasPrivatePoints s.D ∧ HasPrivatePoints s.E ∧ IsFibreFine f s.D ∧ IsFibreFine g s.E ∧
    IsFibreChainMap f g s.D s.E s.H ∧ EndCompat f g h₀ h₁ s.D s.E s.H ∧
    IsEpsChain s.D ε ∧ IsEpsChain s.E ε

/-- From one stage to the next: two applications of the step lemma. -/
theorem BJStage.exists_next (hs : BJStep) {f : X → unitInterval} {g : Y → unitInterval}
    (hf : IsContArcPA f) (hg : IsContArcPA g) (hSX : IsSnakeLike (univ : Set X))
    (hSY : IsSnakeLike (univ : Set Y)) {h₀ : f ⁻¹' {0} ≃ₜ g ⁻¹' {0}}
    {h₁ : f ⁻¹' {1} ≃ₜ g ⁻¹' {1}} {κX κY : ℝ}
    (hκX : ∀ t, ∃ p ∈ f ⁻¹' {t}, ∃ q ∈ f ⁻¹' {t}, κX ≤ dist p q)
    (hκY : ∀ t, ∃ p ∈ g ⁻¹' {t}, ∃ q ∈ g ⁻¹' {t}, κY ≤ dist p q)
    {s : BJStage X Y} {ε : ℝ} (hgood : s.Good f g h₀ h₁ ε) {δ : ℝ} (hδ : 0 < δ)
    (hδX : δ ≤ κX / 3) (hδY : δ ≤ κY / 3) :
    ∃ (s' : BJStage X Y) (K : Fin s'.m → Fin s.n), s'.Good f g h₀ h₁ δ ∧ IsChainMap K ∧
      (∀ j, s'.D.link j ⊆ s.D.link (K (s'.H j))) ∧
      (∀ k, s'.E.link k ⊆ s.E.link (s.H (K k))) := by
  obtain ⟨hDc, hEc, -, -, hDp, -, hDf, hEf, hA, hC, -, -⟩ := hgood
  obtain ⟨N, E', K, hE'c, hE'bj, hE'ε, hE'p, hK, hKC, hB'⟩ :=
    hs X Y f g hf hg hSX hSY h₀ h₁ s.n s.m s.D s.E s.H hDc hEc hDp hEf hA hC δ hδ
  have hE'f : IsFibreFine g E' := isFibreFine_of_isEpsChain hκY E' (IsEpsChain.mono' hE'ε hδY)
  obtain ⟨N', D', H', hD'c, hD'bj, hD'ε, hD'p, hH', hH'C, hB⟩ :=
    hs Y X g f hg hf hSY hSX h₀.symm h₁.symm N s.n E' s.D K hE'c hDc hE'p hDf hK hKC δ hδ
  have hD'f : IsFibreFine f D' := isFibreFine_of_isEpsChain hκX D' (IsEpsChain.mono' hD'ε hδX)
  rw [Homeomorph.symm_symm, Homeomorph.symm_symm] at hH'C
  refine ⟨⟨N', N, D', E', H'⟩, K, ⟨hD'c, hE'c, hD'bj, hE'bj, hD'p, hE'p, hD'f, hE'f, hH', hH'C,
    hD'ε, hE'ε⟩, hK.1, hB, hB'⟩

/-- The initial stage: one-link chains. -/
theorem BJStage.exists_init {f : X → unitInterval} {g : Y → unitInterval}
    (hf : IsContArcPA f) (hg : IsContArcPA g) (h₀ : f ⁻¹' {0} ≃ₜ g ⁻¹' {0})
    (h₁ : f ⁻¹' {1} ≃ₜ g ⁻¹' {1}) :
    ∃ (s : BJStage X Y) (ε : ℝ), s.Good f g h₀ h₁ ε := by
  haveI : Nonempty X := ⟨(hf.2.2.1 0).choose⟩
  haveI : Nonempty Y := ⟨(hg.2.2.1 0).choose⟩
  refine ⟨⟨1, 1, oneLinkChain X, oneLinkChain Y, id⟩, Metric.diam (univ : Set X) +
    Metric.diam (univ : Set Y) + 1, ?_⟩
  have hX0 : (0 : ℝ) ≤ Metric.diam (univ : Set X) := Metric.diam_nonneg
  have hY0 : (0 : ℝ) ≤ Metric.diam (univ : Set Y) := Metric.diam_nonneg
  have hcovX : univ ⊆ (oneLinkChain X).union := fun x _ => mem_iUnion.2 ⟨0, mem_univ x⟩
  have hcovY : univ ⊆ (oneLinkChain Y).union := fun x _ => mem_iUnion.2 ⟨0, mem_univ x⟩
  have hbj : ∀ (Z : Type) [MetricSpace Z] [Nonempty Z], IsBJChain (oneLinkChain Z) := by
    intro Z _ _ i j hij
    have : i = j := Subsingleton.elim _ _
    subst this
    simp at hij
  have hpriv : ∀ (Z : Type) [MetricSpace Z] [Nonempty Z], HasPrivatePoints (oneLinkChain Z) := by
    intro Z _ _ j
    obtain ⟨z⟩ := ‹Nonempty Z›
    exact ⟨z, mem_univ z, fun j' hj' => absurd (Subsingleton.elim j' j) hj'⟩
  refine ⟨hcovX, hcovY, hbj X, hbj Y, hpriv X, hpriv Y, Or.inl rfl, Or.inl rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun i j _ => by simp [Subsingleton.elim i j], Function.surjective_id, ?_, ?_⟩
    · intro t j _
      obtain ⟨y, hy⟩ := hg.2.2.1 t
      exact ⟨y, mem_univ y, hy⟩
    · intro t u v _ hcov y _
      obtain ⟨x, hx⟩ := hf.2.2.1 t
      obtain ⟨j, hj, -⟩ := mem_iUnion₂.1 (hcov (show x ∈ f ⁻¹' {t} from hx))
      exact mem_iUnion₂.2 ⟨j, hj, mem_univ y⟩
  · exact ⟨fun _ _ _ => mem_univ _, fun _ _ _ => mem_univ _⟩
  · intro i
    refine ⟨isCompact_univ.isBounded, ?_⟩
    show Metric.diam (univ : Set X) < _
    linarith
  · intro i
    refine ⟨isCompact_univ.isBounded, ?_⟩
    show Metric.diam (univ : Set Y) < _
    linarith

end Induction

/-- **Theorem 10 from the step lemma**: alternate the step, starting from one-link chains, and
apply `zigzag_homeomorph` and `zigzag_fibre`. -/
theorem bjThm10_of_step (hs : BJStep) : BJThm10 := by
  intro X Y _ _ _ _ f g hf hg hSX hSY h₀ h₁
  classical
  obtain ⟨κX, hκX, hκXs⟩ := exists_fibre_spread hf.2.1 fun t => (hf.2.2.2 t).2.2
  obtain ⟨κY, hκY, hκYs⟩ := exists_fibre_spread hg.2.1 fun t => (hg.2.2.2 t).2.2
  obtain ⟨s₀, ε₀, hs₀⟩ := BJStage.exists_init hf hg h₀ h₁
  set δ : ℕ → ℝ := fun i => min (1 / 2 ^ (i + 1)) (min (κX / 3) (κY / 3)) with hδdef
  have hδpos : ∀ i, 0 < δ i := fun i => lt_min (by positivity) (lt_min (by linarith)
    (by linarith))
  set ε : ℕ → ℝ := fun i => Nat.casesOn i ε₀ fun i => δ i with hεdef
  have hnext : ∀ (i : ℕ) (s : {s : BJStage X Y // s.Good f g h₀ h₁ (ε i)}),
      ∃ (s' : BJStage X Y) (K : Fin s'.m → Fin s.1.n), s'.Good f g h₀ h₁ (ε (i + 1)) ∧
        IsChainMap K ∧ (∀ j, s'.D.link j ⊆ s.1.D.link (K (s'.H j))) ∧
        (∀ k, s'.E.link k ⊆ s.1.E.link (s.1.H (K k))) := fun i s =>
    BJStage.exists_next hs hf hg hSX hSY hκXs hκYs s.2 (hδpos i) ((min_le_right _ _).trans
      (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _))
  let S : ∀ i : ℕ, {s : BJStage X Y // s.Good f g h₀ h₁ (ε i)} := fun i =>
    Nat.rec (motive := fun i => {s : BJStage X Y // s.Good f g h₀ h₁ (ε i)}) ⟨s₀, hs₀⟩
      (fun i s => ⟨(hnext i s).choose, (hnext i s).choose_spec.choose_spec.1⟩) i
  have hSsucc : ∀ i, (S (i + 1)).1 = (hnext i (S i)).choose := fun i => rfl
  let K : ∀ i, Fin (S (i + 1)).1.m → Fin (S i).1.n := fun i => (hnext i (S i)).choose_spec.choose
  have hKspec : ∀ i, IsChainMap (K i) ∧
      (∀ j, (S (i + 1)).1.D.link j ⊆ (S i).1.D.link (K i ((S (i + 1)).1.H j))) ∧
      (∀ k, (S (i + 1)).1.E.link k ⊆ (S i).1.E.link ((S i).1.H (K i k))) := fun i =>
    (hnext i (S i)).choose_spec.choose_spec.2
  have hgood : ∀ i, (S i).1.Good f g h₀ h₁ (ε i) := fun i => (S i).2
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun i : ℕ => δ i) atTop (𝓝 0) := by
      have hg2 : Tendsto (fun i : ℕ => (1 : ℝ) / 2 ^ (i + 1)) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
          (by norm_num)).comp (tendsto_add_atTop_nat 1)
        refine this.congr fun i => ?_
        simp [Function.comp, one_div, inv_pow]
      refine squeeze_zero (fun i => (hδpos i).le) (fun i => min_le_left _ _) hg2
    rw [← tendsto_add_atTop_iff_nat 1]
    exact h1
  obtain ⟨h, hh⟩ := zigzag_homeomorph (P := (univ : Set X)) (Q := (univ : Set Y))
    isCompact_univ isCompact_univ (fun i => (S i).1.D) (fun i => (S i).1.E)
    (fun i => (hgood i).1) (fun i j => by simpa using ((S i).1.D.link_nonempty j))
    (fun i => (hgood i).2.1) (fun i j => by simpa using ((S i).1.E.link_nonempty j))
    (fun i => (hgood i).2.2.2.1) hεt (fun i => (hgood i).2.2.2.2.2.2.2.2.2.2.1)
    (fun i => (hgood i).2.2.2.2.2.2.2.2.2.2.2) (fun i => (S i).1.H) K
    (fun i => (hgood i).2.2.2.2.2.2.2.2.1.1) (fun i => (hgood i).2.2.2.2.2.2.2.2.1.2.1)
    (fun i => (hKspec i).1) (fun i => (hKspec i).2.1) (fun i => (hKspec i).2.2)
  have hfib := zigzag_fibre (P := (univ : Set X)) (Q := (univ : Set Y)) (fun i => (S i).1.D)
    (fun i => (S i).1.E) hεt (fun i => (hgood i).2.2.2.2.2.2.2.2.2.2.2) (fun i => (S i).1.H)
    f g (fun t => by simpa using (isClosed_singleton.preimage hg.1))
    (fun i j p _ hp => by
      obtain ⟨q, hq1, hq2⟩ := (hgood i).2.2.2.2.2.2.2.2.1.2.2.1 (f p) j ⟨p, hp, rfl⟩
      exact ⟨q, mem_univ q, hq1, hq2⟩) h hh
  let F : X ≃ₜ Y := ((Homeomorph.Set.univ X).symm.trans h).trans (Homeomorph.Set.univ Y)
  have hF : ∀ x, F x = (h ⟨x, mem_univ x⟩ : Y) := fun x => rfl
  refine ⟨F, fun x => by rw [hF]; exact hfib ⟨x, mem_univ x⟩, ?_, ?_⟩
  · intro x hx
    rw [hF]
    have := (hh ⟨x, mem_univ x⟩ ⟨(h₀ ⟨x, hx⟩ : Y), mem_univ _⟩).1 (fun i => by
      obtain ⟨j, hj⟩ := mem_iUnion.1 ((hgood i).1 (mem_univ x))
      exact subset_closure (mem_starImage.2
        ⟨j, hj, (hgood i).2.2.2.2.2.2.2.2.2.1.1 j ⟨x, hx⟩ hj⟩))
    exact (congrArg Subtype.val this).symm
  · intro x hx
    rw [hF]
    have := (hh ⟨x, mem_univ x⟩ ⟨(h₁ ⟨x, hx⟩ : Y), mem_univ _⟩).1 (fun i => by
      obtain ⟨j, hj⟩ := mem_iUnion.1 ((hgood i).1 (mem_univ x))
      exact subset_closure (mem_starImage.2
        ⟨j, hj, (hgood i).2.2.2.2.2.2.2.2.2.1.2 j ⟨x, hx⟩ hj⟩))
    exact (congrArg Subtype.val this).symm

end HPC.BJ59
