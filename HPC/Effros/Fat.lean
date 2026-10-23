import Mathlib

/-!
# Batch 134, §A: meager and fat sets (van Mill 2004, §2)

`NowhereMeagre`, `IsFat`, Lemma 2.1 (`IsFat.diff_meagre`) and Proposition 2.2
(`inter_nonempty_of_isFat`). Proposition 2.2 is proved in a relative form
(`inter_nonempty_of_nowhereMeagre`): two analytic nowhere meager sets `S, T` with `S` nonempty
and `S ⊆ closure T` meet. This is the form used inside the open set `E` of Proposition 3.5, and it
avoids subspaces altogether: "meager" always means meager in the ambient space.
-/

namespace HPC.Effros

open Set Topology Filter Metric MeasureTheory

section MeagerFat

variable {X : Type*} [TopologicalSpace X]

/-- `A` is **nowhere meager** in `X`: no nonempty relatively open subset of `A` is meager in
`X`. -/
def NowhereMeagre (A : Set X) : Prop :=
  ∀ V : Set X, IsOpen V → (V ∩ A).Nonempty → ¬ IsMeagre (V ∩ A)

/-- `A` is **fat** in `X`: dense and nowhere meager. Every superset of a fat set is fat. -/
def IsFat (A : Set X) : Prop := Dense A ∧ NowhereMeagre A

theorem IsFat.mono {A B : Set X} (hA : IsFat A) (hAB : A ⊆ B) : IsFat B := by
  refine ⟨hA.1.mono hAB, fun V hV hne hm => ?_⟩
  obtain ⟨y, hyV, -⟩ := hne
  have h1 : (V ∩ A).Nonempty := hA.1.inter_open_nonempty V hV ⟨y, hyV⟩
  exact hA.2 V hV h1 (hm.mono (inter_subset_inter_right _ hAB))

/-- A nowhere meager set minus a meager set is nowhere meager. -/
theorem NowhereMeagre.diff_meagre {S A : Set X} (hS : NowhereMeagre S) (hA : IsMeagre A) :
    NowhereMeagre (S \ A) := by
  intro V hV hne hm
  have hne' : (V ∩ S).Nonempty := hne.mono (inter_subset_inter_right _ diff_subset)
  refine hS V hV hne' ?_
  have : V ∩ S ⊆ (V ∩ (S \ A)) ∪ A := by
    rintro z ⟨hzV, hzS⟩
    by_cases hzA : z ∈ A
    · exact Or.inr hzA
    · exact Or.inl ⟨hzV, hzS, hzA⟩
  exact (hm.union hA).mono this

/-- If `S` is nowhere meager, `A` meager and `V` open with `(V ∩ S).Nonempty`, then
`V ∩ (S \ A)` is nonempty. -/
theorem NowhereMeagre.inter_diff_nonempty {S A V : Set X} (hS : NowhereMeagre S)
    (hA : IsMeagre A) (hV : IsOpen V) (hne : (V ∩ S).Nonempty) : (V ∩ (S \ A)).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  refine hS V hV hne (hA.mono ?_)
  rintro z ⟨hzV, hzS⟩
  by_contra hzA
  exact (h ▸ (⟨hzV, hzS, hzA⟩ : z ∈ V ∩ (S \ A)) : z ∈ (∅ : Set X))

/-- **van Mill, Lemma 2.1.** A fat set minus a meager set is fat. -/
theorem IsFat.diff_meagre {S A : Set X} (hS : IsFat S) (hA : IsMeagre A) : IsFat (S \ A) := by
  refine ⟨?_, hS.2.diff_meagre hA⟩
  rw [dense_iff_inter_open]
  intro V hV hVne
  exact hS.2.inter_diff_nonempty hA hV (hS.1.inter_open_nonempty V hV hVne)

/-- A subset that is not meager is not nowhere dense: its closure has nonempty interior. -/
theorem nonempty_interior_closure_of_not_meagre {A : Set X} (hA : ¬ IsMeagre A) :
    (interior (closure A)).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  exact hA (IsNowhereDense.isMeagre h)

end MeagerFat

/-! ### The nested construction of Proposition 2.2 -/

section Core

variable {P Q Y : Type*} [MetricSpace P] [CompleteSpace P] [MetricSpace Q] [CompleteSpace Q]
  [MetricSpace Y] {α : P → Y} {β : Q → Y}

omit [MetricSpace P] [CompleteSpace P] [MetricSpace Q] [CompleteSpace Q] [MetricSpace Y] in
theorem diam_closure_tendsto {Z : Type*} [MetricSpace Z] (A : ℕ → Set Z)
    (hA : ∀ n, ∃ c, A (n + 1) ⊆ ball c ((1 / 2) ^ n)) :
    Tendsto (fun n => diam (closure (A (n + 1)))) atTop (𝓝 0) := by
  have hle : ∀ n, diam (closure (A (n + 1))) ≤ 2 * (1 / 2) ^ n := by
    intro n
    obtain ⟨c, hc⟩ := hA n
    rw [diam_closure]
    exact (diam_mono hc isBounded_ball).trans (diam_ball (by positivity))
  refine squeeze_zero (fun n => diam_nonneg) hle ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)).const_mul 2

omit [MetricSpace P] [CompleteSpace P] [MetricSpace Q] [CompleteSpace Q] [MetricSpace Y] in
/-- Nested nonempty sets with radii `2⁻ⁿ` in a complete space: a common point of the closures. -/
theorem exists_mem_closure_nested {Z : Type*} [MetricSpace Z] [CompleteSpace Z] (A : ℕ → Set Z)
    (hAa : Antitone A) (hne : ∀ n, (A n).Nonempty)
    (hA : ∀ n, ∃ c, A (n + 1) ⊆ ball c ((1 / 2) ^ n)) : ∃ z, ∀ n, z ∈ closure (A n) := by
  obtain ⟨z, hz⟩ := Metric.nonempty_iInter_of_nonempty_biInter
    (s := fun n => closure (A (n + 1)))
    (fun n => isClosed_closure) (fun n => by
      obtain ⟨c, hc⟩ := hA n
      exact (isBounded_ball.subset hc).closure) (fun N => by
      obtain ⟨z, hz⟩ := hne (N + 1)
      exact ⟨z, mem_iInter₂.2 fun n hn => subset_closure (hAa (by omega) hz)⟩)
    (diam_closure_tendsto A hA)
  exact ⟨z, fun n => closure_mono (hAa (Nat.le_succ n)) (mem_iInter.1 hz n)⟩

/-- The inductive invariant of Proposition 2.2 (invariant (3) in the commission's
reconstruction): `β(V) ⊆ W` and `α(U) ⊆ closure β(V)`, all three open and `U` nonempty. -/
def CoreGood (α : P → Y) (β : Q → Y) (s : Set P × Set Q × Set Y) : Prop :=
  IsOpen s.1 ∧ IsOpen s.2.1 ∧ IsOpen s.2.2 ∧ s.1.Nonempty ∧
    β '' s.2.1 ⊆ s.2.2 ∧ α '' s.1 ⊆ closure (β '' s.2.1)

omit [CompleteSpace P] [CompleteSpace Q] in
/-- One step of the construction of Proposition 2.2 (steps 1–5 of the commission, §3.1). -/
theorem coreGood_step (hα : Continuous α) (hβ : Continuous β)
    (hαo : ∀ U : Set P, IsOpen U → U.Nonempty → (interior (closure (α '' U))).Nonempty)
    (hβo : ∀ V : Set Q, IsOpen V → V.Nonempty → (interior (closure (β '' V))).Nonempty)
    {s : Set P × Set Q × Set Y} (hs : CoreGood α β s) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Set P × Set Q × Set Y, CoreGood α β t ∧ t.1 ⊆ s.1 ∧ t.2.1 ⊆ s.2.1 ∧ t.2.2 ⊆ s.2.2 ∧
      (∃ p, t.1 ⊆ ball p ε) ∧ (∃ q, t.2.1 ⊆ ball q ε) ∧ (∃ y, t.2.2 ⊆ ball y ε) := by
  obtain ⟨U, V, W⟩ := s
  obtain ⟨hU, hV, hW, hUne, hVW, hUV⟩ := hs
  simp only at hU hV hW hUne hVW hUV
  -- Step 1–2: a small open `W'` inside `closure α(U)` and inside `W`.
  set O := interior (closure (α '' U)) with hO
  have hOne := hαo U hU hUne
  have hOW : O ⊆ closure W :=
    interior_subset.trans (closure_minimal (hUV.trans (closure_mono hVW)) isClosed_closure)
  obtain ⟨y, hyO, hyW⟩ : (O ∩ W).Nonempty := by
    obtain ⟨o, ho⟩ := hOne
    have := hOW ho
    rw [_root_.mem_closure_iff] at this
    obtain ⟨w, hwO, hwW⟩ := this O isOpen_interior ho
    exact ⟨w, hwO, hwW⟩
  set W' := O ∩ W ∩ ball y ε with hW'
  have hW'o : IsOpen W' := (isOpen_interior.inter hW).inter isOpen_ball
  have hW'clα : W' ⊆ closure (α '' U) := fun z hz => interior_subset hz.1.1
  -- Step 3: a small open `F ⊆ V` with `β(F) ⊆ W'`.
  have hW'clβ : W' ⊆ closure (β '' V) := hW'clα.trans
    (closure_minimal hUV isClosed_closure)
  obtain ⟨q, hqV, hqW'⟩ : ∃ q ∈ V, β q ∈ W' := by
    have hy : y ∈ W' := ⟨⟨hyO, hyW⟩, mem_ball_self hε⟩
    have := hW'clβ hy
    rw [_root_.mem_closure_iff] at this
    obtain ⟨b, hbW', q, hqV, rfl⟩ := this W' hW'o hy
    exact ⟨q, hqV, hbW'⟩
  set F := V ∩ β ⁻¹' W' ∩ ball q ε with hF
  have hFo : IsOpen F := (hV.inter (hW'o.preimage hβ)).inter isOpen_ball
  have hFne : F.Nonempty := ⟨q, ⟨hqV, hqW'⟩, mem_ball_self hε⟩
  have hFW' : β '' F ⊆ W' := by rintro _ ⟨r, hr, rfl⟩; exact hr.1.2
  -- Step 4: a small open `E ⊆ U` with `α(E) ⊆ interior (closure β(F))`.
  set O' := interior (closure (β '' F)) with hO'
  have hO'ne := hβo F hFo hFne
  have hO'clα : O' ⊆ closure (α '' U) := interior_subset.trans
    (closure_minimal (hFW'.trans hW'clα) isClosed_closure)
  obtain ⟨p, hpU, hpO'⟩ : ∃ p ∈ U, α p ∈ O' := by
    obtain ⟨o, ho⟩ := hO'ne
    have := hO'clα ho
    rw [_root_.mem_closure_iff] at this
    obtain ⟨a, haO', p, hpU, rfl⟩ := this O' isOpen_interior ho
    exact ⟨p, hpU, haO'⟩
  set E := U ∩ α ⁻¹' O' ∩ ball p ε with hE
  have hEo : IsOpen E := (hU.inter (isOpen_interior.preimage hα)).inter isOpen_ball
  have hEne : E.Nonempty := ⟨p, ⟨hpU, hpO'⟩, mem_ball_self hε⟩
  refine ⟨(E, F, W'), ⟨hEo, hFo, hW'o, hEne, hFW', ?_⟩, fun z hz => hz.1.1, fun z hz => hz.1.1,
    fun z hz => hz.1.2, ⟨p, fun z hz => hz.2⟩, ⟨q, fun z hz => hz.2⟩, ⟨y, fun z hz => hz.2⟩⟩
  rintro _ ⟨r, hr, rfl⟩
  exact interior_subset hr.1.2

omit [MetricSpace P] [CompleteSpace P] [MetricSpace Q] [CompleteSpace Q] [MetricSpace Y] in
/-- Dependent choice in the form used here: a sequence of good states, each step related to the
next. -/
theorem exists_seq_of_step {σ : Type*} {G : σ → Prop} {R : ℕ → σ → σ → Prop} {s₀ : σ}
    (h₀ : G s₀) (h : ∀ n s, G s → ∃ t, G t ∧ R n s t) :
    ∃ f : ℕ → σ, f 0 = s₀ ∧ ∀ n, G (f n) ∧ R n (f n) (f (n + 1)) := by
  choose next hnextG hnextR using h
  let g : ℕ → {s // G s} := fun n =>
    Nat.rec ⟨s₀, h₀⟩ (fun n s => ⟨next n s.1 s.2, hnextG n s.1 s.2⟩) n
  exact ⟨fun n => (g n).1, rfl, fun n => ⟨(g n).2, hnextR n (g n).1 (g n).2⟩⟩

/-- **The nested construction of Proposition 2.2.** `P`, `Q` complete metric spaces, `α`, `β`
continuous, the image of every nonempty open set has a closure with nonempty interior, `P`
nonempty and `range α ⊆ closure (range β)`. Then `α p = β q` for some `p`, `q`. -/
theorem exists_eq_of_core (hα : Continuous α) (hβ : Continuous β)
    (hαo : ∀ U : Set P, IsOpen U → U.Nonempty → (interior (closure (α '' U))).Nonempty)
    (hβo : ∀ V : Set Q, IsOpen V → V.Nonempty → (interior (closure (β '' V))).Nonempty)
    [Nonempty P] (hd : range α ⊆ closure (range β)) : ∃ p q, α p = β q := by
  have h0 : CoreGood α β (univ, univ, univ) :=
    ⟨isOpen_univ, isOpen_univ, isOpen_univ, univ_nonempty, subset_univ _,
      by simpa [image_univ] using hd⟩
  obtain ⟨f, -, hf⟩ := exists_seq_of_step (G := CoreGood α β)
    (R := fun n s t => t.1 ⊆ s.1 ∧ t.2.1 ⊆ s.2.1 ∧ t.2.2 ⊆ s.2.2 ∧
      (∃ p, t.1 ⊆ ball p ((1 / 2) ^ n)) ∧ (∃ q, t.2.1 ⊆ ball q ((1 / 2) ^ n)) ∧
      (∃ y, t.2.2 ⊆ ball y ((1 / 2) ^ n))) h0
    (fun n s hs => coreGood_step hα hβ hαo hβo hs (by positivity))
  have hUne : ∀ n, (f n).1.Nonempty := fun n => (hf n).1.2.2.2.1
  have hVne : ∀ n, (f n).2.1.Nonempty := fun n => by
    obtain ⟨p, hp⟩ := hUne n
    have h1 := (hf n).1.2.2.2.2.2 (mem_image_of_mem α hp)
    obtain ⟨b, -, q, hq, -⟩ := _root_.mem_closure_iff.1 h1 univ isOpen_univ trivial
    exact ⟨q, hq⟩
  obtain ⟨p, hp⟩ := exists_mem_closure_nested (fun n => (f n).1)
    (antitone_nat_of_succ_le fun n => (hf n).2.1) hUne fun n => (hf n).2.2.2.2.1
  obtain ⟨q, hq⟩ := exists_mem_closure_nested (fun n => (f n).2.1)
    (antitone_nat_of_succ_le fun n => (hf n).2.2.1) hVne fun n => (hf n).2.2.2.2.2.1
  refine ⟨p, q, ?_⟩
  -- `α p` and `β q` both lie in `closure (W n)` for every `n`
  have hpW : ∀ n, α p ∈ closure (f n).2.2 := fun n => by
    have h1 : α p ∈ closure (α '' (f n).1) :=
      map_mem_closure hα (hp n) fun z hz => mem_image_of_mem α hz
    have h2 : closure (α '' (f n).1) ⊆ closure (f n).2.2 :=
      closure_minimal ((hf n).1.2.2.2.2.2.trans (closure_mono (hf n).1.2.2.2.2.1))
        isClosed_closure
    exact h2 h1
  have hqW : ∀ n, β q ∈ closure (f n).2.2 := fun n =>
    map_mem_closure hβ (hq n) fun z hz => (hf n).1.2.2.2.2.1 (mem_image_of_mem β hz)
  have hWd := diam_closure_tendsto (fun n => (f n).2.2) fun n => (hf n).2.2.2.2.2.2
  have hdist : ∀ n, dist (α p) (β q) ≤ diam (closure (f (n + 1)).2.2) := fun n => by
    obtain ⟨c, hc⟩ := (hf n).2.2.2.2.2.2
    exact dist_le_diam_of_mem (isBounded_ball.subset hc).closure (hpW _) (hqW _)
  have : dist (α p) (β q) ≤ 0 := ge_of_tendsto' hWd hdist
  exact dist_le_zero.1 this

end Core

/-! ### Proposition 2.2 -/

section Prop22

/-- **The reduction of Proposition 2.2.** Let `f : (ℕ → ℕ) → Y` be any map (continuity is not needed here). Remove from
`ℕ → ℕ` the union `O` of all open sets whose image is meager. Then `f(O)` is meager (Lindelöf),
the rest `P = Oᶜ` is closed, hence Polish, and the image of every nonempty relatively open subset
of `P` is not meager. -/
theorem exists_reduced_param {Y : Type*} [TopologicalSpace Y] (f : (ℕ → ℕ) → Y) :
    ∃ C : Set (ℕ → ℕ), IsClosed C ∧ IsMeagre (range f \ f '' C) ∧
      ∀ U : Set C, IsOpen U → U.Nonempty → ¬ IsMeagre ((f ∘ Subtype.val) '' U) := by
  set 𝒰 : Set (Set (ℕ → ℕ)) := {U | IsOpen U ∧ IsMeagre (f '' U)} with h𝒰
  obtain ⟨T, hTc, hT𝒰, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable 𝒰 fun U hU => hU.1
  set O := ⋃₀ 𝒰 with hO
  have hOm : IsMeagre (f '' O) := by
    rw [← hTU, sUnion_eq_biUnion, image_iUnion₂]
    exact isMeagre_biUnion hTc fun U hU => (hT𝒰 hU).2
  have hOo : IsOpen O := isOpen_sUnion fun U hU => hU.1
  refine ⟨Oᶜ, hOo.isClosed_compl, hOm.mono ?_, ?_⟩
  · rintro _ ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_, rfl⟩
    by_contra hxO
    exact hx ⟨x, hxO, rfl⟩
  · intro U hU hne hm
    obtain ⟨U', hU'o, rfl⟩ := isOpen_induced_iff.1 hU
    have hsub : f '' U' ⊆ (f ∘ Subtype.val) '' (Subtype.val ⁻¹' U' : Set (Oᶜ : Set _)) ∪
        f '' O := by
      rintro _ ⟨x, hx, rfl⟩
      by_cases hxO : x ∈ O
      · exact Or.inr ⟨x, hxO, rfl⟩
      · exact Or.inl ⟨⟨x, hxO⟩, hx, rfl⟩
    have hU'𝒰 : U' ∈ 𝒰 := ⟨hU'o, (hm.union hOm).mono hsub⟩
    obtain ⟨⟨x, hxO⟩, hx⟩ := hne
    exact hxO (subset_sUnion_of_mem hU'𝒰 hx)

/-- Closure of a nowhere meager set is unchanged by removing a meager set. -/
theorem NowhereMeagre.closure_subset_closure_diff {Y : Type*} [TopologicalSpace Y] {T M : Set Y}
    (hT : NowhereMeagre T) (hM : IsMeagre M) : closure T ⊆ closure (T \ M) := by
  intro y hy
  rw [_root_.mem_closure_iff] at hy ⊢
  intro o ho hyo
  exact hT.inter_diff_nonempty hM ho (hy o ho hyo)

/-- **van Mill, Proposition 2.2, relative form.** Two analytic nowhere meager subsets `S`, `T`
of a metric space, `S` nonempty and `S ⊆ closure T`, meet. -/
theorem inter_nonempty_of_nowhereMeagre {Y : Type*} [MetricSpace Y] {S T : Set Y}
    (hSa : AnalyticSet S) (hTa : AnalyticSet T) (hS : NowhereMeagre S) (hT : NowhereMeagre T)
    (hSne : S.Nonempty) (hST : S ⊆ closure T) : (S ∩ T).Nonempty := by
  rw [AnalyticSet_def] at hSa hTa
  rcases hSa with rfl | ⟨f, hf, rfl⟩
  · exact absurd hSne (by simp)
  rcases hTa with rfl | ⟨g, hg, rfl⟩
  · obtain ⟨y, hy⟩ := hSne
    simpa using hST hy
  obtain ⟨C, hCc, hCm, hCo⟩ := exists_reduced_param f
  obtain ⟨D, hDc, hDm, hDo⟩ := exists_reduced_param g
  haveI : PolishSpace C := hCc.polishSpace
  haveI : PolishSpace D := hDc.polishSpace
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable C
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable D
  have hSnm : ¬ IsMeagre (range f) := by
    have := hS univ isOpen_univ (by simpa using hSne)
    simpa using this
  haveI : Nonempty C := by
    by_contra h
    rw [not_nonempty_iff] at h
    apply hSnm
    refine hCm.mono ?_
    intro y hy
    refine ⟨hy, ?_⟩
    rintro ⟨x, hx, -⟩
    exact h.false (⟨x, hx⟩ : C)
  have hfC : Continuous (f ∘ Subtype.val : C → Y) := hf.comp continuous_subtype_val
  have hgD : Continuous (g ∘ Subtype.val : D → Y) := hg.comp continuous_subtype_val
  obtain ⟨p, q, hpq⟩ := exists_eq_of_core hfC hgD
    (fun U hU hne => nonempty_interior_closure_of_not_meagre (hCo U hU hne))
    (fun V hV hne => nonempty_interior_closure_of_not_meagre (hDo V hV hne)) (by
      rintro _ ⟨x, rfl⟩
      have h1 := hST ⟨x.1, rfl⟩
      have h2 := hT.closure_subset_closure_diff hDm h1
      refine closure_mono ?_ h2
      rintro z ⟨hz1, hz2⟩
      have : z ∈ g '' D := by
        by_contra h
        exact hz2 ⟨hz1, h⟩
      obtain ⟨w, hw, rfl⟩ := this
      exact ⟨⟨w, hw⟩, rfl⟩)
  exact ⟨f p, ⟨p.1, rfl⟩, ⟨q.1, hpq.symm⟩⟩

/-- **van Mill, Proposition 2.2.** Two analytic fat subsets of a nonempty metric space meet. -/
theorem inter_nonempty_of_isFat {Y : Type*} [MetricSpace Y] [Nonempty Y] {S T : Set Y}
    (hSa : AnalyticSet S) (hTa : AnalyticSet T) (hS : IsFat S) (hT : IsFat T) :
    (S ∩ T).Nonempty :=
  inter_nonempty_of_nowhereMeagre hSa hTa hS.2 hT.2 hS.1.nonempty
    (by rw [hT.1.closure_eq]; exact subset_univ _)

/-- **`Nonempty Y` cannot be dropped from Proposition 2.2** (refutation candidate of the
commission). In an empty space, `∅` is analytic and fat, and `∅ ∩ ∅` is empty. Van Mill's
statement tacitly assumes `X ≠ ∅`. -/
theorem isFat_empty_of_isEmpty {Y : Type*} [TopologicalSpace Y] [IsEmpty Y] :
    AnalyticSet (∅ : Set Y) ∧ IsFat (∅ : Set Y) ∧ ¬ ((∅ : Set Y) ∩ ∅).Nonempty :=
  ⟨analyticSet_empty, ⟨fun y => isEmptyElim y, fun _ _ h => by simp at h⟩, by simp⟩

end Prop22

end HPC.Effros
