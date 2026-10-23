import HPC.Moore.M25Plane
import HPC.Plane.Tree7Arcs
import HPC.Jones.Jones49E

/-!
# Batch 155, item C: Moore's triod theorem, part A — the interlacing lemma

Moore's Theorem 76 (p. 220: two disjoint continua in a closed disc cannot both meet three disjoint
arcs of its boundary) in the form used here: if `x` and `y` are disjoint continua in `D ∪ J`, where
`D` is the inside of a closed curve `J`, then two points of `y` on `J` cannot *interlace* with two
points of `x` on `J`.

* `interlace`: the separation argument, from Janiszewski's theorem only (no cross-cut is built).
  `J = α ∪ β` with `α ∩ β ⊆ x`, a point `y₁ ∈ y ∩ (α \ β)` and a point `y₂ ∈ y ∩ (β \ α)`: with
  `F₁ = x ∪ α`, `F₂ = x ∪ β` (so `F₁ ∩ F₂ = x` is connected) and `Uᵢ` the component of `Fᵢᶜ`
  containing the outside `E`, Janiszewski gives `U₁ ∩ U₂ ∩ (D \ x) = ∅`; `y₂ ∈ U₁ \ U₂`,
  `y₁ ∈ U₂ \ U₁`, and every point of `y` lies in `U₁ ∪ U₂` (a point of `D \ x` in neither lies in a
  component of `F₁ᶜ` whose frontier is inside `x`, which would then contain `y`). So `y` is not
  connected.
* `exists_loop_param`: a simple closed polygon is the image of `[0, 2]` under a continuous map
  injective on `[0, 2)` with equal ends (from `IsSimpleClosedPolygon.split_two'` and
  `tarc_of_isSimplePolyArc`).
* `interlace_param`: the interlacing lemma for parameters `s < u < t < v < 2`.
* `interlace_three`: Moore's Theorem 76 in parameter form: three pairwise separated parameter
  blocks, each containing a parameter of a point of `x` and one of a point of `y`, are impossible.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Moore.Gen

/-- A point of the closure of a connected set `E` missing the closed set `F`, itself off `F`, lies in
the component of `Fᶜ` containing `E`. -/
theorem mem_comp_of_mem_closure {F E : Set Pt} (hF : IsClosed F) {e t : Pt}
    (hE : IsPreconnected E) (heE : e ∈ E) (hEF : Disjoint E F) (ht : t ∈ closure E)
    (htF : t ∉ F) : t ∈ connectedComponentIn Fᶜ e := by
  have hEU : E ⊆ connectedComponentIn Fᶜ e :=
    hE.subset_connectedComponentIn heE hEF.subset_compl_right
  have ho : IsOpen (connectedComponentIn Fᶜ t) := hF.isOpen_compl.connectedComponentIn
  obtain ⟨e', he'O, he'E⟩ := mem_closure_iff.1 ht _ ho (mem_connectedComponentIn htF)
  have h1 : connectedComponentIn Fᶜ t = connectedComponentIn Fᶜ e' :=
    connectedComponentIn_eq he'O
  have h2 : connectedComponentIn Fᶜ e = connectedComponentIn Fᶜ e' :=
    connectedComponentIn_eq (hEU he'E)
  rw [h2, ← h1]; exact mem_connectedComponentIn htF

/-- A point of the frontier of a component of the complement of a closed set lies in that set. -/
theorem mem_of_mem_frontier_comp {F : Set Pt} (hF : IsClosed F) {w z : Pt}
    (hz : z ∈ frontier (connectedComponentIn Fᶜ w)) : z ∈ F := by
  by_contra hzF
  have hzO' : IsOpen (connectedComponentIn Fᶜ z) := hF.isOpen_compl.connectedComponentIn
  obtain ⟨v, hv1, hv2⟩ := mem_closure_iff.1 (frontier_subset_closure hz) _ hzO'
    (mem_connectedComponentIn hzF)
  have hO : IsOpen (connectedComponentIn Fᶜ w) := hF.isOpen_compl.connectedComponentIn
  have : z ∈ connectedComponentIn Fᶜ w := by
    rw [connectedComponentIn_eq hv2, ← connectedComponentIn_eq hv1]
    exact mem_connectedComponentIn hzF
  rw [hO.frontier_eq] at hz
  exact hz.2 this

/-- A preconnected set missing the frontier of an open set `O` and meeting `O` lies in `O`. -/
theorem subset_of_disjoint_frontier {y O : Set Pt} (hy : IsPreconnected y) (hO : IsOpen O)
    (hfr : Disjoint y (frontier O)) {w : Pt} (hwy : w ∈ y) (hwO : w ∈ O) : y ⊆ O := by
  have hsub : y ⊆ O ∪ (closure O)ᶜ := by
    intro z hz
    by_cases h : z ∈ O
    · exact Or.inl h
    · right; intro hc
      exact disjoint_left.1 hfr hz ⟨hc, by rw [hO.interior_eq]; exact h⟩
  exact hy.subset_left_of_subset_union hO isClosed_closure.isOpen_compl
    ((disjoint_compl_right : Disjoint (closure O) (closure O)ᶜ).mono_left subset_closure) hsub
    ⟨w, hwy, hwO⟩

/-- **The interlacing lemma** (Moore 1962, Theorem 76, p. 220, separation form). Let `J` be a closed
set whose complement is the union of the disjoint open sets `D` and `E`, `E` connected with
`J ⊆ closure E`. Let `x`, `y` be disjoint, `x` a continuum, `y` preconnected, both in `D ∪ J`. If
`J = α ∪ β` with `α`, `β` compact and `α ∩ β ⊆ x`, then `y` cannot meet both `α \ β` and `β \ α`. -/
theorem interlace {J D E x y α β : Set Pt} (hDo : IsOpen D) (hEo : IsOpen E)
    (hEc : IsConnected E) (hcov : Jᶜ = D ∪ E) (hDE : Disjoint D E) (hJE : J ⊆ closure E)
    (hx : IsCompact x) (hxc : IsConnected x) (hy : IsPreconnected y)
    (hxJ : x ⊆ D ∪ J) (hyJ : y ⊆ D ∪ J) (hxy : Disjoint x y)
    (hα : IsCompact α) (hβ : IsCompact β) (hαβ : α ∪ β = J) (hαβx : α ∩ β ⊆ x)
    {y₁ y₂ : Pt} (hy₁ : y₁ ∈ y) (hy₁α : y₁ ∈ α) (hy₁β : y₁ ∉ β)
    (hy₂ : y₂ ∈ y) (hy₂α : y₂ ∉ α) (hy₂β : y₂ ∈ β) : False := by
  obtain ⟨e, heE⟩ := hEc.nonempty
  have hEJ : Disjoint E J := by
    rw [disjoint_left]
    intro z hzE hzJ
    have : z ∈ Jᶜ := by rw [hcov]; exact Or.inr hzE
    exact this hzJ
  have hDJ : Disjoint D J := by
    rw [disjoint_left]
    intro z hzD hzJ
    have : z ∈ Jᶜ := by rw [hcov]; exact Or.inl hzD
    exact this hzJ
  have hαJ : α ⊆ J := hαβ ▸ subset_union_left
  have hβJ : β ⊆ J := hαβ ▸ subset_union_right
  have hEx : Disjoint E x := by
    rw [disjoint_left]
    intro z hzE hzx
    rcases hxJ hzx with h | h
    · exact disjoint_left.1 hDE h hzE
    · exact disjoint_left.1 hEJ hzE h
  have hyx : ∀ w ∈ y, w ∉ x := fun w hw hwx => disjoint_left.1 hxy hwx hw
  set F₁ := x ∪ α with hF₁def
  set F₂ := x ∪ β with hF₂def
  have hF₁ : IsCompact F₁ := hx.union hα
  have hF₂ : IsCompact F₂ := hx.union hβ
  have hEF₁ : Disjoint E F₁ := disjoint_union_right.2 ⟨hEx, hEJ.mono_right hαJ⟩
  have hEF₂ : Disjoint E F₂ := disjoint_union_right.2 ⟨hEx, hEJ.mono_right hβJ⟩
  set U₁ := connectedComponentIn F₁ᶜ e with hU₁def
  set U₂ := connectedComponentIn F₂ᶜ e with hU₂def
  have hU₁o : IsOpen U₁ := hF₁.isClosed.isOpen_compl.connectedComponentIn
  have hU₂o : IsOpen U₂ := hF₂.isClosed.isOpen_compl.connectedComponentIn
  have hU₁F : U₁ ⊆ F₁ᶜ := connectedComponentIn_subset _ _
  have hU₂F : U₂ ⊆ F₂ᶜ := connectedComponentIn_subset _ _
  have hJU₁ : ∀ t ∈ J, t ∉ F₁ → t ∈ U₁ := fun t ht htF =>
    mem_comp_of_mem_closure hF₁.isClosed hEc.isPreconnected heE hEF₁ (hJE ht) htF
  have hJU₂ : ∀ t ∈ J, t ∉ F₂ → t ∈ U₂ := fun t ht htF =>
    mem_comp_of_mem_closure hF₂.isClosed hEc.isPreconnected heE hEF₂ (hJE ht) htF
  have hinter : F₁ ∩ F₂ = x := by
    ext z; constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact h1
      · exact h1
      · exact h2
      · exact hαβx ⟨h1, h2⟩
    · intro hz; exact ⟨Or.inl hz, Or.inl hz⟩
  -- Janiszewski: no point of `D \ x` lies in both `U₁` and `U₂`
  have hjD : ∀ u ∈ D, u ∉ x → u ∈ U₁ → u ∈ U₂ → False := by
    intro u huD hux hu1 hu2
    have huJ : u ∉ J := disjoint_left.1 hDJ huD
    have hsep1 : ¬ SeparatesPts F₁ u e := by
      rintro ⟨-, -, h⟩
      apply h
      rw [← connectedComponentIn_eq hu1]
      exact mem_connectedComponentIn (disjoint_left.1 hEF₁ heE)
    have hsep2 : ¬ SeparatesPts F₂ u e := by
      rintro ⟨-, -, h⟩
      apply h
      rw [← connectedComponentIn_eq hu2]
      exact mem_connectedComponentIn (disjoint_left.1 hEF₂ heE)
    have huF : u ∉ F₁ ∪ F₂ := by
      rintro ((h | h) | (h | h))
      · exact hux h
      · exact huJ (hαJ h)
      · exact hux h
      · exact huJ (hβJ h)
    apply HPC.Moore.janiszewski_compact hF₁ hF₂ (Or.inl (hinter ▸ hxc)) hsep1 hsep2
    refine ⟨huF, fun h => ?_, fun h => ?_⟩
    · rcases h with (h | h) | (h | h)
      · exact disjoint_left.1 hEx heE h
      · exact disjoint_left.1 hEJ heE (hαJ h)
      · exact disjoint_left.1 hEx heE h
      · exact disjoint_left.1 hEJ heE (hβJ h)
    · set C := connectedComponentIn (F₁ ∪ F₂)ᶜ u
      have hCJ : C ⊆ D ∪ E := by
        intro z hz
        have hz' := connectedComponentIn_subset _ _ hz
        rw [← hcov]
        intro hzJ
        apply hz'
        rw [← hαβ] at hzJ
        rcases hzJ with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)
      have hCp : IsPreconnected C := isPreconnected_connectedComponentIn
      have hsub := hCp.subset_left_of_subset_union hDo hEo hDE hCJ
        ⟨u, mem_connectedComponentIn huF, huD⟩
      exact disjoint_left.1 hDE (hsub h) heE
  have hy1U1 : y₁ ∉ U₁ := fun h => hU₁F h (Or.inr hy₁α)
  have hy2U2 : y₂ ∉ U₂ := fun h => hU₂F h (Or.inr hy₂β)
  have hy2U1 : y₂ ∈ U₁ := hJU₁ y₂ (hβJ hy₂β) (by
    rintro (h | h)
    · exact hyx y₂ hy₂ h
    · exact hy₂α h)
  have hy1U2 : y₁ ∈ U₂ := hJU₂ y₁ (hαJ hy₁α) (by
    rintro (h | h)
    · exact hyx y₁ hy₁ h
    · exact hy₁β h)
  have hboth : ∀ w ∈ y, w ∈ U₁ → w ∈ U₂ → False := by
    intro w hw h1 h2
    rcases hyJ hw with hD | hJ
    · exact hjD w hD (hyx w hw) h1 h2
    · rw [← hαβ] at hJ
      rcases hJ with h | h
      · exact hU₁F h1 (Or.inr h)
      · exact hU₂F h2 (Or.inr h)
  have hcov' : ∀ w ∈ y, w ∈ U₁ ∨ w ∈ U₂ := by
    intro w hw
    have hwx := hyx w hw
    rcases hyJ hw with hD | hJ
    · by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2⟩ := hcon
      have hwF1 : w ∉ F₁ := by
        rintro (h | h)
        · exact hwx h
        · exact disjoint_left.1 hDJ hD (hαJ h)
      set O := connectedComponentIn F₁ᶜ w with hOdef
      have hOo : IsOpen O := hF₁.isClosed.isOpen_compl.connectedComponentIn
      have hOF : O ⊆ F₁ᶜ := connectedComponentIn_subset _ _
      have hwO : w ∈ O := mem_connectedComponentIn hwF1
      have hOβ : ∀ z ∈ O, z ∉ β := by
        intro z hz hzβ
        have hzU := hJU₁ z (hβJ hzβ) (hOF hz)
        apply h1
        have : O = U₁ := (connectedComponentIn_eq hz).trans (connectedComponentIn_eq hzU).symm
        rw [← this]; exact hwO
      have hOU2 : ∀ v ∈ O, v ∉ U₂ := by
        intro v hvO hvU
        have hOF2 : O ⊆ F₂ᶜ := fun z hz hz2 => by
          rcases hz2 with h | h
          · exact hOF hz (Or.inl h)
          · exact hOβ z hz h
        have hsub : O ⊆ connectedComponentIn F₂ᶜ v :=
          isPreconnected_connectedComponentIn.subset_connectedComponentIn hvO hOF2
        rw [← connectedComponentIn_eq hvU] at hsub
        exact h2 (hsub hwO)
      have hfr : Disjoint y (frontier O) := by
        rw [disjoint_left]
        intro z hzy hzfr
        have hzF1 : z ∈ F₁ := mem_of_mem_frontier_comp hF₁.isClosed hzfr
        rcases hzF1 with h | h
        · exact hyx z hzy h
        · have hzβ : z ∉ β := fun hb => hyx z hzy (hαβx ⟨h, hb⟩)
          have hzU2 := hJU₂ z (hαJ h) (by
            rintro (h' | h')
            · exact hyx z hzy h'
            · exact hzβ h')
          obtain ⟨v, hvU, hvO⟩ := mem_closure_iff.1 (frontier_subset_closure hzfr) _ hU₂o hzU2
          exact hOU2 v hvO hvU
      have hyO : y ⊆ O := subset_of_disjoint_frontier hy hOo hfr hw hwO
      exact hOF (hyO hy₁) (Or.inr hy₁α)
    · rw [← hαβ] at hJ
      by_cases ha : w ∈ α
      · have hb : w ∉ β := fun hb => hwx (hαβx ⟨ha, hb⟩)
        right
        exact hJU₂ w (hαJ ha) (by
          rintro (h | h)
          · exact hwx h
          · exact hb h)
      · left
        exact hJU₁ w (by rw [← hαβ]; exact hJ) (by
          rintro (h | h)
          · exact hwx h
          · exact ha h)
  obtain ⟨w, hw, hw1, hw2⟩ := hy U₁ U₂ hU₁o hU₂o (fun w hw => hcov' w hw) ⟨y₂, hy₂, hy2U1⟩
    ⟨y₁, hy₁, hy1U2⟩
  exact hboth w hw hw1 hw2

/-! ### A loop parametrization of a simple closed polygon -/

/-- A simple closed polygon is the image of `[0, 2]` under a continuous map that is injective on
`[0, 2)` and takes the same value at `0` and `2`. -/
theorem exists_loop_param {J : Set Pt} (hJ : IsSimpleClosedPolygon J) :
    ∃ γ : ℝ → Pt, Continuous γ ∧ γ '' Icc 0 2 = J ∧ InjOn γ (Ico 0 2) ∧ γ 2 = γ 0 := by
  obtain ⟨a, b, -, α₁, α₂, h₁, h₂, hU, hI⟩ := twoArcs_base hJ
  obtain ⟨-, f₁, hf₁, hr₁, hf₁0, hf₁1⟩ := HPC.Jones.tarc_of_isSimplePolyArc h₁
  obtain ⟨-, f₂, hf₂, hr₂, hf₂0, hf₂1⟩ := HPC.Jones.tarc_of_isSimplePolyArc h₂
  set P : ℝ → unitInterval := Set.projIcc 0 1 zero_le_one with hPdef
  have hP : ∀ s : unitInterval, P s = s := fun s => Set.projIcc_val zero_le_one s
  have hP1 : P 1 = 1 := by simpa using hP 1
  have hP0 : P 0 = 0 := by simpa using hP 0
  have hPv : ∀ t ∈ Icc (0:ℝ) 1, (P t : ℝ) = t := fun t ht => by
    rw [hPdef, Set.projIcc_of_mem _ ht]
  have hcP : Continuous P := continuous_projIcc
  refine ⟨fun t => if t ≤ 1 then f₁ (P t) else f₂ (P (2 - t)), ?_, ?_, ?_, ?_⟩
  · refine Continuous.if_le (hf₁.continuous.comp hcP)
      (hf₂.continuous.comp (hcP.comp (continuous_const.sub continuous_id))) continuous_id
      continuous_const fun t ht => ?_
    subst ht
    simp only [show (2:ℝ) - 1 = 1 by norm_num, hP1, hf₁1, hf₂1]
  · ext z; constructor
    · rintro ⟨t, -, rfl⟩
      rw [← hU]
      dsimp only
      split_ifs
      · left; rw [← hr₁]; exact mem_range_self _
      · right; rw [← hr₂]; exact mem_range_self _
    · intro hz
      rw [← hU] at hz
      rcases hz with hz | hz
      · rw [← hr₁] at hz
        obtain ⟨s, rfl⟩ := hz
        refine ⟨s, ⟨s.2.1, s.2.2.trans one_le_two⟩, ?_⟩
        simp only
        rw [if_pos s.2.2, hP]
      · rw [← hr₂] at hz
        obtain ⟨s, rfl⟩ := hz
        by_cases hs : (s : ℝ) = 1
        · refine ⟨1, ⟨zero_le_one, one_le_two⟩, ?_⟩
          have : s = 1 := Subtype.ext (by simpa using hs)
          simp only
          rw [if_pos le_rfl, hP1, hf₁1, this, hf₂1]
        · have hlt := lt_of_le_of_ne s.2.2 hs
          refine ⟨2 - s, ⟨by linarith [s.2.2], by linarith [s.2.1]⟩, ?_⟩
          have : ¬ (2 - (s : ℝ) ≤ 1) := by linarith
          simp only
          rw [if_neg this, sub_sub_cancel, hP]
  · have key : ∀ t t' : ℝ, t ∈ Ico (0:ℝ) 2 → t' ∈ Ico (0:ℝ) 2 → t ≤ 1 → ¬ t' ≤ 1 →
        f₁ (P t) ≠ f₂ (P (2 - t')) := by
      intro t t' ht ht' h1 h1' heq
      have hw : f₁ (P t) ∈ α₁ ∩ α₂ := ⟨hr₁ ▸ mem_range_self _, heq ▸ hr₂ ▸ mem_range_self _⟩
      rw [hI] at hw
      push_neg at h1'
      have hm : 2 - t' ∈ Icc (0:ℝ) 1 := ⟨by linarith [ht'.2], by linarith⟩
      rcases hw with hw | hw
      · rw [heq, ← hf₂0] at hw
        have := congrArg Subtype.val (hf₂.injective hw)
        rw [hPv _ hm] at this
        simp at this
        linarith [ht'.2]
      · rw [heq, ← hf₂1] at hw
        have := congrArg Subtype.val (hf₂.injective hw)
        rw [hPv _ hm] at this
        simp at this
        linarith
    intro t ht t' ht' h
    simp only at h
    by_cases h1 : t ≤ 1 <;> by_cases h1' : t' ≤ 1
    · rw [if_pos h1, if_pos h1'] at h
      have := congrArg Subtype.val (hf₁.injective h)
      rwa [hPv _ ⟨ht.1, h1⟩, hPv _ ⟨ht'.1, h1'⟩] at this
    · rw [if_pos h1, if_neg h1'] at h
      exact (key t t' ht ht' h1 h1' h).elim
    · rw [if_neg h1, if_pos h1'] at h
      exact (key t' t ht' ht h1' h1 h.symm).elim
    · rw [if_neg h1, if_neg h1'] at h
      push_neg at h1 h1'
      have := congrArg Subtype.val (hf₂.injective h)
      rw [hPv _ ⟨by linarith [ht.2], by linarith⟩, hPv _ ⟨by linarith [ht'.2], by linarith⟩]
        at this
      linarith
  · simp only [show ¬ ((2:ℝ) ≤ 1) by norm_num, if_false, sub_self, hP0, hf₂0,
      show (0:ℝ) ≤ 1 from zero_le_one, if_true, hf₁0]

/-- Every point of the loop is the image of a parameter in `[0, 2)`. -/
theorem exists_param_of_mem {J : Set Pt} {γ : ℝ → Pt} (hγJ : γ '' Icc 0 2 = J) (hper : γ 2 = γ 0)
    {q : Pt} (hq : q ∈ J) : ∃ t ∈ Ico (0:ℝ) 2, γ t = q := by
  rw [← hγJ] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  by_cases h2 : t = 2
  · exact ⟨0, ⟨le_rfl, two_pos⟩, by rw [h2, hper]⟩
  · exact ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 h2⟩, rfl⟩

/-- **The interlacing lemma for parameters.** If `s < u < t < v < 2`, `γ s, γ t ∈ x` and
`γ u, γ v ∈ y`, then the disjoint sets `x` (a continuum) and `y` (preconnected) cannot both lie in
`D ∪ J`. -/
theorem interlace_param {J D E x y : Set Pt} {γ : ℝ → Pt} (hγ : Continuous γ)
    (hγJ : γ '' Icc 0 2 = J) (hinj : InjOn γ (Ico 0 2)) (hper : γ 2 = γ 0)
    (hDo : IsOpen D) (hEo : IsOpen E) (hEc : IsConnected E) (hcov : Jᶜ = D ∪ E)
    (hDE : Disjoint D E) (hJE : J ⊆ closure E)
    (hx : IsCompact x) (hxc : IsConnected x) (hy : IsPreconnected y)
    (hxJ : x ⊆ D ∪ J) (hyJ : y ⊆ D ∪ J) (hxy : Disjoint x y)
    {s u t v : ℝ} (hs : 0 ≤ s) (hsu : s < u) (hut : u < t) (htv : t < v) (hv : v < 2)
    (hxs : γ s ∈ x) (hxt : γ t ∈ x) (hyu : γ u ∈ y) (hyv : γ v ∈ y) : False := by
  have hIco : ∀ r, s ≤ r → r ≤ t → r ∈ Ico (0:ℝ) 2 := fun r h1 h2 =>
    ⟨hs.trans h1, by linarith⟩
  have h0 : (0:ℝ) ∈ Ico (0:ℝ) 2 := ⟨le_rfl, two_pos⟩
  refine interlace hDo hEo hEc hcov hDE hJE hx hxc hy hxJ hyJ hxy
    (α := γ '' Icc s t) (β := γ '' (Icc t 2 ∪ Icc 0 s))
    (isCompact_Icc.image hγ) ((isCompact_Icc.union isCompact_Icc).image hγ) ?_ ?_ hyu
    ⟨u, ⟨hsu.le, hut.le⟩, rfl⟩ ?_ hyv ?_ ⟨v, Or.inl ⟨htv.le, hv.le⟩, rfl⟩
  · rw [← image_union, ← hγJ]
    congr 1
    ext r
    simp only [mem_union, mem_Icc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
    · rintro ⟨h1, h2⟩
      by_cases h3 : r ≤ s
      · exact Or.inr (Or.inr ⟨h1, h3⟩)
      · by_cases h4 : r ≤ t
        · exact Or.inl ⟨by linarith, h4⟩
        · exact Or.inr (Or.inl ⟨by linarith, h2⟩)
  · rintro z ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    have haI := hIco a ha.1 ha.2
    by_cases hb2 : b = 2
    · rw [hb2, hper] at hab
      have := hinj h0 haI hab
      have hs0 : s = 0 := le_antisymm (this ▸ ha.1) hs
      rw [← this, ← hs0]; exact hxs
    · have hbI : b ∈ Ico (0:ℝ) 2 := by
        rcases hb with hb | hb
        · exact ⟨by linarith [hb.1], lt_of_le_of_ne hb.2 hb2⟩
        · exact ⟨hb.1, by linarith [hb.2]⟩
      have := hinj hbI haI hab
      subst this
      rcases hb with hb | hb
      · rw [le_antisymm ha.2 hb.1]; exact hxt
      · rw [le_antisymm hb.2 ha.1]; exact hxs
  · rintro ⟨b, hb, hbu⟩
    have huI := hIco u hsu.le hut.le
    by_cases hb2 : b = 2
    · rw [hb2, hper] at hbu
      have := hinj h0 huI hbu
      linarith
    · have hbI : b ∈ Ico (0:ℝ) 2 := by
        rcases hb with hb | hb
        · exact ⟨by linarith [hb.1], lt_of_le_of_ne hb.2 hb2⟩
        · exact ⟨hb.1, by linarith [hb.2]⟩
      have := hinj hbI huI hbu
      subst this
      rcases hb with hb | hb
      · linarith [hb.1]
      · linarith [hb.2]
  · rintro ⟨a, ha, hav⟩
    have := hinj (hIco a ha.1 ha.2) ⟨by linarith, hv⟩ hav
    linarith [ha.2]

/-- **Moore's Theorem 76 in parameter form** (combinatorial step). Let `P`, `Q` be predicates on
parameters such that no `s < u < t < v < 2` (with `0 ≤ s`) has `P s, P t, Q u, Q v` or
`Q s, Q t, P u, P v`. Then there are no three blocks, pairwise strictly ordered, each containing a
`P`-parameter and a different `Q`-parameter in `[0, 2)`. -/
theorem interlace_three {P Q : ℝ → Prop}
    (H : ∀ s u t v, 0 ≤ s → s < u → u < t → t < v → v < 2 → P s → P t → Q u → Q v → False)
    (H' : ∀ s u t v, 0 ≤ s → s < u → u < t → t < v → v < 2 → Q s → Q t → P u → P v → False)
    (p q : Fin 3 → ℝ) (hp : ∀ i, p i ∈ Ico (0:ℝ) 2) (hq : ∀ i, q i ∈ Ico (0:ℝ) 2)
    (hP : ∀ i, P (p i)) (hQ : ∀ i, Q (q i)) (hne : ∀ i, p i ≠ q i)
    (hord : ∀ i j, i ≠ j → (p i < p j ∧ p i < q j ∧ q i < p j ∧ q i < q j) ∨
      (p j < p i ∧ p j < q i ∧ q j < p i ∧ q j < q i)) : False := by
  have pairl : ∀ i j, (p i < p j ∧ p i < q j ∧ q i < p j ∧ q i < q j) →
      (p i < q i ↔ p j < q j) → False := by
    intro i j ⟨h1, h2, h3, h4⟩ hc
    by_cases hi : p i < q i
    · exact H (p i) (q i) (p j) (q j) (hp i).1 hi h3 (hc.1 hi) (hq j).2 (hP i) (hP j) (hQ i) (hQ j)
    · have hi' : q i < p i := lt_of_le_of_ne (not_lt.1 hi) (hne i).symm
      have hj : ¬ p j < q j := fun h => hi (hc.2 h)
      have hj' : q j < p j := lt_of_le_of_ne (not_lt.1 hj) (hne j).symm
      exact H' (q i) (p i) (q j) (p j) (hq i).1 hi' h2 hj' (hp j).2 (hQ i) (hQ j) (hP i) (hP j)
  have pair : ∀ i j, i ≠ j → (p i < q i ↔ p j < q j) → False := by
    intro i j hij hc
    rcases hord i j hij with h | h
    · exact pairl i j h hc
    · exact pairl j i h hc.symm
  by_cases h0 : p 0 < q 0 <;> by_cases h1 : p 1 < q 1 <;> by_cases h2 : p 2 < q 2 <;>
    first
    | exact pair 0 1 (by decide) (by tauto)
    | exact pair 0 2 (by decide) (by tauto)
    | exact pair 1 2 (by decide) (by tauto)

end HPC.Hagopian
