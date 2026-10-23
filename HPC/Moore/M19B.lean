import HPC.Moore.M19Bstep

/-!
# Moore 1919, Theorem B (batch 140, item D)

Moore's proof (pp. 170–172), with his unargued steps supplied:

* "there exists a point `A₁` which is the first point that the segment `AB` has in common with
  `L`": the points of `L` on the open arc `AB` form a closed set `Z` lying in a closed sub-interval
  of the parameter (`seg_nhds`: near `A` and near `B`, `L` lies on `J`, and the open arc `AB` is
  within `J`), so it has a first point.
* "properly joined" (footnote ‡ of p. 171) is the relation `Gen.PJ L I`: equal, or joined by an
  arc of `L` lying in `I`. It is an equivalence relation (`Gen.PJ.symm`, `Gen.PJ.trans`), and each
  class is open in `Z` (`loc_arc`: a closed curve is locally arcwise connected). This is Moore's
  argument for the existence of the last point `Bₙ` and for "`B₁` cannot be a limit point of a set
  of points of `M` no one of which can be properly joined to `A₁`".
* Finiteness of the points `A₁, A₂, …`: Moore uses Theorem A. Here compactness of `Z` gives
  finitely many classes directly, and each step `Aₙ ↦ Bₙ ↦ Aₙ₊₁` leaves one class behind; so
  Theorem A is not needed (see the report, check 3).
* "It is easy to see, with the aid of Theorems 43 and 40 …": `m19_B_step`.
* "the point-set `τ` contains, as a subset, an arc from `A` to `B` …": the arcs are joined one at a
  time (`Gen.TArc.join`), from `B` backwards.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

namespace Gen

variable {X : Type*} [TopologicalSpace X]

/-- `x` *can be properly joined* to `y` (1919, p. 171, footnote ‡), with `L` the closed curve and
`I` the interior of `J`: `x = y`, or an arc of `L` lying in `I` joins them. -/
def PJ (L I : Set X) (x y : X) : Prop := x = y ∨ ∃ K, TArc x y K ∧ K ⊆ L ∩ I

theorem PJ.symm [T2Space X] {L I : Set X} {x y : X} (h : PJ L I x y) : PJ L I y x := by
  rcases h with rfl | ⟨K, hK, hKs⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨K, hK.symm, hKs⟩

theorem PJ.trans [T2Space X] {L I : Set X} {x y z : X} (h : PJ L I x y) (h' : PJ L I y z) :
    PJ L I x z := by
  rcases h with rfl | ⟨K, hK, hKs⟩
  · exact h'
  rcases h' with rfl | ⟨K', hK', hK's⟩
  · exact Or.inr ⟨K, hK, hKs⟩
  by_cases hxz : x = z
  · exact Or.inl hxz
  obtain ⟨γ, hγ, hγa⟩ := hK.join hK'.symm ⟨y, hK.right_mem, hK'.left_mem⟩ hxz
  exact Or.inr ⟨γ, hγa, hγ.trans (union_subset hKs hK's)⟩

end Gen

variable {S : Type*} {σ : Space S}

section Lemmas

variable (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h51 : Space.Axiom5₁ (S := S))
include h1 h3 h4 h51

/-- **A closed curve is locally arcwise connected.** For a point `x` of the closed curve `L` and a
neighbourhood `U` of `x`, every point of `L` near `x` is `x` or is joined to `x` by an arc of `L`
lying in `U`. *Axioms used: 1, 3, 4, 5₁.* -/
theorem loc_arc {L : Set S} (hL : σ.IsSCC L) {x : S} (hx : x ∈ L) {U : Set S}
    (hU : U ∈ @nhds S σ.topology x) :
    ∃ V ∈ @nhds S σ.topology x, ∀ y ∈ V ∩ L, y = x ∨
      ∃ K, @TArc S σ.topology x y K ∧ K ⊆ L ∩ U := by
  letI := σ.topology
  haveI := t2Space h1
  obtain ⟨y₀, hy₀, hxy₀⟩ : ∃ y₀ ∈ L, x ≠ y₀ := by
    obtain ⟨A, B, C₁, C₂, hC₁, -, -, rfl⟩ := hL
    have hC₁t := (isArc_iff_tarc h1 h3 h4 h51).mp hC₁
    by_cases hA : x = A
    · exact ⟨B, Or.inl hC₁t.right_mem, hA ▸ hC₁t.ne⟩
    · exact ⟨A, Or.inl hC₁t.left_mem, hA⟩
  obtain ⟨D₁, D₂, hD₁, hD₂, hDi, hDu⟩ := exists_two_arcs_of_isSCC h1 h3 h4 h51 hL hx hy₀ hxy₀
  obtain ⟨-, g₁, hg₁, rfl, hg₁0, -⟩ := (isArc_iff_tarc h1 h3 h4 h51).mp hD₁
  obtain ⟨-, g₂, hg₂, rfl, hg₂0, -⟩ := (isArc_iff_tarc h1 h3 h4 h51).mp hD₂
  have hnb : ∀ g : unitInterval → S, IsEmbedding g → g 0 = x →
      ∃ r : unitInterval, 0 < r ∧ Ico 0 r ⊆ g ⁻¹' U := by
    intro g hg hg0
    have hV : g ⁻¹' U ∈ 𝓝 (0 : unitInterval) :=
      hg.continuous.continuousAt.preimage_mem_nhds (hg0 ▸ hU)
    obtain ⟨r, hr, hrV⟩ := (mem_nhdsGE_iff_exists_Ico_subset' (a := 0) (u' := 1)
      (zero_lt_one' unitInterval)).mp (mem_nhdsWithin_of_mem_nhds hV)
    exact ⟨r, hr, hrV⟩
  obtain ⟨r₁, hr₁, hr₁U⟩ := hnb g₁ hg₁ hg₁0
  obtain ⟨r₂, hr₂, hr₂U⟩ := hnb g₂ hg₂ hg₂0
  have hcl : ∀ (g : unitInterval → S), IsEmbedding g → ∀ u v : unitInterval,
      IsClosed (g '' Icc u v) := fun g hg u v => (isCompact_Icc.image hg.continuous).isClosed
  refine ⟨(g₁ '' Icc r₁ 1 ∪ g₂ '' Icc r₂ 1)ᶜ,
    ((hcl g₁ hg₁ _ _).union (hcl g₂ hg₂ _ _)).isOpen_compl.mem_nhds ?_, ?_⟩
  · rintro (⟨w, hw, e⟩ | ⟨w, hw, e⟩)
    · exact absurd ((hg₁.injective (e.trans hg₁0.symm)) ▸ hw.1) (not_le.mpr hr₁)
    · exact absurd ((hg₂.injective (e.trans hg₂0.symm)) ▸ hw.1) (not_le.mpr hr₂)
  · rintro y ⟨hyV, hyL⟩
    have key : ∀ (g : unitInterval → S), IsEmbedding g → g 0 = x → ∀ r : unitInterval,
        Ico 0 r ⊆ g ⁻¹' U → range g ⊆ L → ∀ v, g v = y → g v ∉ g '' Icc r 1 →
        y = x ∨ ∃ K, TArc x y K ∧ K ⊆ L ∩ U := by
      intro g hg hg0 r hrU hgL v hv hvr
      have hvr' : v < r := by
        by_contra h; exact hvr ⟨v, ⟨not_lt.mp h, le_one'⟩, rfl⟩
      rcases eq_or_lt_of_le (nonneg' : (0 : unitInterval) ≤ v) with e | hv0
      · left; rw [← hv, ← e, hg0]
      · right
        refine ⟨g '' Icc 0 v, hg0 ▸ hv ▸ TArc.image_Icc hg hv0, ?_⟩
        rintro _ ⟨w, hw, rfl⟩
        exact ⟨hgL (mem_range_self w), hrU ⟨hw.1, lt_of_le_of_lt hw.2 hvr'⟩⟩
    rw [← hDu] at hyL
    rcases hyL with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · exact key g₁ hg₁ hg₁0 r₁ hr₁U (hDu ▸ subset_union_left) v rfl
        (fun h => hyV (Or.inl h))
    · exact key g₂ hg₂ hg₂0 r₂ hr₂U (hDu ▸ subset_union_right) v rfl
        (fun h => hyV (Or.inr h))

/-- Near a point `A` of `J` that is either not on `L` or on a segment common to `J` and `L`, every
point of `L` is on `J`. *Axioms used: 1, 3, 4, 5₁.* -/
theorem seg_nhds {J L : Set S} (hL : σ.IsSCC L) {A : S}
    (hA' : A ∉ L ∨ ∃ T, σ.IsSegmentOf J T ∧ σ.IsSegmentOf L T ∧ A ∈ T) :
    ∃ N ∈ @nhds S σ.topology A, N ∩ L ⊆ J := by
  letI := σ.topology
  haveI := t2Space h1
  have hLc : IsClosed L := by
    obtain ⟨A, B, C₁, C₂, hC₁, hC₂, -, rfl⟩ := (isSCC_iff_tscc h1 h3 h4 h51).mp hL
    exact (hC₁.isCompact.union hC₂.isCompact).isClosed
  rcases hA' with hA | ⟨T, ⟨X', Y', K', hK', hK'J, hT'⟩, ⟨X, Y, K, hK, hKL, rfl⟩, hAT⟩
  · exact ⟨Lᶜ, hLc.isOpen_compl.mem_nhds hA, fun y hy => absurd hy.2 hy.1⟩
  obtain ⟨C₁, C₂, hC₁, hC₂, hCi, hCu, huniq⟩ :=
    fa_scc_two_arcs h1 h3 h4 h51 hL (hKL hK.left_mem) (hKL hK.right_mem) hK.1
  obtain ⟨K₂, hK₂, hKK₂, hKK₂u⟩ : ∃ K₂, σ.IsArc X Y K₂ ∧ K ∩ K₂ = {X, Y} ∧ K ∪ K₂ = L := by
    rcases huniq K hKL hK with rfl | rfl
    · exact ⟨C₂, hC₂, hCi, hCu⟩
    · exact ⟨C₁, hC₁, by rw [inter_comm, hCi], by rw [union_comm, hCu]⟩
  have hK₂c : IsClosed K₂ := ((isArc_iff_tarc h1 h3 h4 h51).mp hK₂).isClosed
  refine ⟨K₂ᶜ, hK₂c.isOpen_compl.mem_nhds ?_, ?_⟩
  · intro hAK₂
    have : A ∈ K ∩ K₂ := ⟨hAT.1, hAK₂⟩
    rw [hKK₂] at this
    exact hAT.2 this
  · rintro y ⟨hyK₂, hyL⟩
    have hyK : y ∈ K := by
      rcases hKK₂u ▸ hyL with h | h
      · exact h
      · exact absurd h hyK₂
    have hyT : y ∈ openArc X Y K := by
      refine ⟨hyK, fun hy => hyK₂ ?_⟩
      have : y ∈ K ∩ K₂ := hKK₂ ▸ hy
      exact this.2
    rw [hT'] at hyT
    exact hK'J hyT.1

end Lemmas

/-- **Theorem B** (p. 170). If `J`, `L` are simple closed curves and `A ≠ B` are points of `J`, each
either not on `L` or on some segment common to `J` and `L`, there is an arc from `A` to `B` lying,
except for its endpoints, within `J` and having only finitely many points in common with `L`.
*Axioms used: 1–8.* Moore's proof, with the steps he calls clear supplied (module docstring and
`LEDGER.md` §6, batch 140, check 2). **Shape change:** the axioms are made explicit. -/
theorem m19_theoremB (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
    {J I L : Set S} (hJ : σ.IsInteriorOf J I) (hL : σ.IsSCC L) {A B : S}
    (hA : A ∈ J) (hB : B ∈ J) (hAB : A ≠ B)
    (hA' : A ∉ L ∨ ∃ T, σ.IsSegmentOf J T ∧ σ.IsSegmentOf L T ∧ A ∈ T)
    (hB' : B ∉ L ∨ ∃ T, σ.IsSegmentOf J T ∧ σ.IsSegmentOf L T ∧ B ∈ T) :
    ∃ K, σ.IsArc A B K ∧ openArc A B K ⊆ I ∧ (K ∩ L).Finite := by
  classical
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨hIo, -, -, -, -, -, -, -, -, hdisIJ, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hJ
  obtain ⟨IL, hILreg, hILL⟩ := h8 L hL
  have hIL : σ.IsInteriorOf L IL := ⟨hL, hILreg, hILL⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hdisL, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hIL
  have hLc : IsClosed L := by
    obtain ⟨A, B, C₁, C₂, hC₁, hC₂, -, rfl⟩ := (isSCC_iff_tscc h1 h3 h4 h51).mp hL
    exact (hC₁.isCompact.union hC₂.isCompact).isClosed
  have hBI : B ∉ I := fun h => disjoint_left.mp hdisIJ h hB
  obtain ⟨X, -, hX, -, hXI, -⟩ := fa_theorem40 h1 h2 h3 h4 h5 h6 h7 h8 hJ hA hB hAB
  obtain ⟨-, α, hα, rfl, hα0, hα1⟩ := (isArc_iff_tarc h1 h3 h4 h51).mp hX
  have hinj := hα.injective
  have hαI : ∀ u, 0 < u → u < 1 → α u ∈ I := by
    intro u hu0 hu1
    refine hXI ⟨mem_range_self u, ?_⟩
    rintro (e | e)
    · exact hu0.ne' (hinj (e.trans hα0.symm))
    · exact hu1.ne (hinj ((mem_singleton_iff.mp e).trans hα1.symm))
  have hαB : ∀ c, c < 1 → α c ≠ B := fun c hc e => hc.ne (hinj (e.trans hα1.symm))
  -- the parameters of the points of `L` on the open arc
  set Z : Set unitInterval := {u | α u ∈ L ∧ 0 < u ∧ u < 1} with hZdef
  have hZ : ∃ a' b' : unitInterval, 0 < a' ∧ b' < 1 ∧ Z = α ⁻¹' L ∩ Icc a' b' := by
    obtain ⟨NA, hNA, hNAJ⟩ := seg_nhds h1 h3 h4 h51 hL hA'
    obtain ⟨NB, hNB, hNBJ⟩ := seg_nhds h1 h3 h4 h51 hL hB'
    have hVA : α ⁻¹' NA ∈ 𝓝 (0 : unitInterval) :=
      hα.continuous.continuousAt.preimage_mem_nhds (hα0 ▸ hNA)
    have hVB : α ⁻¹' NB ∈ 𝓝 (1 : unitInterval) :=
      hα.continuous.continuousAt.preimage_mem_nhds (hα1 ▸ hNB)
    obtain ⟨a', ha', ha'V⟩ := (mem_nhdsGE_iff_exists_Ico_subset' (a := 0) (u' := 1)
      (zero_lt_one' unitInterval)).mp (mem_nhdsWithin_of_mem_nhds hVA)
    obtain ⟨b', hb', hb'V⟩ := (mem_nhdsLE_iff_exists_Ioc_subset' (a := 1) (l' := 0)
      (zero_lt_one' unitInterval)).mp (mem_nhdsWithin_of_mem_nhds hVB)
    refine ⟨a', b', ha', hb', ?_⟩
    ext u
    simp only [hZdef, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Icc]
    constructor
    · rintro ⟨huL, hu0, hu1⟩
      refine ⟨huL, ?_, ?_⟩
      · by_contra h
        push_neg at h
        exact disjoint_left.mp hdisIJ (hαI u hu0 hu1) (hNAJ ⟨ha'V ⟨nonneg', h⟩, huL⟩)
      · by_contra h
        push_neg at h
        exact disjoint_left.mp hdisIJ (hαI u hu0 hu1) (hNBJ ⟨hb'V ⟨h, le_one'⟩, huL⟩)
    · rintro ⟨huL, hu1, hu2⟩
      exact ⟨huL, lt_of_lt_of_le ha' hu1, lt_of_le_of_lt hu2 hb'⟩
  have hZc : IsClosed Z := by
    obtain ⟨a', b', -, -, hZe⟩ := hZ
    rw [hZe]; exact (hLc.preimage hα.continuous).inter isClosed_Icc
  -- properly joined points: each class is open in `Z`
  have hloc : ∀ u ∈ Z, ∀ᶠ w in 𝓝 u, w ∈ Z → PJ L I (α w) (α u) := by
    intro u hu
    obtain ⟨V, hV, hVp⟩ := loc_arc h1 h3 h4 h51 hL hu.1 (hIo.mem_nhds (hαI u hu.2.1 hu.2.2))
    filter_upwards [hα.continuous.continuousAt.preimage_mem_nhds hV] with w hw hwZ
    rcases hVp (α w) ⟨hw, hwZ.1⟩ with e | ⟨K, hK, hKs⟩
    · exact Or.inl e
    · exact Gen.PJ.symm (Or.inr ⟨K, hK, hKs⟩ : PJ L I (α u) (α w))
  -- finitely many classes
  obtain ⟨R, -, hRcov⟩ := hZc.isCompact.elim_nhds_subcover
    (fun u => {w | w ∈ Z → PJ L I (α w) (α u)}) (fun u hu => hloc u hu)
  have hRcov' : ∀ v ∈ Z, ∃ r ∈ R, PJ L I (α v) (α r) := by
    intro v hv
    have := hRcov hv
    simp only [mem_iUnion, mem_setOf_eq] at this
    obtain ⟨r, hr, hvr⟩ := this
    exact ⟨r, hr, hvr hv⟩
  set cnt : unitInterval → ℕ :=
    fun c => (R.filter fun r => ∃ v ∈ Z, c ≤ v ∧ PJ L I (α v) (α r)).card with hcnt
  -- the joining step
  have join_step : ∀ (x y : S) (P γ : Set S), TArc x y P → x ≠ B → y ∈ I → P ⊆ insert x I →
      (P ∩ L).Finite → TArc y B γ → γ ⊆ insert y (insert B I) → (γ ∩ L).Finite →
      ∃ γ', TArc x B γ' ∧ γ' ⊆ insert x (insert B I) ∧ (γ' ∩ L).Finite := by
    intro x y P γ hP hxB hyI hPI hPL hγ hγI hγL
    obtain ⟨γ', hγ'sub, hγ'⟩ := hP.join hγ.symm ⟨y, hP.right_mem, hγ.left_mem⟩ hxB
    refine ⟨γ', hγ', ?_, (hPL.union hγL).subset ?_⟩
    · intro z hz
      rcases hγ'sub hz with h | h
      · rcases hPI h with rfl | h
        · exact Or.inl rfl
        · exact Or.inr (Or.inr h)
      · rcases hγI h with rfl | h
        · exact Or.inr (Or.inr hyI)
        · exact Or.inr h
    · rintro z ⟨hz, hzL⟩
      rcases hγ'sub hz with h | h
      · exact Or.inl ⟨h, hzL⟩
      · exact Or.inr ⟨h, hzL⟩
  -- no point of `L` beyond `c`
  have empty_case : ∀ c : unitInterval, c < 1 → (¬ ∃ v ∈ Z, c ≤ v) →
      ∃ γ, TArc (α c) B γ ∧ γ ⊆ insert (α c) (insert B I) ∧ (γ ∩ L).Finite := by
    intro c hc1 hno
    refine ⟨α '' Icc c 1, hα1 ▸ TArc.image_Icc hα hc1, ?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      rcases eq_or_lt_of_le hu.1 with e | hcu
      · exact Or.inl (e ▸ rfl)
      rcases eq_or_lt_of_le hu.2 with e | hu1
      · exact Or.inr (Or.inl (e ▸ hα1))
      exact Or.inr (Or.inr (hαI u (lt_of_le_of_lt nonneg' hcu) hu1))
    · refine (toFinite ({α c, B} : Set S)).subset ?_
      rintro _ ⟨⟨u, hu, rfl⟩, huL⟩
      rcases eq_or_lt_of_le hu.1 with e | hcu
      · exact Or.inl (e ▸ rfl)
      rcases eq_or_lt_of_le hu.2 with e | hu1
      · exact Or.inr (e ▸ hα1)
      exact absurd ⟨u, ⟨huL, lt_of_le_of_lt nonneg' hcu, hu1⟩, hu.1⟩ hno
  have main : ∀ n : ℕ, ∀ c : unitInterval, cnt c ≤ n → c < 1 → (c = 0 ∨ (0 < c ∧ α c ∉ L)) →
      ∃ γ, TArc (α c) B γ ∧ γ ⊆ insert (α c) (insert B I) ∧ (γ ∩ L).Finite := by
    intro n
    induction n with
    | zero =>
      intro c hcnt0 hc1 _
      refine empty_case c hc1 ?_
      rintro ⟨v, hv, hcv⟩
      obtain ⟨r, hr, hvr⟩ := hRcov' v hv
      have : 0 < cnt c := Finset.card_pos.mpr
        ⟨r, Finset.mem_filter.mpr ⟨hr, v, hv, hcv, hvr⟩⟩
      omega
    | succ n ih =>
      intro c hcntn hc1 hc0
      by_cases hne : ∃ v ∈ Z, c ≤ v
      swap
      · exact empty_case c hc1 hne
      -- `Aₙ = α s`: the first point of `L` after `c`
      set Zc := Z ∩ Ici c with hZcdef
      have hZcc : IsClosed Zc := hZc.inter isClosed_Ici
      have hZcne : Zc.Nonempty := by obtain ⟨v, hv, hcv⟩ := hne; exact ⟨v, hv, hcv⟩
      set s := sInf Zc with hsdef
      have hs : s ∈ Zc := hZcc.csInf_mem hZcne ⟨0, fun _ _ => nonneg'⟩
      have hsmin : ∀ v ∈ Zc, s ≤ v := fun v hv => csInf_le ⟨0, fun _ _ => nonneg'⟩ hv
      have hcs : c < s := by
        refine lt_of_le_of_ne hs.2 fun e => ?_
        rcases hc0 with rfl | ⟨-, hcL⟩
        · exact hs.1.2.1.ne e
        · exact hcL (e ▸ hs.1.1)
      -- `Bₙ = α t`: the last point properly joined to `α s`
      set T : Set unitInterval := {v | v ∈ Z ∧ PJ L I (α v) (α s)} with hTdef
      have hTc : IsClosed T := by
        refine isClosed_of_closure_subset fun v hv => ?_
        have hvZ : v ∈ Z := hZc.closure_subset (closure_mono (fun w hw => hw.1) hv)
        obtain ⟨w, hwN, hwT⟩ := mem_closure_iff_nhds.mp hv _ (hloc v hvZ)
        exact ⟨hvZ, (hwN hwT.1).symm.trans hwT.2⟩
      have hsT : s ∈ T := ⟨hs.1, Or.inl rfl⟩
      set t := sSup T with htdef
      have ht : t ∈ T := hTc.csSup_mem ⟨s, hsT⟩ ⟨1, fun _ _ => le_one'⟩
      have htmax : ∀ v ∈ T, v ≤ t := fun v hv => le_csSup ⟨1, fun _ _ => le_one'⟩ hv
      have hst : s ≤ t := htmax s hsT
      have ht1 : t < 1 := ht.1.2.2
      have ht0 : 0 < t := ht.1.2.1
      -- the gap after `t`
      obtain ⟨u', hu', hu'N⟩ := (mem_nhdsGE_iff_exists_Ico_subset' (a := t) (u' := 1) ht1).mp
        (mem_nhdsWithin_of_mem_nhds (hloc t ht.1))
      obtain ⟨c', htc', hc'⟩ := exists_between (lt_min (show t < u' from hu') ht1)
      have hc'1 : c' < 1 := lt_of_lt_of_le hc' (min_le_right _ _)
      have hc'0 : 0 < c' := ht0.trans htc'
      have hgap : ∀ w, t < w → w ≤ c' → w ∉ Z := by
        intro w htw hwc' hwZ
        have hwN : PJ L I (α w) (α t) :=
          hu'N ⟨htw.le, lt_of_le_of_lt hwc' (lt_of_lt_of_le hc' (min_le_left _ _))⟩ hwZ
        exact absurd (htmax w ⟨hwZ, hwN.trans ht.2⟩) (not_le.mpr htw)
      have hc'L : α c' ∉ L := fun h => hgap c' htc' le_rfl ⟨h, hc'0, hc'1⟩
      -- one class fewer beyond `c'`
      have hcnt' : cnt c' < cnt c := by
        obtain ⟨r₀, hr₀, hsr₀⟩ := hRcov' s hs.1
        refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨r₀, ?_, ?_⟩)
        · intro r hr
          obtain ⟨hrR, v, hv, hcv, hvr⟩ := Finset.mem_filter.mp hr
          exact Finset.mem_filter.mpr
            ⟨hrR, v, hv, (hcs.trans (lt_of_le_of_lt hst (htc'.trans_le hcv))).le, hvr⟩
        · exact Finset.mem_filter.mpr ⟨hr₀, s, hs.1, hs.2, hsr₀⟩
        · intro hr
          obtain ⟨-, v, hv, hcv, hvr⟩ := Finset.mem_filter.mp hr
          have := htmax v ⟨hv, hvr.trans hsr₀.symm⟩
          exact absurd (lt_of_lt_of_le htc' hcv) (not_lt.mpr this)
      obtain ⟨W, hW, hWI, hWL⟩ := ih c' (by omega) hc'1 (Or.inr ⟨hc'0, hc'L⟩)
      have hsI : α s ∈ I := hαI s hs.1.2.1 hs.1.2.2
      have htI : α t ∈ I := hαI t ht0 ht1
      have hc'I : α c' ∈ I := hαI c' hc'0 hc'1
      -- the interval `Bₙ Aₙ₊₁` of `AB`, then `Bₙ … B`
      obtain ⟨W₃, hW₃, hW₃I, hW₃L⟩ := join_step (α t) (α c') (α '' Icc t c') W
        (TArc.image_Icc hα htc') (hαB t ht1) hc'I
        (by
          rintro _ ⟨w, hw, rfl⟩
          exact Or.inr (hαI w (ht0.trans_le hw.1) (lt_of_le_of_lt hw.2 hc'1)))
        ((finite_singleton (α t)).subset (by
          rintro _ ⟨⟨w, hw, rfl⟩, hwL⟩
          rcases eq_or_lt_of_le hw.1 with e | htw
          · exact e ▸ rfl
          · exact absurd ⟨hwL, ht0.trans htw, lt_of_le_of_lt hw.2 hc'1⟩ (hgap w htw hw.2)))
        hW hWI hWL
      -- the arc `Aₙ Z̄ₙ Bₙ` (`m19_B_step`), then `Aₙ … B`
      obtain ⟨W₂, hW₂, hW₂I, hW₂L⟩ : ∃ γ, TArc (α s) B γ ∧ γ ⊆ insert (α s) (insert B I) ∧
          (γ ∩ L).Finite := by
        rcases eq_or_lt_of_le hst with e | hst'
        · rw [e]; exact ⟨W₃, hW₃, hW₃I, hW₃L⟩
        have hne' : α t ≠ α s := fun e => hst'.ne (hinj e.symm)
        rcases ht.2 with e | ⟨K, hK, hKs⟩
        · exact absurd e hne'
        obtain ⟨K', hK', hK'I, hK'IL⟩ := m19_B_step h1 h2 h3 h4 h5 h6 h7 h8 hJ hIL
          ((isArc_iff_tarc h1 h3 h4 h51).mpr hK) (hKs.trans inter_subset_left)
          (hKs.trans inter_subset_right)
        have hK't := ((isArc_iff_tarc h1 h3 h4 h51).mp hK').symm
        refine join_step (α s) (α t) K' W₃ hK't (hαB s hs.1.2.2) htI
          (fun x hx => Or.inr (hK'I hx)) ?_ hW₃ hW₃I hW₃L
        refine (toFinite ({α t, α s} : Set S)).subset ?_
        rintro x ⟨hx, hxL⟩
        by_contra hxts
        exact disjoint_left.mp hdisL (hK'IL ⟨hx, hxts⟩) hxL
      -- the interval `c … Aₙ` of `AB`, then `c … B`
      refine join_step (α c) (α s) (α '' Icc c s) W₂ (TArc.image_Icc hα hcs) (hαB c hc1) hsI
        ?_ ?_ hW₂ hW₂I hW₂L
      · rintro _ ⟨w, hw, rfl⟩
        rcases eq_or_lt_of_le hw.1 with e | hcw
        · exact Or.inl (e ▸ rfl)
        · exact Or.inr (hαI w (lt_of_le_of_lt nonneg' hcw) (lt_of_le_of_lt hw.2 hs.1.2.2))
      · refine (toFinite ({α c, α s} : Set S)).subset ?_
        rintro _ ⟨⟨w, hw, rfl⟩, hwL⟩
        rcases eq_or_lt_of_le hw.1 with e | hcw
        · exact Or.inl (e ▸ rfl)
        rcases eq_or_lt_of_le hw.2 with e | hws
        · exact Or.inr (e ▸ rfl)
        exact absurd (hsmin w ⟨⟨hwL, lt_of_le_of_lt nonneg' hcw, hws.trans hs.1.2.2⟩, hw.1⟩)
          (not_le.mpr hws)
  obtain ⟨γ, hγ, hγs, hγf⟩ := main _ 0 le_rfl (zero_lt_one' unitInterval) (Or.inl rfl)
  rw [hα0] at hγ hγs
  refine ⟨γ, (isArc_iff_tarc h1 h3 h4 h51).mpr hγ, ?_, hγf⟩
  rintro x ⟨hx, hxAB⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hxAB
  rcases hγs hx with h | h | h
  · exact absurd h hxAB.1
  · exact absurd h hxAB.2
  · exact h

end HPC.Moore
