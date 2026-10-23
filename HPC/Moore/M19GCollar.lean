import HPC.Moore.M19GSplit

/-!
# Moore 1919: the annulus lemma (batch 144, item B)

**The closed annulus is a collar** (`exists_collar`). If `J ∪ I` lies within `J'`, there is an
embedding `H` of `J × [0, 1]` onto the closed annulus `J' ∪ I' − I`, the identity on `J × 0`,
sending `J × 1` onto `J'`.

Proof: the annulus is cut into two quadrilaterals `PP'Q'QP` and `QQ'P'PQ` (`annulus_decomp`). Each
receives a prescribed-boundary square map (`m19_schoenflies_boundary_proof`) which agrees with the
other on the two cuts and restricts on the inner side to a parametrization of the corresponding arc
of `J`. `H (z, s)` is the value at height `s` above the parameter of `z`.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-- A continuous left inverse of an embedding of `[0, 1]`, on its range. -/
theorem exists_leftInverse_of_isEmbedding {X : Type*} [TopologicalSpace X]
    {f : unitInterval → X} (hf : IsEmbedding f) :
    ∃ g : X → unitInterval, ContinuousOn g (range f) ∧ ∀ t, g (f t) = t := by
  classical
  refine ⟨Function.invFun f, ?_, Function.leftInverse_invFun hf.injective⟩
  rw [continuousOn_iff_continuous_restrict]
  have : (range f).restrict (Function.invFun f) = hf.toHomeomorph.symm := by
    funext x
    obtain ⟨_, t, rfl⟩ := x
    have e : hf.toHomeomorph.symm ⟨f t, t, rfl⟩ = t := by
      apply hf.toHomeomorph.injective
      rw [Homeomorph.apply_symm_apply]; rfl
    rw [e]; exact Function.leftInverse_invFun hf.injective t
  rw [this]; exact hf.toHomeomorph.symm.continuous

section Collar

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **The annulus lemma, collar form.** If the closed curve `J'` encloses the closed curve `J`
(`J ∪ I ⊆ I'`), there is an embedding `H` of `J × [0, 1]` onto `J' ∪ I' − I` with `H (z, 0) = z`
and `H (J × 1) = J'`. *Axioms used: 1–8.* -/
theorem exists_collar {J I J' I' : Set S} (hI : σ.IsInteriorOf J I)
    (hI' : σ.IsInteriorOf J' I') (hsub : J ∪ I ⊆ I') :
    ∃ H : S × ℝ → S, @HPC.Sq.CollarProp S σ.topology J I (J' ∪ I') J' H := by
  classical
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have arc : ∀ {a b : S} {K : Set S}, TArc a b K → σ.IsArc a b K := fun h =>
    (isArc_iff_tarc h1 h3 h4 h51).mpr h
  obtain ⟨-, -, -, -, -, -, -, -, -, hIJ', -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI'
  obtain ⟨P, Q, P', Q', c₁, c₂, hc₁, hc₂, hP, hQ, hP', hQ', hc₁₂, hc₁D, hc₂D, hc₁J', hc₂J', hc₁s,
    hc₂s⟩ := exists_cuts h1 h2 h3 h4 h5 h6 h7 h8 hI hI' hsub
  obtain ⟨a₁, a₂, b₁, b₂, A₁, A₂, ha₁, ha₂, hai, hau, hb₁, hb₂, hbi, hbu, hA₁, hA₂, hA₁₂, hA₁K,
    hA₂K, hcover⟩ := annulus_decomp h1 h2 h3 h4 h5 h6 h7 h8 hI hI' hsub hc₁ hc₂ hP hQ hP' hQ'
      hc₁₂ hc₁D hc₂D hc₁J' hc₂J' hc₁s hc₂s
  have ha₁J : a₁ ⊆ J := hau ▸ subset_union_left
  have ha₂J : a₂ ⊆ J := hau ▸ subset_union_right
  have hb₁J' : b₁ ⊆ J' := hbu ▸ subset_union_left
  have hb₂J' : b₂ ⊆ J' := hbu ▸ subset_union_right
  -- intersections of the sides
  have cb : ∀ {b : Set S}, b ⊆ J' → P' ∈ b → Q' ∈ b → c₁ ∩ b = {P'} ∧ b ∩ c₂ = {Q'} := by
    intro b hb hP'b hQ'b
    constructor
    · apply subset_antisymm
      · rintro x ⟨hx, hxb⟩; exact mem_of_inter_eq' hc₁J' hx (hb hxb)
      · rintro x rfl; exact ⟨hc₁.right_mem, hP'b⟩
    · apply subset_antisymm
      · rintro x ⟨hxb, hx⟩; exact mem_of_inter_eq' hc₂J' hx (hb hxb)
      · rintro x rfl; exact ⟨hQ'b, hc₂.right_mem⟩
  have ca : ∀ {a : Set S}, a ⊆ J → P ∈ a → Q ∈ a → c₂ ∩ a = {Q} ∧ a ∩ c₁ = {P} := by
    intro a ha hPa hQa
    constructor
    · apply subset_antisymm
      · rintro x ⟨hx, hxa⟩; exact mem_of_inter_eq' hc₂D hx (Or.inl (ha hxa))
      · rintro x rfl; exact ⟨hc₂.left_mem, hQa⟩
    · apply subset_antisymm
      · rintro x ⟨hxa, hx⟩; exact mem_of_inter_eq' hc₁D hx (Or.inl (ha hxa))
      · rintro x rfl; exact ⟨hPa, hc₁.left_mem⟩
  have ba : ∀ {a b : Set S}, a ⊆ J → b ⊆ J' → Disjoint b a := by
    intro a b ha hb
    rw [disjoint_left]
    intro x hxb hxa
    exact disjoint_left.mp hIJ' (hsub (Or.inl (ha hxa))) (hb hxb)
  obtain ⟨cb₁1, cb₁2⟩ := cb hb₁J' hb₁.left_mem hb₁.right_mem
  obtain ⟨cb₂1, cb₂2⟩ := cb hb₂J' hb₂.left_mem hb₂.right_mem
  obtain ⟨ca₁1, ca₁2⟩ := ca ha₁J ha₁.left_mem ha₁.right_mem
  obtain ⟨ca₂1, ca₂2⟩ := ca ha₂J ha₂.left_mem ha₂.right_mem
  -- the two quadrilaterals
  have q₁ : σ.Quad (c₁ ∪ b₁ ∪ c₂ ∪ a₁) A₁ P P' Q' Q c₁ b₁ c₂ a₁ :=
    { interior := hA₁
      ab := arc hc₁
      bc := arc hb₁
      cd := arc hc₂.symm
      da := arc ha₁.symm
      union := rfl
      ab_bc := cb₁1
      bc_cd := cb₁2
      cd_da := ca₁1
      da_ab := ca₁2
      ab_cd := hc₁₂
      bc_da := ba ha₁J hb₁J' }
  have hK₂ : c₂ ∪ b₂ ∪ c₁ ∪ a₂ = c₁ ∪ b₂ ∪ c₂ ∪ a₂ := by
    ext x; simp only [mem_union]; tauto
  have q₂ : σ.Quad (c₂ ∪ b₂ ∪ c₁ ∪ a₂) A₂ Q Q' P' P c₂ b₂ c₁ a₂ :=
    { interior := hK₂ ▸ hA₂
      ab := arc hc₂
      bc := arc hb₂.symm
      cd := arc hc₁.symm
      da := arc ha₂
      union := rfl
      ab_bc := by rw [inter_comm]; exact cb₂2
      bc_cd := by rw [inter_comm]; exact cb₂1
      cd_da := by rw [inter_comm]; exact ca₂2
      da_ab := by rw [inter_comm]; exact ca₂1
      ab_cd := hc₁₂.symm
      bc_da := ba ha₂J hb₂J' }
  have hPa₁ : P ∈ a₁ := ha₁.left_mem
  have hQa₁ : Q ∈ a₁ := ha₁.right_mem
  have hP'c₁ : P' ∈ c₁ := hc₁.right_mem
  have hQ'c₂ : Q' ∈ c₂ := hc₂.right_mem
  have hPc₁ : P ∈ c₁ := hc₁.left_mem
  have hQc₂ : Q ∈ c₂ := hc₂.left_mem
  have a₁c : IsClosed a₁ := ha₁.isClosed
  have a₂c : IsClosed a₂ := ha₂.isClosed
  -- parametrizations
  obtain ⟨-, ψ₁, hψ₁, hψ₁r, hψ₁0, hψ₁1⟩ := hc₁
  obtain ⟨-, ψ₂, hψ₂, hψ₂r, hψ₂0, hψ₂1⟩ := hc₂
  obtain ⟨-, α₁, hα₁, hα₁r, hα₁0, hα₁1⟩ := ha₁
  obtain ⟨-, α₂, hα₂, hα₂r, hα₂0, hα₂1⟩ := ha₂.symm
  obtain ⟨-, β₁, hβ₁, hβ₁r, hβ₁0, hβ₁1⟩ := hb₁
  obtain ⟨-, β₂, hβ₂, hβ₂r, hβ₂0, hβ₂1⟩ := hb₂.symm
  obtain ⟨Φ₁, hΦ₁, hΦ₁r, Φ₁0, Φ₁1, Φ₁1', Φ₁0'⟩ := m19_schoenflies_boundary_proof h1 h2 h3 h4 h5 h6 h7
    h8 q₁ ψ₁ β₁ ψ₂ α₁ ⟨hψ₁, hψ₁r, hψ₁0, hψ₁1⟩ ⟨hβ₁, hβ₁r, hβ₁0, hβ₁1⟩ ⟨hψ₂, hψ₂r, hψ₂0, hψ₂1⟩
    ⟨hα₁, hα₁r, hα₁0, hα₁1⟩
  obtain ⟨Φ₂, hΦ₂, hΦ₂r, Φ₂0, Φ₂1, Φ₂1', Φ₂0'⟩ := m19_schoenflies_boundary_proof h1 h2 h3 h4 h5 h6 h7
    h8 q₂ ψ₂ β₂ ψ₁ α₂ ⟨hψ₂, hψ₂r, hψ₂0, hψ₂1⟩ ⟨hβ₂, hβ₂r, hβ₂0, hβ₂1⟩ ⟨hψ₁, hψ₁r, hψ₁0, hψ₁1⟩
    ⟨hα₂, hα₂r, hα₂0, hα₂1⟩
  obtain ⟨ι₁, hι₁c, hι₁⟩ := exists_leftInverse_of_isEmbedding hα₁
  obtain ⟨ι₂, hι₂c, hι₂⟩ := exists_leftInverse_of_isEmbedding hα₂
  have rι₁ : ∀ z ∈ a₁, α₁ (ι₁ z) = z := by
    intro z hz; rw [← hα₁r] at hz; obtain ⟨t, rfl⟩ := hz; rw [hι₁]
  have rι₂ : ∀ z ∈ a₂, α₂ (ι₂ z) = z := by
    intro z hz; rw [← hα₂r] at hz; obtain ⟨t, rfl⟩ := hz; rw [hι₂]
  set pr : ℝ → unitInterval := projIcc 0 1 zero_le_one with hpr
  have prv : ∀ s ∈ Icc (0 : ℝ) 1, (pr s : ℝ) = s := fun s hs => by
    rw [hpr, projIcc_of_mem _ hs]
  set G₁ : S × ℝ → S := fun p => Φ₁ (ι₁ p.1, pr p.2) with hG₁
  set G₂ : S × ℝ → S := fun p => Φ₂ (ι₂ p.1, pr p.2) with hG₂
  set H : S × ℝ → S := fun p => if p.1 ∈ a₁ then G₁ p else G₂ p with hH
  -- agreement on the common ends
  have ιP₁ : ι₁ P = 0 := by rw [← hα₁0, hι₁]
  have ιQ₁ : ι₁ Q = 1 := by rw [← hα₁1, hι₁]
  have ιP₂ : ι₂ P = 1 := by rw [← hα₂1, hι₂]
  have ιQ₂ : ι₂ Q = 0 := by rw [← hα₂0, hι₂]
  have agree : ∀ z ∈ a₁, z ∈ a₂ → ∀ s, G₁ (z, s) = G₂ (z, s) := by
    intro z hz₁ hz₂ s
    have : z ∈ a₁ ∩ a₂ := ⟨hz₁, hz₂⟩
    rw [hai] at this
    rcases this with rfl | rfl
    · simp only [hG₁, hG₂, ιP₁, ιP₂, Φ₁0, Φ₂1']
    · simp only [hG₁, hG₂, ιQ₁, ιQ₂, Φ₁1', Φ₂0]
  have H₁ : ∀ p : S × ℝ, p.1 ∈ a₁ → H p = G₁ p := fun p hp => if_pos hp
  have H₂ : ∀ p : S × ℝ, p.1 ∈ a₂ → H p = G₂ p := by
    intro p hp
    by_cases h : p.1 ∈ a₁
    · rw [H₁ p h]; exact agree p.1 h hp p.2
    · exact if_neg h
  have hJ : ∀ {z}, z ∈ J → z ∈ a₁ ∨ z ∈ a₂ := fun hz => by rw [← hau] at hz; exact hz
  -- the curves of the two quadrilaterals meet only on the cuts
  have K₁r : range Φ₁ = c₁ ∪ b₁ ∪ c₂ ∪ a₁ ∪ A₁ := hΦ₁r
  have K₂r : range Φ₂ = c₁ ∪ b₂ ∪ c₂ ∪ a₂ ∪ A₂ := by rw [hΦ₂r, hK₂]
  have meet : ∀ x, x ∈ range Φ₁ → x ∈ range Φ₂ → x ∈ c₁ ∨ x ∈ c₂ := by
    intro x hx₁ hx₂
    rw [K₁r] at hx₁
    rw [K₂r] at hx₂
    rcases hx₂ with hx₂ | hx₂
    swap
    · exfalso
      rcases hx₁ with hx₁ | hx₁
      · exact disjoint_left.mp hA₂K hx₂ hx₁
      · exact disjoint_left.mp hA₁₂ hx₁ hx₂
    rcases hx₁ with hx₁ | hx₁
    swap
    · exact absurd hx₂ (disjoint_left.mp hA₁K hx₁)
    rcases hx₁ with ((h | h) | h) | h
    · exact Or.inl h
    · rcases hx₂ with ((h' | h') | h') | h'
      · exact Or.inl h'
      · have : x ∈ b₁ ∩ b₂ := ⟨h, h'⟩
        rw [hbi] at this
        rcases this with e | e
        · exact Or.inl (e ▸ hP'c₁)
        · exact Or.inr ((mem_singleton_iff.mp e) ▸ hQ'c₂)
      · exact Or.inr h'
      · exact absurd h' (disjoint_left.mp (ba ha₂J hb₁J') h)
    · exact Or.inr h
    · rcases hx₂ with ((h' | h') | h') | h'
      · exact Or.inl h'
      · exact absurd h (disjoint_left.mp (ba ha₁J hb₂J') h')
      · exact Or.inr h'
      · have : x ∈ a₁ ∩ a₂ := ⟨h, h'⟩
        rw [hai] at this
        rcases this with e | e
        · exact Or.inl (e ▸ hPc₁)
        · exact Or.inr ((mem_singleton_iff.mp e) ▸ hQc₂)
  -- a value of `Φ₂` on a cut has parameter `0` or `1`
  have cutpar : ∀ b : unitInterval × unitInterval, Φ₂ b ∈ c₁ ∨ Φ₂ b ∈ c₂ → b.1 = 0 ∨ b.1 = 1 := by
    intro b hb
    rcases hb with hb | hb
    · rw [← hψ₁r] at hb
      obtain ⟨t, ht⟩ := hb
      have := hΦ₂.injective ((Φ₂1' t).trans ht)
      exact Or.inr (congrArg Prod.fst this).symm
    · rw [← hψ₂r] at hb
      obtain ⟨t, ht⟩ := hb
      have := hΦ₂.injective ((Φ₂0 t).trans ht)
      exact Or.inl (congrArg Prod.fst this).symm
  -- the end points of `a₂`
  have endpt : ∀ z ∈ a₂, ι₂ z = 0 ∨ ι₂ z = 1 → z ∈ a₁ := by
    intro z hz h
    rcases h with h | h
    · rw [← rι₂ z hz, h, hα₂0]; exact hQa₁
    · rw [← rι₂ z hz, h, hα₂1]; exact hPa₁
  have cross : ∀ z ∈ a₁, ∀ z' ∈ a₂, z' ∉ a₁ → ∀ s s', G₁ (z, s) ≠ G₂ (z', s') := by
    intro z hz z' hz' hz'n s s' he
    have h₁ : G₁ (z, s) ∈ range Φ₁ := mem_range_self _
    have h₂ : G₁ (z, s) ∈ range Φ₂ := he ▸ mem_range_self _
    have hm := meet _ h₁ h₂
    rw [he] at hm
    have := cutpar (ι₂ z', pr s') hm
    exact hz'n (endpt z' hz' this)
  refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity
    have hJsplit : J ×ˢ Icc (0 : ℝ) 1 = a₁ ×ˢ Icc 0 1 ∪ a₂ ×ˢ Icc 0 1 := by
      rw [← hau, union_prod]
    rw [hJsplit]
    have hprc : Continuous pr := continuous_projIcc
    have hι₁c' : ContinuousOn ι₁ a₁ := by rw [← hα₁r]; exact hι₁c
    have hι₂c' : ContinuousOn ι₂ a₂ := by rw [← hα₂r]; exact hι₂c
    refine ContinuousOn.union_of_isClosed ?_ ?_ (a₁c.prod isClosed_Icc) (a₂c.prod isClosed_Icc)
    · refine ContinuousOn.congr ?_ fun p hp => H₁ p hp.1
      refine hΦ₁.continuous.comp_continuousOn (ContinuousOn.prodMk ?_ ?_)
      · exact hι₁c'.comp continuousOn_fst fun p hp => hp.1
      · exact (hprc.comp continuous_snd).continuousOn
    · refine ContinuousOn.congr ?_ fun p hp => H₂ p hp.1
      refine hΦ₂.continuous.comp_continuousOn (ContinuousOn.prodMk ?_ ?_)
      · exact hι₂c'.comp continuousOn_fst fun p hp => hp.1
      · exact (hprc.comp continuous_snd).continuousOn
  · -- injectivity
    rintro ⟨z, s⟩ ⟨hz, hs⟩ ⟨z', s'⟩ ⟨hz', hs'⟩ he
    simp only at hz hs hz' hs'
    have fin : ∀ {Φ : unitInterval × unitInterval → S} {ι : S → unitInterval} {α : unitInterval → S},
        Function.Injective Φ → Φ (ι z, pr s) = Φ (ι z', pr s') →
        α (ι z) = z → α (ι z') = z' → (z, s) = (z', s') := by
      intro Φ ι α hΦ h hz hz'
      have := hΦ h
      simp only [Prod.mk.injEq] at this
      have e1 : z = z' := by rw [← hz, ← hz', this.1]
      have e2 : s = s' := by
        have := congrArg Subtype.val this.2
        rwa [prv s hs, prv s' hs'] at this
      rw [e1, e2]
    by_cases h₁ : z ∈ a₁ <;> by_cases h₁' : z' ∈ a₁
    · rw [H₁ (z, s) h₁, H₁ (z', s') h₁'] at he
      exact fin hΦ₁.injective he (rι₁ z h₁) (rι₁ z' h₁')
    · rw [H₁ _ h₁] at he
      have hz'2 : z' ∈ a₂ := (hJ hz').resolve_left h₁'
      rw [H₂ _ hz'2] at he
      exact absurd he (cross z h₁ z' hz'2 h₁' s s')
    · rw [H₁ (z', s') h₁'] at he
      have hz2 : z ∈ a₂ := (hJ hz).resolve_left h₁
      rw [H₂ (z, s) hz2] at he
      exact absurd he.symm (cross z' h₁' z hz2 h₁ s' s)
    · have hz2 : z ∈ a₂ := (hJ hz).resolve_left h₁
      have hz'2 : z' ∈ a₂ := (hJ hz').resolve_left h₁'
      rw [H₂ (z, s) hz2, H₂ (z', s') hz'2] at he
      exact fin hΦ₂.injective he (rι₂ z hz2) (rι₂ z' hz'2)
  · -- `H (z, 0) = z`
    intro z hz
    have p0 : pr 0 = 0 := by rw [hpr, projIcc_left]; rfl
    rcases hJ hz with h | h
    · rw [H₁ (z, 0) h]; simp only [hG₁, p0, Φ₁0', rι₁ z h]
    · rw [H₂ (z, 0) h]; simp only [hG₂, p0, Φ₂0', rι₂ z h]
  · -- the image
    rw [← hcover]
    apply subset_antisymm
    · rintro _ ⟨⟨z, s⟩, ⟨hz, -⟩, rfl⟩
      rcases hJ hz with h | h
      · rw [H₁ _ h]; exact Or.inl (K₁r ▸ mem_range_self _)
      · rw [H₂ _ h]; exact Or.inr (K₂r ▸ mem_range_self _)
    · rintro x (hx | hx)
      · rw [← K₁r] at hx
        obtain ⟨⟨u, v⟩, rfl⟩ := hx
        have hu : α₁ u ∈ a₁ := hα₁r ▸ mem_range_self u
        refine ⟨(α₁ u, v), ⟨ha₁J hu, v.2⟩, ?_⟩
        rw [H₁ _ hu]
        simp only [hG₁, hι₁, hpr, projIcc_val]
      · rw [← K₂r] at hx
        obtain ⟨⟨u, v⟩, rfl⟩ := hx
        have hu : α₂ u ∈ a₂ := hα₂r ▸ mem_range_self u
        refine ⟨(α₂ u, v), ⟨ha₂J hu, v.2⟩, ?_⟩
        rw [H₂ _ hu]
        simp only [hG₂, hι₂, hpr, projIcc_val]
  · -- the outer curve
    have p1 : pr 1 = 1 := by rw [hpr, projIcc_right]; rfl
    apply subset_antisymm
    · rintro _ ⟨⟨z, s⟩, ⟨hz, hs⟩, rfl⟩
      rw [mem_singleton_iff] at hs
      subst hs
      rcases hJ hz with h | h
      · rw [H₁ _ h]; simp only [hG₁, p1, Φ₁1]; exact hb₁J' (hβ₁r ▸ mem_range_self _)
      · rw [H₂ _ h]; simp only [hG₂, p1, Φ₂1]; exact hb₂J' (hβ₂r ▸ mem_range_self _)
    · intro x hx
      rw [← hbu] at hx
      rcases hx with hx | hx
      · rw [← hβ₁r] at hx
        obtain ⟨u, rfl⟩ := hx
        have hu : α₁ u ∈ a₁ := hα₁r ▸ mem_range_self u
        refine ⟨(α₁ u, 1), ⟨ha₁J hu, rfl⟩, ?_⟩
        rw [H₁ _ hu]; simp only [hG₁, hι₁, p1, Φ₁1]
      · rw [← hβ₂r] at hx
        obtain ⟨u, rfl⟩ := hx
        have hu : α₂ u ∈ a₂ := hα₂r ▸ mem_range_self u
        refine ⟨(α₂ u, 1), ⟨ha₂J hu, rfl⟩, ?_⟩
        rw [H₂ _ hu]; simp only [hG₂, hι₂, p1, Φ₂1]

end Collar

end HPC.Moore
