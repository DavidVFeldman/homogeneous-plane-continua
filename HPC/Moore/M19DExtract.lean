import HPC.Moore.M19DInside

/-!
# Moore 1919, Theorem D: the chords of a closed curve

**Theorem** (`extract_chords`). If the closed curve `h` meets `ABCDA` in finitely many points (at
least one), none of them `A, B, C, D`, and touches `ABCDA` from within at none of them, the part of
`h` within `ABCDA` lies on finitely many mutually exclusive chords of `ABCDA`.

`h` is the sum of two arcs `C₁, C₂` joining two of the common points; the common points cut each
`Cᵢ` into finitely many pieces (`pieces`), and the chords are the pieces within `ABCDA`. Two of
them have no common point: such a point would end both, and `h` would touch `ABCDA` from within
there. A crossing excludes touching (`Space.Crosses.no_fork`, from `TArc.no_fork`: an arc ending at
`p` contains no two arcs from `p` meeting only in `p`).
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

namespace Gen

variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
/-- An arc ending at `p` contains no two arcs from `p` meeting only in `p`. -/
theorem TArc.no_fork {u p m₁ m₂ : X} {t M₁ M₂ : Set X} (ht : TArc u p t) (h₁ : TArc p m₁ M₁)
    (h₂ : TArc p m₂ M₂) (h12 : M₁ ∩ M₂ = {p}) (s₁ : M₁ ⊆ t) (s₂ : M₂ ⊆ t) : False := by
  obtain ⟨-, g, hg, rfl, rfl, rfl⟩ := ht
  have pre : ∀ {m M}, TArc (g 1) m M → M ⊆ range g →
      ∃ s, s < 1 ∧ Icc s 1 ⊆ g ⁻¹' M := by
    intro m M hM hMs
    have hc : IsPreconnected (g ⁻¹' M) := by
      rw [← hg.isInducing.isPreconnected_image, image_preimage_eq_of_subset hMs]
      exact hM.isPreconnected
    obtain ⟨s, rfl⟩ := hMs hM.right_mem
    refine ⟨s, lt_of_le_of_ne le_one' (fun e => hM.ne (by rw [e])), hc.Icc_subset ?_ ?_⟩
    · show g s ∈ M; exact hM.right_mem
    · show g 1 ∈ M; exact hM.left_mem
  obtain ⟨s₁', hs₁, hI₁⟩ := pre h₁ s₁
  obtain ⟨s₂', hs₂, hI₂⟩ := pre h₂ s₂
  have hr : max s₁' s₂' < 1 := max_lt hs₁ hs₂
  have : g (max s₁' s₂') ∈ M₁ ∩ M₂ :=
    ⟨hI₁ ⟨le_max_left _ _, le_one'⟩, hI₂ ⟨le_max_right _ _, le_one'⟩⟩
  rw [h12, mem_singleton_iff] at this
  exact hr.ne (hg.injective this)

/-- An arc from `p` has a sub-arc from `p` within any neighbourhood of `p`. -/
theorem TArc.shrink {p m : X} {M N : Set X} (hM : TArc p m M) (hN : N ∈ 𝓝 p) :
    ∃ m' M', M' ⊆ M ∩ N ∧ TArc p m' M' := by
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := hM
  have h0 : f ⁻¹' N ∈ 𝓝[≥] (0 : unitInterval) :=
    mem_nhdsWithin_of_mem_nhds (hf.continuous.continuousAt.preimage_mem_nhds hN)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset' (a := 0) (u' := 1) (by simp)).mp h0
  obtain ⟨r, hr0, hru⟩ := exists_between (show (0 : unitInterval) < u from hu)
  refine ⟨f r, f '' Icc 0 r, ?_, TArc.image_Icc hf hr0⟩
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨mem_range_self _, hsub ⟨hs.1, hs.2.trans_lt hru⟩⟩

end Gen

/-- A crossing forbids two arcs of `h` from `p`, meeting only in `p`, on the same side. -/
theorem Space.Crosses.no_fork (h1 : σ.Axiom1) {I h : Set S} {p m₁ m₂ : S} {M₁ M₂ : Set S}
    (hc : σ.Crosses I h p) (h₁ : @TArc S σ.topology p m₁ M₁) (h₂ : @TArc S σ.topology p m₂ M₂)
    (h12 : M₁ ∩ M₂ = {p}) (hMh : M₁ ∪ M₂ ⊆ h)
    (hside : (M₁ \ {p} ⊆ I ∧ M₂ \ {p} ⊆ I) ∨
      (M₁ \ {p} ⊆ (@closure S σ.topology I)ᶜ ∧ M₂ \ {p} ⊆ (@closure S σ.topology I)ᶜ)) :
    False := by
  letI := σ.topology
  haveI := t2Space h1
  obtain ⟨N, hN, u, v, t, t', ht, ht', htI, ht'E, hsub⟩ := hc
  obtain ⟨n₁, M₁', hM₁', h₁'⟩ := h₁.shrink hN
  obtain ⟨n₂, M₂', hM₂', h₂'⟩ := h₂.shrink hN
  have h12' : M₁' ∩ M₂' = {p} := by
    apply subset_antisymm
    · rw [← h12]; exact inter_subset_inter (fun z hz => (hM₁' hz).1) (fun z hz => (hM₂' hz).1)
    · rintro z rfl; exact ⟨h₁'.left_mem, h₂'.left_mem⟩
  have mem : ∀ {M M' : Set S}, M' ⊆ M ∩ N → M ⊆ h → ∀ {z}, z ∈ M' → z ∈ t ∪ t' :=
    fun hM' hMh z hz => hsub ⟨hMh (hM' hz).1, (hM' hz).2⟩
  rcases hside with ⟨hs₁, hs₂⟩ | ⟨hs₁, hs₂⟩
  · have into : ∀ {M M' : Set S}, M' ⊆ M ∩ N → M ⊆ h → M \ {p} ⊆ I → M' ⊆ t := by
      intro M M' hM' hMh hs z hz
      by_cases hzp : z = p
      · exact hzp ▸ ht.right_mem
      rcases mem hM' hMh hz with h | h
      · exact h
      · exact absurd (subset_closure (hs ⟨(hM' hz).1, hzp⟩)) (ht'E ⟨h, hzp⟩)
    exact ht.no_fork h₁' h₂' h12' (into hM₁' (subset_union_left.trans hMh) hs₁)
      (into hM₂' (subset_union_right.trans hMh) hs₂)
  · have into : ∀ {M M' : Set S}, M' ⊆ M ∩ N → M ⊆ h → M \ {p} ⊆ (closure I)ᶜ → M' ⊆ t' := by
      intro M M' hM' hMh hs z hz
      by_cases hzp : z = p
      · exact hzp ▸ ht'.left_mem
      rcases mem hM' hMh hz with h | h
      · exact absurd (subset_closure (htI ⟨h, hzp⟩)) (hs ⟨(hM' hz).1, hzp⟩)
      · exact h
    exact ht'.symm.no_fork h₁' h₂' h12' (into hM₁' (subset_union_left.trans hMh) hs₁)
      (into hM₂' (subset_union_right.trans hMh) hs₂)

namespace Gen

variable {X : Type*}

/-- The pieces into which a set `T` of parameters cuts the arc `f`: the images of the intervals
between consecutive points of `T`. -/
def pieces (f : unitInterval → X) (T : Set unitInterval) : Set (Set X) :=
  {Y | ∃ a ∈ T, ∃ b ∈ T, a < b ∧ (∀ t ∈ T, t ∉ Ioo a b) ∧ Y = f '' Icc a b}

theorem pieces_finite (f : unitInterval → X) {T : Set unitInterval} (hT : T.Finite) :
    (pieces f T).Finite :=
  ((hT.prod hT).image fun p => f '' Icc p.1 p.2).subset (by
    rintro _ ⟨a, ha, b, hb, -, -, rfl⟩; exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩)

theorem exists_piece {T : Set unitInterval} (hT : T.Finite) (h0 : 0 ∈ T) (h1 : 1 ∈ T)
    {s : unitInterval} (hs : s ∉ T) :
    ∃ a ∈ T, ∃ b ∈ T, a < b ∧ (∀ t ∈ T, t ∉ Ioo a b) ∧ s ∈ Ioo a b := by
  obtain ⟨a, ⟨haT, has⟩, hamax⟩ :=
    Set.exists_max_image (T ∩ Iic s) id (hT.inter_of_left _) ⟨0, h0, nonneg'⟩
  obtain ⟨b, ⟨hbT, hbs⟩, hbmin⟩ :=
    Set.exists_min_image (T ∩ Ici s) id (hT.inter_of_left _) ⟨1, h1, le_one'⟩
  have has' : a < s := lt_of_le_of_ne has (fun e => hs (e ▸ haT))
  have hbs' : s < b := lt_of_le_of_ne hbs (fun e => hs (e.symm ▸ hbT))
  refine ⟨a, haT, b, hbT, has'.trans hbs', fun t ht htab => ?_, has', hbs'⟩
  rcases le_total t s with h | h
  · exact absurd (hamax t ⟨ht, h⟩) (not_le.mpr htab.1)
  · exact absurd (hbmin t ⟨ht, h⟩) (not_le.mpr htab.2)

theorem piece_eq {T : Set unitInterval} {a b c d : unitInterval} (ha : a ∈ T) (hb : b ∈ T)
    (hc : c ∈ T) (hd : d ∈ T) (hab : ∀ t ∈ T, t ∉ Ioo a b) (hcd : ∀ t ∈ T, t ∉ Ioo c d)
    {s : unitInterval} (hs : s ∈ Ioo a b) (hs' : s ∈ Ioo c d) : a = c ∧ b = d := by
  constructor
  · rcases lt_trichotomy a c with h | h | h
    · exact absurd ⟨h, hs'.1.trans hs.2⟩ (hab c hc)
    · exact h
    · exact absurd ⟨h, hs.1.trans hs'.2⟩ (hcd a ha)
  · rcases lt_trichotomy b d with h | h | h
    · exact absurd ⟨hs'.1.trans hs.2, h⟩ (hcd b hb)
    · exact h
    · exact absurd ⟨hs.1.trans hs'.2, h⟩ (hab d hd)

theorem image_Icc_diff {f : unitInterval → X} (hf : Function.Injective f) {a b : unitInterval} : f '' Icc a b \ {f a, f b} = f '' Ioo a b := by
  ext z
  simp only [mem_diff, mem_image, mem_Icc, mem_Ioo, mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · rintro ⟨⟨s, ⟨h1, h2⟩, rfl⟩, ha, hb⟩
    exact ⟨s, ⟨lt_of_le_of_ne h1 fun e => ha (e ▸ rfl), lt_of_le_of_ne h2 fun e => hb (e ▸ rfl)⟩,
      rfl⟩
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨s, ⟨h1.le, h2.le⟩, rfl⟩, fun e => h1.ne' (hf e), fun e => h2.ne (hf e)⟩

end Gen

section Extract

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7)
include h1 h2 h3 h4 h5 h7

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **The chords of a closed curve touching `ABCDA` from within nowhere.** -/
theorem extract_chords (q : σ.Quad J I A B C D sAB sBC sCD sDA) {h W : Set S}
    (hW : σ.IsInteriorOf h W) (hne : (h ∩ J).Nonempty) (hfin : (h ∩ J).Finite)
    (hcor : Disjoint h {A, B, C, D})
    (hnt : ∀ p ∈ h ∩ J, ∀ (m₁ m₂ : S) (M₁ M₂ : Set S), @TArc S σ.topology p m₁ M₁ →
      @TArc S σ.topology p m₂ M₂ → M₁ ∩ M₂ = {p} → M₁ ∪ M₂ ⊆ h → M₁ \ {p} ⊆ I →
        M₂ \ {p} ⊆ I → False) :
    ∃ T : Set (Set S), T.Finite ∧ (∀ t ∈ T, σ.IsChord J I A B C D t) ∧ T.Pairwise Disjoint ∧
      h ∩ I ⊆ ⋃₀ T := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨hIo, -, -, -, hEo, -, -, -, -, hIJ, -, hJc, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 q.interior
  have hside : ∀ {Y : Set S}, IsPreconnected Y → Disjoint Y J → Y ⊆ I ∨ Y ⊆ (closure I)ᶜ :=
    fun hY hYJ => hY.subset_or_subset hIo hEo (disjoint_compl_right.mono_left subset_closure)
      (by rw [← hJc]; exact fun z hz hzJ => disjoint_left.mp hYJ hz hzJ)
  have hIcl : ∀ {z}, z ∈ I → z ∉ (closure I)ᶜ := fun hz hz' => hz' (subset_closure hz)
  -- arcs from a point, avoiding another
  have orient : ∀ {z a b : S} {Y : Set S}, TArc a b Y → (z = a ∨ z = b) →
      ∃ m M, M ⊆ Y ∧ TArc z m M ∧ M \ {z} ⊆ Y \ {a, b} := by
    intro z a b Y hY hz
    rcases hz with rfl | rfl
    · obtain ⟨m, M, hM, hMa⟩ := hY.shrink (isOpen_compl_singleton.mem_nhds hY.ne)
      refine ⟨m, M, fun u hu => (hM hu).1, hMa, ?_⟩
      rintro u ⟨hu, hun⟩
      refine ⟨(hM hu).1, ?_⟩
      rintro (e | e)
      · exact hun e
      · exact (hM hu).2 e
    · obtain ⟨m, M, hM, hMa⟩ := hY.symm.shrink (isOpen_compl_singleton.mem_nhds hY.ne.symm)
      refine ⟨m, M, fun u hu => (hM hu).1, hMa, ?_⟩
      rintro u ⟨hu, hun⟩
      refine ⟨(hM hu).1, ?_⟩
      rintro (e | e)
      · exact (hM hu).2 e
      · exact hun e
  obtain ⟨p₀, hp₀⟩ := hne
  by_cases hhI : (h ∩ I).Nonempty
  swap
  · exact ⟨∅, finite_empty, by simp, pairwise_empty _, fun z hz => absurd ⟨z, hz⟩ hhI⟩
  -- a second common point
  obtain ⟨p₁, hp₁, hp₁₀⟩ : ∃ p₁ ∈ h ∩ J, p₁ ≠ p₀ := by
    by_contra hno
    push_neg at hno
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨a₀, b₀, C₁, C₂, hC₁, -, -, hhe⟩⟩ :=
      jordan h1 h2 h3 h4 h51 h7 hW
    obtain ⟨p₁, hp₁h, hp₁⟩ : ∃ z ∈ h, z ≠ p₀ := by
      by_cases e : a₀ = p₀
      · exact ⟨b₀, hhe ▸ Or.inl hC₁.right_mem, fun e' => hC₁.ne (e.trans e'.symm)⟩
      · exact ⟨a₀, hhe ▸ Or.inl hC₁.left_mem, e⟩
    obtain ⟨D₁, D₂, hD₁, hD₂, hDi, hDu, -⟩ :=
      fa_scc_two_arcs h1 h3 h4 h51 hW.1 hp₀.1 hp₁h hp₁.symm
    rw [isArc_iff_tarc h1 h3 h4 h51] at hD₁ hD₂
    obtain ⟨n₁, M₁, hM₁, hM₁a, hM₁s⟩ := orient hD₁ (Or.inl rfl)
    obtain ⟨n₂, M₂, hM₂, hM₂a, hM₂s⟩ := orient hD₂ (Or.inl rfl)
    have h12 : M₁ ∩ M₂ = {p₀} := by
      apply subset_antisymm
      · rintro z ⟨hz1, hz2⟩
        by_contra hz0
        have hz : z ∈ D₁ ∩ D₂ := ⟨hM₁ hz1, hM₂ hz2⟩
        rw [hDi] at hz
        rcases hz with e | e
        · exact hz0 e
        · exact (hM₁s ⟨hz1, hz0⟩).2 (Or.inr e)
      · rintro z rfl; exact ⟨hM₁a.left_mem, hM₂a.left_mem⟩
    have hMh : M₁ ∪ M₂ ⊆ h := hDu ▸ union_subset_union hM₁ hM₂
    have hpc : IsPreconnected (h \ {p₀}) := by
      rw [← hDu, union_diff_distrib]
      exact hD₁.symm.isPreconnected_diff_right.union p₁ ⟨hD₁.right_mem, hp₁⟩ ⟨hD₂.right_mem, hp₁⟩
        hD₂.symm.isPreconnected_diff_right
    have hdJ : Disjoint (h \ {p₀}) J :=
      disjoint_left.mpr fun z hz hzJ => hz.2 (hno z ⟨hz.1, hzJ⟩)
    have s₁ : M₁ \ {p₀} ⊆ h \ {p₀} := diff_subset_diff_left (subset_union_left.trans hMh)
    have s₂ : M₂ \ {p₀} ⊆ h \ {p₀} := diff_subset_diff_left (subset_union_right.trans hMh)
    rcases hside hpc hdJ with hI | hE
    · exact hnt p₀ hp₀ n₁ n₂ M₁ M₂ hM₁a hM₂a h12 hMh (s₁.trans hI) (s₂.trans hI)
    · obtain ⟨w, hwh, hwI⟩ := hhI
      have hw0 : w ≠ p₀ := fun e => disjoint_left.mp hIJ hwI (e ▸ hp₀.2)
      exact hIcl hwI (hE ⟨hwh, hw0⟩)
  obtain ⟨C₁, C₂, hC₁, hC₂, hCi, hCu, -⟩ :=
    fa_scc_two_arcs h1 h3 h4 h51 hW.1 hp₀.1 hp₁.1 hp₁₀.symm
  rw [isArc_iff_tarc h1 h3 h4 h51] at hC₁ hC₂
  obtain ⟨-, f₁, hf₁, rfl, hf₁0, hf₁1⟩ := hC₁
  obtain ⟨-, f₂, hf₂, rfl, hf₂0, hf₂1⟩ := hC₂
  set E := h ∩ J with hE
  set P := pieces f₁ (f₁ ⁻¹' E) ∪ pieces f₂ (f₂ ⁻¹' E) with hP
  have hfam : ∀ Y ∈ P, ∃ f : unitInterval → S, (f = f₁ ∨ f = f₂) ∧ ∃ a ∈ f ⁻¹' E,
      ∃ b ∈ f ⁻¹' E, a < b ∧ (∀ t ∈ f ⁻¹' E, t ∉ Ioo a b) ∧ Y = f '' Icc a b := by
    rintro Y (hY | hY)
    · exact ⟨f₁, Or.inl rfl, hY⟩
    · exact ⟨f₂, Or.inr rfl, hY⟩
  have hemb : ∀ {f}, (f = f₁ ∨ f = f₂) → IsEmbedding f ∧ range f ⊆ h := by
    rintro f (rfl | rfl)
    · exact ⟨hf₁, hCu ▸ subset_union_left⟩
    · exact ⟨hf₂, hCu ▸ subset_union_right⟩
  have facts : ∀ {f : unitInterval → S}, (f = f₁ ∨ f = f₂) → ∀ {a b}, a ∈ f ⁻¹' E →
      b ∈ f ⁻¹' E → a < b → (∀ t ∈ f ⁻¹' E, t ∉ Ioo a b) →
      TArc (f a) (f b) (f '' Icc a b) ∧ f '' Icc a b ⊆ h ∧
        f '' Icc a b \ {f a, f b} = f '' Ioo a b ∧ Disjoint (f '' Ioo a b) E ∧
        IsPreconnected (f '' Ioo a b) := by
    intro f hf a b ha hb hab hT
    obtain ⟨hfe, hfh⟩ := hemb hf
    refine ⟨TArc.image_Icc hfe hab, (image_subset_range _ _).trans hfh,
      image_Icc_diff hfe.injective, ?_, isPreconnected_Ioo.image _ hfe.continuous.continuousOn⟩
    rw [disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsE
    exact hT s hsE hs
  have hC12 : range f₁ ∩ range f₂ ⊆ E := by
    rw [hCi]; rintro z (rfl | rfl); exacts [hp₀, hp₁]
  have keyA : ∀ {f f' : unitInterval → S}, (f = f₁ ∨ f = f₂) → (f' = f₁ ∨ f' = f₂) →
      ∀ {a b c d}, a ∈ f ⁻¹' E → b ∈ f ⁻¹' E → (∀ t ∈ f ⁻¹' E, t ∉ Ioo a b) →
      c ∈ f' ⁻¹' E → d ∈ f' ⁻¹' E → (∀ t ∈ f' ⁻¹' E, t ∉ Ioo c d) →
      ∀ {z}, z ∈ f '' Ioo a b → z ∈ f' '' Ioo c d → f '' Icc a b = f' '' Icc c d := by
    intro f f' hf hf' a b c d ha hb hab hc hd hcd z hz hz'
    obtain ⟨s, hs, rfl⟩ := hz
    obtain ⟨s', hs', hss⟩ := hz'
    by_cases e : f = f'
    · subst e
      have := (hemb hf).1.injective hss
      subst this
      obtain ⟨rfl, rfl⟩ := piece_eq ha hb hc hd hab hcd hs hs'
      rfl
    · exfalso
      have hz : f s ∈ range f₁ ∩ range f₂ := by
        rcases hf with rfl | rfl <;> rcases hf' with rfl | rfl
        · exact absurd rfl e
        · exact ⟨mem_range_self _, ⟨s', hss⟩⟩
        · exact ⟨⟨s', hss⟩, mem_range_self _⟩
        · exact absurd rfl e
      exact hab s (hC12 hz) hs
  have hopen : ∀ {f}, (f = f₁ ∨ f = f₂) → ∀ {a b}, a ∈ f ⁻¹' E → b ∈ f ⁻¹' E → a < b →
      (∀ t ∈ f ⁻¹' E, t ∉ Ioo a b) → (f '' Icc a b ∩ I).Nonempty → f '' Ioo a b ⊆ I := by
    intro f hf a b ha hb hab hT hne
    obtain ⟨-, hsub, hdiff, hdis, hpc⟩ := facts hf ha hb hab hT
    have hJ : Disjoint (f '' Ioo a b) J := disjoint_left.mpr fun z hz hzJ =>
      disjoint_left.mp hdis hz ⟨hsub (image_mono Ioo_subset_Icc_self hz), hzJ⟩
    rcases hside hpc hJ with hI | hE'
    · exact hI
    · obtain ⟨z, hzY, hzI⟩ := hne
      have hzJ : z ∉ J := fun h' => disjoint_left.mp hIJ hzI h'
      have hzo : z ∈ f '' Ioo a b := by
        rw [← hdiff]
        refine ⟨hzY, ?_⟩
        rintro (e | e)
        · exact hzJ (e ▸ (ha : f a ∈ E).2)
        · exact hzJ (e ▸ (hb : f b ∈ E).2)
      exact absurd (hE' hzo) (hIcl hzI)
  refine ⟨{Y ∈ P | (Y ∩ I).Nonempty},
    ((pieces_finite f₁ (hfin.preimage hf₁.injective.injOn)).union
      (pieces_finite f₂ (hfin.preimage hf₂.injective.injOn))).subset (sep_subset _ _), ?_, ?_, ?_⟩
  · rintro Y ⟨hY, hYI⟩
    obtain ⟨f, hf, a, ha, b, hb, hab, hT, rfl⟩ := hfam Y hY
    obtain ⟨harc, -, hdiff, -, -⟩ := facts hf ha hb hab hT
    have hnc : ∀ {e}, e ∈ E → e ∈ J \ {A, B, C, D} :=
      fun he => ⟨he.2, disjoint_left.mp hcor he.1⟩
    exact ⟨f a, f b, hnc ha, hnc hb, harc, hdiff ▸ hopen hf ha hb hab hT hYI⟩
  · rintro Y ⟨hY, hYI⟩ Y' ⟨hY', hY'I⟩ hne
    obtain ⟨f, hf, a, ha, b, hb, hab, hT, rfl⟩ := hfam Y hY
    obtain ⟨f', hf', c, hc, d, hd, hcd, hT', rfl⟩ := hfam Y' hY'
    obtain ⟨harc, hsub, hdiff, hdis, -⟩ := facts hf ha hb hab hT
    obtain ⟨harc', hsub', hdiff', hdis', -⟩ := facts hf' hc hd hcd hT'
    have A' : ∀ {z}, z ∈ f '' Ioo a b → z ∈ f' '' Ioo c d → False :=
      fun hz hz' => hne (keyA hf hf' ha hb hT hc hd hT' hz hz')
    have hO : f '' Ioo a b ⊆ I := hopen hf ha hb hab hT hYI
    have hO' : f' '' Ioo c d ⊆ I := hopen hf' hc hd hcd hT' hY'I
    show Disjoint _ _
    rw [disjoint_left]
    intro z hz hz'
    have endY : z = f a ∨ z = f b := by
      by_contra hn
      push_neg at hn
      have hzo : z ∈ f '' Ioo a b := hdiff ▸ ⟨hz, by simp [hn.1, hn.2]⟩
      have hzE : z ∉ E := disjoint_left.mp hdis hzo
      refine A' hzo (hdiff' ▸ ⟨hz', ?_⟩)
      rintro (e | e)
      · exact hzE (e ▸ hc)
      · exact hzE (e ▸ hd)
    have endY' : z = f' c ∨ z = f' d := by
      by_contra hn
      push_neg at hn
      have hzo : z ∈ f' '' Ioo c d := hdiff' ▸ ⟨hz', by simp [hn.1, hn.2]⟩
      have hzE : z ∉ E := disjoint_left.mp hdis' hzo
      refine A' (hdiff ▸ ⟨hz, ?_⟩) hzo
      rintro (e | e)
      · exact hzE (e ▸ ha)
      · exact hzE (e ▸ hb)
    have hzE : z ∈ E := by rcases endY with rfl | rfl; exacts [ha, hb]
    obtain ⟨m, M, hMY, hMa, hMs⟩ := orient harc endY
    obtain ⟨m', M', hMY', hMa', hMs'⟩ := orient harc' endY'
    have h12 : M ∩ M' = {z} := by
      apply subset_antisymm
      · rintro u ⟨hu, hu'⟩
        by_contra hun
        exact A' (hdiff ▸ hMs ⟨hu, hun⟩) (hdiff' ▸ hMs' ⟨hu', hun⟩)
      · rintro u rfl; exact ⟨hMa.left_mem, hMa'.left_mem⟩
    exact hnt z hzE m m' M M' hMa hMa' h12 (union_subset (hMY.trans hsub) (hMY'.trans hsub'))
      ((hdiff ▸ hMs).trans hO) ((hdiff' ▸ hMs').trans hO')
  · rintro z ⟨hzh, hzI⟩
    have hzE : z ∉ E := fun h' => disjoint_left.mp hIJ hzI h'.2
    rw [← hCu] at hzh
    obtain ⟨f, hf, s, rfl⟩ : ∃ f, (f = f₁ ∨ f = f₂) ∧ z ∈ range f := by
      rcases hzh with h' | h'
      exacts [⟨f₁, Or.inl rfl, h'⟩, ⟨f₂, Or.inr rfl, h'⟩]
    have hT : (f ⁻¹' E).Finite := hfin.preimage (hemb hf).1.injective.injOn
    have h0 : (0 : unitInterval) ∈ f ⁻¹' E := by
      rcases hf with e | e <;> subst f
      · show f₁ 0 ∈ E; rw [hf₁0]; exact hp₀
      · show f₂ 0 ∈ E; rw [hf₂0]; exact hp₀
    have h1' : (1 : unitInterval) ∈ f ⁻¹' E := by
      rcases hf with e | e <;> subst f
      · show f₁ 1 ∈ E; rw [hf₁1]; exact hp₁
      · show f₂ 1 ∈ E; rw [hf₂1]; exact hp₁
    obtain ⟨a, ha, b, hb, hab, hT', hs⟩ := exists_piece hT h0 h1' hzE
    have hmem : f s ∈ f '' Icc a b := ⟨s, Ioo_subset_Icc_self hs, rfl⟩
    refine ⟨f '' Icc a b, ⟨?_, f s, hmem, hzI⟩, hmem⟩
    rcases hf with e | e <;> subst f
    · exact Or.inl ⟨a, ha, b, hb, hab, hT', rfl⟩
    · exact Or.inr ⟨a, ha, b, hb, hab, hT', rfl⟩

end Extract

end HPC.Moore
