import HPC.Hagopian.Hagopian84D
import HPC.Moore.M19DExtract
import HPC.Plane.Ingram68Core

/-!
# Jones 1975 I (batch 189), part 1: the setting, an arc toolkit, Jones (c)

Commission 189 §1–§2.2 (skeleton `Jones75A.lean` §1–§2, split). Source: F. B. Jones, *Use of a new
technique in homogeneous continua*, Houston J. Math. 1 (1975), 57–61.

* `JonesSetting`, `jonesSetting_of_plane` (§1);
* a toolkit for arcs inside arcs (`sub_arc_param`: an arc inside an embedded `[0, 1]` is a
  parameter interval, with matching end points);
* **Jones (c)** (`JonesSetting.union_arc`, `JonesSetting.nested`), from hereditary unicoherence
  (`JonesSetting.inter_isPreconnected`) and atriodicity (`JonesSetting.no_three_arms`);
* every point is an interior point of an arc (`JonesSetting.exists_arc_through`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen unitInterval

/-! ## §1. The setting -/

/-- The hypotheses used by Jones 1975 (a)–(c), (d), (f) and by §2–§4 below: homogeneous,
hereditarily unicoherent, atriodic, and containing an arc. A bundle of hypotheses, not open work;
non-vacuity note required all the same. -/
structure JonesSetting (Y : Type*) [MetricSpace Y] [CompactSpace Y] : Prop where
  hom : IsHomogeneous Y
  hu : IsHereditarilyUnicoherent (univ : Set Y)
  atr : IsAtriodic (univ : Set Y)
  arc : ∃ (a b : Y) (A : Set Y), TArc a b A

section PlaneInstance

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§1**: a homogeneous indecomposable plane continuum containing an arc is a `JonesSetting`
(Jones's (a) and (b) are `hagopian75_lemma1`). -/
theorem jonesSetting_of_plane (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (hα : ∃ (a b : M) (A : Set M), TArc a b A) : JonesSetting M :=
  ⟨hX, (hagopian75_lemma1 hX hi).2, (hagopian75_lemma1 hX hi).1, hα⟩

end PlaneInstance

/-! ## An arc toolkit -/

section ArcToolkit

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem Icc_zero_one_I : Icc (0 : I) 1 = univ := eq_univ_of_forall fun _ => ⟨nonneg', le_one'⟩

omit [TopologicalSpace X] [T2Space X] in
theorem image_Icc_zero_one {f : I → X} : f '' Icc 0 1 = range f := by
  rw [Icc_zero_one_I, image_univ]

/-- A closed preconnected nonempty subset of `[0, 1]` is an interval. -/
theorem unitInterval_eq_Icc_of_closed {T : Set I} (hc : IsClosed T) (hp : IsPreconnected T)
    (hne : T.Nonempty) : T = Icc (sInf T) (sSup T) := by
  apply Subset.antisymm
  · intro u hu
    exact ⟨csInf_le (OrderBot.bddBelow T) hu, le_csSup (OrderTop.bddAbove T) hu⟩
  · exact hp.Icc_subset (hc.csInf_mem hne (OrderBot.bddBelow T))
      (hc.csSup_mem hne (OrderTop.bddAbove T))

theorem image_Icc_inter_image_Icc {Z : Type*} {f : I → Z} (hf : Function.Injective f) {s t u : I}
    (hst : s ≤ t) (htu : t ≤ u) : f '' Icc s t ∩ f '' Icc t u = {f t} := by
  rw [← image_inter hf, Icc_inter_Icc, max_eq_right hst, min_eq_left htu, Icc_self,
    image_singleton]

omit [T2Space X] in
/-- The range of an embedding of `[0, 1]` is an arc. -/
theorem tarc_range {f : I → X} (hf : IsEmbedding f) : TArc (f 0) (f 1) (range f) :=
  ⟨fun e => by simpa using congrArg Subtype.val (hf.injective e), f, hf, rfl, rfl, rfl⟩

omit [T2Space X] in
/-- A homeomorphism carries arcs to arcs. -/
theorem _root_.HPC.Moore.Gen.TArc.image_homeomorph {A B : X} {C : Set X} (h : TArc A B C) (g : X ≃ₜ X) :
    TArc (g A) (g B) (g '' C) := by
  obtain ⟨hAB, f, hf, rfl, rfl, rfl⟩ := h
  exact ⟨fun e => hAB (g.injective e), g ∘ f, g.isEmbedding.comp hf, range_comp _ _, rfl, rfl⟩

omit [T2Space X] in
/-- A point of `f [s, t]` whose removal leaves a preconnected set is an end point. -/
theorem endpoint_of_preconnected {f : I → X} (hf : IsEmbedding f) {s t u : I} (hu : u ∈ Icc s t)
    (hpc : IsPreconnected (f '' Icc s t \ {f u})) : u = s ∨ u = t := by
  by_contra hne
  push_neg at hne
  rw [← image_singleton, ← image_diff hf.injective, hf.isInducing.isPreconnected_image] at hpc
  have hst : s ≤ t := hu.1.trans hu.2
  have := hpc.Icc_subset (a := s) (b := t) ⟨left_mem_Icc.2 hst, fun h => hne.1 (Eq.symm h)⟩
    ⟨right_mem_Icc.2 hst, fun h => hne.2 (Eq.symm h)⟩
  exact (this hu).2 rfl

/-- **Arcs inside an arc.** An arc `S` inside the range of an embedding `f` of `[0, 1]` is
`f [s, t]` for some `s < t`, with its end points at `f s` and `f t`. -/
theorem sub_arc_param {f : I → X} (hf : IsEmbedding f) {S : Set X} {p q : X}
    (hS : TArc p q S) (hSf : S ⊆ range f) :
    ∃ s t : I, s < t ∧ S = f '' Icc s t ∧ ((f s = p ∧ f t = q) ∨ (f s = q ∧ f t = p)) := by
  set T := f ⁻¹' S with hT
  have himg : f '' T = S := image_preimage_eq_of_subset hSf
  have hTc : IsClosed T := hS.isClosed.preimage hf.continuous
  have hTp : IsPreconnected T := by
    rw [← hf.isInducing.isPreconnected_image, himg]; exact hS.isPreconnected
  have hTne : T.Nonempty := by
    obtain ⟨u, hu⟩ := hSf hS.left_mem
    exact ⟨u, show f u ∈ S from hu ▸ hS.left_mem⟩
  have hTeq := unitInterval_eq_Icc_of_closed hTc hTp hTne
  have hSeq : S = f '' Icc (sInf T) (sSup T) := by rw [← himg, ← hTeq]
  have key : ∀ r ∈ S, IsPreconnected (S \ {r}) → r = f (sInf T) ∨ r = f (sSup T) := by
    intro r hr hpc
    rw [hSeq] at hr hpc
    obtain ⟨u, hu, rfl⟩ := hr
    rcases endpoint_of_preconnected hf hu hpc with h | h <;> simp [h]
  have hp := key p hS.left_mem hS.symm.isPreconnected_diff_right
  have hq := key q hS.right_mem hS.isPreconnected_diff_right
  have hle : sInf T ≤ sSup T := csInf_le_csSup (OrderBot.bddBelow T) (OrderTop.bddAbove T) hTne
  have hpq := hS.ne
  refine ⟨sInf T, sSup T, lt_of_le_of_ne hle fun e => ?_, hSeq, ?_⟩
  · rw [e] at hp hq
    rcases hp with h | h <;> rcases hq with h' | h' <;> exact hpq (h.trans h'.symm)
  · rcases hp with h | h <;> rcases hq with h' | h'
    · exact absurd (h.trans h'.symm) hpq
    · exact Or.inl ⟨h.symm, h'.symm⟩
    · exact Or.inr ⟨h'.symm, h.symm⟩
    · exact absurd (h.trans h'.symm) hpq

theorem symm_image_Icc (s t : I) : σ '' Icc s t = Icc (σ t) (σ s) := by
  ext u
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨v, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩ <;> rw [← Subtype.coe_le_coe] at * <;> simp only [coe_symm_eq] <;> linarith
  · rintro ⟨h1, h2⟩
    refine ⟨σ u, ⟨?_, ?_⟩, symm_symm u⟩ <;> rw [← Subtype.coe_le_coe] at * <;>
      simp only [coe_symm_eq] at * <;> linarith

theorem range_comp_symm {Z : Type*} (g : I → Z) : range (g ∘ σ) = range g := by
  rw [range_comp, symm_involutive.surjective.range_eq, image_univ]

end ArcToolkit

/-! ## §2.1. Jones (c) -/

section General

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]

omit [CompactSpace Y] in
theorem tarc_isContinuum {a b : Y} {A : Set Y} (h : TArc a b A) : Fold.Q78.IsContinuum A :=
  ⟨h.isCompact, ⟨a, h.left_mem⟩, h.isPreconnected⟩

/-- Two intersecting arcs meet in a connected set (hereditary unicoherence). -/
theorem JonesSetting.inter_isPreconnected (S : JonesSetting Y) {A B : Set Y} {a b a' b' : Y}
    (hA : TArc a b A) (hB : TArc a' b' B) (hAB : (A ∩ B).Nonempty) : IsPreconnected (A ∩ B) := by
  have hc := HPC.Plane.isContinuum_union (tarc_isContinuum hA) (tarc_isContinuum hB) hAB
  have hnt : (A ∪ B).Nontrivial := ⟨a, Or.inl hA.left_mem, b, Or.inl hA.right_mem, hA.ne⟩
  exact (S.hu (A ∪ B) (subset_univ _) hc hnt A B (tarc_isContinuum hA) (tarc_isContinuum hB)
    rfl).isPreconnected

/-- No three arcs through a point `p` pairwise meet only in `p` (atriodicity). -/
theorem JonesSetting.no_three_arms (S : JonesSetting Y) {p : Y} {X₁ X₂ X₃ : Set Y}
    {u₁ v₁ u₂ v₂ u₃ v₃ : Y} (h₁ : TArc u₁ v₁ X₁) (h₂ : TArc u₂ v₂ X₂) (h₃ : TArc u₃ v₃ X₃)
    (p₁ : p ∈ X₁) (p₂ : p ∈ X₂) (p₃ : p ∈ X₃)
    (o₁₂ : X₁ ∩ X₂ ⊆ {p}) (o₁₃ : X₁ ∩ X₃ ⊆ {p}) (o₂₃ : X₂ ∩ X₃ ⊆ {p}) : False := by
  have hN : Fold.Q78.IsContinuum ({p} : Set Y) := ⟨isCompact_singleton, isConnected_singleton⟩
  have nt : ∀ {u v : Y} {X : Set Y}, TArc u v X → ¬ X ⊆ {p} := fun h hX =>
    h.ne ((hX h.left_mem).trans (hX h.right_mem).symm)
  exact not_core_of_isAtriodic S.atr hN (tarc_isContinuum h₁) (tarc_isContinuum h₂)
    (tarc_isContinuum h₃) (subset_univ _) (subset_univ _) (subset_univ _) (subset_univ _)
    ⟨p, p₁, rfl⟩ ⟨p, p₂, rfl⟩ ⟨p, p₃, rfl⟩ o₁₂ o₁₃ o₂₃ (nt h₁) (nt h₂) (nt h₃)

omit [CompactSpace Y] in
/-- The intersection of two arcs, in the parameters of the first. -/
theorem inter_param {f g : I → Y} (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hpc : IsPreconnected (range f ∩ range g)) (hne : (range f ∩ range g).Nonempty) :
    range f ∩ range g = f '' Icc (sInf (f ⁻¹' (range f ∩ range g)))
      (sSup (f ⁻¹' (range f ∩ range g))) := by
  set C := range f ∩ range g
  have hCc : IsClosed C :=
    (isCompact_range hf.continuous).isClosed.inter (isCompact_range hg.continuous).isClosed
  have hTimg : f '' (f ⁻¹' C) = C := image_preimage_eq_of_subset inter_subset_left
  have hTp : IsPreconnected (f ⁻¹' C) := by
    rw [← hf.isInducing.isPreconnected_image, hTimg]; exact hpc
  have hTne : (f ⁻¹' C).Nonempty := by
    obtain ⟨z, ⟨u, rfl⟩, hz⟩ := hne; exact ⟨u, ⟨mem_range_self _, hz⟩⟩
  conv_lhs => rw [← hTimg, unitInterval_eq_Icc_of_closed (hCc.preimage hf.continuous) hTp hTne]

/-- **§2.1, Jones (c), second half** (\"where they have a common end point and intersect somewhere
else, then one of them is a subset of the other\"). -/
theorem JonesSetting.nested (S : JonesSetting Y) {A B : Set Y} {a b c : Y} (hA : TArc a b A)
    (hB : TArc a c B) (hAB : (A ∩ B).Nontrivial) : A ⊆ B ∨ B ⊆ A := by
  have hpc := S.inter_isPreconnected hA hB hAB.nonempty
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := hA
  obtain ⟨-, g, hg, rfl, hg0, rfl⟩ := hB
  have hCeq := inter_param hf hg hpc hAB.nonempty
  set T := f ⁻¹' (range f ∩ range g)
  have h0T : (0 : I) ∈ T := ⟨mem_range_self _, ⟨0, hg0⟩⟩
  have hs : sInf T = 0 := le_antisymm (csInf_le (OrderBot.bddBelow T) h0T) nonneg'
  rw [hs] at hCeq
  set t := sSup T
  have ht0 : 0 < t := by
    refine lt_of_le_of_ne nonneg' fun e => ?_
    rw [← e, Icc_self, image_singleton] at hCeq
    rw [hCeq] at hAB
    exact not_nontrivial_singleton hAB
  have hCarc : TArc (f 0) (f t) (range f ∩ range g) := hCeq ▸ TArc.image_Icc hf ht0
  obtain ⟨s', t', hst', hC', hend⟩ := sub_arc_param hg hCarc inter_subset_right
  have hs' : s' = 0 ∧ g t' = f t := by
    rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hg.injective (h1.trans hg0.symm), h2⟩
    · have : t' = 0 := hg.injective (h2.trans hg0.symm)
      exact absurd hst' (by rw [this]; exact not_lt.mpr nonneg')
  obtain ⟨rfl, hgt⟩ := hs'
  by_cases ht1 : t = 1
  · left
    rw [← image_Icc_zero_one, ← ht1, ← hCeq]; exact inter_subset_right
  by_cases ht1' : t' = 1
  · right
    rw [← image_Icc_zero_one (f := g), ← ht1', ← hC']; exact inter_subset_left
  exfalso
  have ht1 : t < 1 := lt_of_le_of_ne le_one' ht1
  have ht1' : t' < 1 := lt_of_le_of_ne le_one' ht1'
  refine S.no_three_arms (p := f t) (TArc.image_Icc hf ht1) (TArc.image_Icc hg ht1') hCarc
    ⟨t, ⟨le_rfl, le_one'⟩, rfl⟩ (hgt ▸ ⟨t', ⟨le_rfl, le_one'⟩, rfl⟩) hCarc.right_mem ?_ ?_ ?_
  · intro z ⟨hz1, hz2⟩
    have hz : z ∈ f '' Icc 0 t :=
      hCeq ▸ ⟨image_subset_range _ _ hz1, image_subset_range _ _ hz2⟩
    rw [← image_Icc_inter_image_Icc hf.injective ht0.le ht1.le]
    exact ⟨hz, hz1⟩
  · rw [hCeq, inter_comm, image_Icc_inter_image_Icc hf.injective ht0.le ht1.le]
  · rw [hC', inter_comm, image_Icc_inter_image_Icc hg.injective hst'.le ht1'.le, hgt]

omit [CompactSpace Y] in
/-- Gluing: `range f ∩ range g = f [s, 1]` with `f s = g 0`. -/
theorem glue_case {f g : I → Y} (hf : IsEmbedding f) (hg : IsEmbedding g) {s : I} (hs : 0 < s)
    (hC : range f ∩ range g = f '' Icc s 1) (h0 : f s = g 0) :
    TArc (f 0) (g 1) (range f ∪ range g) := by
  have h1 := TArc.image_Icc hf hs
  have h2 : TArc (f s) (g 1) (range g) := h0 ▸ tarc_range hg
  have hint : f '' Icc 0 s ∩ range g = {f s} := by
    apply Subset.antisymm
    · intro z ⟨hz1, hz2⟩
      have hz : z ∈ f '' Icc s 1 := hC ▸ ⟨image_subset_range _ _ hz1, hz2⟩
      rw [← image_Icc_inter_image_Icc hf.injective hs.le le_one']
      exact ⟨hz1, hz⟩
    · rintro _ rfl; exact ⟨⟨s, ⟨hs.le, le_rfl⟩, rfl⟩, h0 ▸ mem_range_self _⟩
  have := h1.union h2 hint
  convert this using 1
  apply Subset.antisymm
  · rintro z (⟨u, -, rfl⟩ | hz)
    · by_cases hu : u ≤ s
      · exact Or.inl ⟨u, ⟨nonneg', hu⟩, rfl⟩
      · have : f u ∈ f '' Icc s 1 := ⟨u, ⟨(not_le.mp hu).le, le_one'⟩, rfl⟩
        rw [← hC] at this; exact Or.inr this.2
    · exact Or.inr hz
  · exact union_subset_union (image_subset_range _ _) subset_rfl

theorem JonesSetting.union_arc_aux (S : JonesSetting Y) {f g : I → Y} (hf : IsEmbedding f)
    (hg : IsEmbedding g) {s t s' t' : I} (hst : s < t) (hst' : s' < t')
    (hC : range f ∩ range g = f '' Icc s t) (hC' : range f ∩ range g = g '' Icc s' t')
    (h1 : f s = g s') (h2 : f t = g t') : ∃ p q : Y, TArc p q (range f ∪ range g) := by
  have hCf : TArc (f s) (f t) (f '' Icc s t) := TArc.image_Icc hf hst
  have hend : t = 1 ∨ t' = 1 := by
    by_contra h
    push_neg at h
    have ht1 : t < 1 := lt_of_le_of_ne le_one' h.1
    have ht1' : t' < 1 := lt_of_le_of_ne le_one' h.2
    refine S.no_three_arms (p := f t) (TArc.image_Icc hf ht1) (TArc.image_Icc hg ht1') hCf
      ⟨t, ⟨le_rfl, le_one'⟩, rfl⟩ (h2 ▸ ⟨t', ⟨le_rfl, le_one'⟩, rfl⟩) hCf.right_mem ?_ ?_ ?_
    · intro z ⟨hz1, hz2⟩
      have hz : z ∈ f '' Icc s t :=
        hC ▸ ⟨image_subset_range _ _ hz1, image_subset_range _ _ hz2⟩
      rw [← image_Icc_inter_image_Icc hf.injective hst.le ht1.le]
      exact ⟨hz, hz1⟩
    · rw [inter_comm, image_Icc_inter_image_Icc hf.injective hst.le ht1.le]
    · rw [← hC, hC', inter_comm, image_Icc_inter_image_Icc hg.injective hst'.le ht1'.le, h2]
  have hbeg : s = 0 ∨ s' = 0 := by
    by_contra h
    push_neg at h
    have hs0 : 0 < s := lt_of_le_of_ne nonneg' (Ne.symm h.1)
    have hs0' : 0 < s' := lt_of_le_of_ne nonneg' (Ne.symm h.2)
    refine S.no_three_arms (p := f s) (TArc.image_Icc hf hs0) (TArc.image_Icc hg hs0') hCf
      ⟨s, ⟨nonneg', le_rfl⟩, rfl⟩ (h1 ▸ ⟨s', ⟨nonneg', le_rfl⟩, rfl⟩) hCf.left_mem ?_ ?_ ?_
    · intro z ⟨hz1, hz2⟩
      have hz : z ∈ f '' Icc s t :=
        hC ▸ ⟨image_subset_range _ _ hz1, image_subset_range _ _ hz2⟩
      rw [← image_Icc_inter_image_Icc hf.injective hs0.le hst.le]
      exact ⟨hz1, hz⟩
    · rw [image_Icc_inter_image_Icc hf.injective hs0.le hst.le]
    · rw [← hC, hC', image_Icc_inter_image_Icc hg.injective hs0'.le hst'.le, h1]
  have caseA : t = 1 → s = 0 → ∃ p q : Y, TArc p q (range f ∪ range g) := by
    rintro rfl rfl
    refine ⟨g 0, g 1, ?_⟩
    rw [image_Icc_zero_one] at hC
    rw [union_eq_right.mpr (hC ▸ inter_subset_right : range f ⊆ range g)]
    exact tarc_range hg
  have caseB : t' = 1 → s' = 0 → ∃ p q : Y, TArc p q (range f ∪ range g) := by
    rintro rfl rfl
    refine ⟨f 0, f 1, ?_⟩
    rw [image_Icc_zero_one] at hC'
    rw [union_eq_left.mpr (hC' ▸ inter_subset_left : range g ⊆ range f)]
    exact tarc_range hf
  rcases hend with ht | ht <;> rcases hbeg with hs | hs
  · exact caseA ht hs
  · by_cases hs0 : s = 0
    · exact caseA ht hs0
    · subst ht hs
      exact ⟨_, _, glue_case hf hg (lt_of_le_of_ne nonneg' (Ne.symm hs0)) hC h1⟩
  · by_cases hs0 : s' = 0
    · exact caseB ht hs0
    · subst ht hs
      refine ⟨_, _, union_comm (range g) (range f) ▸
        glue_case hg hf (lt_of_le_of_ne nonneg' (Ne.symm hs0)) (inter_comm (range f) _ ▸ hC')
        h1.symm⟩
  · exact caseB ht hs

/-- **§2.1, Jones (c), first half** (p. 57: \"If two arcs `A` and `B` of `M` intersect then
`A ∪ B` is an arc\"). -/
theorem JonesSetting.union_arc (S : JonesSetting Y) {A B : Set Y} {a b a' b' : Y}
    (hA : TArc a b A) (hB : TArc a' b' B) (hAB : (A ∩ B).Nonempty) :
    ∃ p q : Y, TArc p q (A ∪ B) := by
  have hpc := S.inter_isPreconnected hA hB hAB
  obtain ⟨-, f, hf, rfl, -, -⟩ := hA
  obtain ⟨-, g, hg, rfl, -, -⟩ := hB
  have hCeq := inter_param hf hg hpc hAB
  set s := sInf (f ⁻¹' (range f ∩ range g))
  set t := sSup (f ⁻¹' (range f ∩ range g))
  clear_value s t
  rcases lt_or_eq_of_le (show s ≤ t from by
    obtain ⟨z, hz⟩ := hAB
    rw [hCeq] at hz
    obtain ⟨u, hu, -⟩ := hz
    exact hu.1.trans hu.2) with hst | hst
  · have hCarc : TArc (f s) (f t) (range f ∩ range g) := hCeq ▸ TArc.image_Icc hf hst
    obtain ⟨s', t', hst', hC', hend⟩ := sub_arc_param hg hCarc inter_subset_right
    rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact S.union_arc_aux hf hg hst hst' hCeq hC' h1.symm h2.symm
    · have hg' : IsEmbedding (g ∘ σ) := hg.comp (Homeomorph.isEmbedding symmHomeomorph)
      have hσ : σ t' < σ s' := by
        rw [← Subtype.coe_lt_coe] at hst' ⊢; simp only [coe_symm_eq]; linarith
      have := S.union_arc_aux hf hg' hst hσ (by rw [range_comp_symm]; exact hCeq)
        (by rw [range_comp_symm, hC', image_comp, symm_image_Icc, symm_symm, symm_symm])
        (by simp [h2]) (by simp [h1])
      rwa [range_comp_symm] at this
  · -- the intersection is a point
    rw [← hst, Icc_self, image_singleton] at hCeq
    have hp : f s ∈ range g := (hCeq ▸ mem_singleton (f s) : f s ∈ range f ∩ range g).2
    obtain ⟨u, hu⟩ := hp
    have hsub : ∀ {X₁ X₂ : Set Y}, X₁ ⊆ range f → X₂ ⊆ range g → X₁ ∩ X₂ ⊆ {f s} :=
      fun h1 h2 => hCeq ▸ inter_subset_inter h1 h2
    have hfa : f s ∈ f '' Icc 0 s := ⟨s, ⟨nonneg', le_rfl⟩, rfl⟩
    have hfb : f s ∈ f '' Icc s 1 := ⟨s, ⟨le_rfl, le_one'⟩, rfl⟩
    have hga : f s ∈ g '' Icc 0 u := ⟨u, ⟨nonneg', le_rfl⟩, hu⟩
    have hgb : f s ∈ g '' Icc u 1 := ⟨u, ⟨le_rfl, le_one'⟩, hu⟩
    -- the end-point dichotomies
    have hs01 : s = 0 ∨ s = 1 := by
      by_contra h
      push_neg at h
      have h0 : 0 < s := lt_of_le_of_ne nonneg' (Ne.symm h.1)
      have h1 : s < 1 := lt_of_le_of_ne le_one' h.2
      have hff : f '' Icc 0 s ∩ f '' Icc s 1 ⊆ {f s} :=
        (image_Icc_inter_image_Icc hf.injective h0.le h1.le).subset
      rcases lt_or_eq_of_le (nonneg' : (0 : I) ≤ u) with hu0 | hu0
      · exact S.no_three_arms (TArc.image_Icc hf h0) (TArc.image_Icc hf h1)
          (TArc.image_Icc hg hu0) hfa hfb hga hff (hsub (image_subset_range _ _)
          (image_subset_range _ _)) (hsub (image_subset_range _ _) (image_subset_range _ _))
      · have hu1 : u < 1 := by rw [← hu0]; exact zero_lt_one' I
        exact S.no_three_arms (TArc.image_Icc hf h0) (TArc.image_Icc hf h1)
          (TArc.image_Icc hg hu1) hfa hfb hgb hff (hsub (image_subset_range _ _)
          (image_subset_range _ _)) (hsub (image_subset_range _ _) (image_subset_range _ _))
    have hu01 : u = 0 ∨ u = 1 := by
      by_contra h
      push_neg at h
      have h0 : 0 < u := lt_of_le_of_ne nonneg' (Ne.symm h.1)
      have h1 : u < 1 := lt_of_le_of_ne le_one' h.2
      have hgg : g '' Icc 0 u ∩ g '' Icc u 1 ⊆ {f s} :=
        hu ▸ (image_Icc_inter_image_Icc hg.injective h0.le h1.le).subset
      have hsub' : ∀ {X₂ : Set Y}, X₂ ⊆ range g → range f ∩ X₂ ⊆ {f s} :=
        fun h2 => hsub subset_rfl h2
      exact S.no_three_arms (tarc_range hf) (TArc.image_Icc hg h0) (TArc.image_Icc hg h1)
        (mem_range_self _) hga hgb (hsub' (image_subset_range _ _))
        (hsub' (image_subset_range _ _)) hgg
    have hint : range f ∩ range g = {f s} := hCeq
    have hint' : range g ∩ range f = {f s} := by rw [inter_comm]; exact hCeq
    rcases hs01 with rfl | rfl <;> rcases hu01 with rfl | rfl
    · exact ⟨_, _, (tarc_range hf).symm.union (hu ▸ tarc_range hg) hint⟩
    · exact ⟨_, _, union_comm (range g) _ ▸ (hu ▸ tarc_range hg).union (tarc_range hf) hint'⟩
    · exact ⟨_, _, (tarc_range hf).union (hu ▸ tarc_range hg) hint⟩
    · exact ⟨_, _, (tarc_range hf).union (hu ▸ (tarc_range hg).symm) hint⟩

/-! ## §2.2. Interior points -/

/-- **§2.2**: every point is an interior point of an arc (homogeneity). -/
theorem JonesSetting.exists_arc_through (S : JonesSetting Y) (x : Y) :
    ∃ (a b : Y) (A : Set Y), TArc a b A ∧ x ∈ A ∧ x ≠ a ∧ x ≠ b := by
  obtain ⟨a, b, A, hA⟩ := S.arc
  obtain ⟨hab, f, hf, rfl, rfl, rfl⟩ := hA
  set m : I := ⟨1 / 2, by norm_num, by norm_num⟩
  obtain ⟨h, hm⟩ := S.hom (f m) x
  refine ⟨h (f 0), h (f 1), h '' range f, (tarc_range hf).image_homeomorph h,
    ⟨f m, mem_range_self _, hm⟩, ?_, ?_⟩
  · rw [← hm]; intro e
    have := congrArg Subtype.val (hf.injective (h.injective e))
    norm_num [m] at this
  · rw [← hm]; intro e
    have := congrArg Subtype.val (hf.injective (h.injective e))
    norm_num [m] at this

end General

end HPC.Hagopian
