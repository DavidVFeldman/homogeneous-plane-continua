import HPC.Moore.M41Side

/-!
# Theorem 41, Case II: replacing the chords on one arc of `J₂` (batch 140, item A)

`half_replace`: let `f` parametrize an arc of `J₂` whose first end `O` is a limit point of the
unbounded component `V` and is not on `J₁`. The *chords* over `f` are the arcs `Z` of `J₁` lying in
`V'` with ends `f u`, `f v` (`u < v`) and open arc without `J₂`. Replacing each `f [u, v]` by its
chord gives an arc from `f 0` to `f 1` (`Gen.arc_replace`): the intervals `(u, v)` are disjoint
because no point of `f (u, v)` is a limit point of `V` (`pocket`), the open arcs of the chords are
disjoint (`chord_subset`), and the chords form a null family (`chords_null`, Theorem A of 1919).
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

namespace Gen

theorem image_Icc_diff_ends {X : Type*} {f : unitInterval → X} (hf : Function.Injective f)
    {u v : unitInterval} : f '' Icc u v \ {f u, f v} = f '' Ioo u v := by
  ext z
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hz⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact ⟨t, ⟨lt_of_le_of_ne ht.1 fun e => hz.1 (by rw [e]),
      lt_of_le_of_ne ht.2 fun e => hz.2 (by rw [e])⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, Ioo_subset_Icc_self ht, rfl⟩, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun e => ht.1.ne' (hf e), fun e => ht.2.ne (hf e)⟩

/-- Two open intervals that meet, neither containing an end of the other, are equal. -/
theorem Ioo_eq_of_not_disjoint {α : Type*} [LinearOrder α] {a b c d : α}
    (h : ¬ Disjoint (Ioo a b) (Ioo c d)) (hc : c ∉ Ioo a b) (hd : d ∉ Ioo a b)
    (ha : a ∉ Ioo c d) (hb : b ∉ Ioo c d) : a = c ∧ b = d := by
  obtain ⟨t, ⟨hat, htb⟩, ⟨hct, htd⟩⟩ := not_disjoint_iff.mp h
  constructor
  · rcases lt_trichotomy a c with h1 | h1 | h1
    · exact absurd ⟨h1, hct.trans htb⟩ hc
    · exact h1
    · exact absurd ⟨h1, hat.trans htd⟩ ha
  · rcases lt_trichotomy b d with h1 | h1 | h1
    · exact absurd ⟨hct.trans htb, h1⟩ hb
    · exact h1
    · exact absurd ⟨hat.trans htd, h1⟩ hd

end Gen

variable {S : Type*} {σ : Space S}

section HalfGen

variable (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h51 : Space.Axiom5₁ (S := S))
include h1 h3 h4 h51

/-- **Replacing the chords over one arc of a closed curve `J₂`**, given the pocket property: the
chords are the arcs of `J₁` in `V'` with ends `f u`, `f v` (`u < v`) and open arc in a set `U`
missing `J₂`, and no point of `f (u, v)` is a limit point of `V`. *Axioms used: 1, 3, 4, 5₁.* -/
theorem half_replace_gen {J₁ J₂ U V : Set S} (hJ₁ : σ.IsSCC J₁) (hJ₂U : Disjoint J₂ U)
    {f : unitInterval → S} (hf : @IsEmbedding _ _ _ σ.topology f) (hfJ : range f ⊆ J₂)
    (hJ₁V : ¬ J₁ ⊆ @closure S σ.topology V)
    (hpock' : ∀ u v Z, u < v → @TArc S σ.topology (f u) (f v) Z → Z ⊆ J₁ →
      Z ⊆ @closure S σ.topology V → Z \ {f u, f v} ⊆ U →
      Disjoint (f '' Ioo u v) (@closure S σ.topology V)) :
    letI := σ.topology
    ∃ D, TArc (f 0) (f 1) D ∧
      D ⊆ range f ∪ ⋃₀ {Z | ∃ u v : unitInterval, u < v ∧ TArc (f u) (f v) Z ∧ Z ⊆ J₁ ∧
        Z ⊆ closure V ∧ Z \ {f u, f v} ⊆ U} ∧
      (∀ Z u v, u < v → TArc (f u) (f v) Z → Z ⊆ J₁ → Z ⊆ closure V →
        Z \ {f u, f v} ⊆ U → Z ⊆ D) ∧
      closure V ∩ range f ⊆ D := by
  letI := σ.topology
  haveI := t2Space h1
  have hJ₂E := hJ₂U
  set P : unitInterval × unitInterval × Set S → Prop := fun x =>
    x.1 < x.2.1 ∧ TArc (f x.1) (f x.2.1) x.2.2 ∧ x.2.2 ⊆ J₁ ∧ x.2.2 ⊆ closure V ∧
      x.2.2 \ {f x.1, f x.2.1} ⊆ U with hP
  have hpock : ∀ x : {x // P x}, Disjoint (f '' Ioo x.1.1 x.1.2.1) (closure V) := by
    rintro ⟨⟨u, v, Z⟩, huv, hZ, hZJ, hZV, hZE⟩
    exact hpock' u v Z huv hZ hZJ hZV hZE
  -- ends of chords are limit points of `V`, so they are in no interval
  have hends : ∀ x y : {x // P x}, x.1.1 ∉ Ioo y.1.1 y.1.2.1 ∧ x.1.2.1 ∉ Ioo y.1.1 y.1.2.1 := by
    intro x y
    constructor
    · intro h
      exact disjoint_left.mp (hpock y) (mem_image_of_mem f h) (x.2.2.2.2.1 x.2.2.1.left_mem)
    · intro h
      exact disjoint_left.mp (hpock y) (mem_image_of_mem f h) (x.2.2.2.2.1 x.2.2.1.right_mem)
  have hZJ₂ : ∀ x : {x // P x}, ∀ z ∈ x.1.2.2, z ∈ J₂ → z = f x.1.1 ∨ z = f x.1.2.1 := by
    intro x z hz hzJ
    by_contra h
    push_neg at h
    exact disjoint_left.mp hJ₂E hzJ (x.2.2.2.2.2 ⟨hz, by simp [h.1, h.2]⟩)
  have hext : ∀ x y : {x // P x}, x.1.1 = y.1.1 → x.1.2.1 = y.1.2.1 → x.1.2.2 = y.1.2.2 →
      x = y := by
    rintro ⟨⟨u, v, Z⟩, hx⟩ ⟨⟨u', v', Z'⟩, hy⟩ h1' h2' h3'
    simp only at h1' h2' h3'
    subst h1' h2' h3'
    rfl
  have hdisj : ∀ x y : {x // P x}, x ≠ y →
      Disjoint (Ioo x.1.1 x.1.2.1) (Ioo y.1.1 y.1.2.1) := by
    intro x y hxy
    by_contra hnd
    obtain ⟨e1, e2⟩ := Ioo_eq_of_not_disjoint hnd (hends y x).1 (hends y x).2 (hends x y).1
      (hends x y).2
    refine hxy (hext x y e1 e2 ?_)
    by_contra hne
    have hZy : σ.IsArc (f x.1.1) (f x.1.2.1) y.1.2.2 := by
      rw [isArc_iff_tarc h1 h3 h4 h51, e1, e2]; exact y.2.2.1
    obtain ⟨-, hu⟩ := two_arcs_eq h1 h3 h4 h51 hJ₁ ((isArc_iff_tarc h1 h3 h4 h51).mpr x.2.2.1)
      hZy x.2.2.2.1 y.2.2.2.1 hne
    exact hJ₁V (hu ▸ union_subset x.2.2.2.2.1 y.2.2.2.2.1)
  have hZdisj : ∀ x y : {x // P x}, x ≠ y →
      Disjoint (x.1.2.2 \ {f x.1.1, f x.1.2.1}) (y.1.2.2 \ {f y.1.1, f y.1.2.1}) := by
    intro x y hxy
    by_contra hnd
    rw [not_disjoint_iff_nonempty_inter] at hnd
    have hxJ : Disjoint (x.1.2.2 \ {f x.1.1, f x.1.2.1}) J₂ := hJ₂E.symm.mono_left x.2.2.2.2.2
    have hyJ : Disjoint (y.1.2.2 \ {f y.1.1, f y.1.2.1}) J₂ := hJ₂E.symm.mono_left y.2.2.2.2.2
    have hfx : ∀ t, f t ∈ J₂ := fun t => hfJ (mem_range_self t)
    have s1 := chord_subset h1 h3 h4 h51 hJ₁ x.2.2.1 y.2.2.1 x.2.2.2.1 y.2.2.2.1 (hfx _) (hfx _)
      hyJ hnd
    have s2 := chord_subset h1 h3 h4 h51 hJ₁ y.2.2.1 x.2.2.1 y.2.2.2.1 x.2.2.2.1 (hfx _) (hfx _)
      hxJ (by rwa [inter_comm])
    have hZ : x.1.2.2 = y.1.2.2 := subset_antisymm s2 s1
    have hu := hZJ₂ x _ (s1 y.2.2.1.left_mem) (hfx _)
    have hv := hZJ₂ x _ (s1 y.2.2.1.right_mem) (hfx _)
    have hxlt := x.2.1
    have hylt := y.2.1
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact absurd (hf.injective (hu.trans hv.symm)) hylt.ne
    · exact hxy (hext x y (hf.injective hu).symm (hf.injective hv).symm hZ)
    · have e1 := hf.injective hu
      have e2 := hf.injective hv
      rw [e1, e2] at hylt
      exact absurd hylt (not_lt.mpr hxlt.le)
    · exact absurd (hf.injective (hu.trans hv.symm)) hylt.ne
  haveI := metrizable h1 h3 h51
  letI := TopologicalSpace.metrizableSpaceMetric S
  have hnull := chords_null h1 h3 h4 h51 hJ₁ (fun x : {x // P x} => f x.1.1)
    (fun x => f x.1.2.1) (fun x => x.1.2.2) (fun x => x.2.2.1) (fun x => x.2.2.2.1) hZdisj
  obtain ⟨D, hD, hDsub, hZD, hfD⟩ := arc_replace hf (fun x : {x // P x} => x.1.1)
    (fun x => x.1.2.1) (fun x => x.1.2.2) (fun x => x.2.1) (fun x => x.2.2.1)
    (fun x => hJ₂E.symm.mono x.2.2.2.2.2 hfJ) hdisj hZdisj hnull
  refine ⟨D, hD, ?_, ?_, ?_⟩
  · intro z hz
    rcases hDsub hz with h | h
    · exact Or.inl h
    · obtain ⟨x, hx⟩ := mem_iUnion.mp h
      exact Or.inr ⟨x.1.2.2, ⟨x.1.1, x.1.2.1, x.2⟩, hx⟩
  · intro Z u v huv hZ hZJ hZV hZE
    exact hZD ⟨(u, v, Z), huv, hZ, hZJ, hZV, hZE⟩
  · rintro z ⟨hzV, t, rfl⟩
    refine hfD t fun x ht => ?_
    exact disjoint_left.mp (hpock x) (mem_image_of_mem f ht) hzV

end HalfGen

section Half

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h7 h8

/-- **Replacing the chords over one arc of `J₂`** (Theorem 41). *Axioms used: 1–5, 7, 8.* -/
theorem half_replace {J₁ J₂ I₂ V : Set S} (hJ₁ : σ.IsSCC J₁) (hI₂ : σ.IsInteriorOf J₂ I₂)
    {f : unitInterval → S} (hf : @IsEmbedding _ _ _ σ.topology f) (hfJ : range f ⊆ J₂)
    (hV : @IsPreconnected S σ.topology V)
    (hVnc : ¬ @IsCompact S σ.topology (@closure S σ.topology V))
    (hVJ₁ : Disjoint V J₁) (hVJ₂ : Disjoint V J₂) (hf0V : f 0 ∈ @closure S σ.topology V)
    (hf0J : f 0 ∉ J₁) (hJ₁V : ¬ J₁ ⊆ @closure S σ.topology V) :
    letI := σ.topology
    ∃ D, TArc (f 0) (f 1) D ∧
      D ⊆ range f ∪ ⋃₀ {Z | ∃ u v : unitInterval, u < v ∧ TArc (f u) (f v) Z ∧ Z ⊆ J₁ ∧
        Z ⊆ closure V ∧ Z \ {f u, f v} ⊆ (closure I₂)ᶜ} ∧
      (∀ Z u v, u < v → TArc (f u) (f v) Z → Z ⊆ J₁ → Z ⊆ closure V →
        Z \ {f u, f v} ⊆ (closure I₂)ᶜ → Z ⊆ D) ∧
      closure V ∩ range f ⊆ D := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, -, -, hfr₂, -, -, -, -, -, -, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI₂
  have hJ₂E : Disjoint J₂ (closure I₂)ᶜ := by
    rw [disjoint_compl_right_iff_subset, ← hfr₂]; exact frontier_subset_closure
  refine half_replace_gen h1 h3 h4 h51 hJ₁ hJ₂E hf hfJ hJ₁V ?_
  intro u v Z huv hZ hZJ hZV hZE
  have hu0 : 0 < u := lt_of_le_of_ne nonneg' fun e => hf0J (e ▸ hZJ hZ.left_mem)
  have hOC : f 0 ∉ f '' Icc u v := by
    rintro ⟨t, ht, e⟩
    have := hf.injective e
    subst this
    exact absurd ht.1 (not_le.mpr hu0)
  have := pocket h1 h2 h3 h4 h5 h7 h8 hI₂ hZ hZE (TArc.image_Icc hf huv)
    ((image_subset_range _ _).trans hfJ) (hfJ (mem_range_self 0)) hOC hV hVnc
    (hVJ₁.mono_right hZJ) hVJ₂ hf0V
  rwa [image_Icc_diff_ends hf.injective] at this

end Half

end HPC.Moore
