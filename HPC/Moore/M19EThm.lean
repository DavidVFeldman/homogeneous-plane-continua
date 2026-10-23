import HPC.Moore.M19ESchoenflies

/-!
# Moore 1919, Theorem E (batch 143, item A)

Theorem E follows from the Schoenflies form (`m19_schoenflies_proof`): with `f` the homeomorphism of
the closed unit square onto `ABCDA + interior`, `α₁` is the set of images of the horizontal
segments `p.2 = t` (`0 < t < 1`), from `f (0, t) ∈ AB` to `f (1, t) ∈ CD`, and `α₂` the set of
images of the vertical segments `p.1 = s` (`0 < s < 1`), from `f (s, 1) ∈ BC` to `f (s, 0) ∈ DA`.

The arcs of the rulings `β₁, β₂, …` are lines of the grid from which the homeomorphism is built,
and by construction each is the image of a segment, so that `α₁`, `α₂` play the roles of Moore's
`ᾱ₁ + α₁*`, `ᾱ₂ + α₂*`; this identification is not stated as a theorem here, and Theorem E does not
need it.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

theorem unitInterval_mem_Ioo (t : unitInterval) : t ∈ Ioo (0 : unitInterval) 1 ↔ t ≠ 0 ∧ t ≠ 1 := by
  rw [mem_Ioo, unitInterval.pos_iff_ne_zero, unitInterval.lt_one_iff_ne_one]

/-- **Theorem E from a square.** If `ABCDA + interior` is the image of the closed unit square by an
embedding sending the sides to the sides, then the two families of images of horizontal and of
vertical segments satisfy (1)–(5) of Theorem E. *Axioms used: 1, 3, 4, 5.* -/
theorem theoremE_of_square (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
    {f : unitInterval × unitInterval → S} (hf : @IsEmbedding _ _ _ σ.topology f)
    (hfr : range f = J ∪ I) (hIJ : Disjoint I J) (hJ : sAB ∪ sBC ∪ sCD ∪ sDA = J)
    (fA : f (0, 0) = A) (fB : f (0, 1) = B) (fC : f (1, 1) = C) (fD : f (1, 0) = D)
    (eAB : f '' {p | p.1 = 0} = sAB) (eBC : f '' {p | p.2 = 1} = sBC)
    (eCD : f '' {p | p.1 = 1} = sCD) (eDA : f '' {p | p.2 = 0} = sDA) :
    ∃ α₁ α₂ : Set (S × S × Set S),
      (∀ a ∈ α₁, σ.IsArc a.1 a.2.1 a.2.2 ∧ a.1 ∈ sAB ∧ a.2.1 ∈ sCD ∧
        openArc a.1 a.2.1 a.2.2 ⊆ I) ∧
      (∀ a ∈ α₂, σ.IsArc a.1 a.2.1 a.2.2 ∧ a.1 ∈ sBC ∧ a.2.1 ∈ sDA ∧
        openArc a.1 a.2.1 a.2.2 ⊆ I) ∧
      (∀ P ∈ J \ {A, B, C, D},
        ((∃! a, a ∈ α₁ ∧ (P = a.1 ∨ P = a.2.1)) ∧ ¬ ∃ a ∈ α₂, P = a.1 ∨ P = a.2.1) ∨
        ((∃! a, a ∈ α₂ ∧ (P = a.1 ∨ P = a.2.1)) ∧ ¬ ∃ a ∈ α₁, P = a.1 ∨ P = a.2.1)) ∧
      (∀ P ∈ I, (∃! a, a ∈ α₁ ∧ P ∈ a.2.2) ∧ (∃! a, a ∈ α₂ ∧ P ∈ a.2.2)) ∧
      (∀ a ∈ α₁, ∀ b ∈ α₂, ∃! P, P ∈ a.2.2 ∩ b.2.2) := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have inj := hf.injective
  have mem : ∀ (p : unitInterval × unitInterval) (T : Set (unitInterval × unitInterval)),
      f p ∈ f '' T ↔ p ∈ T := fun p T => inj.mem_set_image
  have hJp : ∀ p, f p ∈ J ↔ (p.1 = 0 ∨ p.2 = 1 ∨ p.1 = 1 ∨ p.2 = 0) := by
    intro p
    rw [← hJ, ← eAB, ← eBC, ← eCD, ← eDA]
    simp only [mem_union, mem, mem_setOf_eq]
    tauto
  have hIp : ∀ p, f p ∈ I ↔ ¬(p.1 = 0 ∨ p.2 = 1 ∨ p.1 = 1 ∨ p.2 = 0) := by
    intro p
    rw [← hJp]
    constructor
    · intro h hJ'; exact disjoint_left.mp hIJ h hJ'
    · intro h
      have : f p ∈ J ∪ I := hfr ▸ mem_range_self p
      exact this.resolve_left h
  have hK : ∀ P ∈ J ∪ I, ∃ p, f p = P := fun P hP => by rw [← hfr] at hP; exact hP
  have z1 : (0 : unitInterval) ≠ 1 := fun h => by
    have := congrArg Subtype.val h; simp at this
  let a1 : unitInterval → S × S × Set S := fun t => (f (0, t), f (1, t), f '' {p | p.2 = t})
  let a2 : unitInterval → S × S × Set S := fun s => (f (s, 1), f (s, 0), f '' {p | p.1 = s})
  have arc1 : ∀ t, TArc (f (0, t)) (f (1, t)) (f '' {p | p.2 = t}) := by
    intro t
    refine ⟨fun e => z1 (congrArg Prod.fst (inj e)), fun s => f (s, t),
      hf.comp (isEmbedding_prodMkLeft t), ?_, rfl, rfl⟩
    ext z
    constructor
    · rintro ⟨s, rfl⟩; exact ⟨(s, t), rfl, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.1, ?_⟩
      simp only [mem_setOf_eq] at hp
      rw [← hp]
  have arc2 : ∀ s, TArc (f (s, 0)) (f (s, 1)) (f '' {p | p.1 = s}) := by
    intro s
    refine ⟨fun e => z1 (congrArg Prod.snd (inj e)), fun u => f (s, u),
      hf.comp (isEmbedding_prodMkRight s), ?_, rfl, rfl⟩
    ext z
    constructor
    · rintro ⟨u, rfl⟩; exact ⟨(s, u), rfl, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.2, ?_⟩
      simp only [mem_setOf_eq] at hp
      rw [← hp]
  refine ⟨a1 '' Ioo 0 1, a2 '' Ioo 0 1, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨ht0, ht1⟩ := (unitInterval_mem_Ioo t).mp ht
    refine ⟨(isArc_iff_tarc h1 h3 h4 h51).mpr (arc1 t), eAB ▸ ⟨(0, t), rfl, rfl⟩,
      eCD ▸ ⟨(1, t), rfl, rfl⟩, ?_⟩
    rintro _ ⟨⟨p, hp, rfl⟩, hz⟩
    simp only [mem_setOf_eq] at hp
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
    refine (hIp p).mpr ?_
    rintro (h | h | h | h)
    · exact hz.1 (congrArg f (Prod.ext h hp))
    · exact ht1 (hp ▸ h)
    · exact hz.2 (congrArg f (Prod.ext h hp))
    · exact ht0 (hp ▸ h)
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨hs0, hs1⟩ := (unitInterval_mem_Ioo s).mp hs
    refine ⟨(isArc_iff_tarc h1 h3 h4 h51).mpr (arc2 s).symm, eBC ▸ ⟨(s, 1), rfl, rfl⟩,
      eDA ▸ ⟨(s, 0), rfl, rfl⟩, ?_⟩
    rintro _ ⟨⟨p, hp, rfl⟩, hz⟩
    simp only [mem_setOf_eq] at hp
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
    refine (hIp p).mpr ?_
    rintro (h | h | h | h)
    · exact hs0 (hp ▸ h)
    · exact hz.1 (congrArg f (Prod.ext hp h))
    · exact hs1 (hp ▸ h)
    · exact hz.2 (congrArg f (Prod.ext hp h))
  · rintro P ⟨hPJ, hPne⟩
    obtain ⟨p, rfl⟩ := hK P (Or.inl hPJ)
    have hp := (hJp p).mp hPJ
    have nA : p ≠ (0, 0) := fun e => hPne (by rw [e, fA]; simp)
    have nB : p ≠ (0, 1) := fun e => hPne (by rw [e, fB]; simp)
    have nC : p ≠ (1, 1) := fun e => hPne (by rw [e, fC]; simp)
    have nD : p ≠ (1, 0) := fun e => hPne (by rw [e, fD]; simp)
    by_cases hx : p.1 = 0 ∨ p.1 = 1
    · left
      have ht : p.2 ≠ 0 ∧ p.2 ≠ 1 := by
        constructor
        · intro h2
          rcases hx with h | h
          · exact nA (Prod.ext h h2)
          · exact nD (Prod.ext h h2)
        · intro h2
          rcases hx with h | h
          · exact nB (Prod.ext h h2)
          · exact nC (Prod.ext h h2)
      refine ⟨⟨a1 p.2, ⟨⟨p.2, (unitInterval_mem_Ioo _).mpr ht, rfl⟩, ?_⟩, ?_⟩, ?_⟩
      · rcases hx with h | h
        · exact Or.inl (congrArg f (Prod.ext h rfl))
        · exact Or.inr (congrArg f (Prod.ext h rfl))
      · rintro _ ⟨⟨t', -, rfl⟩, h⟩
        have : p.2 = t' := by
          rcases h with h | h
          · exact congrArg Prod.snd (inj h)
          · exact congrArg Prod.snd (inj h)
        rw [this]
      · rintro ⟨_, ⟨s, -, rfl⟩, h⟩
        rcases h with h | h
        · exact ht.2 (congrArg Prod.snd (inj h))
        · exact ht.1 (congrArg Prod.snd (inj h))
    · right
      push_neg at hx
      have hy : p.2 = 1 ∨ p.2 = 0 := by tauto
      have hs : p.1 ≠ 0 ∧ p.1 ≠ 1 := hx
      refine ⟨⟨a2 p.1, ⟨⟨p.1, (unitInterval_mem_Ioo _).mpr hs, rfl⟩, ?_⟩, ?_⟩, ?_⟩
      · rcases hy with h | h
        · exact Or.inl (congrArg f (Prod.ext rfl h))
        · exact Or.inr (congrArg f (Prod.ext rfl h))
      · rintro _ ⟨⟨s', -, rfl⟩, h⟩
        have : p.1 = s' := by
          rcases h with h | h
          · exact congrArg Prod.fst (inj h)
          · exact congrArg Prod.fst (inj h)
        rw [this]
      · rintro ⟨_, ⟨t, -, rfl⟩, h⟩
        rcases h with h | h
        · exact hs.1 (congrArg Prod.fst (inj h))
        · exact hs.2 (congrArg Prod.fst (inj h))
  · intro P hPI
    obtain ⟨p, rfl⟩ := hK P (Or.inr hPI)
    have hp := (hIp p).mp hPI
    push_neg at hp
    obtain ⟨hp0, hp1, hp1', hp0'⟩ := hp
    refine ⟨⟨a1 p.2, ⟨⟨p.2, (unitInterval_mem_Ioo _).mpr ⟨hp0', hp1⟩, rfl⟩, ⟨p, rfl, rfl⟩⟩, ?_⟩,
      ⟨a2 p.1, ⟨⟨p.1, (unitInterval_mem_Ioo _).mpr ⟨hp0, hp1'⟩, rfl⟩, ⟨p, rfl, rfl⟩⟩, ?_⟩⟩
    · rintro _ ⟨⟨t', -, rfl⟩, h⟩
      have : p.2 = t' := (mem p _).mp h
      rw [this]
    · rintro _ ⟨⟨s', -, rfl⟩, h⟩
      have : p.1 = s' := (mem p _).mp h
      rw [this]
  · rintro _ ⟨t, -, rfl⟩ _ ⟨s, -, rfl⟩
    refine ⟨f (s, t), ⟨⟨(s, t), rfl, rfl⟩, ⟨(s, t), rfl, rfl⟩⟩, ?_⟩
    rintro _ ⟨⟨p, hp, rfl⟩, hz⟩
    have hs : p.1 = s := (mem p _).mp hz
    simp only [mem_setOf_eq] at hp
    exact congrArg f (Prod.ext hs hp)

section Thm

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **Theorem E** (p. 176). *Axioms used: 1–8.* -/
theorem m19_theoremE_proof (q : σ.Quad J I A B C D sAB sBC sCD sDA) :
    ∃ α₁ α₂ : Set (S × S × Set S),
      (∀ a ∈ α₁, σ.IsArc a.1 a.2.1 a.2.2 ∧ a.1 ∈ sAB ∧ a.2.1 ∈ sCD ∧
        openArc a.1 a.2.1 a.2.2 ⊆ I) ∧
      (∀ a ∈ α₂, σ.IsArc a.1 a.2.1 a.2.2 ∧ a.1 ∈ sBC ∧ a.2.1 ∈ sDA ∧
        openArc a.1 a.2.1 a.2.2 ⊆ I) ∧
      (∀ P ∈ J \ {A, B, C, D},
        ((∃! a, a ∈ α₁ ∧ (P = a.1 ∨ P = a.2.1)) ∧ ¬ ∃ a ∈ α₂, P = a.1 ∨ P = a.2.1) ∨
        ((∃! a, a ∈ α₂ ∧ (P = a.1 ∨ P = a.2.1)) ∧ ¬ ∃ a ∈ α₁, P = a.1 ∨ P = a.2.1)) ∧
      (∀ P ∈ I, (∃! a, a ∈ α₁ ∧ P ∈ a.2.2) ∧ (∃! a, a ∈ α₂ ∧ P ∈ a.2.2)) ∧
      (∀ a ∈ α₁, ∀ b ∈ α₂, ∃! P, P ∈ a.2.2 ∩ b.2.2) := by
  obtain ⟨f, hf, hfr, fA, fB, fC, fD, eAB, eBC, eCD, eDA⟩ :=
    m19_schoenflies_proof h1 h2 h3 h4 h5 h6 h7 h8 q
  exact theoremE_of_square h1 h3 h4 h5 hf hfr
    (q.disjoint_I_J h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7) q.union fA fB fC fD eAB eBC eCD eDA

end Thm

end HPC.Moore
