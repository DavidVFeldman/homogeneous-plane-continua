import HPC.Moore.M19CDCut

/-!
# Moore 1919: gluing rulings of the two halves of a cut (batch 141, item E)

If `ABCDA` is cut along `x` into `AXX′DA` and `XBCX′X`, and each half carries a ruling such that the
arcs `Y` of the two halves end on `x` at the same points, then the arcs `X` of both halves together
with `x`, and the unions of the arcs `Y` of the two halves meeting on `x`, form a ruling of
`ABCDA` (`Cut.glue`); within each half its arcs are those of the ruling of that half
(`Cut.glue_carrier_iffA`, `Cut.glue_carrier_iffB`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-- An arc of a ruling of a quadrilateral with interior `I′` lies on `I′` and its boundary. -/
theorem Space.XArc.sub_cl {I' a b K : Set S} {A B C D : S} {w : Set S}
    (h : σ.XArc I' a b A B C D w) (ha : a ⊆ K) (hb : b ⊆ K) : w ⊆ I' ∪ K := by
  obtain ⟨P, P', hP, hP', -, hwI⟩ := h
  intro z hz
  by_cases hzP : z = P ∨ z = P'
  · rcases hzP with rfl | rfl
    · exact Or.inr (ha hP.1)
    · exact Or.inr (hb hP'.1)
  · simp only [not_or] at hzP
    exact Or.inl (hwI ⟨hz, by simp [hzP.1, hzP.2]⟩)

/-- The arcs `Y` glued from those of the two halves. -/
def glueY (𝒴A 𝒴B : Set (Set S)) : Set (Set S) :=
  {y | ∃ ya ∈ 𝒴A, ∃ yb ∈ 𝒴B, (ya ∩ yb).Nonempty ∧ y = ya ∪ yb}

namespace Space.Quad.Cut

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}
  {q : σ.Quad J I A B C D sAB sBC sCD sDA} {x : Set S} (c : q.Cut x)

theorem yA_cl {ya : Set S} (h : σ.XArc c.IA x sDA c.X c.X' D A ya) : ya ⊆ c.clA :=
  h.sub_cl (K := c.s₁ ∪ x ∪ c.t₁ ∪ sDA) (fun _ h => Or.inl (Or.inl (Or.inr h))) (fun _ h => Or.inr h)

theorem yB_cl {yb : Set S} (h : σ.XArc c.IB sBC x B C c.X' c.X yb) : yb ⊆ c.clB :=
  h.sub_cl (K := c.s₂ ∪ sBC ∪ c.t₂ ∪ x) (fun _ h => Or.inl (Or.inl (Or.inr h))) (fun _ h => Or.inr h)

/-- An arc `Y` of a ruling of `AXX′DA` runs from a point `e` of the open arc `x` to `DA`, meets `x`
only in `e`, and lies on the closure of `IA`. -/
theorem yA_spec {ya : Set S} (h : σ.XArc c.IA x sDA c.X c.X' D A ya) :
    ∃ e Q, e ∈ x \ {c.X, c.X'} ∧ Q ∈ sDA \ {D, A} ∧ @TArc S σ.topology e Q ya ∧
      ya \ {e, Q} ⊆ c.IA ∧ ya ∩ x = {e} ∧ ya ⊆ c.clA := by
  letI := σ.topology
  have hcl := h.sub_cl (K := c.s₁ ∪ x ∪ c.t₁ ∪ sDA) (fun _ h => Or.inl (Or.inl (Or.inr h)))
    (fun _ h => Or.inr h)
  obtain ⟨e, Q, he, hQ, hya, hyI⟩ := h
  refine ⟨e, Q, he, hQ, hya, hyI, ?_, hcl⟩
  apply subset_antisymm
  · rintro z ⟨hz, hzx⟩
    by_contra hne
    by_cases hzQ : z = Q
    · subst hzQ; exact disjoint_left.mp c.qA.bc_da hzx hQ.1
    · exact (c.IA_sub (hyI ⟨hz, by simp [hzQ]; exact hne⟩)).2 hzx
  · rintro z rfl; exact ⟨hya.left_mem, he.1⟩

/-- An arc `Y` of a ruling of `XBCX′X` runs from `BC` to a point `e` of the open arc `x`, meets `x`
only in `e`, and lies on the closure of `IB`. -/
theorem yB_spec {yb : Set S} (h : σ.XArc c.IB sBC x B C c.X' c.X yb) :
    ∃ P e, P ∈ sBC \ {B, C} ∧ e ∈ x \ {c.X', c.X} ∧ @TArc S σ.topology P e yb ∧
      yb \ {P, e} ⊆ c.IB ∧ yb ∩ x = {e} ∧ yb ⊆ c.clB := by
  letI := σ.topology
  have hcl := h.sub_cl (K := c.s₂ ∪ sBC ∪ c.t₂ ∪ x) (fun _ h => Or.inl (Or.inl (Or.inr h)))
    (fun _ h => Or.inr h)
  obtain ⟨P, e, hP, he, hyb, hyI⟩ := h
  refine ⟨P, e, hP, he, hyb, hyI, ?_, hcl⟩
  apply subset_antisymm
  · rintro z ⟨hz, hzx⟩
    by_contra hne
    by_cases hzP : z = P
    · subst hzP; exact disjoint_left.mp c.qB.bc_da hP.1 hzx
    · exact (c.IB_sub (hyI ⟨hz, by simp [hzP]; exact hne⟩)).2 hzx
  · rintro z rfl; exact ⟨hyb.right_mem, he.1⟩

/-- An arc `X` of a ruling of `AXX′DA` misses `x` and lies on the closure of `IA`. -/
theorem wA_spec {w : Set S} (h : σ.XArc c.IA c.s₁ c.t₁ A c.X c.X' D w) :
    Disjoint w x ∧ w ⊆ c.clA ∧ σ.XArc I sAB sCD A B C D w := by
  have hcl := h.sub_cl (K := c.s₁ ∪ x ∪ c.t₁ ∪ sDA) (fun _ h => Or.inl (Or.inl (Or.inl h)))
    (fun _ h => Or.inl (Or.inr h))
  obtain ⟨P, P', hP, hP', hw, hwI⟩ := h
  refine ⟨disjoint_left.mpr fun z hz hzx => ?_, hcl, ⟨P, P', ?_, ?_, hw,
    hwI.trans (fun _ h => (c.IA_sub h).1)⟩⟩
  · by_cases hzP : z = P
    · subst hzP; exact hP.2 (Or.inr (single hP.1 hzx c.qA.ab_bc))
    by_cases hzP' : z = P'
    · subst hzP'; exact hP'.2 (Or.inl (single hzx hP'.1 c.qA.bc_cd))
    exact (c.IA_sub (hwI ⟨hz, by simp [hzP, hzP']⟩)).2 hzx
  · refine ⟨c.s₁_sub hP.1, ?_⟩
    rintro (h | h)
    · exact hP.2 (Or.inl h)
    · exact c.B_notMem_s₁ (h ▸ hP.1)
  · refine ⟨c.t₁_sub hP'.1, ?_⟩
    rintro (h | h)
    · exact c.C_notMem_t₁ (h ▸ hP'.1)
    · exact hP'.2 (Or.inr h)

/-- An arc `X` of a ruling of `XBCX′X` misses `x` and lies on the closure of `IB`. -/
theorem wB_spec {w : Set S} (h : σ.XArc c.IB c.s₂ c.t₂ c.X B C c.X' w) :
    Disjoint w x ∧ w ⊆ c.clB ∧ σ.XArc I sAB sCD A B C D w := by
  have hcl := h.sub_cl (K := c.s₂ ∪ sBC ∪ c.t₂ ∪ x) (fun _ h => Or.inl (Or.inl (Or.inl h)))
    (fun _ h => Or.inl (Or.inr h))
  obtain ⟨P, P', hP, hP', hw, hwI⟩ := h
  refine ⟨disjoint_left.mpr fun z hz hzx => ?_, hcl, ⟨P, P', ?_, ?_, hw,
    hwI.trans (fun _ h => (c.IB_sub h).1)⟩⟩
  · by_cases hzP : z = P
    · subst hzP; exact hP.2 (Or.inl (single hzx hP.1 c.qB.da_ab))
    by_cases hzP' : z = P'
    · subst hzP'; exact hP'.2 (Or.inr (single hP'.1 hzx c.qB.cd_da))
    exact (c.IB_sub (hwI ⟨hz, by simp [hzP, hzP']⟩)).2 hzx
  · refine ⟨c.s₂_sub hP.1, ?_⟩
    rintro (h | h)
    · exact c.A_notMem_s₂ (h ▸ hP.1)
    · exact hP.2 (Or.inr h)
  · refine ⟨c.t₂_sub hP'.1, ?_⟩
    rintro (h | h)
    · exact hP'.2 (Or.inl h)
    · exact c.D_notMem_t₂ (h ▸ hP'.1)

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
  (h51 : Space.Axiom5₁ (S := S)) (h7 : σ.Axiom7)
include h1 h2 h3 h4 h51 h7

variable {𝒳A 𝒴A 𝒳B 𝒴B : Set (Set S)}

theorem x_inter_J (hxq : σ.XArc I sAB sCD A B C D x) {z : S} (hz : z ∈ x) (hzJ : z ∈ J) :
    z = c.X ∨ z = c.X' := by
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 h51 h7
  obtain ⟨P₀, P₀', hP₀, hP₀', -, -, hxJ⟩ := hxq.inter_J hIJ
  have hX : c.X = P₀ := by
    rcases hxJ c.X c.qA.bc.left_mem (q.sAB_sub (c.s₁_sub c.qA.ab.right_mem)) with h | h
    · exact h
    · exact absurd (h ▸ hP₀'.1) (disjoint_left.mp q.ab_cd (c.s₁_sub c.qA.ab.right_mem))
  have hX' : c.X' = P₀' := by
    rcases hxJ c.X' c.qA.bc.right_mem (q.sCD_sub (c.t₁_sub c.qA.cd.left_mem)) with h | h
    · exact absurd (h ▸ hP₀.1) (disjoint_right.mp q.ab_cd (c.t₁_sub c.qA.cd.left_mem))
    · exact h
  rw [hX, hX']
  exact hxJ z hz hzJ

theorem x_mid_I (hxq : σ.XArc I sAB sCD A B C D x) {z : S} (hz : z ∈ x) (hX : z ≠ c.X)
    (hX' : z ≠ c.X') : z ∈ I := by
  by_cases hzJ : z ∈ J
  · rcases c.x_inter_J h1 h2 h3 h4 h51 h7 hxq hz hzJ with h | h
    · exact absurd h hX
    · exact absurd h hX'
  · obtain ⟨P₀, P₀', hP₀, hP₀', -, hxI⟩ := hxq
    refine hxI ⟨hz, ?_⟩
    rintro (h | h)
    · exact hzJ (h ▸ q.sAB_sub hP₀.1)
    · exact hzJ (h ▸ q.sCD_sub hP₀'.1)

/-- An arc `Y` of `AXX′DA` and an arc `Y` of `XBCX′X` that meet end at the same point `e` of `x`,
and together form an arc from `BC` to `DA` within `ABCDA`. -/
theorem pair_spec (hxq : σ.XArc I sAB sCD A B C D x) {ya yb : Set S}
    (ha : σ.XArc c.IA x sDA c.X c.X' D A ya) (hb : σ.XArc c.IB sBC x B C c.X' c.X yb)
    (hne : (ya ∩ yb).Nonempty) :
    ∃ e, ya ∩ x = {e} ∧ yb ∩ x = {e} ∧ σ.XArc I sBC sDA B C D A (ya ∪ yb) := by
  letI := σ.topology
  haveI := t2Space h1
  obtain ⟨e, Q, he, hQ, hya, hyaI, hyax, hyacl⟩ := c.yA_spec ha
  obtain ⟨P, e', hP, he', hyb, hybI, hybx, hybcl⟩ := c.yB_spec hb
  have hcap : ∀ z ∈ ya ∩ yb, z = e ∧ z = e' := by
    rintro z ⟨hza, hzb⟩
    have hzx := c.inter_cl h1 h2 h3 h4 h51 h7 ⟨hyacl hza, hybcl hzb⟩
    exact ⟨single hza hzx hyax, single hzb hzx hybx⟩
  obtain ⟨z, hz⟩ := hne
  obtain ⟨rfl, rfl⟩ := hcap z hz
  refine ⟨z, hyax, hybx, P, Q, hP, hQ, ?_, ?_⟩
  · rw [union_comm]
    refine hyb.union hya (subset_antisymm (fun w hw => (hcap w ⟨hw.2, hw.1⟩).1 ▸ mem_singleton _) ?_)
    rintro w rfl; exact ⟨hyb.right_mem, hya.left_mem⟩
  · rintro w ⟨hw | hw, hwPQ⟩
    · by_cases hwz : w = z
      · subst hwz
        exact c.x_mid_I h1 h2 h3 h4 h51 h7 hxq he.1 (fun h => he.2 (Or.inl h))
          (fun h => he.2 (Or.inr h))
      · refine (c.IA_sub (hyaI ⟨hw, ?_⟩)).1
        simp only [mem_insert_iff, mem_singleton_iff, not_or] at hwPQ ⊢
        exact ⟨hwz, hwPQ.2⟩
    · by_cases hwz : w = z
      · subst hwz
        exact c.x_mid_I h1 h2 h3 h4 h51 h7 hxq he.1 (fun h => he.2 (Or.inl h))
          (fun h => he.2 (Or.inr h))
      · refine (c.IB_sub (hybI ⟨hw, ?_⟩)).1
        simp only [mem_insert_iff, mem_singleton_iff, not_or] at hwPQ ⊢
        exact ⟨hwPQ.1, hwz⟩

/-- **Gluing.** Rulings of the two halves give, together with `x`, a ruling of `ABCDA` whose arcs
`Y` are the unions of an arc `Y` of each half meeting on `x`. (When the ends on `x` match, every arc
of either half is part of such a union: `Cut.glue_carrier_iffA`, `Cut.glue_carrier_iffB`.) -/
theorem glue (hxq : σ.XArc I sAB sCD A B C D x)
    (RA : σ.ArcRuling c.IA c.s₁ x c.t₁ sDA A c.X c.X' D 𝒳A 𝒴A)
    (RB : σ.ArcRuling c.IB c.s₂ sBC c.t₂ x c.X B C c.X' 𝒳B 𝒴B) :
    σ.ArcRuling I sAB sBC sCD sDA A B C D (insert x (𝒳A ∪ 𝒳B)) (glueY 𝒴A 𝒴B) := by
  letI := σ.topology
  have icl := c.inter_cl h1 h2 h3 h4 h51 h7
  have wA := fun w (hw : w ∈ 𝒳A) => c.wA_spec (RA.arcX w hw)
  have wB := fun w (hw : w ∈ 𝒳B) => c.wB_spec (RB.arcX w hw)
  have yA := fun y (hy : y ∈ 𝒴A) => c.yA_spec (RA.arcY y hy)
  have yB := fun y (hy : y ∈ 𝒴B) => c.yB_spec (RB.arcY y hy)
  have pr := fun ya (ha : ya ∈ 𝒴A) yb (hb : yb ∈ 𝒴B) =>
    c.pair_spec h1 h2 h3 h4 h51 h7 hxq (RA.arcY ya ha) (RB.arcY yb hb)
  -- an arc `X` of one half misses the arcs `Y` of the other half
  have wAyB : ∀ w ∈ 𝒳A, ∀ y ∈ 𝒴B, Disjoint w y := fun w hw y hy =>
    disjoint_left.mpr fun z hzw hzy =>
      disjoint_left.mp (wA w hw).1 hzw (icl ⟨(wA w hw).2.1 hzw, c.yB_cl (RB.arcY y hy) hzy⟩)
  have wByA : ∀ w ∈ 𝒳B, ∀ y ∈ 𝒴A, Disjoint w y := fun w hw y hy =>
    disjoint_left.mpr fun z hzw hzy =>
      disjoint_left.mp (wB w hw).1 hzw (icl ⟨c.yA_cl (RA.arcY y hy) hzy, (wB w hw).2.1 hzw⟩)
  refine ⟨(RA.finX.union RB.finX).insert x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ((RA.finY.prod RB.finY).image fun p => p.1 ∪ p.2).subset ?_
    rintro _ ⟨ya, ha, yb, hb, -, rfl⟩
    exact ⟨(ya, yb), ⟨ha, hb⟩, rfl⟩
  · rintro w (rfl | hw | hw)
    · exact hxq
    · exact (wA w hw).2.2
    · exact (wB w hw).2.2
  · rintro _ ⟨ya, ha, yb, hb, hne, rfl⟩
    obtain ⟨e, -, -, h⟩ := pr ya ha yb hb hne
    exact h
  · refine pairwise_insert.mpr ⟨pairwise_union.mpr ⟨RA.disjX, RB.disjX, ?_⟩, ?_⟩
    · intro a ha b hb _
      have : Disjoint a b := disjoint_left.mpr fun z hza hzb =>
        disjoint_left.mp (wA a ha).1 hza (icl ⟨(wA a ha).2.1 hza, (wB b hb).2.1 hzb⟩)
      exact ⟨this, this.symm⟩
    · rintro b (hb | hb) _
      · exact ⟨(wA b hb).1.symm, (wA b hb).1⟩
      · exact ⟨(wB b hb).1.symm, (wB b hb).1⟩
  · rintro _ ⟨ya, ha, yb, hb, hne, rfl⟩ _ ⟨ya', ha', yb', hb', hne', rfl⟩ hneq
    obtain ⟨e, hax, hbx, -⟩ := pr ya ha yb hb hne
    obtain ⟨e', hax', hbx', -⟩ := pr ya' ha' yb' hb' hne'
    have hee : e ≠ e' := by
      rintro rfl
      have hya : ya = ya' := by
        by_contra h
        exact disjoint_left.mp (RA.disjY ha ha' h) (hax.symm ▸ mem_singleton e : e ∈ ya ∩ x).1
          (hax'.symm ▸ mem_singleton e : e ∈ ya' ∩ x).1
      have hyb : yb = yb' := by
        by_contra h
        exact disjoint_left.mp (RB.disjY hb hb' h) (hbx.symm ▸ mem_singleton e : e ∈ yb ∩ x).1
          (hbx'.symm ▸ mem_singleton e : e ∈ yb' ∩ x).1
      exact hneq (by rw [hya, hyb])
    have hya : ya ≠ ya' := by
      rintro rfl
      exact hee (single (hax.symm ▸ mem_singleton e : e ∈ ya ∩ x).1
        (hax.symm ▸ mem_singleton e : e ∈ ya ∩ x).2 hax' ▸ rfl)
    have hyb : yb ≠ yb' := by
      rintro rfl
      exact hee (single (hbx.symm ▸ mem_singleton e : e ∈ yb ∩ x).1
        (hbx.symm ▸ mem_singleton e : e ∈ yb ∩ x).2 hbx' ▸ rfl)
    have cross : ∀ {u v e e' : S} {ua vb : Set S}, ua ∩ x = {e} → vb ∩ x = {e'} → e ≠ e' →
        ua ⊆ c.clA → vb ⊆ c.clB → Disjoint ua vb := by
      intro u v e e' ua vb hu hv hee hua hvb
      refine disjoint_left.mpr fun z hzu hzv => hee ?_
      have hzx := icl ⟨hua hzu, hvb hzv⟩
      rw [← single hzu hzx hu, ← single hzv hzx hv]
    refine disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨RA.disjY ha ha' hya, ?_⟩,
      disjoint_union_right.mpr ⟨?_, RB.disjY hb hb' hyb⟩⟩
    · exact cross (u := e) (v := e) hax hbx' hee
        (c.yA_cl (RA.arcY ya ha)) (c.yB_cl (RB.arcY yb' hb'))
    · exact (cross (u := e) (v := e) hax' hbx hee.symm (c.yA_cl (RA.arcY ya' ha'))
        (c.yB_cl (RB.arcY yb hb))).symm
  · rintro w (rfl | hw | hw) _ ⟨ya, ha, yb, hb, hne, rfl⟩
    · obtain ⟨e, hax, hbx, -⟩ := pr ya ha yb hb hne
      refine ⟨e, ⟨(hax.symm ▸ mem_singleton e : e ∈ ya ∩ w).2, Or.inl
        (hax.symm ▸ mem_singleton e : e ∈ ya ∩ w).1⟩, ?_⟩
      rintro z ⟨hzx, hz | hz⟩
      · exact single hz hzx hax
      · exact single hz hzx hbx
    · obtain ⟨P, ⟨hPw, hPy⟩, hu⟩ := RA.cross w hw ya ha
      refine ⟨P, ⟨hPw, Or.inl hPy⟩, ?_⟩
      rintro z ⟨hzw, hz | hz⟩
      · exact hu z ⟨hzw, hz⟩
      · exact absurd hz (disjoint_left.mp (wAyB w hw yb hb) hzw)
    · obtain ⟨P, ⟨hPw, hPy⟩, hu⟩ := RB.cross w hw yb hb
      refine ⟨P, ⟨hPw, Or.inr hPy⟩, ?_⟩
      rintro z ⟨hzw, hz | hz⟩
      · exact absurd hz (disjoint_left.mp (wByA w hw ya ha) hzw)
      · exact hu z ⟨hzw, hz⟩

/-- Within `IA`, the arcs of the glued ruling are those of the ruling of `AXX′DA`. -/
theorem glue_carrier_iffA
    (RA : σ.ArcRuling c.IA c.s₁ x c.t₁ sDA A c.X c.X' D 𝒳A 𝒴A)
    (RB : σ.ArcRuling c.IB c.s₂ sBC c.t₂ x c.X B C c.X' 𝒳B 𝒴B)
    (mA : ∀ ya ∈ 𝒴A, ∃ yb ∈ 𝒴B, (ya ∩ yb).Nonempty) {z : S} (hz : z ∈ c.IA) :
    z ∈ ⋃₀ insert x (𝒳A ∪ 𝒳B) ∪ ⋃₀ glueY 𝒴A 𝒴B ↔ z ∈ ⋃₀ 𝒳A ∪ ⋃₀ 𝒴A := by
  have icl := c.inter_cl h1 h2 h3 h4 h51 h7
  have hzx := (c.IA_sub hz).2
  have hzA : z ∈ c.clA := Or.inl hz
  constructor
  · rintro (⟨w, rfl | hw | hw, hzw⟩ | ⟨_, ⟨ya, ha, yb, hb, -, rfl⟩, hz' | hz'⟩)
    · exact absurd hzw hzx
    · exact Or.inl ⟨w, hw, hzw⟩
    · exact absurd (icl ⟨hzA, (c.wB_spec (RB.arcX w hw)).2.1 hzw⟩) hzx
    · exact Or.inr ⟨ya, ha, hz'⟩
    · exact absurd (icl ⟨hzA, c.yB_cl (RB.arcY yb hb) hz'⟩)
        hzx
  · rintro (⟨w, hw, hzw⟩ | ⟨ya, ha, hzy⟩)
    · exact Or.inl ⟨w, Or.inr (Or.inl hw), hzw⟩
    · obtain ⟨yb, hb, hne⟩ := mA ya ha
      exact Or.inr ⟨ya ∪ yb, ⟨ya, ha, yb, hb, hne, rfl⟩, Or.inl hzy⟩

/-- Within `IB`, the arcs of the glued ruling are those of the ruling of `XBCX′X`. -/
theorem glue_carrier_iffB
    (RA : σ.ArcRuling c.IA c.s₁ x c.t₁ sDA A c.X c.X' D 𝒳A 𝒴A)
    (RB : σ.ArcRuling c.IB c.s₂ sBC c.t₂ x c.X B C c.X' 𝒳B 𝒴B)
    (mB : ∀ yb ∈ 𝒴B, ∃ ya ∈ 𝒴A, (ya ∩ yb).Nonempty) {z : S} (hz : z ∈ c.IB) :
    z ∈ ⋃₀ insert x (𝒳A ∪ 𝒳B) ∪ ⋃₀ glueY 𝒴A 𝒴B ↔ z ∈ ⋃₀ 𝒳B ∪ ⋃₀ 𝒴B := by
  have icl := c.inter_cl h1 h2 h3 h4 h51 h7
  have hzx := (c.IB_sub hz).2
  have hzB : z ∈ c.clB := Or.inl hz
  constructor
  · rintro (⟨w, rfl | hw | hw, hzw⟩ | ⟨_, ⟨ya, ha, yb, hb, -, rfl⟩, hz' | hz'⟩)
    · exact absurd hzw hzx
    · exact absurd (icl ⟨(c.wA_spec (RA.arcX w hw)).2.1 hzw, hzB⟩) hzx
    · exact Or.inl ⟨w, hw, hzw⟩
    · exact absurd (icl ⟨c.yA_cl (RA.arcY ya ha) hz', hzB⟩)
        hzx
    · exact Or.inr ⟨yb, hb, hz'⟩
  · rintro (⟨w, hw, hzw⟩ | ⟨yb, hb, hzy⟩)
    · exact Or.inl ⟨w, Or.inr (Or.inr hw), hzw⟩
    · obtain ⟨ya, ha, hne⟩ := mB yb hb
      exact Or.inr ⟨ya ∪ yb, ⟨ya, ha, yb, hb, hne, rfl⟩, Or.inr hzy⟩

end Ax

end Space.Quad.Cut

end HPC.Moore
