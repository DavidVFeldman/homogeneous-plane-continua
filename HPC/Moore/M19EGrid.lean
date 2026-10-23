import HPC.Moore.M19EFamily
import HPC.Moore.GridMesh

/-!
# Moore 1919, Theorem E: the grid of two families of cross-cuts (batch 143)

Given parametrizations of `AB` and `BC`, a set `𝒜X` of pairwise disjoint arcs from `AB` to `CD`
and a set `𝒜Y` of pairwise disjoint arcs from `BC` to `DA`, each arc of `𝒜X` meeting each arc of
`𝒜Y` in just one point, the two families of lines (`lineFam`) form a pre-grid in `J + I` in the
sense of `HPC.Sq.PreGrid` (`preGrid`). The lines of the first family are `DA`, `BC` and the arcs
of `𝒜X`; those of the second are `AB`, `CD` and the arcs of `𝒜Y`.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- An arc from `s` to `t` meets `s` in just one point (`s`, `t` disjoint parts of `J`). -/
theorem Space.XArc.inter_left_unique {I s t : Set S} {a b c d : S} {x : Set S}
    (hx : σ.XArc I s t a b c d x) (hIJ : Disjoint I J) (hs : s ⊆ J) (hst : Disjoint s t) :
    ∃! P, P ∈ x ∩ s := by
  letI := σ.topology
  obtain ⟨P, P', hP, hP', hxt, -, hJ⟩ := hx.inter_J hIJ
  refine ⟨P, ⟨hxt.left_mem, hP.1⟩, fun z hz => ?_⟩
  rcases hJ z hz.1 (hs hz.2) with h | h
  · exact h
  · exact absurd (h ▸ hP'.1) (disjoint_left.mp hst hz.2)

theorem Space.XArc.inter_right_unique {I s t : Set S} {a b c d : S} {x : Set S}
    (hx : σ.XArc I s t a b c d x) (hIJ : Disjoint I J) (ht : t ⊆ J) (hst : Disjoint s t) :
    ∃! P, P ∈ x ∩ t := by
  letI := σ.topology
  obtain ⟨P, P', hP, hP', hxt, -, hJ⟩ := hx.inter_J hIJ
  refine ⟨P', ⟨hxt.right_mem, hP'.1⟩, fun z hz => ?_⟩
  rcases hJ z hz.1 (ht hz.2) with h | h
  · exact absurd (h ▸ hP.1) (disjoint_right.mp hst hz.2)
  · exact h

/-- The line sets of the family `lineFam q f 𝒜`. -/
def lfLine (sDA sBC : Set S) (𝒜 : Set (Set S)) : Option (Option 𝒜) → Set S
  | none => sDA
  | some none => sBC
  | some (some x) => x

section Lines

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
  (q : σ.Quad J I A B C D sAB sBC sCD sDA) {f : unitInterval → S}
  (hf : @IsEmbedding _ _ _ σ.topology f) (hfr : range f = sAB) (hf0 : f 0 = A) (hf1 : f 1 = B)
  (𝒜 : Set (Set S)) (h𝒜 : ∀ x ∈ 𝒜, σ.XArc I sAB sCD A B C D x) (hd : 𝒜.Pairwise Disjoint)

include h1 h2 h3 h4 h5 h7 h8 hf hfr hf0 hf1 h𝒜 in
theorem lfL_inter_lfR (i : Option (Option 𝒜)) :
    lfL q f 𝒜 i ∩ lfR q f 𝒜 i = lfLine sDA sBC 𝒜 i :=
  match i with
  | none => lineFam_line_none q 𝒜
  | some none => lineFam_line_one q 𝒜
  | some (some x) => lineFam_line_arc h1 h2 h3 h4 h5 h7 h8 q hf hfr hf0 hf1 𝒜 h𝒜 x

include h1 h2 h3 h4 h5 h7 h8 hf hfr hf0 hf1 h𝒜 hd in
/-- Distinct lines have distinct positions. -/
theorem lfT_injective : Function.Injective (lfT q f 𝒜) := by
  have tA := lf_t_arc h1 h2 h3 h4 h5 h7 h8 q hf hfr hf0 hf1 𝒜 h𝒜
  intro i j hij
  match i, j, hij with
  | none, none, _ => rfl
  | some none, some none, _ => rfl
  | none, some none, h => exact absurd h zero_ne_one
  | some none, none, h => exact absurd h one_ne_zero
  | none, some (some y), h => exact absurd h (tA y).1.ne
  | some (some x), none, h => exact absurd h (tA x).1.ne'
  | some none, some (some y), h => exact absurd h (tA y).2.ne'
  | some (some x), some none, h => exact absurd h (tA x).2.ne
  | some (some x), some (some y), h =>
    by_contra hne
    have hxy : (x : Set S) ≠ y := fun e => hne (by rw [Subtype.ext e])
    obtain ⟨t, ht, -, -, hft⟩ := lr_t (lineRec_spec h1 h2 h3 h4 h5 h7 h8 q hf hfr hf0 hf1 (h𝒜 x x.2))
    obtain ⟨u, hu, -, -, hfu⟩ := lr_t (lineRec_spec h1 h2 h3 h4 h5 h7 h8 q hf hfr hf0 hf1 (h𝒜 y y.2))
    have : t = u := Subtype.ext (by
      have h' : (q.lineRec f x).1 = (q.lineRec f y).1 := h
      rw [← ht, ← hu]; exact h')
    subst this
    exact disjoint_left.mp (hd x.2 y.2 hxy) hft hfu

include h1 h2 h3 h4 h5 h7 h8 hf hfr hf0 hf1 h𝒜 in
theorem lineFam_line (i : Option (Option 𝒜)) :
    @HPC.Sq.Family.line S σ.topology _ _ (lineFam h1 h2 h3 h4 h5 h7 h8 q hf hfr hf0 hf1 𝒜 h𝒜 hd) i =
      lfLine sDA sBC 𝒜 i :=
  lfL_inter_lfR h1 h2 h3 h4 h5 h7 h8 q hf hfr hf0 hf1 𝒜 h𝒜 i

end Lines

theorem existsUnique_of_eq_singleton {s : Set S} {P : S} (h : s = {P}) : ∃! z, z ∈ s :=
  ⟨P, h ▸ rfl, fun z hz => by rw [h] at hz; exact hz⟩

theorem existsUnique_inter_comm {a b : Set S} (h : ∃! P, P ∈ a ∩ b) : ∃! P, P ∈ b ∩ a := by
  rwa [inter_comm]

section Grid

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
  (q : σ.Quad J I A B C D sAB sBC sCD sDA) {fA fB : unitInterval → S}
  (hfA : @IsEmbedding _ _ _ σ.topology fA) (hfAr : range fA = sAB) (hfA0 : fA 0 = A)
  (hfA1 : fA 1 = B)
  (hfB : @IsEmbedding _ _ _ σ.topology fB) (hfBr : range fB = sBC) (hfB0 : fB 0 = B)
  (hfB1 : fB 1 = C)
  (𝒜X : Set (Set S)) (h𝒜X : ∀ x ∈ 𝒜X, σ.XArc I sAB sCD A B C D x) (hdX : 𝒜X.Pairwise Disjoint)
  (𝒜Y : Set (Set S)) (h𝒜Y : ∀ y ∈ 𝒜Y, σ.XArc I sBC sDA B C D A y) (hdY : 𝒜Y.Pairwise Disjoint)
  (hcross : ∀ x ∈ 𝒜X, ∀ y ∈ 𝒜Y, ∃! P, P ∈ x ∩ y)

include h1 h2 h3 h4 h5 h7 q h𝒜X h𝒜Y hcross in
/-- Every line of the first family meets every line of the second in just one point. -/
theorem lfLine_cross (i : Option (Option 𝒜X)) (k : Option (Option 𝒜Y)) :
    ∃! P, P ∈ lfLine sDA sBC 𝒜X i ∩ lfLine sAB sCD 𝒜Y k := by
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7
  match i, k with
  | none, none => exact existsUnique_of_eq_singleton q.da_ab
  | none, some none => exact existsUnique_of_eq_singleton (by rw [inter_comm]; exact q.cd_da)
  | none, some (some y) =>
    exact existsUnique_inter_comm ((h𝒜Y y y.2).inter_right_unique hIJ q.sDA_sub q.bc_da)
  | some none, none => exact existsUnique_of_eq_singleton (by rw [inter_comm]; exact q.ab_bc)
  | some none, some none => exact existsUnique_of_eq_singleton q.bc_cd
  | some none, some (some y) =>
    exact existsUnique_inter_comm ((h𝒜Y y y.2).inter_left_unique hIJ q.sBC_sub q.bc_da)
  | some (some x), none => exact (h𝒜X x x.2).inter_left_unique hIJ q.sAB_sub q.ab_cd
  | some (some x), some none => exact (h𝒜X x x.2).inter_right_unique hIJ q.sCD_sub q.ab_cd
  | some (some x), some (some y) => exact hcross x x.2 y y.2

/-- **The pre-grid** of the two families of cross-cuts. -/
noncomputable def preGrid :
    @HPC.Sq.PreGrid S σ.topology (Option (Option 𝒜X)) (Option (Option 𝒜Y)) (J ∪ I) :=
  letI := σ.topology
  { FX := lineFam h1 h2 h3 h4 h5 h7 h8 q hfA hfAr hfA0 hfA1 𝒜X h𝒜X hdX
    FY := lineFam h1 h2 h3 h4 h5 h7 h8 q.rot hfB hfBr hfB0 hfB1 𝒜Y h𝒜Y hdY
    cross_ne := fun i k => by
      rw [lineFam_line, lineFam_line]
      exact (lfLine_cross h1 h2 h3 h4 h5 h7 q 𝒜X h𝒜X 𝒜Y h𝒜Y hcross i k).exists
    cross_sub := fun i k => by
      rw [lineFam_line, lineFam_line]
      exact fun a ha b hb => (lfLine_cross h1 h2 h3 h4 h5 h7 q 𝒜X h𝒜X 𝒜Y h𝒜Y hcross i k).unique
        ha hb }

end Grid

end HPC.Moore
