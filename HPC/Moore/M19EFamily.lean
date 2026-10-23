import HPC.Moore.M19ELines
import HPC.Moore.GridSquare

/-!
# Moore 1919, Theorem E: a family of lines from a set of disjoint cross-cuts (batch 143)

Given a quadrilateral `ABCDA`, a parametrization `f` of `AB` and a set `𝒜` of pairwise disjoint arcs
from `AB` to `CD`, the line records of the arcs of `𝒜`, together with the sides `DA` (position `0`)
and `BC` (position `1`), form a family of lines in `J + I` in the sense of `HPC.Sq.Family`
(`lineFam`). The index type is `Option (Option 𝒜)`: `none` is `DA`, `some none` is `BC`.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- The chosen line record of an arc. -/
noncomputable def Space.Quad.lineRec (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    (f : unitInterval → S) (x : Set S) : ℝ × Set S × Set S :=
  Classical.epsilon (q.IsLineRec f x)

section Basic

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7)
include h1 h2 h3 h4 h5 h7

theorem isClosed_K (q : σ.Quad J I A B C D sAB sBC sCD sDA) : @IsClosed S σ.topology (J ∪ I) := by
  letI := σ.topology
  have := (jordan h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7 q.interior).2.2.2.2.2.2.2.2.1
  rw [union_comm, ← this]; exact isClosed_closure

/-- A part of `ABCDA` is in the closure of the rest of `J + I`. -/
theorem side_front (q : σ.Quad J I A B C D sAB sBC sCD sDA) {s : Set S} (hs : s ⊆ J) : s ⊆ @closure S σ.topology ((J ∪ I) \ s) := by
  letI := σ.topology
  have hj := jordan h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7 q.interior
  have hIJ := hj.2.2.2.2.2.2.2.2.2.1
  refine hs.trans ?_
  have : J ⊆ closure I := by rw [hj.2.2.2.2.2.2.2.2.1]; exact subset_union_right
  refine this.trans (closure_mono fun z hz => ⟨Or.inr hz, fun hzs => ?_⟩)
  exact disjoint_left.mp hIJ hz (hs hzs)

end Basic

section Fam

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h7 h8

variable (q : σ.Quad J I A B C D sAB sBC sCD sDA) {f : unitInterval → S}
  (hf : @IsEmbedding _ _ _ σ.topology f) (hfr : range f = sAB) (hf0 : f 0 = A) (hf1 : f 1 = B)
include hf hfr hf0 hf1

theorem lineRec_spec {x : Set S} (hx : σ.XArc I sAB sCD A B C D x) :
    q.IsLineRec f x (q.lineRec f x) :=
  Classical.epsilon_spec (exists_lineRec h1 h2 h3 h4 h5 h7 h8 q hf hfr hf0 hf1 hx)

end Fam

section FamDef

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
  (q : σ.Quad J I A B C D sAB sBC sCD sDA) {f : unitInterval → S}
  (hf : @IsEmbedding _ _ _ σ.topology f) (hfr : range f = sAB) (hf0 : f 0 = A) (hf1 : f 1 = B)
  (𝒜 : Set (Set S)) (h𝒜 : ∀ x ∈ 𝒜, σ.XArc I sAB sCD A B C D x) (hd : 𝒜.Pairwise Disjoint)

/-- Positions of the lines. -/
noncomputable def lfT (f : unitInterval → S) (𝒜 : Set (Set S)) : Option (Option 𝒜) → ℝ
  | none => 0
  | some none => 1
  | some (some x) => (q.lineRec f x).1

/-- `L`-sides of the lines. -/
noncomputable def lfL (f : unitInterval → S) (𝒜 : Set (Set S)) : Option (Option 𝒜) → Set S
  | none => sDA
  | some none => J ∪ I
  | some (some x) => (q.lineRec f x).2.1

/-- `R`-sides of the lines. -/
noncomputable def lfR (f : unitInterval → S) (𝒜 : Set (Set S)) : Option (Option 𝒜) → Set S
  | none => J ∪ I
  | some none => sBC
  | some (some x) => (q.lineRec f x).2.2

include h1 h2 h3 h4 h5 h7 h8 hf hfr hf0 hf1 h𝒜 in
theorem lf_t_arc (x : 𝒜) : (lfT q f 𝒜 (some (some x))) ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨t, ht, h0, h1', -⟩ := lr_t (lineRec_spec h1 h2 h3 h4 h5 h7 h8 q hf hfr hf0 hf1 (h𝒜 x x.2))
  simp only [lfT]; rw [ht]; exact ⟨h0, h1'⟩

/-- **The family of lines** of `𝒜`. -/
noncomputable def lineFam : @HPC.Sq.Family S σ.topology (Option (Option 𝒜)) (J ∪ I) :=
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have spec : ∀ x : 𝒜, q.IsLineRec f x (q.lineRec f x) := fun x =>
    lineRec_spec h1 h2 h3 h4 h5 h7 h8 q hf hfr hf0 hf1 (h𝒜 x x.2)
  have tA := lf_t_arc h1 h2 h3 h4 h5 h7 h8 q hf hfr hf0 hf1 𝒜 h𝒜
  have hDA : IsClosed sDA := ((isArc_iff_tarc h1 h3 h4 h51).mp q.da).isClosed
  have hBC : IsClosed sBC := ((isArc_iff_tarc h1 h3 h4 h51).mp q.bc).isClosed
  have hK := isClosed_K h1 h2 h3 h4 h5 h7 q
  { t := lfT q f 𝒜
    L := lfL q f 𝒜
    R := lfR q f 𝒜
    i0 := none
    i1 := some none
    t_mem := fun i => match i with
      | none => ⟨le_rfl, zero_le_one⟩
      | some none => ⟨zero_le_one, le_rfl⟩
      | some (some x) => ⟨(tA x).1.le, (tA x).2.le⟩
    t_i0 := rfl
    t_i1 := rfl
    closedL := fun i => match i with
      | none => hDA
      | some none => hK
      | some (some x) => lr_closedL h1 h2 h3 h4 h5 h7 (spec x)
    closedR := fun i => match i with
      | none => hK
      | some none => hBC
      | some (some x) => lr_closedR h1 h2 h3 h4 h5 h7 (spec x)
    union := fun i => match i with
      | none => union_eq_right.mpr (q.sDA_sub.trans subset_union_left)
      | some none => union_eq_left.mpr (q.sBC_sub.trans subset_union_left)
      | some (some x) => lr_union (h𝒜 x x.2) (spec x)
    L_one := fun i hi => match i, hi with
      | none, hi => absurd hi zero_ne_one
      | some none, _ => rfl
      | some (some x), hi => absurd hi (tA x).2.ne
    R_zero := fun i hi => match i, hi with
      | none, _ => rfl
      | some none, hi => absurd hi one_ne_zero
      | some (some x), hi => absurd hi (tA x).1.ne'
    mono := fun i j hij => match i, j, hij with
      | none, none, h => absurd h (lt_irrefl _)
      | none, some none, _ => ⟨q.sDA_sub.trans subset_union_left,
          q.sBC_sub.trans subset_union_left, q.bc_da.symm⟩
      | none, some (some x), _ => by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, h₁, -, h₂, -⟩ :=
            lr_halves h1 h2 h3 h4 h5 h7 (spec x)
          refine ⟨h₁, fun z hz => ?_, h₂⟩
          show z ∈ J ∪ I
          rw [← lr_union (h𝒜 x x.2) (spec x)]; exact Or.inr hz
      | some none, j, h => absurd h (not_lt.mpr (match j with
          | none => zero_le_one
          | some none => le_rfl
          | some (some x) => (tA x).2.le))
      | some (some x), none, h => absurd h (not_lt.mpr (tA x).1.le)
      | some (some x), some none, _ => by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h₁, -, h₂⟩ :=
            lr_halves h1 h2 h3 h4 h5 h7 (spec x)
          refine ⟨fun z hz => ?_, h₁, h₂⟩
          show z ∈ J ∪ I
          rw [← lr_union (h𝒜 x x.2) (spec x)]; exact Or.inl hz
      | some (some x), some (some y), h => by
          have hxy : (x : Set S) ≠ y := fun e => by
            have : x = y := Subtype.ext e
            subst this; exact lt_irrefl _ h
          exact lr_mono h1 h2 h3 h4 h5 h7 hf hfr hf0 hf1 (h𝒜 x x.2) (h𝒜 y y.2) (spec x)
            (spec y) (hd x.2 y.2 hxy) h
    frontL := fun i hi => match i, hi with
      | none, _ => by
          rintro z ⟨hz, -⟩
          exact side_front h1 h2 h3 h4 h5 h7 q q.sDA_sub (s := sDA) hz
      | some none, hi => absurd hi (lt_irrefl _)
      | some (some x), _ => by
          show (q.lineRec f x).2.1 ∩ (q.lineRec f x).2.2 ⊆ _
          rw [lr_line h1 h2 h3 h4 h5 h7 (spec x)]
          exact lr_frontL h1 h2 h3 h4 h5 h7 (spec x)
    frontR := fun i hi => match i, hi with
      | none, hi => absurd hi (lt_irrefl _)
      | some none, _ => by
          rintro z ⟨-, hz⟩
          exact side_front h1 h2 h3 h4 h5 h7 q q.sBC_sub (s := sBC) hz
      | some (some x), _ => by
          show (q.lineRec f x).2.1 ∩ (q.lineRec f x).2.2 ⊆ _
          rw [lr_line h1 h2 h3 h4 h5 h7 (spec x)]
          exact lr_frontR h1 h2 h3 h4 h5 h7 (spec x)
    conn := fun i => match i with
      | none => by
          show IsPreconnected (sDA ∩ (J ∪ I))
          rw [inter_eq_left.mpr (q.sDA_sub.trans subset_union_left)]
          exact ((isArc_iff_tarc h1 h3 h4 h51).mp q.da).isPreconnected
      | some none => by
          show IsPreconnected ((J ∪ I) ∩ sBC)
          rw [inter_eq_right.mpr (q.sBC_sub.trans subset_union_left)]
          exact ((isArc_iff_tarc h1 h3 h4 h51).mp q.bc).isPreconnected
      | some (some x) => by
          show IsPreconnected ((q.lineRec f x).2.1 ∩ (q.lineRec f x).2.2)
          rw [lr_line h1 h2 h3 h4 h5 h7 (spec x)]
          exact lr_conn (h𝒜 x x.2) }

end FamDef

section FamAPI

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
  (q : σ.Quad J I A B C D sAB sBC sCD sDA) {f : unitInterval → S}
  (hf : @IsEmbedding _ _ _ σ.topology f) (hfr : range f = sAB) (hf0 : f 0 = A) (hf1 : f 1 = B)
  (𝒜 : Set (Set S)) (h𝒜 : ∀ x ∈ 𝒜, σ.XArc I sAB sCD A B C D x) (hd : 𝒜.Pairwise Disjoint)

theorem lineFam_line_none :
    lfL q f 𝒜 none ∩
      lfR q f 𝒜 none = sDA :=
  inter_eq_left.mpr (q.sDA_sub.trans subset_union_left)

theorem lineFam_line_one :
    lfL q f 𝒜 (some none) ∩
      lfR q f 𝒜 (some none) = sBC :=
  inter_eq_right.mpr (q.sBC_sub.trans subset_union_left)

include h1 h2 h3 h4 h5 h7 h8 hf hfr hf0 hf1 h𝒜 in
theorem lineFam_line_arc (x : 𝒜) :
    lfL q f 𝒜 (some (some x)) ∩
      lfR q f 𝒜 (some (some x)) = x :=
  lr_line h1 h2 h3 h4 h5 h7 (lineRec_spec h1 h2 h3 h4 h5 h7 h8 q hf hfr hf0 hf1 (h𝒜 x x.2))

include h1 h2 h3 h4 h5 h7 h8 hf hfr hf0 hf1 h𝒜 in
theorem lineFam_fL (s : unitInterval) (i : Option (Option 𝒜)) :
    f s ∈ lfL q f 𝒜 i ↔
      (s : ℝ) ≤ lfT q f 𝒜 i := by
  have hfs : f s ∈ sAB := hfr ▸ mem_range_self s
  match i with
  | none =>
    show f s ∈ sDA ↔ (s : ℝ) ≤ 0
    constructor
    · intro h
      have : f s ∈ sDA ∩ sAB := ⟨h, hfs⟩
      rw [q.da_ab, mem_singleton_iff, ← hf0] at this
      rw [@IsEmbedding.injective _ _ _ σ.topology _ hf _ _ this]; exact le_rfl
    · intro h
      have : s = 0 := Subtype.ext (le_antisymm h unitInterval.nonneg')
      rw [this, hf0]; exact q.da.right_mem
  | some none =>
    show f s ∈ J ∪ I ↔ (s : ℝ) ≤ 1
    exact ⟨fun _ => unitInterval.le_one', fun _ => Or.inl (q.sAB_sub hfs)⟩
  | some (some x) =>
    exact lr_fL h1 h2 h3 h4 h5 h7 hf hfr hf0 (h𝒜 x x.2)
      (lineRec_spec h1 h2 h3 h4 h5 h7 h8 q hf hfr hf0 hf1 (h𝒜 x x.2)) s

include h1 h2 h3 h4 h5 h7 h8 hf hfr hf0 hf1 h𝒜 in
theorem lineFam_fR (s : unitInterval) (i : Option (Option 𝒜)) :
    f s ∈ lfR q f 𝒜 i ↔
      lfT q f 𝒜 i ≤ (s : ℝ) := by
  have hfs : f s ∈ sAB := hfr ▸ mem_range_self s
  match i with
  | none =>
    show f s ∈ J ∪ I ↔ (0 : ℝ) ≤ s
    exact ⟨fun _ => unitInterval.nonneg', fun _ => Or.inl (q.sAB_sub hfs)⟩
  | some none =>
    show f s ∈ sBC ↔ (1 : ℝ) ≤ s
    constructor
    · intro h
      have : f s ∈ sAB ∩ sBC := ⟨hfs, h⟩
      rw [q.ab_bc, mem_singleton_iff, ← hf1] at this
      rw [@IsEmbedding.injective _ _ _ σ.topology _ hf _ _ this]; exact le_rfl
    · intro h
      have : s = 1 := Subtype.ext (le_antisymm unitInterval.le_one' h)
      rw [this, hf1]; exact q.bc.left_mem
  | some (some x) =>
    exact lr_fR h1 h2 h3 h4 h5 h7 hf hfr hf1 (h𝒜 x x.2)
      (lineRec_spec h1 h2 h3 h4 h5 h7 h8 q hf hfr hf0 hf1 (h𝒜 x x.2)) s

end FamAPI

end HPC.Moore
