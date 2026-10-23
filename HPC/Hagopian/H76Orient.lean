import HPC.Hagopian.H76Last

/-!
# Batch 182, §1.2 and §2.2–§2.4: the last step; orientation; honest claims; the reduction

Commission 182.

* §2.2 (orientation). `Thm1Setup.up o W` and `Thm1Setup.dn o W` are the two sides of `W` in the low
  frame, exchanged by `o : Bool`: `o = false` is the printed orientation (`up = above`,
  `dn = below`), `o = true` the mirror. With the mirror cap of §2.1 (`cross_strand_near_above`),
  the cap, the order of strands, E1 and both endings hold in either orientation
  (`cross_strand_near_o`, `property4_step_unless_o`, `case1_ending_oriented`,
  `case2_ending_oriented`).
* §1.2 (the last step, `i = 2`). `LastStepWitness` and `last_step_ending`; the named `Prop`
  `LastStepClaims` and `not_property4_x3x4` (`[x₃, x₄]` does not have Property 4).
* §2.3 (honest claims). `StepCase`: the printed case hypothesis that E1 leaves (`yᵢ` between `S_J`
  and `S_I`, in orientation `o`). `Case1Claims'`, `Case2Claims'`: no antecedent `¬ Property4 J`;
  the antecedent `StepCase` instead; the witness fields as in batch 181, oriented.
* §1.3 (shape). `BlockLayersMeetSides3`: the case split for `3 ≤ i ≤ m` only.
* §2.4 (the reduction). `StepStrands` (E0 + E1 output, named) and
  `hagopian76_property4_step_cond2`. `StepFrame`, `stepStrands_of_frame` and
  `hagopian76_theorem1_of_cases2` are in `Hagopian76AA.lean`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section B182Orient

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §2.2: orientation -/

/-- **The side "up" in orientation `o`**: above `W` for `o = false` (the printed orientation,
p. 348: "we suppose `d⁻¹[J]` is below `d⁻¹[I]` and `f(yᵢ)` is above `d⁻¹[I]`"), below `W` for
`o = true`. -/
def Thm1Setup.up (S : Thm1Setup M) : Bool → Set Pt → Set Pt
  | false, W => S.V.above W
  | true, W => S.V.below W

/-- **The side "down" in orientation `o`**: below `W` for `o = false`, above `W` for `o = true`. -/
def Thm1Setup.dn (S : Thm1Setup M) : Bool → Set Pt → Set Pt
  | false, W => S.V.below W
  | true, W => S.V.above W

/-- The oriented sides of a piece are disjoint. -/
theorem Thm1Setup.dn_up_disjoint (S : Thm1Setup M) (o : Bool) {W : Set Pt} (hW : S.V.IsPiece W) :
    Disjoint (S.dn o W) (S.up o W) := by
  cases o
  · exact hW.sides_disjoint
  · exact hW.sides_disjoint.symm

/-- **The oriented cap** (§2.1, §2.2): `a ∈ Mid` down from a crossing piece `W`, `b` up from it,
`ρ(a, b) < ε₃` give `ρ(a, Cl W) < ε₃` (`cross_strand_near`, `cross_strand_near_above`). -/
theorem cross_strand_near_o (S : Thm1Setup M) (o : Bool) {W : Set Pt}
    (hW : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ W)
    (hWs : Disjoint (S.V.below W) (S.V.above W)) {a b : Pt} (ha : a ∈ midSet M S.π S.F S.D' S.n)
    (haW : a ∈ S.dn o W) (hbW : b ∈ S.up o W) (hab : dist a b < S.ε₃) :
    infDist a (closure W) < S.ε₃ := by
  cases o
  · exact cross_strand_near S hW hWs ha haW hbW hab
  · exact cross_strand_near_above S hW hWs ha haW hbW hab

/-- **Separation by one block strand, oriented** (`property4_of_strand_sep`). -/
theorem property4_of_strand_sep_o (S : Thm1Setup M) (o : Bool) {u v : unitInterval} {W : Set Pt}
    (hW : S.IsBlockStrand u v W) {y : M} (hy : S.GoodPoint y)
    (hpos : ((y : Pt) ∈ S.up o W ∧ ((S.D.f y : M) : Pt) ∈ S.dn o W) ∨
      ((y : Pt) ∈ S.dn o W ∧ ((S.D.f y : M) : Pt) ∈ S.up o W)) :
    Property4 S.D u v := by
  cases o
  · exact property4_of_strand_sep S hW hy hpos
  · exact property4_of_strand_sep S hW hy hpos.symm

/-- **The order of strands, oriented** (S4c): if `W' ⊆ dn o W` (pieces), then
`up o W ⊆ up o W'`. -/
theorem Thm1Setup.up_subset_up (S : Thm1Setup M) (o : Bool) {W W' : Set Pt} (hW : S.V.IsPiece W)
    (hW' : S.V.IsPiece W') (h : W' ⊆ S.dn o W) : S.up o W ⊆ S.up o W' := by
  cases o
  · exact VFrame.above_subset_above hW hW' h
  · exact VFrame.below_subset_below hW hW' h

/-- **S4b, oriented**: a piece disjoint from a piece `W` is down or up from it. -/
theorem Thm1Setup.piece_sides_o (S : Thm1Setup M) (o : Bool) {W X : Set Pt} (hW : S.V.IsPiece W)
    (hX : S.V.IsPiece X) (hWX : Disjoint W X) : X ⊆ S.dn o W ∨ X ⊆ S.up o W := by
  cases o
  · exact VFrame.piece_sides hW hX hWX
  · exact (VFrame.piece_sides hW hX hWX).symm

/-- A good point's component misses every block strand (it misses `F`). -/
theorem Thm1Setup.GoodPoint.disjoint_strand {S : Thm1Setup M} {y : M} (hy : S.GoodPoint y)
    {u v : unitInterval} {W : Set Pt} (hW : S.IsBlockStrand u v W) : Disjoint W (S.comp y) := by
  refine disjoint_left.2 fun z hzJ hzC => disjoint_left.1 hy.miss hzC ?_
  exact image_mono (layerSet_subset _ _) (hW.sub hzJ)

theorem Thm1Setup.GoodPoint.mem_mid {S : Thm1Setup M} {y : M} (hy : S.GoodPoint y) :
    (y : Pt) ∈ midSet M S.π S.F S.D' S.n :=
  S.K_subset_mid ⟨y, hy.mem_K, rfl⟩

theorem Thm1Setup.dist_f_lt (S : Thm1Setup M) (y : M) :
    dist (y : Pt) ((S.D.f y : M) : Pt) < S.ε₃ := by
  have := S.D.f_small y
  rw [Subtype.dist_eq, dist_comm] at this
  exact this

/-- **E1, oriented** (`property4_step_unless_setup` in orientation `o`; p. 348: "Then `d⁻¹[J]`
separates `yᵢ` from `f(yᵢ)` in `π⁻¹[D]` and `J` has Property 4 unless `yᵢ` is above `d⁻¹[J]`").
For `y` down from `S_I`, `f(y)` up from it, and `S_J ⊆ dn o S_I`: `J` has Property 4 at `y`, or the
strand of `y` is up from `S_J` ("between"). -/
theorem property4_step_unless_o (S : Thm1Setup M) (o : Bool) {uI vI uJ vJ : unitInterval}
    {SI SJ : Set Pt} (hSI : S.IsBlockStrand uI vI SI) (hSJ : S.IsBlockStrand uJ vJ SJ)
    (hJI : SJ ⊆ S.dn o SI) {y : M} (hy : S.GoodPoint y)
    (hfI : ((S.D.f y : M) : Pt) ∈ S.up o SI) :
    Property4 S.D uJ vJ ∨ S.comp y ⊆ S.up o SJ := by
  rcases S.piece_sides_o o hSJ.piece hy.piece (hy.disjoint_strand hSJ) with h | h
  · left
    exact property4_of_strand_sep_o S o hSJ hy
      (Or.inr ⟨h hy.mem_comp, S.up_subset_up o hSI.piece hSJ.piece hJI hfI⟩)
  · exact Or.inr h

/-- **§2.2, `case1_ending` in both orientations** (p. 349: "It is not above `d⁻¹[I]` because
`ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃` and `ρ(yᵢ₋₁, f(yᵢ₋₁)) < ε₃`. Hence `J` has Property 4"; p. 348: "(Other
cases are handled with similar arguments …)"). Let `y` be a good point up from `S_J` and down from
`S_I`, at distance `≥ ε₃` from `Cl S_I`, with `f(y)` up from `S_I` or down from `S_J`. Then `J`
has Property 4 at `y`. -/
theorem case1_ending_oriented (S : Thm1Setup M) (o : Bool) {uI vI uJ vJ : unitInterval}
    {SI SJ : Set Pt} (hSI : S.IsBlockStrand uI vI SI) (hSJ : S.IsBlockStrand uJ vJ SJ) {y : M}
    (hy : S.GoodPoint y) (hbetween : (y : Pt) ∈ S.up o SJ ∧ (y : Pt) ∈ S.dn o SI)
    (hfar : S.ε₃ ≤ infDist (y : Pt) (closure SI))
    (hband : ((S.D.f y : M) : Pt) ∈ S.up o SI ∨ ((S.D.f y : M) : Pt) ∈ S.dn o SJ) :
    Property4 S.D uJ vJ := by
  rcases hband with hf | hf
  · exact absurd (cross_strand_near_o S o hSI.crossing hSI.piece.sides_disjoint hy.mem_mid
      hbetween.2 hf (S.dist_f_lt y)) (not_lt.2 hfar)
  · exact property4_of_strand_sep_o S o hSJ hy (Or.inl ⟨hbetween.1, hf⟩)

/-- **Case 1 witness, oriented** (the fields of `Case1Witness`, batch 181, in orientation `o`). -/
structure Case1WitnessO (S : Thm1Setup M) (x : ℕ → unitInterval) (i : ℕ) (o : Bool) where
  y : M
  SI : Set Pt
  SJ : Set Pt
  first : S.GoodPoint y
  strandI : S.IsBlockStrand (x (2 * i - 1)) (x (2 * i)) SI
  strandJ : S.IsBlockStrand (x (2 * i - 3)) (x (2 * i - 2)) SJ
  between : (y : Pt) ∈ S.up o SJ ∧ (y : Pt) ∈ S.dn o SI
  far : S.ε₃ ≤ infDist (y : Pt) (closure SI)
  band : ((S.D.f y : M) : Pt) ∈ S.up o SI ∨ ((S.D.f y : M) : Pt) ∈ S.dn o SJ

theorem Case1WitnessO.property4 {S : Thm1Setup M} {x : ℕ → unitInterval} {i : ℕ} {o : Bool}
    (w : Case1WitnessO S x i o) : Property4 S.D (x (2 * i - 3)) (x (2 * i - 2)) :=
  case1_ending_oriented S o w.strandI w.strandJ w.first w.between w.far w.band

/-- **Case 2 witness, oriented** (the fields of `Case2Witness`, batch 181, in orientation `o`). -/
structure Case2WitnessO (S : Thm1Setup M) (x : ℕ → unitInterval) (i : ℕ) (o : Bool) where
  y : M
  SI : Set Pt
  SJ : Set Pt
  first : S.GoodPoint y
  strandI : S.IsBlockStrand (x (2 * i - 1)) (x (2 * i)) SI
  strandJ : S.IsBlockStrand (x (2 * i - 3)) (x (2 * i - 2)) SJ
  claim_a : (y : Pt) ∈ S.up o SJ → (y : Pt) ∈ S.dn o SI
  claim_b : (y : Pt) ∈ S.up o SJ → (y : Pt) ∈ S.dn o SI →
    ((S.D.f y : M) : Pt) ∉ S.dn o SJ → ((S.D.f y : M) : Pt) ∈ S.up o SI
  claim_d : (y : Pt) ∈ S.up o SJ → infDist (y : Pt) (closure SI) < S.ε₃ → False
  claim_e : (y : Pt) ∈ S.dn o SJ → ((S.D.f y : M) : Pt) ∈ S.up o SJ

/-- **§2.2, `case2_ending` in both orientations** (p. 349). As `case2_ending`, with the oriented
cap (c). -/
theorem case2_ending_oriented (S : Thm1Setup M) (x : ℕ → unitInterval) (i : ℕ) (o : Bool)
    (w : Case2WitnessO S x i o) : Property4 S.D (x (2 * i - 3)) (x (2 * i - 2)) := by
  have hy := w.first
  rcases S.piece_sides_o o w.strandJ.piece hy.piece (hy.disjoint_strand w.strandJ) with h | h
  · have hyb : (w.y : Pt) ∈ S.dn o w.SJ := h hy.mem_comp
    exact property4_of_strand_sep_o S o w.strandJ hy (Or.inr ⟨hyb, w.claim_e hyb⟩)
  · have hya : (w.y : Pt) ∈ S.up o w.SJ := h hy.mem_comp
    have hyI := w.claim_a hya
    by_cases hfb : ((S.D.f w.y : M) : Pt) ∈ S.dn o w.SJ
    · exact property4_of_strand_sep_o S o w.strandJ hy (Or.inl ⟨hya, hfb⟩)
    · exact (w.claim_d hya (cross_strand_near_o S o w.strandI.crossing
        w.strandI.piece.sides_disjoint hy.mem_mid hyI (w.claim_b hya hyI hfb)
        (S.dist_f_lt w.y))).elim

/-! ## §1.2: the last step -/

/-- **The witness of the last step** (commission 182 §1.2; `i = 2`, `J = [x₁, x₂] = [0, e]`,
`I = [x₃, x₄]`): Case 1 read with the bottom edge in place of the `J`-strand. A good point `y`
(E2.1), an `I`-strand `S_I`, `y` down from `S_I` ("between the bottom edge and `S_I`": nothing of
`π⁻¹[D]` is below `E`), `ρ(y, Cl S_I) ≥ ε₃` (E2.4), and `f(y)` up from `S_I` (the band
`P = d⁻¹[[x₁, x₄]] ∪ Q`: `f(y)` is above `S_I` or below `E`, and the second is impossible). -/
structure LastStepWitness (S : Thm1Setup M) (x : ℕ → unitInterval) where
  o : Bool
  y : M
  SI : Set Pt
  good : S.GoodPoint y
  strandI : S.IsBlockStrand (x 3) (x 4) SI
  down : (y : Pt) ∈ S.dn o SI
  far : S.ε₃ ≤ infDist (y : Pt) (closure SI)
  band : ((S.D.f y : M) : Pt) ∈ S.up o SI

/-- **§1.2, `last_step_ending`**: a witness of the last step gives `False` (the oriented cap
against `far`). -/
theorem last_step_ending (S : Thm1Setup M) {x : ℕ → unitInterval} (w : LastStepWitness S x) :
    False :=
  absurd (cross_strand_near_o S w.o w.strandI.crossing w.strandI.piece.sides_disjoint
    w.good.mem_mid w.down w.band (S.dist_f_lt w.y)) (not_lt.2 w.far)

/-- **Named `Prop`: the claims of the last step** (§1.2): if `[x₃, x₄]` has Property 4, a witness
of the last step exists. The printed step is a proof by contradiction ("The resulting contradiction
will complete our proof"), so this `Prop` is, by design, equivalent to `¬ Property4 [x₃, x₄]`
(second non-vacuity check, report §1.2). -/
def LastStepClaims (S : Thm1Setup M) (x : ℕ → unitInterval) : Prop :=
  Property4 S.D (x 3) (x 4) → Nonempty (LastStepWitness S x)

/-- **The last step**: from `LastStepClaims`, `[x₃, x₄]` does not have Property 4. -/
theorem not_property4_x3x4 (S : Thm1Setup M) (x : ℕ → unitInterval) (h : LastStepClaims S x) :
    ¬ Property4 S.D (x 3) (x 4) := fun hP =>
  let ⟨w⟩ := h hP
  last_step_ending S w

/-! ## §1.3 (shape): the case split for `3 ≤ i ≤ m` -/

/-- **Named `Prop`: the case split for `3 ≤ i ≤ m`** (commission 182 §1.3; p. 348: "The proof now
breaks down into two cases"). The batch-181 `BlockLayersMeetSides` restricted to `i ≥ 3`; at `i = 2`
it is false (`blockLayersMeetSides_false`). -/
def BlockLayersMeetSides3 (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ) : Prop :=
  ∀ i, 3 ≤ i → i ≤ m →
    (∃ a ∈ ({3 / 22, 19 / 22} : Set ℝ), S.LayerMeetsSide (x (2 * i - 1)) a) ∧
    (∃ b ∈ ({3 / 22, 19 / 22} : Set ℝ), S.LayerMeetsSide (x (2 * i - 2)) b)

/-! ## §2.3: honest claims -/

/-- **The printed case hypothesis left by E1** (commission 182 §2.3; p. 348: "and `J` has
Property 4 unless `yᵢ` is above `d⁻¹[J]`"), in orientation `o`: `yᵢ` is a good point, `S_I` an
`I`-strand with `yᵢ` down from it and `f(yᵢ)` up from it (E0), `S_J` a `J`-strand down from `S_I`,
and the strand of `yᵢ` up from `S_J` (the second alternative of `property4_step_unless_o`). -/
structure StepCase (S : Thm1Setup M) (x : ℕ → unitInterval) (i : ℕ) (o : Bool) (yi : M)
    (SI SJ : Set Pt) : Prop where
  good : S.GoodPoint yi
  strandI : S.IsBlockStrand (x (2 * i - 1)) (x (2 * i)) SI
  strandJ : S.IsBlockStrand (x (2 * i - 3)) (x (2 * i - 2)) SJ
  order : SJ ⊆ S.dn o SI
  y_dn : (yi : Pt) ∈ S.dn o SI
  f_up : ((S.D.f yi : M) : Pt) ∈ S.up o SI
  between : S.comp yi ⊆ S.up o SJ

/-- **Named `Prop`: the claims of Case 1, restated** (commission 182 §2.3): for `3 ≤ i ≤ m`, in the
Case 1 configuration and the printed case hypothesis `StepCase` (any orientation), a Case 1 witness
in that orientation exists. No antecedent `¬ Property4 J`. -/
def Case1Claims' (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ) : Prop :=
  ∀ i, 3 ≤ i → i ≤ m → Case1Config S x i → ∀ o yi SI SJ, StepCase S x i o yi SI SJ →
    Nonempty (Case1WitnessO S x i o)

/-- **Named `Prop`: the claims of Case 2, restated** (commission 182 §2.3). -/
def Case2Claims' (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ) : Prop :=
  ∀ i, 3 ≤ i → i ≤ m → Case2Config S x i → ∀ o yi SI SJ, StepCase S x i o yi SI SJ →
    Nonempty (Case2WitnessO S x i o)

/-! ## §2.4: the reduction -/

/-- **Named `Prop`: the output of E0 and E1** (p. 348: "Then `d⁻¹[J]` separates `yᵢ` from `f(yᵢ)`
in `π⁻¹[D]` and `J` has Property 4 unless `yᵢ` is above `d⁻¹[J]`"): for `3 ≤ i ≤ m`, if `I` has
Property 4 then `J` has Property 4 or the printed case hypothesis holds in some orientation.
Reduced to `StepFrame` by `stepStrands_of_frame` (`Hagopian76AA.lean`). -/
def StepStrands (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ) : Prop :=
  ∀ i, 3 ≤ i → i ≤ m → Property4 S.D (x (2 * i - 1)) (x (2 * i)) →
    Property4 S.D (x (2 * i - 3)) (x (2 * i - 2)) ∨ ∃ o yi SI SJ, StepCase S x i o yi SI SJ

/-- **§2.4, the step** (commission 182 §2.4), from the named `Prop`s `StepStrands` (E0 + E1),
`LastStepClaims` (`i = 2`), `BlockLayersMeetSides3` (the case split for `i ≥ 3`) and the restated
`Case1Claims'`, `Case2Claims'`. At `i = 2` the step holds because its antecedent fails
(`not_property4_x3x4`); for `i ≥ 3`, E1 either gives Property 4 for `J` or the case hypothesis, and
then the case split and the claims give a witness whose ending gives Property 4 for `J`. -/
theorem hagopian76_property4_step_cond2 (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ)
    (hstr : StepStrands S x m) (hlast : LastStepClaims S x) (hsides : BlockLayersMeetSides3 S x m)
    (h1 : Case1Claims' S x m) (h2 : Case2Claims' S x m) : Property4Step S.D x m := by
  intro i hi2 him hI
  rcases Nat.lt_or_ge i 3 with hi | hi3
  · obtain rfl : i = 2 := by omega
    exact absurd hI (not_property4_x3x4 S x hlast)
  rcases hstr i hi3 him hI with hJ | ⟨o, yi, SI, SJ, hc⟩
  · exact hJ
  obtain ⟨hs1, hs2⟩ := hsides i hi3 him
  rcases case1_or_case2 S x i hs1 hs2 with hcfg | hcfg
  · obtain ⟨w⟩ := h1 i hi3 him hcfg o yi SI SJ hc
    exact w.property4
  · obtain ⟨w⟩ := h2 i hi3 him hcfg o yi SI SJ hc
    exact case2_ending_oriented S x i o w

end B182Orient

end HPC.Hagopian
