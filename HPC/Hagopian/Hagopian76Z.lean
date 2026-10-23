import HPC.Hagopian.H76CapLow
import HPC.Hagopian.H76TipRel

/-!
# Batch 181: Hagopian 1976, Theorem 1 — saturation; 3c; Case 1 strand by strand; Case 2 sentence by
# sentence

Commission 181. The skeleton is split under `HPC/Hagopian/`:

| Item | Status | Lean name (file) |
| --- | --- | --- |
| §1.1 `noncrossing_half_in_O` | open | comment block below |
| §1.2–§1.3 `chunk_points` | open | comment block below |
| §1.4 step 3 (relaxed mirror triod) | proved | `tip_meets_end_layer_mirror_rel`, `tip_triod_mirror_rel`, `chunk_edge_case_mirror` (`H76TipRel.lean`) |
| §1.4 steps 1, 2, 4 (`chunk_edge_case`) | open | comment block below |
| 2d `no_end_layer_chunk`, 2e `innerComponentsCross_hagopian` | open | `InnerComponentsCross` stays a hypothesis |
| §2.1 3c | proved | `block_components_cross`, `Thm1Setup.inner_point_in_block` (`H76Block3c.lean`) |
| §2.2 E0, E1 | proved | `property4_strand`, `property4_step_unless_setup` (here); frame forms `VFrame.property4_step_unless`, `VFrame.opposite_of_sepIn` (`H76Cap.lean`) |
| §3.1 fields | proved | `Thm1Setup.hε₃O`, `Thm1Setup.hε₃S` (`H76Thm1Setup.lean`), `exists_eps_mid_O`, `exists_eps_mid_sides` (`H76Mid.lean`) |
| §3.1 `f(y) ∈ π⁻¹[D]` | proved | `f_mem_O_of_mem_K` (`H76CapLow.lean`) |
| §3.2.1 | proved | `above_closure_misses_bottom` (`H76CapLow.lean`) |
| §3.2.2 cap lemma | proved | `cross_strand_near` (`H76CapLow.lean`) |
| §3.2.3 mirror | proved, with a hypothesis | `cross_strand_near_mirror` (`H76CapLow.lean`) |
| §3.3–§3.6 | named fields | `Case1Witness` (here) |
| §3.7 ending | proved | `case1_ending` (here) |
| §3.8 Case 1 | proved, conditional | `case1` (here) |
| §4 (a)–(e) | (c) proved, others named fields | `Case2Witness`, `case2_ending` (here) |
| §4 Case 2 | proved, conditional | `case2` (here) |
| §5 the step | proved, conditional | `hagopian76_property4_step_cond` (here) |
| Theorem 1 | conditional | `hagopian76_theorem1_of_cases` (here) |

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 348–349. Route: commission 181.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

theorem SepIn.symm {O A : Set Pt} {p q : Pt} (h : SepIn O A p q) : SepIn O A q p :=
  ⟨h.2.1, h.1, fun S hS hSO hqS hpS => h.2.2 S hS hSO hpS hqS⟩

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## Vocabulary: points of `K` on strands, block strands -/

/-- The component `C_y` of `y` in `M ∩ π⁻¹[D]` (Hagopian's `y`-component). -/
def Thm1Setup.comp (S : Thm1Setup M) (y : M) : Set Pt :=
  connectedComponentIn (M ∩ S.π ⁻¹' (S.F '' S.D')) (y : Pt)

/-- **A point of `K` usable for Property 4** (the output of E2.1, §3.3): `y ∈ K`, the closure of
its component `C_y` is essential to `h[R(E)]` (clause (1) of Property 4), `C_y` is a piece of the
low frame, and `C_y` misses `F` (`L ∩ F = ∅`). -/
structure Thm1Setup.GoodPoint (S : Thm1Setup M) (y : M) : Prop where
  mem_K : y ∈ S.D.K
  ess : IsEssential S.k (S.D.h ⁻¹' (Subtype.val ⁻¹' closure (S.comp y)))
  piece : S.V.IsPiece (S.comp y)
  miss : Disjoint (S.comp y) (toPt S.D.G)

/-- **A block strand** (`S_I`, `S_J` of (β)): a crossing piece, piece of the low frame, inside
`d⁻¹[[u, v]]`. -/
structure Thm1Setup.IsBlockStrand (S : Thm1Setup M) (u v : unitInterval) (W : Set Pt) : Prop where
  crossing : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ W
  piece : S.V.IsPiece W
  sub : W ⊆ toPt (layerSet S.D.d (Icc u v))

theorem Thm1Setup.GoodPoint.mem_O {S : Thm1Setup M} {y : M} (hy : S.GoodPoint y) :
    (y : Pt) ∈ S.π ⁻¹' (S.F '' S.D') := by
  obtain ⟨-, q, hqD, hq, -⟩ := S.K_subset_mid ⟨y, hy.mem_K, rfl⟩
  exact ⟨q, hqD, hq.symm⟩

theorem Thm1Setup.GoodPoint.mem_comp {S : Thm1Setup M} {y : M} (hy : S.GoodPoint y) :
    (y : Pt) ∈ S.comp y :=
  mem_connectedComponentIn ⟨y.2, hy.mem_O⟩

theorem Thm1Setup.GoodPoint.rset {S : Thm1Setup M} {y : M} (hy : S.GoodPoint y) :
    S.D.h.symm y ∈ Rset S.k := by
  refine hy.ess.1 ?_
  show ((S.D.h (S.D.h.symm y) : M) : Pt) ∈ closure (S.comp y)
  rw [S.D.h.apply_symm_apply]
  exact subset_closure hy.mem_comp

theorem Thm1Setup.GoodPoint.notMem_G {S : Thm1Setup M} {y : M} (hy : S.GoodPoint y) :
    (y : Pt) ∉ toPt S.D.G :=
  fun h => disjoint_left.1 hy.miss hy.mem_comp h

theorem Thm1Setup.isClosed_toPt_layerSet (S : Thm1Setup M) (u v : unitInterval) :
    IsClosed (toPt (layerSet S.D.d (Icc u v))) :=
  (isClosed_M_of_compact (M := M)).isClosedEmbedding_subtypeVal.isClosedMap _
    (isClosed_layerSet_Icc S.D.hG u v)

/-- **Separation by one block strand gives Property 4** (E0 ⇐, §3.7.2): if `y` is a good point and
`y`, `f(y)` lie on opposite sides of a strand `S_B` of the block `B = [u, v]`, then `B` has
Property 4 at `y` (SSL converse, then `Cl S_B ⊆ d⁻¹[B]`). -/
theorem property4_of_strand_sep (S : Thm1Setup M) {u v : unitInterval} {W : Set Pt}
    (hW : S.IsBlockStrand u v W) {y : M} (hy : S.GoodPoint y)
    (hpos : ((y : Pt) ∈ S.V.above W ∧ ((S.D.f y : M) : Pt) ∈ S.V.below W) ∨
      ((y : Pt) ∈ S.V.below W ∧ ((S.D.f y : M) : Pt) ∈ S.V.above W)) :
    Property4 S.D u v := by
  have hsep : SepIn S.V.O (closure W) (y : Pt) ((S.D.f y : M) : Pt) := by
    rcases hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact VFrame.sepIn_of_between hW.piece (singleton_subset_iff.2 h2)
        (singleton_subset_iff.2 h1) rfl rfl
    · exact (VFrame.sepIn_of_between hW.piece (singleton_subset_iff.2 h1)
        (singleton_subset_iff.2 h2) rfl rfl).symm
  have hcl : closure W ⊆ toPt (layerSet S.D.d (Icc u v)) :=
    closure_minimal hW.sub (S.isClosed_toPt_layerSet u v)
  have hBG : toPt (layerSet S.D.d (Icc u v)) ⊆ toPt S.D.G := image_mono (layerSet_subset _ _)
  refine ⟨y, hy.mem_K, hy.ess, hsep.mono hcl (fun h => hy.notMem_G (hBG h)) (fun h => ?_)⟩
  exact f_notMem_G_of_Rset S hy.rset (val_mem_toPt_iff.1 (hBG h))

/-! ## §2. E0 and E1 in the set-up -/

/-- Crossing pieces are pieces of the low frame of the set-up (`isPiece_of_isCrossingPiece`). -/
theorem Thm1Setup.isPiece_of_crossing (S : Thm1Setup M) {X : Set Pt}
    (hX : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ X) : S.V.IsPiece X :=
  isPiece_of_isCrossingPiece S.hπ.continuous S.hF (by norm_num) (by norm_num) (by norm_num)
    S.c₁_le_one S.hI S.hIs S.hDo S.hR.sub S.hDf (x₀ := 1 / 2) ⟨by norm_num, by norm_num⟩ S.hw₂
    S.hFw S.hseg (S.hR.isOpen.preimage S.hπ.continuous) S.lowFrame_hyps.1 S.hsub S.injOn_O
    S.hπ.surjective S.lowFrame_hyps.2 hX

/-- Two components of `M ∩ π⁻¹[D]` are equal or disjoint. -/
theorem Thm1Setup.comp_eq_or_disjoint (S : Thm1Setup M) (y y' : M) :
    S.comp y = S.comp y' ∨ Disjoint (S.comp y) (S.comp y') := by
  by_cases h : (S.comp y ∩ S.comp y').Nonempty
  · obtain ⟨z, hz, hz'⟩ := h
    left
    unfold Thm1Setup.comp at hz hz' ⊢
    rw [connectedComponentIn_eq hz, connectedComponentIn_eq hz']
  · exact Or.inr (disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 h))

/-- **E0 (⇒) in the set-up** (commission 181 §2.2, first bullet; with 3c and
`sepByCrossing_of_inner_crossing`): with saturation on an interval containing `1/2`, if the block
`B = [x₂ᵢ₋₁, x₂ᵢ]` separates a good point `y` from `f(y)` in `π⁻¹[D]`, and the component of `f(y)`
in `M ∩ π⁻¹[D]` is a piece missing `F`, then some `B`-strand `S_B` has `y` and `f(y)` on opposite
sides. -/
theorem property4_strand (S : Thm1Setup M) {lo hi : ℝ}
    (hICC : InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ lo hi)
    (hlo : lo < 1 / 2) (hhi : 1 / 2 < hi) {x : ℕ → unitInterval} {m : ℕ} (hx : S.IsBlocks x m)
    {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) {y : M} (hy : S.GoodPoint y)
    (hfP : S.V.IsPiece (S.comp (S.D.f y))) (hfG : Disjoint (S.comp (S.D.f y)) (toPt S.D.G))
    (hsep : SepIn (S.π ⁻¹' (S.F '' S.D')) (toPt (layerSet S.D.d (Icc (x (2 * i - 1)) (x (2 * i)))))
      (y : Pt) ((S.D.f y : M) : Pt)) :
    ∃ W, S.IsBlockStrand (x (2 * i - 1)) (x (2 * i)) W ∧
      (((y : Pt) ∈ S.V.below W ∧ ((S.D.f y : M) : Pt) ∈ S.V.above W) ∨
        ((y : Pt) ∈ S.V.above W ∧ ((S.D.f y : M) : Pt) ∈ S.V.below W)) := by
  set Z := toPt (layerSet S.D.d (Icc (x (2 * i - 1)) (x (2 * i)))) with hZdef
  have hZG : Z ⊆ toPt S.D.G := image_mono (layerSet_subset _ _)
  have hcross : ∀ z ∈ Z ∩ S.V.O, (∃ v, S.V.lev z v) →
      IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
        (connectedComponentIn (Z ∩ S.V.O) z) := by
    rintro z hz ⟨v, hv⟩
    have hv' : v ∈ Ioo 0 S.w₂ ∧ S.π z = S.F (1 / 2, v) := hv
    have hzm : ∃ q ∈ S.D', S.π z = S.F q ∧ q.1 ∈ Ioo lo hi :=
      ⟨(1 / 2, v), S.hsub ⟨rfl, hv'.1⟩, hv'.2, hlo, hhi⟩
    have h3c := block_components_cross S hICC x m hx i hi1 him z hz hzm
    change IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (connectedComponentIn (Z ∩ S.π ⁻¹' (S.F '' S.D')) z)
    rw [h3c]
    exact hICC z ⟨hZG hz.1, hz.2⟩ hzm
  have hZ : ∀ z ∈ Z ∩ S.V.O, (∃ v, S.V.lev z v) →
      S.V.IsPiece (connectedComponentIn (Z ∩ S.V.O) z) := fun z hz hzσ =>
    S.isPiece_of_crossing (hcross z hz hzσ)
  have hfO : ((S.D.f y : M) : Pt) ∈ S.π ⁻¹' (S.F '' S.D') := hsep.2.1.1
  have hfmem : ((S.D.f y : M) : Pt) ∈ S.comp (S.D.f y) :=
    mem_connectedComponentIn ⟨(S.D.f y).2, hfO⟩
  have hXZ : Disjoint (S.comp y) Z := hy.miss.mono_right hZG
  have hYZ : Disjoint (S.comp (S.D.f y)) Z := hfG.mono_right hZG
  obtain ⟨z, hzZO, hzσ, hWP, hWsep⟩ := VFrame.sepByCrossing_of_inner_crossing (V := S.V) hZ
    hy.piece hfP (S.comp_eq_or_disjoint y (S.D.f y)) hXZ hYZ hy.mem_comp hfmem hsep
  set W := connectedComponentIn (Z ∩ S.V.O) z with hW
  have hWZ : W ⊆ Z := (connectedComponentIn_subset _ _).trans inter_subset_left
  refine ⟨W, ⟨hcross z hzZO hzσ, hWP, hWZ⟩, ?_⟩
  exact VFrame.opposite_of_sepIn hWP hy.piece hfP (hXZ.mono_right hWZ).symm
    (hYZ.mono_right hWZ).symm hy.mem_comp hfmem hWsep

/-- **E1 in the set-up** (commission 181 §2.2, second and third bullets; p. 348: "Then `d⁻¹[J]`
separates `yᵢ` from `f(yᵢ)` in `π⁻¹[D]` and `J` has Property 4 unless `yᵢ` is above `d⁻¹[J]`").
In the printed configuration (`y` below the `I`-strand `S_I`, `f(y)` above it), for a `J`-strand
`S_J ≺ S_I`: either `J` has Property 4 (at `y` itself), or the strand of `y` is above `S_J` while
`y` is below `S_I` ("between", (β)). -/
theorem property4_step_unless_setup (S : Thm1Setup M) {uI vI uJ vJ : unitInterval}
    {SI SJ : Set Pt} (hSI : S.IsBlockStrand uI vI SI) (hSJ : S.IsBlockStrand uJ vJ SJ)
    (hJI : SJ ⊆ S.V.below SI) {y : M} (hy : S.GoodPoint y) (hyI : (y : Pt) ∈ S.V.below SI)
    (hfI : ((S.D.f y : M) : Pt) ∈ S.V.above SI) :
    Property4 S.D uJ vJ ∨ (S.comp y ⊆ S.V.above SJ ∧ (y : Pt) ∈ S.V.below SI) := by
  have hdisj : Disjoint SJ (S.comp y) := by
    refine disjoint_left.2 fun z hzJ hzC => disjoint_left.1 hy.miss hzC ?_
    exact image_mono (layerSet_subset _ _) (hSJ.sub hzJ)
  rcases VFrame.piece_sides hSJ.piece hy.piece hdisj with h | h
  · left
    exact property4_of_strand_sep S hSJ hy
      (Or.inr ⟨h hy.mem_comp, VFrame.above_subset_above hSI.piece hSJ.piece hJI hfI⟩)
  · exact Or.inr ⟨h, hyI⟩

/-! ## §3. Case 1, strand by strand -/

/-- **§3.7, the ending of Case 1** (p. 349: "It is not above `d⁻¹[I]` because
`ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃` and `ρ(yᵢ₋₁, f(yᵢ₋₁)) < ε₃`. Hence `J` has Property 4."). Let `y` be a good
point between `S_J` and `S_I` (§3.4), at distance `≥ ε₃` from `Cl S_I` (§3.5), with `f(y)` above
`S_I` or below `S_J` (§3.6). Then `J` has Property 4 at `y`.

*Proof:* above `S_I` is excluded by the cap lemma `cross_strand_near` (with `a = y ∈ Mid`, `b = f(y)`,
`ρ(y, f(y)) < ε₃`); below `S_J` gives Property 4 for `J` (`property4_of_strand_sep`). The order
`S_J ≺ S_I` is not used. -/
theorem case1_ending (S : Thm1Setup M) {uI vI uJ vJ : unitInterval} {SI SJ : Set Pt}
    (hSI : S.IsBlockStrand uI vI SI) (hSJ : S.IsBlockStrand uJ vJ SJ) {y : M}
    (hy : S.GoodPoint y) (hbetween : (y : Pt) ∈ S.V.above SJ ∧ (y : Pt) ∈ S.V.below SI)
    (hfar : S.ε₃ ≤ infDist (y : Pt) (closure SI))
    (hband : ((S.D.f y : M) : Pt) ∈ S.V.above SI ∨ ((S.D.f y : M) : Pt) ∈ S.V.below SJ) :
    Property4 S.D uJ vJ := by
  rcases hband with hf | hf
  · exfalso
    have hd : dist (y : Pt) ((S.D.f y : M) : Pt) < S.ε₃ := by
      have := S.D.f_small y
      rw [Subtype.dist_eq, dist_comm] at this
      exact this
    have := cross_strand_near S hSI.crossing hSI.piece.sides_disjoint
      (S.K_subset_mid ⟨y, hy.mem_K, rfl⟩) hbetween.2 hf hd
    linarith
  · exact property4_of_strand_sep S hSJ hy (Or.inl ⟨hbetween.1, hf⟩)

/-- Hagopian's side segments `π⁻¹[⟨p₁, r⟩]` (`a = 3/22`) and `π⁻¹[⟨p₅, s⟩]` (`a = 19/22`), closed,
heights in `[0, c₁]`: the layer `d⁻¹(u)` meets the one over `a`. -/
def Thm1Setup.LayerMeetsSide (S : Thm1Setup M) (u : unitInterval) (a : ℝ) : Prop :=
  (toPt (layer S.D.d u) ∩ S.π ⁻¹' (S.F '' (({a} : Set ℝ) ×ˢ Icc 0 S.c₁))).Nonempty

/-- **The Case 1 configuration** (p. 348: "Suppose `d⁻¹(x₂ᵢ₋₁)` and `d⁻¹(x₂ᵢ₋₂)` intersect the same
element of `{π⁻¹[⟨p₁, r⟩], π⁻¹[⟨p₅, s⟩]}`"). -/
def Case1Config (S : Thm1Setup M) (x : ℕ → unitInterval) (i : ℕ) : Prop :=
  ∃ a ∈ ({3 / 22, 19 / 22} : Set ℝ), S.LayerMeetsSide (x (2 * i - 1)) a ∧
    S.LayerMeetsSide (x (2 * i - 2)) a

/-- **The Case 2 configuration** (p. 349: "Suppose `d⁻¹(x₂ᵢ₋₁)` and `d⁻¹(x₂ᵢ₋₂)` intersect
different elements of `{π⁻¹[⟨p₁, r⟩], π⁻¹[⟨p₅, s⟩]}`"). -/
def Case2Config (S : Thm1Setup M) (x : ℕ → unitInterval) (i : ℕ) : Prop :=
  ∃ a ∈ ({3 / 22, 19 / 22} : Set ℝ), ∃ b ∈ ({3 / 22, 19 / 22} : Set ℝ), a ≠ b ∧
    S.LayerMeetsSide (x (2 * i - 1)) a ∧ S.LayerMeetsSide (x (2 * i - 2)) b

/-- The two cases are exhaustive once both layers meet a side segment. -/
theorem case1_or_case2 (S : Thm1Setup M) (x : ℕ → unitInterval) (i : ℕ)
    (h1 : ∃ a ∈ ({3 / 22, 19 / 22} : Set ℝ), S.LayerMeetsSide (x (2 * i - 1)) a)
    (h2 : ∃ b ∈ ({3 / 22, 19 / 22} : Set ℝ), S.LayerMeetsSide (x (2 * i - 2)) b) :
    Case1Config S x i ∨ Case2Config S x i := by
  obtain ⟨a, ha, hla⟩ := h1
  obtain ⟨b, hb, hlb⟩ := h2
  by_cases hab : a = b
  · subst hab; exact Or.inl ⟨a, ha, hla, hlb⟩
  · exact Or.inr ⟨a, ha, b, hb, hab, hla, hlb⟩

/-- **The open claims of Case 1** (§3.3–§3.6), for the step `I = [x₂ᵢ₋₁, x₂ᵢ] → J = [x₂ᵢ₋₃, x₂ᵢ₋₂]`.
Each field renders one printed sentence (pp. 348–349):
* `first` (§3.3, E2.1): "Let `Cᵢ₋₁` be the first component … Note that `Cl Cᵢ₋₁` is essential to
  `h[R(E)]`. … Let `yᵢ₋₁` be a point of `K ∩ Cᵢ₋₁`" — with `L ∩ F = ∅` (so `Cᵢ₋₁` misses `F`) and
  `Cᵢ₋₁` a piece;
* `strandI`, `strandJ`: the strands `S_I`, `S_J` adjacent to `yᵢ₋₁` (β);
* `between` (§3.4): "we see that `yᵢ₋₁` is between `d⁻¹[I]` and `d⁻¹[J]`";
* `far` (§3.5, E2.4): "`ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃`; for otherwise, a subcontinuum of `L` would violate
  Property 2" — rendered with `Cl S_I` for `d⁻¹[I]` (weaker);
* `band` (§3.6): "Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`". -/
structure Case1Witness (S : Thm1Setup M) (x : ℕ → unitInterval) (i : ℕ) where
  y : M
  SI : Set Pt
  SJ : Set Pt
  first : S.GoodPoint y
  strandI : S.IsBlockStrand (x (2 * i - 1)) (x (2 * i)) SI
  strandJ : S.IsBlockStrand (x (2 * i - 3)) (x (2 * i - 2)) SJ
  between : (y : Pt) ∈ S.V.above SJ ∧ (y : Pt) ∈ S.V.below SI
  far : S.ε₃ ≤ infDist (y : Pt) (closure SI)
  band : ((S.D.f y : M) : Pt) ∈ S.V.above SI ∨ ((S.D.f y : M) : Pt) ∈ S.V.below SJ

/-- **Named `Prop`: the open claims of Case 1** (§3.3–§3.6): whenever `I` has Property 4, `J` does
not, and the Case 1 configuration holds, a `Case1Witness` exists. -/
def Case1Claims (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ) : Prop :=
  ∀ i, 2 ≤ i → i ≤ m → Property4 S.D (x (2 * i - 1)) (x (2 * i)) →
    ¬ Property4 S.D (x (2 * i - 3)) (x (2 * i - 2)) → Case1Config S x i →
    Nonempty (Case1Witness S x i)

/-- **§3.8, Case 1** (pp. 348–349), conditional on the named `Prop` `Case1Claims` (§3.3–§3.6).
The ending §3.7 and the facts §3.1–§3.2 are proved (`case1_ending`). -/
theorem case1 (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ) (hC : Case1Claims S x m)
    (i : ℕ) (hi2 : 2 ≤ i) (him : i ≤ m) (hI : Property4 S.D (x (2 * i - 1)) (x (2 * i)))
    (hcfg : Case1Config S x i) : Property4 S.D (x (2 * i - 3)) (x (2 * i - 2)) := by
  by_contra hJ
  obtain ⟨w⟩ := hC i hi2 him hI hJ hcfg
  exact hJ (case1_ending S w.strandI w.strandJ w.first w.between w.far w.band)

/-! ## §4. Case 2, sentence by sentence -/

/-- **The claims of Case 2** (p. 349), one field per printed claim, about the point `yᵢ₋₁` of
E2.1 and the strands `S_I`, `S_J` adjacent to it:
* `first`: "Define `Cᵢ₋₁`, `L`, `yᵢ₋₁`, and `N` as in Case 1";
* (a) `claim_a`: "If `yᵢ₋₁` is above `d⁻¹[J]`, it is between `d⁻¹[I]` and `d⁻¹[J]`";
* (b) `claim_b`: "… and `f(yᵢ₋₁)` is above `d⁻¹[I]`", in the form left after the good case
  (`f(yᵢ₋₁)` below `S_J`, where `J` has Property 4 at once) is split off;
* (c) is proved, not a field: `case2_ending` derives `ρ(yᵢ₋₁, Cl S_I) < ε₃` from (b) by the cap
  lemma (and for `yᵢ` the same holds by Property 4 for `I`);
* (d) `claim_d`: "Since both `yᵢ` and `yᵢ₋₁` are within `ε₃` of `d⁻¹[I]`, it follows as in Case 1
  that a subcontinuum of `L` violates Property 2";
* (e) `claim_e`: "Hence `yᵢ₋₁` is below `d⁻¹[J]` and `f(yᵢ₋₁)` is above" — the part "`f(yᵢ₋₁)` is
  above `d⁻¹[J]`" when `yᵢ₋₁` is below `S_J`, which nothing printed supports (report §4). -/
structure Case2Witness (S : Thm1Setup M) (x : ℕ → unitInterval) (i : ℕ) where
  y : M
  SI : Set Pt
  SJ : Set Pt
  first : S.GoodPoint y
  strandI : S.IsBlockStrand (x (2 * i - 1)) (x (2 * i)) SI
  strandJ : S.IsBlockStrand (x (2 * i - 3)) (x (2 * i - 2)) SJ
  claim_a : (y : Pt) ∈ S.V.above SJ → (y : Pt) ∈ S.V.below SI
  claim_b : (y : Pt) ∈ S.V.above SJ → (y : Pt) ∈ S.V.below SI →
    ((S.D.f y : M) : Pt) ∉ S.V.below SJ → ((S.D.f y : M) : Pt) ∈ S.V.above SI
  claim_d : (y : Pt) ∈ S.V.above SJ → infDist (y : Pt) (closure SI) < S.ε₃ → False
  claim_e : (y : Pt) ∈ S.V.below SJ → ((S.D.f y : M) : Pt) ∈ S.V.above SJ

/-- **Case 2 from its claims** (p. 349). The point `yᵢ₋₁` lies on its strand `C_{yᵢ₋₁}`, which is
below or above `S_J` (S4b: both are pieces, disjoint since `C_{yᵢ₋₁}` misses `F`).
* Below: by (e), `f(yᵢ₋₁)` is above `S_J`; `J` separates.
* Above: by (a) `yᵢ₋₁` is between; if `f(yᵢ₋₁)` is below `S_J`, `J` separates; otherwise (b) puts
  `f(yᵢ₋₁)` above `S_I`, so (c) the cap lemma gives `ρ(yᵢ₋₁, Cl S_I) < ε₃`, against (d). -/
theorem case2_ending (S : Thm1Setup M) (x : ℕ → unitInterval) (i : ℕ) (w : Case2Witness S x i) :
    Property4 S.D (x (2 * i - 3)) (x (2 * i - 2)) := by
  have hy := w.first
  have hdisj : Disjoint w.SJ (S.comp w.y) := by
    refine disjoint_left.2 fun z hzJ hzC => disjoint_left.1 hy.miss hzC ?_
    exact image_mono (layerSet_subset _ _) (w.strandJ.sub hzJ)
  rcases VFrame.piece_sides w.strandJ.piece hy.piece hdisj with h | h
  · have hyb : (w.y : Pt) ∈ S.V.below w.SJ := h hy.mem_comp
    exact property4_of_strand_sep S w.strandJ hy (Or.inr ⟨hyb, w.claim_e hyb⟩)
  · have hya : (w.y : Pt) ∈ S.V.above w.SJ := h hy.mem_comp
    have hyI := w.claim_a hya
    by_cases hfb : ((S.D.f w.y : M) : Pt) ∈ S.V.below w.SJ
    · exact property4_of_strand_sep S w.strandJ hy (Or.inl ⟨hya, hfb⟩)
    · exfalso
      have hfa := w.claim_b hya hyI hfb
      have hd : dist (w.y : Pt) ((S.D.f w.y : M) : Pt) < S.ε₃ := by
        have := S.D.f_small w.y
        rw [Subtype.dist_eq, dist_comm] at this
        exact this
      -- (c): the cap lemma
      have hc := cross_strand_near S w.strandI.crossing w.strandI.piece.sides_disjoint
        (S.K_subset_mid ⟨w.y, hy.mem_K, rfl⟩) hyI hfa hd
      exact w.claim_d hya hc

/-- **Named `Prop`: the open claims of Case 2** (§4 (a), (b), (d), (e)). -/
def Case2Claims (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ) : Prop :=
  ∀ i, 2 ≤ i → i ≤ m → Property4 S.D (x (2 * i - 1)) (x (2 * i)) →
    ¬ Property4 S.D (x (2 * i - 3)) (x (2 * i - 2)) → Case2Config S x i →
    Nonempty (Case2Witness S x i)

/-- **§4, Case 2** (p. 349), conditional on the named `Prop` `Case2Claims`; claim (c) is proved
(`case2_ending`). -/
theorem case2 (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ) (hC : Case2Claims S x m)
    (i : ℕ) (hi2 : 2 ≤ i) (him : i ≤ m) (hI : Property4 S.D (x (2 * i - 1)) (x (2 * i)))
    (hcfg : Case2Config S x i) : Property4 S.D (x (2 * i - 3)) (x (2 * i - 2)) := by
  by_contra hJ
  obtain ⟨w⟩ := hC i hi2 him hI hJ hcfg
  exact hJ (case2_ending S x i w)

/-! ## §5. The step -/

/-- **Named `Prop`: the end layers of `J` and of the gap meet the side segments** (implicit in
"The proof now breaks down into two cases", p. 348): for `2 ≤ i ≤ m`, `d⁻¹(x₂ᵢ₋₁)` and `d⁻¹(x₂ᵢ₋₂)`
each meet `π⁻¹[⟨p₁, r⟩]` or `π⁻¹[⟨p₅, s⟩]`. -/
def BlockLayersMeetSides (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ) : Prop :=
  ∀ i, 2 ≤ i → i ≤ m →
    (∃ a ∈ ({3 / 22, 19 / 22} : Set ℝ), S.LayerMeetsSide (x (2 * i - 1)) a) ∧
    (∃ b ∈ ({3 / 22, 19 / 22} : Set ℝ), S.LayerMeetsSide (x (2 * i - 2)) b)

/-- **§5, the step** (Cases 1–2, pp. 348–349), in its strongest conditional form: from the named
`Prop`s `BlockLayersMeetSides` (the case split), `Case1Claims` (§3.3–§3.6) and `Case2Claims`
(§4 (a), (b), (d), (e)), the induction step `Property4Step` holds. The block hypotheses `IsBlocks`
are not used. -/
theorem hagopian76_property4_step_cond (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ)
    (hsides : BlockLayersMeetSides S x m) (h1 : Case1Claims S x m) (h2 : Case2Claims S x m) :
    Property4Step S.D x m := by
  intro i hi2 him hI
  obtain ⟨hs1, hs2⟩ := hsides i hi2 him
  rcases case1_or_case2 S x i hs1 hs2 with hc | hc
  · exact case1 S x m h1 i hi2 him hI hc
  · exact case2 S x m h2 i hi2 him hI hc

end Thm1

/-- **Theorem 1 from saturation and the claims of Cases 1–2** (the reduction of §5): if, for every
set-up, `InnerComponentsCross` holds (2e) and, for every block sequence, the named `Prop`s
`BlockLayersMeetSides`, `Case1Claims` and `Case2Claims` hold, then every homogeneous indecomposable
plane continuum is hereditarily indecomposable. -/
theorem hagopian76_theorem1_of_cases
    (hICC : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M),
      InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
        (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)))
    (hcases : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M) x m,
      S.IsBlocks x m → BlockLayersMeetSides S x m ∧ Case1Claims S x m ∧ Case2Claims S x m) :
    Hagopian76Thm1 :=
  hagopian76_theorem1_of_step hICC fun M _ _ S x m hx => by
    obtain ⟨hs, h1, h2⟩ := hcases M S x m hx
    exact hagopian76_property4_step_cond S x m hs h1 h2

/-! ## Open items (commission 181 §1; obstructions in `OPEN.md`, batch 181)

**OPEN (§1.1, `noncrossing_half_in_O`).** Shape (report 180 §9): for `y = h(e)` over
`(3/22 + 8/n, 19/22 − 8/n)` whose component `W` in `F ∩ π⁻¹[D]` is not a crossing piece, one half
`K⁻ = F ∩ h[k⁻¹[[0, k(e)]]]` or `K⁺` lies in `π⁻¹[D]`. Obstruction: boundary bumping in the half
`K⁻` (step 1) needs `K⁻` as a continuum through `y` (the component of `K⁻ ∩ O` through `y`), and the
frontier analysis of steps 2–5 needs the closure of `F − E` to meet `E` only in `d⁻¹(e)`; neither is
formalized.

theorem noncrossing_half_in_O (S : Thm1Setup M) (y : M) (e : S.E) (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < S.θ / 4) (hye : h e = y) (hy : (y : Pt) ∈ toPt S.D.G)
    (hym : ∃ q ∈ S.D', S.π y = S.F q ∧ q.1 ∈ Ioo (3/22 + 8/S.n) (19/22 - 8/S.n))
    (hW : ¬ IsCrossingPiece S.π S.F S.D' (3/22) (19/22) S.r₂ S.s₂ S.I₂
      (connectedComponentIn (toPt S.D.G ∩ S.π ⁻¹' (S.F '' S.D')) y)) :
    (∀ e', S.k e' ≤ S.k e → h e' ∈ S.D.G → S.π (h e') ∈ S.F '' S.D') ∨
    (∀ e', S.k e ≤ S.k e' → h e' ∈ S.D.G → S.π (h e') ∈ S.F '' S.D') := by
  sorry

**OPEN (§1.2–§1.3, `chunk_points`).** Needs the void interior of `d⁻¹(1)` in `F` transported to
`F ∩ U`, the finiteness of crossing components through a convergent sequence, and the strand lemma
at `zⱼ` for (iii).

**OPEN (§1.4, `chunk_edge_case`).** Step 3 is proved in parameter form (`chunk_edge_case_mirror`,
`H76TipRel.lean`: the mirror triod needs only `2/n < σ < 1`). Steps 1–2 need the points `zⱼ` and (iii)
at `zⱼ` (§1.2–§1.3). Step 4 (`τ₁ = 1`) is undecided: the configuration is
`d⁻¹(1) ⊇ F ∩ hⱼ[k⁻¹((τ, 1])]` with `F ∩ hⱼ[k⁻¹(1)] ≠ ∅`, i.e. the end layer of `F` contains every
point of `F` on the translate beyond the tip layer, up to the far end layer `hⱼ[k⁻¹(1)]`.

**OPEN (2d `no_end_layer_chunk`, 2e `innerComponentsCross_hagopian`).** Need §1.1–§1.4.

theorem innerComponentsCross_hagopian (S : Thm1Setup M) :
    InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)) := by
  sorry

**OPEN (`hagopian76_property4_step`, `hagopian76_theorem1_final`).** Proved conditionally:
`hagopian76_property4_step_cond`, `hagopian76_theorem1_of_cases`.
-/

end HPC.Hagopian
