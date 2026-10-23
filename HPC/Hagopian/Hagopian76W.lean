import HPC.Hagopian.H76SepCross
import HPC.Hagopian.H76EndLayer
import HPC.Hagopian.H76Blocks
import HPC.Hagopian.H76Comp

/-!
# Batch 178: Hagopian 1976, Theorem 1 — the order of strands without Schoenflies; separation along
# the vertical; the end layer of `F`; unicoherence; the assembly; the step

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 346–349. Route: commission 178 §1–§8.
Skeleton as delivered: `doc/batches/skeletons/Hagopian76W.lean`.

Supporting files:
* `H76Unicoh` — §5: two continua with disconnected intersection separate the plane
  (`borsuk_exists_log`); separation in a domain is separation in the plane with `Y` adjoined;
* `H76Order` — §1, §2 in an abstract **vertical frame** (`VFrame`): pieces, their sides
  `A(X)` (`below`) and `B(X)` (`above`), S4b–S4e, SSL, its converse, the corollary;
* `H76OrderConcrete` — the concrete frame `lowFrame` (`O = π⁻¹[D]`, `σ` the low vertical over
  `t₀`), its hypotheses (`lowFrame_hyps`), crossing pieces (`IsCrossingPiece`), and
  **crossing pieces are pieces** (`isPiece_of_isCrossingPiece`: S4a and the disjointness of the
  sides, from `K0_crosscut_aux` and `crossing_separates_aux`);
* `H76EndLayer` — §3a: `d⁻¹(1) ⊄ π⁻¹[D]`;
* `H76SepCross` — §4.C, conditional: `SepByCrossing` from SSL;
* `H76Blocks` — §6: the blocks of `St J` (finite combinatorics);
* `H76Comp` — §4.A: the composant argument; `exists_T12Data_comp` (the companion
  `exists_T12Data'`, with the base point and both composant conditions).

Shapes are recorded at each statement and in `doc/batches/REPORT-batch178.md`. Items left open are
commented out at the end, with the obstructions in `OPEN.md`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## §5. Unicoherence of the plane -/

/-- **Two continua with disconnected intersection separate the plane** (the converse of
Janiszewski's theorem; unicoherence in separation form). Route (commission 178 §5):
`borsuk_exists_log` applied to `exp(πiφ)` on `A`, `exp(−πiφ)` on `B`,
`φ = d(·, K₁) / (d(·, K₁) + d(·, K₂))` (here an Urysohn function). Statement unchanged. -/
theorem separatesPlane_union_of_inter_disconnected {A B K₁ K₂ : Set Pt} (hA : IsCompact A)
    (hAc : IsConnected A) (hB : IsCompact B) (hBc : IsConnected B) (hK₁ : IsClosed K₁)
    (hK₂ : IsClosed K₂) (hAB : A ∩ B = K₁ ∪ K₂) (hK : Disjoint K₁ K₂) (hK₁n : K₁.Nonempty)
    (hK₂n : K₂.Nonempty) :
    SeparatesPlane (A ∪ B) :=
  separatesPlane_union_of_inter_disconnected_aux hA hAc hB hBc hK₁ hK₂ hAB hK hK₁n hK₂n

/-- **Separation in a domain is separation in the plane with the frontier continuum adjoined**
(commission 178 §3a step 3, §5).

*Shape (left to me):* for `O` open, `Y` disjoint from `O` and containing `Fr O`, and `p, q ∈ O − X`:
`SepIn O X p q ↔ SeparatesPts (X ∪ Y) p q`. Neither compactness nor connectedness of `X` or `Y` is
needed. -/
theorem sepIn_iff_separatesPts_union {O X Y : Set Pt} (hO : IsOpen O) (hYO : Disjoint Y O)
    (hfr : frontier O ⊆ Y) {p q : Pt} (hp : p ∈ O \ X) (hq : q ∈ O \ X) :
    SepIn O X p q ↔ SeparatesPts (X ∪ Y) p q :=
  sepIn_iff_separatesPts_union_aux hO hYO hfr hp hq

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §1. The order of crossing pieces (S4, without Schoenflies)

*Shape (left to me).* The order is developed in an abstract vertical frame `VFrame` (`H76Order`):
`O` open and connected; the vertical `σ` given by `lev P v` ("`P` is the point of `σ` at height
`v`"). A **piece** (`VFrame.IsPiece`) is connected, in `O`, closed in `O`, with compact nonempty
set of `σ`-heights and disjoint sides. `A(X) = V.below X`, `B(X) = V.above X` are commission 178's
sets, with "below `m(X)`" read as "below every height of `Cl X`". `X′ ≺ X` is `X′ ⊆ V.below X`.
Commission 178's crossing pieces are pieces of the concrete frame `lowFrame`
(`isPiece_of_isCrossingPiece`). -/

/-- **S4a**: every crossing piece meets the low vertical `σ` (from `rect_domain_crosscut`,
transported in `K0_crosscut_aux`). *Shape:* the hypotheses of `K0_crosscut_aux`; `σ` is
`π⁻¹F[{x₀} × (0, w₂)]`. -/
theorem crossing_piece_meets_sigma {π : Pt → Pt} {γ : unitInterval → Pt} (hπc : Continuous π)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hc1 : c ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIs : (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) =
      {(a, r₂), (b, s₂)})
    {D' : Set (ℝ × ℝ)} (hDo : IsOpen D') (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    {x₀ w₂ : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hw₂ : w₂ ∈ Ioc 0 c) (hFw : F (x₀, w₂) ∈ I₂)
    (hseg : Disjoint (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    {X : Set Pt} (hX : IsCrossingPiece π F D' a b r₂ s₂ I₂ X) :
    ∃ P ∈ X, π P ∈ F '' (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂) := by
  by_contra h
  push_neg at h
  exact K0_crosscut_aux hπc hF ha hab hb hc1 hI hIs hDo hDR hDf hx₀ hw₂ hFw hseg
    hX.preconnected (fun P hP => ⟨hX.subset_O hP, h P hP⟩) hX.left hX.right

/-- **S4b, totality**: for disjoint pieces `X`, `X′`: `X′ ⊆ A(X)` or `X′ ⊆ B(X)`. -/
theorem crossing_piece_sides {V : VFrame} {X X' : Set Pt} (hX : V.IsPiece X)
    (hX' : V.IsPiece X') (hXX' : Disjoint X X') : X' ⊆ V.below X ∨ X' ⊆ V.above X :=
  VFrame.piece_sides hX hX' hXX'

/-- **S4c, antisymmetry** (symmetric form): `X′ ⊆ A(X) ↔ X ⊆ B(X′)`, for disjoint pieces. -/
theorem crossing_piece_below_iff {V : VFrame} {X X' : Set Pt} (hX : V.IsPiece X)
    (hX' : V.IsPiece X') (hXX' : Disjoint X X') : X' ⊆ V.below X ↔ X ⊆ V.above X' :=
  VFrame.below_iff_above hX hX' hXX'

/-- **S4d, transitivity**: `X″ ≺ X′ ≺ X → X″ ≺ X` (`X″` need only be a set; `X`, `X′` disjoint
pieces). -/
theorem crossing_piece_below_trans {V : VFrame} {X X' X'' : Set Pt} (hX : V.IsPiece X)
    (hX' : V.IsPiece X') (hXX' : Disjoint X X') (h1 : X'' ⊆ V.below X') (h2 : X' ⊆ V.below X) :
    X'' ⊆ V.below X :=
  VFrame.below_trans hX hX' hXX' h1 h2

/-- **S4e, no pocket**: a piece (for example a strand) disjoint from the piece `X` lies in
`A(X) ∪ B(X)`. -/
theorem crossing_piece_no_pocket {V : VFrame} {X S : Set Pt} (hX : V.IsPiece X)
    (hS : V.IsPiece S) (hXS : Disjoint X S) : S ⊆ V.below X ∪ V.above X :=
  VFrame.no_pocket hX hS hXS

/-! ## §2. Separation along the vertical -/

/-- **SSL**: if `Z` separates `x` from `y` in `O`, and `x`, `y` lie on pieces `X`, `Y` (equal or
disjoint) missing `Z`, then `X ≠ Y`, they are ordered, some `z ∈ Z ∩ σ` lies between them, and if
the component `W_z` of `Z ∩ O` is a piece, `Cl W_z` separates `x` from `y`.

*Shape:* `Z` is any set (compactness is not used); "between" is `z ∈ A(X) ∩ B(Y)` (or the
symmetric case); the closest-points construction of step 2 is inside the proof
(`VFrame.exists_sep_point`). -/
theorem strand_separation {V : VFrame} {X Y Z : Set Pt} {x y : Pt} (hX : V.IsPiece X)
    (hY : V.IsPiece Y) (hXY : X = Y ∨ Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hx : x ∈ X) (hy : y ∈ Y) (hsep : SepIn V.O Z x y) :
    X ≠ Y ∧ Disjoint X Y ∧ (Y ⊆ V.below X ∨ X ⊆ V.below Y) ∧
      ∃ z ∈ Z, (∃ v, V.lev z v) ∧
        ((z ∈ V.below X ∧ z ∈ V.above Y) ∨ (z ∈ V.below Y ∧ z ∈ V.above X)) ∧
        (V.IsPiece (connectedComponentIn (Z ∩ V.O) z) →
          SepIn V.O (closure (connectedComponentIn (Z ∩ V.O) z)) x y) :=
  VFrame.strand_separation hX hY hXY hXZ hYZ hx hy hsep

/-- **SSL, converse**: a piece `W` with `Y ≺ W ≺ X` (here `Y ⊆ A(W)`, `X ⊆ B(W)`) separates
`x ∈ X` from `y ∈ Y` in `O`. -/
theorem strand_separation_converse {V : VFrame} {W X Y : Set Pt} {x y : Pt} (hW : V.IsPiece W)
    (hY : Y ⊆ V.below W) (hX : X ⊆ V.above W) (hx : x ∈ X) (hy : y ∈ Y) :
    SepIn V.O (closure W) x y :=
  VFrame.sepIn_of_between hW hY hX hx hy

/-- **`SepByCrossing`, general form**: if every component of `Z ∩ O` meeting `σ` is a piece, and
`x`, `y` lie on pieces missing `Z`, then `SepIn O Z x y` gives separation by the closure of one
such component. -/
theorem sepByCrossing_of_inner_crossing {V : VFrame} {X Y Z : Set Pt} {x y : Pt}
    (hZ : ∀ z ∈ Z ∩ V.O, (∃ v, V.lev z v) → V.IsPiece (connectedComponentIn (Z ∩ V.O) z))
    (hX : V.IsPiece X) (hY : V.IsPiece Y) (hXY : X = Y ∨ Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) (hx : x ∈ X) (hy : y ∈ Y) (hsep : SepIn V.O Z x y) :
    ∃ z ∈ Z ∩ V.O, (∃ v, V.lev z v) ∧ V.IsPiece (connectedComponentIn (Z ∩ V.O) z) ∧
      SepIn V.O (closure (connectedComponentIn (Z ∩ V.O) z)) x y :=
  VFrame.sepByCrossing_of_inner_crossing hZ hX hY hXY hXZ hYZ hx hy hsep

/-! ## §3. The end layer of `F`, and saturation -/

/-- **3a**: for a `T12Data` package, `d⁻¹(1) ⊄ π⁻¹[D]` (irreducibility, Janiszewski,
`no_proper_subcontinuum_separates`). *Shape:* the set-up of `exists_T12Data` restricted to what
is used (the collar, the cross region, the arc `I₂` and the frontier of `D`). -/
theorem T12Data.end_layer_not_subset (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    {γ : unitInterval → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {c₁ : ℝ} (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D')
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((3 / 22, r₂) : ℝ × ℝ) (19 / 22, s₂)
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (hIR : I₂ ⊆ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc (3 / 22) (19 / 22) ×ˢ {0}) ∪
        F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂) ∪ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂))
    {ε₃ : ℝ} (D : T12Data E k π F D' ε₃) :
    ¬ toPt (layer D.d 1) ⊆ π ⁻¹' (F '' D') := by
  obtain ⟨hYk, -, hYO, hfr⟩ := pi_preimage_frontier_D_aux hE hπ hπS hF (by norm_num)
    (by norm_num) (by norm_num) hc₁ hI hIR hR.isOpen hFDf
  have hdisj : Disjoint (π ⁻¹' (F '' D')) (toPt E) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨m, hmE, rfl⟩
    exact Set.disjoint_left.1 (crossSet_disjoint_E hγπ hF hc₁ hR.sub E) ⟨hmE, hx⟩ hmE
  exact T12Data.end_layer_not_subset_aux hX hi hE D (hR.isOpen.preimage hπ.continuous) hdisj hYk
    hYO hfr

/-- **Named `Prop` `InnerComponentsCross`** (commission 178 §3b, if it stays open): every component
of `G ∩ π⁻¹[D]` through a point over an abscissa in `(lo, hi)` is a crossing piece. For
Hagopian's `F` and `(lo, hi)` the inner middle `(3/22 + 2/n, 19/22 − 2/n)` this is item 3b. -/
def InnerComponentsCross (G : Set M) (π : Pt → Pt) (F : ℝ × ℝ → Pt) (D' : Set (ℝ × ℝ))
    (a b r₂ s₂ : ℝ) (I₂ : Set Pt) (lo hi : ℝ) : Prop :=
  ∀ z ∈ toPt G ∩ π ⁻¹' (F '' D'), (∃ q ∈ D', π z = F q ∧ q.1 ∈ Ioo lo hi) →
    IsCrossingPiece π F D' a b r₂ s₂ I₂ (connectedComponentIn (toPt G ∩ π ⁻¹' (F '' D')) z)

/-! ## §4. The strands of `p`, `f(p)`; `SepByCrossing`, the conditional form -/

/-- **4.A**: the strands that matter miss `F`, by composants (commission 178 §4.A).

*Shape (left to me):* in the set-up of `exists_T12Data`, there is a package `D` with base point
`x₀ ∈ k⁻¹(t₀)`, `D.p = D.h x₀`, such that every proper subcontinuum of `M` through a point of
`h[R(E)] ∪ h₁[R(E)]` misses `F = D.G`. The closure of a strand is such a subcontinuum
(`strand_lemma`), and `p = h x₀`, `f(p) = h₁ x₀` are such points. The composant conditions are
exported by `exists_T12Data_comp` (no field added to `T12Data`). -/
theorem strand_misses_F_of_composant (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D')
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc (3 / 22) (19 / 22) ×ˢ Ico (-c') 0)) (π '' M))
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((3 / 22, r₂) : ℝ × ℝ) (19 / 22, s₂)
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (hIs : (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∩
      (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) = {(3 / 22, r₂), (19 / 22, s₂)})
    (hIR : I₂ ⊆ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁)) (hDo : IsOpen D')
    (hDf : frontier D' = (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∪
        Icc (3 / 22) (19 / 22) ×ˢ {0} ∪ ({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂ ∪
        ({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc (3 / 22) (19 / 22) ×ˢ {0}) ∪
        F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂) ∪ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂))
    {t₀ w₂ : ℝ} (ht₀1 : 3 / 22 + 2 / (n : ℝ) ≤ t₀) (ht₀2 : t₀ ≤ 19 / 22 - 2 / (n : ℝ))
    (hw₂ : w₂ ∈ Ioc 0 c₁) (hFw : F (t₀, w₂) ∈ I₂)
    (hseg : Disjoint (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂)
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (K₀ : Set M) {ε₃ : ℝ} (hε₃ : 0 < ε₃) :
    ∃ D : T12Data E k π F D' ε₃, D.K = insert D.p K₀ ∧ ∃ x : E, (k x : ℝ) = t₀ ∧ D.p = D.h x ∧
      ∀ z ∈ D.h '' Rset k ∪ D.h₁ '' Rset k, ∀ K : Set M, Fold.Q78.IsContinuum K → K ≠ univ →
        z ∈ K → Disjoint K D.G  :=
  exists_T12Data_strands hX hi hE hπ hπS hγπ hF hS hn hc₁ hR hbelow hI hIs hIR hDo hDf hFDf ht₀1
    ht₀2 hw₂ hFw hseg K₀ hε₃


omit [ConnectedSpace M] in
/-- **4.C, conditional** (commission 178 §4.C): in the frame of the low vertical over `x₀` (with
`x₀` in `(lo, hi)`), `InnerComponentsCross` for `G` and crossing pieces `X ∋ p`, `Y ∋ q` missing
`G` (for Hagopian: the strands of `p` and `f(p)`, item 4.A–B) give `SepByCrossing G … p q`.

*Shape:* the hypotheses of `crossing_sides` with `a = 3/22`, `b = 19/22`, `c = c₁`, plus those of
`lowFrame` (`lowFrame_hyps` discharges the connectedness ones when `π⁻¹[D]` misses `E`). -/
theorem sep_by_crossing {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπc : Continuous π) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {c₁ : ℝ} (hc1 : c₁ ≤ 1)
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((3 / 22, r₂) : ℝ × ℝ) (19 / 22, s₂)
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (hIs : (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∩
      (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) = {(3 / 22, r₂), (19 / 22, s₂)})
    {D' : Set (ℝ × ℝ)} (hDo : IsOpen D') (hDR : D' ⊆ Ioo (3 / 22) (19 / 22) ×ˢ Ioo 0 c₁)
    (hDf : frontier D' = (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∪
        Icc (3 / 22) (19 / 22) ×ˢ {0} ∪ ({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂ ∪
        ({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂)
    {x₀ w₂ : ℝ} (hx₀ : x₀ ∈ Ioo (3 / 22) (19 / 22)) (hw₂ : w₂ ∈ Ioc 0 c₁)
    (hFw : F (x₀, w₂) ∈ I₂)
    (hseg : Disjoint (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (hOo : IsOpen (π ⁻¹' (F '' D'))) (hOc : IsPreconnected (π ⁻¹' (F '' D')))
    (hsub : ({x₀} : Set ℝ) ×ˢ Ioo 0 w₂ ⊆ D') (hπinj : InjOn π (π ⁻¹' (F '' D')))
    (hsurj : Function.Surjective π)
    (hsegc : ∀ J : Set ℝ, IsPreconnected J →
      IsPreconnected (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ (J ∩ Ioo 0 w₂)))))
    {G : Set M} (hG : IsClosed G) {lo hi : ℝ} (hlo : lo < x₀) (hhi : x₀ < hi)
    (hICC : InnerComponentsCross G π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ lo hi)
    {X Y : Set Pt} {p q : Pt}
    (hX : IsCrossingPiece π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ X)
    (hY : IsCrossingPiece π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ Y)
    (hXY : X = Y ∨ Disjoint X Y) (hXG : Disjoint X (toPt G)) (hYG : Disjoint Y (toPt G))
    (hp : p ∈ X) (hq : q ∈ Y) :
    SepByCrossing G π F c₁ D' (π ⁻¹' (F '' D')) p q := by
  refine sepByCrossing_of_sigma_pieces hπc hF hc1 hI hIs hDo hDR hDf hx₀ hw₂ hFw hseg hOo hOc
    hsub hπinj hsurj hsegc hG (fun z hz hzσ => hICC z hz ?_) hX hY hXY hXG hYG hp hq
  obtain ⟨w, ⟨hw1, hw2⟩, hFw'⟩ := hzσ
  refine ⟨w, hsub ⟨hw1, hw2⟩, hFw'.symm, ?_⟩
  rw [show w.1 = x₀ from hw1]
  exact ⟨hlo, hhi⟩

/-! ## §6. The blocks -/

omit [CompactSpace M] [ConnectedSpace M] in
/-- **C′**: the blocks are the components of `St J`; each block is a union of members of `J`;
`x₁ = 0`, `x₂ = e`, `x₂ₙ = 1`; no member of `J` meets a gap.

*Shape:* the inputs are hypotheses: `e` from `hagopian76_J_xs`, finiteness from
`hagopian76_I_finite`, `x₂ₙ = 1` as `LastIntervalReachesOne` (§4), and **the members of `I` are
nondegenerate** (`r₁ < r₂`), which is not proved: a crossing component inside one layer would give an
isolated block `[u, u]`, incompatible with strict monotonicity. The conclusion contains the block
data of `hagopian76_T15_T17_cond2`, plus the union and gap clauses of commission 178 §6. -/
theorem exists_blocks {G : Set M} {d : G → unitInterval} {π : Pt → Pt} {F : ℝ × ℝ → Pt}
    {c₁ : ℝ} {D' : Set (ℝ × ℝ)} {E : Set M} {e : unitInterval} (he0 : 0 < e)
    (hE : layerSet d (Icc 0 e) = E) (he : ∀ p ∈ crossingIntervals d π F c₁ D', e < p.1)
    (hfin : (crossingIntervals d π F c₁ D').Finite)
    (hnd : ∀ p ∈ crossingIntervals d π F c₁ D', p.1 < p.2)
    (hlast : LastIntervalReachesOne d π F c₁ D') :
    ∃ (x : ℕ → unitInterval) (n : ℕ), 2 ≤ n ∧ StrictMonoOn x (Icc 1 (2 * n)) ∧ x 1 = 0 ∧
      layerSet d (Icc 0 (x 2)) = E ∧
      (∀ r ∈ crossingIntervals d π F c₁ D', ∃ i, 1 ≤ i ∧ i ≤ n ∧
        x (2 * i - 1) ≤ r.1 ∧ r.2 ≤ x (2 * i)) ∧
      x (2 * n) = 1 ∧
      (∀ i, 1 ≤ i → i ≤ n → ∀ t ∈ Icc (x (2 * i - 1)) (x (2 * i)),
        t ≤ e ∨ ∃ r ∈ crossingIntervals d π F c₁ D', t ∈ Icc r.1 r.2) ∧
      (∀ i, 1 ≤ i → i < n → ∀ r ∈ crossingIntervals d π F c₁ D',
        r.2 ≤ x (2 * i) ∨ x (2 * i + 1) ≤ r.1) :=
  exists_blocks_aux he0 hE he hfin hnd hlast

end Thm1

/-! ## Open items

The obstructions are in `OPEN.md` (batch 178) and in `doc/batches/REPORT-batch178.md`.

**OPEN (3b, `inner_components_cross`).** Named as `InnerComponentsCross`. The set-up (S1, the
continua `K⁻`, `K⁺`, boundary bumping) and case 2 of the route are routine; case 3.3 (the end layer
`d⁻¹(1)` swallowing a chunk `h[k⁻¹((τ, τ₁))]` through `y`) is not settled by the three named tools:
see the report, §3b.

theorem inner_components_cross … : InnerComponentsCross D.G π F D' (3 / 22) (19 / 22) r₂ s₂ I₂
    (3 / 22 + 2 / n) (19 / 22 - 2 / n) := by
  sorry

-- `block_components_cross` (3c): proved in batch 181 (`H76Block3c.lean`), with saturation as a hypothesis.

-- `strand_misses_F_of_composant` (4.A): proved above.

-- `p_on_crossing_piece` (4.B): proved in batch 179 (`H76PieceB.lean`), with `Disjoint I₂ (π '' M)`.

**OPEN (4.C, `hagopian76_x2n_eq_one_final`, `hagopian76_property4_top_final`).** From
`sep_by_crossing` (proved, conditional on `InnerComponentsCross` and on crossing pieces through
`p`, `f(p)` missing `F`) via `hagopian76_x2n_eq_one` and `hagopian76_property4_top`; the
unconditional forms wait on 3b and 4.A–B.

theorem hagopian76_x2n_eq_one_final … : LastIntervalReachesOne D.d π F c₁ D' := by
  sorry

theorem hagopian76_property4_top_final … : Property4 D s₂ 1 := by
  sorry

-- `exists_blocks` (§6): proved above, with nondegeneracy of the members of `I` as a hypothesis.

-- `crossingIntervals_nondegenerate` (§6): proved in batch 179 (`H76Uniform2.lean`), from Property 3.

-- `hagopian76_theorem1_of_step` (§7): proved in batch 179 (`H76Thm1Setup.lean`), with `InnerComponentsCross` as a second hypothesis.

**OPEN (§8, E0–E2.6, `hagopian76_property4_step`).** See `doc/notes/hagopian76-cases.md`.

-- `property4_step_unless` (E0, E1): proved in batch 181 (`property4_strand`, `property4_step_unless_setup`, `Hagopian76Z.lean`).

theorem hagopian76_property4_step … : Property4Step D x n := by
  sorry

**OPEN (`hagopian76_theorem1_final`).** The strongest conditional form remains
`hagopian76_T15_T17_cond2` together with `sep_by_crossing`.

-- `hagopian76_theorem1_final`: proved in batch 190 as `hagopian76_theorem1`, `Jones75B.lean`.
-/

end HPC.Hagopian
