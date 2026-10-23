import HPC.Hagopian.H76Sides
import HPC.Hagopian.H76ChainSep

/-!
# Batch 178, §1–§2: the order of crossing pieces without Schoenflies; separation along the vertical

This file works in an **abstract vertical frame** (`VFrame`): an open connected `O ⊆ R²` and a
"vertical" `σ ⊆ O`, given by a relation `lev P v` ("`P` is the point of `σ` at height `v`"), with
heights in `(0, w)`, one point per height, every height occupied, and the points over any interval
of heights forming a connected set. The concrete frame (the low vertical `σ = π⁻¹F[{t₀} × (0, w₂)]`
in `O = π⁻¹[D]`) is built in `H76OrderConcrete.lean`.

A **piece** (`VFrame.IsPiece`) is a connected `X ⊆ O`, closed in `O`, whose set of `σ`-heights
`hts X` is compact and nonempty, and whose two sides `below X` and `above X` are disjoint. The two
sides are defined as in `belowSet` / `aboveSet` (batch 169): the points of `O − Cl X` joined in
`O − Cl X` to a point of `σ` below (above) every height of `Cl X`. Commission 178's crossing pieces
are pieces of the concrete frame (`H76OrderConcrete.lean`): disjointness of the sides is
`crossing_sides`, nonemptiness of the heights is `rect_domain_crosscut` (via `K0_crosscut_aux`).

Proved here, with no further plane topology (commission 178 §1, §2):
* **S4b** `VFrame.piece_sides`: for disjoint pieces, `X′ ⊆ A(X)` or `X′ ⊆ B(X)`;
* **S4c** `VFrame.below_iff_above`: `X′ ⊆ A(X) ↔ X ⊆ B(X′)` (the clopen argument);
* **S4d** `VFrame.below_trans`;
* **S4e** `VFrame.no_pocket`;
* **SSL** `VFrame.strand_separation` and its converse `VFrame.sepIn_of_between`;
* **the corollary** `VFrame.sepByCrossing_of_inner_crossing`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane

/-- **An abstract vertical frame** (commission 178 §1): an open connected `O`, and a vertical
`σ = {P | ∃ v, lev P v} ⊆ O` with heights in `(0, w)`, one point at each height, and connected
pieces over intervals of heights. -/
structure VFrame where
  /-- the domain (`π⁻¹[D]`) -/
  O : Set Pt
  /-- the height of the top of `σ` (the lowest point of `I₂` over `t₀`) -/
  w : ℝ
  /-- `lev P v`: `P` is the point of `σ` at height `v` -/
  lev : Pt → ℝ → Prop
  isOpen_O : IsOpen O
  isPreconnected_O : IsPreconnected O
  lev_mem : ∀ P v, lev P v → P ∈ O
  lev_pos : ∀ P v, lev P v → v ∈ Ioo 0 w
  lev_inj : ∀ P Q v, lev P v → lev Q v → P = Q
  lev_exists : ∀ v ∈ Ioo 0 w, ∃ P, lev P v
  seg_preconnected : ∀ J : Set ℝ, IsPreconnected J → IsPreconnected {P | ∃ t ∈ J, lev P t}

namespace VFrame

variable (V : VFrame)

/-- The `σ`-heights of `Cl X`. -/
def hts (X : Set Pt) : Set ℝ := {v | ∃ P ∈ closure X, V.lev P v}

/-- `A(X)`: the points of `O − Cl X` joined in `O − Cl X` to a point of `σ` below `Cl X`. -/
def below (X : Set Pt) : Set Pt :=
  {P | ∃ S : Set Pt, IsPreconnected S ∧ S ⊆ V.O \ closure X ∧ P ∈ S ∧
    ∃ P₀ ∈ S, ∃ v, V.lev P₀ v ∧ ∀ u ∈ V.hts X, v < u}

/-- `B(X)`: the points of `O − Cl X` joined in `O − Cl X` to a point of `σ` above `Cl X`. -/
def above (X : Set Pt) : Set Pt :=
  {P | ∃ S : Set Pt, IsPreconnected S ∧ S ⊆ V.O \ closure X ∧ P ∈ S ∧
    ∃ P₀ ∈ S, ∃ v, V.lev P₀ v ∧ ∀ u ∈ V.hts X, u < v}

/-- **A piece** (commission 178 §1, abstracted): connected, in `O`, closed in `O`, with compact
nonempty set of `σ`-heights, and with disjoint sides. -/
structure IsPiece (X : Set Pt) : Prop where
  preconnected : IsPreconnected X
  subset_O : X ⊆ V.O
  closure_inter : closure X ∩ V.O ⊆ X
  hts_compact : IsCompact (V.hts X)
  hts_nonempty : (V.hts X).Nonempty
  sides_disjoint : Disjoint (V.below X) (V.above X)

variable {V}

/-! ### Elementary facts about the sides -/

theorem below_subset (X : Set Pt) : V.below X ⊆ V.O \ closure X := by
  rintro P ⟨S, -, hSO, hPS, -⟩; exact hSO hPS

theorem above_subset (X : Set Pt) : V.above X ⊆ V.O \ closure X := by
  rintro P ⟨S, -, hSO, hPS, -⟩; exact hSO hPS

/-- A connected subset of `O − Cl X` meeting `A(X)` lies in `A(X)`. -/
theorem subset_below {X S : Set Pt} (hS : IsPreconnected S) (hSO : S ⊆ V.O \ closure X)
    {Q : Pt} (hQS : Q ∈ S) (hQ : Q ∈ V.below X) : S ⊆ V.below X := by
  obtain ⟨S', hS', hS'O, hQS', P₀, hP₀, v, hv, hvu⟩ := hQ
  intro P hP
  exact ⟨S ∪ S', hS.union Q hQS hQS' hS', union_subset hSO hS'O, Or.inl hP, P₀, Or.inr hP₀, v,
    hv, hvu⟩

/-- A connected subset of `O − Cl X` meeting `B(X)` lies in `B(X)`. -/
theorem subset_above {X S : Set Pt} (hS : IsPreconnected S) (hSO : S ⊆ V.O \ closure X)
    {Q : Pt} (hQS : Q ∈ S) (hQ : Q ∈ V.above X) : S ⊆ V.above X := by
  obtain ⟨S', hS', hS'O, hQS', P₀, hP₀, v, hv, hvu⟩ := hQ
  intro P hP
  exact ⟨S ∪ S', hS.union Q hQS hQS' hS', union_subset hSO hS'O, Or.inl hP, P₀, Or.inr hP₀, v,
    hv, hvu⟩

/-- A connected subset of `O − Cl X` containing a point of `σ` below `Cl X` lies in `A(X)`. -/
theorem subset_below_of_lev {X S : Set Pt} (hS : IsPreconnected S) (hSO : S ⊆ V.O \ closure X)
    {Q : Pt} (hQS : Q ∈ S) {v : ℝ} (hv : V.lev Q v) (hvu : ∀ u ∈ V.hts X, v < u) :
    S ⊆ V.below X :=
  fun _ hP => ⟨S, hS, hSO, hP, Q, hQS, v, hv, hvu⟩

theorem subset_above_of_lev {X S : Set Pt} (hS : IsPreconnected S) (hSO : S ⊆ V.O \ closure X)
    {Q : Pt} (hQS : Q ∈ S) {v : ℝ} (hv : V.lev Q v) (hvu : ∀ u ∈ V.hts X, u < v) :
    S ⊆ V.above X :=
  fun _ hP => ⟨S, hS, hSO, hP, Q, hQS, v, hv, hvu⟩

/-- A point of `σ` at a height not in `hts X` is not in `Cl X`. -/
theorem notMem_closure_of_lev {X : Set Pt} {Q : Pt} {v : ℝ} (hv : V.lev Q v)
    (hvX : v ∉ V.hts X) : Q ∉ closure X := fun h => hvX ⟨Q, h, hv⟩

/-- A point of `σ` below `Cl X` is in `A(X)`. -/
theorem mem_below_of_lev {X : Set Pt} {Q : Pt} {v : ℝ} (hv : V.lev Q v)
    (hvu : ∀ u ∈ V.hts X, v < u) : Q ∈ V.below X :=
  subset_below_of_lev isPreconnected_singleton
    (singleton_subset_iff.2 ⟨V.lev_mem Q v hv,
      notMem_closure_of_lev hv fun h => lt_irrefl _ (hvu v h)⟩) rfl hv hvu rfl

theorem mem_above_of_lev {X : Set Pt} {Q : Pt} {v : ℝ} (hv : V.lev Q v)
    (hvu : ∀ u ∈ V.hts X, u < v) : Q ∈ V.above X :=
  subset_above_of_lev isPreconnected_singleton
    (singleton_subset_iff.2 ⟨V.lev_mem Q v hv,
      notMem_closure_of_lev hv fun h => lt_irrefl _ (hvu v h)⟩) rfl hv hvu rfl

/-- The segment of `σ` over the heights `J` (`J ⊆ (0, w)` not needed: heights are automatic). -/
def seg (V : VFrame) (J : Set ℝ) : Set Pt := {P | ∃ t ∈ J, V.lev P t}

theorem seg_subset_O (J : Set ℝ) : V.seg J ⊆ V.O := by
  rintro P ⟨t, -, ht⟩; exact V.lev_mem P t ht

theorem isOpen_below {X : Set Pt} : IsOpen (V.below X) :=
  isOpen_joined (T := {P₀ | ∃ v, V.lev P₀ v ∧ ∀ u ∈ V.hts X, v < u})
    (V.isOpen_O.sdiff isClosed_closure)

theorem isOpen_above {X : Set Pt} : IsOpen (V.above X) :=
  isOpen_joined (T := {P₀ | ∃ v, V.lev P₀ v ∧ ∀ u ∈ V.hts X, u < v})
    (V.isOpen_O.sdiff isClosed_closure)

/-- A point of `O − Cl X` in the closure of `A(X)` is in `A(X)`. -/
theorem mem_below_of_mem_closure {X : Set Pt} {P : Pt} (hP : P ∈ V.O \ closure X)
    (hPc : P ∈ closure (V.below X)) : P ∈ V.below X := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (V.isOpen_O.sdiff isClosed_closure) P hP
  obtain ⟨Q, hQb, hQ⟩ := mem_closure_iff.1 hPc _ isOpen_ball (mem_ball_self hr)
  exact subset_below (convex_ball P r).isPreconnected hball hQb hQ (mem_ball_self hr)

theorem mem_above_of_mem_closure {X : Set Pt} {P : Pt} (hP : P ∈ V.O \ closure X)
    (hPc : P ∈ closure (V.above X)) : P ∈ V.above X := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (V.isOpen_O.sdiff isClosed_closure) P hP
  obtain ⟨Q, hQb, hQ⟩ := mem_closure_iff.1 hPc _ isOpen_ball (mem_ball_self hr)
  exact subset_above (convex_ball P r).isPreconnected hball hQb hQ (mem_ball_self hr)

/-! ### Pieces -/

namespace IsPiece

variable {X : Set Pt}

theorem hts_pos (_hX : V.IsPiece X) {u : ℝ} (hu : u ∈ V.hts X) : u ∈ Ioo 0 V.w := by
  obtain ⟨P, -, hP⟩ := hu; exact V.lev_pos P u hP

/-- The least height `m(X)`. -/
noncomputable def lo (_hX : V.IsPiece X) : ℝ := sInf (V.hts X)

/-- The greatest height `M(X)`. -/
noncomputable def hi (_hX : V.IsPiece X) : ℝ := sSup (V.hts X)

theorem lo_mem (hX : V.IsPiece X) : hX.lo ∈ V.hts X := hX.hts_compact.sInf_mem hX.hts_nonempty

theorem hi_mem (hX : V.IsPiece X) : hX.hi ∈ V.hts X := hX.hts_compact.sSup_mem hX.hts_nonempty

theorem lo_le (hX : V.IsPiece X) {u : ℝ} (hu : u ∈ V.hts X) : hX.lo ≤ u :=
  csInf_le hX.hts_compact.bddBelow hu

theorem le_hi (hX : V.IsPiece X) {u : ℝ} (hu : u ∈ V.hts X) : u ≤ hX.hi :=
  le_csSup hX.hts_compact.bddAbove hu

/-- A point of `σ` at a height of `Cl X` lies in `X`. -/
theorem mem_of_lev (hX : V.IsPiece X) {P : Pt} {v : ℝ} (hv : V.lev P v) (hvX : v ∈ V.hts X) :
    P ∈ X := by
  obtain ⟨Q, hQX, hQ⟩ := hvX
  rw [V.lev_inj P Q v hv hQ]
  exact hX.closure_inter ⟨hQX, V.lev_mem Q v hQ⟩

theorem nonempty (hX : V.IsPiece X) : X.Nonempty := by
  obtain ⟨u, P, hP, hu⟩ := hX.hts_nonempty
  exact ⟨P, hX.mem_of_lev hu ⟨P, hP, hu⟩⟩

/-- A set in `O` missing `X` misses `Cl X`. -/
theorem disjoint_closure (hX : V.IsPiece X) {Y : Set Pt} (hYO : Y ⊆ V.O) (hXY : Disjoint X Y) :
    Disjoint (closure X) Y :=
  disjoint_left.2 fun _ hPc hPY => disjoint_left.1 hXY (hX.closure_inter ⟨hPc, hYO hPY⟩) hPY

theorem subset_diff_closure (hX : V.IsPiece X) {Y : Set Pt} (hYO : Y ⊆ V.O)
    (hXY : Disjoint X Y) : Y ⊆ V.O \ closure X :=
  fun _ hP => ⟨hYO hP, disjoint_right.1 (hX.disjoint_closure hYO hXY) hP⟩

/-- Disjoint pieces have disjoint heights. -/
theorem hts_disjoint (hX : V.IsPiece X) {Y : Set Pt} (hY : V.IsPiece Y) (hXY : Disjoint X Y)
    {u : ℝ} (huX : u ∈ V.hts X) (huY : u ∈ V.hts Y) : False := by
  obtain ⟨P, -, hP⟩ := id huX
  exact disjoint_left.1 hXY (hX.mem_of_lev hP huX) (hY.mem_of_lev hP huY)

/-- The point of `X` at the least height. -/
theorem exists_lo (hX : V.IsPiece X) : ∃ P ∈ X, V.lev P hX.lo := by
  obtain ⟨P, -, hP⟩ := hX.lo_mem
  exact ⟨P, hX.mem_of_lev hP hX.lo_mem, hP⟩

theorem exists_hi (hX : V.IsPiece X) : ∃ P ∈ X, V.lev P hX.hi := by
  obtain ⟨P, -, hP⟩ := hX.hi_mem
  exact ⟨P, hX.mem_of_lev hP hX.hi_mem, hP⟩

end IsPiece

/-! ### S4b: totality -/

/-- **S4b (totality)**: if `X`, `X′` are disjoint pieces, then `X′ ⊆ A(X)` or `X′ ⊆ B(X)`. -/
theorem piece_sides {X X' : Set Pt} (hX : V.IsPiece X) (hX' : V.IsPiece X')
    (hXX' : Disjoint X X') : X' ⊆ V.below X ∨ X' ⊆ V.above X := by
  have hX'O := hX.subset_diff_closure hX'.subset_O hXX'
  have hXO := hX'.subset_diff_closure hX.subset_O hXX'.symm
  by_cases hlow : ∃ v ∈ V.hts X', ∀ u ∈ V.hts X, v < u
  · obtain ⟨v, hv, hvu⟩ := hlow
    obtain ⟨P, -, hP⟩ := id hv
    exact Or.inl (subset_below_of_lev hX'.preconnected hX'O (hX'.mem_of_lev hP hv) hP hvu)
  by_cases hhigh : ∃ v ∈ V.hts X', ∀ u ∈ V.hts X, u < v
  · obtain ⟨v, hv, hvu⟩ := hhigh
    obtain ⟨P, -, hP⟩ := id hv
    exact Or.inr (subset_above_of_lev hX'.preconnected hX'O (hX'.mem_of_lev hP hv) hP hvu)
  exfalso
  push_neg at hlow hhigh
  -- `m(X) < ` every height of `X′`, and `M(X) >` every height of `X′`
  have hlo : ∀ v ∈ V.hts X', hX.lo < v := by
    intro v hv
    obtain ⟨u, hu, huv⟩ := hlow v hv
    refine lt_of_le_of_ne ((hX.lo_le hu).trans huv) fun h => ?_
    exact hX.hts_disjoint hX' hXX' hX.lo_mem (h ▸ hv)
  have hhi : ∀ v ∈ V.hts X', v < hX.hi := by
    intro v hv
    obtain ⟨u, hu, huv⟩ := hhigh v hv
    refine lt_of_le_of_ne (huv.trans (hX.le_hi hu)) fun h => ?_
    exact hX.hts_disjoint hX' hXX' hX.hi_mem (h ▸ hv)
  obtain ⟨P, hPX, hP⟩ := hX.exists_lo
  obtain ⟨Q, hQX, hQ⟩ := hX.exists_hi
  have h1 : X ⊆ V.below X' := subset_below_of_lev hX.preconnected hXO hPX hP hlo
  have h2 : Q ∈ V.above X' := mem_above_of_lev hQ hhi
  exact disjoint_left.1 hX'.sides_disjoint (h1 hQX) h2

/-! ### S4c: antisymmetry -/

/-- `B(X) ⊆ B(X′)` when `X′ ⊆ A(X)`. -/
theorem above_subset_above {X X' : Set Pt} (hX : V.IsPiece X) (hX' : V.IsPiece X')
    (h : X' ⊆ V.below X) : V.above X ⊆ V.above X' := by
  -- `B(X)` misses `Cl X′`
  have hmiss : ∀ P ∈ V.above X, P ∉ closure X' := fun P hP hPc =>
    disjoint_left.1 hX.sides_disjoint (h (hX'.closure_inter ⟨hPc, (above_subset X hP).1⟩)) hP
  have hBO : V.above X ⊆ V.O \ closure X' := fun P hP => ⟨(above_subset X hP).1, hmiss P hP⟩
  rintro P ⟨S, hS, hSO, hPS, P₀, hP₀S, v, hv, hvu⟩
  have hSB : S ⊆ V.above X := subset_above_of_lev hS hSO hP₀S hv hvu
  -- the segment above `M(X)`
  set Sg := V.seg (Ioo hX.hi V.w) with hSg
  have hSgB : Sg ⊆ V.above X := by
    rintro Q ⟨t, ht, hQ⟩
    exact mem_above_of_lev hQ fun u hu => (hX.le_hi hu).trans_lt ht.1
  have hP₀Sg : P₀ ∈ Sg := ⟨v, ⟨hvu _ hX.hi_mem, (V.lev_pos P₀ v hv).2⟩, hv⟩
  have hT : IsPreconnected (S ∪ Sg) :=
    hS.union P₀ hP₀S hP₀Sg (V.seg_preconnected _ isPreconnected_Ioo)
  -- a point of the segment above both `M(X)` and `M(X′)`
  have hw1 := (hX.hts_pos hX.hi_mem).2
  have hw2 := (hX'.hts_pos hX'.hi_mem).2
  set t := (max hX.hi hX'.hi + V.w) / 2 with ht
  have htw : t ∈ Ioo 0 V.w := ⟨by
    have := (hX.hts_pos hX.hi_mem).1
    have := le_max_left hX.hi hX'.hi
    linarith, by have := max_lt hw1 hw2; linarith⟩
  obtain ⟨Q, hQ⟩ := V.lev_exists t htw
  have htX : hX.hi < t := by have := le_max_left hX.hi hX'.hi; have := max_lt hw1 hw2; linarith
  have htX' : hX'.hi < t := by
    have := le_max_right hX.hi hX'.hi; have := max_lt hw1 hw2; linarith
  have hQSg : Q ∈ Sg := ⟨t, ⟨htX, htw.2⟩, hQ⟩
  exact ⟨S ∪ Sg, hT, fun z hz => hBO (union_subset hSB hSgB hz), Or.inl hPS, Q, Or.inr hQSg, t,
    hQ, fun u hu => (hX'.le_hi hu).trans_lt htX'⟩

/-- `A(X) ⊆ A(X′)` when `X′ ⊆ B(X)`. -/
theorem below_subset_below {X X' : Set Pt} (hX : V.IsPiece X) (hX' : V.IsPiece X')
    (h : X' ⊆ V.above X) : V.below X ⊆ V.below X' := by
  have hmiss : ∀ P ∈ V.below X, P ∉ closure X' := fun P hP hPc =>
    disjoint_left.1 hX.sides_disjoint hP (h (hX'.closure_inter ⟨hPc, (below_subset X hP).1⟩))
  have hAO : V.below X ⊆ V.O \ closure X' := fun P hP => ⟨(below_subset X hP).1, hmiss P hP⟩
  rintro P ⟨S, hS, hSO, hPS, P₀, hP₀S, v, hv, hvu⟩
  have hSA : S ⊆ V.below X := subset_below_of_lev hS hSO hP₀S hv hvu
  set Sg := V.seg (Ioo 0 hX.lo) with hSg
  have hSgA : Sg ⊆ V.below X := by
    rintro Q ⟨t, ht, hQ⟩
    exact mem_below_of_lev hQ fun u hu => ht.2.trans_le (hX.lo_le hu)
  have hP₀Sg : P₀ ∈ Sg := ⟨v, ⟨(V.lev_pos P₀ v hv).1, hvu _ hX.lo_mem⟩, hv⟩
  have hT : IsPreconnected (S ∪ Sg) :=
    hS.union P₀ hP₀S hP₀Sg (V.seg_preconnected _ isPreconnected_Ioo)
  have hw1 := (hX.hts_pos hX.lo_mem)
  have hw2 := (hX'.hts_pos hX'.lo_mem)
  set t := min hX.lo hX'.lo / 2 with ht
  have hmpos : 0 < min hX.lo hX'.lo := lt_min hw1.1 hw2.1
  have htX : t < hX.lo := by have := min_le_left hX.lo hX'.lo; linarith
  have htX' : t < hX'.lo := by have := min_le_right hX.lo hX'.lo; linarith
  have htw : t ∈ Ioo 0 V.w := ⟨by linarith, by linarith [hw1.2]⟩
  obtain ⟨Q, hQ⟩ := V.lev_exists t htw
  have hQSg : Q ∈ Sg := ⟨t, ⟨htw.1, htX⟩, hQ⟩
  exact ⟨S ∪ Sg, hT, fun z hz => hAO (union_subset hSA hSgA hz), Or.inl hPS, Q, Or.inr hQSg, t,
    hQ, fun u hu => htX'.trans_le (hX'.lo_le hu)⟩

/-- The clopen argument: a set open in `R²`, contained in `O`, with frontier in `O` empty, nonempty
and missing a nonempty subset of `O`, contradicts the connectedness of `O`. -/
theorem clopen_contra {B T : Set Pt} (hBo : IsOpen B) (hBO : B ⊆ V.O)
    (hfr : V.O ∩ closure B ⊆ B) (hBne : B.Nonempty) (hTO : T ⊆ V.O) (hTne : T.Nonempty)
    (hBT : Disjoint B T) : False := by
  obtain ⟨P, hP⟩ := hBne
  obtain ⟨Q, hQ⟩ := hTne
  obtain ⟨R, -, hR1, hR2⟩ := V.isPreconnected_O B (closure B)ᶜ hBo isClosed_closure.isOpen_compl
    (fun z hz => by
      by_cases h : z ∈ closure B
      · exact Or.inl (hfr ⟨hz, h⟩)
      · exact Or.inr h)
    ⟨P, hBO hP, hP⟩
    ⟨Q, hTO hQ, fun h => disjoint_left.1 hBT (hfr ⟨hTO hQ, h⟩) hQ⟩
  exact hR2 (subset_closure hR1)

/-- **Not both `X′ ⊆ A(X)` and `X ⊆ A(X′)`.** -/
theorem not_below_below {X X' : Set Pt} (hX : V.IsPiece X) (hX' : V.IsPiece X')
    (hXX' : Disjoint X X') (h1 : X' ⊆ V.below X) (h2 : X ⊆ V.below X') : False := by
  have hB1 := above_subset_above hX hX' h1
  have hB2 := above_subset_above hX' hX h2
  have hB : V.above X = V.above X' := hB1.antisymm hB2
  -- nonempty: a point of `σ` above both
  have hw1 := (hX.hts_pos hX.hi_mem).2
  have hw2 := (hX'.hts_pos hX'.hi_mem).2
  set t := (max hX.hi hX'.hi + V.w) / 2 with ht
  have htX : hX.hi < t := by have := le_max_left hX.hi hX'.hi; have := max_lt hw1 hw2; linarith
  have htw : t ∈ Ioo 0 V.w := ⟨by
    have := (hX.hts_pos hX.hi_mem).1
    linarith, by have := max_lt hw1 hw2; linarith⟩
  obtain ⟨Q, hQ⟩ := V.lev_exists t htw
  have hQB : Q ∈ V.above X := mem_above_of_lev hQ fun u hu => (hX.le_hi hu).trans_lt htX
  refine clopen_contra isOpen_above (fun z hz => (above_subset X hz).1) ?_ ⟨Q, hQB⟩
    hX.subset_O hX.nonempty (disjoint_left.2 fun z hzB hzX => (above_subset X hzB).2
      (subset_closure hzX))
  rintro P ⟨hPO, hPc⟩
  by_cases hPX : P ∈ closure X
  · by_cases hPX' : P ∈ closure X'
    · exact (disjoint_left.1 hXX' (hX.closure_inter ⟨hPX, hPO⟩)
        (hX'.closure_inter ⟨hPX', hPO⟩)).elim
    · rw [hB] at hPc ⊢
      exact mem_above_of_mem_closure ⟨hPO, hPX'⟩ hPc
  · exact mem_above_of_mem_closure ⟨hPO, hPX⟩ hPc

/-- **Not both `X′ ⊆ B(X)` and `X ⊆ B(X′)`.** -/
theorem not_above_above {X X' : Set Pt} (hX : V.IsPiece X) (hX' : V.IsPiece X')
    (hXX' : Disjoint X X') (h1 : X' ⊆ V.above X) (h2 : X ⊆ V.above X') : False := by
  have hA1 := below_subset_below hX hX' h1
  have hA2 := below_subset_below hX' hX h2
  have hA : V.below X = V.below X' := hA1.antisymm hA2
  have hw1 := hX.hts_pos hX.lo_mem
  have hw2 := hX'.hts_pos hX'.lo_mem
  set t := hX.lo / 2 with ht
  have htX : t < hX.lo := by linarith [hw1.1]
  have htw : t ∈ Ioo 0 V.w := ⟨by linarith [hw1.1], by linarith [hw1.2]⟩
  obtain ⟨Q, hQ⟩ := V.lev_exists t htw
  have hQA : Q ∈ V.below X := mem_below_of_lev hQ fun u hu => htX.trans_le (hX.lo_le hu)
  refine clopen_contra isOpen_below (fun z hz => (below_subset X hz).1) ?_ ⟨Q, hQA⟩
    hX.subset_O hX.nonempty (disjoint_left.2 fun z hzA hzX => (below_subset X hzA).2
      (subset_closure hzX))
  rintro P ⟨hPO, hPc⟩
  by_cases hPX : P ∈ closure X
  · by_cases hPX' : P ∈ closure X'
    · exact (disjoint_left.1 hXX' (hX.closure_inter ⟨hPX, hPO⟩)
        (hX'.closure_inter ⟨hPX', hPO⟩)).elim
    · rw [hA] at hPc ⊢
      exact mem_below_of_mem_closure ⟨hPO, hPX'⟩ hPc
  · exact mem_below_of_mem_closure ⟨hPO, hPX⟩ hPc

/-- **S4c (antisymmetry, symmetric form)**: for disjoint pieces, `X′ ⊆ A(X) ↔ X ⊆ B(X′)`. -/
theorem below_iff_above {X X' : Set Pt} (hX : V.IsPiece X) (hX' : V.IsPiece X')
    (hXX' : Disjoint X X') : X' ⊆ V.below X ↔ X ⊆ V.above X' := by
  constructor
  · intro h
    rcases piece_sides hX' hX hXX'.symm with h' | h'
    · exact (not_below_below hX hX' hXX' h h').elim
    · exact h'
  · intro h
    rcases piece_sides hX hX' hXX' with h' | h'
    · exact h'
    · exact (not_above_above hX' hX hXX'.symm h h').elim

/-! ### S4d, S4e -/

/-- **S4d (transitivity)**: `X″ ≺ X′ ≺ X → X″ ≺ X` (`X″` need only be a set). -/
theorem below_trans {X X' X'' : Set Pt} (hX : V.IsPiece X) (hX' : V.IsPiece X')
    (hXX' : Disjoint X X') (h1 : X'' ⊆ V.below X') (h2 : X' ⊆ V.below X) :
    X'' ⊆ V.below X :=
  h1.trans (below_subset_below hX' hX ((below_iff_above hX hX' hXX').1 h2))

/-- **S4e (no pocket)**: a piece disjoint from the piece `X` lies in `A(X) ∪ B(X)`. -/
theorem no_pocket {X S : Set Pt} (hX : V.IsPiece X) (hS : V.IsPiece S) (hXS : Disjoint X S) :
    S ⊆ V.below X ∪ V.above X := by
  rcases piece_sides hX hS hXS with h | h
  · exact h.trans subset_union_left
  · exact h.trans subset_union_right

/-! ### §2. Separation along the vertical -/

/-- **Converse of SSL**: a piece `W` with `Y ≺ W ≺ X` separates `x ∈ X` from `y ∈ Y` in `O`. -/
theorem sepIn_of_between {W X Y : Set Pt} {x y : Pt} (hW : V.IsPiece W) (hY : Y ⊆ V.below W)
    (hX : X ⊆ V.above W) (hx : x ∈ X) (hy : y ∈ Y) : SepIn V.O (closure W) x y := by
  refine ⟨above_subset W (hX hx), below_subset W (hY hy), fun S hS hSO hxS hyS => ?_⟩
  exact disjoint_left.1 hW.sides_disjoint (hY hy) (subset_above hS hSO hxS (hX hx) hyS)

/-- **SSL, step 4**: if `Y ≺ X` and `Z` separates `x ∈ X` from `y ∈ Y` in `O` (with `X`, `Y`
missing `Z`), some `z ∈ Z ∩ σ` lies in `A(X) ∩ B(Y)` (on the open segment of `σ` between the top
point of `Y` below `m(X)` and the bottom point `m(X)` of `X`). -/
theorem exists_sep_point {X Y Z : Set Pt} {x y : Pt} (hX : V.IsPiece X) (hY : V.IsPiece Y)
    (hXY : Disjoint X Y) (hYX : Y ⊆ V.below X) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hx : x ∈ X) (hy : y ∈ Y) (hsep : SepIn V.O Z x y) :
    ∃ z ∈ Z, (∃ v, V.lev z v) ∧ z ∈ V.below X ∧ z ∈ V.above Y := by
  have hXB : X ⊆ V.above Y := (below_iff_above hX hY hXY).1 hYX
  set p' := hX.lo with hp'
  obtain ⟨P', hP'X, hP'⟩ := hX.exists_lo
  -- `m(Y) < m(X)`
  have hmY : hY.lo < p' := by
    rcases lt_trichotomy hY.lo p' with h | h | h
    · exact h
    · exact (hX.hts_disjoint hY hXY hX.lo_mem (by rw [← hp', ← h]; exact hY.lo_mem)).elim
    · exfalso
      have : P' ∈ V.below Y := mem_below_of_lev hP' fun u hu => h.trans_le (hY.lo_le hu)
      exact disjoint_left.1 hY.sides_disjoint this (hXB hP'X)
  -- `p` := the greatest height of `Y` below `m(X)`
  set K := V.hts Y ∩ Iic p' with hK
  have hKc : IsCompact K := hY.hts_compact.inter_right isClosed_Iic
  have hKne : K.Nonempty := ⟨hY.lo, hY.lo_mem, hmY.le⟩
  set p := sSup K with hp
  have hpK : p ∈ K := hKc.sSup_mem hKne
  have hpp' : p < p' := lt_of_le_of_ne hpK.2 fun h =>
    hX.hts_disjoint hY hXY hX.lo_mem (by rw [← hp', ← h]; exact hpK.1)
  obtain ⟨P, hPcl, hP⟩ := hpK.1
  have hPY : P ∈ Y := hY.mem_of_lev hP hpK.1
  -- heights strictly between `p` and `p'` are heights of neither
  have hgapX : ∀ t, t < p' → t ∉ V.hts X := fun t ht h => (hX.lo_le h).not_gt ht
  have hgapY : ∀ t ∈ Ioo p p', t ∉ V.hts Y := fun t ht h =>
    (le_csSup hKc.bddAbove ⟨h, ht.2.le⟩).not_gt ht.1
  by_contra hno
  push_neg at hno
  -- the segment `[p, p′]` of `σ` misses `Z`, unless a point of it does the job
  have hsegO : V.seg (Icc p p') ⊆ V.O \ Z := by
    rintro Q ⟨t, ht, hQ⟩
    refine ⟨V.lev_mem Q t hQ, fun hQZ => ?_⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h; rw [V.lev_inj Q P _ hQ hP] at hQZ; exact disjoint_left.1 hYZ hPY hQZ
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · subst h'; rw [V.lev_inj Q P' _ hQ hP'] at hQZ; exact disjoint_left.1 hXZ hP'X hQZ
    -- an interior point: it is below `X` and above `Y`
    have hQA : Q ∈ V.below X := mem_below_of_lev hQ fun u hu => h'.trans_le (hX.lo_le hu)
    have hS : IsPreconnected (V.seg (Icc t p') ∪ X) :=
      (V.seg_preconnected _ isPreconnected_Icc).union P' ⟨p', ⟨h'.le, le_rfl⟩, hP'⟩ hP'X
        hX.preconnected
    have hSO : V.seg (Icc t p') ∪ X ⊆ V.O \ closure Y := by
      rintro R (⟨s, hs, hR⟩ | hR)
      · refine ⟨V.lev_mem R s hR, notMem_closure_of_lev hR fun hsY => ?_⟩
        rcases eq_or_lt_of_le hs.2 with h'' | h''
        · exact hX.hts_disjoint hY hXY (h''.symm ▸ hX.lo_mem) hsY
        · exact hgapY s ⟨h.trans_le hs.1, h''⟩ hsY
      · exact hY.subset_diff_closure hX.subset_O hXY.symm hR
    have hQB : Q ∈ V.above Y :=
      subset_above hS hSO (Or.inr hP'X) (hXB hP'X) (Or.inl ⟨t, ⟨le_rfl, h'.le⟩, hQ⟩)
    exact hno Q hQZ ⟨t, hQ⟩ hQA hQB
  -- then `X ∪ [P, P′] ∪ Y` joins `x` to `y` off `Z`
  have hT : IsPreconnected (X ∪ V.seg (Icc p p') ∪ Y) :=
    (hX.preconnected.union P' hP'X
      (show P' ∈ V.seg (Icc p p') from ⟨p', ⟨hpp'.le, le_rfl⟩, hP'⟩)
      (V.seg_preconnected _ isPreconnected_Icc)).union P
      (show P ∈ X ∪ V.seg (Icc p p') from Or.inr ⟨p, ⟨le_rfl, hpp'.le⟩, hP⟩)
      hPY hY.preconnected
  refine hsep.2.2 _ hT ?_ (Or.inl (Or.inl hx)) (Or.inr hy)
  rintro R ((hR | hR) | hR)
  · exact ⟨hX.subset_O hR, disjoint_left.1 hXZ hR⟩
  · exact hsegO hR
  · exact ⟨hY.subset_O hR, disjoint_left.1 hYZ hR⟩

/-- **SSL, step 5**: a piece `W ⊆ Z` through a point of `A(X) ∩ B(Y)` lies between: `Y ≺ W ≺ X`,
and `Cl W` separates `x` from `y`. -/
theorem between_of_mem {W X Y Z : Set Pt} {x y z : Pt} (hW : V.IsPiece W) (hX : V.IsPiece X)
    (hY : V.IsPiece Y) (hWZ : W ⊆ Z) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hzW : z ∈ W)
    (hzA : z ∈ V.below X) (hzB : z ∈ V.above Y) (hx : x ∈ X) (hy : y ∈ Y) :
    W ⊆ V.below X ∧ W ⊆ V.above Y ∧ Y ⊆ V.below W ∧ X ⊆ V.above W ∧
      SepIn V.O (closure W) x y := by
  have hWX : Disjoint X W := hXZ.mono_right hWZ
  have hWY : Disjoint Y W := hYZ.mono_right hWZ
  have h1 : W ⊆ V.below X :=
    subset_below hW.preconnected (hX.subset_diff_closure hW.subset_O hWX) hzW hzA
  have h2 : W ⊆ V.above Y :=
    subset_above hW.preconnected (hY.subset_diff_closure hW.subset_O hWY) hzW hzB
  have h3 : X ⊆ V.above W := (below_iff_above hX hW hWX).1 h1
  have h4 : Y ⊆ V.below W := (below_iff_above hW hY hWY.symm).2 h2
  exact ⟨h1, h2, h4, h3, sepIn_of_between hW h4 h3 hx hy⟩

/-- **SSL (strand separation lemma)** (commission 178 §2). Let `x ∈ X`, `y ∈ Y` with `X`, `Y`
pieces missing `Z`, equal or disjoint, and let `Z` separate `x` from `y` in `O`. Then `X ≠ Y`, the
two are ordered (`Y ≺ X` or `X ≺ Y`), and there is `z ∈ Z ∩ σ` between them (in `A(X) ∩ B(Y)`, or
in `A(Y) ∩ B(X)`). If the component `W_z` of `Z ∩ O` through `z` is a piece, it lies between `X`
and `Y` and `Cl W_z` alone separates `x` from `y` in `O`. -/
theorem strand_separation {X Y Z : Set Pt} {x y : Pt} (hX : V.IsPiece X) (hY : V.IsPiece Y)
    (hXY : X = Y ∨ Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hx : x ∈ X)
    (hy : y ∈ Y) (hsep : SepIn V.O Z x y) :
    X ≠ Y ∧ Disjoint X Y ∧ (Y ⊆ V.below X ∨ X ⊆ V.below Y) ∧
      ∃ z ∈ Z, (∃ v, V.lev z v) ∧
        ((z ∈ V.below X ∧ z ∈ V.above Y) ∨ (z ∈ V.below Y ∧ z ∈ V.above X)) ∧
        (V.IsPiece (connectedComponentIn (Z ∩ V.O) z) →
          SepIn V.O (closure (connectedComponentIn (Z ∩ V.O) z)) x y) := by
  have hne : X ≠ Y := by
    rintro rfl
    exact hsep.2.2 X hX.preconnected
      (fun P hP => ⟨hX.subset_O hP, disjoint_left.1 hXZ hP⟩) hx hy
  have hdisj : Disjoint X Y := hXY.resolve_left hne
  have hz : ∀ z, z ∈ Z → z ∈ V.O → connectedComponentIn (Z ∩ V.O) z ⊆ Z ∧
      z ∈ connectedComponentIn (Z ∩ V.O) z := fun z hzZ hzO =>
    ⟨(connectedComponentIn_subset _ _).trans inter_subset_left,
      mem_connectedComponentIn ⟨hzZ, hzO⟩⟩
  rcases piece_sides hX hY hdisj with h | h
  · obtain ⟨z, hzZ, hzσ, hzA, hzB⟩ := exists_sep_point hX hY hdisj h hXZ hYZ hx hy hsep
    refine ⟨hne, hdisj, Or.inl h, z, hzZ, hzσ, Or.inl ⟨hzA, hzB⟩, fun hW => ?_⟩
    obtain ⟨hWZ, hzW⟩ := hz z hzZ (below_subset X hzA).1
    exact (between_of_mem hW hX hY hWZ hXZ hYZ hzW hzA hzB hx hy).2.2.2.2
  · have hXY' : X ⊆ V.below Y := (below_iff_above hY hX hdisj.symm).2 h
    obtain ⟨z, hzZ, hzσ, hzA, hzB⟩ :=
      exists_sep_point hY hX hdisj.symm hXY' hYZ hXZ hy hx (by
        obtain ⟨h1, h2, h3⟩ := hsep
        exact ⟨h2, h1, fun S hS hSO hyS hxS => h3 S hS hSO hxS hyS⟩)
    refine ⟨hne, hdisj, Or.inr hXY', z, hzZ, hzσ, Or.inr ⟨hzA, hzB⟩, fun hW => ?_⟩
    obtain ⟨hWZ, hzW⟩ := hz z hzZ (below_subset Y hzA).1
    have := (between_of_mem hW hY hX hWZ hYZ hXZ hzW hzA hzB hy hx).2.2.2.2
    obtain ⟨h1, h2, h3⟩ := this
    exact ⟨h2, h1, fun S hS hSO hxS hyS => h3 S hS hSO hyS hxS⟩

/-- **`SepByCrossing`, general form** (commission 178 §2, corollary): if every component of
`Z ∩ O` meeting `σ` is a piece, and `x`, `y` lie on pieces `X`, `Y` (equal or disjoint) missing
`Z`, then separation of `x` from `y` in `O` by `Z` is separation by the closure of one component
of `Z ∩ O` that is a piece. -/
theorem sepByCrossing_of_inner_crossing {X Y Z : Set Pt} {x y : Pt}
    (hZ : ∀ z ∈ Z ∩ V.O, (∃ v, V.lev z v) → V.IsPiece (connectedComponentIn (Z ∩ V.O) z))
    (hX : V.IsPiece X) (hY : V.IsPiece Y) (hXY : X = Y ∨ Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) (hx : x ∈ X) (hy : y ∈ Y) (hsep : SepIn V.O Z x y) :
    ∃ z ∈ Z ∩ V.O, (∃ v, V.lev z v) ∧ V.IsPiece (connectedComponentIn (Z ∩ V.O) z) ∧
      SepIn V.O (closure (connectedComponentIn (Z ∩ V.O) z)) x y := by
  obtain ⟨-, -, -, z, hzZ, hzσ, -, hW⟩ := strand_separation hX hY hXY hXZ hYZ hx hy hsep
  have hzO : z ∈ V.O := by obtain ⟨v, hv⟩ := hzσ; exact V.lev_mem z v hv
  have hP := hZ z ⟨hzZ, hzO⟩ hzσ
  exact ⟨z, ⟨hzZ, hzO⟩, hzσ, hP, hW hP⟩

end VFrame

end HPC.Hagopian
