import HPC.HO16.HO16D

/-!
# Batch 197, definitions: ladders (commission 197 §2)

The definitions of the batch-197 skeleton `HO16E.lean` (commission 197), split under `HPC/HO16/`,
textually the skeleton's.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

noncomputable section Ladder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## §2. Ladders -/

/-- `y_i(v)`: the `i`-th entry (counting from 1) of the list of heights at `v`. -/
def ladderY (y : E → List ℝ) (v : E) (i : ℕ) : ℝ := (y v).getD (i - 1) 0

/-- **Ladder data** on `G` (commission 197 §2): an oriented decomposition `S` of `G`; at each
vertex `v` a list `y v` of heights in `(0, 1)` of odd length; on each edge `s` either no event
(`ev s = none`; the lists at `s.1` and `s.2` have the same length) or a wedge at `s.2`
(`ev s = some (m, λ, h)`; the list at `s.2` is two longer, the wedge takes places `m`, `m + 1`
there, its tip lies over the point of parameter `λ ∈ (0, 1)` of `s`, at height `h ∈ (0, 1)`). -/
def IsLadder (G : Set E) (S : Finset (E × E)) (y : E → List ℝ)
    (ev : E × E → Option (ℕ × ℝ × ℝ)) : Prop :=
  (∀ s ∈ S, s.1 ≠ s.2) ∧ G = (⋃ s ∈ S, segment ℝ s.1 s.2) ∧ PairwiseEndpoints S ∧
  (∀ s ∈ S, Odd (y s.1).length ∧ Odd (y s.2).length ∧
    (∀ t ∈ y s.1, t ∈ Ioo (0 : ℝ) 1) ∧ ∀ t ∈ y s.2, t ∈ Ioo (0 : ℝ) 1) ∧
  (∀ s ∈ S, ev s = none → (y s.1).length = (y s.2).length) ∧
  (∀ s ∈ S, ∀ (m : ℕ) (lam h : ℝ), ev s = some (m, lam, h) →
    (y s.2).length = (y s.1).length + 2 ∧ 1 ≤ m ∧ m ≤ (y s.1).length + 1 ∧
    lam ∈ Ioo (0 : ℝ) 1 ∧ h ∈ Ioo (0 : ℝ) 1)

/-- Left end `l_i` of the zig-zag interval of the curve of rank `i` (`m ≤ i ≤ j`) on a wedge edge
with `j` curves at `s.1`, wedge at place `m`, tip at parameter `λ`:
`l_i = λ (2(j − i) + 1) / (2(j − m) + 3)`. -/
def zzL (j m : ℕ) (lam : ℝ) (i : ℕ) : ℝ :=
  lam * (2 * ((j - i : ℕ) : ℝ) + 1) / (2 * ((j - m : ℕ) : ℝ) + 3)

/-- Right end `r_i = λ (2(j − i) + 2) / (2(j − m) + 3)` of the zig-zag interval. -/
def zzR (j m : ℕ) (lam : ℝ) (i : ℕ) : ℝ :=
  lam * (2 * ((j - i : ℕ) : ℝ) + 2) / (2 * ((j - m : ℕ) : ℝ) + 3)

/-- On a wedge edge, the line of the curve of rank `i ≥ m` at `s.1`: from `(s.1, y_i(s.1))` to
`(s.2, y_{i+2}(s.2))`, at parameter `μ`. -/
def zzLine (y : E → List ℝ) (s : E × E) (i : ℕ) (μ : ℝ) : E × ℝ :=
  AffineMap.lineMap (s.1, ladderY y s.1 i) (s.2, ladderY y s.2 (i + 2)) μ

/-- The part of the `i`-th sheet over the edge `s` (commission 197 §2): with no event, the
segment from `(s.1, y_i(s.1))` to `(s.2, y_i(s.2))`; on a wedge edge, the segment of rank `i` below
the wedge, and from the wedge up the zig-zag pieces `C¹ᵢ`, `C²ᵢ₋₁`, `C³ᵢ₋₂` and the wedge halves. -/
def ladderPiece (y : E → List ℝ) (s : E × E) (e : Option (ℕ × ℝ × ℝ)) (i : ℕ) :
    Set (E × ℝ) :=
  match e with
  | none =>
      if 1 ≤ i ∧ i ≤ (y s.1).length then
        segment ℝ (s.1, ladderY y s.1 i) (s.2, ladderY y s.2 i) else ∅
  | some (m, lam, h) =>
      (if 1 ≤ i ∧ i < m ∧ i ≤ (y s.1).length then
        segment ℝ (s.1, ladderY y s.1 i) (s.2, ladderY y s.2 i) else ∅) ∪
      (if m ≤ i ∧ i ≤ (y s.1).length then
        segment ℝ (zzLine y s i 0) (zzLine y s i (zzR (y s.1).length m lam i)) else ∅) ∪
      (if m + 1 ≤ i ∧ i ≤ (y s.1).length + 1 then
        segment ℝ (zzLine y s (i - 1) (zzL (y s.1).length m lam (i - 1)))
          (zzLine y s (i - 1) (zzR (y s.1).length m lam (i - 1))) else ∅) ∪
      (if m + 2 ≤ i ∧ i ≤ (y s.1).length + 2 then
        segment ℝ (zzLine y s (i - 2) (zzL (y s.1).length m lam (i - 2)))
          (zzLine y s (i - 2) 1) else ∅) ∪
      (if i = m ∨ i = m + 1 then
        segment ℝ (AffineMap.lineMap s.1 s.2 lam, h) (s.2, ladderY y s.2 i) else ∅)

/-- The `i`-th sheet of a ladder. -/
def ladderSheet (S : Finset (E × E)) (y : E → List ℝ) (ev : E × E → Option (ℕ × ℝ × ℝ))
    (i : ℕ) : Set (E × ℝ) :=
  ⋃ s ∈ S, ladderPiece y s (ev s) i

/-- The height of a ladder: the longest list. -/
def ladderHeight (S : Finset (E × E)) (y : E → List ℝ) : ℕ :=
  S.sup fun s => max (y s.1).length (y s.2).length

end Ladder

end HPC.HO16
