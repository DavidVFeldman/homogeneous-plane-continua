import HPC.Span.OT82A

/-!
# Batch 192 skeleton: Theorem C II — the strip theorem; `OTThm32`; Theorem C

Save as `HPC/Span/OT82B.lean` (splitting under `HPC/Span/` is expected); add
`import HPC.Span.OT82B` at the end of `HPC.lean`. Every `sorry` is a work item. Items stated as
`True` are *shape left to you*; record each shape in the report. The definitions `plPath` and
`stripPoly` are suggestions: change them freely (and record it) if another form is easier.
Unproved items are commented out with an `OPEN` note, as before.

Source: Oversteegen–Tymchatyn 1982, §2 and Theorems 3.1–3.2
(`doc/sources/oversteegen-tymchatyn1982.pdf`; transcriptions in `doc/notes/ot82.md`). Route:
commission 192, which replaces Lemma 2.3, Lemma 2.4, Remark 2.5 and the zero-set continua of
Theorem 2.7 by a common-zero lemma and chains.
-/

namespace HPC.Span

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Hagopian

/-! ## §3. Parity tools (commission §3) -/

/-- **§3.1**: the parity vanishes off a compact convex set containing the vertices. -/
theorem parity_eq_zero_of_not_mem_convex {n : ℕ} (v : Fin n → Pt) {C : Set Pt}
    (hC : Convex ℝ C) (hCc : IsCompact C) (hv : ∀ i, v i ∈ C) {z : Pt} (hz : z ∉ C) :
    parity v z = 0 := by
  sorry

/-- **§3.2, vertex perturbation**: moving every vertex by at most `ρ` does not change the parity at
a point farther than `ρ` from the polygon. -/
theorem parity_eq_of_perturb {n : ℕ} (v w : Fin n → Pt) {ρ : ℝ} (hvw : ∀ i, dist (v i) (w i) ≤ ρ)
    {z : Pt} (hz : ρ < infDist z (polygonOf v)) : parity v z = parity w z := by
  sorry

/-- **§3.3, the flip across a vertical edge.** If edge `i` is a nondegenerate segment on the line
`x = c`, the point `b` is inside it, and every other edge stays farther than `r` from `b`, then the
parities just left and just right of `b` differ. (`HPC.Plane.parity_flip_vertical`, in `Jct2`, is
the flip across a horizontal edge; hence the name.) -/
theorem parity_flip_vertical_edge {n : ℕ} (v : Fin n → Pt) (i : Fin n) {c : ℝ}
    (hi : (v i).1 = c) (hi' : (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩).1 = c)
    (hne : v i ≠ v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)
    {b : Pt} (hb : b ∈ openSegment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩))
    {r : ℝ} (hr : 0 < r)
    (hfar : ∀ j : Fin n, j ≠ i → ∀ z ∈ polyEdge v j, r < dist z b)
    {ξ : ℝ} (hξ : 0 < ξ) (hξr : ξ < r) :
    parity v (c + ξ, b.2) ≠ parity v (c - ξ, b.2) := by
  sorry

/-! ## §4. A common zero on a rectangle (commission §4) -/

/-- **§4**: two functions on `[0, 1] × [p, q]`, both `≥ 0` on the left side and `≤ 0` on the right
side, the first `≤ 0` on the bottom row and the second `≤ 0` on the top row, have a common zero. -/
theorem common_zero_rect {p q : ℝ} (hpq : p < q) {φ ψ : ℝ × ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc 0 1 ×ˢ Icc p q)) (hψ : ContinuousOn ψ (Icc 0 1 ×ˢ Icc p q))
    (hl : ∀ u ∈ Icc p q, 0 ≤ φ (0, u) ∧ 0 ≤ ψ (0, u))
    (hr : ∀ u ∈ Icc p q, φ (1, u) ≤ 0 ∧ ψ (1, u) ≤ 0)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, φ (t, p) ≤ 0) (ht : ∀ t ∈ Icc (0 : ℝ) 1, ψ (t, q) ≤ 0) :
    ∃ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc p q, φ z = 0 ∧ ψ z = 0 := by
  sorry

/-! ## §5. Strips (commission §5) -/

/-- The piecewise linear path through `a 0, …, a s` at the times `j / s`, frozen outside `[0, 1]`
(a suggestion; `0 < s` is assumed wherever it is used). A sum of clamped ramps, so continuity is
`fun_prop`. -/
noncomputable def plPath {s : ℕ} (a : Fin (s + 1) → Pt) (t : ℝ) : Pt :=
  a 0 + ∑ j : Fin s, (max 0 (min 1 ((s : ℝ) * t - j))) • (a j.succ - a j.castSucc)

/-- The closed polygon `S_t = B₀ ∪ f[0, t] ∪ B_t ∪ g[0, t]` (O–T Lemma 2.2) as a vertex list:
`f(min(t, k/s))` for `k ≤ s`, then `g(min(t, (2s + 1 − k)/s))`. Edge `s` is `B_t`, the closing
edge is `B₀`. (A suggestion.) -/
noncomputable def stripPoly {s : ℕ} (a b : Fin (s + 1) → Pt) (t : ℝ) : Fin (2 * s + 2) → Pt :=
  fun k => if k.val ≤ s then plPath a (min t ((k.val : ℝ) / s))
    else plPath b (min t (((2 * s + 1 - k.val : ℕ) : ℝ) / s))

/-- **§5.1**: basic facts on `plPath` and `stripPoly` (values at `j / s`, continuity,
`‖f t − g t‖ ≤ max ‖a j − b j‖`, `polygonOf (stripPoly a b t) ⊆ B₀ ∪ f[0,1] ∪ B_t ∪ g[0,1]`,
parity of `stripPoly a b 0` is `0`, the odd set `U_t` lies in `x > 0`). *Shape left to you.* -/
theorem strip_basic : True := by
  sorry

/-- **§5.2, O–T Lemma 2.2**: near `(t₀, z₀)` with `z₀ ∉ S_{t₀}`, the point `z` is off `S_t` and the
parity of `S_t` at `z` is that of `S_{t₀}` at `z₀`. *Shape left to you.* -/
theorem parity_strip_eventually : True := by
  sorry

/-- **§5.3**: the sign function `φ_h(t, u) = ±dist(h u, B_t)` is continuous, with the boundary
signs of the commission. *Shape left to you.* -/
theorem strip_sign_continuous : True := by
  sorry

/-- **§5.4, the strip lemma** (O–T Theorem 2.7, in the form used): a continuum `W` in the strip
bounded by `B₀ = [a 0, b 0]` on the line `x = 0`, the paths through the `a j` and the `b j`, and
`B₁ = [a s, b s]`, touching `x = 0` only inside `B₀`, has every surjective-span witness meeting
`{d ≤ ε}`. -/
theorem strip_lemma {s : ℕ} (hs : 0 < s) (a b : Fin (s + 1) → Pt) {ε : ℝ}
    (hab : ∀ j, dist (a j) (b j) ≤ ε) (ha0 : (a 0).1 = 0) (hb0 : (b 0).1 = 0)
    (haR : ∀ j, 0 ≤ (a j).1) (hbR : ∀ j, 0 ≤ (b j).1)
    {W : Set Pt} (hW : Fold.Q78.IsContinuum W) (hWR : ∀ z ∈ W, 0 ≤ z.1)
    (hW0 : ∃ z ∈ W, z.1 = 0) (hWB₀ : ∀ z ∈ W, z.1 = 0 → z ∈ openSegment ℝ (a 0) (b 0))
    (hWf : Disjoint W (plPath a '' Icc 0 1)) (hWg : Disjoint W (plPath b '' Icc 0 1))
    (hWB₁ : Disjoint W (segment ℝ (a (Fin.last s)) (b (Fin.last s)))) :
    ∀ Z ⊆ W ×ˢ W, Fold.Q78.IsContinuum Z → Prod.fst '' Z = W → Prod.snd '' Z = W →
      ∃ p ∈ Z, dist p.1 p.2 ≤ ε := by
  sorry

/-! ## §6. Disjoint crossing continua are ordered (commission §6) -/

/-- **§6** (commission 191 §7): two disjoint continua crossing the closed strip `[a, b] × ℝ` meet
the line `x = a` in sets one of which lies strictly below the other. -/
theorem crossing_traces_separated {a b : ℝ} (hab : a < b) {K K' : Set Pt}
    (hK : Fold.Q78.IsContinuum K) (hK' : Fold.Q78.IsContinuum K')
    (hKS : K ⊆ Icc a b ×ˢ univ) (hK'S : K' ⊆ Icc a b ×ˢ univ)
    (hKa : ∃ z ∈ K, z.1 = a) (hKb : ∃ z ∈ K, z.1 = b)
    (hK'a : ∃ z ∈ K', z.1 = a) (hK'b : ∃ z ∈ K', z.1 = b) (hdisj : Disjoint K K') :
    (∀ z ∈ K, ∀ z' ∈ K', z.1 = a → z'.1 = a → z.2 < z'.2) ∨
      (∀ z ∈ K, ∀ z' ∈ K', z.1 = a → z'.1 = a → z'.2 < z.2) := by
  sorry

/-! ## §7. Theorem 3.2 (strip form) and Theorem C (commission §7) -/

/-- **O–T Theorem 3.2, strip form.** -/
theorem ot82_theorem32 : OTThm32 := by
  sorry

/-- **Theorem C** (Hoehn–Oversteegen 2016, p. 180): every homogeneous indecomposable plane
continuum has span zero. -/
theorem theoremC : TheoremC :=
  theoremC_of_thm32 ot82_theorem32

end HPC.Span
