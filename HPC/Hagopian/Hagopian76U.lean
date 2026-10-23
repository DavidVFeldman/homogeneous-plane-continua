import HPC.Hagopian.H76Eps3
import HPC.Hagopian.H76Prop4

/-!
# Batch 176: Hagopian 1976, Theorem 1 — positions by `ε₃`; the cutting step; Property 4;
# the induction; the assembly

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Routes: commission 176 §1.
Skeleton as delivered: `doc/batches/skeletons/Hagopian76U.lean`.

Supporting files:
* `H76Eps3` — uniform continuity of `π` and of the inverse collar; `Property2At` and its
  monotonicity in `ε₃`;
* `H76Cut` — `SepIn.mono`; Janiszewski's theorem inside a domain (`sepIn_union_cases`); closures of
  crossing components lie in the layers of their intervals; the named `Prop` `SepByCrossing`; the
  cutting step and the separation above a gap of `St J` from it;
* `H76Prop4` — the structure `T12Data`, the `Prop` `Property4`, Property 4 for the top block, the
  base case and the closing contradiction.

Every skeleton item was stated as `True` (shape left to me); the shapes are recorded at each
statement and in `doc/batches/REPORT-batch176.md`. Items left open are commented out at the end,
with the obstructions in `OPEN.md`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **A. Positions by `ε₃`** (commission 176 §1.A; p. 348: "Note that `f(yᵢ₋₁)` belongs to
`L₆ ∩ π⁻¹[D]`"). For every `ε₂ > 0` there is `ε₃ ∈ (0, ε₂)` such that
* Property 2 holds at `ε₃` (and at every smaller positive value, `Property2At.mono`), and
* every point `w` of `M` within `ε₃` of a point `y` of `M` over the abscissa `1/2` (Hagopian's `K`
  lies over `p₃`, abscissa `11/22`), with `w` over a point of the closed collar rectangle, lies over
  an abscissa in `(3/8, 5/8)`. This applies to `w = f(y)`, `f⁻¹(y)`, `h(x)`, `h₁(x)` for
  `ε₃`-homeomorphisms.

*Shape (left to me):* the position is stated for any `w` within `ε₃` (not only `f(yᵢ₋₁)`), with
`y` exactly over `1/2`; the middle is open, `(3/8, 5/8) ⊆ [3/8, 5/8]`. -/
theorem eps3_positions_middle (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπc : Continuous π)
    {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {ε₂ : ℝ} (hε₂ : 0 < ε₂) :
    ∃ ε₃ > 0, ε₃ < ε₂ ∧ Property2At k ε₂ ε₃ ∧
      ∀ (y w : M) (z z' : ℝ × ℝ), z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 →
        z' ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 → z.1 = 1 / 2 → π (y : Pt) = F z →
        π (w : Pt) = F z' → dist (y : Pt) w < ε₃ → z'.1 ∈ Ioo (3 / 8 : ℝ) (5 / 8) := by
  obtain ⟨ε₀, hε₀, hε₀2, hP2⟩ := hagopian76_property2 hX hi hE hε₂
  obtain ⟨δ, hδ, hclose⟩ := pi_abscissa_close (M := M) hπc
    (isCompact_Icc.prod isCompact_Icc) hF.1 (μ := 1 / 8) (by norm_num)
  refine ⟨min ε₀ δ, lt_min hε₀ hδ, (min_le_left _ _).trans_lt hε₀2,
    Property2At.mono (fun h hh H hH d hd hT hU => hP2 h hh H hH d hd hT hU) (min_le_left _ _),
    fun y w z z' hz hz' hz1 hy hw hd => ?_⟩
  have := hclose y w z hz z' hz' hy hw (hd.trans_le (min_le_right _ _))
  rw [hz1, abs_lt] at this
  constructor <;> linarith [this.1, this.2]

omit [CompactSpace M] [ConnectedSpace M] in
/-- **A′. Positions of images under an `ε₃`-homeomorphism**, the form used at p. 348. With `ε₃` of
`eps3_positions_middle`: if `y` is over the abscissa `1/2` and `f` is an `ε₃`-homeomorphism with
`f(y)` over `D`, then `f(y)` is over an abscissa in `(3/8, 5/8)`. -/
theorem eps3_image_middle {π : Pt → Pt} {F : ℝ × ℝ → Pt} {ε₃ : ℝ}
    (hpos : ∀ (y w : M) (z z' : ℝ × ℝ), z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 →
        z' ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 → z.1 = 1 / 2 → π (y : Pt) = F z →
        π (w : Pt) = F z' → dist (y : Pt) w < ε₃ → z'.1 ∈ Ioo (3 / 8 : ℝ) (5 / 8))
    {c₁ : ℝ} (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') (f : M ≃ₜ M)
    (hf : ∀ v, dist (f v) v < ε₃) (y : M) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1)
    (hy : π (y : Pt) = F (1 / 2, u)) (z' : ℝ × ℝ) (hz' : z' ∈ D') (hfy : π (f y : Pt) = F z') :
    z'.1 ∈ Ioo (3 / 8 : ℝ) (5 / 8) := by
  have hz'R : z' ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hR.sub hz'
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hd : dist (y : Pt) (f y : Pt) < ε₃ := by
    rw [dist_comm]; exact hf y
  exact hpos y (f y) (1 / 2, u) z' ⟨⟨by norm_num, by norm_num⟩, hu⟩ hz'R rfl hy hfy hd

omit [CompactSpace M] [ConnectedSpace M] in
/-- **B. `sep_by_crossing` gives the cutting step** (commission 176 §1.B: "With `sep_by_crossing`,
`TailCutKeepsSep` follows: the tail beyond the last block holds no crossing component").

*Shape (left to me):* `sep_by_crossing` itself is the named `Prop` `SepByCrossing` (open), stated
for `X = G` and the given pair `p`, `q`, with closures of crossing components. What is proved is
the implication, and Janiszewski's theorem inside a domain (`sepIn_union_cases`), the tool of
route 3. -/
theorem sep_by_crossing_cut {E G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d)
    {π : Pt → Pt} {F : ℝ × ℝ → Pt} {c₁ : ℝ} {D' : Set (ℝ × ℝ)} {O : Set Pt} {p q : Pt}
    (hSBC : SepByCrossing G π F c₁ D' O p q) : TailCutKeepsSep E d π F c₁ D' O p q :=
  tailCutKeepsSep_of_sepByCrossing hG hSBC

/-- **B′. `x₂ₙ = 1` from `SepByCrossing`** (p. 348: "Note that … `x₂ₙ = 1`"). Hypotheses of
`hagopian76_x2n_eq_one_of_cut`, with `SepByCrossing` for `p`, `q` in place of `TailCutKeepsSep`.

*Shape (left to me):* conditional on the named `Prop` `SepByCrossing`. -/
theorem hagopian76_x2n_eq_one (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) (hne : G ≠ E) {O : Set Pt} {p q : Pt}
    (hsep : SepIn O (toPt G) p q)
    (hirr : ∀ F', IsExtensionAway E (layer k 0) F' → SepIn O (toPt F') p q → F' ⊆ G → F' = G) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      SepByCrossing G π F c₁ D' O p q → LastIntervalReachesOne d π F c₁ D' := by
  obtain ⟨c, hc, hc1, hcut⟩ := hagopian76_x2n_eq_one_of_cut hX hi hE he hend hπ hπS hγπ hF hLch
    hEL hLG hP1 hG hEG hX0 hne hsep hirr
  exact ⟨c, hc, hc1, fun c₁ D' hc₁ hR hSBC =>
    hcut c₁ D' hc₁ hR (tailCutKeepsSep_of_sepByCrossing hG hSBC)⟩

/-- **C. Property 4 for the top block** (p. 348: "The interval `[x₂ₙ₋₁, x₂ₙ]` has the following
property"), on a `T12Data` package, with `yₙ = p`.

*Shape (left to me):*
* the T12/T13 output is the structure `T12Data` (a hypothesis: its existence, in particular T12 (2)
  for the same `h` that T12 (3) uses, is not yet proved);
* clause (2) is conditional on `SepByCrossing` for `p`, `f(p)`;
* `π⁻¹[D]` is surrounded by a compact connected `Y` (for Hagopian's domain, `Y = π⁻¹[Fr D]`; not
  derived here);
* the top block is `[s₂, 1]` above a gap `s₁ < s₂` of `St J` (`s₁ = x₂ₙ₋₂`, `s₂ = x₂ₙ₋₁`;
  `x₂ₙ = 1` is `hagopian76_x2n_eq_one`). -/
theorem hagopian76_property4_top (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} {π : Pt → Pt} {F : ℝ × ℝ → Pt} {D' : Set (ℝ × ℝ)} {ε₃ : ℝ}
    (D : T12Data E k π F D' ε₃) {c₁ : ℝ} {Y : Set Pt} (hY : IsCompact Y) (hYc : IsConnected Y)
    (hYO : Disjoint Y (π ⁻¹' (F '' D'))) (hfr : frontier (π ⁻¹' (F '' D')) ⊆ Y)
    (hSBC : SepByCrossing D.G π F c₁ D' (π ⁻¹' (F '' D')) D.p (D.f D.p))
    {s₁ s₂ : unitInterval} (h0 : 0 < s₁) (h12 : s₁ < s₂) (hEs : E ⊆ layerSet D.d (Icc 0 s₁))
    (hgap : ∀ r ∈ crossingIntervals D.d π F c₁ D', r.2 ≤ s₁ ∨ s₂ ≤ r.1) :
    Property4 D s₂ 1 :=
  property4_top_of_sepByCrossing hX hi D hY hYc hYO hfr hSBC h0 h12 hEs hgap

end Thm1

/-- **Named `Prop`: the induction step of Property 4** (pp. 348–349, Cases 1–2): for `2 ≤ i ≤ n`,
if `[x₂ᵢ₋₁, x₂ᵢ]` has Property 4, so does `[x₂ᵢ₋₃, x₂ᵢ₋₂]`. Open (item D). -/
def Property4Step {M : Set Pt} {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    {F : ℝ × ℝ → Pt} {D' : Set (ℝ × ℝ)} {ε₃ : ℝ} (D : T12Data E k π F D' ε₃)
    (x : ℕ → unitInterval) (n : ℕ) : Prop :=
  ∀ i, 2 ≤ i → i ≤ n → Property4 D (x (2 * i - 1)) (x (2 * i)) →
    Property4 D (x (2 * i - 3)) (x (2 * i - 2))

section Assembly

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **E. T15–T17, conditional** (p. 348: "The resulting contradiction will complete our proof").
On a `T12Data` package `D` with the blocks `x₁ < x₂ < ⋯ < x₂ₙ` of `St J` (`n ≥ 2`; `x₁ = 0`,
`d⁻¹[[0, x₂]] = E`, every member of `I` inside a block, `x₂ₙ = 1`), the named `Prop`s
`SepByCrossing` (for `p`, `f(p)`) and `Property4Step` give `False`.

*Shape (left to me):* the conditional form asked for in §1.E. Exactly what remains:
* `SepByCrossing` (item B);
* `Property4Step` (item D);
* the existence of `D` (T12 (2) for the `h` of T12 (3); T13 gives `G`), of the blocks
  (the finite `I`, `hagopian76_I_finite`), and of `Y` (`π⁻¹[Fr D]`);
* the reduction of `Hagopian76Thm1` to this set-up (T1–T11, proved piecewise, not assembled).
`x₂ₙ = 1` is a hypothesis here; in the full set-up it is `hagopian76_x2n_eq_one`. -/
theorem hagopian76_T15_T17_cond (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {c₁ : ℝ} (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D')
    (hD'c : IsPreconnected D') {ε₃ : ℝ} (D : T12Data E k π F D' ε₃) {Y : Set Pt}
    (hY : IsCompact Y) (hYc : IsConnected Y) (hYO : Disjoint Y (π ⁻¹' (F '' D')))
    (hfr : frontier (π ⁻¹' (F '' D')) ⊆ Y)
    (hSBC : SepByCrossing D.G π F c₁ D' (π ⁻¹' (F '' D')) D.p (D.f D.p))
    (x : ℕ → unitInterval) (n : ℕ) (hn : 2 ≤ n) (hx : StrictMono x) (hx1 : x 1 = 0)
    (hx2 : layerSet D.d (Icc 0 (x 2)) = E)
    (hblocks : ∀ r ∈ crossingIntervals D.d π F c₁ D', ∃ i, 1 ≤ i ∧ i ≤ n ∧
      x (2 * i - 1) ≤ r.1 ∧ r.2 ≤ x (2 * i))
    (hxn : x (2 * n) = 1) (hstep : Property4Step D x n) : False := by
  have hmono := hx.monotone
  have h0 : 0 < x (2 * n - 2) := by
    rw [← hx1]; exact hx (by omega)
  have h12 : x (2 * n - 2) < x (2 * n - 1) := hx (by omega)
  have hEs : E ⊆ layerSet D.d (Icc 0 (x (2 * n - 2))) := by
    exact hx2.symm.subset.trans (layerSet_mono D.d (Icc_subset_Icc le_rfl (hmono (by omega))))
  have hgap : ∀ r ∈ crossingIntervals D.d π F c₁ D',
      r.2 ≤ x (2 * n - 2) ∨ x (2 * n - 1) ≤ r.1 := by
    intro r hr
    obtain ⟨i, hi1, hin, h1, h2⟩ := hblocks r hr
    rcases lt_or_eq_of_le hin with hlt | rfl
    · exact Or.inl (h2.trans (hmono (by omega)))
    · exact Or.inr h1
  have htop := hagopian76_property4_top hX hi D hY hYc hYO hfr hSBC h0 h12 hEs hgap
  refine false_of_property4_chain D x n (by omega) (by obtain ⟨y, hy, hess, hsep⟩ := htop; exact ⟨y, hy, hess, by rw [hxn]; exact hsep⟩) hstep ?_
  rw [hx1]
  exact not_property4_E hπ hπS hγπ hF hc₁ hR hD'c D hx2

end Assembly

/-! ## Open items

The obstructions are in `OPEN.md` (batch 176) and in `doc/batches/REPORT-batch176.md`.

**OPEN (B, `SepByCrossing`).** If `G` separates `p` from `f(p)` in `π⁻¹[D]`, so do the closures of
the crossing components of `G ∩ π⁻¹[D]`. Route 3 is now available in the form needed for
*disjoint* (or `O`-disjoint) compact pieces (`sepIn_union_cases`); `SepByCrossing` is not of that
form: the crossing components and the rest of `G ∩ π⁻¹[D]` are not separated by a layer of `d`
missing `π⁻¹[D]`. Route 1's obstruction is the one the commission names: a component of
`G ∩ π⁻¹[D]` meeting `d⁻¹(1)` and reaching into the middle (P3's exception). Route 2 needs the
pocket classification of the components of `π⁻¹[D] − G`, which is not formalized.

theorem sep_by_crossing … : SepByCrossing G π F c₁ D' (π ⁻¹' (F '' D')) p (f p) := by
  sorry

**OPEN (C, the existence of `T12Data`).** `hagopian76_T12_uncond` gives `h`, `h₁` and the
separation (T12 (3)); `hagopian76_T12_parts12` gives the essential closure (T12 (2)) for a
different `ε₁`-homeomorphism `h′` (T9's), not for `h`. Combining them needs `h⁻¹[Cl C]` essential
to `R(E)` for the `h` of T12 (3).

theorem exists_T12Data … : Nonempty (T12Data E k π F D' ε₃) := by
  sorry

**OPEN (D, `Property4Step`).**
* "Let `Cᵢ₋₁` be the first component …": the extensions of `Cl Cᵢ` away from `X` are translates of
  extensions of `E` (or lie in `h[R(E)]`); transporting Property 3 and `hagopian76_I_finite` by `h`
  needs these extensions to be type A′ continua with decompositions compatible with `D`, and the
  \"first\" component needs the order of crossing components along the extension; neither is
  formalized.
* "`N` does not come within `ε₂` of `π⁻¹(p₄)`": P3 transported by `h` controls `L` over the middle
  (abscissae `[3/8, 5/8]`), but `π⁻¹(p₄)` lies over `15/22 > 5/8`, outside the controlled range.
* "Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`": with item A, `f(yᵢ₋₁)` is over the
  middle; the pocket control there is `cover_pocket_middle`. The separation of `P ∪ Q` is still
  route 2.

theorem hagopian76_property4_step … : Property4Step D x n := by
  sorry

**OPEN (E, the assembly).** `hagopian76_T15_T17_cond` is the conditional form; the unconditional
theorem waits on B, C (existence of `T12Data`), D and the assembly of the set-up.

-- `hagopian76_theorem1_final`: proved in batch 190 as `hagopian76_theorem1`, `Jones75B.lean`.
-/

end HPC.Hagopian
