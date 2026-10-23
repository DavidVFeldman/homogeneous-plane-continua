import HPC.Jones.Jones49C

/-!
# Batch 152 skeleton: Whyburn 1939, §14 Theorem (boundaries of complementary domains of a compact
semi-locally-connected plane continuum are locally connected)

Save as `HPC/Jones/Jones49D.lean` (splitting under `HPC/Jones/` is expected); add
`import HPC.Jones.Jones49D` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be
adjusted, each change recorded at the statement and in the report.

Source: Whyburn, *Semi-locally-connected sets*, Amer. J. Math. 61 (1939), pp. 747–749
(`doc/sources/whyburn1939.pdf`, PDF pp. 16–18), read from page images at 150 dpi. The proof:
1. (p. 747) reduction to bounded `R` by inversion (gap: `A.21` of the ledger; not used);
2. if `R` lacks property S, points `pᵢ → p ∈ M` of `R`, no two joinable in `R` by a connected set of
   diameter `< 4ε` — this is the negation of the hypothesis of `moore22_sufficiency_local`;
3. **`p` not a cut point of `M`** (pp. 747–748): (6.22) gives `δ` and the component `N`; a subarc
   `xy` of an arc `p₁p₂` in `R`, ends on `C_δ`, interior outside `C_δ`, `x`, `y` not joinable by a
   continuum of `R` in `V_{2ε}(p)`; `u`, `v` separating `x`, `y` on `C_δ`; `J = xy + xuy`; `I` the
   complementary region of `J` not containing `N`; `0 ∈ I·V_ε(p)` joined to `u`; "by a theorem of
   R. L. Moore, there exists a simple closed curve `C ⊂ J + C_ε` such that if `E` is the
   complementary region of `C` containing `0`, then `E ⊂ I·V_ε(p)`"; the arc `x₁wy₁` of `C` gives a
   continuum of `R` in `V_{2ε}(p)` joining `x` and `y`, a contradiction;
4. **general `p`** (p. 748): arcs `pᵢq` in `R` to a point `q` outside `V_ε(p)`, first points `qᵢ` on
   `C_ε`, a limit continuum `H ⊂ M`, every point of `H` within `V_ε(p)` a cut point of `M` (by 3);
   "then there exists a point `p′` of `H·V_ε(p)` which is of order 2 in `M`" (footnote 6; now
   `whyburn_3_2`); "Hence there exists a simple closed curve `K` in `V_ε(p)` such that `K·M = c + d`,
   `c, d ∈ M`, and the complementary region `D` of `K` containing `p′` lies in `V_ε(p)`"; pigeonhole
   on the two components of `K − (c + d)`.
-/

namespace HPC.Jones

open Set Topology Metric Filter HPC.Plane

/-- **"A theorem of R. L. Moore"** (p. 748, footnote 14; in substance F.A. Theorem 43, corrected),
in `ℝ²`, in the form the proof uses. *The shape is left to you* (REPORT-batch151 §8: build it
directly, as the component of `I·V_ε(p)` containing `0`). -/
theorem whyburn39_moore_curve : True := by
  sorry

/-- **The curve `K` from order 2** (p. 748, unargued). *The shape is left to you.* Whyburn's
pigeonhole needs only: an open `D ∋ p′` inside `V_ε(p)` whose frontier meets `M` in finitely many
points and minus `M` has finitely many components. State and prove whatever form the proof needs,
and record whether Whyburn's Jordan-curve form holds as stated (it requires `c`, `d` accessible from
`Mᶜ` on both sides). -/
theorem whyburn39_curve_from_order_two : True := by
  sorry

/-- **Step 3** (`p` not a cut point, pp. 747–748): Whyburn's local condition holds at a boundary
point `p` of a complementary domain `R` that is not a cut point of `M` — no sequence of points of `R`
converging to `p` is pairwise non-joinable in `R` by connected sets of diameter `< ε`. -/
theorem whyburn39_local_noncut {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    (hS : ∀ z : M, SemiLocConnAt z) {x : Pt} (hx : x ∉ M) {p : M}
    (hp : (p : Pt) ∈ frontier (connectedComponentIn Mᶜ x))
    (hpc : IsConnected ({p}ᶜ : Set M)) {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ u : ℕ → Pt, (∀ n, u n ∈ connectedComponentIn Mᶜ x) ∧ Tendsto u atTop (𝓝 (p : Pt)) ∧
      ∀ i j, i ≠ j → ¬ ∃ C ⊆ connectedComponentIn Mᶜ x, IsPreconnected C ∧ u i ∈ C ∧ u j ∈ C ∧
        Bornology.IsBounded C ∧ diam C < ε := by
  sorry

/-- **Theorem 14** (p. 747). If `M` is a compact semi-locally-connected plane continuum, the boundary
of each complementary domain of `M`, bounded or not, is locally connected. -/
theorem whyburn39_theorem14 {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    (hS : ∀ z : M, SemiLocConnAt z) {x : Pt} (hx : x ∉ M) :
    LocallyConnectedSpace (frontier (connectedComponentIn Mᶜ x)) := by
  sorry

end HPC.Jones
