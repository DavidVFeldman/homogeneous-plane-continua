import HPC.Hagopian.Hagopian76D
import HPC.Hagopian.H76Essential
import HPC.Hagopian.H76USC
import HPC.Hagopian.H76Schoen2

/-!
# Batch 160 skeleton: Hagopian 1976, Lemma 6 (steps 1–8) and the unnumbered claims, Lemma 7;
# two-sided Schoenflies, the metric form of upper semicontinuity, Lemma 9

The proofs are in `H76USC`, `H76Schoen2`, `H76Absorb`, `H76Lemma6`, `H76Step8`, `H76Composant`,
`H76Essential` (report `doc/batches/REPORT-batch160.md`). All statement shapes are the skeleton's,
unchanged. Lemma 7 and Lemma 9 remain open and are commented out below with their obstructions.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 341–345.

**Already in the repository** (report 159 §1.A, item 1, overlooked them):
* `hagopian76_lemma4_chain`: extensions away from `X` are linearly ordered by inclusion;
* `hagopian76_lemma4`: no maximal element;
* `hagopian76_lemma4_seq`: the strictly increasing sequence `{Fᵢ}` with `R(X, E) = ⋃ Fᵢ`;
* `hagopian76_initial_segment`: each smaller extension is an initial segment of each larger one,
  with its layers among the larger one's (apply it with `E := F`, since both have end set `X`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Section2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## A. Lemma 6 -/

/-- **Lemma 6, first part** (pp. 342–343, steps 1–7): "First we prove that `Cl R(X, E)` is
indecomposable." Supporting lemmas for the steps are expected (commission §2 A). -/
theorem hagopian76_lemma6_X (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    Fold.Q78.IsIndecomposable (closure (extUnion E (layer k 0))) :=
  lemma6_X_aux hX hi hE

/-- **Lemma 6, the step "`Cl R(X, E) = Cl R(E)`"** (p. 343, step 8). -/
theorem hagopian76_closure_extUnion (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    closure (extUnion E (layer k 0)) = closure (Rset k) :=
  closure_extUnion_aux hX hi hE

/-- **Lemma 6** (p. 341). "The continuum `Cl R(E)` is indecomposable." -/
theorem hagopian76_lemma6 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    Fold.Q78.IsIndecomposable (closure (Rset k)) :=
  lemma6_aux hX hi hE

/-- **"Since `M` is atriodic, `R(E)` is a composant of `Cl R(E)`"** (p. 343). -/
theorem hagopian76_Rset_composant (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {x : M}
    (hx : x ∈ Rset k) : Rset k = HPC.composant (closure (Rset k)) x :=
  Rset_composant_aux hX hi hE hx

/-- **"Note that every continuum essential to `R(E)` is of type A′ (Lemma 5)"** (p. 343). -/
theorem hagopian76_essential_typeA' (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {H : Set M}
    (hH : IsEssential k H) : IsTypeA' H :=
  essential_typeA'_aux hX hi hE hH

/-! ## B. Lemma 7 -/

-- `hagopian76_lemma7`: proved in batch 162, `Hagopian76G.lean`.

/-! ## C. Upper semicontinuity in metric form -/

omit [CompactSpace M] [ConnectedSpace M] in
/-- **Layers near a layer are near it** (report 159 §5): upper semicontinuity of the decomposition
of `E` in metric form. -/
theorem layer_nbhd_small {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {ε : ℝ} (hε : 0 < ε) (s : unitInterval) :
    ∃ δ > 0, ∀ t : unitInterval, dist t s < δ →
      toPt (layer k t) ⊆ Metric.thickening ε (toPt (layer k s)) :=
  layer_nbhd_small_aux hE hε s

end Section2

/-! ## D. Two-sided Schoenflies -/

/-- **Schoenflies with two adjacent sides prescribed** (report 159 §5): bottom side on `φ`, left
side on `ψ`, the two arcs of `J` meeting only at their common first point. -/
theorem plane_schoenflies₂ {J D : Set Pt} (hJ : TSCC J) (hD : IsOpen D) (hDc : IsConnected D)
    (hDb : Bornology.IsBounded D) (hDJ : frontier D = J) {φ ψ : unitInterval → Pt}
    (hφ : IsEmbedding φ) (hψ : IsEmbedding ψ) (hφJ : range φ ⊆ J) (hψJ : range ψ ⊆ J)
    (h0 : φ 0 = ψ 0) (hφψ : range φ ∩ range ψ = {φ 0}) :
    ∃ f : unitInterval × unitInterval → Pt, IsEmbedding f ∧ range f = J ∪ D ∧
      (∀ t, f (t, 0) = φ t) ∧ (∀ t, f (0, t) = ψ t) ∧
      f '' {p | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1} = D :=
  plane_schoenflies₂_aux hJ hD hDc hDb hDJ hφ hψ hφJ hψJ h0 hφψ

/-! ## E. Lemma 9 (restated from `Hagopian76D.lean`) -/

section Lemma9

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

-- `hagopian76_lemma9` (Lemma 9, collar form): proved in batch 163, `Hagopian76H.lean`.

end Lemma9

end HPC.Hagopian
