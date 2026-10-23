import HPC.Hagopian.Hagopian76B
import HPC.Hagopian.H76Lemma5End
import HPC.Hagopian.H76Quot
import HPC.Hagopian.H76Moore28
import HPC.Hagopian.H76Sub

/-!
# Batch 158 skeleton: Hagopian 1976, D1 closed by lower semicontinuity; Lemmas 5–7; Moore 1962
# Theorem 28; the arc parametrization; Lemma 9

Batch 158 (`doc/batches/COMMISSION-batch158.md`; report `doc/batches/REPORT-batch158.md`). The
skeleton is kept as `doc/batches/skeletons/Hagopian76C.lean`. Supporting proofs are in
`H76Far.lean` (item A), `H76Lemma5End.lean` (items A, B), `H76Moore28.lean` (item E) and
`H76Quot.lean` (item F, first part). Items that remain open are commented out (no `sorry`), each
with an `OPEN (batch 158)` note; their obstructions are in `OPEN.md`. Shape changes are recorded at
the statement and in the report.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 341–345; Bing 1960 p. 215
(`doc/sources/bing1960.pdf`); Moore 1962 Theorem 28, p. 156 (`doc/sources/moore1962-excerpts.pdf`).

**The route to D1** (commission §1, checked step by step in the report). For an extension `F` of
`E` away from `X` with `s = max d|E`, `0 < s < 1`, `W = d⁻¹(s)` is a layer of `F` that is not an end
set, so the decomposition of `F` is lower semicontinuous at `W` (`hagopian76_lemma5_interior`
applied to `F`). The layers of `F` below `s` are layers of `E` (`hagopian76_lemma4_layers'`), and
every point of `W` is a limit of points of these layers whose parameters in `E` tend to `k y`, for
one `y ∈ W` that is a limit of `d⁻¹([0, s))` (continuity of `k`). So `W` lies in one layer of `E`;
since `k⁻¹(1) ⊆ W`, that layer is `k⁻¹(1)`, and `W = k⁻¹(1)`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Section2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## A. D1, in the strong form -/

/-- **The far layer is the far end set.** For an extension `F` of `E` away from `X`, with
`s = max d|E`: either `F = E`, or `0 < s < 1` and `d⁻¹(s) = k⁻¹(1)`. Proof: the commission's route
(file header; `far_layer_aux`, `H76Far.lean`). -/
theorem hagopian76_far_layer (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E F : Set M} {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F) (hX0 : layer d 0 = layer k 0) :
    F = E ∨ ∃ s : unitInterval, 0 < s ∧ s < 1 ∧ layer d s = layer k 1 := by
  obtain ⟨s, hs0, -, -, -, -, -, -, h1, h2⟩ := far_layer_aux hX hi hE hF hEF hX0
  by_cases hs : s = 1
  · exact Or.inl (h1 hs)
  · have hs1 : s < 1 := lt_of_le_of_ne unitInterval.le_one' hs
    exact Or.inr ⟨s, hs0, hs1, h2 hs1⟩

/-- **`E` is an initial segment of every extension** (the strong form; the batch-156 rendering
`layerSet d (Icc 0 s) = E`, true in this setting though stronger than the printed sentence; used on
p. 347: "Let `e` be the point of `[0, 1]` such that `d⁻¹[[0, e]] = E`"). Every layer of `E` is a
layer of `F`. (`initial_segment_aux`, `H76Lemma5End.lean`.) -/
theorem hagopian76_initial_segment (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E F : Set M} {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F) (hX0 : layer d 0 = layer k 0) :
    ∃ s : unitInterval, 0 < s ∧ layerSet d (Icc 0 s) = E ∧
      ∀ t : unitInterval, ∃ u : unitInterval, layer k t = layer d u :=
  initial_segment_aux hX hi hE hF hEF hX0

/-- **Lemma 4, first paragraph, as printed** (p. 341), in the re-rendered form of
`Hagopian76B.lean` (whose commented-out copy is replaced by a pointer). "There exists a positive
number `s` such that `d[E] = [0, s]`. Since `F` is irreducible, for each positive number `r` less
than `s`, the set `d⁻¹(r)` is in `E`. Since the decompositions of `E` and `F` are minimal, each
element of the decomposition of `E` (except possibly `k⁻¹(1)`) is an element of the decomposition of
`F`." Derived from `hagopian76_initial_segment`. -/
theorem hagopian76_lemma4_layers (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E F : Set M} {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F) (hX0 : layer d 0 = layer k 0) :
    ∃ s : unitInterval, 0 < s ∧ (∀ r, r < s → layer d r ⊆ E) ∧ E ⊆ layerSet d (Icc 0 s) ∧
      (layer d s ∩ E).Nonempty ∧
      ∀ t : unitInterval, t ≠ 1 → ∃ u : unitInterval, layer k t = layer d u := by
  obtain ⟨s, hs0, hseg, hlay⟩ := hagopian76_initial_segment hX hi hE hF hEF hX0
  have hsub : ∀ r, r ≤ s → layer d r ⊆ E := fun r hr => by
    rw [← hseg]
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, ⟨unitInterval.nonneg', (mem_singleton_iff.1 hy) ▸ hr⟩, rfl⟩
  obtain ⟨x, hx⟩ := layer_nonempty hF.2.1.2.1 s
  exact ⟨s, hs0, fun r hr => hsub r hr.le, hseg.ge, ⟨x, hx, hsub s le_rfl hx⟩,
    fun t _ => hlay t⟩

/-- **D1, the configuration to exclude** (restated from the commented-out copy in
`Hagopian76B.lean`): with `s = max d|E`, no layer `k⁻¹(t)`, `t < 1`, lies in a layer of `F` that
meets `k⁻¹(1)`. Derived from `hagopian76_lemma4_layers` and `no_swallowed_of_lemma4_layers`. -/
theorem hagopian76_no_swallowed_layer (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E F : Set M} {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F) (hX0 : layer d 0 = layer k 0) {t u : unitInterval}
    (ht : t < 1) (hsub : layer k t ⊆ layer d u) (hZ : (layer k 1 ∩ layer d u).Nonempty) : False := by
  obtain ⟨-, -, -, -, -, hlay⟩ := hagopian76_lemma4_layers hX hi hE hF hEF hX0
  exact no_swallowed_of_lemma4_layers hE hlay ht hsub hZ

/-! ## B. Lemma 5 (restated from the commented-out copies in `Hagopian76B.lean`) -/

/-- **Lemma 5** (p. 341). At an end set `X` of `E`, take an extension of `E` away from `Z` (Lemma 4,
applied to the reversed map); `X` lies in a layer of it that is not an end set, at which it is lower
semicontinuous; the layers of `E` are its layers (item A). Hagopian's two-sided `F` is not
needed. Then `hagopian76_lemma5_of_ends`. (`lemma5_aux`, `H76Lemma5End.lean`.) -/
theorem hagopian76_lemma5 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    [CompactSpace E] {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    IsContinuousDecomp (Setoid.ker k) :=
  lemma5_aux hX hi hE

/- OPEN (batch 158): `hagopian76_two_sided_extension` — not needed: Lemma 5 is proved without it (`hagopian76_lemma5`). Item A gives `E` as an initial segment of each extension, but the union `F₁ ∪ F₂` still needs a glued admissible map, its irreducibility, and `F₁ ∩ F₂ = E` (the tails beyond `Z` and beyond `X` disjoint), which is an atriodicity argument of the type of `ext_of_branch`, not a consequence of item A. See `OPEN.md`, batch 158, item B.

/-- **The continuum `F` of Hagopian's proof of Lemma 5** (p. 341), from item A: two extensions
meet exactly in `E`. Not needed for Lemma 5 by the route above; prove it if it is short, otherwise
record that it is not needed. -/
theorem hagopian76_two_sided_extension (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ (F₁ F₂ : Set M) (d : (F₁ ∪ F₂ : Set M) → unitInterval),
      IsExtensionAway E (layer k 0) F₁ ∧ IsExtensionAway E (layer k 1) F₂ ∧
      IsMinimalAdmissible (F₁ ∪ F₂) d ∧ Disjoint (layer d 0 ∪ layer d 1) E := by
  sorry
-/

/-! ## C, D. Lemma 6, the unnumbered claims, Lemma 7 (restated from `Hagopian76B.lean`) -/

/- OPEN (batch 158): `hagopian76_closure_extUnion`, `hagopian76_lemma6`, `hagopian76_Rset_composant`, `hagopian76_essential_typeA'`, `hagopian76_lemma7` — the D1 obstruction is gone (item A supplies step 6's "subcollection", Lemma 5 is proved), but steps 1–8 of Lemma 6 were not formalized in this batch: each needs the composant/triod machinery of the 1975 ¶2 argument transported to `Cl R(X, E)` (the limit point `c` of the far ends, the homeomorphisms `h₁`, `h₂`, the triod `C ∪ N ∪ h₁⁻¹[N] ∪ h₂⁻¹[P]`). The containment of an essential continuum in one extension uses `c ∉ R(X, E)` (step 5 of Lemma 6). Lemma 7 uses Lemmas 5 and 6. See `OPEN.md`, batch 158, items C and D.

/-- **Lemma 6, the step "`Cl R(X, E) = Cl R(E)`"** (p. 343). -/
theorem hagopian76_closure_extUnion (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    closure (extUnion E (layer k 0)) = closure (Rset k) := by
  sorry

/-- **Lemma 6** (p. 341). "The continuum `Cl R(E)` is indecomposable." -/
theorem hagopian76_lemma6 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    Fold.Q78.IsIndecomposable (closure (Rset k)) := by
  sorry

/-- **"Since `M` is atriodic, `R(E)` is a composant of `Cl R(E)`"** (p. 343). -/
theorem hagopian76_Rset_composant (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {x : M}
    (hx : x ∈ Rset k) : Rset k = HPC.composant (closure (Rset k)) x := by
  sorry

/-- **"Note that every continuum essential to `R(E)` is of type A′ (Lemma 5)"** (p. 343). -/
theorem hagopian76_essential_typeA' (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {H : Set M}
    (hH : IsEssential k H) : IsTypeA' H := by
  sorry

/-- **Lemma 7** (p. 343). -/
theorem hagopian76_lemma7 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
        (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < δ) →
        (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε < dist t w) →
        ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε := by
  sorry
-/

end Section2

/-! ## E. Moore 1962 Theorem 28 -/

/-- **Moore 1962, Theorem 28** (p. 156). "If `D` is a simple domain and each of the two mutually
exclusive continua `H` and `K` is a subset of `D` [read: of `D ∪ J`] and each of them intersects
`J`, the boundary of `D`, then no pair of points of `H` separates two points of `K` from each other
on `J`." Here `D` is the bounded complementary domain of the simple closed curve `J`.

*Route* (`moore62_theorem28_aux`, `H76Moore28.lean`): an arc `L` from `a` to `b` through the
exterior (accessibility of a simple closed curve from each side, batch 152); the side `T` of the
simple closed curve `P ∪ L` away from `D`; Janiszewski's theorem for `H ∪ L` and `Cl D`. The
batch-151 crossing results are not used. -/
theorem moore62_theorem28 {J D H K : Set Pt} (hJ : TSCC J) (hD : IsOpen D) (hDc : IsConnected D)
    (hDb : Bornology.IsBounded D) (hDJ : frontier D = J) (hH : Fold.Q78.IsContinuum H)
    (hK : Fold.Q78.IsContinuum K) (hHK : Disjoint H K) (hHD : H ⊆ D ∪ J) (hKD : K ⊆ D ∪ J)
    {a b c f : Pt} (ha : a ∈ H ∩ J) (hb : b ∈ H ∩ J) (hc : c ∈ K ∩ J) (hf : f ∈ K ∩ J) (hab : a ≠ b) :
    connectedComponentIn (J \ {a, b}) c = connectedComponentIn (J \ {a, b}) f :=
  moore62_theorem28_aux hJ hD hDc hDb hDJ hH hK hHK hHD hKD ha hb hc hf hab

/-! ## F. The arc `π[E]` parametrized; decomposable accessibility; Lemma 9 -/

section Lemma9

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **`exists_quotient_plane` with the parametrization** `γ t = π(k⁻¹(t))` (report 157, §5).
(`exists_quotient_plane'_aux`, `H76Quot.lean`.) -/
theorem exists_quotient_plane' (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ (π : Pt → Pt) (γ : unitInterval → Pt), IsQuotientMap π ∧
      (∀ p q, π p = π q ↔ layerSetoid k p q) ∧ IsEmbedding γ ∧
      (∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) ∧ range γ = π '' toPt E :=
  exists_quotient_plane'_aux hX hi hE

/-- **Abutting on the same side** (Bing 1960, p. 215: "`cd` and `ef` are said to abut on opposite
sides of `ab` if there is a homeomorphism of `E²` onto itself that takes `ab` onto a horizontal
segment and `cd`, `ef` onto vertical segments which lie except for their points of contact with
`ab` on opposite sides of the line containing `ab`"), the same-side form. The shape is the one
proposed in report 157 §5.
Superseded (batch 159) by the collar form `DecompAccessibleC` (`Hagopian76D.lean`). -/
def AbutSameSide (α C₁ C₂ : Set Pt) : Prop :=
  ∃ (φ : Pt ≃ₜ Pt) (a b x₁ x₂ h₁ h₂ : ℝ), a < x₁ ∧ x₁ < b ∧ a < x₂ ∧ x₂ < b ∧ 0 < h₁ ∧ 0 < h₂ ∧
    φ '' α = Icc a b ×ˢ {0} ∧ φ '' C₁ = {x₁} ×ˢ Icc 0 h₁ ∧ φ '' C₂ = {x₂} ×ˢ Icc 0 h₂

/-- **Decomposably accessible from a side** (p. 344): "there exist arc segments `A` and `B` in
`R² − π[M]` such that (1) `π[U] ∈ Cl A`, (2) `π[Y] ∈ Cl B`, and (3) `Cl A` and `Cl B` abut on the
same side of the arc `π[E]` in `R²` [2, p. 215]". With `γ` the parametrization of `π[E]`. -/
def DecompAccessible (πM : Set Pt) (γ : unitInterval → Pt) (u y : unitInterval) : Prop :=
  0 < u ∧ u < 1 ∧ 0 < y ∧ y < 1 ∧ u ≠ y ∧
    ∃ (A B : Set Pt) (a₀ b₀ : Pt), TArc a₀ (γ u) (closure A) ∧ TArc b₀ (γ y) (closure B) ∧
      A = closure A \ {γ u} ∧ B = closure B \ {γ y} ∧ Disjoint A πM ∧ Disjoint B πM ∧
      AbutSameSide (range γ) (closure A) (closure B)

-- `hagopian76_lemma9` (Lemma 9): proved in batch 163 in collar form (`DecompAccessibleC`), `Hagopian76H.lean`.

end Lemma9

end HPC.Hagopian
