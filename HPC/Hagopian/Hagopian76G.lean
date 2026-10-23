import HPC.Hagopian.H76Lemma7Ray

/-!
# Batch 162 skeleton: Hagopian 1976, Lemma 7 by half-ray density; Lemma 9's proof in collar
# rectangles; T6–T8 (`I₁`, `I₂`, `D`); T9 in full; T11; Property 3

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 343–347. The uploaded skeleton is kept
unchanged in `doc/batches/skeletons/Hagopian76G.lean`; the report is
`doc/batches/REPORT-batch162.md`.

**Status.**
* **Proved** (item A): `halfray_dense` (skeleton shape, unchanged) and `hagopian76_lemma7`
  (skeleton shape, unchanged), by the route of commission 162 §1, steps 1–5. Supporting files:
  * `H76HalfRay.lean`: end layers of pieces (`piece_end_layers`, `piece_map`), independence of
    `R(·)` from the map (`Rset_eq_of_maps`), `extUnion_eq_of_subset`, `closure_Rset_piece`,
    `closure_Rset_of_common`, `closure_Rset_essential` (`Cl R(G) = Cl R(E)` for `G` essential), the
    separation of the two half-rays (`halfray_inter_subset`) and their density (`halfray_dense_aux`);
  * `H76Lemma7Ray.lean`: `exists_F_halfray` (steps 3–4) and `lemma7_aux` (Lemma 7).
* **Also proved:** `hagopian76_property2` (T10, Property 2), immediate from Lemma 7.
* **Open** (commented out below, no `sorry`; obstructions in `OPEN.md`, batch-162 section): Lemma 9
  (item B), T6, T7, T8, T9 in full, T11, Property 3.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## A. Lemma 7 -/

/-- **Half-ray density at any layer.** For a continuum `G` essential to `R(E)`, with its minimal
map `d` and an interior layer `d⁻¹(u)`, each of the two "half-rays" of the composant `R(E)` from
`d⁻¹(u)` is dense in `Cl R(E)`: the union of the extensions of `d⁻¹[[u, 1]]` away from `d⁻¹(u)`,
and that of the extensions of `d⁻¹[[0, u]]` away from `d⁻¹(u)`. For `G = E` this is
`hagopian76_closure_extUnion` and `closure_extUnion_one`.

Proof (`halfray_dense_aux`): the half `d⁻¹[[u, 1]]` carries a minimal admissible map with end layers
`d⁻¹(u)`, `d⁻¹(1)` (`piece_map`); by Lemma 6, step 8, the closure of its extensions away from `d⁻¹(u)`
is `Cl R(d⁻¹[[u, 1]])`; this equals `Cl R(G)` (`closure_Rset_piece`: extensions away from a common
end set coincide, `extUnion_eq_of_subset`), and `Cl R(G) = Cl R(E)` (`closure_Rset_essential`). -/
theorem halfray_dense (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hGE : IsEssential k G) {u : unitInterval} (hu0 : 0 < u)
    (hu1 : u < 1) :
    closure (extUnion (layerSet d (Icc u 1)) (layer d u)) = closure (Rset k) ∧
      closure (extUnion (layerSet d (Icc 0 u)) (layer d u)) = closure (Rset k) :=
  halfray_dense_aux hX hi hE hG hGE hu0 hu1

/-- **The two half-rays meet only in the layer** (commission 162 §1, step 3). -/
theorem halfray_inter (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {G : Set M}
    {d : G → unitInterval} (hd : IsMinimalAdmissible G d) {u : unitInterval} (hu0 : 0 < u)
    (hu1 : u < 1) {Kup Kdn : Set M}
    (hKup : IsExtensionAway (layerSet d (Icc u 1)) (layer d u) Kup)
    (hKdn : IsExtensionAway (layerSet d (Icc 0 u)) (layer d u) Kdn) :
    Kup ∩ Kdn ⊆ layer d u :=
  halfray_inter_subset hX hi hd hu0 hu1 hKup hKdn

/-- **Lemma 7** (p. 343), restated. Route (commission §1): Hagopian's `F` taken inside the
translate `f hᵢ[R(E)]`, on the side of the layer `f[Uᵢ]` that does not contain `t`, by
`halfray_dense`; then `hagopian76_lemma7_triod`. The continuum `F` is `f hᵢ[K]` for an extension `K`
of one half of `hᵢ⁻¹[Hᵢ]` away from the layer `hᵢ⁻¹[Uᵢ]`. Whether `F` is essential to `f hᵢ[R(E)]`
was not checked, and is not used: the proof uses only `u ∈ F`, `t ∉ F` and `F ∩ A ≠ ∅`.
(`lemma7_aux`.) -/
theorem hagopian76_lemma7 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
        (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < δ) →
        (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε < dist t w) →
        ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε :=
  lemma7_aux hX hi hE hε

/-! ## T10: Property 2 (from Lemma 7) -/

/-- **T10, Property 2** (p. 346). "Define `ε₂` to be the minimum of `ε₁` and `ρ(M, π⁻¹[I₁ ∪ I₂])`. By
Lemma 7, there exists a positive number `ε₃` less than `ε₂` such that if `h` is an
`ε₃`-homeomorphism of `M` onto `M`, then `h[R(E)]` has the following property: PROPERTY 2. If `H` is
a continuum essential to `h[R(E)]` with end sets `T` and `V` such that `ρ(T, V) < ε₃` and if there
exists an element `U` of the decomposition of `H` such that `ρ(T, U) > ε₂`, then each point of `R(E)`
is within `ε₂` of `H`." Not an item of this batch (report 161 §5 lists it for the remainder); added
because it is immediate from Lemma 7. Stated for every `ε₂ > 0` (Hagopian's `ε₂` needs `I₁`, `I₂`,
which are open); "essential to `h[R(E)]`" is rendered as in Lemma 7, `IsEssential k (h ⁻¹' H)`. -/
theorem hagopian76_property2 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₂ : ℝ} (hε₂ : 0 < ε₂) :
    ∃ ε₃ > 0, ε₃ < ε₂ ∧ ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₃) →
      ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
        (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < ε₃) →
        (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε₂ < dist t w) →
        ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε₂ := by
  obtain ⟨δ, hδ, hL⟩ := hagopian76_lemma7 hX hi hE hε₂
  refine ⟨min δ (ε₂ / 2), lt_min hδ (by positivity), (min_le_right _ _).trans_lt (by linarith),
    fun h hh H hH d hd ⟨t, ht, v, hv, htv⟩ hU => ?_⟩
  exact hL h (fun w => (hh w).trans_le (min_le_left _ _)) H hH d hd
    ⟨t, ht, v, hv, htv.trans_le (min_le_left _ _)⟩ hU

/-! ## B. Lemma 9 and the collar geometry (open) -/

-- `hagopian76_lemma9` (Lemma 9, collar form): proved in batch 163, `Hagopian76H.lean`.

-- `hagopian76_T6` (T3, T6): proved in batch 163, `Hagopian76H.lean`.

-- `hagopian76_T7`, `hagopian76_T8`, `hagopian76_T9_full`, `hagopian76_T11`: proved in batch 165,
-- `Hagopian76J.lean` (T8 as property (D), T11 with `K` replaced by `π⁻¹[D ∩ ⟨p₃, q₃⟩]`).

/- **OPEN (batch 162, Property 3).** p. 347: "No component of `F ∩ π⁻¹[D]` whose closure meets both
`π⁻¹[⟨p₁, r⟩]` and `π⁻¹[⟨p₅, s⟩]` is contained in an element of the decomposition of `F`. … Let `v`
be the first point of `[0, 1]` such that …". Needs `D` (T8). (i) "the first point `v`" is unargued
(ledger check 162.7): the set of such `v` is closed only if a limit of crossing components contained
in layers `d⁻¹(vₙ)` again contains a crossing component, which is again the crossing property of
`D`; (ii) as in batch 161. The step "By Lemmas 2 and 3" is proved (`hagopian76_property3_shift`).
-/

end Thm1

end HPC.Hagopian
