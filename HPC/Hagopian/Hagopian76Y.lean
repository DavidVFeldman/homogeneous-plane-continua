import HPC.Hagopian.H76Tip

/-!
# Batch 180: Hagopian 1976, Theorem 1 — the set-up repaired; saturation; 3c; the step

Commission 180. `Thm1Setup`, `exists_thm1Setup` and `hagopian76_theorem1_of_step` are restated in
place in `H76Thm1Setup.lean` (§1.2–§1.3); the composant-data package is `hagopian76_T15_T17_cond4`
(`H76Cond4.lean`, §1.2.2).

Where the items are:

| Item | Status | Lean name (file) |
| --- | --- | --- |
| §1.1 certificate | proved | `property4_lower_false_of_K_eq` (here) |
| §1.2 repaired set-up | proved | `Thm1Setup`, `exists_thm1Setup` (`H76Thm1Setup.lean`) |
| §1.2.2 package with composant data | proved | `hagopian76_T15_T17_cond4` (`H76Cond4.lean`) |
| §1.3 restatements | proved | `exists_thm1Setup`, `hagopian76_theorem1_of_step` (`H76Thm1Setup.lean`) |
| §1.3 positive check | proved | `Thm1Setup.K_meets_crossing` (here) |
| §2.1 tip meets end layer | proved | `tip_meets_end_layer`, `tip_meets_end_layer_mirror`, `tip_end_layer_continuum` (`H76Tip.lean`) |
| 2a tip triod (and mirror) | proved | `tip_triod`, `tip_triod_mirror` (`H76Tip.lean`) |
| 2b own tip layer (third arm nonempty) | proved | `tip_triod_on_tip_layer` (`H76Tip.lean`) |
| 2c degenerate chunk | proved | `degenerate_chunk_iii` (`H76Tip.lean`) |
| 2d nondegenerate chunk | open | comment block below |
| 2e saturation | open | `InnerComponentsCross` stays a hypothesis |
| 3c, E0, E1 | open | comment block below |
| §4 (E2.1–E2.6, the step) | open | `Property4Step` stays a hypothesis |
| Theorem 1 | conditional | `hagopian76_theorem1_of_step` |

The open items are stated in the comment block at the end of this file, with their obstructions; see
also `OPEN.md` (batch 180) and `doc/batches/REPORT-batch180.md`.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 346–349. Route: commission 180.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §1. The set-up -/

/-- **§1.1, certificate.** With `K = {p}`, Property 4 fails for every block below the top: it
would make the proper extension `d⁻¹[[0, x₂ᵢ₋₂]]` separate `p` from `f(p)` in `π⁻¹[D]`, against
`D.irr`.

*Proof* (commission 180 §1.1, steps 1–5; no hole found): `yₙ = p`; `A := d⁻¹[[0, x₂ᵢ₋₂]]` contains
`d⁻¹[J]` and misses `p`, `f(p)` (they are off `D.G`), so it separates them too; `A` is an extension
of `E` away from `k⁻¹(0)` (`piece_map`, `lsc_of_minimalAdmissible`); `A ≠ D.G` since
`x₂ᵢ₋₂ < x₂ₘ = 1` and `d⁻¹(1) ≠ ∅`; this contradicts `D.irr`. -/
theorem property4_lower_false_of_K_eq {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    {F : ℝ × ℝ → Pt} {D' : Set (ℝ × ℝ)} {ε₃ : ℝ} (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) (D : T12Data E k π F D' ε₃) (hK : D.K = {D.p})
    {x : ℕ → unitInterval} {m : ℕ} (hx : StrictMonoOn x (Icc 1 (2 * m)))
    (hx2 : layerSet D.d (Icc 0 (x 2)) = E) (hxm : x (2 * m) = 1) {i : ℕ} (hi2 : 2 ≤ i)
    (him : i ≤ m) :
    ¬ Property4 D (x (2 * i - 3)) (x (2 * i - 2)) := by
  rintro ⟨y, hyK, -, hsep⟩
  rw [hK, mem_singleton_iff] at hyK
  subst hyK
  haveI : CompactSpace D.G := isCompact_iff_compactSpace.mp D.hG.isCompact
  have hlt : ∀ a b, 1 ≤ a → a < b → b ≤ 2 * m → x a < x b := fun a b ha hab hb =>
    hx ⟨ha, by omega⟩ ⟨by omega, hb⟩ hab
  set s := x (2 * i - 2) with hsdef
  have hs0 : 0 < s := lt_of_le_of_lt unitInterval.nonneg' (hlt 1 (2 * i - 2) le_rfl (by omega)
    (by omega))
  have hs1 : s < 1 := by rw [← hxm]; exact hlt _ _ (by omega) (by omega) le_rfl
  have h2s : x 2 ≤ s := hx.monotoneOn ⟨by norm_num, by omega⟩ ⟨by omega, by omega⟩ (by omega)
  set A := layerSet D.d (Icc 0 s) with hA
  have hEA : E ⊆ A := by
    rw [← hx2]; exact layerSet_mono D.d (Icc_subset_Icc le_rfl h2s)
  obtain ⟨pA, hpA, hpA0, -⟩ := piece_map D.hG (lsc_of_minimalAdmissible hX hi D.hG) hs0
    (P := A) rfl
  have hextA : IsExtensionAway E (layer k 0) A := ⟨hEA, pA, hpA, hpA0.trans D.hX0⟩
  have hAG : A ⊆ D.G := layerSet_subset D.d _
  obtain ⟨g1, hg1⟩ := D.hG.2.1.2.1 1
  have hAne : A ≠ D.G := by
    intro h
    have : (g1 : M) ∈ A := by rw [h]; exact g1.2
    obtain ⟨g', hg', hgg'⟩ := this
    have : g' = g1 := Subtype.ext hgg'
    subst this
    have h1 : (1 : unitInterval) ≤ s := by rw [← hg1]; exact hg'.2
    exact absurd (lt_of_lt_of_le hs1 h1) (lt_irrefl _)
  have hJA : toPt (layerSet D.d (Icc (x (2 * i - 3)) s)) ⊆ toPt A :=
    image_mono (layerSet_mono D.d (Icc_subset_Icc unitInterval.nonneg' le_rfl))
  have hAsub : toPt A ⊆ toPt D.G := image_mono hAG
  have hsepG := D.sep
  have hsepA : SepIn (π ⁻¹' (F '' D')) (toPt A) (D.p : Pt) ((D.h.symm.trans D.h₁) D.p : Pt) :=
    ⟨⟨hsepG.1.1, fun h => hsepG.1.2 (hAsub h)⟩, ⟨hsepG.2.1.1, fun h => hsepG.2.1.2 (hAsub h)⟩,
      fun S hS hSO hpS => hsep.2.2 S hS (fun z hz => ⟨(hSO hz).1, fun h => (hSO hz).2 (hJA h)⟩)
        hpS⟩
  exact hAne (D.irr A hextA hsepA hAG)

/-- **§1.3, positive check**: every crossing piece inside `M` meets `K` (S4a with the new `K₀`).
This is what E2.1 uses to choose `yᵢ₋₁`.

*Proof:* a crossing piece missing `K ⊇ K₀ = M ∩ π⁻¹F[{1/2} × (0, w₂)]` lies in `M ∩ π⁻¹[D] − K₀`,
hence in `π⁻¹[D] − π⁻¹F[{1/2} × (0, w₂)]`; its closure meets both open side segments, against the
cross-cut lemma `hagopian76_K0_crosscut`. -/
theorem Thm1Setup.K_meets_crossing (S : Thm1Setup M) {C : Set Pt}
    (hC : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ C) (hCM : C ⊆ M) :
    (C ∩ toPt S.D.K).Nonempty := by
  by_contra hne
  have hc1 : S.c₁ ≤ 1 := S.hc₁.trans S.hS.c_le
  refine hagopian76_K0_crosscut S.hπ S.hF (by norm_num : (0 : ℝ) < 3 / 22)
    (by norm_num : (3 / 22 : ℝ) < 19 / 22) (by norm_num : (19 / 22 : ℝ) < 1) hc1 S.hI S.hIs
    S.hDo S.hR.sub S.hDf (t₀ := 1 / 2) ⟨by norm_num, by norm_num⟩ S.hw₂ S.hFw S.hseg
    hC.preconnected ?_ hC.left hC.right
  intro z hz
  refine ⟨hC.subset_O hz, fun hzV => hne ⟨z, hz, ⟨z, hCM hz⟩, ?_, rfl⟩⟩
  rw [S.hK]
  exact mem_insert_of_mem _ hzV

end Thm1

/-! ## Open items (commission 180 §2–§4)

The obstructions are in `OPEN.md` (batch 180) and in `doc/batches/REPORT-batch180.md` §2–§4.

**OPEN (2d, `no_end_layer_chunk`).** Not formalized. What is missing, in order: (1) the reduction of
a non-crossing component `W` to "one half `K⁻` or `K⁺` lies in `O`" (commission 178 §3b, step 2,
checked informally in report 178, not formalized); (2) the choice of `zⱼ → c` in `F ∩ U` with
`d(zⱼ) < 1` (void interior of `d⁻¹(1)` in `F`), and the non-crossing of the components `Wⱼ` for large
`j` (finiteness, `crossing_components_finite`); (3) the transfer of (iii) to `zⱼ` through
`c ∉ hⱼ[E]` (needs the strand lemma at `zⱼ` with the margin of §2.2); (4) the edge case where `zⱼ`
lies on its own tip layer and 2b's third arm is empty. With (1)–(4), `tip_triod`,
`tip_triod_on_tip_layer` and `degenerate_chunk_iii` close 2a–2c.

theorem no_end_layer_chunk : … := by
  sorry

**OPEN (2e, `innerComponentsCross_hagopian`).** Needs 2d and step 2 of commission 178 §3b.

theorem innerComponentsCross_hagopian (S : Thm1Setup M) :
    InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)) := by
  sorry

-- `block_components_cross` (3c), `property4_step_unless` (E0, E1): proved in batch 181 (`H76Block3c.lean`, `Hagopian76Z.lean`).

**OPEN (§4: E2.1, E2.4, the cap, E2.5, Case 2; `hagopian76_property4_step`).** Not started beyond
the set-up: the fields used by each step are in `Thm1Setup` (report §1.2), and
`Thm1Setup.K_meets_crossing` gives the choice of `yᵢ₋₁ ∈ K` in E2.1. E2.1 needs the shortest
extension `L` (a chain-intersection argument over the extensions in `h[R(E)]`); E2.4 needs `H ⊆ L`
identified as an extension of a piece of `h[E]`; the cap needs the two-point intersection
`d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∩ Q`; E2.5 needs a second frame in `O_L` and the bound of E2.5.2 (the segment
`[yᵢ₋₁, f(yᵢ₋₁)]` in `O`), which is not a uniform property of `ε₃` (report §1.2, field audit);
Case 2 needs "`Cᵢ₋₁` is above `d⁻¹[I]`" (report §4.5).

theorem hagopian76_property4_step (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ)
    (hx : S.IsBlocks x m) : Property4Step S.D x m := by
  sorry

**OPEN (`hagopian76_theorem1_final`).** By `hagopian76_theorem1_of_step` (the strongest conditional
form), it follows from `innerComponentsCross_hagopian` and `hagopian76_property4_step`.

-- `hagopian76_theorem1_final`: proved in batch 190 as `hagopian76_theorem1`, `Jones75B.lean`.
-/

end HPC.Hagopian
