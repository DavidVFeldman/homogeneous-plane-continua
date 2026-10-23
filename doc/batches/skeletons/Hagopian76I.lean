import HPC.Hagopian.Hagopian76H

/-!
# Batch 164 skeleton: Hagopian 1976, Theorem 1 — the reparametrization; T7 (`I₂`); T8 (`D`);
# T9 in full; T11 (`K`); Property 3

Save as `HPC/Hagopian/Hagopian76I.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76I` at the end of `HPC.lean`. The items are marked *shape left to you*:
they are internal steps of Theorem 1, and their shapes must serve T12–T17 (report 162 §5). For each,
quote the printed sentence it renders. Unproved items are to be commented out with an `OPEN` note, as
before.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 345–347.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **The reparametrization** (OPEN.md, batch 163): a type A′ continuum with an accessible interior
layer can be given a minimal admissible map whose accessible layer lies outside `[3/22, 19/22]`,
with `π`, `γ` and the collar transported. *Shape left to you.* -/
theorem hagopian76_reparam : True := by
  sorry

/-- **T7** (p. 346). [Quotation moved to doc/sources/transcriptions/hagopian76.md, §doc/batches/skeletons/Hagopian76I.lean, docstring of `hagopian76_T7` (Hagopian 1976, p. 346); batch 204.] *Shape left to you*; commission §1 has notes. -/
theorem hagopian76_T7 : True := by
  sorry

/-- **T8** (p. 346). "Define `r` and `s` to be the end points of `I₂` belonging to `⟨p₁, q₁⟩` and
`⟨p₅, q₅⟩` respectively. Let `D` be the bounded complementary domain of
`I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩` in `R²`." Include property (D) of `hagopian76_T9`.
*Shape left to you.* -/
theorem hagopian76_T8 : True := by
  sorry

/-- **T9 in full** (p. 346). "Suppose `B` is a component of `M ∩ π⁻¹[D]` that intersects
`⋃{Lᵢ : 4 ≤ i ≤ 8}`. Since `M` is atriodic, it follows from Property 1 and Lemma 5 that `Cl B` is
the image of a subcontinuum of `E` (essential to `R(E)`) under an `ε₁`-homeomorphism. Note that the
chain `L − {L₁, L₁₁}` follows `Cl B`." Also the definition of `ε₂` (p. 346: "the minimum of `ε₁` and
`ρ(M, π⁻¹[I₁ ∪ I₂])`") and Property 2 at that `ε₂` (`hagopian76_property2`). *Shape left to you.* -/
theorem hagopian76_T9_full : True := by
  sorry

/-- **T11** (p. 347). "Let `K` be the component of `π⁻¹[D ∩ ⟨p₃, q₃⟩]` whose closure meets both
`π⁻¹(p₃)` and `π⁻¹[I₂]`. Note that `K` separates `L₂ ∩ M ∩ π⁻¹[D]` from `L₁₀ ∩ M ∩ π⁻¹[D]` in
`π⁻¹[D]`." *Shape left to you.* -/
theorem hagopian76_T11 : True := by
  sorry

/-- **Property 3** (p. 347), in full, for any extension `F` of `E` away from `k⁻¹(0)` (the property
its proof uses; report 161 §1.4), with `hagopian76_property3_shift`. *Shape left to you.* -/
theorem hagopian76_property3 : True := by
  sorry

end HPC.Hagopian
