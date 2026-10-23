import HPC.Hagopian.Hagopian84B

/-!
# Batch 187 skeleton: Hagopian 1984 IV — Lemma 13; Lemma 16′; the bridge `J(Z)`

Save as `HPC/Hagopian/Hagopian84C.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian84C` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; record each shape in the report. Unproved items are
commented out with an `OPEN` note, as before. Every theorem with a named `Prop` or structure among
its hypotheses gets a non-vacuity note.

Source: Hagopian 1984 (`doc/sources/hagopian1984.pdf`), pp. 339–343. Route: commission 187.
Indexing as in `Hagopian84B.lean`: links `P 0, …, P 4` (the paper's `P₁, …, P₅`), `P 2` is the
paper's `P₃`, `midUnion P = ⋃𝒫′`. A *strand* is the closure of a component of `midUnion P`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## §2. Lemma 13

Prove `chainLinks84_runsStraight`, `chainLinks84_regular` (your batch-186 shapes, commented out in
`Hagopian84B.lean`) and `hagopian84_lemma13` (skeleton shape, also there). Move the statements
here or uncomment them in place; either way, leave one-line pointers. Route: commission 187 §2. -/

/-! ## §3. Lemma 16′ -/

section Lemma16

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§3.2, identification**: for `x ∈ ⋃𝒫∖Cl(P 0 ∪ P 4)`, the layer through `x` of the strand
through `x` is a member of `Δ(𝒫)` (hence the member containing `x`). -/
theorem strand_layer_mem_delta {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P)
    (hr : IsRegular5 P) {x : M} (hx : x ∈ midUnion P) (hx0 : x ∉ closure (P 0 ∪ P 4))
    {c : closure (connectedComponentIn (midUnion P) x) → unitInterval}
    (hc : IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) x)) c)
    {t : unitInterval} (hxt : x ∈ layer c t) : layer c t ∈ Delta5 P := by
  sorry

/-- **§3.4, the degenerate alternative is impossible**: if `(F, d)` is type λ and its end layer
`d⁻¹(0)` misses `midUnion P`, no layer of `F` contains a strand. -/
theorem not_strand_subset_extension_layer (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P) (hr : IsRegular5 P)
    {F : Set M} {d : F → unitInterval} (hd : IsMinimalAdmissible F d)
    (hd0 : Disjoint (layer d 0) (midUnion P)) {y : M} (hy : y ∈ midUnion P) (u : unitInterval) :
    ¬ closure (connectedComponentIn (midUnion P) y) ⊆ layer d u := by
  sorry

/-- **§3.1, Lemma 16′** (p. 343: "By Lemmas 7 and 16, each element of the decomposition of `F(Z)`
that intersects `⋃𝒫′` is an element of the decomposition of the closure of a component of
`⋃𝒫′`"), for any type λ `F` whose end layer `d⁻¹(0)` misses `midUnion P`. -/
theorem strand_layer_of_extension (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P) (hr : IsRegular5 P)
    {F : Set M} {d : F → unitInterval} (hd : IsMinimalAdmissible F d)
    (hd0 : Disjoint (layer d 0) (midUnion P)) {u : unitInterval} {y : M} (hy : y ∈ layer d u)
    (hym : y ∈ midUnion P) :
    ∃ c' : closure (connectedComponentIn (midUnion P) y) → unitInterval,
      IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) y)) c' ∧
        ∃ t, layer d u = layer c' t := by
  sorry

end Lemma16

/-! ## §4. The bridge `J(Z)` (p. 343) -/

section Bridge

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§4.2**: a strand layer meeting `Cl (P 0)` lies in `Cl (P 0)` (and likewise for `P 4`); so a
member of `Ω(𝒫)∖Δ(𝒫)` lies in `Cl (P 0)` or in `Cl (P 4)`, and misses `Cl (P 2)`. *Shape left to
you.* -/
theorem omega_not_delta_side : True := by
  sorry

/-- **§4.4, the bridge** (p. 343, "Hence there is an essential subcontinuum `J(Z)` of `F(Z)` that
contains `Z`, misses `Cl P₃`, and has one end set in `K(Z) ∩ (⋃Δ(𝒫))` and the other end set in
`(⋃Δ(𝒫))∖K(Z)`"). Adding "the two end layers lie in different components" is welcome. -/
theorem exists_bridge84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P) (hr : IsRegular5 P)
    {Z : Set M} (hZ : Z ∈ Omega5 P) (hZd : Z ∉ Delta5 P) :
    ∃ (J : Set M) (j : J → unitInterval), IsMinimalAdmissible J j ∧ (∃ t, Z = layer j t) ∧
      Disjoint J (closure (P 2)) ∧ layer j 0 ∈ Delta5 P ∧ layer j 1 ∈ Delta5 P ∧
      ∀ u, (layer j u ∩ midUnion P).Nonempty → ∃ y ∈ midUnion P,
        ∃ c' : closure (connectedComponentIn (midUnion P) y) → unitInterval,
          IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) y)) c' ∧
            ∃ t, layer j u = layer c' t := by
  sorry

end Bridge

/-! ## §5. If time remains: `𝒫(Z)` and the cover

**§5.1, `𝒫(Z)`**: Lemma 13 for `J(Z)` with `A := closure (P 2)`, `B := ⋃₀ Delta5 P`, and
`Z ∈ Delta5 (𝒫(Z))`. *Shape left to you.* **§5.2, the cover**: reconnaissance only (commission 187
§5.2); report the argument for the closedness of `⋃𝔅`, or the obstruction. -/

end HPC.Hagopian
