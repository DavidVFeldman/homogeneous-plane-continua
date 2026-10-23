Commission read: `doc/batches/COMMISSION-batch188.md` ("Commission: batch 188 — Part E, Hagopian 1984 V: `𝔇`; claims (5)–(6); `hagopian84_decomp`").

# Report, batch 188

## 0. Summary, omissions

**Every item of the commission is proved.** That covers the transfer lemma (§2), the data,
`𝔇`, disjointness and the relation (§3), claims (5) and (6) (§4), the package and
**`hagopian84_decomp : Hagopian84Decomp`** (§5.1–§5.6), **`hagopian76_theorem1_jones`** (§5.7),
and the printed `⋃𝔅 = M` (§5.8). All are in `HPC/Hagopian/Hagopian84D.lean`, in the skeleton's
shapes, with no shape changes. No declaration contains `sorry`, and nothing was refuted.
`axioms.txt` has **2414 lines** (2392 + 22 added, none removed), and `sorryAx` occurs in none.

After this batch, the arc step `NoArcIndecHomPlane` (Jones 1975) is the only open input of
`Hagopian76Thm1` on the 1984 route.

Status lines:
* STATUS: §2 `omega_layer_of_mem_mid`, `omega_mem_delta_of_mem_mid` proved
* STATUS: §3.1 `exists_coverData84` proved
* STATUS: §3.3 `CoverData84.exists_mem` proved
* STATUS: §3.4 `CoverData84.members_disjoint` proved
* STATUS: §3.5 `CoverData84.setoid`, `CoverData84.cls_eq` proved
* STATUS: §4.1 `CoverData84.omega_subset_members` proved
* STATUS: §4.2 `CoverData84.omega_mem_members` proved
* STATUS: §4.3 `CoverData84.invariant` proved
* STATUS: §5.1–§5.5 `CoverData84.isJonesDecomp` proved
* STATUS: §5.6 `hagopian84_decomp` proved
* STATUS: §5.7 `hagopian76_theorem1_jones` proved
* STATUS: §5.8 `sUnion_cover84_eq_univ` proved

**Omissions (§0 rule).**
1. **The printed (5) for members of `Ω(𝒫(Zᵢ))` outside `⋃𝒫(Zᵢ)′`** (optional in the commission)
   is not formalized; (6) does not need it. §4.2 records the argument.
2. **The lower semicontinuity of `𝔇`** (§7.3) is not formalized and not needed; see §7, H84.34.

## 1. Files and wiring

* `HPC/Hagopian/Hagopian84D.lean`: the skeleton with its proofs, plus the helper lemmas marked
  "(Added.)". These are `midUnion_subset_iUnion84`, `mem_midUnion_of_diff84`,
  `endlayers_subset_closure84`, `exists_piece_between84`, `CoverData84.exists_chain_of_mem`,
  `CoverData84.eq_of_meet_delta`, `CoverData84.setoid_iff`, `delta_translate_small84` and
  `exists_pos_forall_finset84`.
* `HPC.lean` ends with `import HPC.Hagopian.Hagopian84D`.
* `Hagopian84A.lean`: the commented-out copies of Lemmas 13 and 16, `hagopian84_quotient_arc`,
  `hagopian84_decomp` and `hagopian76_theorem1_jones` are replaced by one-line pointers.
* `Hagopian84C.lean`: only the header and the §5 comment are changed (§5.8).
* The uploads moved to `doc/batches/COMMISSION-batch188.md` and
  `doc/batches/skeletons/Hagopian84D.lean`.

## 2. The transfer lemma (proved)

The proof follows commission §2 step by step.
1. `Z = c⁻¹(r)` for the map `c` that regularity gives (`exists_layer_eq_of_minimal`).
2. Take `p` in the strand and in `P 2` (`strand_meets_P2_P0`). The layer `c⁻¹(s)` through `p`
   lies in `P 2` (`layer_subset_link`).
3. `z ∈ ⋃Q` misses `Cl P 2`, so `s ≠ r`.
4. `exists_piece_between84` packages step 4. It applies `minimalAdmissible_restrict` on
   `[[min, max]]`, then `unitInterval.symm` when `r < s`. This gives `d` with `d⁻¹(0) = c⁻¹(s)` and
   `d⁻¹(1) = Z`.
5. Lemma 16′ for `Q` (`strand_layer_of_extension`, `u = 1`, `y = z`).
6. For the second part, `strand_layer_mem_delta`.

The proof uses (2) and not (3).

## 3. The data, `𝔇`, disjointness (proved)

**`exists_coverData84`.**
1. `¬ IsHereditarilyIndecomposable univ` gives a decomposable subcontinuum.
2. `hagopian75_exists_typeA'` gives a minimal admissible `(E, k)` inside it.
3. Lemma 13 with `ε = 1`, `A = ∅`, `B = univ`.
4. `hagopian84_cover`.

**Disjointness** follows the cases of commission §3.4.
* **(a)** `delta5_partition`.
* **(b)** `CoverData84.eq_of_meet_delta`. The common point lies in
  `⋃𝒫(Zᵢ) ∖ Cl(P(Zᵢ)₀ ∪ P(Zᵢ)₄)`, hence in `midUnion` (`mem_midUnion_of_diff84`). The transfer
  lemma then gives `B ∈ Δ(𝒫(Zᵢ))`, and `delta5_partition` for `𝒫(Zᵢ)` gives `A = B`.
* **(c)** If either member meets `⋃Δ(𝒫)`, apply (b) twice.
* **(c), otherwise:** `hagopian76_lemma3` with `h` the identity and the maps of
  `delta_regular_rep`. Their end layers lie in `Cl(·₀ ∪ ·₄) ⊆ ⋃Δ(𝒫)` by (3)
  (`endlayers_subset_closure84`), which `A ∪ B` misses.

**The relation.** Reflexivity uses 3.3 and transitivity uses disjointness. `cls_eq` says the
class of `x` is the member through `x`.

## 4. Claims (5) and (6) (proved)

**4.1 (`omega_subset_members`).** A member `Z ∈ Ω(𝒫) ∖ Δ(𝒫)` lies in `Cl P 0` or `Cl P 4`. So a
point of `Z` is not in `⋃Δ(𝒫)` (`delta5_partition`), and the cover puts it in some
`⋃Δ(𝒫(Zᵢ))`. The transfer lemma finishes.

**4.2 (`omega_mem_members`).**
1. If `W ∉ Δ(Q)`, then `W ⊆ Cl(Q 0 ∪ Q 4) ⊆ ⋃Δ(𝒫)`.
2. Take `w ∈ W` and the member `Y ∈ Δ(𝒫)` through `w`. The transfer lemma makes `Y` a layer of
   `Cl(cc(w))`, the closure of the component of `midUnion Q` through `w`.
3. `W` lies in the component `K′` that it comes from. This is the last part of
   `delta_subset_component`, rerun with `W ⊆ midUnion Q`.
4. Hence `K′ = cc(w)` (`connectedComponentIn_eq`), and `layer_eq_of_common_point` gives `W = Y`.

**The printed (5) in full (not formalized).** The argument of the commission's independent check
is recorded here:
1. Let `W` be a layer, outside `⋃Q′`, of a strand `S = Cl K` of `Q`. Then `W ⊆ Q 0` or
   `W ⊆ Q 4`, so `W ⊆ ⋃Δ(𝒫)`.
2. Take the member `Y ∈ Δ(𝒫)` through a point `v ∈ W`, and its strand `T`.
3. `S ⊄ Y`. Otherwise take `z ∈ K ∩ Q 2`: the transfer lemma makes `Y` a layer of `S`, and no
   layer contains its whole strand.
4. If `S ⊄ T`, Lemma 7 applies, since `T ∖ S ≠ ∅` through `P 2`. If `S ⊆ T`, `layers_agree`
   applies, and its degenerate alternative would put `S` inside `Y`.
5. So `Y = W`.

I see no obstruction, but this argument is not formalized.

**4.3 (`invariant`).** For each chain `R`, `delta_translate_small84` gives
`δ_R = min(ε_R, η_R)`. Here `ε_R` comes from Lemma 15 and `η_R` from `delta5_dist_pos`, which
keeps `h[D] ⊆ midUnion R`. `exists_pos_forall_finset84` takes the minimum over the `Finset`.
Then 4.1 or 4.2 applies.

## 5. The package (proved)

* **usc.**
  * Closed: a member is a layer of a compact set (`isClosed_layer`).
  * Upper semicontinuity: the set `{z : cls z ⊆ U}` is open. For `z₀` in it, take `ε` with
    `thickening ε (cls z₀) ⊆ U`. Lemma 14 at `z₀` gives `δ`, and `isOpen_sUnion_delta5` gives a
    ball `δ′`. Inside the smaller ball, every `cls z` is a member of the same `Δ(R)` and lies
    within `ε` of `cls z₀`.
* **conn:** `layer_nonempty'` and `layer_isPreconnected'`.
* **proper:** `R 0 ≠ ∅` (`inter_iff 0 0`), and a member of `Δ(R)` misses `Cl R 0`.
* **invariant:** claim (6).
* **arc:**
  1. Take `x ∈ P 1 ∩ P 2` and the map `c` that regularity gives.
  2. `exists_interval_in_delta` gives `[a, b]`.
  3. Take the map `e` of `minimalAdmissible_restrict` on `c⁻¹[[a, b]]`. Every fibre of `e` is a
     member of `𝔇`, and by disjointness these fibres are exactly the traces of the classes.
* **`hagopian84_decomp`** and **`hagopian76_theorem1_jones`** are taken from the skeleton
  unchanged.
* **§5.8 `sUnion_cover84_eq_univ`:** a direct corollary of `exists_finite_cover84`.

## 6. Non-vacuity notes

1. **`CoverData84`** (a structure for constructed data). It appears among the hypotheses of
   `exists_mem`, `members_disjoint`, `cls_eq`, `omega_subset_members`, `omega_mem_members`,
   `invariant` and `isJonesDecomp`.
   1. *Not refuted:* `exists_coverData84` builds it whenever `M` is a homogeneous indecomposable
      plane continuum that is not hereditarily indecomposable. This is exactly the hypothesis of
      `Hagopian84Decomp`, so it is not refuted by a short argument (Theorem 1 of 1976 says such
      `M` do not exist, but that is the open target, not a short argument).
   2. *Not equivalent to the conclusions:* `CoverData84` records chains and a cover. The
      conclusions (disjointness, claims (5) and (6), u.s.c., the arc) need Lemma 16′, Lemma 3,
      Lemmas 14 and 15, and the transfer lemma.
2. **Transfer lemma hypotheses** (chain properties of `𝒫` and `Q`, and `h2`).
   1. *Not refuted:* for each `Zᵢ` they are discharged by the chains of `exists_chainZ84`.
   2. *Not equivalent:* `h2` is about the union of `Q`. The conclusion is about the strands of
      `Q`, and the proof needs Lemma 16′.
3. **`hagopian76_theorem1_jones`, hypothesis `NoArcIndecHomPlane`** (a named `Prop` for open
   work).
   1. *Not refuted:* it is Bing's 1960 theorem (indecomposable case), proved in Jones 1975; no
      short argument refutes it.
   2. *Not equivalent to `Hagopian76Thm1`:* it says no homogeneous indecomposable plane continuum
      contains an arc. The conclusion is hereditary indecomposability. The step between them is
      Hagopian 1984's decomposition (`hagopian84_decomp`) together with the plane quotient
      argument of `hagopian76_theorem1_of_jones`. The argument is direct: if `M` is not
      hereditarily indecomposable, its quotient contains an arc. Formally it is a proof by
      contradiction against `hA`, which is how the printed argument runs.
4. **`sUnion_cover84_eq_univ`, hypothesis `hQ`:** as in batch 187, note 4. It is discharged by
   `exists_chainZ84`, and it is not equivalent to the conclusion.

## 7. Ledger entries

The `LEDGER.md` subsection "Hagopian 1984 V: `𝔇`; claims (5)–(6); `hagopian84_decomp` (batch
188)" quotes the printed sentences for each entry.
* **H84.29**, reclassified per §0: the statement is proved (`sUnion_cover84_eq_univ`); the printed
  reason is unargued.
* **H84.30** Disjointness, first case. Lemma 7's `E∖F ≠ ∅` is not argued, and the case `S_A ⊆ Y`
  is not excluded. The transfer lemma covers every case. Gap in exposition.
* **H84.31** Disjointness, last case. Correct, with the end sets read off the maps that run
  straight.
* **H84.32** (5). "(3) and Lemma 7" needs the transfer lemma in the case `S ⊆ Y`. (5) is proved
  where (6) uses it. Gap in exposition.
* **H84.33** (6). The bound `η` is in the proof of Lemma 15 but not in its statement; this batch
  makes it explicit.
* **H84.34** "It follows from Lemma 14 that `𝔇` is continuous". The u.s.c. half is proved. The
  l.s.c. half follows by the same argument from the other inclusion of Lemma 14; it is not
  formalized and not needed.
* **H84.35** The "first note" is not used. Its second half ("intersects `M∖⋃𝒫′`") is unargued.
  No argument was found, and it needs more than the end-set positions of `J(Z)`. Since `M` is not
  locally connected, the components of `⋃𝒫′` are not open. So strands of `𝒫(Zᵢ)` that only come
  near the end sets of `J(Z)` need not have their end layers in different components. Lemma 13 and
  (3) do not supply that.

Nothing is refuted, and the count of defective proofs stays at fourteen.

## 8. Axioms

The `Axioms.lean` group "Hagopian 1984 V (batch 188)" has 22 declarations. The regenerated
`axioms.txt` has **2414 lines** (2392 + 22, none removed), and `sorryAx` occurs in no line. The
per-theorem audit is in `doc/batches/audits/axioms-batch188.txt`. Each of the 22 depends on
exactly `[propext, Classical.choice, Quot.sound]`. They are, all in namespace `HPC.Hagopian`:
`midUnion_subset_iUnion84`, `mem_midUnion_of_diff84`, `endlayers_subset_closure84`,
`exists_piece_between84`, `omega_layer_of_mem_mid`, `omega_mem_delta_of_mem_mid`,
`exists_coverData84`, `CoverData84.exists_mem`, `CoverData84.exists_chain_of_mem`,
`CoverData84.eq_of_meet_delta`, `CoverData84.members_disjoint`, `CoverData84.setoid_iff`,
`CoverData84.cls_eq`, `CoverData84.omega_subset_members`, `CoverData84.omega_mem_members`,
`delta_translate_small84`, `exists_pos_forall_finset84`, `CoverData84.invariant`,
`CoverData84.isJonesDecomp`, `sUnion_cover84_eq_univ`, `hagopian84_decomp`,
`hagopian76_theorem1_jones`.

## 9. Dependency map of `Hagopian76Thm1` (the 1984 route)

```
Hagopian76Thm1
└─ hagopian76_theorem1_jones                              [proved, batch 188]
   └─ hagopian76_theorem1_of_jones                        [proved, batch 184]
      ├─ exists_plane_quotient_of_monotone                [proved]
      ├─ indecomposable_of_monotone_image                 [proved]
      ├─ NoArcIndecHomPlane (Bing 1960 / Jones 1975)      [OPEN, named Prop — the last input]
      └─ Hagopian84Decomp: hagopian84_decomp              [proved, batch 188]
         └─ hagopian84Decomp_of_package                   [proved, batch 186]
            └─ CoverData84.isJonesDecomp                  [proved, batch 188]
               ├─ exists_coverData84                      [proved, batch 188]
               │  ├─ hagopian75_exists_typeA'             [proved]
               │  ├─ Lemma 13                             [proved, batch 187]
               │  └─ hagopian84_cover                     [proved, batch 187]
               ├─ members_disjoint ← transfer lemma, Lemma 3   [proved, batch 188]
               │  └─ transfer lemma ← Lemma 16′           [proved, batch 188 / 187]
               ├─ usc ← Lemma 14                          [proved, batch 186]
               ├─ invariant ← (5), (6), Lemma 15          [proved, batch 188 / 186]
               └─ arc ← exists_interval_in_delta          [proved, batch 186]
```

## 10. Skeleton proposal for the arc step (`NoArcIndecHomPlane`, Jones 1975)

Source: `doc/sources/jones1975.pdf`, transcribed and mapped in `doc/notes/jones75.md`.

**Jones's steps, and the repository material each uses.**
1. **Effros corollary:** `effros_homogeneous` (proved).
2. **(a) hereditary unicoherence and (b) atriodicity:** `hagopian75_lemma1_hu` and
   `hagopian75_lemma1` (proved).
3. **(c) two meeting arcs form an arc:** from (a) and (b). Needs a lemma that an atriodic,
   hereditarily unicoherent union of two arcs is an arc. Arcs as `TArc`, which is not yet linked
   to `M`.
4. **(d) the maximal ray `T`:**
   * `T` is the union of a chain of arcs from `a`, and is an injective image of `[0, ∞)`.
   * Every point of `ab` is a limit of `T − ab`, by a "first point `c`" argument with Effros.
   * `T̄ − T` is nondegenerate, and three nearby points give a triod.
   * Uses (b), (c) and Effros.
5. **(e) accessible arcs are accessible from one side only:** uses collars (`exists_collar`,
   `IsAccessibleFrom`, `exists_accessible_above`) and the density of composants.
6. **(f) the metric lemma on arcs `abc`:** uses Effros only.
7. **The Theorem:**
   * an accessible maximal ray;
   * collar coordinates for `[t₀, t₅]`;
   * `η` from (f);
   * the irreducible subarc `[t_a, t_b]`, with its order fixed by the Jordan curve theorem
     (`jordan_curve_theorem`);
   * the domains `Dᵢ`;
   * `ε`, `δ` from Effros;
   * the fixed point `t_f`, by the intermediate value theorem along `T`;
   * the limit argument contradicting (f).

**Named claims for a first batch** (file `HPC/Jones/Jones75.lean`):
```lean
theorem jones75_f (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) (p : M) {D : Set Pt}
    (hD : IsOpen D) (hpD : (p : Pt) ∉ closure D) :
    ∃ ε > 0, ∀ (a b c : M) (ab bc : Set M), IsArcBetween ab a b → IsArcBetween bc b c →
      ab ∩ bc = {b} → (a : Pt) ∈ D → (c : Pt) ∈ D → ¬ (p ∈ thickening ε ab ∧ bc ⊆ thickening ε ab)
theorem jones75_c (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {A B : Set M} {a b a' b' : M}
    (hA : IsArcBetween A a b) (hB : IsArcBetween B a' b') (hAB : (A ∩ B).Nonempty) :
    ∃ p q, IsArcBetween (A ∪ B) p q
def MaxRay (a : M) (A : Set M) : Set M  -- union of all arcs from `a` containing `A`
theorem jones75_d_ray … : ∃ γ : NNReal → M, Continuous γ ∧ Function.Injective γ ∧ range γ = MaxRay a A
theorem jones75_d_limit … : A ⊆ closure (MaxRay a A \ A)
theorem jones75_e … -- one-sided accessibility, in collar coordinates
theorem jones75_accessible_ray … -- the unargued "T is accessible" (decide first: a gap?)
theorem jones75_noArc : NoArcIndecHomPlane
```
Here `IsArcBetween` is a new definition: a subset homeomorphic to `[0, 1]` with the given end
points. Suggested order: (f), (c), (d), the accessibility sentence, (e), then the Theorem.
Candidate ledger entries: the accessibility of `T`; "So there is a fixed point `t_f`"; and the
final "it is easy to see".

## 11. Files

See `doc/batches/batch188-MANIFEST.txt`; every listed file is in
`doc/batches/batch188-files.tar.gz`.
