Commission read: `doc/batches/COMMISSION-batch175.md` ("Commission: batch 175 — Part E, Hagopian 1976 XX: Theorem 1 — layers of `F` along a translate; no deep pockets; `x₂ₙ = 1`; Property 4; the induction").

# Report, batch 175

## 0. Summary

* **A (P1–P3, `cover_pocket_middle`): proved, by the shortcut in P3's last bullet, with two shape
  changes.**
  * `component_over_middle_crossing`: every component `C` of `F ∩ π⁻¹[D]` through a point over the
    middle is a crossing component **or meets the far end set `d⁻¹(1)`**.
  * The exception is needed. An extension can end over the middle: cut a longer extension at a layer
    there. The component through a point of that end layer then reaches only one side. This
    justification is informal; no counterexample is formalized.
  * "The middle" is the abscissa range `[3/8, 5/8]`, not `[7/22, 15/22]`; see §1.A.
  * P2 is proved in the form `translate_through_point_in_F`. P1 is neither formalized nor needed.
  * `cover_pocket_middle`: a non-crossing component that misses `d⁻¹(1)` has no point over the
    middle.
* **B (`x₂ₙ = 1`): reduced to one named `Prop`; the reduction is proved.**
  * `hagopian76_x2n_eq_one_of_cut`: for Hagopian's irreducible `F`, `TailCutKeepsSep` implies
    `LastIntervalReachesOne`.
  * `hagopian76_tail_middle` proves the first step of P4: beyond the last crossing interval, the
    components reaching the middle are those that meet `d⁻¹(1)`.
  * `TailCutKeepsSep` itself (the Janiszewski step) is open.
* **C (Property 4 for the top block): open.** It has the same obstruction as B, plus the T12 set-up.
* **D (the induction): open.** P3 reaches the pockets only over `[3/8, 5/8]`; `N`/`ε₂` is unchanged.
* **E (the assembly): open.** The only conditional form is B's.
* **Nothing is refuted.** The count of defective proofs stays at fourteen.

STATUS lines, in order:
* `STATUS: A proved (component_over_middle_crossing, cover_pocket_middle, translate_through_point_in_F; P1 not needed; shapes changed: exception d⁻¹(1), middle [3/8, 5/8])`
* `STATUS: B open, reduced (hagopian76_x2n_eq_one_of_cut: TailCutKeepsSep → LastIntervalReachesOne; hagopian76_tail_middle)`
* `STATUS: C open`
* `STATUS: D open`
* `STATUS: E open`

The build:
* `lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76T` at the end of `HPC.lean`.
* The regenerated `axioms.txt` has 1880 lines (1867 + 13, one per new theorem), with `sorryAx` in none.
* All 13 new theorems use only `propext`, `Classical.choice` and `Quot.sound`.
* No declaration uses `sorry`. The word occurs only in the comment block at the end of
  `Hagopian76T.lean`, which holds the open shapes.

Files (all under `HPC/Hagopian/`):
* `Hagopian76T.lean`: the skeleton, with the delivered statements and the open items commented out;
* `H76Pocket.lean`: boundary bumping inside an extension, P3, P2, no deep pockets, the tail lemma;
* `H76X2n.lean`: the named `Prop` `TailCutKeepsSep` and `x₂ₙ = 1` from it.

No earlier `Hagopian76*.lean` file was edited. The batch-173 `CoverPocket` in `Hagopian76R.lean` is
stated over `L₆`, which `cover_pocket_middle` does not cover (§1.A), so it is not proved as stated
and stays.

## 1. The items

### 1.A P1, P2, P3, `cover_pocket_middle`

**P3, by the shortcut** (`component_over_middle_aux`; skeleton `component_over_middle_crossing`).
Set-up: that of `hagopian76_property3`, without `E ⊆ G`, so that `G` is any type A′ continuum with
`d⁻¹(0) = k⁻¹(0)`.

Statement: there is `c > 0` such that the following holds for
* every domain `D = F[D′]` of height `c₁ ≤ c`, and
* every `y ∈ G ∩ π⁻¹[D]` at abscissa in `[3/8, 5/8]`.

Then `C = connectedComponentIn (G ∩ π⁻¹[D]) y` meets `d⁻¹(1)`, or is an `IsCrossingComponent`.

Proof:
1. **The translate.**
   * Link control (`hagopian76_link_control`) puts `y` in a link `Lⱼ` with `1 ≤ j ≤ 9`.
   * Property 1 (`hP1`) gives an `ε₁`-homeomorphism `h` with `y = h(x)`, `x ∈ E`.
   * The thin strip (`pi_thin_near_layer`, `η = min(ε₁, 1/100)`) gives a point `e ∈ E` within `η` of
     `y`, whose parameter is within `η` of the abscissa of `y`.
   * Then `dist(x, e) < 2ε₁`, so `IsEps1.sep_of_gap` gives `k(x) ∈ (3/11, 8/11]`.
2. **Bumping inside `G`** (`bump_in_extension`). This replaces P2's `Q ⊆ F`. Let `K` be a half of the
   translate: `h[k⁻¹[[0, k(x)]]]` or `h[k⁻¹[[k(x), 1]]]`.
   * `K ∩ G` is a continuum (hereditary unicoherence, `isContinuum_inter_of_HU`).
   * If `K ∩ G ⊆ π⁻¹[D]`: the far end of `K` is not over `D` (`EndCtl`), so `K ⊄ G`. No hair for `G`
     (`subset_of_meets_avoids`) then makes `K` meet `d⁻¹(0) ∪ d⁻¹(1)`. Here `d⁻¹(0) = k⁻¹(0)` is not
     over `D`, so `K ∩ G` meets `d⁻¹(1)`. As a connected subset of `G ∩ π⁻¹[D]` through `y`, `K ∩ G`
     lies in `C`.
   * Otherwise, boundary bumping (`exists_mem_closure_component_notMem`) in `K ∩ G` gives a
     connected `Z ⊆ G ∩ π⁻¹[D]` through `y`, hence `Z ⊆ C`, with a point `q ∈ K ∩ G − π⁻¹[D]` in its
     closure.
3. **Where `q` is.** `π(q)` lies on the frontier of `D`, so `q` is over the axis or over a side
   segment (`IsCrossRegion.frontier_sub`).
   * *Not over the axis.* Then `q ∈ E`. `Cl Z` is a continuum meeting `E` at `q`, and it misses
     `k⁻¹(0)` and `k⁻¹(1)`, which lie over `F(0, 0)` and `F(1, 0)`, outside `Cl D`. So no hair for
     `E` (`hagopian76_no_hair`) gives `Cl Z ⊆ E`. But `y ∈ Z` is over `D`, and `E` is over the axis.
   * *Not over the far side.* This is coarse monotonicity: the left half has parameters `≤ 8/11`,
     the right half `> 3/11`.

The commission asked about D1's step 1 (`Q ∩ E = ∅`). It is not needed in that form: only the
frontier point has to be kept off the axis, and no hair for `E` does that for the closure of the
bumped part.

**Shape changes, at the statement and here.**
1. **The exception "`C` meets `d⁻¹(1)`".** The far end set is the commission's "delicate case" of P2.
   Repeated proper extensions do not remove it: the claim fails when `G` ends over the middle.
   (Informal example: cut an extension `G′` at a layer `d′⁻¹(s)` over the middle; the component
   through that end layer is a half translate reaching one side only.) The exception is carried in
   the statement, and `component_over_middle_crossing_of_end` gives the clean form when `d⁻¹(1)` is
   not over `D`.
2. **The middle is `[3/8, 5/8]`.**
   * `y = h(x)` with an `ε₁`-homeomorphism only places `k(x)` within about two elevenths of the
     abscissa of `y`. Coarse monotonicity at the one-eleventh scale then needs `k(x) ∈ (3/11, 8/11]`.
   * The commission's middle `[7/22, 15/22]` would allow `k(x)` down to about `1/11`. The right half
     of the translate could then fail to clear the left side.
   * So the induction's `L₆` (abscissae `(5/11 − η, 8/11 + η)`) is not inside the middle; see 1.D.
   * The margins come from `IsEps1` (one-eleventh pieces). A finer chain would widen the middle.
     That would change T4/T5 and is not done.

**P2** (`translate_through_middle_aux`; skeleton `translate_through_point_in_F`): every
`y ∈ M` over `F[[3/8, 5/8] × [0, c]]` is `h(x)` as above, with `k(x) ∈ (3/11, 8/11]`. If `y ∈ G`,
every piece `h[k⁻¹[S]]` with the following properties lies in `G`:
* `S ∋ k(x)` is a closed interval;
* the parameters in `S` are `≥ 3/22`, so the piece misses `k⁻¹(0)` by `EndCtl`;
* the piece misses `d⁻¹(1)`.

The proof is no hair for `G`. On the commission's question "Check whether this can repeat": it can.
The end set of each proper extension can again meet `Q`. P3 does not need P2 in the form `Q ⊆ F`,
because bumping is done in `K ∩ G`.

**P1: not formalized, not needed.** The shortcut uses neither `φ` nor the triod. Atriodicity
(Hagopian 1975 Lemma 1) enters only through `subset_of_meets_avoids`, as before. So candidate ledger
entry 4 does not arise.

**`cover_pocket_middle`** (`cover_pocket_middle_aux`): a component of `G ∩ π⁻¹[D]` that is not
crossing and misses `d⁻¹(1)` has no point over `D` at abscissa in `[3/8, 5/8]`. Here "pocket" is read
as "non-crossing component".

### 1.B `x₂ₙ = 1`

**Proved:**
* **`hagopian76_tail_middle`** (`tail_middle_reaches_end_aux`). Suppose every `[x, y] ∈ I` has
  `y < t`. Then every `y′ ∈ G ∩ π⁻¹[D]` at abscissa in `[3/8, 5/8]` with `d(y′) > t` lies in a
  component that meets `d⁻¹(1)`.
  * Proof: if the component were crossing, its irreducible interval `[a, b]` would be in `I`, and
    `d(y′) ≤ b < t`.
  * This is P4's first sentence, corrected by the exception of P3.
* **`hagopian76_x2n_eq_one_of_cut`** (`x2n_eq_one_of_cut`). Hypotheses:
  * the set-up of `hagopian76_property3`;
  * `G ≠ E`, separating `p` from `q` in `O`;
  * irreducibility (T13, `hagopian76_T13_uncond`).

  Conclusion: `TailCutKeepsSep → LastIntervalReachesOne`.
  * Proof: `I` is finite (`I_finite_aux`). Take `t < 1` above every right endpoint and above the
    parameter `s` of `k⁻¹(1)` (`ext_layers`).
  * `d⁻¹[[0, t]]` is then an extension of `E` away from `k⁻¹(0)` (`piece_map` with Lemma 5,
    `lsc_of_minimalAdmissible`). It is proper, since it misses `d⁻¹(1)`.
  * By `TailCutKeepsSep` it separates, so irreducibility gives a contradiction.

**Named `Prop`:**
* `TailCutKeepsSep E d π F c₁ D' O p q`: if `G` separates `p` from `q` in `O`, then so does every
  `d⁻¹[[0, t]]` with `t < 1`, `E ⊆ d⁻¹[[0, t]]`, and `y < t` for all `[x, y] ∈ I`.

**Obstruction** (the commission's "kept inside the middle" check):
* A path from `p` to `q` avoiding `d⁻¹[[0, t]]` may have to leave the middle, to get around crossing
  components of `d⁻¹[[0, t]]`, and there it can meet shallow tail components.
* By `hagopian76_tail_middle`, the only tail components that reach the middle are those meeting
  `d⁻¹(1)`. All other tail components are shallow.
* Shallow tail components touch the side segments. That such a component cannot be part of a
  barrier between two middle points is a statement of plane separation (Janiszewski, compact form).
  The project has it only for polygonal sets (`janiszewski_polygonal`).
* For components meeting `d⁻¹(1)` there is a further question: whether Hagopian's `F` can end over
  the middle. Irreducibility should forbid it, but that is again the cutting step.

### 1.C Property 4 for `[x₂ₙ₋₁, x₂ₙ]` (open)

* Clause (2), "only the last block separates", is the cutting step applied to the gaps between
  blocks as well as to the tail. It has the same obstruction as B.
* Clause (1) needs the point `yₙ ∈ K` and the essential-continuum set-up of T12.

### 1.D The induction (open)

* **Pockets.**
  * `cover_pocket_middle` keeps non-crossing components that miss `d⁻¹(1)` off `[3/8, 5/8]`.
  * The induction needs `f(yᵢ₋₁) ∈ L₆` (Lean index 5), over abscissae `(5/11 − η, 8/11 + η)`, which is
    wider than `[3/8, 5/8]`.
  * It also needs the components of `π⁻¹[D] − P` for `P = d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ Q`, a block plus an
    arc, not a whole extension.
* **`N` and `ε₂`.**
  * P2 applies to any extension of `E` away from `k⁻¹(0)`. `N` lies in the shortest extension `L` of
    `Cl Cᵢ` containing `Cᵢ₋₁`, and `L` is not of that kind.
  * "`L − {L₁, L₁₁}` follows `Cl Cᵢ₋₁` and `Cl Cᵢ`" still needs Property 3 for `L` and the
    first-component argument.

### 1.E The assembly (open)

The only conditional form is `hagopian76_x2n_eq_one_of_cut`. Property 4 and its step are not written
as named `Prop`s: they need `K`, `h`, `f` of T12 and the blocks `xᵢ`, and no proof route is checked.

## 2. Ledger entries (`LEDGER.md` §6, batch 175)

1. **p. 348:** "Note that … `x₂ₙ = 1`." **Open; reduced** to `TailCutKeepsSep`
   (`hagopian76_x2n_eq_one_of_cut`). The tail beyond the last crossing block meets the middle only in
   components reaching `d⁻¹(1)` (`hagopian76_tail_middle`). Gap in exposition, not a refutation.
2. **p. 348:** Property 4 for the top block. **Open** (same obstruction).
3. **pp. 348–349, Cases 1 and 2:**
   * "Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`": **partly addressed.** No
     non-crossing component missing `d⁻¹(1)` reaches the abscissae `[3/8, 5/8]`
     (`cover_pocket_middle`). The induction's range `L₆` is wider.
   * "the continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`": **open**.
   * "Let `Cᵢ₋₁` be the first component …": **open**.
4. **Atriodicity in P1:** does not arise. P1 is not used; atriodicity enters P3 only through
   `subset_of_meets_avoids`, as in earlier batches.

No statement of Hagopian's is refuted. The count stays at fourteen.

## 3. Axioms

Group *Hagopian 1976 XX (batch 175)* of `Axioms.lean`. The per-theorem output is in
`doc/batches/audits/axioms-batch175.txt`. Each of the 13 theorems depends on
`[propext, Classical.choice, Quot.sound]`:
* skeleton: `translate_through_point_in_F`, `component_over_middle_crossing`,
  `component_over_middle_crossing_of_end`, `cover_pocket_middle`, `hagopian76_tail_middle`,
  `hagopian76_x2n_eq_one_of_cut`;
* `H76Pocket.lean`: `bump_in_extension`, `component_over_middle_aux`, `cover_pocket_middle_aux`,
  `component_over_middle_crossing_aux`, `tail_middle_reaches_end_aux`,
  `translate_through_middle_aux`;
* `H76X2n.lean`: `x2n_eq_one_of_cut`.

Named `Prop` introduced: `TailCutKeepsSep` (`def … : Prop`). The only theorem that assumes it is
`hagopian76_x2n_eq_one_of_cut`, as a hypothesis.

## 4. Dependency map of Theorem 1, updated

```
link control + Property 1 + thin strip ── translate_through_point_in_F (P2)          [PROVED]
                    │
bump_in_extension (no hair for G, HU) ──┐
no hair for E, coarse monotonicity ─────┴─ component_over_middle_crossing (P3)        [PROVED]
                    │                       (exception: C meets d⁻¹(1); middle [3/8, 5/8])
                    ├─ component_over_middle_crossing_of_end                         [PROVED]
                    ├─ cover_pocket_middle                                           [PROVED]
                    └─ hagopian76_tail_middle (+ irreducible intervals)              [PROVED]
                                   │
 hagopian76_I_finite, ext_layers, piece_map, T13
                                   │
   TailCutKeepsSep (plane separation: tail not needed)                             [open]
                                   │
   hagopian76_x2n_eq_one_of_cut: TailCutKeepsSep → LastIntervalReachesOne          [PROVED]
                                   │
   Property 4 for [x₂ₙ₋₁, x₂ₙ] (cutting step for gaps; T12 set-up)                 [open]
   induction, Cases 1–2 (pockets over L₆; N and ε₂)                                [open]
                                   │
   hagopian76_theorem1_final                                                       [open]
```

## 5. Skeleton proposal for what remains

```
-- the cutting step, in the plane-topology form it needs
theorem sepIn_of_shallow … (hsep : SepIn O (toPt (A ∪ T)) p q)
    (hT : ∀ C, IsComponentOf C (T ∩ O) → ¬ reaches the middle) (hpq : p, q over the middle) :
    SepIn O (toPt A) p q

-- Hagopian's F does not end over D
theorem end_not_over_D … (hirr : … T13 …) : Disjoint (layer d 1) (crossSet G π F D')

-- then TailCutKeepsSep, and the same with the gaps between blocks for Property 4 (2)
theorem tailCutKeepsSep … : TailCutKeepsSep E d π F c₁ D' (π ⁻¹' (F '' D')) p (f p)

-- widening the middle to L₆: a finer chain (n links instead of 11) in T4/T5,
-- or a two-step translate (h then a second ε₁-homeomorphism along L₆)
theorem component_over_L6_crossing … : … z.1 ∈ Icc (5/11 - η) (8/11 + η) …
```
