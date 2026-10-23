Commission read: `doc/batches/COMMISSION-batch172.md` ("Commission: batch 172 — Part E, Hagopian 1976 XVII: Theorem 1 — the end case of Property 3; the `I₂` case and the side edges by Schoenflies; the ends of crossing components; T15–T17").

(The batch-171 commission and skeleton were uploaded again at the start of this run, by mistake; they
are byte-identical to `doc/batches/COMMISSION-batch171.md` and `doc/batches/skeletons/Hagopian76P.lean`
and were removed from the root. This report answers commission 172 only.)

# Report, batch 172

## 0. Summary

* **A (the end case of Property 3): the end case is closed; Property 3 is reduced to one
  configuration, which is open.** A new lemma, the **swallowing lemma**
  (`continuum_subset_layer_of_open`), says: a subcontinuum `W` of a type A′ continuum `G` that has
  a nonempty relatively open part inside one layer of `G` lies in that layer. The middle translate
  `h[k⁻¹((4/11, 7/11))]` given by `follows_crossing` is such a part of `h[E] ∩ G`. So a layer
  `d⁻¹(v)`, `0 < v < 1`, containing a crossing contains **all** of `h[E]` (`translate_subset_layer`),
  and then all of `h[G]` (`translate_extension_subset_layer`). This happens however the translate
  meets the end sets, so cases (a) and (b) of §1.A are not needed
  (`hagopian76_property3_translate`). What is left is to exclude an `ε₁`-homeomorphism with
  `h[G] ⊆ d⁻¹(v)`, named `Property3End`. Property 3 is proved from `Property3End`
  (`hagopian76_property3_of_end`). `Property3End` itself is proved from either of two statements,
  both open:
  * `Cl R(E) = M` (`property3End_of_closure_Rset`);
  * the batch-169 dichotomy (`property3End_of_dichotomy`).

  Both use `closure_Rset_subset_of_translate`: such an `h` puts `Cl R(E)` inside one layer of
  `h⁻¹[G]`.
* **B (Schoenflies): the `I₂` case is proved; the side edges and pockets are open.**
  * `jordan_inner_collar` builds the inner collar of an arc of a Jordan curve from the square form
    of `plane_schoenflies`.
  * `rect_frontier_domain` shows that `D′` is the Jordan domain of its frontier.
  * `top_component_above_aux` is the `I₂` case.
  * `crossing_sides_cover_schoenflies` combines the bottom-edge and `I₂` cases, with no low-strip
    hypothesis.
* **C (the ends of crossing components): open.**
* **D (T15–T17, the assembly): open; not reached.** The named `Prop` for A is `Property3End`.
  Conditional forms of Property 3 are delivered. No conditional form of Theorem 1 is delivered,
  because T15–T17 themselves (I finite, Property 4, Bing, the first component) are not formalized.
* **Nothing is refuted.** The count of defective proofs stays at fourteen.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76Q` at the end of `HPC.lean`. The regenerated
`axioms.txt` has 1817 lines (1799 + 18), with `sorryAx` in none. All 18
new theorems use only `propext`, `Classical.choice` and `Quot.sound`. No declaration uses `sorry`.
The word occurs only in the comment block at the end of `Hagopian76Q.lean`, which holds the open
shapes.

Files (all under `HPC/Hagopian/`):
* `Hagopian76Q.lean`: the skeleton, with the delivered statements and the open items commented out;
* `H76Swallow.lean`: the swallowing lemma and its consequences for translates;
* `H76InnerCollar.lean`: the inner collar, the Jordan domain `D′`, the `I₂` case.

None of the earlier files is edited: none of them held a commented-out copy of a statement proved
here. The `I₂` case is a part of `crossing_sides_cover'`, which stays open.

## 1. The items

STATUS lines, in order:
* `STATUS: A open (end case closed: hagopian76_property3_translate; Property 3 proved from
  Property3End, and Property3End from Cl R(E) = M or from RsetDichotomy)`
* `STATUS: B open (I₂ case proved: crossing_sides_cover_schoenflies; side edges and pockets open)`
* `STATUS: C open`
* `STATUS: D open (not reached)`

### 1.A The end case of Property 3

**The swallowing lemma** (`continuum_subset_layer_of_open`). Let `G` be a type A′ continuum with
minimal admissible map `d`, let `W ⊆ G` be a continuum, `V` open, and suppose
`∅ ≠ W ∩ V ⊆ d⁻¹(v)`. Then `W ⊆ d⁻¹(v)`.

*Proof.*
1. Suppose `w ∈ W` with `d(w) = u₁ > v`; the case `u₁ < v` is the same for the reversed map
   `σ ∘ d`.
2. `W` meets `d⁻¹(v)` and `d⁻¹(u₁)`, so `d⁻¹((v, u₁)) ⊆ W` (`layerSet_Ioo_subset`).
3. Take `x ∈ W ∩ V`. Lemma 5 gives lower semicontinuity (`lsc_of_minimalAdmissible`): an open
   `Wo ⊇ d⁻¹(v)` in `G` every point of which has its layer meeting `V`.
4. The continuum `d⁻¹[[v, m]]` (`v < m < u₁`) is not contained in `d⁻¹(v)`, so it has a point of
   `Wo` off `d⁻¹(v)`. Otherwise `d⁻¹(v)` would be relatively clopen in it.
5. The layer of that point lies in `d⁻¹((v, u₁)) ⊆ W` and meets `V`. That gives a point of
   `W ∩ V ⊆ d⁻¹(v)` whose parameter is not `v`.

**Consequences.**
* `translate_subset_layer`: suppose `d⁻¹(v)`, `0 < v < 1`, contains `h[k⁻¹(A)]` for a nonempty open
  `A`. Then `h[E] ⊆ d⁻¹(v)`.
  * Apply the lemma to `W = h[E] ∩ G`, which is a continuum by hereditary unicoherence, and to
    `V = h[V₀]`, where `k⁻¹(A) = E ∩ V₀` (`layerSet_eq_inter_open`).
  * Then `h[E]` meets `G` and misses its end sets, so `h[E] ⊆ G` (`subset_of_meets_avoids`).
* `translate_extension_subset_layer`: if `G` is an extension of `E` away from `k⁻¹(0)` and
  `h[E] ⊆ d⁻¹(v)`, then `h[G] ⊆ d⁻¹(v)`. Since `E = d⁻¹[[0, s]]` (`hagopian76_initial_segment`),
  apply the previous result to `G` itself with `A = [0, s)`.
* `layer_disjoint_of_not_subset` (observation §1.A.1): a layer `d⁻¹(v)` that is not inside
  `E = d⁻¹[[0, s]]` misses `E`, so `v > s`. In `hagopian76_property3_translate`, `Cl B ∩ E = ∅`
  (`closure_disjoint_E_of_above`) supplies this.

**`hagopian76_property3_translate`.** This uses the set-up of `follows_crossing`, with `G` an
extension of `E` away from `k⁻¹(0)` (the `F` of T13). If `Cl B ⊆ d⁻¹(v)`, `0 < v < 1`, then
`d⁻¹(v) ∩ E = ∅`, and for the `ε₁`-homeomorphism `h` of `follows_crossing`,
`h[k⁻¹((4/11, 7/11))] ⊆ Cl B` and `h[G] ⊆ d⁻¹(v)`.

**The commission's observations, checked.**
1. *`v` lies beyond `E`:* correct, `layer_disjoint_of_not_subset`.
2. *Cases (a) and (b):* the split is correct, but it is not needed. In either case the swallowing
   lemma applies to the middle piece, which lies in `C` whatever the ends do.
   * In case (b), `h[k⁻¹(t)]` meets `d⁻¹(0) ∪ d⁻¹(1)` and lies in `h[E] ⊆ C`. This contradicts
     `0 < v < 1` at once.
   * The `EndCtl` check asked for in (b) is therefore not needed. It does hold: if
     `h[k⁻¹[[t, 6/11]]] ⊆ F`, then it contains `k⁻¹(1) = d⁻¹(s)`, and `EndCtl` (second half)
     forbids an `ε₁`-move from parameters `≤ 6/11` onto `k⁻¹(1)`. This was checked informally and is
     not formalized, since it is subsumed.
3. *Case (a), "is `h[E]` essential to `R(E)`":* not needed, for the same reason. The absorption step
   in the commission's case (a) is correct: `h[k⁻¹[[6/11, 1]]]` misses `k⁻¹(0)` by `EndCtl`, so it is
   absorbed. But the swallowing lemma already gives `h[E] ⊆ C ⊆ G` directly.

**The remaining configuration: `Property3End`.** An `ε₁`-homeomorphism with `h[G] ⊆ d⁻¹(v)`.
* `closure_Rset_subset_of_translate`: such an `h` gives `Cl R(E) ⊆ U = h⁻¹[d⁻¹(v)]`, an interior
  layer of `h⁻¹[G]`.
  * Every extension `F′` away from `k⁻¹(0)` has the relatively open initial piece `d_{F′}⁻¹[[0, s))`
    inside `E ⊆ G ⊆ U`.
  * The swallowing lemma (in `h⁻¹[G]`) gives `F′ ∩ h⁻¹[G] ⊆ U`, then `F′ ⊆ h⁻¹[G]`, then `F′ ⊆ U`.
  * Close up using `Cl R(k⁻¹(0), E) = Cl R(E)` (Lemma 6, step 8).
* `property3End_of_closure_Rset`: if `Cl R(E) = M`, then `M ⊆ U`, which is impossible.
* `property3End_of_dichotomy`: under the dichotomy, `h[R(E)]` meets `R(E)` (both contain `h[E]`),
  so `R(E) = h[R(E)] ⊆ d⁻¹(v) ⊆ G`. This is against Lemma 4 (`G` has a proper extension).
* `hagopian76_property3_of_end`, `hagopian76_property3_of_closure`: Property 3 (no interior layer of
  the extension contains the closure of a crossing) from `Property3End`, and from `Cl R(E) = M`.

*Obstruction:* without `Cl R(E) = M` or the dichotomy, nothing available excludes the following: a
proper indecomposable `Cl R(E)` inside one layer of `h⁻¹[G]`, with `h[Cl R(E)] ⊆ d⁻¹(v) ⊆ G ⊆ R(E)`.
* Such an `h` preserves the composant of `E`. Any `h` of `follows_crossing` does, since `h[E]` meets
  `B ⊆ R(E)`.
* So the composant trick that removed the dichotomy from T12 (batch 171) does not apply: there `h`
  was chosen, here it is given.

**Note on the paper** (informal). Hagopian's least-`v` argument moves the layer `d⁻¹(v)` to a lower
layer by a small homeomorphism `g`. The configuration found here is exactly what that move has to
exclude: the layer contains a whole translate of the extension. The margin problem of batches
170–171 is no longer the obstruction.

### 1.B The `I₂` case and the side edges, by Schoenflies

**The form of Schoenflies used.** The project's `plane_schoenflies` (batch 159) is the square form.
For a Jordan domain `D` with `∂D = J` and an arc `φ` of `J`, it gives an embedding
`f : [0, 1]² → R²` onto `J ∪ D`, with `f(t, 0) = φ(t)` and the open square mapped onto `D`. The disc
coordinates of the commission are replaced by these square coordinates. No metric in the new
coordinates is needed.

* **`jordan_inner_collar`.** For a closed `Q` missing the arc, take `δ > 0` below the height of the
  compact `f⁻¹[Q]` (`exists_height_below`), and set `N = f[(0, 1) × (0, δ)]`.
  * `N` is connected, as the image of a product of intervals.
  * `N` is open, as `N = V ∩ D` for an open `V` (`f` is an embedding).
  * `N` lies in `D` and misses `Q`.
  * Every point `φ(t) = f(t, 0)` has a neighbourhood `V₁` (the trace of `{y < δ}`) with
    `V₁ ∩ D ⊆ N`.
* **`rect_frontier_domain`.** Let `D′` be open, inside the open rectangle, with frontier `I` plus
  the frame. Then `∂D′` is a simple closed curve (`I ∪ U`, as in `rect_domain_aux`), and `D′` is
  its bounded complementary domain:
  * `D′` misses the unbounded domain, which would otherwise lie in `D′` (`conn_sub_of_frontier`);
  * the bounded domain meets `D′`, so lies in it.

  Hence `D′` is connected. This hypothesis is not among those of the batch-169/171 statements and
  is now derived.
* **`top_component_above_aux` (the `I₂` case).** The argument of the bottom case, with the low
  strip replaced by the collar `F[N]` of the arc `I = [a, b] × (0, c] ∩ F⁻¹[I₂]`:
  * `Q = F⁻¹[π[Z]]` (closed in the collar square) misses `I`, because `Z` misses `π⁻¹[I₂]`;
  * `π⁻¹[F[N]]` is connected (`isPreconnected_preimage_off`), misses `Z`, and contains a point over
    `F(t₀, u)` for some `u ∈ (0, w₂)`, since the vertical below `F(t₀, w₂) ∈ I₂` lies in `D′`
    (`rect_domain_vert`);
  * a component whose closure meets `π⁻¹[I₂]` meets `π⁻¹[F[N]]`, by the neighbourhood property.
* **`crossing_sides_cover_schoenflies`.** The bottom and `I₂` cases together, for compact `Z`
  missing `π⁻¹` of the bottom edge and `π⁻¹[I₂]`. The low strip hypothesis of
  `crossing_bottom_below` is derived from `rect_domain_low`.

**Side edges and pockets (open).**
* *What T17 needs:* that `f(yᵢ₋₁)` (in `L₆`, inside `π⁻¹[D]`) lies in a component of
  `π⁻¹[D] − Cl Cᵢ₋₁` whose closure reaches the bottom edge or `π⁻¹[I₂]`.
* *Is this in Hagopian's argument?* Not as printed. "Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or
  below `d⁻¹[J]`" presupposes that every point of `π⁻¹[D]` off the crossing continuum is above or
  below it. In the square coordinates, a component of `D′ − Z′` (`Z′` the image of
  `Cl Cᵢ₋₁`) can meet `∂D′` only in a side segment, between two points of `Z′` (a pocket).
* Non-separation of the plane by `Z′` does not exclude pockets. Link control keeps `L₆` away from
  the side segments, but not away from a pocket, which can reach inward.
* So the printed sentence has an unargued case. This is a gap in exposition, not a refutation: no
  configuration with `f(yᵢ₋₁)` in a pocket has been constructed.

### 1.C The ends of crossing components (open)

Not proved. Commission §1.C asks whether Property 3 with the first-component argument of T17 makes
C unnecessary. The answer is no, as far as can be seen without formalizing T17 (informal):
* Property 3 (now: from `Property3End`) concerns crossings contained in a single layer of the
  extension.
* "The continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`" concerns how far the closure of a
  crossing component runs along the chain, `L₁` and `L₉`.
* The reduction of A no longer passes through the end links (the batch-171 "end case" is gone), so
  item A no longer bears on C. C remains as stated in batch 171.

### 1.D T15–T17 and the assembly (open)

Not reached. Named `Prop`s:
* `Property3End d ε₁` (`def`, in `Hagopian76Q.lean`): no `ε₁`-homeomorphism carries the extension
  `G` into one of its interior layers. It is used by `hagopian76_property3_of_end`.
* `RsetDichotomy k` (batch 169) and `closure (Rset k) = univ` (batch 169, C.1, commented out as
  `closure_Rset_eq_univ`) each imply `Property3End`.

Proposed names for the other open steps (not introduced as definitions, since nothing uses them
yet): `CoverPocket` (no point of `L₆ ∩ π⁻¹[D]` lies in a pocket component) and `CrossingEnds` (the
statement of `crossing_component_ends`). No conditional form of `Hagopian76Thm1` is stated:
"`I` is finite", Property 4 with its induction, and the use of Bing's lemma are not formalized
even conditionally.

## 2. Ledger entries (`LEDGER.md` §6, batch 172)

1. **p. 347, Property 3** (the four sentences, as in batch 171). **Reduced further; open.**
   * A layer of `F` containing a crossing contains a whole translate `h[F]` of `F`
     (`hagopian76_property3_translate`).
   * Property 3 follows from `Property3End`, which follows from `Cl R(E) = M` or from the dichotomy.
2. **p. 347:** "It follows from Property 3 that I is finite." Not reached. **Open.**
3. **p. 348:** "Note that [x₁, x₂] does not have Property 4." Not reached. **Open.**
4. **pp. 348–349:**
   * "Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J]": the bottom and `I₂` cases are
     **proved** (`crossing_sides_cover_schoenflies`). Components meeting the frontier only in a side
     segment (pockets) are **open**, and the printed argument does not address them (§1.B).
   * "the continuum N does not come within ε₂ of π⁻¹(p₄)": item C, **open**.
   * "Let Cᵢ₋₁ be the first component …": not reached, **open**.

No statement of Hagopian's is refuted. The count stays at fourteen.

## 3. Axioms

Group *Hagopian 1976 XVII (batch 172)* of `Axioms.lean`; the per-theorem output is in
`doc/batches/audits/axioms-batch172.txt`. Each of the 18 theorems depends on
`[propext, Classical.choice, Quot.sound]`:
* `hagopian76_property3_translate`, `hagopian76_property3_of_end`,
  `closure_Rset_subset_of_translate`, `property3End_of_closure_Rset`, `property3End_of_dichotomy`,
  `hagopian76_property3_of_closure`, `crossing_sides_cover_schoenflies`;
* `layerSet_eq_inter_open`, `mem_layer_self`, `param_of_mem_layer`, `swallow_core`,
  `continuum_subset_layer_of_open`, `translate_subset_layer`, `translate_extension_subset_layer`,
  `layer_disjoint_of_not_subset`;
* `jordan_inner_collar`, `rect_frontier_domain`, `top_component_above_aux`.

## 4. Dependency map of Theorem 1, updated

```
T6/T7 ─ hagopian76_D ─ hagopian76_K0 ─ K0_crosscut
            │               │
            │      crossing_translate (Lemma T) ── crossing_piece_of_R (Lemma R)
            │               │
            │        crossing_separates ─ crossing_sides [disjoint]
            │                │
            │        crossing_sides_cover_schoenflies [bottom + I₂: proved]
            │          ├─ crossing_bottom_below ── rect_domain_low
            │          └─ top_component_above_aux ── jordan_inner_collar (plane_schoenflies)
            │                                    └─ rect_frontier_domain (Jordan curve theorem)
            │          side edges / pockets (CoverPocket)                         [open]
T8/T9_full ─ crossing_essential ─ T12_parts12
     │                                        │
 T9_pieces ─ follows_crossing        hagopian76_T12_uncond, hagopian76_T13_uncond
     │
 lemma3_half ─ hagopian76_property3_reduced
     │
 Lemma 5 (lsc) ─ continuum_subset_layer_of_open ─ translate_subset_layer
                                                 ─ translate_extension_subset_layer
     │
 hagopian76_property3_translate ─ hagopian76_property3_of_end ◄── Property3End     [open]
                                                                    ▲
                     closure_Rset_subset_of_translate ─ property3End_of_closure_Rset ◄─ Cl R(E) = M [open]
                                                     └─ property3End_of_dichotomy  ◄─ RsetDichotomy [open]
     │
   crossing_component_ends (CrossingEnds)                                            [open]
     │
   T15–T17 (I finite; Property 4; Bing; covering cases; ends of Cᵢ₋₁)                [open]
     │
   hagopian76_theorem1                                                               [open]
```

## 5. Skeleton proposal for what remains

```
-- A
theorem property3_end … : Property3End d ε₁            -- or: theorem closure_Rset_eq_univ …
-- B
def CoverPocket … : Prop                               -- f(yᵢ₋₁) not in a pocket component
theorem crossing_sides_cover' … (CoverPocket …) :
    π ⁻¹' (F '' D') \ Z ⊆ belowSet π F D' t₀ u₁ Z ∪ aboveSet π F D' t₀ u₂ w₂ Z
-- C
theorem crossing_component_ends … :
    (toPt (closure B) ∩ L 1).Nonempty ∧ (toPt (closure B) ∩ L 9).Nonempty
-- D
theorem hagopian76_I_finite … (Property 3) ; theorem hagopian76_property4_base … ;
theorem hagopian76_property4_step … ; theorem hagopian76_T15_T17 … : False
theorem hagopian76_theorem1_of (h3 : ∀ …, Property3End …) (hP : CoverPocket …)
    (hC : CrossingEnds …) : Hagopian76Thm1
```

## 6. Build provenance

The run started from a checkout with the compiled Mathlib files present and no local build outputs
of `HPC`.
1. `lake build HPC.Hagopian.Hagopian76P` was run first.
2. The new files were checked with `lake env lean`, then built with `lake build HPC.Hagopian.<file>`.
3. Then `lake build HPC`.
4. `axioms.txt` was regenerated with `lake env lean Axioms.lean > axioms.txt`.
