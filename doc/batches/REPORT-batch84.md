Commission read: `COMMISSION-batch84.md`, with its skeleton `Snake51.lean` (saved as `HPC/Plane/Snake51.lean`; `import HPC.Plane.Snake51` added at the end of `HPC.lean`).

# Report — batch 84: Bing 1951 Theorem 4, and the pseudo-arc in the plane

**Summary.**
* **Counterexample.** The skeleton's `exists_rect_chain_following` is **false as stated**. This is proved: `rectStepSkeleton_false : ¬ RectStepSkeleton` in `HPC/Plane/Counter.lean`, where `RectStepSkeleton` is the skeleton's statement, copied verbatim as a `Prop`. The skeleton's statement is kept, commented out, in `Snake51.lean` with the reason. A **reshaped** `exists_rect_chain_following` is proved in its place (§2.1).
* `theorem4`, `exists_description_plane` and `pseudoArc_exists` are **proved with their conclusions unchanged**.
* The four skeleton definitions (`IsOpenRect`, `HasRoom`, `IsRectChain`, `IsEpsChain`/`IsSnakeLike`) are kept verbatim. The working invariant for plane chains is a new definition, `IsTame` (§3.1–3.2).
* `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every result of this batch, including the counterexample. The output is in `axioms-batch84.txt`, produced by `lake env lean Axioms84.lean`.
* `lake build HPC` completes. The only `sorry` warnings are the three parked ones, which this batch did not touch:
  * `HPC/Fold/Theorem4.lean:23` (`theorem3_end`);
  * `HPC/PseudoArc/Theorem14.lean` (`covering_step`);
  * `HPC/PseudoArc/Theorem14.lean` (`theorem14`).
  
  No file under `HPC/Plane/` contains a `sorry`, apart from the text of the commented-out skeleton statement.
* `covering_step`, `theorem14` and `theorem3_end` were not attempted (§4.3 of the commission).

**Files** (all new, in `HPC/Plane/`):
* `Snake51.lean`: the skeleton. Final statements, the reshaped planar step, and `Description.links_subset_compact`.
* `Counter.lean`: the counterexample.
* `StdChain.lean`: `Pt`, the standard rectangles `stdRect j = (2j, 2j+3) × (0,1)`, the chain `tameChain Φ m`, `IsTame`, overlap zones and end boxes.
* `Joints.lean`: the combinatorial core. Joint positions for a slow pattern with unit steps.
* `Shear.lean`: the folding homeomorphism `Ψ`, a composition of two shears.
* `StdStep.lean`: `std_step`, the planar step in standard coordinates.
* `RealStep.lean`: `real_step`, the step for tame chains, moved by uniform continuity.
* `Stutter.lean`: stuttered Bing patterns, and `crooked_of_tight_pat`.
* `Descr.lean`: the description of the pseudo-arc in the plane.
* `Transfer.lean`: restriction of a description to a compact set containing its links. It gives `isContinuum_M_of` and `theorem13_of`.
* `CSide.lean`: minimal covering chains, and the refinement step on the `C`-side.
* `T4.lean`: the construction of Theorem 4, and Theorem 11 applied to it.

Also `Axioms84.lean` and `axioms-batch84.txt`.

## 1. Counterexamples

**The skeleton's `exists_rect_chain_following` is false** (`HPC/Plane/Counter.lean`, `rectStepSkeleton_false`, proved).

The data:
* the coarse chain `D` of three open rectangles `(0,1)×(0,1)`, `(1/2,21/2)×(0,1)`, `(10,11)×(0,1)`;
* the identity pattern `x = id : Fin 3 → Fin 3`, which is onto and has unit steps;
* `n = 3` and `ε = 1`.

`D` is a chain, every link is an open rectangle, and it has room: the witnesses are `(1/4,1/2)`, `(5,1/2)` and `(43/4,1/2)`. So `IsRectChain D` holds.

Why no `D'` exists:
* `D'_1` meets `D'_0`, and `closure D'_0 ⊆ D_0`, so `D'_1` has a point with first coordinate `< 1`.
* `D'_1` also meets `D'_2`, and `closure D'_2 ⊆ D_2`, so it has a point with first coordinate `> 10`.
* `D'_1 ⊆ D_1` is bounded, so `diam D'_1 > 9 > ε`.

The failure is general. Wherever the pattern steps (`x t ≠ x (t+1)`), one or two fine links must bridge from the private part of one coarse link to the private part of the next. So the fine mesh cannot go below the scale of the coarse overlaps if the pattern is allowed to change value at every index. The repair is a **slowness** hypothesis (§3.3).

No other skeleton statement is false.

## 2. Targets, in order

### 2.1 `exists_rect_chain_following` — reshaped, proved

```lean
theorem exists_rect_chain_following {m : ℕ} (D : Chain Pt m) (hD : IsTame D) (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ) (x : Fin n → Fin m), 0 < n →
      (∀ t t' : Fin n, t'.val = t.val + 1 → ((x t' : ℤ) - (x t : ℤ)).natAbs ≤ 1) →
      (∀ s s' : Fin n, (x s : ℤ) + 2 ≤ x s' → N ≤ ((s : ℤ) - (s' : ℤ)).natAbs) →
      ∃ D' : Chain Pt n, IsTame D' ∧
        (∀ t, closure (D'.link t) ⊆ D.link (x t)) ∧
        (∀ (t : Fin n) (l : Fin m), (D'.link t ∩ D.link l).Nonempty →
          ∃ t' : Fin n, (t'.val ≤ t.val + 1 ∧ t.val ≤ t'.val + 1) ∧ l = x t') ∧
        (∀ t, Bornology.IsBounded (D'.link t) ∧ (Metric.diam (D'.link t) ≤ ε ∨
          ∃ k k' : Fin m, k.val ≤ k'.val ∧ k'.val ≤ k.val + 1 ∧
            D'.link t ⊆ D.link k ∪ D.link k'))
```

The changes, with their reasons:

1. **Rectangle chains are replaced by tame chains.**
   * `IsTame D` means `D.link j = Φ '' stdRect j` for some homeomorphism `Φ` of the plane.
   * The fine chain is `Φ ∘ Ψ` applied to the standard rectangles, where `Ψ` is an explicit piecewise-linear homeomorphism (two shears). Its links are homeomorphic images of rectangles, not axis-parallel rectangles.
   * Tameness is inherited by the fine chain, and it gives all the "room" the next step needs (overlap zones, private parts, end boxes) in standard coordinates. So `HasRoom` is not used as the invariant. The definition is kept verbatim, and the counterexample's chain satisfies it.
2. **A slowness hypothesis is added.** `N` depends on `D` and `ε`, and `x` must be `N`-slow: values two apart are taken only at indices at least `N` apart. Without some such clause the statement is false (§1).
3. **Surjectivity of `x` is dropped.** The step does not need it. "Every coarse link contains the closure of a fine link" follows from the closure clause once `x` is onto. `theorem4` supplies an onto pattern and uses exactly this (`tchain_meets`).
4. **`diam D'_t < ε` is replaced** by: `D'_t` is bounded, and either `diam D'_t ≤ ε`, or `D'_t` lies in the union of two consecutive coarse links.
   * The second case happens only at the turns of `x`, where the fine chain makes its U-turn inside an overlap zone of the coarse chain.
   * In the iteration this still gives mesh `≤ 4/2^i` at level `i`, because coarse zones are themselves small (`dlink_diam`, `tlink_diam`).
   * The exact clause "mesh `< ε`" is not established for this construction.

The tightness clause is kept exactly as in the skeleton.

Proof outline:
* `std_step` builds, in standard coordinates, a homeomorphism `Ψ` with:
  * `Ψ(closure stdRect t) ⊆ stdRect (x t)`;
  * tightness;
  * small pieces, or containment in a zone;
  * nested end boxes.

  The joint `t` (between fine links `t−1` and `t`) is placed at a horizontal position `P t` (`Joints.lean`):
  * mid-overlap for a transition;
  * for a stay, inside the private part, at a position interpolating between the nearest turns. This is where `N`-slowness gives pieces of width `O(1/N)`.

  `Ψ(u,v) = (βu + h(q), q)` with `q = 1/4 + Cu + (C/8)v` (`Shear.lean`).
* `real_step` moves this through `Φ`, using uniform continuity of `Φ` on the compact region of the coarse chain.
* The final statement turns "inside the zone `k`" into "inside `D_k ∪ D_{k'}`" (`zone_inter_stdRect_subset`).

### 2.2 `theorem4` — proved, conclusion unchanged

```lean
theorem theorem4 {X : Type*} [MetricSpace X] {M : Set X} (hM : IsSnakeLike M) :
    ∃ N : Set Pt, Fold.Q78.IsContinuum N ∧ Nonempty (M ≃ₜ N)
```

This is `theorem4_of` (`T4.lean`), which assumes only that `M` is compact, connected and covered by `ε`-chains for every `ε`.

The construction runs by recursion on the level `i` (`tstage`, stage type `TStage`). Level `i` consists of:
* a minimal covering chain `C_i` of `M`;
* a homeomorphism `Φ_i`;
* the tame chain `D_i = tameChain Φ_i m_i`, with the same number `m_i` of links.

Step `i` (`t4_step`, with `ε = 1/2^i`):
1. `real_step Φ_i` gives the slowness `N` required at this level.
2. `refine_step` (the `C`-side, §3.5) gives a minimal cover `C_{i+1}` of mesh `< 1/2^i`, refining `C_i` along a pattern `x_i` that is onto, has unit steps and is `N`-slow.
3. `real_step` then gives `Ψ`, and `Φ_{i+1} = Ψ ∘ Φ_i`.

Level 0 is a minimal cover of mesh `< 1` together with the standard rectangles.

Bounds:
* links of `C_i` are bounded, with diameter `< 8/2^i`;
* links of `D_i` have diameter `≤ 4/2^i`;
* zones of level `i` have diameter `≤ 2/2^i`.

Theorem 11 (`MatchingCovers.exists_homeomorph`) is applied with `ε_i = 8/2^i`, which is summable and positive, `M₁ = M` and `M₂ = N := ⋂_i D_i^*` (`tN`). The conditions are checked as follows:
* **(1) covers.** `M` is covered by minimality. `N` is covered by definition.
* **(2) meets.** Every link of `C_i` meets `M`: `MinCover.meets`. Every link of `D_i` meets `N`: `link_inter_iInter_union_nonempty`. It uses nested compact closures, and needs `x_i` onto so that every link contains the closure of a link of the next level.
* **(3) diameters and boundedness.** From the bounds above.
* **(4) matching.** `Chain.pattern_matching` in both directions, with strict bounds `< 8/2^i`.

`N` is compact (`isCompact_iInter_union`): `⋂ D_i^* = ⋂ ⋃_t closure (D_i)_t`. `N` is connected as the image of `M` under the homeomorphism.

### 2.3 `exists_description_plane` — proved, conclusion unchanged

This is `exists_description_plane'` (`Descr.lean`), built with `DStage`, `desc_step`, `dstage` and `planeDescription`:
* **Level 0** is the standard chain of three rectangles.
* **Level `i+1`** is `real_step` applied along the *stuttered* Bing pattern `u ↦ bingF (m_i − 1) (u / K_i)` (`stutPat`), where `K_i` is the slowness required at level `i`. So `m_{i+1} = K_i · z (m_i − 1)`.
* **Crookedness** follows from tightness by `crooked_of_tight_pat` (batch 82's `crooked_of_tight`, for an arbitrary crooked pattern with unit steps) and `stut_crooked` (stuttering keeps `bingF` crooked).
* **End points.** `P ∈ ⋂ Φ_i(boxA)` and `Q ∈ ⋂ Φ_i(boxB m_i)`. The boxes nest because the first two and the last two values of a stuttered pattern agree. The boxes lie in the private parts of the first and last links, which gives `Chain.IsFrom`.
* **`P ≠ Q`** holds at level 0.
* **Mesh** is `≤ 4/2^i`.

Change from §3.4 of the commission: `bingPattern` itself is not slow, so it is stuttered, with each value repeated `K_i` times.

### 2.4 `pseudoArc_exists` — proved, conclusion unchanged

Take the description `Δ` from §2.3. All links of `Δ` lie in the compact set `closure (Δ.D 0)^*` (`Description.links_subset_compact`: the links of level 0 are bounded, and `ℝ²` is proper). Then:
* **Continuum.** `Description.isContinuum_M_of` (`Transfer.lean`). It restricts `Δ` to that compact subspace, where the repository's `isContinuum_M` applies (it assumes a compact ambient space), and pulls the result back.
* **Nontrivial.** `P, Q ∈ Δ.M` and `P ≠ Q`.
* **Hereditarily indecomposable.** `Description.theorem10 Δ`, which needs no compactness.
* **Homogeneous.** `Description.theorem13_of`: Theorem 13 in the compact restriction, carried to `Δ.M` by the identity homeomorphism between the two copies of `M`.

## 3. The commission's §3, claim by claim

### 3.1 The planar construction is the whole content

Agreed, and it is by far the largest part of the work (`Joints`, `Shear`, `StdStep`, `RealStep`). The skeleton's formulation of the step is false (§1). The picture in §3.1 is what is built: fine links laid along a path, crossing through overlaps at transitions, U-turning at turns. It is built in standard coordinates and transported by `Φ`.

**The tightness clause costs nothing, as claimed.** It is proved with the statement unchanged, and it is what makes each level crooked in §2.3.

Rectangles: the fine links are homeomorphic images of rectangles under explicit piecewise-linear maps, not rectangles. Bing's "interiors of rectangles" is therefore not reproduced literally. Nothing in Theorem 4 or in the description depends on it.

The metric is the sup metric on `ℝ × ℝ`, as in the skeleton.

### 3.2 Room

`HasRoom` is replaced as the invariant by tameness (`IsTame`). In standard coordinates the private parts, overlap zones and end boxes are explicit, and every chain produced is again tame. `HasRoom`/`IsRectChain` are kept verbatim and appear only in the counterexample.

### 3.3 Bing's "nine links" — **yes, a quantitative clause is needed**

The construction needs a slowness clause, and without one the step is false (§1). It is added to `exists_rect_chain_following` as `N`-slowness, where `N` depends on the coarse chain and on `ε`: `std_step` takes `N = max 12 ⌈1/η⌉` for the modulus `η` coming from uniform continuity of `Φ`.

It is arranged on the `C`-side inside `refine_step`:
1. Let `δ` be a Lebesgue number of the cover of `M` by the links of `C_i`.
2. Take `C_{i+1}` minimal, of mesh `< δ/(N+2)`.
3. Then any `N + 1` consecutive links of `C_{i+1}` lie in one `δ`-ball about a point of `M`, hence in one link of `C_i`.
4. So their pattern values differ by at most one, which is `N`-slowness.

This is Bing's clause, with `N` in place of 9. It is achieved by taking the next chain finer, rather than by passing to a deeper level as `eventually_thick` does.

Not determined: whether Bing's constant 9 suffices for a construction with mesh tending to 0. This construction lets `N` grow with the level.

### 3.4 The pseudo-arc in the plane

Done as described, with two changes:
* **Stuttered Bing patterns** are used (§2.3), because `bingPattern` is not slow.
* **End points come from nested closed boxes** in the private parts of the first and last links. This is the clause of the step for `x 0 = x 1 = 0` and `x (n−1) = x (n−2) = m − 1`, as §3.4 anticipates.

The mesh is `4/2^i`, not `1/2^{i+1}`; the description only needs `ε_i → 0`.

**Transfer from compact spaces.** The repository's `isContinuum_M` and `theorem13` assume a compact ambient space. The restriction in `Transfer.lean` removes this for descriptions whose links lie in a compact set, which every description in `ℝ²` satisfies.

### 3.5 Theorem 4 and minimal covering subchains

`MinCover C M` (`CSide.lean`) means: `M ⊆ C^*`, and for every `k`, neither the links before `k` nor the links after `k` cover `M`. This is equivalent to "no proper subchain covers", since a proper subchain lies before some `k` or after some `k`.

* **`exists_minCover`.** Every chain covering a nonempty `M` contains a minimal covering subchain `C(a,b)`, taken of least length (`Nat.find`). Its links are links of the original chain, so refinement and mesh are kept.
* **`MinCover.meets`.** Every link of a minimal cover meets a connected `M`, by the argument of §3.5: split into the links before and after `j`, two disjoint open sets. The end-link case is covered because one side is then empty.
* **`surj_of_minCover`.** The refinement pattern into a minimal cover is onto: a pattern with unit steps that misses `k` stays on one side of `k`, contradicting minimality.
* **`refine_step`.** Refinement by a Lebesgue number, as in §3.5, with the slowness of §3.3 added.

The `D`-side and Theorem 11 are as in §3.5 of the commission, with these differences:
* `ε_i = 8/2^i`;
* the plane chains are tame chains;
* the level-`i` step on the `D`-side is taken with `ε = 1/2^i`.

**(2) meets** on the `D`-side uses nested compact closures (`link_inter_iInter_union_nonempty`), the same argument as `Description.link_inter_M_nonempty`. It needs the pattern to be onto.

### 3.6 Implicit hypotheses

* **Compactness.** `IsSnakeLike` includes `IsContinuum`, hence compactness. The ambient metric space `X` is arbitrary; it is not assumed compact.
* **Nonemptiness** comes from `IsConnected`. It is used to get at least one link at every level (`TStage.hm`).
* No further hypotheses were needed.

## 4. Not attempted

`covering_step`, `theorem14`, `theorem3_end` (parked, unchanged).
