Commission read: `COMMISSION-batch89.md` (batch 89 — Bing, *Concerning hereditarily indecomposable continua*, Pacific J. Math. 1 (1951), §4: monotone decompositions, Theorems 3 and 4).

# Report, batch 89

The skeleton `Monotone51.lean` is saved as `HPC/Plane/Monotone51.lean`, and
`import HPC.Plane.Monotone51` is the last line of `HPC.lean`. One new supporting file:

| file | contents |
| --- | --- |
| `HPC/Plane/Monotone51Comb.lean` | `Mono.exists_chain_of_intervals`: the combinatorial core of Theorem 3 (Bing's windows, abstractly) |
| `HPC/Plane/Monotone51.lean` | the skeleton's definition and four statements, all proved; helper lemmas `Mono.image_inter_preimage`, `Mono.isConnected_inter_preimage`, `Mono.isContinuum_inter_preimage` |

Neither file contains `sorry`. `Axioms89.lean` prints the axioms (output in
`axioms-batch89.txt`): every statement uses only `propext`, `Classical.choice`, `Quot.sound`.
Nothing in this batch depends on the old parked `sorry`s (`covering_step`, `theorem3_end`,
`theorem10_1951`, …), which were not attempted.

## 0. Counterexamples

None. All five skeleton items are proved **exactly as stated**. No shapes were changed. The only
departure from the skeleton is in the module docstring, which now describes the delivery.

## 1. Targets

1. **`IsMonotoneMap`**: kept verbatim.
2. **`theorem3_HIC`** (Theorem 3), proved as stated. `IsSnakeLike M` supplies compactness of
   `M`. Nothing is assumed of `M'` beyond being a subset of a metric space.
   * `M'` is a compact continuum: it is the image of `M`.
   * Given `ε`, put `η = ε/9`. Uniform continuity of `f` on the compact `M` gives `δ`. Take a
     `δ/2`-chain `C` covering `M`, every link meeting `M` (`exists_cover_meeting`, batch 85).
   * For `y ∈ M'` let `R y i` mean that link `i` meets the fibre `F y = M ∩ f⁻¹{y}`. Let
     `G p q = {y : F y ⊆ c(p) ∪ ⋯ ∪ c(q)}`, Bing's `D(p, q)`, as a subset of the subspace `M'`.
   * The hypotheses of the combinatorial lemma are checked:
     - each `F y` meets an interval of links (`Chain.meet_ordConnected`, batch 86);
     - fibres meeting the same or adjacent links have images within `η`;
     - `G p q` is open, being the complement of the compact image `f '' (M ∖ U)` (§3 item 2);
     - two `G`s whose index ranges are at least two apart are disjoint.
   * `Mono.exists_chain_of_intervals` then gives a chain of the space `M'` covering it, of mesh at
     most `6η`.
   * `PA51.liftChain` (batch 88) lifts it to a chain of `Y` with radius `η`. That chain still
     covers `M'`, and its mesh is at most `6η + 2η = 8ε/9 < ε`.
3. **`isHereditarilyIndecomposable_image`**, proved as stated (§3 item 5 below). Let `K'` be a
   subcontinuum of `M'`.
   * Its preimage `K = M ∩ f⁻¹K'` is a continuum (`Mono.isContinuum_inter_preimage`). So are the
     preimages of `A'` and `B'`, and these two cover `K`.
   * `K` is indecomposable, so one of them is all of `K`.
   * Apply `f ''`. Since `f '' (M ∩ f⁻¹S) = S` for `S ⊆ M'` (`Mono.image_inter_preimage`), `A' = K'`
     or `B' = K'`.
4. **`isContinuum_image`**, proved as stated: the image of a compact connected set under a map
   continuous on it is compact and connected.
5. **`theorem4_HIC`** (Theorem 4), proved as stated. These pieces give `IsPseudoArc M'`, and
   `theorem1_HIC'` (batch 88) gives `M ≃ₜ M'`:
   * chainable: `theorem3_HIC`;
   * hereditarily indecomposable: item 3;
   * nondegenerate: if `M'` were a single point `y`, the fibre over `y` would be all of `M`,
     against `hproper`.

## 2. §3 item 4: Bing's windows, replaced

**The gap in Bing's text.** I could not supply a reason why consecutive windows
`D(n_{3k+1}, n_{3k+5})` and `D(n_{3k+4}, n_{3k+8})` meet. Knowing which links each fibre meets
does not by itself imply it. The following check was done by hand and is not in Lean.
* Abstract the data to: each fibre carries an interval of link indices; the intervals cover every
  index; the `n_i` are defined from the intervals as Bing does.
* Take the intervals `[2m, 2m+3]` for `m ≥ 0`. Then `n_i = 2i − 1`. The overlap
  `[n_{3k+4}, n_{3k+5}] = [6k+7, 6k+9]` has only three indices, so no interval of four indices
  fits inside it.
* So with these intervals no fibre is shown to lie in Bing's overlap. (Whether a fibre is
  *covered* by `c(6k+7) ∪ ⋯ ∪ c(6k+9)` also depends on where its points in `c(6k+6)` lie, which the
  interval data do not record.) This does not refute Theorem 3:
  I have not checked whether such intervals can come from an actual monotone map of a chainable
  continuum. In an arc they cannot, because there are fibres between any two disjoint
  nondegenerate fibres. It only shows that Bing's argument needs more than it says.
* The construction below avoids the question.

**The replacement** (`HPC/Plane/Monotone51Comb.lean`). For a fibre `y`, let `a y` and `b y` be the
first and last indices of the links it meets.
* *Step function.* `s i` is the largest `b y` over fibres with `a y ≤ i`. It is monotone, and
  `i ≤ s i` for `i < n`.
* *Block boundaries.* `N 0 = 0` and `N (k+1) = max (s (N k), N k) + 1`. The `+ 1` is absent from
  Bing. Without it his `n_{i+1} = n_i` is possible (all fibres meeting `c(n_i)` end at `n_i`), and
  his sequence stalls. With it the boundaries increase strictly.
* *Block `k`* is the set of indices `[N k, N (k+1) − 1]`. Two facts drive everything:
  - (B1) Some fibre `z k` has `a (z k) ≤ N k` and `b (z k) = s (N k) = N (k+1) − 1`, so its
    interval contains the whole block `k`. For `k ≥ 1` also `a (z k) ≥ N (k−1)`: otherwise
    `b (z k) ≤ s (N (k−1)) < N k`. So `z k` lies in blocks `k − 1` and `k`.
  - (B2) A fibre with `a y` in block `k` has `b y ≤ s (N (k+1)) < N (k+2)`, so it lies in blocks
    `k` and `k + 1`.
* *Windows.* Window `j` is `G (N (3j)) (N (3j+5) − 1)`: five blocks, starting every three blocks.
  This is Bing's `D(n_{3k+1}, n_{3k+5})` widened by one step. Consecutive windows now overlap on
  two blocks, that is, on three consecutive boundaries `N (3j+3)`, `N (3j+4)`, `N (3j+5)`. This is
  the first option suggested in the commission.
* *Number of windows.* `J` is the least `j ≥ 1` with `n ≤ N (3j+2)`, so the last window runs to
  the end of the chain.

The chain conditions:
* **Consecutive windows meet.** By (B1), `z (3j+4)` lies in blocks `3j+3` and `3j+4`, which is
  inside both windows `j` and `j + 1`. This needs `N (3j+4) < n`, which follows from the
  minimality of `J`.
* **Non-consecutive windows are disjoint.** Window `j` ends at index `N (3j+5) − 1`, and window
  `j + 2` starts at `N (3j+6) ≥ N (3j+5) + 1`. A point of a fibre lying in both would be in two
  links whose indices differ by at least 2.
* **Covering.** By (B2), a fibre starting in block `k` lies in blocks `k` and `k + 1`. Both are
  inside window `⌊k/3⌋`, or inside the last window if `⌊k/3⌋ ≥ J`.
* **Mesh: Bing's count, plus one.** A fibre `y` in window `j` meets some link of a block `k` of
  the window (`3j ≤ k ≤ 3j+4`), so `dist y (z k) < η`. Consecutive `z k` and `z (k+1)` meet the
  adjacent links `N (k+1) − 1` and `N (k+1)`, so `dist (z k) (z (k+1)) < η`. Two fibres in one
  window are therefore within `η + 4η + η = 6η`. Bing's windows span four `n`-steps and give his
  `5 · ε/5`. Ours span five blocks and give `6η`, and `η = ε/9` absorbs the further `2η` of the
  lift to `Y`.

## 3. §3 item 5: why the preimage of a connected set is connected

`Mono.isConnected_inter_preimage` uses a direct argument with closed sets; it does not go through
Mathlib's quotient maps. The setting:
* `M ⊆ X` is compact, and `f` is continuous on `M` with connected fibres.
* `K' ⊆ M'` is connected, and need not be closed.
* `K = M ∩ f⁻¹K'`. It is nonempty because `K' ⊆ f '' M`.

For preconnectedness, use `isPreconnected_closed_iff`. Let `u`, `v` be closed sets of `X` covering
`K`, each meeting `K`.
* The images `f '' (M ∩ u)` and `f '' (M ∩ v)` are compact, hence closed in `Y`.
* They cover `K'` and both meet it. So, `K'` being preconnected, some `y ∈ K'` lies in both.
* The fibre `M ∩ f⁻¹{y}` is connected and lies in `K ⊆ u ∪ v`. It meets `u` and `v` (at the
  preimage points just found), hence meets `u ∩ v`, which gives a point of `K ∩ u ∩ v`.

This is the closed-map argument of the commission, with the closedness of `f` used only through
the compact images `f '' (M ∩ u)`. `Mono.isContinuum_inter_preimage` adds that for closed `K'` the
preimage is compact, being a closed subset of `M`.

## 4. Not attempted

`covering_step`, `theorem14` (1948), `theorem3_end`, `theorem10_1951`, as instructed.
