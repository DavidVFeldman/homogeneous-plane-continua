Commission read: `COMMISSION-batch91.md` (batch 91 — Bing's windows restored (Pacific Theorem 3), and a reconnaissance on Duke 1951 Theorem 10), with its skeleton `Recon91.lean` (saved as `HPC/Plane/Recon91.lean`; `import HPC.Plane.Recon91` added at the end of `HPC.lean`).

# Report, batch 91

## Summary

* **Refutations: none.** Q1 is **proved**, not refuted. The `sin(1/x)` candidate fails (§2, Q1).
* **Item 1** (`theorem3_HIC_windows`): **proved**, in the skeleton's form. It is derived from a
  sharper statement, `theorem3_HIC_bing`, which names Bing's sequence `n_i` and his windows
  exactly.
* **Item 2**:
  * Q1 (`exists_proper_meeting_all_links`) is **proved**.
  * Q2 does not arise, because Q1 is not refuted.
  * Q3 is **open**. Bing's surgery itself is now **proved in Lean**, under weaker hypotheses than
    his text (`theorem10_1951_of_lastLink`). This reduces Theorem 10 to one precisely stated
    claim.
  * Q4: the strongest proved forms are the surgery reduction and Theorem 10 for end points
    (`theorem10_1951_of_endPoint`). Once Q1 holds, the skeleton's `theorem10_1951_of_step` is
    *equivalent* to Theorem 10, so it was not kept as a theorem.
* **Item 3**: the note has been added to the head of `HPC/Plane/Monotone51Comb.lean`.
* `lake build HPC` passes. The new files (`Recon91.lean`, `Windows91.lean`, `Composant91.lean`,
  `Surgery91.lean`, all in `HPC/Plane/`) contain no `sorry`. The `sorry` warnings in the build are
  the parked ones: `theorem3_end`, `covering_step`, `theorem14` (1948), `theorem10_1951` and
  `exists_tame_chain_near`.
* Axioms (`Axioms91.lean` → `axioms-batch91.txt`): every new result uses only `propext`,
  `Classical.choice` and `Quot.sound`. `theorem10_1951` and `endPoint_of_condA` still show
  `sorryAx`; they are unchanged.

**Shape changes.**
* `exists_proper_meeting_all_links`: the hypothesis `hD : M ⊆ D.union` was not used and has been
  removed.
* `theorem10_1951_of_step`: kept only as a comment, since once Q1 holds it says the same as
  `theorem10_1951` (see Q4).
* `theorem3_HIC_windows`: unchanged.
* `theorem10_1951` (`EndPoints51.lean`): not edited.

## 1. Refutations

None.

## 2. Item 1 — Bing's windows

**What is proved.** `Mono.exists_bing_windows` (`HPC/Plane/Windows91.lean`) is the abstract
combinatorial core. `theorem3_HIC_bing` (`HPC/Plane/Recon91.lean`) is the theorem. Indices start
from `0`, so Bing's `n_1` is `bingSeq 0 = 0` and his `D(n_{3k+1}, n_{3k+5})` is our
`D(n_{3k}, n_{3k+4})`.

* `bingNext R m i` is Bing's step. It is the largest `j` such that some fibre meets both `c(i)`
  and `c(j)`. `bingSeq` iterates it starting from `0`.
* The chain `C` covers `M`, and every link of `C` meets `M`.
* `J` is the first index with `n_J = m − 1`, and `K = ⌊(J − 2)/3⌋`.
* The windows are `D(n_{3k}, n_{3k+4})` for `k < K`, and the last one is `D(n_{3K}, n_J)`.
* These windows are exactly the traces on `M'` of the links of an `ε`-chain of `Y` that covers
  `M'`.
* `theorem3_HIC_windows`, the skeleton's statement, follows from this.

**The last window.** The commission's rule for the last window, `j − 5 ≤ 3k + 1 < j − 3`
(1-indexed), admits no `k` when `j ≡ 1 (mod 3)`. For example, with `j = 7` it asks for
`3k + 1 ∈ {2, 3}`. We take `K = ⌊(J − 2)/3⌋` instead.
* The last window then spans 2 to 4 of Bing's blocks.
* When `J ≤ 4` (that is, `j ≤ 5`) there is a single window, `D(n_1, n_j)`, which is all of `M'`.
  This is Bing's case `j ≤ 4`, together with `j = 5`, where his only window is also all of `M'`.

**The six properties, and what each needed.**
1. *`n_i` strictly increasing* (until `m − 1`, then constant). This is observation 1.
   * It needs a point **of `M`** in `c(i) ∩ c(i+1)`.
   * That point exists because `M` is connected: `M` is covered by the two open sets
     `c(0) ∪ ⋯ ∪ c(i)` and `c(i+1) ∪ ⋯`, it meets both, and they intersect only inside
     `c(i) ∩ c(i+1)`.
   * The text leaves this to the reader. The rest is the definition.
2. *Each window is nonempty and open.*
   * **Open**: the complement of `D(a, b)` is the image of the compact set `M ∖ (c(a) ∪ ⋯ ∪ c(b))`,
     as in batch 89.
   * **Nonempty**: take a fibre realising `n_{p+2}` from link `n_{p+1}`. It cannot meet `c(n_p)`,
     since otherwise `n_{p+2} ≤ n_{p+1}`. So it lies in `D(n_p, n_{p+2})`. This is the definition
     of `n_i` together with the interval property (Nadler 12.12).
   * Nonemptiness needs windows spanning at least two blocks, which explains the choice of the
     last window.
3. *Non-adjacent windows are disjoint.* Windows `k` and `k + 2` are separated by
   `n_{3k+6} ≥ n_{3k+4} + 2` (strict increase), and then link adjacency applies. Nothing beyond
   observation 1 is needed.
4. *The windows cover `M'`.* A fibre whose first link lies in `[n_l, n_{l+1})` ends by
   `n_{l+2}`: if it reaches `n_{l+1}` it meets that link, so it ends by `n_{l+2}`. So it lies in
   window `min(⌊l/3⌋, K)`. This is the definition plus the interval property.
5. *Consecutive windows meet.* This is observation 2, the connectedness of `M'`. It is proved
   exactly as the commission states it: the unions of windows `≤ k` and `≥ k + 1` would separate
   `M'`.
6. *Mesh.* Let `z_l` be a fibre realising `n_{l+1}` from link `n_l`.
   * Consecutive `z_l` both meet `c(n_{l+1})`, so they are within `η`.
   * A fibre in window `k` meets a link between `n_l` and `n_{l+1}` for some `l` in
     `[3k, 3k + 3]`, so it is within `η` of `z_l`.
   * Hence the window diameter is `≤ 5η`. This needed a short argument of its own.
   * With `η = ε/8`, the extension of the windows to open sets of `Y` (batch 88's `liftChain`,
     which adds `2η`) gives mesh `< ε`.
   * The proof uses `ε/8` instead of Bing's `ε/5` to leave room for that extension.
   * Bing's `4ε/5` is not reproduced. The bound proved for the windows is `5η`.

Hence properties 1, 2 and 4 needed the interval property (a connected set meeting two links meets
every link between them). Property 6 needed the chain of fibres `z_l`. Properties 3 and 5 needed
only the two observations.

## 3. Item 2 — Theorem 10

### Q1 — `exists_proper_meeting_all_links`: **proved**

Proof (`HPC/Plane/Composant91.lean`):
* `exists_subcontinuum_meeting_closedBall` (**boundary bumping**). The component of `p` in the
  compact set `M ∖ B(x, s)` meets `B̄(x, s)`.
  * In the compact space `M ∖ B(x, s)`, the component is the intersection of the clopen sets
    containing it (`connectedComponent_eq_iInter_isClopen`).
  * By compactness, one of these clopen sets misses the points adherent to `M ∩ B(x, s)`.
  * The clopen form of boundary bumping (batch 81, `T13.clopen_meets_closure_diff`) rules this out.
* `exists_proper_subcontinuum_meeting` (**the composant of `p` is dense**). Every open set meeting
  a nondegenerate continuum `M` meets a proper subcontinuum of `M` through `p`.
* `exists_proper_meeting_all_links_of_condB`. Condition B makes the subcontinua through `p`
  nested, so the largest of the finitely many subcontinua (one meeting each link) meets every
  link. Condition B follows from condition A (`condB_of_condA`, batch 85).

**Why the `sin(1/x)` candidate fails.** The links of `D` are open in the ambient space, and every
point of the limit bar is a limit of points of the curve. So a link cannot meet `M` only inside
the bar. Each link meets the curve at some point `(x_i, sin(1/x_i))`. The arc of the curve from `p`
to the point with `x = min x_i` is a proper subcontinuum through `p` that meets every link. The
commission's other claims about this continuum (condition A at `p`, irreducibility from `p` to bar
points) were not needed and were not checked in Lean.

### Q2 — does not arise

Q1 is not refuted. Informally, Theorem 10 also holds for the `sin(1/x)` continuum and its free end
`p`: that continuum is chainable and `p` is an end point, so `theorem10_1951_of_endPoint` applies.
That `p` is an end point was **not** formalized, so this is not a verified claim.

### Q3 — the "fewer links" sentence: **open**, with the surgery now proved

**Proved** (`HPC/Plane/Surgery91.lean`, `theorem10_1951_of_lastLink` and its mirror
`theorem10_1951_of_lastLink'`). Bing's surgery, under hypotheses weaker than his:
* Let `p` satisfy condition B in the continuum `M`, and let `D` cover `M`.
* Suppose some subcontinuum `M'' ∋ p` of `M` (not necessarily proper, and not necessarily meeting
  every link) has a chain `F` with the properties of Theorem 10 for `M''`.
* Suppose the last link `f_k` of `F` contains a point `y ≠ p` of `M''` lying in `d_1` (or in
  `d_m`).
* Then Theorem 10 holds for `M`.

Compared with Bing's construction:
* `y` may lie in `cl f_{k−1}` and in `cl d_2`. The last link of `F` is merged with the cut `N`
  (a small ball about `y`), and `cl N` is removed from `d_2, d_3, …` in the `D`-part. These links
  stay covered because `cl N ⊆ d_1`.
* The component of `p` in `M ∖ N` lies in `M''`, by condition B, because `M''` meets `N`.
* `exists_clopen_split` gives the clopen piece `H` inside `F.union`. This is the compactness
  argument of batch 85, now in Lean.
* Disjoint thickenings `U ⊇ H` and `V ⊇ M ∖ (N ∪ H)` with `p ∉ cl V` separate the two parts.
* The resulting weak chain `F ∩ U, …, (f_k ∩ U) ∪ N, d_1 ∩ V, (d_2 ∩ V) ∖ cl N, …` is trimmed by
  `exists_chain_of_weak`.

**So Theorem 10 follows from the following claim**, which is what is missing: *for a continuum
`M`, a point `p` satisfying condition A and a chain `D` covering `M`, some subcontinuum `M'' ∋ p`
has a Theorem-10 chain `F` whose last link meets `M'' ∩ (d_1 ∪ d_m)` at a point other than `p`.*
The converse was not examined: a chain given by Theorem 10 for `M` need not have its last link in
`d_1 ∪ d_m`.

Neither Bing's minimal counterexample nor the existence of `M''` (Q1) is needed for the surgery.
They would be needed only to *produce* such an `F`.

**On the alternative minimality.** Take the least number of links among Theorem-10 chains of `M''`
whose last link meets `M'' ∩ (d_1 ∪ d_m)`. This family is nonempty exactly when the claim above
holds for `M''`, so the alternative minimality restates the gap and does not close it.

One informal observation, not proved in Lean: the links met by a connected set through `p` form an
interval of indices. So, as subcontinua through `p` grow, the last link they reach is `d_1` or
`d_m`. This suggests taking `M''` to be the smallest subcontinuum through `p` meeting every link
(closed links). It does not by itself control the last link of an arbitrary chain `F` for that
`M''`.

### Q4 — strongest form established

* **Theorem 10 as stated**: open (`theorem10_1951` keeps its `sorry`).
* **Theorem 10 with the step as a hypothesis**: once Q1 holds, this is *equivalent* to Theorem 10.
  For nondegenerate `M`, after trimming `D` to the links meeting `M` (batch 85), Q1 supplies the
  hypothesis; a degenerate `M = {p}` is covered by one link. This equivalence is argued here, not
  formalized. So it is not a weaker form, and it is kept only as a comment in `Recon91.lean`.
* **Theorem 10 from the last-link claim** (`theorem10_1951_of_lastLink`, `…'`): proved, with only
  condition B. This is the strongest conditional form reached.
* **Theorem 10 for hereditarily decomposable `M`**: not reached.
* **Theorem 10 for end points** (`theorem10_1951_of_endPoint`): proved.
  * Take a fine end-point chain whose mesh is below a Lebesgue number of `D`; it refines `D`.
  * Remove a small closed ball about `p` from every link but the first.
  * Trim the result to the links meeting `M`.

`endPoint_of_condA` (batch 85) still depends on `theorem10_1951` alone, and so on its `sorry`.
None of the new results changes that. The end-point form cannot serve Theorem 13, since it assumes
the conclusion.

## 4. Item 3 — the ledger

A note has been appended to the module docstring of `HPC/Plane/Monotone51Comb.lean`. It says that
Bing's windows are valid (`Mono.exists_bing_windows`, `theorem3_HIC_bing`) and that the block
boundaries of batch 89 are an alternative, not a repair. No other existing file was edited, apart
from the import line in `HPC.lean` prescribed by the commission.

## 5. Not attempted

`covering_step`, `theorem14` (1948), `theorem3_end` and `exists_tame_chain_near`, as instructed.
