# Commission: batch 202 — Part G, V: a plane circle of pseudo-arcs

**Go!** This batch runs on top of the batch-201 work. Two files come with it, as separate uploads:

* `COMMISSION-batch202.md`: this text, also pasted into the prompt.
* `BJ59E.lean`: the skeleton.
  * Save it as `HPC/BJ59/BJ59E.lean`. You may split it under `HPC/BJ59/`.
  * Add `import HPC.BJ59.BJ59E` at the end of `HPC.lean`. Adjust the skeleton's imports as needed.
  * Save copies under `doc/batches/` (`COMMISSION-batch202.md`, `skeletons/BJ59E.lean`) and
    include them in the tarball, as in batch 201.

No new source: Bing–Jones is `doc/sources/bing-jones1959.pdf` (PDF page `n` is journal page
`169 + n`).

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule)**, as before, including the test of every new definition and
  every named `Prop` on degenerate inputs.
* **Quotations (standing rule).** Check every quotation and every reading of a formula against
  page images rendered at 200 dpi or more, and at 400 dpi for subscripts, primes, tildes and bars,
  not against the text layer. The quotations of this batch are from pp. 189–191.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Bing–Jones 1959, V (batch 202)");
  * `README.md`;
  * `LEDGER.md`: a new section "Bing–Jones §7, the plane example (batch 202)";
  * `OPEN.md`;
  * `doc/notes/bj59.md` (append).

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 201

* **Delivery.** The download was current (`axioms.txt` 3776 lines, equal to the tarball's). The
  download's `HPC/` still lacks the 64 Lean files listed in commission 201 §0, but your tarball
  carries current copies of every file under `HPC/Hagopian/`, `HPC/Jones/` and `HPC/Span/`, and
  overlaying them changes nothing. Please keep doing that.
* **Audit.** 66 new theorems (63 on the three standard axioms, 2 on `propext` and `Quot.sound`, 1
  on `propext`); `sorryAx` in none; the thirteen new files contain no `sorry`, `admit` or `axiom`.
  20 of the 21 declarations of the skeleton are textually the skeleton's; `exists_pattern` is
  stronger, and `exists_pattern_skeleton` gives the skeleton's form. Accepted.
* **Results.** Everything: `bjThm10 : BJThm10`, and with it the classification with
  Domokos–Prajs's third class with no named hypothesis. Thank you.
* **Ledger.** BJ.30–BJ.40 adopted. I agree with counting none of them; the counts stay at 24
  false printed statements and 18 defective proofs.
* **Omission noted.** The non-degenerate witnesses for `BJStep`, `BJThm10` and the window lemmas
  waited for a continuous snake-like arc of pseudo-arcs. This batch produces one (§8).

## 1. The plan

What is left of the classification is `BJPlaneExample : ∃ C : Set Pt, IsCircleOfPA C`. With it,
`ho16_classification₃` and `ho16_classification_plane₃` hold with no named hypothesis.

Bing–Jones §7 does not construct the example. P. 189, 400 dpi:

> "7. **A circle of pseudo-arcs.** It follows from Theorem 10 that each circle of pseudo-arcs is
> homogeneous and that any two of them are homeomorphic. In this section we show that the plane
> contains a circle of pseudo-arcs."

P. 190 introduces the arcs `V_i` (vertex `b_i`, end points `a_i`, `c_i`) and states: "Now there
exists a sequence D₁, D₂, D₃, ⋯ of circular chains of simple domains in the plane such that"
(1)–(9) hold. P. 191 ends the paper:

> "Now let M=∏D_i^* and let G denote the set of all subcontinua of M which are irreducible from
> W₁ to W₂. The reader will observe that if (9) were omitted the construction of the chains D_i
> could be carried out in such a way that each element of G would be an arc if its intersection
> with W₁+W₂ were two points and indecomposable if this intersection were three points. Also, in
> this case M would be a continuous circle-like circle of continua. With the addition of (9) one
> may see with the help of [3] that each element of G is a pseudo-arc. It follows from Theorem 10
> that M is homogeneous."

The chains `D_i` are not constructed, and three things are not argued: that the elements of `G`
are disjoint and fill `M`, that `G` is a continuous decomposition with a circle as quotient, and
that each element of `G` is a pseudo-arc. On the last: (9) makes each new column `T_ij` crooked in
a pair `T_hk + T_hl` of old columns. As far as I can see, this does not make a run of two new
columns crooked in two old ones, and an element of `G` covered by two adjacent columns at some
level needs exactly that. Two crooked chains joined end to end are not crooked in general.

This batch therefore builds the example by a different construction, of my design. It is not
Bing–Jones's, and the ledger says so (§7). It has four parts.

1. **A recognition theorem** (§3). A *circular description* (§2) is a sequence of circular chains
   `L_k` in a metric space, each refining the last along a *lifted pattern* `π_k : ℤ → ℤ` of
   degree one, with closures nested, tightness and mesh tending to zero. In addition, every link
   carries a closed arc of the base circle `ℝ/ℤ`: link `t` of level `k` carries the arc of length
   `λ_k` centred at `o_k + t/N_k`. The arcs are labels, not geometry. Five conditions on the
   patterns and arcs (nesting of arcs, survival, crookedness of runs, two size conditions) make
   `M = ⋂_k ⋃_t L_k t` a circle of pseudo-arcs. The map onto the circle sends `p` to the
   intersection of the arcs of the links containing `p`. The fibre over `z` is the intersection of
   the *runs* of `z`, the links whose arcs contain `z`. Crookedness of each run in the previous
   one makes fibres hereditarily indecomposable, and survival makes the map open.
2. **Sweep patterns** (§4). Explicit patterns that satisfy the conditions. The new chain sweeps
   back and forth across a window of old links that slides once around the circle. Each sweep is
   a stuttered Bing pattern. Between consecutive window changes there are three sweeps, and the
   window changes one end at a time, at the end where the walk is not. A run of the new chain
   spans at most two window changes, and a combinatorial lemma (the sweep lemma) makes every such
   run crooked.
3. **The circular planar step** (§5). The analogue of batch 84's `real_step` for circular chains
   in an annulus. A covering-space form of the shear: on the universal cover the map
   `(u, v) ↦ (P̂(u) + ε₀ v, 1/2 + C (P̂(u) − u/Q − 2y₀ − 3/2) + C ε₀ v)` is a homeomorphism for
   every continuous `P̂`. It commutes with the deck translations, so it descends to a homeomorphism
   of the plane. Two passes of the new chain over the same place are separated vertically by `C`
   times the drift between them. This replaces the global height of the linear shear, which
   cannot close up around a circle.
4. **Assembly** (§6). Levels built alternately with §4 and §5, starting from the standard
   circular chain of 16 polar rectangles. The result is a circular description in the plane, so
   `BJPlaneExample`, and with it the corollaries of §6.3.

I checked the combinatorics of §4 numerically before writing this (a script over the first two
levels; §4.5). The English proofs below are complete; the planar step (§5) follows batch 84's
construction, and only the changes are spelled out.

## 2. Circular descriptions (skeleton §2)

**Conventions.** Indices of links are integers, read modulo `N_k`. All lifts are explicit: the
centre of link `t` of level `k` is the real number `c_k(t) = o_k + t / N_k`, so
`c_k(t + N_k) = c_k(t) + 1`. Write `δ_k = 1/(2 N_k)`. A run of a real number `z` at level `k` is
`R_k(z) = {t ∈ ℤ : |z − c_k(t)| ≤ λ_k / 2}`, a set of consecutive integers.

`CircDescr X` (skeleton) has the fields below. The names in brackets are the skeleton's.

* (`N`, `four_le`) sizes `N k ≥ 4`.
* (`L`, `isOpen_L`, `periodic`, `meet_iff`, `preconn`) links `L k t ⊆ X`, open, preconnected,
  `L k (t + N k) = L k t`, and `L k s` meets `L k t` iff `s − t` is within 1 of a multiple of
  `N k`.
* (`K`, `isCompact_K`, `L_subset`) a compact set containing every link.
* (`ε`, `ε_tendsto`, `diam_le`) `diam (L k t) ≤ ε k`, `ε k → 0`.
* (`pat`, `pat_period`, `pat_step`) the lifted pattern: `pat k (t + N (k+1)) = pat k t + N k`, and
  steps of size at most 1.
* (`nest`) `closure (L (k+1) t) ⊆ L k (pat k t)`.
* (`tight`) if `L (k+1) t` meets `L k l` then `pat k t' = l + n N k` for some `t'` within 1 of `t`
  and some integer `n`.
* (`o`, `lam`, `lam_tendsto`) offsets and arc lengths, `λ_k → 0`.
* (`five_le_lam`, `lam_add_four_le`) `5 ≤ λ_k N_k` and `λ_k N_k + 4 ≤ N_k`.
* (`arcNest`) `|c_{k+1}(t) − c_k(π_k t)| ≤ (λ_k − λ_{k+1}) / 2` for every integer `t`: the arc of
  a new link lies in the arc of its image, with no shift by an integer.
* (`surv`) **survival**: if `|z − c_k(l)| ≤ λ_k/2 − δ_k`, there is `t` with `π_k t = l` and
  `|z − c_{k+1}(t)| ≤ λ_{k+1}/2 − δ_{k+1}`.
* (`crook`) **crookedness**: for every `k` and every integer `a`, the sequence
  `u ↦ π_k (a + u)` is `PatCrookedOn` on `[0, ⌈λ_{k+1} N_{k+1}⌉ + 3]`.

`CircDescr.M Δ = ⋂ k, ⋃ t, Δ.L k t`.

## 3. The recognition theorem (skeleton §3)

**Theorem (`CircDescr.isCircleOfPA`).** For every circular description `Δ`, `IsCircleOfPA Δ.M`.

The skeleton also names `isCompact_M`, `inter_M_nonempty`, `fib` and `fib_meets`; use or
restate them as convenient. Write `U_k = ⋃_t L_k t` and `π_k = pat k`.

**(3.1) `M` is a continuum.** By `nest`, `closure U_{k+1} ⊆ U_k` (the links of a level are
finitely many up to periodicity, so the closure of the union is the union of the closures).
Hence `M = ⋂_k closure U_k`, a nested intersection of compact sets. `U_k` is connected:
consecutive links meet (`meet_iff`) and links are preconnected, so `L_k 0 ∪ ⋯ ∪ L_k t` is
connected for every `t ≥ 0` by induction, and `U_k` is the union of these increasing connected
sets (periodicity). So each `closure U_k` is a nonempty compact connected set, and so is `M`.

**(3.2) Consecutive links meet in `M` (`inter_M_nonempty`).** Fix `k`, `t`.
* Since `π_k (s + N_{k+1}) = π_k s + N_k` with `N_k > 0`, `π_k` takes values `≤ t` and values
  `≥ t + 1`. With steps of size at most 1, there is `s` with `π_k s = t` and `π_k (s+1) = t + 1`
  (take an index with value `≤ t` and a later one with value `≥ t + 1`, and the last index between
  them with value `≤ t`).
* Repeating at each level gives `t_k = t` and integers `t_j` (`j > k`) with
  `π_j t_{j+1} = t_j` and `π_j (t_{j+1} + 1) = t_j + 1`.
* Put `C_j = closure (L_j t_j) ∩ closure (L_j (t_j + 1))`. It is compact and nonempty
  (`meet_iff`), and by `nest`, `C_{j+1} ⊆ L_j t_j ∩ L_j (t_j + 1) ⊆ C_j`.
* A point `q` of `⋂_j C_j` lies in `L_j t_j ⊆ U_j` for every `j ≥ k` (as `q ∈ C_{j+1}`). For
  `j < k`, `nest` applied downwards puts `q` in `U_j` as well. So `q ∈ M ∩ L_k t ∩ L_k (t+1)`.

**(3.3) The base map.** For `p ∈ M` and `k`, let `A_k(p) ⊆ ℝ/ℤ` be the union of the arcs
`[c_k(t) − λ_k/2, c_k(t) + λ_k/2]` (mod 1) over the links `L_k t ∋ p`.
* `p` lies in at most two links per period, and they are consecutive (`meet_iff`, `N_k ≥ 4`). So
  `A_k(p)` is a nonempty closed arc of length at most `λ_k + 1/N_k`.
* `A_{k+1}(p) ⊆ A_k(p)`: if `p ∈ L_{k+1} t` then `p ∈ L_k (π_k t)` (`nest`) and the arc of `t`
  lies in the arc of `π_k t` (`arcNest`).
* `λ_k → 0`, and `N_k → ∞` because `5 ≤ λ_k N_k`. So `⋂_k A_k(p)` is one point; call it `φ(p)`.

Let `f = h ∘ φ`, with `h : ℝ/ℤ ≃ₜ Circle` the standard homeomorphism.

**(3.4) Fibres.** For `z ∈ ℝ` put `V_k(z) = ⋃_{t ∈ R_k(z) + N_k ℤ} L_k t`. Then
`φ⁻¹(z mod 1) = ⋂_k V_k(z)`, and `V_{k+1}(z) ⊆ V_k(z)`.
* (`⊆`) If `φ(p) = z mod 1`, then `z mod 1 ∈ A_{k+1}(p)`, so some `L_{k+1} t ∋ p` has `z` within
  `λ_{k+1}/2` of `c_{k+1}(t)` after a shift by an integer `n`. Replace `t` by `t − n N_{k+1}`
  (periodicity) to make the shift 0. Then `p ∈ L_k (π_k t)` and, by `arcNest`, `π_k t ∈ R_k(z)`.
* (`⊇`) If `p` lies in a link of `R_k(z)` for every `k`, then `z mod 1 ∈ A_k(p)` for every `k`,
  so `φ(p) = z mod 1`. Every such `p` lies in `M`.
* (decreasing) a link of `R_{k+1}(z)` lies in the link of its image, which is in `R_k(z)`
  (`arcNest`).

**(3.5) Survival (`fib_meets`).** If `|z − c_k(l)| ≤ λ_k/2 − δ_k`, the fibre over `z` meets
`L_k l`.
* By `surv`, repeatedly: `t_k = l` and `t_{j+1}` with `π_j t_{j+1} = t_j` and
  `|z − c_j(t_j)| ≤ λ_j/2 − δ_j` for all `j ≥ k`.
* The compact sets `closure (L_j t_j)` are nested (`nest`) and nonempty. A point `q` of their
  intersection lies in `L_j t_j` with `t_j ∈ R_j(z)` for every `j ≥ k`, so `q ∈ V_j(z)` for
  `j ≥ k`, hence for all `j` (the `V_j(z)` decrease). By (3.4), `φ(q) = z mod 1`, and `q ∈ L_k l`.

Two consequences:
* `φ` is onto: consecutive centres are `1/N_k` apart and `λ_k/2 − δ_k ≥ 1/(2N_k)`, so every `z`
  is within `λ_k/2 − δ_k` of some centre.
* Every fibre is nondegenerate: the `l` with `|z − c_k(l)| ≤ λ_k/2 − δ_k` fill an interval of
  length `λ_k N_k − 1 ≥ 4` (in units of `1/N_k`), so they include `l` and `l + 2`. The fibre meets
  `L_k l` and `L_k (l+2)`, which are disjoint.

**(3.6) `φ` is continuous.** If `p_n → p` and `p ∈ L_k t`, then `p_n ∈ L_k t` for large `n`, and
`φ(p_n)`, `φ(p)` both lie in the union of the arcs of `t − 1`, `t`, `t + 1`, an arc of length
`λ_k + 2/N_k`. Let `k → ∞`.

**(3.7) `φ` is open.** Let `p ∈ M`, `r > 0`, and `k` with `2 ε_k < r`.
* Choose `t` with `p ∈ L_k t` and a lift `z` of `φ(p)` with `|z − c_k(t)| ≤ λ_k/2` ((3.3)).
* The three shrunk arcs `|y − c_k(s)| ≤ λ_k/2 − δ_k`, `s = t − 1, t, t + 1`, cover the interval
  `|y − c_k(t)| ≤ λ_k/2 + 1/(2N_k)`: their centres are `1/N_k` apart and their half-lengths are at
  least `1/(2N_k)`. So every `y` with `|y − z| < 1/(2N_k)` is in one of them.
* For such `y`, (3.5) gives `q` in the fibre over `y` and in `L_k s`, which meets `L_k t ∋ p`.
  So `dist(p, q) ≤ diam L_k s + diam L_k t ≤ 2 ε_k < r`.
* Hence `φ(B(p, r) ∩ M)` contains the image of `(z − 1/(2N_k), z + 1/(2N_k))`.

**(3.8) Runs as chains.** For `z ∈ ℝ`, `R_k(z) = {a, a + 1, …, a + n − 1}` with
`n ≤ λ_k N_k + 1 ≤ N_k − 3`. The links `L_k (a + i)`, `i < n`, form a `Chain X n`: links meet iff
their indices differ by at most 1 (`meet_iff`; `n ≤ N_k − 2` rules out the other multiples of
`N_k`). In `↥M`, the traces `L_k (a + i) ∩ M` form a `Chain ↥M n`: consecutive traces meet by
(3.2), every trace is nonempty by (3.5), and disjointness passes to traces.

**(3.9) Runs are crooked.** Let `E` be the run chain of `R_{k+1}(z) = {a, …, a + n_E − 1}` and
`D` that of `R_k(z) = {b, …, b + n_D − 1}`. Then `E.IsCrookedIn' D`.
* `π_k` maps `a, …, a + n_E − 1` into `b, …, b + n_D − 1` (`arcNest`, with no integer shift),
  and `L_{k+1} t ⊆ L_k (π_k t)`. So `E` refines `D`.
* Tightness inside the runs: if `L_{k+1} t` (`t` in the run) meets `L_k l` (`l` in the run),
  `tight` gives `t'` within 1 of `t` and an integer `n` with `π_k t' = l + n N_k`. As
  `|π_k t' − π_k t| ≤ 1` and `l`, `π_k t` both lie in a run of length `≤ N_k − 3`, `n = 0`.
* `crook` with `a − 1` in place of `a` makes `π_k` crooked on `[a − 1, a + n_E]`, as
  `n_E + 1 ≤ ⌈λ_{k+1} N_{k+1}⌉ + 2`.
* Now argue as in `crooked_of_tight_pat` (batch 84), with the window enlarged by one index at
  each end. Given links `i`, `j` of `E` meeting links `α`, `β` of `D` with `α + 2 < β`, tightness
  gives `u'`, `v'` within 1 of `i`, `j` with `π_k u' = α` and `π_k v' = β`. Crookedness gives `r`,
  `s` strictly between `u'` and `v'`, in the right order, with `π_k r = β − 1` and
  `π_k s = α + 1`.
  * `π_k r = β − 1 > α + 1 ≥ π_k i`, so `r ≠ i`; `π_k s = α + 1 < β − 1 ≤ π_k j`, so `s ≠ j`
    (as `hri`, `hsj` in `crooked_of_tight_pat`).
  * With `|u' − i|, |v' − j| ≤ 1`, strictness then gives `r`, `s` strictly between `i` and `j`,
    so they lie in the run.

  Write a lemma `crooked_of_tight_pat'` for this enlarged form.

**(3.10) Fibres are pseudo-arcs.** Let `F` be the fibre over `z`, a subset of `↥M`.
* *Continuum:* `F = ⋂_k closure (W_k)`, with `W_k` the union of the links of `R_k(z)` (one
  period). `closure W_{k+1} ⊆ W_k` (`nest`, `arcNest`), and `W_k` is connected (a run of
  preconnected links, consecutive ones meeting). So `F` is a nested intersection of nonempty
  compact connected sets.
* *Nondegenerate:* (3.5).
* *Chainable:* the run chains of (3.8) in `↥M` cover `F` (by (3.4)) and have mesh `≤ ε_k`.
* *Hereditarily indecomposable:* let `H ⊆ F` be a subcontinuum with `H = A ∪ B`, `A` and `B`
  proper subcontinua. Choose `p ∈ H \ A`, `q ∈ H \ B` and `δ > 0` with `B(p, δ) ∩ A = ∅` and
  `B(q, δ) ∩ B = ∅`. Take `k` with `3 ε_k < δ`. Apply `Description.theorem10_core` with
  `D` = the run chain of `R_k(z)`, `E` = that of `R_{k+1}(z)` ((3.9)), in `X` with the subsets of
  `F` read in `X`. This is Bing's argument of `Description.theorem10`; only the source of
  crookedness changes. Transfer to `↥M` as the library does elsewhere (`PA51Lift`).

**(3.11) `M` is circle-like.** For `ε > 0` take `k` with `ε_k < ε`. The traces
`L_k t ∩ M` (`0 ≤ t < N_k`) form a `CircChain ↥M N_k`:
* they are open and cover `↥M`;
* two traces meet iff the cyclic distance of the indices is at most 1, by `meet_iff` and (3.2),
  and every trace is nonempty by (3.5);
* diameters are at most `ε_k`.

With (3.1) this is `IsCircleLike (univ : Set ↥M)`. Then `f` is continuous, open and onto, with
pseudo-arc fibres ((3.6), (3.7), (3.5), (3.10)): `IsCircleOfPA Δ.M`.

## 4. Sweep patterns (skeleton §4)

### 4.1 The sweep lemma

A *sweep* is a block of consecutive indices `[σ₀, σ₁]` with a window `[b, t]` (integers,
`t − b ≥ 1`) and a direction, on which `g` takes values in `[b, t]`, is `PatCrookedOn`, starts at
`b` and ends at `t` (up), or starts at `t` and ends at `b` (down).

A *sweep walk* on `[lo, hi]` is a function `g` with steps of size at most 1, and a cutting of
`[lo, hi]` into consecutive blocks satisfying the following:
* the inner blocks are sweeps;
* the first block is a final segment of a sweep, and the last block is an initial segment of one
  (partial sweeps: same window and direction conditions, except that the first need not start at
  its extreme and the last need not end at it);
* consecutive blocks have opposite directions;
* the last value of a block equals the first value of the next, and is the extreme where the
  block ends;
* windows change only at junctions, and only by one end: after an up block (ending at `t`), the
  next window is `[b, t]` or `[b + 1, t]`; after a down block (ending at `b`), it is `[b, t]` or
  `[b, t + 1]`.

A junction where the window changes is an *event*.

**Lemma (sweep lemma).** A sweep walk on `[lo, hi]` with at most three events is `PatCrookedOn` on
`[lo, hi]`.

*Proof.* Take `i`, `j` in `[lo, hi]` with `g i ≤ h`, `h + 3 ≤ k ≤ g j`. The ascending case
`i < j` comes first; the descending case `j < i` is at the end.
* **Reduction.** Let `t₀` be the last index in `[i, j]` with `g ≤ h`, and `s₀` the first index in
  `[t₀, j]` with `g ≥ k`. Unit steps give `g t₀ = h`, `g s₀ = k`, and `h < g < k` strictly
  between them. It suffices to find `t₀ < r < s < s₀` with `g r = k − 1` and `g s = h + 1`.
* Let `σ` be the block containing `t₀`.
* **Case 1: `s₀ ∈ σ`.** Crookedness of `σ` on `[t₀, s₀]`.
* **Case 2: `s₀ ∉ σ`.**
  * `t₀` is not the last index of `σ`. Otherwise the next block starts at the value `h`, at an
    index in `(t₀, s₀]`, against the choice of `t₀`.
  * So the last index `e` of `σ` lies in `(t₀, s₀)`, and `h < g e < k`.
  * If `σ` were down, `g e = b_σ ≤ g t₀ = h`. So `σ` is up, `g e = t_σ`, and `t_σ < k`.
  * The next block `σ'` is down, with values `≤ t_σ < k`, so `s₀` lies beyond it and `σ'` is a
    full sweep ending at its bottom `b_{σ'}`. As `σ'` lies in `(t₀, s₀)`, `b_{σ'} > h ≥ b_σ`.
  * So the junction `σ|σ'` is an event: `h = b_σ` and `b_{σ'} = h + 1`.
  * **Case 2a: `k − 1 ≤ t_σ`.** Take `r` the first index after `t₀` in `σ` with `g r = k − 1`
    (`σ` climbs from `h` to `t_σ`), and `s` the last index of `σ'`.
  * **Case 2b: `k − 1 > t_σ`.** To reach `k ≥ t_σ + 2` the top must grow twice after `σ'`.
    Tops grow only at junctions after a down block. Between the two growths the walk climbs to
    the top and must come down again, so there is a junction after an up block in between. With
    the event `σ|σ'` and at most three events in all, that junction is not an event, so the
    bottom is still `h + 1` there.
    * Take `r` the first index with `g r = k − 1 = t_σ + 1`. It lies in the first up block after
      the first growth, and that block ends at the top `k − 1`. (If `k − 1 > t_σ + 1`, three
      growths are needed, and with `σ|σ'` that makes four events.)
    * Take `s` the end of the down block that follows. That block runs from the top `k − 1` to
      the bottom `h + 1` before the second growth, so `r < s < s₀`.
* **The descending case `j < i`.** Only Case 1 occurs, because windows move only upwards.
  * Let `s₀` be the last index in `[j, i]` with `g ≥ k`, and `t₀` the first index after `s₀` with
    `g ≤ h`. Then `g s₀ = k`, `g t₀ = h`, and `h < g < k` strictly between them. It suffices to
    find `s₀ < s < r < t₀` with `g s = h + 1` and `g r = k − 1`.
  * Suppose `t₀` is not in the block `σ` of `s₀`. Then `s₀` is not the last index of `σ`, since
    the next block starts at the same value. So the end `e` of `σ` lies in `(s₀, t₀)`, with
    `h < g e < k`.
  * If `σ` were up, `g e = t_σ ≥ g s₀ = k`. So `σ` is down and `g e = b_σ > h`.
  * The next block `σ'` is up, and its bottom is `b_σ`, since bottoms change only after up
    blocks. Its values are `≥ b_σ > h`, so `t₀ ∉ σ'`, and `σ'` is a full sweep ending at its top,
    which is at least `t_σ ≥ k`, inside `(s₀, t₀)`: a contradiction.
  * So `t₀ ∈ σ`, and the crookedness of `σ` on `[s₀, t₀]` gives the witnesses. ∎

(Reversing the indices together with `g ↦ −g` maps sweep walks to sweep walks, but it maps the
descending case to itself, so it does not reduce one case to the other.)

A script check: with one sweep between events, intervals with four events fail; with three
sweeps between events, five events still pass and six fail. The lemma needs no more than three.
The skeleton does not state the sweep lemma; choose its shape (for instance, a list of blocks with
their windows and directions).

### 4.2 The pattern

Parameters: integers `m ≥ 5` and `S ≥ 1`. Put
* `d₁ = m − 2`, `d₂ = m − 1`, `L = S · z(d₁) · z(d₂)` (`z` is `HPC.Fold.z`), `P = 3L`,
* `Q = 2P = 6 S z(m−2) z(m−1)` (`sweepQ m S` in the skeleton).

The old link `l` sits at `l` and the new link `t` at `y(t) = 1/4 + t/Q`, in old units. The window
radius is `ρ = m/2 − 1/4`.

**Periods.** For `j ∈ ℤ`, period `j` is the block of indices `[jP, (j+1)P)`. Its `y`-range is
`[e_j, e_{j+1})` with `e_j = 1/4 + j/2`. Its window is
* `t_j = ⌊(j + m)/2⌋`, `b_j = ⌈(j + 2 − m)/2⌉`,
* the integers `l` with `|l − y| ≤ ρ` for every `y` in `[e_j, e_{j+1}]`.

The width `d_j = t_j − b_j` is `m − 1` when `j + m` is even and `m − 2` when it is odd. From
period `j` to `j + 1` the top grows when `j + m` is odd and the bottom shrinks when `j + m` is even,
one end at a time.

**Sweeps.** Period `j` consists of three sweeps of length `L` across its window, each the stuttered
Bing pattern with stutter `K_j = L / z(d_j)` (so `K_j = S z(m−1)` or `S z(m−2)`, both `≥ S`):
* up: `u ↦ b_j + bingF d_j (u / K_j)`, `0 ≤ u < L`;
* down: `u ↦ t_j − bingF d_j (u / K_j)`.

Period `j` starts at the bottom iff `j + m` is even, and the sweeps alternate. So a period that
follows a top growth starts at the bottom, and a period that follows a bottom shrink starts at the
top, as the sweep lemma requires.

### 4.3 Properties (`exists_sweepPattern`)

1. **Period.** `x (t + Q) = x t + 1`: `t_{j+2} = t_j + 1`, `b_{j+2} = b_j + 1`, same parity.
2. **Unit steps.** Inside a sweep (`stut_lip`); at a junction both sides take the same extreme
   value.
3. **Slowness.** The walk is a sequence of maximal constant blocks of length `≥ S`, consecutive
   blocks differing by 1. So `x s + 2 ≤ x t` forces `|s − t| ≥ S`.
4. **Nesting.** `|x t − y(t)| ≤ ρ`. In period `j`, `y(t) ∈ [e_j, e_{j+1})` and
   `b_j ≤ x t ≤ t_j`, with `t_j ≤ e_j + ρ = (j + m)/2` and `b_j ≥ e_{j+1} − ρ = (j + 2 − m)/2`.
5. **Survival.** If `|y − l| ≤ m/2 − 1/2`, there is `t` with `x t = l` and
   `|y − y(t)| ≤ 1/4 − 1/(2Q)`.
   * The periods whose window contains `l` are `j = 2l − m, …, 2l + m − 2`, covering the
     `y`-range `[l − ρ, l + ρ)`.
   * Every sweep of these periods takes the value `l`.
   * First period `j₁ = 2l − m`: `t_{j₁} = l` is a new top and the period starts at the bottom.
     Its first sweep reaches `l` at an index with `y ≤ l − ρ + (L − 1)/Q < l − ρ + 1/6`.
   * Last period `j₂ = 2l + m − 2`: `b_{j₂} = l`, and its third sweep starts at `l`, at
     `y = l + ρ − 1/6`.
   * Consecutive visits are less than `2L` indices apart, a `y`-gap below `1/3 ≤ 1/2 − 1/Q`.
   * So the intervals `[y(t) − 1/4 + 1/(2Q), y(t) + 1/4 − 1/(2Q)]` over the visits cover
     `[l − ρ + 1/4, l + ρ − 1/4] = [l − m/2 + 1/2, l + m/2 − 1/2]`.
6. **Crookedness.** `u ↦ x (a + u)` is `PatCrookedOn` on `[0, P + 3]` for every integer `a`.
   * `[a, a + P + 3]` contains at most two multiples of `P` (`P ≥ 4`), so at most two events;
     junctions inside a period keep the window.
   * Each sweep is crooked (`stut_crooked`, shifted and reflected). Apply the sweep lemma.

### 4.4 Remarks

* Three sweeps per period are needed for survival. With one sweep, consecutive visits to a link
  can be a whole period apart (`y`-gap `1/2`), more than `1/2 − 1/Q`. The script confirms that
  survival fails then.
* In §6 the new level has `λ N = Q/2 = P`, so the crookedness window `⌈λ_{k+1} N_{k+1}⌉ + 3` of
  `crook` is `P + 3`.

### 4.5 The script

`m = 5`, `S = 1` (and `S = 2`), `N = 16`: `Q = 468`, `N' = Q N = 7488`. Checked over a full
revolution: unit steps, period, nesting, survival (exact rational arithmetic), and crookedness on
all intervals of length `P + 4`. Also `m = 7`, `N = 20` and `m = 5` with five sweeps per period.
No failures. With one sweep per period survival fails at the first link.

## 5. The circular planar step (skeleton §5)

**Standard circular chains.** `stdRectZ t = (2t, 2t + 3) × (0, 1)` for `t ∈ ℤ`, and
`zoneZ t = [2t + 8/5, 2t + 17/5] × [0, 1]` (batch 84's `stdRect` and `zone`, with integer index).
`circExp N (u, v) = (e^v cos(πu/N), e^v sin(πu/N))`, of period `2N` in `u`.
`stdCircLink N t = circExp N '' stdRectZ t` and `stdCircZone N t = circExp N '' zoneZ t`.

Library tools to reuse instead of duplicating: `HPC/Plane/Cyc2Circle.lean` (`exists_angle`,
`angle_unique`, `circPt`), `HPC/BJ59/CircleLike.lean` (`circP`, `circArc`, `circArcChain`, and
`isCircleLike_circle` for the base circle), and batch 84's `Joints`, `Shear`, `StdStep`,
`RealStep`. Note that `Pt` carries the sup metric.

**`stdCircLink_meet_iff`.** For `N ≥ 4`, `stdCircLink N s` meets `stdCircLink N t` iff `s − t` is
within 1 of a multiple of `N`. Two points have the same image iff the `v` agree and the `u` differ
by a multiple of `2N`, and the `u`-intervals `(2s, 2s+3)`, `(2t + 2Nn, 2t + 2Nn + 3)` meet iff
`|s − t − Nn| ≤ 1`.

**`circ_step`** (the analogue of `real_step`). Given `Φ : Pt ≃ₜ Pt`, `N ≥ 4`, `ε > 0` and a bound
`B`, there is `S ≥ 12` such that every lifted pattern `x : ℤ → ℤ` with the following properties
is realized:
* `x (t + Q) = x t + 1`, `Q ≥ 2`;
* unit steps;
* `S`-slow: `x s + 2 ≤ x t ⇒ |s − t| ≥ S`;
* `|x t − (y₀ + t/Q)| ≤ B`.

Realized means: there is `ψ : Pt ≃ₜ Pt` such that, with the new chain
`(ψ.trans Φ) '' stdCircLink (Q N) t` and the old chain `Φ '' stdCircLink N l`, the following
hold:
1. the closure of new link `t` lies in old link `x t`;
2. tightness: new link `t` meets old link `l` only if `x t' = l + nN` with `|t' − t| ≤ 1`;
3. each new link has diameter `≤ ε` or lies in an old zone `Φ '' stdCircZone N k`;
4. each new zone `(ψ.trans Φ) '' stdCircZone (Q N) t` has diameter `≤ ε`.

**Construction.**
* **Joint positions.** `P(t) ∈ ℝ` for `t ∈ ℤ`, by the formulas of `Joints.P` applied to the
  lifted pattern:
  * stay (`x (t−1) = x t`): `2 x t + 3/2 + f(t)/4`;
  * transition: `2 min(x (t−1), x t) + 5/2`;
  * `f(t) = (ℓ − r)/(ℓ + r)` from the doubled distances to the nearest indices with values
    `x t ∓ 1`, capped at `2S`.

  These are local, so `P(t + Q N) = P(t) + 2N`. The lemmas of `Joints` (`link_cases`,
  `link_facts`, `P_stay_step`, …) transfer: each concerns a bounded window of indices. Re-prove
  them for `ℤ`-indexed patterns, or reduce to the finite case on windows.
* **Interpolation.** `P̂(u) = P(t)` for `u ∈ [2t − 2/5, 2t + 7/5]` (the `u`-range of
  `zoneZ (t − 1)`), linear from `P(t)` to `P(t+1)` on `[2t + 7/5, 2t + 8/5]`, as the ramps of
  batch 84's `Shear` (`σ`, `τ`). The pieces tile `ℝ`, `P̂(u + 2QN) = P̂(u) + 2N`, and `P̂` is
  constant equal to `P(t+1)` on `zoneZ t`'s `u`-range.
* **The shear on the cover.** With small constants `ε₀, C > 0`,
  `Ψ̃(u, v) = (P̂(u) + ε₀ v, 1/2 + C (P̂(u) − u/Q − 2y₀ − 3/2) + C ε₀ v)`.
  * *Homeomorphism of `ℝ²`:* it is the vertical shear `(u, v) ↦ (u, w)`,
    `w = P̂(u) − u/Q + ε₀ v`, followed by the linear map
    `(u, w) ↦ (u/Q + w, 1/2 + C (w − 2y₀ − 3/2))` of determinant `C/Q ≠ 0`.
  * *Injectivity, directly:* equal images force `u/Q = u'/Q` (subtract the second coordinate
    divided by `C` from the first), then `v = v'`.
  * *Equivariance:* `Ψ̃(u + 2QN, v) = Ψ̃(u, v) + (2N, 0)`.
* **Heights.** `|P̂(u) − u/Q − 2y₀ − 3/2| ≤ 2B + 4`: the joint formulas give
  `|P(t) − 2x t − 3/2| ≤ 1`, a ramp adds at most 2, `|2x t − 2y₀ − 2t/Q| ≤ 2B`, and
  `|u − 2t| ≤ 8/5` adds at most `4/5` through `u/Q`. With `C (2B + 5) ≤ 1/8` and `ε₀ ≤ 1/20`,
  `Ψ̃` maps `ℝ × [0, 1]` into heights in `(1/4, 3/4)`. (`ε₀ ≤ 1/20` is also what `link_facts`
  leaves for transition links to lie in old zones.)
* **Descent.** `ψ (circExp (QN) p) = circExp N (Ψ̃ p)` for every `p ∈ ℝ²`; this defines `ψ` on
  `ℝ² \ {0}`, and `ψ 0 = 0`.
  * It is well defined and bijective by equivariance (for `Ψ̃` and for `Ψ̃⁻¹`).
  * It is continuous away from 0 because `circExp` is a local homeomorphism.
  * It is continuous at 0, and so is its inverse, because the second coordinate of `Ψ̃(u, v)` is
    `C ε₀ v` plus a bounded function of `u`: `|ψ w| ≤ e^{B'} |w|^{C ε₀}`.
* **The four properties.** On the cover, `Ψ̃ '' stdRectZ t` has horizontal projection in
  `[min(P t, P(t+1)), max(P t, P(t+1)) + ε₀]` and heights in `(1/4, 3/4)`.
  * Containment and tightness are then batch 84's horizontal analysis (`link_facts`), read
    modulo `2N` through `circExp N`.
  * Smallness: the image of a stay link has width `|P(t+1) − P(t)| + ε₀` and height
    `C (|P(t+1) − P(t)| + 3/Q + ε₀)`. Stay steps are `O(1/S)` (`P_stay_step`), so stay links are
    small for `S` large. Transition links lie in old zones. `Ψ̃ '' zoneZ t` is a parallelogram
    inside a box of width `ε₀` and height `C (9/(5Q) + ε₀)`.
  * Then use uniform continuity of `circExp N` on `ℝ × [0, 1]`, which is periodic and so
    uniformly continuous, and of `Φ` on the compact annulus `1 ≤ |p| ≤ e`, as in `real_step`.

Choose `ε₀` and `C` from `ε`, `B` and the moduli of continuity, then `S`.

## 6. Assembly (skeleton §6)

### 6.1 Levels

A level is `(N, Φ, m, o)` with `N ≥ 16`, `m ≥ 5`, `m + 4 ≤ N`:
* level 0 is `(16, id, 5, 0)`;
* from level `i`, with `η_i = 1/2^i` and `B = m/2 − 1/4`:
  * take `S` from `circ_step Φ N η_i B`;
  * take `x` from `exists_sweepPattern m S` and put `Q = sweepQ m S`;
  * take `ψ` from `circ_step` with `y₀ = 1/4`;
  * level `i + 1` is `(Q N, ψ.trans Φ, Q/2, o + 1/(4N))`.

Then `Q/2 = 3 S z(m−2) z(m−1) ≥ 5` and `Q/2 + 4 ≤ Q N`.

### 6.2 The circular description in the plane (`exists_circDescr_plane`)

* `N k`, `L k t = Φ_k '' stdCircLink (N k) t`, `pat k` = the pattern of step `k`, `o k`,
  `λ_k = m_k / N_k`.
* `K` = the closed annulus `1 ≤ |p| ≤ e`. Level-0 links lie in it, and all others by `nest`.
* `isOpen_L`, `preconn`: homeomorphic images of open preconnected sets (`circExp N` is open on
  `ℝ × (0, 1)`).
* `periodic`: `stdRectZ (t + N) = stdRectZ t + (2N, 0)` and `circExp N` has period `2N`.
* `meet_iff`: `stdCircLink_meet_iff`. `nest`, `tight`: `circ_step` 1 and 2. `pat_period`:
  §4.3 1 iterated `N_k` times, `x (t + Q N_k) = x t + N_k`. `pat_step`: §4.3 2.
* `ε k = 16/2^k`, `diam_le`: as `dlink_diam` (batch 84).
  * Level-0 links and zones lie in the closed sup-ball of radius `e`, so their diameters are at
    most `2e < 8`.
  * A level-`(i+1)` link has diameter `≤ η_i` (`circ_step` 3), or lies in a level-`i` zone, of
    diameter `≤ η_{i−1}` by `circ_step` 4 at the previous step, or `< 8` when `i = 0`.
  * So level `k` has mesh `≤ 8 ≤ 16/2^k` for `k ≤ 1`, and `≤ 4/2^k` for `k ≥ 2`.
* `lam_tendsto`: `λ_{k+1} = 1/(2N_k)`. `five_le_lam`, `lam_add_four_le`: §6.1.
* `arcNest`: `|c_{k+1}(t) − c_k(x t)| = |1/4 + t/Q − x t| / N_k ≤ (m/2 − 1/4)/N_k`
  `= (λ_k − λ_{k+1})/2`, by §4.3 4.
* `surv`: put `y = N_k (z − o_k)`. The hypothesis is `|y − l| ≤ m/2 − 1/2`; §4.3 5 gives `t` with
  `|y − 1/4 − t/Q| ≤ 1/4 − 1/(2Q)`, which is the conclusion multiplied by `N_k`
  (`λ_{k+1}/2 = 1/(4N_k)`, `δ_{k+1} = 1/(2QN_k)`).
* `crook`: `λ_{k+1} N_{k+1} = Q/2 = P`, and §4.3 6.

### 6.3 The example and the corollaries

* `bjPlaneExample : BJPlaneExample` from `CircDescr.isCircleOfPA`.
* With no named hypothesis:
  * `ho16_classification₄` (Bing–Jones's third class);
  * `ho16_classification_plane₄`;
  * `dp22_theorem61'` (Domokos–Prajs 6.1, "if");
  * `dp22_theorem61_iff'`;
  * `hoCircleLike'`.

## 7. Ledger

New section "Bing–Jones §7, the plane example (batch 202)", in the convention "printed X, read Y"
where it applies. Check each quotation at 400 dpi.

1. **P. 190**: "Now there exists a sequence D₁, D₂, D₃, ⋯ of circular chains of simple domains in
   the plane such that" (1)–(9). The chains are not constructed. Not established; the example is
   obtained here by another construction (§§3–6), not Bing–Jones's.
2. **P. 191**: "Also, in this case M would be a continuous circle-like circle of continua." Here
   "in this case" means with (9) omitted; the same claim for the chains with (9) is implicit in
   the next two sentences. That the elements of `G` are disjoint, fill `M`, and form a continuous
   decomposition with a circle as quotient is not argued in either case.
3. **P. 191**: "With the addition of (9) one may see with the help of [3] that each element of G
   is a pseudo-arc." Unargued. (9) reads: "if h<i and T_ij is a refinement of T_hk+T_hl, T_ij is
   crooked [3] with respect to T_hk+T_hl where l=(k+1) mod n(h)." Check the subscripts at 400 dpi.
   As far as I can see, (9) does not control an element of `G` covered by two adjacent columns at
   a level. Say whether you agree. A certificate is welcome: two chains, each crooked in the
   union of two consecutive subchains (columns) of a fixed chain, whose concatenation is not
   crooked in the union of the columns it refines.
4. **P. 190**: "It is easy to see that G is an upper-semicontinuous collection of arcs, G is a
   circle (if its elements are thought of as points) and G* (the sum of the elements of G) is a
   circle-like continuum." This is about the `V`-collection and is not used. Unargued; harmless.
5. **Route.** The construction of this batch uses no part of §7 except its claim. Not a defect.

Add any other defect of §7 you meet. Count nothing yourself; say which items, if any, you would
count.

## 8. Non-vacuity

* `CircDescr`: `exists_circDescr_plane` is the witness. Say what the degenerate inputs give:
  constant `N` is impossible (`ε → 0` with links of a fixed chain), and `four_le` and
  `five_le_lam` exclude the small cases.
* The sweep lemma: test it on a single sweep (no junction) and on a walk with exactly three
  events. Give a sweep walk with four events that is not crooked, as a certificate that the bound
  is needed.
* `exists_sweepPattern`: the hypotheses `m ≥ 5`, `S ≥ 1`. Give the certificate of §4.4 if it is
  cheap: with one sweep per period, survival fails.
* `circExp`, `stdCircLink`, `stdCircZone`: for `N = 0`, `circExp 0` maps everything onto the
  ray `{(e^v, 0)}` and `stdCircLink_meet_iff` fails (its right side becomes `|s − t| ≤ 1`). For
  `N = 1, 2, 3` both sides of `stdCircLink_meet_iff` hold for all `s`, `t`; record this.
* `circ_step`: its hypotheses hold for the stuttered identity `x t = ⌊t / Q⌋` with `Q ≥ S`.
* **The omission of batch 201.** The halves of the plane example are continuous snake-like arcs of
  pseudo-arcs (`IsSnakeHalvesMap`). Give non-degenerate witnesses for `BJStep`, `BJThm10`,
  `bj_theorem8_cor_sub`, `bj_theorem5_window` and `exists_window_set` from them.

## 9. Order

1. §4 (the sweep lemma, then `exists_sweepPattern`), with its tests.
2. §3, the recognition theorem.
3. §5, the circular planar step.
4. §6, the assembly and the corollaries.
5. §8.

§7 alongside. If time runs short, finish §§3–4 before §5: they do not depend on it. Leave
anything open as an `OPEN.md` entry with the obstruction.

## 10. Deliverables

1. **The items of §§3–6 and §8.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch202.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. **`LEDGER.md`:** the new section of §7.
3. **Notes:** append to `doc/notes/bj59.md`.
4. **Publish the changes, as in batch 201**: `doc/batches/batch202-files.tar.gz` with every file
   added or changed (including the commission and skeleton copies) and
   `doc/batches/batch202-MANIFEST.txt`.
5. **The report.** Its first line names the commission it read. It covers the following:
   * the items in order, the shape changes and the non-vacuity notes;
   * the ledger entries and the axioms used by each theorem;
   * whether `ho16_classification₄` and `ho16_classification_plane₄` depend on any named
     hypothesis.
