# Commission: batch 4 — consolidation infrastructure

**Go!** Runs on top of the batch-3 delivery (run 87042441-b076-4e09-ae82-352394b66137). One
new file, `HPC/Chains/Consolidation.lean`; root `HPC.lean` updated. Nothing else touched.
Every `sorry` is a work item; delivery contains none.

## Purpose

Bing 1948 Theorems 3 and 4 are not in this batch: their published proofs are incomplete at
two points and their statement is ambiguous in a way that matters (see the accompanying
notes, not part of the archive). This batch builds what their correct statements and proofs
will need, all of which is provable now: block consolidations as an explicit map, chain
reversal, crookedness of subchains and in subchains, minimal and maximal index maps, the
monotone grouping lemma, the easy case of Theorem 4 as a corollary, and a counterexample
fixing the meaning of "contained in only the first link".

## Protocol

As batches 1–3: no `sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`; `#print axioms`
on every theorem showing only the three standard axioms; census first; report rather than
repair; first make the skeleton compile with proofs still `sorry`, changing only syntax and
mathlib names, recording every change; on any statement that cannot be made to compile
without changing its meaning, stop and report. The `Nat.find`-based definition of `minIdx`
and the `Σ`-typed `monoBlocks` are suggestions; if a cleaner encoding is preferred, use it
and record the change, keeping the *stated properties* (`minIdx_subset`, `minIdx_le`,
`monoBlocks_spec`) as the specification.

Batch-1 and batch-3 results expected to be used: `Chain.link_nonempty`, `Chain.sub`,
`Chain.refineIdx`, `Chain.pattern_lipschitz`, `Chain.exists_value_between`, and the discrete
intermediate value lemmas of `HPC/Chains/Aux.lean`.

## 1. Definitions

- `IsBlockMap β`: `β : Fin n → Fin p` surjective, moving by at most one between adjacent
  indices.
- `ofBlocks D β hβ`: the chain whose `u`-th link is the union of the links of `D` in block
  `u`.
- `reverse D`: link `i` is `D.link (Fin.rev i)`.
- `minIdx h t`, `maxIdx h t`: for `h : E.Refines D`, the least and greatest index `j` with
  `E.link t ⊆ D.link j`. `maxIdx` is defined as the reversal of `minIdx` for the reversed
  coarse chain.
- `group n j = min (j − 1) (n − 3)` (natural subtraction), the group of coarse index `j`:
  `0` for `j ≤ 1`, `j − 1` for `2 ≤ j ≤ n − 3`, `n − 3` for `j ≥ n − 2`.
- `monoBlocks h hn`: the block map `t ↦ group n (minIdx t)`, shifted down by its minimum
  value so that its range is an initial segment, packaged with `p` = number of blocks.

## 2. Reading of "contained in only the first link"

Throughout the project, for a block consolidation given by `β`, *"`d_i` is contained in only
the first link of `F`"* means **`β i = 0`** — the block reading. The alternative reading —
`d_i` disjoint from every link of `F` but the first — forces the neighbors `d_{i±1}` into
block `0` as well, and `not_exists_strong_first_block` shows that is impossible in general.
Consequences for later batches are in the notes.

## 3. Proofs

### ofBlocks

*Openness.* A union of open sets.

*Adjacency.* Let `u u' : Fin p`. (⇒) If `(link u ∩ link u').Nonempty`, pick `x` in it; then
`x ∈ D.link t ∩ D.link t'` with `β t = u`, `β t' = u'`; by `D.adjacent`, `|t − t'| ≤ 1`; if
`t = t'` then `u = u'`; otherwise `hβ.lip` (in one of the two orientations) gives
`|u − u'| ≤ 1`. (⇐) If `u = u'`: by surjectivity pick `t` with `β t = u`; `D.link t` is
nonempty (`link_nonempty`) and lies in `link u`. If `u' = u + 1` (the other case is
symmetric): by surjectivity there are `t₀` with `β t₀ = u` and `t₁` with `β t₁ = u + 1`.
Walking from `t₀` to `t₁` (in whichever direction), `β` changes by at most one per step
(`hβ.lip`), starts at `u` and ends at `u + 1`; let `t'` be the first index on the walk with
`β t' ≥ u + 1` and `t` its predecessor; then `β t ≤ u` and `β t' ≥ u + 1` with
`|β t' − β t| ≤ 1` force `β t = u`, `β t' = u + 1`. `t, t'` are adjacent, so
`D.link t ∩ D.link t'` is nonempty and lies in `link u ∩ link (u+1)`. *(This "first index
where the value crosses" argument is the discrete intermediate value theorem of Aux; use it.)*

### ofBlocks_isConsolidationOf

`D.Refines (ofBlocks …)`: `D.link t ⊆ link (β t)`. Each `link u` is `⋃ t ∈ S, D.link t` with
`S = {t | β t = u}`.

### On the converse (not a theorem in this batch)

That every batch-1 D6 consolidation arises from a block map is **false**: D6 does not require
the index sets `S_u` to partition `Fin n`, so a link `d_t` covered by `d_{t−1} ∪ d_{t+1}` may
belong to no `S_u`, and any choice of block for it can fail to reproduce `F`. The skeleton
carries a note to this effect and no statement. From this batch on, Theorems 3–5 are stated
for `ofBlocks`; D6 stays only where already used.

### reverse

*Adjacency.* `(D.link (rev i) ∩ D.link (rev j)).Nonempty ↔ |rev i − rev j| ≤ 1`, and
`rev i − rev j = j − i` as integers.

*reverse_reverse.* `Fin.rev_rev`.

*Refines.reverse_left / reverse_right.* Reindex the witnesses by `rev`.

*IsCrookedIn'.reverse_left.* Given `h k` with `h + 2 < k` and links `i j` of `E.reverse`
meeting `D.link h`, `D.link k`: these are links `rev i`, `rev j` of `E`; the hypothesis gives
`r s` with `Between (rev i) r s (rev j)` and the containments; take `rev r`, `rev s`. `Between`
is preserved by `rev` on all four indices since `rev` reverses order.

*IsCrookedIn'.reverse_right.* Given `h k` of `D.reverse` with `h + 2 < k`, i.e. coarse links
`rev h`, `rev k` of `D` with `rev k + 2 < rev h`. Apply the hypothesis to the pair
`(rev k, rev h)` with the roles of `i` and `j` exchanged: it yields `r s` with
`Between j r s i`, `E.link r ⊆ D.link (rev h − 1)` and `E.link s ⊆ D.link (rev k + 1)`. Now
`Between j r s i` is `Between i s r j` with `r` and `s` exchanged, and in `D.reverse` the
link adjacent to `k` toward `h` is `rev (rev k + 1)` and the link adjacent to `h` toward `k`
is `rev (rev h − 1)`; so `(s, r)` is the witness pair. *(supply: the index arithmetic.)*

### IsCrookedIn'.sub

The subchain has links `E.link (i + t)`; a pair of its links meeting `D.link h`, `D.link k`
is a pair of links of `E`, so the hypothesis gives `r s` between them in `E`'s indexing;
since `Between` places `r, s` strictly between the two, they are indices of the subchain.

### IsCrookedIn'.restrict

Coarse indices of `D.sub a b` are `a + h'`; the hypothesis for `D` at `(a + h', a + k')` gives
`r s` with `E.link r ⊆ D.link (a + k' − 1)` and `E.link s ⊆ D.link (a + h' + 1)`, which are
links `k' − 1`, `h' + 1` of the subchain.

### subset_adjacent_of_subset

`E.link t` is nonempty (`link_nonempty`) and lies in `D.link j ∩ D.link j'`, so that
intersection is nonempty; `D.adjacent`.

### minIdx, minIdx_subset, minIdx_le

`Nat.find` on the predicate `∃ hj, E.link t ⊆ D.link ⟨j, hj⟩`, which is satisfied by
`refineIdx`; `Nat.find_spec` and `Nat.find_min'`. The `sorry` in the definition is the
bound `Nat.find … < n`, from `Nat.find_spec`.

### maxIdx_subset, le_maxIdx

Unfold `maxIdx`; `E.link t ⊆ D.reverse.link (minIdx …) = D.link (rev (minIdx …))`. For
`le_maxIdx`, `hj` reversed gives `E.link t ⊆ D.reverse.link (rev j)`, so
`minIdx ≤ rev j`, so `j ≤ rev minIdx`.

### minIdx_lip, maxIdx_lip

`E.link t ⊆ D.link (minIdx t)`, `E.link t' ⊆ D.link (minIdx t')`, and `E.link t ∩ E.link t'`
is nonempty (`E.adjacent`), so `D.link (minIdx t) ∩ D.link (minIdx t')` is nonempty;
`D.adjacent`. Same for `maxIdx`.

### minIdx_near_of_inter

`E.link t ⊆ D.link (minIdx t)` meets `D.link j`, so those two links of `D` meet; `D.adjacent`.

### monoBlocks, monoBlocks_spec

Let `g t := group n (minIdx t).val`. Since `minIdx` is Lipschitz (`minIdx_lip`) and `group n`
is monotone with increments `≤ 1`, `g` moves by at most one between adjacent `t`. Let
`g₀ := min over t of g t` (nonempty finite set) and `g₁ := max`. Since `g` takes values in
`[g₀, g₁]` and moves by ≤ 1, it takes every value in between (discrete IVT); set
`p := g₁ − g₀ + 1` and `β t := ⟨g t − g₀, _⟩`. `β` is surjective onto `Fin p` and Lipschitz:
`IsBlockMap β`.

*Blocks in two adjacent links.* Fix `u`. The links in block `u` all have `g t = u + g₀ =: v`.
If `v = 0`: `minIdx t ≤ 1`, so `E.link t ⊆ D.link 0 ∪ D.link 1`; take `j = 0`. If
`1 ≤ v ≤ n − 4`: `minIdx t = v + 1` exactly, so `E.link t ⊆ D.link (v+1)`; take `j = v + 1`
(and the union with `D.link (v+2)` is harmless). If `v = n − 3`: `minIdx t ≥ n − 2`, so
`E.link t ⊆ D.link (n−2) ∪ D.link (n−1)`; take `j = n − 2`. In each case the containment
holds for every link in the block, hence for the union. *(supply: the case split on `v` and
the arithmetic of `group`.)*

*First and last.* `minIdx t ≤ 1` gives `g t = 0`, the least possible value of `group`, so
`g₀ = 0` and `β t = 0`. `minIdx t ≥ n − 2` gives `g t = n − 3`, the greatest possible value,
so `g₁ = n − 3` and `β t = p − 1`.

### exists_blocks_first_last

By `minIdx_near_of_inter`, `hr` gives `minIdx r ≤ 1` and `hs` gives `minIdx s ≥ n − 2`.
Apply `monoBlocks_spec`.

### Ecx, Dcx

Interval arithmetic. `Ecx`: consecutive intervals overlap `(1,2), (3,4), (5,6), (7,8)`; the
pairs two apart, `(0,2)/(3,6)`, `(1,4)/(5,8)`, `(3,6)/(7,9)`, are disjoint, as are those
further apart. `Dcx`: `(2.2,3.5) ∩ (3.2,5.8) = (3.2,3.5)`, `(3.2,5.8) ∩ (5.5,6.8) = (5.5,5.8)`,
`(2.2,3.5) ∩ (5.5,6.8) = ∅`.

### Dcx_refines

`d₀ ⊆ e₁ = (1,4)`, `d₁ ⊆ e₂ = (3,6)`, `d₂ ⊆ e₃ = (5,8)`.

### Dcx_isCrookedIn'

Refinement as above. The coarse pairs `(h, k)` with `h + 2 < k` are `(0,3)`, `(0,4)`, `(1,4)`.
No link of `Dcx` meets `e₀ = (0,2)` (all lie in `(2.2, 6.8)`) and none meets `e₄ = (7,9)`. So
every instance of the condition has a false hypothesis.

### not_exists_strong_first_block

Suppose `β 0 = β 1 = β 2 =: u`. Then `(Dcx.ofBlocks β hβ).link u ⊇ d₀ ∪ d₂`, which contains
`2.3` and `6.7`. The four candidate unions of adjacent links of `Ecx` are `(0,4)`, `(1,6)`,
`(3,8)`, `(5,9)`; none contains both `2.3` and `6.7`.

## 4. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: what was supplied at each step; any statement that did not go through.

## 5. Not in this batch

Bing 1948 Theorems 3, 4 (general case), 5, 6; the reduction in Bing 1951; the D8/D9 gap.
