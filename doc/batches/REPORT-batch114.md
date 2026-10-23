Commission read: `COMMISSION-batch114.md` — batch 114, the covering step of Bing 1948, Theorem 14, by Lehner's Lemma 3.

# Report, batch 114

**Refutations:** none. No statement of the skeleton is false.

All three items are **proved**; none is open. The two new files contain no `sorry`. The eight
statements of the skeleton and the five auxiliary results depend only on
`[propext, Classical.choice, Quot.sound]` (`doc/batches/audits/axioms-batch114.txt`, from
`doc/batches/audits/Axioms114.lean`). OPEN.md item 2 is closed. `axioms.txt` was regenerated: 309
lines as before (two lines moved from the open groups to the Bing 1948 group), and `sorryAx` now
appears in **4** lines (`theorem3_end`, `theorem14`, `fugate_cor1`, `theorem15`), down from 6 as
the commission expects. `lake build HPC` succeeds (8332 jobs together with `HPCArchive` and
`HPCCensus`, which also build); its only `sorry` warnings are the three remaining open targets.
`theorem14`, `theorem3_end` and `fugate_cor1` were not attempted (§3.3).

The paper `lehner1961.pdf` did not come with this upload; the work follows the transcription in
§1 of the commission.

## 0. Files

* `HPC/PseudoArc/Lehner.lean` (from the skeleton). The eight statements of the skeleton, with the
  namespaces of the repository: `HPC.isPseudoArc_of_subcontinuum`,
  `HPC.not_mem_composant_of_irreducible`, `HPC.exists_epsChain_of_irreducible`,
  `HPC.Chain.IsConsolidationOf.trans`, `HPC.exists_description_consolidating`,
  `HPC.lehner_lemma3_two`, `HPC.Description.covering_step`,
  `HPC.Description.exists_description_covering` (the last two are the names printed by
  `Axioms.lean`; `CoveringStep` is `HPC.Description.CoveringStep`, unchanged, in `Theorem14.lean`).
* `HPC/PseudoArc/LehnerCore.lean` (new). The chain combinatorics of Lehner's proof, namespace
  `HPC.Lehner`: `exists_eq_of_lip` (discrete intermediate values on `Fin v`), `dist_le_of_near`
  (points of links at index distance `≤ 2` are `3δ`-close), `indices` (Lehner's `s_1, r_1, t_1,
  w_1, x_1, y_1, z_1`), `blocks` (the chain `D`), `core` (the two together).

Existing files edited: `HPC.lean` (`import HPC.PseudoArc.Lehner` at the end);
`HPC/PseudoArc/Theorem14.lean` (`covering_step` with its `-- OPEN` marker and
`exists_description_covering` deleted, a note left in their place, module doc updated; `theorem14`
stays, still `sorry`); `Axioms.lean` / `axioms.txt` (`covering_step` out of *Open targets*,
`exists_description_covering` out of *Consequences*, both into the Bing 1948 group under "Theorem
14: the covering step, by Lehner's Lemma 3 (n = 2) (batch 114)"); `OPEN.md` (item 2: "closed in
batch 114", other numbers unchanged; item 3 now notes that the covering description is proved).
`README.md` does not mention the covering step and was not edited. The commission is filed as
`doc/batches/COMMISSION-batch114.md`, the skeleton as `doc/batches/skeletons/Lehner.lean`, the
previous audit as `doc/batches/audits/axioms-before-batch114.txt`. The root file
`theorems-3-4-scheduling(20).md` (the current `doc/theorems-3-4-scheduling.md` plus new sections)
came with this upload but is not mentioned in the commission; it was left where it is.

## 1. Item 1 — proved

* `isPseudoArc_of_subcontinuum`: is `Plane.isPseudoArc_of_subcontinuum` (`PseudoArc51.lean`,
  batch 88), restated in namespace `HPC` as the skeleton asks.
* `not_mem_composant_of_irreducible`: a proper subcontinuum of `W` through `A` and `B` contradicts
  irreducibility. **Shape change:** the hypothesis `A ≠ B` is dropped (unused).
* `exists_epsChain_of_irreducible`: `W` is a pseudo-arc, its end points are in different
  composants of `W`, `Plane.exists_description_of_chainable_HI` gives a description of `W` from `P'`
  to `R`, and a level with mesh `< min(ε, dist(P', R))` is the chain (`two_le_n_of_lt` gives
  `m ≥ 2`). No link has to be removed: every link of every level meets the described continuum
  (`Description.link_inter_M_nonempty`, batch 81). **Shape change:** the conclusion also states
  that the links are bounded. In Mathlib an unbounded set has diameter `0`, so `diam < ε` alone
  does not bound a link, and boundedness is needed in item 2 to put the closure of a link in a
  ball.
* `Chain.IsConsolidationOf.trans`: refinements compose; a union of unions of links is a union of
  links.
* `exists_description_consolidating`: `exists_description_of_steps` with the property "is a
  consolidation of some level of `Δ`", carried from `Description.exists_step`. It is proved as
  stated, but item 2 does not use it, because it does not say that `k ≥ i`. `CoveringStep` needs
  `L < k`, and a consolidation of `D_k` is not in general a consolidation of a deeper level (see
  the ledger, (10)).

## 2. Item 2 — `lehner_lemma3_two`, proved

The statement is unchanged.

**The chains.** Fix `L`. Choose the following:
* `λ_L` is a Lebesgue number of `D_L` on the compact `M`;
* `η > 0` is such that `B(Q', η)` misses `W` (`Q' ∉ W` by `ne_M_and_not_mem`, batch 83);
* `ε = min(λ_L, η, 1/(L+1))/2`.

`E = E_1` comes from item 1 at mesh `ε`, and `λ_1` is a Lebesgue number of `E` on the compact `W`.
Then, with `L_1 ≥ L` and `3/(L_1+1) < λ_1`:
* `F` is the chain of `Description.exists_step` at level `L_1` (Theorem 13's step from `P'` to
  `Q'`). It is a consolidation of `D_{k_1}`, `k_1 > L_1`, has mesh `≤ 1/(L_1+1)`, and the closures
  of its links lie in links of `D_{L_1}`.
* `G` is the chain of `exists_step` at level `k_1 + 1`. It is a consolidation of `D_{k_2}`,
  `k_2 > k_1 + 1`, and the closures of its links lie in links of `D_{k_1+1}`.

`G` is crooked in `F`: `D_{k_1+1}` is crooked in `F` (Theorem 1,
`isCrookedIn'_of_isConsolidationOf`), and `G` refines `D_{k_1+1}` (Theorem 2,
`isCrookedIn'_of_refines`). So Lehner's `D_{j-1}`, `D_j` are two successive steps of Theorem 13,
and no second description is needed.

**`H_2` and `E_2` are not needed.** The covering step asks only for `D(P_1, Q_1) ⊇ H_1` and for a
chain to `Q'`. The last link of `G` already contains `Q'` and no other link of `G` does. So Lehner's
right-hand half (`H_2`, `E_2`, `t_2, s_2, r_2, w_2, x_2, y_2, z_2`, `E_1* ∩ E_2* = ∅`) is dropped.
The constructed chain is `[d_1, …, d_{m_1}]` followed by `g_{z_1+1}, …, g_v` unchanged.

**Indices** (`Lehner.indices`; 1-based as in Lehner, the Lean file is 0-based):
* `s_1` is the last link of `F` meeting `W`. The links meeting `W` are exactly `f_1, …, f_{s_1}`
  (`Chain.meet_ordConnected`, batch 86: `W` is connected and lies in `F*`, and `P' ∈ f_1`).
* **Window condition** (Lehner's "4-linked subchain … contained in a link of `E_1`"): every link
  of `F` within two links of a link meeting `W` lies in a link of `E`. This holds because points of
  such a link are within `3·mesh(F) < λ_1` of a point of `W` (`dist_le_of_near`).
* `f_1 ⊆ e_1` (it contains `P'`, which lies only in `e_1`). So `R ∉ f_1`, because `m_1 ≥ 2` and
  `R` lies only in `e_{m_1}`.
* `r_1` is a link of `F` containing `R`, with `2 ≤ r_1 ≤ s_1`. Any such link will do; Lehner's
  "last" is not needed.
* `t_1 := s_1 + 2`, used in place of Lehner's maximal `t_1`. Then `f_{t_1−1}` misses `W`. Every
  link up to `t_1` lies in a link of `E` by the window condition. `t_1 ≤ u` because otherwise
  `f_u ∋ Q'` would lie in a link of `E`, which meets `W` and has diameter `< ε < η`. So `Q' ∉ E*`.
  `t_1 > 3` since `s_1 ≥ r_1 ≥ 2`.
* `w_1` is the first link of `G` meeting `f_{t_1}`. Such a link exists: the minimal-containing-link
  index `μ` (`Refines.minIdx`) goes from `1` (at `g_1 ∋ P'`) to `u` (at `g_v ∋ Q'`) by steps of at
  most one, so some `g_l ⊆ f_{t_1}`.
* Crookedness of `G` in `F` is applied with `h = 1`, `k = t_1`, `i = 1` (`g_1` meets `f_1` at
  `P'`) and `j = w_1`. It gives `1 < x_1 < y_1 < w_1` with `g_{x_1} ⊆ f_{t_1−1}` and
  `g_{y_1} ⊆ f_2`.
* Before `w_1`, `μ < t_1`; otherwise `μ` reaches `t_1` earlier, and that link of `G` meets
  `f_{t_1}`. Hence every `g_l`, `l < w_1`, lies in a link of `E`.
* `μ(x_1) ≥ t_1 − 2 = s_1 ≥ r_1` and `μ(y_1) ≤ 2 ≤ r_1`. So some `z_1 ∈ [x_1, y_1]` has
  `μ(z_1) = r_1`, that is `g_{z_1} ⊆ f_{r_1} ⊆ e_{m_1}` (`f_{r_1}` lies in a link of `E` and
  contains `R`).
* The links of `G` meeting `W` precede `x_1`: otherwise `g_{x_1}` would meet `W` by the interval
  property, but `g_{x_1} ⊆ f_{s_1+1}`. Hence `W ⊆ G(1, x_1)* ⊆ G(1, z_1)*`.

**The chain `D`** (`Lehner.blocks`). Assign to each `g_l`, `l ≤ z_1`, a link `e_{γ(l)}` of `E`
containing it, with `γ(z_1) = m_1`. Any assignment changes by at most one between consecutive
`l`, since consecutive links of `G` meet. Then:
* `β(l) = γ(l)` for `l ≤ z_1`, and `β(l) = m_1 + (l − z_1)` after `z_1`;
* `β` is a schedule (`Chain.IsSchedule`), hence a block map (`IsSchedule.exists_blockMap`);
* `D = G.ofBlocks β` is a consolidation of `G`, hence of `D_{k_2}` (item 1, `trans`).

Its blocks `≤ m_1` lie in the links of `E` with the same index, and its later blocks are single
links of `G`. These facts give the following.
* **`IsFrom P' Q'`.** `P'` lies only in `g_1`, which has `β = 1`, and `Q'` lies only in `g_v`,
  which has the largest value of `β`.
* **`CoversUpTo`**, with `b = m_1`. `R` lies in some `g_l` with `l < x_1`, which has `γ(l) = m_1`.
  `R` is in no block `< m_1`, since such a block lies in `e_{<m_1}`. And `W ⊆ G(1, z_1)*` lies in
  the blocks `≤ m_1`.
* **Closures in links of `D_L`.** A block inside `e_i` has its closure in `B̄(y, diam e_i)` for a
  point `y ∈ e_i ∩ W ⊆ M`, and `B̄(y, diam e_i) ⊆ B(y, λ_L)`, which lies in a link of `D_L`. A block
  that is a link `g_l` has its closure in a link of `D_{k_1+1}`, inside a link of `D_L`.
* **Mesh `≤ 1/(L+1)`.** The first kind of block has mesh `< ε`, the second `≤ 1/(k_1+2)`.
* **`L < k_2`.**

## 3. Item 3 — proved

`covering_step` is `lehner_lemma3_two`, and `exists_description_covering` is
`exists_description_covering_of_step` (batch 83) applied to it. Both statements are unchanged from
`Theorem14.lean`. They were moved and audited as described in §0.

## 4. Ledger of Lehner's proof (p. 376)

Each place where the one page needs a fact it does not state, or where the formalization departs
from it:

1. **The two-link ambiguity.** A link of `G` may lie in two adjacent links of `F`, or of `E_1`.
   * For `F`, the index used is the *minimal* containing link (`minIdx`). It moves by at most one
     because consecutive links of `G` meet. This makes "`g_{z_1}` lies in `f_{r_1}`" a discrete
     intermediate value statement.
   * For `E_1`, *any* choice moves by at most one, for the same reason. The only constraint is
     `γ(z_1) = m_1`, which is forced by `g_{z_1} ⊆ e(1)_{m_1}`. The assignment at `l = 1` is forced
     too, because `P'` lies only in `e(1)_1`.
2. **`y_1 > x_1` strict.** The repository's `Between` is strict, so this comes for free. (The
   commission's worry was the other way round.)
3. **`m_1 ≥ 2`.** This comes from item 1, using a level of mesh `< dist(P', R)`. It is used to get
   `R ∉ e(1)_1 ⊇ f_1`, hence `r_1 ≥ 2` and `t_1 > 3`, which crookedness needs. Lehner's `5 ≤ r_1`
   is not needed.
4. **The closure condition.** Lehner's "any link of `D_i` that contains a link of `D_{i+1}` also
   contains its closure" is not used. The closures asked by `CoveringStep` come from the Lebesgue
   number of `D_L` on `M` (for blocks inside links of `E_1`) and from `exists_step` (for links of
   `G`). The repository's `Chain` has no closure clause, and none is needed.
5. **The Lebesgue condition.** Lehner asks that any 4-linked subchain of `F` one of whose links
   meets `H_1` lies in a link of `E_1`. What is used is that every link of `F` within two links of
   a link meeting `H_1` lies in a link of `E_1` (3 links, `3·mesh(F) < λ_1`). With it, `t_1 = s_1 +
   2` replaces Lehner's maximal `t_1`. Only the links up to `t_1 − 1` need to lie in links of
   `E_1`.
6. **`t_1` is a link of `F`.** This needs `Q' ∉ E_1*`, which is arranged by `ε < dist(Q', H_1)`.
   Lehner gets it from `E_1* ∩ E_2* = ∅` and `Q' = Q_2 ∈ E_2*`.
7. **"The first link of `G` to intersect `f_{t_1}`" exists.** This follows from discrete
   intermediate values along `G`, from `g_1 ⊆ f_1` to `g_v ⊆ f_u`. `g_1 ⊆ f_1` is not stated
   either; it holds because `P'` lies only in `f_1`.
8. **`H_1 ⊆ G(1, x_1)*`.** This uses that the links meeting a connected subset of a chain's union
   form an interval (`meet_ordConnected`), together with `H_1 ⊆ G*` (the levels cover `M`).
9. **`H_2`, `E_2`, Theorem 2 for `H_2`, `E_1* ∩ E_2* = ∅`.** None of these is needed for
   `CoveringStep` (§2).
10. **Theorem 3's sequence `D_1, D_2, …`.** This is replaced by two steps of Theorem 13
    (`exists_step`) and Theorems 1 and 2 for crookedness. A description whose levels are
    consolidations of levels of `Δ` (`exists_description_consolidating`, as stated) would not do
    by itself. `CoveringStep` needs `L < k`, the statement gives no lower bound on `k`, and a
    consolidation of `D_k` is not a consolidation of `D_{k'}` for `k' > k` in general.
11. **The closure clause of Lehner's chains** (closures of non-adjacent links disjoint) is not used
    anywhere.
