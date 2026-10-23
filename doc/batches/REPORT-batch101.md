Commission read: `COMMISSION-batch101.md` (batch 101: Fugate 1966 — Lemma 2 corrected, Miller's theorem, Lemma 4, Theorem 1 (sufficiency), Corollary 1). Its skeleton `Fugate66B.lean` is saved as `HPC/Plane/Fugate66B.lean` (with the shape changes below), and `import HPC.Plane.Fugate66B` is added at the end of `HPC.lean`. No existing file was edited.

# Report, batch 101

## Summary

**Refutation first.**

* **`miller_1_5` is false as transcribed (item 2).** This is proved in Lean as `miller_1_5_false`
  (`HPC/Plane/Fugate66BMiller.lean`), using the two-half-disk example the commission suggested. Take
  the closed unit disk `Disk` of `ℂ`, with `A` the closed upper half (`im ≥ 0`) and `B` the closed
  lower half (`im ≤ 0`). Both are continua, and `A ∪ B` is the whole disk. The disk is unicoherent
  (`isUnicoherent_disk`). The boundary circle `D` is a subcontinuum that is not unicoherent: it is
  the union of its two closed semicircles, which meet in `{1, −1}`. And `D` lies in neither half.
  The statement is commented out in `Fugate66B.lean`, with this explanation.
  * Unicoherence of the disk is proved in general, as `isUnicoherent_univ_of_contraction`: a
    connected metric space that an explicit homotopy contracts to a point is unicoherent. Suppose
    `X = H ∪ K` with `H ∩ K = P ⊔ Q`. Take an Urysohn function `φ` (`0` on `P`, `1` on `Q`), and the
    map equal to `exp(2πiφ)` on `H` and to `1` on `K`. It has a continuous logarithm, by homotopy
    lifting for the covering `exp` (Mathlib's `IsCoveringMap.liftHomotopy`). On `K` the
    logarithm's `Im/2π` is integer-valued, and on `H` so is `Im/2π − φ`. Both are therefore
    constant, which is impossible at `p ∈ P`, `q ∈ Q`.
  * **The hypothesis that restores the conclusion** is that `A` and `B` are hereditarily
    unicoherent (`miller_1_5_of_hu`). Under it there is no non-unicoherent `D` at all, because
    `A ∪ B` is then hereditarily unicoherent (next point). Miller's paper was not available, so
    whether this is his hypothesis cannot be checked. It is the one Fugate's application supplies,
    since snake-like continua are hereditarily unicoherent.

**Proved.** Every item below uses only `propext`, `Classical.choice` and `Quot.sound`
(`axioms-batch101.txt`):

1. **Lemma 2, corrected** (`fugate_lemma2'`), together with a taut form (`fugate_lemma2'_taut`).
2. **What Theorem 1 needs from Miller** (`hu_union_of_snakeLike`), proved directly and more
   generally (`isHereditarilyUnicoherent_union`): two hereditarily unicoherent continua with
   connected intersection have a hereditarily unicoherent union. **This resolves the circularity
   the commission names**; see item 2.
3. **Lemma 4** (`fugate_lemma4`, the skeleton's chain form). A ℕ-indexed form
   (`fugate_lemma4_weak`) carries all of Lemma 4's data.
4. **Theorem 1, sufficiency, under Fugate's own hypotheses** (`fugate_theorem1_sufficiency'`:
   `A ∪ B` atriodic and unicoherent). Also proved: the separately named form with
   `IsHereditarilyUnicoherent (A ∪ B)` (`fugate_theorem1_sufficiency_hu`), and **Theorem 1 as an
   iff** (`fugate_theorem1'`).
5. **Corollary 1** (`fugate_cor1'`, plus the iff `fugate_cor1_iff`) under the hypothesis that the
   whole union is hereditarily unicoherent. With Theorem 1 closed, **Corollary 2** also follows
   (`fugate_cor2'`).

**Still open, not attempted per §3:** `exists_irreducibleBetween_of_atriodic` (Sorgenfrey's
theorem). Batch 100's Lemma 3 (⇒) still depends on it.

**Batch 100's `sorry`s.** As the skeleton prescribes, batch 100's `fugate_theorem1_sufficiency`,
`fugate_theorem1`, `fugate_cor1` and `fugate_cor2` in `Fugate66.lean` keep their `sorry`. The new
files import `Fugate66.lean`, so they cannot be imported back into it. Their closed replacements are
`fugate_theorem1_sufficiency'`, `fugate_theorem1'`, `fugate_cor1'`/`fugate_cor1_iff` and
`fugate_cor2'`. During the pruning pass, the old bodies can be replaced by these.

**Files.**
* `HPC/Plane/Fugate66B.lean`: the skeleton's statements, with proofs.
* `HPC/Plane/Fugate66BLemma2.lean`: Definition 5 (`ContainedExactly'`, moved here so that the later
  files can use it) and Lemma 2.
* `HPC/Plane/Fugate66BHU.lean`: hereditary unicoherence of unions, and Moore's separation theorem
  for two closed sets.
* `HPC/Plane/Fugate66BLemma4.lean`: Lemma 4 in ℕ-indexed form.
* `HPC/Plane/Fugate66BThm1.lean`: Theorem 1, sufficiency.
* `HPC/Plane/Fugate66BMiller.lean`: the refutation.
* `Axioms101.lean` / `axioms-batch101.txt`: the axiom checks.

`lake build HPC` succeeds. The new files contain no `sorry`.

## Shape changes (all recorded in the files)

* **`ContainedExactly'`.** Clause (2) is stated as Fugate states it: `A` lies in no proper subchain
  of `F(j..k)`. Concretely, `A` has a point of `F_j` in no other link of `F(j..k)`, and a point of
  `F_k` in no other link of `F(j..k)`. The skeleton's gloss "equivalently `A` meets `F_j` and
  `F_k`" is weaker, since it allows `A ⊆ F*(j..k−1)`. It also does not give what Theorem 1 uses: a
  point `c ∈ A ∩ B` in `E_m` and in no other link of `E(j,m)`. Without that point, Fugate's index
  `r` need not exist and Claim 3's "`A ∩ B ⊄ M`" fails. The skeleton's `by omega` index proofs
  inside a conjunction did not elaborate (the bounds were not in scope), so the bounds are now
  existential binders. The definition moved to `Fugate66BLemma2.lean`.
* **`fugate_lemma4`.** The index bounds in clause (6) are binders,
  `∀ (hk : 1 ≤ k) (hkn : k < n), ∃ htm : t < m, j ≤ t ∧ …`, for the same elaboration reason. The
  unused hypothesis `(A ∩ B).Nonempty` is removed, since terminality already includes it.
* **`hu_union_of_snakeLike`.** The unused hypothesis `(A ∩ B).Nonempty` is removed, since
  unicoherence of `A ∪ B` makes `A ∩ B` a continuum.
* **`miller_1_5`.** Commented out, because it is false. `miller_1_5_false` is the formal negation
  (for spaces in `Type`), and `miller_1_5_of_hu` is the corrected form.
* **`fugate_theorem1_sufficiency'`, `fugate_cor1'`.** As in the skeleton.

## Items

### Item 1 — Lemma 2 corrected: **proved**

`fugate_lemma2'` proves Definition 5 in full. Start from batch 100's `fugate_lemma1`, which gives a
chain `G` refining `E` whose last link contains a point `x₁ ∈ A` lying in the closure of no other
link. Then `exists_containedExactly_last` runs batch 100's construction:
* take the largest `s` with `A ⊆ G*(s..)`;
* remove a closed neighbourhood of `A` from the earlier links;
* trim.

The last link meets `A`, so it survives the trimming. That makes the segment final and the
`k`-witness `x₁`. The `j`-witness is a point of `A` in `G_s` and in no later link, which exists by
maximality of `s`.

* **Gap in Fugate's text.** Fugate's cut chain (`G_i = F_i ∩ W` for `i ≤ s−1`) is called a chain,
  but `F_{s−1} ∩ W` may fail to meet `F_s`, and early links may become empty. Trimming
  (`exists_chain_of_weak`) repairs this: the links meeting `M` form a run, which is a chain.
* **Hypotheses.** Atriodicity and hereditary unicoherence are not used, as in batch 100.
* **Clause (3).** Fugate's "if `E` is taut so is `G`" is replaced by the stronger "`G` is taut"
  (`fugate_lemma2'_taut`). Every chain is shrunk to a taut one (`exists_taut_shrink`): closures of
  the new links lie in the old ones, and prescribed points (the two witnesses of Definition 5 (2))
  are kept.

### Item 2 — Miller's theorem: `miller_1_5` **refuted**; `hu_union_of_snakeLike` **proved**

The refutation is in the summary.

`isHereditarilyUnicoherent_union`: if `A`, `B` are hereditarily unicoherent continua and `A ∩ B`
is connected, then `A ∪ B` is hereditarily unicoherent. **The circularity the commission names**
(Claim 1-style reasoning needs `D` to be hereditarily unicoherent) **is avoided by Moore's
separation theorem**, as follows.

* **Key step** (`isPreconnected_inter_of_hu`, needing only that `B` is hereditarily unicoherent).
  Every subcontinuum `H` of `A ∪ B` meets `A` in a connected set.
  * Suppose `H ∩ A = P ⊔ Q`, with `P` and `Q` closed.
  * No connected subset of `H ∩ B` meets both `P ∩ B` and `Q ∩ B`. Its closure would meet the
    continuum `A ∩ B` of `B` in a connected set (since `B` is hereditarily unicoherent), and that
    set lies in `P ⊔ Q` and meets both.
  * Moore's theorem (`exists_closed_split_of_no_connected`) therefore splits `H ∩ B = H₁ ⊔ L₁`
    with `P ∩ B ⊆ H₁` and `Q ∩ B ⊆ L₁`.
  * Then `H = (P ∪ H₁) ⊔ (Q ∪ L₁)`, so `H` is not connected, a contradiction.
* **The union.** Let `H`, `L` be subcontinua of `A ∪ B`. By the key step, `H ∩ L ∩ A` and
  `H ∩ L ∩ B` are connected. Suppose they were disjoint. Then `(H ∩ A) ∪ (L ∩ A)` (a continuum in
  `A`) would meet the continuum `A ∩ B` in the two disjoint nonempty closed sets `H ∩ A ∩ B` and
  `L ∩ A ∩ B`. This contradicts hereditary unicoherence of `A`.

`hu_union_of_snakeLike` follows because snake-like continua are hereditarily unicoherent, and
unicoherence of `A ∪ B` makes `A ∩ B` connected.

### Item 3 — Lemma 4: **proved**

`fugate_lemma4_weak` follows Fugate's construction:
* `G` from `fugate_lemma2'_taut`;
* a Lebesgue number `δ` for the cover of `A ∩ B` by `G_j − Cl G*(0..j−1), G_{j+1}, …`;
* `H` a taut `ε''`-chain of `B`, with `ε'' = min(ε, δ)/2`;
* disjoint open sets `S ⊇ A − B` and `T ⊇ B − A`, by complete normality (Mathlib's
  `completely_normal`);
* the cuts `F_i = H_i ∩ T` (`i < k`), `E_i = G_i ∩ S` (`i < j`), `E_i = G_i − Cl F*(0..k−1)`
  (`i ≥ j`, `i ≠ t`), and `E_t = G_t − Cl F*(0..k−2)`.

Its output is two finite ℕ-indexed families of open sets with all of Lemma 4's data (structure
`Fit`). Tautness is stated as disjointness of nonadjacent closures. `fugate_lemma4` trims both
families to chains:
* the links meeting `A` form a run containing `E_j, …, E_{m−1}`, because `E_j` and `E_{m−1}`
  contain the two witnesses of Definition 5;
* likewise for `F` and `B`;
* so only initial segments are dropped, and every clause survives the shift of indices.

**`k = 0`** (`A ∩ B` reaching the first link of `F`). Clause (6) is then vacuous. It cannot happen
once `B ⊄ A` and `ε < dist(b, A ∩ B)` for some `b ∈ B − A`, because every link of `F(k..n−1)` meets
`A ∩ B`. Theorem 1 does not need this: when `k = 0` it uses `B ⊆ F* ⊆ E*`, by clause (3).

Where Fugate's text needs more than it says:
* **"`E_i = G_i − Cl F*(1,k−1)` still meets `E_{i+1}`."** Not shown, and not true in general; the
  same goes for the `G_i ∩ S`. So `E` and `F` need not be chains before trimming. This is harmless
  because the proof of Theorem 1 uses only that nonadjacent links are disjoint (weak chains).
* **"The cut links still cover `A`."** True but unstated: `Cl F*(0..k−1) ∩ A = ∅`. The reason is
  that `Cl T ∩ (A − B) = ∅` (as `S` is open and disjoint from `T`) and
  `Cl H*(0..k−1) ∩ (A ∩ B) = ∅` (exactness of `H`). Similarly `B ⊆ F*`, because a point of `B` in
  `H_i` with `i < k` lies outside `A`, hence in `T`.
* **The Lebesgue-number step.** Fugate's "closure of each link of `H₁` meeting `A ∩ B` lies in a
  link of `G(j,m)`" needs the metric form of the Lebesgue lemma (balls of radius `δ` about points
  of `A ∩ B`), not a Lebesgue number for subsets of `A ∩ B`. It is applied to the links of the
  refined `H(k..n−1)`. That each of these meets `A ∩ B` follows from exact containment:
  `A ∩ B` is connected and meets `H_k` and `H_{n−1}`. Fugate's `b` (the least distance between
  nonadjacent links of `G`) is not needed. `t` can be any index `≥ j` with `Cl H_k ⊆ G_t`.

### Item 4 — Theorem 1, sufficiency: **proved**

`fugate_theorem1_sufficiency_hu` first disposes of the trivial cases `B ⊆ A` and `A ⊆ B`. It then
uses Claim 1 (batch 100's `inter_isTerminalSub_of_union`) and the data of Lemma 4, and builds a
**weak** `ε`-chain covering `A ∪ B`: open sets of diameter `< ε` whose nonadjacent members are
disjoint. `isSnakeLike_of_weak` turns it into a chain by trimming. There are three cases.

* **`k = 0`:** `E` itself.
* **Case i** (`Cl F_{k−1}` meets no `E_i` with `i < m−1`): `E ⊕ F(k−1..0)`.
* **Case ii** (otherwise). Then `t < m−1` and `Cl F_{k−1} ∩ E_{m−1} = ∅`, by clause (6). The chain
  is Fugate's `𝒢 = E(0..j−1) ⊕ E(j..m−2) ∩ S ⊕ E'_{m−1} ⊕ F(r−1..k) ∩ T ⊕ (F_{k−1} ∩ T) ∪ (F_{k−1} − Cl E*) ⊕ F(k−2..0)`,
  where:
  * `r` is the least index `≥ k` with `Cl F_r ⊄ E*(j..m−2)`. It exists by the witness point of
    Definition 5 (2), and `Cl F_r ⊆ E_{m−1}`;
  * `E'_{m−1} = E_{m−1} − Cl F*(k..r−2)`;
  * `D = (A ∪ B) ∩ (Cl E*(j..m−2) − E'_{m−1})`;
  * `S` and `T` are thickenings of the two closed pieces of `D` given by Claim 3 and Moore's
    theorem.

  Covering and the nonadjacency check are verified link by link.

Where Fugate's text needs more than it says:
* **"For notational convenience assume `E' = E`."** This is not a re-run of Lemma 4. `E'` is used
  directly, and only the following is needed:
  * `E'_{m−1}` misses `Cl F_l` for `k ≤ l ≤ r−2` (by definition);
  * `F_r ⊆ E'_{m−1}` (by tautness of `F`);
  * the witness `c ∈ A ∩ B` lies in `E'_{m−1}`;
  * points of `E_{m−1} − E'_{m−1}` lie in `E*(j..m−2)` (by minimality of `r`), so `E'` still
    covers `A` and `B ∩ F*(k..n−1)`.

  `E(0..m−2) ⊕ E'_{m−1}` need not be a chain (`E'_{m−1}` may lose its overlap with `E_{m−2}`), so
  "`E'` has (1)–(6)" holds only in the weak sense, which is all that is used.
* **"`r ≥ k+1`."** Not needed: Claim 3's final step works for `r = k` too.
* **Claim 2** is the case of Claim 3 where the continuum is a single point, so it is not proved
  separately.
* **Claim 3.** Fugate says that `A ∩ B`, `A ∩ M`, `B ∩ M` are continua and that none lies in the
  union of the other two.
  * They are continua because `A ∪ B` is hereditarily unicoherent (now proved, item 2).
  * `A ∩ B ⊄ M` holds because the witness `c ∈ A ∩ B` lies in `E'_{m−1}`, which `D ⊇ M` misses.
    Fugate does not say this.
  * The triod comes from the corrected Sorgenfrey lemma (batch 100's `isTriod_union_of_three`,
    which needs a hereditarily unicoherent union).
* **"Moore, Theorem 44."** Proved for two closed sets in a compact set
  (`exists_closed_split_of_no_connected`, from batch 91's `exists_clopen_split`).
* **"Hence `𝒢` is a chain."** Fugate checks only that nonadjacent links are disjoint; that adjacent
  links meet is not shown. This is handled by trimming: the links meeting `A ∪ B` form a run that
  is a chain.
* **Case `k = 0`.** Not discussed by Fugate; it is trivial.

`fugate_theorem1_sufficiency'` (Fugate's hypotheses: atriodic and unicoherent) follows, with
hereditary unicoherence supplied by `hu_union_of_snakeLike`. So does `fugate_theorem1'` (the iff).

### Item 5 — Corollary 1: **proved, under hereditary unicoherence of the union**

`fugate_cor1'` uses **the skeleton's hypothesis**: `⋃ A_i` atriodic and hereditarily unicoherent.
The proof is an induction through `fugate_theorem1_sufficiency_hu`. Each partial union
`A_0 ∪ … ∪ A_i` inherits atriodicity and hereditary unicoherence, and it meets `A_{i+1}` (in
`A_i ∩ A_{i+1}`). `fugate_cor1_iff` gives both directions: snake-like iff atriodic, under the
hereditary unicoherence hypothesis.

**Fugate's weaker hypothesis** (the union unicoherent) **is not reached.** The two-piece reduction
`hu_union_of_snakeLike` needs each partial union to meet the next piece in a connected set, and
unicoherence of the whole union does not obviously give that. This is recorded, not refuted.

**Corollary 2** (`fugate_cor2'`) is batch 100's `fugate_cor2_of_theorem1`, with Theorem 1 now
supplied.

## Not attempted (§3)

`covering_step`, `theorem14` (1948), `theorem3_end`, `exists_tame_chain_near`,
`isArc_of_separatesPairs`, `exists_degenerate_interior_elt`, `theorem11_1951_of_T10'`,
`exists_irreducibleBetween_of_atriodic`.
