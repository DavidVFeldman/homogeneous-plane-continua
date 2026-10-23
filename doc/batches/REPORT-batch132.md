Commission read: COMMISSION-batch132.md (batch 132 — Fugate's Corollary 1: the last `sorry`; Part I, Corollary 1 under (∗); Part II, (∗) from Ingram 1968).

# Report, batch 132

**Outcome.** Nothing refuted. `fugate_cor1` (Fugate 1966, Corollary 1, as stated, every clause) is
**proved**, and so is (U) (`fugateU_holds`). Part I is proved as commissioned. In Part II, (∗)
(`ingramStar_holds`) is proved by the **direct route** of §2 ("Alternative route"), through
Ingram's Lemmas 1 and 2. It does not go through his Theorem 2(2) and circle-likeness. Nadler 12.51
is also proved. Sorgenfrey 1.8 and Ingram's Lemma 3 are **open**; Ingram's Theorems 1 and 2(2) were
**not attempted**, because the direct route replaces them. None of these four is needed.

Build: `lake build HPC` succeeds. `HPC.lean` ends with `import HPC.Plane.Fugate66Cor1Proof` and
`import HPC.Plane.Ingram68`. No declaration of the main build uses `sorry`. `axioms.txt` has been
regenerated: 675 lines (629 before, 47 new in the batch-132 group, and the former open-target line
`fugate_cor1` moved into that group). **`sorryAx` occurs in no line.** Every line shows
`[propext, Classical.choice, Quot.sound]` or a subset of it. The previous `axioms.txt` is saved
as `doc/batches/audits/axioms-before-batch132.txt`. The per-batch audit
`doc/batches/audits/axioms-batch132.{lean,txt}` covers all 47 theorems of the four new files.

## Layout

| file | contents |
|---|---|
| `HPC/Plane/Fugate66Cor1Proof.lean` | Part I (the skeleton, every `sorry` proved) |
| `HPC/Plane/Ingram68Core.lean` | Part II: core lemma, Ingram's Lemmas 1 and 2, (∗∗) |
| `HPC/Plane/Ingram68Star.lean` | Part II: (∗) |
| `HPC/Plane/Ingram68.lean` | the Part II skeleton: circle-like definitions, Nadler 12.51, `fugate_cor1`, `fugateU_holds`; the unproved skeleton items commented out verbatim, with the obstruction |

The skeleton was split into these files for size. The uploads are kept as
`doc/batches/skeletons/{Fugate66Cor1Proof,Ingram68}-batch132.lean`. The hand proof is
`doc/notes/fugate-cor1-proof.md`, Ingram's paper `doc/sources/ingram1968.pdf`, and the commission
`doc/batches/COMMISSION-batch132.md`.

## Part I — Corollary 1 under (∗)

| item | verdict |
|---|---|
| 1. `exists_split_of_not_isConnected`, `not_isUnicoherent_of_split` | **proved** as stated (plus `not_isPreconnected_of_split`) |
| 2. `subset_of_unicoherent_absorb` | **proved** as stated, through `subset_of_unicoherent_absorb'`, which assumes only (∗∗) for `Y ∪ A` (below) |
| 3. `isHereditarilyUnicoherent_partial` | **proved**; the hypothesis `hp : p ≤ k` was unused and is removed (for `p ≥ k` the partial union is the whole union) |
| 4. `fugateCor1Sufficiency_of_ingramStar` | **proved**, through `fugateCor1Sufficiency_of_ingramStarWeak` |
| 5. `fugate_cor1_of_ingramStar`, `fugateU_of_ingramStar` | **proved** with the given bodies |

**Shape changes.**
* *(∗∗).* `IngramStarWeak` is new: if `P ⊆ Y` and `Q ⊆ A` are continua meeting in a nonempty
  disconnected set, then `P ∪ Q = Y ∪ A`. It is the only consequence of (∗) that Steps 4–5 use.
  (∗) implies it (`ingramStarWeak_of_ingramStar`), and Part II proves it directly first
  (`ingramStarWeak_holds`).
* *Re-indexing.* The tail `A_{p+1}, …, A_k` is not re-indexed as a `Fin (k − p)`-chain. Instead,
  the induction runs over the interval unions `chainUnion A a b = A_a ∪ ⋯ ∪ A_b` of an `ℕ`-indexed
  chain (`isSnakeLike_chainUnion_of_ingramStarWeak`, strong induction on `b − a`). `finChainExt`
  translates between the two forms. In the final step the tail union equals the whole union, so the
  induction hypothesis gives chainability of `X` directly, and no separate contradiction is needed.

**Refutation candidates (the hand proof).** None refuted. The hand proof has **no error**:
* `M₁ ∩ M₂ = Y ∩ A`: holds, since `M₁ ∩ M₂ = (Y ∩ A) ∪ (Y ∩ A ∩ B)`.
* `H` and `K` both meet `B`: holds. If `H ∩ B = ∅`, then `M₁ = Y ∩ (A ∪ B)` splits into `H` and
  `K ∪ (Y ∩ B)`.
* The case `p = k`: excluded, because `U_k = X` is unicoherent.
* The re-indexing: replaced by interval unions, as above.

## Part II — (∗) from Ingram 1968

| item | verdict |
|---|---|
| 1. `cycDist`, `CircChain`, `IsCircEpsChain`, `IsCircleLike` | definitions, kept as in the skeleton |
| 1. `isSnakeLike_of_subset_circleLike` (Nadler 12.51) | **proved** as stated. The proof drops the link through `x ∉ Z` (its diameter is below `infDist x Z`) and reads the other links cyclically from the next index. Two of them meet iff their indices differ by at most 1, because index differences are at most `n − 2`. `CompactSpace` is not needed. |
| 2. `exists_isTriod_of_isWeakTriod`, `not_three_of_isAtriodic` (Sorgenfrey 1.8) | **open** (commented out). Not refuted; the obstruction is below. Not needed. |
| 3. `ingram_lemma1` | **proved**, in the used form of the skeleton. Ingram's appeal to Sorgenfrey is replaced by `not_isAtriodic_of_three` (core `A`). |
| 3. `ingram_lemma2` | **proved**. Shape change: the hypothesis `hAhu : IsHereditarilyUnicoherent A` is added, and it is used only for terminality. Irreducibility needs no extra hypothesis and is proved in the more general form `eq_of_subset_of_split` (`H`, `K` only closed). In the application `A` is snake-like. |
| 3. `ingram_lemma3` | **open** (commented out). The obstruction is below. Not needed. |
| 4. `ingram_theorem1` | **not attempted** (direct route) |
| 5. `ingram_theorem2_circleLike` | **not attempted** (direct route) |
| 6. `ingramStar_holds`, `fugate_cor1`, `fugateU_holds` | **proved**. `fugate_cor1` and `fugateU_holds` use the given bodies. |

**Route taken: direct.**
1. *Core lemma* (`isTriod_of_core`). Let `N` be a continuum and `X₁, X₂, X₃` continua that meet `N`,
   pairwise meet only inside `N`, and do not lie in `N`. Then `N ∪ X₁ ∪ X₂ ∪ X₃` is a triod. This
   lemma replaces every appeal Ingram makes to Sorgenfrey in Lemmas 1–2. His "component of
   `B − (B ∩ D)`" becomes an arm obtained by boundary bumping (`exists_arm`).
2. *(∗∗)* (`ingramStarWeak_holds`). Lemma 1 gives `Y ∩ A = H ⊔ K`. Hereditary unicoherence of `Y`
   and of `A` makes `P ∩ Q` meet both `H` and `K`. Lemma 2 (irreducibility) gives `P ∪ H ∪ K = Y`
   and `Q ∪ H ∪ K = A`. A point of `H ∖ (P ∪ Q)` would give a triod with core
   `(H ∩ P') ∪ (H ∩ Q')`.
3. *(∗)* (`ingramStar_holds`). Let `M ⊊ Y ∪ A` and `z ∉ M`.
   * `z ∈ Y ∖ A`: by irreducibility no subcontinuum of `Y ∖ O` (`O` a ball about `z`) meets both
     `H` and `K`, so the cut-wire theorem splits `Y ∖ O`. Then `M` lies in the hereditarily
     unicoherent continuum `C_H ∪ A ∪ C_K` (`isUnicoherent_of_not_mem_diff`).
   * `z ∈ H` with `A ∖ Y ⊆ M`: terminality of `H` in `A` replaces `A` by a subcontinuum `A*`
     missing `z` with `Y ∪ A* = Y ∪ A`, and the first case applies (`isUnicoherent_of_not_mem_piece`).

**Obstructions (open items, not needed).**
* *Sorgenfrey 1.8.* The core lemma needs one continuum that contains the three pairwise
  intersections and none of the three continua. For a general weak triod, which need not be
  unicoherent, no such continuum is available. The textbook ball construction was not formalized.
  In the hereditarily unicoherent case the repository already has `isTriod_union_of_three`.
  Checked: the form with a *common point* is the right one. The θ-curve (LEDGER) is a weak triod
  that is not a triod but contains one.
* *Lemma 3.* Ingram's reduction gives `H ∩ A = L₁ ⊔ L₂`, both meeting `K`, with `L₁ ⊄ K`.
  * If also `L₂ ⊄ K`, the configuration is a triod with core `K`: the arms are `L₁`, `L₂`, and an
    arm of `B` at `K` that misses `L`.
  * If `L₂ ⊆ K`, Ingram needs a triod in `K ∪ L₁ ∪ (H ∩ B)`. The only candidate core,
    `K ∩ H = (K ∩ L₁) ⊔ L₂`, is disconnected, so this is Sorgenfrey's theorem in a non-unicoherent
    configuration.

## Defects

* **Ingram 1968.** No false step found in Lemmas 1–3.
  * Every appeal to Sorgenfrey was checked: the three continua have a common point, and none lies
    in the union of the other two.
  * The two steps of Lemma 3 flagged in §3.4 are correct. "Since `M₂` is a subcontinuum of `A`":
    `M₂ ⊆ H ∩ A = L₁ ⊔ L₂` is connected and meets `L₁`. Case 2: `L₁ ∩ (H ∩ B) ⊆ L₁ ∩ K = ∅`.
  * In the formalization, terminality in Lemma 2 needs the core `(H ∪ L₁) ∩ (H ∪ L₂)` to be a
    continuum, which holds when `A` is hereditarily unicoherent. Hence the added hypothesis. This
    is a gap in the replacement, not a defect in Ingram's proof, which instead uses Sorgenfrey.
  * Theorems 1 and 2(2) were not checked.
  * Recorded in `LEDGER.md`.
* **Hand proof (`fugate-cor1-proof.md`).** No error. The only change is the bookkeeping of the
  re-indexing, as above.

## Edits to existing files

1. `HPC/Plane/Fugate66.lean`: the sorried `fugate_cor1` and its docstring are deleted, and a
   one-line comment points to `HPC/Plane/Ingram68.lean`.
2. `Axioms.lean`: new group "Fugate's Corollary 1: Part I (Corollary 1 under (∗)); Part II (Ingram
   1968; (∗)); `fugate_cor1` proved (batch 132)". It lists every new theorem, with `fugate_cor1` and
   `fugateU_holds`. The group *Open targets* is now empty. `axioms.txt` has been regenerated.
3. `OPEN.md`: item 1 is closed (moved to the table of closed items, noting the direct route). The
   skeleton items that were not formalized are listed. "Not attempted: `treeLike_nonseparating`"
   is unchanged.
4. `LEDGER.md`: the Corollary 1 row is rewritten. New rows: the introduction versus Theorem 1
   mismatch, and Ingram's appeals to Sorgenfrey.
5. `README.md`: the Fugate 1966 line ("every numbered statement proved"), a line for Ingram 1968,
   Ingram 1968 under `doc/sources/`, and the batch count 132.

## Final count

`sorryAx`: **0 lines** in `axioms.txt` (675 lines).
