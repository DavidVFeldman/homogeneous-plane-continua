# Commission: batch 132 — Fugate's Corollary 1: the last `sorry`

**Go!** This is a long run with two parts. It runs on top of the batch-131 delivery.

Five files accompany this commission as separate uploads, not an archive:

* `COMMISSION-batch132.md` — this text (also pasted into the prompt);
* `Fugate66Cor1Proof.lean` — the Part I skeleton. Save it as `HPC/Plane/Fugate66Cor1Proof.lean`.
* `Ingram68.lean` — the Part II skeleton. Save it as `HPC/Plane/Ingram68.lean`.
* `fugate-cor1-proof.md` — my hand proof of Corollary 1 from Theorem 1 and (∗). Save it as
  `doc/notes/fugate-cor1-proof.md`.
* `fm63115.pdf` — Ingram, *Decomposable circle-like continua*, Fund. Math. 63 (1968), 193–198.
  Save it as `doc/sources/ingram1968.pdf`.

Add `import HPC.Plane.Fugate66Cor1Proof` and then `import HPC.Plane.Ingram68` at the end of the
root `HPC.lean`. Shapes may be adjusted, with each change recorded.

The report names the commission read in its first line. Each item is reported as *proved*,
*refuted*, or *open with the obstruction stated*.

**Priority.** Part I first. It is self-contained: (∗) is a hypothesis, and only repository
material is needed. If Part II does not close, Part I still lands. In that case leave
`fugate_cor1` in `Fugate66.lean` untouched and report how far Part II got.

## 0. On batch 131

Audited and accepted: `PlaneFacts` discharged (`planeFacts_holds`), and Duke Theorems 6–7
unconditional. 629 declarations, `sorryAx` in one line, root tidy.

Since then a literature check has been done on Fugate's Corollary 1, which Fugate states without
proof. Nothing turned up that proves, refutes or discusses it for more than two pieces. Sources
checked:
* both reviews (MR0196720, Zbl 0139.40701);
* Fugate 1969;
* Bennett–Fugate 1977;
* Nadler 1992;
* Macías 2005;
* the Houston Problem Book;
* the citing papers of Gordh 1973, Ingram 1968 and Alhassan 2020.

Fugate's Theorem 1 *as printed* says "a-triodic and unicoherent", as `fugate_theorem1` does. His
introduction and the MR review say "hereditarily unicoherent". This mismatch is to be recorded
as a ledger line (edit 4).

## 1. Part I — Corollary 1 under (∗) (`Fugate66Cor1Proof.lean`)

The argument is in `fugate-cor1-proof.md` and in the skeleton header. Items:

1. `exists_split_of_not_isConnected`, `not_isUnicoherent_of_split` (small general facts).
2. **`subset_of_unicoherent_absorb`** — the heart of the proof (Steps 3–5). It uses no
   chainability and no atriodicity: only unicoherence of `Y ∪ A ∪ B` on four decompositions,
   plus (∗) for `Y ∪ A`.
3. `isHereditarilyUnicoherent_partial` (Step 1).
4. **`fugateCor1Sufficiency_of_ingramStar`** — strong induction on `k`, Steps 1–6. The
   re-indexing of the tail `A_{p+1}, …, A_k` as a chain `Fin (k − p) → Set S` is bookkeeping.
5. `fugate_cor1_of_ingramStar`, `fugateU_of_ingramStar` (bodies given).

**Refutation candidates.** If my hand proof is wrong, the error is most likely in one of these:
* the claim `M₁ ∩ M₂ = Y ∩ A`;
* the claim that both `H` and `K` meet `B` (from connectedness of `M₁`);
* the case `p = k`, excluded because `X` is unicoherent;
* the re-indexing.

## 2. Part II — (∗) from Ingram 1968 (`Ingram68.lean`)

Items, in Ingram's order:

1. **Circular chains and circle-likeness** (`cycDist`, `CircChain`, `IsCircEpsChain`,
   `IsCircleLike`): definitions, adjust as convenient.
   **`isSnakeLike_of_subset_circleLike`** (Nadler 12.51): drop the link through a point outside
   `Z`; the docstring has the argument.
2. **Sorgenfrey 1944, Theorem 1.8** (`exists_isTriod_of_isWeakTriod`,
   `not_three_of_isAtriodic`): a weak triod (`IsWeakTriod`, `SorgenfreyDefs.lean`) contains a
   triod. Ingram uses this in each of Lemmas 1–3.
   * The repository has `isTriod_union_of_three` only under hereditary unicoherence. LEDGER line
     77 records that the θ-curve is a "Fugate triod" but not a triod.
   * Check that the weak-triod form is right. It needs a *common point*, not mere pairwise
     intersection. If it is false as stated, refute it and give the form Ingram's lemmas actually
     need.
3. **Ingram, Lemmas 1, 2, 3** (`ingram_lemma1`, `ingram_lemma2`, `ingram_lemma3`).
4. **Ingram, Theorem 1** (`ingram_theorem1`): from `fugate_lemma1` (repository) and tautness
   (`exists_taut_epsChain`).
5. **Ingram, Theorem 2(2), sufficiency** (`ingram_theorem2_circleLike`). This is the long item;
   §3.5 transcribes the construction.
6. **`ingramStar_holds`**, then **`fugate_cor1`** and `fugateU_holds` (bodies given).

**Alternative route.** A direct proof of (∗), from Lemmas 1–3 together with terminality and
irreducibility (`ingram_lemma2`) and without circle-likeness, is acceptable in place of items 4–5.
Report which route was taken. Lemma 3 is exactly the tool for subcontinua that meet only one of
the two components of `Y ∩ A`.

**Where errors may be.** Ingram's proofs are terse, and parts of §3.5 rest on a scan whose
indices are hard to read. Where his argument has a gap or a false step, record it (it goes in
the ledger, like Bing's) and repair it.

## 3. Ingram 1968, transcribed (statements verbatim; proofs as printed, condensed only where noted)

Conventions. Ingram uses metric ρ. "Terminal" means: for each two subcontinua `K`, `L` of `M`
that intersect `H`, either `K ⊆ H ∪ L` or `L ⊆ H ∪ K`. This is the repository's
`IsTerminalSub`. A chain is *regular* (taut) if non-intersecting links are a positive distance
apart. Cook: if `M` is chainable and `D` is a chain covering `M`, there is a regular chain
covering `M` which is a strong refinement of `D`.

**Fugate, Lemma 1** (as cited by Ingram). If `H` is a terminal subcontinuum of the chainable
continuum `M` and `ε > 0`, then there is a regular ε-chain `C(c₁, …, cₙ)` covering `M` such
that `c₁ − (c₁ ∩ c̄₂)` intersects `H`. (Repository: `fugate_lemma1`, last-link form.)

### 3.1 Theorem 1

[Quotation moved to doc/sources/transcriptions/ingram68.md, §doc/batches/COMMISSION-batch132.md, 3. Ingram 1968, transcribed (passage 1); batch 204.]

*(Note: the clause "we assume …" reads as a without-loss case reduction: if `d_j − (d_j ∩
d̄_{j−1})` meets `K`, `D` is already the chain. Check this, and check that the spliced
collection is a chain.)*

### 3.2 Lemma 1

[Quotation moved to doc/sources/transcriptions/ingram68.md, §doc/batches/COMMISSION-batch132.md, 3. Ingram 1968, transcribed (passage 2); batch 204.]

### 3.3 Lemma 2

[Quotation moved to doc/sources/transcriptions/ingram68.md, §doc/batches/COMMISSION-batch132.md, 3. Ingram 1968, transcribed (passage 3); batch 204.]

### 3.4 Lemma 3

[Quotation moved to doc/sources/transcriptions/ingram68.md, §doc/batches/COMMISSION-batch132.md, 3. Ingram 1968, transcribed (passage 4); batch 204.]

*(The Case 1 step "since M₂ is a subcontinuum of A" and the Case 2 conclusion are as printed.
Check both.)*

### 3.5 Theorem 2(2), sufficiency

[Quotation moved to doc/sources/transcriptions/ingram68.md, §doc/batches/COMMISSION-batch132.md, 3. Ingram 1968, transcribed (passage 5); batch 204.]

*(Remark for the formalization. The construction is a splice of a chain on `A` and a chain on
`B` along `H` and `K`, with the `U`/`V` separation repairing the overlap near `H`. If the case
analysis ("other cases similar") or any of the "we may assume" steps hides a gap, record it and
repair it. The direct route to (∗) in §2 avoids all of this.)*

## 4. Edits to existing files (exhaustive list)

1. **`HPC/Plane/Fugate66.lean`** — only if Part II closes. Delete the sorried theorem
   `fugate_cor1` and its docstring. Leave a one-line comment pointing to
   `HPC/Plane/Ingram68.lean`. Nothing else in the library uses it; `Axioms.lean` line 810 does.
2. **`Axioms.lean`** — new group: "Fugate's Corollary 1: Part I (Corollary 1 under (∗)); Part II
   (Ingram 1968; (∗)); `fugate_cor1` proved (batch 132)". Include every new theorem, and
   `#print axioms HPC.Plane.fugate_cor1` and `HPC.Plane.fugateU_holds`. Regenerate `axioms.txt`.
   If Part II closes, the expected result is **`sorryAx` in no line**.
3. **`OPEN.md`**:
   * Item 1 (`fugate_cor1`): mark closed, with the note "proved in batch 132 from Fugate's
     Theorem 1 and Ingram 1968 Theorem 2(2) + Nadler 12.51 (circle-like ⇒ proper subcontinua
     chainable); Fugate gives no proof, and Ingram postdates Fugate".
   * "Not attempted: `treeLike_nonseparating`" unchanged.
   * If Part II does not close, item 1 becomes "reduced to (∗)", with the obstruction.
4. **`LEDGER.md`**:
   * The Fugate 1966 Corollary 1 row: "Stated without proof. True: proved (batch 132) via (∗),
     from Ingram 1968 Theorem 2(2). The induction through Theorem 1 that Fugate presumably
     intends needs (U), which holds but is not elementary." Add rows for any defects found in
     Ingram 1968.
   * New row: "Fugate 1966, introduction (p. 460) versus Theorem 1 (p. 466): the introduction
     says 'a-triodic and hereditarily unicoherent', the theorem 'a-triodic and unicoherent'.
     Equivalent for two pieces (Miller 1.5 / `isHereditarilyUnicoherent_union`); harmless.
     Barrett's MR review follows the introduction; the zbMATH review, Ingram 1968 and Alhassan
     2020 follow the theorem."
5. **`README.md`**: the Fugate 1966 line ("every numbered statement proved", if Part II closes),
   and batch count 132.

## 5. Deliverables

1. Parts I and II; edits 1–5. Write `#print axioms` output to
   `doc/batches/audits/axioms-batch132.txt`, and regenerate `axioms.txt`.
2. The report. Its first line names the commission read. It covers:
   * Part I items in order;
   * Part II items in order, with the route taken for (∗);
   * any defects found in Ingram 1968, and in my hand proof;
   * the final count of `sorryAx`.
3. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`, `doc/notes/` and
   `doc/sources/`. Nothing at the root.
4. Not attempted: `treeLike_nonseparating`.
