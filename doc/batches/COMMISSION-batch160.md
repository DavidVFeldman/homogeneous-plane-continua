# Commission: batch 160 — Part E, Hagopian 1976 V: Lemma 6 in full, Lemma 7; two-sided Schoenflies; Lemma 9

**Go!** This batch runs on top of the batch-159 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch160.md`: this text, also pasted into the prompt.
* `Hagopian76E.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76E.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76E` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 V (batch 160)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * `HPC/Hagopian/Hagopian76D.lean`: delete the commented-out copies of statements proved here,
    leaving one-line pointers.

## 0. On batch 159

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Statements.** `plane_schoenflies` and `exists_collar` are in the skeleton's shapes. You chose the
  shape of `hagopian76_lemma8_caps`, as asked, and it is accepted.
* **Audit.** `axioms.txt` has 1455 lines, with `sorryAx` in none, all on the standard three axioms.

**Accepted.**
* **The plane Schoenflies theorem**, transported from Moore 1919 through the plane model of Moore's
  axioms.
* **The collar**, built from a closing arc, a cross-cut, two half-collars (the outer one by
  inversion), and gluing. This is a substantial piece of Part A plane topology, and the exposition
  will use it.
* **Lemma 8 with caps.**
* **The comparison of the collar form with Bing's definition.**

**A correction to report 159 §1.A.** The first obstruction listed for Lemma 6 is not an obstruction.
Both results it asks for are proved:
* "A cofinal *sequence* needs, in addition, that any two extensions away from `X` are comparable by
  inclusion … a triod argument … not yet formalized": that is `hagopian76_lemma4_chain` (batch 156,
  `ext_chain`);
* the sequence itself is `hagopian76_lemma4_seq` (batch 156, from `exists_proper_extension` and
  `exists_strictMono_seq_of_chain`).

The skeleton header lists these. With `hagopian76_initial_segment`, which makes each smaller
extension an initial segment of each larger one, the union `R(X, E)` is an increasing union of
initial segments. The rest of Lemma 6 rests on that.

## 1. Where this sits

Lemma 6 is now the main gateway: T10, T12, T13, T16, T17 of the dependency map, and Lemma 7 through
it. **Do item A first and give it most of the batch.** Items C–E (Schoenflies with two sides
prescribed, `layer_nbhd_small`, Lemma 9) come after. Property 1 and T4–T9 move to batch 161, using
your report-159 §5 proposal.

## 2. Items

**A. Lemma 6** (`hagopian76_lemma6_X`, then `hagopian76_closure_extUnion`, `hagopian76_lemma6`),
and the unnumbered claims (`hagopian76_Rset_composant`, `hagopian76_essential_typeA'`).

Write `𝓕` for the extensions away from `X`, and `Fᵢ` for the sequence of `hagopian76_lemma4_seq`.
Each `F ∈ 𝓕` has its map `d_F`, with `d_F⁻¹(0) = X`. For `F ⊆ H` in `𝓕`, `F = d_H⁻¹[[0, s]]` for
some `s < 1` when `F ≠ H` (initial segment). A subcontinuum of `F` that meets `X` and some other
layer contains an initial segment `d_F⁻¹[[0, b]]` (the interval lemma, with Lemma 5 at `X`).

The following is my reading of steps 1–5. Check it, and formalize steps 1–8 as supporting lemmas
under the hypothesis `Cl R(X, E) = B ∪ C`, with `B`, `C` proper subcontinua.
1. **"`B` contains `X`"** (after renaming). `E ∩ B` and `E ∩ C` are continua (Lemma 1) with union
   `E`.
   * If `E ∩ B ⊆ X`, then `E ∩ C ⊇ E − X`, which is dense in `E` because `X` has void interior. So
     `E ⊆ C`.
   * Otherwise `E ∩ B` meets `X` and another layer, so it contains an initial segment, hence `X`.
   * Either way, one of `B`, `C` contains `X`. Call it `B`.
2. **"The sets `X` and `C` are disjoint."** Suppose `C` meets `X`; then `C ⊇ X` by the same
   argument. `B − C` and `C − B` are nonempty and open in `Cl R(X, E)`, and `R(X, E)` is dense, so
   some `Fᵢ = H` meets both. Then `H ∩ B` and `H ∩ C` are continua containing `X`, with union `H`.
   The one that contains a point of the far end layer of `H` is `H` (end-set property), so `H ⊆ B`
   or `H ⊆ C`, which is a contradiction.
3. **"Let `K` be an element of `𝓕` that meets `C − B`. Note that `B − C` is contained in `K`."**
   * `K ∩ B ⊇ X`. If the far end of `K` were in `B`, then `K ⊆ B`; so the far end is in `C` and
     `K ∩ C` is a tail of `K`.
   * For `w ∈ (B − C) ∩ Fⱼ` with `K ⊊ Fⱼ`: `Fⱼ ∩ B = d⁻¹[[0, b]]` and `K = d⁻¹[[0, κ]]` with
     `κ > b`, since `K` meets `C − B`. So `w ∈ K`.
   * Points of `B − C` outside `R(X, E)` lie in the closure of `(B − C) ∩ R(X, E)`, which is in `K`.
4. **The sequence and `c`.** `K ⊆ Fᵢ` for large `i`. Otherwise `R(X, E) ⊆ K` would be compact and
   equal to `K`, against no maximal element. For such `i` the far end `zᵢ` lies in `C`, by step 3's
   argument. Take `c` a cluster point of `{zᵢ}`; then `c ∈ C`.
5. **"`c` belongs to `Cl R(X, E) − R(X, E)`."** Suppose `c ∈ R(X, E)`. Take `L ∈ 𝓕` containing
   `K ∪ {c}`, `w ∈ R(X, E) − L`, `δ = min(ε, ρ(w, L))` with `ε = ρ(X, C)`, and, by Lemma 2, `i` and a
   `δ`-homeomorphism `f` with `f(c) = zᵢ` and `w ∈ Fᵢ`. Then `L ⊊ Fᵢ`.
   * **`L ∩ f[L] = ∅`.** `f[L] ∩ Fᵢ` is a continuum (Lemma 1) containing `zᵢ`. If it met
     `L = d⁻¹[[0, ℓ]]`, it would contain `d⁻¹((ℓ, 1))`, which contains `w`, against
     `ρ(w, f[L]) > 0`.
   * **`f[L] ⊆ R(X, E)`** ("Since `M` is atriodic"). `f[L]` meets `Fᵢ` near its far end and is a
     type A′ continuum through `zᵢ = f(c)`. By atriodicity, one side of it lies in `Fᵢ` and the other
     leaves `Fᵢ` beyond the far end. `Fᵢ ∪ f[L]` then contains an extension away from `X` containing
     `f[L]` (`ext_of_branch`, or its proof). **This is the step to write out with care.** If `c` is
     not in an interior layer of `L`, say what changes.
   * **The contradiction.** `f[X] ∩ C = ∅`, since `f` moves points less than `ρ(X, C)`. So
     `f[X] ⊆ B − C ⊆ K ⊆ L`, against `L ∩ f[L] = ∅`, because `f[L] ⊆ Cl R(X, E) = B ∪ C`.

Steps 6–8 (pp. 342–343) are yours. Step 6 now has its "subcollection" from
`hagopian76_initial_segment`. Quote each sentence in the ledger. If a step does not hold as printed,
give the configuration and what is needed.

Step 8 is "`Cl R(X, E) = Cl R(E)`", via "the second paragraph in the proof of Theorem 1 of [5]",
which is `hagopian75_no_indecomposable_interior` or its proof.

For the unnumbered claims:
* For `hagopian76_essential_typeA'`, formalize the containment of report 158 §1.C (an essential
  continuum lies in one extension), then use `isTypeA'_of_subcontinuum` with Lemma 5. If the
  containment uses `c ∉ R(X, E)` outside the contradiction hypothesis of Lemma 6, say how. Step 5
  proves it only under that hypothesis.
* For `hagopian76_Rset_composant`, use Lemma 6 and atriodicity.

**B. Lemma 7.** Its two sentences are in commission 157 §3.6.

**C. `layer_nbhd_small`.** This is the metric form of upper semicontinuity.

**D. `plane_schoenflies₂`.** This is two adjacent sides prescribed. A homeomorphism of the square
fixing the bottom side and carrying a reparametrized boundary arc to the left side should give it,
from `plane_schoenflies` together with Moore's boundary-extension form (`m19_schoenflies_param`).

**E. Lemma 9.**
* Put `π[I − {y}]` vertical in the same coordinates as `π[E]`, using item D.
* Build the chain `G` from collar rectangles, with the `ε` conditions from item C.
* Apply Theorem 28 to the rectangle `π[G₂]`, as your report-159 §1.E.3 proposes. Name the four
  boundary points and say which separates which; Hagopian does not.

## 3. Places to check (candidate ledger entries)

1. **pp. 342–343, Lemma 6:** steps 1–8, each with the printed sentence quoted. In particular:
   * step 1: "Since `E` is irreducible and `M` is hereditarily unicoherent, and since `X` does not
     have interior relative to `E`, it follows that `B` contains `X`";
   * step 4: "Since `M` is second countable, there exists a monotone strictly increasing sequence";
   * step 5: "Since `M` is hereditarily unicoherent and `f[L]` contains `zᵢ` and misses `w`, and
     since `Fᵢ` is irreducible, the sets `L` and `f[L]` are disjoint. Since `M` is atriodic, it
     follows that `f[L]` is a subset of `R(X, E)`";
   * step 6: "Then since no element `Y` of the decomposition of `N` has the property that `h₁⁻¹[Y]`
     contains `N`, the point `c` belongs to `R(E)`";
   * step 7: "Thus `C ∪ N ∪ h₁⁻¹[N] ∪ h₂⁻¹[P]` is a triod";
   * step 8.
2. **p. 343:** the two unnumbered claims.
3. **pp. 343–344, Lemma 7.**
4. **pp. 344–345, Lemma 9:** as in commission 159 §3.5, with the Theorem 28 configuration named.

## 4. Deliverables

1. Items A–E.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch160.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * the batch-161 skeleton proposal (Property 1, T4–T9, T11, T14), revised in the light of this
     batch.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
