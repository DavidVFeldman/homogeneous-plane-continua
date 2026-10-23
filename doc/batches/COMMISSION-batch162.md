# Commission: batch 162 — Part E, Hagopian 1976 VII: Lemma 7 by half-ray density; Lemma 9's proof; T6–T9, T11, Property 3

**Go!** This batch runs on top of the batch-161 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch162.md`: this text, also pasted into the prompt.
* `Hagopian76G.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76G.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76G` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 VII (batch 162)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * `HPC/Hagopian/Hagopian76D.lean`, `Hagopian76E.lean`, `Hagopian76F.lean`: delete the
    commented-out copies of statements proved here, leaving one-line pointers.

## 0. On batch 161

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1556 lines, with `sorryAx` in none, all on the standard three axioms.
* **Shape changes accepted:**
  * `IsEps1` in `hagopian76_eps1`;
  * `hagopian76_chain11`;
  * the shape of `hagopian76_property1`, which is strong and usable;
  * T9 for a `D` with property (D).

**Accepted.**
* **Ledger check 2.** The printed `ε₁` does not make the chain of `ε₁`-neighbourhoods follow `h[E]`;
  a smaller `ε₁` does. The ledger records this as unargued, with a repair, not as a defective proof.
* **`lemma8_caps_sep`.**
* **`hagopian76_property3_shift`.**
* **The Lemma 7 triod.** You showed that the arms are taken at the layer of `uⱼ`, which settles the
  end-layer case.

## 1. Lemma 7: the continuum `F` exists, and Hagopian's sentence says how

`Lemma7F` asks for too much. It quantifies over *arbitrary* `u ≠ t` in one composant of `Cl R(E)`,
and is probably false in that generality: when `u` lies near the end of a ray-like composant, every
continuum through `u` that reaches far away passes through `t`. Hagopian's `u` and `t` are not
arbitrary:
* `uᵢ ∈ Uᵢ` and `tᵢ ∈ Tᵢ` are points of layers of `Hᵢ`, an essential continuum of the line
  `hᵢ[R(E)]`;
* `ρ(Tᵢ, Uᵢ) > ε`.

His sentence is "By Lemma 2, an integer `i` and a homeomorphism `f` of `M` onto `M` exist such that a
continuum `F` essential to `fhᵢ[R(E)]` contains `u`, misses `t`, and intersects `A`". I read it as
follows; check it.

1. Lemma 2 gives a small `f` with `f(uᵢ) = u`, for `i` large. Then `u` lies in the layer `f[Uᵢ]` of
   the line `fhᵢ[R(E)]`, which is a translate of the composant `R(E)` of `Cl R(E)`.
2. `t ∉ f[Uᵢ]`, because `ρ(t, f[Uᵢ]) ≥ ρ(Tᵢ, Uᵢ) − ρ(t, tᵢ) − (displacement of f) > 0` for `i`
   large.
3. The line through the layer `f[Uᵢ]` has two half-rays, which meet only in that layer. If `t` lies
   on the line at all, its layer is on one side. Take the other half-ray.
4. **Each half-ray is dense** in the translate of `Cl R(E)`, by `halfray_dense`, transported by
   `fhᵢ`. So an initial segment `F` of it reaches within `ε/4` of `p`, once `f` and `hᵢ` are close
   enough to the identity. `F` contains `u` and misses `t`.
5. `hagopian76_lemma7_triod` finishes, as in your `lemma7_of_F`. You need only `t ∉ F`, then
   `ε′ < ρ(t, F)/2` and `j` large.

So the work is:
* **`halfray_dense`**. For `G = E` it is `hagopian76_closure_extUnion` and `closure_extUnion_one`.
  In general it needs `Cl R(E′) = Cl R(E)` for the type A′ pieces `E′ = d⁻¹[[u, 1]]` and
  `d⁻¹[[0, u]]` of an essential `G` (`isTypeA'_of_subcontinuum`). Both are composants of their
  closures (`hagopian76_Rset_composant`) and they share `E′`. Write the argument out.
* **Lemma 7 by steps 1–5**, replacing `Lemma7F` by the direct construction.
* **Record in the ledger:** Hagopian's sentence is unargued and true by steps 1–5; `Lemma7F` is too
  strong. If you can refute `Lemma7F` cheaply (a Knaster-type ray composant), do so; otherwise
  record it as not needed.

## 2. Items

Order:
1. A: `halfray_dense`, Lemma 7.
2. B: Lemma 9's proof in collar rectangles, giving T3 and T6.
3. T7 and T8, giving property (D) and so T9 in full.
4. T11.
5. Property 3.

Follow report 161 §1.6 for the Lemma 9 configuration, including its two corrections: the continuum
through `b₁`, `b₂` includes the segment of `A`, and the links must be collar rectangles. For the items
marked *shape left to you*, quote the printed sentence and choose shapes that T12, T13, T15–T17 can
use.

## 3. Places to check (candidate ledger entries)

1. **pp. 343–344, Lemma 7:** "By Lemma 2, an integer `i` and a homeomorphism `f` … exist such that a
   continuum `F` essential to `fhᵢ[R(E)]` contains `u`, misses `t`, and intersects `A`". Record its
   status after item A. Record whether `F` is in fact essential, and whether that is used.
2. **pp. 344–345, Lemma 9:** the Theorem 28 configuration, formally.
3. **p. 346, T6:** "It follows from the proof of Lemma 9 that there exists a horizontal interval `I₁`
   …".
4. **p. 346, T7:** "We find that there exists such an arc `I₂` as follows. … By choosing `y`
   sufficiently close to `E` and `h` sufficiently close to the identity, we get that every point of
   `R²` between `⟨p₁, p₅⟩` and a subarc of `π[A]` irreducible between `⟨p₁, q₁⟩` and `⟨p₅, q₅⟩`
   belongs to `π[St L]`." This is unargued.
5. **p. 346, T8, T9:** "Note that the chain `L − {L₁, L₁₁}` follows `Cl B`."
6. **p. 347, T11:** "Note that `K` separates …".
7. **p. 347, Property 3:** "Let `v` be the first point of `[0, 1]` such that …".

## 4. Deliverables

1. The items of §2.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch162.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * a skeleton proposal for the remainder: T10 (Property 2), T12, T13, T15–T17, and the assembly
     `hagopian76_theorem1 : Hagopian76Thm1`.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
