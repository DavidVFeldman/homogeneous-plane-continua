# Commission: batch 161 — Part E, Hagopian 1976 VI: Theorem 1 set-up (ε₁, the chain, Properties 1 and 3, T9, T11); Lemma 7; Lemma 9

**Go!** This batch runs on top of the batch-160 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch161.md`: this text, also pasted into the prompt.
* `Hagopian76F.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76F.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76F` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 VI (batch 161)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * `HPC/Hagopian/Hagopian76D.lean` and `Hagopian76E.lean`: delete the commented-out copies of
    statements proved here, leaving one-line pointers.

## 0. On batch 160

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Statements.** All are in the skeleton's shapes; the `omit` in `layer_nbhd_small` is accepted.
* **Audit.** `axioms.txt` has 1505 lines, with `sorryAx` in none, all on the standard three axioms.

**Accepted.**
* **Lemma 6 in full, and both unnumbered claims.**
* **Absorption** (`subset_extUnion_of_meets`: a continuum missing `X` and meeting an extension lies
  in `R(X, E)`). It is Hagopian's step-5 sentence "Since `M` is atriodic, it follows that `f[L]` is a
  subset of `R(X, E)`", made general. It gives `C ⊆ R(X, E)` at once, so steps 6–7 (the case
  `c ∉ R(X, E)`) are vacuous.
  * The ledger records steps 6–7 as superfluous, not checked, and not wrong as far as checked.
  * It records Hagopian's printed claim "The point `c` belongs to `Cl R(X, E) − R(X, E)`" as an
    intermediate conclusion of a proof by contradiction, which your route never needs.
* **Step 8 without homeomorphisms.**
* **The containment of essential continua**, via "`R(X, E)` is not closed".
* **`plane_schoenflies₂`**, by choosing the quadrilateral so that Moore's four prescribed sides
  include `φ` and `ψ`.
* **`layer_nbhd_small`.**

## 1. Lemma 7: what I see

You located two unargued sentences (report 160 §1.B). My reading of them follows; check it.

**The triod is fine, given `F`.** Take `F` a continuum containing `u`, with `t ∉ F`, meeting `A`.
1. Choose `ε′ < min(ε/4, ρ(t, F)/2)`, and `j` large with `ρ(tⱼ, t)` and `ρ(vⱼ, t)` both less than
   `ρ(t, F)/2`.
2. Lemma 2 gives an `ε′`-homeomorphism `g` with `g(u) = uⱼ`. Then `g[F]` misses `tⱼ` and `vⱼ`, and
   meets `B = {x : ρ(x, p) < ε/2}`, which `Hⱼ` misses.
3. So `g[F] ∩ Hⱼ` is a continuum (Lemma 1) through `uⱼ`, inside `Hⱼ` and missing `tⱼ`, `vⱼ`.
4. The two pieces of `Hⱼ` beyond it, toward `Tⱼ` and toward `Vⱼ`, and the piece of `g[F]` outside
   `Hⱼ` are three arms. That is a triod (`isTriod_of_core`), against Lemma 1.

Write this out, including the case where `g[F] ∩ Hⱼ` reaches an end layer without containing `tⱼ`
or `vⱼ`.

**The gap is the existence of `F`**, a continuum through `u` that meets `A` and misses `t`. Here `u`,
`t`, `p` are limit points in `Cl R(E)`, which is indecomposable (Lemma 6).
* *If `u` and `t` lie in different composants of `Cl R(E)`:* any proper subcontinuum through `u`
  misses `t`, and one meets `A`, since composants are dense (`composant_dense`).
* *If they lie in the same composant:* this is the open case. Possible routes:
  * use the freedom in choosing `uᵢ ∈ Uᵢ` and the subsequence, so that the limit `u` avoids the
    composant of `t`;
  * or show that in an indecomposable, atriodic, hereditarily unicoherent continuum, each of the two
    "halves" of a composant at `u` is dense, and take the half away from `t`;
  * or find another argument.

  Hagopian's "By Lemma 2, an integer `i` and a homeomorphism `f` … exist" suggests a continuum
  inside some `hᵢ[R(E)]` moved by `f` so that it passes through `u`. Reconstruct what he may have
  meant.

If Lemma 7 stays open, say whether Property 2, the only use of Lemma 7 on p. 346, can be had another
way.

## 2. Items

Order, after your report-160 §5 proposal:
1. T4, `hagopian76_eps1`.
2. T5: `Wset`, `exists_Gset`, the chain and `L`, and Property 1 (`hagopian76_property1`).
3. T9 (`hagopian76_T9`).
4. Property 3 (`hagopian76_property3`).
5. T11 (`hagopian76_T11`).
6. Lemma 9.
7. Lemma 7.

The items marked *shape left to you* in the skeleton are internal to Theorem 1's proof. For each,
quote the printed sentence it renders, and choose the shape so that the remaining steps (T6–T8, T10,
T12, T13, T15–T17) can use it. If a step needs the collar coordinates or `D` (T8), define what is
needed, for example `Iarc₁`, `Iarc₂`, `Dom` as in report 159 §5, and record it.

For Lemma 9, the Theorem 28 configuration is the one in report 160 §1.E (the rectangle `π[G₂]`,
points `a₁`, `a₂`, `b₁`, `b₂`). Check it formally. Make sure freeness keeps `πh[D]` off the left
side.

## 3. Places to check (candidate ledger entries)

1. **pp. 345–346, `ε₁`:** "Define `ε₁` to be one-third the minimum of the union of" the four families.
   Record which of them each later step uses.
2. **p. 346:** "Note that if `h` is an `ε₁`-homeomorphism of `M` onto `M`, then the chain formed by
   taking `ε₁`-neighborhoods in `R²` of the elements of `{k⁻¹[[(i − 1)/11, i/11]] : 1 ≤ i ≤ 11}`
   follows `h[E]`." This is unargued.
3. **p. 346, Property 1**, and the parenthetical about `A` and `B`.
4. **p. 346, T9:** "Since `M` is atriodic, it follows from Property 1 and Lemma 5 that `Cl B` is the
   image of a subcontinuum of `E` (essential to `R(E)`) under an `ε₁`-homeomorphism. Note that the
   chain `L − {L₁, L₁₁}` follows `Cl B`."
5. **p. 347, T11:** "Note that `K` separates `L₂ ∩ M ∩ π⁻¹[D]` from `L₁₀ ∩ M ∩ π⁻¹[D]` in
   `π⁻¹[D]`."
6. **p. 347, Property 3** and its proof: "Let `v` be the first point of `[0, 1]` such that …"; "By
   Lemma 1 and Property 1, `L` follows a type A′ continuum in `d⁻¹(v)` that meets `L₆ ∩ π⁻¹[D]`. By
   Lemmas 2 and 3, a homeomorphism `g` of `M` onto `M` and a point `u` of `[0, v)` exist such that
   `gd⁻¹(v) = d⁻¹(u)` …".
7. **pp. 343–344, Lemma 7:** the two sentences, with §1's analysis.
8. **pp. 344–345, Lemma 9:** the Theorem 28 configuration.

## 4. Deliverables

1. The items of §2.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch161.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * a skeleton proposal for the rest of Theorem 1: T6–T8, T10 (Property 2), T12, T13, T15–T17
     (Property 4 and the induction), and the final assembly `hagopian76_theorem1 : Hagopian76Thm1`.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
