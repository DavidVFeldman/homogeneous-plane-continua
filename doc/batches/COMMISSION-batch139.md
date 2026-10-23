# Commission: batch 139 — Part D, Moore III: F.A. §7, Theorems 35–43

**Go!** This batch builds on the batch-138 delivery. Two files come with it, as separate uploads:

* `COMMISSION-batch139.md`: this text, which is also pasted into the prompt.
* `MooreFA7.lean`: the skeleton.
  * Save it as `HPC/Moore/FA7.lean` and add `import HPC.Moore.FA7` at the end of `HPC.lean`.
  * Splitting it into several files under `HPC/Moore/` is expected.

The source is `moore1916.pdf`, pp. 150–157, already in `doc/sources/`.

**Rules.**
* You may adjust shapes. Record each change at the statement and in the report.
* The report's first line names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Moore F.A. §7 (batch 139)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open.

## 0. On batch 138

Audited and accepted.
* **Fidelity.** The skeleton copy is byte-identical. Definitions match the skeleton. Statements
  differ only by axioms made explicit and by recorded weakenings, with one exception: Theorem 32.
* **Axioms.** `axioms.txt` has 882 lines, with `sorryAx` in none.
* **Accepted results:**
  * the refutation of Theorem 23 at the empty region;
  * the correction in Theorem 28;
  * Kline's proof, with its gap filled (the first point of `DC` on `CAB` may be `B`);
  * the batch-137 ledger correction (Theorem 5 (3), `R′ₙ`).

**Theorem 32: one follow-up (optional, low priority).** Your counterexample to the literal
statement is a point `C ∈ R` lying on `AB`. It shows that `C ∉ AB` is needed. It does not show
that the stronger hypothesis you added, `R ∩ AB = ∅`, is needed.
* Try to prove Theorem 32 with `C ∉ AB` in place of `Disjoint R K`. Your `accessible` lemma may
  already give it.
* If that succeeds, keep both forms, and record which one Theorems 33–34 and later uses need.
* If it fails, record why.

## 1. Where this sits

| batch | content |
|---|---|
| 137, 138 | F.A. §§2–6 (done) |
| **139 (this one)** | F.A. §7, Theorems 35–43 |
| 140 | Moore 1919, *Concerning a set of postulates for plane analysis situs*: a space satisfying Σ₁/Σ₂ is a number plane |
| 141 | Moore 1925 §I and Theorem 22 |
| 142 | Jones 1955 Theorem 2, with Jones 1949 |

Theorems 35–43 are what Moore 1919 and 1925 use from §7. They cite Theorems 36, 37, 40, 42 and 43
by number, and 35, 38, 39 and 41 feed those. Theorems 44–52 are not commissioned. Theorem 48, the
Lennes-type characterization of the simple closed curve, is not needed.

## 2. Items

All statements are in skeleton §2. Follow Moore's proofs where they are printed: 35, 36, 37, and 39
(sketched). For Theorem 41, the proof is sketched up to "It may be proved that `J` is a closed curve
satisfying the requirements of Theorem 41".

The other proofs must be supplied:
* 38 ("analogous");
* 40, 42 and 43 (no proof printed);
* the last step of 41.

Record, for each theorem, the axioms actually used.

* **Theorem 38.** The skeleton leaves the shape to you (`True` placeholder). Model it on Theorem 37,
  and record the reading of "`A₁XA₂OA₁`" and of conclusions (1) and (3).
* **Theorem 40** is the one most used later. Moore 1919 builds its grids from arcs inside and outside
  closed curves.

## 3. Places to check (candidate ledger entries)

1. **Theorem 35** ("Every region contains at least one simple closed curve") fails for the empty
   region. Refute the printed form, as in batches 137–138.
2. **Theorem 36:** "there exists a simple closed curve which lies in `R` and encloses `O`". Moore
   1925 Theorem 19 needs the interior to lie in `R` as well. Prove `fa_theorem36_interior_subset`
   (it follows from Theorem 21) and record that this is not part of the printed statement.
3. **Footnote, p. 152:** "Two arcs of a closed curve can have no point in common unless one of them
   contains an endpoint of the other one." Prove it (`fa_arcs_of_scc_meet`).
4. **Theorem 37 proof:**
   * "Hence, in view of Theorem 29, it is clear that if `W₁` is between `Z₁` and `O` on the arc
     `A₁O` then `W₂` must be between `Z₂` and `O` on the arc `A₂O`";
   * "If Theorem 37 is false there exists a point `L₁` on `A₁O` and a point `L₂` on `A₂O` such that
     `L₁` is a limit point of `M₁` …".

   Supply both steps.
5. **Theorem 39 proof:**
   * "It may be easily shown with the help of Theorems 5 and 36 that there exists a sequence of
     closed Jordan curves `J₁, J₂, …`";
   * "With the use of (1) it may be shown that `I` contains a point of `Jₙ`";
   * "It is clear that, for a given `n`, the arc `AₓBₓ` is completely determined by the point `X`";
   * "It may be easily proved that `J̄ₙ` is a closed Jordan curve";
   * "It easily follows (cf. proof of Theorem 25) that there exists an arc `T₁T₂` …";
   * "It may be easily proved that the point-set `O + P₁P̄ₙ₂ + ⋯` is an arc from `P₁` to `O`";
   * "That a point without `J` can be so joined to any point of `J` may be proved in a similar
     manner".

   That is seven unargued steps. Supply each, or replace the argument; any correct route is fine.
   If you replace it, quote the printed sentences that the replacement covers.
6. **Theorem 41 proof:**
   * Case I: "it easily follows that either `I₁` is in `I₂` or `I₂` is in `I₁`";
   * Case II: the closing sentence, "It may be proved that `J` is a closed curve …".
7. **Theorem 43 with `G` empty.** The hypotheses then hold vacuously. The conclusion forces
   `J₁, J₂ ⊆ J`, hence `J₁ = J₂ = J`, with the interior of `J` both inside and outside itself. So
   the printed statement appears false for `G = ∅`. Refute it, or show why not, and prove the
   corrected form.
8. **Degenerate cases.** As before, watch for empty regions and endpoint cases in every "there
   exists".

## 4. Deliverables

1. Items in §2.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch139.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for F.A. §7 giving the outcome of each check in §3, with the
   printed sentence quoted.
3. The report. Its first line names the commission it read. It then gives:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * what batch 140 (Moore 1919) needs from F.A.

   For the last of these, read the 1919 paper's citations of F.A.: pp. 132, 133, 139, 149, 152–153
   and 159, and Theorems 12, 15, 36, 37, 40, 42, 43. Say whether anything beyond Theorem 43 is
   needed, in particular open curves (p. 159, Theorems 49–51).
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the
   root.
