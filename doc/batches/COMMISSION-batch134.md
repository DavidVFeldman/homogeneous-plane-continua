# Commission: batch 134 — the Effros theorem (van Mill's proof) and Ungar's corollary

**Go!** This opens Part C of the classification project (CLASSIFICATION-OUTLINE.md). It runs on
top of the batch-133 delivery.

Three files accompany this commission as separate uploads, not an archive:

* `COMMISSION-batch134.md` — this text (also pasted into the prompt);
* `Effros.lean` — a skeleton, `sorry`s as work items. Save it as `HPC/Effros/Effros.lean`, in a new
  directory, and add `import HPC.Effros.Effros` at the end of the root `HPC.lean`. Splitting into
  several files under `HPC/Effros/` is expected.
* `mill2004.pdf` — J. van Mill, *A note on the Effros theorem*, Amer. Math. Monthly 111 (2004),
  801–806. Save it as `doc/sources/vanmill2004.pdf`.

Shapes may be adjusted, with each change recorded. The report names the commission read in its
first line. Each item is reported as *proved*, *refuted*, or *open with the obstruction stated*.

No existing file is edited except the following:
* `HPC.lean`;
* `Axioms.lean` and `axioms.txt` (new group "Effros theorem (batch 134)");
* `README.md` (a line for Part C, and the batch count);
* `OPEN.md`, only if something is left open.

## 0. On batch 133

Audited and accepted:
* `IsTreeLike` is repaired, and `isTreeLikeOld_of_isContinuum` certifies the old definition.
* `treeLike_nonseparating` is proved.
* Duke Theorem 7 is proved as printed, and Theorem 6 as an equivalence.
* 692 lines, `sorryAx` in none.

Both Bing papers are now complete. I checked every definition that bounds a diameter for the
boundedness clause; only the old `IsTreeLike` lacked it. That is the lesson for this and future
batches: **every `diam … < ε` comes with `Bornology.IsBounded`.** (`supMove` below is a supremum
over a compact space and is finite; still check that `⨆` behaves as intended, i.e. that it is
bounded above.)

## 1. Why this theorem, and in which form

Every later part of the classification uses the Effros theorem in Ungar's form
(`effros_homogeneous`):
* Jones's decomposition theorem;
* Hagopian;
* Rogers;
* Oversteegen–Tymchatyn;
* Hoehn–Oversteegen.

The form is: in a homogeneous compact metric space, nearby points are exchanged by a homeomorphism
that moves nothing much.

The general statement for a Polish group (`effros_open_mapping`) is the right level of generality.
Part F will need the homeomorphism group as a Polish group again.

## 2. Items

**A. Meager and fat sets** (§A of the skeleton): `NowhereMeagre`, `IsFat`, `IsFat.mono`,
`IsFat.diff_meagre` (van Mill 2.1), `nonempty_interior_closure_of_not_meagre`, and
`inter_nonempty_of_isFat` (van Mill 2.2).
* Use Mathlib's `IsMeagre` and `MeasureTheory.AnalyticSet` (continuous images of `ℕ → ℕ`, or ∅).
  Polish spaces and their open subsets give analytic images (`AnalyticSet.image_of_continuous`
  and relatives).

**B. The open mapping principle** (§B): `exists_vanMill_basis`, `orbitPart`, `vanMill_3_1`, `3_2`,
`3_3`, `3_4`, `3_5`, `effros_open_mapping`, `isOpenMap_smul_left`.
* Hypotheses: a Polish topological group acting continuously and transitively on a nonempty metric
  Baire space.
* Van Mill's Remark 5 says only separate continuity is used. Weaken the hypothesis if that is
  convenient; it is not required.

**C. The homeomorphism group of a compact metric space** (§C): `supMove`, its two inequalities,
then items C.1–C.3.
* C.1: the group, its topology, and `IsTopologicalGroup`.
* C.2: `PolishSpace`.
* C.3: the action, `ContinuousSMul`, and `supMove`-balls as neighbourhoods of `1`.
* First check what Mathlib provides: a group structure on `Homeomorph`, a topology on homeomorphism
  groups, `ContinuousMap` metric, completeness and second countability for compact domains. Use
  what exists. The skeleton header gives a construction if nothing does.
* This is the likeliest place for the batch to run long. If C does not close, prove D from B under
  an explicit hypothesis packaging C, and report.

**D. Ungar's corollary** (§D): `effros_homogeneous`, and `effros_homogeneous_set` for compact
subsets of a metric space, homogeneous in their own topology. Do not forget the Lebesgue-number
step.

**Refutation candidates.**
* `vanMill_3_2` uses only that `U ∈ 𝓝 1`. Check whether the Lindelöf step needs anything else
  (second countability of `G` follows from Polish).
* `inter_nonempty_of_isFat` needs `Nonempty Y`.
* In `vanMill_3_5`, Proposition 2.2 is applied inside the open subspace `E`. "Fat in `E`" must be
  derived from Corollary 3.3, which speaks of `X`: meager in `E` versus meager in `X` for subsets
  of an open `E`.

## 3. Van Mill 2004, §§2–3, transcribed

[Quotation moved to doc/sources/transcriptions/vanmill04.md, §doc/batches/COMMISSION-batch134.md, 3. Van Mill 2004, §2 and 3.1; batch 204.]

### 3.2 Section 3: the open mapping principle

[Quotation moved to doc/sources/transcriptions/vanmill04.md, §doc/batches/COMMISSION-batch134.md, 3.2 Section 3, to Lemma 3.4; batch 204.]

**Suspected gap (mine — confirm or refute).** "Not nowhere dense" means that the *closure* has
nonempty interior, not the set itself. As printed, the step is unjustified at this point of the
argument. The conclusion is true after Corollary 3.6, but 3.6 depends on 3.4 and 3.5, so that
would be circular.

**Repair (closure form; the skeleton states it this way).**

*3.4′.* `x ∈ int cl Uₙx`.
* `V := int cl Uₙ₊₁x` is nonempty (3.2), and it meets `Uₙ₊₁x` because `V ⊆ cl Uₙ₊₁x`. Say
  `hx ∈ V` with `h ∈ Uₙ₊₁`.
* Then `x ∈ h⁻¹V`, which is open.
* `h⁻¹V ⊆ h⁻¹ cl(Uₙ₊₁x) = cl(h⁻¹Uₙ₊₁x) ⊆ cl(Uₙx)`, by (i) and (ii).

*3.5′.* `int cl Uₙ₊₁x ⊆ Uₙx`. This is van Mill's proof with `int` replaced by `int cl`:
* For `z ∈ V := int cl Uₙ₊₁x`, put `W := int cl Uₙ₊₁z`, which contains `z` by 3.4′. Let
  `E = V ∩ W`.
* `Uₙ₊₁x ∩ E` and `Uₙ₊₁z ∩ E` are dense in `E`, nowhere meager, and analytic.
* By 2.2 in `E` they meet.

*3.6.* `Uₙx ⊇ int cl Uₙ₊₁x ∋ x` (3.4′ at level `n + 1`, then 3.5′).

This is also the shape of the classical open mapping theorem, which van Mill says his proof
follows. If you find that van Mill's printed step can be justified as it stands, say how. Either
way the ledger records the outcome.

*From here on `G` is analytic* (here: Polish). `γ_x` maps `Uₙ` onto `Uₙx`. `Uₙ` is open in `G`,
hence analytic, so `Uₙx` is analytic.

**Proposition 3.5.** `int Uₙ₊₁x ⊆ Uₙx`.

*Proof.* Let `z ∈ V := int Uₙ₊₁x`, and let `W` be the interior of `Uₙ₊₁z`. By 3.4,
`E = V ∩ W` is an open neighbourhood of `z`.
* `E ⊆ Uₙ₊₁x`, so `Uₙ₊₁x ∩ E` is dense in `E`; likewise `Uₙ₊₁z ∩ E`. Both are analytic.
* By 3.3 and Proposition 2.2, applied in `E`, they meet, say at `y = gx = hz` with
  `g, h ∈ Uₙ₊₁`.
* Then `φ = h⁻¹g` satisfies `φx = z` and `φ ∈ Uₙ₊₁Uₙ₊₁ ⊆ Uₙ`. So `z ∈ Uₙx`.

**Corollary 3.6.** `Uₙx` is a neighbourhood of `x` (3.4 and 3.5). With 3.1, `Uₙx` is open.

## 4. Deliverables

1. Items A–D.
   * Write `#print axioms` output to `doc/batches/audits/axioms-batch134.txt`, and regenerate
     `axioms.txt`. `sorryAx` stays in no line; anything left open is commented out with its
     obstruction, as in batch 132.
   * Edit `README.md`: a Part C line, and the batch count.
2. The report. Its first line names the commission read. It covers:
   * items in order;
   * what Mathlib provided for C;
   * whether my reconstruction of Proposition 2.2's invariant (3) was right, and whether the
     Lemma 3.4 gap is real;
   * any defect found in van Mill's text. It goes in a new `LEDGER.md` section for the
     classification sources.
3. Housekeeping: uploads go to `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`. Nothing
   at the root.
