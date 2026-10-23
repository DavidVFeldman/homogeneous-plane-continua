# Report: batch 55 — the witness inside the residue, and Bing's seam

## 0. The counterexample, first

**The σ-route is not a theorem, even with the walk allowed to change.** Question 2 of the
commission asks whether a fold of the upper sequence `τ = 9 − σ` onto one of the five canonical
walks yields a fold of the lower one, `9 − ρ`, onto *some* walk of that fixed finite list. It does
not, and the failure is not a near miss: over the general model the census finds **501 basepoints**
at which the `τ`-pair folds onto one of the five and the pair of `9 − ρ` folds onto **none** of the
five.

The counterexample is not only counted, it is exhibited and checked by the kernel.
`HPC/Fold/Audit55.lean` carries one of those basepoints as explicit integer arms — the two
`τ`-arms `tG`, `tT`, the two `ρ`-arms with their reflections `rG`, `rT`, and the two original arms
`pG`, `pT` — together with the hypotheses the σ-route is entitled to assume:

* `pG_lowAt`, `pT_lowAt`, `tG_highAt`, `tT_highAt` — the arms have the announcements of the branch;
* `tG_base`, `pG_base` — the basepoint stands where the route puts it;
* `tG_folds_Vee`, `tT_folds_Vee` — the `τ`-pair folds onto the V-walk (and, separately,
  onto `w₄`);
* five theorems `rT_not_folds_Lam`, `rG_not_folds_Vee`, `rT_not_folds_w3`, `rG_not_folds_w4`,
  `rT_not_folds_w5` — for each of the five walks, one arm of `9 − ρ` provably refuses it.

The summary theorem

```lean
theorem sigma_route_walk_not_transported :
    (FoldsOnto tG … ∧ FoldsOnto tT …) ∧ ¬ FoldsOnto rT … ∧ ¬ FoldsOnto rG … ∧ … 
```

is the conjunction of those clauses; every clause is decided by the kernel (`decide +kernel`) on
the dynamic program of `HPC/Fold/Decide.lean`, and the theorem depends on
`[propext, Classical.choice, Quot.sound]` only — no `native_decide`.

So the answer to question 2 is **no**, and with it the hope that the branch `L + 5` follows from
the branch `L + 4` by transporting the walk along `σ ↦ ρ` closes. The per-walk losses over the
corpus show it is not one weak walk either: `Λ` 0, V 7 952, `w₃` 5 450, `w₄` 3 241, `w₅` 499
basepoints where that particular walk serves `τ` and fails on `9 − ρ`, and at 13 170 basepoints
some walk is lost while another still serves — the 501 are where the last one goes too.

**No §1 target is refuted.** This counterexample kills a *route*, not a target: it says the σ-route
cannot prove the branch `L + 5`, not that the branch is false. Over the whole corpus of this batch
no pair fails `cross_ceil_sentence`, `cross_valley_profile` or `unserved_three_walks`.

---

## 1. The targets

Unchanged and untouched this batch. `HPC/Fold/CrossCeil.lean` still carries one `sorry`
(`cross_ceil_sentence`), `HPC/Fold/Mixed.lean` three, `HPC/Fold/General.lean` two; no statement of
any target was weakened, and no earlier file was edited. `lake build HPC` is clean.

What the census says about them, over 4 042 faithful pairs of the general model (non-thin links
46 666 of 6 045 161, 0.772 %; the audit list of §4 below):

* **branch `L + 4`**: 1 131 275 basepoints, 337 173 of them unserved by the three-turn walks;
  every one is served by `w₃`, `w₄` or `w₅` (`w₃` 337 092, `w₄` 48 859, `w₅` 334 776; **by none 0**).
  6 787 650 exactness checks, **0 failures**; 0 equivalence failures.
* **`cross_ceil_sentence`**: 54 600 basepoints with an arm failing `Leg3Ceil`, 455 of them missing
  the `Λ`-walk; the `w₅` sentence holds at all 455. `CeilPeakResidual` 34, `CeilHighResidual` 0;
  inside the peak residue the V-walk and `w₅` serve all 34, and neither of the two clauses the
  reduction still needs fails anywhere.
* **`cross_valley_profile`**: 219 311 basepoints with an arm failing `Leg3Valley`, both arms fold
  onto the V-walk at all of them. `ValleyResidual` 281 176, with a failing arm 117 211; the
  conclusion **fails 0 times** there, and the V-walk serves the whole residue.
* **branch `L + 5`**: 1 410 106 basepoints, 332 268 unserved; the three reflected walks serve
  331 543, leaving **725** (batch 54: 857), of which 614 are served by some walk of at most three
  turns and **111** by none. The walks that pick up what the reflections miss are headed by
  `5 → 7 → 1 → 8` (246 pairs) and `4 → 7 → 1 → 8` (253 pairs).

So the targets stand where they stood: nothing refutes them, and the residues are served whole by
walks already in the list.

---

## 2. The three questions

### 2.1 Question 1 — where is the witness?

Measured, at every residual pair, by reading the V-criterion and `TopW5` as their definitions read
them and the crookedness clause as the structure field states it.

**The valley residue** (`ValleyResidual` with a failing arm): 95 209 pairs analysed, 6 377 with
both arms failing, 15 625 with no ascent on the arm at all.

| question | answer |
|---|---|
| does the criterion hold? | at **95 209 of 95 209**; fails 0 |
| index of the first witness | 8 (47 285), 12 (47 291), 22 (304), 26 (329) |
| its level | **`L + 2` exactly, at every one** |
| distance from the ascent | 29 (425), 31 (94 784) |
| is it further out than the residual time `u`? | **yes, at all 95 209** |
| is it forced by one clause application? | **at 16 916 only**; realised at the same 16 916; **neither at 78 293** |

**The ceiling residue** (`CeilPeakResidual`, `Λ`-free): 11 pairs. `TopW5` holds at all 11; the
first witness sits at index 31, at level `L + 2`, 31 steps from the ascent; **forced 0, realised 0**.

**The reading.** The witness is real, it is always at `L + 2`, and it is always far — never the
residual time the proof already finds at index two or three, but a time thirty-odd steps further
out. And it is **not** a consequence of one application of the crookedness clause: at more than
four fifths of the valley residue (78 293 of 95 209) no single application either forces the
witness or realises one, and at the ceiling residue no application does at all. The commission's
dichotomy therefore resolves the second way: *the witness is not a clause consequence, and the
residue is a real obstruction to this method* — one application of the clause, from anchors the
proof can name, does not reach it.

The anchor search is the quantitative form of the same statement. 1 643 distinct anchoring schemes
were recorded over 95 220 pairs, with anchors searched within 24 steps of the basepoint and at a
span of at most 20. Measured from the basepoint, the widest scheme covers **4 364** pairs (39
schemes tie); measured from the ascent, the widest covers **6 392** (85 schemes tie). No anchoring
comes near covering the residue, so there is no uniform missing step of this shape. (The search is
bounded: a scheme with anchors further out than 24 steps, or of span above 20, would not have been
seen. Within that box the answer is unambiguous.)

### 2.2 Question 2 — the σ-route with the walk allowed to change

**No.** See §0: 501 basepoints of the general model where the `τ`-pair folds onto one of the five
and the `(9 − ρ)`-pair folds onto none, with an explicit kernel-checked instance in
`HPC/Fold/Audit55.lean`. The phenomenon is not an artefact of one generator family: the
sub-census over the chains outside Bing's family (2 664 faithful pairs) already shows it, at 15 of
its 856 535 `τ`-served basepoints, while the two purely thin chains show none of it (0 of 364).
Batch 54's finding — that
the route loses a *walk* but never a *basepoint* — was a fact about that corpus, not a theorem: with
the larger corpus of this batch the basepoint goes too.

### 2.3 Question 3 — engines for four turns

Delivered, in `HPC/Fold/Leg4Wide.lean`, sorry-free.

`HPC/Fold/Leg4.lean` folds an arm onto the four-leg walk `leg4Walk L H K M P` (up from `P − 1` to
the peak `K`, down to the valley `M`, up to `H − 1`, down to `L + 1`) only inside

```
L + 2 ≤ P ≤ L + 4,   P + 1 ≤ K ≤ H − 1,   M = P − 2,   M + 3 ≤ K,   H ≤ K + 3,
```

which excludes both test walks of the commission: the base at `L + 5`, the valley three below the
base, and the mirror shape whose first leg is a single step. The new engine's window is

```
L + 2 ≤ P ≤ L + 6,   P ≤ K ≤ H − 1,   L + 1 ≤ M ≤ P − 2,   M + 3 ≤ K,   H ≤ K + 3,
```

with the base anywhere in `[P − 1, P]` (plus `f 0 ≤ K − 1`, automatic when `P < K`), so the three
obstructions named in batch 54 §2.2 are all inside it. The main theorem is

> **`foldsOnto_leg4W`.** A 1-Lipschitz arm in `[L, H]` based in `[P − 1, P]` folds onto
> `leg4Walk L H K M P` as soon as its descents to `P − 3`, its descents to `P − 4` and its ascents
> to `K + 2` are announced.

and with it `val4_boundsW`, `val4_walkW`, `val4_gstepW`, the six progress clauses
`prog4_EW/RW/E2W/SW/S2W/TW`, the invariant `gseq4_invW`, `foldsOnto_leg4W_of_val4`, the reflection
transfer `foldsOnto_leg4W_refl`, and the two test walks:

* **`foldsOnto_walk5738`** — `5 → 7 → 3 → 8 → 1`, i.e. `leg4Walk L (L+9) (L+7) (L+3) (L+6)`: an arm
  based at `L + 5` or `L + 6` in the band `[L, L + 9]` folds onto it as soon as its descents to
  `L + 3`, its descents to `L + 2` and its ascents to `L + 9` are announced. This is the shortest
  walk serving the hardest pairs of the branch-`L + 5` censuses.
* **`foldsOnto_walk4371`** — `4 → 3 → 7 → 1 → 8`, the mirror shape. It is the reflection of
  `leg4Walk L (L+9) (L+6) (L+2) (L+6)`, that is the engine at **`K = P`** (first leg of one step)
  and **`M = P − 4`** (valley four below the base) — two parameters the old window forbids
  outright. An arm based at `L + 4` folds onto it as soon as its ascents to `L + 6`, its ascents to
  `L + 7` and its descents to `L + 1` are announced.

**The one substantive change: where the floor announcements are read.** `HPC/Fold/Leg4.lean` reads
them at `M − 1` and `M − 2`; the wide engine reads them at `P − 3` and `P − 4`. For `M = P − 2`
those are the same two levels, so the new engine contains the old one on its window — but for a
deeper valley they are different, and the raise is *forced*, not cosmetic. `engine-batch55.c`
sweeps every parameter set of the window at `L = 0`, `H = 9` and runs both readings side by side on
the corpus. The result is reported in §2.4.

No crookedness is used inside the engine, which is why `foldsOnto_leg4W_refl` transports a fold of
the reflected arm onto `leg4Walk` into a fold of the arm onto `leg4Walk'` for free, and why the
mirror walk costs one reflection instead of a second engine.

### 2.4 The engine sweep

`engine-batch55.c` (log: `engine-batch55.log`; an earlier single-parameter run is
`engine-batch55-p6m3.log`). For each parameter set `L = 0`, `H = 9`, `L + 2 ≤ P ≤ L + 6`,
`L + 1 ≤ M ≤ P − 2`, `M + 3 ≤ K ≤ H − 1`, `H ≤ K + 3`, `P ≤ K`, it collects the arms of the corpus
based within two of `P` that satisfy the three announcements and checks, for each, that the greedy
stays inside `Val4`, that the invariant of `gseq4_inv` holds, and that the arm folds onto the walk.

**Result: 29 parameter sets; the reading of `HPC/Fold/Leg4Wide.lean` — at `P − 3` and `P − 4` —
fails at 0 of them, and the reading of `HPC/Fold/Leg4.lean` — at `M − 1` and `M − 2` — fails at 18
of them.** The split is exactly the one the theorem predicts: the old reading survives at the 11
sets with `M = P − 2` (where the two readings coincide) and fails at all 18 sets with
`M < P − 2`. At the parameters of the first test walk, `P = 6`, `M = 3`, `K = 7`, the old reading
announces 941 043 arms of which **256 417 leave `Val4`, do not fold, and break the invariant**;
the new reading announces 372 612 arms and **none** of them leaves `Val4`, fails to fold, or breaks
the invariant. Raising the two floor announcements is therefore necessary and sufficient over the
whole window, at the price of announcing fewer arms.

The single-parameter run makes the same point concretely: at `P = 6`, `M = 3`, `K = 7` — the
parameters of `5 → 7 → 3 → 8 → 1` — the announcements as `HPC/Fold/Leg4.lean` states them are
satisfied by 771 831 arms that **do not fold onto the walk**; read at `P − 3` and `P − 4` instead,
1 120 068 arms are announced and **none** fails `Val4` or the invariant.

---

## 3. Bing's seam

Delivered as a program with its table: `seam-batch55.py`, log `seam-batch55.log`. The construction
of p. 733 is carried out literally, in the thin model, with the inductive consolidation supplied by
exhaustive search over consolidations of at most nine blocks (the least size is found first, and
the table also reports whether each property holds at *every* least consolidation, not just at one).

For each basepoint of `bing 0 4`, `bing 0 5`, `bing 0 6` the program chooses `d_i` (a link outside
`e₁ ∪ e₂` and outside `e_{m−1} ∪ e_m`), takes `D(h, k)` maximal containing `d_i` with no interior
link meeting `e₁` or `e_m`, consolidates it as `H = [h₁, …, h_s]`, finds `h_u` — the first link of
`H` meeting `e₁ ∪ e_m` — and assembles `F` as `H(1, u − 1)` followed by the remaining links of `D`
grouped by the blocks of `E`. It then reports: is `h_u` inside the two end links; is `F` a chain;
is `d_i` in the first link of `F` only; the width of every block of `F`; and in particular the
width of the seam block, the one receiving `h_u`'s links.

### The table

`bing 0 4`, `E` of 5 links, 13 links in the chain, pattern `0 1 2 1 2 3 2 1 2 3 2 3 4`; the five
basepoints with `d_i` admissible, `H` of width 2:

| `d_i` | level | `D(h,k)` | `s` | `H` widths | #`H` | `u` | end | `h_u` | in end links | `F` chain | `d_i` first only | `F` widths | **seam** |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 2 | 2 | [0,12] | 4 | 1 2 2 2 | 4 | 2 | `e₁` | 0,1 | yes | yes | yes | 1 2 1 2 | **2** |
| 4 | 2 | [0,12] | 4 | 2 2 2 2 | 2 | 2 | `e₁` | 0,1 | yes | yes | yes | 2 2 1 2 | **2** |
| 6 | 2 | [0,12] | 4 | 2 2 1 2 | 4 | 2 | `e_m` | 3,4 | yes | yes | yes | 2 2 1 2 | **2** |
| 8 | 2 | [0,12] | 4 | 2 2 1 2 | 2 | 2 | `e_m` | 3,4 | yes | yes | yes | 2 2 1 2 | **2** |
| 10 | 2 | [0,12] | 4 | 1 2 1 2 | 4 | 2 | `e_m` | 3,4 | yes | yes | yes | 1 2 1 2 | **2** |

The basepoint the commission names, `bing 0 4` at `d_i = 6`, in full:

```
c = (1, 3, 1, 0)
H  = [[6, 7, 8], [5, 9, 11, 12], [2, 4, 10], [0, 1, 3]]
F  = [[6, 7, 8], [5, 9, 11, 12], [2, 4, 10], [0, 1, 3]]     widths 2 2 1 2, chain, seam width 2
```

Totals over all 84 basepoints of `bing 0 4`, `bing 0 5`, `bing 0 6` (per-basepoint rows for
`bing 0 5` and `bing 0 6` are in the log):

| pass | with a consolidation | `h_u` in the end links | `F` a chain | `d_i` first only | blocks of width ≥ 3 | seam widths |
|---|---|---|---|---|---|---|
| `H` of width 2, `u ≥ 1` | 84/84 | **84** | **84** | **84** | **0** | **[2]** |
| `H` of width 3, `u ≥ 1` | 84/84 | 0 | 59 | 25 | 4 | [2] |
| `H` of width 3, `u ≥ 2` | 84/84 | 3 | 6 | 84 | 14 | [2] |

### What the table says

**The prediction fails.** With the consolidation the exposition prescribes — `H` with every `h_j`
inside two adjacent links of `E` — the construction goes through at every one of the 84 basepoints:
`F` is always a chain, `d_i` is always in the first link of `F` only, **no block of `F` ever
exceeds two links**, and the seam block has width **two**, never three, at every basepoint and at
every least consolidation. `h_u` never reaches into `e₃`: it is inside `e₁ ∪ e₂` (or
`e_{m−1} ∪ e_m`) at all 84. So the predicted width-three seam does not occur here, and the reason
it does not is the reason Bing gives: the hypothesis that `h_u` meets `e₁` forces `h_u ⊂ e₁ ∪ e₂`.

**Widening `H` breaks something else.** The two extra passes allow `H` of width three, to see
whether the seam is merely hiding behind the width-two hypothesis. It is not. Allowing width three
does produce blocks of `F` of width three or more (4 basepoints with `u ≥ 1`, 14 with `u ≥ 2`) —
but the seam block itself is still of width two everywhere, and the damage lands elsewhere: `h_u`
stops being inside the end links (0 of 84, resp. 3 of 84), and `F` stops being a chain (59 of 84,
resp. 6 of 84). A width-three consolidation is not a wider seam; it is a broken construction.

One repair is recorded in the table for completeness: keeping `h_u` as a block of `F` of its own
(`F'`) gives a seam of width 1 in every pass, at the cost of `F'` failing to be a chain at 32 of
the 84 basepoints in the first pass.

---

## 4. Deliverables and audit

1. **Proved, sorry-free.** `HPC/Fold/Leg4Wide.lean` (the wide four-leg engine and the two test
   walks) and `HPC/Fold/Audit55.lean` (the σ-route counterexample). `lake build HPC` is clean; both
   files are in `HPC.lean`; no `sorry`, no `native_decide`, no new `axiom`, no `@[implemented_by]`.
   `#print axioms` on the delivered theorems:

   ```
   'HPC.Fold.foldsOnto_leg4W'      depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.foldsOnto_leg4W_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.foldsOnto_walk5738'   depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.foldsOnto_walk4371'   depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.Audit55.sigma_route_walk_not_transported'
                                   depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

2. **Censuses over the general model**, under the tightened audit protocol: `census-batch55.c`,
   log `census-batch55.log`, samples `census-batch55-sample.txt` and the shrunk counterexample
   `census-batch55-sigma.txt` (from which `gen-audit55.py` generates `HPC/Fold/Audit55.lean`). The
   audit list at the end of the log names every predicate evaluated by its own definition —
   `IsCrookedIvF`, `IsLip`, `HighAt`, `LowAt`, `Leg3Valley`, `Leg3Ceil`, `Valley4`, `Valley5`,
   `TopW5`, `MidW4`, `CeilW4`, `BottomW4`, `FoldsOnto` (the dynamic program of
   `HPC/Fold/Decide.lean`) for all five walks and their reflections, and the four residues — and
   the single proxy, reported as a proxy: the *narrow* valley residue of batch 53, which reads the
   interval pair and is kept beside the Lean predicate `ValleyNarrowResidual`, which reads `ρ`
   alone. New this batch: the witness analysis reads the V-criterion and `TopW5` as their
   definitions read them and the crookedness clause as the structure field states it; the σ-route
   question uses the same `FoldsOnto` program on `τ = 9 − σ` and on `9 − ρ`.

3. **The §3 table** above, produced by `seam-batch55.py` (log `seam-batch55.log`).

4. **This report**, in the commission's order.
