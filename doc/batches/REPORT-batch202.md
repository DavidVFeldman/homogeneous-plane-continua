Commission read: `doc/batches/COMMISSION-batch202.md` ("Commission: batch 202 — Part G, V: a plane circle of pseudo-arcs").

# Report, batch 202

## 0. Summary, omissions, shape changes

**Every declaration of the skeleton is proved, with the skeleton's statements**, including the
recognition theorem `CircDescr.isCircleOfPA`, `exists_sweepPattern`, `circ_step`,
`exists_circDescr_plane` and hence **a plane circle of pseudo-arcs**
(`HPC.BJ59.bjPlaneExample : BJPlaneExample`). With `bjThm10` (batch 201), the classification of
homogeneous plane continua with Bing–Jones's third class, and its plane form, hold **with no named
hypothesis** (`ho16_classification₄`, `ho16_classification_plane₄`); so do Domokos–Prajs 6.1 in
both directions (`dp22_theorem61'`, `dp22_theorem61_iff'`) and `hoCircleLike'`. Nothing is
commented out and no new file contains `sorry`, `admit` or `axiom`.

The skeleton is split under `HPC/BJ59/` (sixteen files: `CircDescr.lean`, `CircFibre.lean`,
`CircMap.lean`, `Sweep.lean`, `Sweep3.lean`, `SweepPattern.lean`, `CircJoints.lean`,
`CircCover.lean`, `CircDescent.lean`, `CircStd.lean`, `CircStep.lean`, `CircPlane.lean`,
`BJ59E.lean`, `NonVac202.lean`, `NonVac202b.lean`, `NonVac202c.lean`). `HPC/BJ59/BJ59E.lean` holds
§6 and a docstring mapping each skeleton declaration to its file. A script check confirms that all
25 declarations of the skeleton occur in the library with the skeleton's text up to `:=` (or
`where`). The new theorems are audited in `doc/batches/audits/axioms-batch202.txt`; none depends on
`sorryAx`. `lake build HPC` succeeds (8860 jobs).

```
STATUS: CircDescr, CircDescr.M, CircDescr.fib defined (as in the skeleton); tested (§6)
STATUS: CircDescr.isCompact_M proved
STATUS: CircDescr.inter_M_nonempty proved
STATUS: CircDescr.fib_meets proved
STATUS: CircDescr.isCircleOfPA proved
STATUS: sweep lemma proved (shape: fixed block length; sweep_lemma with at most two events, as used; sweep_lemma3 with at most three events, the commission's bound)
STATUS: exists_sweepPattern proved
STATUS: stdCircLink_meet_iff proved
STATUS: circ_step proved
STATUS: exists_circDescr_plane proved
STATUS: bjPlaneExample proved
STATUS: ho16_classification₄, ho16_classification_plane₄ proved (no named hypothesis)
STATUS: dp22_theorem61', dp22_theorem61_iff', hoCircleLike' proved (no named hypothesis)
STATUS: non-vacuity (§8) proved, including the batch-201 omission
```

**Items: proved** — all of the above. **Refuted** — none. **Open** — none of this batch.

**Omissions** (also in `OPEN.md`).
* The certificate of commission §4.4 (with one sweep per period, survival fails) is not formalized;
  the commission asks for it only "if it is cheap".
* The certificate welcome in commission §7 item 3 (two chains, each crooked in the union of two
  consecutive columns, whose concatenation is not crooked in the columns it refines) is not given.
  The analysis is in ledger BJ.43.
* `crooked_of_tight_pat'` (commission (3.9)) is not stated as a separate lemma: the enlarged form
  of `crooked_of_tight_pat` is proved inline, for runs, as `CircDescr.runChain_crooked`
  (`HPC/BJ59/CircFibre.lean`).

**Shape changes.**
* *The sweep lemma* (not in the skeleton; commission §4.1 leaves the shape free). Blocks have a
  fixed length `L` (`[n L, (n + 1) L]`, consecutive blocks sharing their junction), with windows
  `b n`, `t n` and directions `up n`, alternating; the first and last blocks of the interval are
  partial automatically. Two forms are proved:
  * `sweep_lemma` (`HPC/BJ59/Sweep.lean`): at most **two** events in the interval. This is the form
    used by `exists_sweepPattern`: an interval of length `P + 3` contains at most two multiples of
    `P = 3L`, and junctions inside a period keep the window. With at most two events, Case 2b of
    the commission's proof cannot occur.
  * `sweep_lemma3` (`HPC/BJ59/Sweep3.lean`): at most **three** events, the commission's bound, with
    Case 2b carried out as a statement about the windows alone (`sweep_window_case2b`). It is
    tested on a window with exactly three events and shown sharp by a walk with four events that
    is not crooked (§6).
* *Survival in `surv`/`exists_sweepPattern`*, *`circ_step`*, *`CircDescr`*: as in the skeleton.
* The skeleton's single file is split (above). The skeleton's §§2–5 declarations were moved,
  textually unchanged, to the files named in the docstring of `HPC/BJ59/BJ59E.lean`.

## 1. §2–§3: circular descriptions and the recognition theorem (`CircDescr.lean`, `CircFibre.lean`, `CircMap.lean`)

Following commission §3:
* (3.1) `isCompact_M`, `isConnected_M`: `M = ⋂ closure U_k` (`M_eq`), each `U_k` preconnected
  (consecutive links meet, periodicity).
* (3.2) `inter_M_nonempty`: nested indices `t_j` with `π_j t_{j+1} = t_j`,
  `π_j (t_{j+1} + 1) = t_j + 1`, and the nested compact sets `closure L_j t_j ∩ closure L_j (t_j+1)`.
* (3.4) runs: `runA`, `runB`, `runChain k y`, a `Chain X` of the links whose arcs contain `y`;
  `fib_eq_iInter`.
* (3.5) `fib_meets` by `surv` and nested closures; fibres are nonempty and nontrivial
  (`fib_nonempty`, `fib_nontrivial`).
* (3.9) `runChain_crooked`: a run of level `k + 1` is crooked in the run of level `k` (tightness
  inside runs, `tight_run`, with the integer shift zero; `crook` on the window enlarged by one index
  at each end).
* (3.10) `isPseudoArc_fib`: continuum (`isContinuum_fib`), snake-like (`isSnakeLike_fib`),
  hereditarily indecomposable (`isHereditarilyIndecomposable_fib`, through
  `Description.theorem10_core`).
* (3.3), (3.6), (3.7) the base map `fmap : M → Circle`, `p ↦ circP 1 (yOf p)`:
  `exists_fib`, `fib_add_int`, `fmap_eq_iff`, `continuous_fmap`, `surjective_fmap`,
  `isOpenMap_fmap`.
* (3.11) `traceChain k : CircChain Δ.M (Δ.N k)` and `isCircleLike_M`.
* `isCircleOfPA` through `isCircleOfPA_iff` (batch 198).

## 2. §4: sweep patterns (`Sweep.lean`, `Sweep3.lean`, `SweepPattern.lean`)

`PatCrookedOnZ` (crookedness for integer indices) and its transfers to and from `PatCrookedOn`. The
sweep lemma: §0. `sweepX m S` is the pattern of commission §4.2: sweeps of length
`L = S z(m−2) z(m−1)`, three per period, period `j` with window `[swB m j, swT m j]`,
`swT m j = ⌊(j + m)/2⌋`, `swB m j = ⌈(j + 2 − m)/2⌉`, sweep `n` up iff `n + m` is even (the
commission's rule, since `n = 3j + r` has the parity of `j + r`). `exists_sweepPattern` collects
period, unit steps, slowness, nesting, survival and crookedness (`sweepX_crook`, from
`sweep_lemma` with at most two events per window of length `P + 3`).

## 3. §5: the circular planar step (`CircJoints.lean`, `CircCover.lean`, `CircDescent.lean`, `CircStd.lean`, `CircStep.lean`)

* Joint positions for lifted patterns (`CircJ.jointZ`): batch 84's `Joints` applied to one finite
  window of the lifted pattern (indices `−M, …, QN + M − 1`, `M = S + 3`), with a shift lemma
  (`P_shift`) showing that joint positions are local; `link_facts_Z` is `Joints.link_facts` for
  every integer index.
* The ramps `Ramp.phat` (commission "Interpolation") and the shear on the cover `cover`, a
  homeomorphism of `ℝ × ℝ` for every continuous `g` (explicit inverse).
* Descent (`Descent.descHomeo`): through `E N (u, v) = exp (v + iπu/N)`, continuous local sections
  from the logarithm, extension by `0 ↦ 0` from the linear bound on the second coordinate of the
  cover map and of its inverse.
* `stdCircLink_meet_iff` (and `stdCircLink_meet_iff'` for every `N ≠ 0`).
* `circ_step`: the four properties read off on the cover, as commission §5.

## 4. §6: the assembly and the corollaries (`CircPlane.lean`, `BJ59E.lean`)

Levels `(N, Φ, m, o)` as commission §6.1 (`lvl`), and `planeDescr : CircDescr Pt` with the fields
of commission §6.2 (`CircPlane.arcNest`, `CircPlane.surv`, `CircPlane.crook`, `pat_period`, …).
`exists_circDescr_plane := ⟨planeDescr⟩`; `bjPlaneExample` is the skeleton's proof. The five
corollaries are the batch-199–201 results with `BJThm10` and `BJPlaneExample` discharged.

**Named hypotheses.** `ho16_classification₄` and `ho16_classification_plane₄` take no named
hypothesis: their statements carry none, and their proofs apply `ho16_classification₃` and
`ho16_classification_plane₃` to `bjPlaneExample`, a theorem. Their axioms are `propext`, `Classical.choice`, `Quot.sound` (§7).

## 5. Ledger

New section "Bing–Jones §7, the plane example (batch 202)" in `LEDGER.md`, items BJ.41–BJ.47:
BJ.41 the chains `D_i` are not constructed (commission §7 item 1); BJ.42 M a continuous circle-like
circle of continua, unargued (item 2); BJ.43 the elements of `G` are pseudo-arcs, unargued, with
(9) checked at 400 dpi and the commission's doubt shared (item 3); BJ.44 the arc collection (item
4); BJ.45 route (item 5); BJ.46 the labels of the figure on p. 191 (new; slip); BJ.47 the letter
`G` used twice (new; harmless). I would count BJ.43 as a defective proof; I count nothing myself,
and the counts are left unchanged (24 false printed statements, 18 defective proofs).

**Quotations.** Every quotation (pp. 189–191) was checked against page images at 200 dpi, and (9)
and the labels of the figure against crops at 400 dpi; they agree with the page images.

## 6. Non-vacuity (`NonVac202.lean`, `NonVac202b.lean`, `NonVac202c.lean`)

* `CircDescr`: `exists_circDescr_plane` is the witness. Degenerate inputs: in every circular
  description `N k → ∞` (`CircDescr.N_tendsto`), so constant `N` is impossible; `four_le` and
  `five_le_lam` exclude the small cases.
* The sweep lemma: on a single sweep (`nonvac_sweep_single`) and on a window of the sweep pattern
  with exactly two events (`nonvac_sweep_two_events`, `sweep_event`); `sweep_lemma3` on a window
  with exactly three events (`nonvac_sweep_three_events`); and **a sweep walk with four events
  that is not crooked** (`nonvac_sweep_four_events`): blocks of length 2, windows of width 1 or 2,
  every structural hypothesis of the sweep lemma, exactly four events in `[0, 10]`, values
  `0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4` there, no return from 3 to 1 after reaching 3. On `[0, 7]` the
  same walk has exactly three events and is crooked (non-vacuously: it takes the values 0 and 3).
* `exists_sweepPattern`: the hypotheses `m ≥ 5`, `S ≥ 1` are used by `planeDescr` at every level;
  the certificate of §4.4 is not given (§0).
* `circExp`, `stdCircLink`, `stdCircZone`: `circExp_zero` (for `N = 0` everything goes to the ray
  `{(e^v, 0)}`), `not_stdCircLink_meet_iff_zero` (the criterion fails for `N = 0`),
  `stdCircLink_meet_small` (for `N = 1, 2, 3` both sides hold for all `s`, `t`).
* `circ_step`: its hypotheses hold for the stuttered identity `x t = ⌊t / Q⌋` with `Q ≥ S`
  (`nonvac_circ_step_hyps`).
* **The omission of batch 201**: `exists_snakeArcPA` (a half of the plane example is a continuous
  snake-like arc of pseudo-arcs), and from it non-degenerate witnesses `nonvac_bjThm10`,
  `nonvac_bjStep`, `nonvac_bj_theorem8_cor_sub`, `nonvac_bj_theorem5_window` (the last uses
  `exists_window_set`).

## 7. Axioms

`doc/batches/audits/axioms-batch202.txt` (254 lines, one per new theorem; added to
`Axioms.lean` as the group "Bing–Jones 1959, V (batch 202)"): 231 depend on `[propext, Classical.choice, Quot.sound]`, 22 on `[propext, Quot.sound]` (arithmetic of the sweep pattern: `swT_even`, `swT_odd`, `swB_even`, `swB_odd`, `swD_even`, `swD_odd`, `swD_eq`, `swK_mul`, `swK_eq`, `swK_pos`, `S_dvd_swK`, `sweepL_ge`, `stut_zero'`, `stut_last`, `sweepX_block`, `swVal_last`, `swT_add2`, `swB_add2`, `swD_add2`, `sweepL_pos`; and `Cert4.cert4_range`, `Cert4.cert4_end`), 1 on `[propext]` (`sweepQ_eq`). `sorryAx`: none.
`axioms.txt` is regenerated (4030 lines, 254 more than batch 201's 3776; the first 3776 lines are
unchanged and the last 254 are `doc/batches/audits/axioms-batch202.txt`). The theorems of the skeleton and
the main new results all depend on `[propext, Classical.choice, Quot.sound]`:

| theorem | axioms |
| --- | --- |
| `CircDescr.isCompact_M`, `CircDescr.inter_M_nonempty`, `CircDescr.fib_meets`, `CircDescr.isCircleOfPA` | `propext`, `Classical.choice`, `Quot.sound` |
| `sweep_lemma`, `sweep_lemma3`, `exists_sweepPattern` | the same |
| `stdCircLink_meet_iff`, `circ_step` | the same |
| `exists_circDescr_plane`, `bjPlaneExample` | the same |
| `ho16_classification₄`, `ho16_classification_plane₄`, `dp22_theorem61'`, `dp22_theorem61_iff'`, `hoCircleLike'` | the same |

## 8. Delivery

`doc/batches/batch202-files.tar.gz` with every file added or changed in this batch (the new Lean
files, the edited files, the commission and skeleton copies, this report, the audit and the
manifest), and `doc/batches/batch202-MANIFEST.txt`. As in batch 201, the tarball also carries
every Lean file under `HPC/Hagopian/`, `HPC/Jones/` and `HPC/Span/` in its current form (listed as
`C`).

## 9. What remains

No named input of Part G remains. Optional, from batch 199: `isAtriodic_of_atomic` (not
attempted). Optional certificates of commission §4.4 and §7 item 3 (§0).
