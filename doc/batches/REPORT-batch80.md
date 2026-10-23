Commission read: `COMMISSION-batch80.md`, with its skeleton `Theorem5.lean` (saved as `HPC/PseudoArc/Theorem5.lean`; `import HPC.PseudoArc.Theorem5` added at the end of `HPC.lean`).

# Report — batch 80: Theorem 5, Theorem 6, Theorem 12 unconditional

## 0. Counterexamples and statement changes (reported first)

**Counterexample: the skeleton's `theorem6Pos_shift` and `patternFollowing` are false.** They have
no hypothesis `P ≠ Q`. Take the one-point space `X = PUnit` with `P = Q`. Give every level one link
(the whole space) and set `ε i = 1/(i+1)`. This is a `Description`: crookedness holds vacuously
with one link, and `IsFrom P P` holds for a one-link chain. Take the pattern `0, 0` of length
`N = 2` in the first level. It is an `IsPattern`: it starts at link `0` and ends at link
`n 0 - 1 = 0`. A chain with two links cannot be a chain from `P` to `P`, because `P` would have to
be in the first link only and also in the last link only. The Lean statements are:

* `HPC.Description.not_theorem6Pos_shift_unconditional`: the unconditional form of
  `theorem6Pos_shift` is false.
* `HPC.Description.not_patternFollowing_unconditional`: the unconditional form of
  `patternFollowing` is false.
* `HPC.Description.unitDescription_not_theorem6`: `Theorem6Statement` from `Statements79.lean`
  (any level `j`) also fails for this description.

All three are proved in `HPC/PseudoArc/Theorem5.lean` with axioms `[propext, Classical.choice, Quot.sound]`.

**Changes made.**

* `theorem6Pos_shift` and `patternFollowing` now take `(hPQ : P ≠ Q)`. The skeleton's two
  statements are kept in the file, commented out, with the reason written next to them.
* `theorem12`: the statement is unchanged; it already assumed `P₁ ≠ Q₁` and `P₂ ≠ Q₂`. Its proof
  now passes these to `patternFollowing`.
* `theorem5`: the statement is unchanged. `Theorem5Statement` is proved exactly as written in
  `Statements79.lean`.
* **`Statements79.lean` is not modified.**

**Definition audit.** I re-read `Theorem5Statement`, `IsPatternFromTo`, `Chain.IsConsolidationOn`,
`Theorem6(Pos)Statement`, `IsPattern`, `PatternFollowing`, `Description`, `IsCrookedIn'`,
`IsFrom` and `ofBlocks`. Apart from the missing `P ≠ Q` above, none of them makes a target false
or vacuous. Two readings matter for the proof:

* In `Theorem5Statement`, "consolidation of the links of `D_j` contained in `D_2(u, v)`" means
  *every* link of `D_j` inside a link `d(2)_s` with `u ≤ s ≤ v`. At a deep level this includes
  links of `D_j` that leave `d(2)_u`, go some way into `D_2(u, v)` and come back to `d(2)_u`
  without ever reaching `d(2)_v` (and the same for `v`). `E` must place all of them, and each
  such excursion must itself follow the pattern (§3, "excursions").
* `u < v` follows from the hypotheses: `u = v` would make `closure d(2)_u` disjoint from itself,
  but links are nonempty.

## 1. Targets

| target | status |
|---|---|
| 1. `theorem5` : `Theorem5Statement Δ` under `[CompactSpace X]` | **proved as stated**, `sorry`-free |
| 2. `theorem6Pos_shift` | **proved with the added hypothesis `P ≠ Q`** (false without it, §0) |
| 3. `patternFollowing` | **proved with `P ≠ Q`** (false without it, §0) |
| 3. `theorem12` (statement unchanged) | **proved, unconditional**: Bing's uniqueness theorem for descriptions |
| extra: `theorem6` (`Theorem6Statement Δ`, any `j`, with `P ≠ Q`) | proved |

**Axioms and build.**

* `axioms-batch80.txt` is the output of `lake env lean Axioms80.lean`. Every listed declaration
  (`theorem5`, `theorem6Pos_shift`, `theorem6`, `patternFollowing`, `theorem12`, the
  counterexamples, and the cores `PatCore.realize`, `PatCore.run_lift`, `T5.assemble`) depends
  only on `[propext, Classical.choice, Quot.sound]`.
* `lake build HPC` completes with 8213 jobs. The only `sorry` warning in the build is still
  `theorem3_end` (`HPC/Fold/Theorem4.lean`), which is parked and not used here.
* The only literal `sorry` in `Theorem5.lean` is inside the commented-out false skeleton
  statement.

**Files (all new except `HPC.lean` and `Theorem5.lean`):**

| file | content |
|---|---|
| `HPC/PseudoArc/PatCore.lean` | the combinatorial setting (`Al`, `Real`, `Setting`, `Slow`, `Good`) and elementary lemmas |
| `HPC/PseudoArc/PatMain.lean` | the induction: cases (P4)–(P6), `ih_all`, **`realize`** |
| `HPC/PseudoArc/PatGeom.lean` | chain distances, thick readings, crookedness → `Setting`, block consolidations; **`theorem6Pos_of_ne`** |
| `HPC/PseudoArc/PatRuns.lean` | time shift and reversal, ramps up and down, excursions, **`run_lift`** |
| `HPC/PseudoArc/T5Read.lean` | the coarse reading with end zones for Theorem 5 (`Setup`, `rd`, soundness, forcing, slowness) |
| `HPC/PseudoArc/T5Runs.lean` | the extended pattern `xext`; lift over one run (`run_lift_geom`) |
| `HPC/PseudoArc/T5Assemble.lean` | maximal runs; the crossing run (`exists_crossing`); run boundaries |
| `HPC/PseudoArc/T5Chain.lean` | lifts over all runs (`lift_all`); the chain `E` (`assemble`) |
| `HPC/PseudoArc/T5Main.lean` | choice of the deep level (Bing's (P1)); **`theorem5_of`** |
| `HPC/PseudoArc/Theorem5.lean` | the skeleton, completed; the counterexamples |

## 2. The route, and the statement that inducts (§4.1 of the commission)

The proof does not transcribe Bing's induction over geometric configurations. It isolates a
**purely combinatorial statement about integer sequences**, `HPC.PatCore.realize`, proves that by
induction, and derives Theorems 6 and 5 from it by geometry at one deep level.

* **Fine reading `σ : ℕ → ℤ`.** This is the reading of a fine chain `F = D_{m+1}` in `R = D_m`:
  time `f` is a link of `F`, and `σ f` is the index of a link of `R` containing it. It moves by at
  most one per step. It is *crooked*: if `|σ f − σ f'| ≥ 3` with `f < f'`, there are times
  `f < r < s < f'` with `σ r` within 2 of `σ f'` and `σ s` within 2 of `σ f`. This is
  `Chain.setting_of_crooked`, from `IsCrookedIn'` of `D_{m+1}` in `D_m`.
* **Coarse reading `τ : ℤ → ℤ`.** This reads positions of `R` as links of `D_1`. It is `w`-slow:
  positions at most `w` apart read values at most one apart.
* **Allowed values.** A value `v` is allowed at time `f` with radius `d` (`Al`) if some position
  within `d` of `σ f` reads `v`.
* **What `realize` says.** Let `x` be a pattern of length `N` whose first value is its minimum
  and whose last value is its maximum. Suppose `w ≥ 4N + 10`, the readings `τ(σ f)` stay between
  these two values, and they start and end at them. Then there is a lift `φ` moving by at most
  one, from index `0` to `N − 1`, with `x(φ f)` allowed at every time `f`.

**The inducting statement is `PatCore.IH`.** It says that lifts exist over every time interval
shorter than `n`, for every slow reading `τ` and every configuration satisfying `Good`. `Good`
generalises `realize` in two ways Bing's text needs:

1. The lift is over an arbitrary sub-interval `[a, b]` of times and an arbitrary sub-pattern
   `[p, q]`.
2. The end conditions are *anchors with a radius budget*: `x p` is allowed at `a`, and `x q` at
   `b`, within radius `e`, with `e + 2(q − p) ≤ B` and `w ≥ 2B + 10`.

The anchors are the combinatorial form of Bing's "end collections" `A`, `B` (§4.1). `realize` is
`IH` for all `n` (`ih_all`, strong induction on `b − a`) applied with `e = 0`.

**Downward patterns** (§4.1, the `G` piece) come from symmetries of the combinatorial statement,
not from reversing `D_1`:

* negating the readings (`real_of_neg`, `slow_neg`);
* reflecting the pattern (`real_reflect`);
* reversing time (`setting_rev`, `real_of_rev`).

Crookedness is invariant under time reversal.

**Theorem 6** (`PatGeom.theorem6Pos_of_ne`). Take `W = 4N + 10`. Choose `m` with two properties:
every `W + 1` consecutive links of `D_m` lie in one link of `D_1` (a *thick reading*,
`eventually_thick`), and `D_{m+1}` has at least `N` links. Then apply `realize` to
`σ : D_{m+1} → D_m` and to the thick reading, clamped to `ℤ`. The lift is a block map
(`IsBlockMap`), and `E = ofBlocks` is a chain from `P` to `Q` following the pattern, at level
`j = m + 1 > 0`. `P ≠ Q` is used for `n_{m+1} ≥ N` (`n_tendsto_atTop`), and §0 shows it cannot be
dropped.

**Theorem 5** (`T5Main.theorem5_of`). The levels are `D_0, D_1` (Bing's `D_1, D_2`), then `D_m`,
then `D_{m+1} = D_j`.

* **The reading.** The coarse reading `T5.rd` of `D_m` has two extra end values:
  - positions within `W` of a link meeting `d(2)_u` read `h − 1`;
  - positions within `W` of a link meeting `d(2)_v` read `k + 1`;
  - a ring of width `W` around each zone reads `h` (resp. `k`);
  - elsewhere a position reads `ρ(τ1 p)`, where `τ1` is a thick reading of `D_m` in `D_2` and
    `ρ` sends `d(2)_t` (`u < t < v`) to a link of `D_1(h, k)` containing it.
* **The pattern.** The extended pattern is `xext = h − 1, x_1, …, x_N, k + 1`, with
  `W = 4(N + 2) + 10`.
* **Soundness** (`Setup.sound`). Near a link `f` of `D_j` in `D_2(u, v)`:
  - reading `h − 1` forces `f ⊆ d(1)_h`, and reading `k + 1` forces `f ⊆ d(1)_k`;
  - a value `c` in `[h, k]` forces `f ⊆ d(1)_c` and `f` disjoint from `d(2)_u ∪ d(2)_v`.
* **Forcing** (`force_u`, `force_v`). Near a link meeting `d(2)_u`, only `h − 1` is read, which
  forces lift index `0`. Near `d(2)_v`, only `k + 1` is read, which forces index `N + 1`.
* **Slowness** (`slow_rel`) holds between positions near links in `D_2(u, v)`. Each run's reading
  is clamped to such positions.
* **Runs.** The links of `D_j` in `D_2(u, v)` fall into maximal runs. Each run begins and ends at
  a link inside `d(2)_u` or `d(2)_v` (`touch_of_boundary`, plus `P`/`Q` for runs at the ends of
  `D_j`). Each run is lifted (`run_lift_geom`):
  - crossings `u → v` and `v → u` by the core, forwards or time-reversed;
  - excursions `u → u` and `v → v` by `run_exc` / `run_exc_top`, which split at the highest (or
    lowest) time and lift up and back down.
* **The chain `E`.** Shifting the lifts down by one and clamping to `[0, N − 1]` gives the block
  of each link. One crossing run (`exists_crossing`, found by an intermediate value argument on
  the reading of `D_j` in `D_2`) goes from index `0` to `N + 1`. That makes every block nonempty
  and consecutive blocks adjacent, so the unions of the blocks form a chain `E` (`assemble`).
* **The three conclusions follow from soundness:**
  - `E` follows `x`;
  - `E` is a consolidation of the links of `D_j` in `D_2(u, v)`;
  - no interior link of `E` meets `d(2)_u ∪ d(2)_v`.
* `j = m + 1 > w`.

## 3. Bing's paragraphs (P1)–(P6)

**(P1) The mesh constant.** Proved, in a changed form.
* `eventually_thick` / `eventually_thick_at`: use a Lebesgue number for the cover of
  `closure (D_{i+1})^*` by the links of `D_i`, together with the mesh tending to `0`.
* `eventually_zone`: a thickening of the compact set `closure d(2)_u` lies inside `d(1)_h`
  (`IsCompact.exists_thickening_subset_open`). The same lemma with `O = (closure d(2)_v)ᶜ` gives
  the separation of the two end zones.
* **Not in Bing.** The windows must be as long as the pattern: `W = 4N + 10`, or `4(N+2) + 10`
  for Theorem 5. Bing's fixed "five-linked subchains" do not suffice for this route.
* **Not in Bing.** The lemma `Chain.dist_le_of_mem_links`: points of links `k` apart are within
  `(k + 1)·mesh`.
* Compactness enters only here (§4.3 of the commission).

**(P2) Base case.** Bing's `n = k − h + 1` is not a separate case. The base cases of the induction
are:
* `case_const`: a constant pattern, by the ramp `real_ramp`;
* `case_amp1`: two adjacent values with neither end value repeated. Crookedness is not needed
  here; `amp1_both` finds a time near which both values are allowed.

Monotone patterns go through the general cases.

**(P3) Induction.** Bing's minimal counterexample on the pattern length `n` is replaced by strong
induction on the *length of the time interval* (`ih_all`). The pattern length is controlled by
the invariant `q − p ≤ b − a` in `Good`.

**(P4) Case `x_1 = x_2`.**
* `case_plateau`, and `case_plateau_end` for a repeated last value.
* The sub-pattern `x_2, …, x_n` is lifted over `[a + 1, b]`, and time `a` is prepended at index
  `p`.
* **What the elided step required: an anchor with slack.** After dropping the first time, `x_2`
  is known to be allowed at time `a + 1` only within radius `e + 1`, not `e` (`al_move`). So the
  induction hypothesis must accept anchors with a radius. That is the budget `e` in `Good`. It
  grows by one per plateau step, is bounded by `e + 2(q − p) ≤ B`, and needs `w ≥ 2B + 10`.
* This is the combinatorial content of Bing's "`e_1 ⊆ f_1 + d(2)_u`, `e_2 ⊆ f_1 + f_2`": the
  first two links of `E` share `f_1`, which costs one unit of slack.
* No hypothesis on the continuum beyond Bing's was needed; in particular nothing like
  "`closure d(2)_u` disjoint from `f_2`".
* In Theorem 5, the property "only the first link meets `d(2)_u`" is not carried through the
  induction at all. It is enforced afterwards by the end-zone reading: `force_u` gives lift
  index `0`, and soundness gives disjointness for all interior indices.

**(P5) The pattern returns to its minimum.** `case_return`, as Bing describes it.
* Crookedness of the fine reading is applied between the start of the interval and the first
  time above the peak of the pattern before its return. This splits the interval into an ascent,
  a descent and the rest, each lifted by the induction hypothesis.
* The three-chain split is the crookedness clause of `D_{m+1}` in `D_m`, as §4.4 says. It is used
  through `Setting.crook`, and "links of `D_m`" are converted into "inside a link of `D_1`" by the
  slow reading, as in (P1).
* The claim to check in §4.4 ("`D_{m+1}(p, z)` avoids `d(2)_v`") has no counterpart in the
  combinatorial induction. In Theorem 5 it is replaced by the forcing lemmas.

**(P6) The pattern never returns to its minimum.** `case_noreturn`.
* After the last time the reading is at the minimum, the rest of the pattern is lifted.
* Before that time, each excursion of the reading above the minimum is lifted by splitting at its
  highest time: up, then back down by time reversal.
* Bing's collection `W'` (links of `W` meeting `d(1)_h`) has no separate counterpart. Its role,
  fixing where the lift of `x_2, …, x_n` may start, is taken by the anchor condition of `Good`.

**Beyond (P1)–(P6): excursions in Theorem 5.** The runs of `D_j` in `D_2(u, v)` that leave
`d(2)_u` and return to it (see §0) are not treated in Bing's text. They need
`PatRuns.run_exc` (and `run_exc_top` for `v`). The window length `W ≥ 4(N + 2) + 10` guarantees
that such an excursion is long enough in time to climb the pattern as far as its reading climbs.

## 4. Answers to the specific questions of §4

1. *Generalised statement.* The statement that inducts is the combinatorial `PatCore.IH` /
   `Good` (§2), not a geometric `Theorem5'`. Downward patterns come from symmetries: negation,
   reflection and time reversal. `Theorem5Statement` follows from `realize` (via `run_lift`)
   together with the geometry in `T5*.lean`. The only restriction is `b = 2`, as stated; the
   intermediate levels `m`, `m + 1` are chosen inside the proof.
2. *The elided step (P4).* It required an anchor radius budget in the induction hypothesis
   (§3 (P4)), and no extra geometric hypothesis.
3. *Compactness.* Used only in (P1): Lebesgue numbers and thickenings of compact closures.
4. *Three-chain split.* It is the crookedness of `D_{m+1}` in `D_m` (`setting_of_crooked`).
5. *Theorem 6 from Theorem 5.* Theorem 6 was proved directly rather than from Theorem 5. It does
   need `P ≠ Q`: this is the §0 counterexample, which also refutes `Theorem6Statement`. No shift
   to a deep level is needed in the statement, since the proof picks `j = m + 1` itself.
