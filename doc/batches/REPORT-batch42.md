# Report: batch 42 — the general statement, and what the branch method is missing

Two new Lean files, `HPC/Fold/Profile.lean` and `HPC/Fold/Span9Profile.lean`; the commissioned
`HPC/Fold/General.lean` is added as received, with a paragraph appended to its module docstring
recording the state after this batch. Root `HPC.lean` imports the three. No earlier Lean file is
touched. The searches are `census-batch42.c` (exhaustive and random generation of members of the
faithful model), `census-batch42b.c` (the windows of Bing's chains), `census-batch42c.c` (long
random members), `census-batch42d.c` (the greedy three-leg engine at `P = L + 4`, as an
automaton), `census-batch42e.c`, `census-batch42f.c`, `census-batch42g.c`, `census-batch42h.c`,
`census-batch42i.c` and `census-batch42j.c` (exhaustive over **arms**, with crookedness tested
exactly).

## 0. No counterexample

**No counterexample to `theorem3` was found.** Nothing in this batch suggests one: every actual
pair examined, in both open branches, is served, and by a walk with two turning targets.

## 1. §2.1 — the two open branches are inhabited, and every actual pair in them is served

The corpus is stated exactly: **every contiguous window of `bing 0 N`, `N = 9, 10, 11`, whose
range of levels is exactly nine** — 1 694 639 windows — and every basepoint of every such window.
A window of a crooked sequence is a crooked sequence (`isCrookedIvF_restrict`, batch 30), so each
(window, basepoint) is an actual pair of the faithful model. This is `census-batch42b.c`.

| branch | pairs found | unserved | least turning targets |
|---|---|---|---|
| `ρ i = L + 4`, both arms `HighAt (L+1) (L+8)` | 10 588 | 0 | 2, in every case |
| `ρ i = L + 5`, both arms `LowAt (L+1) (L+8)` | 11 184 | 0 | 2, in every case |

More than that: **one walk serves every pair of a branch** in this corpus — the Λ-walk
`L+3, L+4, …, L+8, L+7, …, L+1` at the branch `L + 4`, and its mirror
`L+6, L+5, …, L+1, L+2, …, L+8` at the branch `L + 5`. Both were checked against every hit,
by exact `FoldsOnto` (bitmask reachability), not by a sufficient condition.

So the branches are inhabited, the pairs in them are served, and they are served cheaply. The
census over arm classes of batches 40–41 is not contradicted: it quantifies over a larger class.

An attempt was also made to census the model itself rather than a chain in it. `census-batch42.c`
enumerates every member of `IsCrookedIvF` with levels in `[0, 9]`: the count grows by a factor of
about 3.8 per link (20, 76, 310, 1 268, …, 59 945 816 at length twelve), and no member of span
nine is short, so exhaustion is out of reach; random members of length 300 grown with backtracking
(`census-batch42c.c`) never reached span nine either. The corpus above is therefore the honest
one, and it is a corpus of windows of Bing's chains.

## 2. §2.2 — what distinguishes actual pairs from the classes: *when*, not *what*

This is the substantial finding of the batch, and it is now a theorem rather than an observation.

A fold assigns to the index `j` of an arm a walk time `β j` with `β 0 = 0` and steps of at most
one, so **`β j ≤ j` always**. Every condition in the repository's vocabulary — `HighAt`, `LowAt`,
`CrookUp`, the flags `E`, `E2`, `R`, `S` of the greedy engines — records *which* events have
happened in an arm's past, never *how many steps* they took. But the index bound is exactly a
statement about how many steps, and at span nine it is what decides the fold.

`HPC/Fold/Profile.lean` replaces the event vocabulary by the **ascent profile**, and proves it
exact:

> **`foldsOnto_lam_iff_profile`.** Let `f` be a 1-Lipschitz arm with values in `[L, H]`, starting
> within one of `p` (so the arm need not start *at* the base of the walk, which is what `S3`
> requires and what Lemma F1 did not allow), and let `κ = max (H - 1) p`. Then `f` folds onto the
> Λ-itinerary `lamCenter p H L` **iff** `CritLamProfile f p H`, and, for a Lipschitz arm, that
> criterion says (`critLamProfile_iff_of_isLip`):
>
> *before the arm ever drops to `p - 2`, it stands at the level `κ - 1` at an index at least
> `κ - p`.*

`foldsOnto_vee_iff_profile` and `critVeeProfile_iff_of_isLip` are the mirror statements for the
V-itinerary. The time assignment is explicit and two-phase (`pseq`): the largest time the level
allows on the ascending leg, and, past the peak time, the largest time on the descending leg.

The index clause is the whole difference. Dropping it makes the criterion false: the arm

```
4 5 5 6 7 6 5 4 3 2 1                (L = 0, p = 3, κ = 8)
```

stands at `κ - 1 = 7`, and satisfies the event criterion `CritLam` of Lemma F1 through its
non-ascending step, but it reaches `7` at index four, one step too early to be at the peak time,
and it does not fold. `census-batch42f.c` checks the equivalence exhaustively — 713 817 arms of
length up to thirteen, at four different `(p, L, H, start)` — with zero discrepancies in either
direction, and finds 204 arms on which the event criterion `CritLam` holds while the fold fails.

And the index clause is exactly what **crookedness** supplies, which is why actual pairs behave
better than the classes. `census-batch42g.c` computes, by exhaustion over arms with `CrookUp` and
`CrookDown` tested over all pairs, the least index at which a crooked arm can stand `t` levels
above its start:

| levels climbed | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| least index | 1 | 2 | 4 | 7 | 13 |

and the same downwards. The first four of these are proved in Lean (`crookUp_climb3`,
`crookUp_climb4`, `crookUp_climb5` — the last with the provable bound twelve rather than the
observed thirteen — and `crookDown_fall3`, `crookDown_fall4`).

So the answer to §2.2 is: **an actual arm climbs slowly, and a class member need not.** The
automaton of batches 40–41 keeps the set of legal walk times and so does see the index bound, but
it approximates crookedness by a clause family; the clause family does not imply the timing law,
and the timing law is what the branch needs.

## 3. What this closes at span nine, and what is left

`HPC/Fold/Span9Profile.lean` applies the criterion to the two open branches. At the branch
`ρ i = L + 4` the two walks are the Λ-walk based at `L + 3` and the V-walk based at `L + 5`, and
the theorems are

* `s3_span_nine_mid_low_of_lamProfile` — served if, for **each** arm, before it drops to `L + 1`
  it stands at `L + 7` at an index at least five (the exact criterion, no crookedness needed);
* `s3_span_nine_mid_low_of_veeProfile` — served if, for each arm, before it rises to `L + 7` it
  stands at `L + 2` or below at an index at least four;
* `s3_span_nine_mid_low_of_top` — served if each arm has been at the ceiling `L + 8` before it
  ever drops to `L + 1`. Here the index is *not* a hypothesis: `crookUp_climb4` supplies it;
* `s3_span_nine_mid_low_of_floor` — served if each arm has been at `L + 1` before it ever rises
  to `L + 7`; the index comes from `crookDown_fall3`;

and `s3_span_nine_mid_high_of_veeProfile`, `s3_span_nine_mid_high_of_lamProfile`,
`s3_span_nine_mid_high_of_floor`, `s3_span_nine_mid_high_of_top` are the four statements at the
mirror branch `ρ i = L + 5`, with base `L + 6` and `L + 4` respectively.

What is left is exactly one configuration: a basepoint whose two arms meet **different** ends of
the band first, one arm being of Λ-type and the other of V-type. That the two types cover every
arm is checked exhaustively and not proved: `census-batch42j.c` enumerates every arm of the branch
at `L + 4` of length up to **21** — 754 567 643 of them, with `CrookUp`, `CrookDown`,
`HighAt (L+1) (L+9)`, `HighAt (L+1) (L+8)` and `LowAt L (L+7)` all tested exactly — and finds
**no arm failing both criteria**. (`census-batch42i.c` is the same run with the two
crookedness-free announcements in place of the criteria, also with no failure up to length 20.)

Two negative facts worth recording, both from this batch:

* the branch is **not** served by one walk. The arm `4 3 2 2 1` (levels as offsets from `L`)
  satisfies every condition of the branch and does not fold onto the Λ-walk, and the arm
  `4 3 3 3 3 3 3 3 3 3 4 5` does not fold onto the V-walk (`census-batch42h.c`). A further split
  is unavoidable, and the split found here — which end of the band the arm meets first — is the
  one the criterion dictates.
* the repository's greedy three-leg engine does **not** extend to the basepoint `P = L + 4`
  unchanged. `census-batch42d.c` runs the greedy of `HPC/Fold/Leg3.lean` as an exact automaton
  over `(level, greedy time, monotone flags)`; at `P = L + 3`, `K = L + 5`, `H = L + 7` the
  repository's floor announcement `R` keeps it legal, as it must, but at `P = L + 4`, `K = L + 8`,
  `H = L + 9` the announcement that keeps it legal is the much stronger *"before ever dropping to
  `L + 1` the arm has been at `L + 8`"*, which actual arms of the branch do not satisfy. The
  greedy of `Profile.lean` is a different one, and it is exact.

## 4. §2.3 — a uniform statement

Not proved, and this batch does not claim a route to it. What it does supply is the shape one
should have: for a walk made of monotone legs, the set of legal times at an index is an interval
per leg, so the exact criterion is a *profile* condition — a level reached at an index at least
the number of steps the walk needs to get there — and it is decidable by the arm's own timing.
`Profile.lean` proves this for the one-turn walks (Λ and V) in both directions, at any band, any
base, and any start within one of the base. The same argument with one more phase gives the
three-leg walks of `HPC/Fold/Leg3.lean`, and with `k` phases the `k`-leg walks; the obstruction to
`S3` is then not the shape of the walk but the pairing: for each of the two arms the criterion
picks out which walks serve it, and what has to be shown is that the two sets of walks meet. The
cross-arm crookedness clause — the one that fires with `s` on one arm and `t` on the other, which
no fold lemma in the repository uses — is what should force that, and the argument in §3's first
negative fact is an instance of it: if one arm dives to `L + 1` at once while the other reaches
`L + 9`, the clause between those two times forces an `L + 8` on the second arm before it has been
low, which the branch condition `HighAt (L + 1) (L + 8)` forbids.

## 5. Verification

`lake build HPC` succeeds. The new files contain no `sorry`; the `sorry`s in the project are the
commissioned open statement of `HPC/Fold/Open.lean` and the two commissioned targets of
`HPC/Fold/General.lean`, which are unproved. `#print axioms` reports
`[propext, Classical.choice, Quot.sound]` for `foldsOnto_lam_iff_profile`,
`foldsOnto_vee_iff_profile`, `critLamProfile_iff_of_isLip`, `crookUp_climb3`, `crookUp_climb4`,
`crookUp_climb5`, `crookDown_fall3`, `crookDown_fall4`, `exists_folds_of_profile`,
`exists_folds_of_veeProfile`, and for the eight span-nine theorems of `HPC/Fold/Span9Profile.lean`.

## 6. Continuation: the clause across the basepoint

Everything above reads crookedness *inside one arm*. The clause of `IsCrookedIvF` is not
restricted in that way, and `HPC/Fold/CrossArm.lean` records the unrestricted form and puts it to
work at the branch.

* `crookUp_seq`, `crookDown_seq` — `CrookUp ρ` and `CrookDown ρ` for the whole sequence, so the
  two trigger times may lie on opposite arms of a basepoint. No fold lemma before this batch used
  the clause in that position.
* `no_arm_split_high_low`, `no_arm_split_low_high` — **no basepoint of a span-nine sequence keeps
  one arm off the floor of the band and the other off its ceiling.** If the forward arm never
  drops to `L + 1`, the level `L` is attained on the backward arm; if the backward arm never rises
  to `L + 7`, the level `L + 9` is attained on the forward arm; the clause between those two times
  returns a time at `L + 7` or above before the basepoint, or a time at `L + 1` or below after it,
  and each contradicts one of the two assumptions. The reflected statement is the same argument
  read upside down.
* `s3_span_nine_no_vacuous_mix` and its reflection turn this into a fold statement: the mixed
  configuration in which the Λ-criterion holds for one arm only because that arm never meets the
  floor, and the V-criterion holds for the other only because it never meets the ceiling, does not
  occur. This is the first sub-case of the open mixed configuration of §3 to be settled, and it is
  settled by the cross-arm clause, exactly as §4 predicted the remaining cases should be.

The file also makes the gap exact:

* `s3_span_nine_of_attained` — `s3_span_nine` follows from its special case in which both ends of
  the band are attained. (If an end is missed, the band is eight wide and `s3_span_eight` serves
  every basepoint.) The cross-arm argument needs the ends, and this is what supplies them.
* `s3_span_nine_of_mid` — with that reduction, `s3_span_nine` follows from the two branches of
  `s3_span_nine_except` *stated with both ends of the band as hypotheses*. This is the form in
  which the remaining work should be attacked.

`census-batch42k.c` re-runs the corpus of §1 — every window of `bing 0 N`, `N = 9, 10, 11`, of
span exactly nine — and classifies each branch pair by the two exact criteria rather than by an
announcement. The result sharpens §1:

| branch | pairs | both arms Λ-criterion | both arms V-criterion | mixed | neither |
|---|---|---|---|---|---|
| `L + 4` | 10 588 | 10 588 | 0 | 0 | 0 |
| `L + 5` | 11 184 | 11 184 | 0 | 0 | 0 |

(at the branch `L + 5` the arms are reflected through the middle of the band before the two tests
are applied). No pair of the corpus has an arm that never meets the floor, or one that never meets
the ceiling, so the vacuous sub-case just excluded in Lean is empty in the corpus as well — as the
theorem requires. The open configuration of §3 is therefore still not exhibited by any actual pair
examined, and the remaining work is to exclude it, or to serve it, in general.

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for `crookUp_seq`,
`crookDown_seq`, `no_arm_split_high_low`, `no_arm_split_low_high`, `s3_span_nine_no_vacuous_mix`,
`s3_span_nine_no_vacuous_mix'`, `s3_span_nine_of_attained` and `s3_span_nine_of_mid`.
