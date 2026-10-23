# Report — batch 13: upward and symmetric crookedness

One new file, `HPC/Fold/Symmetry.lean` (371 lines); root `HPC.lean` updated as supplied by the
batch; the commission text kept as `COMMISSION-batch13.md`. Nothing else was touched.

`lake build` succeeds on `RequestProject` and `HPC`. The new file contains no
`sorry`/`admit`/`axiom`/`native_decide`/`implemented_by` and elaborates with no linter
warnings. Every theorem in it has axiom profile `[propext, Classical.choice, Quot.sound]`.

## 1. Census

Everything in `HPC/Fold/Symmetry.lean`, in file order. "Project" dependencies are results from
earlier batches; "mathlib" lists library lemmas used beyond the `omega`, `simp`, `decide`,
`ring` and `rcases`/`obtain` tactics.

| name | kind | project dependencies | mathlib dependencies |
|---|---|---|---|
| `IsCrookedSeqUp` | def | — | — |
| `IsCrookedSeqUpMixed` | def | — | — |
| `IsCrookedSeqSym` | def | — | — |
| `IsCrookedSeq.sym` | theorem | `IsCrookedSeq` (b7), `IsCrookedSeqSym` | — |
| `IsCrookedSeqUp.sym` | theorem | `IsCrookedSeqUp`, `IsCrookedSeqSym` | — |
| `IsCrookedSeqUpMixed.sym` | theorem | `IsCrookedSeqUpMixed`, `IsCrookedSeqSym` | — |
| `IsCrookedSeqSym.neg` | theorem | `IsCrookedSeqSym` | `abs_neg` |
| `IsCrookedSeqSym.rev` | theorem | `IsCrookedSeqSym`, `revSeq` (b12) | `Fin.lt_def`, `Fin.ext`, `congrArg`, `abs_sub_comm` |
| `negWitness` | def | — | — |
| `not_isCrookedSeq_neg` | theorem | `IsCrookedSeq` (b7), `negWitness` | — (kernel evaluation) |
| `not_isCrookedSeqUpMixed_neg` | theorem | `IsCrookedSeq` (b7), `IsCrookedSeqUpMixed`, `negWitness` | — (kernel evaluation) |
| `isCrookedSeqUp_neg_iff` | theorem | `IsCrookedSeq` (b7), `IsCrookedSeqUp` | `abs_neg` |
| `maxIdx_crooked_step` | theorem | `IsCrookedIn'` (b2), `Refines.maxIdx`, `maxIdx_subset`, `le_maxIdx`, `subset_adjacent_of_subset` (b4), `Chain.link_nonempty` (b1), `Between` (b2) | `Fin.le_def` |
| `isCrookedSeqUp_maxIdx` | theorem | `maxIdx_crooked_step`, `IsCrookedSeqUp` | `abs_cases` |
| `sync_up` | theorem | `IsCrookedSeqUp` | `norm_num` on a literal |
| `sync_up'` | theorem | `IsCrookedSeqUp` | `norm_num` on a literal |
| `sync_up_mixed` | theorem | `IsCrookedSeqUpMixed` | `norm_num` on a literal |
| `sync_up_mixed'` | theorem | `IsCrookedSeqUpMixed` | `norm_num` on a literal |
| `sync_sym` | theorem | `IsCrookedSeqSym` | `norm_num` on a literal |
| `MixedGapUp` | def | `hStarArm`, `lStarArm` (b9), `armG`, `armT` (b6), `IsLip` (b6), `IsCrookedSeqUp` | — |
| `MixedGapUp_witnesses` | def | as `MixedGapUp` | — |

## 2. The one change: which bounds the upward transport displaces

The commissioned table (§1) displaces two of the four bounds upward and keeps the other two:
in the ascending case it asks for `f r ∈ [f t − 1, f t]` but still `f r' ∈ [f s, f s + 1]`.
That is **not** what transport through `maxIdx` yields, and the commission's own module
docstring ("the same shape with every bound one unit higher") describes the form that does.

The transport is symmetric between the two ends. With `h' = maxIdx s`, `k' = maxIdx t` and
`k' ≥ h' + 3`, crookedness gives `r` with `E.link r ⊆ D.link (k' − 1)` and `r'` with
`E.link r' ⊆ D.link (h' + 1)`. At the far end, `le_maxIdx` gives `maxIdx r ≥ k' − 1` and
`subset_adjacent_of_subset` gives `maxIdx r ≤ k'`, i.e. `[f t − 1, f t]` — one above what
`minIdx` gives, as the commission says. At the near end the very same two steps give
`maxIdx r' ≥ h' + 1` and `maxIdx r' ≤ h' + 2`, i.e. `[f s + 1, f s + 2]` — also one above what
`minIdx` gives, and one above the commissioned interval. There is no route to
`maxIdx r' ≤ h' + 1`: `E.link r'` may well lie in `D.link (h' + 2)` as well, and `maxIdx` takes
the larger index by definition. So `isCrookedSeqUp_maxIdx` for the commissioned intervals does
not follow from this argument; no claim either way is made about its truth, and nothing in the
file depends on one.

Following the precedent of batch 7 (`IsCrookedSeqStrong` kept verbatim, the weakened
`IsCrookedSeq` used in the theorems), the file therefore contains **both**:

* `IsCrookedSeqUp` — the uniformly displaced form, all four bounds one higher. This is the one
  `isCrookedSeqUp_maxIdx` proves, the one `MixedGapUp` and `MixedGapUp_witnesses` are stated
  over, and the one `sync_up`/`sync_up'` assume.
* `IsCrookedSeqUpMixed` — the commissioned intervals, verbatim. Every statement commissioned
  for the upward form is also proved for it, so nothing is lost: `IsCrookedSeqUpMixed.sym`, and
  `sync_up_mixed`/`sync_up_mixed'`, which give the commissioned conclusion
  `f j = p − 1 ∧ f k = p + 1` exactly as written.

The corollaries over `IsCrookedSeqUp` are adjusted, exactly as batch 7 adjusted the corollaries
of `IsCrookedSeq`. The commission's point — that the upward displacement makes `sync` exact
where `IsCrookedSeq` leaves it loose — survives, but it is the *upper* witness that becomes
exact, not the lower one:

* `sync` (b7, `minIdx` form): `f j = p − 1` exactly, `f k ≥ p` only.
* `sync_up` (`maxIdx` form): `f k = p + 1` exactly, `p − 1 ≤ f j ≤ p` only.
* `sync_up_mixed` (commissioned intervals): both exact.

This is forced, and is the honest content of the displacement: pushing every bound up by one
moves the pinned value from the bottom of the window to the top. `sync_up'` is the ascending
mirror, where correspondingly the *first* witness is the pinned one, again at `p + 1`.

`sync_sym` is proved as commissioned, with conclusion `f j ≤ p ∧ p ≤ f k`. Its hypothesis
`hmid` turned out not to be needed — with slack two on each side the conclusion follows from
crookedness alone — so it is retained as commissioned but bound as `_hmid`, and the docstring
records this. Every other explicit hypothesis of every theorem is load-bearing.

## 3. The witness for `not_isCrookedSeq_neg`

Found by exhaustive search over all sequences of length `4 ≤ n ≤ 7` with values in `[0, 3]`;
the shortest witnesses have length four and there are exactly two, mirror images of each other.
The one recorded, as `negWitness`, is

```
0, 1, 1, 3
```

Its only pair of indices whose levels differ by at least three is the pair of endpoints, and
it is ascending, so `IsCrookedSeq` asks for `s < r < r' < t` with `f r ∈ [1, 2]` and
`f r' ∈ [0, 1]`; the two middle links, both at level `1`, serve. After negation the pair is
descending, and `IsCrookedSeq` asks for `f r ∈ [−3, −2]`, which neither middle link satisfies.
Both halves are settled by kernel evaluation (`decide`), the condition being a decidable
statement about a four-element index type.

The same witness gives `not_isCrookedSeqUpMixed_neg`: its negation is not crooked in the
commissioned mixed sense either, which is the second half of the commission's remark.

It is *not* a witness against the uniformly displaced `IsCrookedSeqUp`, and no witness exists,
because of a duality the search turned up and the file now records as
**`isCrookedSeqUp_neg_iff`**:

> `IsCrookedSeqUp (fun j => − f j) ↔ IsCrookedSeq f`.

Negation exchanges the `minIdx` form and the `maxIdx` form exactly — an ascending pair for `−f`
is a descending pair for `f`, and under that exchange the four displaced intervals of one
notion are precisely the four intervals of the other. This says in a sharp form what batch 12
observed loosely: the failure of negation symmetry is a one-unit displacement and nothing more,
and `IsCrookedSeqUp` as defined here is the exact negation-partner of `IsCrookedSeq`, which the
mixed form is not. It also gives a second, structural reason to prefer the uniformly displaced
intervals.

## 4. Whether `IsCrookedSeqSym.rev` factored through batch 12

It did not factor, and could not: batch 12's `isCrookedSeq_revSeq` is a statement about
`IsCrookedSeq`, and `IsCrookedSeqSym` is strictly weaker, so neither hypothesis nor conclusion
transfers. What did transfer is the *argument*, line for line — the reversed witnesses
`r ↦ n − 1 − r'`, `r' ↦ n − 1 − r`, the exchange of the ascending and descending cases, and the
bookkeeping in `Fin`. Only the four numerical bounds change, and with slack two they are again
matched by `omega`. The file's proof is that argument with the wider intervals.

## 5. Not attempted

`MixedGapUp` and `MixedGapUp_witnesses` are definitions and are left open, as commissioned; the
derivation of the witnesses from the two gap hypotheses is the next batch's work. No
counterexample to either turned up while formalizing. Also untouched, as §7 directs:
`SmallDemandCase`, `HighExitValley`, the assembly into `F2Prime`, Bing 1948 Theorems 4, 5, 6,
the reduction in Bing 1951, and the D8/D9 gap.
