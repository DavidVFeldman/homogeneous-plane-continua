# Report — batch 7: the Synchronization Lemma

Delivered: `HPC/Fold/Sync.lean`, with the root `HPC.lean` as supplied by the batch (it now
imports `HPC.Fold.Sync`). The batch-7 commission text is kept as `COMMISSION-batch7.md`.
Nothing else in the project was touched.

`lake build` succeeds on the whole project. `HPC/Fold/Sync.lean` contains no
`sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`, and every theorem of the file has
axiom profile exactly `[propext, Classical.choice, Quot.sound]`.

## 1. Census

All names live in the namespace `HPC.Fold`.

| Name | Kind | Depends on |
| --- | --- | --- |
| `IsCrookedSeqStrong` | def | — (the commissioned strong form, kept verbatim) |
| `IsCrookedSeq` | def | — (the weakened form actually used; see §2) |
| `IsCrookedSeqStrong.isCrookedSeq` | thm | the two definitions; `omega` |
| `sync` | thm | `IsCrookedSeq`; `abs`, `norm_num`, `omega` |
| `sync'` | thm | `IsCrookedSeq`; `abs`, `norm_num`, `omega` |
| `no_immediate_opposite_exit` | thm | `sync`; `Fin.lt_def`, `Fin.ext`, `abs_le`, `omega` |
| `sync_dip` | thm | `sync` |
| `minIdx_crooked_step` | thm | batch 1 `Chain.IsCrookedIn'`, `Chain.Between`, `Chain.link_nonempty`; batch 4 `Chain.Refines.minIdx`, `minIdx_subset`, `minIdx_le`, `subset_adjacent_of_subset`; `Fin.le_def`, `omega` |
| `isCrookedSeq_minIdx` | thm | `minIdx_crooked_step`, `IsCrookedSeq`; `abs_cases`, `not_lt`, `omega` |

Mathlib dependencies are confined to: `Fin` order and extensionality lemmas (`Fin.lt_def`,
`Fin.le_def`, `Fin.ext`), integer absolute value (`abs_le`, `abs_cases`), `not_lt`, `lt_trans`,
and the `omega` / `norm_num` tactics. No new imports beyond the two the skeleton already had.

`minIdx_crooked_step` is the one auxiliary added; it is the single application of chain
crookedness read through `minIdx`, factored out so that the ascending and descending branches
of `isCrookedSeq_minIdx` can share it.

## 2. The two directed changes

### (a) `IsCrookedSeq` is weakened (commission §3, `isCrookedSeq_minIdx`, *(supply)*)

The commission anticipated that the exact values might not survive the passage to `minIdx`,
and they do not. Crookedness of `E` in `D` puts the intermediate link `r` **inside** the coarse
link `k − 1`, whence `minIdx r ≤ k − 1` by minimality; but `E.link r` may also lie inside the
coarse link `k − 2`, in which case `minIdx r = k − 2`. The only lower bound available is the
adjacency bound: `E.link r` is contained in both `D.link (minIdx r)` and `D.link (k − 1)`, so
those two coarse links meet and `minIdx r ≥ k − 2`. The same one-unit loss, always *downward*,
occurs for the second link `r'`. So the definition used in the file is

```
(f s < f t → (f t - 2 ≤ f r ∧ f r ≤ f t - 1) ∧ (f s ≤ f r' ∧ f r' ≤ f s + 1)) ∧
(f t < f s → (f t ≤ f r ∧ f r ≤ f t + 1) ∧ (f s - 2 ≤ f r' ∧ f r' ≤ f s - 1))
```

i.e. each of the four commissioned values is replaced by the interval consisting of it and the
value one below it. The commissioned exact form is kept verbatim in the file as
`IsCrookedSeqStrong`, and `IsCrookedSeqStrong.isCrookedSeq` shows it implies the weak form, so
every theorem of the file applies unchanged to a strongly crooked sequence and nothing is lost.

Consequences for the statements, as §3 allows:

* `sync` now concludes `f j = p − 1 ∧ p ≤ f k` instead of `f j = p − 1 ∧ f k = p + 1`. Note
  that the *first* exact value survives: the weak form only gives `f j ≤ p − 1`, but the
  window hypothesis `hmid` supplies `p − 1 ≤ f j`. This is better than the `f j ≤ p` the
  commission offered. Together with `hmid` one also has `f k ≤ p + 1`.
* `sync'` (the mirror) concludes `p ≤ f j ∧ f k = p − 1`. The asymmetry between the two
  statements is real, not an artefact: the loss in the weak form is always downward, because
  `minIdx` is a minimum, so it is always the *lower* of the two intermediate values that the
  window hypothesis pins down exactly.
* `sync_dip` concludes `f j = p − 1` and, after `j`, `p ≤ f k`.
* `no_immediate_opposite_exit` is unchanged as a statement (it concludes `False`); its proof
  needs only the surviving exact value `f j = p − 1`.

### (b) The Lipschitz hypothesis on `no_immediate_opposite_exit` (commission §3)

Added as directed:

```
(hlip : ∀ s t : Fin n, t.val = s.val + 1 → |f t - f s| ≤ 1)
```

It is genuinely needed and genuinely used: without it the three levels strictly between `a`
and `b` could read `p − 1, p, p + 1`, which satisfies the conclusion of `sync` and produces no
contradiction. With it, `f a = p + 2` and the window force `f (a+1) = p + 1`, and `f (a+2) =
f i = p`, so the only index strictly between `a` and `b` at level `p − 1` is `a + 3 = i + 1`;
`sync` places `j` at level `p − 1` with a further index strictly between `j` and `b`, and there
is none. Every explicit hypothesis of the theorem is load-bearing.

## 3. What was supplied

* **`sync`** (§3): as in the commission, with the descending case of `IsCrookedSeq` applied at
  `(u, v)`; `|f v − f u| = 4 ≥ 3`. Supplied: the observation that `hmid` upgrades the weak
  lower bound on `f r` to the exact value `p − 1`. Contrary to the commission's expectation,
  `hmid` is therefore **used**, and is not marked unused.
* **`sync'`** (§3): the ascending case, symmetrically; here `hmid` pins the *second* value.
* **`no_immediate_opposite_exit`** (§3): the argument sketched in the commission, with the
  directed Lipschitz hypothesis; supplied: the enumeration of the indices strictly between `a`
  and `b` as `a+1, i, i+1` in the `Fin` order (via `Fin.lt_def` and `omega`) and the exclusion
  of each as a candidate for `j`.
* **`sync_dip`** (§3): immediate from `sync`.
* **`isCrookedSeq_minIdx`** (§3, *(supply: prove what is true)*): supplied in full, with the
  weakening described above; the two bounds on each intermediate index come from `minIdx_le`
  (upper) and `subset_adjacent_of_subset` applied to `minIdx_subset` and the crookedness
  containment (lower). Supplied also: the orientation bookkeeping — in the descending case the
  crookedness hypothesis must be applied to the pair `(minIdx t, minIdx s)` and the links
  `(t, s)`, so that `Between t r r' s` holds with `s < r' < r < t`, and the two produced links
  must be returned in the opposite order.

## 4. Statements that did not go through

None. All five commissioned statements are proved, two of them in the weakened form that §3
authorizes and that §2(a) above records precisely; no statement was dropped, replaced, or
proved vacuously.

## 5. Axiom profiles

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for
`IsCrookedSeqStrong.isCrookedSeq`, `sync`, `sync'`, `no_immediate_opposite_exit`, `sync_dip`,
`minIdx_crooked_step` and `isCrookedSeq_minIdx`.
