# Report — batch 6: the Λ-itinerary and the peak-window criterion (Lemma F1)

Delivered complete. `lake build` succeeds on `RequestProject` and `HPC`; the new file
`HPC/Fold/Itinerary.lean` contains no `sorry`, `admit`, `axiom`, `native_decide` or
`implemented_by`, and `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`
for every one of its theorems (§4).

Nothing outside `HPC/Fold/Itinerary.lean` was touched except the root `HPC.lean`, which is the
one supplied with the batch. The batch-6 commission text is kept as `COMMISSION-batch6.md`.

## 1. Census

Commissioned:

| name | status |
|---|---|
| `HPC.Fold.IsLip` | as commissioned |
| `HPC.Fold.κ`, `lamLen`, `lamCenter` | as commissioned |
| `HPC.Fold.lamCenter_zero` | proved (hypothesis `hp` unused, kept as `_hp`) |
| `HPC.Fold.lamCenter_lip` | proved (hypothesis `hu` unused, kept as `_hu`) |
| `HPC.Fold.lamCenter_covers` | proved |
| `HPC.Fold.FoldsOnto` | as commissioned |
| `HPC.Fold.NonAscAt`, `CritLam` | as commissioned |
| `HPC.Fold.foldsOnto_lam_iff` | proved |
| `HPC.Fold.veeLen`, `veeCenter`, `CritVee` | as commissioned |
| `HPC.Fold.foldsOnto_vee_iff` | proved |
| `HPC.Fold.armG`, `armT` | as commissioned |
| `HPC.Fold.armG_isLip`, `armT_isLip` | proved |
| `HPC.Fold.exists_schedule_of_folds` | proved |
| `HPC.Fold.exists_blocks_first_of_folds` | proved |

Added (not commissioned, needed by the proofs):

* `le_κ` — the peak is at least the starting level (`le_max_right`); used everywhere.
* `lt_lamLen_iff` — membership in the walk as an inequality over `ℤ`:
  `u < lamLen p H L ↔ (u : ℤ) ≤ (κ p H − p) + max (κ p H − L − 1) 0`. This removes `Int.toNat`
  from every length side condition and lets `omega` finish them.
* `lamCenter_asc`, `lamCenter_desc` — the two branches of `lamCenter` (`if_pos`, `if_neg`).
  Every window computation in the file goes through one of these two.
* `exists_least_index` — a nonempty predicate on `Fin m` has a least index satisfying it
  (`Finset.exists_min_image` on `univ.filter P`). Used for the switch index `j*`, for the first
  drop index, and for the first time the fold reaches the peak time.
* `le_index_of_lip` — a Lipschitz `ℕ`-valued sequence starting at `0` satisfies `β j ≤ j`.
* `exists_lt_eq_of_lip` — a *bounded* discrete intermediate value theorem on `Fin m`: if
  `β a ≤ v < β b` then `β t = v` for some `t` with `a ≤ t < b`. The batch-5 lemmas
  (`exists_eq_of_lip`, private to `Schedule.lean`) give the value but not the index bound, and
  the (⇒) direction of Lemma F1 needs the index to lie strictly before the drop index `d`.
* `le_add_of_all_asc` — if every step of `(j₁, j₂]` is strictly ascending then
  `f j₁ + (j₂ − j₁) ≤ f j₂`; the induction behind the two "otherwise `f` strictly increases"
  steps of the commission.
* `foldsOnto_lam_of_crit`, `crit_of_foldsOnto_lam` — the two directions of Lemma F1, of which
  `foldsOnto_lam_iff` is the conjunction. Splitting them keeps each proof self-contained.
* `foldsOnto_neg` — folding onto a reflected walk is folding of the reflected arm; this is the
  unfolding the commission asks for in §4.

Mathlib used: `Finset.exists_min_image`, `Finset.mem_filter`, `Finset.mem_univ`, `Fin.ext`,
`Fin.isLt`, `Int.lt_toNat`, `abs_le`, `abs_sub_comm`, `le_max_left`, `le_max_right`,
`le_antisymm`, `if_pos`, `if_neg`, `dif_pos`, `dif_neg`, plus `omega`, `simp`, `dsimp`,
`push_neg`, `push_cast`, `ring`. Batch-4 results used: `Chain.Refines.minIdx`. Batch-5 results
used: `Chain.IsSchedule`, `Chain.exists_blocks_of_walk`, `Chain.unionRange`,
`Chain.IsBlockMap`, `Chain.ofBlocks`.

## 2. Changes to the skeleton

No commissioned statement was changed in meaning, and no name, hypothesis or conclusion was
altered, with the two exceptions below, both of which are the batch-1 convention for a
hypothesis that turns out to be unnecessary (kept in the statement, marked unused):

* `lamCenter_zero`: `hp : p ≤ H` is not needed — `lamCenter p H L 0 = p` holds because
  `κ p H ≥ p` always, so time `0` is on the ascending leg whatever `H` is. Written `_hp`.
* `lamCenter_lip`: `hu : u + 1 < lamLen p H L` is not needed — consecutive centers of the
  formula differ by exactly one at every time, inside the walk or past its end (past the end
  the formula continues descending). Written `_hu`.

The one internal statement that differs from the commission's phrasing is the (⇒) direction:
`crit_of_foldsOnto_lam` needs neither `IsLip f` nor the upper bound `f ≤ H`, since all the
Lipschitz information it uses is that of the fold `β`. It is therefore stated without them;
the commissioned `foldsOnto_lam_iff` of course still carries all of its hypotheses.

`lamLen` and `lamCenter` are used exactly as defined; `lamCenter` does not mention `L`, which
produces the file's single linter warning (`unused variable L` in the commissioned signature).
The signature is left as commissioned.

## 3. What was supplied at each step

* **`lamCenter_covers`, the case split** *(supply)*. Five cases, in this order: `p ≤ ℓ ≤ κ`
  (time `ℓ − p`, exact hit); `ℓ > κ`, which forces `ℓ = κ + 1` because `ℓ ≤ H ≤ κ + 1` (time
  `κ − p`, the peak, distance one); `ℓ < p` with `κ − L − 1 < 1`, in which case `p ≤ κ ≤ L + 1`
  so `ℓ ≥ L ≥ p − 1` and time `0` serves; `ℓ < p`, `κ − L − 1 ≥ 1` and `ℓ ≥ L + 1` (time
  `(κ − p) + (κ − ℓ)` on the descending leg, exact hit); and `ℓ = L` (time
  `(κ − p) + (κ − L − 1)`, the last center `L + 1`, distance one). Each length side condition
  is `lt_lamLen_iff` plus `omega`.
* **Lemma F1 (⇐), case `p ≥ κ`.** As commissioned: `β j := (p − 1 − f j).toNat`. Lipschitz and
  the length bound are `omega` from `|f j' − f j| ≤ 1` and `L ≤ f j`. Window: if `f j ≥ p − 1`
  the time is `0` and the center is `p`, and `f j ≤ H ≤ p + 1` (here `κ = p` forces
  `H − 1 ≤ p`); otherwise the time is positive, hence on the descending leg, with center
  `p − (p − 1 − f j) = f j + 1`.
* **Lemma F1 (⇐), case `p < κ`.** Then `κ = H − 1`. The phase is
  `φ j := if ∃ t ≤ j, NonAscAt f t then 1 else 0`, and `g := f + φ`. Three facts are proved
  about it: `φ ⟨0⟩ = 0` (a non-ascending step has positive index); `f j' ≤ f j` whenever `φ`
  steps from `0` to `1` at `j'` (the witness `t ≤ j'` cannot satisfy `t ≤ j`, so `t = j'`); and
  hence `g` is 1-Lipschitz, the case `φ j = 1, φ j' = 0` being impossible by monotonicity of
  the witness condition. The phase-one bound and window are isolated as two auxiliaries
  (`hbound1`, `hwin1`) so that both branches below can use them.
* **The switch index.** Instead of naming the first drop index, the proof splits on
  `Q := ∃ js, κ ≤ g js ∧ ∀ j ≤ js, p − 1 ≤ f j` ("the peak is reached before any drop"). If `Q`
  holds, `exists_least_index` gives the least such `js`, and minimality gives both
  `g j ≤ κ − 1` and `p − 1 ≤ f j` for every `j < js`; `js ≥ 1` since `g ⟨0⟩ = p < κ`. The
  assignment is `β j := (g j − p).toNat` for `j < js` and
  `β j := ((κ − p) + max (κ − 1 − f j) 0).toNat` for `j ≥ js`, which at `js` itself equals
  `κ − p` because `f js ≥ κ − 1`. Continuity at the switch is where the commission's case
  analysis on `φ` is replaced by a one-line argument: `g` is Lipschitz, so
  `g (js − 1) ≥ g js − 1 ≥ κ − 1`, and `g (js − 1) ≤ κ − 1` by minimality, whence
  `g (js − 1) = κ − 1` exactly and the two times differ by one.
* **The criterion produces the switch.** If `Q` fails, then first the arm never drops: for a
  least drop index `d`, each of the three clauses of `CritLam` yields `j < d` with `g j ≥ κ` —
  clause 1 because `φ ≥ 0`; clause 2 by splitting on whether some step of `(j₁, j₂]` is
  non-ascending (if so `φ j₂ = 1`, if not `le_add_of_all_asc` gives `f j₂ ≥ f j₁ + 1 ≥ κ`);
  clause 3 because a non-ascending step before `j` forces `φ j = 1` — and all levels at indices
  `≤ j` are then `≥ p − 1`, i.e. `Q` holds, a contradiction. With no drop, `g j ≤ κ − 1`
  everywhere (again by failure of `Q`), and phase one alone is a fold.
* **Lemma F1 (⇒).** With `A := (κ − p).toNat` the peak time: the window at `d` gives
  `A < β d`, since an ascending-leg center is `≥ p` while `f d ≤ p − 2` needs a center
  `≤ p − 1`. `exists_lt_eq_of_lip` then gives an index below `d` where `β = A`, and
  `exists_least_index` the least index `j₀` with `β j₀ = A`; `j₀ < d` by minimality, and
  `j₀ ≥ 1` since `β ⟨0⟩ = 0 < A`. The value `β (j₀ − 1)` is `A − 1`: it is not `A` by
  minimality, and `A + 1` is excluded because `exists_lt_eq_of_lip` applied on `[0, j₀ − 1)`
  would produce an earlier index with value `A`. The windows at times `A` and `A − 1` give
  `f j₀ ∈ [κ − 1, κ + 1]` and `f (j₀ − 1) ≤ κ`. The three clauses then follow as commissioned;
  in the last one, if no step of `(0, j₀]` were non-ascending then `le_add_of_all_asc` gives
  `p + j₀ ≤ f j₀ = κ − 1`, i.e. `j₀ ≤ A − 1`, contradicting `A = β j₀ ≤ j₀` (`le_index_of_lip`).
  The step at `j₀` itself is ascending in that subcase (`f j₀ = κ − 1 > κ − 2 = f (j₀ − 1)`),
  so the non-ascending step is strictly before `j₀`, as the clause requires.
* **The V case, the unfolding** *(supply)*. `foldsOnto_neg` states
  `FoldsOnto f len (fun u => −c u) ↔ FoldsOnto (fun j => −f j) len c` — the same `β` works, and
  `|f j − (−c)| = |(−f j) − c|` is `omega` after `abs_le`. Since `veeLen p H L` and
  `veeCenter p H L` are by definition `lamLen (−p) (−L) (−H)` and
  `fun u => −lamCenter (−p) (−L) (−H) u`, and `CritVee f p L` is by definition
  `CritLam (fun j => −f j) (−p) (−L)`, a `show` puts the goal in that shape and
  `foldsOnto_lam_iff` applied to `−f` with `p, H, L` replaced by `−p, −L, −H` finishes.
* **Assembly.** `β t := βG (t − i)` for `t ≥ i` and `βT (i − t)` for `t < i`. The two branch
  equations are proved for `t ≥ i` and for `t ≤ i` respectively — at the overlap `t = i` both
  branches are `0` by the folds' initial conditions — after which the bound, the window and the
  Lipschitz property split into the three cases `i ≤ t`, `t' ≤ i`, and the crossing step, the
  last being subsumed by the two branch equations, so no separate argument at `i` is needed.
  That the arms recover `ρ` is `Fin.ext` on `i + (t − i) = t` and `i − (i − t) = t`.
* **Bridge.** `exists_schedule_of_folds` applied to `ρ t := (minIdx t : ℤ)` gives `β` with
  `β i = 0`; `IsSchedule β` is its Lipschitz clause (converted from `|·| ≤ 1` to `natAbs ≤ 1`)
  together with `⟨i, β i = 0⟩`, and batch-5 `Chain.exists_blocks_of_walk` with `b := c` gives
  the block consolidation with blocks inside three consecutive links; its clause
  `∀ t, (β' t).val = β t` at `t = i` gives `(β' i).val = 0`. The Lipschitz property of `minIdx`
  (batch 4) is not needed: the folds already carry all the regularity used.

## 4. Axiom profiles

`#print axioms` returns `[propext, Classical.choice, Quot.sound]` for each of `le_κ`,
`lt_lamLen_iff`, `lamCenter_zero`, `lamCenter_lip`, `lamCenter_covers`, `exists_least_index`,
`le_index_of_lip`, `exists_lt_eq_of_lip`, `le_add_of_all_asc`, `foldsOnto_lam_of_crit`,
`crit_of_foldsOnto_lam`, `foldsOnto_lam_iff`, `foldsOnto_neg`, `foldsOnto_vee_iff`,
`armG_isLip`, `armT_isLip`, `exists_schedule_of_folds`, `exists_blocks_first_of_folds`
(all in namespace `HPC.Fold`); `lamCenter_asc` and `lamCenter_desc` depend on no axioms at all.
No decision procedure beyond `omega` is used; `decide` and `native_decide` do not appear.

## 5. Statements that did not go through

None. Every commissioned statement was proved with its meaning unchanged, and none was
weakened or replaced.
