Commission read: `COMMISSION-batch78.md` (uploaded as `COMMISSION-batch78(1).md`), with its `Theorem4.lean`.

# Report — batch 78: Bing's Theorem 4

**No counterexample.** The definitions used by the two statements (`IsCrookedIn'`, `IsBlockMap`,
`ofBlocks`, `unionRange`, `Refines.minIdx/maxIdx`) were read again; nothing makes either statement
vacuous or false. Both statements are kept exactly as they were in the skeleton. No hypothesis was
reshaped (§4.2).

| target | status |
|---|---|
| `theorem4` (`HPC/Fold/Theorem4.lean`) | **proved**, `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]` |
| `theorem3_end` (`HPC/Fold/Theorem4.lean`) | **open**, still `sorry` (the only live `sorry` in the repository) |

`theorem4` does **not** depend on `theorem3_end`. See `axioms-batch78.txt`, which is produced by
`lake env lean Axioms78.lean`. `lake build HPC` is clean (8190 jobs). The only `sorry` warning comes
from `theorem3_end`. The hypothesis `hn : 0 < n` of `theorem4` is not used, because `r : Fin n`
already forces it. It is kept because it is part of the commissioned statement, and its docstring
says so.

New files:

* `HPC/Fold/Splice78.lean` (namespace `HPC.Fold.B78`, no `sorry`) contains the construction.
* `HPC/Fold/Theorem4.lean` is the commissioned skeleton, now importing `Splice78`.
* `HPC/Fold/Questions78.lean` holds the §4.3 and §4.4 statements. It is not imported by `HPC.lean`.
  It is built explicitly and imported by `Axioms78.lean`.
* `Axioms78.lean` and `axioms-batch78.txt`.

## 2. Targets

### 2.2 `theorem4`: proved, by a route that avoids the end-link clause

Bing's splice needs `theorem3_end` so that the block `H_u ∋ h` lands in group 0. The Lean proof gets
the same effect without it. It asks the Theorem-3 fold for one extra fact at the splice point, and
that fact can be obtained from the existing jump-zigzag machinery (`Z77.greedy_fit`):

1. **`fold_low_end`.** Take the level sequence of the prefix `[0, a]` read from the basepoint `r`,
   where `a` meets `D.link 0` (so `ρ(a) ≤ 1`). Append **one fake point at level `0`** just after `a`.
   The crookedness clause still holds for the extended sequence, exactly because `E.link a` meets the
   first coarse link. `greedy_fit` then gives a common fold of both arms and also a time `U` with
   `|U − β(a)| ≤ 1` and `c(U) ≤ 1`. This is the time at which the right arm reaches the fake point.
2. **`prefix_fold` / `suffix_fold`.** This is the same statement for `E` on `[0, a]` from `r`, and,
   through `E.reverse` and `D.reverse`, for `[b, n)` from `s` on the reversed levels `N − 1 − σ`.
3. **`splice_schedule`** (pure integers, needs `N ≥ 6`):
   * keep the prefix blocks with index `< U`;
   * keep the suffix blocks with index `< V` (in reverse order at the end);
   * dissolve every other link into level groups `clamp(level − 2, 0, N − 5)`. The level is `ρ`
     before `b` and `σ` from `b` on.

   Because `c(U) ≤ 1`, every link at block `U − 1` or `U` has `ρ ≤ 3`. So the kept prefix ends next
   to group 0, which is the job the end-link clause does in Bing's proof. `N ≥ 6` gives `b ≥ a + 3`
   and keeps the two kept parts apart. The schedule is 1-Lipschitz, `β(r) = 0`, `β(s)` is maximal,
   and every block lies in a three-level window of `ρ` or of `σ`.
4. **`assemble`** turns such a schedule into `(q, β', hβ')` together with the three-link containment
   (`link_sub_of_level`).
5. **`theorem4_core`** covers `N ≥ 7` with `r ≤ a < b ≤ s`, `a` meeting the first link and `b` the
   last. In `theorem4`, the other orientation (the high link comes first) is reduced to this one by
   `D.reverse` (`unionRange_reverse`).
   * `k = 3`: a single block.
   * `4 ≤ k ≤ 6`: every fine link lies in the first three or in the last three coarse links.
     **`two_window`** builds a two-type alternating schedule directly, with no crookedness needed.

### 2.1 `theorem3_end`: open

The fake-point fold gives a time `U` whose centre is at most `1`. It does **not** say that the end
link's own block, at time `β(end) ∈ {U − 1, U, U + 1}`, is centred at most `L + 1`. The bad case is
the one recorded in §4.1 of the commission: an up-leg that starts at `L + 2` just after a down phase
has turning level `L + 2`, with the end link at level `L + 1` at leg position 0. Both `fold_low_end`
and the Theorem-4 splice get around this by using the *time* `U` rather than the end link's block.
`theorem3_end` requires the end link's block itself. So it needs information about how the greedy
choice behaves inside a leg (which leg is taken first, and where it starts), and this batch did not
establish that. The statement is kept unchanged with `sorry`, and nothing in the repository uses it.

## 4. Questions

1. **The end-link clause from the jump zigzag.** The resolution used here is the second kind the
   commission allows: *rearrange the splice*. The splice is cut at the time `U` where the fold reaches
   a fake level-0 point appended after `h` (Bing's `h` is our `a`), not at the block of `h`. Because
   the fake point is at level `0`, `c(U) ≤ 1`, so blocks `U − 1` and `U` reach level at most `3`. In
   Bing's convention this means `L + 2` and `L + 3` do not occur next to the kept prefix. A kept block
   `U − 1` that contains `a` (which can happen) does no harm when `N ≥ 6`. The clause itself
   (`theorem3_end`) does not follow from this argument, because the end link's block can sit one step
   before `U` at walk value `L + 2`. That is exactly the configuration described in §4.1. It is left
   open.
2. **Meets versus lies in.** The skeleton's `Nonempty`-intersection form was kept. The proof converts
   it at once with `minIdx_near_of_inter` (`ρ(h) ≤ 1`, or `σ(h) ≥ N − 2` at the top). The fake-point
   step (`fold_low_end`) uses exactly `ρ(a) ≤ 1` together with the crookedness clause read at level 0.
   So the level form would serve equally well, but no second statement was needed.
3. **A chain from `R` to `S`.** In `HPC/Fold/Questions78.lean`:
   ```lean
   theorem isFrom_ofBlocks_iff (E : Chain X n) (β : Fin n → Fin q) (hβ : IsBlockMap β)
       (hq : 0 < q) (R S : X) :
       (E.ofBlocks β hβ).IsFrom R S ↔
         ((∃ t, R ∈ E.link t) ∧ (∀ t, R ∈ E.link t → (β t).val = 0) ∧
          (∃ t, S ∈ E.link t) ∧ (∀ t, S ∈ E.link t → (β t).val = q - 1))
   theorem isFrom_ofBlocks_of_theorem4 ... (hr : (β r).val = 0) (hs : (β s).val = q - 1)
       (hR : R ∈ E.link r) (hRonly : ∀ t, R ∈ E.link t → t = r)
       (hS : S ∈ E.link s) (hSonly : ∀ t, S ∈ E.link t → t = s) :
       (E.ofBlocks β hβ).IsFrom R S
   ```
   Both are proved, with standard axioms. The answer: Theorem 13 needs `IsFrom R S` for `F`, and by
   the `iff` this is equivalent to **every** fine link containing `R` being in block 0 (and likewise
   for `S` and the last block).
   * If `R` lies in `d_r` alone and `S` in `d_s` alone, then `theorem4`'s conclusion `β'(r) = 0`,
     `β'(s) = q − 1` is enough (second theorem).
   * If `R ∈ d_r ∩ d_{r±1}`, then `β'(r) = 0` alone is not enough. One also needs `β'(r±1) = 0`.
     Adjacent links can be in different blocks: nothing in `theorem4`'s conclusion rules this out, and
     the prefix fold is free to put `r ± 1` in block 1.

   So Theorem 13 needs either a way to choose `r` with `R` in `d_r` alone, or a strengthened
   `theorem4` whose basepoint is a pair of adjacent links. A point of a chain lies in at most two
   links, and they are adjacent. This strengthening was not attempted.
4. **Theorem 10.** The repository has no vocabulary for subcontinua or indecomposability. As far as
   checked, Mathlib does not provide "indecomposable continuum" either. `Questions78.lean` adds the
   definitions and the statement only, with no proof:
   ```lean
   def IsContinuum (K : Set X) : Prop := IsCompact K ∧ IsConnected K
   def IsIndecomposable (K : Set X) : Prop :=
     IsContinuum K ∧ ∀ A B : Set X, IsContinuum A → IsContinuum B → A ⊆ K → B ⊆ K →
       A ∪ B = K → A = K ∨ B = K
   def Theorem10Statement {P Q : X} (Δ : Description X P Q) : Prop :=
     ∀ K : Set X, K ⊆ Δ.M → IsContinuum K → IsIndecomposable K
   ```
   All three elaborate. Proving it would require the standard link between chains and subcontinua:
   a subcontinuum `K ⊆ M` gives, at each level, the subchain of links meeting `K`, and crookedness
   applied to those subchains must be turned into a separation argument. None of this exists in the
   repository yet.
