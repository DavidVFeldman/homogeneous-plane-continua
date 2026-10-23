# Report — batch 12: Agreement reduced to one configuration

One new file, `HPC/Fold/Agree.lean` (232 lines); root `HPC.lean` updated as supplied by the
batch; the commission text kept as `COMMISSION-batch12.md`. Nothing else was touched.

`lake build` succeeds on `RequestProject` and `HPC`. The new file contains no
`sorry`/`admit`/`axiom`/`native_decide`/`implemented_by` and elaborates with no linter
warnings.

## 1. Census

Everything in `HPC/Fold/Agree.lean`, in file order. "Project" dependencies are results from
earlier batches; "mathlib" lists the library lemmas used beyond the `omega`, `simp`,
`push_neg` and `rintro`/`rcases` tactics.

| name | kind | project dependencies | mathlib dependencies |
|---|---|---|---|
| `lStarArm_mem` | theorem | `hStarArm_mem` (b9), `lStarArm` (b9) | — |
| `lStarArm_le` | theorem | `le_hStarArm` (b9), `lStarArm` (b9) | — |
| `not_hStarArm_and_lStarArm` | theorem | `hStarArm_mem` (b9), `lStarArm_mem` | `le_total` |
| `le_lStarArm_of_hStarArm` | theorem | `not_hStarArm_and_lStarArm` | — |
| `hStarArm_le_of_lStarArm` | theorem | `not_hStarArm_and_lStarArm` | — |
| `hStarArm_congr` | theorem | `hStarArm` (b9) | `funext`, `Fin.eta` (via `simpa`) |
| `lStarArm_congr` | theorem | `hStarArm_congr`, `lStarArm` (b9) | — |
| `revSeq` | def | — | `Fin.isLt` |
| `revIdx` | def | — | `Fin.isLt` |
| `revSeq_revIdx` | theorem | `revSeq`, `revIdx` | `congrArg`, `Fin.ext` |
| `isLip_revSeq` | theorem | `IsLip` (b6), `revSeq` | `abs_sub_comm` |
| `isCrookedSeq_revSeq` | theorem | `IsCrookedSeq` (b7), `revSeq` | `Fin.lt_def`, `Fin.ext`, `congrArg`, `abs_sub_comm` |
| `armG_revSeq_apply` | theorem | `armG`, `armT` (b6), `revSeq`, `revIdx` | `congrArg`, `Fin.ext` |
| `armT_revSeq_apply` | theorem | `armG`, `armT` (b6), `revSeq`, `revIdx` | `congrArg`, `Fin.ext` |
| `MixedGap` | def | `hStarArm`, `lStarArm` (b9), `armG`, `armT` (b6), `IsLip` (b6), `IsCrookedSeq` (b7) | — |
| `mixedGap_swap` | theorem | `MixedGap`, `isLip_revSeq`, `isCrookedSeq_revSeq`, `revSeq_revIdx`, `hStarArm_congr`, `lStarArm_congr`, `armG_revSeq_apply`, `armT_revSeq_apply` | — |
| `agreement_of_mixedGap` | theorem | `Agreement` (b11), `MixedGap`, `mixedGap_swap`, `le_hStarArm` (b9), `lStarArm_le`, `le_lStarArm_of_hStarArm` | `abs_cases`, `Fin.ext`, `congrArg`, `Nat.succ_pos` |

The four commissioned items are `not_hStarArm_and_lStarArm`, `le_lStarArm_of_hStarArm`,
`hStarArm_le_of_lStarArm` and `agreement_of_mixedGap`, together with the definition
`MixedGap`, which is kept verbatim as supplied. `hStarArm_le_of_lStarArm` is proved but not
used further in the file; it is the mirror contrapositive the commission asks for.

## 2. Changes

**No commissioned statement was changed, weakened or replaced, and none failed.** Every
explicit hypothesis of the four commissioned theorems is load-bearing, so nothing is marked
unused this time.

Two auxiliaries had to be added because the reflected versions of the batch-9 facts about
`hStarArm` were not available:

* `lStarArm_mem` — the reflection of `hStarArm_mem`: some index attains `lStarArm f p`, and
  every index at or before it has level at most `p + 1`. Obtained by applying `hStarArm_mem`
  to `fun j => - f j` at `-p` and unfolding `lStarArm f p = - hStarArm (fun j => - f j) (-p)`.
* `lStarArm_le` — the reflection of `le_hStarArm`: `lStarArm f p ≤ p`, by the same device.

Both are stated for a general arm and are reusable.

## 3. How the arm symmetry of §2 of the commission was handled

The commission flags this as the one thing to supply: the reduction needs `MixedGap` with the
roles of the two arms exchanged, but `armG ρ i : Fin (n − i) → ℤ` and `armT ρ i : Fin (i+1) → ℤ`
have different index types, so a literal swap is not available.

The route taken is the second of the two the commission offers, in the following form. Rather
than proving a four-way case split with two separate residual configurations, the swap is
realised as an operation on the *data*: reverse the sequence.

* `revSeq ρ t = ρ (n − 1 − t)` and `revIdx i = n − 1 − i`, with `revSeq ρ (revIdx i) = ρ i`.
* `isLip_revSeq` and `isCrookedSeq_revSeq`: both hypotheses of `MixedGap` survive reversal.
  Lipschitzness is immediate. Crookedness needs a check, because the weak `IsCrookedSeq` of
  batch 7 is *not* symmetric under negating a sequence — its four bounds are all displaced
  one unit downward — but it **is** symmetric under reversing one: reversal exchanges the
  ascending and descending cases *and* exchanges the two witnesses, `r ↦ n − 1 − r'` and
  `r' ↦ n − 1 − r`, and under that double exchange the four bounds match up exactly. This is
  the only nontrivial verification in the section.
* `armG_revSeq_apply` and `armT_revSeq_apply`: the forward arm of the reversed sequence at the
  reversed basepoint is the backward arm of the original, index for index, and vice versa.
* `hStarArm_congr` and `lStarArm_congr` absorb the remaining index-type mismatch: two arms
  whose lengths are provably equal and which agree at every index have the same peak (resp.
  valley) demand. The proof is `subst` on the length equality followed by `funext`, so no
  transport machinery is needed.

Since `MixedGap` is universally quantified over all sequences and basepoints, instantiating it
at `(revSeq ρ, revIdx i)` and rewriting with the four congruences gives `mixedGap_swap`:

```
¬ (hStarArm (armG ρ i) (ρ i) + 2 ≤ hStarArm (armT ρ i) (ρ i) ∧
   lStarArm (armG ρ i) (ρ i) + 2 ≤ lStarArm (armT ρ i) (ρ i))
```

which is exactly the mirror the reduction needs. So `MixedGap` really is self-mirroring, and
the theorem `agreement_of_mixedGap` takes `MixedGap` alone as its hypothesis, as commissioned.

## 4. What was supplied at each step of the English argument

**§1, the single-arm lemma.** As in the commission. `hStarArm_mem` gives `j` with
`A j = hStarArm A p ≥ p + 2` and `p − 1 ≤ A j'` for all `j' ≤ j`; the new `lStarArm_mem` gives
`k` with `A k = lStarArm A p ≤ p − 2` and `A k' ≤ p + 1` for all `k' ≤ k`. `Fin m` is linearly
ordered (`le_total`), and each of the two orderings of `j, k` contradicts one of the two prefix
conditions; `omega` closes both. No crookedness, no Lipschitz property, no relation between `p`
and the ambient bounds is used. The two contrapositives are `by_contra` plus `omega`.

**§2, the reduction.** The four base facts `p ≤ hG`, `p ≤ hT`, `lG ≤ p`, `lT ≤ p` come from
`le_hStarArm` and the new `lStarArm_le` at index `0` of each arm; the two `h0` side conditions
`armG ρ i ⟨0,_⟩ = ρ i` and `armT ρ i ⟨0,_⟩ = ρ i` are `congrArg ρ` on `i + 0 = i` and
`i − 0 = i`.

Negating `Agreement` gives `2 ≤ |Δh|` and `2 ≤ |Δl|`; `abs_cases` on each turns this into the
four-way split, and the cases are:

* `hT + 2 ≤ hG`, `lT + 2 ≤ lG` — forbidden by `MixedGap` directly.
* `hT + 2 ≤ hG`, `lG + 2 ≤ lT` — then `hG ≥ hT + 2 ≥ p + 2`, so `le_lStarArm_of_hStarArm` on
  `armG` gives `lG ≥ p − 1`, while `lG ≤ lT − 2 ≤ p − 2`. Contradiction.
* `hG + 2 ≤ hT`, `lT + 2 ≤ lG` — the same with the arms exchanged: `le_lStarArm_of_hStarArm`
  on `armT` gives `lT ≥ p − 1`, while `lT ≤ lG − 2 ≤ p − 2`. Contradiction.
* `hG + 2 ≤ hT`, `lG + 2 ≤ lT` — forbidden by `mixedGap_swap`.

No counterexample to `MixedGap` turned up while formalizing.

## 5. Axiom profiles

`#print axioms` for every theorem of the file:

```
HPC.Fold.lStarArm_mem              [propext, Classical.choice, Quot.sound]
HPC.Fold.lStarArm_le               [propext, Classical.choice, Quot.sound]
HPC.Fold.not_hStarArm_and_lStarArm [propext, Classical.choice, Quot.sound]
HPC.Fold.le_lStarArm_of_hStarArm   [propext, Classical.choice, Quot.sound]
HPC.Fold.hStarArm_le_of_lStarArm   [propext, Classical.choice, Quot.sound]
HPC.Fold.hStarArm_congr            [propext, Classical.choice, Quot.sound]
HPC.Fold.lStarArm_congr            [propext, Classical.choice, Quot.sound]
HPC.Fold.revSeq_revIdx             [propext, Quot.sound]
HPC.Fold.isLip_revSeq              [propext, Classical.choice, Quot.sound]
HPC.Fold.isCrookedSeq_revSeq       [propext, Classical.choice, Quot.sound]
HPC.Fold.armG_revSeq_apply         [propext, Quot.sound]
HPC.Fold.armT_revSeq_apply         [propext, Quot.sound]
HPC.Fold.mixedGap_swap             [propext, Classical.choice, Quot.sound]
HPC.Fold.agreement_of_mixedGap     [propext, Classical.choice, Quot.sound]
```

All within the permitted set; three of them do not even need choice.

## 6. Not in this batch

As §5 of the commission: `MixedGap` itself, `SmallDemandCase`, `HighExitValley`, the assembly
into `F2Prime`, Bing 1948 Theorems 4, 5, 6, the reduction in Bing 1951, and the D8/D9 gap.
