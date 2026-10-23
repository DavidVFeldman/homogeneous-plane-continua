Commission read: `COMMISSION-batch102.md` (batch 102: Sorgenfrey's theorem, Nadler 11.22–11.35). Its skeleton `Sorgenfrey.lean` is saved as `HPC/Plane/Sorgenfrey.lean`, split over four files (shape change recorded below), and `import HPC.Plane.Sorgenfrey` is added at the end of `HPC.lean`. No existing file was edited.

# Report, batch 102

## Summary

**Refutation first.**

* **11.28 as transcribed (`isConnected_diff_of_superset`) is false.** Take `H = Ū`. Then `U ∖ H = ∅`,
  and the empty set is not connected (`IsConnected` requires nonempty). Proved in Lean as
  `isConnected_diff_of_superset_false` (`HPC/Plane/SorgenfreyLemmas.lean`): the arc
  `[0, 1] = [0, ½] ⊕ [½, 1]` in `unitInterval` is not a weak triod (it is irreducible between `0`
  and `1`, and a weak triod is irreducible between no two points), and `H = Ū = [0, ½]` satisfies
  every hypothesis. Against the page: Nadler's proof says "assuming for the purpose of proof that
  `U − H ≠ ∅`", so his statement tacitly treats the empty set as connected or assumes `U ⊄ H`. The
  skeleton's statement is kept, commented out, with this explanation; the corrected
  `isConnected_diff_of_superset'` adds the hypothesis `((X ∖ Z) ∖ H).Nonempty`. Every use of 11.28
  in Nadler (11.32: `W̄` a continuum; 11.34: each `Ū_j` a continuum) has this hypothesis available.

**Proved.** Everything else, including **Sorgenfrey's theorem (11.34) in Nadler's form**, with only
`propext`, `Classical.choice` and `Quot.sound` (`axioms-batch102.txt`, from `Axioms102.lean`). No
new file contains `sorry` (the only occurrence is inside the commented-out false 11.28).

| Item | Statement | Lean name | Status |
|---|---|---|---|
| 1 | 11.25 triod ⇒ weak triod | `isWeakTriod_of_isTriod` | proved |
| 1 | 11.26 unicoherent: triod ⇔ weak triod | `isTriod_iff_isWeakTriod` | proved |
| 1 | after 11.24: a weak triod is irreducible between no two points | `not_irreducible_of_isWeakTriod` | proved |
| 2 | 11.27 `X ∖ Y`, `X ∖ Z` connected | `isConnected_diff_of_not_weakTriod` | proved |
| 2 | 11.28 as transcribed | `isConnected_diff_of_superset` | **refuted** (`isConnected_diff_of_superset_false`) |
| 2 | 11.28 corrected (`U ∖ H ≠ ∅`) | `isConnected_diff_of_superset'` | proved |
| 3 | 11.30 `irr(A, B)` exists | `exists_irrFromTo` | proved |
| 4 | 11.31 | `nadler_11_31` | proved (hypothesis `B ⊆ Ū` dropped, unused) |
| 4 | 11.32 | `nadler_11_32` | proved (hypothesis `A ≠ Ū` dropped, implied) |
| 4 | 11.33 | `nadler_11_33` | proved |
| 5 | 11.15.1 (case used): indecomposable ⇒ irreducible | `exists_irreducible_of_indecomposable` | proved |
| 5 | 11.34 (a) | `exists_irrFromTo_point` | proved |
| 5 | **11.34 Sorgenfrey's theorem** | `sorgenfrey` | **proved** |
| 6 | 11.35 | `irreducible_iff_not_isTriod` | proved |
| 6 | Fugate: atriodic + hereditarily unicoherent ⇒ irreducible | `sorgenfrey_irreducible_of_atriodic_hu` | proved |
| 6 | Fugate's Lemma 3, both directions | `isTerminalSub_iff_irreducible'` | proved |

So the last `sorry` of the Fugate files is now discharged in sorry-free form:
`sorgenfrey_irreducible_of_atriodic_hu` is batch 100's `exists_irreducibleBetween_of_atriodic`
(which keeps its `sorry` by import order, as the skeleton says; it is on the pruning list), and
`isTerminalSub_iff_irreducible'` is Fugate's Lemma 3 with no open dependency.

## Files and shape changes

* `HPC/Plane/SorgenfreyDefs.lean` — the skeleton's four definitions (`IsEssentialSum₃`,
  `IsEssentialSum₂`, `IsWeakTriod`, `IrrFromTo`), **unchanged**, moved here so that the proofs can
  be split; general topology: Nadler 6.2 (`exists_separated_of_not_isPreconnected`), 6.3
  (`isContinuum_union_piece`, via batch 100's `isPreconnected_union_piece` rather than batch 94's
  `isConnected_union_of_separation`, which is stated for a whole connected space), boundary
  bumping 5.4 and 5.7 (`exists_continuum_bump_closed`, `exists_continuum_bump_open`; the closed form
  is batch 91's `exists_subcontinuum_meeting_closedBall` argument for a general closed set), the
  elementary facts about `X = Y ⊕ Z`, and a constructor `isWeakTriod_of`.
* `HPC/Plane/SorgenfreyLemmas.lean` — 11.25–11.33 under the skeleton's names.
* `HPC/Plane/SorgenfreyMain.lean` — 11.34 (a).
* `HPC/Plane/Sorgenfrey.lean` — 11.34, 11.35, the Fugate consequences.

Statement changes: 11.28 (refuted; corrected form added); 11.31 drops `hBU : B ⊆ Ū` (never used);
11.32 drops `hAne : A ≠ Ū` (if `A = Ū` then `W = ∅` and `W̄ = E ⊕ F` is impossible, since
`IsEssentialSum₂` makes `W̄` a continuum). All other statements are verbatim.

## Ledger of Nadler's text

Places where the text needs more than it says, item by item.

1. **11.25.** The construction `X_i = N ∪ A_i` needs `N ≠ ∅` (here part of the definition of a
   triod, `N` a continuum) and 6.3 for each `N ∪ A_i`; the closedness of `N ∪ A_i` (the closure of
   `A_i` misses the other two pieces) is implicit.
2. **11.27.** "Similarly, `V` is connected": the same argument with `U`, `V` exchanged (one lemma,
   `step1`, used twice). Moore's theorem 5.2 is applied to `Y ∩ Z` with the closed sets
   `Ū ∩ Y ∩ Z` and `V̄ ∩ Y ∩ Z`; batch 101's `exists_closed_split_of_no_connected` asks for no
   *connected* subset meeting both, which follows from (2) by taking closures. (3) `Ū ∩ V̄ = ∅` is
   not needed separately: the disjointness (7) of `M ∪ Ū` and `N ∪ V̄` is checked directly from the
   separation and the split.
3. **11.28.** Needs `U − H ≠ ∅` (refutation above).
4. **11.30.** Left as an exercise in Nadler; proved by Zorn on subcontinua meeting `A` and `B`
   (nested intersections stay connected, batch 99's `isPreconnected_sInter_chain'`, and keep
   meeting the compact sets `A`, `B`).
5. **11.31.** "Since `K ⊆ U − A`": `K ⊆ L − A ⊆ Ū − A`, and `Ū − A ⊆ U` uses `A ⊇ Ū ∩ Z`. The
   boundary-bumping step 5.7 is applied to the open set `Aᶜ` in `L`, which is proper because
   `L ∩ Z ≠ ∅` and `L ∩ Z ⊆ Ū ∩ Z ⊆ A`. The hypothesis `B ⊆ Ū` is never used.
6. **11.32.** "(`W̄` is a continuum by 11.28)" uses `U − A ≠ ∅`, which follows from `A ≠ Ū`
   (and conversely `W̄ = E ⊕ F` forces it). Unicoherence is applied to `X = W̄ ∪ (Z ∪ A)`.
7. **11.33.** The component `J` of `K − U` containing `V̄`, and "by 5.7, `J ∩ Ū ≠ ∅`": `K − U`
   is closed, so this is the closed form of boundary bumping. The proof here uses instead the open
   form at `q` with `O = Ūᶜ`, giving a continuum `J₀ ∋ q` in `K` meeting `Ū` and missing `U`, and
   takes `J = J₀ ∪ V̄`. The rest is as in the text.
8. **11.34, reduction.** 11.15.1 (indecomposable ⇒ irreducible) needs a point outside the
   composant of `p`; this is batch 81's `T13.exists_not_mem_proper_subcontinua` (Baire). The final
   `p ≠ q` (required by the skeleton) holds because `p ∈ U`, `q ∈ V` and `U ∩ V = ∅`.
9. **11.34, the induction.** Simplified, with the change recorded: the step at stage `n` absorbs the
   `n`-th point `d_n` of a dense sequence of `U` (`K_{n+1} = K_n` if `d_n ∈ K_n`); there is no
   minimal index `n(j)`, and `K_0 = Ū ∩ Z` is allowed. The step takes `C = irr(d_n, K_n)` inside
   `Ū` (11.30) and `K_{n+1} = K_n ∪ C`; 11.31 with `A = K_n`, `B = C` shows `K_{n+1} ≠ Ū`. Nadler's
   `C_{j+1} ⊆ Ū_j` and the identity `irr(p, Ū_j ∩ K_j) = irr(p, K_j)` are not needed. What the
   rest of the proof uses is exactly (7): each `K_n` is a proper subcontinuum of `Ū` containing
   `Ū ∩ Z`, the `K_n` increase, and every `d_k` lies in `K_{k+1}`. The dense sequence comes from
   separability of `U` (Mathlib's `IsSeparable.exists_countable_dense_subset`).
10. **(12).** "By 11.15 and 11.17, `U_m − M ≠ ∅`": composants of a nondegenerate indecomposable
    continuum are proper (Baire). Used in the form: for `a ∈ Ū_m ∩ K_m` there is `r` in no proper
    subcontinuum through `a`; then any subcontinuum through `r` meeting `Ū_m ∩ K_m` is all of `Ū_m`
    (its union with `Ū_m ∩ K_m` is a continuum through `a` and `r`, hence `Ū_m`, and `Ū_m` is
    indecomposable while `Ū_m ∩ K_m` is proper). That `r ∉ K_m` needs one more line (otherwise
    `{r}` would be all of `Ū_m`). 5.7 is applied to `L` and the open set `(Z ∪ K_m)ᶜ`.
11. **(*).** "`F − E` is a nonempty open subset of `U`" needs `F ⊆ U_ℓ` (from (8) and (14)) and
    `U_ℓ = X ∩ (Z ∪ K_ℓ)ᶜ` open in `X`; the bars on `J` in the text are essential (the component
    `J` of `K_j − F` is not closed). Here `J = J₀ ∪ K_ℓ` with `J₀` from 5.7 at a point of `K_ℓ` in
    `K_j` with `O = Fᶜ`; `J ∩ (F − E) = ∅` because `F − E` is open in `X`. "`F ∩ K_j ≠ ∅` for some
    `j > ℓ`" uses density and that every `d_k` eventually lies in the `K_j`.
12. **(20)–(25).** As in the text; (21) is used in the form "some `K_ℓ ∖ Z ⊄ Q`" (otherwise `Q`
    contains the dense sequence, hence `Ū`).
13. **11.35.** The "trivial" half is 11.25 and the remark after 11.24.

## Not attempted (§3.3)

`covering_step`, `theorem14` (1948), `theorem3_end`, `exists_tame_chain_near`,
`isArc_of_separatesPairs`, `exists_degenerate_interior_elt` (false), `theorem11_1951_of_T10'`.

## Build

`lake build HPC` succeeds. `Axioms102.lean` prints the axioms of every item; the output is
`axioms-batch102.txt`.
