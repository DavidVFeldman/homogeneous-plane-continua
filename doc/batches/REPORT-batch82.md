Commission read: `COMMISSION-batch82.md`, with its skeleton `Theorem7.lean` (saved as `HPC/Fold/Theorem7.lean`; `import HPC.Fold.Theorem7` added at the end of `HPC.lean`, followed by `import HPC.Fold.Theorem8Counter`).

# Report — batch 82: Bing 1948, Theorems 7, 8, 9 in full; Theorem 3's end-link clause

**Summary.**
* `theorem7`, `theorem8` (corrected) and `theorem9` are proved, with no `sorry`.
* Two counterexamples to Theorem 8 are machine-checked: one to the skeleton's form, one to Bing's printed statement (`not_theorem8_literal`).
* `theorem3_end` is **not** proved. It remains the only live `sorry` in the repository.
* `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every result of this batch except `theorem3_end`. The output is in `axioms-batch82.txt`, produced by `lake env lean Axioms82.lean`.
* `lake build HPC` completes. Its only `sorry` warning is `HPC/Fold/Theorem4.lean:23` (`theorem3_end`).

## 0. Definition audit

I checked the definitions the statements use:
* `Chain` (open links, `link i ∩ link j ≠ ∅ ↔ |i − j| ≤ 1`);
* `IsCrookedIn'` (Bing 1948: links that *meet* `D.link h`, `D.link k`);
* `FollowsPattern` (`F.link i ⊆ D.link (x i)`);
* `IsBlockMap` / `ofBlocks` (surjective, 1-Lipschitz block maps and their unions);
* `unionRange j 3`;
* `z`, and `bingPath` with its index form `bingF`.

These agree with Bing's notions in the block reading that batch 4 recorded. `bingPattern m` is `bingPath 0 (m − 1)` read at position `i`. Its values are `bingF (m − 1) i` (`bingPath_get_eq`, `bingPattern_val`), and they lie in `[0, m − 1]` (`bingF_range`).

## 1. Counterexamples (reported first)

### 1a. The skeleton's Theorem 8 is false — `theorem8_skeleton_false` (`HPC/Fold/Theorem8Counter.lean`)

The skeleton concludes that *both* chains follow `bingPattern m` forwards. The counterexample:
* Let `D` be a three-link chain.
* Put `F₁ = F₂ = C = D.reverse`.
* The hypotheses all hold. Crookedness in a three-link chain is vacuous (`isCrookedIn'_three`), and each end link of `D` contains a link of `D.reverse`.
* But `D.reverse.link 0 = D.link 2 ⊄ D.link 0` (`revThree_not_follows`).

The Lean statement is the negation of the skeleton's statement for `X = ℝ` and `m = 3`, with `D` the intervals `(0,2), (1,4), (3,5)`. The skeleton form is kept in `HPC/Fold/Theorem7.lean`, commented out, with this reason next to it.

### 1b. Bing's Theorem 8 as printed is false — `not_theorem8_literal` (`HPC/Fold/Theorem8Counter.lean`)

This is the §3.1 counterexample the commission asked for. The space is `ℕ` (discrete, so every set is open), using finite sets only.

* `E` (four links): `{0,1,10,11}`, `{1,2,3,4,11,12,13,14,20}`, `{2,3,4,5,12,13,14,15}`, `{5,6,15,16}`.
* `D₁` (six links): `{0,1}`, `{1,2,20}`, `{2,3}`, `{3,4}`, `{4,5}`, `{5,6}`.
* `D₂` (six links): `{10,11}`, `{11,12}`, `{12,13}`, `{13,14,20}`, `{14,15}`, `{15,16}`.

Machine-checked facts:
* Both `D₁` and `D₂` are crooked in `E`.
* Each has its first link in `E₀` and its last link in `E₃`.
* Each has `z 3 = 6` links. By `theorem7_minimal` that is the fewest possible, so no proper consolidation has these properties.
* Both follow `bingPattern 4 = (0,1,2,1,2,3)` forwards.

Nevertheless:
* **No chain has links `D₁.link i ∪ D₂.link i`.** The second and fourth unions share the point `20`, which is the crosswise intersection of §3.1.
* **No chain with links `D₁.link i ∪ D₂.link (5 − i)` refines `E`,** so none is crooked in `E`. Its first link contains `0` and `16`, and no link of `E` contains both.

So the union clause of Theorem 8 is void or false as printed, whichever way the corresponding links are paired.

A related remark, **not formalized**: the orientation clause ("`D₁` follows a pattern that `D₂` follows") also fails literally when `D₂` is `D₁` reversed. In a three-link `E`, take `D₁ = E` and `D₂ = E.reverse`. A common pattern would need a link of `E` containing both `e₀` and `e₂`.

## 2. Targets (§1)

### 2.1 `theorem3_end` — not proved

It is still `sorry` in `HPC/Fold/Theorem4.lean`. As the commission ordered, I worked on it last and found no new device this batch. It would help for the end-link clause to be isolated for folds whose end link is the fold point: for `i = 0` the identity consolidation satisfies all of it, and so does the reversal for `i = n − 1`. That observation is not in Lean. The general case is the batch-78 obstacle, unchanged.

### 2.2 `theorem7` — proved as skeletoned (`HPC/Fold/Theorem7.lean`)

The chain of results:
* **Pattern as a function.** `bingF d u` is `bingPath 0 d` at index `u` (`HPC/Fold/BingF.lean`). It is defined by structural recursion on its three pieces (Bing's alternate definition).
* **Crookedness of the pattern.** `bingF_crooked` (`HPC/Fold/BingCrook.lean`) shows the pattern is crooked.
* **Lifting theorem.** `liftStmt` (`HPC/Fold/Lift82Main.lean`) proves the core step: a fine chain crooked in `D` lifts to Bing's pattern. Every fine link is assigned a position whose level is compatible with the link.
* **Assembly.** `exists_full_lift` and `exists_blocks_bingF` (`HPC/Fold/T7Assemble.lean`) turn the lift into a block map onto `Fin (z (m−1))`. Its blocks follow `bingF` and meet only the levels of their own and neighbouring positions.
* **Crookedness of the consolidation.** `crooked_of_tight` shows the consolidation is crooked.

**Minimality** is `theorem7_minimal`: a chain crooked in `D` with links in both end links of `D` has at least `z (m − 1)` links. It follows from `minGap`.

### 2.3 `theorem8` — corrected and proved (`HPC/Fold/Theorem7.lean`)

The corrected statement has the same hypotheses: two chains with `z (m − 1)` links, crooked in `D`, each with a link in each end link. The conclusions:
* Each chain follows `bingPattern m` **forwards or backwards**.
* Any chain `C` whose links are the unions of corresponding links, when both chains are oriented alike, is crooked in `D`. `C` is quantified in the conclusion.

Proof:
* **Orientation** (`followsPattern_or_reverse`). `theorem7` applied to the chain itself gives a block map `Fin Z → Fin Z`. A block map of `Fin p` onto itself is the identity or the reversal (`blockMap_self`), because a surjective 1-Lipschitz self-map of a finite interval is a bijection.
* **Union.**
  * **Local shape of the pattern** (`bingF_local`, `HPC/Fold/BingLocal.lean`). The pattern never stays flat. At every interior valley at level `v` it reaches `v + 2` two steps away on one side, and at every interior peak it reaches `v − 2`. The proof is by induction through the three pieces; the junction points are checked by hand.
  * **Tightness** (`tight_of_crooked`, `HPC/Fold/T8Tight.lean`). A crooked chain following the pattern meets only levels of its own or neighbouring positions: a link meeting a level beyond its neighbours at a valley or peak would contradict crookedness with the link two steps away.
  * A union of two tight chains is tight, and tight implies crooked (`crooked_of_tight`). This gives `crooked_union_of_bingF`.

### 2.4 `theorem9` — proved as skeletoned (`HPC/Fold/Theorem7.lean`, construction in `HPC/Fold/T9*.lean`)

* **`t ≤ r`.** The claim is trivial. The consolidation with every block a single link works, since `β t = t ≤ r ≤ u`. So the content of Bing's theorem is the case `r < t < s`.
* **`r < t < s`** (`theorem9_core`, `HPC/Fold/T9Main.lean`). This is Bing's proof in the block reading:
  1. `G₁` is a Theorem 7 block function on `E(0, r)` with `0` in block `0` and `r` in block `Z − 1`. `G₂` is one on `E(r, s)` read backwards, with `s` in block `0` and `r` in block `Z − 1` (`exists_blocks_up`, `exists_blocks_down`). The end placement uses `exists_nat_blocks_ends`: if the first link lies in `D.link 0` and the last in `D.link (m−1)`, moving the two end links into the end blocks keeps a pattern-following, tight block map.
  2. `H` is the overlay `γ = G₁` on `0..r` and `G₂` on `r..s`. Its links are the unions of corresponding links of `G₁` and `G₂`.
  3. `H + E(s+1, n)` is the block consolidation of `E` by `foldMap m s γ`. It is crooked (`crooked_foldChain`, §3.5).
  4. Theorem 4 (`theorem4`) applied to `H + E(s+1, n)`, with first block the position `Z − 1 − v` of `t` (`v = γ t`), gives `K`.
  5. `F` keeps the blocks `< v` of `G₁` on `0..r` and puts everything else in block `v + (K-block)`.

  Checks:
  * `F` is 1-Lipschitz, because the fine links of `G₁`-block `v` are exactly those of `H`-link `h_v`, which `K` puts first.
  * `F` is surjective, by a discrete intermediate value theorem on `t..n−1`.
  * `F`'s first block contains `0` and its last contains `n − 1`.
  * Every block lies in one link of `D` (the `G₁` part) or in three consecutive links (the `K` part).
  * Every `u ≥ r` has block `≥ v` = the block of `t`.

  The hypothesis `hrs : r < s` is kept but is not needed by the proof.

## 3. Facts about the text (§3)

1. **Theorem 8's "chain whose links are the sums".**
   * **Confirmed:** crosswise intersections occur, and §1b is a kernel-checked instance in a four-link `E` following `P(4)`.
   * **In Theorem 9's use, `H` is a chain automatically in the block reading.** It is the block consolidation of `E(0, s)` by the overlay `γ`. `γ` is a block function because `G₁` and `G₂` both put `r` in block `Z − 1` (the blocks containing `d_{r−1}, d_r, d_{r+1}` are the last ones, as the commission says). A block consolidation of a chain is a chain, so no crosswise intersection can arise.
   * Its crookedness comes from the tightness of `G₁` and `G₂`, i.e. from the union clause of the corrected Theorem 8.
2. **Theorem 7's "plus a link of `D` in `e_1`".**
   * The block reading needs no sharpening of Bing's hypotheses: `theorem7` holds with one link in `e_1` and one in `e_n`, as stated. In the block reading `f_1` is not "all links of `D` in `e_1`". It is the block of the position `0` of the lift.
   * Theorem 9 needed more: the end links themselves must be in the end blocks. That holds when the end links lie in the end links of `D` (`exists_nat_blocks_ends`). The argument: an end link inside `e_1` is in block `0` or `1`, and moving it to block `0` keeps the map a tight, surjective block map.
3. **Theorem 7's minimality.** `theorem7_minimal` states it as a corollary. Any chain crooked in `D` reaching both end links has at least `z (m − 1)` links, and `theorem7`'s consolidation has exactly that many.
4. **Theorem 7's "other elements of `D`".**
   * In the proof here, every fine link is placed at once by the lifting theorem (`liftStmt`), not by placing `F₁, F₂, F₃` first and the rest afterwards.
   * The placement is forced to be compatible: each fine link gets a position whose pattern level contains it, and it meets only the levels of that position's neighbours.
   * Crookedness of `F` then follows from that tightness and the crookedness of the pattern (`crooked_of_tight`). So "the forced placement keeps `F` crooked and following `P`" holds.
5. **Theorem 9's `H + D(s+1, n)`.** It is made a chain as the block consolidation of `E` by `foldMap m s γ`:
   * fine index `u ≤ s` goes to position `Z − 1 − γ(u)`, i.e. `H` reversed, so that the `H`-link containing `d_s` is adjacent to `d_{s+1}`;
   * fine index `u > s` goes to position `Z − 1 + (u − s)`, a singleton.

   Its crookedness (`crooked_foldChain`) is proved directly, in four cases. It does not go through Theorem 2:
   * both links in the `H` part: from the crooked pattern and tightness (`pat_pair`);
   * both in the tail: from `E`'s crookedness;
   * low link in `H`, high in the tail: find a fine link in the tail at the low level (intermediate value on the fine levels, starting from `d_s ⊆ e_1`), then use `E`'s crookedness;
   * low link in the tail, high in `H`: use the crooked pattern between the `H`-position of level `0` and the high link.
6. **The conclusion of Theorem 9.** It is stated as in the skeleton: every `u ≥ r` has `β u ≥ β t`.
   * **I confirm the reading "`d_1` and `d_s` respectively".** `G₂` consolidates `D(r, s)` read backwards, from `d_s ∈ e_1` to `d_r ∈ e_m`. Its first block contains `d_s` and its last contains `d_r` (`exists_blocks_down`).
   * As noted in §2.4, the conclusion is trivial for `t ≤ r`, where the trivial consolidation works.

## 4. Statement changes (each with its reason)

* `bingPattern`: the placeholder bound is proved. The length proof is written out (`bingPattern_len`) because the skeleton's `simpa` did not compile.
* `theorem8`: reshaped because the skeleton form is false (§1a):
  * "follows `bingPattern m`" became "follows it forwards or backwards";
  * the union clause is conditional on equal orientation;
  * the chain `C` moved into the conclusion.
* `theorem7_minimal`: added (§3.3).
* `theorem7`, `theorem9`: as skeletoned. For `theorem9`, the hypothesis `hrs` turned out to be unnecessary and is kept.

## 5. Files

New:
* `HPC/Fold/BingF.lean`, `BingCrook.lean`, `BingLocal.lean`: Bing's pattern as a function, its crookedness, and its local shape.
* `HPC/Fold/Lift82.lean`, `Lift82Main.lean`, `T7Profile.lean`, `T7Assemble.lean`: the lifting theorem and the Theorem 7 consolidation.
* `HPC/Fold/T8Tight.lean`: tightness, the union clause, and block maps of `Fin p` onto itself.
* `HPC/Fold/T9Ends.lean`, `T9Fold.lean`, `T9Blocks.lean`, `T9Main.lean`: Theorem 9.
* `HPC/Fold/Theorem8Counter.lean`: the counterexamples.
* `Axioms82.lean`, `axioms-batch82.txt`.

Changed:
* `HPC/Fold/Theorem7.lean` (the skeleton, now proved).
* `HPC.lean` (two imports).
