# Commission: batch 177 — Part E, Hagopian 1976 XXII: Theorem 1 — the strand lemma; the endgame rebuilt on it

**Go!** This batch runs on top of the batch-176 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch177.md`: this text, also pasted into the prompt.
* `Hagopian76V.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76V.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76V` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XXII (batch 177)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers.

**Progress lines** as before.

## 0. On batch 176

Audited and accepted. All of it.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1901 lines, with `sorryAx` in none, all on standard axioms.

**Accepted.**
* `eps3_positions_middle`, `sepIn_union_cases`, `closure_crossing_subset_interval`.
* `sep_by_crossing_cut`, `hagopian76_x2n_eq_one`, `sepIn_above_gap`, `hagopian76_property4_top`.
* `T12Data`, `Property4`, and **`hagopian76_T15_T17_cond`**: the contradiction, conditionally.

## 1. Diagnosis: what has been slowing the endgame

Every open step since batch 166 has the same cause. Our geometric control near `E` is at the
resolution of the chain `L`, which has eleven pieces, and comes from `ε₁`-homeomorphisms
(Property 1). That control is too coarse:
* "`L − {L₁, L₁₁}` follows `Cl B`" (T9) was open;
* the middle of P3 shrank to `[3/8, 5/8]`;
* `p₄ = 15/22` fell outside it;
* pockets could only be excluded over the middle;
* `SepByCrossing` stalls on components meeting `d⁻¹(1)`.

Lemma T (batch 167) had fine control from **small** homeomorphisms. But it was tied to `D`: its
threshold `δ` came from the low strip of `D`, so it could not be used for all of `D`.

**The fix: choose the resolution before `D`.** The only things that depend on `D` are the height of
the thin strip and `ε₂`, `ε₃`. The fineness of the local structure near `E` depends only on `E`,
on `n`, and on Effros. Fix `n` first, then make `D` thin enough. Then every point of `M` over
almost all of `D` lies on a small translate of `E`. The batch-175 bumping argument (in `h[E]`
rather than in the low strip) shows that the component through it is a crossing **strand**, whose
closure lies in that translate. Below this is the strand lemma (§2) and what follows from it (§3).
Check every step.

## 2. The strand lemma

**Constants, in this order. None depends on `D`.**
1. `n ≥ 100`, an integer. The **inner middle** is the abscissa range
   `[3/22 + 3/n, 19/22 − 3/n]`, which contains `11/22` (`K`) and `15/22` (`p₄`).
2. `θ = θ(n) > 0`: the minimum of `dist(a, b)` over `a, b ∈ E` with `|k(a) − k(b)| ≥ 1/n`. It is
   positive by compactness, since the set of such pairs is compact and misses the diagonal.
3. `δ′ > 0` from uniform Effros (`effros_homogeneous_set`) for `ε = θ/4`: any `y, e ∈ M` with
   `dist(y, e) < δ′` have `y = h(e)` for some `θ/4`-homeomorphism `h`.
4. `η = min(δ′, θ/4, 1/n)`, and `c(n) > 0` from `pi_thin_near_layer` for this `η`: every `x ∈ M`
   over `F[[0, 1] × [−c, c]]` at abscissa `s` has a point `e ∈ E` with `dist(x, e) < η` and
   `|k(e) − s| < η`.

**Then `D` is chosen** (T7, `hagopian76_D`) with height `≤ c(n)`, **and only after that `ε₂`, `ε₃`.**
Check that this order is compatible with T4–T13 as formalized:
* `ε₁` and `L` (Property 1) come before `n` and do not depend on it;
* T7 gives `I₂` at every height `≤` any prescribed `c`;
* `ε₂ = min(ε₁, ρ(M, π⁻¹[I₁ ∪ I₂]), …)` may be shrunk further, and Property 2 holds for every
  `ε₂ > 0`.

**S0 (fine monotonicity).** Let `h` be a `θ/4`-homeomorphism, `z ∈ E`, and suppose `h(z)` lies over
the thin strip at abscissa `s`. Then `|k(z) − s| < 2/n`.
* Proof: `h(z)` is within `η` of some `e′` with `|k(e′) − s| < η ≤ 1/n`. Then
  `dist(z, e′) < θ/4 + η < θ`, so `|k(z) − k(e′)| < 1/n`.
* In particular `h[k⁻¹(0)]` and `h[k⁻¹(1)]` are not over `Cl D`, since `2/n < 3/22`.

**S1 (every point is on a small translate).** Every `y ∈ M ∩ π⁻¹[D]` is `h(e)` for some `e ∈ E`
with `|k(e) − s_y| < 1/n`, where `s_y` is the abscissa of `y`, and some `θ/4`-homeomorphism `h`.
This is step 4 together with step 3.

**S2 (the closure of a component lies in that translate).** Let `C` be the component of
`M ∩ π⁻¹[D]` through `y = h(e)`. Then `Cl C ⊆ h[E]`.
* `Cl C` is a continuum over `Cl D`, meets `h[E]` at `y`, and misses `h[k⁻¹(0)]` and `h[k⁻¹(1)]`
  by S0.
* Apply no hair (`hagopian76_no_hair`) to the type A′ continuum `h[E]` with the map `k ∘ h⁻¹`. The
  transport of `IsMinimalAdmissible` along a homeomorphism of `M` is used inside `property1_aux`;
  state it separately if it is not already a lemma.

**S3 (crossing).** If `s_y` lies in the inner middle, then `C` is a crossing component: its closure
meets both open side edges. This is the batch-175 bumping argument in the halves
`h[k⁻¹[[0, k(e)]]]` and `h[k⁻¹[[k(e), 1]]]`, which lie in `M`, with S0 in place of
`IsEps1.sep_of_gap`.
* A frontier point over the axis is excluded by no hair for `E`.
* A frontier point over `I₂` is excluded because `I₂` misses `π[M]`.
* A frontier point over the far side is excluded by S0, since the inner-middle margin is `3/n`.

Call `C` a **strand**. By S2, `Cl C = h[G]` with `G ⊆ E` a subcontinuum meeting parameters within
`2/n` of `3/22` and of `19/22`. So `Cl C ⊇ h[k⁻¹((3/22 + 2/n, 19/22 − 2/n))]` (`layerSet_Ioo_subset`).
**A strand is a small translate of the middle segment of `E`.**

**S4 (order).** Distinct strands are disjoint, and their closures meet only over the side segments.
For a strand `S`, every component of `π⁻¹[D] − Cl S` is one of three kinds:
* **below `S`**, reaching `π⁻¹` of the bottom edge;
* **above `S`**, reaching `π⁻¹[I₂]`;
* a **pocket**, whose closure meets the frontier of `D` only in one side segment.

Use the Schoenflies square coordinates (`jordan_inner_collar`) and `no_proper_subcontinuum_separates`.
* A component touching both side segments, but neither the top nor the bottom, would contain a
  cross-cut of `D′` from side to side missing `Cl S′`. That contradicts `Cl S′` meeting the left
  side both above and below the cut.
* **No pocket contains a point of `M` over the inner middle.** Such a point lies on a strand (S3),
  and a strand is connected, misses `Cl S`, and reaches both sides.
* Hence the strands are **linearly ordered**: each strand is below or above each other one. Every
  point of `M` over the inner middle, off a given strand, is below or above it. **This is
  Hagopian's "either above or below", for the points it is applied to.**

**S5 (type A′ continua meet the inner middle in whole strands).** Let `G ⊆ M` be type A′ with end
sets `X₀`, `X₁` (for example Hagopian's `F`, or `L`, or `h[R(E)]`-pieces). Let `S` be a strand
meeting `G`, with `Cl S` missing `X₀ ∪ X₁`.
* Then `Cl S ⊆ G` (no hair for `G`), and `S` is a component of `G ∩ π⁻¹[D]`.
* So: **every component of `G ∩ π⁻¹[D]` through a point over the inner middle is a whole strand,
  except possibly the strands whose closures meet an end set of `G`** ("end strands").
* For Hagopian's `F`, `d⁻¹(0) = k⁻¹(0)` is not over `Cl D`, so only `d⁻¹(1)` can produce an end
  strand.
* Show that the part of `F` in an end strand is a "hair". Its closure meets one side segment only
  near the side (fine monotonicity: `F`'s layers along a small translate are translated layers, by
  `lemma3_half`), and no pocket of it reaches the inner middle.

**S6 (fine positions).** Every point of a strand over abscissa `s` lies in `h[k⁻¹(t)]` with
`|t − s| < 2/n`. Together with S1, every `y ∈ M ∩ π⁻¹[D]` at abscissa `s` is within `θ/4 + η` of
`k⁻¹(t)` for some `t` with `|t − s| < 1/n`.

## 3. The endgame rebuilt on strands

**A. `exists_T12Data`.** Take `ε₃ ≤ θ/2`. For `p = h(x)` with `h` an `ε₃/2`-homeomorphism, S2
applied with `e = x` gives `Cl C_p ⊆ h[E]`. By S3, `h⁻¹[Cl C_p]` contains
`k⁻¹((3/22 + 2/n, 19/22 − 2/n))`, so it is essential to `R(E)`. This is Hagopian's "by Lemma 5".
The other fields come from `exists_generic_pq_comp_aux` and `hagopian76_T13_uncond`.
* Note: on the 200-dpi scan, p. 347 reads "essential to `R(E)` onto `Cl C`". The `R(J)` seen earlier
  came from extracted text. **There is no misprint.**

**B. `Y = π⁻¹[Fr D]` is compact and connected.** `π` is a monotone perfect map: it is closed and its
fibres are compact and connected. `Fr D` is a simple closed curve.

**C. The blocks of `St J`.** Merge the finitely many members of `I`, add `[0, e]`, and sort.

**D. `SepByCrossing`, by the ladder.** `p` and `q = f(p)` lie in `M`, over the inner middle (A of
batch 176), and off `R(E) ⊇ F`. Let `S_p`, `S_q` be their strands.
* **Claim:** if no whole `F`-strand lies between `S_p` and `S_q` in the order of S4, then `F` does
  not separate `p` from `q` in `π⁻¹[D]`.
* Path: run along `S_p` from `p` to `K₀`, then along `K₀` to `S_q`, then along `S_q` to `q`.
  * `F ∩ K₀` lies in `F`-strands, since `K₀` is over abscissa `1/2`, in the inner middle, and
    `F ∩ π⁻¹[D]` there consists of whole strands and hairs (S5).
  * `S_p` misses `F` unless `S_p` is an end strand of `F`. In that case, replace the path along
    `S_p` by a path in the band just above or just below it; hairs do not block bands (S5).
  * Check the details.
* `S_p` is connected but need not be path-connected. Work with connected sets, as `SepIn` does.
* "Between" needs care: the vertical `K₀` may meet a strand in a fat translated layer. An
  alternative to the path is `sepIn_union_cases` inside the inner domain
  `O_inner = π⁻¹[D ∩ F[(3/22 + 3/n, 19/22 − 3/n) × ℝ]]`:
  * there, `F` consists of finitely many whole strands, whose closures are pairwise disjoint inside
    `O_inner` (S4), together with hairs in end strands;
  * separation in `π⁻¹[D]` implies separation in `O_inner`;
  * relate a strand's separating `p` from `q` in `O_inner` to its separating them in `π⁻¹[D]` through
    the sides of S4.
* **Conversely,** a whole `F`-strand between them separates them (`crossing_separates`). This gives
  `SepByCrossing`, since the whole `F`-strands are closures of crossing components of `F`. It also
  gives `x₂ₙ = 1` and Property 4 for the top block, through the batch-176 reductions.

**E. `Property4Step`** (Cases 1–2, pp. 348–349), sentence by sentence, with strands:
1. **`C_i` and `C_{i−1}` are strands; `L ⊆ h[R(E)]` misses `F`** (`translate_Rset_disjoint`). By S5,
   `L` meets the inner middle in whole strands, except at its end sets.
2. **"Let `C_{i−1}` be the first component …".** Parametrize `L` (type A′, an extension of
   `Cl C_i` away from `X`). Its strands have parameter intervals with disjoint interiors, as in
   batch 174. Let `u* = inf` of the parameters beyond `Cl C_i` whose layers meet a strand other than
   `C_i`.
   * A limit of such strands is a crossing continuum over `Cl D` (S0 keeps it off the sides' far
     parts). It lies in the layers near `u*`.
   * It is not inside the end set `Z` of `Cl C_i`, which lies over abscissae within `2/n` of the
     left side (S6). So it lies on a strand `S*` with parameters `≥ u*`. That is `C_{i−1}`.
3. **"By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]`, `y_{i−1}` is between `d⁻¹[I]` and
   `d⁻¹[J]`."** Case 1: the gap `d⁻¹[[x₂ᵢ₋₂, x₂ᵢ₋₁]]` leaves `D` at the left side and returns there,
   through stubs and hairs only (S5). Together with the left side segment `σ` between the attachment
   points, it forms a cap `Λ` on the band between `J` and `I`. `L` leaves `C_i` through `Z ⊆ σ`.
   * **`Λ` separates the plane.** The gap piece and `σ` are continua whose intersection is not
     connected: it contains the two attachment points and nothing joining them. By the unicoherence
     of the plane (the converse of Janiszewski's theorem), their union separates.
   * **It does not matter which side of `Λ` is bounded.** Near `σ`, the two sides of `Λ` are the
     band (inside `D`) and the region just outside `D`.
     * If the outside region is the bounded one, `L` (which misses `F`) is trapped there after
       leaving through `Z`, and can return to `D` only through `σ`.
     * If `Λ` wraps around `D`, so that `D` is on the bounded side, `L` is outside `Λ` after
       leaving, and can re-enter the bounded side only through `σ`.

     In both cases `L` re-enters `D` through `σ`. Check this. In particular, `L` crosses `σ` at
     `Z` on the way out, so the argument should be run on `L` minus `Cl C_i`.
   * **Interleaving.** Other `F`-strands may have left ends on `σ`, between the attachment points
     `a_J` and `a_I`. `L` then re-enters a sub-band, but that sub-band still lies above `d⁻¹[J]` and
     below `d⁻¹[I]` in the sense needed, provided blocks are compared by the order of S4. Check that
     Hagopian's "between" means exactly this. Strands of the block `J` itself may lie above `a_J`.
   * If any of this fails, state what is needed as a named `Prop` and continue.
4. **"`N` does not come within `ε₂` of `π⁻¹(p₄)`."** With S6 and §2's constants:
   * `N` meets `D` only in the parts of `C_i`, `C_{i−1}` left of abscissa `1/2 + 4/n`, and in stubs
     within `3/n` of the left side;
   * `Q` is over `15/22`;
   * so, for `ε₂ ≤ θ/2` and `ε₂` small against the uniform continuity of `π` on `M`, `N` stays `ε₂`
     away from `Q`. A point of `M` within `ε₂` of `Q` would be over `D` near `p₄`, or in `E`, or below
     the axis near `p₄`. The last is excluded by `I₁`.
   * Shrink `ε₂` accordingly; Property 2 is unaffected.
5. **"`y_{i−1}` is below `C_i` and `ρ(y_{i−1}, d⁻¹[I]) ≥ ε₃`; otherwise a subcontinuum of `L` would
   violate Property 2."** Formalize with `Property2At`. Identify the subcontinuum `H ⊆ L` and its end
   sets `T`, `V`.
6. **"`f[N]` does not intersect `P`; hence `f(y_{i−1})` is either above `d⁻¹[I]` or below
   `d⁻¹[J]`."**
   * `f[N] ⊆ h₁[R(E)]` misses `F`.
   * `f[N]` misses `Q` by 4.
   * `f(y_{i−1})` is in `M`, over the inner middle (batch 176 A), so S4 applies and "between, left of
     `Q`" is the enclosed region.
7. **Case 2** in the same way.

**F. The assembly.** Prove `hagopian76_theorem1_final : Hagopian76Thm1` if A–E close, or else the
strongest conditional form, with named `Prop`s for exactly what is open (`CapEncloses`, if it
arises).

## 4. Order

The strand lemma first (S0–S6), then A, B, C, D, E, F. If the strand lemma takes the whole batch,
stop after S6 and A, and report.

## 5. Places to check (candidate ledger entries)

1. **p. 346, T9:** "Note that the chain `L − {L₁, L₁₁}` follows `Cl B`": its status after S3–S6, in
   the fine form.
2. **p. 348:** "Note that `x₂ₙ = 1`" (final status).
3. **p. 348, Case 1:** "By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` …". Is the cap case
   (§3.E.3) a gap?
4. **p. 348:** "the continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`" and "Since `L − {L₁, L₁₁}`
   follows …".
5. **p. 349:** "Hence `f(yᵢ₋₁)` is either above …"; Case 2.
6. **The order of constants** (§2). Record that the resolution must be fixed before `D`, and that
   Hagopian's text does not fix an order.

## 6. Deliverables

1. The items of §2–§3.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch177.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s and structures are listed in the report.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * a skeleton proposal for what remains.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
