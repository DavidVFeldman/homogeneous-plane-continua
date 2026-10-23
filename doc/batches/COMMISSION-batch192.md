# Commission: batch 192 — Theorem C II: the strip theorem; `OTThm32`; Theorem C

**Go!** This batch runs on top of the batch-191 work. Two files come with it, as separate uploads:

* `COMMISSION-batch192.md`: this text, also pasted into the prompt.
* `OT82B.lean`: the skeleton.
  * Save it as `HPC/Span/OT82B.lean`. You may split it under `HPC/Span/`.
  * Add `import HPC.Span.OT82B` at the end of `HPC.lean`. It imports `HPC.Span.OT82A`.
  * It contains `crossing_traces_separated` (commission 191 §7) as a live statement. Remove the
    commented-out copy at the end of `HPC/Span/OT82A.lean` (replace it by a one-line pointer).

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule).** For every theorem whose hypotheses include a named `Prop` or a
  structure, the report gives a note with the two checks:
  1. the hypothesis is not refuted by a short argument from the set-up;
  2. it is not equivalent to the conclusion it is used for, unless the printed argument is a proof
     by contradiction.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Theorem C II (batch 192)");
  * `README.md`;
  * `LEDGER.md`: the section "Oversteegen–Tymchatyn 1982 and Cook 1967";
  * `OPEN.md`;
  * `doc/notes/ot82.md`;
  * `HPC/Span/OT82A.lean`: only the comment block of §7 (see above).

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 191

* **Delivery.** This time the project download was stale (its `axioms.txt` has 2550 lines). The
  tarball overlaid on my batch-190 tree gives 2595 lines, as your report says. Keep publishing the
  tarball and manifest (§10.4).
* **Copies.** The skeleton, commission and both PDFs are byte-identical to what I sent.
* **Audit.** `axioms.txt` has 2595 lines (2550 + 45 added, none removed), with `sorryAx` in none.
  All 45 new theorems use subsets of the standard three axioms. The six `HPC/Span/` files contain
  no `sorry`, `admit` or `axiom` outside comments. Every definition and every fixed statement
  matches the skeleton. The three dropped hypotheses (`[CompactSpace X]` twice, `hA0`) are
  generalizations and are accepted.
* **Results.** `theoremC_of_thm32 : OTThm32 → TheoremC` with everything else proved. Your proof of
  Cook's Theorem 4 (one closed neighbourhood instead of the sequence `Cₙ`) and the single dense
  proper subcontinuum in §5.4 are improvements.
* **Ledger.** OT.1–OT.7 adopted, with your two further misprints (p. 136 "R²" for `I²`; p. 138
  "h_λ(Z)" for `h_λ(z)`), which I checked against the images.
* **§7** (`crossing_traces_separated`) was left open, as allowed. The obstruction you name (strip
  forms of the crosscut and pocket lemmas) is avoided below: §6 proves it with the crossing parity
  alone.

## 1. The plan

Prove `OTThm32` and with it `theoremC : TheoremC`, Theorem C of Hoehn–Oversteegen.
1. Parity tools (§3).
2. A common-zero lemma on a rectangle (§4).
3. Strips: the polygons `S_t`, the sign function, the strip lemma (§5).
4. The order of disjoint crossing continua (§6).
5. `ot82_theorem32 : OTThm32` and `theoremC` (§7).

If the whole does not fit, stop after §5 and report the obstruction.

**The route differs from O–T §2 in three places** (all my readings, to be recorded; §8):
* O–T's Lemma 2.3 and Theorem 2.7 find continua in the zero sets of two sign functions on `I²` and
  let them meet ("there exists a continuum H in C such that (0,p) ∈ H and H meets both I × {0} and
  I × {1}"; "Clearly K ∩ H ≠ φ"). Here a common zero is found directly, by a logarithm on the
  rectangle (§4). No continuum in a zero set is needed.
* O–T reduce maps of continua to maps of arcs by Lemma 2.4 and Remark 2.5 (a locally connected
  continuum near `X`). Here a fine chain in the span witness `Z` and straight segments between
  consecutive points give the two paths directly (§5.4, step 3). No locally connected
  neighbourhood is needed.
* O–T's arcs `A_i` in the Hilbert cube are replaced by piecewise linear paths through the images
  of a fine chain of points of `Y` (§7, step 4).

Notation: `Pt = ℝ × ℝ` with the sup metric; `L₀ = {x = 0}`; for points `a, b` of the plane,
`[a, b]` is the segment. `parity`, `polygonOf`, `polyEdge`, `CrossesEast`, `ceInd`,
`parity_eq_sum`, `crossesEast_comm`, `ceInd_comm`, `parity_locallyConstant`,
`parity_eq_of_isPreconnected`, `parity_eq_zero_of_far` are in `HPC/Plane/Jct1.lean`,
`Tree67.lean` and `Tree7.lean`. None of them needs the polygon to be simple.

## 2. What O–T print, and what is used

The printed statements are transcribed in `doc/notes/ot82.md` (your batch-191 notes).
* **Lemma 2.1** (p. 131) is the parity of a closed polygon: the repository's `parity`.
* **Lemma 2.2** (pp. 132–133), continuity of `U_t` in `t`: §5.2, by vertex perturbation.
* **Lemma 2.3** (pp. 133–134): only its sign function `φ` is used (§5.3).
* **Theorem 2.7** (pp. 135–136), in the form needed: the strip lemma (§5.4).
* **Theorems 3.1–3.2** (pp. 136–138): §7.

## 3. Parity tools

**3.1** `parity_eq_zero_of_not_mem_convex`.
* The polygon lies in `C`: its segments join points of the convex `C`.
* Separate `z` from the compact convex `C` by an open half-plane `H ∋ z` disjoint from `C`
  (`geometric_hahn_banach_point_closed`, or by hand).
* `H` is convex, so preconnected. It contains points of arbitrarily large norm, where the parity
  is `0` (`parity_eq_zero_of_far`). Conclude with `parity_eq_of_isPreconnected`.

**3.2** `parity_eq_of_perturb` (hypothesis `ρ < infDist z (polygonOf v)`). Move the vertices one
at a time: `v = v⁰, v¹, …, vⁿ = w`, where `vᵏ⁺¹` differs from `vᵏ` only at index `k`.
* *One step.* Write `p = vᵏ(k−1)`, `m = v(k)`, `m' = w(k)`, `p' = vᵏ(k+1)`. By `parity_eq_sum`
  and `ceInd_comm`, the difference of the two parities is the sum of the parities of the closed
  triangles `[p, m, m']` and `[m, p', m']`. (The edge `[m, m']` occurs in both and cancels mod 2.)
* The vertices of the first triangle are within `ρ` of the edge `[v(k−1), v(k)]` of `v` (`p` is
  `v(k−1)` or `w(k−1)`); those of the second are within `ρ` of `[v(k), v(k+1)]`. So each triangle
  lies in `cthickening ρ` of an edge of `v`, a compact convex set (`Convex.cthickening`,
  `IsCompact.cthickening`) not containing `z`. By 3.1 the triangle parities vanish at `z`.
* A zero-length edge is never crossed (`CrossesEast` needs a strict straddle). The cases
  `n ≤ 2` need a line each in Lean.

**3.3** `parity_flip_vertical_edge` (edge `i` nondegenerate: `hne`). The east rays from
`(c + ξ, b.2)` and `(c − ξ, b.2)` are at the same height. An edge is crossed by one ray and not the
other exactly when it straddles the height `b.2` and its point at that height has first coordinate
in `(c − ξ, c + ξ]`. (Without `hne` the statement fails for a one-vertex polygon.)
* Edge `i` qualifies: `b.2` lies strictly between the heights of its ends, and its point at that
  height is `(c, b.2)`.
* Any other qualifying edge would pass within `ξ < r` of `b`, which `hfar` excludes.

So the crossing counts differ by exactly one.

## 4. A common zero on a rectangle

`common_zero_rect`. Let `R = [0, 1] × [p, q]`, and suppose `φ` and `ψ` have no common zero on `R`.
1. `Φ = φ + iψ` is continuous and nonvanishing on the convex `R`. `HPC.Moore.exists_log_of_convex`
   (`HPC/Moore/Borsuk.lean`) gives a continuous `g` with `exp ∘ g = Φ` on `R`. Put `θ = Im g`, a
   continuous argument of `Φ`.
2. Corners.
   * At `(0, p)`, `φ = 0` (it is `≥ 0` on the left side and `≤ 0` on the bottom), so `ψ > 0` and
     `θ ≡ π/2`.
   * At `(0, q)`, `ψ = 0`, so `φ > 0` and `θ ≡ 0`.

   (`≡` is mod `2π`.)
3. Sides. On each side `Φ` lies in a closed quarter- or half-plane, so `θ` takes values in a
   disjoint union of closed intervals `[c + 2πk, c' + 2πk]` with `c' − c < 2π`. Connectedness of
   the side picks one `k`.
   * Left side (first quadrant): `θ ∈ [2πk₁, 2πk₁ + π/2]`. So `θ(0, p) = 2πk₁ + π/2` and
     `θ(0, q) = 2πk₁`.
   * Top row (`ψ ≤ 0`): `θ ∈ [2πk₂ − π, 2πk₂]`. At `(0, q)` this forces `k₂ = k₁`.
   * Right side (third quadrant): `θ ∈ [2πk₃ − π, 2πk₃ − π/2]`. At `(1, q)` this forces
     `k₃ = k₁`.
   * Bottom row (`φ ≤ 0`): `θ ∈ [2πk₄ + π/2, 2πk₄ + 3π/2]`. At `(1, p)`, `θ` also lies in
     `[2πk₁ − π, 2πk₁ − π/2]`, which forces `k₄ = k₁ − 1`.
4. Then `θ(0, p) = 2πk₁ + π/2` must lie in `[2πk₁ − 3π/2, 2πk₁ − π/2]`. It does not.

(This replaces O–T's continua in the zero sets. Their "first part of Lemma 2.3" gives continua from
bottom to top only, not through `(0, p)`.)

## 5. Strips

**Data.** `s ≥ 1`; `a, b : Fin (s + 1) → Pt`, with `a 0, b 0 ∈ L₀` and all `a j, b j` in
`{x ≥ 0}`; `f = plPath a`, `g = plPath b` (piecewise linear through the `a j` and the `b j` at
times `j/s`; the skeleton's `plPath` is a sum of clamped ramps, so `fun_prop` gives continuity).
Further notation:
* `B_t = [f t, g t]`, so `B₀ = [a 0, b 0] ⊆ L₀` and `B₁ = [a s, b s]`;
* `S_t = polygonOf (stripPoly a b t) = B₀ ∪ f[0, t] ∪ B_t ∪ g[0, t]`;
* `U_t = {z ∉ S_t : parity (stripPoly a b t) z = 1}`;
* `ε ≥ max_j ‖a j − b j‖`, so `‖f t − g t‖ ≤ ε` by convexity of the norm.

**5.1 (`strip_basic`, shape left to you).**
* `plPath a (j/s) = a j`, and `plPath a` is continuous.
* `t ↦ stripPoly a b t` is continuous.
* `S_t ⊆ B₀ ∪ f[0, 1] ∪ B_t ∪ g[0, 1]` and `S_t ⊆ {x ≥ 0}`.
* `parity (stripPoly a b 0) ≡ 0`: the vertices are `a 0` (repeated) and `b 0` (repeated). Only
  the edges `a 0 → b 0` and `b 0 → a 0` can be crossed, and they cancel.
* `U_t ⊆ {x > 0}`. On `{x < 0}` the parity is `0` (3.1 with the convex hull of the vertices,
  which lies in `{x ≥ 0}`). A point of `L₀` off `S_t` has a disc off `S_t` (closed), which meets
  `{x < 0}`; so its parity is `0` too.

**5.2 (`parity_strip_eventually`, O–T Lemma 2.2).** If `t₀ ∈ [0, 1]` and `z₀ ∉ S_{t₀}`, then for
`(t, z)` near `(t₀, z₀)`: `z ∉ S_t`, and
`parity (stripPoly a b t) z = parity (stripPoly a b t₀) z₀`.
(`z ∉ S_t` because every edge of `S_t` is within `ρ` of the corresponding edge of `S_{t₀}`.)
* Let `d = infDist z₀ S_{t₀} > 0`. By uniform continuity of `f`, `g`, every vertex of
  `stripPoly a b t` is within `ρ < d/4` of the corresponding vertex for `t₀` when `t` is near
  `t₀`.
* Take `z` within `d/4` of `z₀`. Then `2ρ < d/2 < infDist z S_{t₀}`.
* Apply 3.2, then `parity_locallyConstant` at `z₀`.

**5.3 (the sign function, shape left to you).** Let `V = U₁ ∪ (B₀ ∖ (f[0, 1] ∪ g[0, 1] ∪ B₁))`,
and let `h : [0, 1] → V` be continuous. (`f`, `g` or `B₁` may meet `L₀` inside `B₀`; such points
are excluded from `V`. `B₀ ∖ (f ∪ g)` lies inside the open segment, since `a 0 = f 0`,
`b 0 = g 0`.) Define on `[0, 1]²`:
```
φ_h(t, u) = −infDist (h u) B_t   if h u ∈ U_t or (h u).1 = 0,
φ_h(t, u) = +infDist (h u) B_t   otherwise.
```
* **Continuity** at `(t₀, u₀)`. Let `δ₀ > 0` be the distance from `h([0, 1])` to
  `f[0, 1] ∪ g[0, 1] ∪ B₁` (positive: `V` misses these compact sets, and `h([0,1])` is compact).
  0. `U_t ⊆ {x > 0}` (5.1) is used in cases 2–3 and in the boundary sign at `t = 0`.
  1. If `h u₀ ∈ B_{t₀}`: `φ_h(t₀, u₀) = 0`, and `|φ_h| = infDist (h u) B_t` is continuous.
  2. If `h u₀ ∉ B_{t₀}` and `(h u₀).1 ≠ 0`: then `h u₀ ∈ U₁`, so it is off `f`, `g` and `B₀`, hence
     off `S_{t₀}`. For `(t, u)` near `(t₀, u₀)`, `h u` is off `L₀` and off `S_t` (the vertices of
     `S_t` move little), and by 5.2 its parity is that of `h u₀`. So the sign is constant.
  3. If `h u₀ ∉ B_{t₀}` and `(h u₀).1 = 0`: then `t₀ > 0` (since `B_0 = B₀ ∋ h u₀`). Near `b = h u₀`
     the only edge of `S_t`, for `t` near `t₀`, is `B₀`. Indeed `f`, `g` and `B₁` stay `δ₀` away,
     and `B_t` stays away for `t` near `t₀`.
     * By 3.3, the parity just right of `b` is `1 −` (the parity just left of `b`).
     * The parity left of `L₀` is `0`, by 3.1 with the convex hull of the vertices
       (`S_t ⊆ {x ≥ 0}`).
     * So nearby points `h u` off `L₀` have parity `1`, and lie in `U_t` (they are off `S_t`).
       Points on `L₀` have sign `−` by definition. So the sign is `−` near `(t₀, u₀)`.
* **Boundary signs.**
  * `φ_h(0, u) ≥ 0`: `U_0 = ∅` by 5.1; if `(h u).1 = 0` then `h u ∈ B₀ = B_0`, so `φ_h = 0`.
  * `φ_h(1, u) ≤ 0`: `h u ∈ U₁` or `(h u).1 = 0`.
  * If `(h p).1 = 0`, then `φ_h(t, p) ≤ 0` for all `t`.
* **Zeros.** `φ_h(t, u) = 0` iff `h u ∈ B_t`.

**5.4 (`strip_lemma`).** Hypotheses as in the skeleton: `W` a continuum in `{x ≥ 0}`, meeting
`L₀`, with `W ∩ L₀ ⊆ B₀ ∖ {a 0, b 0}`, and disjoint from `f[0, 1]`, `g[0, 1]` and `B₁`.
(These hypotheses force `a 0 ≠ b 0`: `W ∩ L₀` is nonempty and lies in the open segment.)
1. **`W ∖ L₀ ⊆ U₁`.** Let `C` be a component of `W ∖ L₀`.
   * Boundary bumping in `W` (`W ∩ L₀ ≠ ∅`): `cl C` meets `W ∩ L₀` at some `b`.
   * `b` is interior to `B₀` and farther than some `r > 0` from every other edge of `S₁` (they lie
     in `f[0,1] ∪ g[0,1] ∪ B₁`).
   * By 3.3 and 3.1 the parity is `1` on the half-disc right of `L₀` near `b`. `C` meets that
     half-disc.
   * `C` is connected and off `S₁` (off `L₀ ⊇ B₀`, and off `f`, `g`, `B₁`), so `C ⊆ U₁`.
2. Let `Z ⊆ W × W` be a continuum with `π₁ Z = π₂ Z = W`. Suppose `α = min_Z d(p.1, p.2) > ε`.
   Take `η > 0` with `2η < α − ε` and `η <` the distance from `W` to `f[0,1] ∪ g[0,1] ∪ B₁`.
3. **The two paths.**
   * Pick `z_A ∈ Z` with `π₁ z_A ∈ L₀` and `z_B ∈ Z` with `π₂ z_B ∈ L₀` (both projections are onto
     `W`, which meets `L₀`).
   * Take an `η`-chain `z_A = z₀, z₁, …, z_m = z_B` in `Z` with `m ≥ 1` (a connected compact metric
     space is `η`-chain connected; repeat a point if needed). Let `h` and `k` be the piecewise
     linear paths through the `π₁ zⱼ` and the `π₂ zⱼ` at the times `j/m`.
   * Each segment of `h` joins two points of `W` at distance `< η`, so it stays `η`-close to `W`:
     off `f`, `g`, `B₁`, and in `{x ≥ 0}`.
     * If both ends are on `L₀`, the segment lies in `B₀ ∖ {a 0, b 0}`.
     * Otherwise its part off `L₀` is connected, off `S₁`, and contains an end in
       `W ∖ L₀ ⊆ U₁`; so it lies in `U₁`.

     Hence `h, k : [0, 1] → V` (they also miss `f` and `g`, being `η`-close to `W`).
   * `h(0) ∈ L₀` and `k(1) ∈ L₀`.
   * On each piece, `h u − k u` is a convex combination of `π₁ zⱼ − π₂ zⱼ` and
     `π₁ zⱼ₊₁ − π₂ zⱼ₊₁`, and consecutive values differ by `< 2η`. So
     `d(h u, k u) > α − 2η > ε`.
4. **The common zero.** Apply §4 on `[0, 1] × [0, 1]` with `φ = φ_h` (bottom row `u = 0`, where
   `h 0 ∈ L₀`) and `ψ = φ_k` (top row `u = 1`, where `k 1 ∈ L₀`). The hypotheses are the boundary
   signs of 5.3. At a common zero `(t, u)`, `h u, k u ∈ B_t`, so
   `d(h u, k u) ≤ ‖f t − g t‖ ≤ ε`. This contradicts step 3.

## 6. Disjoint crossing continua are ordered

`crossing_traces_separated`. Let `S = [a, b] × ℝ`, `L_a = {a} × ℝ`, `L_b = {b} × ℝ`.
1. **Interleaving.** If neither alternative holds, then after exchanging `K` and `K'` there are
   `p, q ∈ K ∩ L_a` and `w ∈ K' ∩ L_a` with `p.2 < w.2 < q.2`. (Compare the lowest points of the
   two traces. The lower trace's lowest and highest points are `p` and `q`; the other trace's
   lowest point is `w`.)
2. **A polygonal path.** Let `W` be the component of `S ∖ K` containing `K'`. It is relatively
   open in `S` and contains a point `e` of `K' ∩ L_b`.
   * The repository's `exists_polyPath_of_isConnected` is for open subsets of the plane; here argue
     directly. For `z ∈ W` and `r < infDist z K`, `ball z r ∩ S` is convex, misses `K`, and so lies
     in `W`; every point of it is joined to `z` by a segment inside it. Hence the set of points
     reachable from `w` by polygonal paths in `W` is relatively open in `W`, and so is its
     complement in `W`. `W` is connected, so every point is reachable.
   * So there is a polygonal path `β = [w = β₀, β₁, …, β_m = e]` in `W`. It need not be simple,
     and it may touch `L_a` and `L_b` anywhere.
3. **A closed polygon.** Choose `M` larger than every `|height|` of `K`, `K'` and `β`. Close `β`
   by a detour outside `S`:
   * from `e` to `(b + 1, e.2)`;
   * down to `(b + 1, −M)`;
   * across to `(a − 1, −M)`;
   * up to `(a − 1, w.2)`;
   * back to `w`.

   Call the closed polygon `P`. `K` misses `P`: `β ⊆ W ⊆ S ∖ K`; the detour's vertical edges and
   its horizontal edges at heights `e.2` and `w.2` lie outside `S` except at `e` and `w`, which
   are not in `K`; its bottom edge crosses the strip at height `−M`, below every point of `K`.
4. **Parities.** `K` is connected and misses `P`, so `parity P p = parity P q`.
   * The segments from `p` to `p⁻ = (a − ½, p.2)` and from `q` to `q⁻ = (a − ½, q.2)` miss `P`.
     (Their only point in `S` is `p`, resp. `q`, which is in `K` and so not on `β`; the detour's
     horizontal edges are at other heights; the vertical edge is at `x = a − 1`.) So
     `parity P p⁻ = parity P q⁻`.
   * On the line `x = a − 2`, which misses `P`, the parity is constant. It is `0`: far up, the east
     ray meets nothing.
   * From `(a − 2, p.2)` to `p⁻` the only edge crossed is the vertical detour edge `x = a − 1`,
     whose heights `[−M, w.2]` contain `p.2` in their interior. So `parity P p⁻ = 1` (count the
     crossings of the two east rays, as in 3.3).
   * From `(a − 2, q.2)` to `q⁻` no edge is crossed (`q.2 > w.2`). So `parity P q⁻ = 0`.
   * Contradiction.

No Jordan curve theorem and no arc is needed: `parity` does not need simplicity.

## 7. Theorem 3.2 (strip form) and Theorem C

`ot82_theorem32 : OTThm32`. Let `J = {i | SurjSpanPos (h i '' X)}`, and suppose `J` is uncountable.
Write `Wᵢ = h i '' X ⊆ K i`.
1. **One scale.** For `i ∈ J` pick a witness `Zᵢ` and let `αᵢ` be the minimum of `d` on it. Let
   `gapᵢ = (h i y).1 − max_{z ∈ X} (h i z).1 > 0`. Some `n ≥ 1` has (take `n ≥ 1` throughout:
   in Lean `1/0 = 0`)
   `J₁ = {i ∈ J : 1/n ≤ αᵢ ∧ 1/n ≤ gapᵢ}` uncountable.
2. **Clustering** (O–T: "the set of all mappings of X into R² is a separable metric space").
   Put `ρ = 1/(16n)`.
   * For `i ∈ J₁` let `mᵢ ≥ 1` be such that `d(c, c') < 1/mᵢ ⇒ ‖h i c − h i c'‖ < ρ`. Some `m` has
     `J₂ = {i ∈ J₁ : mᵢ = m}` uncountable.
   * Let `N` be a finite `1/m`-net of `Y`. The map `i ↦ (h i c)_{c ∈ N}` takes values in a
     separable metric space. So an uncountable `J₃ ⊆ J₂` has all its values within `ρ` of each
     other.
   * Then `‖h i c − h j c‖ < 3ρ` for all `i, j ∈ J₃` and all `c ∈ Y`.
3. **Order.** By §6 (applied with `a = 0`, `b = 1`), the traces of the `K i` on `L₀` are linearly
   ordered. Take three distinct `i₁, i₂, i₃ ∈ J₃` with the trace of `K i₂` between the other two:
   every point of `K i₂ ∩ L₀` lies strictly between `h i₁ x` and `h i₃ x`.
4. **The strip.** Let `ρ₀ > 0` be a third of the least distance between `K i₁`, `K i₂` and
   `K i₃`. Take `η'` with `d(c, c') < η' ⇒ ‖h iₖ c − h iₖ c'‖ < ρ₀` for `k = 1, 3`.
   * Take an `η'`-chain `x = c₀, …, c_s = y` in `Y`; `s ≥ 1`, since `y ∉ X` by the gap.
   * Put `a j = h i₁ (c j)`, `b j = h i₃ (c j)`, and `ε = 3ρ`.
5. **The hypotheses of the strip lemma** for `W = W_{i₂}`:
   * `‖a j − b j‖ < 3ρ`;
   * `a 0, b 0 ∈ L₀`;
   * all `a j`, `b j` and `W` lie in `[0, 1] × ℝ`;
   * `h i₂ x ∈ W ∩ L₀`, and `W ∩ L₀ ⊆ K i₂ ∩ L₀` lies strictly inside `B₀` (step 3);
   * `f[0, 1]` lies within `ρ₀` of `K i₁` (each segment joins points less than `ρ₀` apart), so it
     misses `W ⊆ K i₂`; likewise `g`;
   * the first coordinates on `B₁ = [h i₁ y, h i₃ y]` exceed `(h i₂ y).1 − 3ρ`, which is at least
     `max_W x + 1/n − 3ρ > max_W x`, so `B₁` misses `W`.
6. **Contradiction.** The strip lemma gives a point of `Z_{i₂}` with `d ≤ 3ρ < 1/n ≤ α_{i₂}`.

`theoremC := theoremC_of_thm32 ot82_theorem32` then has no hypotheses.

## 8. Places to check (ledger)

Add to the section "Oversteegen–Tymchatyn 1982 and Cook 1967", quoting the printed sentences:
1. **Theorem 2.7, the continua `H` and `K` (p. 136).** "It is easy to see that the first part of
   Lemma 2.3 is valid even if (π₁ ∘ f)⁻¹(b) ≠ 1 ≠ (π₁ ∘ g)⁻¹(b) so there exists a continuum H in
   C such that (0,p) ∈ H and H meets both I × {0} and I × {1}" and "Clearly, K ∩ H ≠ φ".
   * The first part of Lemma 2.3 gives continua from bottom to top, not through `(0, p)`.
   * The intersection needs a crossing argument.
   * Both are replaced by §4. Record whether you find either step false or only unargued.
2. **Theorem 2.7, continuity of `φ` when `(π₁ f)⁻¹(b) ≠ {1}`** (an independent check of
   commission 191): `φ` can be discontinuous where `h` meets `B₁` at a point through which `f` or
   `g` crosses `B₁`. Harmless where `h` stays off `B₁`, as here. Confirm or refute.
3. **Remark 2.5 and Lemma 2.4 (pp. 134–135)**: not needed (§5.4, step 3). Record that the locally
   connected `Y` of Remark 2.5 would have to stay inside `U ∪ B₀ ∪ B₁`, which O–T do not argue.
4. **Lemma 2.3 and Theorems 2.6–2.7**: "the component of U₁ whose boundary meets each of f(I) and
   g(I) in a nondegenerate continuum" presumes uniqueness; the boundary condition is not used (here
   `U₁` itself serves).
5. **Theorem 3.1 (p. 137)**: "Let λ₁, λ₂, λ₃ ∈ Λ such that h_λ₂(X) separates h_λ₁(X) from h_λ₃(X)
   in [0,1] × R" is unargued; for crossing images it is §6 together with step 3 of §7. The
   Hilbert-cube arcs are not needed (§7, step 4).
6. **Classification.** If `ot82_theorem32` is proved, record the status of the printed Theorem
   3.2 and of the proofs of 2.7, 3.1 and 3.2 under the ledger's labels. I propose:
   * the proof of Theorem 3.2 is defective (two suppositions not available together, OT.4); its
     statement is not decided (only the strip form is proved);
   * Theorem 2.7: unargued steps, replaced.

   Argue otherwise if you disagree.

## 9. Order

§3, §4, §6 (independent of each other), then §5, then §7.

## 10. Deliverables

1. **The items of §3–§7.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch192.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. **`LEDGER.md`:** §8.
3. **Notes:** `doc/notes/ot82.md`: the route of §3–§7 in a paragraph.
4. **Publish the changes, as in batch 191.** At the end of the run:
   * create `doc/batches/batch192-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch192-MANIFEST.txt`;
   * publish both, as you published the report.
5. **The report.** Its first line names the commission it read. It covers:
   * the items in order;
   * the non-vacuity notes;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of `theoremC`, with every open input marked (if §7 is proved, there should
     be none);
   * what the classification now has: the verified statements about homogeneous plane continua
     (Theorems A, B, C), with any named hypotheses.
6. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/` and `doc/batches/skeletons/`.
   * Nothing is left at the root.
