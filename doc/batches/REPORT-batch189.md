Commission read: `doc/batches/COMMISSION-batch189.md` ("Commission: batch 189 — Part E, Jones 1975 I: arcs and lines; no small reversal; recurrence").

# Report, batch 189

## 0. Summary, omissions

**Every formal item of the commission (§2–§5) is proved.** The files are
`HPC/Jones/Jones75Arcs.lean` (§1, §2.1, §2.2), `HPC/Jones/Jones75Line.lean` (§2.3),
`HPC/Jones/Jones75Rev.lean` (§2.4, §3), `HPC/Jones/Jones75L.lean` (§5) and
`HPC/Jones/Jones75A.lean` (§4, and the index of the skeleton). `HPC.lean` ends with
`import HPC.Jones.Jones75A`. No declaration contains `sorry`, and nothing is left commented out.
Nothing is refuted.

`axioms.txt` has **2479 lines** (2414 + 65 added, none removed). `sorryAx` occurs in none of them.
The 65 new theorems (group "Jones 1975 I (batch 189)" of `Axioms.lean`; copy in
`doc/batches/audits/axioms-batch189.txt`) all use exactly `[propext, Classical.choice, Quot.sound]`.

§6 is the reconnaissance, in prose only, as commissioned. It recommends the Poincaré–Bendixson
route, gives a full hand proof (which corrects two steps of the sketch in the commission), and
proposes a skeleton for batch 190.

**Shape changes** (each one is also recorded at the statement):
* `JonesSetting.line_arc`: the hypothesis `S : JonesSetting Y` was not used, so it was dropped.
  The statement only needs `IsLine ℓ`.
* `JonesSetting.no_reversal_arc`: the hypothesis `hAC : A ∩ C = {p}` was not used, so it was
  dropped. The statement is therefore stronger.
* `no_backtrack_in_collar`: the skeleton left the placeholder `no_backtrack_in_collar : True`.
  The commission's claim is now stated and proved in two forms: `JonesSetting.no_backtrack` (an
  abstract coordinate) and `no_backtrack_in_collar` (the collar form of §5).
* The skeleton is split over five files under `HPC/Jones/`, as allowed.
* There are additional proved helper lemmas, all listed in the audit. One existing name clashed:
  the gluing map of §2.3 is called `rayGlue`, because `glueMap` already exists in
  `HPC/Hagopian/H76AdaptHalf.lean`.

**Omissions.** None of the requested items are left out. The solenoid claims of §1.1/§7.1 are
checked as a hand argument (§3 below) and are not formalized; the commission says they need not be.

Status lines:
* STATUS: §1 `jonesSetting_of_plane` proved
* STATUS: §2.1 `JonesSetting.union_arc`, `JonesSetting.nested` proved
* STATUS: §2.2 `JonesSetting.exists_arc_through` proved
* STATUS: §2.3 `JonesSetting.exists_line` proved
* STATUS: §2.4 `JonesSetting.line_arc`, `JonesSetting.homeo_on_line` proved
* STATUS: §3.1 `JonesSetting.no_reversal_arc` proved
* STATUS: §3.2 `JonesSetting.exists_no_reversal` proved
* STATUS: §3.3 `JonesSetting.orientation` proved
* STATUS: §4.1 `JonesSetting.omegaLim_saturated` proved
* STATUS: §4.2 `JonesSetting.line_recurrent` proved
* STATUS: §4.3 `JonesSetting.jones75_d` proved
* STATUS: §5 `JonesSetting.no_backtrack`, `no_backtrack_in_collar` proved
* STATUS: §6 reconnaissance done (report only); `jones75_noArc : NoArcIndecHomPlane` open (not
  attempted, as commissioned)

## 1. The items, in order

### §1. The setting

`JonesSetting Y` (structure, unchanged): `Y` is a compact metric space that is homogeneous,
hereditarily unicoherent, atriodic, and contains an arc.

`jonesSetting_of_plane (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) (hα : ∃ a b A, TArc a b A) : JonesSetting M`
**proved**, from `hagopian75_lemma1` (Jones's (a) and (b)).

### §2. Arcs and lines

* **§2.1 `JonesSetting.union_arc`** (Jones (c), first half) **proved**. `A ∩ B` is a subcontinuum
  (`JonesSetting.inter_isPreconnected`, by hereditary unicoherence), hence a parameter interval of
  each arc (`inter_param`). At an end of it, three arms would give a triod
  (`JonesSetting.no_three_arms`). The case analysis is in `JonesSetting.union_arc_aux`/`glue_case`,
  which glue with `TArc.union`.
* **§2.1 `JonesSetting.nested`** (Jones (c), second half) **proved**. The far end of `A ∩ B` is an
  end point of `A` or of `B`, since otherwise there are three arms at it.
* **§2.2 `JonesSetting.exists_arc_through`** **proved**. Map an interior point of a given arc to
  `x` by homogeneity (`TArc.image_homeomorph`).
* **§2.3 `JonesSetting.exists_line`** **proved**, by the commission's route.
  * The arcs from `x` through `[x, c]` form a chain (`JonesSetting.rayArcs_total`).
  * There is no largest one (`JonesSetting.extend`).
  * A countable cofinal sequence exists (`JonesSetting.exists_ray_seq`, with separability), and it
    is reparametrized into a `RayChain` (`JonesSetting.exists_rayChain`).
  * `rayGlue` glues the pieces into a continuous injection of `[0, ∞)` (`continuous_rayGlue`,
    `rayGlue_injective`, `range_rayGlue`).
  * The two rays meet only in `x` (`JonesSetting.ray_inter`), and their union is the arc component
    (`JonesSetting.arcComp_eq_rays`).
* **§2.4 `JonesSetting.line_arc`** **proved** (shape change above). The companion results are
  `JonesSetting.arc_unique` (two arcs with the same end points are equal) and
  `JonesSetting.arc_in_line` (an arc meeting a line lies in it).
* **§2.4 `JonesSetting.homeo_on_line`** **proved**, through `JonesSetting.homeo_on_line_gen`. `h`
  maps the arc component of `ℓ 0` onto that of `h (ℓ 0)`, and arcs onto arcs. In parameters this
  gives a bijection of `ℝ` that maps compact intervals onto compact intervals, hence a continuous
  bijection, hence strictly monotone.

### §3. No small reversal

* **§3.1 (R0) `JonesSetting.no_reversal_arc`** **proved**, by the commission's argument through
  `nested` (shape change above).
* **§3.2 (R) `JonesSetting.exists_no_reversal`** **proved**.
  * `JonesSetting.local_no_reversal` gives a `ρ_q`, an Effros `δ_q` and the conjugation
    `g h g⁻¹`.
  * "Reversing one arc at a fixed point is reversing every arc there" comes from `homeo_on_line`.
  * A finite subcover finishes the proof.
* **§3.3 (O) `JonesSetting.orientation`** **proved**, in the strengthened form (`ψ` strictly
  increasing, continuous and onto). If `ψ` decreased, `ψ(s) − s` would have a zero, and (R) would
  fail there.

### §4. Recurrence

* **§4.1 `JonesSetting.omegaLim_saturated`** **proved**.
  * The line `ℓ` is not eventually inside a compact arc of a line `λ`. Otherwise `ℓ[C, ∞)` would
    lie in a compact subarc of `λ[0, s]`, which contradicts injectivity when `λ` is `ℓ`; when `λ`
    is a different line, its arc component is disjoint from `ℓ`'s.
  * Effros `hₙ` with `hₙ(z) = ℓ(uₙ)` and `ψₙ` from `homeo_on_line` then give `ψₙ(s) ≥ T` together
    with `d(ℓ(ψₙ(s)), λ(s)) < ε`.
* **§4.2 `JonesSetting.line_recurrent`** **proved**, by the independent check's argument.
  * `JonesSetting.zero_mem_omegaLim` uses Effros with `ε = ½ d(ℓ(0), ω(ℓ))`; `ω(ℓ)` is nonempty by
    compactness.
  * Applying this to the shifts `ℓ(· + c)` (`IsLine.shift`, `omegaLim_shift`) gives the result.
* **§4.3 `JonesSetting.jones75_d`** **proved**, for every line and both directions; the backward
  direction uses `IsLine.neg`.

### §5. (L), no backtracking

* **`JonesSetting.no_backtrack`** **proved**, in a general form. Let `X : Y → ℝ` be continuous on a
  set `W` that is a neighbourhood of each `ℓ t`, `0 < t < 1`, with `X (ℓ t) = t`. For every
  `κ > 0` there is `η > 0` such that no piece `ℓ[u, β]` with all points in the metric strip
  `{p ∈ W : X p ∈ [κ, 1−κ], d(p, ℓ(X p)) < η}` satisfies `X (ℓ β) ≤ X (ℓ u) − κ`.
  * The proof is the commission's steps 1–5, with the last time `u₁` at which `X ≥ s + κ/2`, the
    Effros map `ℓ(r) ↦ ℓ(u₁)`, (O), and the intermediate value theorem.
  * The independent check's condition "points stay where `X` is defined" is
    `uniform_near_compact`. It is a lemma for a function continuous on a neighbourhood of a compact
    set.
* **`no_backtrack_in_collar`** **proved**, in the collar form. For `M : Set Pt` with
  `JonesSetting M`, a line `ℓ` of `M`, and a collar `F` (`IsCollar`) of `γ = ℓ|[0,1]`: for every
  `κ > 0` there is `η > 0` such that if `ℓ[u, β]` lies in `F([κ, 1−κ] × (−η, η))`,
  `ℓ u = F(x₁, y₁)` and `ℓ β = F(x₂, y₂)`, then `x₂ > x₁ − κ`.
  * The proof derives this from `no_backtrack`, with `X` the first collar coordinate (continuous
    on the open collar, through `IsEmbedding.toHomeomorph`).
  * `η` comes from uniform continuity of `F` on the closed rectangle.
  * Connectedness of `M` is not used.

## 2. Non-vacuity notes

**`JonesSetting Y`** is a structure. It is the hypothesis of every theorem of §2–§5 except
`uniform_near_compact`, the arc toolkit and the `arcComp` lemmas, which take no such hypothesis.

1. *Not refuted by a short argument; satisfied by the dyadic solenoid `Σ`.* This is a hand
   argument, not formalized.
   * `Σ` is a compact metric topological group, hence homogeneous.
   * It is indecomposable. Hence it is unicoherent: if `Σ = A ∪ B` with `A`, `B` subcontinua, one
     of them is `Σ`, and then `A ∩ B` is the other one.
   * Its proper nondegenerate subcontinua are arcs, which are unicoherent. So it is hereditarily
     unicoherent.
   * It is atriodic in the sense of `IsTriod`. An arc minus a subcontinuum has at most two
     components. If `K ⊊ Σ` is a subcontinuum, then `K` lies in one composant, `Σ ∖ K` contains
     another composant `C′`, which is dense and connected, and `C′ ⊆ Σ ∖ K ⊆ cl C′`, so `Σ ∖ K` is
     connected.
   * It contains arcs.

   So §2–§4 and `JonesSetting.no_backtrack` (with any arc of `Σ` and a coordinate on a
   neighbourhood of it) are not vacuous.
2. *Not equivalent to the conclusions.* The conclusions are
   * (c),
   * the existence of lines,
   * the monotone action of homeomorphisms,
   * (R), (O),
   * recurrence, and
   * (L).

   None of them gives homogeneity or the existence of an arc. For example, the conclusions of
   §2.1 hold trivially in a space with no arcs.

**`jonesSetting_of_plane` and `no_backtrack_in_collar`** (planar instances).
1. The hypotheses are a homogeneous indecomposable plane continuum with an arc, or a compact planar
   `M` with `JonesSetting M`. They are not refuted by a short argument. Refuting them is exactly the
   open target `NoArcIndecHomPlane` (by Bing 1960 they are in fact never satisfied by a plane
   continuum).
2. They are not equivalent to the conclusions. They are used in a proof by contradiction: §6 derives
   `False` from them, which is the printed structure of Jones's Theorem.

**`IsLine ℓ`** (a named `Prop`).
1. It is satisfiable: `exists_line` produces lines in every `JonesSetting`, and in `Σ` the arc
   components are lines.
2. It is not equivalent to the conclusions it is used for (arcs of a line, monotone actions, limit
   sets).

## 3. Ledger entries (new section "Jones 1975 I" in `LEDGER.md`)

* **J75.1, p. 59, (f): defective proof.**
  * The last inference ("This is impossible since the `3ε`-neighbourhood of `q₁p₁` contains no
    point of `p₂q₂`") is a non sequitur. `g[a′b′]` can run past `q₁` along the arc
    `q₁pq₂ ∪ g[a′b′c′]`.
  * The dyadic solenoid satisfies everything the proof uses ((a), (b), (c), Effros), yet (f) fails
    in it, even with `d(b, p) < ε`. The construction is the commission's, checked: forward rays
    are dense because `{n ≥ N}` is dense in the 2-adic integers.
  * Two further steps are unargued: "takes `b` to `p`", because the negation gives only a point of
    `ab` near `p`; and "leaves … `q₁` and `q₂` … in `D`", for a homeomorphism that is not small.
  * The phrase "close enough to `b`" should read "close enough to `p`".
  * The statement is true for plane continua, but only vacuously, once the Theorem is known.
  * Replaced by (R), (O) and (L), all proved. **Counted as the fifteenth defective proof.**
* **J75.2, p. 58, (d), second sentence: gap; statement true (proved, `jones75_d`).**
  * The "first point" exists when such points exist.
  * The transport step ignores orientation; adding `d(a, ce)` to the minimum, or using (O), repairs
    it.
  * The triod paragraph produces no triod as printed, because nothing makes the images meet `T`.
  * Replaced by recurrence. Not counted.
* **J75.3, p. 57, (c): true; the argument from (a) and (b) is unstated.** Proved (`union_arc`,
  `nested`). Not counted.
* **J75.4, pp. 59–61, the Theorem: defective proof (a false step).**
  * "let us assume that `T` is accessible" is unargued.
  * The choice of `η` rests on (f).
  * "This makes `h` take `[t₀, t_d]` onto (approximately) `[t_d, t₀]`. So there is a fixed point"
    is unargued, and false for `ε < ε₀` by (O).
  * "Clearly `t_f` cannot lie in `D̄₁ ∪ D̄₂ ∪ D̄₃`" is unargued (and moot).
  * "it is easy to see that `p ∉ D̄₂` and property (f) is violated" is unargued, and rests on J75.1.
  * The Theorem itself is true (Bing 1960). **Counted as the sixteenth defective proof.**
* **J75.5, the notes:** pages 57–61 (the sixth PDF page is blank), and "`d(h(p), p) ≤ ε`" as
  printed. Corrected in `doc/notes/jones75.md` §1 and §4.

The count of defective proofs rises from fourteen to sixteen. No statement of Jones's is refuted.

## 4. Axioms

All 65 new theorems use exactly `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). The full
list is in `doc/batches/audits/axioms-batch189.txt`. The main results are:

| theorem | axioms |
| --- | --- |
| `HPC.Hagopian.jonesSetting_of_plane` | propext, Classical.choice, Quot.sound |
| `HPC.Hagopian.JonesSetting.union_arc`, `.nested`, `.exists_arc_through` | same |
| `HPC.Hagopian.JonesSetting.exists_line` | same |
| `HPC.Hagopian.JonesSetting.line_arc`, `.homeo_on_line`, `.arc_unique`, `.arc_in_line` | same |
| `HPC.Hagopian.JonesSetting.no_reversal_arc`, `.exists_no_reversal`, `.orientation` | same |
| `HPC.Hagopian.JonesSetting.omegaLim_saturated`, `.zero_mem_omegaLim`, `.line_recurrent`, `.jones75_d` | same |
| `HPC.Hagopian.JonesSetting.no_backtrack`, `HPC.Hagopian.no_backtrack_in_collar` | same |

The definitions are `JonesSetting`, `arcComp`, `IsLine`, `rayArcs`, `RayChain`, `fractI`,
`rayGlue`, `lineΦ`, `omegaLim` and `IsArcSaturated`.

## 5. Files

New:
* `HPC/Jones/Jones75Arcs.lean`
* `HPC/Jones/Jones75Line.lean`
* `HPC/Jones/Jones75Rev.lean`
* `HPC/Jones/Jones75L.lean`
* `HPC/Jones/Jones75A.lean`
* `doc/batches/REPORT-batch189.md`
* `doc/batches/audits/axioms-batch189.txt`

Changed:
* `HPC.lean`
* `Axioms.lean`
* `axioms.txt`
* `README.md`
* `LEDGER.md`
* `OPEN.md`
* `doc/notes/jones75.md`

Moved:
* `COMMISSION-batch189.md` → `doc/batches/COMMISSION-batch189.md`
* `Jones75A.lean` → `doc/batches/skeletons/Jones75A.lean`

Delivery: `doc/batches/batch189-files.tar.gz` and `doc/batches/batch189-MANIFEST.txt`. Every file
added, changed or moved in this run is in the tarball. Repository files that are cited in §1 and §6
but were not changed in this run are not included.

## 6. Reconnaissance: the planar core

### 6.1 Choice of route: Poincaré–Bendixson

I recommend the Poincaré–Bendixson route, in the corrected form of §6.3. Reasons:

* It needs none of the unargued planar steps of Jones's route: the accessibility of `T`, (e), and
  "the next arc of `T` below `[t_a, t_b]` and … the Jordan curve theorem to get the proper order".
  Each of these would be a formalization project of its own, and the accessibility sentence is a
  gap in the paper.
* It uses only results proved in this batch ((O) and recurrence), Effros, the collar, the Jordan
  curve theorem, and **one** planar lemma that is missing from the repository: the cross-cut lemma
  (§6.4).
* It needs neither (L) nor the 1976 crossing machinery. (L) is proved anyway. On Jones's route its
  role is the choice of `η` and the contradiction from `[t_c, t_d]`, but that route also needs the
  existence of such crossing arcs in every thin strip, which is the unargued part.

Jones's route, step by step, for comparison:
* (i) Accessibility: needs `IsAccessibleFrom` and `exists_accessible_above`, plus a new argument
  that an accessible point lies on an arc of `M`. This is unargued in print.
* (ii) (e): collar and `exists_accessible_above`.
* (iii) Crossing arcs `[t_a, t_b]` and `[t_c, t_d]` from `x = 5` to `x = 0` in every thin strip:
  recurrence plus a Jordan-curve ordering argument, unargued in print.
* (iv) The contradiction: (L).

Step (iii) is where the real planar difficulty sits. The Poincaré–Bendixson argument below is, in
effect, a complete version of it.

### 6.2 What the commission's sketch gets right, and two corrections

The sketch orders passes by region, not by height on the vertical, and traps later passes with a
Jordan curve `σ ∪ ℓ[x₀, x_m]`. Both ideas are right. Two steps do not hold as written:

1. **"`ℓ` meets `J` only inside passes lying in `R`" and "the left part of `R` lies in the other
   component".** Pieces of `ℓ` between the two passes in time that are *not* passes (shallow
   U-turns through the edges of the box) can enter `R`. Then `R ∩ J ≠ σ°`, and neither part of
   `R ∖ σ` need lie in a single component of `J^c`.
   * *Repair:* make `R` lie in a thinner box in which every point of `ℓ` lies on a pass. This is
     the flow-box property (FB) below, which takes Effros and (O) at two scales.
   * Then `R ∩ J = σ°` exactly.
2. **"So no later pass enters `R`."** A later path from the right part to a later pass in the left
   part must cross `σ°`. But the wiggles let `ℓ` cross `σ°` back and forth inside a single pass,
   so "crossing `σ°`" does not by itself exclude anything.
   * *Repair:* use the *last* time `s*` that `ℓ` is on `σ` before the later pass starts.
   * The pass `P*` through `ℓ(s*)` lies in `R` and ends on the right edge, which lies in the right
     component, after `s*`. After `s*`, however, `ℓ` stays in the left component. This is the
     contradiction.

Also, the base pass can be taken straight (`P₀ = F([¼, ¾] × {0})`), which removes one use of the
θ-curve theorem: the box minus `P₀` is two rectangles.

### 6.3 The hand proof of `NoArcIndecHomPlane`

**Setting.**
* Let `M ⊂ ℝ²` be a homogeneous indecomposable continuum containing an arc. Then
  `S : JonesSetting M` holds (`jonesSetting_of_plane`, from the arc `α ≃ₜ [0, 1]` of
  `NoArcIndecHomPlane` via `TArc`).
* Take a line `ℓ` (`exists_line`) and let `γ = ℓ|[0,1]`.
* Take a collar `F` of `γ` (`exists_collar`). `F` is an embedding of `[0,1] × [−1,1]` with
  `F(t, 0) = ℓ(t)`. It maps `(0,1) × (−1,1)` homeomorphically onto an open set. On the closed
  rectangle, closures and frontiers commute with `F`.
* Write `(X, Y)` for the collar coordinates, and `o = ℓ(½) = F(½, 0)`.
* Let `ε₀` be the bound of (O) (`orientation`). Fix `κ = 1/16`.

**Boxes.**
* For `0 < η ≤ ½` let `Q_η = F([¼, ¾] × [−η, η])`.
* Its open part is `Q°_η = F((¼, ¾) × (−η, η))`.
* Its left edge is `L_η = F({¼} × [−η, η])` and its right edge is `Rt_η = F({¾} × [−η, η])`.

**Passes.**
* Fix a box height `η`. A *pass* is `ℓ[a, b]` with `a < b`, `ℓ(a) ∈ L_η`, `ℓ(b) ∈ Rt_η` and
  `ℓ((a, b)) ⊆ Q°_η`.
* (P1) Distinct passes have disjoint parameter intervals, so they are disjoint sets. If `a < a′ < b`,
  then `ℓ(a′) ∈ L_η ∩ Q°_η = ∅`. The end `b` is the first exit after `a`.
* (P2) Only finitely many passes meet any bounded parameter interval. Each pass joins `L_η` to
  `Rt_η`, which are a positive distance apart, and `ℓ` is uniformly continuous on compact
  intervals.
* (P3) `P₀ = ℓ[¼, ¾] = F([¼, ¾] × {0})` is a pass.
* (P4) `Q°_η ∖ P₀` is the disjoint union of the open upper and lower rectangles. A pass other than
  `P₀` has its interior in one of them, and its end points off `P₀` (by injectivity). So it lies
  *above* or *below* `P₀`.

**Shadow lemma (Effros + (O)).** Let `0 < ε < ε₀`. Assume that points within `ε` of
`γ([κ, 1−κ])` have collar coordinates within `(κ, η′)` of `(s, 0)` (`uniform_near_compact` for
`X` and for `Y`). Let `δ` be the Effros bound for `ε`.

Claim: if `z = ℓ(u)` is within `δ` of `ℓ(x)`, with `x ∈ [¼, ¾]`, then `z` lies on a pass of
`Q_{η′}`, and this pass lies inside `h(ℓ[1/4 − 2κ, 3/4 + 2κ])` for an `ε`-homeomorphism `h`.

*Proof.*
1. Effros gives `h` with `h(ℓ(x)) = z`.
2. (O), applied to `ℓ(· + x)`, gives `h(ℓ(s)) = ℓ(ψ(s))` with `ψ` increasing and continuous, and
   `ψ(x) = u`.
3. On `[s₁, s₂] = [¼ − 2κ, ¾ + 2κ]` we have `X(ℓ(ψ(s))) ∈ (s − κ, s + κ)` and `|Y| < η′`. So `X`
   starts below `¼`, ends above `¾`, and equals `X(z) ∈ [¼, ¾]` at `u`.
4. Put `a = sup {v ≤ u : X(ℓ(v)) ≤ ¼}` and `b = inf {v ≥ u : X(ℓ(v)) ≥ ¾}`, with `v` ranging over
   `[ψ(s₁), ψ(s₂)]`. Then `ℓ[a, b]` is a pass through `z`.

**Two scales.**
* *Scale 1.* Choose `ε₁ < ε₀` with `η′ = η` (the box height `η = ½`, say) and let `δ₁` be its
  Effros bound. Choose `η₂ > 0` with `d(F(x, y), F(x, 0)) < δ₁` for `|y| ≤ η₂` and `x ∈ [¼, ¾]`.
* **(FB) flow box:** every point of `ℓ` in `Q_{η₂}` lies on a pass of `Q_η`. This is the shadow
  lemma at `x = X(z)`.
* *Scale 2.* Choose `ε₂ < ε₀` with `η′ = η₂/2`, and let `δ₂` be its bound. Then every point of `ℓ`
  within `δ₂` of `o` lies on a *thin* pass, that is, a pass contained in `Q_{η₂}`. (By (P1) this
  is the pass given by FB.)
* By recurrence (`line_recurrent`: `o ∈ ω(ℓ)`), points `ℓ(u)` with `u` arbitrarily large lie
  within `δ₂` of `o`.
* Hence there are thin passes starting arbitrarily late. By (P2), among the thin passes after a
  given time there is a first one.

**The region between `P₀` and a thin pass `P_m` above `P₀`.**
* Let `P_m = ℓ[a_m, b_m]` with `a_m > ¾`.
* Apply the cross-cut lemma (§6.4) to the upper rectangle `F((¼, ¾) × (0, η))`, a Jordan domain,
  and the cross-cut `P_m`. The upper rectangle minus `P_m` has two components.
  * The lower one, `R`, has frontier `P₀ ∪ L_ab ∪ P_m ∪ R_ab`. Here `L_ab` and `R_ab` are the edge
    segments between the end points of `P₀` and `P_m`.
  * The other one has the top edge in its frontier.
* The strip `F((¼, ¾) × (η₂, η))` is connected, misses `P_m`, and meets the top edge in its
  closure, so it lies in the other component. Hence `R ⊆ Q_{η₂}`.
* So **every point of `ℓ` in `R` lies on a pass, and that pass lies in `R`.** Its interior is
  connected and misses `P₀ ∪ P_m`.

**Trapping lemma.** Suppose `P_m` is a thin pass above `P₀`, after `P₀`, and no pass with
parameter interval in `(¾, a_m)` lies in `R`. Then no pass after `P_m` lies in `R`.

*Proof.*
1. *`σ`.*
   * `P_m` meets `V = F({½} × [0, η₂])`, because `X` runs from `¼` to `¾` along it.
   * Let `y_m` be the least height of a point of `P_m` on `V`, let `x_m = F(½, y_m) = ℓ(t_m)`, and
     let `σ = F({½} × [0, y_m])`.
   * `σ° = F({½} × (0, y_m))` is connected and misses `P₀ ∪ P_m`. Its closure meets both `P₀`
     (at `o`) and `P_m`, and only `R` has both in its frontier. So `σ° ⊆ R`.
2. *`J = σ ∪ ℓ[½, t_m]` is a Jordan curve.*
   * `σ ∩ ℓ[½, t_m] = {o, x_m}`. `P₀` meets `σ` only in `o`, and `P_m` only in `x_m`.
   * A point of `ℓ((¾, a_m))` on `σ° ⊆ R` would lie on a pass in `R` with interval in `(¾, a_m)`,
     which the hypothesis excludes.
   * The same argument gives **`R ∩ J = σ°`**.
   * Apply `jordan_curve_theorem`: `J^c = W ⊔ W′`, both with frontier `J`.
3. *Two sides.*
   * By the cross-cut lemma again, `R ∖ σ = R_L ⊔ R_R`, with frontiers `σ ∪ A_L` and `σ ∪ A_R`,
     where
     * `A_L = P₀[ℓ(¼), o] ∪ L_ab ∪ P_m[ℓ(a_m), x_m]`;
     * `A_R = P₀[o, ℓ(¾)] ∪ R_ab ∪ P_m[x_m, ℓ(b_m)]`.
   * `R_L` and `R_R` are connected and miss `J`, so each lies in one component of `J^c`.
   * They lie in different components. At `w ∈ σ°`, a small disk minus `σ` is two half-disks, both
     in `R ∖ σ`. Both components of `J^c` meet the disk (`w` is on both frontiers). So the halves
     are in different components, and in different parts `R_L`, `R_R`.
   * Write `W_L ⊇ R_L` and `W_R ⊇ R_R`.
4. *Frontier points.*
   * Let `w ∈ A_L ∪ A_R` with `w ∉ J`. A small disk around `w` misses `J` and meets `R_L` or `R_R`
     respectively. So the points of `A_L ∖ J` are in `W_L`, and those of `A_R ∖ J` are in `W_R`.
   * In particular `ℓ(b_m) ∈ W_R`, and every point of `L_ab°` off `J` is in `W_L`.
5. *Trap.*
   * Suppose a pass `P = ℓ[a, b]` with `a > b_m` lies in `R`. Then `ℓ(a) ∈ L_ab°`, so
     `ℓ(a) ∈ W_L`.
   * For `s > t_m`, `ℓ(s)` meets `J` only in `σ°`, by injectivity. So `ℓ[b_m, a]` meets `σ°`.
   * Let `s*` be the last time in `[b_m, a]` with `ℓ(s*) ∈ σ`. Then `s* < a`.
   * `ℓ(s*) ∈ σ° ⊆ R` lies on a pass `P* = ℓ[a*, b*] ⊆ R` (FB). Since `s* ∈ (b_m, a)` and the
     intervals are disjoint (P1), `b* ∈ (s*, a)`.
   * `ℓ(b*) ∈ Rt ∩ cl R = R_ab`, and `ℓ(b*)` is not an end point of `R_ab` (injectivity). So
     `ℓ(b*) ∈ W_R`.
   * But `ℓ((s*, a])` misses `J` and ends in `W_L`, so `ℓ(b*) ∈ W_L`. This is a contradiction.

**The contradiction.**
1. Let `P_{m₁}` be the first thin pass after `P₀`; say it lies above `P₀`. The case below is
   symmetric (`Y ↦ −Y`).
   * Every pass in `R(P₀, P_{m₁}) ⊆ Q_{η₂}` is thin. So the hypothesis of the trapping lemma holds
     by minimality.
   * Hence no pass after `P_{m₁}` lies in `R(P₀, P_{m₁})`.
2. Let `N_o` be a small square around `o` that misses `P_{m₁}` (and, below, `P_{m₂}`).
   * `N_o ∩ {Y > 0}` is connected and misses `P₀ ∪ P_{m₁}`, and its closure contains `o ∈ P₀`.
   * Of the two components above `P₀`, only `R` has `o` in its frontier. So
     `N_o ∩ {Y > 0} ⊆ R(P₀, P_{m₁})`.
   * So, by step 1 and FB, late points of `ℓ` in `N_o` are not above `P₀`.
3. By recurrence, late points of `ℓ` within `min(δ₂, size of N_o)` of `o` exist.
   * They are below `P₀` and lie on thin passes.
   * So there is a first thin pass `P_{m₂}` below `P₀` after `P_{m₁}`.
4. The hypothesis of the trapping lemma holds for `P_{m₂}`.
   * A pass in `R(P₀, P_{m₂})` is thin and below `P₀`.
   * Thin passes before `P_{m₁}` do not exist, by minimality of `m₁`.
   * Thin passes between `P_{m₁}` and `P_{m₂}` that lie below `P₀` do not exist, by minimality of
     `m₂`.
5. Hence no pass after `P_{m₂}` lies in `R(P₀, P_{m₂})`, which contains `N_o ∩ {Y < 0}` by the
   argument of step 2.
6. A late point of `ℓ` near `o` therefore lies on neither side of `P₀`, nor on `P₀` (injectivity).
   This is a contradiction, so `M` contains no arc. ∎

**What is used.**
* From this batch: `jonesSetting_of_plane`, `exists_line`, `orientation`, `line_recurrent`, and
  `uniform_near_compact`.
* From the repository: `effros_homogeneous`, `exists_collar`/`IsCollar`, and
  `jordan_curve_theorem`.
* New: the cross-cut lemma (§6.4), used three times.
* Not needed: (L), (e), `IsAccessibleFrom`, `exists_accessible_above`, Schoenflies (except
  possibly inside the proof of the cross-cut lemma), and the 1976 crossing machinery.

### 6.4 Plane topology: what the repository has and lacks

Has:
* `jordan_curve_theorem` (`Jones55T2A.lean`: two components, each with frontier `J`).
* `jordan_side` (`Jones49EPlane.lean`).
* The θ-curve lemma `theta_no_common_side` and `theta_separation` (`Jones49FTheta.lean`).
* `janiszewski_compact` (`M25Plane.lean`).
* `compl_union_two_components` (`Mullikin.lean`).
* `plane_schoenflies`, `plane_schoenflies₂` (`Hagopian76D.lean`, `Hagopian76E.lean`).
* `exists_side_arc` (`H76Moore28.lean`).
* `TArc.exists_closing_arc` (`H76Collar.lean`).
* `exists_collar`, `exists_collar_adapted`.
* The special cross-cut `rect_domain_crosscut` (`H76Crosscut.lean`: a vertical segment in a
  collar rectangle below an arc).
* The axiomatic cross-cuts of Moore 1919 (`M19CD2.lean`), which are not in the plane form.

Lacks — **the cross-cut lemma** in general form:

> If `D ⊂ ℝ²` is a bounded Jordan domain with `frontier D = C` (a simple closed curve), and `A` is
> an arc from `p ∈ C` to `q ∈ C` with `A ∖ {p, q} ⊆ D`, then `D ∖ A = D₁ ⊔ D₂`, both open and
> connected, with `frontier Dᵢ = A ∪ Cᵢ`, where `C₁` and `C₂` are the two arcs of `C` from `p` to
> `q`.

This is the θ-curve theorem for `C₁ ∪ C₂ ∪ A`. It follows from what the repository has:
* `C₁ ∪ A` and `C₂ ∪ A` are Jordan curves; their bounded sides are `D₁` and `D₂`.
* Disjointness and `D ∖ A = D₁ ∪ D₂` come from `theta_no_common_side` together with
  `compl_union_two_components`.
* The frontiers come from `jordan_curve_theorem`.

The local facts (a small square minus a segment through its centre, or minus a corner, has two
components) are elementary in collar coordinates.

### 6.5 Skeleton proposal for batch 190

File `HPC/Jones/Jones75P.lean` (planar), importing `HPC.Jones.Jones75A`:

```lean
/-- The cross-cut lemma (θ-curve theorem). -/
theorem crosscut_split {C D A C₁ C₂ : Set Pt} {p q : Pt} (hC : TSCC C) (hDo : IsOpen D)
    (hDc : IsConnected D) (hDb : Bornology.IsBounded D) (hDf : frontier D = C)
    (hA : TArc p q A) (hAD : A \ {p, q} ⊆ D) (h₁ : TArc p q C₁) (h₂ : TArc p q C₂)
    (hC₁₂ : C₁ ∪ C₂ = C) (hC₁₂' : C₁ ∩ C₂ = {p, q}) :
    ∃ D₁ D₂ : Set Pt, IsOpen D₁ ∧ IsConnected D₁ ∧ IsOpen D₂ ∧ IsConnected D₂ ∧
      Disjoint D₁ D₂ ∧ D \ A = D₁ ∪ D₂ ∧ frontier D₁ = A ∪ C₁ ∧ frontier D₂ = A ∪ C₂
```

File `HPC/Jones/Jones75B.lean` (boxes, passes, flow box), for `M : Set Pt`, `S : JonesSetting M`,
a line `ℓ`, and a collar `F` of `ℓ|[0,1]`:

```lean
/-- A pass of the box of height `η`. -/
def IsPass (F : ℝ × ℝ → Pt) (η : ℝ) (ℓ : ℝ → M) (a b : ℝ) : Prop :=
  a < b ∧ (∃ y ∈ Icc (-η) η, (ℓ a : Pt) = F (1/4, y)) ∧ (∃ y ∈ Icc (-η) η, (ℓ b : Pt) = F (3/4, y)) ∧
    ∀ s ∈ Ioo a b, (ℓ s : Pt) ∈ F '' (Ioo (1/4) (3/4) ×ˢ Ioo (-η) η)

theorem IsPass.disjoint … : IsPass F η ℓ a b → IsPass F η ℓ a' b' → (a, b) ≠ (a', b') →
    Disjoint (Icc a b) (Icc a' b')
theorem IsPass.finite … (N : ℝ) : {ab : ℝ × ℝ | IsPass F η ℓ ab.1 ab.2 ∧ ab.1 ≤ N ∧ -N ≤ ab.2}.Finite
theorem IsPass.above_or_below … : IsPass F η ℓ a b → (a, b) ≠ (1/4, 3/4) →
    (∀ s ∈ Icc a b, 0 < Y (ℓ s)) ∨ (∀ s ∈ Icc a b, Y (ℓ s) < 0)      -- collar coordinate `Y`
theorem shadow_pass (S : JonesSetting M) … : ∀ η' > 0, ∃ δ > 0, ∀ x ∈ Icc (1/4) (3/4), ∀ u,
    dist (ℓ u) (ℓ x) < δ → ∃ a b, IsPass F η' ℓ a b ∧ u ∈ Icc a b
theorem flow_box (S : JonesSetting M) … : ∃ η₂ > 0, ∀ u, (ℓ u : Pt) ∈ F '' (Icc (1/4) (3/4) ×ˢ Icc (-η₂) η₂) →
    ∃ a b, IsPass F η ℓ a b ∧ u ∈ Icc a b
theorem exists_late_thin_pass (S : JonesSetting M) … : ∀ T, ∃ a b, T < a ∧ IsPass F η ℓ a b ∧
    ∀ s ∈ Icc a b, (ℓ s : Pt) ∈ F '' (Icc (1/4) (3/4) ×ˢ Icc (-η₂) η₂)
```

File `HPC/Jones/Jones75C.lean` (trap and the Theorem):

```lean
/-- The region between the base pass and a thin pass above it, with its frontier. -/
theorem exists_region … : ∃ R, IsOpen R ∧ IsConnected R ∧ R ⊆ F '' (Ioo (1/4) (3/4) ×ˢ Ioc 0 η₂) ∧
    frontier R = P₀ ∪ L_ab ∪ P_m ∪ R_ab
theorem trap (S : JonesSetting M) … (hnone : ∀ a b, IsPass F η ℓ a b → 3/4 < a → b < a_m →
    ¬ (ℓ '' Ioo a b ⊆ R)) : ∀ a b, IsPass F η ℓ a b → b_m < a → ¬ (ℓ '' Ioo a b ⊆ R)
theorem not_recurrent_of_traps … : False
theorem jones75_noArc : NoArcIndecHomPlane
```

Suggested order: `crosscut_split` first (pure plane topology, the only new planar input); then
`IsPass` and (P1), (P2), (P4); then `shadow_pass`/`flow_box` (metric, along the lines of
`no_backtrack_in_collar`); then `exists_region`, `trap`, and the assembly. The bridge from
`α ≃ₜ unitInterval` in `NoArcIndecHomPlane` to a `TArc` in `M` is routine.
