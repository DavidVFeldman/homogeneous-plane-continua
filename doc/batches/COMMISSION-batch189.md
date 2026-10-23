# Commission: batch 189 — Part E, Jones 1975 I: arcs and lines; no small reversal; recurrence

**Go!** This batch runs on top of the batch-188 work. Two files come with it, as separate uploads:

* `COMMISSION-batch189.md`: this text, also pasted into the prompt.
* `Jones75A.lean`: the skeleton.
  * Save it as `HPC/Jones/Jones75A.lean`. You may split it under `HPC/Jones/`.
  * Add `import HPC.Jones.Jones75A` at the end of `HPC.lean`. It imports
    `HPC.Hagopian.Hagopian84D`.

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
  * `Axioms.lean` and `axioms.txt` (new group "Jones 1975 I (batch 189)");
  * `README.md`;
  * `LEDGER.md`: a new section for Jones 1975;
  * `OPEN.md`;
  * `doc/notes/jones75.md`.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 188

* **Delivery.** The project download was stale again: its `axioms.txt` is the batch-186 one. Your
  tarball and manifest carried the work; the overlay gives 2414 lines. Keep publishing both (§8.4).
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 2414 lines (2392 + 22 added, none removed), with `sorryAx` in none.
  The 22 new declarations use only the standard three axioms. `Hagopian84D.lean`,
  `Hagopian84A.lean` and `Hagopian84C.lean` contain no `sorry` outside comments. The skeleton's
  statements are unchanged.
* **`hagopian84_decomp : Hagopian84Decomp` is verified**, and with it
  `hagopian76_theorem1_jones (hA : NoArcIndecHomPlane) : Hagopian76Thm1`. The arc step is now the
  last open input of Theorem 1 of Hagopian 1976 on this route. This batch starts on it.
* Your ledger entries H84.29–H84.35 and the non-vacuity notes are right as written.

## 1. The plan, and what my reading of Jones 1975 found

I read Jones 1975 from page images at 250 dpi. `doc/notes/jones75.md` transcribes it correctly,
with two slips (§7). The paper proves the Theorem from (a)–(f). Two findings change the route. An
independent check of this commission (a separate agent, before sending) confirmed 1.1 and §2–§4,
corrected my reading of (d), simplified §4, found a hole in §5, and suggested the planar route of
§6.
Its corrections are folded in below.

**1.1 The proof of (f) is defective (candidate ledger entry; check it).** (f) reads: "If `p` is a
point of `M` and `D` is an open set in `E` with `p ∉ D̄`, then there exists a positive number `ε`
such that no arc `abc` in `M` has the property that both `a` and `c` belong to `D` and the
`ε`-neighbourhood of the subarc `ab` contains both `p` and the subarc `bc`."
* The proof uses only the Effros corollary and (c), and through (c) only (a) and (b). It ends: "This
  is impossible since the `3ε`-neighbourhood of `q₁p₁` contains no point of `p₂q₂` (and
  conversely)."
* That inference is a non sequitur. The images of `a′b′` and `b′c′` lie on the arc
  `L = q₁pq₂ ∪ g[a′b′c′]` (an arc by (c)). But `g[a′b′]` may continue along `L` beyond `q₁` and come
  back near `p₂q₂`. Nothing confines it to `q₁pq₂`.
* **The dyadic solenoid `Σ` refutes the argument.** `Σ` is a homogeneous, indecomposable,
  hereditarily unicoherent, atriodic continuum. It contains arcs, and (c) holds in it (its arc
  components are dense lines). So every step Jones uses holds in `Σ`. Yet (f) fails in `Σ`, even in
  the stronger form with `d(b, p) < ε`. Here is the construction.
  * Take a line `λ` with `λ(0) = a ∈ D`. Choose `S` with `λ[0, S]` `ε/2`-dense in `Σ`.
  * Pick `S₁ ≥ S` with `d(λ(S₁), p) < ε`, and `S₂ > S₁` with `λ(S₂) ∈ D`.
  * Then `abc = λ[0, S₂]` with `b = λ(S₁)` has `N_ε(ab) = Σ ⊇ {p} ∪ bc`.
  * Here "`D` open in `E`" is read as `D` open in `Σ`. Forward rays are dense because `{n ≥ N}` is
    dense in the 2-adic integers.
  * `Σ` is atriodic in the sense of `IsTriod`: an arc minus a subcontinuum has at most two
    components, and `Σ` minus a proper subcontinuum contains a dense composant, so it is connected.
* Two earlier steps of the same proof are unargued as well.
  * The negation of (f) gives a point of `ab` within `ε` of `p`, not `b` itself. Both "a
    homeomorphism … which takes `b` to `p`" and "`b′` is close enough to `b` so that there exists a
    homeomorphism … that moves `b′` to `p` but moves no point more than `ε`" need `b` (or `b′`) near
    `p`. "Close enough to `b`" should read "close enough to `p`".
  * "Leaves the images `q₁` and `q₂` of `a` and `c` respectively in `D`" is unjustified for a
    homeomorphism that is not small.
* For plane continua, (f) is vacuously true once the Theorem is known. The proof, however, does not
  establish it, and the Theorem's proof uses (f) twice: for the choice of `η`, and in its last
  sentence ("property (f) is violated"). Planarity has to enter the argument for (f), or (f) has to
  be replaced.

**1.2 The replacement.** What the Theorem needs from (f) is that a small homeomorphism cannot fold
`T` back on itself. That holds in general, under the hypotheses of `JonesSetting` alone, by a
different argument (§3).
* **(R)** No `ε₀`-homeomorphism fixing a point reverses the arc component through it.
* **(O)** Consequently, an `ε₀`-homeomorphism that carries a point of a line `ℓ` into `ℓ` is
  increasing on `ℓ`. Otherwise it would be a decreasing bijection of `ℓ ≅ ℝ`, it would have a fixed
  point, and it would reverse there.
* Jones's last paragraph (`t_f`, `D₂`, the sequence `εₙ`, `p`) becomes unnecessary. His claim that
  `h` reverses `T` ("This makes `h` take `[t₀, t_d]` onto (approximately) `[t_d, t₀]`") is unargued,
  and by (O) it is false for `ε < ε₀`. The contradiction comes instead from `[t_c, t_d]`, a piece of
  `T` from `x = 5` to `x = 0` in a thin strip, through (L) of §5.
* His choice of `η` (no folds in thin strips) also becomes (L): near an arc of a line, in a thin
  enough strip, the line never moves backwards by `κ` or more.

What remains is planar. On Jones's route it is the existence of a backward move near the bottom
arc: the crossing arcs `[t_a, t_b]` and `[t_c, t_d]`, which go from `x = 5` to `x = 0`. The
alternative is a Poincaré–Bendixson argument that does without them (§6). §6 asks for a
reconnaissance of this core; it is not formalized in this batch.

**1.3 The batches.**
* This batch: lines (§2), (R) and (O) (§3), recurrence (§4), (L) if time remains (§5), and the
  reconnaissance (§6). The Poincaré–Bendixson route of §6 does not need (L); Jones's route does.
* The next batches: the planar core, then `jones75_noArc : NoArcIndecHomPlane`.

## 2. Arcs and lines (general `Y`; skeleton §1–§2)

`JonesSetting Y`: `Y` compact metric, homogeneous, hereditarily unicoherent, atriodic, containing
an arc. `jonesSetting_of_plane` gets it for a homogeneous indecomposable plane continuum with an
arc, from `hagopian75_lemma1`. Effros applies to `Y` (`effros_homogeneous`).

**2.1 Jones (c)** (`union_arc`, `nested`).
1. `A ∩ B` is a continuum (hereditary unicoherence), hence a point or a subarc of each.
2. At each end point of `A ∩ B`, count the arms of `A ∪ B`: the subarc `A ∩ B` (if nondegenerate),
   a tail of `A`, a tail of `B`. Three arms meeting at one point give a triod, against
   atriodicity. So at most one tail at each end (two tails in all if `A ∩ B` is a point).
3. Then `A ∪ B` is an arc (`TArc.union`; look for sub-arc lemmas in `HPC/Moore/`).
4. `nested`: with a common end point `a` and a second common point, `A ∩ B` is a subarc from `a`.
   Its far end is an end point of `A` or of `B`, since otherwise there are three arms there.

**2.2 Interior points** (`exists_arc_through`). Map an interior point of the given arc to `x`.

**2.3 Lines** (`exists_line`). Fix an arc `[a, c]` with `x` interior.
1. *Rays.* `R⁺` is the union of the arcs from `x` that contain `[x, c]`. By `nested` these arcs
   form a chain.
2. *No largest arc.* If `[x, z]` were largest, take an arc `A_z` with `z` interior (2.2). The union
   `[x, z] ∪ A_z` is an arc (2.1). `A_z` has points on the far side of `z`, so the subarc from `x`
   beyond `z` is larger.
3. *Countable cofinality.* `R⁺` is separable. Cover a countable dense subset by arcs of the chain.
   If these were bounded by one arc `[x, y]`, then `R⁺ ⊆ [x, y]` (closed), and `[x, y]` would be
   largest. So they are cofinal.
4. *Parametrize* `[0, ∞)` piecewise along an increasing cofinal sequence of arcs. Do the same for
   `R⁻` (through `a`).
5. `R⁺ ∩ R⁻ = {x}`: an arc from `x` containing both `[x, a]` and `[x, c]` would make them nested.
   `R⁺ ∪ R⁻` is the arc component (2.1 with `[a, c]`).

**2.4** (`line_arc`, `homeo_on_line`).
* Two arcs with the same end points are equal (2.1).
* So a subarc of a line is the image of a parameter interval.
* A homeomorphism maps arc components onto arc components. In parameters it is a bijection of `ℝ`
  that maps compact intervals onto compact intervals, hence continuous and strictly monotone.

## 3. No small reversal (skeleton §3)

**3.1 (R0)** (`no_reversal_arc`). Let `A = [a, p]` and `C = [p, c]` with `A ∩ C = {p}`, and let
`ρ = min(ρ(a, C), ρ(c, A)) > 0`. Suppose `h(p) = p`, `h` moves every point by less than `ρ`, and
`h[A]` meets `C∖{p}`.
* `h[A]` and `C` are arcs from `p` meeting elsewhere, so they are nested (2.1).
* If `C ⊆ h[A]`, then `c = h(y)` with `y ∈ A`, and `d(c, y) < ρ ≤ ρ(c, A)`. Impossible.
* If `h[A] ⊆ C`, then `h(a) ∈ C` and `d(a, h(a)) < ρ ≤ ρ(a, C)`. Impossible.

**3.2 (R), uniform** (`exists_no_reversal`).
1. For each `q`, take an arc through `q` (2.2) and its `ρ_q` from 3.1.
2. Effros gives `δ_q` for `ρ_q / 3`.
3. For `b` within `δ_q` of `q`, let `g` be a `ρ_q/3`-homeomorphism with `g(b) = q`. If `h` fixes
   `b`, moves points less than `ρ_q/3`, and reverses the line through `b`, then `g h g⁻¹` fixes `q`,
   moves points less than `ρ_q`, and reverses the line through `q`. On a line, reversing one arc at
   a fixed point is the same as reversing every arc there (2.4). This contradicts 3.1.
4. Cover `Y` by finitely many balls `B(q, δ_q)` and take `ε₀ = min ρ_q / 3`.

**3.3 (O)** (`orientation`). Let `ε < ε₀` and `h(ℓ(0)) ∈ ℓ`. Then `h` maps `ℓ` onto `ℓ`, so by 2.4
`h(ℓ(s)) = ℓ(ψ(s))` with `ψ` a continuous monotone bijection of `ℝ`. If `ψ` decreases, `ψ(s) − s`
is continuous, strictly decreasing and onto, so `ψ(s*) = s*` for some `s*`, and `h` reverses `ℓ` at
`ℓ(s*)`. This contradicts (R). The skeleton's `orientation` is strengthened to give `ψ` continuous
and onto as well, which §5 uses.

## 4. Recurrence (skeleton §4)

This replaces Jones's proof of "every point of `ab` is a limit point of `T − ab`". His proof has two
steps, and the independent check corrected my first reading of the first.
* "Let `c` be the first point of `T` (if there is one) which is a limit point of `T − ae` for some
  point `e` beyond `c`." If such points exist, a first one does: for a witness `e`, the set
  `cl(T − ae) ∩ ae` is closed and misses `a`, and its first point is the first such point. (I had
  read the argument as showing only that no first point exists; that was wrong.)
* **The gap is orientation.** "Then `c′` has the properties possessed by `c`" holds only if the
  Effros homeomorphism preserves the direction of `T`. If it reverses, `a = g(y)` for some `y` in
  `ce`, and `2ε < d(a, W)` does not exclude that. Adding `d(a, ce)` to the minimum, or using (O),
  repairs it.
* The conclusion of that step, that no such `c` exists, is not yet a contradiction. The triod
  paragraph ("Then `T` union with the image of `T` under two such homeomorphisms … would contain a
  triod") must supply one, and as printed nothing makes those images meet `T`.

Report both as ledger entries. The route below needs neither:

**4.1** (`omegaLim_saturated`).
1. Let `z = lim ℓ(uₙ)` with `uₙ → ∞`, and let `λ` be the line through `z`.
2. Effros gives `εₙ`-homeomorphisms `hₙ` with `hₙ(z) = ℓ(uₙ)` and `εₙ → 0`. By 2.4,
   `hₙ(λ(s)) = ℓ(ψₙ(s))` with `ψₙ(0) = uₙ`.
3. Fix `s`. If `ψₙ(s) ≤ C` along a subsequence, then for every `L`, eventually
   `ℓ[C, C + L] ⊆ hₙ[λ(between 0 and s)] ⊆ N_{εₙ}(λ[0, s])`. Hence `ℓ[C, ∞) ⊆ λ[0, s]`, a compact
   arc, which is impossible: on a different line because arc components are disjoint, on the same
   line by injectivity.
4. So `ψₙ(s) → ∞` and `λ(s) ∈ ω(ℓ)`.

**4.2** (`line_recurrent`; the independent check's argument, shorter than my Zorn argument). Every
line lies in its own forward limit set.
1. Let `K = ω(ℓ)`: nonempty, compact, saturated (4.1). Suppose `ℓ(0) ∉ K`, and let
   `ε = ½ d(ℓ(0), K)`.
2. Take `p ∈ K` and `t` with `ℓ(t)` within the Effros `δ` of `p`, and an `ε`-homeomorphism `g` with
   `g(ℓ(t)) = p`.
3. `g` carries the line `ℓ` onto the line through `p`, which lies in `K`. So `g(ℓ(0)) ∈ K` and
   `d(ℓ(0), g(ℓ(0))) < ε < d(ℓ(0), K)`. Impossible.
4. Apply this to every reparametrization `s ↦ ℓ(s + c)` and `s ↦ ℓ(−s)`. Every line is forward and
   backward recurrent.

This is Jones's own `½d(a, T̄ − T)` device, and it replaces his triod paragraph.

**4.3** `jones75_d` follows for every line, in both directions. Jones states it for every arc `ab`
and the ray from `a` through `b`. §6 needs only one direction.

## 5. In the plane: (L), no backtracking (skeleton §5, shape left to you; if time remains)

Let `ℓ` be a line of the plane continuum `M`, and let `F` be a collar (`exists_collar`, `IsCollar`)
of `γ(t) = ℓ(t)`, `t ∈ [0, 1]`. Write `X` for the first collar coordinate.

**Claim.** For every `κ > 0` there is `η > 0` such that no piece `ℓ[u, β]` lies in
`F([κ, 1 − κ] × (−η, η))` with `X(ℓ(β)) ≤ X(ℓ(u)) − κ`.

**Proof.**
1. Take `ε < ε₀` (3.3) with two properties:
   * `d(F(p), F(p′)) < ε` forces the first coordinates to differ by less than `κ/4` on the compact
     square;
   * `ε` is less than the distance from `F([κ, 1 − κ/2] × {0})` to the complement of the open
     collar `F((0, 1) × (−1, 1))`, so that the points of step 3 stay where `X` is defined (the
     independent check found this condition missing).

   Let `δ` be the Effros bound for `ε`. Take `η` with `d(F(x, y), F(x, 0)) < δ` for `|y| < η`.
   Throughout, `u < β`.
2. Let `s = X(ℓ(β))`, `u₁` the last time in `[u, β]` with `X ≥ s + κ/2`, and `r = s + κ/2`.
3. Effros gives `h` with `h(ℓ(r)) = ℓ(u₁)`. By (O), `h` is increasing on `ℓ`. So
   `h(ℓ(r + κ/4)) = ℓ(t)` with `t > u₁`, and `X(ℓ(t)) > r` to within `κ/4`.
4. If `t ≤ β`, this contradicts `X < r` on `(u₁, β]`.
5. If `t > β`, then `ℓ(β) = h(ℓ(t′))` with `t′ ∈ [r, r + κ/4]` (intermediate values, `ψ`
   continuous), so `X(ℓ(β)) > s`. Impossible.

Jones's choice of `η` is the case of a fold. His `[t_c, t_d]`, an arc of `T` from `x = 5` to `x = 0`
in a thin strip, contradicts (L) at once.

## 6. Reconnaissance: the planar core (report only)

Write a complete hand proof of `NoArcIndecHomPlane` from §2–§5, with every planar step argued. List
the repository material each step uses: `jordan_curve_theorem`, `exists_collar`, `IsAccessibleFrom`,
`exists_accessible_above`, Schoenflies, and the 1976 machinery of crossings. Then propose a skeleton
for the next batch. Two routes; choose one and say why.

1. **Jones's route.**
   * `T` is accessible from below along `[t₀, t₅]`. This is unargued: "let us assume that `T` is
     accessible from the complement of `M`".
   * (e).
   * Then show that in every thin strip above `[t₀, t₅]`, `T` has a piece from `x = 5` to `x = 0`.
     In the text: "if the order of `t_a` and `t_b` were reversed … we would take the next arc of `T`
     below `[t_a, t_b]` and appeal to the Jordan curve theorem to get the proper order".
   * Then (L) gives the contradiction.
2. **A Poincaré–Bendixson route** (recommended by the independent check; its sketch, not checked
   in detail).
   * *Passes.* By Effros and (O), each point of `ℓ` within `δ` of `ℓ(½)` lies on an `ε`-shadow of
     the base arc, hence on a unique left-to-right crossing (*pass*) of a collar box `B`. By
     recurrence (4.2) passes come arbitrarily near `ℓ(½)`.
   * *Wiggles are real.* Collar coordinates are only topological, so a pass can cross the vertical
     segment `V` through `ℓ(½)` several times, and two passes can interleave on `V`. Jordan curves
     built from consecutive hits on `V` are simple, but the trapping argument fails. Choosing first
     and last hits does not repair this.
   * *The fix: order passes by crossing order in `B`, not by height on `V`.* Take pass 0 (the base)
     and a later pass `m` such that no pass between them in time lies in the region `R` of `B`
     between them.
     * Let `σ ⊂ V` be a subarc with interior in `R` and ends on the two passes. It exists because
       the two closed sets of hits on `V` have adjacent points.
     * Then `J = σ ∪ ℓ[x₀, x_m]` is a Jordan curve.
     * Just after `x_m`, `ℓ` lies in the component containing the right part of `R`.
     * Every later pass inside `R` starts in the left part of `R`, which lies in the other
       component.
     * `ℓ` meets `J` only inside passes lying in `R`. So no later pass enters `R`.
   * *The contradiction.* Apply this with `m₁` the first pass and `m₂` the first later pass on the
     other side of pass 0. Every later return close enough to `ℓ(½)` lies in `R(0, m₁)` or
     `R(0, m₂)`, which contradicts recurrence.
   * *Planar inputs:* the Jordan curve theorem, the θ-curve theorem (a box minus two disjoint
     crossings has three components; a cross-cut splits a Jordan domain), and the two-sidedness of
     collar segments. Accessibility, (e) and (L) are not needed.

   Check this sketch, write it out in full, and say which pieces of plane topology the repository
   lacks (the θ-curve theorem, cross-cuts).

## 7. Places to check (candidate ledger entries; new section "Jones 1975" in `LEDGER.md`)

1. **(f), p. 59:** proof defective (§1.1, the solenoid), with the two further unargued steps of
   §1.1. Check the solenoid claims as a hand argument. They need not be formalized.
2. **(d), p. 58:** the "first point" step is sound as to existence, but its transport step ignores
   orientation (§4). The triod paragraph does not give a contradiction as printed.
3. **(c), p. 57:** true; the argument is (a) plus (b), unstated.
4. **The Theorem, pp. 59–61:**
   * "let us assume that `T` is accessible";
   * "There exists a positive integer `η` … This follows from property (f)";
   * "This makes `h` take `[t₀, t_d]` onto (approximately) `[t_d, t₀]`. So there is a fixed point"
     (unargued; by (O) false for `ε < ε₀`);
   * "Clearly `t_f` cannot lie in `D̄₁ ∪ D̄₂ ∪ D̄₃`";
   * "it is easy to see that `p ∉ D̄₂` and property (f) is violated".
5. **`doc/notes/jones75.md`:**
   * the pages are 57–61 (the sixth PDF page is blank), not 57–62;
   * the Effros corollary is printed with "`d(h(p), p) ≤ ε`", not "`< ε`".

## 8. Deliverables

1. **The items of §2–§5.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch189.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. **`LEDGER.md`:** a new section "Jones 1975", with the printed sentences quoted.
3. **Notes:** `doc/notes/jones75.md` (the corrections of §7.5, and the route of §2–§6).
4. **Publish the changes, as in batch 188.** At the end of the run:
   * create `doc/batches/batch189-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch189-MANIFEST.txt`;
   * publish both, as you published the report.
5. **The report.** Its first line names the commission it read. It covers:
   * the items in order;
   * the non-vacuity notes (`JonesSetting` is a structure);
   * the ledger entries;
   * the axioms used by each theorem;
   * the reconnaissance of §6, with a skeleton proposal for the next batch.
6. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/` and `doc/batches/skeletons/`.
   * Nothing is left at the root.
