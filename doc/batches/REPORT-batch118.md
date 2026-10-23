Commission read: COMMISSION-batch118.md (batch 118 — Bing 1951 (Duke), Theorem 6 relative to `PlaneFacts`).

# Report, batch 118

**Outcome.** Every item is proved. Nothing in the skeleton is refuted. Two statements changed shape;
both changes drop hypotheses the proofs do not use, so each new statement implies the old one.
`theorem6_1951 (hPF : PlaneFacts)` depends on `[propext, Classical.choice, Quot.sound]` only.
**`PlaneFacts'` was not needed:** `local_side` is proved from `jct`, and `PlaneFacts` is unchanged.
`HPC/Plane/Tree67.lean` was not edited.

The skeleton is installed as `HPC/Plane/Tree6.lean`, and `import HPC.Plane.Tree6` is the last line
of `HPC.lean`. The uploads were moved to their usual places: `doc/batches/COMMISSION-batch118.md` and
`doc/batches/skeletons/Tree6.lean`. Auxiliary material is in five new files, each imported by the
next:

| file | contents |
| --- | --- |
| `HPC/Plane/Tree6Local.lean` | the local geometry of a simple closed polygon (two rays from each point), two rays cutting a square, `local_side_of_split`, `sides_of_split` |
| `HPC/Plane/Tree6Arcs.lean` | polygonal paths in vertex-function form (`vpath`, `IsSArc`), polygonal connectivity, loop erasure, first point in a closed set, reversal, concatenation, two arcs closing into a simple closed polygon, the three-set theta polygon |
| `HPC/Plane/Tree6Cut.lean` | initial and final parts of a simple arc, splitting a simple arc at a point |
| `HPC/Plane/Tree6Thread.lean` | open and closed chains of simple arcs (`chain_sarc`, `closed_chain_polygon`) |
| `HPC/Plane/Tree6Trim.lean` | threading a closed chain through a circular chain of sets (`trim_chain`, `trim_close`, `threaded_nat`, `threaded_nat_chain`) |

No `sorry` remains in any of these files or in `HPC/Plane/Tree6.lean`. The only existing files
edited are `HPC.lean` (the import), `Axioms.lean` (a new §3 group) and `axioms.txt`
(regenerated).

## Refutations

None. The commission listed three candidates.
* **`IsThreaded`'s clauses** are consistent: `exists_threaded` produces instances, and
  `IsThreaded.isSimpleClosedPolygon` holds.
* **`exists_threaded`'s hypotheses** are sufficient as stated. The "no three links share a point"
  hypothesis the commission anticipated is **not needed** (details under item 2).
* **The shape of `exists_theta_point`** is true. It was weakened on the hypothesis side only
  (item 4).

## Items

1. **Polygonal arcs — proved.** `exists_polyPath_of_isConnected`, `exists_simplePolyArc_of_polyPath`,
   `IsSimplePolyArc.isContinuum`, `.split`, `.exists_first_mem`.
   * Representation: the definitions `polyPathOf` and `IsSimplePolyArc` (vertex lists) are
     unchanged. The proofs use a vertex function `v : ℕ → Pt` with a vertex count `n`
     (`vpath v n`, `IsSArc v n`), linked to the list form by `isSimplePolyArc_iff`
     (`v i = w.getD i 0`, `n = w.length`, and `List.ofFn` the other way).
   * Polygonal connectivity, as commissioned: the points reachable by a polygonal path are open
     and relatively closed in `h`.
   * Loop erasure: a path from `p` to `q` with the **fewest vertices** among the paths inside the
     given one is simple. A repeated vertex, a backtrack (three consecutive vertices with
     overlapping segments) or a crossing of two segments would each give a shorter path inside it.
   * `split`: the point is either a vertex or inside one segment. In both cases the two parts are
     simple arcs that meet only at the point.
   * `exists_first_mem`: on the first segment that meets `K`, take the point whose parameter is
     the least element of the compact set of parameters `t ∈ [0, 1]` landing in `K`.
2. **Threading — proved, with no added hypothesis.** `IsThreaded.isSimpleClosedPolygon`,
   `exists_threaded`, statements unchanged.
   * `IsThreaded.isSimpleClosedPolygon`: re-index over `ℕ`. Arcs `0, …, m−2` concatenate into one
     simple arc (`chain_sarc`, by induction; each new arc meets the union of the earlier ones only
     at the junction, since non-consecutive arcs are disjoint). That arc and arc `m−1` meet exactly
     in the two junction points, so they close into a simple closed polygon
     (`closed_chain_polygon`, via `isSimpleClosedPolygon_of_two_arcs`).
   * `exists_threaded`: there are two cases.
     * **Some point lies in three links.** By `hcirc` the three links are then pairwise adjacent,
       which forces `m = 3`. The three links share an open ball, and a small right triangle in it
       threads them, with one side in each link (`threaded_nat_chain`).
     * **No point lies in three links.** This is the commissioned trimming (`threaded_nat`).
       * Choose `Q i ∈ d (i−1) ∩ d i` and simple arcs `G i ⊆ d i` from `Q i` to `Q (i+1)` (item 1).
         `Q i ≠ Q (i+1)`, since otherwise the point would lie in three links.
       * Forward (`trim_chain`, for `i = 0, …, m−2`): cut the current arc at its first point `x`
         on `G (i+1)`. The start of the current arc is not on `G (i+1)`, since that would be a
         point of three links. Then restart along `G (i+1)` from `x` (its final part, `exists_suffix`).
         Here `x ≠ Q (i+2)` for the same reason.
       * Closing (`trim_close`): cut the last arc at its first point `y` on the trimmed arc `0`, and
         keep only the part of arc `0` from `y`. Its end `P 1` survives because `y ≠ P 1`: a point
         of `d (m−1) ∩ d 0 ∩ d 1`.
       * The junction points are distinct, and non-consecutive arcs are disjoint because
         non-adjacent links are.

     So "no three links share a point" is needed only inside one branch of the case split. Where it
     fails, `m = 3` and the triangle replaces trimming. The commission's worry about `m = 3` is
     answered by that split.
   * Theorem 6 itself does not use `exists_threaded`. Like the skeleton's docstring of
     `compFamily_no_circular`, it merges `h₃, …, h_m` into `V` and uses the three-set version
     `exists_theta_polygon` (from `theta_polygon_of_three`: polygonal arcs `p₀ → p₁ → p₂ → p₀`,
     then three trims at first points).
3. **Consequences of `jct` — proved.**
   * `polyInterior_disjoint_of_unbounded`, as stated, with no `jct`. A connected unbounded `W`
     missing `J` lies in one component of `Jᶜ`, which is unbounded. Compactness of `J` is not used.
   * `PlaneFacts.split` (new, a convenience): `polyInterior Γ = U` and the other facts of `jct` in
     one statement.
   * **`PlaneFacts.local_side`**, statement unchanged. What is proved: the ball is the sup-metric
     ball, an open square.
     * `polygon_local_rays`: for small `r`, `Γ ∩ ball w r` is the union of two rays from `w` (in
       directions that are nonzero and not positively parallel) intersected with the ball. When `w`
       is not a vertex the two rays are opposite.
     * `ball_diff_rays`: the square minus the two rays is the union of two preconnected pieces. When
       the rays are opposite, these are two convex halves. Otherwise they are a convex sector and the
       union of two convex half-plane pieces that meet.
     * `local_side_of_split`: each piece lies in `U` or in the exterior. Since `w` is in the closure
       of both, `U ∩ ball w r` is exactly one piece, nonempty and connected, for every
       `0 < r ≤ r₀`.
   * **`PlaneFacts.sides` — proved, shape change:** the hypothesis `hαcl : IsClosed α` was
     unused and is dropped. The union of the local pieces `U ∩ ball w r_w` over `w ∈ α`
     (radii small enough to lie in `h`) is preconnected. This holds for preconnected `α`
     (`isPreconnected_biUnion_of_local_meet`): the piece at `w` meets the piece at every nearby
     point of `α`, since both contain a smaller local piece there. The union contains every local
     piece. Its closure contains `α`, because each piece has `w` in its closure.
4. **The point `q` — proved (`PlaneFacts.exists_theta_point`), shape change, by the docstring's
   argument with `janiszewski` in the compact form.**
   * **Shape change:** the pieces are only assumed connected and to contain the junction points:
     `p₂ ∈ α₁ ∩ α₂`, `p₃ ∈ α₂ ∩ β`, `p₁ ∈ β ∩ α₁`. The skeleton's `α₁ ∩ α₂ = {p₂}`,
     `α₂ ∩ β = {p₃}`, `β ∩ α₁ = {p₁}` and the distinctness of the `p`'s were not used and are
     dropped. The new statement implies the old one.
   * One step of the docstring's argument changed. Instead of "a path from `x` to `y` leaves `C`
     through `frontier C ∩ U`", the formal proof shows that the component of `x` in
     `(A ∪ B ∪ Γ)ᶜ` lies in `U` and in `C ∪ (closure C)ᶜ`, hence in `C`, while `y ∉ C`.
   * Final contradiction: `S₁ ∪ S_V`, which is connected through `z`, joins `x` to `y` while
     missing `A ∪ Γ`.
   * `janiszewski` is applied to `A ∪ Γ` and `B ∪ Γ`. Both are compact (closed subsets of the
     bounded `closure U`), and their intersection is `Γ` (connected) because `A ∩ B = ∅`.
   * `PlaneFacts` is used through `jct` (for the split, `local_side` and `sides`) and through
     `janiszewski`. No new field was needed.
5. **Theorem 6 — proved.** `compFamily_no_triple`, `compFamily_no_circular`, `theorem6_1951`,
   statements unchanged.
   * `compFamily_no_triple`: components of `d₀ ∩ d` for the same `d` are equal or disjoint. Three
     distinct members meeting at a point therefore come from three distinct `d`'s, which have no
     common point.
   * `compFamily_no_circular`: as in the docstring, with `exists_theta_polygon` for `h₁`, `h₂` and
     `V = h₃ ∪ ⋯ ∪ h_m`. `V` is connected as the union of a chain, and `V ∩ h₁ ∩ h₂ = ∅` by
     `compFamily_no_triple`. The interior of `Γ` lies in `d₀`, by
     `polyInterior_disjoint_of_unbounded` applied to `W = d₀ᶜ`; that `W` is connected and unbounded
     is `PlaneFacts.compl_polyInterior`, from `jct`.
   * `theorem6_1951`: as commissioned, with `exists_notched_cover_bdd`. This is the batch-117 cover
     with the boundedness of the links recorded, and it has the same proof. Boundedness is needed
     because in a metric space the diameter of an unbounded set is `0`, so a bound on `diam`
     alone does not bound a set.
     * `H'` is a finite subfamily of `compFamily d₀ D` covering `M`. It consists of the components
       of points of `M`, chosen by compactness of `M`, so every member meets `M`.
     * Open: by `isOpen_connectedComponentIn_of_isOpen`.
     * Coherent: by `isCoherent_of_minimal_cover`.
     * No triple point: by `compFamily_no_triple`.
     * No circular subchain: by `compFamily_no_circular`.
     * `diam < ε`: each member lies in a bounded link of `D`.

## Ledger notes: sentences of Bing's two paragraphs that needed more than they say

* **The coherence of `H'`.** Bing takes it for granted. It needs every member to meet the connected
  `M`. `H'` is built from components of points of `M`, so each member contains a point of `M`;
  `isCoherent_of_minimal_cover` (batch 117) then applies without minimality.
* **The connectedness of the `h_i` used for threading.** "Let `p_1 p_2 ⋯ p_m p_1` be a simple closed
  curve such that `p_i p_{i+1}` lies in `h_i`" needs each `h_i` to be connected, so that polygonal
  arcs exist inside it. The members of `compFamily` are components, hence connected
  (`compFamily_props`).
  * Building the curve takes item 1: polygonal connectivity, loop erasure, first points and
    splitting.
  * It also takes the trimming of item 2. When three links share a point (`m = 3`), the trimming
    does not apply and a small triangle replaces it.
  * For Theorem 6 only three sets are needed: `h₁`, `h₂` and the connected union
    `V = h₃ ∪ ⋯ ∪ h_m`.
* **The point `q`.** "There is a point `q` on the interior of this simple closed curve which is a
  boundary point of `h_1`, a boundary point of `h_2`, and a boundary point of `h_1 · h_2`" is not
  argued by Bing.
  * It takes the Janiszewski argument of item 4.
  * That argument rests on the local two-sidedness of a polygon (`local_side`, `sides`). This is
    the longest part of the batch, `HPC/Plane/Tree6Local.lean`.
  * Bing's "boundary point of `h_1 · h_2`" is formalized as `q ∈ closure (h₁ ∩ h₂)`. That is all
    the argument uses.
* **The use of `W`** (the unbounded complementary domain). That the interior of the threaded curve
  lies in `d₀` is "a connected unbounded set missing `Γ` misses the interior of `Γ`"
  (`polyInterior_disjoint_of_unbounded`), applied to `W = d₀ᶜ`.
  * The fact itself needs no Jordan curve theorem.
  * The connectedness and unboundedness of `d₀ᶜ` come from `jct` (`PlaneFacts.compl_polyInterior`):
    `d₀ᶜ` is the exterior `V` together with `J ⊆ closure V`.

## Audit

* `Axioms.lean` has a new group, "Bing 1951 (Duke) §3, Theorem 6 — relative to `PlaneFacts`
  (batch 118)", with the 14 theorems of the skeleton.
* `doc/batches/audits/axioms-batch118.txt` is `#print axioms` for every theorem of
  `HPC/Plane/Tree6.lean` and of the five auxiliary files (102 theorems), generated by the script
  `axioms-batch118.lean`. Every one shows `[propext, Classical.choice, Quot.sound]` or a subset of
  it.
* `doc/batches/audits/axioms-before-batch118.txt` is the previous `axioms.txt`.
* `axioms.txt` is regenerated (376 lines, up from 362). `sorryAx` still appears in exactly two
  lines: `theorem3_end` and `fugate_cor1`.

Not attempted, as commissioned: Theorem 7, `theorem3_end`, `fugate_cor1`.

## Next

Batch 119 as planned. `exists_threaded` is available for `m` links if Theorem 7 needs it, as are
`IsSimplePolyArc.split` and the chain lemmas for building polygons from arcs.
