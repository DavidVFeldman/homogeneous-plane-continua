Commission read: `doc/batches/COMMISSION-batch144.md` (batch 144 — Part D, Moore VIII: the end of Moore 1919. A Σ-space is a number plane).

# Report, batch 144

`lake build HPC` succeeds with `import HPC.Moore.M19G` added at the end of `HPC.lean`. The skeleton is
kept verbatim at `doc/batches/skeletons/Moore1919G.lean`, and the commission at
`doc/batches/COMMISSION-batch144.md` (both moved from the root; nothing new is at the root). The
sources are `doc/sources/moore1919.pdf`, pp. 169, 177–178, and `doc/sources/moore1916.pdf` (F.A.),
pp. 159, 162–163. `HPC/Moore/M19G.lean` is the skeleton with its `sorry`s replaced by proofs, one
shape change (`m19_annulus`, whose shape the commission left open) and two added statements
(`m19_annulus_square`, `m19_openCurve`). The statements of `m19_schoenflies_boundary`, `m19_plane`,
`m19_theoremG` and `m19_final` are unchanged. The main build carries no `sorry` in the new files.
`axioms.txt` (regenerated, 996 lines = 971 + 25) has `sorryAx` in no line.

**Outcome in one line.** Items A (Schoenflies with prescribed boundary), B (the annulus lemma),
C (`m19_plane`) and D (Theorem G with the open-curve property; the final paragraph) are *proved*.
Nothing is left open, and `OPEN.md` is unchanged.

| file | content |
|---|---|
| `HPC/Moore/M19GSquare.lean` | pure topology (`HPC.Sq`): **the square of `Grid.exists_square` restricts to the grid's parametrizations on two lines** (`Grid.exists_square_param`, from `Grid.mem_L_of_pos_eq` via `Grid.pos_phi`, `Grid.pos_psi`); **homeomorphisms of the square fixing two adjacent sides pointwise and prescribed on the other two** (`exists_square_reparam`, by the fibrewise interpolation `interp`) |
| `HPC/Moore/M19GPaste.lean` | pure topology (`HPC.Sq`): **pasting compatible square maps over an exhaustion into a homeomorphism `ℝ × ℝ ≃ₜ X`** (`exhaust_homeomorph`); **the radial step**: a square map of radius `r` and a collar of its boundary give one of radius `r + 1` (`radial_step`); **a plane from an exhaustion with collars** (`plane_of_collars`); the base stage (`stage_of_square`) |
| `HPC/Moore/M19GBoundary.lean` | **Schoenflies with two sides prescribed** (`m19_schoenflies_param`, batch 143's construction with its last step replaced) and **with four sides prescribed** (`m19_schoenflies_boundary_proof`) |
| `HPC/Moore/M19GCuts.lean` | the extreme points of a disc on a horizontal line of a square (`extreme_points`); **a closed curve has only one interior** (`interior_unique`); every closed curve is a quadrilateral (`exists_quad`); **a closed curve with its interior is a square, boundary to the curve** (`exists_square_of_interior`); **two cuts of the annulus** (`exists_cuts`) |
| `HPC/Moore/M19GSplit.lean` | cutting an interior along an arc (`half_split`); **the annulus is the union of two quadrilaterals** with disjoint interiors (`annulus_decomp`) |
| `HPC/Moore/M19GCollar.lean` | **the closed annulus is a collar of the inner curve** (`exists_collar`) |
| `HPC/Moore/M19GPlane.lean` | the exhaustion (`m19_plane_exhaust`); **the plane** (`m19_plane_proof`); the annulus lemma in square form (`annulus_square`) |
| `HPC/Moore/M19GCor.lean` | open curves in F.A.'s sense (`Space.IsOpenCurveFA`); **closed embeddings of `ℝ` give open curves** (`isOpenCurveFA_of_isClosedEmbedding`); **Moore's sequential limits are the limits of the region topology** (`isSeqLimit_iff_tendsto`); Theorem G and the final paragraph from a homeomorphism with `ℝ²` (`theoremG_of_homeomorph`, `final_of_homeomorph`) |
| `HPC/Moore/M19G.lean` | the skeleton: `m19_schoenflies_boundary`, `m19_annulus`, `m19_annulus_square` (added), `m19_plane`, `m19_theoremG`, `m19_openCurve` (added), `m19_final` |

All names below are in namespace `HPC.Moore` unless stated.

## Items

**A. `m19_schoenflies_boundary` — proved** (Axioms 1–8), statement as in the skeleton. As the
commission suggested: two sides come from the grid construction itself. Batch 143's construction
takes parametrizations `fA` of `AB` and `fB` of `BC`. The line `kφ` of the first family carrying
`fA` has position `0`, and the position of `fA s` in the second family is `s` (`Grid.pos_phi`); so
by `Grid.mem_L_of_pos_eq` the square sends `(0, s)` to `fA s` (`Grid.exists_square_param`), and
likewise on `BC`. This gives `m19_schoenflies_param`. For the other two sides, let `a`, `b` be the
homeomorphisms of `[0, 1]` comparing the square's restriction to `CD` and `DA` with the given
parametrizations `φDC`, `φAD`. `exists_square_reparam` builds a homeomorphism `H` of the square
fixing `p.1 = 0` and `p.2 = 1` pointwise with `H (1, y) = (1, a y)` and `H (x, 0) = (b x, 0)` (the
interpolation `(x, y) ↦ (x, (1 − w x) y + w x · a y)`, then the same in the other coordinate).
Composing gives the four prescribed sides.

**B. `m19_annulus` — proved** (Axioms 1–8). **Shape change:** the skeleton's `True` is replaced by
the **collar form**: if `J₁ ∪ I₁ ⊆ I₂`, there is `H : S × ℝ → S`, continuous and injective on
`J₁ × [0, 1]`, with `H (z, 0) = z` on `J₁`, `H '' (J₁ × [0, 1]) = J₂ ∪ I₂ − I₁` and
`H '' (J₁ × {1}) = J₂`. Composed with any homeomorphism of `J₁` onto the boundary of a square, this
is a square annulus compatible with that homeomorphism. The **square form** is added as
`m19_annulus_square`: an embedding `Ψ` of the square of radius `r` (sup norm) onto `J₁ ∪ I₁`,
boundary onto `J₁`, extends to an embedding `Ψ'` of the square of radius `r + 1` onto `J₂ ∪ I₂`,
boundary onto `J₂`, mapping the square annulus `r ≤ ‖p‖ ≤ r + 1` onto `J₂ ∪ I₂ − I₁`.
*Proof.* (1) **Two cuts** (`exists_cuts`): put `J₂ ∪ I₂` on a square (`exists_square_of_interior`);
on a horizontal line through a point of `I₁` the extreme points of `J₁ ∪ I₁` lie on `J₁`
(`extreme_points`); the horizontal segments from them to the sides of the square give disjoint
arcs `PP'`, `QQ'` meeting `J₁ ∪ I₁` only in `P`, `Q` and `J₂` only in `P'`, `Q'`. (2) **Two
quadrilaterals** (`annulus_decomp`): `J₁ = a₁ + a₂`, `J₂ = b₁ + b₂` (arcs from `P` to `Q` and from
`P'` to `Q'`), and the closed curves `Kᵢ = PP' + bᵢ + Q'Q + aᵢ` have disjoint interiors `Aᵢ` with
`K₁ + A₁ + K₂ + A₂ = J₂ + I₂ − I₁` (by `half_split`, cutting an interior along an arc, twice, and
`interior_unique`). (3) **Gluing** (`exists_collar`): each `Kᵢ + Aᵢ` receives a square map with
prescribed boundary (item A): on `aᵢ` a parametrization of `aᵢ`, on the cuts the same
parametrizations of `PP'` and `QQ'` for both, on `bᵢ` anything. The two maps agree on the cuts and
`H (z, s)` is the value at height `s` above the parameter of `z` on `J₁` (continuity on the closed
pieces `a₁ × [0, 1]` and `a₂ × [0, 1]`, via a continuous left inverse of an embedding of `[0, 1]`,
`exists_leftInverse_of_isEmbedding`).
**Fig. 3:** Moore's nine-cell ruling is **not proved as stated**. In its place the proof uses two
cuts and two quadrilaterals (the commission suggested four quadrilaterals; two suffice).

**C. `m19_plane` — proved** (Axioms 1–8), statement as in the skeleton: `S` with the region topology
is homeomorphic to `ℝ × ℝ`. Theorem F's exhaustion `Jₙ ∪ Iₙ ⊆ Iₙ₊₁`, `⋃ Iₙ = S`
(`m19_plane_exhaust`, from `m19_theoremF_proof`); `J₀ ∪ I₀` is a square with boundary `J₀`
(`exists_square_of_interior`, `HPC.Sq.stage_of_square`); each annulus is a collar of `Jₙ`
(`exists_collar`), so the square map of radius `n + 1` extends radially to one of radius `n + 2`
(`HPC.Sq.radial_step`: `Ψ' p = H (Ψ ((n+1) p / ‖p‖), ‖p‖ − (n+1))`). The compatible maps are pasted
over the exhaustion (`HPC.Sq.exhaust_homeomorph`: the maps agree on the smaller squares, so their
union is a homeomorphism `ℝ × ℝ ≃ₜ S` agreeing with each of them on its square). The space is
Hausdorff by batch 137 (`t2Space`).

**D. Corollaries — proved.**
* `m19_theoremG` (Axioms 1–8), statement as in the skeleton: `G₁` is the set of images of the
  horizontal lines `ℝ × {y}` and `G₂` of the vertical lines `{x} × ℝ` under the homeomorphism of
  `m19_plane` (`theoremG_of_homeomorph`); each is the range of a closed embedding of `ℝ`.
* `m19_openCurve` (**added**; Axiom 1 only): the range of a closed embedding of `ℝ` is an open curve in
  F.A.'s sense (p. 159), defined as `Space.IsOpenCurveFA`: closed, connected, and for each of its
  points `P`, `M − P` is the union of two disjoint nonempty connected sets neither containing a
  limit point of the other. The two sets are the images of `(−∞, t)` and `(t, ∞)`. So the curves of
  `m19_theoremG` are open curves in F.A.'s sense.
* `m19_final` (Axioms 1–8), statement as in the skeleton: a bijection `e : S ≃ ℝ × ℝ` such that `P` is
  a sequential limit point of `u` (Moore's `IsSeqLimit`) iff `e (u n) → e P`. The commission's route
  was through metrizability; the proof does not need it: `isSeqLimit_iff_tendsto` shows from Axiom 1
  alone that Moore's sequential limit is convergence in the region topology (the regions are a
  basis; Moore's definition quantifies over regions about `P`), and `e` is the homeomorphism.

## Ledger entries (`LEDGER.md` §6, subsection *batch 144*)

1. **Fig. 3, the nine-cell ruling**: unargued; *not proved as stated*, replaced by two cuts and two
   quadrilaterals (`exists_cuts`, `annulus_decomp`).
2. **The open curves `kₘ`, `tₙ`**: unargued; needed by Moore's route, *not needed* by ours.
3. **"This process may be continued … two sequences of arcs `gₘ₀, gₘ₁, …`"** and **"The sum of all
   the arcs … is clearly a continuous open curve"** (p. 178): unargued; *not needed*. The open
   curves of our route are images of lines, open curves in F.A.'s sense by `m19_openCurve`.
4. **"It is clear that through every point there is just one curve of the set `α` …"** (p. 178):
   unargued; *supplied* by `m19_theoremG`.
5. **The final paragraph** (the correspondence of `t₀` with the reals; *"It is clear that the
   correspondence thus established … is continuous"*): unargued; *supplied* by `m19_final`. Neither
   the 1915 characterization of the line nor metrizability is used.
6. **"Σ₁ or Σ₂"** (p. 169): `m19_plane` is stated and proved for **Σ₁** (Axioms 1–8) only, as in the
   skeleton. The Σ₂ form is not formalized. F.A. p. 163: Σ₂ is Axioms 1–5, 6′, 7′, 8, with
   *"AXIOM 6′. If R is a region and AB is an arc such that AB − A is a subset of R then (R + A) − AB
   is connected"* and *"AXIOM 7′. Every boundary point of a region is a limit point of the exterior of
   that region"*; F.A. asserts without proof that Σ₁ and Σ₂ *"are equivalent with respect to point and
   limit point of a point-set"*. **For batch 145, Σ₂ is not needed** if Moore 1925 Theorem 21's
   verification of Axioms 6 and 7 themselves (after 6′ and 7′) is formalized: then `m19_plane` applies
   as it stands. Σ₂ would be needed only to skip that verification, and then F.A.'s unproved
   equivalence would have to be supplied.

Further: Schoenflies with prescribed boundary, the annulus lemma in both forms, `interior_unique`
and `exists_square_of_interior` are recorded as outcomes.

## Axioms

From `doc/batches/audits/axioms-batch144.txt` (generated by `axioms-batch144.lean`), which lists all
46 theorems of the nine new files: every theorem uses `[propext, Classical.choice, Quot.sound]` or a
subset of it (`mem_of_inter_eq'` uses none). In particular:

| theorem | Lean axioms | Moore's axioms |
|---|---|---|
| `m19_schoenflies_boundary` | `propext, Classical.choice, Quot.sound` | 1–8 |
| `m19_annulus`, `m19_annulus_square` | `propext, Classical.choice, Quot.sound` | 1–8 |
| `m19_plane` | `propext, Classical.choice, Quot.sound` | 1–8 |
| `m19_theoremG` | `propext, Classical.choice, Quot.sound` | 1–8 |
| `m19_openCurve` | `propext, Classical.choice, Quot.sound` | 1 |
| `m19_final` | `propext, Classical.choice, Quot.sound` | 1–8 |
| `interior_unique` | `propext, Classical.choice, Quot.sound` | 1–5, 7 |
| `HPC.Sq.Grid.exists_square_param`, `HPC.Sq.exists_square_reparam`, `HPC.Sq.exhaust_homeomorph`, `HPC.Sq.radial_step`, `HPC.Sq.plane_of_collars` | `propext, Classical.choice, Quot.sound` | none (pure topology) |

"Moore's axioms" lists the hypotheses the statement carries (for the skeleton's statements, the
skeleton's `include`). Group *Moore 1919, the plane (batch 144)* of `Axioms.lean` lists the 25 main
names. The previous `axioms.txt` is kept as `doc/batches/audits/axioms-before-batch144.txt`; the new
one differs from it only by the 25 added lines.

## Reading plan for batch 145: Moore 1925 §I and Theorem 22

`doc/sources/moore1925.pdf` and the transcription notes of §I mentioned in the commission are not yet
in the project, so this plan is organized by what has to be verified rather than by a reading of
Moore's proofs. Theorem numbers below are those of the commission (§I: Theorems 1–22; 4–7, 9, 10 and
15–19 proved only by analogy; Theorem 21 verifies Σ₂, then Axioms 6 and 7; Theorem 22 concludes).

**The target.** For an upper semicontinuous decomposition `G` of the plane into bounded
nonseparating continua, build a `Space` structure on the set of elements (regions and the sequence
`K₁, K₂, …` of Axiom 1) satisfying Axioms 1–8, and show that its region topology is the quotient
topology. Then `m19_plane` gives `Quotient ≃ₜ ℝ²`, which is what Jones 1955 Theorem 2 (batch 146)
uses.

**What transfers directly from batches 137–144.**
* **The endpoint**: `m19_plane` (Σ₁) and, if wanted, `m19_theoremG`, `m19_final`. No Σ₂ form is
  needed if Axioms 6 and 7 are verified (ledger entry 6 above).
* **The bridge** (batch 137, `HPC/Moore/Basic.lean`): the region topology of a `Space`, its
  metrizability and Hausdorffness, and `isSeqLimit_iff_tendsto` (batch 144), so the comparison with
  the quotient topology can be done by comparing bases or convergent sequences.
* **The decomposition side** (`HPC/Jones/Decomp.lean`, batch 136): for an u.s.c. decomposition, the
  quotient map is closed, the quotient is Hausdorff, second countable and metrizable. These give
  Axioms 4 and 5 and much of Axiom 1 once regions are defined.
* **The plane side**: the elements are continua in `ℝ²`; Moore's regions of the decomposition space
  are images of plane regions saturated by `G`. The arc and closed-curve theory of F.A. developed in
  batches 137–143 is about the abstract space and cannot be used to *verify* the axioms (it presupposes
  them); for the plane itself Mathlib supplies connectedness and compactness, and the Jordan curve
  theorem in `ℝ²` is needed for Axiom 8 and for regions that are interiors of curves. Whether the
  project's plane results (`HPC/Plane`) contain a usable Jordan curve theorem for `ℝ²` should be
  checked first; if not, `m19_plane` cannot be applied to `ℝ²` itself to get one (circular), and
  this becomes the main missing piece.

**Order of reading.** (1) Moore's definition of the regions of the decomposition space and of the
sequence `Kₙ`. (2) The theorems that verify Axioms 1–5 (the u.s.c. property and the nonseparation
of the elements); compare with `HPC/Jones/Decomp.lean`. (3) Theorems 4–7, 9, 10, 15–19, proved by
analogy: for each, identify the F.A. or plane theorem invoked and whether it is about the plane
(usable) or about the abstract space (not usable before the axioms hold). (4) Theorem 21: Axioms
6′, 7′, then 6, 7, and Axiom 8 — the crux, where the nonseparating hypothesis enters. (5) Theorem 22.
A candidate shortcut to weigh against Moore's route: verify Axioms 1–8 directly for the quotient
topology using plane topology, without Moore's intermediate Σ₂ step.
