# What remains for the Hoehn–Oversteegen classification (H–O Theorem 2)

State of the repository as of batch 196. `axioms.txt` contains no `sorryAx`. On the indecomposable
branch the only open input is the named `Prop` `HPC.HO16.HOThm15` (H–O Theorem 15); `HOThm20`
now follows from it (`HPC.HO16.ho16_theorem20_of_thm15`). The decomposable branch is not yet
assembled, and the circle of pseudo-arcs is not yet defined (sections 2 and 3 below).

## The target

H–O Theorem 2 (p. 180): up to homeomorphism, the only non-degenerate homogeneous plane continua
are (1) the circle, (2) the pseudo-arc and (3) the circle of pseudo-arcs. H–O deduce it as follows:

* **indecomposable case:** Theorem B (Hagopian), Theorem C (O–T) and Theorem 1 show the
  continuum is a pseudo-arc;
* **decomposable case:** Theorem A (Jones) applies, and the Bing–Jones uniqueness of the circle of
  pseudo-arcs finishes the argument.

## Status, piece by piece

| piece | status | Lean |
|---|---|---|
| Theorem B: indecomposable homogeneous plane ⇒ hereditarily indecomposable | **proved** | `HPC.Hagopian.hagopian76_theorem1` |
| Theorem C: indecomposable homogeneous plane ⇒ span zero | **proved** | `HPC.Span.theoremC` |
| H–O Theorem 4, grid graphs, paths, ε-map ⇒ snake-like | **proved** | `HPC/HO16/HO16A.lean` and imports |
| simple folds, Lemma 6, Prop. 7, Theorem 8 for folds | **proved** | batch 194 |
| Defs. 9, 12, 13, 16, Props. 10, 11, 17, Claim 14.1, Lemma 18 | **proved** | batch 195 |
| Proposition 19 (full) | **proved** | `HPC.HO16.hoProp19_holds`, `ho16_prop19_full`, `ho16_prop19` |
| Theorem 20 from Theorem 15 (the induction, the fold tower, reduction to components) | **proved** | `HPC.HO16.ho16_theorem20_of_thm15` |
| H–O Theorem 1 "if", plane case | **proved from `HOThm20`**, hence from `HOThm15` | `HPC.HO16.ho16_theorem1_plane` |
| Bing 1951: the pseudo-arc is unique | **proved** | `pseudoArc_unique` |
| indecomposable branch of Theorem 2 | **proved from `HOThm15`** | `HPC.HO16.homeomorph_pseudoArc_of_indec_homogeneous_of_thm15` |
| Theorem A (Jones 1955 Thm 2, with Jones 1949 Thm 1) | **proved** | `HPC.Jones.jones55_theorem2'`, `jones55_elements_indecomposable'` |
| the pseudo-arc is a homogeneous plane continuum | **proved** | `HPC/Plane/Snake51.lean` |
| **`HOThm15`** (H–O Theorem 15, stairwells of odd height near a separator) | **open** | `HPC/HO16/P19Defs.lean` |
| **decomposable branch: assembly** | not written | — |
| **circle of pseudo-arcs: definition and Bing–Jones uniqueness** | not formalized; source not in `doc/sources` | — |
| circle of pseudo-arcs is a homogeneous plane continuum (needed only for the "conversely" reading) | not formalized | — |

## 1. `HOThm15`: the last open item of the indecomposable branch

H–O Theorem 15 (pp. 194–198): for a connected PL graph `G`, a separator `M ⊆ G × (0, 1)` of
`G × {0}` from `G × {1}` and an open `U ⊇ M`, there is `S ⊆ U ∩ G × (0, 1)` with a stairwell
structure of odd height. Proposition 19 and the Theorem 20 induction are done (batch 196), so this
is all that stands between the repository and an unconditional
`homeomorph_pseudoArc_of_indec_homogeneous`.

What the library lacks for it (report 196, §6):

1. **Two-dimensional PL machinery**: PL functions on a triangulation of `G × [0, 1]` (prisms over the
   edges of a subdivision of `G`); only one-dimensional subdivisions exist now (`Subdiv.lean`).
2. **General position**: perturbing vertex values so the zero set meets each 2-cell in a segment
   avoiding vertices, and so the finitely many critical first coordinates `Z′` avoid the
   non-ordinary points of `G`.
3. **Structure of the zero set** of a generic PL function (a finite 1-dimensional PL set separating
   `{u < 0}` from `{u > 0}`), kept inside `U` via a sign function `u = d(·, R₀′) − d(·, R₁′)` and a
   fine enough approximation (compactness of `G⋆ \ U`).
4. **Reading off sheets**: over each component of `G \ Z′` the zero set is a finite union of graphs
   ordered by height; consecutive ones glue into sheets with end sets over `Z′`; the odd number of
   crossings of each vertical fibre gives odd height; then (S1)–(S5) are checked one by one.

H–O's own route (Claim 15.1, irreducible separators after Kuratowski §§46, 49, removal of wedges)
is an alternative; the PL-function route above avoids the irreducible-separator theory.

## 2. The decomposable branch

Take `M` decomposable, homogeneous, a plane continuum. `jones55_theorem2'` already gives the
following:

* `lSetoid M` is a continuous decomposition;
* `M / lSetoid M ≃ₜ Circle`;
* every element `Lset x` is connected, homogeneous, indecomposable and non-separating.

What is missing:

1. **The glue, which is routine.** The elements `Lset x` are compact, since they are closed in `M`.
   Homeomorphisms of `M` permute them (`lSetoid_homeomorph`). Hence they are either all degenerate
   or all non-degenerate:
   * **degenerate:** the quotient map is a homeomorphism, so `M ≃ₜ Circle`;
   * **non-degenerate:** transport homogeneity and indecomposability to `Subtype.val '' Lset x ⊆ ℝ²`
     and apply the indecomposable branch. Every element is then a pseudo-arc, which needs `HOThm15`.
2. **The circle of pseudo-arcs**, which is not in the repository. There is no definition of it, and
   the Bing–Jones paper (*Another homogeneous plane continuum*, Trans. AMS 90 (1959)) is not in
   `doc/sources`. H–O (p. 183) describe the needed result as follows: a circle-like continuum with an
   open map onto the circle whose fibres are pseudo-arcs is unique up to homeomorphism. Two ways to
   apply it:
   * **Bing–Jones's result in the form H–O quote:** circle-likeness of `M` must then be proved
     separately. Here this is a planar fact about continuous decompositions of `M` over `S¹`; for
     example, `P × S¹` has such a decomposition but does not embed in the plane.
   * **a plane form, if the source has one:** this form has no circle-likeness hypothesis. Which form
     the source actually proves was not checked, because the paper is not in the repository.

   One option is to take "the circle of pseudo-arcs" to mean any continuum in this uniqueness class.
   Then the definition and the uniqueness theorem become a single formalization item, which needs
   the Bing–Jones source.
3. **The "conversely" direction.** This step is optional and depends on how Theorem 2 is read: it
   shows that all three continua really occur. The circle and the pseudo-arc are done. The circle
   of pseudo-arcs needs the Bing–Jones construction, together with the proofs that it embeds in the
   plane and is homogeneous.

## 3. Not needed for Theorem 2

* H–O Theorem 1 for continua that are not planar. This would need "span zero ⇒ tree-like" (H–O cite
  [31]). The plane route avoids it by using grid graphs.
* The "only if" direction of Theorem 1.
* The converse of Theorem 20.
* Rogers' converse to Theorem A.
* H–O Theorem 3, on homogeneous plane compacta. It would also need the product theorem of
  Mislove–Rogers, which H–O cite as [41].
