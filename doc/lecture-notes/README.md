# Lecture notes: homogeneous plane continua, following the formal proof

These notes rewrite the Lean proof in this repository as ordinary mathematics, for
undergraduates who know basic metric topology (open and closed sets, compactness,
connectedness). They follow the formal proof step by step and do not depend on the original
papers: every definition is stated and every step is proved in the text. Where the formal
proof takes a different route from the literature, the notes follow the formal proof.

The whole formal proof of the classification is far too long for one set of notes, so the notes
are planned as a series of eight volumes. **All eight volumes are written.**

| Volume | Content | Status |
|---|---|---|
| 1 | Chains and crookedness; descriptions; described continua are hereditarily indecomposable; Bing's crooked pattern; an explicit construction of a pseudo-arc in the plane | written (`vol1/`) |
| 2 | Composants; Bing's consolidation theorem and pattern following; matching covers; the folding theorem; every pseudo-arc has a description; uniqueness and homogeneity of the pseudo-arc | written (`vol2/`) |
| 3 | General continuum theory: boundary bumping, irreducibility, non-cut points, triods and Sorgenfrey's theorem, snake-like and circle-like continua, upper semicontinuous decompositions, the homeomorphism group and the Effros theorem | written (`vol3/`) |
| 4 | Plane topology I: logarithms, Borsuk, Janiszewski, polygons, enclosing polygons, tree-like continua | written (`vol4/`) |
| 5 | Plane topology II: Moore's characterization of the plane, decompositions of the plane, the Jordan curve theorem | written (`vol5/`) |
| 6 | The indecomposable case: hereditary indecomposability (Hagopian, Jones), span zero (Oversteegen-Tymchatyn), snake-likeness (Hoehn-Oversteegen) | written (`vol6/`) |
| 7 | The decomposable case: aposyndesis, Jones's decomposition, Menger and Whyburn on order, boundaries of complementary domains (Whyburn 1939), homogeneous aposyndetic plane continua are circles (Jones 1949) | written (`vol7/`) |
| 8 | Circles of pseudo-arcs: atomic arcs are snake-like, Bing-Jones Theorem 10, uniqueness and homogeneity, a plane circle of pseudo-arcs; the classification theorem | written (`vol8/`) |

## Volume 1

Source: `vol1/main.tex`, which includes the chapter files `vol1/ch0-intro.tex` …
`vol1/ch5-plane.tex` and the appendix `vol1/appA-formal.tex`. To build:

```
cd doc/lecture-notes/vol1
pdflatex main && pdflatex main
```

It uses only standard packages (`amsmath`, `amssymb`, `amsthm`, `enumitem`, `booktabs`,
`longtable`, `tikz`, `hyperref`, `geometry`, `lmodern`) and contains only ASCII characters.

Contents:

0. Introduction and plan of the notes
1. Preliminaries from metric topology (including limits of finely chained sets)
2. Chains and crookedness
3. Descriptions and hereditary indecomposability (Bing's theorem)
4. Crooked patterns (Bing's pattern, its crookedness, stuttering, tight realizations)
5. A pseudo-arc in the plane (joint positions, the folding homeomorphism, the construction)
A. Table of correspondence with the Lean declarations

After most results there is a "Formal counterpart" line naming the corresponding Lean
declaration; these lines can be skipped.

## Volume 2

Source: `vol2/main.tex`, which includes the chapter files `vol2/ch0-intro.tex` …
`vol2/ch8-main.tex` and the appendix `vol2/appA-formal.tex`. To build:

```
cd doc/lecture-notes/vol2
pdflatex main && pdflatex main
```

It uses the same packages as Volume 1 and contains only ASCII characters. References to
Volume 1 are written "Volume 1, Lemma 2.5" and use Volume 1's printed numbering.

Contents:

0. Introduction (statements, the shape of the proof, where the formal proof differs from Bing)
1. Composants (no composant of an indecomposable continuum is everything; a continuum as a
   space in its own right)
2. Consolidations and other tools for chains (block maps, Bing's Theorem 1: crookedness passes
   to consolidations, subchains joining two points)
3. Pattern following (Bing's Theorem 6, via a combinatorial theorem on integer sequences)
4. Matching covers (Bing's Theorem 11)
5. Two descriptions give a homeomorphism (Bing's Theorem 12)
6. The folding theorem (Bing's Theorem 4, three-link form, by a greedy zigzag)
7. Every pseudo-arc has a description (Bing 1951, Theorem 1)
8. The main theorems (uniqueness, homogeneity, subcontinua, end points)
A. Table of correspondence with the Lean declarations

## Volume 3

Source: `vol3/main.tex`, which includes the chapter files `vol3/ch0-intro.tex` …
`vol3/ch7-effros.tex` and the appendix `vol3/appA-formal.tex`. To build:

```
cd doc/lecture-notes/vol3
pdflatex main && pdflatex main
```

It uses the same packages as Volumes 1 and 2 and contains only ASCII characters. References to
Volumes 1 and 2 use their printed numbering ("Volume 1, Lemma 2.8", "Volume 2, Theorem 1.4"). The
chapters can be read almost independently; Chapter 5 uses chains from Volume 1, and Chapters 2 and
4 use one theorem on composants from Volume 2.

Contents:

0. Introduction (the main results, where they are used, where the formal proof differs from the
   literature)
1. Separated sets and boundary bumping (a continuum plus one piece of a separation, nested
   intersections, components as intersections of clopen sets, separating two closed sets in a
   compact set, the boundary bumping theorem in closed, open and metric form)
2. Irreducible continua (existence of irreducible subcontinua; indecomposable continua are
   irreducible)
3. Non-cut points (Moore's theorem for compact connected T1 spaces, following Nadler 6.3-6.7)
4. Triods and Sorgenfrey's theorem (triods, weak triods, unicoherence; indecomposable continua are
   not triods; Nadler 11.25-11.35, with 11.28 corrected)
5. Snake-like and circle-like continua (subcontinua; snake-like continua are hereditarily
   unicoherent and atriodic; the epsilon-map criterion and topological invariance; the circle;
   proper subcontinua of circle-like continua are snake-like)
6. Upper semicontinuous decompositions (the decomposition space is compact metrizable; monotone
   decompositions; continuity at a residual set of elements)
7. The homeomorphism group and the Effros theorem (the homeomorphism group is Polish; analytic
   nowhere meager sets; van Mill's proof of the open mapping principle; Ungar's corollary)
A. Table of correspondence with the Lean declarations

## Volume 4

Source: `vol4/main.tex`, which includes the chapter files `vol4/ch0-intro.tex` …
`vol4/ch5-treelike.tex` and the appendix `vol4/appA-formal.tex`. To build:

```
cd doc/lecture-notes/vol4
pdflatex main && pdflatex main
```

It uses the same packages as the earlier volumes and contains only ASCII characters. References to
Volumes 1 and 3 use their printed numbering ("Volume 3, Theorem 1.9").

Contents:

0. Introduction (the main results, where they are used, where the formal proof differs from the
   literature, conventions: the sup metric on the plane, points as complex numbers)
1. Continuous logarithms (uniqueness, existence on contractible spaces via homotopy lifting,
   logarithms on small balls, unicoherence of the plane, Brouwer's theorem)
2. Separation by logarithms (same component gives a logarithm, a bounded component forbids one;
   Janiszewski's theorem for compact sets; Borsuk's theorem; topological invariance of plane
   separation)
3. Polygons and the polygonal Jordan curve theorem (a half-open crossing rule, local constancy of the
   parity, the Jordan curve theorem for simple closed polygons, polygonal paths and arcs, no
   logarithm on a polygon around a point)
4. Graphs, mod-2 cycles and enclosing polygons (a separating graph contains an odd cycle,
   decomposition into simple cycles, grid unions, enclosing polygons in a given neighbourhood,
   polygons around points)
5. Tree-like continua (tree chains and their leaves; logarithms on fine tree chains; tree-like
   continua contain no separating continuum; logarithms on tree-like continua; Bing's Theorem 6 by
   notched squares, enclosing polygons and the compact Janiszewski theorem; plane separation up to
   subcontinua; a survey of Bing's Theorem 7)
A. Table of correspondence with the Lean declarations

The direct proof of Bing's Theorem 6 in Chapter 5 was formalized for these notes, in
`HPC/Plane/Theorem6Direct.lean` (`HPC.Plane.theorem6_direct`); the formal development's
earlier proof derives Theorem 6 from Theorem 7.

## Volume 5

Source: `vol5/main.tex`, which includes the chapter files `vol5/ch0-intro.tex` …
`vol5/ch9-quotient.tex` and the appendix `vol5/appA-formal.tex`. To build:

```
cd doc/lecture-notes/vol5
pdflatex main && pdflatex main
```

It uses the same packages as the earlier volumes and contains only ASCII characters. References to
Volumes 1, 3 and 4 use their printed numbering ("Volume 4, Theorem 2.7").

Contents:

0. Introduction (the main results, where they are used, where the formal proof differs from the
   literature: printed statements that are false, the Jordan curve theorem without the
   characterization of the plane, coordinates by a grid; conventions)
1. Arcs and simple closed curves (irreducible continua with two non-cut points are arcs, cut-point
   characterizations of arcs and circles, limits of arcs, replacing pieces of an arc)
2. Decompositions of the plane into non-separating continua (Moore decompositions, the quotient
   space of elements, metrizability, components of complements, Moore 1925 Theorems 1-4)
3. Arcs of elements (Moore 1925 Theorems 5-10 and 12; the decomposition into points)
4. Mullikin's theorem and the Jordan curve theorem (Mullikin's theorem, corrected; Moore 1925
   Theorem 11; the Jordan curve theorem)
5. Moore's axioms and the bridge to topology (Axioms 1-8, the region topology, metrizability,
   arcs in domains)
6. Closed curves in a Moore space (F.A. Theorems 20-43: interiors, cross-cuts, curves in regions,
   chords)
7. Double rulings and Moore's Theorem D (quadrilaterals, rulings, Theorem C refuted and corrected,
   fine rulings)
8. Grids, the Schoenflies theorem and Moore's characterization of the plane (a compact set with a
   grid is a square, Schoenflies, the annulus lemma, exhaustion and pasting, Theorems F and G)
9. The space of elements is a plane (Moore 1925 Theorems 13-22, monotone decompositions of a plane
   continuum, cross-cuts, Schoenflies and collars in the plane)
A. Table of correspondence with the Lean declarations

Some long case analyses in Chapters 6-8 are given as proofs in outline, marked as such; the
complete arguments are in the Lean declarations named in the "Formal counterpart" lines.

## Volume 6

Source: `vol6/main.tex`, which includes the chapter files `vol6/ch0-intro.tex` …
`vol6/ch10-ladders.tex` and the appendix `vol6/appA-formal.tex`. To build:

```
cd doc/lecture-notes/vol6
pdflatex main && pdflatex main
```

It uses the same packages as the earlier volumes and contains only ASCII characters. References to
Volumes 1-5 use their printed numbering ("Volume 3, Theorem 1.9").

Contents:

0. Introduction (the indecomposable case in three steps, the main results, where the formal proof
   differs from the literature, conventions)
1. First consequences of homogeneity in the plane (composants, Effros neighbourhoods, Moore's triod
   theorem; atriodicity, hereditary unicoherence, no proper subcontinuum separates the plane)
2. Continua of type lambda (admissible maps and layers, Kuratowski's family D, existence of type
   lambda continua, uniqueness of the decomposition, Hagopian 1976 Lemma 3; two quoted theorems that
   are false as cited)
3. Hagopian's decomposition (Hagopian 1984: extensions, rigidity of layers, chains, the
   decomposition and its quotient; proofs in outline)
4. No arc, and hereditary indecomposability (Jones's lines, properties (R) and (O), recurrence,
   passes through a collar, the trapping lemma; Hagopian's theorem)
5. Span zero (span, Cook's confluence theorem, Davis's theorem, Oversteegen-Tymchatyn Theorem 3.6
   and Corollary 3.5, Theorem C)
6. The strip theorem (parity of closed polygons, a common zero on a rectangle, the strip lemma,
   Oversteegen-Tymchatyn Theorem 3.2)
7. Snake-likeness: the plan of Hoehn and Oversteegen (PL graphs and separation, Theorem 4, grid
   approximations, Theorem 1 from Theorem 20; the printed Theorem 1 fails for a point)
8. Simple folds (the Krasinkiewicz-Minc lemma, Theorem 8, a library for PL graphs, existence of
   folds, Lemma 6, Proposition 7)
9. Stairwells, and Theorem 20 from Theorem 15 (sides, Propositions 10 and 11, straight sets,
   stairwell and broken stairwell structures, Propositions 17 and 19, Lemma 18, a false sentence on
   p. 208, the lifting induction)
10. Theorem 15: ladders (ladders, a ladder is a stairwell of odd height, a sign function, a ladder
    inside a neighbourhood of a separator)
A. Table of correspondence with the Lean declarations

Chapter 3 and parts of Chapters 9 and 10 are given as proofs in outline, marked as such; the
complete arguments are in the Lean declarations named in the "Formal counterpart" lines.

## Volume 7

Source: `vol7/main.tex`, which includes the chapter files `vol7/ch0-intro.tex` …
`vol7/ch9-decomposable.tex` and the appendix `vol7/appA-formal.tex`. To build:

```
cd doc/lecture-notes/vol7
pdflatex main && pdflatex main
```

It uses the same packages as the earlier volumes and contains only ASCII characters. References to
Volumes 1-6 use their printed numbering ("Volume 3, Theorem 1.10").

Contents:

0. Introduction (the decomposable case in three steps, the main results, where the formal proof
   differs from the literature, conventions)
1. Aposyndesis (Jones 1948: openness, the sets L_y are continua, aposyndesis from the frontier,
   semi-local connectedness, Whyburn (6.2), decomposability, products; the rest of the paper and two
   statements false as printed)
2. Homogeneity and aposyndesis (spreading, from the Effros theorem; the Lemma of Jones 1951 by a
   lower semicontinuous function; Bing 1948 Theorem 5 and Corollary 2 by tight continua; Jones's
   claims (3) and (5))
3. Jones's aposyndetic decomposition (Jones 1955 Theorem 1: the sets L_x partition, are terminal,
   form a continuous decomposition with homogeneous aposyndetic quotient; the elements; elements of
   a plane continuum do not separate the plane; Jones 1951 Theorem 1)
4. Order and Menger's theorem (order of a point, triods, curves of finite order are locally
   connected and arcwise connected, a continuum all of whose points have order 2 is a circle)
5. Whyburn's separating point-order theorem (separating points of open sets, Whyburn (9.1),
   separation chains and their order, good points and residues, a cut-wire argument; Whyburn (3.2),
   (8.4), (9.2))
6. Continua crossing an annulus (lifting to a strip, strip separation by a continuous argument, the
   order of disjoint crossing sets, sectors; the sector theorem and the cyclic order; crossing
   continua from a failure of connectedness im kleinen)
7. Boundaries of complementary domains (Whyburn 1939 (6.22), a joining lemma from Janiszewski's
   theorem, Theorem 14 without inversion, the theta-curve lemma, cyclic Peano continua, Corollary 1)
8. Homogeneous aposyndetic plane continua are circles (Jones 1949: the setting, local separating
   points, Case 1 by Baire, Case 2 with the separation of M - (A + B); Theorems 1 and 2, false as
   printed for a point)
9. The decomposable case (the plane of elements, Jones 1955 Theorem 2 and its closing remarks, the
   elements are pseudo-arcs, the main theorem: a circle or an open atomic map onto the circle with
   pseudo-arc fibres)
A. Table of correspondence with the Lean declarations

## Volume 8

Source: `vol8/main.tex`, which includes the chapter files `vol8/ch0-intro.tex` …
`vol8/ch12-classification.tex` and the appendix `vol8/appA-formal.tex`. To build:

```
cd doc/lecture-notes/vol8
pdflatex main && pdflatex main
```

It uses the same packages as the earlier volumes and contains only ASCII characters. References to
Volumes 1-7 use their printed numbering ("Volume 7, Theorem 9.8").

Contents:

0. Introduction (what remains after Volumes 6 and 7, the main results, where the formal proof
   differs from the literature, conventions)
1. Arcs and circles of pseudo-arcs (definitions, the two halves of a map onto the circle, the
   circle, the pseudo-arc and circles of pseudo-arcs are distinct)
2. Atomic arcs are snake-like (the saturation lemma, terminal points, hereditary unicoherence,
   Bing's minimal counterexample, Bing 1951 Theorem 10 and Fugate's Lemma 1 for terminal
   subcontinua, Fugate's gluing; Bing 1951 Theorem 11 for atomic maps)
3. Chains in the sense of Bing and Jones (nonadjacent links apart, shrinking, private points, runs,
   chain maps, Theorem 6 in the form used, folding a chain along a walk, fibre-fine chains)
4. Snake-like arcs of continua (Theorems 3 and 4, Theorem 5 false as printed and repaired, windows,
   Step 1(b))
5. Theorems 7 and 8 (chains following a chain map on one pseudo-arc and on an arc of pseudo-arcs;
   the corollary to Theorem 8; printed forms that fail)
6. The homeomorphism from a zigzag (Bing and Jones pp. 188-189)
7. Theorem 10 (Conditions A and C, the pieces at the ends and on sub-arcs, the step, the induction)
8. Uniqueness, homogeneity and recognition (gluing two halves; any two circles of pseudo-arcs are
   homeomorphic and each is homogeneous; Domokos-Prajs Theorem 6.1; decomposable homogeneous plane
   continua are circle-like)
9. Circular descriptions (nested circular chains carrying arcs of the circle; the continuum
   described is a circle of pseudo-arcs)
10. Sweep patterns (the sweep lemma, the sweep pattern and its properties)
11. A circle of pseudo-arcs in the plane (standard circular chains, the circular planar step by a
    shear on the universal cover of the punctured plane, the assembly)
12. The classification theorem (the decomposable case, the classification and its plane form, how
    the named inputs were discharged)
A. Table of correspondence with the Lean declarations

Bing's surgery and Fugate's Lemma 1 (Chapter 2), Theorem 7 (Chapter 5), the step of Theorem 10
(Chapter 7) and the planar step (Chapter 11) are given as proofs in outline, marked as such; the complete arguments are in the Lean declarations
named in the "Formal counterpart" lines.
