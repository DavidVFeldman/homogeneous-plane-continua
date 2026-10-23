# Commission: batch 129 — polygonal Janiszewski, part III: polygonal sets, the field change, the two uses; `PlaneFacts` down to one field

**Go!** Runs on top of the batch-128 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch129.md` — this text (also pasted into the prompt);
* `JanPoly.lean` — a skeleton of the new material. Save it as `HPC/Plane/JanPoly.lean`, add
  `import HPC.Plane.JanPoly` at the end of the root `HPC.lean`. Shapes may be adjusted with the
  change recorded.

This batch **edits existing files** — the list in §2 is exhaustive: `HPC/Plane/Tree67.lean` (the
field), `HPC/Plane/Tree7Cross.lean` (`crosscut'`), `HPC/Plane/Tree6.lean` (`exists_theta_point`,
`compFamily_no_circular`, `theorem6_1951`), `HPC/Plane/Tree7.lean` (`treeChain_of_cover`),
`HPC/Plane/Tree7Comp.lean` (`theorem7_1951`), `HPC/Plane/Jct2.lean`
(`planeFacts_of_enclose_janiszewski`), plus `HPC.lean`, `Axioms.lean`/`axioms.txt`, `README.md`,
`OPEN.md`. If the dependency order forces a different placement of the new lemmas (`JanPoly`
imports `Cyc2` which imports `Jct2` which imports `Tree7Comp`, while `Tree6` needs
`janiszewski_polygonal`'s *statement* only through the field), put the field's new statement in
`Tree67.lean` in terms of a definition of `IsPolygonal` placed early enough — move `IsPolygonal` and
its basic lemmas to a small new file `HPC/Plane/Polygonal.lean` imported by `Tree67`, and leave the
proofs that need `Cyc2` in `JanPoly.lean`. Record the final layout.

The report names the commission read in its first line; items *proved / refuted / open with the
obstruction stated*.

## 0. On batch 128

Audited and accepted: `JaniszewskiPoly` proved, no refutation; the sector lemma in its circle
form (`vertex_arcs`, `Complex.arg`, the jump formula on an interval), the strips as the carriers
of side-membership, `gFun_const` by `IsPreconnected.induction₂'` on the plane minus the vertices.
549 declarations, `sorryAx` in one line, root tidy. Your note on isolated points is taken up in
item 1.

## 1. New material (`JanPoly.lean`)

1. **Polygonal sets** (`IsPolygonal` = `graphSet` of a finite set of segments, degenerate ones
   allowed; compactness, unions, segments, points, simple closed polygons, finite unions).
2. **Isolated points** (`isConnected_diff_singleton_of_isOpen`, `separatesPts_insert_iff`,
   `janiszewski_polygonal`). `janiszewski_polygonal` is `janiszewskiPoly_holds` plus the reduction
   from degenerate segments; the docstring flags the one subtle case (an isolated point of `A` that
   lies in `B` becomes an isolated point of `A ∩ B`, so a connected `A ∩ B` with two points has no
   such point, and a single-point `A ∩ B` is handled by the `∅` case of the nondegenerate parts).
   If the reduction turns out to need a hypothesis I have not foreseen, state the strongest form
   you can prove and say what the field would have to say instead.
3. **Local half-disk of a polygon interior** (`polyInterior_local_halfDisk`, from `ball_diff_chord`,
   `parity_flip_edge` and the identification of `polyInterior` with the odd parity set in
   `jct_polygon`'s proof).
4. **Polygonality of `Γ₁ ∩ closure (h₁ ∩ h₂)`** (`isPolygonal_segment_inter_polygon`,
   `exists_open_pieces`, `isPolygonal_frontier_inter_closure`), as in the docstring. This is the
   bookkeeping of the batch.

## 2. The edits

1. **The field** (`HPC/Plane/Tree67.lean`). Replace
   `janiszewski : ∀ A B, IsCompact A → IsCompact B → (IsConnected (A ∩ B) ∨ A ∩ B = ∅) → …`
   by
   `janiszewski : ∀ A B, IsPolygonal A → IsPolygonal B → (IsConnected (A ∩ B) ∨ A ∩ B = ∅) → ∀ x y, ¬ SeparatesPts A x y → ¬ SeparatesPts B x y → ¬ SeparatesPts (A ∪ B) x y`.
   Keep the compact form in a comment with the note "weakened to polygonal sets in batch 129; the
   two uses are polygonal; the compact form is Janiszewski's theorem, not needed". The other two
   fields are unchanged. Then, in `Jct2.lean` or `JanPoly.lean`:
   `planeFacts_of_enclose (henc : …) : PlaneFacts := ⟨jct_polygon, henc, janiszewski_polygonal⟩`,
   and keep `planeFacts_of_enclose_janiszewski` with the polygonal field (or delete it, noted).
2. **`crosscut'`** (`Tree7Cross.lean`): the two sets are `α₁ ∪ c` and `α₂ ∪ c`, simple closed
   polygons, polygonal by `IsSimpleClosedPolygon.isPolygonal`. Same proof otherwise.
3. **`exists_theta_point`** (`Tree6.lean`): new hypotheses `{Γ₁ Γ₂ : Set Pt}
   (hΓ₁ : IsSimpleClosedPolygon Γ₁) (hΓ₂ : IsSimpleClosedPolygon Γ₂)` with `h₁ = polyInterior Γ₁`,
   `h₂ = polyInterior Γ₂` (replace `ho₁`, `ho₂` by these, or keep `h₁`, `h₂` and add equations);
   the sets `A := Γ₁ ∩ closure (h₁ ∩ h₂)`, `B := Γ₂ ∩ closure (h₁ ∩ h₂)` in place of
   `closure C ∩ frontier hᵢ` (note `frontier (polyInterior Γᵢ) = Γᵢ` by `split`), polygonal by
   `isPolygonal_frontier_inter_closure`; `A ∪ Γ`, `B ∪ Γ` polygonal by `IsPolygonal.union`. The
   argument (docstring of batch 118) is otherwise verbatim: if there is no `q` then `A ∩ B ⊆ Γ`,
   so `(A ∪ Γ) ∩ (B ∪ Γ) = Γ`; `A ∪ B ∪ Γ` separates `x` from `y` because `frontier C ∩ U ⊆
   frontier (h₁ ∩ h₂) ∩ U ⊆ (Γ₁ ∪ Γ₂) ∩ closure (h₁ ∩ h₂) = A ∪ B`; `B ∪ Γ` does not separate (`S₂`
   misses `B ⊆ Γ₂`); Janiszewski; `A ∪ Γ` does not separate `x` from `z` (`S₁`); `S_V` misses `A`
   (`A ⊆ closure (h₁ ∩ h₂)`, `V` open missing `h₁ ∩ h₂`). Keep the old statement in a comment with
   the note that it held for arbitrary open `h₁`, `h₂` under the compact Janiszewski.
4. **`compFamily_no_circular`** (`Tree6.lean`): add the hypothesis
   `hpoly : ∀ h ∈ compFamily (polyInterior J) D, ∃ Γ, IsSimpleClosedPolygon Γ ∧ h = polyInterior Γ`
   and pass the polygons to the new `exists_theta_point`. **`treeChain_of_cover`** (`Tree7.lean`):
   the same hypothesis, passed through. **`theorem7_1951`** (`Tree7Comp.lean`): supply it from
   `component_inter_eq_polyInterior` with `notched_eq_polyInterior`, `isSimpleClosedPolygon_
   notchedPoly` and `finite_inter_notchedPoly_of_gp` — the general-position cover is already what
   it uses. **`theorem6_1951`** (`Tree6.lean`): its present proof uses `exists_notched_cover_bdd`,
   not the general-position cover, so its components need not be polygon interiors; re-prove it
   from `theorem7_1951` (a tree chain of polygon interiors of mesh `< ε` is a tree chain of mesh
   `< ε`), statement unchanged. Note in its docstring that Theorem 6 is now a corollary of
   Theorem 7 in the repository, the reverse of Bing's order, and why.
5. **Audit**: `Axioms.lean` group "Polygonal Janiszewski (batch 129)" with the new theorems and
   `planeFacts_of_enclose`; the Duke §3 group's note updated ("relative to `PlaneFacts`, whose
   fields `jct` and `janiszewski` are proved; `enclose` remains a hypothesis"). `axioms.txt`
   regenerated (`sorryAx` in one line). **`OPEN.md`** *Relative results*: the interface now has one
   undischarged field, `enclose`. **`README.md`**: the same, batch count 129.

Report each item; refutations first (candidates: `separatesPts_insert_iff` as stated; the
reduction in `janiszewski_polygonal`; `isPolygonal_frontier_inter_closure` — if some configuration
of two polygons makes `Γ₁ ∩ closure (h₁ ∩ h₂)` fail to be a finite union of segments and points,
that is a refutation of my analysis and the sets must be chosen differently).

## 3. Deliverables

1. Items 1–4 and edits 1–5; `#print axioms` in `doc/batches/audits/axioms-batch129.txt`;
   `axioms.txt` regenerated.
2. Report: first line names the commission read; items and edits in order; the final file layout;
   what `enclose` (batches 130–132: the thickened grid union, the classification of its boundary,
   the outer boundary of a polyomino, holes inside `G`) can reuse from Jct/Cyc.
3. Housekeeping: uploads to `doc/batches/`, `doc/batches/skeletons/`; notes to `doc/`; nothing at
   the root.
4. Not attempted: `enclose`, `fugate_cor1`, `treeLike_nonseparating`.
