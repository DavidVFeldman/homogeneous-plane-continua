import HPC.PseudoArc.Thm14
import HPC.Plane.Polygonal

/-!
# Batch 117: Bing 1951 (Duke) §3, Theorems 6 and 7 — definitions, the plane-topology interface,
# and the grid cover

Batch 117 delivery of the skeleton (original: `doc/batches/skeletons/Tree67.lean`). Every work
item is proved; the fields of `PlaneFacts` are *hypotheses*. Two skeleton statements were refuted
and corrected (`janiszewski_closed_false`: the `janiszewski` field now asks compact sets;
`inter_gridSq_subset_notched_false`: the distance hypothesis is now strict); the commissioned
versions are kept in block comments. Hypotheses found unnecessary were dropped, each noted in the
docstring. Report: `doc/batches/REPORT-batch117.md`.

**Bing's definitions (p. 653).** A chain is a finite collection of open sets `d_1, …, d_j` with
`d_i ∩ d_j ≠ ∅ iff |i − j| ≤ 1`, links not required connected. A *circular chain* has more than
two links and its first and last links intersect. A finite *coherent* collection `G` of open sets
is a *tree chain* if no three of the open sets have a point in common and no subcollection of `G`
is a circular chain. (`G` is coherent if for each proper subcollection `G'` of it, an element of
`G'` intersects an element of `G − G'`.) A compact continuum is *tree-like* if for each `ε > 0`
there is a tree chain covering it with links of diameter `< ε`.

**Theorem 6 (p. 656).** *Each bounded plane continuum which does not contain a continuum which
separates the plane is tree-like.* **Theorem 7 (p. 657).** *If `M` is a tree-like plane continuum
and `ε` a positive number, there is a tree-chain covering `M` whose links are the interiors of
simple closed curves of diameters less than `ε`.* ("In the proof of Theorem 6 we establish the
following result.")

**The interface.** Bing's proof uses three facts of plane topology that the repository does not
have and that are not to be proved here: the Jordan curve theorem for simple closed polygons; a
simple closed curve around a non-separating continuum inside any neighbourhood of it ("there is
an unbounded continuum `W` which does not intersect `M` such that the complement of `W` is the
interior `d_0` of a simple closed curve and `d_1, …, d_n` covers `d_0`"); and Janiszewski's
theorem, from which the point `q` of the circular-chain contradiction will be derived in batch
118. They are bundled as the hypotheses `PlaneFacts`; every theorem of §3 is proved relative to
it — discharged in batch 131: `planeFacts_holds` (`Enc2.lean`). (David: "treated as a hypothesis, albeit known actually to be a theorem".) Two more facts enter
for Theorem 7 and are recorded in the ledger when they are reached (batch 119): components of the
intersection of two polygon interiors are polygon interiors; a tree-like plane continuum contains
no continuum separating the plane.

The plane is `Pt = ℝ × ℝ` with its product (sup) metric, as everywhere in `HPC/Plane`; "diameter
less than `ε`" is in that metric, which only changes constants.
-/

namespace HPC.Plane

open Set Metric

open scoped Classical

/-! ### Polygons, interiors, separation -/

/-- A closed polygon with `n ≥ 3` vertices: the union of the segments `v i — v (i+1)` (indices
mod `n`). -/
def polygonOf {n : ℕ} (v : Fin n → Pt) : Set Pt :=
  ⋃ i : Fin n, segment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)

/-- A **simple closed polygon**: a closed polygon whose vertices are distinct, non-adjacent edges
are disjoint and adjacent edges meet only at their common vertex. -/
def IsSimpleClosedPolygon (J : Set Pt) : Prop :=
  ∃ (n : ℕ) (_ : 3 ≤ n) (v : Fin n → Pt), J = polygonOf v ∧ Function.Injective v ∧
    ∀ i j : Fin n, i ≠ j →
      (((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) →
        segment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) ∩
          segment ℝ (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) ⊆
            {v i, v j, v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩}) ∧
      (¬ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) →
        Disjoint (segment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩))
          (segment ℝ (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩)))

/-- The **interior** of a compact set `J` of the plane: the union of the bounded components of
its complement. (No Jordan curve theorem is needed to define it.) -/
def polyInterior (J : Set Pt) : Set Pt :=
  {x | x ∉ J ∧ Bornology.IsBounded (connectedComponentIn Jᶜ x)}

/-- `A` **separates the plane** (Bing: "separates the plane"): its complement is not connected. -/
def SeparatesPlane (A : Set Pt) : Prop := ¬ IsConnected Aᶜ

/-- `A` separates `x` from `y`: they lie in different components of `Aᶜ`. -/
def SeparatesPts (A : Set Pt) (x y : Pt) : Prop :=
  x ∉ A ∧ y ∉ A ∧ y ∉ connectedComponentIn Aᶜ x

/-! ### Tree chains -/

/-- A finite collection `G` of open sets is **coherent** (Bing): every nonempty proper
subcollection has an element meeting an element of the rest. -/
def IsCoherent (G : Finset (Set Pt)) : Prop :=
  ∀ G' ⊂ G, G'.Nonempty → ∃ A ∈ G', ∃ B ∈ G \ G', (A ∩ B).Nonempty

/-- A **circular chain** of open sets: `m > 2` sets `d 0, …, d (m-1)`, `d i ∩ d j ≠ ∅ iff
`|i − j| ≤ 1` *or* `{i, j} = {0, m-1}`. -/
def IsCircularChain (G : Finset (Set Pt)) : Prop :=
  ∃ (m : ℕ) (_ : 2 < m) (d : Fin m → Set Pt), Function.Injective d ∧ G = Finset.univ.image d ∧
    ∀ i j : Fin m, (d i ∩ d j).Nonempty ↔
      (((i : ℤ) - j).natAbs ≤ 1 ∨ (i.val = 0 ∧ j.val = m - 1) ∨ (j.val = 0 ∧ i.val = m - 1))

/-- A **tree chain** (Bing, p. 653): a finite coherent collection of open sets, no three with a
common point, no subcollection a circular chain. -/
def IsTreeChain (G : Finset (Set Pt)) : Prop :=
  (∀ A ∈ G, IsOpen A) ∧ IsCoherent G ∧
    (∀ A ∈ G, ∀ B ∈ G, ∀ C ∈ G, A ≠ B → B ≠ C → A ≠ C → A ∩ B ∩ C = ∅) ∧
    ∀ G' ⊆ G, ¬ IsCircularChain G'

/-- A compact continuum is **tree-like** if for every `ε > 0` some tree chain of bounded links of
diameter `< ε` covers it.

**Repaired in batch 133.** Up to batch 132 the links were asked `diam A < ε` only, not
`Bornology.IsBounded A`:
`(∀ A ∈ G, diam A < ε)`. Mathlib's `diam` of an unbounded set is `0`, so `{univ}` was a tree chain
of every mesh and every continuum (a circle included) satisfied the old definition
(`IsTreeLikeOld`, `isTreeLikeOld_of_isContinuum` in `TreeLikeNS.lean`). Boundedness is now
required, as `IsEpsChain` (snake-like) has. -/
def IsTreeLike (M : Set Pt) : Prop :=
  Fold.Q78.IsContinuum M ∧ ∀ ε : ℝ, 0 < ε → ∃ G : Finset (Set Pt), IsTreeChain G ∧
    (∀ A ∈ G, Bornology.IsBounded A ∧ diam A < ε) ∧ M ⊆ ⋃ A ∈ G, A

/-! ### The interface -/

/- **The interface as commissioned — refuted (batch 117).** Its third field is false for closed
sets of the plane: see `janiszewski_closed_false` below (the two closed half-lines `[0, ∞) × {0}`
and `(-∞, 0] × {0}` meet in a point, neither separates `(0, 1)` from `(0, -1)`, their union, the
`x`-axis, does). A structure with a false field has no inhabitant, so every theorem stated relative
to it would be vacuous. Kept as commissioned, commented out; the corrected `PlaneFacts` below
requires `A` and `B` compact, which is Janiszewski's theorem as it holds in the plane (and is what
batch 118 uses: there `A`, `B` are closures of bounded links).

structure PlaneFacts : Prop where
  jct : ∀ J : Set Pt, IsSimpleClosedPolygon J →
    ∃ U V : Set Pt, IsOpen U ∧ IsOpen V ∧ Jᶜ = U ∪ V ∧ Disjoint U V ∧
      IsConnected U ∧ IsConnected V ∧ Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧
      frontier U = J ∧ frontier V = J
  enclose : ∀ M : Set Pt, Fold.Q78.IsContinuum M → ¬ SeparatesPlane M →
    ∀ G : Set Pt, IsOpen G → M ⊆ G →
      ∃ J : Set Pt, IsSimpleClosedPolygon J ∧ Disjoint J M ∧ M ⊆ polyInterior J ∧
        polyInterior J ⊆ G
  janiszewski : ∀ A B : Set Pt, IsClosed A → IsClosed B → (IsConnected (A ∩ B) ∨ A ∩ B = ∅) →
    ∀ x y : Pt, ¬ SeparatesPts A x y → ¬ SeparatesPts B x y → ¬ SeparatesPts (A ∪ B) x y
-/

/-- **The commissioned `janiszewski` field is false** (so the commissioned `PlaneFacts` had no
inhabitant): `A = [0, ∞) × {0}` and `B = (-∞, 0] × {0}` are closed, `A ∩ B = {(0, 0)}` is
connected, neither separates `(0, 1)` from `(0, -1)` (the three convex half-planes `y > 0`,
`x < 0` resp. `x > 0`, and `y < 0` give a connected set avoiding it), and `A ∪ B` is the `x`-axis,
which does. -/
theorem janiszewski_closed_false : ¬ ∀ A B : Set Pt, IsClosed A → IsClosed B →
    (IsConnected (A ∩ B) ∨ A ∩ B = ∅) →
    ∀ x y : Pt, ¬ SeparatesPts A x y → ¬ SeparatesPts B x y → ¬ SeparatesPts (A ∪ B) x y := by
  intro h
  set A : Set Pt := Ici 0 ×ˢ {0}
  set B : Set Pt := Iic 0 ×ˢ {0}
  have hup : IsPreconnected {p : Pt | 0 < p.2} :=
    (convex_halfSpace_gt (LinearMap.snd ℝ ℝ ℝ).isLinear 0).isPreconnected
  have hdn : IsPreconnected {p : Pt | p.2 < 0} :=
    (convex_halfSpace_lt (LinearMap.snd ℝ ℝ ℝ).isLinear 0).isPreconnected
  have hl : IsPreconnected {p : Pt | p.1 < 0} :=
    (convex_halfSpace_lt (LinearMap.fst ℝ ℝ ℝ).isLinear 0).isPreconnected
  have hr : IsPreconnected {p : Pt | 0 < p.1} :=
    (convex_halfSpace_gt (LinearMap.fst ℝ ℝ ℝ).isLinear 0).isPreconnected
  have hnotsep : ∀ (C : Set Pt) (S : Set Pt), IsPreconnected S → S ⊆ Cᶜ →
      ((0 : ℝ), (1 : ℝ)) ∈ S → ((0 : ℝ), (-1 : ℝ)) ∈ S → ¬ SeparatesPts C (0, 1) (0, -1) := by
    intro C S hS hSC hx hy ⟨_, _, hc⟩
    exact hc (hS.subset_connectedComponentIn hx hSC hy)
  refine h A B (isClosed_Ici.prod isClosed_singleton) (isClosed_Iic.prod isClosed_singleton) ?_
    (0, 1) (0, -1) ?_ ?_ ?_
  · left
    have : A ∩ B = {(0, 0)} := by
      ext ⟨p, q⟩
      simp only [A, B, mem_inter_iff, mem_prod, mem_Ici, mem_Iic, mem_singleton_iff,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, -⟩; exact ⟨le_antisymm h3 h1, h2⟩
      · rintro ⟨rfl, rfl⟩; simp
    rw [this]; exact isConnected_singleton
  · refine hnotsep A ({p : Pt | 0 < p.2} ∪ {p : Pt | p.1 < 0} ∪ {p : Pt | p.2 < 0})
      ((hup.union ((-1 : ℝ), (1 : ℝ)) (by simp) (by simp) hl).union ((-1 : ℝ), (-1 : ℝ))
        (by simp) (by simp) hdn) ?_ (by simp) (by simp)
    rintro ⟨p, q⟩ hpq ⟨h1, h2⟩
    simp only [mem_singleton_iff] at h2
    simp only [mem_union, mem_setOf_eq, h2] at hpq
    simp only [mem_Ici] at h1
    rcases hpq with (h | h) | h <;> linarith
  · refine hnotsep B ({p : Pt | 0 < p.2} ∪ {p : Pt | 0 < p.1} ∪ {p : Pt | p.2 < 0})
      ((hup.union ((1 : ℝ), (1 : ℝ)) (by simp) (by simp) hr).union ((1 : ℝ), (-1 : ℝ))
        (by simp) (by simp) hdn) ?_ (by simp) (by simp)
    rintro ⟨p, q⟩ hpq ⟨h1, h2⟩
    simp only [mem_singleton_iff] at h2
    simp only [mem_union, mem_setOf_eq, h2] at hpq
    simp only [mem_Iic] at h1
    rcases hpq with (h | h) | h <;> linarith
  · refine ⟨by simp [A, B], by simp [A, B], fun hy => ?_⟩
    have hsub : connectedComponentIn (A ∪ B)ᶜ (0, 1) ⊆
        {p : Pt | 0 < p.2} ∪ {p : Pt | p.2 < 0} := by
      intro p hp
      have hp' := connectedComponentIn_subset _ _ hp
      simp only [A, B, mem_compl_iff, mem_union, mem_prod, mem_Ici, mem_Iic,
        mem_singleton_iff, not_or, not_and] at hp'
      simp only [mem_union, mem_setOf_eq]
      rcases lt_trichotomy p.2 0 with h' | h' | h'
      · exact Or.inr h'
      · rcases le_total 0 p.1 with h'' | h''
        · exact absurd h' (hp'.1 h'')
        · exact absurd h' (hp'.2 h'')
      · exact Or.inl h'
    rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_connectedComponentIn _ _
      (isOpen_lt continuous_const continuous_snd) (isOpen_lt continuous_snd continuous_const) hsub
      (by
        ext p; simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨-, h1, h2⟩; linarith) with h' | h'
    · have := h' hy; simp at this; linarith
    · have := h' (mem_connectedComponentIn (by simp [A, B])); simp at this; linarith

/-- **The plane-topology facts used by Bing's proof of Theorem 6, as hypotheses** (weakened to
polygonal sets in batch 129; corrected in
batch 117: `janiszewski` now asks `A`, `B` compact; see `janiszewski_closed_false`).
* `jct`: the Jordan curve theorem for simple closed polygons — the complement has exactly two
  components, one bounded and one unbounded, and the polygon is the frontier of each;
* `enclose`: around a compact continuum `M` that does not separate the plane, inside any open
  `G ⊇ M`, there is a simple closed polygon `J` missing `M` with `M ⊆ polyInterior J ⊆ G`
  (Bing's `W = ℝ² ∖ d_0`, "unbounded continuum which does not intersect `M`, the complement of
  `W` is the interior `d_0` of a simple closed curve and `d_1, …, d_n` covers `d_0`");
* `janiszewski`: if `A`, `B` are polygonal (finite unions of segments and points; batch 129 — until
  batch 128 the field asked `A`, `B` compact), `A ∩ B` is connected or empty, and neither separates
  `x` from `y`, then `A ∪ B` does not separate `x` from `y`. The two uses (`crosscut'`,
  `exists_theta_point`) apply it to polygonal sets; the field is proved as `janiszewski_polygonal`
  (`HPC/Plane/JanPoly.lean`). -/
structure PlaneFacts : Prop where
  jct : ∀ J : Set Pt, IsSimpleClosedPolygon J →
    ∃ U V : Set Pt, IsOpen U ∧ IsOpen V ∧ Jᶜ = U ∪ V ∧ Disjoint U V ∧
      IsConnected U ∧ IsConnected V ∧ Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧
      frontier U = J ∧ frontier V = J
  enclose : ∀ M : Set Pt, Fold.Q78.IsContinuum M → ¬ SeparatesPlane M →
    ∀ G : Set Pt, IsOpen G → M ⊆ G →
      ∃ J : Set Pt, IsSimpleClosedPolygon J ∧ Disjoint J M ∧ M ⊆ polyInterior J ∧
        polyInterior J ⊆ G
  /- The compact form (batches 117–128):
  janiszewski : ∀ A B : Set Pt, IsCompact A → IsCompact B →
    (IsConnected (A ∩ B) ∨ A ∩ B = ∅) →
    ∀ x y : Pt, ¬ SeparatesPts A x y → ¬ SeparatesPts B x y → ¬ SeparatesPts (A ∪ B) x y
  weakened to polygonal sets in batch 129; the two uses are polygonal; the compact form is
  Janiszewski's theorem, not needed. -/
  janiszewski : ∀ A B : Set Pt, IsPolygonal A → IsPolygonal B →
    (IsConnected (A ∩ B) ∨ A ∩ B = ∅) →
    ∀ x y : Pt, ¬ SeparatesPts A x y → ¬ SeparatesPts B x y → ¬ SeparatesPts (A ∪ B) x y

/-- If `Jᶜ = U ∪ V` with `U`, `V` open and disjoint and `U` connected, the component of `Jᶜ`
through a point of `U` is `U`. -/
theorem connectedComponentIn_eq_of_split {J U V : Set Pt} (hU : IsOpen U) (hV : IsOpen V)
    (hJ : Jᶜ = U ∪ V) (hd : Disjoint U V) (hUc : IsConnected U) {x : Pt} (hx : x ∈ U) :
    connectedComponentIn Jᶜ x = U := by
  apply subset_antisymm
  · have hsub : connectedComponentIn Jᶜ x ⊆ U ∪ V := hJ ▸ connectedComponentIn_subset _ _
    rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_connectedComponentIn U V hU hV
      hsub (by rw [hd.inter_eq, inter_empty]) with h | h
    · exact h
    · exact absurd (h (mem_connectedComponentIn (hJ ▸ Or.inl hx))) (hd.notMem_of_mem_left hx)
  · exact hUc.isPreconnected.subset_connectedComponentIn hx (hJ ▸ subset_union_left)

/-- With `U`, `V` as in `jct`, `polyInterior J = U`. -/
theorem polyInterior_eq_of_split {J U V : Set Pt} (hU : IsOpen U) (hV : IsOpen V)
    (hJ : Jᶜ = U ∪ V) (hd : Disjoint U V) (hUc : IsConnected U) (hVc : IsConnected V)
    (hUb : Bornology.IsBounded U) (hVb : ¬ Bornology.IsBounded V) : polyInterior J = U := by
  ext x
  constructor
  · rintro ⟨hxJ, hb⟩
    have : x ∈ U ∪ V := hJ ▸ hxJ
    rcases this with h | h
    · exact h
    · rw [connectedComponentIn_eq_of_split hV hU (by rw [hJ, union_comm]) hd.symm hVc h] at hb
      exact absurd hb hVb
  · intro hx
    refine ⟨fun h => (hJ ▸ Or.inl hx : x ∈ Jᶜ) h, ?_⟩
    rw [connectedComponentIn_eq_of_split hU hV hJ hd hUc hx]
    exact hUb

/-- Under `jct`, `polyInterior J` is the bounded component `U`, and the frontier facts transfer. -/
theorem PlaneFacts.polyInterior_eq (h : PlaneFacts) {J : Set Pt} (hJ : IsSimpleClosedPolygon J) :
    IsOpen (polyInterior J) ∧ IsConnected (polyInterior J) ∧
      Bornology.IsBounded (polyInterior J) ∧ frontier (polyInterior J) = J ∧
      IsConnected (J ∪ polyInterior J)ᶜ := by
  obtain ⟨U, V, hU, hV, hJU, hd, hUc, hVc, hUb, hVb, hfU, -⟩ := h.jct J hJ
  rw [polyInterior_eq_of_split hU hV hJU hd hUc hVc hUb hVb]
  refine ⟨hU, hUc, hUb, hfU, ?_⟩
  rw [compl_union, hJU, union_inter_distrib_right, inter_compl_self, empty_union,
    inter_eq_left.2 hd.symm.subset_compl_right]
  exact hVc

/-! ### The grid cover (Bing, first paragraph of the proof of Theorem 6) -/

/-- A plane set containing no continuum that separates the plane is nowhere dense: a ball inside
it would contain a sphere (in the sup metric, the boundary of a square), a continuum whose
complement is the disjoint union of the open ball and the open exterior. (The hypothesis `hM` of
the skeleton, that `M` is a continuum, is not needed and was dropped.) -/
theorem interior_eq_empty_of_noSeparating {M : Set Pt}
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) : interior M = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hrk : 1 < Module.rank ℝ Pt := by rw [rank_prod']; simp; norm_num
  have hsub : sphere x (r / 2) ⊆ M := fun p hp =>
    interior_subset (hball (sphere_subset_ball (by linarith) hp))
  refine hns _ hsub ⟨isCompact_sphere x _, isConnected_sphere hrk x (by linarith)⟩ ?_
  intro hc
  have hcomp : (sphere x (r / 2))ᶜ ⊆ ball x (r / 2) ∪ (closedBall x (r / 2))ᶜ := by
    intro p hp
    simp only [mem_compl_iff, mem_sphere, mem_ball, mem_closedBall, mem_union, not_le] at hp ⊢
    rcases lt_or_gt_of_ne hp with h | h
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨z, -, hz1, hz2⟩ := hc.isPreconnected _ _ isOpen_ball isClosed_closedBall.isOpen_compl
    hcomp ⟨x, by simp; positivity, mem_ball_self (by linarith)⟩
    ⟨x + (r, r), by
      simp [Prod.norm_def]
      rw [abs_of_pos hr]; intro h; linarith, by
      simp [mem_closedBall, dist_eq_norm, Prod.norm_def]; rw [abs_of_pos hr]; linarith⟩
  exact hz2 (ball_subset_closedBall hz1)

/-- The closed grid square of side `ε` with lower-left corner `o + ε • (a, b)`. -/
def gridSq (o : Pt) (ε : ℝ) (a b : ℤ) : Set Pt :=
  Icc (o.1 + ε * a) (o.1 + ε * (a + 1)) ×ˢ Icc (o.2 + ε * b) (o.2 + ε * (b + 1))

/-- The vertices of the grid with offset `o`. -/
def gridVertices (o : Pt) (ε : ℝ) : Set Pt :=
  {p | ∃ a b : ℤ, p = (o.1 + ε * a, o.2 + ε * b)}

/-- **An offset with no grid vertex on `M`** (Bing: "no point of `M` is on the vertex of any of
the quadrilaterals"). Proof by Baire's theorem rather than the commissioned finite-union argument:
the offsets putting the vertex of index `(a, b)` on `M` form a translate of `M`, closed and nowhere
dense; countably many of them cannot cover the plane. (The skeleton's hypotheses `hb` and `hε`
are not needed and were dropped.) -/
theorem exists_grid_offset {M : Set Pt} (hM : IsClosed M) (hnd : interior M = ∅) (ε : ℝ) :
    ∃ o : Pt, Disjoint (gridVertices o ε) M := by
  by_contra hcon
  push_neg at hcon
  let f : ℤ × ℤ → Set Pt := fun ab =>
    (Homeomorph.addRight ((ε * ab.1, ε * ab.2) : Pt)) ⁻¹' M
  have hcl : ∀ ab, IsClosed (f ab) := fun ab => hM.preimage (Homeomorph.continuous _)
  have hcov : ⋃ ab, f ab = univ := by
    refine eq_univ_of_forall fun o => ?_
    obtain ⟨p, ⟨a, b, rfl⟩, hpM⟩ := not_disjoint_iff.1 (hcon o)
    exact mem_iUnion.2 ⟨(a, b), by simpa [f] using hpM⟩
  obtain ⟨ab, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hcov
  rw [← Homeomorph.preimage_interior, hnd] at hx
  exact hx

/-- The finitely many grid squares meeting `M`, as a finset of index pairs. -/
theorem finite_gridSq_meeting {M : Set Pt} (hb : Bornology.IsBounded M) (o : Pt) {ε : ℝ}
    (hε : 0 < ε) : {ab : ℤ × ℤ | (gridSq o ε ab.1 ab.2 ∩ M).Nonempty}.Finite := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  set N : ℤ := ⌈(R + |o.1| + |o.2|) / ε⌉ + 1
  refine ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)).subset ?_
  rintro ⟨a, b⟩ ⟨p, ⟨⟨h1, h2⟩, h3, h4⟩, hpM⟩
  have hp := hR hpM
  rw [mem_closedBall, dist_zero_right, Prod.norm_def] at hp
  have hx := (le_max_left _ _).trans hp
  have hy := (le_max_right _ _).trans hp
  rw [Real.norm_eq_abs, abs_le] at hx hy
  have ho1 := abs_le.1 (le_refl |o.1|)
  have ho2 := abs_le.1 (le_refl |o.2|)
  have hN : (R + |o.1| + |o.2|) / ε ≤ ⌈(R + |o.1| + |o.2|) / ε⌉ := Int.le_ceil _
  rw [div_le_iff₀ hε] at hN
  have key : ∀ c : ℤ, ε * c ≤ ε * (N - 1) → c ≤ N - 1 := fun c h => by
    have := le_of_mul_le_mul_left h hε; exact_mod_cast this
  simp only [mem_prod, mem_Icc]
  push_cast at h1 h2 h3 h4
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have : -a - 1 ≤ N - 1 := key _ (by push_cast [N]; nlinarith [abs_nonneg o.2])
    omega
  · have : a ≤ N - 1 := key _ (by push_cast [N]; nlinarith [abs_nonneg o.2])
    omega
  · have : -b - 1 ≤ N - 1 := key _ (by push_cast [N]; nlinarith [abs_nonneg o.1])
    omega
  · have : b ≤ N - 1 := key _ (by push_cast [N]; nlinarith [abs_nonneg o.1])
    omega

/-- **The notched enlargement** of a grid square: the open square, together with open strips of
width `η` along its four sides, each strip stopped at distance `r` from the two ends of its side.
(`r > η`; the square's corners and `r`-neighbourhoods of them are not enlarged.) -/
def notched (o : Pt) (ε η r : ℝ) (a b : ℤ) : Set Pt :=
  Ioo (o.1 + ε * a) (o.1 + ε * (a + 1)) ×ˢ Ioo (o.2 + ε * b) (o.2 + ε * (b + 1)) ∪
  Ioo (o.1 + ε * a + r) (o.1 + ε * (a + 1) - r) ×ˢ
    Ioo (o.2 + ε * b - η) (o.2 + ε * (b + 1) + η) ∪
  Ioo (o.1 + ε * a - η) (o.1 + ε * (a + 1) + η) ×ˢ
    Ioo (o.2 + ε * b + r) (o.2 + ε * (b + 1) - r)

theorem isOpen_notched (o : Pt) (ε η r : ℝ) (a b : ℤ) : IsOpen (notched o ε η r a b) :=
  ((isOpen_Ioo.prod isOpen_Ioo).union (isOpen_Ioo.prod isOpen_Ioo)).union
    (isOpen_Ioo.prod isOpen_Ioo)

/-- A notched square lies in the closed box of side `ε + 2η` around its square. -/
theorem notched_subset_box (o : Pt) {ε η r : ℝ} (hη : 0 < η) (hr : 0 < r) (a b : ℤ) :
    notched o ε η r a b ⊆ Icc (o.1 + ε * a - η) (o.1 + ε * (a + 1) + η) ×ˢ
      Icc (o.2 + ε * b - η) (o.2 + ε * (b + 1) + η) := by
  intro p hp
  simp only [notched, mem_union, mem_prod, mem_Ioo, mem_Icc] at hp ⊢
  rcases hp with (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩) | ⟨⟨h1, h2⟩, h3, h4⟩ <;>
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

theorem diam_notched_le (o : Pt) {ε η r : ℝ} (hε : 0 < ε) (hη : 0 < η) (hr : 0 < r)
    (a b : ℤ) : diam (notched o ε η r a b) ≤ ε + 2 * η := by
  refine diam_le_of_forall_dist_le (by linarith) fun p hp q hq => ?_
  have hp' := notched_subset_box o hη hr a b hp
  have hq' := notched_subset_box o hη hr a b hq
  simp only [mem_prod, mem_Icc] at hp' hq'
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  refine max_le (abs_sub_le_iff.2 ⟨?_, ?_⟩) (abs_sub_le_iff.2 ⟨?_, ?_⟩) <;> nlinarith

/- **`M ∩ q̄ ⊆ d` as commissioned — refuted** (`inter_gridSq_subset_notched_false`): with
`r ≤ dist p v` a point of a side at distance exactly `r` from a corner is in no part of the notched
square (the strips are open and stop at distance `r`). Corrected below with `r < dist p v`, which
is what `exists_notched_cover` provides.

theorem inter_gridSq_subset_notched {M : Set Pt} (o : Pt) {ε η r : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hr : 0 < r) (hrε : 2 * r < ε)
    (hfar : ∀ p ∈ M, ∀ v ∈ gridVertices o ε, r ≤ dist p v) (a b : ℤ) :
    M ∩ gridSq o ε a b ⊆ notched o ε η r a b := by
  sorry
-/

/-- **The commissioned `inter_gridSq_subset_notched` is false**: `o = 0`, `ε = 1`, `η = 1/8`,
`r = 1/4`, `M = {(0, 1/4)}`; the point is at distance `≥ 1/4` from every vertex of the unit grid,
lies in the closed unit square, and is in none of the three parts of its notched enlargement. -/
theorem inter_gridSq_subset_notched_false : ¬ ∀ (M : Set Pt) (o : Pt) (ε η r : ℝ),
    0 < ε → 0 < η → 0 < r → 2 * r < ε →
    (∀ p ∈ M, ∀ v ∈ gridVertices o ε, r ≤ dist p v) →
    ∀ a b : ℤ, M ∩ gridSq o ε a b ⊆ notched o ε η r a b := by
  intro h
  have hfar : ∀ p ∈ ({((0 : ℝ), (1 / 4 : ℝ))} : Set Pt), ∀ v ∈ gridVertices 0 1,
      (1 / 4 : ℝ) ≤ dist p v := by
    rintro p rfl v ⟨a, b, rfl⟩
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    refine le_max_of_le_right ?_
    simp only [Prod.snd_zero, one_mul, zero_add]
    rcases lt_trichotomy b 0 with hb | rfl | hb
    · have : (b : ℝ) ≤ -1 := by exact_mod_cast (show b ≤ -1 by omega)
      rw [abs_of_pos (by linarith)]; linarith
    · simp
    · have : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
      rw [abs_of_neg (by linarith)]; linarith
  have := h _ 0 1 (1 / 8) (1 / 4) one_pos (by norm_num) (by norm_num) (by norm_num) hfar 0 0
    ⟨rfl, by simp [gridSq]; norm_num⟩
  simp [notched] at this
  norm_num at this

/-- **`M ∩ q̄ ⊆ d`** (corrected: `r < dist p v`): if `M` keeps distance `> r` from every grid
vertex, every point of `M` in the closed square lies in its notched enlargement. (The skeleton's
`hε`, `hr`, `hrε` are not needed and were dropped.) -/
theorem inter_gridSq_subset_notched {M : Set Pt} (o : Pt) {ε η r : ℝ} (hη : 0 < η)
    (hfar : ∀ p ∈ M, ∀ v ∈ gridVertices o ε, r < dist p v) (a b : ℤ) :
    M ∩ gridSq o ε a b ⊆ notched o ε η r a b := by
  rintro ⟨x, y⟩ ⟨hpM, ⟨h1, h2⟩, h3, h4⟩
  simp only at h1 h2 h3 h4
  have hv : ∀ a' b' : ℤ, r < max |x - (o.1 + ε * a')| |y - (o.2 + ε * b')| := fun a' b' => by
    have := hfar _ hpM _ ⟨a', b', rfl⟩
    rwa [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at this
  have v00 := hv a b
  have v01 := hv a (b + 1)
  have v10 := hv (a + 1) b
  have v11 := hv (a + 1) (b + 1)
  push_cast at v01 v10 v11
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at v00
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at v01
  rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at v10
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at v11
  rw [lt_max_iff] at v00 v01 v10 v11
  have hA : (x = o.1 + ε * a ∨ x = o.1 + ε * (a + 1)) →
      o.2 + ε * b + r < y ∧ y < o.2 + ε * (b + 1) - r := by
    rintro (h | h)
    · constructor
      · rcases v00 with v | v <;> linarith
      · rcases v01 with v | v <;> linarith
    · constructor
      · rcases v10 with v | v <;> linarith
      · rcases v11 with v | v <;> linarith
  have hB : (y = o.2 + ε * b ∨ y = o.2 + ε * (b + 1)) →
      o.1 + ε * a + r < x ∧ x < o.1 + ε * (a + 1) - r := by
    rintro (h | h)
    · constructor
      · rcases v00 with v | v <;> linarith
      · rcases v10 with v | v <;> linarith
    · constructor
      · rcases v01 with v | v <;> linarith
      · rcases v11 with v | v <;> linarith
  simp only [notched, mem_union, mem_prod, mem_Ioo]
  by_cases hx : o.1 + ε * a < x ∧ x < o.1 + ε * (a + 1)
  · by_cases hy : o.2 + ε * b < y ∧ y < o.2 + ε * (b + 1)
    · exact Or.inl (Or.inl ⟨hx, hy⟩)
    · have := hB (by
        rcases h3.lt_or_eq with h3 | h3
        · rcases h4.lt_or_eq with h4 | h4
          · exact absurd ⟨h3, h4⟩ hy
          · exact Or.inr h4
        · exact Or.inl h3.symm)
      exact Or.inl (Or.inr ⟨this, by linarith, by linarith⟩)
  · have := hA (by
      rcases h1.lt_or_eq with h1 | h1
      · rcases h2.lt_or_eq with h2 | h2
        · exact absurd ⟨h1, h2⟩ hx
        · exact Or.inr h2
      · exact Or.inl h1.symm)
    exact Or.inr ⟨⟨by linarith, by linarith⟩, this⟩

/-- Notched squares of diagonal neighbours `(a, b)`, `(a + 1, b + 1)` are disjoint (`η < r`). -/
theorem notched_diag1 (o : Pt) {ε η r : ℝ} (hηr : η < r) (a b : ℤ) :
    notched o ε η r a b ∩ notched o ε η r (a + 1) (b + 1) = ∅ := by
  refine eq_empty_of_forall_notMem fun p ⟨h1, h2⟩ => ?_
  simp only [notched, mem_union, mem_prod, mem_Ioo] at h1 h2
  push_cast at h2
  rcases h1 with (⟨⟨_, _⟩, _, _⟩ | ⟨⟨_, _⟩, _, _⟩) | ⟨⟨_, _⟩, _, _⟩ <;>
  rcases h2 with (⟨⟨_, _⟩, _, _⟩ | ⟨⟨_, _⟩, _, _⟩) | ⟨⟨_, _⟩, _, _⟩ <;> linarith

/-- Notched squares of diagonal neighbours `(a, b + 1)`, `(a + 1, b)` are disjoint (`η < r`). -/
theorem notched_diag2 (o : Pt) {ε η r : ℝ} (hηr : η < r) (a b : ℤ) :
    notched o ε η r a (b + 1) ∩ notched o ε η r (a + 1) b = ∅ := by
  refine eq_empty_of_forall_notMem fun p ⟨h1, h2⟩ => ?_
  simp only [notched, mem_union, mem_prod, mem_Ioo] at h1 h2
  push_cast at h1 h2
  rcases h1 with (⟨⟨_, _⟩, _, _⟩ | ⟨⟨_, _⟩, _, _⟩) | ⟨⟨_, _⟩, _, _⟩ <;>
  rcases h2 with (⟨⟨_, _⟩, _, _⟩ | ⟨⟨_, _⟩, _, _⟩) | ⟨⟨_, _⟩, _, _⟩ <;> linarith

/-- Meeting notched squares have indices at most one apart in each coordinate (`2η < ε`). -/
theorem notched_bound {o : Pt} {ε η r : ℝ} (hε : 0 < ε) (hη : 0 < η) (hr : 0 < r)
    (hηε : 2 * η < ε) {a b a' b' : ℤ}
    {p : Pt} (h1 : p ∈ notched o ε η r a b) (h2 : p ∈ notched o ε η r a' b') :
    a ≤ a' + 1 ∧ b ≤ b' + 1 := by
  simp only [notched, mem_union, mem_prod, mem_Ioo] at h1 h2
  have hx : o.1 + ε * a - η < p.1 ∧ p.1 < o.1 + ε * (a' + 1) + η := by
    constructor
    · rcases h1 with (⟨⟨_, _⟩, _, _⟩ | ⟨⟨_, _⟩, _, _⟩) | ⟨⟨_, _⟩, _, _⟩ <;> linarith
    · rcases h2 with (⟨⟨_, _⟩, _, _⟩ | ⟨⟨_, _⟩, _, _⟩) | ⟨⟨_, _⟩, _, _⟩ <;> linarith
  have hy : o.2 + ε * b - η < p.2 ∧ p.2 < o.2 + ε * (b' + 1) + η := by
    constructor
    · rcases h1 with (⟨⟨_, _⟩, _, _⟩ | ⟨⟨_, _⟩, _, _⟩) | ⟨⟨_, _⟩, _, _⟩ <;> linarith
    · rcases h2 with (⟨⟨_, _⟩, _, _⟩ | ⟨⟨_, _⟩, _, _⟩) | ⟨⟨_, _⟩, _, _⟩ <;> linarith
  have ka : (a : ℝ) < a' + 2 := lt_of_mul_lt_mul_left (by linarith) hε.le
  have kb : (b : ℝ) < b' + 2 := lt_of_mul_lt_mul_left (by linarith) hε.le
  constructor
  · have : a < a' + 2 := by exact_mod_cast ka
    omega
  · have : b < b' + 2 := by exact_mod_cast kb
    omega

/-- Two notched squares meet only if their squares are equal or share a side. -/
theorem notched_adj {o : Pt} {ε η r : ℝ} (hε : 0 < ε) (hη : 0 < η) (hηr : η < r)
    (hηε : 2 * η < ε)
    {a b a' b' : ℤ} {p : Pt} (h1 : p ∈ notched o ε η r a b) (h2 : p ∈ notched o ε η r a' b') :
    (a = a' ∧ b ≤ b' + 1 ∧ b' ≤ b + 1) ∨ (b = b' ∧ a ≤ a' + 1 ∧ a' ≤ a + 1) := by
  have hr : 0 < r := hη.trans hηr
  obtain ⟨k1, k2⟩ := notched_bound hε hη hr hηε h1 h2
  obtain ⟨k3, k4⟩ := notched_bound hε hη hr hηε h2 h1
  by_contra hc
  have hd : (a' = a + 1 ∨ a = a' + 1) ∧ (b' = b + 1 ∨ b = b' + 1) := by omega
  rcases hd with ⟨ha | ha, hb | hb⟩ <;> subst ha <;> subst hb
  · exact (eq_empty_iff_forall_notMem.1 (notched_diag1 o hηr a b)) p ⟨h1, h2⟩
  · exact (eq_empty_iff_forall_notMem.1 (notched_diag2 o hηr a b')) p ⟨h1, h2⟩
  · exact (eq_empty_iff_forall_notMem.1 (notched_diag2 o hηr a' b)) p ⟨h2, h1⟩
  · exact (eq_empty_iff_forall_notMem.1 (notched_diag1 o hηr a' b')) p ⟨h2, h1⟩

/-- **No three notched squares share a point** (`η < r`, `2 r < ε`): two notched squares meet
only if the squares share a side; three distinct squares cannot pairwise share sides. -/
theorem notched_no_triple (o : Pt) {ε η r : ℝ} (hε : 0 < ε) (hη : 0 < η) (hηr : η < r)
    (hrε : 2 * r < ε) {a b a' b' a'' b'' : ℤ}
    (h1 : (a, b) ≠ (a', b')) (h2 : (a', b') ≠ (a'', b'')) (h3 : (a, b) ≠ (a'', b'')) :
    notched o ε η r a b ∩ notched o ε η r a' b' ∩ notched o ε η r a'' b'' = ∅ := by
  refine eq_empty_of_forall_notMem fun p ⟨⟨p1, p2⟩, p3⟩ => ?_
  have hηε : 2 * η < ε := by linarith
  have e12 := notched_adj hε hη hηr hηε p1 p2
  have e23 := notched_adj hε hη hηr hηε p2 p3
  have e13 := notched_adj hε hη hηr hηε p1 p3
  simp only [ne_eq, Prod.mk.injEq, not_and_or] at h1 h2 h3
  omega

/-- The points `c + ε a`, `a ∈ ℤ`, form a closed subset of `ℝ` (`ε ≠ 0`). -/
theorem isClosed_lattice1 (c : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    IsClosed {x : ℝ | ∃ a : ℤ, x = c + ε * a} := by
  have : {x : ℝ | ∃ a : ℤ, x = c + ε * a} = (fun x => (x - c) / ε) ⁻¹' range Int.cast := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, mem_range]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, by field_simp; ring⟩
    · rintro ⟨a, ha⟩; exact ⟨a, by rw [ha]; field_simp; ring⟩
  rw [this]
  exact Int.isClosedEmbedding_coe_real.isClosed_range.preimage (by fun_prop)

theorem isClosed_gridVertices (o : Pt) {ε : ℝ} (hε : ε ≠ 0) : IsClosed (gridVertices o ε) := by
  have : gridVertices o ε = {x : ℝ | ∃ a : ℤ, x = o.1 + ε * a} ×ˢ
      {x : ℝ | ∃ a : ℤ, x = o.2 + ε * a} := by
    ext ⟨x, y⟩
    simp only [gridVertices, mem_setOf_eq, mem_prod, Prod.mk.injEq]
    constructor
    · rintro ⟨a, b, h1, h2⟩; exact ⟨⟨a, h1⟩, b, h2⟩
    · rintro ⟨⟨a, h1⟩, b, h2⟩; exact ⟨a, b, h1, h2⟩
  rw [this]
  exact (isClosed_lattice1 _ hε).prod (isClosed_lattice1 _ hε)

/-- Every point lies in the grid square indexed by the floors of its scaled coordinates. -/
theorem mem_gridSq_floor (o p : Pt) {ε : ℝ} (hε : 0 < ε) :
    p ∈ gridSq o ε ⌊(p.1 - o.1) / ε⌋ ⌊(p.2 - o.2) / ε⌋ := by
  have k1 := Int.floor_le ((p.1 - o.1) / ε)
  have k2 := Int.lt_floor_add_one ((p.1 - o.1) / ε)
  have k3 := Int.floor_le ((p.2 - o.2) / ε)
  have k4 := Int.lt_floor_add_one ((p.2 - o.2) / ε)
  rw [le_div_iff₀ hε] at k1 k3
  rw [div_lt_iff₀ hε] at k2 k4
  simp only [gridSq, mem_prod, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- A nonempty compact set disjoint from a nonempty closed set keeps a positive distance. -/
theorem exists_far {M V : Set Pt} (hM : IsCompact M) (hne : M.Nonempty) (hV : IsClosed V)
    (hVne : V.Nonempty) (hd : Disjoint V M) :
    ∃ r0 > 0, ∀ p ∈ M, ∀ v ∈ V, r0 ≤ dist p v := by
  obtain ⟨p0, hp0, hmin⟩ := hM.exists_isMinOn hne (continuous_infDist_pt V).continuousOn
  exact ⟨infDist p0 V, (hV.notMem_iff_infDist_pos hVne).1 (hd.notMem_of_mem_right hp0),
    fun p hp v hv => (hmin hp).trans (infDist_le_dist_of_mem hv)⟩

/-- **The cover** (Bing: "There is an `ε` collection `d_1, …, d_n` of interiors of simple closed
curves such that `d_i` contains `M · q̄_i` and no point belongs to three of the `d_i`'s"): a finite
family of notched squares, open, of diameter `< ε`, covering `M`, with no triple intersections. The
polygon property of the `d_i` is not stated here (batch 119). Constants: grid side `δ = ε/2`,
`r = min (r₀/2) (δ/4)` with `r₀ > 0` the distance from `M` to the grid vertices, `η = r/2`.
(The skeleton's hypothesis `hb` follows from compactness and was dropped.) -/
theorem exists_notched_cover {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : Finset (Set Pt), (∀ d ∈ D, IsOpen d) ∧ (∀ d ∈ D, diam d < ε) ∧ M ⊆ ⋃ d ∈ D, d ∧
      (∀ d ∈ D, (d ∩ M).Nonempty) ∧
      ∀ d₁ ∈ D, ∀ d₂ ∈ D, ∀ d₃ ∈ D, d₁ ≠ d₂ → d₂ ≠ d₃ → d₁ ≠ d₃ → d₁ ∩ d₂ ∩ d₃ = ∅ := by
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨o, ho⟩ := exists_grid_offset hM.1.isClosed (interior_eq_empty_of_noSeparating hns) δ
  obtain ⟨r0, hr0, hfar0⟩ := exists_far hM.1 hM.2.nonempty (isClosed_gridVertices o hδ0.ne')
    ⟨_, 0, 0, rfl⟩ ho
  set r := min (r0 / 2) (δ / 4) with hr
  have hr0' : 0 < r := lt_min (by positivity) (by positivity)
  have hrr0 : r < r0 := (min_le_left _ _).trans_lt (by linarith)
  have hrδ : 2 * r < δ := by have := min_le_right (r0 / 2) (δ / 4); linarith
  set η := r / 2 with hη
  have hη0 : 0 < η := by positivity
  have hηr : η < r := by linarith
  have hfar : ∀ p ∈ M, ∀ v ∈ gridVertices o δ, r < dist p v := fun p hp v hv =>
    hrr0.trans_le (hfar0 p hp v hv)
  have hS := finite_gridSq_meeting hM.1.isBounded o hδ0
  refine ⟨hS.toFinset.image (fun ab => notched o δ η r ab.1 ab.2), ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨ab, -, rfl⟩ := Finset.mem_image.1 hd
    exact isOpen_notched _ _ _ _ _ _
  · intro d hd
    obtain ⟨ab, -, rfl⟩ := Finset.mem_image.1 hd
    refine (diam_notched_le o hδ0 hη0 hr0' _ _).trans_lt ?_
    have := min_le_right (r0 / 2) (δ / 4)
    linarith
  · intro p hp
    have hsq := mem_gridSq_floor o p hδ0
    refine mem_iUnion₂.2 ⟨_, Finset.mem_image.2 ⟨(⌊(p.1 - o.1) / δ⌋, ⌊(p.2 - o.2) / δ⌋),
      hS.mem_toFinset.2 ⟨p, hsq, hp⟩, rfl⟩, ?_⟩
    exact inter_gridSq_subset_notched o hη0 hfar _ _ ⟨hp, hsq⟩
  · intro d hd
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.1 hd
    obtain ⟨q, hq, hqM⟩ := hS.mem_toFinset.1 hab
    exact ⟨q, inter_gridSq_subset_notched o hη0 hfar _ _ ⟨hqM, hq⟩, hqM⟩
  · intro d₁ h₁ d₂ h₂ d₃ h₃ n12 n23 n13
    obtain ⟨⟨a₁, b₁⟩, -, rfl⟩ := Finset.mem_image.1 h₁
    obtain ⟨⟨a₂, b₂⟩, -, rfl⟩ := Finset.mem_image.1 h₂
    obtain ⟨⟨a₃, b₃⟩, -, rfl⟩ := Finset.mem_image.1 h₃
    exact notched_no_triple o hδ0 hη0 hηr hrδ
      (fun h => n12 (by obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl))
      (fun h => n23 (by obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl))
      (fun h => n13 (by obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl))

/-! ### Two lemmas for batch 118 -/

/-- Components of open subsets of the plane are open (the plane is locally connected). -/
theorem isOpen_connectedComponentIn_of_isOpen {U : Set Pt} (hU : IsOpen U) (x : Pt) :
    IsOpen (connectedComponentIn U x) :=
  hU.connectedComponentIn

/-- A finite open cover of a connected set by sets each meeting it is coherent (a split of the
cover into two subfamilies with no intersections across would split the set). Bing does not argue
the coherence of `H'`; this supplies it. (The skeleton's minimality hypothesis `hmin'` is not
needed and was dropped; `hmin`, every element meets `M`, suffices.) -/
theorem isCoherent_of_minimal_cover {M : Set Pt} (hM : IsConnected M) (G : Finset (Set Pt))
    (hopen : ∀ A ∈ G, IsOpen A) (hcov : M ⊆ ⋃ A ∈ G, A) (hmin : ∀ A ∈ G, (A ∩ M).Nonempty) :
    IsCoherent G := by
  intro G' hG' hne
  by_contra hcon
  push_neg at hcon
  obtain ⟨B, hBG, hBG'⟩ := Finset.exists_of_ssubset hG'
  obtain ⟨A, hA⟩ := hne
  have hU : IsOpen (⋃ C ∈ G', C) := isOpen_biUnion fun C hC => hopen C (hG'.subset hC)
  have hV : IsOpen (⋃ C ∈ G \ G', C) :=
    isOpen_biUnion fun C hC => hopen C (Finset.mem_sdiff.1 hC).1
  have hcov' : M ⊆ (⋃ C ∈ G', C) ∪ ⋃ C ∈ G \ G', C := by
    intro p hp
    obtain ⟨C, hC, hpC⟩ := mem_iUnion₂.1 (hcov hp)
    by_cases h : C ∈ G'
    · exact Or.inl (mem_iUnion₂.2 ⟨C, h, hpC⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨C, Finset.mem_sdiff.2 ⟨hC, h⟩, hpC⟩)
  obtain ⟨p, hpA, hpM⟩ := hmin A (hG'.subset hA)
  obtain ⟨q, hqB, hqM⟩ := hmin B hBG
  obtain ⟨z, -, hzU, hzV⟩ := hM.isPreconnected _ _ hU hV hcov'
    ⟨p, hpM, mem_iUnion₂.2 ⟨A, hA, hpA⟩⟩
    ⟨q, hqM, mem_iUnion₂.2 ⟨B, Finset.mem_sdiff.2 ⟨hBG, hBG'⟩, hqB⟩⟩
  obtain ⟨C, hC, hzC⟩ := mem_iUnion₂.1 hzU
  obtain ⟨D, hD, hzD⟩ := mem_iUnion₂.1 hzV
  exact (eq_empty_iff_forall_notMem.1 (hcon C hC D hD)) z ⟨hzC, hzD⟩

end HPC.Plane
