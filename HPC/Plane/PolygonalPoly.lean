import HPC.Plane.Tree67

/-!
# Batch 129: polygonality of the sets of `exists_theta_point`

Placed right after `HPC/Plane/Tree67.lean` (it needs `IsSimpleClosedPolygon` and `polyInterior`),
and imported by `HPC/Plane/Tree6.lean` and `HPC/Plane/Tree7Cross.lean`, the two users of the
`janiszewski` field.

* `IsSimpleClosedPolygon.isPolygonal`: a simple closed polygon is polygonal.
* `isSaturated_polyInterior`: `polyInterior Γ` is a union of components of `Γᶜ`.
* `isPolygonal_frontier_inter_closure` (the key lemma of the commission): for simple closed
  polygons `Γ₁`, `Γ₂`, the set `Γ₁ ∩ closure (polyInterior Γ₁ ∩ polyInterior Γ₂)` is polygonal. It
  is the special case of `isPolygonal_inter_closure_inter` (`HPC/Plane/Polygonal.lean`), which
  holds for any two polygonal sets and any saturated `W₁`, `W₂`; no Jordan curve theorem, no
  vertex analysis and no half-disk identification of `polyInterior` are needed.
-/

namespace HPC.Plane

open Set Metric

/-- A closed polygon `polygonOf v` is polygonal. -/
theorem isPolygonal_polygonOf {n : ℕ} (v : Fin n → Pt) : IsPolygonal (polygonOf v) := by
  classical
  refine ⟨Finset.univ.image
    (fun i : Fin n => (v i, v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)), ?_⟩
  rw [Finset.set_biUnion_finset_image]
  simp [polygonOf]

/-- A simple closed polygon is polygonal. -/
theorem IsSimpleClosedPolygon.isPolygonal {J : Set Pt} (hJ : IsSimpleClosedPolygon J) :
    IsPolygonal J := by
  obtain ⟨n, -, v, rfl, -⟩ := hJ
  exact isPolygonal_polygonOf v

/-- `polyInterior Γ` (the union of the bounded components of `Γᶜ`) is saturated. -/
theorem isSaturated_polyInterior (Γ : Set Pt) : IsSaturated Γ (polyInterior Γ) := by
  refine ⟨fun x hx => hx.1, fun S hS hSΓ ⟨x, hxS, hxP⟩ y hy => ⟨hSΓ hy, ?_⟩⟩
  rw [← connectedComponentIn_eq (hS.subset_connectedComponentIn hxS hSΓ hy)]
  exact hxP.2

/-- `Γ₁ ∩ closure (polyInterior Γ₁ ∩ polyInterior Γ₂)` is polygonal for any polygonal `Γ₁`, `Γ₂`. -/
theorem isPolygonal_inter_closure_polyInterior {Γ₁ Γ₂ : Set Pt} (h₁ : IsPolygonal Γ₁)
    (h₂ : IsPolygonal Γ₂) :
    IsPolygonal (Γ₁ ∩ closure (polyInterior Γ₁ ∩ polyInterior Γ₂)) :=
  isPolygonal_inter_closure_inter h₁ h₂ (isSaturated_polyInterior Γ₁) (isSaturated_polyInterior Γ₂)

/-- The intersection of saturated sets is saturated for the union. -/
theorem IsSaturated.inter {Γ Γ' W W' : Set Pt} (h : IsSaturated Γ W) (h' : IsSaturated Γ' W') :
    IsSaturated (Γ ∪ Γ') (W ∩ W') := by
  refine ⟨fun x hx hxΓ => ?_, fun S hS hSΓ ⟨x, hxS, hxW, hxW'⟩ => ?_⟩
  · rcases hxΓ with h1 | h1
    · exact h.1 hx.1 h1
    · exact h'.1 hx.2 h1
  · have h1 : S ⊆ Γᶜ := fun y hy hyΓ => hSΓ hy (Or.inl hyΓ)
    have h2 : S ⊆ Γ'ᶜ := fun y hy hyΓ => hSΓ hy (Or.inr hyΓ)
    exact fun y hy => ⟨h.2 S hS h1 ⟨x, hxS, hxW⟩ hy, h'.2 S hS h2 ⟨x, hxS, hxW'⟩ hy⟩

/-- **The form used by `exists_theta_point`**: for polygonal `Γ`, `Γ₁`, `Γ₂`, the set
`Γ₁ ∩ closure (polyInterior Γ ∩ polyInterior Γ₁ ∩ polyInterior Γ₂)` is polygonal
(`isPolygonal_inter_closure_inter` with `W₁ = polyInterior Γ₁` for `Γ₁` and
`W₂ = polyInterior Γ ∩ polyInterior Γ₂` for `Γ ∪ Γ₂`). -/
theorem isPolygonal_inter_closure_polyInterior₃ {Γ Γ₁ Γ₂ : Set Pt} (h : IsPolygonal Γ)
    (h₁ : IsPolygonal Γ₁) (h₂ : IsPolygonal Γ₂) :
    IsPolygonal (Γ₁ ∩ closure (polyInterior Γ ∩ polyInterior Γ₁ ∩ polyInterior Γ₂)) := by
  have := isPolygonal_inter_closure_inter h₁ (h.union h₂) (isSaturated_polyInterior Γ₁)
    ((isSaturated_polyInterior Γ).inter (isSaturated_polyInterior Γ₂))
  rwa [show polyInterior Γ₁ ∩ (polyInterior Γ ∩ polyInterior Γ₂) =
    polyInterior Γ ∩ polyInterior Γ₁ ∩ polyInterior Γ₂ by
      rw [← inter_assoc, inter_comm (polyInterior Γ₁)]] at this

/-- **The key polygonality lemma** (commission statement). For simple closed polygons `Γ₁`, `Γ₂`
the set `Γ₁ ∩ closure (polyInterior Γ₁ ∩ polyInterior Γ₂)` is polygonal. Proof: the general
`isPolygonal_inter_closure_inter` — per segment `e` of `Γ₁`, between consecutive "special"
parameters (ends of `e` and the ends of `e ∩ σ` for every segment `σ` of `Γ₁` or `Γ₂`) a small ball
about a point of `e` meets `Γ₁ ∪ Γ₂` only on the line of `e`, its two open half-disks are each
inside or outside each interior, and so membership in `closure (h₁ ∩ h₂)` is locally constant along
the open piece of `e`. -/
theorem isPolygonal_frontier_inter_closure {Γ₁ Γ₂ : Set Pt} (h₁ : IsSimpleClosedPolygon Γ₁)
    (h₂ : IsSimpleClosedPolygon Γ₂) :
    IsPolygonal (Γ₁ ∩ closure (polyInterior Γ₁ ∩ polyInterior Γ₂)) :=
  isPolygonal_inter_closure_polyInterior h₁.isPolygonal h₂.isPolygonal

end HPC.Plane
