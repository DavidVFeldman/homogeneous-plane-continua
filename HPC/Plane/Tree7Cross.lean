import HPC.Plane.Tree7Arcs
import HPC.Plane.PolygonalPoly

/-!
# Batch 119, auxiliary: the cross-cut theorem

`crosscut'`: a simple polygonal arc `c` from `a` to `b` meeting a simple closed polygon `J` exactly in
its ends, with its interior inside `polyInterior J`, splits `polyInterior J` into the interiors of
the two simple closed polygons `α₁ ∪ c` and `α₂ ∪ c`. The proof uses `jct` (through
`PlaneFacts.split`) and `janiszewski`; it does not need `local_side`: a point of `αᵢ` off `{a, b}`
is in the closure of the exterior `V` of `J`, and `V` lies in the exterior of `αⱼ ∪ c`, so an open
set around it cannot lie in the interior of `αⱼ ∪ c`.
-/

namespace HPC.Plane

open Set Metric

/-- A preconnected set missing `Γ` lies on one side of a split of `Γᶜ`. -/
theorem side_of_split {Γ U V S : Set Pt} (hU : IsOpen U) (hV : IsOpen V) (hJ : Γᶜ = U ∪ V)
    (hd : Disjoint U V) (hS : IsPreconnected S) (hSΓ : Disjoint S Γ) : S ⊆ U ∨ S ⊆ V :=
  isPreconnected_iff_subset_of_disjoint.1 hS U V hU hV (hJ ▸ hSΓ.subset_compl_right)
    (by rw [hd.inter_eq, inter_empty])

theorem PlaneFacts.isCompact_poly (hPF : PlaneFacts) {Γ : Set Pt} (hΓ : IsSimpleClosedPolygon Γ) :
    IsCompact Γ := by
  obtain ⟨-, -, -, -, -, hUb, hfr, -⟩ := hPF.split hΓ
  refine Metric.isCompact_of_isClosed_isBounded (hfr ▸ isClosed_frontier) ?_
  rw [← hfr]; exact hUb.closure.subset frontier_subset_closure

theorem disjoint_polyInterior_self {Γ : Set Pt} : Disjoint (polyInterior Γ) Γ := by
  rw [Set.disjoint_left]; exact fun x hx => hx.1

/-- **The cross-cut theorem** (auxiliary form). -/
theorem PlaneFacts.crosscut' (hPF : PlaneFacts) {J : Set Pt} (hJ : IsSimpleClosedPolygon J)
    {c : Set Pt} {a b : Pt} (hab : a ≠ b) (hc : IsSimplePolyArc c a b)
    (hcJ : c ∩ J = {a, b}) (hcU : c \ {a, b} ⊆ polyInterior J) :
    ∃ α₁ α₂ : Set Pt, IsSimplePolyArc α₁ a b ∧ IsSimplePolyArc α₂ a b ∧ α₁ ∪ α₂ = J ∧
      α₁ ∩ α₂ = {a, b} ∧
      IsSimpleClosedPolygon (α₁ ∪ c) ∧ IsSimpleClosedPolygon (α₂ ∪ c) ∧
      polyInterior J \ c = polyInterior (α₁ ∪ c) ∪ polyInterior (α₂ ∪ c) ∧
      Disjoint (polyInterior (α₁ ∪ c)) (polyInterior (α₂ ∪ c)) ∧
      closure (polyInterior (α₁ ∪ c)) ∩ J = α₁ ∧ closure (polyInterior (α₂ ∪ c)) ∩ J = α₂ := by
  have haJ : a ∈ J := by
    have : a ∈ c ∩ J := by rw [hcJ]; exact Or.inl rfl
    exact this.2
  have hbJ : b ∈ J := by
    have : b ∈ c ∩ J := by rw [hcJ]; exact Or.inr rfl
    exact this.2
  have hac : a ∈ c := hc.left_mem
  have hbc : b ∈ c := hc.right_mem
  obtain ⟨α₁, α₂, h₁, h₂, hU12, hI12⟩ := hJ.split_two' haJ hbJ hab
  -- the two arcs meet `c` only at the ends
  have hαc : ∀ α : Set Pt, IsSimplePolyArc α a b → α ⊆ J → α ∩ c = {a, b} := by
    intro α hα hαJ
    apply subset_antisymm
    · rintro z ⟨hz1, hz2⟩
      rw [← hcJ]; exact ⟨hz2, hαJ hz1⟩
    · rintro z (rfl | rfl)
      · exact ⟨hα.left_mem, hac⟩
      · exact ⟨hα.right_mem, hbc⟩
  have h₁J : α₁ ⊆ J := hU12 ▸ subset_union_left
  have h₂J : α₂ ⊆ J := hU12 ▸ subset_union_right
  have hΓ₁ : IsSimpleClosedPolygon (α₁ ∪ c) := isSimpleClosedPolygon_of_arcs' h₁ hc (hαc α₁ h₁ h₁J)
  have hΓ₂ : IsSimpleClosedPolygon (α₂ ∪ c) := isSimpleClosedPolygon_of_arcs' h₂ hc (hαc α₂ h₂ h₂J)
  -- the splits
  obtain ⟨V, hUo, hVo, hJV, hdUV, hUb, hfrU, hclU, hclV, hVc, hVu⟩ := hPF.split hJ
  set U := polyInterior J with hUdef
  have hUJ : Disjoint U J := disjoint_polyInterior_self
  have hVJ : Disjoint V J := by
    rw [Set.disjoint_left]; intro x hxV hxJ
    have : x ∈ U ∪ V := Or.inr hxV
    rw [← hJV] at this; exact this hxJ
  have hcl : c ⊆ U ∪ J := by
    intro z hz
    by_cases hz' : z ∈ ({a, b} : Set Pt)
    · right; rw [← hcJ] at hz'; exact hz'.2
    · left; exact hcU ⟨hz, hz'⟩
  -- general facts about `Γ = α ∪ c` for `α` one of the two arcs and `β` the other
  have key : ∀ α β : Set Pt, IsSimplePolyArc α a b → IsSimplePolyArc β a b → α ∪ β = J →
      α ∩ β = {a, b} → IsSimpleClosedPolygon (α ∪ c) →
      ∃ W : Set Pt, IsOpen W ∧ (α ∪ c)ᶜ = polyInterior (α ∪ c) ∪ W ∧
        Disjoint (polyInterior (α ∪ c)) W ∧ IsConnected W ∧ V ⊆ W ∧ β \ {a, b} ⊆ W ∧
        polyInterior (α ∪ c) ⊆ U ∧ Disjoint (polyInterior (α ∪ c)) J ∧
        frontier (polyInterior (α ∪ c)) = α ∪ c ∧ (polyInterior (α ∪ c)).Nonempty := by
    intro α β hα hβ hαβU hαβI hΓ
    obtain ⟨W, hU'o, hWo, hJW, hdW, hU'b, hfr', hcl', -, hWc, hWu⟩ := hPF.split hΓ
    have hαJ : α ⊆ J := hαβU ▸ subset_union_left
    have hΓsub : α ∪ c ⊆ U ∪ J := union_subset (hαJ.trans subset_union_right) hcl
    -- `V ⊆ W`
    have hVΓ : Disjoint V (α ∪ c) := by
      rw [Set.disjoint_left]; intro x hxV hxΓ
      rcases hΓsub hxΓ with h | h
      · exact hdUV.notMem_of_mem_left h hxV
      · exact hVJ.notMem_of_mem_left hxV h
    have hVW : V ⊆ W := by
      rcases side_of_split hU'o hWo hJW hdW hVc.isPreconnected hVΓ with h | h
      · exact absurd (hU'b.subset h) hVu
      · exact h
    -- `β \ {a, b} ⊆ W`
    have hS := hβ.isConnected_diff_ends'
    have hSΓ : Disjoint (β \ {a, b}) (α ∪ c) := by
      rw [Set.disjoint_left]; rintro x ⟨hxβ, hxab⟩ hxΓ
      rcases hxΓ with h | h
      · exact hxab (hαβI ▸ ⟨h, hxβ⟩)
      · exact hxab (hcJ ▸ ⟨h, (hαβU ▸ (subset_union_right : β ⊆ α ∪ β)) hxβ⟩)
    have hSW : β \ {a, b} ⊆ W := by
      rcases side_of_split hU'o hWo hJW hdW hS.isPreconnected hSΓ with h | h
      · exfalso
        obtain ⟨w, hw⟩ := hS.nonempty
        have hwJ : w ∈ J := (hαβU ▸ (subset_union_right : β ⊆ α ∪ β)) hw.1
        obtain ⟨y, hyU', hyV⟩ := mem_closure_iff.1 (hclV w hwJ) _ hU'o (h hw)
        exact hdW.notMem_of_mem_left hyU' (hVW hyV)
      · exact h
    -- the interior misses `J`
    have hU'Γ : Disjoint (polyInterior (α ∪ c)) (α ∪ c) := disjoint_polyInterior_self
    have hU'J : Disjoint (polyInterior (α ∪ c)) J := by
      rw [Set.disjoint_left]; intro x hx hxJ
      rw [← hαβU] at hxJ
      rcases hxJ with h | h
      · exact hU'Γ.notMem_of_mem_left hx (Or.inl h)
      · by_cases hxab : x ∈ ({a, b} : Set Pt)
        · rcases hxab with rfl | rfl
          · exact hU'Γ.notMem_of_mem_left hx (Or.inr hac)
          · exact hU'Γ.notMem_of_mem_left hx (Or.inr hbc)
        · exact hdW.notMem_of_mem_left hx (hSW ⟨h, hxab⟩)
    have hne : (polyInterior (α ∪ c)).Nonempty := by
      obtain ⟨y, -, hy⟩ := mem_closure_iff.1 (hcl' a (Or.inr hac)) univ isOpen_univ trivial
      exact ⟨y, hy⟩
    have hU'U : polyInterior (α ∪ c) ⊆ U := by
      rcases side_of_split hUo hVo hJV hdUV (hPF.polyInterior_eq hΓ).2.1.isPreconnected hU'J
        with h | h
      · exact h
      · obtain ⟨y, hy⟩ := hne
        exact absurd (hVW (h hy)) (hdW.notMem_of_mem_left hy)
    exact ⟨W, hWo, hJW, hdW, hWc, hVW, hSW, hU'U, hU'J, hfr', hne⟩
  obtain ⟨W₁, hW₁o, hJW₁, hdW₁, hW₁c, hVW₁, hSW₁, hU₁U, hU₁J, hfr₁, hne₁⟩ :=
    key α₁ α₂ h₁ h₂ hU12 hI12 hΓ₁
  obtain ⟨W₂, hW₂o, hJW₂, hdW₂, hW₂c, hVW₂, hSW₂, hU₂U, hU₂J, hfr₂, hne₂⟩ :=
    key α₂ α₁ h₂ h₁ (by rw [union_comm, hU12]) (by rw [inter_comm, hI12]) hΓ₂
  set U₁ := polyInterior (α₁ ∪ c) with hU₁def
  set U₂ := polyInterior (α₂ ∪ c) with hU₂def
  have hU₁o : IsOpen U₁ := (hPF.polyInterior_eq hΓ₁).1
  have hU₂o : IsOpen U₂ := (hPF.polyInterior_eq hΓ₂).1
  have hU₁Γ : Disjoint U₁ (α₁ ∪ c) := disjoint_polyInterior_self
  have hU₂Γ : Disjoint U₂ (α₂ ∪ c) := disjoint_polyInterior_self
  have hU₁c : Disjoint U₁ c := hU₁Γ.mono_right subset_union_right
  have hU₂c : Disjoint U₂ c := hU₂Γ.mono_right subset_union_right
  -- `U₂` misses `Γ₁`
  have hcross : ∀ (α β Uβ Wβ : Set Pt), Disjoint Uβ (β ∪ c) → α \ {a, b} ⊆ Wβ →
      Disjoint Uβ Wβ → Disjoint Uβ (α ∪ c) := by
    intro α β Uβ Wβ hUβ hαW hdβ
    rw [Set.disjoint_left]; intro x hx hxΓ
    rcases hxΓ with h | h
    · by_cases hxab : x ∈ ({a, b} : Set Pt)
      · rcases hxab with rfl | rfl
        · exact hUβ.notMem_of_mem_left hx (Or.inr hac)
        · exact hUβ.notMem_of_mem_left hx (Or.inr hbc)
      · exact hdβ.notMem_of_mem_left hx (hαW ⟨h, hxab⟩)
    · exact hUβ.notMem_of_mem_left hx (Or.inr h)
  have hU₂Γ₁ : Disjoint U₂ (α₁ ∪ c) := hcross α₁ α₂ U₂ W₂ hU₂Γ hSW₂ hdW₂
  have hU₁Γ₂ : Disjoint U₁ (α₂ ∪ c) := hcross α₂ α₁ U₁ W₁ hU₁Γ hSW₁ hdW₁
  have hdis : Disjoint U₁ U₂ := by
    rcases side_of_split hU₁o hW₁o hJW₁ hdW₁ (hPF.polyInterior_eq hΓ₂).2.1.isPreconnected
      hU₂Γ₁ with h21 | h21
    · rcases side_of_split hU₂o hW₂o hJW₂ hdW₂ (hPF.polyInterior_eq hΓ₁).2.1.isPreconnected
        hU₁Γ₂ with h12 | h12
      · exfalso
        have heq : U₁ = U₂ := subset_antisymm h12 h21
        have hΓeq : α₁ ∪ c = α₂ ∪ c := by rw [← hfr₁, ← hfr₂, heq]
        obtain ⟨w, hw⟩ := h₁.isConnected_diff_ends'.nonempty
        have hw2 : w ∈ α₂ ∪ c := hΓeq ▸ (Or.inl hw.1 : w ∈ α₁ ∪ c)
        have hwW : w ∈ W₂ := hSW₂ hw
        have : w ∈ U₂ ∪ W₂ := Or.inr hwW
        rw [← hJW₂] at this
        exact this hw2
      · exact Set.disjoint_of_subset_left h12 hdW₂.symm
    · exact Set.disjoint_of_subset_right h21 hdW₁
  refine ⟨α₁, α₂, h₁, h₂, hU12, hI12, hΓ₁, hΓ₂, ?_, hdis, ?_, ?_⟩
  · apply subset_antisymm
    · rintro x ⟨hxU, hxc⟩
      obtain ⟨y, hyV⟩ := hVc.nonempty
      have hxJ : x ∉ J := hUJ.notMem_of_mem_left hxU
      have hyJc : y ∉ J ∪ c := by
        rintro (h | h)
        · exact hVJ.notMem_of_mem_left hyV h
        · rcases hcl h with h' | h'
          · exact hdUV.notMem_of_mem_left h' hyV
          · exact hVJ.notMem_of_mem_left hyV h'
      have hunion : (α₁ ∪ c) ∪ (α₂ ∪ c) = J ∪ c := by
        rw [← hU12]; ext z; simp only [mem_union]; tauto
      have hsep : SeparatesPts ((α₁ ∪ c) ∪ (α₂ ∪ c)) x y := by
        rw [hunion]
        refine ⟨fun h => h.elim hxJ hxc, hyJc, fun hy => ?_⟩
        have hK : connectedComponentIn (J ∪ c)ᶜ x ⊆ U := by
          rcases side_of_split hUo hVo hJV hdUV isPreconnected_connectedComponentIn
            (Set.disjoint_left.2 fun z hz hzJ =>
              (connectedComponentIn_subset _ _ hz : z ∉ J ∪ c) (Or.inl hzJ)) with h | h
          · exact h
          · exact absurd (h (mem_connectedComponentIn fun h' => h'.elim hxJ hxc))
              (hdUV.notMem_of_mem_left hxU)
        exact hdUV.notMem_of_mem_left (hK hy) hyV
      have hinter : (α₁ ∪ c) ∩ (α₂ ∪ c) = c := by
        rw [← inter_union_distrib_right, hI12]
        exact union_eq_right.2 (by rintro z (rfl | rfl) <;> assumption)
      have hside : ∀ (α Uα Wα : Set Pt), (α ∪ c)ᶜ = Uα ∪ Wα → IsOpen Wα → IsConnected Wα →
          V ⊆ Wα → SeparatesPts (α ∪ c) x y → x ∈ Uα := by
        intro α Uα Wα hJW hWo hWc hVW hs
        have : x ∈ Uα ∪ Wα := hJW ▸ hs.1
        rcases this with h | h
        · exact h
        · exfalso
          apply hs.2.2
          exact hWc.isPreconnected.subset_connectedComponentIn h (hJW ▸ subset_union_right)
            (hVW hyV)
      by_contra hno
      have hn1 : ¬ SeparatesPts (α₁ ∪ c) x y := fun hs =>
        hno (Or.inl (hside α₁ U₁ W₁ hJW₁ hW₁o hW₁c hVW₁ hs))
      have hn2 : ¬ SeparatesPts (α₂ ∪ c) x y := fun hs =>
        hno (Or.inr (hside α₂ U₂ W₂ hJW₂ hW₂o hW₂c hVW₂ hs))
      exact hPF.janiszewski _ _ hΓ₁.isPolygonal hΓ₂.isPolygonal
        (Or.inl (by rw [hinter]; exact hc.isContinuum.2)) x y hn1 hn2 hsep
    · rintro x (hx | hx)
      · exact ⟨hU₁U hx, hU₁c.notMem_of_mem_left hx⟩
      · exact ⟨hU₂U hx, hU₂c.notMem_of_mem_left hx⟩
  · rw [closure_eq_self_union_frontier, hfr₁, union_inter_distrib_right,
      hU₁J.inter_eq, empty_union, union_inter_distrib_right, hcJ,
      inter_eq_left.2 h₁J]
    exact union_eq_left.2 (by rintro z (rfl | rfl); exacts [h₁.left_mem, h₁.right_mem])
  · rw [closure_eq_self_union_frontier, hfr₂, union_inter_distrib_right,
      hU₂J.inter_eq, empty_union, union_inter_distrib_right, hcJ,
      inter_eq_left.2 h₂J]
    exact union_eq_left.2 (by rintro z (rfl | rfl); exacts [h₂.left_mem, h₂.right_mem])

end HPC.Plane
