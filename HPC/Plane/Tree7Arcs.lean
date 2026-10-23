import HPC.Plane.Tree6

/-!
# Batch 119, auxiliary: arcs of a simple closed polygon

Reversal and concatenation of simple polygonal arcs (set form), the segment as an arc, an arc minus
its ends is connected, and splitting a simple closed polygon at two of its points (`split_two`):
a polygon is first written as an arc plus its closing edge (`twoArcs_base`); then the two split
points are moved one at a time (`TwoArcs.move`), splitting the arc containing the new point and
gluing the other piece to the other arc.
-/

namespace HPC.Plane

open Set Metric

/-- A segment with distinct ends is not contained in a finite set. -/
theorem segment_not_subset_finite {a b : Pt} (hab : a ≠ b) {F : Set Pt} (hF : F.Finite) :
    ¬ segment ℝ a b ⊆ F := by
  intro h
  have hinj : Set.InjOn (fun t : ℝ => a + t • (b - a)) (Icc 0 1) := by
    intro s _ t _ hst
    have hd : b - a ≠ 0 := sub_ne_zero.2 hab.symm
    simp only [add_right_inj] at hst
    exact smul_left_injective ℝ hd hst
  have himg : (fun t : ℝ => a + t • (b - a)) '' Icc 0 1 ⊆ F := by
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
    apply h
    rw [segment_eq_image']
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
  exact (Set.Icc_infinite (show (0 : ℝ) < 1 from one_pos)) (Set.Finite.of_finite_image
    (hF.subset himg) hinj)

theorem vpath_two (v : ℕ → Pt) : vpath v 2 = segment ℝ (v 0) (v 1) := by
  ext x
  simp only [mem_vpath]
  constructor
  · rintro ⟨i, hi, hx⟩
    obtain rfl : i = 0 := by omega
    exact hx
  · intro hx
    exact ⟨0, by omega, hx⟩

/-- A segment with distinct ends is a simple polygonal arc. -/
theorem isSimplePolyArc_segment {x y : Pt} (hxy : x ≠ y) : IsSimplePolyArc (segment ℝ x y) x y := by
  refine isSimplePolyArc_iff.2 ⟨fun i => if i = 0 then x else y, 2, ⟨le_rfl, ?_, ?_, ?_⟩, by simp,
    by simp, by rw [vpath_two]; simp⟩
  · intro i j hij hj
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 1 := by omega
    simpa using hxy
  · intro i hi; omega
  · intro i j hij hj; omega

theorem IsSimplePolyArc.reverse {α : Set Pt} {a b : Pt} (h : IsSimplePolyArc α a b) :
    IsSimplePolyArc α b a := by
  obtain ⟨v, n, hv, rfl, rfl, rfl⟩ := isSimplePolyArc_iff.1 h
  refine isSimplePolyArc_iff.2 ⟨fun i => v (n - 1 - i), n, hv.reverse, by simp, ?_,
    (vpath_reverse v n).symm⟩
  simp only
  rw [show n - 1 - (n - 1) = 0 by omega]

theorem IsSimplePolyArc.concat {α β : Set Pt} {a b c : Pt} (hα : IsSimplePolyArc α a b)
    (hβ : IsSimplePolyArc β b c) (hαβ : α ∩ β = {b}) : IsSimplePolyArc (α ∪ β) a c := by
  obtain ⟨v, n, hv, rfl, hvn, rfl⟩ := isSimplePolyArc_iff.1 hα
  obtain ⟨u, k, hu, hu0, rfl, rfl⟩ := isSimplePolyArc_iff.1 hβ
  have hn := hv.1
  have hk := hu.1
  have hvu : v (n - 1) = u 0 := hvn.trans hu0.symm
  refine isSimplePolyArc_iff.2 ⟨vcat v n u, n + k - 1, hv.concat hu hvu (by rw [hαβ, hu0]),
    by simp [vcat, show 0 < n by omega], ?_, (vpath_vcat (by omega) (by omega) hvu).symm⟩
  simp only [vcat, show ¬ (n + k - 1 - 1 < n) by omega, if_false]
  congr 1
  omega

theorem IsSimplePolyArc.ne {α : Set Pt} {a b : Pt} (h : IsSimplePolyArc α a b) : a ≠ b := by
  obtain ⟨v, n, hv, rfl, rfl, rfl⟩ := isSimplePolyArc_iff.1 h
  exact hv.2.1 0 (n - 1) (by have := hv.1; omega) (by have := hv.1; omega)

theorem IsSimplePolyArc.left_mem {α : Set Pt} {a b : Pt} (h : IsSimplePolyArc α a b) : a ∈ α := by
  obtain ⟨v, n, hv, rfl, rfl, rfl⟩ := isSimplePolyArc_iff.1 h
  exact hv.start_mem

theorem IsSimplePolyArc.right_mem {α : Set Pt} {a b : Pt} (h : IsSimplePolyArc α a b) :
    b ∈ α := by
  obtain ⟨v, n, hv, rfl, rfl, rfl⟩ := isSimplePolyArc_iff.1 h
  exact hv.end_mem

/-- **Joining two simple polygonal arcs** with the same ends, meeting only at the ends. -/
theorem isSimpleClosedPolygon_of_arcs' {α β : Set Pt} {a b : Pt} (hα : IsSimplePolyArc α a b)
    (hβ : IsSimplePolyArc β a b) (hαβ : α ∩ β = {a, b}) : IsSimpleClosedPolygon (α ∪ β) := by
  obtain ⟨v, n, hv, rfl, rfl, rfl⟩ := isSimplePolyArc_iff.1 hα
  obtain ⟨u, k, hu, hu0, hu1, rfl⟩ := isSimplePolyArc_iff.1 hβ.reverse
  have := isSimpleClosedPolygon_of_two_arcs hv hu hu0.symm hu1 (by rw [hαβ, hu0])
  exact this

/-- An arc minus its ends is connected. -/
theorem IsSimplePolyArc.isConnected_diff_ends' {α : Set Pt} {a b : Pt}
    (hα : IsSimplePolyArc α a b) : IsConnected (α \ {a, b}) := by
  obtain ⟨v, n, hv, rfl, rfl, rfl⟩ := isSimplePolyArc_iff.1 hα
  have hn := hv.1
  set S : ℕ → Set Pt := fun i => segment ℝ (v i) (v (i + 1)) \ {v 0, v (n - 1)} with hS
  have hne : ∀ i, i + 1 < n → v i ≠ v (i + 1) := fun i hi => hv.2.1 i (i + 1) (by omega) hi
  have hopen : ∀ i, i + 1 < n → openSegment ℝ (v i) (v (i + 1)) ⊆ S i := by
    intro i hi x hx
    refine ⟨openSegment_subset_segment _ _ _ hx, ?_⟩
    rintro (h | h)
    · subst h
      have := hv.start_mem_seg hi (openSegment_subset_segment _ _ _ hx)
      subst this
      exact hne 0 hi ((left_mem_openSegment_iff).1 hx)
    · have hi' := hv.end_mem_seg hi (h ▸ openSegment_subset_segment _ _ _ hx)
      subst hi'
      rw [show n - 2 + 1 = n - 1 by omega] at hx
      rw [h] at hx
      exact hne (n - 2) (by omega) (by
        rw [show n - 2 + 1 = n - 1 by omega]; exact ((right_mem_openSegment_iff).1 hx))
  have hconn : ∀ i, i + 1 < n → IsConnected (S i) := by
    intro i hi
    have hc : IsConnected (openSegment ℝ (v i) (v (i + 1))) :=
      ⟨⟨(1/2 : ℝ) • v i + (1/2 : ℝ) • v (i + 1), 1/2, 1/2, by norm_num, by norm_num, by norm_num,
        rfl⟩, (convex_openSegment _ _).isPreconnected⟩
    refine hc.subset_closure (hopen i hi) ?_
    rw [closure_openSegment]
    exact diff_subset
  have heq : vpath v n \ {v 0, v (n - 1)} = ⋃ i ∈ Iio (n - 1), S i := by
    ext x
    simp only [mem_diff, mem_vpath, mem_iUnion, mem_Iio, exists_prop, hS]
    constructor
    · rintro ⟨⟨i, hi, hx⟩, hx'⟩
      exact ⟨i, by omega, hx, hx'⟩
    · rintro ⟨i, hi, hx, hx'⟩
      exact ⟨⟨i, by omega, hx⟩, hx'⟩
  rw [heq]
  refine IsConnected.biUnion_of_chain ⟨0, by simp; omega⟩ ordConnected_Iio
    (fun i hi => hconn i (by simp at hi; omega)) ?_
  intro i hi hi'
  simp only [mem_Iio, Order.succ_eq_add_one] at hi hi' ⊢
  refine ⟨v (i + 1), ⟨right_mem_segment _ _ _, ?_⟩, ⟨left_mem_segment _ _ _, ?_⟩⟩ <;>
  · rintro (h | h)
    · exact hv.2.1 0 (i + 1) (by omega) (by omega) h.symm
    · exact hv.2.1 (i + 1) (n - 1) (by omega) (by omega) h

/-- Two arcs from `a` to `b` decomposing `J`, meeting only at the ends. -/
def TwoArcs (J : Set Pt) (a b : Pt) : Prop :=
  ∃ α₁ α₂ : Set Pt, IsSimplePolyArc α₁ a b ∧ IsSimplePolyArc α₂ a b ∧ α₁ ∪ α₂ = J ∧
    α₁ ∩ α₂ = {a, b}

theorem TwoArcs.symm {J : Set Pt} {a b : Pt} (h : TwoArcs J a b) : TwoArcs J b a := by
  obtain ⟨α₁, α₂, h₁, h₂, hU, hI⟩ := h
  exact ⟨α₁, α₂, h₁.reverse, h₂.reverse, hU, by rw [hI, pair_comm]⟩

/-- Moving the second end of a two-arc decomposition to another point of `J`. -/
theorem TwoArcs.move {J : Set Pt} {a b c : Pt} (h : TwoArcs J a b) (hc : c ∈ J) (hca : c ≠ a)
    (hcb : c ≠ b) : TwoArcs J a c := by
  have key : ∀ α₁ α₂ : Set Pt, IsSimplePolyArc α₁ a b → IsSimplePolyArc α₂ a b →
      α₁ ∪ α₂ = J → α₁ ∩ α₂ = {a, b} → c ∈ α₁ → TwoArcs J a c := by
    intro α₁ α₂ h₁ h₂ hU hI hc₁
    obtain ⟨A₁, A₂, hA₁, hA₂, hAU, hAI⟩ := h₁.split hc₁ hca hcb
    have hbA₁ : b ∉ A₁ := by
      intro hb
      have : b ∈ A₁ ∩ A₂ := ⟨hb, hA₂.right_mem⟩
      rw [hAI] at this; exact hcb this.symm
    have haA₂ : a ∉ A₂ := by
      intro ha
      have : a ∈ A₁ ∩ A₂ := ⟨hA₁.left_mem, ha⟩
      rw [hAI] at this; exact hca this.symm
    have hA₁sub : A₁ ⊆ α₁ := hAU ▸ subset_union_left
    have hA₂sub : A₂ ⊆ α₁ := hAU ▸ subset_union_right
    have h2A : α₂ ∩ A₂ = {b} := by
      ext x
      simp only [mem_inter_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hx2, hxA⟩
        have : x ∈ α₁ ∩ α₂ := ⟨hA₂sub hxA, hx2⟩
        rw [hI] at this
        rcases this with rfl | rfl
        · exact absurd hxA haA₂
        · rfl
      · rintro rfl; exact ⟨h₂.right_mem, hA₂.right_mem⟩
    refine ⟨A₁, α₂ ∪ A₂, hA₁, h₂.concat hA₂.reverse h2A, ?_, ?_⟩
    · rw [← hU, ← hAU]; ext x; simp only [mem_union]; tauto
    · ext x
      simp only [mem_inter_iff, mem_union, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hx1, hx2 | hx2⟩
        · have : x ∈ α₁ ∩ α₂ := ⟨hA₁sub hx1, hx2⟩
          rw [hI] at this
          rcases this with rfl | rfl
          · exact Or.inl rfl
          · exact absurd hx1 hbA₁
        · have : x ∈ A₁ ∩ A₂ := ⟨hx1, hx2⟩
          rw [hAI] at this; exact Or.inr this
      · rintro (rfl | rfl)
        · exact ⟨hA₁.left_mem, Or.inl h₂.left_mem⟩
        · exact ⟨hA₁.right_mem, Or.inr hA₂.left_mem⟩
  obtain ⟨α₁, α₂, h₁, h₂, hU, hI⟩ := h
  rw [← hU] at hc
  rcases hc with hc | hc
  · exact key α₁ α₂ h₁ h₂ hU hI hc
  · exact key α₂ α₁ h₂ h₁ (by rw [union_comm, hU]) (by rw [inter_comm, hI]) hc

/-- A simple closed polygon is an arc plus its closing edge. -/
theorem twoArcs_base {J : Set Pt} (hJ : IsSimpleClosedPolygon J) :
    ∃ x y : Pt, x ≠ y ∧ TwoArcs J x y := by
  obtain ⟨n, hn, v, rfl, hinj, hpoly⟩ := hJ
  set w : ℕ → Pt := fun i => if h : i < n then v ⟨i, h⟩ else v ⟨0, by omega⟩ with hwdef
  have hw : ∀ i (h : i < n), w i = v ⟨i, h⟩ := fun i h => by simp [hwdef, h]
  have hwinj : ∀ i j, i < j → j < n → w i ≠ w j := by
    intro i j hij hj he
    rw [hw i (by omega), hw j hj] at he
    have := congrArg Fin.val (hinj he)
    simp at this; omega
  -- the edges
  have hedge : ∀ i (h : i + 1 < n), segment ℝ (v ⟨i, by omega⟩)
      (v ⟨((⟨i, by omega⟩ : Fin n).val + 1) % n, Nat.mod_lt _ (by omega)⟩) =
      segment ℝ (w i) (w (i + 1)) := by
    intro i h
    rw [hw i (by omega), hw (i + 1) h]
    congr 2
    exact Fin.ext (Nat.mod_eq_of_lt h)
  have hlast : segment ℝ (v ⟨n - 1, by omega⟩)
      (v ⟨((⟨n - 1, by omega⟩ : Fin n).val + 1) % n, Nat.mod_lt _ (by omega)⟩) =
      segment ℝ (w 0) (w (n - 1)) := by
    rw [segment_symm, hw 0 (by omega), hw (n - 1) (by omega)]
    congr 2
    exact Fin.ext (by simp [show n - 1 + 1 = n by omega])
  have hfin : ∀ (a b c d : Pt), a ≠ b → segment ℝ a b ⊆ segment ℝ c d →
      segment ℝ a b ∩ segment ℝ c d ⊆ ({a, b, d} : Set Pt) → False := by
    intro a b c d hab hsub hint
    refine segment_not_subset_finite hab (F := {a, b, d}) (by simp) ?_
    intro z hz
    exact hint ⟨hz, hsub hz⟩
  have hne1 : ∀ i, i + 1 < n → w i ≠ w (i + 1) := fun i hi => hwinj i (i + 1) (by omega) hi
  have hsarc : IsSArc w n := by
    refine ⟨by omega, hwinj, ?_, ?_⟩
    · intro i hi z hz
      have h := (hpoly ⟨i, by omega⟩ ⟨i + 1, by omega⟩
        (by simp [Fin.ext_iff])).1 (Or.inl (by simp [Nat.mod_eq_of_lt (show i + 1 < n by omega)]))
      rw [hedge i (by omega)] at h
      have e2 : segment ℝ (v ⟨i + 1, by omega⟩) (v ⟨((⟨i + 1, by omega⟩ : Fin n).val + 1) % n,
          Nat.mod_lt _ (by omega)⟩) = segment ℝ (w (i + 1)) (w (i + 1 + 1)) := hedge (i + 1) hi
      rw [e2] at h
      have e3 : v ⟨((⟨i, by omega⟩ : Fin n).val + 1) % n, Nat.mod_lt _ (by omega)⟩ =
          w (i + 1) := by
        rw [hw (i + 1) (by omega)]; congr 1
        exact Fin.ext (by simp only; exact Nat.mod_eq_of_lt (by omega))
      rw [e3, ← hw i (by omega), ← hw (i + 1) (by omega)] at h
      rcases h hz with h1 | h1 | h1
      · exfalso
        subst h1
        refine hfin (w i) (w (i + 1)) (w (i + 1)) (w (i + 1 + 1)) (hne1 i (by omega)) ?_ ?_
        · exact (convex_segment _ _).segment_subset hz.2 (left_mem_segment _ _ _)
        · intro u hu
          rcases h hu with h2 | h2 | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inl h2)
      · exact h1
      · exact h1
    · intro i j hij hj
      have h := (hpoly ⟨i, by omega⟩ ⟨j, by omega⟩ (by
        intro h; simp only [Fin.ext_iff] at h; omega)).2 (by
        simp only
        rw [Nat.mod_eq_of_lt (show i + 1 < n by omega), Nat.mod_eq_of_lt (show j + 1 < n by omega)]
        omega)
      rwa [hedge i (by omega), hedge j hj] at h
  refine ⟨w 0, w (n - 1), hwinj 0 (n - 1) (by omega) (by omega), vpath w n,
    segment ℝ (w 0) (w (n - 1)), isSimplePolyArc_iff.2 ⟨w, n, hsarc, rfl, rfl, rfl⟩,
    isSimplePolyArc_segment (hwinj 0 (n - 1) (by omega) (by omega)), ?_, ?_⟩
  · ext z
    simp only [mem_union, mem_vpath, polygonOf, mem_iUnion]
    constructor
    · rintro (⟨i, hi, hz⟩ | hz)
      · exact ⟨⟨i, by omega⟩, by rw [hedge i hi]; exact hz⟩
      · exact ⟨⟨n - 1, by omega⟩, by rw [hlast]; exact hz⟩
    · rintro ⟨i, hz⟩
      by_cases hi : i.val + 1 < n
      · left
        refine ⟨i.val, hi, ?_⟩
        rw [← hedge i.val hi]; exact hz
      · right
        have : i = ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [this] at hz
        rw [← hlast]; exact hz
  · apply subset_antisymm
    · rintro z ⟨hzP, hzE⟩
      obtain ⟨i, hi, hz⟩ := mem_vpath.1 hzP
      have hIL : (⟨i, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by simp [Fin.ext_iff]; omega
      have h := hpoly ⟨i, by omega⟩ ⟨n - 1, by omega⟩ hIL
      rw [hedge i hi, hlast] at h
      by_cases hi0 : i = 0
      · subst hi0
        have h1 := h.1 (Or.inr (by simp [show n - 1 + 1 = n by omega]))
        have e3 : v ⟨((⟨0, by omega⟩ : Fin n).val + 1) % n, Nat.mod_lt _ (by omega)⟩ = w 1 := by
          rw [hw 1 (by omega)]; congr 1
          exact Fin.ext (by simp only; exact Nat.mod_eq_of_lt (by omega))
        rw [e3, ← hw 0 (by omega), ← hw (n - 1) (by omega)] at h1
        rcases h1 ⟨hz, hzE⟩ with h2 | h2 | h2
        · exact Or.inl h2
        · exact Or.inr h2
        · exfalso
          subst h2
          refine segment_not_subset_finite (hne1 0 (by omega)) (F := {w 0, w (n - 1), w (0 + 1)})
            (by simp) fun u hu => h1 ⟨hu, ?_⟩
          exact (convex_segment _ _).segment_subset (left_mem_segment _ _ _) hzE hu
      by_cases hin : i = n - 2
      · subst hin
        have h1 := h.1 (Or.inl (by simp [Nat.mod_eq_of_lt (show n - 2 + 1 < n by omega)]; omega))
        have e3 : v ⟨((⟨n - 2, by omega⟩ : Fin n).val + 1) % n, Nat.mod_lt _ (by omega)⟩ =
            w (n - 1) := by
          rw [hw (n - 1) (by omega)]; congr 1
          exact Fin.ext (by simp [Nat.mod_eq_of_lt (show n - 2 + 1 < n by omega)]; omega)
        rw [e3, ← hw (n - 2) (by omega), ← hw (n - 1) (by omega)] at h1
        rcases h1 ⟨hz, hzE⟩ with h2 | h2 | h2
        · exfalso
          subst h2
          have hw1 : w (n - 2 + 1) = w (n - 1) := by rw [show n - 2 + 1 = n - 1 by omega]
          refine segment_not_subset_finite (hne1 (n - 2) (by omega))
            (F := {w (n - 2), w (n - 1), w (n - 1)}) (by simp) fun u hu => h1 ⟨hu, ?_⟩
          rw [hw1] at hu
          exact (convex_segment _ _).segment_subset hzE (right_mem_segment _ _ _) hu
        · exact Or.inr h2
        · exact Or.inr h2
      · exfalso
        have h2 := h.2 (by
          simp only
          rw [Nat.mod_eq_of_lt (show i + 1 < n by omega), show n - 1 + 1 = n by omega,
            Nat.mod_self]
          omega)
        exact h2.notMem_of_mem_left hz hzE
    · rintro z (rfl | rfl)
      · exact ⟨hsarc.start_mem, left_mem_segment _ _ _⟩
      · exact ⟨hsarc.end_mem, right_mem_segment _ _ _⟩

/-- **Splitting a simple closed polygon at two of its points.** -/
theorem IsSimpleClosedPolygon.split_two' {J : Set Pt} (hJ : IsSimpleClosedPolygon J) {a b : Pt}
    (ha : a ∈ J) (hb : b ∈ J) (hab : a ≠ b) : TwoArcs J a b := by
  obtain ⟨x, y, hxy, h⟩ := twoArcs_base hJ
  -- first make `a` an end
  have hA : ∃ z, z ≠ a ∧ TwoArcs J a z := by
    by_cases hax : a = x
    · subst hax; exact ⟨y, hxy.symm, h⟩
    by_cases hay : a = y
    · subst hay; exact ⟨x, hxy, h.symm⟩
    exact ⟨x, fun h' => hax h'.symm, (h.move ha hax hay).symm⟩
  obtain ⟨z, hza, hz⟩ := hA
  by_cases hbz : b = z
  · subst hbz; exact hz
  · exact hz.move hb hab.symm hbz

end HPC.Plane
