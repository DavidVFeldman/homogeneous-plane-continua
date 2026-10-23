import HPC.Moore.Sec6Arc

/-!
# Batch 147: two arcs with only their ends in common are cut by any two points

General topology (a Hausdorff space). If `X`, `Y` are arcs from `p` to `q` (`Gen.TArc`) with
`X ∩ Y = {p, q}`, then `(X ∪ Y) − x − y` is not connected for any two distinct points `x`, `y` of
`X ∪ Y`. This is the cut property in Moore's definition of a simple closed curve of elements (1925,
p. 417), used for `isSCCElt_union`.

Proof: if `x`, `y` lie on the same arc, say `x = f s`, `y = f t` with `s < t` for a parametrization
`f` of `X`, then `f '' [s, t]` and `f '' ([0, s] ∪ [t, 1]) ∪ Y` are closed, cover the set and meet it
in disjoint nonempty pieces. Otherwise `x = f s ∈ X − Y` and `y = g t ∈ Y − X`, and the pieces are
`f '' [0, s] ∪ g '' [0, t]` and `f '' [s, 1] ∪ g '' [t, 1]`.
-/

namespace HPC.Moore

open Set Topology

namespace Gen

variable {T : Type*} [TopologicalSpace T]

/-- A set covered by two closed sets, meeting each but not their intersection, is not connected. -/
theorem not_isConnected_of_closed_cover {S F₁ F₂ : Set T} (h₁ : IsClosed F₁) (h₂ : IsClosed F₂)
    (hcov : S ⊆ F₁ ∪ F₂) (hn₁ : (S ∩ F₁).Nonempty) (hn₂ : (S ∩ F₂).Nonempty)
    (hdis : ∀ z ∈ S, z ∈ F₁ → z ∈ F₂ → False) : ¬ IsConnected S := by
  intro h
  obtain ⟨z, hzS, hz1, hz2⟩ := isPreconnected_closed_iff.1 h.2 F₁ F₂ h₁ h₂ hcov hn₁ hn₂
  exact hdis z hzS hz1 hz2

/-- The arc `Y` has a point off the arc `X` when `X ∩ Y = {p, q}`. -/
theorem TArc.exists_mem_not_mem {p q : T} {X Y : Set T} (hY : TArc p q Y)
    (hXY : X ∩ Y = {p, q}) : ∃ z ∈ Y, z ∉ X := by
  obtain ⟨z, hzY, hz⟩ := hY.nonempty_diff
  refine ⟨z, hzY, fun hzX => hz ?_⟩
  rw [← hXY]; exact ⟨hzX, hzY⟩

variable [T2Space T]

/-- Two points on the same arc, in parameter order. -/
theorem cut_same_arc_lt {p q : T} {X Y : Set T} {f : unitInterval → T} (hf : IsEmbedding f)
    (hfX : range f = X) (hf0 : f 0 = p) (hf1 : f 1 = q) (hY : TArc p q Y)
    (hXY : X ∩ Y = {p, q}) {s t : unitInterval} (hst : s < t) :
    ¬ IsConnected ((X ∪ Y) \ {f s, f t}) := by
  have hYc : IsClosed Y := hY.isClosed
  set F₁ : Set T := f '' Icc s t
  set F₂ : Set T := f '' (Icc 0 s ∪ Icc t 1) ∪ Y
  have hF₁ : IsClosed F₁ := (isCompact_Icc.image hf.continuous).isClosed
  have hF₂ : IsClosed F₂ :=
    ((isCompact_Icc.union isCompact_Icc).image hf.continuous).isClosed.union hYc
  refine not_isConnected_of_closed_cover hF₁ hF₂ ?_ ?_ ?_ ?_
  · rintro z ⟨hz | hz, -⟩
    · rw [← hfX] at hz
      obtain ⟨u, rfl⟩ := hz
      by_cases h1 : u ≤ s
      · exact Or.inr (Or.inl ⟨u, Or.inl ⟨unitInterval.nonneg', h1⟩, rfl⟩)
      by_cases h2 : t ≤ u
      · exact Or.inr (Or.inl ⟨u, Or.inr ⟨h2, unitInterval.le_one'⟩, rfl⟩)
      push_neg at h1 h2
      exact Or.inl ⟨u, ⟨h1.le, h2.le⟩, rfl⟩
    · exact Or.inr (Or.inr hz)
  · obtain ⟨m, hsm, hmt⟩ := exists_between hst
    refine ⟨f m, ⟨Or.inl (hfX ▸ mem_range_self m), ?_⟩, ⟨m, ⟨hsm.le, hmt.le⟩, rfl⟩⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun e => hsm.ne' (hf.injective e), fun e => hmt.ne (hf.injective e)⟩
  · obtain ⟨z, hzY, hzX⟩ := hY.exists_mem_not_mem hXY
    refine ⟨z, ⟨Or.inr hzY, ?_⟩, Or.inr hzY⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun e => hzX (e ▸ hfX ▸ mem_range_self s), fun e => hzX (e ▸ hfX ▸ mem_range_self t)⟩
  · rintro z ⟨-, hzst⟩ ⟨u, ⟨hsu, hut⟩, rfl⟩ hz2
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzst
    have hsu' : s < u := lt_of_le_of_ne hsu fun e => hzst.1 (e ▸ rfl)
    have hut' : u < t := lt_of_le_of_ne hut fun e => hzst.2 (e ▸ rfl)
    rcases hz2 with ⟨v, hv, hvu⟩ | hzY
    · have := hf.injective hvu
      subst this
      rcases hv with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h (not_le.2 hsu')
      · exact absurd h (not_le.2 hut')
    · have hmem : f u ∈ X ∩ Y := ⟨hfX ▸ mem_range_self u, hzY⟩
      rw [hXY] at hmem
      rcases hmem with h | h
      · rw [← hf0] at h
        have := hf.injective h; subst this
        exact absurd hsu' (not_lt.2 unitInterval.nonneg')
      · rw [mem_singleton_iff, ← hf1] at h
        have := hf.injective h; subst this
        exact absurd hut' (not_lt.2 unitInterval.le_one')

/-- Two distinct points on the same arc cut `X ∪ Y`. -/
theorem cut_same_arc {p q : T} {X Y : Set T} (hX : TArc p q X) (hY : TArc p q Y)
    (hXY : X ∩ Y = {p, q}) {x y : T} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    ¬ IsConnected ((X ∪ Y) \ {x, y}) := by
  obtain ⟨-, f, hf, hfX, hf0, hf1⟩ := hX
  rw [← hfX] at hx hy
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  rcases lt_or_gt_of_ne (fun e : s = t => hxy (e ▸ rfl)) with h | h
  · exact cut_same_arc_lt hf hfX hf0 hf1 hY hXY h
  · rw [pair_comm]; exact cut_same_arc_lt hf hfX hf0 hf1 hY hXY h

/-- Points on different arcs, off the other arc, cut `X ∪ Y`. -/
theorem cut_diff_arcs {p q : T} {X Y : Set T} (hX : TArc p q X) (hY : TArc p q Y)
    (hXY : X ∩ Y = {p, q}) {x y : T} (hx : x ∈ X) (hxY : x ∉ Y) (hy : y ∈ Y) (hyX : y ∉ X) :
    ¬ IsConnected ((X ∪ Y) \ {x, y}) := by
  obtain ⟨-, f, hf, hfX, hf0, hf1⟩ := hX
  obtain ⟨-, g, hg, hgY, hg0, hg1⟩ := hY
  have hpX : p ∈ X := hfX ▸ hf0 ▸ mem_range_self 0
  have hqX : q ∈ X := hfX ▸ hf1 ▸ mem_range_self 1
  have hpY : p ∈ Y := hgY ▸ hg0 ▸ mem_range_self 0
  have hqY : q ∈ Y := hgY ▸ hg1 ▸ mem_range_self 1
  rw [← hfX] at hx
  rw [← hgY] at hy
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  have hs0 : s ≠ 0 := fun e => hxY (e ▸ hf0 ▸ hpY)
  have hs1 : s ≠ 1 := fun e => hxY (e ▸ hf1 ▸ hqY)
  have ht0 : t ≠ 0 := fun e => hyX (e ▸ hg0 ▸ hpX)
  have ht1 : t ≠ 1 := fun e => hyX (e ▸ hg1 ▸ hqX)
  have hfXY : ∀ u v, f u = g v → (u = 0 ∧ v = 0) ∨ (u = 1 ∧ v = 1) := by
    intro u v huv
    have hmem : f u ∈ X ∩ Y := ⟨hfX ▸ mem_range_self u, huv ▸ hgY ▸ mem_range_self v⟩
    rw [hXY] at hmem
    rcases hmem with h | h
    · left
      exact ⟨hf.injective (h.trans hf0.symm), hg.injective ((huv.symm.trans h).trans hg0.symm)⟩
    · rw [mem_singleton_iff] at h
      right
      exact ⟨hf.injective (h.trans hf1.symm), hg.injective ((huv.symm.trans h).trans hg1.symm)⟩
  set F₁ : Set T := f '' Icc 0 s ∪ g '' Icc 0 t
  set F₂ : Set T := f '' Icc s 1 ∪ g '' Icc t 1
  have hF₁ : IsClosed F₁ := ((isCompact_Icc.image hf.continuous).union
    (isCompact_Icc.image hg.continuous)).isClosed
  have hF₂ : IsClosed F₂ := ((isCompact_Icc.image hf.continuous).union
    (isCompact_Icc.image hg.continuous)).isClosed
  refine not_isConnected_of_closed_cover hF₁ hF₂ ?_ ?_ ?_ ?_
  · rintro z ⟨hz | hz, -⟩
    · rw [← hfX] at hz
      obtain ⟨u, rfl⟩ := hz
      rcases le_total u s with h | h
      · exact Or.inl (Or.inl ⟨u, ⟨unitInterval.nonneg', h⟩, rfl⟩)
      · exact Or.inr (Or.inl ⟨u, ⟨h, unitInterval.le_one'⟩, rfl⟩)
    · rw [← hgY] at hz
      obtain ⟨u, rfl⟩ := hz
      rcases le_total u t with h | h
      · exact Or.inl (Or.inr ⟨u, ⟨unitInterval.nonneg', h⟩, rfl⟩)
      · exact Or.inr (Or.inr ⟨u, ⟨h, unitInterval.le_one'⟩, rfl⟩)
  · refine ⟨p, ⟨Or.inl hpX, ?_⟩, Or.inl ⟨0, ⟨le_rfl, unitInterval.nonneg'⟩, hf0⟩⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun e => hs0 (hf.injective (hf0.trans e)).symm, fun e => hyX (e ▸ hpX)⟩
  · refine ⟨q, ⟨Or.inl hqX, ?_⟩, Or.inl ⟨1, ⟨unitInterval.le_one', le_rfl⟩, hf1⟩⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun e => hs1 (hf.injective (hf1.trans e)).symm, fun e => hyX (e ▸ hqX)⟩
  · rintro z ⟨-, hzst⟩ hz1 hz2
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzst
    have hs0' : 0 < s := lt_of_le_of_ne unitInterval.nonneg' (Ne.symm hs0)
    have hs1' : s < 1 := lt_of_le_of_ne unitInterval.le_one' hs1
    have ht0' : 0 < t := lt_of_le_of_ne unitInterval.nonneg' (Ne.symm ht0)
    have ht1' : t < 1 := lt_of_le_of_ne unitInterval.le_one' ht1
    rcases hz1 with ⟨u, ⟨-, hus⟩, rfl⟩ | ⟨u, ⟨-, hut⟩, rfl⟩ <;>
      rcases hz2 with ⟨v, ⟨hsv, -⟩, hv⟩ | ⟨v, ⟨htv, -⟩, hv⟩
    · have := hf.injective hv; subst this
      exact hzst.1 (by rw [le_antisymm hus hsv])
    · rcases hfXY u v hv.symm with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · exact absurd htv (not_le.2 ht0')
      · exact absurd hus (not_le.2 hs1')
    · rcases hfXY v u hv with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact absurd hsv (not_le.2 hs0')
      · exact absurd hut (not_le.2 ht1')
    · have := hg.injective hv; subst this
      exact hzst.2 (by rw [le_antisymm hut htv])

/-- **Two arcs with only their ends in common are cut by any two of their points.** -/
theorem tscc_cut {p q : T} {X Y : Set T} (hX : TArc p q X) (hY : TArc p q Y)
    (hXY : X ∩ Y = {p, q}) {x y : T} (hx : x ∈ X ∪ Y) (hy : y ∈ X ∪ Y) (hxy : x ≠ y) :
    ¬ IsConnected ((X ∪ Y) \ {x, y}) := by
  have hYX : Y ∩ X = {p, q} := by rw [inter_comm, hXY]
  by_cases hxX : x ∈ X <;> by_cases hyX : y ∈ X
  · exact cut_same_arc hX hY hXY hxX hyX hxy
  · have hyY : y ∈ Y := hy.resolve_left hyX
    by_cases hxY : x ∈ Y
    · rw [union_comm]; exact cut_same_arc hY hX hYX hxY hyY hxy
    · exact cut_diff_arcs hX hY hXY hxX hxY hyY hyX
  · have hxY : x ∈ Y := hx.resolve_left hxX
    by_cases hyY : y ∈ Y
    · rw [union_comm]; exact cut_same_arc hY hX hYX hxY hyY hxy
    · rw [pair_comm]; exact cut_diff_arcs hX hY hXY hyX hyY hxY hxX
  · rw [union_comm]
    exact cut_same_arc hY hX hYX (hx.resolve_left hxX) (hy.resolve_left hyX) hxy

end Gen

end HPC.Moore
