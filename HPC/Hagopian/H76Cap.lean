import HPC.Hagopian.H76Block3c

/-!
# Batch 181, §2.2 and §3.2: E0/E1 and the cap lemma in a vertical frame

Commission 181 §2.2 (E0, E1) and §3.2 (the cap lemma), in the abstract vertical frame `VFrame`
(batch 178).

* `VFrame.sepIn_of_below_below` (E0/E1, §3.7.2): if `W_J ≺ W_I` and `Y ≺ W_J` while `X` lies above
  `W_I`, then `Cl W_J` separates `x ∈ X` from `y ∈ Y` (S4c, S4d, then the SSL converse).
* `VFrame.property4_step_unless` (E0, E1 in strand terms): when `Cl W_I` separates `y` from `x`
  with `y` below and `x` above, every piece `W_J` is either between `y` and `W_I` (and then separates)
  or not (the case "between" of (β)).
* `VFrame.exists_mem_closure_of_segment` (§3.2.2, abstract cap): a segment from a point below a piece
  `W` to a point above it meets `Cl W`, unless it meets `Cl(B(W)) − O`.
* `VFrame.infDist_lt_of_segment` (§3.2.2): consequently `ρ(a, Cl W) ≤ ρ(a, b)`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane

namespace VFrame

variable {V : VFrame}

/-- A point below `W` is not in the closure of the region above `W` (the sides are disjoint and
`A(W)` is open). -/
theorem notMem_closure_above_of_below {W : Set Pt} (hW : Disjoint (V.below W) (V.above W))
    {a : Pt} (ha : a ∈ V.below W) : a ∉ closure (V.above W) := by
  intro hc
  obtain ⟨Q, hQb, hQ⟩ := mem_closure_iff.1 hc _ isOpen_below ha
  exact disjoint_left.1 hW hQb hQ

/-- **The abstract cap** (commission 181 §3.2.2, first step). Let `a` lie below `W` and `b` above
`W`. A preconnected set `T` containing `a` and `b` that misses `Cl(B(W)) − O` meets `Cl W`.

*Proof:* `T ⊆ B(W) ∪ (Cl B(W))ᶜ` would disconnect `T`; a point of `T` in `Cl B(W) − B(W)` lies in
`O`, and if it were off `Cl W` it would be in `B(W)` (`mem_above_of_mem_closure`). -/
theorem exists_mem_closure_of_preconnected {W T : Set Pt}
    (hW : Disjoint (V.below W) (V.above W)) (hT : IsPreconnected T) {a b : Pt} (haT : a ∈ T)
    (hbT : b ∈ T) (ha : a ∈ V.below W) (hb : b ∈ V.above W)
    (hbad : Disjoint T (closure (V.above W) \ V.O)) : ∃ c ∈ T, c ∈ closure W := by
  by_contra hno
  push_neg at hno
  have hsub : T ⊆ V.above W ∪ (closure (V.above W))ᶜ := by
    intro c hc
    by_cases hcl : c ∈ closure (V.above W)
    · left
      have hcO : c ∈ V.O := by
        by_contra hcO
        exact disjoint_left.1 hbad hc ⟨hcl, hcO⟩
      exact mem_above_of_mem_closure ⟨hcO, hno c hc⟩ hcl
    · exact Or.inr hcl
  obtain ⟨c, -, hc1, hc2⟩ := hT _ _ isOpen_above isClosed_closure.isOpen_compl hsub ⟨b, hbT, hb⟩
    ⟨a, haT, notMem_closure_above_of_below hW ha⟩
  exact hc2 (subset_closure hc1)

/-- **The abstract cap for a segment** (commission 181 §3.2.2): if `a` is below `W`, `b` above
`W`, and the segment `[a, b]` misses `Cl(B(W)) − O`, then `[a, b]` meets `Cl W`. -/
theorem exists_mem_closure_of_segment {W : Set Pt} (hW : Disjoint (V.below W) (V.above W))
    {a b : Pt} (ha : a ∈ V.below W) (hb : b ∈ V.above W)
    (hbad : Disjoint (segment ℝ a b) (closure (V.above W) \ V.O)) :
    ∃ c ∈ segment ℝ a b, c ∈ closure W :=
  exists_mem_closure_of_preconnected hW (convex_segment a b).isPreconnected (left_mem_segment ℝ a b)
    (right_mem_segment ℝ a b) ha hb hbad

/-- A point of the segment `[a, b]` is no farther from `a` than `b` is. -/
theorem dist_le_of_mem_segment {a b c : Pt} (hc : c ∈ segment ℝ a b) : dist a c ≤ dist a b := by
  have h := (convex_closedBall a (dist a b)).segment_subset (mem_closedBall_self dist_nonneg)
    (mem_closedBall.2 (dist_comm b a).le) hc
  rw [mem_closedBall] at h
  rw [dist_comm]
  exact h

/-- **The cap, metric form** (commission 181 §3.2.2): under the hypotheses of
`exists_mem_closure_of_segment`, `ρ(a, Cl W) ≤ ρ(a, b)`; in particular `ρ(a, b) < ε₃` gives
`ρ(a, Cl W) < ε₃`. -/
theorem infDist_le_of_segment {W : Set Pt} (hW : Disjoint (V.below W) (V.above W))
    {a b : Pt} (ha : a ∈ V.below W) (hb : b ∈ V.above W)
    (hbad : Disjoint (segment ℝ a b) (closure (V.above W) \ V.O)) :
    infDist a (closure W) ≤ dist a b := by
  obtain ⟨c, hc, hcW⟩ := exists_mem_closure_of_segment hW ha hb hbad
  exact (infDist_le_dist_of_mem hcW).trans (dist_le_of_mem_segment hc)

/-- A point above `W` is not in the closure of the region below `W`. -/
theorem notMem_closure_below_of_above {W : Set Pt} (hW : Disjoint (V.below W) (V.above W))
    {a : Pt} (ha : a ∈ V.above W) : a ∉ closure (V.below W) := by
  intro hc
  obtain ⟨Q, hQb, hQ⟩ := mem_closure_iff.1 hc _ isOpen_above ha
  exact disjoint_left.1 hW hQ hQb

/-- **The abstract cap, mirror form** (commission 181 §2.2, §3.2.3): `a` above `W`, `b` below `W`,
and a preconnected `T ∋ a, b` missing `Cl(A(W)) − O` meets `Cl W`. -/
theorem exists_mem_closure_of_preconnected_mirror {W T : Set Pt}
    (hW : Disjoint (V.below W) (V.above W)) (hT : IsPreconnected T) {a b : Pt} (haT : a ∈ T)
    (hbT : b ∈ T) (ha : a ∈ V.above W) (hb : b ∈ V.below W)
    (hbad : Disjoint T (closure (V.below W) \ V.O)) : ∃ c ∈ T, c ∈ closure W := by
  by_contra hno
  push_neg at hno
  have hsub : T ⊆ V.below W ∪ (closure (V.below W))ᶜ := by
    intro c hc
    by_cases hcl : c ∈ closure (V.below W)
    · left
      have hcO : c ∈ V.O := by
        by_contra hcO
        exact disjoint_left.1 hbad hc ⟨hcl, hcO⟩
      exact mem_below_of_mem_closure ⟨hcO, hno c hc⟩ hcl
    · exact Or.inr hcl
  obtain ⟨c, -, hc1, hc2⟩ := hT _ _ isOpen_below isClosed_closure.isOpen_compl hsub ⟨b, hbT, hb⟩
    ⟨a, haT, notMem_closure_below_of_above hW ha⟩
  exact hc2 (subset_closure hc1)

/-- **The cap, metric mirror form**: `a` above `W`, `b` below `W`, `[a, b]` missing
`Cl(A(W)) − O` give `ρ(a, Cl W) ≤ ρ(a, b)`. -/
theorem infDist_le_of_segment_mirror {W : Set Pt} (hW : Disjoint (V.below W) (V.above W))
    {a b : Pt} (ha : a ∈ V.above W) (hb : b ∈ V.below W)
    (hbad : Disjoint (segment ℝ a b) (closure (V.below W) \ V.O)) :
    infDist a (closure W) ≤ dist a b := by
  obtain ⟨c, hc, hcW⟩ := exists_mem_closure_of_preconnected_mirror hW
    (convex_segment a b).isPreconnected (left_mem_segment ℝ a b) (right_mem_segment ℝ a b) ha hb
    hbad
  exact (infDist_le_dist_of_mem hcW).trans (dist_le_of_mem_segment hc)

/-! ### E0, E1 (commission 181 §2.2) and the ending of Case 1 (§3.7.2) -/

/-- **Separation by the lower strand** (commission 181 §2.2 second bullet, and §3.7.2): if
`W_J ≺ W_I` (pieces), `y` lies on a set `Y ≺ W_J`, and `x` lies above `W_I`, then
`Cl W_J` separates `x` from `y` in `O` (S4c, S4d, SSL converse). -/
theorem sepIn_of_below_below {WI WJ Y : Set Pt} {x y : Pt} (hWI : V.IsPiece WI)
    (hWJ : V.IsPiece WJ) (hJI : WJ ⊆ V.below WI) (hY : Y ⊆ V.below WJ)
    (hy : y ∈ Y) (hx : x ∈ V.above WI) : SepIn V.O (closure WJ) x y := by
  have hxa : V.above WI ⊆ V.above WJ := above_subset_above hWI hWJ hJI
  exact sepIn_of_between hWJ hY (singleton_subset_iff.2 (hxa hx)) rfl hy

/-- **E0, E1 in strand terms** (commission 181 §2.2; p. 348: "Then `d⁻¹[J]` separates `yᵢ` from
`f(yᵢ)` in `π⁻¹[D]` and `J` has Property 4 unless `yᵢ` is above `d⁻¹[J]`"). Let `W_I` be a piece
with `y ∈ A(W_I)` and `x ∈ B(W_I)` (so `Cl W_I` separates them), and let `y` lie on a piece `Y`.
For a piece `W_J` disjoint from `Y`, with `W_J ≺ W_I`: either `Y ≺ W_J`, and then
`Cl W_J` separates `x` from `y`; or `Y` lies above `W_J` while `y` is below `W_I` ("between",
(β)). -/
theorem property4_step_unless {WI WJ Y : Set Pt} {x y : Pt} (hWI : V.IsPiece WI)
    (hWJ : V.IsPiece WJ) (hY : V.IsPiece Y) (hYJ : Disjoint WJ Y)
    (hJI : WJ ⊆ V.below WI) (hyY : y ∈ Y) (hy : y ∈ V.below WI) (hx : x ∈ V.above WI) :
    SepIn V.O (closure WJ) x y ∨ (Y ⊆ V.above WJ ∧ y ∈ V.below WI) := by
  rcases piece_sides hWJ hY hYJ with h | h
  · exact Or.inl (sepIn_of_below_below hWI hWJ hJI h hyY hx)
  · exact Or.inr ⟨h, hy⟩

/-- **Two points below `W` are joined off `Cl W`** (through the vertical below `Cl W`). -/
theorem joined_of_below {W : Set Pt} {x y : Pt} (hx : x ∈ V.below W) (hy : y ∈ V.below W) :
    ∃ T : Set Pt, IsPreconnected T ∧ T ⊆ V.O \ closure W ∧ x ∈ T ∧ y ∈ T := by
  obtain ⟨S₁, hS₁, hS₁O, hxS₁, P₁, hP₁, v₁, hv₁, hv₁u⟩ := hx
  obtain ⟨S₂, hS₂, hS₂O, hyS₂, P₂, hP₂, v₂, hv₂, hv₂u⟩ := hy
  set T := V.seg (Icc (min v₁ v₂) (max v₁ v₂)) with hT
  have hTc : IsPreconnected T := V.seg_preconnected _ isPreconnected_Icc
  have hTO : T ⊆ V.O \ closure W := by
    rintro P ⟨t, ht, hP⟩
    refine ⟨V.lev_mem P t hP, notMem_closure_of_lev hP fun htW => ?_⟩
    rcases le_total v₁ v₂ with h | h
    · have := hv₂u t htW
      rw [max_eq_right h] at ht
      linarith [ht.2]
    · have := hv₁u t htW
      rw [max_eq_left h] at ht
      linarith [ht.2]
  have hP₁T : P₁ ∈ T := ⟨v₁, ⟨min_le_left _ _, le_max_left _ _⟩, hv₁⟩
  have hP₂T : P₂ ∈ T := ⟨v₂, ⟨min_le_right _ _, le_max_right _ _⟩, hv₂⟩
  refine ⟨S₁ ∪ T ∪ S₂, (hS₁.union P₁ hP₁ hP₁T hTc).union P₂ (Or.inr hP₂T) hP₂ hS₂,
    union_subset (union_subset hS₁O hTO) hS₂O, Or.inl (Or.inl hxS₁), Or.inr hyS₂⟩

/-- **Two points above `W` are joined off `Cl W`** (through the vertical above `Cl W`). -/
theorem joined_of_above {W : Set Pt} {x y : Pt} (hx : x ∈ V.above W) (hy : y ∈ V.above W) :
    ∃ T : Set Pt, IsPreconnected T ∧ T ⊆ V.O \ closure W ∧ x ∈ T ∧ y ∈ T := by
  obtain ⟨S₁, hS₁, hS₁O, hxS₁, P₁, hP₁, v₁, hv₁, hv₁u⟩ := hx
  obtain ⟨S₂, hS₂, hS₂O, hyS₂, P₂, hP₂, v₂, hv₂, hv₂u⟩ := hy
  set T := V.seg (Icc (min v₁ v₂) (max v₁ v₂)) with hT
  have hTc : IsPreconnected T := V.seg_preconnected _ isPreconnected_Icc
  have hTO : T ⊆ V.O \ closure W := by
    rintro P ⟨t, ht, hP⟩
    refine ⟨V.lev_mem P t hP, notMem_closure_of_lev hP fun htW => ?_⟩
    rcases le_total v₁ v₂ with h | h
    · have := hv₁u t htW
      rw [min_eq_left h] at ht
      linarith [ht.1]
    · have := hv₂u t htW
      rw [min_eq_right h] at ht
      linarith [ht.1]
  have hP₁T : P₁ ∈ T := ⟨v₁, ⟨min_le_left _ _, le_max_left _ _⟩, hv₁⟩
  have hP₂T : P₂ ∈ T := ⟨v₂, ⟨min_le_right _ _, le_max_right _ _⟩, hv₂⟩
  refine ⟨S₁ ∪ T ∪ S₂, (hS₁.union P₁ hP₁ hP₁T hTc).union P₂ (Or.inr hP₂T) hP₂ hS₂,
    union_subset (union_subset hS₁O hTO) hS₂O, Or.inl (Or.inl hxS₁), Or.inr hyS₂⟩

/-- **Separation by `Cl W` puts the two points on opposite sides** (E0, ⇒, second half): if `x`, `y`
lie on pieces `X`, `Y` disjoint from the piece `W` and `Cl W` separates them in `O`, then one of
`X`, `Y` is below `W` and the other above. -/
theorem opposite_of_sepIn {W X Y : Set Pt} {x y : Pt} (hW : V.IsPiece W) (hX : V.IsPiece X)
    (hY : V.IsPiece Y) (hWX : Disjoint W X) (hWY : Disjoint W Y) (hx : x ∈ X) (hy : y ∈ Y)
    (hsep : SepIn V.O (closure W) x y) :
    (x ∈ V.below W ∧ y ∈ V.above W) ∨ (x ∈ V.above W ∧ y ∈ V.below W) := by
  rcases piece_sides hW hX hWX with hXb | hXa <;> rcases piece_sides hW hY hWY with hYb | hYa
  · obtain ⟨T, hT, hTO, hxT, hyT⟩ := joined_of_below (hXb hx) (hYb hy)
    exact (hsep.2.2 T hT hTO hxT hyT).elim
  · exact Or.inl ⟨hXb hx, hYa hy⟩
  · exact Or.inr ⟨hXa hx, hYb hy⟩
  · obtain ⟨T, hT, hTO, hxT, hyT⟩ := joined_of_above (hXa hx) (hYa hy)
    exact (hsep.2.2 T hT hTO hxT hyT).elim

end VFrame

end HPC.Hagopian
