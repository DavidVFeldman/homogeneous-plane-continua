import Mathlib

/-!
# Batch 194, §3 core: a common subdivision of finitely many segments

For a finite family `T` of nondegenerate segments of a real normed space and a finite set `P` of
points, there is a finite family `S` of nondegenerate segments, two different ones meeting at most
in common endpoints, such that every segment of `T` is the union of the pieces of `S` it
contains, every piece lies in a segment of `T`, and every point of `P` lying on `⋃ T` is an
endpoint of a piece (`exists_common_subdivision`). This is commission 194, §3.1, in the form that
§3.0 (refinement) needs.

The cut points `cutV T P` are the endpoints of the segments of `T`, the points of `P`, and the
two ends of every pairwise intersection (computed along the first segment of the pair as the
`sInf`/`sSup` of the parameter interval `cutI`). A *piece* is a segment between two cut points,
inside a segment of `T`, whose open segment contains no cut point; each piece is kept with one
orientation, chosen by a well-ordering of `E`.
-/

namespace HPC.HO16.Subdiv

open Set

/-- One-dimensional core of the cross lemma. -/
theorem real_cross {ν ν' ξ α β : ℝ} (hne : ν ≠ ν') (hξ : ξ ∈ openSegment ℝ ν ν') (hα : α ≤ ξ)
    (hβ : ξ ≤ β) (hαn : α ∉ openSegment ℝ ν ν') (hβn : β ∉ openSegment ℝ ν ν') :
    uIcc ν ν' ⊆ Icc α β := by
  rw [openSegment_eq_Ioo' hne] at hξ hαn hβn
  simp only [mem_Ioo, not_and_or, not_lt] at hξ hαn hβn
  intro u hu
  rw [mem_uIcc] at hu
  rcases le_total ν ν' with h | h <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h] at hξ hαn hβn <;>
    rcases hαn with h1 | h1 <;> rcases hβn with h2 | h2 <;> rcases hu with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    exact ⟨by linarith, by linarith⟩

/-- One-dimensional core of the same-line lemma. -/
theorem real_same {ν ν' μ μ' ξ : ℝ} (hne : ν ≠ ν') (hξ : ξ ∈ openSegment ℝ ν ν')
    (hξ' : ξ ∈ uIcc μ μ') (hμμ : μ ≠ μ')
    (h1 : μ ∉ openSegment ℝ ν ν') (h2 : μ' ∉ openSegment ℝ ν ν')
    (h3 : ν ∉ openSegment ℝ μ μ') (h4 : ν' ∉ openSegment ℝ μ μ') :
    (μ = ν ∧ μ' = ν') ∨ (μ = ν' ∧ μ' = ν) := by
  rw [openSegment_eq_Ioo' hne] at hξ h1 h2
  rw [openSegment_eq_Ioo' hμμ] at h3 h4
  rw [mem_uIcc] at hξ'
  simp only [mem_Ioo, not_and_or, not_lt] at hξ h1 h2 h3 h4
  rcases le_total ν ν' with h | h <;> rcases le_total μ μ' with h' | h' <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h, h'] at hξ h1 h2 h3 h4 <;>
    rcases hξ with ⟨a1, a2⟩ <;>
    rcases h1 with b | b <;> rcases h2 with c | c <;> rcases h3 with d | d <;>
    rcases h4 with e | e <;>
    rcases hξ' with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;>
    first | (exfalso; linarith) | (left; constructor <;> linarith) |
      (right; constructor <;> linarith)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_segment_iff_lineMap {a b x : E} :
    x ∈ segment ℝ a b ↔ ∃ u ∈ Icc (0 : ℝ) 1, AffineMap.lineMap a b u = x := by
  rw [segment_eq_image_lineMap]; rfl

theorem segment_lineMap (a b : E) (u v : ℝ) :
    segment ℝ (AffineMap.lineMap a b u) (AffineMap.lineMap a b v) =
      AffineMap.lineMap a b '' uIcc u v := by
  rw [← segment_eq_uIcc, image_segment]

theorem openSegment_lineMap (a b : E) (u v : ℝ) :
    openSegment ℝ (AffineMap.lineMap a b u) (AffineMap.lineMap a b v) =
      AffineMap.lineMap a b '' openSegment ℝ u v := by
  rw [image_openSegment]

theorem isClosed_segment' (a b : E) : IsClosed (segment ℝ a b) := by
  rw [segment_eq_image_lineMap]
  exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed

theorem isCompact_segment' (a b : E) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

/-- The parameters along `t` of the points of `t ∩ t'`. -/
def cutI (t t' : E × E) : Set ℝ :=
  Icc 0 1 ∩ AffineMap.lineMap t.1 t.2 ⁻¹' segment ℝ t'.1 t'.2

theorem cutI_interval {t t' : E × E} {u : ℝ} (hu : u ∈ cutI t t') :
    sInf (cutI t t') ≤ u ∧ u ≤ sSup (cutI t t') ∧
      Icc (sInf (cutI t t')) (sSup (cutI t t')) ⊆ cutI t t' := by
  have hcl : IsClosed (cutI t t') :=
    isClosed_Icc.inter ((isClosed_segment' _ _).preimage AffineMap.lineMap_continuous)
  have hcv : Convex ℝ (cutI t t') :=
    (convex_Icc 0 1).inter ((convex_segment _ _).affine_preimage _)
  have hbb : BddBelow (cutI t t') := ⟨0, fun x hx => hx.1.1⟩
  have hba : BddAbove (cutI t t') := ⟨1, fun x hx => hx.1.2⟩
  have hne : (cutI t t').Nonempty := ⟨u, hu⟩
  refine ⟨csInf_le hbb hu, le_csSup hba hu, ?_⟩
  have h1 := hcl.csInf_mem hne hbb
  have h2 := hcl.csSup_mem hne hba
  intro x hx
  apply hcv.segment_subset h1 h2
  rw [segment_eq_Icc (hx.1.trans hx.2)]; exact hx

open Classical in
/-- The cut points. -/
noncomputable def cutV (T : Finset (E × E)) (P : Finset E) : Finset E :=
  T.image Prod.fst ∪ T.image Prod.snd ∪ P ∪
    (T ×ˢ T).image (fun q => AffineMap.lineMap q.1.1 q.1.2 (sInf (cutI q.1 q.2))) ∪
    (T ×ˢ T).image (fun q => AffineMap.lineMap q.1.1 q.1.2 (sSup (cutI q.1 q.2)))

section CutV

variable {T : Finset (E × E)} {P : Finset E}

theorem mem_cutV_fst {t : E × E} (ht : t ∈ T) : t.1 ∈ cutV T P := by
  classical
  unfold cutV
  simp only [Finset.mem_union, Finset.mem_image]
  exact Or.inl (Or.inl (Or.inl (Or.inl ⟨t, ht, rfl⟩)))

theorem mem_cutV_snd {t : E × E} (ht : t ∈ T) : t.2 ∈ cutV T P := by
  classical
  unfold cutV
  simp only [Finset.mem_union, Finset.mem_image]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨t, ht, rfl⟩)))

theorem mem_cutV_of_mem {p : E} (hp : p ∈ P) : p ∈ cutV T P := by
  classical
  unfold cutV
  simp only [Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr hp))

theorem mem_cutV_sInf {t t' : E × E} (ht : t ∈ T) (ht' : t' ∈ T) :
    AffineMap.lineMap t.1 t.2 (sInf (cutI t t')) ∈ cutV T P := by
  classical
  unfold cutV
  simp only [Finset.mem_union, Finset.mem_image]
  exact Or.inl (Or.inr ⟨(t, t'), Finset.mem_product.2 ⟨ht, ht'⟩, rfl⟩)

theorem mem_cutV_sSup {t t' : E × E} (ht : t ∈ T) (ht' : t' ∈ T) :
    AffineMap.lineMap t.1 t.2 (sSup (cutI t t')) ∈ cutV T P := by
  classical
  unfold cutV
  simp only [Finset.mem_union, Finset.mem_image]
  exact Or.inr ⟨(t, t'), Finset.mem_product.2 ⟨ht, ht'⟩, rfl⟩

end CutV

/-- A piece: a segment between two cut points, inside a segment of `T`, whose open segment
contains no cut point. -/
def IsPiece (T : Finset (E × E)) (V : Finset E) (q : E × E) : Prop :=
  q.1 ∈ V ∧ q.2 ∈ V ∧ q.1 ≠ q.2 ∧ (∃ t ∈ T, segment ℝ q.1 q.2 ⊆ segment ℝ t.1 t.2) ∧
    ∀ v ∈ V, v ∉ openSegment ℝ q.1 q.2

theorem IsPiece.swap {T : Finset (E × E)} {V : Finset E} {q : E × E} (h : IsPiece T V q) :
    IsPiece T V q.swap := by
  obtain ⟨h1, h2, h3, ⟨t, ht, hst⟩, h5⟩ := h
  refine ⟨h2, h1, h3.symm, ⟨t, ht, ?_⟩, ?_⟩
  · simpa [segment_symm] using hst
  · intro v hv; simpa [openSegment_symm] using h5 v hv

section Pieces

variable {T : Finset (E × E)} {P : Finset E}

/-- **Cross lemma**: a piece in `t` sharing an inner point with `t'` lies in `t'`. -/
theorem piece_cross {q t t' : E × E} (ht : t ∈ T) (ht' : t' ∈ T)
    (htne : t.1 ≠ t.2) (hq : IsPiece T (cutV T P) q)
    (hqt : segment ℝ q.1 q.2 ⊆ segment ℝ t.1 t.2)
    {x : E} (hx : x ∈ openSegment ℝ q.1 q.2) (hx' : x ∈ segment ℝ t'.1 t'.2) :
    segment ℝ q.1 q.2 ⊆ segment ℝ t'.1 t'.2 := by
  obtain ⟨ν, hν, h1⟩ := (mem_segment_iff_lineMap).1 (hqt (left_mem_segment ℝ q.1 q.2))
  obtain ⟨ν', hν', h2⟩ := (mem_segment_iff_lineMap).1 (hqt (right_mem_segment ℝ q.1 q.2))
  have hinj : Function.Injective (AffineMap.lineMap t.1 t.2 : ℝ → E) :=
    AffineMap.lineMap_injective ℝ htne
  rw [← h1, ← h2, openSegment_lineMap] at hx
  obtain ⟨ξ, hξ, rfl⟩ := hx
  have hνν : ν ≠ ν' := by rintro rfl; exact hq.2.2.1 (h1.symm.trans h2)
  have hξI : ξ ∈ cutI t t' := by
    refine ⟨?_, hx'⟩
    have : openSegment ℝ ν ν' ⊆ Icc 0 1 :=
      (openSegment_subset_segment ℝ _ _).trans ((convex_Icc 0 1).segment_subset hν hν')
    exact this hξ
  obtain ⟨hα, hβ, hI⟩ := cutI_interval hξI
  have hαn : sInf (cutI t t') ∉ openSegment ℝ ν ν' := by
    intro h
    apply hq.2.2.2.2 _ (mem_cutV_sInf ht ht')
    rw [← h1, ← h2, openSegment_lineMap]; exact mem_image_of_mem _ h
  have hβn : sSup (cutI t t') ∉ openSegment ℝ ν ν' := by
    intro h
    apply hq.2.2.2.2 _ (mem_cutV_sSup ht ht')
    rw [← h1, ← h2, openSegment_lineMap]; exact mem_image_of_mem _ h
  have key := real_cross hνν hξ hα hβ hαn hβn
  rw [← h1, ← h2, segment_lineMap]
  rintro _ ⟨u, hu, rfl⟩
  exact (hI (key hu)).2

/-- **Same-line lemma**: two pieces in the same segment sharing a point inner to the first are
the same up to orientation. -/
theorem piece_same {V : Finset E} {q q' t : E × E} (htne : t.1 ≠ t.2) (hq : IsPiece T V q)
    (hq' : IsPiece T V q') (hqt : segment ℝ q.1 q.2 ⊆ segment ℝ t.1 t.2)
    (hq't : segment ℝ q'.1 q'.2 ⊆ segment ℝ t.1 t.2) {x : E}
    (hx : x ∈ openSegment ℝ q.1 q.2) (hx' : x ∈ segment ℝ q'.1 q'.2) :
    q' = q ∨ q' = q.swap := by
  obtain ⟨ν, -, h1⟩ := (mem_segment_iff_lineMap).1 (hqt (left_mem_segment ℝ q.1 q.2))
  obtain ⟨ν', -, h2⟩ := (mem_segment_iff_lineMap).1 (hqt (right_mem_segment ℝ q.1 q.2))
  obtain ⟨μ, -, h3⟩ := (mem_segment_iff_lineMap).1 (hq't (left_mem_segment ℝ q'.1 q'.2))
  obtain ⟨μ', -, h4⟩ := (mem_segment_iff_lineMap).1 (hq't (right_mem_segment ℝ q'.1 q'.2))
  have hinj : Function.Injective (AffineMap.lineMap t.1 t.2 : ℝ → E) :=
    AffineMap.lineMap_injective ℝ htne
  have hνν : ν ≠ ν' := by rintro rfl; exact hq.2.2.1 (h1.symm.trans h2)
  have hμμ : μ ≠ μ' := by rintro rfl; exact hq'.2.2.1 (h3.symm.trans h4)
  rw [← h1, ← h2, openSegment_lineMap] at hx
  obtain ⟨ξ, hξ, rfl⟩ := hx
  rw [← h3, ← h4, segment_lineMap] at hx'
  obtain ⟨ζ, hζ, hζe⟩ := hx'
  rw [hinj hζe] at hζ
  have n1 : μ ∉ openSegment ℝ ν ν' := by
    intro h; apply hq.2.2.2.2 _ hq'.1
    rw [← h1, ← h2, openSegment_lineMap, ← h3]; exact mem_image_of_mem _ h
  have n2 : μ' ∉ openSegment ℝ ν ν' := by
    intro h; apply hq.2.2.2.2 _ hq'.2.1
    rw [← h1, ← h2, openSegment_lineMap, ← h4]; exact mem_image_of_mem _ h
  have n3 : ν ∉ openSegment ℝ μ μ' := by
    intro h; apply hq'.2.2.2.2 _ hq.1
    rw [← h3, ← h4, openSegment_lineMap, ← h1]; exact mem_image_of_mem _ h
  have n4 : ν' ∉ openSegment ℝ μ μ' := by
    intro h; apply hq'.2.2.2.2 _ hq.2.1
    rw [← h3, ← h4, openSegment_lineMap, ← h2]; exact mem_image_of_mem _ h
  rcases real_same hνν hξ hζ hμμ n1 n2 n3 n4 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left; ext
    · rw [← h3, ← h1, e1]
    · rw [← h4, ← h2, e2]
  · right; ext
    · rw [← h3, Prod.fst_swap, ← h2, e1]
    · rw [← h4, Prod.snd_swap, ← h1, e2]

theorem piece_inter_aux (hT : ∀ t ∈ T, t.1 ≠ t.2) {q q' : E × E}
    (hq : IsPiece T (cutV T P) q) (hq' : IsPiece T (cutV T P) q') (hne : q' ≠ q)
    (hne' : q' ≠ q.swap) {x : E} (hx : x ∈ segment ℝ q.1 q.2) (hx' : x ∈ segment ℝ q'.1 q'.2) :
    x = q.1 ∨ x = q.2 := by
  by_contra h
  push_neg at h
  have hxo : x ∈ openSegment ℝ q.1 q.2 :=
    mem_openSegment_of_ne_left_right h.1.symm h.2.symm hx
  obtain ⟨t, ht, hqt⟩ := hq.2.2.2.1
  obtain ⟨t', ht', hq't'⟩ := hq'.2.2.2.1
  have hsub := piece_cross ht ht' (hT t ht) hq hqt hxo (hq't' hx')
  rcases piece_same (hT t' ht') hq hq' hsub hq't' hxo hx' with h' | h'
  · exact hne h'
  · exact hne' h'

/-- Two pieces that differ up to orientation meet at most in common endpoints. -/
theorem piece_inter (hT : ∀ t ∈ T, t.1 ≠ t.2) {q q' : E × E}
    (hq : IsPiece T (cutV T P) q) (hq' : IsPiece T (cutV T P) q') (hne : q' ≠ q)
    (hne' : q' ≠ q.swap) :
    segment ℝ q.1 q.2 ∩ segment ℝ q'.1 q'.2 ⊆ ({q.1, q.2} : Set E) ∩ {q'.1, q'.2} := by
  rintro x ⟨hx, hx'⟩
  refine ⟨piece_inter_aux hT hq hq' hne hne' hx hx', ?_⟩
  have hne2 : q ≠ q'.swap := by
    intro h; apply hne'; rw [h, Prod.swap_swap]
  exact piece_inter_aux hT hq' hq (Ne.symm hne) hne2 hx' hx

/-- **Covering**: every point of a segment of `T` lies on a piece inside it, and is an endpoint
of that piece if it is a cut point. -/
theorem exists_piece_cover {t : E × E} (ht : t ∈ T) (htne : t.1 ≠ t.2) {x : E}
    (hx : x ∈ segment ℝ t.1 t.2) :
    ∃ q, IsPiece T (cutV T P) q ∧ segment ℝ q.1 q.2 ⊆ segment ℝ t.1 t.2 ∧
      x ∈ segment ℝ q.1 q.2 ∧ (x ∈ cutV T P → x = q.1 ∨ x = q.2) := by
  set V := cutV T P with hV
  set f : ℝ → E := ⇑(AffineMap.lineMap (k := ℝ) t.1 t.2) with hf
  have hinj : Function.Injective f := AffineMap.lineMap_injective ℝ htne
  set C : Set ℝ := Icc 0 1 ∩ f ⁻¹' (V : Set E) with hCdef
  have hC : C.Finite :=
    (V.finite_toSet.preimage hinj.injOn).subset inter_subset_right
  have h0 : (0 : ℝ) ∈ C := ⟨⟨le_rfl, zero_le_one⟩, by
    show f 0 ∈ (V : Set E); rw [hf, AffineMap.lineMap_apply_zero]; exact mem_cutV_fst ht⟩
  have h1 : (1 : ℝ) ∈ C := ⟨⟨zero_le_one, le_rfl⟩, by
    show f 1 ∈ (V : Set E); rw [hf, AffineMap.lineMap_apply_one]; exact mem_cutV_snd ht⟩
  obtain ⟨ξ, hξ, rfl⟩ := (mem_segment_iff_lineMap).1 hx
  obtain ⟨α, hαA, hαmax⟩ := exists_max_image {c ∈ C | c ≤ ξ ∧ c < 1} id
    (hC.subset (fun c hc => hc.1)) ⟨0, h0, hξ.1, zero_lt_one⟩
  obtain ⟨β, hβB, hβmin⟩ := exists_min_image {c ∈ C | α < c} id
    (hC.subset (fun c hc => hc.1)) ⟨1, h1, hαA.2.2⟩
  have hαβ : α < β := hβB.2
  have hξβ : ξ ≤ β := by
    by_contra h
    push_neg at h
    have := hαmax β ⟨hβB.1, h.le, lt_of_lt_of_le h hξ.2⟩
    simp only [id] at this
    linarith
  have hα0 : 0 ≤ α := hαA.1.1.1
  have hβ1 : β ≤ 1 := hβB.1.1.2
  have hseg : segment ℝ (f α) (f β) = f '' Icc α β := by
    rw [hf, segment_lineMap, uIcc_of_le hαβ.le]
  refine ⟨(f α, f β), ⟨hαA.1.2, hβB.1.2, hinj.ne hαβ.ne, ⟨t, ht, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · rw [hseg, segment_eq_image_lineMap]
    exact image_mono (Icc_subset_Icc hα0 hβ1)
  · intro v hv hvo
    rw [hf, openSegment_lineMap, openSegment_eq_Ioo hαβ] at hvo
    obtain ⟨c, hc, rfl⟩ := hvo
    have hcB : c ∈ {c ∈ C | α < c} :=
      ⟨⟨⟨hα0.trans hc.1.le, hc.2.le.trans hβ1⟩, hv⟩, hc.1⟩
    have := hβmin c hcB
    simp only [id] at this
    linarith [hc.2]
  · show segment ℝ (f α) (f β) ⊆ segment ℝ t.1 t.2
    rw [hseg, segment_eq_image_lineMap]
    exact image_mono (Icc_subset_Icc hα0 hβ1)
  · show f ξ ∈ segment ℝ (f α) (f β)
    rw [hseg]
    exact mem_image_of_mem _ ⟨hαA.2.1, hξβ⟩
  · intro hxV
    have hξC : ξ ∈ C := ⟨hξ, hxV⟩
    rcases lt_or_eq_of_le hξ.2 with hlt | heq
    · left
      have := hαmax ξ ⟨hξC, le_rfl, hlt⟩
      simp only [id] at this
      show f ξ = f α
      rw [le_antisymm this hαA.2.1]
    · right
      have := hβmin 1 ⟨h1, hαA.2.2⟩
      simp only [id] at this
      show f ξ = f β
      rw [heq, le_antisymm hβ1 (heq ▸ hξβ)]

/-- **Common subdivision** (commission 194, §3.1, in the form used for §3.0). -/
theorem exists_common_subdivision (T : Finset (E × E)) (hT : ∀ t ∈ T, t.1 ≠ t.2)
    (P : Finset E) :
    ∃ S : Finset (E × E), (∀ s ∈ S, s.1 ≠ s.2) ∧
      (∀ s ∈ S, ∃ t ∈ T, segment ℝ s.1 s.2 ⊆ segment ℝ t.1 t.2) ∧
      (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' →
        segment ℝ s.1 s.2 ∩ segment ℝ s'.1 s'.2 ⊆ ({s.1, s.2} : Set E) ∩ {s'.1, s'.2}) ∧
      (∀ t ∈ T, ∀ x ∈ segment ℝ t.1 t.2, ∃ s ∈ S, x ∈ segment ℝ s.1 s.2 ∧
        segment ℝ s.1 s.2 ⊆ segment ℝ t.1 t.2) ∧
      (∀ p ∈ P, ∀ t ∈ T, p ∈ segment ℝ t.1 t.2 → ∃ s ∈ S, p = s.1 ∨ p = s.2) := by
  classical
  set V := cutV T P with hV
  refine ⟨((V ×ˢ V).filter (IsPiece T V)).filter (fun q => WellOrderingRel q.1 q.2),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_filter] at hs
    exact hs.1.2.2.2.1
  · intro s hs
    simp only [Finset.mem_filter] at hs
    exact hs.1.2.2.2.2.1
  · intro s hs s' hs' hne
    simp only [Finset.mem_filter] at hs hs'
    refine piece_inter hT hs.1.2 hs'.1.2 (Ne.symm hne) ?_
    rintro rfl
    exact _root_.asymm hs.2 hs'.2
  · -- orientation: every piece has a representative in `S`
    have hrep : ∀ q, IsPiece T V q → ∃ s ∈ ((V ×ˢ V).filter (IsPiece T V)).filter
        (fun q => WellOrderingRel q.1 q.2), segment ℝ s.1 s.2 = segment ℝ q.1 q.2 ∧
          ({s.1, s.2} : Set E) = {q.1, q.2} := by
      intro q hq
      rcases trichotomous_of WellOrderingRel q.1 q.2 with h | h | h
      · exact ⟨q, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hq.1, hq.2.1⟩, hq⟩, h⟩, rfl, rfl⟩
      · exact absurd h hq.2.2.1
      · refine ⟨q.swap, ?_, by simp [segment_symm], by simp [Set.pair_comm]⟩
        exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hq.2.1, hq.1⟩, hq.swap⟩, h⟩
    intro t ht x hx
    obtain ⟨q, hq, hqt, hxq, -⟩ := exists_piece_cover (P := P) ht (hT t ht) hx
    obtain ⟨s, hs, hseg, -⟩ := hrep q hq
    exact ⟨s, hs, hseg ▸ hxq, hseg ▸ hqt⟩
  · intro p hp t ht hpt
    obtain ⟨q, hq, -, -, hv⟩ := exists_piece_cover (P := P) ht (hT t ht) hpt
    have hpq := hv (mem_cutV_of_mem hp)
    rcases trichotomous_of WellOrderingRel q.1 q.2 with h | h | h
    · exact ⟨q, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hq.1, hq.2.1⟩, hq⟩, h⟩, hpq⟩
    · exact absurd h hq.2.2.1
    · refine ⟨q.swap, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hq.2.1, hq.1⟩, hq.swap⟩, h⟩, ?_⟩
      simpa [or_comm] using hpq

end Pieces

end HPC.HO16.Subdiv
