import HPC.HO16.Lemma18

/-!
# Batch 195, §5 and §9: a certificate and an example (in ℝ)

Part of the batch-195 skeleton `HO16C.lean` (commission 195), split under `HPC/HO16/`.

* `ho16_p193_remark_false`: the remarks of pp. 193–194 fail without "G connected".
* `stairwell_example`: a stairwell structure of height 3 over `[0, 3]` (non-vacuity of
  `IsStairwellStr`); `broken_stairwell_example` (through `ho16_prop17`, of
  `IsBrokenStairwellStr`); `lemma18_example` (the hypotheses of `ho16_lemma18`);
  `prop19_fold_example` (the hypotheses of `ho16_prop19_fold`).
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

/-! ## Interval tools -/

theorem isStraight_segment {G : Set ℝ} {p q : ℝ × ℝ} (h : p.1 ≠ q.1)
    (hsub : segment ℝ p q ⊆ G ×ˢ Icc (0 : ℝ) 1) : IsStraight G (segment ℝ p q) := by
  refine ⟨hsub, Subdiv.isClosed_segment' p q, injOn_fst_segment h, ?_⟩
  rw [image_fst_segment]
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [segment_eq_Icc h'.le]; exact isPLGraph_Icc h'
  · rw [segment_symm, segment_eq_Icc h'.le]; exact isPLGraph_Icc h'

theorem isStraight_prod_singleton {G : Set ℝ} {a b c : ℝ} (hab : a < b)
    (hsub : Icc a b ×ˢ ({c} : Set ℝ) ⊆ G ×ˢ Icc (0 : ℝ) 1) :
    IsStraight G (Icc a b ×ˢ ({c} : Set ℝ)) := by
  refine ⟨hsub, isClosed_Icc.prod isClosed_singleton, ?_, ?_⟩
  · rintro ⟨x, y⟩ ⟨-, hy⟩ ⟨x', y'⟩ ⟨-, hy'⟩ hxx
    simp only [mem_singleton_iff] at hy hy'
    simp only at hxx
    rw [hxx, hy, hy']
  · rw [fst_image_prod _ (singleton_nonempty c)]
    exact isPLGraph_Icc hab

/-! ## §5. The certificate for pp. 193–194 -/

/-- **p. 193 / p. 194 without "G connected"**: false. `G = [0, 1] ∪ [2, 3]`, `S = [0, 1] × {½}`
has a stairwell structure of height 1 and `π(S) ≠ G`. -/
theorem ho16_p193_remark_false :
    ¬ ∀ (G : Set ℝ) (S : Set (ℝ × ℝ)), IsPLGraph G → S ⊆ G ×ˢ Ioo (0 : ℝ) 1 →
      HasStairwell G S 1 → Prod.fst '' S = G := by
  intro H
  have hG : IsPLGraph (Icc (0 : ℝ) 1 ∪ Icc 2 3) :=
    (isPLGraph_Icc (by norm_num)).union (isPLGraph_Icc (by norm_num))
  have hsub : Icc (0 : ℝ) 1 ×ˢ ({1 / 2} : Set ℝ) ⊆ (Icc (0 : ℝ) 1 ∪ Icc 2 3) ×ˢ Ioo (0 : ℝ) 1 := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [mem_singleton_iff] at hy
    refine ⟨Or.inl hx, ?_⟩
    rw [hy]; norm_num
  have hstr : IsStraight (Icc (0 : ℝ) 1 ∪ Icc 2 3) (Icc (0 : ℝ) 1 ×ˢ ({1 / 2} : Set ℝ)) :=
    isStraight_prod_singleton (by norm_num) fun p hp => ⟨(hsub hp).1, Ioo_subset_Icc_self (hsub hp).2⟩
  have himg : Prod.fst '' (Icc (0 : ℝ) 1 ×ˢ ({1 / 2} : Set ℝ)) = Icc 0 1 :=
    fst_image_prod _ (singleton_nonempty _)
  have hfr : relFrontier (Icc (0 : ℝ) 1 ∪ Icc 2 3) (Icc 0 1) = ∅ := by
    ext x
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    rw [isClosed_Icc.closure_eq] at h1
    have hsub' : (Icc (0 : ℝ) 1 ∪ Icc 2 3) \ Icc 0 1 ⊆ Icc 2 3 := by
      rintro z ⟨hz | hz, hz'⟩
      · exact absurd hz hz'
      · exact hz
    have h2' := closure_minimal hsub' isClosed_Icc h2
    linarith [h1.2, h2'.1]
  have hend : endSet (Icc (0 : ℝ) 1 ∪ Icc 2 3) (Icc (0 : ℝ) 1 ×ˢ ({1 / 2} : Set ℝ)) = ∅ := by
    rw [endSet, himg, hfr, preimage_empty, inter_empty]
  have hS : HasStairwell (Icc (0 : ℝ) 1 ∪ Icc 2 3) (Icc (0 : ℝ) 1 ×ˢ ({1 / 2} : Set ℝ)) 1 := by
    refine ⟨fun _ => Icc (0 : ℝ) 1 ×ˢ ({1 / 2} : Set ℝ), fun _ => ∅, le_rfl,
      fun _ _ => ⟨⟨(0, 1 / 2), by norm_num⟩, hstr⟩, by simp, fun _ _ => ?_, rfl, rfl,
      fun i hi => absurd hi.2 (not_lt.2 hi.1), fun _ _ => ?_, ⟨by simp, by simp⟩⟩
    · rw [hend, union_empty]
      exact ⟨rfl, disjoint_empty _, finite_empty, finite_empty⟩
    · rw [image_empty]
      exact ⟨hasConsCompl_empty _ _, hasConsCompl_empty _ _⟩
  have h := H _ _ hG hsub hS
  rw [himg] at h
  have h2 : (2 : ℝ) ∈ Icc (0 : ℝ) 1 := by
    rw [h]; exact Or.inr ⟨le_rfl, by norm_num⟩
  norm_num at h2

/-! ## §9. A stairwell structure of height 3 over `[0, 3]` -/

theorem relFrontier_Icc03_Icc02 : relFrontier (Icc (0 : ℝ) 3) (Icc 0 2) = {2} := by
  have hd : Icc (0 : ℝ) 3 \ Icc 0 2 = Ioc 2 3 := by
    ext x
    simp only [mem_diff, mem_Icc, mem_Ioc, not_and, not_le]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3 h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, fun _ => h1⟩
  rw [relFrontier, hd, closure_Ioc (by norm_num), isClosed_Icc.closure_eq]
  ext x
  simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
  constructor
  · rintro ⟨⟨-, h1⟩, h2, -⟩; linarith
  · rintro rfl; norm_num

theorem relFrontier_Icc03_Icc12 : relFrontier (Icc (0 : ℝ) 3) (Icc 1 2) = {1, 2} := by
  have hd : Icc (0 : ℝ) 3 \ Icc 1 2 = Ico 0 1 ∪ Ioc 2 3 := by
    ext x
    simp only [mem_diff, mem_Icc, mem_Ico, mem_Ioc, mem_union, not_and, not_le]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hx : x < 1
      · exact Or.inl ⟨h1, hx⟩
      · exact Or.inr ⟨h3 (by linarith), h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨⟨h1, by linarith⟩, fun h => by linarith⟩
      · exact ⟨⟨by linarith, h2⟩, fun _ => h1⟩
  rw [relFrontier, hd, closure_union, closure_Ico (by norm_num), closure_Ioc (by norm_num),
    isClosed_Icc.closure_eq]
  ext x
  simp only [mem_inter_iff, mem_Icc, mem_union, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨-, h3⟩ | ⟨h3, -⟩⟩
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl)
    · norm_num
    · norm_num

theorem relFrontier_Icc03_Icc13 : relFrontier (Icc (0 : ℝ) 3) (Icc 1 3) = {1} := by
  have hd : Icc (0 : ℝ) 3 \ Icc 1 3 = Ico 0 1 := by
    ext x
    simp only [mem_diff, mem_Icc, mem_Ico, not_and, not_le]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, lt_of_not_ge fun hx => absurd (h3 hx) (by linarith)⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, fun h => by linarith⟩
  rw [relFrontier, hd, closure_Ico (by norm_num), isClosed_Icc.closure_eq]
  ext x
  simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
  constructor
  · rintro ⟨⟨h1, -⟩, -, h2⟩; linarith
  · rintro rfl; norm_num

/-- If `∂A ⊆ B`, then `A` has consistent complement relative to `B`. -/
theorem hasConsCompl_of_relFrontier_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G A B : Set E} (hG : IsPLGraph G) (hA : IsClosed A) (h : relFrontier G A ⊆ B) :
    HasConsCompl G A B := fun x _ =>
  Or.inl ((hG.relFrontier_comp_subset_relFrontier hA x).trans h)

theorem isOrdinaryPt_Icc03 {x : ℝ} (h0 : 0 < x) (h3 : x < 3) : IsOrdinaryPt (Icc 0 3) x := by
  refine ⟨0, 3, h0.ne, h3.ne', ?_, ?_, ?_⟩
  · rw [segment_eq_Icc h0.le, segment_eq_Icc h3.le]
    ext y
    simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨-, h1⟩, h2, -⟩; linarith
    · rintro rfl; exact ⟨⟨h0.le, le_rfl⟩, le_rfl, h3.le⟩
  · rw [segment_eq_Icc h0.le, segment_eq_Icc h3.le]
    exact union_subset (Icc_subset_Icc le_rfl h3.le) (Icc_subset_Icc h0.le le_rfl)
  · rw [segment_eq_Icc h0.le, segment_eq_Icc h3.le]
    refine mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset (Icc_mem_nhds h0 h3) ?_)
    intro y hy
    by_cases hyx : y ≤ x
    · exact Or.inl ⟨hy.1, hyx⟩
    · exact Or.inr ⟨(not_le.1 hyx).le, hy.2⟩

/-- A stairwell structure of height 3 over `G = [0, 3]` with `𝓔(S₁) ≠ ∅` and `α₃ ≠ ∅` (the explicit
structure of commission §9; `stairwell_example` is its skeleton form). -/
theorem stairwell_example' :
    ∃ (S : Set (ℝ × ℝ)) (T α : ℕ → Set (ℝ × ℝ)),
      IsStairwellStr (Icc (0 : ℝ) 3) S 3 T α ∧ S ⊆ Icc (0 : ℝ) 3 ×ˢ Ioo (0 : ℝ) 1 ∧
      (endSet (Icc (0 : ℝ) 3) (T 1)).Nonempty ∧ (α 3).Nonempty := by
  set S₁ : Set (ℝ × ℝ) := Icc (0 : ℝ) 2 ×ˢ ({1 / 4} : Set ℝ) with hS₁
  set S₂ : Set (ℝ × ℝ) := segment ℝ ((2 : ℝ), (1 / 4 : ℝ)) (1, 1 / 2) with hS₂
  set S₃ : Set (ℝ × ℝ) := segment ℝ ((1 : ℝ), (1 / 2 : ℝ)) (3, 3 / 4) with hS₃
  set T : ℕ → Set (ℝ × ℝ) := fun i => if i = 1 then S₁ else if i = 2 then S₂ else S₃ with hT
  set α : ℕ → Set (ℝ × ℝ) := fun i =>
    if i = 2 then {((2 : ℝ), (1 / 4 : ℝ))} else if i = 3 then {((1 : ℝ), (1 / 2 : ℝ))} else ∅
    with hα
  have hT1 : T 1 = S₁ := by simp [hT]
  have hT2 : T 2 = S₂ := by simp [hT]
  have hT3 : T 3 = S₃ := by simp [hT]
  have hα1 : α 1 = ∅ := by simp [hα]
  have hα2 : α 2 = {((2 : ℝ), (1 / 4 : ℝ))} := by simp [hα]
  have hα3 : α 3 = {((1 : ℝ), (1 / 2 : ℝ))} := by simp [hα]
  have hα4 : α 4 = ∅ := by simp [hα]
  have hconv : Convex ℝ (Icc (0 : ℝ) 3 ×ˢ Ioo (0 : ℝ) 1) := convex_Icc _ _ |>.prod (convex_Ioo _ _)
  have hsub₁ : S₁ ⊆ Icc (0 : ℝ) 3 ×ˢ Ioo (0 : ℝ) 1 := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [mem_singleton_iff] at hy
    exact ⟨⟨hx.1, by linarith [hx.2]⟩, by rw [hy]; norm_num⟩
  have hsub₂ : S₂ ⊆ Icc (0 : ℝ) 3 ×ˢ Ioo (0 : ℝ) 1 :=
    hconv.segment_subset (by norm_num) (by norm_num)
  have hsub₃ : S₃ ⊆ Icc (0 : ℝ) 3 ×ˢ Ioo (0 : ℝ) 1 :=
    hconv.segment_subset (by norm_num) (by norm_num)
  have hstar : ∀ {X : Set (ℝ × ℝ)}, X ⊆ Icc (0 : ℝ) 3 ×ˢ Ioo (0 : ℝ) 1 →
      X ⊆ Icc (0 : ℝ) 3 ×ˢ Icc (0 : ℝ) 1 := fun h p hp => ⟨(h hp).1, Ioo_subset_Icc_self (h hp).2⟩
  have hst₁ : IsStraight (Icc (0 : ℝ) 3) S₁ := isStraight_prod_singleton (by norm_num) (hstar hsub₁)
  have hst₂ : IsStraight (Icc (0 : ℝ) 3) S₂ := isStraight_segment (by norm_num) (hstar hsub₂)
  have hst₃ : IsStraight (Icc (0 : ℝ) 3) S₃ := isStraight_segment (by norm_num) (hstar hsub₃)
  have hπ₁ : Prod.fst '' S₁ = Icc 0 2 := fst_image_prod _ (singleton_nonempty _)
  have hπ₂ : Prod.fst '' S₂ = Icc 1 2 := by
    rw [image_fst_segment, segment_symm, segment_eq_Icc (by norm_num)]
  have hπ₃ : Prod.fst '' S₃ = Icc 1 3 := by
    rw [image_fst_segment, segment_eq_Icc (by norm_num)]
  have hinj₂ := injOn_fst_segment (p := ((2 : ℝ), (1 / 4 : ℝ))) (q := (1, 1 / 2)) (by norm_num)
  have hinj₃ := injOn_fst_segment (p := ((1 : ℝ), (1 / 2 : ℝ))) (q := (3, 3 / 4)) (by norm_num)
  have hE₁ : endSet (Icc (0 : ℝ) 3) S₁ = {((2 : ℝ), (1 / 4 : ℝ))} := by
    rw [endSet, hπ₁, relFrontier_Icc03_Icc02]
    ext ⟨x, y⟩
    simp only [hS₁, mem_inter_iff, mem_prod, mem_Icc, mem_singleton_iff, mem_preimage,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨-, hy⟩, hx⟩; exact ⟨hx, hy⟩
    · rintro ⟨rfl, rfl⟩; norm_num
  have hE₂ : endSet (Icc (0 : ℝ) 3) S₂ = {((2 : ℝ), (1 / 4 : ℝ))} ∪ {((1 : ℝ), (1 / 2 : ℝ))} := by
    rw [endSet, hπ₂, relFrontier_Icc03_Icc12]
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_insert_iff, mem_singleton_iff, mem_union]
    constructor
    · rintro ⟨hp, h1 | h2⟩
      · right; exact hinj₂ hp (right_mem_segment ℝ _ _) h1
      · left; exact hinj₂ hp (left_mem_segment ℝ _ _) h2
    · rintro (rfl | rfl)
      · exact ⟨left_mem_segment ℝ _ _, Or.inr rfl⟩
      · exact ⟨right_mem_segment ℝ _ _, Or.inl rfl⟩
  have hE₃ : endSet (Icc (0 : ℝ) 3) S₃ = {((1 : ℝ), (1 / 2 : ℝ))} := by
    rw [endSet, hπ₃, relFrontier_Icc03_Icc13]
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hp, h1⟩; exact hinj₃ hp (left_mem_segment ℝ _ _) h1
    · rintro rfl; exact ⟨left_mem_segment ℝ _ _, rfl⟩
  have hG : IsPLGraph (Icc (0 : ℝ) 3) := isPLGraph_Icc (by norm_num)
  -- consistency of `[1, 2]` relative to `{1}` and to `{2}`
  have hc₂ : ∀ B : Set ℝ, B = {1} ∨ B = {2} → HasConsCompl (Icc (0 : ℝ) 3) (Icc 1 2) B := by
    intro B hB x hx
    have hfr := hG.relFrontier_comp_subset_relFrontier isClosed_Icc (A := Icc (1 : ℝ) 2) x
    rw [relFrontier_Icc03_Icc12] at hfr
    have hsplit : Icc (0 : ℝ) 3 \ Icc 1 2 ⊆ Iio 1 ∪ Ioi 2 := by
      rintro z ⟨-, hz⟩
      simp only [mem_Icc, not_and, not_le] at hz
      by_cases h : z < 1
      · exact Or.inl h
      · exact Or.inr (hz (not_lt.1 h))
    have hC := connectedComponentIn_subset (Icc (0 : ℝ) 3 \ Icc 1 2) x
    have hxC := mem_connectedComponentIn hx
    rcases hsplit hx with h | h
    · have hCl : _root_.connectedComponentIn (Icc (0 : ℝ) 3 \ Icc 1 2) x ⊆ Iio 1 :=
        isPreconnected_connectedComponentIn.subset_left_of_subset_union isOpen_Iio isOpen_Ioi
          (Set.disjoint_left.2 fun z (h1 : z < 1) (h2 : 2 < z) => by linarith)
          (hC.trans hsplit) ⟨x, hxC, h⟩
      have h1 : relFrontier (Icc (0 : ℝ) 3) (_root_.connectedComponentIn (Icc (0 : ℝ) 3 \ Icc 1 2) x)
          ⊆ {1} := by
        intro z hz
        have hz' := hfr hz
        have hzc : z ≤ 1 := closure_minimal (hCl.trans Iio_subset_Iic_self) isClosed_Iic hz.1
        rcases hz' with h' | h'
        · exact h'
        · rw [mem_singleton_iff] at h'; linarith
      rcases hB with rfl | rfl
      · exact Or.inl h1
      · exact Or.inr (Set.disjoint_of_subset_left h1 (by norm_num))
    · have hCr : _root_.connectedComponentIn (Icc (0 : ℝ) 3 \ Icc 1 2) x ⊆ Ioi 2 :=
        isPreconnected_connectedComponentIn.subset_right_of_subset_union isOpen_Iio isOpen_Ioi
          (Set.disjoint_left.2 fun z (h1 : z < 1) (h2 : 2 < z) => by linarith)
          (hC.trans hsplit) ⟨x, hxC, h⟩
      have h2 : relFrontier (Icc (0 : ℝ) 3) (_root_.connectedComponentIn (Icc (0 : ℝ) 3 \ Icc 1 2) x)
          ⊆ {2} := by
        intro z hz
        have hz' := hfr hz
        have hzc : 2 ≤ z := closure_minimal (hCr.trans Ioi_subset_Ici_self) isClosed_Ici hz.1
        rcases hz' with h' | h'
        · rw [h'] at hzc; norm_num at hzc
        · exact h'
      rcases hB with rfl | rfl
      · exact Or.inr (Set.disjoint_of_subset_left h2 (by norm_num))
      · exact Or.inl h2
  refine ⟨⋃ i ∈ Icc 1 3, T i, T, α, ⟨le_refl _ |>.trans (by norm_num), ?_, rfl, ?_, hα1, hα4,
    ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i hi
    rcases (by have := hi.1; have := hi.2; omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · rw [hT1]; exact ⟨⟨(0, 1 / 4), by norm_num [hS₁]⟩, hst₁⟩
    · rw [hT2]; exact ⟨⟨_, left_mem_segment ℝ _ _⟩, hst₂⟩
    · rw [hT3]; exact ⟨⟨_, left_mem_segment ℝ _ _⟩, hst₃⟩
  · intro i hi
    rcases (by have := hi.1; have := hi.2; omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · rw [hT1, hE₁, hα1, show (1 : ℕ) + 1 = 2 from rfl, hα2, empty_union]
      exact ⟨rfl, empty_disjoint _, finite_empty, finite_singleton _⟩
    · rw [hT2, hE₂, hα2, show (2 : ℕ) + 1 = 3 from rfl, hα3]
      exact ⟨rfl, by norm_num, finite_singleton _, finite_singleton _⟩
    · rw [hT3, hE₃, hα3, show (3 : ℕ) + 1 = 4 from rfl, hα4, union_empty]
      exact ⟨rfl, disjoint_empty _, finite_singleton _, finite_empty⟩
  · intro i hi
    rcases (by have := hi.1; have := hi.2; omega : i = 1 ∨ i = 2) with rfl | rfl
    · refine ⟨Ioi 1, isOpen_Ioi.mem_nhdsSet.2 ?_, ?_⟩
      · rw [show (1 : ℕ) + 1 = 2 from rfl, hα2, image_singleton]
        intro z hz; rw [mem_singleton_iff] at hz; rw [hz]; norm_num
      · rw [show (1 : ℕ) + 1 = 2 from rfl, hT1, hT2, hπ₁, hπ₂]
        ext z
        simp only [mem_inter_iff, mem_Icc, mem_Ioi]
        constructor
        · rintro ⟨⟨-, h2⟩, h1⟩; exact ⟨⟨h1.le, h2⟩, h1⟩
        · rintro ⟨⟨-, h2⟩, h1⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
    · refine ⟨Iio 2, isOpen_Iio.mem_nhdsSet.2 ?_, ?_⟩
      · rw [show (2 : ℕ) + 1 = 3 from rfl, hα3, image_singleton]
        intro z hz; rw [mem_singleton_iff] at hz; rw [hz]; norm_num
      · rw [show (2 : ℕ) + 1 = 3 from rfl, hT2, hT3, hπ₂, hπ₃]
        ext z
        simp only [mem_inter_iff, mem_Icc, mem_Iio]
        constructor
        · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨h1, by linarith⟩, h2⟩
        · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨h1, h2.le⟩, h2⟩
  · intro i hi
    rcases (by have := hi.1; have := hi.2; omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · rw [hT1, hα1, show (1 : ℕ) + 1 = 2 from rfl, hα2, image_empty, image_singleton, hπ₁]
      exact ⟨hasConsCompl_empty _ _, hasConsCompl_of_relFrontier_subset hG isClosed_Icc
        relFrontier_Icc03_Icc02.le⟩
    · rw [hT2, hα2, show (2 : ℕ) + 1 = 3 from rfl, hα3, image_singleton, image_singleton, hπ₂]
      exact ⟨hc₂ _ (Or.inr rfl), hc₂ _ (Or.inl rfl)⟩
    · rw [hT3, hα3, show (3 : ℕ) + 1 = 4 from rfl, hα4, image_empty, image_singleton, hπ₃]
      exact ⟨hasConsCompl_of_relFrontier_subset hG isClosed_Icc relFrontier_Icc03_Icc13.le,
        hasConsCompl_empty _ _⟩
  · show IsGeneric (Icc (0 : ℝ) 3) [Prod.fst '' α 2, Prod.fst '' α 3]
    rw [hα2, hα3, image_singleton, image_singleton]
    refine ⟨?_, by simp⟩
    intro B hB
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB
    rcases hB with rfl | rfl
    · refine ⟨finite_singleton _, by norm_num, fun x hx => ?_⟩
      rw [mem_singleton_iff] at hx
      rw [hx]; exact isOrdinaryPt_Icc03 (by norm_num) (by norm_num)
    · refine ⟨finite_singleton _, by norm_num, fun x hx => ?_⟩
      rw [mem_singleton_iff] at hx
      rw [hx]; exact isOrdinaryPt_Icc03 (by norm_num) (by norm_num)
  · refine iUnion₂_subset fun i hi => ?_
    rcases (by have := hi.1; have := hi.2; omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · rw [hT1]; exact hsub₁
    · rw [hT2]; exact hsub₂
    · rw [hT3]; exact hsub₃
  · rw [hT1, hE₁]; exact singleton_nonempty _
  · rw [hα3]; exact singleton_nonempty _

/-- **Non-vacuity (§9)**: a stairwell structure of height 3 over `G = [0, 3]`. -/
theorem stairwell_example :
    ∃ (S : Set (ℝ × ℝ)) (T α : ℕ → Set (ℝ × ℝ)),
      IsStairwellStr (Icc (0 : ℝ) 3) S 3 T α ∧ S ⊆ Icc (0 : ℝ) 3 ×ˢ Ioo (0 : ℝ) 1 := by
  obtain ⟨S, T, α, h, hS, -⟩ := stairwell_example'
  exact ⟨S, T, α, h, hS⟩

/-- **Non-vacuity (§9)**: `IsBrokenStairwellStr` is satisfiable — `ho16_prop17` applied to
`stairwell_example` gives a broken stairwell structure of height 1 with a pit at level 1. -/
theorem broken_stairwell_example :
    ∃ (S : Set (ℝ × ℝ)) (T α : ℕ → Set (ℝ × ℝ)) (γ P₁ P₂ : Set (ℝ × ℝ)),
      IsBrokenStairwellStr (Icc (0 : ℝ) 3) S 1 1 T α γ P₁ P₂ := by
  obtain ⟨S, T, α, h, -⟩ := stairwell_example
  exact ⟨S, _, _, _, _, _, ho16_prop17 h le_rfl⟩

/-- **Non-vacuity (§9)**: every hypothesis of `ho16_lemma18` is met — the batch-194 fold on
`[0, 3]` (`G₁ = [0, 2]`, `G₂ = [1, 2]`, `G₃ = [1, 3]`) and the straight set `[0, 3] × {½}`,
whose projection has empty frontier in `[0, 3]`. -/
theorem lemma18_example :
    ∃ (F₁ F₂ F₃ : Set (ℝ × ℝ)) (S : Set (ℝ × ℝ)),
      IsSimpleFoldOf (Icc (0 : ℝ) 3) (Icc 0 2) (Icc 1 2) (Icc 1 3) F₁ F₂ F₃ ∧
      IsStraight (Icc (0 : ℝ) 3) S ∧
      Disjoint (relFrontier (Icc (0 : ℝ) 3) (Prod.fst '' S))
        (relFrontier (Icc (0 : ℝ) 3) (Icc 1 2)) := by
  obtain ⟨F₁, F₂, F₃, hF, -⟩ := exists_simpleFold_example
  refine ⟨F₁, F₂, F₃, Icc (0 : ℝ) 3 ×ˢ ({1 / 2} : Set ℝ), hF, ?_, ?_⟩
  · refine isStraight_prod_singleton (by norm_num) ?_
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [mem_singleton_iff] at hy
    exact ⟨hx, by rw [hy]; norm_num, by rw [hy]; norm_num⟩
  · rw [fst_image_prod _ (singleton_nonempty _)]
    have : relFrontier (Icc (0 : ℝ) 3) (Icc 0 3) = ∅ := by
      simp [relFrontier]
    rw [this]; exact Set.empty_disjoint _

/-- **Non-vacuity (§9)**: every hypothesis of `ho16_prop19_fold` (and of Proposition 19 as
printed, including `γ_{i₀} ≠ ∅`) is met — `ho16_prop17` applied to `stairwell_example'` gives a
broken stairwell structure over the connected graph `[0, 3]` with `𝓔(P₁) ≠ ∅` and `γ ≠ ∅`. -/
theorem prop19_fold_example :
    ∃ (S : Set (ℝ × ℝ)) (T α : ℕ → Set (ℝ × ℝ)) (γ P₁ P₂ : Set (ℝ × ℝ)),
      IsPLGraph (Icc (0 : ℝ) 3) ∧ IsConnected (Icc (0 : ℝ) 3) ∧
      IsBrokenStairwellStr (Icc (0 : ℝ) 3) S 1 1 T α γ P₁ P₂ ∧ γ.Nonempty ∧
      (endSet (Icc (0 : ℝ) 3) P₁).Nonempty := by
  obtain ⟨S, T, α, h, -, hE, hγ⟩ := stairwell_example'
  exact ⟨S, _, _, _, _, _, isPLGraph_Icc (by norm_num), isConnected_Icc (by norm_num),
    ho16_prop17 h le_rfl, hγ, hE⟩

end HPC.HO16
