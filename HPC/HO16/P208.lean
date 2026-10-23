import HPC.HO16.P19Defs

/-!
# Batch 196, §4: a false sentence on p. 208

H–O p. 208 (the (S4′) argument for `P′₂`): "Moreover, φ(D)⊂π(P₁∪P₂), so ∂D̃∩π(α_{i₀})=∅ by (S6′)
for S." The certificate `ho16_p208_false`: a broken stairwell structure of height 3 with a pit at
level 2 on `G = [0, 10]` and a point `x = 3/2 ∈ π(P₂) \ π(S₂)` whose component `[0, 4)` in
`G \ π(S₂)` has the frontier point `4 ∈ π(α₂)`.

The data are commission 196 §4's projections (`π(S₁) = [4, 10]`, `π(S₂) = [4, 6]`, `π(S₃) = G`,
`π(P₁) = [1, 2] ∪ [11/2, 10]`, `π(P₂) = [1, 2] ∪ [11/2, 6]`, `π(α₂) = {4}`, `π(γ₂) = {6}`, so
`a = 11/2`), with every sheet placed at height `1/2`: the statement is about `G` only, and the
heights of the commission's example play no role in it.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

/-! ## Library: horizontal sheets and intervals in `ℝ` -/

theorem fst_image_prod_single (A : Set ℝ) (c : ℝ) : Prod.fst '' (A ×ˢ ({c} : Set ℝ)) = A :=
  fst_image_prod A (singleton_nonempty c)

theorem isStraight_prod_single {G A : Set ℝ} {c : ℝ} (hc : c ∈ Icc (0:ℝ) 1) (hAG : A ⊆ G)
    (hA : IsPLGraph A) : IsStraight G (A ×ˢ ({c} : Set ℝ)) := by
  refine ⟨prod_mono hAG (singleton_subset_iff.2 hc), hA.isCompact.isClosed.prod isClosed_singleton,
    ?_, by rw [fst_image_prod_single]; exact hA⟩
  rintro ⟨x, y⟩ ⟨-, hy⟩ ⟨x', y'⟩ ⟨-, hy'⟩ h
  simp only [mem_singleton_iff] at hy hy'
  simp only at h
  rw [h, hy, hy']

theorem endSet_prod_single {G A : Set ℝ} {c : ℝ} (hA : IsClosed A) :
    endSet G (A ×ˢ ({c} : Set ℝ)) = relFrontier G A ×ˢ ({c} : Set ℝ) := by
  ext ⟨x, y⟩
  simp only [endSet, fst_image_prod_single, mem_inter_iff, mem_prod, mem_preimage]
  constructor
  · rintro ⟨⟨-, hy⟩, hx⟩; exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨by have := hx.1; rwa [hA.closure_eq] at this, hy⟩, hx⟩

theorem isOrdinaryPt_Icc {l r y : ℝ} (hy : y ∈ Ioo l r) : IsOrdinaryPt (Icc l r) y := by
  obtain ⟨hl, hr⟩ := hy
  set δ := min (y - l) (r - y) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min (by linarith) (by linarith))
  have hδ1 : δ < y - l := by
    have := min_le_left (y - l) (r - y); rw [hδ]; linarith
  have hδ2 : δ < r - y := by
    have := min_le_right (y - l) (r - y); rw [hδ]; linarith
  refine ⟨y - δ, y + δ, by linarith, by linarith, ?_, ?_, ?_⟩
  · rw [segment_eq_Icc (by linarith), segment_eq_Icc (by linarith), Icc_inter_Icc]
    simp [hδ0.le]
  · rw [segment_eq_Icc (by linarith), segment_eq_Icc (by linarith)]
    rintro z (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
  · rw [segment_eq_Icc (by linarith), segment_eq_Icc (by linarith),
      Icc_union_Icc_eq_Icc (by linarith) (by linarith)]
    exact mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))

/-- The component of `x` in `G \ A` lies strictly between two points outside `G \ A`. -/
theorem comp_subset_Ioo {G A : Set ℝ} {x l r : ℝ} (hl : l ∉ G \ A) (hr : r ∉ G \ A)
    (hlx : l < x) (hxr : x < r) : connectedComponentIn (G \ A) x ⊆ Ioo l r := by
  intro y hy
  have hx : x ∈ connectedComponentIn (G \ A) x :=
    mem_connectedComponentIn (connectedComponentIn_nonempty_iff.1 ⟨y, hy⟩)
  have hpre := isPreconnected_connectedComponentIn (F := G \ A) (x := x)
  constructor
  · by_contra h
    push_neg at h
    exact hl (connectedComponentIn_subset _ _ (hpre.Icc_subset hy hx ⟨h, hlx.le⟩))
  · by_contra h
    push_neg at h
    exact hr (connectedComponentIn_subset _ _ (hpre.Icc_subset hx hy ⟨hxr.le, h⟩))

theorem hasConsCompl_of_gaps {G A B : Set ℝ} (hG : IsPLGraph G) (hA : IsClosed A)
    (h : ∀ x ∈ G \ A, ∃ l r, l < x ∧ x < r ∧ l ∉ G \ A ∧ r ∉ G \ A ∧
      (A ∩ Icc l r ⊆ B ∨ Disjoint (A ∩ Icc l r) B)) : HasConsCompl G A B := by
  intro x hx
  obtain ⟨l, r, hlx, hxr, hl, hr, hB⟩ := h x hx
  have hsub : relFrontier G (connectedComponentIn (G \ A) x) ⊆ A ∩ Icc l r := by
    intro z hz
    refine ⟨hG.relFrontier_comp_subset hA x hz, ?_⟩
    have := closure_mono (comp_subset_Ioo hl hr hlx hxr) hz.1
    rw [closure_Ioo (by linarith)] at this
    exact this
  rcases hB with hB | hB
  · exact Or.inl (hsub.trans hB)
  · exact Or.inr (hB.mono_left hsub)

theorem relFrontier_eq_of {G A K D : Set ℝ} (hA : IsClosed A) (hK : IsClosed K)
    (hGK : G \ A ⊆ K) (hD : A ∩ K ⊆ D) (hDA : D ⊆ A)
    (hDcl : ∀ p ∈ D, ∃ l r, l < r ∧ (p = l ∨ p = r) ∧ Ioo l r ⊆ G \ A) :
    relFrontier G A = D := by
  apply Subset.antisymm
  · rintro y ⟨h1, h2⟩
    rw [hA.closure_eq] at h1
    exact hD ⟨h1, closure_minimal hGK hK h2⟩
  · intro p hp
    refine ⟨subset_closure (hDA hp), ?_⟩
    obtain ⟨l, r, hlr, hp', hsub⟩ := hDcl p hp
    refine closure_mono hsub ?_
    rw [closure_Ioo hlr.ne]
    rcases hp' with rfl | rfl
    · exact ⟨le_rfl, hlr.le⟩
    · exact ⟨hlr.le, le_rfl⟩

/-! ## The example -/

/-- The example of commission 196 §4, with all sheets at height `1/2`: `G = [0, 10]`. -/
def p208G : Set ℝ := Icc 0 10
def p208A1 : Set ℝ := Icc 4 10
def p208A2 : Set ℝ := Icc 4 6
def p208P1 : Set ℝ := Icc 1 2 ∪ Icc (11/2) 10
def p208P2 : Set ℝ := Icc 1 2 ∪ Icc (11/2) 6

theorem p208_rf_A1 : relFrontier p208G p208A1 = {4} := by
  refine relFrontier_eq_of isClosed_Icc isClosed_Icc (K := Icc 0 4) ?_ ?_ ?_ ?_
  · rintro y ⟨⟨h1, h2⟩, h3⟩; simp only [p208A1, mem_Icc, not_and, not_le] at h3
    exact ⟨h1, by by_contra h; push_neg at h; linarith [h3 h.le]⟩
  · rintro y ⟨⟨h1, h2⟩, h3, h4⟩; simp only [mem_singleton_iff]; linarith
  · rintro y rfl; simp only [p208A1, mem_Icc]; norm_num
  · rintro p rfl
    refine ⟨3, 4, by norm_num, Or.inr rfl, ?_⟩
    rintro y ⟨h1, h2⟩
    simp only [p208G, p208A1, mem_diff, mem_Icc, not_and, not_le]
    exact ⟨⟨by linarith, by linarith⟩, fun h => by linarith⟩

theorem p208_rf_A2 : relFrontier p208G p208A2 = {4, 6} := by
  refine relFrontier_eq_of isClosed_Icc (isClosed_Icc.union isClosed_Icc)
    (K := Icc 0 4 ∪ Icc 6 10) ?_ ?_ ?_ ?_
  · rintro y ⟨⟨h1, h2⟩, h3⟩; simp only [p208A2, mem_Icc, not_and, not_le] at h3
    by_cases h : y ≤ 4
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨by push_neg at h; linarith [h3 h.le], h2⟩
  · rintro y ⟨⟨h1, h2⟩, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩
    · exact Or.inl (by linarith)
    · exact Or.inr (by simp only [mem_singleton_iff]; linarith)
  · rintro y (rfl | rfl) <;> simp only [p208A2, mem_Icc] <;> norm_num
  · rintro p (rfl | rfl)
    · refine ⟨3, 4, by norm_num, Or.inr rfl, ?_⟩
      rintro y ⟨h1, h2⟩
      simp only [p208G, p208A2, mem_diff, mem_Icc, not_and, not_le]
      exact ⟨⟨by linarith, by linarith⟩, fun h => by linarith⟩
    · refine ⟨6, 7, by norm_num, Or.inl rfl, ?_⟩
      rintro y ⟨h1, h2⟩
      simp only [p208G, p208A2, mem_diff, mem_Icc, not_and, not_le]
      exact ⟨⟨by linarith, by linarith⟩, fun _ => by linarith⟩

theorem p208_rf_G : relFrontier p208G p208G = ∅ := by
  simp [relFrontier]

theorem p208_rf_P1 : relFrontier p208G p208P1 = {1, 2, 11/2} := by
  refine relFrontier_eq_of (isClosed_Icc.union isClosed_Icc) (isClosed_Icc.union isClosed_Icc)
    (K := Icc 0 1 ∪ Icc 2 (11/2)) ?_ ?_ ?_ ?_
  · rintro y ⟨⟨h1, h2⟩, h3⟩
    simp only [p208P1, mem_union, mem_Icc, not_or, not_and, not_le] at h3
    by_cases h : y ≤ 1
    · exact Or.inl ⟨h1, h⟩
    · push_neg at h
      refine Or.inr ⟨(h3.1 h.le).le, ?_⟩
      by_contra h'; push_neg at h'; linarith [h3.2 h'.le]
  · rintro y ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
    · linarith
    · exact Or.inr (Or.inr (by simp only [mem_singleton_iff]; linarith))
  · rintro y (rfl | rfl | rfl) <;> simp only [p208P1, mem_union, mem_Icc] <;> norm_num
  · rintro p (rfl | rfl | rfl)
    · refine ⟨1/2, 1, by norm_num, Or.inr rfl, ?_⟩
      rintro y ⟨h1, h2⟩
      simp only [p208G, p208P1, mem_diff, mem_union, mem_Icc, not_or, not_and, not_le]
      exact ⟨⟨by linarith, by linarith⟩, fun h => by linarith, fun h => by linarith⟩
    · refine ⟨2, 3, by norm_num, Or.inl rfl, ?_⟩
      rintro y ⟨h1, h2⟩
      simp only [p208G, p208P1, mem_diff, mem_union, mem_Icc, not_or, not_and, not_le]
      exact ⟨⟨by linarith, by linarith⟩, fun _ => by linarith, fun h => by linarith⟩
    · refine ⟨5, 11/2, by norm_num, Or.inr rfl, ?_⟩
      rintro y ⟨h1, h2⟩
      simp only [p208G, p208P1, mem_diff, mem_union, mem_Icc, not_or, not_and, not_le]
      exact ⟨⟨by linarith, by linarith⟩, fun _ => by linarith, fun h => by linarith⟩

theorem p208_rf_P2 : relFrontier p208G p208P2 = {1, 2, 11/2, 6} := by
  refine relFrontier_eq_of (isClosed_Icc.union isClosed_Icc)
    ((isClosed_Icc.union isClosed_Icc).union isClosed_Icc)
    (K := Icc 0 1 ∪ Icc 2 (11/2) ∪ Icc 6 10) ?_ ?_ ?_ ?_
  · rintro y ⟨⟨h1, h2⟩, h3⟩
    simp only [p208P2, mem_union, mem_Icc, not_or, not_and, not_le] at h3
    by_cases h : y ≤ 1
    · exact Or.inl (Or.inl ⟨h1, h⟩)
    · push_neg at h
      by_cases h' : y ≤ 11/2
      · exact Or.inl (Or.inr ⟨(h3.1 h.le).le, h'⟩)
      · push_neg at h'
        exact Or.inr ⟨(h3.2 h'.le).le, h2⟩
  · rintro y ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, (⟨h3, h4⟩ | ⟨h3, h4⟩) | ⟨h3, h4⟩⟩
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
    · linarith
    · linarith
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (by simp only [mem_singleton_iff]; linarith)))
  · rintro y (rfl | rfl | rfl | rfl) <;> simp only [p208P2, mem_union, mem_Icc] <;> norm_num
  · rintro p (rfl | rfl | rfl | rfl)
    · refine ⟨1/2, 1, by norm_num, Or.inr rfl, ?_⟩
      rintro y ⟨h1, h2⟩
      simp only [p208G, p208P2, mem_diff, mem_union, mem_Icc, not_or, not_and, not_le]
      exact ⟨⟨by linarith, by linarith⟩, fun h => by linarith, fun h => by linarith⟩
    · refine ⟨2, 3, by norm_num, Or.inl rfl, ?_⟩
      rintro y ⟨h1, h2⟩
      simp only [p208G, p208P2, mem_diff, mem_union, mem_Icc, not_or, not_and, not_le]
      exact ⟨⟨by linarith, by linarith⟩, fun _ => by linarith, fun h => by linarith⟩
    · refine ⟨5, 11/2, by norm_num, Or.inr rfl, ?_⟩
      rintro y ⟨h1, h2⟩
      simp only [p208G, p208P2, mem_diff, mem_union, mem_Icc, not_or, not_and, not_le]
      exact ⟨⟨by linarith, by linarith⟩, fun _ => by linarith, fun h => by linarith⟩
    · refine ⟨6, 7, by norm_num, Or.inl rfl, ?_⟩
      rintro y ⟨h1, h2⟩
      simp only [p208G, p208P2, mem_diff, mem_union, mem_Icc, not_or, not_and, not_le]
      exact ⟨⟨by linarith, by linarith⟩, fun _ => by linarith, fun _ => by linarith⟩

def p208T (i : ℕ) : Set (ℝ × ℝ) :=
  if i = 1 then p208A1 ×ˢ {1/2} else if i = 2 then p208A2 ×ˢ {1/2}
  else if i = 3 then p208G ×ˢ {1/2} else ∅
def p208α (i : ℕ) : Set (ℝ × ℝ) := if i = 2 then ({4} : Set ℝ) ×ˢ {1/2} else ∅
def p208γ : Set (ℝ × ℝ) := ({6} : Set ℝ) ×ˢ {1/2}
def p208PP1 : Set (ℝ × ℝ) := p208P1 ×ˢ {1/2}
def p208PP2 : Set (ℝ × ℝ) := p208P2 ×ˢ {1/2}
def p208S : Set (ℝ × ℝ) := (⋃ i ∈ Icc 1 3, p208T i) ∪ p208PP1 ∪ p208PP2

theorem p208_half : (1/2 : ℝ) ∈ Icc (0:ℝ) 1 := by norm_num

theorem isPLGraph_p208G : IsPLGraph p208G := isPLGraph_Icc (by norm_num)
theorem isPLGraph_p208A1 : IsPLGraph p208A1 := isPLGraph_Icc (by norm_num)
theorem isPLGraph_p208A2 : IsPLGraph p208A2 := isPLGraph_Icc (by norm_num)
theorem isPLGraph_p208P1 : IsPLGraph p208P1 := (isPLGraph_Icc (by norm_num)).union (isPLGraph_Icc (by norm_num))
theorem isPLGraph_p208P2 : IsPLGraph p208P2 := (isPLGraph_Icc (by norm_num)).union (isPLGraph_Icc (by norm_num))

theorem p208A1_sub : p208A1 ⊆ p208G := Icc_subset_Icc (by norm_num) le_rfl
theorem p208A2_sub : p208A2 ⊆ p208G := Icc_subset_Icc (by norm_num) (by norm_num)
theorem p208P1_sub : p208P1 ⊆ p208G :=
  union_subset (Icc_subset_Icc (by norm_num) (by norm_num)) (Icc_subset_Icc (by norm_num) le_rfl)
theorem p208P2_sub : p208P2 ⊆ p208G :=
  union_subset (Icc_subset_Icc (by norm_num) (by norm_num)) (Icc_subset_Icc (by norm_num) (by norm_num))

theorem p208T1 : p208T 1 = p208A1 ×ˢ {1/2} := by simp [p208T]
theorem p208T2 : p208T 2 = p208A2 ×ˢ {1/2} := by simp [p208T]
theorem p208T3 : p208T 3 = p208G ×ˢ {1/2} := by simp [p208T]
theorem p208α2 : p208α 2 = ({4} : Set ℝ) ×ˢ {1/2} := by simp [p208α]
theorem p208α_ne {i : ℕ} (h : i ≠ 2) : p208α i = ∅ := by simp [p208α, h]

theorem endSet_p208T1 : endSet p208G (p208T 1) = ({4} : Set ℝ) ×ˢ {1/2} := by
  rw [p208T1, endSet_prod_single (A := p208A1) isClosed_Icc, p208_rf_A1]
theorem endSet_p208T2 : endSet p208G (p208T 2) = ({4, 6} : Set ℝ) ×ˢ {1/2} := by
  rw [p208T2, endSet_prod_single (A := p208A2) isClosed_Icc, p208_rf_A2]
theorem endSet_p208T3 : endSet p208G (p208T 3) = ∅ := by
  rw [p208T3, endSet_prod_single (A := p208G) isClosed_Icc, p208_rf_G, empty_prod]
theorem endSet_p208PP1 : endSet p208G p208PP1 = ({1, 2, 11/2} : Set ℝ) ×ˢ {1/2} := by
  rw [p208PP1, endSet_prod_single (A := p208P1) (isClosed_Icc.union isClosed_Icc), p208_rf_P1]
theorem endSet_p208PP2 : endSet p208G p208PP2 = ({1, 2, 11/2, 6} : Set ℝ) ×ˢ {1/2} := by
  rw [p208PP2, endSet_prod_single (A := p208P2) (isClosed_Icc.union isClosed_Icc), p208_rf_P2]

theorem disj_single_prod {a b c : ℝ} (h : a ≠ b) :
    Disjoint (({a} : Set ℝ) ×ˢ ({c} : Set ℝ)) (({b} : Set ℝ) ×ˢ ({c} : Set ℝ)) :=
  disjoint_prod.2 (Or.inl (disjoint_singleton.2 h))

theorem gens_ordinary {B : Set ℝ} (hB : B ⊆ Ioo 0 10) : ∀ x ∈ B, IsOrdinaryPt p208G x :=
  fun _ hx => isOrdinaryPt_Icc (hB hx)

/-- **Commission 196 §4**: the certificate for p. 208. -/
theorem ho16_p208_false :
    ∃ (G : Set ℝ) (S : Set (ℝ × ℝ)) (T α : ℕ → Set (ℝ × ℝ)) (γ P₁ P₂ : Set (ℝ × ℝ)) (x : ℝ),
      IsPLGraph G ∧ IsConnected G ∧ IsBrokenStairwellStr G S 3 2 T α γ P₁ P₂ ∧ γ.Nonempty ∧
      (endSet G P₁).Nonempty ∧ x ∈ Prod.fst '' P₂ \ Prod.fst '' T 2 ∧
      (relFrontier G (connectedComponentIn (G \ Prod.fst '' T 2) x) ∩
        Prod.fst '' α 2).Nonempty := by
  have hfT1 : Prod.fst '' p208T 1 = p208A1 := by rw [p208T1, fst_image_prod_single]
  have hfT2 : Prod.fst '' p208T 2 = p208A2 := by rw [p208T2, fst_image_prod_single]
  have hfT3 : Prod.fst '' p208T 3 = p208G := by rw [p208T3, fst_image_prod_single]
  have hfα2 : Prod.fst '' p208α 2 = {4} := by rw [p208α2, fst_image_prod_single]
  have hfγ : Prod.fst '' p208γ = {6} := by rw [p208γ, fst_image_prod_single]
  have hfP1 : Prod.fst '' p208PP1 = p208P1 := by rw [p208PP1, fst_image_prod_single]
  have hfP2 : Prod.fst '' p208PP2 = p208P2 := by rw [p208PP2, fst_image_prod_single]
  have hfE1 : Prod.fst '' endSet p208G p208PP1 = {1, 2, 11/2} := by
    rw [endSet_p208PP1, fst_image_prod_single]
  have hα1 : p208α 1 = ∅ := p208α_ne (by norm_num)
  have hα3 : p208α 3 = ∅ := p208α_ne (by norm_num)
  have hα4 : p208α 4 = ∅ := p208α_ne (by norm_num)
  have hG := isPLGraph_p208G
  refine ⟨p208G, p208S, p208T, p208α, p208γ, p208PP1, p208PP2, 3/2, hG, isConnected_Icc (by norm_num),
    ⟨by norm_num, by norm_num, ?S1, ?P1ne, ?P1s, ?P2ne, ?P2s, rfl, ?S2, ?S2a, ?S2b, ?S2c, ?S2d,
      ?fin, ?finγ, hα1, hα4, ?EP2, ?EP12, ?S3, ?S3P, ?S3W, ?S4, ?S4γ, ?S4P, ?S4Pγ, ?S5, ?S6⟩,
    ?γne, ?E1ne, ?xmem, ?front⟩
  case S1 =>
    intro i hi
    obtain ⟨h1, h3⟩ := hi
    interval_cases i
    · rw [p208T1]; exact ⟨⟨(4, 1/2), by simp [p208A1]; norm_num⟩,
        isStraight_prod_single p208_half p208A1_sub isPLGraph_p208A1⟩
    · rw [p208T2]; exact ⟨⟨(4, 1/2), by simp [p208A2]; norm_num⟩,
        isStraight_prod_single p208_half p208A2_sub isPLGraph_p208A2⟩
    · rw [p208T3]; exact ⟨⟨(4, 1/2), by simp [p208G]; norm_num⟩,
        isStraight_prod_single p208_half subset_rfl hG⟩
  case P1ne => exact ⟨(1, 1/2), by simp [p208PP1, p208P1]⟩
  case P1s => exact isStraight_prod_single p208_half p208P1_sub isPLGraph_p208P1
  case P2ne => exact ⟨(1, 1/2), by simp [p208PP2, p208P2]⟩
  case P2s => exact isStraight_prod_single p208_half p208P2_sub isPLGraph_p208P2
  case S2 =>
    intro i hi hi2
    obtain ⟨h1, h3⟩ := hi
    interval_cases i
    · rw [endSet_p208T1, hα1, p208α2, empty_union]; exact ⟨rfl, empty_disjoint _⟩
    · exact absurd rfl hi2
    · rw [endSet_p208T3, hα3, hα4, union_empty]; exact ⟨rfl, disjoint_empty _⟩
  case S2a =>
    rw [endSet_p208T2, p208α2, hα3, union_empty, p208γ, ← union_prod]
    rfl
  case S2b => rw [hα3]; exact disjoint_empty _
  case S2c => rw [p208α2, p208γ]; exact disj_single_prod (by norm_num)
  case S2d => rw [hα3]; exact empty_disjoint _
  case fin =>
    intro i _
    by_cases h : i = 2
    · subst h; rw [p208α2]; exact (finite_singleton _).prod (finite_singleton _)
    · rw [p208α_ne h]; exact finite_empty
  case finγ => exact (finite_singleton _).prod (finite_singleton _)
  case EP2 =>
    rw [endSet_p208PP2, endSet_p208PP1, p208γ, ← union_prod]
    congr 1
    ext y; simp only [mem_insert_iff, mem_singleton_iff, mem_union]; tauto
  case EP12 =>
    rw [endSet_p208PP1, p208γ]
    refine disjoint_prod.2 (Or.inl ?_)
    simp only [disjoint_singleton_right, mem_insert_iff, mem_singleton_iff]
    norm_num
  case S3 =>
    intro i hi
    obtain ⟨h1, h3⟩ := hi
    interval_cases i
    · refine ⟨Ioo 3 5, ?_, ?_⟩
      · rw [p208α2, fst_image_prod_single]
        exact isOpen_Ioo.mem_nhdsSet.2 (singleton_subset_iff.2 ⟨by norm_num, by norm_num⟩)
      · rw [hfT1, hfT2]
        ext y; simp only [p208A1, p208A2, mem_inter_iff, mem_Icc, mem_Ioo]
        constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> exact ⟨⟨h1, by linarith⟩, h3, h4⟩
    · refine ⟨∅, ?_, by rw [inter_empty, inter_empty]⟩
      rw [hα3, image_empty, nhdsSet_empty]; exact Filter.mem_bot
  case S3P =>
    refine ⟨Ioo (1/2) (23/4), ?_, ?_⟩
    · rw [hfE1]
      refine isOpen_Ioo.mem_nhdsSet.2 ?_
      rintro y (rfl | rfl | rfl) <;> constructor <;> norm_num
    · rw [hfP1, hfP2]
      ext y; simp only [p208P1, p208P2, mem_inter_iff, mem_union, mem_Icc, mem_Ioo]
      constructor
      · rintro ⟨h | ⟨h1, h2⟩, h3, h4⟩
        · exact ⟨Or.inl h, h3, h4⟩
        · exact ⟨Or.inr ⟨h1, by linarith⟩, h3, h4⟩
      · rintro ⟨h | ⟨h1, h2⟩, h3, h4⟩
        · exact ⟨Or.inl h, h3, h4⟩
        · exact ⟨Or.inr ⟨h1, by linarith⟩, h3, h4⟩
  case S3W =>
    refine ⟨Ioo (23/4) 7, ?_, ?_⟩
    · rw [hfγ]
      exact isOpen_Ioo.mem_nhdsSet.2 (singleton_subset_iff.2 ⟨by norm_num, by norm_num⟩)
    · rw [hfP2, hfT2]
      ext y; simp only [p208A2, p208P2, mem_inter_iff, mem_union, mem_Icc, mem_Ioo]
      constructor
      · rintro ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, h3, h4⟩
        · linarith
        · exact ⟨⟨by linarith, h2⟩, h3, h4⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨Or.inr ⟨by linarith, h2⟩, h3, h4⟩
  case S4 =>
    intro i hi
    obtain ⟨h1, h3⟩ := hi
    interval_cases i
    · rw [hα1, image_empty, hfT1, p208α2, fst_image_prod_single]
      refine ⟨hasConsCompl_empty _ _, hasConsCompl_of_gaps hG isClosed_Icc ?_⟩
      rintro x ⟨⟨hx0, hx10⟩, hxA⟩
      simp only [p208A1, mem_Icc, not_and, not_le] at hxA
      have hx4 : x < 4 := by by_contra h; push_neg at h; linarith [hxA h]
      refine ⟨-1, 4, by linarith, hx4, fun h => by linarith [h.1.1], fun h => h.2 ⟨le_rfl, by norm_num⟩, Or.inl ?_⟩
      rintro y ⟨⟨h1, -⟩, -, h2⟩
      exact le_antisymm h2 h1
    · rw [hfT2, p208α2, fst_image_prod_single, hα3, image_empty]
      refine ⟨hasConsCompl_of_gaps hG isClosed_Icc ?_, hasConsCompl_empty _ _⟩
      rintro x ⟨⟨hx0, hx10⟩, hxA⟩
      simp only [p208A2, mem_Icc, not_and, not_le] at hxA
      by_cases hx4 : x < 4
      · refine ⟨-1, 4, by linarith, hx4, fun h => by linarith [h.1.1], fun h => h.2 ⟨le_rfl, by norm_num⟩, Or.inl ?_⟩
        rintro y ⟨⟨h1, -⟩, -, h2⟩
        exact le_antisymm h2 h1
      · push_neg at hx4
        have hx6 := hxA hx4
        refine ⟨6, 11, hx6, by linarith, fun h => h.2 ⟨by norm_num, le_rfl⟩, fun h => by linarith [h.1.2], Or.inr ?_⟩
        rw [disjoint_singleton_right]
        rintro ⟨-, h, -⟩
        linarith
    · rw [hα3, hα4, image_empty]
      exact ⟨hasConsCompl_empty _ _, hasConsCompl_empty _ _⟩
  case S4γ =>
    rw [hfT2, hfγ]
    refine hasConsCompl_of_gaps hG isClosed_Icc ?_
    rintro x ⟨⟨hx0, hx10⟩, hxA⟩
    simp only [p208A2, mem_Icc, not_and, not_le] at hxA
    by_cases hx4 : x < 4
    · refine ⟨-1, 4, by linarith, hx4, fun h => by linarith [h.1.1], fun h => h.2 ⟨le_rfl, by norm_num⟩, Or.inr ?_⟩
      rw [disjoint_singleton_right]
      rintro ⟨-, -, h⟩
      linarith
    · push_neg at hx4
      have hx6 := hxA hx4
      refine ⟨6, 11, hx6, by linarith, fun h => h.2 ⟨by norm_num, le_rfl⟩, fun h => by linarith [h.1.2], Or.inl ?_⟩
      rintro y ⟨⟨-, h1⟩, h2, -⟩
      exact le_antisymm h1 h2
  case S4P =>
    rw [hfP2, hfE1]
    refine hasConsCompl_of_gaps hG (isClosed_Icc.union isClosed_Icc) ?_
    rintro x ⟨⟨hx0, hx10⟩, hxA⟩
    simp only [p208P2, mem_union, mem_Icc, not_or, not_and, not_le] at hxA
    by_cases hx1 : x < 1
    · refine ⟨-1, 1, by linarith, hx1, fun h => by linarith [h.1.1],
        fun h => h.2 (Or.inl ⟨le_rfl, by norm_num⟩), Or.inl ?_⟩
      rintro y ⟨⟨h1, -⟩ | ⟨h1, -⟩, -, h2⟩
      · exact Or.inl (le_antisymm h2 h1)
      · linarith
    · push_neg at hx1
      have hx2 := hxA.1 hx1
      by_cases hx5 : x < 11/2
      · refine ⟨2, 11/2, hx2, hx5, fun h => h.2 (Or.inl ⟨by norm_num, le_rfl⟩),
          fun h => h.2 (Or.inr ⟨le_rfl, by norm_num⟩), Or.inl ?_⟩
        rintro y ⟨⟨-, h1⟩ | ⟨h1, -⟩, h2, h3⟩
        · exact Or.inr (Or.inl (le_antisymm h1 h2))
        · exact Or.inr (Or.inr (le_antisymm h3 h1))
      · push_neg at hx5
        have hx6 := hxA.2 hx5
        refine ⟨6, 11, hx6, by linarith, fun h => h.2 (Or.inr ⟨by norm_num, le_rfl⟩),
          fun h => by linarith [h.1.2], Or.inr ?_⟩
        rw [Set.disjoint_left]
        rintro y ⟨⟨-, h1⟩ | ⟨-, h1⟩, h2, -⟩ hy
        · linarith
        · simp only [mem_insert_iff, mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl <;> norm_num at h1 h2
  case S4Pγ =>
    rw [hfP2, hfγ]
    refine hasConsCompl_of_gaps hG (isClosed_Icc.union isClosed_Icc) ?_
    rintro x ⟨⟨hx0, hx10⟩, hxA⟩
    simp only [p208P2, mem_union, mem_Icc, not_or, not_and, not_le] at hxA
    by_cases hx1 : x < 1
    · refine ⟨-1, 1, by linarith, hx1, fun h => by linarith [h.1.1],
        fun h => h.2 (Or.inl ⟨le_rfl, by norm_num⟩), Or.inr ?_⟩
      rw [disjoint_singleton_right]
      rintro ⟨-, -, h⟩
      linarith
    · push_neg at hx1
      have hx2 := hxA.1 hx1
      by_cases hx5 : x < 11/2
      · refine ⟨2, 11/2, hx2, hx5, fun h => h.2 (Or.inl ⟨by norm_num, le_rfl⟩),
          fun h => h.2 (Or.inr ⟨le_rfl, by norm_num⟩), Or.inr ?_⟩
        rw [disjoint_singleton_right]
        rintro ⟨-, -, h⟩
        linarith
      · push_neg at hx5
        have hx6 := hxA.2 hx5
        refine ⟨6, 11, hx6, by linarith, fun h => h.2 (Or.inr ⟨by norm_num, le_rfl⟩),
          fun h => by linarith [h.1.2], Or.inl ?_⟩
        rintro y ⟨⟨-, h1⟩ | ⟨-, h1⟩, h2, -⟩
        · linarith
        · exact le_antisymm h1 h2
  case S5 =>
    have hl : (((List.range' 2 (3 - 1)).map fun i => Prod.fst '' p208α i) ++
        [Prod.fst '' endSet p208G p208PP1, Prod.fst '' p208γ]) = [{4}, ∅, {1, 2, 11/2}, {6}] := by
      rw [hfE1, hfγ]
      simp [List.range', hfα2, hα3]
    rw [hl]
    refine ⟨?_, ?_⟩
    · intro B hB
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
      rcases hB with rfl | rfl | rfl | rfl
      · refine ⟨finite_singleton _, ?_, gens_ordinary ?_⟩ <;>
          rintro y rfl <;> simp [p208G] <;> norm_num
      · exact ⟨finite_empty, empty_subset _, fun x hx => absurd hx (notMem_empty x)⟩
      · refine ⟨by simp, ?_, gens_ordinary ?_⟩ <;>
          rintro y (rfl | rfl | rfl) <;> simp [p208G] <;> norm_num
      · refine ⟨finite_singleton _, ?_, gens_ordinary ?_⟩ <;>
          rintro y rfl <;> simp [p208G] <;> norm_num
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
      refine ⟨⟨disjoint_empty _, ?_, ?_⟩, ⟨empty_disjoint _, empty_disjoint _⟩, ?_⟩
      · simp only [disjoint_singleton_left, mem_insert_iff, mem_singleton_iff]; norm_num
      · simp only [disjoint_singleton_left, mem_singleton_iff]; norm_num
      · simp only [disjoint_singleton_right, mem_insert_iff, mem_singleton_iff]; norm_num
  case S6 =>
    rw [hfα2, image_union, hfP1, hfP2, disjoint_singleton_left]
    simp only [p208P1, p208P2, mem_union, mem_Icc]
    norm_num
  case γne => exact ⟨(6, 1/2), by simp [p208γ]⟩
  case E1ne => exact ⟨(1, 1/2), by rw [endSet_p208PP1]; simp⟩
  case xmem =>
    rw [hfP2, hfT2]
    simp only [p208P2, p208A2, mem_diff, mem_union, mem_Icc]
    norm_num
  case front =>
    rw [hfT2, hfα2]
    refine ⟨4, ⟨?_, ?_⟩, rfl⟩
    · have hsub : Ico 0 4 ⊆ connectedComponentIn (p208G \ p208A2) (3/2) := by
        refine isPreconnected_Ico.subset_connectedComponentIn ⟨by norm_num, by norm_num⟩ ?_
        rintro y ⟨h1, h2⟩
        simp only [p208G, p208A2, mem_diff, mem_Icc, not_and, not_le]
        exact ⟨⟨h1, by linarith⟩, fun h => by linarith⟩
      refine closure_mono hsub ?_
      rw [closure_Ico (by norm_num)]
      exact ⟨by norm_num, le_rfl⟩
    · refine subset_closure ⟨by simp [p208G]; norm_num, fun h => ?_⟩
      have := comp_subset_Ioo (G := p208G) (A := p208A2) (l := -1) (r := 4)
        (fun h => by linarith [h.1.1]) (fun h => h.2 ⟨le_rfl, by norm_num⟩)
        (by norm_num) (by norm_num) h
      exact lt_irrefl _ this.2

end HPC.HO16
