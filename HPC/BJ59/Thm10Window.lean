import HPC.BJ59.Thm10Lib
import HPC.BJ59.Thm5
import HPC.BJ59.Transfer
import HPC.BJ59.Arc
import HPC.Plane.Theorem11

/-!
# Batch 201, §3: windows (Step 2(c), p. 185)

`exists_window_set` and `bj_theorem5_window` (statements as in the skeleton).
Route: commission 201 §3.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

section SubArc

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]

/-- The affine map of `[a, b]` onto `[0, 1]`, clamped. -/
noncomputable def winScale (a b : unitInterval) : unitInterval → unitInterval :=
  fun s => Set.projIcc 0 1 zero_le_one (((s : ℝ) - a) / ((b : ℝ) - a))

/-- The affine map of `[0, 1]` onto `[a, b]`. -/
def winInv (a b : unitInterval) (hab : a ≤ b) : unitInterval → unitInterval :=
  fun s => ⟨(a : ℝ) + s * ((b : ℝ) - a), by
    have h1 : (a : ℝ) ≤ b := hab
    have h2 := s.2.1; have h3 := s.2.2; have h4 := a.2.1; have h5 := b.2.2
    constructor <;> nlinarith⟩

theorem winInv_mem {a b : unitInterval} (hab : a ≤ b) (s : unitInterval) :
    winInv a b hab s ∈ Icc a b := by
  have h1 : (a : ℝ) ≤ b := hab
  have h2 := s.2.1; have h3 := s.2.2
  constructor
  · show (a : ℝ) ≤ (a : ℝ) + s * ((b : ℝ) - a); nlinarith
  · show (a : ℝ) + s * ((b : ℝ) - a) ≤ b; nlinarith

theorem continuous_winInv {a b : unitInterval} (hab : a ≤ b) : Continuous (winInv a b hab) :=
  Continuous.subtype_mk (continuous_const.add (continuous_subtype_val.mul continuous_const)) _

theorem continuous_winScale (a b : unitInterval) : Continuous (winScale a b) :=
  continuous_projIcc.comp ((continuous_subtype_val.sub continuous_const).div_const _)

/-- On `[a, b]`, `winScale` and `winInv` are inverse. -/
theorem winScale_eq_iff {a b : unitInterval} (hab : a < b) {s : unitInterval} (hs : s ∈ Icc a b)
    (s' : unitInterval) : winScale a b s = s' ↔ s = winInv a b hab.le s' := by
  have h1 : (a : ℝ) < b := hab
  have hs1 : (a : ℝ) ≤ s := hs.1
  have hs2 : (s : ℝ) ≤ b := hs.2
  have hval : ((winScale a b s : unitInterval) : ℝ) = ((s : ℝ) - a) / ((b : ℝ) - a) := by
    simp only [winScale]
    rw [Set.projIcc_of_mem]
    constructor
    · exact div_nonneg (by linarith) (by linarith)
    · rw [div_le_one (by linarith)]; linarith
  constructor
  · intro h
    apply Subtype.ext
    show (s : ℝ) = (a : ℝ) + s' * ((b : ℝ) - a)
    rw [← h, hval]
    have hne : (b : ℝ) - a ≠ 0 := by linarith
    rw [div_mul_cancel₀ _ hne]; ring
  · intro h
    apply Subtype.ext
    rw [hval, h]
    show ((a : ℝ) + s' * ((b : ℝ) - a) - a) / ((b : ℝ) - a) = s'
    have hne : (b : ℝ) - a ≠ 0 := by linarith
    rw [show (a : ℝ) + s' * ((b : ℝ) - a) - a = s' * ((b : ℝ) - a) by ring, mul_div_cancel_right₀ _ hne]

theorem winScale_winInv {a b : unitInterval} (hab : a < b) (s' : unitInterval) :
    winScale a b (winInv a b hab.le s') = s' :=
  (winScale_eq_iff hab (winInv_mem hab.le s') s').2 rfl

/-- **Transfer to a window**: `g ⁻¹' [a, b]`, with `g` rescaled to `[0, 1]`, is again a
continuous snake-like arc of pseudo-arcs. -/
theorem window_transfer {g : Y → unitInterval} (hg : IsContArcPA g)
    (hS : IsSnakeLike (univ : Set Y)) {a b : unitInterval} (hab : a < b) :
    CompactSpace (g ⁻¹' Icc a b) ∧
      (∀ s' : unitInterval, Subtype.val '' ((fun y : g ⁻¹' Icc a b => winScale a b (g y)) ⁻¹'
        {s'}) = g ⁻¹' {winInv a b hab.le s'}) ∧
      IsContArcPA (fun y : g ⁻¹' Icc a b => winScale a b (g y)) ∧
      IsSnakeLike (univ : Set (g ⁻¹' Icc a b)) := by
  have hQc : IsCompact (g ⁻¹' Icc a b) := (isClosed_Icc.preimage hg.1).isCompact
  haveI hcs : CompactSpace (g ⁻¹' Icc a b) := isCompact_iff_compactSpace.1 hQc
  set g' : g ⁻¹' Icc a b → unitInterval := fun y => winScale a b (g y) with hg'
  have hfib : ∀ s' : unitInterval, Subtype.val '' (g' ⁻¹' {s'}) =
      g ⁻¹' {winInv a b hab.le s'} := by
    intro s'
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      simp only [mem_preimage, mem_singleton_iff, hg'] at hy' ⊢
      exact (winScale_eq_iff hab y'.2 s').1 hy'
    · intro hy
      simp only [mem_preimage, mem_singleton_iff] at hy
      have hyQ : y ∈ g ⁻¹' Icc a b := by
        simp only [mem_preimage, hy]; exact winInv_mem hab.le s'
      exact ⟨⟨y, hyQ⟩, by
        simp only [mem_preimage, mem_singleton_iff, hg']
        exact (winScale_eq_iff hab hyQ s').2 hy, rfl⟩
  refine ⟨hcs, hfib, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (continuous_winScale a b).comp (hg.1.comp continuous_subtype_val)
  · intro V hV
    obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hV
    have : g' '' (Subtype.val ⁻¹' W) = winInv a b hab.le ⁻¹' (g '' W) := by
      ext s'
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y, hy, ?_⟩
        exact ((winScale_eq_iff hab y.2 (g' y)).1 rfl)
      · rintro ⟨y, hyW, hy⟩
        have hyQ : y ∈ g ⁻¹' Icc a b := by
          simp only [mem_preimage, hy]; exact winInv_mem hab.le s'
        exact ⟨⟨y, hyQ⟩, hyW, (winScale_eq_iff hab hyQ s').2 hy⟩
    rw [this]
    exact (hg.2.1 W hW).preimage (continuous_winInv hab.le)
  · intro s'
    obtain ⟨y, hy⟩ := hg.2.2.1 (winInv a b hab.le s')
    have hyQ : y ∈ g ⁻¹' Icc a b := by simp only [mem_preimage, hy]; exact winInv_mem hab.le s'
    exact ⟨⟨y, hyQ⟩, (winScale_eq_iff hab hyQ s').2 hy⟩
  · intro s'
    apply isPseudoArc_subtype_of_image
    rw [hfib s']
    exact hg.2.2.2 _
  · have hQcont : Fold.Q78.IsContinuum (g ⁻¹' Icc a b) := by
      refine ⟨hQc, ?_, ?_⟩
      · obtain ⟨y, hy⟩ := hg.2.2.1 a
        exact ⟨y, by simp only [mem_preimage, hy]; exact ⟨le_rfl, hab.le⟩⟩
      · exact isPreconnected_preimage_Icc hg.1 hg.2.2.1
          (fun t => (hg.2.2.2 t).1.1.2.isPreconnected) a b
    exact isSnakeLike_univ_of_isSnakeLike (isSnakeLike_of_subcontinuum hS hQcont (subset_univ _))

/-- `bj_theorem5_window` when the run ends inside the chain (`u < N`). -/
theorem bj_theorem5_window_aux {g : Y → unitInterval} (hg : IsContArcPA g)
    (hS : IsSnakeLike (univ : Set Y)) {a b : unitInterval} (hab : a < b) {N : ℕ}
    (F : Chain Y N) {t u : ℕ} (htu : t ≤ u) (huN : u < N)
    (hTf : ∀ s ∈ Icc a b, ∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ g ⁻¹' {s}).Nonempty)
    (hTc : g ⁻¹' Icc a b ⊆ ⋃ (k : Fin N) (_ : t ≤ k.val ∧ k.val ≤ u), F.link k)
    {U : Set Y} (hU : IsOpen U) (hUne : U.Nonempty) (hUab : U ⊆ g ⁻¹' Ioo a b)
    (hFU : ∀ s ∈ Icc a b, ∀ k : Fin N, t ≤ k.val → k.val ≤ u →
      ¬ F.link k ∩ g ⁻¹' {s} ⊆ closure U) :
    ∃ A B : Set Y, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧ A ∪ B = Uᶜ ∧
      g ⁻¹' Icc 0 a ⊆ A ∧ g ⁻¹' Icc b 1 ⊆ B ∧ ∀ s ∈ Icc a b,
        (∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ (A ∩ g ⁻¹' {s})).Nonempty) ∨
          (∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ (B ∩ g ⁻¹' {s})).Nonempty) := by
  classical
  obtain ⟨hcs, hfib, hg', hSQ⟩ := window_transfer hg hS hab
  obtain ⟨g', hg'def⟩ : ∃ g' : g ⁻¹' Icc a b → unitInterval,
      g' = fun y => winScale a b (g y.1) := ⟨_, rfl⟩
  rw [← hg'def] at hfib hg'
  have hind : ∀ s', Fold.Q78.IsIndecomposable (g' ⁻¹' {s'}) :=
    fun s' => (hg'.2.2.2 s').2.1 _ subset_rfl (hg'.2.2.2 s').1.1
  have hf : IsArcOfContinua g' := ⟨hg'.1, hg'.2.2.1, fun s' => (hg'.2.2.2 s').1.1⟩
  have hg'eq : ∀ (x : g ⁻¹' Icc a b) (s' : unitInterval), g' x = s' ↔
      g x.1 = winInv a b hab.le s' := fun x s' => by
    rw [hg'def]; exact winScale_eq_iff hab x.2 s'
  have hval0 : ((winInv a b hab.le 0 : unitInterval) : ℝ) = a := by
    show (a : ℝ) + ((0 : unitInterval) : ℝ) * _ = a; simp
  have hval1 : ((winInv a b hab.le 1 : unitInterval) : ℝ) = b := by
    show (a : ℝ) + ((1 : unitInterval) : ℝ) * _ = b; simp
  -- the run as a chain on the window
  let ix : Fin (u - t + 1) → Fin N := fun j => ⟨t + j.val, by omega⟩
  let L : Fin (u - t + 1) → Set (g ⁻¹' Icc a b) := fun j => Subtype.val ⁻¹' F.link (ix j)
  have hLo : ∀ j, IsOpen (L j) := fun j => (F.isOpen _).preimage continuous_subtype_val
  have hLdisj : ∀ i j : Fin (u - t + 1), 1 < ((i : ℤ) - j).natAbs → L i ∩ L j = ∅ := by
    intro i j hij
    refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
    have := (F.adjacent_iff (ix i) (ix j)).1 ⟨x.1, hx.1, hx.2⟩
    simp only [ix] at this
    omega
  have hLK : ∀ j, (L j ∩ g' ⁻¹' {0}).Nonempty := by
    intro j
    obtain ⟨y, hyF, hys⟩ := hTf _ (winInv_mem hab.le 0) (ix j) (by simp [ix]) (by simp [ix]; omega)
    have hy : y ∈ Subtype.val '' (g' ⁻¹' {0}) := by rw [hfib]; exact hys
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨y', hyF, hy'⟩
  have hKL : g' ⁻¹' {0} ⊆ ⋃ j, L j := by
    intro x _
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 (hTc x.2)
    refine mem_iUnion.2 ⟨⟨k.val - t, by omega⟩, ?_⟩
    have hix : ix ⟨k.val - t, by omega⟩ = k := Fin.ext (by simp only [ix]; omega)
    show x.1 ∈ F.link (ix _)
    rw [hix]; exact hxk
  let E : Chain (g ⁻¹' Icc a b) (u - t + 1) :=
    { link := L
      isOpen := hLo
      adjacent := by
        intro i j
        constructor
        · rintro ⟨x, hxi, hxj⟩
          have := (F.adjacent_iff (ix i) (ix j)).1 ⟨x.1, hxi, hxj⟩
          simp only [ix] at this
          omega
        · intro hij
          have hK := (hg'.2.2.2 0).1.1.2.isPreconnected
          by_cases h : i.val = j.val
          · obtain rfl : i = j := Fin.ext h
            obtain ⟨x, hx, -⟩ := hLK i
            exact ⟨x, hx, hx⟩
          · rcases (show j.val = i.val + 1 ∨ i.val = j.val + 1 by omega) with h' | h'
            · exact adjacent_meet_of_cover hK L hLo hKL hLK hLdisj i j h'
            · rw [inter_comm]; exact adjacent_meet_of_cover hK L hLo hKL hLK hLdisj j i h' }
  -- the transition set on the window
  have hU' : IsOpen (Subtype.val ⁻¹' U : Set (g ⁻¹' Icc a b)) :=
    hU.preimage continuous_subtype_val
  have hUne' : (Subtype.val ⁻¹' U : Set (g ⁻¹' Icc a b)).Nonempty := by
    obtain ⟨y, hy⟩ := hUne
    have h := hUab hy
    exact ⟨⟨y, ⟨h.1.le, h.2.le⟩⟩, hy⟩
  have hU01 : Disjoint (Subtype.val ⁻¹' U : Set (g ⁻¹' Icc a b)) (g' ⁻¹' {0, 1}) := by
    refine Set.disjoint_left.2 fun x hxU hx01 => ?_
    have h := hUab hxU
    simp only [mem_preimage, mem_Ioo] at h
    have h1 : (a : ℝ) < g x.1 := h.1
    have h2 : ((g x.1 : unitInterval) : ℝ) < b := h.2
    rcases hx01 with h0 | h0
    · rw [(hg'eq x 0).1 h0, hval0] at h1; exact lt_irrefl _ h1
    · rw [(hg'eq x 1).1 h0, hval1] at h2; exact lt_irrefl _ h2
  have hEU : ∀ s' i, ¬ E.link i ∩ g' ⁻¹' {s'} ⊆ closure (Subtype.val ⁻¹' U) := by
    intro s' i hsub
    refine hFU _ (winInv_mem hab.le s') (ix i) (by simp [ix]) (by simp [ix]; omega) ?_
    rintro y ⟨hyF, hys⟩
    have hy : y ∈ Subtype.val '' (g' ⁻¹' {s'}) := by rw [hfib]; exact hys
    obtain ⟨y', hy', rfl⟩ := hy
    exact continuous_subtype_val.closure_preimage_subset U (hsub ⟨hyF, hy'⟩)
  haveI := hcs
  obtain ⟨A', B', hA', hB', hAB', hABU', hA0', hB1', hdich'⟩ :=
    theorem5_repaired hf hg'.2.1 hSQ hind E hU' hUne' hU01 hEU
  -- the endpoints of the window
  have hto0 : ∀ x : g ⁻¹' Icc a b, ((g x.1 : unitInterval) : ℝ) ≤ a → x ∈ A' := by
    intro x hx
    apply hA0'
    show g' x = 0
    rw [hg'eq]
    exact Subtype.ext (by rw [hval0]; exact le_antisymm hx x.2.1)
  have hto1 : ∀ x : g ⁻¹' Icc a b, (b : ℝ) ≤ g x.1 → x ∈ B' := by
    intro x hx
    apply hB1'
    show g' x = 1
    rw [hg'eq]
    exact Subtype.ext (by rw [hval1]; exact le_antisymm x.2.2 hx)
  refine ⟨Subtype.val '' A' ∪ g ⁻¹' Icc 0 a, Subtype.val '' B' ∪ g ⁻¹' Icc b 1,
    (hA'.isCompact.image continuous_subtype_val).isClosed.union (isClosed_Icc.preimage hg.1),
    (hB'.isCompact.image continuous_subtype_val).isClosed.union (isClosed_Icc.preimage hg.1),
    ?_, ?_, subset_union_right, subset_union_right, ?_⟩
  · refine Set.disjoint_left.2 ?_
    rintro y (⟨y', hyA', rfl⟩ | hya) (⟨y'', hyB', hyeq⟩ | hyb)
    · obtain rfl : y'' = y' := Subtype.ext hyeq
      exact Set.disjoint_left.1 hAB' hyA' hyB'
    · exact Set.disjoint_left.1 hAB' hyA' (hto1 y' hyb.1)
    · subst hyeq
      exact Set.disjoint_left.1 hAB' (hto0 y'' hya.2) hyB'
    · have h1 : ((g y : unitInterval) : ℝ) ≤ a := hya.2
      have h2 : (b : ℝ) ≤ g y := hyb.1
      have h3 : (a : ℝ) < b := hab
      linarith
  · ext y
    constructor
    · rintro ((⟨y', hy', rfl⟩ | hya) | (⟨y', hy', rfl⟩ | hyb)) hyU
      · have : y' ∈ A' ∪ B' := Or.inl hy'
        rw [hABU'] at this; exact this hyU
      · have h := hUab hyU
        have h1 : (a : ℝ) < g y := h.1
        have h2 : ((g y : unitInterval) : ℝ) ≤ a := hya.2
        linarith
      · have : y' ∈ A' ∪ B' := Or.inr hy'
        rw [hABU'] at this; exact this hyU
      · have h := hUab hyU
        have h1 : ((g y : unitInterval) : ℝ) < b := h.2
        have h2 : (b : ℝ) ≤ g y := hyb.1
        linarith
    · intro hyU
      by_cases h1 : ((g y : unitInterval) : ℝ) ≤ a
      · exact Or.inl (Or.inr ⟨(g y).2.1, h1⟩)
      by_cases h2 : (b : ℝ) ≤ g y
      · exact Or.inr (Or.inr ⟨h2, (g y).2.2⟩)
      push_neg at h1 h2
      have hyQ : y ∈ g ⁻¹' Icc a b := ⟨h1.le, h2.le⟩
      have : (⟨y, hyQ⟩ : g ⁻¹' Icc a b) ∈ A' ∪ B' := by rw [hABU']; exact hyU
      rcases this with h | h
      · exact Or.inl (Or.inl ⟨_, h, rfl⟩)
      · exact Or.inr (Or.inl ⟨_, h, rfl⟩)
  · intro s hs
    have hss : s = winInv a b hab.le (winScale a b s) := (winScale_eq_iff hab hs _).1 rfl
    have hpt : ∀ (C : Set (g ⁻¹' Icc a b)) (k : Fin N) (_ : t ≤ k.val) (_ : k.val ≤ u),
        (E.link ⟨k.val - t, by omega⟩ ∩ (C ∩ g' ⁻¹' {winScale a b s})).Nonempty →
        (F.link k ∩ (Subtype.val '' C ∩ g ⁻¹' {s})).Nonempty := by
      rintro C k hk1 hk2 ⟨x, hxE, hxC, hxs⟩
      have hix : ix ⟨k.val - t, by omega⟩ = k := Fin.ext (by simp only [ix]; omega)
      have hxE' : x.1 ∈ F.link (ix ⟨k.val - t, by omega⟩) := hxE
      rw [hix] at hxE'
      refine ⟨x.1, hxE', ⟨x, hxC, rfl⟩, ?_⟩
      show g x.1 = s
      rw [(hg'eq x _).1 hxs, ← hss]
    rcases hdich' (winScale a b s) with h | h
    · left
      intro k hk1 hk2
      obtain ⟨y, hy1, hy2, hy3⟩ := hpt A' k hk1 hk2 (h _)
      exact ⟨y, hy1, Or.inl hy2, hy3⟩
    · right
      intro k hk1 hk2
      obtain ⟨y, hy1, hy2, hy3⟩ := hpt B' k hk1 hk2 (h _)
      exact ⟨y, hy1, Or.inl hy2, hy3⟩

/-- **Theorem 5 (repaired) on a window** `[a, b]`, extended to the whole space (Step 2(c),
p. 185). -/
theorem bj_theorem5_window {g : Y → unitInterval} (hg : IsContArcPA g)
    (hS : IsSnakeLike (univ : Set Y)) {a b : unitInterval} (hab : a < b) {N : ℕ}
    (F : Chain Y N) {t u : ℕ} (htu : t ≤ u)
    (hTf : ∀ s ∈ Icc a b, ∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ g ⁻¹' {s}).Nonempty)
    (hTc : g ⁻¹' Icc a b ⊆ ⋃ (k : Fin N) (_ : t ≤ k.val ∧ k.val ≤ u), F.link k)
    {U : Set Y} (hU : IsOpen U) (hUne : U.Nonempty) (hUab : U ⊆ g ⁻¹' Ioo a b)
    (hUF : ∃ k : Fin N, t ≤ k.val ∧ k.val ≤ u ∧ closure U ⊆ F.link k)
    (hFU : ∀ s ∈ Icc a b, ∀ k : Fin N, t ≤ k.val → k.val ≤ u →
      ¬ F.link k ∩ g ⁻¹' {s} ⊆ closure U) :
    ∃ A B : Set Y, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧ A ∪ B = Uᶜ ∧
      g ⁻¹' Icc 0 a ⊆ A ∧ g ⁻¹' Icc b 1 ⊆ B ∧ ∀ s ∈ Icc a b,
        (∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ (A ∩ g ⁻¹' {s})).Nonempty) ∨
          (∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ (B ∩ g ⁻¹' {s})).Nonempty) := by
  obtain ⟨k₀, hk₀t, hk₀u, -⟩ := hUF
  have hk₀N := k₀.isLt
  obtain ⟨A, B, hA, hB, hAB, hABU, hA0, hB1, hdich⟩ := bj_theorem5_window_aux hg hS hab F
    (u := min u (N - 1)) (by omega) (by omega)
    (fun s hs k h1 h2 => hTf s hs k h1 (by omega))
    (fun y hy => by
      obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.1 (hTc hy)
      exact mem_iUnion₂.2 ⟨k, ⟨hk.1, by have := k.isLt; omega⟩, hyk⟩)
    hU hUne hUab (fun s hs k h1 h2 => hFU s hs k h1 (by omega))
  refine ⟨A, B, hA, hB, hAB, hABU, hA0, hB1, fun s hs => ?_⟩
  rcases hdich s hs with h | h
  · exact Or.inl fun k h1 h2 => h k h1 (by have := k.isLt; omega)
  · exact Or.inr fun k h1 h2 => h k h1 (by have := k.isLt; omega)

/-- A nonempty open part of a connected non-degenerate set has two distinct points. -/
theorem exists_two_points_of_open {Z : Type*} [MetricSpace Z] {K V : Set Z}
    (hK : IsPreconnected K) (hKn : K.Nontrivial) (hV : IsOpen V) (hVK : (V ∩ K).Nonempty) :
    ∃ p ∈ V ∩ K, ∃ q ∈ V ∩ K, p ≠ q := by
  obtain ⟨p, hp⟩ := hVK
  by_contra h
  push_neg at h
  obtain ⟨q, hq, hqp⟩ := hKn.exists_ne p
  have hsep := hK V {p}ᶜ hV isOpen_compl_singleton (fun x hx => by
    by_cases hxp : x = p
    · exact Or.inl (hxp ▸ hp.1)
    · exact Or.inr hxp) ⟨p, hp.2, hp.1⟩ ⟨q, hq, hqp⟩
  obtain ⟨x, hxK, hxV, hxp⟩ := hsep
  exact hxp (h p hp x ⟨hxV, hxK⟩).symm

/-- A transition set for `bj_theorem5_window`: inside a given link of the run, over the open
window, and too small to contain the part of any link of the run in any fibre of the window. -/
theorem exists_window_set {g : Y → unitInterval} (hg : IsContArcPA g) {a b : unitInterval}
    (hab : a < b) {N : ℕ} (F : Chain Y N) {t u : ℕ}
    (hTf : ∀ s ∈ Icc a b, ∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ g ⁻¹' {s}).Nonempty)
    {y : Fin N} (hty : t ≤ y.val) (hyu : y.val ≤ u) :
    ∃ U : Set Y, IsOpen U ∧ U.Nonempty ∧ U ⊆ g ⁻¹' Ioo a b ∧ closure U ⊆ F.link y ∧
      ∀ s ∈ Icc a b, ∀ k : Fin N, t ≤ k.val → k.val ≤ u →
        ¬ F.link k ∩ g ⁻¹' {s} ⊆ closure U := by
  classical
  have hab' : (a : ℝ) < b := hab
  -- the middle of the window
  set s₀ : unitInterval := ⟨((a : ℝ) + b) / 2, by
    constructor <;> linarith [a.2.1, b.2.2]⟩ with hs₀
  have hs₀v : (s₀ : ℝ) = ((a : ℝ) + b) / 2 := rfl
  have hs₀ab : s₀ ∈ Icc a b := ⟨show (a : ℝ) ≤ s₀ by rw [hs₀v]; linarith,
    show (s₀ : ℝ) ≤ b by rw [hs₀v]; linarith⟩
  -- two far points in every link of the run, over the fibres near `s₀`
  have hfar : ∀ k : Fin N, ∃ ρ > 0, ∃ θ > 0, t ≤ k.val → k.val ≤ u → ∀ s : unitInterval,
      |(s : ℝ) - s₀| ≤ θ → ∃ x ∈ F.link k ∩ g ⁻¹' {s}, ∃ x' ∈ F.link k ∩ g ⁻¹' {s},
        ρ ≤ dist x x' := by
    intro k
    by_cases hk : t ≤ k.val ∧ k.val ≤ u
    · obtain ⟨p, hp, q, hq, hpq⟩ := exists_two_points_of_open
        (hg.2.2.2 s₀).1.1.2.isPreconnected (hg.2.2.2 s₀).2.2 (F.isOpen k)
        (hTf s₀ hs₀ab k hk.1 hk.2)
      have hd : 0 < dist p q := dist_pos.2 hpq
      obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.1 (F.isOpen k) p hp.1
      obtain ⟨r₂, hr₂, hb₂⟩ := Metric.isOpen_iff.1 (F.isOpen k) q hq.1
      set r := min (min r₁ r₂) (dist p q / 4) with hr
      have hrpos : 0 < r := lt_min (lt_min hr₁ hr₂) (by linarith)
      obtain ⟨θ₁, hθ₁, hθ₁m⟩ := exists_meets_near hg.2.1 (isOpen_ball (x := p) (ε := r))
        ⟨p, mem_ball_self hrpos, hp.2⟩
      obtain ⟨θ₂, hθ₂, hθ₂m⟩ := exists_meets_near hg.2.1 (isOpen_ball (x := q) (ε := r))
        ⟨q, mem_ball_self hrpos, hq.2⟩
      refine ⟨dist p q / 2, by linarith, min θ₁ θ₂, lt_min hθ₁ hθ₂, fun _ _ s hs => ?_⟩
      obtain ⟨x, hx1, hx2⟩ := hθ₁m s (hs.trans (min_le_left _ _))
      obtain ⟨x', hx'1, hx'2⟩ := hθ₂m s (hs.trans (min_le_right _ _))
      have hxr : dist x p < r := hx1
      have hx'r : dist x' q < r := hx'1
      refine ⟨x, ⟨hb₁ (lt_of_lt_of_le hxr ((min_le_left _ _).trans (min_le_left _ _))), hx2⟩,
        x', ⟨hb₂ (lt_of_lt_of_le hx'r ((min_le_left _ _).trans (min_le_right _ _))), hx'2⟩, ?_⟩
      have h4 : r ≤ dist p q / 4 := min_le_right _ _
      have := dist_triangle4 p x x' q
      rw [dist_comm p x] at this
      linarith
    · exact ⟨1, one_pos, 1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose ρk hρk θk hθk hfark using hfar
  obtain ⟨ρ, hρ, hρle⟩ := exists_pos_forall_le ρk hρk
  obtain ⟨θ, hθ, hθle⟩ := exists_pos_forall_le θk hθk
  -- the point and the radius
  obtain ⟨z, hzy, hzs⟩ := hTf s₀ hs₀ab y hty hyu
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 (F.isOpen y) z hzy
  set r := min (r₀ / 2) (ρ / 4) with hr
  have hrpos : 0 < r := lt_min (by linarith) (by linarith)
  set θ' := min θ (((b : ℝ) - a) / 4) with hθ'
  have hθ'pos : 0 < θ' := lt_min hθ (by linarith)
  set U : Set Y := ball z r ∩ g ⁻¹' {s | |(s : ℝ) - s₀| < θ'} with hU
  have hUo : IsOpen U := isOpen_ball.inter ((isOpen_lt
    ((continuous_subtype_val.sub continuous_const).abs) continuous_const).preimage hg.1)
  have hzU : z ∈ U := ⟨mem_ball_self hrpos, by
    simp only [mem_preimage, mem_setOf_eq]
    simp only [mem_preimage, mem_singleton_iff] at hzs
    rw [hzs, sub_self, abs_zero]; exact hθ'pos⟩
  have hclU : closure U ⊆ closedBall z r ∩ g ⁻¹' {s | |(s : ℝ) - s₀| ≤ θ'} := by
    apply closure_minimal
    · refine inter_subset_inter ball_subset_closedBall (fun w hw => ?_)
      simp only [mem_preimage, mem_setOf_eq] at hw ⊢
      exact hw.le
    · exact isClosed_closedBall.inter (isClosed_le
        ((continuous_subtype_val.sub continuous_const).abs) continuous_const |>.preimage hg.1)
  refine ⟨U, hUo, ⟨z, hzU⟩, fun w hw => ?_, fun w hw => ?_, fun s hs k hk1 hk2 hsub => ?_⟩
  · have h := hw.2
    simp only [mem_preimage, mem_setOf_eq] at h
    rw [abs_lt] at h
    have h1 : θ' ≤ ((b : ℝ) - a) / 4 := min_le_right _ _
    simp only [mem_preimage, mem_Ioo]
    exact ⟨show (a : ℝ) < g w by rw [hs₀v] at h; linarith,
      show ((g w : unitInterval) : ℝ) < b by rw [hs₀v] at h; linarith⟩
  · have h := (hclU hw).1
    apply hball
    rw [mem_closedBall] at h
    rw [mem_ball]
    linarith [min_le_left (r₀ / 2) (ρ / 4)]
  · obtain ⟨w, hw⟩ := hTf s hs k hk1 hk2
    have hws := (hclU (hsub hw)).2
    simp only [mem_preimage, mem_setOf_eq] at hws
    have hw2 := hw.2
    simp only [mem_preimage, mem_singleton_iff] at hw2
    rw [hw2] at hws
    obtain ⟨x, hx, x', hx', hxx'⟩ := hfark k hk1 hk2 s
      (hws.trans ((min_le_left _ _).trans (hθle k)))
    have h1 := (hclU (hsub hx)).1
    have h2 := (hclU (hsub hx')).1
    rw [mem_closedBall] at h1 h2
    have := dist_triangle_right x x' z
    have h3 : r ≤ ρ / 4 := min_le_right _ _
    linarith [hρle k]

end SubArc

end HPC.BJ59
