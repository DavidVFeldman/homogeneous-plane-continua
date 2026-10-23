import HPC.Plane.CantorOrganOrder
import HPC.Plane.Atriodic51B

/-!
# Batch 97: the Cantor organ, part five — Bing's hypotheses and Bing's elements

The Cantor organ `Organ` satisfies `BingS` (`organ_bingS`): it is a nondegenerate continuum,
atriodic, hereditarily unicoherent and hereditarily decomposable. All three hereditary properties
come from the linear order of `HPC/Plane/CantorOrganOrder.lean`: subcontinua are exactly the
closed order-convex sets.

Bing's element of a point `s` is the layer of `s` (`organ_bingElt`), a nondegenerate arc
(`organ_bingElt_ne_singleton`); no interior layer is an end element (`organ_not_isEndElt`); and
at a layer over a *good* parameter the layers vary continuously in the Hausdorff metric
(`organ_layer_hausdorff`).
-/

namespace HPC.Plane.Org

open Set Filter Topology

/-! ## Order-convexity toolkit -/

theorem ordConvex_univ : OrdConvex (univ : Set Organ) := fun _ _ _ _ _ _ _ => trivial

theorem ordConvex_inter {X Y : Set Organ} (hX : OrdConvex X) (hY : OrdConvex Y) :
    OrdConvex (X ∩ Y) :=
  fun a ha c hc b h1 h2 => ⟨hX a ha.1 c hc.1 b h1 h2, hY a ha.2 c hc.2 b h1 h2⟩

theorem ordConvex_Iic (m : ℝ) : OrdConvex (F ⁻¹' Iic m) :=
  fun _ _ _ hc _ _ h2 => (F_le_of_key_le h2).trans hc

theorem ordConvex_Ici (m : ℝ) : OrdConvex (F ⁻¹' Ici m) :=
  fun _ ha _ _ _ h1 _ => le_trans ha (F_le_of_key_le h1)

theorem mem_gam_image_iff {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 2)
    {y : Organ} : y ∈ gam t '' Icc u v ↔ F y = t ∧ u ≤ pos y ∧ pos y ≤ v := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    have hτ' : τ ∈ Icc (0 : ℝ) 2 := ⟨hu.trans hτ.1, hτ.2.trans hv⟩
    rw [F_gam ht, pos_gam ht hτ']
    exact ⟨rfl, hτ.1, hτ.2⟩
  · rintro ⟨hF, h1, h2⟩
    refine ⟨pos y, ⟨h1, h2⟩, ?_⟩
    have := (pos_spec y).2; rwa [hF] at this

theorem ordConvex_gam {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 2) :
    OrdConvex (gam t '' Icc u v) := by
  intro a ha c hc b h1 h2
  rw [mem_gam_image_iff ht hu hv] at ha hc ⊢
  have hb1 := F_le_of_key_le h1
  have hb2 := F_le_of_key_le h2
  have hFb : F b = t := le_antisymm (hb2.trans hc.1.le) (ha.1.symm.le.trans hb1)
  refine ⟨hFb, ?_, ?_⟩
  · rcases key_le_iff.mp h1 with h | h
    · rw [ha.1, hFb] at h; exact absurd h (lt_irrefl _)
    · exact ha.2.1.trans h.2
  · rcases key_le_iff.mp h2 with h | h
    · rw [hc.1, hFb] at h; exact absurd h (lt_irrefl _)
    · exact h.2.trans hc.2.2

theorem isContinuum_of_ordConvex {X : Set Organ} (hX : OrdConvex X) (hXc : IsClosed X)
    (hne : X.Nonempty) : Fold.Q78.IsContinuum X :=
  ⟨hXc.isCompact, hne, isPreconnected_of_ordConvex hX⟩

theorem ordConvex_of_isContinuum {K : Set Organ} (hK : Fold.Q78.IsContinuum K) : OrdConvex K :=
  ordConvex_of_continuum hK.1.isClosed hK.2.2

/-! ## Bing's hypotheses -/

theorem organ_nonempty : Nonempty Organ := ⟨pt (fun _ => false) 0⟩

theorem organ_connected : ConnectedSpace Organ := by
  haveI := organ_nonempty
  exact connectedSpace_iff_univ.mpr ⟨univ_nonempty, isPreconnected_of_ordConvex ordConvex_univ⟩

theorem pt_zero_ne_one (c : Cs) : pt c 0 ≠ pt c 1 := by
  intro h
  have h1 := pt_height c (y := 0) ⟨le_rfl, zero_le_one⟩
  have h2 := pt_height c (y := 1) ⟨zero_le_one, le_rfl⟩
  rw [h] at h1
  rw [h1] at h2
  exact zero_ne_one h2

theorem organ_nontrivial : Nontrivial Organ :=
  ⟨⟨pt (fun _ => false) 0, pt (fun _ => false) 1, pt_zero_ne_one _⟩⟩

theorem organ_hu : IsHereditarilyUnicoherent (univ : Set Organ) := by
  intro K _ hK _ H K' hH hK' hun
  refine ⟨?_, isPreconnected_of_ordConvex
    (ordConvex_inter (ordConvex_of_isContinuum hH) (ordConvex_of_isContinuum hK'))⟩
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hpc : IsPreconnected (H ∪ K') := hun ▸ hK.2.2
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hpc H K' hH.1.isClosed hK'.1.isClosed
    subset_rfl (by rw [hne, inter_empty]) with h | h
  · obtain ⟨x, hx⟩ := hK'.2.1
    exact (eq_empty_iff_forall_notMem.mp hne) x ⟨h (Or.inr hx), hx⟩
  · obtain ⟨x, hx⟩ := hH.2.1
    exact (eq_empty_iff_forall_notMem.mp hne) x ⟨hx, h (Or.inl hx)⟩

/-- A preconnected subset of the union of three mutually separated sets lies in one of them. -/
theorem subset_one_of_three {T A B C : Set Organ} (hT : IsPreconnected T) (hTs : T ⊆ A ∪ B ∪ C)
    (d1 : Disjoint (closure A) B) (d2 : Disjoint A (closure B)) (d3 : Disjoint (closure A) C)
    (d4 : Disjoint A (closure C)) (d5 : Disjoint (closure B) C) (d6 : Disjoint B (closure C)) :
    T ⊆ A ∨ T ⊆ B ∨ T ⊆ C := by
  have h1 : T ⊆ A ∪ (B ∪ C) := fun x hx => by
    rcases hTs hx with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases subset_side_of_isPreconnected hT h1 (disjoint_union_right.mpr ⟨d1, d3⟩)
    (by rw [closure_union]; exact disjoint_union_right.mpr ⟨d2, d4⟩) with h | h
  · exact Or.inl h
  · exact Or.inr (subset_side_of_isPreconnected hT h d5 d6)

theorem three_two {A B C L H : Set Organ} {a b c : Organ} (haB : a ∉ B) (haC : a ∉ C)
    (hbA : b ∉ A) (hbC : b ∉ C) (hcA : c ∉ A) (hcB : c ∉ B) (ha' : a ∈ L ∪ H) (hb' : b ∈ L ∪ H)
    (hc' : c ∈ L ∪ H) (hL : L ⊆ A ∨ L ⊆ B ∨ L ⊆ C) (hH : H ⊆ A ∨ H ⊆ B ∨ H ⊆ C) : False := by
  rcases hL with h | h | h <;> rcases hH with h' | h' | h' <;> rcases ha' with e1 | e1 <;>
    rcases hb' with e2 | e2 <;> rcases hc' with e3 | e3 <;>
    first | exact haB (h e1) | exact haC (h e1) | exact haB (h' e1) | exact haC (h' e1) | exact hbA (h e2) | exact hbC (h e2) | exact hbA (h' e2) | exact hbC (h' e2) | exact hcA (h e3) | exact hcB (h e3) | exact hcA (h' e3) | exact hcB (h' e3)

theorem organ_atriodic : IsAtriodic (univ : Set Organ) := by
  rintro T - ⟨hT, N, hN, -, A, B, C, hA, hB, hC, heq, d1, d2, d3, d4, d5, d6⟩
  obtain ⟨n, hn⟩ := hN.2.1
  have hTc := ordConvex_of_isContinuum hT
  have hNc := ordConvex_of_isContinuum hN
  set Lo : Set Organ := {x | x ∈ T \ N ∧ key x < key n}
  set Hi : Set Organ := {x | x ∈ T \ N ∧ key n < key x}
  have hLo : OrdConvex Lo := by
    rintro a ⟨⟨haT, -⟩, -⟩ c ⟨⟨hcT, hcN⟩, hcn⟩ b h1 h2
    refine ⟨⟨hTc a haT c hcT b h1 h2, fun hbN => hcN (hNc b hbN n hn c h2 hcn.le)⟩,
      lt_of_le_of_lt h2 hcn⟩
  have hHi : OrdConvex Hi := by
    rintro a ⟨⟨haT, haN⟩, han⟩ c ⟨⟨hcT, -⟩, -⟩ b h1 h2
    refine ⟨⟨hTc a haT c hcT b h1 h2, fun hbN => haN (hNc n hn b hbN a han.le h1)⟩,
      lt_of_lt_of_le han h1⟩
  have hsplit : A ∪ B ∪ C ⊆ Lo ∪ Hi := by
    intro x hx
    rw [← heq] at hx
    rcases lt_or_gt_of_ne (fun h : key x = key n => hx.2 (key_injective h ▸ hn)) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hsub : ∀ X : Set Organ, X ⊆ Lo ∪ Hi → X ⊆ A ∪ B ∪ C := by
    intro X hX x hx
    rw [← heq]
    rcases hX hx with h | h
    · exact h.1
    · exact h.1
  have hLo3 := subset_one_of_three (isPreconnected_of_ordConvex hLo)
    (hsub Lo subset_union_left) d1 d2 d3 d4 d5 d6
  have hHi3 := subset_one_of_three (isPreconnected_of_ordConvex hHi)
    (hsub Hi subset_union_right) d1 d2 d3 d4 d5 d6
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  obtain ⟨c, hc⟩ := hC
  have haB : a ∉ B := fun h => disjoint_left.mp d1 (subset_closure ha) h
  have haC : a ∉ C := fun h => disjoint_left.mp d3 (subset_closure ha) h
  have hbA : b ∉ A := fun h => disjoint_left.mp d1 (subset_closure h) hb
  have hbC : b ∉ C := fun h => disjoint_left.mp d5 (subset_closure hb) h
  have hcA : c ∉ A := fun h => disjoint_left.mp d3 (subset_closure h) hc
  have hcB : c ∉ B := fun h => disjoint_left.mp d5 (subset_closure h) hc
  have ha' := hsplit (Or.inl (Or.inl ha))
  have hb' := hsplit (Or.inl (Or.inr hb))
  have hc' := hsplit (Or.inr hc)
  exact three_two haB haC hbA hbC hcA hcB ha' hb' hc' hLo3 hHi3

/-- Splitting a continuum by two closed sets. -/
theorem split_continuum {K P Q : Set Organ} (hK : Fold.Q78.IsContinuum K) (hP : IsClosed P)
    (hQ : IsClosed Q) (hPc : OrdConvex P) (hQc : OrdConvex Q) {a c : Organ} (ha : a ∈ K)
    (hc : c ∈ K) (haP : a ∈ P) (hcP : c ∉ P) (hcQ : c ∈ Q) (haQ : a ∉ Q) (hKPQ : K ⊆ P ∪ Q) :
    ∃ A B : Set Organ, Fold.Q78.IsContinuum A ∧ Fold.Q78.IsContinuum B ∧ A ≠ K ∧ B ≠ K ∧
      A ∪ B = K := by
  have hKc := ordConvex_of_isContinuum hK
  refine ⟨K ∩ P, K ∩ Q, isContinuum_of_ordConvex (ordConvex_inter hKc hPc)
    (hK.1.isClosed.inter hP) ⟨a, ha, haP⟩, isContinuum_of_ordConvex (ordConvex_inter hKc hQc)
    (hK.1.isClosed.inter hQ) ⟨c, hc, hcQ⟩, fun h => hcP (h ▸ hc).2, fun h => haQ (h ▸ ha).2, ?_⟩
  rw [← inter_union_distrib_left]
  exact inter_eq_left.mpr hKPQ

theorem organ_hd : IsHereditarilyDecomposable (univ : Set Organ) := by
  intro K _ hK hKnt
  by_cases hF : ∃ a ∈ K, ∃ c ∈ K, F a < F c
  · obtain ⟨a, ha, c, hc, hac⟩ := hF
    set m := (F a + F c) / 2
    refine split_continuum hK (isClosed_Iic.preimage continuous_F)
      (isClosed_Ici.preimage continuous_F) (ordConvex_Iic m) (ordConvex_Ici m) ha hc ?_ ?_ ?_ ?_ ?_
    · show F a ≤ m; simp only [m]; linarith
    · show ¬ F c ≤ m; simp only [m]; linarith
    · show m ≤ F c; simp only [m]; linarith
    · show ¬ m ≤ F a; simp only [m]; linarith
    · intro x _; rcases le_total (F x) m with h | h
      · exact Or.inl h
      · exact Or.inr h
  · push_neg at hF
    obtain ⟨a, ha, c, hc, hac⟩ := hKnt
    have hFK : ∀ x ∈ K, F x = F a := fun x hx => le_antisymm (hF a ha x hx) (hF x hx a ha)
    set t := F a
    have ht : t ∈ Icc (0 : ℝ) 1 := F_mem a
    have hpos : pos a ≠ pos c := fun h => hac (eq_of_F_pos (hFK c hc).symm h)
    have hsplit : ∀ a c : Organ, a ∈ K → c ∈ K → pos a < pos c →
        ∃ A B : Set Organ, Fold.Q78.IsContinuum A ∧ Fold.Q78.IsContinuum B ∧ A ≠ K ∧ B ≠ K ∧
          A ∪ B = K := by
      intro a c ha hc hlt
      set μ := (pos a + pos c) / 2
      have hpa := (pos_spec a).1
      have hpc := (pos_spec c).1
      have hμ0 : 0 ≤ μ := by simp only [μ]; linarith [hpa.1, hpc.1]
      have hμ2 : μ ≤ 2 := by simp only [μ]; linarith [hpa.2, hpc.2]
      have hcl : ∀ u v : ℝ, IsClosed (gam t '' Icc u v) := fun u v =>
        (isCompact_Icc.image (continuous_gam ht)).isClosed
      refine split_continuum hK (hcl 0 μ) (hcl μ 2) (ordConvex_gam ht le_rfl hμ2)
        (ordConvex_gam ht hμ0 le_rfl) ha hc ?_ ?_ ?_ ?_ ?_
      · rw [mem_gam_image_iff ht le_rfl hμ2]
        exact ⟨hFK a ha, hpa.1, by simp only [μ]; linarith⟩
      · rw [mem_gam_image_iff ht le_rfl hμ2]
        rintro ⟨-, -, h⟩; simp only [μ] at h; linarith
      · rw [mem_gam_image_iff ht hμ0 le_rfl]
        exact ⟨hFK c hc, by simp only [μ]; linarith, hpc.2⟩
      · rw [mem_gam_image_iff ht hμ0 le_rfl]
        rintro ⟨-, h, -⟩; simp only [μ] at h; linarith
      · intro x hx
        have hpx := (pos_spec x).1
        rcases le_total (pos x) μ with h | h
        · exact Or.inl ((mem_gam_image_iff ht le_rfl hμ2).mpr ⟨hFK x hx, hpx.1, h⟩)
        · exact Or.inr ((mem_gam_image_iff ht hμ0 le_rfl).mpr ⟨hFK x hx, h, hpx.2⟩)
    rcases lt_or_gt_of_ne hpos with h | h
    · exact hsplit a c ha hc h
    · exact hsplit c a hc ha h

/-- **The Cantor organ satisfies Bing's standing hypothesis.** -/
theorem organ_bingS : BingS Organ :=
  ⟨organ_connected, organ_nontrivial, organ_atriodic, organ_hu, organ_hd⟩

/-! ## Bing's elements are the layers -/

theorem isContinuum_preimage_Icc {u v : ℝ} {s : Organ} (hs : F s ∈ Icc u v) :
    Fold.Q78.IsContinuum (F ⁻¹' Icc u v) :=
  ⟨(isClosed_Icc.preimage continuous_F).isCompact, ⟨s, hs⟩,
    isPreconnected_preimage_F isPreconnected_Icc⟩

theorem bingElt_subset_layer (s : Organ) : bingElt s ⊆ layer (F s) := by
  intro x hx
  by_contra hxt
  have hne : F x ≠ F s := hxt
  set t := F s
  set η := |F x - t| / 3
  have hη : 0 < η := by simp only [η]; have := abs_pos.mpr (sub_ne_zero.mpr hne); linarith
  have hH := isContinuum_preimage_Icc (u := t - 2 * η) (v := t + 2 * η) (s := s)
    ⟨by linarith, by linarith⟩
  have hH' := isContinuum_preimage_Icc (u := t - η) (v := t + η) (s := s)
    ⟨by linarith, by linarith⟩
  have hsub : F ⁻¹' Icc (t - η) (t + η) ⊆ interior (F ⁻¹' Icc (t - 2 * η) (t + 2 * η)) := by
    refine Subset.trans ?_ (interior_maximal (preimage_mono Ioo_subset_Icc_self)
      (isOpen_Ioo.preimage continuous_F))
    intro y hy; exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hsint : s ∈ interior (F ⁻¹' Icc (t - η) (t + η)) :=
    interior_maximal (preimage_mono Ioo_subset_Icc_self) (isOpen_Ioo.preimage continuous_F)
      (show F s ∈ Ioo (t - η) (t + η) from ⟨by linarith, by linarith⟩)
  have hxH := bingElt_subset hH ⟨_, hH', hsub, hsint⟩ hx
  have h1 := hxH.1
  have h2 := hxH.2
  have h3 : |F x - t| = 3 * η := by simp only [η]; ring
  rcases le_or_gt (F x) t with h | h
  · rw [abs_of_nonpos (by linarith)] at h3; linarith
  · rw [abs_of_pos (by linarith)] at h3; linarith

theorem lft_eq_rgt_zero : lft 0 = rgt 0 := by
  have ht : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  rcases lft_eq_or_pair ht with h | ⟨m, hm⟩
  · exact h
  · exfalso
    have h1 := lam_flip1_true hm.1.2.2
    have h2 := lam_nonneg (flip1 (rgt 0) m)
    have h3 := wL.p_pos m
    have h4 := (rgt_spec ht).1
    linarith

theorem lft_eq_rgt_one : lft 1 = rgt 1 := by
  have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  rcases lft_eq_or_pair ht with h | ⟨m, hm⟩
  · exact h
  · exfalso
    have h1 := lam_flip1_false hm.1.2.1
    have h2 := lam_le_one (flip1 (lft 1) m)
    have h3 := wL.p_pos m
    have h4 := (lft_spec ht).1
    linarith

/-- A subcontinuum containing a point of the left strand in its interior contains the strand. -/
theorem side_L {K : Set Organ} (hK : IsClosed K) (hKc : IsPreconnected K) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (ht0 : 0 < t) {q : Organ} (hq : q ∈ interior K)
    (hqs : q ∈ strand (lft t)) : strand (lft t) ⊆ K := by
  obtain ⟨hl1, hl2⟩ := lft_spec ht
  obtain ⟨y, -, rfl⟩ := hqs
  have hcl := pt_mem_closure_left (frequently_true hl2 (by rw [hl1]; exact ht0))
    (show (0 : ℝ) < lam (lft t) by rw [hl1]; exact ht0) y
  obtain ⟨a, haK, haF⟩ := mem_closure_iff.mp hcl _ isOpen_interior hq
  have haF2 : F a < lam (lft t) := haF.2
  exact strand_lft_subset hK hKc ht (interior_subset haK) (interior_subset hq)
    (by rw [← hl1]; exact haF2) (by rw [F_pt, hl1])

/-- A subcontinuum containing a point of the right strand in its interior contains the strand. -/
theorem side_R {K : Set Organ} (hK : IsClosed K) (hKc : IsPreconnected K) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (ht1 : t < 1) {q : Organ} (hq : q ∈ interior K)
    (hqs : q ∈ strand (rgt t)) : strand (rgt t) ⊆ K := by
  obtain ⟨hr1, hr2⟩ := rgt_spec ht
  obtain ⟨y, -, rfl⟩ := hqs
  have hcl := pt_mem_closure_right (frequently_false hr2 (by rw [hr1]; exact ht1))
    (show lam (rgt t) < 1 by rw [hr1]; exact ht1) y
  obtain ⟨a, haK, haF⟩ := mem_closure_iff.mp hcl _ isOpen_interior hq
  have haF1 : lam (rgt t) < F a := haF.1
  exact strand_rgt_subset hK hKc ht (interior_subset haK) (interior_subset hq)
    (by rw [← hr1]; exact haF1) (by rw [F_pt, hr1])

theorem side_L' {K : Set Organ} (hK : IsClosed K) (hKc : IsPreconnected K) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {q : Organ} (hq : q ∈ interior K)
    (hqs : q ∈ strand (lft t)) : strand (lft t) ⊆ K := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h
    rw [lft_eq_rgt_zero] at hqs ⊢
    exact side_R hK hKc ht zero_lt_one hq hqs
  · exact side_L hK hKc ht h hq hqs

theorem side_R' {K : Set Organ} (hK : IsClosed K) (hKc : IsPreconnected K) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {q : Organ} (hq : q ∈ interior K)
    (hqs : q ∈ strand (rgt t)) : strand (rgt t) ⊆ K := by
  rcases eq_or_lt_of_le ht.2 with h | h
  · subst h
    rw [← lft_eq_rgt_one] at hqs ⊢
    exact side_L hK hKc ht zero_lt_one hq hqs
  · exact side_R hK hKc ht h hq hqs

theorem layer_subset_bingElt (s : Organ) : layer (F s) ⊆ bingElt s := by
  intro x hx
  refine mem_sInter.mpr ?_
  rintro H ⟨hH, H', hH', hH'H, hs⟩
  set t := F s
  have ht : t ∈ Icc (0 : ℝ) 1 := F_mem s
  have hcl := hH.1.isClosed
  have hcl' := hH'.1.isClosed
  have hH'sub : H' ⊆ H := hH'H.trans interior_subset
  obtain ⟨z, hzl, hzr⟩ := strands_meet ht
  have hslayer : s ∈ layer t := rfl
  rw [layer_eq ht] at hslayer hx
  have key : strand (lft t) ⊆ H ∧ strand (rgt t) ⊆ H := by
    rcases hslayer with hsl | hsr
    · have h1 := side_L' hcl' hH'.2.2 ht hs hsl
      exact ⟨h1.trans hH'sub, side_R' hcl hH.2.2 ht (hH'H (h1 hzl)) hzr⟩
    · have h1 := side_R' hcl' hH'.2.2 ht hs hsr
      exact ⟨side_L' hcl hH.2.2 ht (hH'H (h1 hzr)) hzl, h1.trans hH'sub⟩
  rcases hx with hx | hx
  · exact key.1 hx
  · exact key.2 hx

/-- **Bing's elements of the organ are its layers.** -/
theorem organ_bingElt (s : Organ) : bingElt s = layer (F s) :=
  Subset.antisymm (bingElt_subset_layer s) (layer_subset_bingElt s)

/-- **Every element of the organ is nondegenerate.** -/
theorem organ_bingElt_ne_singleton (s : Organ) : bingElt s ≠ {s} := by
  intro h
  rw [organ_bingElt] at h
  have ht := F_mem s
  have h0 : pt (lft (F s)) 0 ∈ layer (F s) :=
    strand_lft_subset_layer ht ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have h1 : pt (lft (F s)) 1 ∈ layer (F s) :=
    strand_lft_subset_layer ht ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  rw [h] at h0 h1
  exact pt_zero_ne_one _ (h0.trans h1.symm)

/-- **Interior layers are not end elements.** -/
theorem organ_not_isEndElt {r : Organ} (h0 : 0 < F r) (h1 : F r < 1) : ¬ IsEndElt r := by
  intro hr
  set q := pt (fun _ => false) 0
  set q' := pt (fun _ => true) 0
  have hq : F q = 0 := by rw [F_pt, lam_const_false]
  have hq' : F q' = 1 := by rw [F_pt, lam_const_true]
  have hne : ∀ a b : Organ, F a ≠ F b → bingElt a ≠ bingElt b := by
    intro a b hab h
    have : a ∈ bingElt b := h ▸ mem_bingElt a
    rw [organ_bingElt] at this
    exact hab this
  refine hr q q' (hne _ _ (by rw [hq]; exact h0.ne)) (hne _ _ (by rw [hq']; exact h1.ne'))
    (hne _ _ (by rw [hq, hq']; exact zero_ne_one)) ?_
  rw [organ_bingElt, organ_bingElt, organ_bingElt, hq, hq']
  refine ⟨?_, ?_, F ⁻¹' Iio (F r), F ⁻¹' Ioi (F r), isOpen_Iio.preimage continuous_F,
    isOpen_Ioi.preimage continuous_F, ?_, ?_, ?_, ?_⟩
  · rw [disjoint_left]; intro x hx hx'
    have e1 : F x = F r := hx
    have e2 : F x = 0 := hx'
    linarith
  · rw [disjoint_left]; intro x hx hx'
    have e1 : F x = F r := hx
    have e2 : F x = 1 := hx'
    linarith
  · rw [disjoint_left]; intro x hx hx'
    have e1 : F x < F r := hx
    have e2 : F r < F x := hx'
    linarith
  · intro x hx
    have : F x ≠ F r := hx.2
    rcases lt_or_gt_of_ne this with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro x hx
    have e : F x = 0 := hx
    show F x < F r; linarith
  · intro x hx
    have e : F x = 1 := hx
    show F r < F x; linarith

/-! ## Continuity of the layers at a good parameter -/

/-- **Layers vary continuously at a good parameter.** -/
theorem organ_layer_hausdorff {c : Cs} (hc : Good c) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ y : Organ, |F y - lam c| < η →
      Metric.hausdorffDist (layer (F y)) (layer (lam c)) < ε := by
  set V : Set Cs := {b | |PP b - PP c| < ε / 2 ∧ |QQ b - QQ c| < ε / 2}
  have hV : IsOpen V := by
    refine IsOpen.inter ?_ ?_
    · exact isOpen_lt ((continuous_PP.sub continuous_const).abs) continuous_const
    · exact isOpen_lt ((continuous_QQ.sub continuous_const).abs) continuous_const
  have hcV : c ∈ V := ⟨by simp; linarith, by simp; linarith⟩
  have hK : IsClosed (lam '' Vᶜ) := (hV.isClosed_compl.isCompact.image continuous_lam).isClosed
  have hnot : lam c ∉ lam '' Vᶜ := by
    rintro ⟨b, hb, hbc⟩
    exact hb (hc.lam_eq hbc ▸ hcV)
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl (lam c) hnot
  have hinV : ∀ b : Cs, |lam b - lam c| < η → b ∈ V := by
    intro b hb
    by_contra hbV
    exact hball (show lam b ∈ Metric.ball (lam c) η by rw [Metric.mem_ball, Real.dist_eq]; exact hb)
      ⟨b, hbV, rfl⟩
  have hdist : ∀ b : Cs, b ∈ V → ∀ h ∈ Icc (0 : ℝ) 1, dist (pt b h) (pt c h) ≤ ε / 2 := by
    intro b hb h hh
    exact (dist_pt_same_height hh).trans (max_le hb.1.le hb.2.le)
  refine ⟨η, hη, fun y hy => lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  apply Metric.hausdorffDist_le_of_mem_dist (by linarith)
  · intro x hx
    obtain ⟨b, h, hh, rfl⟩ := exists_pt x
    have hb : lam b = F y := by rw [← F_pt b h]; exact hx
    exact ⟨pt c h, F_pt c h, hdist b (hinV b (by rw [hb]; exact hy)) h hh⟩
  · intro x hx
    obtain ⟨b, h, hh, rfl⟩ := exists_pt x
    have hb : lam b = lam c := by rw [← F_pt b h]; exact hx
    obtain rfl := hc.lam_eq hb
    obtain ⟨b', hb'⟩ := lam_surj (F_mem y)
    refine ⟨pt b' h, by show F (pt b' h) = F y; rw [F_pt, hb'], ?_⟩
    rw [dist_comm]
    exact hdist b' (hinV b' (by rw [hb']; exact hy)) h hh

/-- A good parameter strictly inside `(0, 1)`. -/
def goodC : Cs := fun k => decide (k % 3 ≠ 0)

theorem goodC_good : Good goodC :=
  ⟨0, fun j => ⟨by simp [goodC], by simp [goodC], by simp [goodC]⟩⟩

theorem lam_goodC_pos : 0 < lam goodC := by
  rcases eq_or_lt_of_le (lam_nonneg goodC) with h | h
  · exfalso
    have := goodC_good.lam_eq (b := fun _ => false) (by rw [lam_const_false]; exact h)
    have h1 := congrFun this 1
    simp [goodC] at h1
  · exact h

theorem lam_goodC_lt_one : lam goodC < 1 := by
  rcases eq_or_lt_of_le (lam_le_one goodC) with h | h
  · exfalso
    have := goodC_good.lam_eq (b := fun _ => true) (by rw [lam_const_true]; exact h.symm)
    have h1 := congrFun this 0
    simp [goodC] at h1
  · exact h

end HPC.Plane.Org
