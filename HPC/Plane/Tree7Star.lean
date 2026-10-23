import HPC.Plane.Tree6

/-!
# Batch 119, auxiliary: strongly star-shaped open sets (the notched squares)

A set `N` is *strongly star-shaped* about `c` if every point `c + t • (y - c)` with `0 ≤ t < 1` and
`y ∈ closure N` lies in `N`. A finite union of open convex sets containing `c` is strongly
star-shaped about `c` (`Convex.combo_interior_closure_mem_interior`), and a strongly star-shaped
set is connected, regular open (if open), and has connected unbounded complement and connected
unbounded exterior (if bounded): the ray from `c` through a point outside beyond that point stays
outside. The notched square is the union of three open rectangles containing the centre of its
square.
-/

namespace HPC.Plane

open Set Metric

/-- `N` is strongly star-shaped about `c`. -/
def StrongStar (N : Set Pt) (c : Pt) : Prop :=
  ∀ y ∈ closure N, ∀ t : ℝ, 0 ≤ t → t < 1 → c + t • (y - c) ∈ N

theorem strongStar_of_convex {R₁ R₂ R₃ : Set Pt} {c : Pt} (h₁ : IsOpen R₁) (h₂ : IsOpen R₂)
    (h₃ : IsOpen R₃) (k₁ : Convex ℝ R₁) (k₂ : Convex ℝ R₂) (k₃ : Convex ℝ R₃)
    (c₁ : c ∈ R₁) (c₂ : c ∈ R₂) (c₃ : c ∈ R₃) : StrongStar (R₁ ∪ R₂ ∪ R₃) c := by
  have key : ∀ R : Set Pt, IsOpen R → Convex ℝ R → c ∈ R → ∀ y ∈ closure R, ∀ t : ℝ,
      0 ≤ t → t < 1 → c + t • (y - c) ∈ R := by
    intro R hR hk hc y hy t ht0 ht1
    have := hk.combo_interior_closure_mem_interior (hR.interior_eq.symm ▸ hc) hy
      (a := 1 - t) (b := t) (by linarith) ht0 (by ring)
    rw [hR.interior_eq] at this
    convert this using 1
    simp only [smul_sub, sub_smul, one_smul]; abel
  intro y hy t ht0 ht1
  rw [closure_union, closure_union] at hy
  rcases hy with (hy | hy) | hy
  · exact Or.inl (Or.inl (key R₁ h₁ k₁ c₁ y hy t ht0 ht1))
  · exact Or.inl (Or.inr (key R₂ h₂ k₂ c₂ y hy t ht0 ht1))
  · exact Or.inr (key R₃ h₃ k₃ c₃ y hy t ht0 ht1)

theorem StrongStar.starConvex {N : Set Pt} {c : Pt} (h : StrongStar N c) (hc : c ∈ N) :
    StarConvex ℝ c N := by
  intro y hy a b ha hb hab
  rcases eq_or_lt_of_le hb with hb0 | hb1
  · subst hb0; simp at hab; subst hab; simpa using hc
  rcases lt_or_eq_of_le (show b ≤ 1 by linarith) with hb2 | hb2
  · have := h y (subset_closure hy) b hb hb2
    convert this using 1
    rw [show a = 1 - b by linarith]; simp only [smul_sub, sub_smul, one_smul]; abel
  · subst hb2; rw [show a = 0 by linarith]; simpa using hy

theorem StrongStar.isConnected {N : Set Pt} {c : Pt} (h : StrongStar N c) (hc : c ∈ N) :
    IsConnected N :=
  ((h.starConvex hc).isPathConnected hc).isConnected

/-- A strongly star-shaped open set is regular open. -/
theorem StrongStar.regular {N : Set Pt} {c : Pt} (h : StrongStar N c) (ho : IsOpen N) :
    interior (closure N) = N := by
  apply subset_antisymm _ (ho.subset_interior_iff.2 subset_closure)
  intro p hp
  by_contra hpN
  have hout : ∀ s : ℝ, 1 < s → c + s • (p - c) ∉ closure N := by
    intro s hs hy
    have := h _ hy (1 / s) (by positivity) (by rw [div_lt_one (by linarith)]; exact hs)
    apply hpN
    convert this using 1
    rw [add_sub_cancel_left, smul_smul, one_div_mul_cancel (by linarith), one_smul,
      add_sub_cancel]
  have hlim : Filter.Tendsto (fun s : ℝ => c + s • (p - c)) (nhdsWithin 1 (Ioi 1)) (nhds p) := by
    have : Filter.Tendsto (fun s : ℝ => c + s • (p - c)) (nhds 1)
        (nhds (c + (1:ℝ) • (p - c))) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 1)
    rw [one_smul, add_sub_cancel] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in nhdsWithin (1:ℝ) (Ioi 1), c + s • (p - c) ∈ interior (closure N) :=
    hlim (isOpen_interior.mem_nhds hp)
  obtain ⟨s, hs1, hs2⟩ := (hev.and self_mem_nhdsWithin).exists
  exact hout s hs2 (interior_subset hs1)

/-- The complement of a closed sup-metric ball is connected and unbounded. -/
theorem isConnected_compl_closedBall_pt (c : Pt) (R : ℝ) :
    IsConnected (closedBall c R)ᶜ ∧ ¬ Bornology.IsBounded (closedBall c R)ᶜ := by
  set H1 : Set Pt := {p | c.1 + R < p.1}
  set H2 : Set Pt := {p | p.1 < c.1 - R}
  set H3 : Set Pt := {p | c.2 + R < p.2}
  set H4 : Set Pt := {p | p.2 < c.2 - R}
  have hcv : ∀ (f : Pt →ₗ[ℝ] ℝ) (a : ℝ), IsPreconnected {p : Pt | a < f p} ∧
      IsPreconnected {p : Pt | f p < a} := fun f a =>
    ⟨(convex_halfSpace_gt f.isLinear a).isPreconnected,
      (convex_halfSpace_lt f.isLinear a).isPreconnected⟩
  have p1 : IsPreconnected H1 := (hcv (LinearMap.fst ℝ ℝ ℝ) _).1
  have p2 : IsPreconnected H2 := (hcv (LinearMap.fst ℝ ℝ ℝ) _).2
  have p3 : IsPreconnected H3 := (hcv (LinearMap.snd ℝ ℝ ℝ) _).1
  have p4 : IsPreconnected H4 := (hcv (LinearMap.snd ℝ ℝ ℝ) _).2
  set K := |R| + 1
  have hRK := abs_le.1 (le_refl |R|)
  have hK1 : 0 < K := by positivity
  have heq : (closedBall c R)ᶜ = H1 ∪ H3 ∪ H2 ∪ H4 := by
    ext p
    simp only [mem_compl_iff, mem_closedBall, not_le, Prod.dist_eq, Real.dist_eq, lt_max_iff,
      lt_abs, H1, H2, H3, H4, mem_union, mem_setOf_eq]
    constructor
    · rintro ((h | h) | (h | h))
      · left; left; left; linarith
      · left; right; linarith
      · left; left; right; linarith
      · right; linarith
    · rintro (((h | h) | h) | h)
      · left; left; linarith
      · right; left; linarith
      · left; right; linarith
      · right; right; linarith
  have e1 : c + (K + R, K + R) ∈ H1 := show c.1 + R < c.1 + (K + R) by linarith
  have e3 : c + (K + R, K + R) ∈ H3 := show c.2 + R < c.2 + (K + R) by linarith
  have f3 : c + (-(K + R), K + R) ∈ H3 := show c.2 + R < c.2 + (K + R) by linarith
  have f2 : c + (-(K + R), K + R) ∈ H2 := show c.1 + -(K + R) < c.1 - R by linarith
  have g1 : c + (K + R, -(K + R)) ∈ H1 := show c.1 + R < c.1 + (K + R) by linarith
  have g4 : c + (K + R, -(K + R)) ∈ H4 := show c.2 + -(K + R) < c.2 - R by linarith
  have q13 : IsPreconnected (H1 ∪ H3) := p1.union _ e1 e3 p3
  have q132 : IsPreconnected (H1 ∪ H3 ∪ H2) := q13.union _ (Or.inr f3) f2 p2
  have q : IsPreconnected (H1 ∪ H3 ∪ H2 ∪ H4) := q132.union _ (Or.inl (Or.inl g1)) g4 p4
  have hne : (H1 ∪ H3 ∪ H2 ∪ H4).Nonempty := ⟨_, Or.inl (Or.inl (Or.inl e1))⟩
  refine ⟨heq ▸ ⟨hne, q⟩, fun hb => ?_⟩
  have : Bornology.IsBounded (univ : Set Pt) := by
    rw [← compl_union_self (closedBall c R)]; exact hb.union isBounded_closedBall
  exact NormedSpace.unbounded_univ ℝ Pt this

/-- A set containing the outside of a ball about `c`, not containing `c`, and closed under
pushing points outwards along rays from `c`, is connected and unbounded. -/
theorem isConnected_of_outward {S : Set Pt} {c : Pt} (hc : c ∉ S)
    (hray : ∀ x ∈ S, ∀ s : ℝ, 1 ≤ s → c + s • (x - c) ∈ S) {R : ℝ}
    (hR : (closedBall c R)ᶜ ⊆ S) : IsConnected S ∧ ¬ Bornology.IsBounded S := by
  obtain ⟨hBc, hBu⟩ := isConnected_compl_closedBall_pt c R
  refine ⟨⟨hBc.nonempty.mono hR, ?_⟩, fun hb => hBu (hb.subset hR)⟩
  obtain ⟨x₀, hx₀⟩ := hBc.nonempty
  refine isPreconnected_of_forall x₀ fun y hy => ?_
  set ray := (fun s : ℝ => c + s • (y - c)) '' Ici 1
  have hyc : y ≠ c := fun h => hc (h ▸ hy)
  have hray_c : IsPreconnected ray :=
    isPreconnected_Ici.image _ (Continuous.continuousOn (by fun_prop))
  have hyr : y ∈ ray := ⟨1, self_mem_Ici, by simp⟩
  have hn : 0 < ‖y - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hyc)
  set s := max 1 ((|R| + 1) / ‖y - c‖)
  have hs1 : 1 ≤ s := le_max_left _ _
  have hfar : c + s • (y - c) ∈ (closedBall c R)ᶜ := by
    simp only [mem_compl_iff, mem_closedBall, dist_eq_norm, add_sub_cancel_left, not_le,
      norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < s by linarith)]
    have : (|R| + 1) / ‖y - c‖ ≤ s := le_max_right _ _
    rw [div_le_iff₀ hn] at this
    linarith [le_abs_self R]
  refine ⟨(closedBall c R)ᶜ ∪ ray, union_subset hR ?_, Or.inl hx₀, Or.inr hyr,
    hBc.isPreconnected.union _ hfar ⟨s, hs1, rfl⟩ hray_c⟩
  rintro _ ⟨s', hs', rfl⟩
  exact hray y hy s' hs'

theorem StrongStar.pull {N : Set Pt} {c : Pt} (h : StrongStar N c) {x : Pt} {s : ℝ} (hs : 1 < s)
    (hy : c + s • (x - c) ∈ closure N) : x ∈ N := by
  have := h _ hy (1 / s) (by positivity) (by rw [div_lt_one (by linarith)]; exact hs)
  convert this using 1
  rw [add_sub_cancel_left, smul_smul, one_div_mul_cancel (by linarith), one_smul, add_sub_cancel]

/-- The complement of a bounded strongly star-shaped set is connected and unbounded. -/
theorem StrongStar.compl_connected {N : Set Pt} {c : Pt} (h : StrongStar N c) (hc : c ∈ N)
    (hb : Bornology.IsBounded N) : IsConnected Nᶜ ∧ ¬ Bornology.IsBounded Nᶜ := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall c
  refine isConnected_of_outward (fun h' => h' hc) (fun x hx s hs hy => ?_)
    (compl_subset_compl.2 hR)
  rcases eq_or_lt_of_le hs with rfl | hs
  · exact hx (by simpa using hy)
  · exact hx (h.pull hs (subset_closure hy))

/-- The exterior (complement of the closure) of a bounded strongly star-shaped set is connected
and unbounded. -/
theorem StrongStar.compl_closure_connected {N : Set Pt} {c : Pt} (h : StrongStar N c)
    (hc : c ∈ N) (hb : Bornology.IsBounded N) :
    IsConnected (closure N)ᶜ ∧ ¬ Bornology.IsBounded (closure N)ᶜ := by
  obtain ⟨R, hR⟩ := hb.closure.subset_closedBall c
  refine isConnected_of_outward (fun h' => h' (subset_closure hc)) (fun x hx s hs hy => ?_)
    (compl_subset_compl.2 hR)
  rcases eq_or_lt_of_le hs with rfl | hs
  · exact hx (by simpa using hy)
  · exact hx (subset_closure (h.pull hs hy))

/-! ### The notched square -/

/-- The centre of the grid square of index `(a, b)`. -/
noncomputable def sqCentre (o : Pt) (δ : ℝ) (a b : ℤ) : Pt := (o.1 + δ * a + δ / 2, o.2 + δ * b + δ / 2)

theorem strongStar_notched (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) :
    StrongStar (notched o δ η r a b) (sqCentre o δ a b) ∧
      sqCentre o δ a b ∈ notched o δ η r a b := by
  have hc : sqCentre o δ a b ∈ notched o δ η r a b := by
    left; left
    simp only [sqCentre, mem_prod, mem_Ioo]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  refine ⟨?_, hc⟩
  have hc2 : sqCentre o δ a b ∈ Ioo (o.1 + δ * a + r) (o.1 + δ * (a + 1) - r) ×ˢ
      Ioo (o.2 + δ * b - η) (o.2 + δ * (b + 1) + η) := by
    simp only [sqCentre, mem_prod, mem_Ioo]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  have hc3 : sqCentre o δ a b ∈ Ioo (o.1 + δ * a - η) (o.1 + δ * (a + 1) + η) ×ˢ
      Ioo (o.2 + δ * b + r) (o.2 + δ * (b + 1) - r) := by
    simp only [sqCentre, mem_prod, mem_Ioo]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  have hc1 : sqCentre o δ a b ∈ Ioo (o.1 + δ * a) (o.1 + δ * (a + 1)) ×ˢ
      Ioo (o.2 + δ * b) (o.2 + δ * (b + 1)) := by
    simp only [sqCentre, mem_prod, mem_Ioo]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  exact strongStar_of_convex (isOpen_Ioo.prod isOpen_Ioo) (isOpen_Ioo.prod isOpen_Ioo)
    (isOpen_Ioo.prod isOpen_Ioo) ((convex_Ioo _ _).prod (convex_Ioo _ _))
    ((convex_Ioo _ _).prod (convex_Ioo _ _)) ((convex_Ioo _ _).prod (convex_Ioo _ _)) hc1 hc2 hc3

end HPC.Plane
