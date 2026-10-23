import HPC.Moore.M25BDefs
import HPC.Plane.JanPoly

/-!
# Batch 146: refutations in the decomposition of the plane into its points

The decomposition `ptSetoid` of `S` into its points satisfies Moore's standing hypothesis
(`mooreDecomp_ptSetoid`), and `Quotient.mk` is a homeomorphism `ptHomeo : Pt ≃ₜ Quotient ptSetoid`.
Statements about sets of elements are therefore statements about plane sets, and the printed forms
of Theorems 2, 7, 10, 11 (and Mullikin's Theorem 5) are refuted by explicit plane examples.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

/-- The decomposition of the plane into its points. -/
def ptSetoid : Setoid Pt := ⟨(· = ·), ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

theorem elt_ptSetoid (x : Pt) : elt ptSetoid x = {x} := by
  ext y; rfl

theorem isConnected_compl_singleton_pt (x : Pt) : IsConnected ({x}ᶜ : Set Pt) := by
  have := isConnected_diff_singleton_of_isOpen isOpen_univ isConnected_univ x
  rwa [← compl_eq_univ_diff] at this

/-- The decomposition into points satisfies the standing hypothesis of §I. -/
theorem mooreDecomp_ptSetoid : MooreDecomp ptSetoid where
  compact x := by rw [elt_ptSetoid]; exact isCompact_singleton
  connected x := by rw [elt_ptSetoid]; exact isConnected_singleton
  nonsep x := by rw [elt_ptSetoid, SeparatesPlane, not_not]; exact isConnected_compl_singleton_pt x
  usc x e he := ⟨e, he, fun y ⟨p, hp, hpd⟩ q hq => by
    rw [elt_ptSetoid, mem_singleton_iff] at hp hq
    rw [hq, ← hp]; exact hpd⟩

/-- For the decomposition into points, `Quotient.mk` is a homeomorphism. -/
def ptHomeo : Pt ≃ₜ Quotient ptSetoid where
  toFun := Quotient.mk ptSetoid
  invFun := Quotient.lift id (fun _ _ h => h)
  left_inv _ := rfl
  right_inv q := by induction q using Quotient.inductionOn; rfl
  continuous_toFun := continuous_quotient_mk'
  continuous_invFun := continuous_quot_lift _ continuous_id

theorem ptHomeo_apply (x : Pt) : ptHomeo x = Quotient.mk ptSetoid x := rfl

theorem ptsOf_ptHomeo (H : Set (Quotient ptSetoid)) : ptsOf ptSetoid H = ptHomeo ⁻¹' H := rfl

theorem ptsOf_ptHomeo_image (S : Set Pt) : ptsOf ptSetoid (ptHomeo '' S) = S :=
  ptHomeo.preimage_image S

/-! ## Plane facts -/

theorem not_isPreconnected_of_split {X : Type*} [TopologicalSpace X] {s u v : Set X}
    (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v) (hs : s ⊆ u ∪ v) {a b : X} (ha : a ∈ s)
    (hau : a ∈ u) (hb : b ∈ s) (hbv : b ∈ v) : ¬ IsPreconnected s := fun h => by
  rcases h.subset_or_subset hu hv huv hs with h | h
  · exact disjoint_left.1 huv (h hb) hbv
  · exact disjoint_left.1 huv hau (h ha)

theorem false_of_split {X : Type*} [TopologicalSpace X] {C U V : Set X} (hC : IsPreconnected C)
    (hU : IsOpen U) (hV : IsOpen V) (hUn : U.Nonempty) (hVn : V.Nonempty) (hUV : Disjoint U V)
    (h : U ∪ V = C) : False := by
  obtain ⟨u, hu⟩ := hUn
  obtain ⟨v, hv⟩ := hVn
  exact not_isPreconnected_of_split hU hV hUV h.ge (h ▸ Or.inl hu) hu (h ▸ Or.inr hv) hv hC

theorem convex_fst_lt (a : ℝ) : Convex ℝ {p : Pt | p.1 < a} :=
  (convex_Iio a).linear_preimage (LinearMap.fst ℝ ℝ ℝ)

theorem convex_fst_gt (a : ℝ) : Convex ℝ {p : Pt | a < p.1} :=
  (convex_Ioi a).linear_preimage (LinearMap.fst ℝ ℝ ℝ)

theorem convex_snd_lt (a : ℝ) : Convex ℝ {p : Pt | p.2 < a} :=
  (convex_Iio a).linear_preimage (LinearMap.snd ℝ ℝ ℝ)

theorem convex_snd_gt (a : ℝ) : Convex ℝ {p : Pt | a < p.2} :=
  (convex_Ioi a).linear_preimage (LinearMap.snd ℝ ℝ ℝ)

theorem isConnected_of_convex {s : Set Pt} (hs : Convex ℝ s) (x : Pt) (hx : x ∈ s) :
    IsConnected s :=
  ⟨⟨x, hx⟩, hs.isPreconnected⟩

/-- A horizontal segment. -/
def hseg (a b c : ℝ) : Set Pt := Icc a b ×ˢ {c}

theorem isCompact_hseg (a b c : ℝ) : IsCompact (hseg a b c) :=
  isCompact_Icc.prod isCompact_singleton

theorem isConnected_hseg {a b : ℝ} (h : a ≤ b) (c : ℝ) : IsConnected (hseg a b c) :=
  (isConnected_Icc h).prod isConnected_singleton

/-- A convex set minus a horizontal segment is connected, given witnesses to the left (above and
below the segment's line) and to the right. -/
theorem isConnected_convex_diff_hseg {B : Set Pt} (hB : Convex ℝ B) {a b c a' b' t : ℝ}
    (ha : a' < a) (hb : b < b') (ht : 0 < t) (h1 : (a', c + t) ∈ B) (h2 : (a', c - t) ∈ B)
    (h3 : (b', c + t) ∈ B) : IsConnected (B \ hseg a b c) := by
  have e : B \ hseg a b c = ((B ∩ {p : Pt | p.1 < a} ∪ B ∩ {p | c < p.2}) ∪ B ∩ {p | p.2 < c}) ∪
      B ∩ {p | b < p.1} := by
    ext p
    simp only [hseg, mem_diff, mem_prod, mem_Icc, mem_singleton_iff, mem_union, mem_inter_iff,
      mem_setOf_eq]
    constructor
    · rintro ⟨hp, h⟩
      by_cases h1 : p.1 < a
      · tauto
      by_cases h2 : b < p.1
      · tauto
      rcases lt_trichotomy p.2 c with h3 | h3 | h3
      · tauto
      · exact absurd ⟨⟨not_lt.1 h1, not_lt.1 h2⟩, h3⟩ h
      · tauto
    · rintro (((⟨hp, h⟩ | ⟨hp, h⟩) | ⟨hp, h⟩) | ⟨hp, h⟩) <;> refine ⟨hp, ?_⟩ <;>
        rintro ⟨⟨h1, h2⟩, h3⟩ <;> linarith
  rw [e]
  refine IsConnected.union ?_ (IsConnected.union ?_ (IsConnected.union ?_
    (isConnected_of_convex (hB.inter (convex_fst_lt a)) (a', c + t) ⟨h1, ha⟩)
    (isConnected_of_convex (hB.inter (convex_snd_gt c)) (a', c + t) ⟨h1, by simpa using ht⟩))
    (isConnected_of_convex (hB.inter (convex_snd_lt c)) (a', c - t) ⟨h2, by simpa using ht⟩))
    (isConnected_of_convex (hB.inter (convex_fst_gt b)) (b', c + t) ⟨h3, hb⟩)
  · exact ⟨(b', c + t), Or.inl (Or.inr ⟨h3, by simpa using ht⟩), h3, hb⟩
  · exact ⟨(a', c - t), Or.inl ⟨h2, ha⟩, h2, by simpa using ht⟩
  · exact ⟨(a', c + t), ⟨h1, ha⟩, h1, by simpa using ht⟩

/-- The complement of a horizontal segment is connected. -/
theorem isConnected_compl_hseg (a b c : ℝ) : IsConnected (hseg a b c)ᶜ := by
  rw [compl_eq_univ_diff]
  exact isConnected_convex_diff_hseg convex_univ (show a - 1 < a by linarith)
    (show b < b + 1 by linarith) one_pos trivial trivial trivial

theorem frontier_compl_hseg_subset (a b c : ℝ) : frontier (hseg a b c)ᶜ ⊆ hseg a b c := by
  rw [frontier_compl]
  exact (isCompact_hseg a b c).isClosed.frontier_subset

/-- Every point of the segment is approached from above by points of `s`. -/
theorem hseg_subset_closure {a b c : ℝ} {s : Set Pt}
    (hs : ∀ z ∈ hseg a b c, ∀ δ, 0 < δ → δ ≤ 1 / 4 → (z.1, c + δ) ∈ s) :
    hseg a b c ⊆ closure s := by
  intro z hz
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨(z.1, c + min ε (1 / 4) / 2), hs z hz _ (by positivity) ?_, ?_⟩
  · have := min_le_right ε (1 / 4); linarith
  · have hz2 : z.2 = c := hz.2
    have h1 := min_le_left ε (1 / 4)
    have h2 : 0 < min ε (1 / 4) := lt_min hε (by norm_num)
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hz2]
    simp only [sub_self, abs_zero]
    rw [max_lt_iff]
    refine ⟨hε, ?_⟩
    rw [show c - (c + min ε (1 / 4) / 2) = -(min ε (1 / 4) / 2) by ring, abs_neg,
      abs_of_pos (by positivity)]
    linarith

theorem frontier_compl_hseg (a b c : ℝ) : frontier (hseg a b c)ᶜ = hseg a b c := by
  refine (frontier_compl_hseg_subset a b c).antisymm fun z hz => ⟨?_, ?_⟩
  · refine hseg_subset_closure (fun w _ δ hδ _ => ?_) hz
    rintro ⟨-, h⟩
    have : c + δ = c := h
    linarith
  · rw [(isCompact_hseg a b c).isClosed.isOpen_compl.interior_eq]
    exact fun h => h hz

end HPC.Moore
