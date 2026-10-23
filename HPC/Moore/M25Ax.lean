import HPC.Moore.M25Thm2
import HPC.Moore.Thm15

/-!
# Batch 145, item G: the unnumbered claim of p. 420 (Axioms 1, 2, 4, 5 and F.A. Theorem 4)

Moore 1925, p. 420: for the space `S(G)` of elements, with Moore's regions, "Axioms 1, 2, 4 and 5
and Theorem 4 of F. A. hold true" (no proof printed: "methods largely analogous to those used in a
similar connection in my paper *Concerning the prime parts of a continuum*").

The proofs here go through the quotient topology:

* **Axiom 1.** The quotient is metrizable (`quotient_metrizable_plane`). Level `k`: a finite cover
  of the compact set of elements meeting the disc `‖x‖ ≤ k` by Moore regions lying in balls of
  radius `1/(k+1)` (Theorem 3, through `exists_region_subset`). The levels are laid end to end
  (`blockStart`, `levelOf`). Moore's `Kₙ'` is the quotient closure (`cl_eq_closure_quot`).
* **Axiom 2.** Regions are connected in the quotient, and Moore's connectedness is quotient
  connectedness once Axiom 1 holds (`isConn_iff`, `spaceOfElts_topology`).
* **Axiom 4.** `R'` is the quotient closure of `R`, inside the image of the compact set
  `closure R̄`.
* **Axiom 5.** The elements containing the points `(n, 0)`: infinitely many (the quotient map is
  proper), with no limit element (a tube about any element meets only finitely many of them).
* **F.A. Theorem 4.** A finite nonempty region would have a compact open nonempty point set.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

/-! ### Laying finite families end to end -/

/-- The start of block `k` when block `j` has length `len j`. -/
def blockStart (len : ℕ → ℕ) (k : ℕ) : ℕ := ∑ j ∈ Finset.range k, len j

theorem blockStart_mono {len : ℕ → ℕ} {a b : ℕ} (h : a ≤ b) :
    blockStart len a ≤ blockStart len b :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)

section Blocks

variable {len : ℕ → ℕ} (hlen : ∀ j, 1 ≤ len j)
include hlen

theorem le_blockStart (k : ℕ) : k ≤ blockStart len k := by
  induction k with
  | zero => simp [blockStart]
  | succ k ih =>
    simp only [blockStart, Finset.sum_range_succ] at ih ⊢
    have := hlen k; omega

theorem exists_level (n : ℕ) : ∃ k, n < blockStart len (k + 1) :=
  ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (le_blockStart hlen (n + 1))⟩

open Classical in
/-- The block containing position `n`. -/
noncomputable def levelOf (n : ℕ) : ℕ := Nat.find (exists_level hlen n)

theorem lt_blockStart_levelOf (n : ℕ) : n < blockStart len (levelOf hlen n + 1) := by
  classical exact Nat.find_spec (exists_level hlen n)

theorem le_levelOf {n k : ℕ} (h : blockStart len k ≤ n) : k ≤ levelOf hlen n := by
  by_contra hk
  push_neg at hk
  have := blockStart_mono (len := len) (by omega : levelOf hlen n + 1 ≤ k)
  have := lt_blockStart_levelOf hlen n
  omega

theorem levelOf_eq {n k : ℕ} (h1 : blockStart len k ≤ n) (h2 : n < blockStart len (k + 1)) :
    levelOf hlen n = k := by
  classical
  refine le_antisymm (Nat.find_min' (exists_level hlen n) h2) (le_levelOf hlen h1)

end Blocks

/-! ### Two facts about the points `(n, 0)` -/

theorem not_isBounded_of_forall_nat {T : Set Pt} (hT : ∀ n : ℕ, ((n : ℝ), (0 : ℝ)) ∈ T) :
    ¬ Bornology.IsBounded T := by
  intro hb
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1 hb
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have h1 := hC _ (hT n)
  have h2 : ‖((n : ℝ), (0 : ℝ)).1‖ ≤ ‖((n : ℝ), (0 : ℝ))‖ := norm_fst_le _
  simp only [Real.norm_natCast] at h2
  linarith

variable {r : Setoid Pt}

section hG

variable (hG : MooreDecomp r)
include hG

/-- **Axiom 1** for the space of elements. -/
theorem m25_axiom1 : (spaceOfElts r).Axiom1 := by
  haveI := quotient_metrizable_plane hG
  letI := TopologicalSpace.metrizableSpaceMetric (Quotient r)
  -- regions about `q` in the ball of radius `1/(k+1)`
  have hreg : ∀ (k : ℕ) (q : Quotient r), ∃ R, mooreRegion R ∧ q ∈ R ∧
      R ⊆ ball q (1 / ((k : ℝ) + 1)) := fun k q =>
    exists_region_subset hG (ball_mem_nhds q (by positivity))
  choose Rg hRg hqR hRball using hreg
  -- level `k`: a finite cover of the elements meeting `closedBall 0 k`
  have hcov : ∀ k : ℕ, ∃ t : Finset (Quotient r),
      Quotient.mk r '' closedBall (0 : Pt) k ⊆ ⋃ q ∈ t, Rg k q := fun k =>
    (isCompact_closedBall (0 : Pt) k).image continuous_mk |>.elim_finite_subcover
      (fun q => Rg k q) (fun q => (hRg k q).1)
      (fun x _ => mem_iUnion.2 ⟨x, hqR k x⟩)
  choose t ht using hcov
  set q0 : Quotient r := Quotient.mk r 0
  set l : ℕ → List (Quotient r) := fun k => q0 :: (t k).toList with hl
  have hlen : ∀ k, 1 ≤ (l k).length := fun k => by simp [hl]
  set lev := levelOf hlen with hlev
  set K : ℕ → Set (Quotient r) := fun n =>
    Rg (lev n) ((l (lev n)).getD (n - blockStart (fun k => (l k).length) (lev n)) q0) with hK
  refine ⟨K, fun n => hRg _ _, ?_, ?_⟩
  · -- every element lies in `Kₙ` for arbitrarily large `n`
    intro m P
    obtain ⟨X, rfl⟩ := Quotient.mk_surjective P
    obtain ⟨k, hk⟩ := exists_nat_gt (max (m : ℝ) ‖X‖)
    have hXk : X ∈ closedBall (0 : Pt) k := by
      rw [mem_closedBall, dist_zero_right]; exact (le_max_right _ _).trans hk.le
    obtain ⟨q, hq, hPq⟩ := mem_iUnion₂.1 (ht k (mem_image_of_mem _ hXk))
    have hql : q ∈ l k := by simp [hl, hq]
    obtain ⟨i, hi, hqi⟩ := List.getElem_of_mem hql
    set n := blockStart (fun k => (l k).length) k + i
    have hb1 : blockStart (fun k => (l k).length) k ≤ n := Nat.le_add_right _ _
    have hb2 : n < blockStart (fun k => (l k).length) (k + 1) := by
      simp only [n, blockStart, Finset.sum_range_succ]; omega
    have hlevn : lev n = k := levelOf_eq hlen hb1 hb2
    have hmk : m < k := by exact_mod_cast (le_max_left _ _).trans_lt hk
    refine ⟨n, ?_, ?_⟩
    · exact lt_of_lt_of_le hmk ((le_blockStart hlen k).trans hb1)
    · simp only [hK, hlevn]
      rw [show n - blockStart (fun k => (l k).length) k = i by omega, List.getD_eq_getElem _ _ hi,
        hqi]
      exact hPq
  · -- Axiom 1 (2)
    intro R hR P hPR P' hP'R hPP'
    obtain ⟨ε, hε, hεR⟩ := Metric.isOpen_iff.1 hR.1 P hPR
    have hd : 0 < dist P P' := dist_pos.2 hPP'
    set ε' := min ε (dist P P')
    have hε' : 0 < ε' := lt_min hε hd
    obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt (half_pos hε')
    refine ⟨blockStart (fun k => (l k).length) k0, fun n hn hPn => ?_⟩
    have hlevn : k0 ≤ lev n := le_levelOf hlen hn.le
    rw [cl_eq_closure_quot hG]
    set q := (l (lev n)).getD (n - blockStart (fun k => (l k).length) (lev n)) q0
    have hsub : closure (K n) ⊆ closedBall q (1 / ((lev n : ℝ) + 1)) :=
      (closure_mono (hRball _ _)).trans closure_ball_subset_closedBall
    have hsmall : 1 / ((lev n : ℝ) + 1) ≤ 1 / ((k0 : ℝ) + 1) := by
      gcongr
    have hPq : dist P q < 1 / ((lev n : ℝ) + 1) := mem_ball.1 (hRball _ _ hPn)
    intro z hz
    have hzq : dist z q ≤ 1 / ((lev n : ℝ) + 1) := mem_closedBall.1 (hsub hz)
    have hzP : dist z P < ε' := by
      have := dist_triangle_right z P q
      linarith
    refine ⟨hεR (mem_ball.2 (hzP.trans_le (min_le_left _ _))), fun hzP' => ?_⟩
    rw [mem_singleton_iff] at hzP'
    subst hzP'
    rw [dist_comm] at hzP
    exact absurd (hzP.trans_le (min_le_right _ _)) (lt_irrefl _)

/-- **Axiom 2** for the space of elements: every region is connected. -/
theorem m25_axiom2 : (spaceOfElts r).Axiom2 := by
  intro R hR
  rw [isConn_iff (m25_axiom1 hG), spaceOfElts_topology hG]
  exact hR.2.1.isPreconnected

/-- **Axiom 4** for the space of elements: `R'` has the Heine–Borel property. -/
theorem m25_axiom4 : (spaceOfElts r).Axiom4 := by
  intro R hR
  rw [heineBorel_iff, spaceOfElts_topology hG, cl_eq_closure_quot hG]
  have hc : IsCompact (Quotient.mk r '' closure (ptsOf r R)) :=
    hR.2.2.1.isCompact_closure.image continuous_mk
  refine hc.of_isClosed_subset isClosed_closure (closure_minimal ?_
    (isClosedMap_mk_plane hG _ isClosed_closure))
  calc R = Quotient.mk r '' ptsOf r R := (image_ptsOf R).symm
    _ ⊆ _ := image_mono subset_closure

/-- **Axiom 5** for the space of elements: the elements containing the points `(n, 0)` form an
infinite set with no limit element. -/
theorem m25_axiom5 : (spaceOfElts r).Axiom5 := by
  haveI := t1Space_quot hG
  set f : ℕ → Quotient r := fun n => Quotient.mk r ((n : ℝ), (0 : ℝ)) with hf
  refine ⟨range f, fun hfin => ?_, fun p hp => ?_⟩
  · have hc : IsCompact (ptsOf r (range f)) := (isProperMap_mk hG).isCompact_preimage hfin.isCompact
    exact not_isBounded_of_forall_nat (T := ptsOf r (range f)) (fun n => ⟨n, rfl⟩) hc.isBounded
  · rw [← m25_theorem4 hG, isLimitElt_iff hG, accPt_iff_nhds] at hp
    obtain ⟨X, rfl⟩ := Quotient.mk_surjective p
    obtain ⟨N, hN⟩ := (isCompact_ptsOf_singleton hG (Quotient.mk r X)).isBounded.subset_ball
      (0 : Pt)
    set U := tube r (ball (0 : Pt) N)
    have hpU : Quotient.mk r X ∈ U := hN
    have hfinU : (range f ∩ U).Finite := by
      refine ((finite_lt_nat ⌈N⌉₊).image f).subset ?_
      rintro _ ⟨⟨n, rfl⟩, hnU⟩
      refine ⟨n, ?_, rfl⟩
      have h1 : ((n : ℝ), (0 : ℝ)) ∈ ball (0 : Pt) N := mem_of_mem_tube hnU rfl
      rw [mem_ball, dist_zero_right] at h1
      have h2 : ‖((n : ℝ), (0 : ℝ)).1‖ ≤ ‖((n : ℝ), (0 : ℝ))‖ := norm_fst_le _
      simp only [Real.norm_natCast] at h2
      have : (n : ℝ) < ⌈N⌉₊ := lt_of_lt_of_le (h2.trans_lt h1) (Nat.le_ceil N)
      exact_mod_cast this
    have hV : U \ ((range f ∩ U) \ {Quotient.mk r X}) ∈ 𝓝 (Quotient.mk r X) := by
      refine Filter.inter_mem ((isOpen_tube hG isOpen_ball).mem_nhds hpU) ?_
      exact ((hfinU.diff).isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl))
    obtain ⟨y, ⟨hyV, hyM⟩, hyp⟩ := hp _ hV
    exact hyV.2 ⟨⟨hyM, hyV.1⟩, hyp⟩

/-- **F.A. Theorem 4** for the space of elements: every nonempty region is infinite. -/
theorem m25_region_infinite {R : Set (Quotient r)} (hR : mooreRegion R) (hne : R.Nonempty) :
    R.Infinite := by
  intro hfin
  have hc : IsCompact (ptsOf r R) := (isProperMap_mk hG).isCompact_preimage hfin.isCompact
  have hcl : IsClopen (ptsOf r R) := ⟨hc.isClosed, isOpen_iff_ptsOf.1 hR.1⟩
  obtain ⟨q, hq⟩ := hne
  obtain ⟨X, rfl⟩ := Quotient.mk_surjective q
  have huniv := hcl.eq_univ ⟨X, hq⟩
  exact not_isBounded_of_forall_nat (T := ptsOf r R) (fun n => huniv ▸ mem_univ _) hc.isBounded

/-- **The unnumbered claim of p. 420.** Axioms 1, 2, 4, 5 and F.A. Theorem 4 (for nonempty regions)
hold for the space of elements with Moore's regions. -/
theorem m25_axioms1245 :
    (spaceOfElts r).Axiom1 ∧ (spaceOfElts r).Axiom2 ∧ (spaceOfElts r).Axiom4 ∧
      (spaceOfElts r).Axiom5 ∧
      ∀ R ∈ (spaceOfElts r).region, R.Nonempty → R.Infinite :=
  ⟨m25_axiom1 hG, m25_axiom2 hG, m25_axiom4 hG, m25_axiom5 hG,
    fun _ hR hne => m25_region_infinite hG hR hne⟩

end hG

end HPC.Moore
