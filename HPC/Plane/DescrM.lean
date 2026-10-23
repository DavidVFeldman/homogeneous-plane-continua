import HPC.Plane.PseudoArc51

/-!
# A pseudo-arc inside the standard chain of `m` rectangles

Batch 90 (COMMISSION-batch90.md §3.6). The construction of `HPC/Plane/Descr.lean` (batch 84)
started from the standard chain of three rectangles; here it starts from the standard chain of
`m ≥ 3` rectangles `stdRect j`, `j < m`, with every later step unchanged (`desc_step`). The
continuum of the resulting description is a pseudo-arc inside `⋃_{j<m} stdRect j` meeting every
`stdRect j`.
-/

namespace HPC.Plane

open Set Metric HPC.Fold

namespace DM

variable (m₀ : ℕ) (hm₀ : 3 ≤ m₀)

/-- The levels of the construction, starting from the standard chain of `m₀` rectangles. -/
noncomputable def dstage : ℕ → DStage
  | 0 => ⟨m₀, Homeomorph.refl _, hm₀⟩
  | i + 1 => Classical.choose (desc_step (dstage i) (ε := 1 / 2 ^ i) (by positivity))

/-- The stutter factor used at step `i`. -/
noncomputable def dK (i : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec
    (desc_step (dstage m₀ hm₀ i) (ε := 1 / 2 ^ i) (by positivity)))

theorem dstage_spec (i : ℕ) :
    2 ≤ dK m₀ hm₀ i ∧ (dstage m₀ hm₀ (i + 1)).m = dK m₀ hm₀ i * z ((dstage m₀ hm₀ i).m - 1) ∧
      (∀ t : Fin (dstage m₀ hm₀ (i + 1)).m, ∃ l : Fin (dstage m₀ hm₀ i).m,
        (l : ℤ) = stut ((dstage m₀ hm₀ i).m - 1) (dK m₀ hm₀ i) t ∧
        closure ((tameChain (dstage m₀ hm₀ (i + 1)).Φ (dstage m₀ hm₀ (i + 1)).m).link t) ⊆
          (tameChain (dstage m₀ hm₀ i).Φ (dstage m₀ hm₀ i).m).link l) ∧
      (∀ (t : Fin (dstage m₀ hm₀ (i + 1)).m) (l : Fin (dstage m₀ hm₀ i).m),
        ((tameChain (dstage m₀ hm₀ (i + 1)).Φ (dstage m₀ hm₀ (i + 1)).m).link t ∩
          (tameChain (dstage m₀ hm₀ i).Φ (dstage m₀ hm₀ i).m).link l).Nonempty →
        ∃ u' : ℕ, u' < (dstage m₀ hm₀ (i + 1)).m ∧ u' ≤ t.val + 1 ∧ t.val ≤ u' + 1 ∧
          (l : ℤ) = stut ((dstage m₀ hm₀ i).m - 1) (dK m₀ hm₀ i) u') ∧
      (∀ t : Fin (dstage m₀ hm₀ (i + 1)).m,
        diam ((tameChain (dstage m₀ hm₀ (i + 1)).Φ (dstage m₀ hm₀ (i + 1)).m).link t) ≤ 1 / 2 ^ i ∨
        ∃ k : ℕ, k < (dstage m₀ hm₀ i).m ∧
          (tameChain (dstage m₀ hm₀ (i + 1)).Φ (dstage m₀ hm₀ (i + 1)).m).link t ⊆
            (dstage m₀ hm₀ i).Φ '' zone k) ∧
      (∀ k : ℕ, k < (dstage m₀ hm₀ (i + 1)).m →
        Bornology.IsBounded ((dstage m₀ hm₀ (i + 1)).Φ '' zone k) ∧
        diam ((dstage m₀ hm₀ (i + 1)).Φ '' zone k) ≤ 1 / 2 ^ i) ∧
      (dstage m₀ hm₀ (i + 1)).Φ '' boxA ⊆ (dstage m₀ hm₀ i).Φ '' boxA ∧
      (dstage m₀ hm₀ (i + 1)).Φ '' boxB (dstage m₀ hm₀ (i + 1)).m ⊆
        (dstage m₀ hm₀ i).Φ '' boxB (dstage m₀ hm₀ i).m :=
  Classical.choose_spec (Classical.choose_spec
    (desc_step (dstage m₀ hm₀ i) (ε := 1 / 2 ^ i) (by positivity)))

/-- The chains of the construction. -/
noncomputable def dchain (i : ℕ) : Chain Pt (dstage m₀ hm₀ i).m :=
  tameChain (dstage m₀ hm₀ i).Φ (dstage m₀ hm₀ i).m

theorem dstage_zero_m : (dstage m₀ hm₀ 0).m = m₀ := rfl

theorem dstage_zero_Φ (p : Pt) : (dstage m₀ hm₀ 0).Φ p = p := rfl

theorem dzone_diam (i : ℕ) (k : ℕ) (hk : k < (dstage m₀ hm₀ i).m) :
    Bornology.IsBounded ((dstage m₀ hm₀ i).Φ '' zone k) ∧
      diam ((dstage m₀ hm₀ i).Φ '' zone k) ≤ 2 / 2 ^ i := by
  cases i with
  | zero =>
      have e : (dstage m₀ hm₀ 0).Φ '' zone k = zone k := by
        ext p; simp [dstage_zero_Φ]
      rw [e]
      exact ⟨(isCompact_zone k).isBounded, by simpa using diam_zone_le k⟩
  | succ i =>
      obtain ⟨b, d⟩ := (dstage_spec m₀ hm₀ i).2.2.2.2.2.1 k hk
      refine ⟨b, d.trans (le_of_eq ?_)⟩
      rw [pow_succ]; field_simp

theorem dlink_diam (i : ℕ) (t : Fin (dstage m₀ hm₀ i).m) :
    diam ((dchain m₀ hm₀ i).link t) ≤ 4 / 2 ^ i := by
  cases i with
  | zero =>
      have e : (dchain m₀ hm₀ 0).link t = stdRect t := by
        ext p; simp [dchain, dstage_zero_Φ, tameChain]
      rw [e]; simp only [pow_zero, div_one]; linarith [diam_stdRect_le t]
  | succ i =>
      rcases (dstage_spec m₀ hm₀ i).2.2.2.2.1 t with h | ⟨k, hk, hs⟩
      · refine h.trans ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]; nlinarith [pow_pos
          (show (0 : ℝ) < 2 by norm_num) i]
      · obtain ⟨b, d⟩ := dzone_diam m₀ hm₀ i k hk
        refine (diam_mono hs b).trans (d.trans (le_of_eq ?_))
        rw [pow_succ]; field_simp; norm_num

theorem exists_P : (⋂ i, (dstage m₀ hm₀ i).Φ '' boxA).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
  · intro i; exact (dstage_spec m₀ hm₀ i).2.2.2.2.2.2.1
  · intro i; exact boxA_nonempty.image _
  · exact isCompact_boxA.image (dstage m₀ hm₀ 0).Φ.continuous
  · intro i; exact (isCompact_boxA.image (dstage m₀ hm₀ i).Φ.continuous).isClosed

theorem exists_Q : (⋂ i, (dstage m₀ hm₀ i).Φ '' boxB (dstage m₀ hm₀ i).m).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
  · intro i; exact (dstage_spec m₀ hm₀ i).2.2.2.2.2.2.2
  · intro i; exact (boxB_nonempty _).image _
  · exact (isCompact_boxB _).image (dstage m₀ hm₀ 0).Φ.continuous
  · intro i; exact ((isCompact_boxB _).image (dstage m₀ hm₀ i).Φ.continuous).isClosed

theorem isFrom_of {P Q : Pt} (hP : P ∈ ⋂ i, (dstage m₀ hm₀ i).Φ '' boxA)
    (hQ : Q ∈ ⋂ i, (dstage m₀ hm₀ i).Φ '' boxB (dstage m₀ hm₀ i).m) (i : ℕ) :
    (dchain m₀ hm₀ i).IsFrom P Q := by
  have hm := (dstage m₀ hm₀ i).hm
  rw [mem_iInter] at hP hQ
  obtain ⟨a, ha, rfl⟩ := hP i
  obtain ⟨b, hb, hbQ⟩ := hQ i
  refine ⟨by omega, ⟨a, boxA_subset_stdRect ha, rfl⟩, ⟨b, ?_, hbQ⟩, ?_, ?_⟩
  · have := boxB_subset_stdRect (show 0 < (dstage m₀ hm₀ i).m by omega) hb
    simpa using this
  · intro j hj
    obtain ⟨a', ha', e⟩ := hj
    have := (dstage m₀ hm₀ i).Φ.injective e
    subst this
    by_contra hne
    have hj0 : (j : ℕ) ≠ 0 := fun h => hne (Fin.ext h)
    exact Set.disjoint_left.mp (boxA_disjoint hj0) ha ha'
  · intro j hj
    obtain ⟨b', hb', e⟩ := hj
    rw [← hbQ] at e
    have := (dstage m₀ hm₀ i).Φ.injective e
    subst this
    by_contra hne
    have hj1 : (j : ℕ) + 1 < (dstage m₀ hm₀ i).m := by
      have : (j : ℕ) ≠ (dstage m₀ hm₀ i).m - 1 := fun h => hne (Fin.ext h)
      omega
    exact Set.disjoint_left.mp (boxB_disjoint hj1) hb hb'

/-- The description of a pseudo-arc in the plane, starting from `m₀` standard rectangles. -/
noncomputable def planeDescription {P Q : Pt} (hP : P ∈ ⋂ i, (dstage m₀ hm₀ i).Φ '' boxA)
    (hQ : Q ∈ ⋂ i, (dstage m₀ hm₀ i).Φ '' boxB (dstage m₀ hm₀ i).m) : Description Pt P Q where
  n i := (dstage m₀ hm₀ i).m
  D := dchain m₀ hm₀
  isFrom := isFrom_of m₀ hm₀ hP hQ
  crooked i := by
    obtain ⟨hK, hm, h1, h2, -⟩ := dstage_spec m₀ hm₀ i
    refine crooked_of_tight_pat (stut ((dstage m₀ hm₀ i).m - 1) (dK m₀ hm₀ i)) (stut_lip _ _) ?_
      (fun u => ?_) h2
    · rw [hm]; exact stut_crooked _ _ (by omega)
    · obtain ⟨l, hl, hs⟩ := h1 u
      exact ⟨l, hl, subset_closure.trans hs⟩
  closure_subset i t := by
    obtain ⟨l, -, hs⟩ := (dstage_spec m₀ hm₀ i).2.2.1 t
    exact ⟨l, hs⟩
  ε i := 4 / 2 ^ i
  ε_pos i := by positivity
  ε_tendsto := by
    have : Filter.Tendsto (fun i : ℕ => (4 : ℝ) * (1 / 2) ^ i) Filter.atTop (nhds (4 * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 4
    simp only [mul_zero] at this
    refine this.congr fun i => ?_
    rw [one_div, inv_pow]; ring
  bdd i t := tameChain_link_bounded _ _ t
  diam_le i t := dlink_diam m₀ hm₀ i t

end DM

/-- **A pseudo-arc inside the standard chain of `m ≥ 3` rectangles**, meeting every rectangle. -/
theorem exists_pseudoArc_stdRect {m : ℕ} (hm : 3 ≤ m) :
    ∃ M : Set Pt, IsPseudoArc M ∧ M ⊆ ⋃ j : Fin m, stdRect j ∧
      ∀ j : Fin m, (M ∩ stdRect j).Nonempty := by
  obtain ⟨P, hP⟩ := DM.exists_P m hm
  obtain ⟨Q, hQ⟩ := DM.exists_Q m hm
  set Δ := DM.planeDescription m hm hP hQ
  have hPQ : P ≠ Q := by
    rintro rfl
    obtain ⟨a, ha, e1⟩ := mem_iInter.mp hP 0
    obtain ⟨b, hb, e2⟩ := mem_iInter.mp hQ 0
    rw [DM.dstage_zero_Φ] at e1 e2
    subst e1
    rw [e2, DM.dstage_zero_m] at hb
    obtain ⟨⟨-, h⟩, -⟩ := ha
    obtain ⟨⟨h', -⟩, -⟩ := hb
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨hKc, hK⟩ := Description.links_subset_compact Δ
  have hpa := isPseudoArc_of_description Δ hPQ _ hK hKc
  have e0 : ∀ j : Fin m, (Δ.D 0).link j = stdRect j := fun j => by
    ext p; simp [Δ, DM.planeDescription, DM.dchain, DM.dstage_zero_Φ, tameChain]
  have hsub : Δ.M ⊆ (Δ.D 0).union := Δ.M_subset_union 0
  refine ⟨Δ.M, hpa, ?_, ?_⟩
  · intro x hx
    have := hsub hx
    simp only [Chain.union, mem_iUnion] at this ⊢
    obtain ⟨j, hj⟩ := this
    exact ⟨j, e0 j ▸ hj⟩
  · obtain ⟨hn, hP0, hQ1, -, -⟩ := Δ.isFrom 0
    have hn' : (Δ.n 0) = m := rfl
    intro j
    rw [← e0 j]
    have hP' : (Δ.M ∩ (Δ.D 0).link ⟨0, hn⟩).Nonempty := ⟨P, Δ.P_mem_M, hP0⟩
    have hQ' : (Δ.M ∩ (Δ.D 0).link ⟨Δ.n 0 - 1, by omega⟩).Nonempty := ⟨Q, Δ.Q_mem_M, hQ1⟩
    rcases Nat.lt_or_ge 0 j.val with h0 | h0
    · rcases Nat.lt_or_ge j.val (m - 1) with h1 | h1
      · exact Chain.inter_link_nonempty_between (Δ.D 0) hpa.1.1.2.isPreconnected hsub
          (show (⟨0, hn⟩ : Fin (Δ.n 0)) < j from Fin.lt_def.mpr h0)
          (show j < ⟨Δ.n 0 - 1, by omega⟩ from Fin.lt_def.mpr (by simp only [hn']; omega)) hP' hQ'
      · have : j = ⟨Δ.n 0 - 1, by omega⟩ := Fin.ext (by simp only [hn']; omega)
        rw [this]; exact hQ'
    · have : j = ⟨0, hn⟩ := Fin.ext (by show j.val = 0; omega)
      rw [this]; exact hP'

end HPC.Plane
