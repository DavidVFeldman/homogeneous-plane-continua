import HPC.Plane.RealStep
import HPC.Plane.Stutter
import HPC.PseudoArc.Description

/-!
# A description of the pseudo-arc in the plane

Batch 84 (COMMISSION-batch84.md §3.4). Level `0` is the standard chain of three rectangles; level
`i + 1` is produced by the planar step from level `i` along the stuttered Bing pattern
`u ↦ bingF (m_i - 1) (u / K_i)`, with `K_i` the slowness the step asks for. Tightness makes each
level crooked in the previous one (`crooked_of_tight_pat`), the nested end boxes provide the end
points `P` and `Q`.
-/

namespace HPC.Plane

open Set Metric HPC.Fold

theorem diam_stdRect_le (j : ℕ) : diam (stdRect j) ≤ 3 := by
  refine diam_le_of_forall_dist_le (by norm_num) ?_
  rintro ⟨a, b⟩ ⟨⟨h1, h2⟩, h3, h4⟩ ⟨c, d⟩ ⟨⟨h5, h6⟩, h7, h8⟩
  apply dist_le_of_abs_le
  · rw [abs_le]; simp only at *; constructor <;> linarith
  · rw [abs_le]; simp only at *; constructor <;> linarith

theorem diam_zone_le (j : ℕ) : diam (zone j) ≤ 2 := by
  refine diam_le_of_forall_dist_le (by norm_num) ?_
  rintro ⟨a, b⟩ ⟨⟨h1, h2⟩, h3, h4⟩ ⟨c, d⟩ ⟨⟨h5, h6⟩, h7, h8⟩
  apply dist_le_of_abs_le
  · rw [abs_le]; simp only at *; constructor <;> linarith
  · rw [abs_le]; simp only at *; constructor <;> linarith

theorem div_last {K z : ℕ} (hK : 2 ≤ K) (hz : 1 ≤ z) : (K * z - 1) / K = z - 1 := by
  apply Nat.div_eq_of_lt_le
  · have : (z - 1) * K = K * z - K := by
      rw [Nat.sub_mul, one_mul, mul_comm]
    have : K ≤ K * z := Nat.le_mul_of_pos_right K hz
    omega
  · have : (z - 1 + 1) * K = K * z := by rw [Nat.sub_add_cancel hz, mul_comm]
    have : 1 ≤ K * z := le_trans (by omega) (Nat.le_mul_of_pos_right K hz)
    omega

theorem div_last' {K z : ℕ} (hK : 2 ≤ K) (hz : 1 ≤ z) : (K * z - 2) / K = z - 1 := by
  apply Nat.div_eq_of_lt_le
  · have : (z - 1) * K = K * z - K := by
      rw [Nat.sub_mul, one_mul, mul_comm]
    have : K ≤ K * z := Nat.le_mul_of_pos_right K hz
    omega
  · have : (z - 1 + 1) * K = K * z := by rw [Nat.sub_add_cancel hz, mul_comm]
    have : 2 ≤ K * z := le_trans hK (Nat.le_mul_of_pos_right K hz)
    omega

/-- A level of the construction: a tame chain `Φ(stdRect j)`, `j < m`. -/
structure DStage where
  m : ℕ
  Φ : Pt ≃ₜ Pt
  hm : 3 ≤ m

/-- One step of the construction of the pseudo-arc. -/
theorem desc_step (S : DStage) {ε : ℝ} (hε : 0 < ε) :
    ∃ S' : DStage, ∃ K : ℕ, 2 ≤ K ∧ S'.m = K * z (S.m - 1) ∧
      (∀ t : Fin S'.m, ∃ i : Fin S.m, (i : ℤ) = stut (S.m - 1) K t ∧
        closure ((tameChain S'.Φ S'.m).link t) ⊆ (tameChain S.Φ S.m).link i) ∧
      (∀ (t : Fin S'.m) (l : Fin S.m),
        ((tameChain S'.Φ S'.m).link t ∩ (tameChain S.Φ S.m).link l).Nonempty →
        ∃ u' : ℕ, u' < S'.m ∧ u' ≤ t.val + 1 ∧ t.val ≤ u' + 1 ∧ (l : ℤ) = stut (S.m - 1) K u') ∧
      (∀ t : Fin S'.m, diam ((tameChain S'.Φ S'.m).link t) ≤ ε ∨
        ∃ k : ℕ, k < S.m ∧ (tameChain S'.Φ S'.m).link t ⊆ S.Φ '' zone k) ∧
      (∀ k : ℕ, k < S'.m → Bornology.IsBounded (S'.Φ '' zone k) ∧ diam (S'.Φ '' zone k) ≤ ε) ∧
      S'.Φ '' boxA ⊆ S.Φ '' boxA ∧ S'.Φ '' boxB S'.m ⊆ S.Φ '' boxB S.m := by
  have hm0 : 0 < S.m := by have := S.hm; omega
  obtain ⟨N, hN, hstep⟩ := real_step S.Φ hm0 hε
  have hz := z_pos (S.m - 1)
  have hK : 2 ≤ N := by omega
  set n := N * z (S.m - 1) with hn
  have hn12 : 12 ≤ n := le_trans hN (Nat.le_mul_of_pos_right N hz)
  obtain ⟨Ψ, h1, h2, h3, h4, h5, h6⟩ := hstep n (stutPat S.m N hm0) (by omega)
    (stutPat_unitSteps S.m N hm0) (stutPat_slow S.m N hm0 (by omega))
  have hval := stutPat_val S.m N hm0
  refine ⟨⟨n, Ψ.trans S.Φ, by omega⟩, N, hK, rfl, ?_, ?_, h3, h4, ?_, ?_⟩
  · intro t
    exact ⟨stutPat S.m N hm0 t, hval t, h1 t⟩
  · intro t l h
    obtain ⟨t', ht', e⟩ := h2 t l h
    refine ⟨t', t'.isLt, ht'.1, ht'.2, ?_⟩
    rw [e, hval]
  · apply h5 (by omega)
    · have := hval ⟨0, by omega⟩
      simp only [stut, Nat.zero_div, bingF_zero] at this
      exact_mod_cast this
    · have := hval ⟨1, by omega⟩
      simp only [stut, Nat.div_eq_of_lt (show 1 < N by omega), bingF_zero] at this
      exact_mod_cast this
  · apply h6 (by omega)
    · have := hval ⟨n - 1, by omega⟩
      simp only [stut] at this
      rw [show (n - 1) / N = z (S.m - 1) - 1 from div_last hK hz, bingF_top _ _ le_rfl] at this
      have e : ((S.m - 1 : ℕ) : ℤ) = (S.m : ℤ) - 1 := by push_cast [Nat.cast_sub hm0]; ring
      omega
    · have := hval ⟨n - 2, by omega⟩
      simp only [stut] at this
      rw [show (n - 2) / N = z (S.m - 1) - 1 from div_last' hK hz, bingF_top _ _ le_rfl] at this
      have e : ((S.m - 1 : ℕ) : ℤ) = (S.m : ℤ) - 1 := by push_cast [Nat.cast_sub hm0]; ring
      omega

/-- The levels of the construction. -/
noncomputable def dstage : ℕ → DStage
  | 0 => ⟨3, Homeomorph.refl _, le_rfl⟩
  | i + 1 => Classical.choose (desc_step (dstage i) (ε := 1 / 2 ^ i) (by positivity))

/-- The stutter factor used at step `i`. -/
noncomputable def dK (i : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (desc_step (dstage i) (ε := 1 / 2 ^ i) (by positivity)))

theorem dstage_spec (i : ℕ) :
    2 ≤ dK i ∧ (dstage (i + 1)).m = dK i * z ((dstage i).m - 1) ∧
      (∀ t : Fin (dstage (i + 1)).m, ∃ l : Fin (dstage i).m, (l : ℤ) = stut ((dstage i).m - 1) (dK i) t ∧
        closure ((tameChain (dstage (i + 1)).Φ (dstage (i + 1)).m).link t) ⊆
          (tameChain (dstage i).Φ (dstage i).m).link l) ∧
      (∀ (t : Fin (dstage (i + 1)).m) (l : Fin (dstage i).m),
        ((tameChain (dstage (i + 1)).Φ (dstage (i + 1)).m).link t ∩
          (tameChain (dstage i).Φ (dstage i).m).link l).Nonempty →
        ∃ u' : ℕ, u' < (dstage (i + 1)).m ∧ u' ≤ t.val + 1 ∧ t.val ≤ u' + 1 ∧
          (l : ℤ) = stut ((dstage i).m - 1) (dK i) u') ∧
      (∀ t : Fin (dstage (i + 1)).m,
        diam ((tameChain (dstage (i + 1)).Φ (dstage (i + 1)).m).link t) ≤ 1 / 2 ^ i ∨
        ∃ k : ℕ, k < (dstage i).m ∧
          (tameChain (dstage (i + 1)).Φ (dstage (i + 1)).m).link t ⊆ (dstage i).Φ '' zone k) ∧
      (∀ k : ℕ, k < (dstage (i + 1)).m → Bornology.IsBounded ((dstage (i + 1)).Φ '' zone k) ∧
        diam ((dstage (i + 1)).Φ '' zone k) ≤ 1 / 2 ^ i) ∧
      (dstage (i + 1)).Φ '' boxA ⊆ (dstage i).Φ '' boxA ∧
      (dstage (i + 1)).Φ '' boxB (dstage (i + 1)).m ⊆ (dstage i).Φ '' boxB (dstage i).m :=
  Classical.choose_spec (Classical.choose_spec (desc_step (dstage i) (ε := 1 / 2 ^ i) (by positivity)))

/-- The chains of the construction. -/
noncomputable def dchain (i : ℕ) : Chain Pt (dstage i).m := tameChain (dstage i).Φ (dstage i).m

theorem dstage_zero_m : (dstage 0).m = 3 := rfl

theorem dstage_zero_Φ (p : Pt) : (dstage 0).Φ p = p := rfl

/-- Zones of level `i` are small. -/
theorem dzone_diam (i : ℕ) (k : ℕ) (hk : k < (dstage i).m) :
    Bornology.IsBounded ((dstage i).Φ '' zone k) ∧ diam ((dstage i).Φ '' zone k) ≤ 2 / 2 ^ i := by
  cases i with
  | zero =>
      have e : (dstage 0).Φ '' zone k = zone k := by
        ext p; simp [dstage_zero_Φ]
      rw [e]
      exact ⟨(isCompact_zone k).isBounded, by simpa using diam_zone_le k⟩
  | succ i =>
      obtain ⟨b, d⟩ := (dstage_spec i).2.2.2.2.2.1 k hk
      refine ⟨b, d.trans (le_of_eq ?_)⟩
      rw [pow_succ]; field_simp

/-- Links of level `i` have diameter at most `4 / 2^i`. -/
theorem dlink_diam (i : ℕ) (t : Fin (dstage i).m) : diam ((dchain i).link t) ≤ 4 / 2 ^ i := by
  cases i with
  | zero =>
      have e : (dchain 0).link t = stdRect t := by
        ext p; simp [dchain, dstage_zero_Φ]
      rw [e]; simp only [pow_zero, div_one]; linarith [diam_stdRect_le t]
  | succ i =>
      rcases (dstage_spec i).2.2.2.2.1 t with h | ⟨k, hk, hs⟩
      · refine h.trans ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]; nlinarith [pow_pos
          (show (0 : ℝ) < 2 by norm_num) i]
      · obtain ⟨b, d⟩ := dzone_diam i k hk
        refine (diam_mono hs b).trans (d.trans (le_of_eq ?_))
        rw [pow_succ]; field_simp; norm_num

/-- The end point `P`: a point in the nested boxes `Φ_i(boxA)`. -/
theorem exists_P : (⋂ i, (dstage i).Φ '' boxA).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
  · intro i; exact (dstage_spec i).2.2.2.2.2.2.1
  · intro i; exact boxA_nonempty.image _
  · exact isCompact_boxA.image (dstage 0).Φ.continuous
  · intro i; exact (isCompact_boxA.image (dstage i).Φ.continuous).isClosed

theorem exists_Q : (⋂ i, (dstage i).Φ '' boxB (dstage i).m).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
  · intro i; exact (dstage_spec i).2.2.2.2.2.2.2
  · intro i; exact (boxB_nonempty _).image _
  · exact (isCompact_boxB _).image (dstage 0).Φ.continuous
  · intro i; exact ((isCompact_boxB _).image (dstage i).Φ.continuous).isClosed

theorem isFrom_of {P Q : Pt} (hP : P ∈ ⋂ i, (dstage i).Φ '' boxA)
    (hQ : Q ∈ ⋂ i, (dstage i).Φ '' boxB (dstage i).m) (i : ℕ) : (dchain i).IsFrom P Q := by
  have hm := (dstage i).hm
  rw [mem_iInter] at hP hQ
  obtain ⟨a, ha, rfl⟩ := hP i
  obtain ⟨b, hb, hbQ⟩ := hQ i
  refine ⟨by omega, ⟨a, boxA_subset_stdRect ha, rfl⟩, ⟨b, ?_, hbQ⟩, ?_, ?_⟩
  · have := boxB_subset_stdRect (show 0 < (dstage i).m by omega) hb
    simpa using this
  · intro j hj
    obtain ⟨a', ha', e⟩ := hj
    have := (dstage i).Φ.injective e
    subst this
    by_contra hne
    have hj0 : (j : ℕ) ≠ 0 := fun h => hne (Fin.ext h)
    exact Set.disjoint_left.mp (boxA_disjoint hj0) ha ha'
  · intro j hj
    obtain ⟨b', hb', e⟩ := hj
    rw [← hbQ] at e
    have := (dstage i).Φ.injective e
    subst this
    by_contra hne
    have hj1 : (j : ℕ) + 1 < (dstage i).m := by
      have : (j : ℕ) ≠ (dstage i).m - 1 := fun h => hne (Fin.ext h)
      omega
    exact Set.disjoint_left.mp (boxB_disjoint hj1) hb hb'

/-- **The description of the pseudo-arc in the plane.** -/
noncomputable def planeDescription {P Q : Pt} (hP : P ∈ ⋂ i, (dstage i).Φ '' boxA)
    (hQ : Q ∈ ⋂ i, (dstage i).Φ '' boxB (dstage i).m) : Description Pt P Q where
  n i := (dstage i).m
  D := dchain
  isFrom := isFrom_of hP hQ
  crooked i := by
    obtain ⟨hK, hm, h1, h2, -⟩ := dstage_spec i
    refine crooked_of_tight_pat (stut ((dstage i).m - 1) (dK i)) (stut_lip _ _) ?_
      (fun u => ?_) h2
    · rw [hm]; exact stut_crooked _ _ (by omega)
    · obtain ⟨l, hl, hs⟩ := h1 u
      exact ⟨l, hl, subset_closure.trans hs⟩
  closure_subset i t := by
    obtain ⟨l, -, hs⟩ := (dstage_spec i).2.2.1 t
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
  diam_le i t := dlink_diam i t

theorem exists_description_plane' :
    ∃ (P Q : Pt), P ≠ Q ∧ Nonempty (Description Pt P Q) := by
  obtain ⟨P, hP⟩ := exists_P
  obtain ⟨Q, hQ⟩ := exists_Q
  refine ⟨P, Q, ?_, ⟨planeDescription hP hQ⟩⟩
  rintro rfl
  have h1 := mem_iInter.mp hP 0
  have h2 := mem_iInter.mp hQ 0
  obtain ⟨a, ha, e1⟩ := h1
  obtain ⟨b, hb, e2⟩ := h2
  rw [dstage_zero_Φ] at e1 e2
  subst e1
  rw [e2] at hb
  rw [dstage_zero_m] at hb
  obtain ⟨⟨-, h⟩, -⟩ := ha
  obtain ⟨⟨h', -⟩, -⟩ := hb
  push_cast at h'
  linarith

end HPC.Plane
