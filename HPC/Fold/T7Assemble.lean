import HPC.Fold.T7Profile

/-!
# Theorem 7: assembling the lift into a block consolidation

Batch 82. From the lifting theorem: a fine chain `E` crooked in `D` (`m ≥ 3` links) with links in
the first and last links of `D` has a block map onto `Fin (z (m-1))` whose blocks follow Bing's
pattern `bingF (m-1)` and meet only the levels of their own and neighbouring positions; the
resulting consolidation is crooked in `D`.
-/

namespace HPC.Fold

open HPC.Chain

variable {X : Type*} [MetricSpace X]

/-- A full lift: every fine link carried, the first position and the last one both used. -/
theorem exists_full_lift {n m : ℕ} (hm : 3 ≤ m) {E : Chain X n} {D : Chain X m}
    (hcr : E.IsCrookedIn' D) (hlo : ∃ t, E.link t ⊆ D.link ⟨0, by omega⟩)
    (hhi : ∃ t, E.link t ⊆ D.link ⟨m - 1, by omega⟩) :
    ∃ β : ℕ → ℕ, IsLift (chainK E D) (chainM E D) (fun u => 0 + bingF (m - 1) u) (z (m - 1)) 0
      (n - 1) β ∧ (∃ t < n, β t = 0) ∧ (∃ t < n, β t = z (m - 1) - 1) := by
  obtain ⟨t0, h0⟩ := hlo
  obtain ⟨ts, hs⟩ := hhi
  have hn : 0 < n := Fin.pos t0
  have hP := isProfile_chain hcr
  have hPr := hP.rev
  have hband : ∀ s0 s1, Band (chainM E D) 0 (m - 1) s0 s1 := fun s0 s1 t _ _ h hh => by
    have := chainM_bound hh; omega
  have hbandr : ∀ s0 s1, Band (fun t => chainM E D (n - 1 - t)) 0 (m - 1) s0 s1 :=
    fun s0 s1 t _ _ h hh => by have := chainM_bound hh; omega
  have hK0 : (0 : ℤ) ∈ chainK E D t0 := ⟨t0.isLt, ⟨0, by omega⟩, rfl, h0⟩
  have hKs : (0 : ℤ) + ((m - 1 : ℕ) : ℤ) ∈ chainK E D ts :=
    ⟨ts.isLt, ⟨m - 1, by omega⟩, by simp, hs⟩
  have hts0 : ts.val ≠ t0.val := by
    intro he
    obtain ⟨x, hx⟩ := E.link_nonempty t0
    have h1 := h0 hx
    have h2 := hs (show x ∈ E.link ts by rw [Fin.ext he]; exact hx)
    have := (D.adjacent_iff ⟨0, by omega⟩ ⟨m - 1, by omega⟩).1 ⟨x, h1, h2⟩
    simp at this; omega
  -- forward from `t0`
  obtain ⟨β1, hl1, h10⟩ := liftStmt (m - 1) n _ _ hP 0 t0 (n - 1) (by omega) (by omega)
    (hP.sub t0 t0.isLt hK0) (hband _ _)
  have hl1' := hl1.adjust_start hP h10 hK0 (hband _ _) (by omega) (by omega)
  -- backward from `t0`
  have hK0r : (0 : ℤ) ∈ chainK E D (n - 1 - (n - 1 - t0)) := by
    rw [show n - 1 - (n - 1 - t0.val) = t0.val by omega]; exact hK0
  obtain ⟨β2, hl2, h20⟩ := liftStmt (m - 1) n _ _ hPr 0 (n - 1 - t0) (n - 1) (by omega)
    (by omega) (hP.sub _ (by omega) hK0r) (hbandr _ _)
  have hl2' := hl2.adjust_start hPr h20 hK0r (hbandr _ _) (by omega) (by omega)
  have hl2r := hl2'.timeRev (by omega) (by omega)
  rw [show n - 1 - (n - 1) = 0 by omega, show n - 1 - (n - 1 - t0.val) = t0.val by omega] at hl2r
  -- glue at `t0`
  have hG := hl2r.glue hl1' (Nat.zero_le _) (fun h => by
    have := hl1'.2 t0 le_rfl h
    simp only [if_true] at this ⊢
    constructor <;> omega)
  -- move the top link to the end
  have hG' := hG.adjust_top hP (Nat.zero_le ts.val) (by omega) hKs
    (fun h hh => by have := chainM_bound hh; omega) (by omega)
  refine ⟨_, hG', ⟨t0, t0.isLt, ?_⟩, ⟨ts, ts.isLt, by simp⟩⟩
  simp only [hts0.symm, if_false, le_refl, if_true]

/-- The block map of Theorem 7, before it is phrased through `bingPattern`. -/
theorem exists_blocks_bingF {n m : ℕ} (hm : 3 ≤ m) {E : Chain X n} {D : Chain X m}
    (hcr : E.IsCrookedIn' D) (hlo : ∃ t, E.link t ⊆ D.link ⟨0, by omega⟩)
    (hhi : ∃ t, E.link t ⊆ D.link ⟨m - 1, by omega⟩) :
    ∃ (β : Fin n → Fin (z (m - 1))) (_ : IsBlockMap β),
      (∀ t, ∃ i : Fin m, (i : ℤ) = bingF (m - 1) (β t) ∧ E.link t ⊆ D.link i) ∧
      (∀ t (i : Fin m), (E.link t ∩ D.link i).Nonempty →
        ∃ u : ℕ, u < z (m - 1) ∧ u ≤ (β t).val + 1 ∧ (β t).val ≤ u + 1 ∧
          (i : ℤ) = bingF (m - 1) u) := by
  obtain ⟨β, hl, ⟨tA, htA, hA⟩, ⟨tB, htB, hB⟩⟩ := exists_full_lift hm hcr hlo hhi
  have hc : ∀ t : Fin n, Compat (chainK E D) (chainM E D) (fun u => 0 + bingF (m - 1) u)
      (z (m - 1)) t (β t) := fun t => hl.1 t (Nat.zero_le _) (by omega)
  refine ⟨fun t => ⟨β t, (hc t).1⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- surjectivity, by the discrete intermediate value theorem
    intro u
    let g : ℕ → ℤ := fun t => (β (min t (n - 1)) : ℤ)
    have hg : ∀ t, |g (t + 1) - g t| ≤ 1 := by
      intro t
      simp only [g]
      rcases Nat.lt_or_ge t (n - 1) with h | h
      · rw [show min (t + 1) (n - 1) = t + 1 by omega, show min t (n - 1) = t by omega]
        have := hl.2 t (Nat.zero_le _) h
        rw [abs_le]; constructor <;> omega
      · rw [show min (t + 1) (n - 1) = n - 1 by omega, show min t (n - 1) = n - 1 by omega]
        simp
    have hu := u.isLt
    obtain ⟨s, hs1, hs2, hs3⟩ := exists_eq_of_lip g hg (max tA tB - min tA tB) (min tA tB) u (by
      rcases le_total tA tB with h | h
      · left
        rw [show min tA tB = tA by omega, show tA + (max tA tB - tA) = tB by omega]
        simp only [g, show min tA (n - 1) = tA by omega, show min tB (n - 1) = tB by omega, hA, hB]
        omega
      · right
        rw [show min tA tB = tB by omega, show tB + (max tA tB - tB) = tA by omega]
        simp only [g, show min tA (n - 1) = tA by omega, show min tB (n - 1) = tB by omega, hA, hB]
        omega)
    refine ⟨⟨s, by omega⟩, Fin.ext ?_⟩
    simp only [g, show min s (n - 1) = s by omega] at hs3
    simp only; omega
  · intro t t' htt'
    have := hl.2 t (Nat.zero_le _) (by omega)
    rw [show t' = ⟨t.val + 1, by omega⟩ from Fin.ext htt']
    simp only
    omega
  · intro t
    obtain ⟨_, i, hi, hsub⟩ := (hc t).2.1
    exact ⟨i, by rw [hi]; ring, hsub⟩
  · intro t i hne
    have hmem : (i : ℤ) ∈ chainM E D t := ⟨t.isLt, i, rfl, hne⟩
    have hct := hc t
    rcases hct.2.2 _ hmem with e | ⟨h0, e⟩ | ⟨h0, e⟩
    · exact ⟨β t, hct.1, by simp, by simp, by rw [e]; ring⟩
    · exact ⟨β t - 1, by have := hct.1; omega, by simp; omega, by simp; omega, by rw [e]; ring⟩
    · exact ⟨β t + 1, h0, by dsimp only; omega, by dsimp only; omega, by rw [e]; ring⟩

/-- A chain with `z (m-1)` links whose links follow `bingF (m-1)` and meet only the levels of their
own and neighbouring positions is crooked. -/
theorem crooked_of_tight {m : ℕ} {F : Chain X (z (m - 1))} {D : Chain X m}
    (h1 : ∀ u : Fin (z (m - 1)), ∃ i : Fin m, (i : ℤ) = bingF (m - 1) u ∧ F.link u ⊆ D.link i)
    (h2 : ∀ (u : Fin (z (m - 1))) (l : Fin m), (F.link u ∩ D.link l).Nonempty →
      ∃ u' : ℕ, u' < z (m - 1) ∧ u' ≤ u.val + 1 ∧ u.val ≤ u' + 1 ∧ (l : ℤ) = bingF (m - 1) u') :
    F.IsCrookedIn' D := by
  have hsub : ∀ (u : Fin (z (m - 1))) (i : Fin m), (i : ℤ) = bingF (m - 1) u →
      F.link u ⊆ D.link i := by
    intro u i hi
    obtain ⟨i', hi', hsub'⟩ := h1 u
    have : i' = i := Fin.ext (by omega)
    rw [← this]; exact hsub'
  have hlip := bingF_lip (m - 1)
  refine ⟨fun u => ?_, ?_⟩
  · obtain ⟨i, _, hi⟩ := h1 u
    exact ⟨i, hi⟩
  intro h k hk i j hi hj
  obtain ⟨u', hu1, hu2, hu3, hu4⟩ := h2 i h hi
  obtain ⟨v', hv1, hv2, hv3, hv4⟩ := h2 j k hj
  obtain ⟨r, s, hb, hr, hs⟩ := bingF_crooked (m - 1) u' v' (Nat.zero_le _) (by omega)
    (Nat.zero_le _) (by omega) h k (by rw [hu4]) (by rw [hv4]) (by omega)
  have near : ∀ (a b : ℕ), a ≤ b + 1 → b ≤ a + 1 → |bingF (m - 1) a - bingF (m - 1) b| ≤ 1 := by
    intro a b hab hba
    rcases (show a = b ∨ a = b + 1 ∨ b = a + 1 by omega) with e | e | e
    · subst e; simp
    · subst e; exact hlip b
    · subst e; rw [abs_sub_comm]; exact hlip a
  have ni := near u' i hu2 hu3
  have nj := near v' j hv2 hv3
  rw [abs_le] at ni nj
  have hbr : r < z (m - 1) := by unfold NBetween at hb; omega
  have hbs : s < z (m - 1) := by unfold NBetween at hb; omega
  have hri : r ≠ i.val := fun e => by rw [e] at hr; omega
  have hsj : s ≠ j.val := fun e => by rw [e] at hs; omega
  refine ⟨⟨r, hbr⟩, ⟨s, hbs⟩, ?_, hsub _ _ (by simp only; rw [hr]; omega),
    hsub _ _ (by simp only; rw [hs]; omega)⟩
  unfold NBetween at hb
  unfold Between
  simp only [Fin.lt_def, gt_iff_lt]
  omega

/-- A block consolidation whose blocks follow `bingF (m-1)` and meet only the levels of their own
and neighbouring positions is crooked. -/
theorem ofBlocks_crooked_of_tight {n m : ℕ} {E : Chain X n} {D : Chain X m}
    (β : Fin n → Fin (z (m - 1))) (hβ : IsBlockMap β)
    (h1 : ∀ t, ∃ i : Fin m, (i : ℤ) = bingF (m - 1) (β t) ∧ E.link t ⊆ D.link i)
    (h2 : ∀ t (i : Fin m), (E.link t ∩ D.link i).Nonempty →
        ∃ u : ℕ, u < z (m - 1) ∧ u ≤ (β t).val + 1 ∧ (β t).val ≤ u + 1 ∧
          (i : ℤ) = bingF (m - 1) u) :
    (E.ofBlocks β hβ).IsCrookedIn' D := by
  refine crooked_of_tight (fun u => ?_) (fun u l ⟨x, hx1, hx2⟩ => ?_)
  · obtain ⟨t, ht⟩ := hβ.surj u
    obtain ⟨i, hi, -⟩ := h1 t
    refine ⟨i, by rw [hi, ht], fun x hx => ?_⟩
    rw [ofBlocks_link] at hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
    obtain ⟨t', ht', hxt⟩ := hx
    obtain ⟨i', hi', hsub'⟩ := h1 t'
    have : i' = i := Fin.ext (by rw [ht'] at hi'; rw [ht] at hi; omega)
    rw [← this]; exact hsub' hxt
  · rw [ofBlocks_link] at hx1
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx1
    obtain ⟨t, ht, hxt⟩ := hx1
    obtain ⟨u', h1', h2', h3', h4'⟩ := h2 t l ⟨x, hxt, hx2⟩
    exact ⟨u', h1', by rw [← ht]; exact h2', by rw [← ht]; exact h3', h4'⟩

end HPC.Fold
