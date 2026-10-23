import HPC.Fold.Pair79Splice

/-!
# Batch 79: Theorem 4 with two-link basepoints, the main case

`pair_suffix_fold` is `pair_prefix_fold` for the reversed chains; `theorem4_pair_core` splices
the two with `splice_schedule_pair`; `assemble_pair` and `pair_windows` turn a schedule into the
consolidation of the statement.
-/

namespace HPC.Fold.B79

open HPC.Chain

variable {X : Type*} [MetricSpace X]

/-- **The suffix fold for two-link basepoints**: `pair_prefix_fold` for the reversed chains. -/
theorem pair_suffix_fold {n N : ℕ} {E : Chain X n} {D : Chain X N} (hcr : E.IsCrookedIn' D)
    (hN : 4 ≤ N) (s' s b : Fin n) (hs : s.val = s'.val + 1) (hbs : b ≤ s)
    (hb : (E.link b ∩ D.link ⟨N - 1, by omega⟩).Nonempty) :
    ∃ (lQ : Fin n → ℤ) (cQ : ℕ → ℤ) (βQ : Fin n → ℕ) (V : ℕ),
      (∀ t, ((hcr.1.minIdx t : ℕ) : ℤ) ≤ lQ t ∧ lQ t ≤ ((hcr.1.maxIdx t : ℕ) : ℤ)) ∧
      βQ s = 0 ∧ ((b ≤ s' ∧ βQ s' = 0) ∨ (b = s ∧ V = 0)) ∧
      (∀ t t' : Fin n, t'.val = t.val + 1 → b ≤ t → |(βQ t' : ℤ) - βQ t| ≤ 1) ∧
      (∀ t, b ≤ t → |((N : ℤ) - 1 - lQ t) - cQ (βQ t)| ≤ 1) ∧
      |(V : ℤ) - βQ b| ≤ 1 ∧ cQ V ≤ 1 := by
  have hcr' : E.reverse.IsCrookedIn' D.reverse := hcr.reverse_left.reverse_right
  have hb' : (E.reverse.link (Fin.rev b) ∩ D.reverse.link ⟨0, by omega⟩).Nonempty := by
    rw [reverse_link, reverse_link, Fin.rev_rev]
    have : Fin.rev (⟨0, by omega⟩ : Fin N) = ⟨N - 1, by omega⟩ := Fin.ext (by simp [Fin.val_rev])
    rw [this]; exact hb
  have hsv := s.isLt
  obtain ⟨lP, cP, βP, U, h1, h2, h3, h4, h5, h6, h7⟩ :=
    pair_prefix_fold hcr' hN (Fin.rev s) (Fin.rev s') (Fin.rev b)
      (by simp only [Fin.val_rev]; omega) (Fin.rev_le_rev.mpr hbs) hb'
  refine ⟨fun t => (N : ℤ) - 1 - lP (Fin.rev t), cP, fun t => βP (Fin.rev t), U, ?_, h2, ?_, ?_,
    ?_, h6, h7⟩
  · intro t
    obtain ⟨k1, k2⟩ := h1 (Fin.rev t)
    have e1 : E.link t ⊆ D.link (Fin.rev (hcr'.1.minIdx (Fin.rev t))) := by
      have := minIdx_subset hcr'.1 (Fin.rev t)
      rwa [reverse_link, reverse_link, Fin.rev_rev] at this
    have e2 : E.link t ⊆ D.link (Fin.rev (hcr'.1.maxIdx (Fin.rev t))) := by
      have := maxIdx_subset hcr'.1 (Fin.rev t)
      rwa [reverse_link, reverse_link, Fin.rev_rev] at this
    have g1 := le_maxIdx hcr.1 t e1
    have g2 := minIdx_le hcr.1 t e2
    rw [Fin.le_def, Fin.val_rev] at g1 g2
    have := (hcr'.1.minIdx (Fin.rev t)).isLt
    have := (hcr'.1.maxIdx (Fin.rev t)).isLt
    beta_reduce at k1 k2 ⊢
    constructor <;> omega
  · rcases h3 with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · exact Or.inl ⟨Fin.rev_le_rev.mp k1, k2⟩
    · exact Or.inr ⟨Fin.rev_injective k1, k2⟩
  · intro t t' htt' hbt
    have e : (Fin.rev t).val = (Fin.rev t').val + 1 := by
      simp only [Fin.val_rev]; have := t'.isLt; omega
    have := h4 (Fin.rev t') (Fin.rev t) e (Fin.rev_le_rev.mpr hbt)
    rw [abs_sub_comm]; exact this
  · intro t hbt
    have := h5 (Fin.rev t) (Fin.rev_le_rev.mpr hbt)
    simp only [sub_sub_cancel]; exact this

/-- **From a schedule to the conclusion, with two-link basepoints.** -/
theorem assemble_pair {n N : ℕ} {E : Chain X n} {D : Chain X N} (r r' s' s : Fin n)
    (β : Fin n → ℕ) (hlip : ∀ t t' : Fin n, t'.val = t.val + 1 → |(β t' : ℤ) - β t| ≤ 1)
    (hr : β r = 0) (hr' : β r' = 0) (hs : ∀ t, β t ≤ β s) (hs' : β s' = β s)
    (hblk : ∀ v, ∃ w : ℕ, ∀ t, β t = v → E.link t ⊆ D.unionRange w 3) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' r).val = 0 ∧ (β' r').val = 0 ∧ (β' s').val = q - 1 ∧ (β' s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  have hsch : IsSchedule β :=
    ⟨fun t t' h => by have := hlip t t' h; rw [abs_le] at this; omega, ⟨r, hr⟩⟩
  obtain ⟨p, β', hβ', hval⟩ := hsch.exists_blockMap
  have hp : 0 < p := (β' r).pos
  have hsq : (β' s).val = p - 1 := by
    obtain ⟨t0, ht0⟩ := hβ'.surj ⟨p - 1, by omega⟩
    have h1 := hs t0
    rw [← hval t0, ← hval s, ht0] at h1
    have h2 := (β' s).isLt
    simp only at h1
    omega
  refine ⟨p, β', hβ', by rw [hval, hr], by rw [hval, hr'], ?_, hsq, ?_⟩
  · rw [hval, hs', ← hval, hsq]
  · intro u
    obtain ⟨w, hw⟩ := hblk u.val
    refine ⟨w, ?_⟩
    rw [ofBlocks_link]
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    exact hw t (by rw [← hval t, ht]) hxt

/-- **Theorem 4 with two-link basepoints, the main case**: at least six coarse links, a link
`a` meeting the first coarse link before a link `b` meeting the last, `r ≤ a < b ≤ s`. -/
theorem theorem4_pair_core {n N : ℕ} {E : Chain X n} {D : Chain X N} (hN : 6 ≤ N)
    (hcr : E.IsCrookedIn' D) (r r' s' s : Fin n) (hr : r'.val = r.val + 1)
    (hs : s.val = s'.val + 1) (a b : Fin n) (hra : r ≤ a) (hab : a < b) (hbs : b ≤ s)
    (ha : (E.link a ∩ D.link ⟨0, by omega⟩).Nonempty)
    (hb : (E.link b ∩ D.link ⟨N - 1, by omega⟩).Nonempty) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' r).val = 0 ∧ (β' r').val = 0 ∧ (β' s').val = q - 1 ∧ (β' s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  obtain ⟨lP, cP, βP, U, p1, p2, p3, p4, p5, p6, p7⟩ :=
    pair_prefix_fold hcr (by omega) r r' a hr hra ha
  obtain ⟨lQ, cQ, βQ, V, q1, q2, q3, q4, q5, q6, q7⟩ :=
    pair_suffix_fold hcr (by omega) s' s b hs hbs hb
  obtain ⟨hI, -, hnn, hσN, hlipρ, hlipσ⟩ := seq_facts hcr
  have hρσ : ∀ t, ((hcr.1.minIdx t : ℕ) : ℤ) ≤ ((hcr.1.maxIdx t : ℕ) : ℤ) := hI.le
  have hwid : ∀ t, ((hcr.1.maxIdx t : ℕ) : ℤ) ≤ ((hcr.1.minIdx t : ℕ) : ℤ) + 1 := hI.width
  have hcross : ∀ t t' : Fin n, t'.val = t.val + 1 →
      |((hcr.1.maxIdx t' : ℕ) : ℤ) - ((hcr.1.minIdx t : ℕ) : ℤ)| ≤ 1 := by
    intro t t' h
    obtain ⟨z, hz1, hz2⟩ := (E.adjacent_iff t' t).mpr (by omega)
    have := (D.adjacent _ _).mp ⟨z, maxIdx_subset hcr.1 t' hz1, minIdx_subset hcr.1 t hz2⟩
    rw [abs_le]; omega
  have ha' : ((hcr.1.minIdx a : ℕ) : ℤ) ≤ 1 := by
    have := minIdx_near_of_inter hcr.1 a ⟨0, by omega⟩ ha
    simp only at this; omega
  have hbρ : (N : ℤ) - 2 ≤ ((hcr.1.minIdx b : ℕ) : ℤ) := by
    have := minIdx_near_of_inter hcr.1 b ⟨N - 1, by omega⟩ hb
    have := (hcr.1.minIdx b).isLt
    simp only at *; omega
  have hb' : (N : ℤ) - 2 ≤ ((hcr.1.maxIdx b : ℕ) : ℤ) := by have := hρσ b; omega
  have hab1 : a.val + 1 ≠ b.val := fun h => by
    have := hcross a b h.symm; rw [abs_le] at this; omega
  obtain ⟨β, hlip, hr0, hsmax, hblk, hA, hB, hC, hD⟩ := splice_schedule_pair N hN
    (fun t => ((hcr.1.minIdx t : ℕ) : ℤ)) (fun t => ((hcr.1.maxIdx t : ℕ) : ℤ))
    hnn hρσ hσN hwid lP lQ p1 q1 hlipρ hlipσ hcross r a b s hra hab hbs ha' hb'
    cP βP U p2 p4 p5 p6 p7 cQ βQ V q2 q4 q5 q6 q7
  have hab' : a.val < b.val := hab
  have hr'0 : β r' = 0 := by
    rcases p3 with ⟨hr'a, h0⟩ | ⟨har, hU0⟩
    · exact hA r' hr'a h0
    · subst har
      refine hB hU0 r' (by rw [Fin.lt_def]; omega) ?_
      have := hlipρ a r' hr; simp only at this ⊢; rw [abs_le] at this; omega
  have hs'0 : β s' = β s := by
    rcases q3 with ⟨hbs', h0⟩ | ⟨hbs_eq, hV0⟩
    · exact hC s' hbs' h0
    · subst hbs_eq
      refine hD hV0 s' (by rw [Fin.lt_def]; omega) ?_
      have := hlipρ s' b hs; simp only at this ⊢; rw [abs_le] at this; omega
  exact assemble_pair r r' s' s β hlip hr0 hr'0 hsmax hs'0 (fun v => by
    obtain ⟨w, hw⟩ := hblk v
    exact ⟨w, fun t ht => B78.link_sub_of_level hcr.1 t w (hw t ht)⟩)

/-- **Two windows suffice when every link lies in one of them**, two-link basepoints. -/
theorem pair_windows {n N : ℕ} {E : Chain X n} {D : Chain X N} (P Q : Fin n → Prop)
    (wP wQ : ℕ) (hPQ : ∀ t, P t ∨ Q t) (hPw : ∀ t, P t → E.link t ⊆ D.unionRange wP 3)
    (hQw : ∀ t, Q t → E.link t ⊆ D.unionRange wQ 3) (r r' s' s : Fin n)
    (hr : r'.val = r.val + 1) (hs : s.val = s'.val + 1) (hmid : r' < s')
    (hPr : P r) (hPr' : P r')
    (hcase : (Q s' ∧ Q s) ∨ (P s' ∧ P s ∧ ∃ c, r' < c ∧ c < s' ∧ Q c)) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' r).val = 0 ∧ (β' r').val = 0 ∧ (β' s').val = q - 1 ∧ (β' s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  classical
  have hmid' : r'.val < s'.val := hmid
  have hrr : r ≠ s' ∧ r ≠ s ∧ r' ≠ s' ∧ r' ≠ s := by
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      (have := congrArg Fin.val h; simp only at this; omega)
  rcases hcase with ⟨hQs', hQs⟩ | ⟨hPs', hPs, c, hrc, hcs, hQc⟩
  · refine assemble_pair r r' s' s
      (fun t => if t = s' ∨ t = s then 1 else if P t then 0 else 1) ?_ ?_ ?_ ?_ ?_ ?_
    · intro t t' _
      dsimp only; rw [abs_le]; split_ifs <;> omega
    · simp only [hrr.1, hrr.2.1, or_self, if_false, if_pos hPr]
    · simp only [hrr.2.2.1, hrr.2.2.2, or_self, if_false, if_pos hPr']
    · intro t; simp only [or_true, if_true]; split_ifs <;> omega
    · simp only [true_or, or_true, if_true]
    · intro v
      by_cases hv : v = 0
      · refine ⟨wP, fun t ht => hPw t ?_⟩
        simp only at ht
        split_ifs at ht with h1 h2
        · omega
        · exact h2
        · omega
      · refine ⟨wQ, fun t ht => hQw t ?_⟩
        simp only at ht
        split_ifs at ht with h1 h2
        · rcases h1 with h | h
          · rw [h]; exact hQs'
          · rw [h]; exact hQs
        · omega
        · exact (hPQ t).resolve_left h2
  · have hrc' : r'.val < c.val := hrc
    have hcs' : c.val < s'.val := hcs
    refine assemble_pair r r' s' s (fun t => if t.val < c.val then (if P t then 0 else 1)
      else if t.val = c.val then 1 else (if P t then 2 else 1)) ?_ ?_ ?_ ?_ ?_ ?_
    · intro t t' htt'
      dsimp only; rw [abs_le]; split_ifs <;> omega
    · simp only [show r.val < c.val by omega, if_true, if_pos hPr]
    · simp only [hrc', if_true, if_pos hPr']
    · intro t
      simp only [show ¬ s.val < c.val by omega, show ¬ s.val = c.val by omega, if_false,
        if_pos hPs]
      split_ifs <;> omega
    · simp only [show ¬ s.val < c.val by omega, show ¬ s.val = c.val by omega,
        show ¬ s'.val < c.val by omega, show ¬ s'.val = c.val by omega, if_false,
        if_pos hPs, if_pos hPs']
    · intro v
      by_cases hv : v = 1
      · refine ⟨wQ, fun t ht => hQw t ?_⟩
        simp only at ht
        split_ifs at ht with h1 h2 h3 h4
        · omega
        · exact (hPQ t).resolve_left h2
        · have : t = c := Fin.ext h3
          rw [this]; exact hQc
        · omega
        · exact (hPQ t).resolve_left h4
      · refine ⟨wP, fun t ht => hPw t ?_⟩
        simp only at ht
        split_ifs at ht with h1 h2 h3 h4
        · exact h2
        · omega
        · omega
        · exact h4
        · omega

end HPC.Fold.B79
