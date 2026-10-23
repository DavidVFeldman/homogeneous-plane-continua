import HPC.BJ59.Thm7Ends

/-!
# Batch 199, library: Bing–Jones Theorem 7, second sentence, for `n ≥ 3` (commission 199, §6)

The buffered walk `bufIdx` and the buffered pattern `bufPat` in the collar chain of
`exists_collar_chain`; following the pattern and folding along the walk gives
`bj7_ends_compact` (compact pseudo-arc), and lifting the links as in `bj_theorem7'` gives
`bj_theorem7_ends'`.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane

/-! ### The buffered walk and pattern -/

section BufPat

variable {n m r s : ℕ} {Hn : ℕ → ℕ}

theorem bufIdx_main (i : ℕ) (hi : i < m) : bufIdx m r s (r + i + 2) = i := by
  unfold bufIdx unfoldIdx unfoldLen; split_ifs <;> omega

theorem bufIdx_of_lt_two {k : ℕ} (hk : k < 2) : bufIdx m r s k = r := if_pos hk

theorem bufIdx_of_ge {k : ℕ} (hk : unfoldLen m r s + 2 ≤ k) : bufIdx m r s k = s := by
  unfold bufIdx; split_ifs <;> omega

theorem bufIdx_two (hm : 0 < m) : bufIdx m r s 2 = r := by
  unfold bufIdx unfoldIdx unfoldLen; split_ifs <;> omega

theorem bufIdx_pen (hrs : r ≤ s) (hs : s < m) : bufIdx m r s (unfoldLen m r s + 1) = s := by
  unfold bufIdx unfoldIdx unfoldLen; split_ifs <;> omega

theorem bufPat_mid {k : ℕ} (h2 : 2 ≤ k) (hk : k < unfoldLen m r s + 2) :
    bufPat n m r s Hn k = Hn (bufIdx m r s k) + 2 := by
  unfold bufPat; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem bufPat_pen : bufPat n m r s Hn (unfoldLen m r s + 2) = n + 2 := by
  unfold bufPat; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem bufPat_last : bufPat n m r s Hn (unfoldLen m r s + 3) = n + 3 := by
  unfold bufPat; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem bufPat_zero : bufPat n m r s Hn 0 = 0 := if_pos rfl

theorem bufPat_one : bufPat n m r s Hn 1 = 1 := by
  unfold bufPat; rw [if_neg (by omega), if_pos rfl]

theorem bufPat_cases (k : ℕ) (hk : k < unfoldLen m r s + 4) :
    k = 0 ∨ k = 1 ∨ (2 ≤ k ∧ k < unfoldLen m r s + 2) ∨ k = unfoldLen m r s + 2 ∨
      k = unfoldLen m r s + 3 := by omega


theorem bufPat_lt (hrs : r ≤ s) (hs : s < m) (hHn : ∀ j < m, Hn j < n) (k : ℕ) : bufPat n m r s Hn k < n + 4 := by
  unfold bufPat
  have := hHn _ (bufIdx_lt (r := r) (by omega) hs k)
  split_ifs <;> omega

theorem collarψ_bufPat (hrs : r ≤ s) (hs : s < m) (hHn : ∀ j < m, Hn j < n) (hr0 : Hn r = 0)
    (hs0 : Hn s = n - 1) (k : ℕ) (hk : k < unfoldLen m r s + 4) :
    collarψ n (bufPat n m r s Hn k) = Hn (bufIdx m r s k) := by
  rcases bufPat_cases k hk with h | h | ⟨h1, h2⟩ | h | h
  · subst h; rw [bufPat_zero, bufIdx_of_lt_two (by omega), hr0]; rfl
  · subst h; rw [bufPat_one, bufIdx_of_lt_two (by omega), hr0]; rfl
  · rw [bufPat_mid h1 h2]
    have := hHn _ (bufIdx_lt (r := r) (by omega) hs k)
    unfold collarψ; split_ifs <;> omega
  · subst h; rw [bufPat_pen, bufIdx_of_ge le_rfl, hs0]; unfold collarψ; split_ifs <;> omega
  · subst h; rw [bufPat_last, bufIdx_of_ge (by omega), hs0]; unfold collarψ; split_ifs <;> omega

theorem bufPat_eq_zero (k : ℕ) (hk : k < unfoldLen m r s + 4) (h0 : bufPat n m r s Hn k = 0) :
    k = 0 := by
  rcases bufPat_cases k hk with h | h | ⟨h1, h2⟩ | h | h
  · exact h
  · subst h; rw [bufPat_one] at h0; omega
  · rw [bufPat_mid h1 h2] at h0; omega
  · subst h; rw [bufPat_pen] at h0; omega
  · subst h; rw [bufPat_last] at h0; omega

theorem bufPat_eq_last (hrs : r ≤ s) (hs : s < m) (hHn : ∀ j < m, Hn j < n) (k : ℕ) (hk : k < unfoldLen m r s + 4)
    (h0 : bufPat n m r s Hn k = n + 3) : k = unfoldLen m r s + 3 := by
  rcases bufPat_cases k hk with h | h | ⟨h1, h2⟩ | h | h
  · subst h; rw [bufPat_zero] at h0; omega
  · subst h; rw [bufPat_one] at h0; omega
  · rw [bufPat_mid h1 h2] at h0
    have := hHn _ (bufIdx_lt (r := r) (by omega) hs k)
    omega
  · subst h; rw [bufPat_pen] at h0; omega
  · exact h

theorem bufPat_step (hrs : r ≤ s) (hs : s < m) (hr0 : Hn r = 0) (hs0 : Hn s = n - 1)
    (hstep : ∀ j j', j < m → j' < m → (j : ℤ) - j' ≤ 1 → (j' : ℤ) - j ≤ 1 →
      (Hn j : ℤ) - Hn j' ≤ 1 ∧ (Hn j' : ℤ) - Hn j ≤ 1)
    (k : ℕ) (hk : k + 1 < unfoldLen m r s + 4) :
    ((bufPat n m r s Hn (k + 1) : ℤ) - bufPat n m r s Hn k).natAbs ≤ 1 := by
  have hL : 1 ≤ unfoldLen m r s := by unfold unfoldLen; omega
  rcases (by omega : k = 0 ∨ k = 1 ∨ (2 ≤ k ∧ k + 1 < unfoldLen m r s + 2) ∨
      k = unfoldLen m r s + 1 ∨ k = unfoldLen m r s + 2) with h | h | ⟨h1, h2⟩ | h | h
  · subst h; rw [bufPat_zero, bufPat_one]; norm_num
  · subst h
    rw [bufPat_one, bufPat_mid (k := 2) le_rfl (by omega), bufIdx_two (by omega), hr0]
    norm_num
  · rw [bufPat_mid h1 (by omega), bufPat_mid (k := k + 1) (by omega) h2]
    have := bufIdx_step hrs hs k
    have := hstep _ _ (bufIdx_lt (r := r) (by omega) hs k) (bufIdx_lt (r := r) (by omega) hs (k + 1)) this.1 this.2
    omega
  · subst h
    rw [bufPat_mid (k := unfoldLen m r s + 1) (by omega) (by omega), bufIdx_pen hrs hs, hs0,
      bufPat_pen]
    omega
  · subst h; rw [bufPat_pen, bufPat_last]; omega

end BufPat

/-! ### The compact case -/

section Compact

variable {S : Type*} [MetricSpace S]

/-- The case `r ≤ s` of `bj7_ends_compact`. -/
theorem bj7_ends_compact_of_le (hP : IsPseudoArc (univ : Set S)) {n m : ℕ} (hn : 3 ≤ n)
    (T : Chain S n) (hT : univ ⊆ T.union) (H : Fin m → Fin n) (hH : IsChainMap H) {r s : Fin m}
    (hrs : r ≤ s) (hr : (H r).val = 0) (hs : (H s).val = n - 1) {A B : Set S}
    (hAc : IsCompact A) (hAne : A.Nonempty) (hA : A ⊆ T.link (H r))
    (hBc : IsCompact B) (hBne : B.Nonempty) (hB : B ⊆ T.link (H s)) :
    ∃ E : Chain S m, univ ⊆ E.union ∧ (∀ i, E.link i ⊆ T.link (H i)) ∧
      A ⊆ E.link r ∧ B ⊆ E.link s := by
  classical
  haveI : ConnectedSpace S := connectedSpace_iff_univ.2 hP.1.1.2
  haveI : CompactSpace S := isCompact_univ_iff.1 hP.1.1.1
  have hA0 : A ⊆ T.linkN 0 := by
    rw [T.linkN_of_lt (by omega)]
    convert hA using 2
    exact Fin.ext hr.symm
  have hB0 : B ⊆ T.linkN (n - 1) := by
    rw [T.linkN_of_lt (by omega)]
    convert hB using 2
    exact Fin.ext hs.symm
  obtain ⟨M, hMcov, hMT, hMA, hMB⟩ := exists_collar_chain hn T hT hAc hAne hA0 hBc hBne hB0
  set Hn : ℕ → ℕ := fun j => if h : j < m then (H ⟨j, h⟩).val else 0 with hHn_def
  have hHn_eq : ∀ i : Fin m, Hn i = H i := fun i => dif_pos i.2
  have hHn_lt : ∀ j < m, Hn j < n := fun j hj => by
    rw [show j = (⟨j, hj⟩ : Fin m).val from rfl, hHn_eq]; exact (H _).2
  have hr0 : Hn r = 0 := by rw [hHn_eq, hr]
  have hs0 : Hn s = n - 1 := by rw [hHn_eq, hs]
  have hstep : ∀ j j', j < m → j' < m → (j : ℤ) - j' ≤ 1 → (j' : ℤ) - j ≤ 1 →
      (Hn j : ℤ) - Hn j' ≤ 1 ∧ (Hn j' : ℤ) - Hn j ≤ 1 := fun j j' hj hj' h1 h2 => by
    have := hH ⟨j, hj⟩ ⟨j', hj'⟩ (by simp only; omega)
    rw [show j = (⟨j, hj⟩ : Fin m).val from rfl, show j' = (⟨j', hj'⟩ : Fin m).val from rfl,
      hHn_eq, hHn_eq]
    omega
  have hrs' : r.val ≤ s.val := hrs
  set L := unfoldLen m r s with hL_def
  have hL : 1 ≤ L := by rw [hL_def]; unfold unfoldLen; omega
  -- the pattern
  set x : Fin (L + 4) → Fin (n + 4) := fun k =>
    ⟨bufPat n m r s Hn k, bufPat_lt hrs' s.2 hHn_lt k⟩ with hx_def
  have hx : Description.IsPattern x := by
    refine ⟨by omega, by omega, Fin.ext (show bufPat n m r s Hn 0 = 0 from bufPat_zero), Fin.ext ?_, fun t t' htt' => ?_⟩
    · show bufPat n m r s Hn (L + 4 - 1) = n + 4 - 1
      rw [show L + 4 - 1 = L + 3 by omega, bufPat_last]; omega
    · show ((bufPat n m r s Hn t' : ℤ) - bufPat n m r s Hn t).natAbs ≤ 1
      rw [htt']
      exact bufPat_step hrs' s.2 hr0 hs0 hstep t (by omega)
  obtain ⟨M', hM'M, hM'cov, p, q, hfrom, hpq, hcomp⟩ := exists_chain_isFrom hP M hMcov
  obtain ⟨E', hE'cov, hE'fol⟩ := exists_follow_pattern hP M' hM'cov hfrom hpq hcomp x hx
  -- folding along the walk
  set π : Fin (L + 4) → Fin m := fun k => ⟨bufIdx m r s k, bufIdx_lt r.2 s.2 k⟩ with hπ_def
  have hπ : ∀ k l : Fin (L + 4), ((k : ℤ) - l).natAbs ≤ 1 → ((π k : ℤ) - π l).natAbs ≤ 1 :=
    fun k l hkl => by
      rcases (by omega : l.val = k.val + 1 ∨ k.val = l.val + 1 ∨ k.val = l.val) with h | h | h
      · have := bufIdx_step (m := m) hrs' s.2 k
        simp only [hπ_def, h]; omega
      · have := bufIdx_step (m := m) hrs' s.2 l
        simp only [hπ_def, h]; omega
      · simp only [hπ_def, h]; omega
  set main : Fin m → Fin (L + 4) := fun i => ⟨r + i + 2, by rw [hL_def]; unfold unfoldLen; omega⟩
  have hmain : ∀ i, π (main i) = i := fun i => Fin.ext (bufIdx_main i i.2)
  have hmainadj : ∀ i j : Fin m, ((i : ℤ) - j).natAbs ≤ 1 → ((main i : ℤ) - main j).natAbs ≤ 1 :=
    fun i j h => by simp only [main]; push_cast; omega
  set E := foldChain E' π hπ main hmain hmainadj
  -- every point lies in a link of `E'` inside the matching link of `M`
  have hE'M : ∀ k z, z ∈ E'.link k → z ∈ M.link (x k) := fun k z hz => hM'M _ (hE'fol k hz)
  refine ⟨E, fun z _ => ?_, fun i z hz => ?_, fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨k, hk⟩ := mem_iUnion.1 (hE'cov (mem_univ z))
    exact mem_iUnion.2 ⟨_, link_subset_foldChain E' _ _ _ _ _ k hk⟩
  · rw [foldChain_link] at hz
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 hz
    have h1 := hMT _ (hE'M k z hzk)
    rw [show ((x k : Fin (n + 4)) : ℕ) = bufPat n m r s Hn k from rfl,
      collarψ_bufPat hrs' s.2 hHn_lt hr0 hs0 k k.2,
      T.linkN_of_lt (hHn_lt _ (bufIdx_lt r.2 s.2 k))] at h1
    convert h1 using 2
    apply Fin.ext
    rw [← hk]
    exact (hHn_eq _).symm
  · obtain ⟨k, hk⟩ := mem_iUnion.1 (hE'cov (mem_univ a))
    have h0 := hMA a ha _ (hE'M k a hk)
    have hk0 : k.val = 0 := bufPat_eq_zero k k.2 h0
    have hπk : π k = r := Fin.ext (by simp only [hπ_def, hk0]; exact bufIdx_of_lt_two (by omega))
    have := link_subset_foldChain E' π hπ main hmain hmainadj k hk
    rwa [hπk] at this
  · obtain ⟨k, hk⟩ := mem_iUnion.1 (hE'cov (mem_univ b))
    have h0 := hMB b hb _ (hE'M k b hk)
    have hk0 : k.val = L + 3 := bufPat_eq_last hrs' s.2 hHn_lt k k.2 h0
    have hπk : π k = s := Fin.ext (by simp only [hπ_def, hk0]; exact bufIdx_of_ge (by omega))
    have := link_subset_foldChain E' π hπ main hmain hmainadj k hk
    rwa [hπk] at this

/-- **Bing–Jones Theorem 7, second sentence, in a compact pseudo-arc** (`n ≥ 3`, `A`, `B`
compact nonempty). -/
theorem bj7_ends_compact (hP : IsPseudoArc (univ : Set S)) {n m : ℕ} (hn : 3 ≤ n)
    (T : Chain S n) (hT : univ ⊆ T.union) (H : Fin m → Fin n) (hH : IsChainMap H) {r s : Fin m}
    (hr : (H r).val = 0) (hs : (H s).val = n - 1) {A B : Set S}
    (hAc : IsCompact A) (hAne : A.Nonempty) (hA : A ⊆ T.link (H r))
    (hBc : IsCompact B) (hBne : B.Nonempty) (hB : B ⊆ T.link (H s)) :
    ∃ E : Chain S m, univ ⊆ E.union ∧ (∀ i, E.link i ⊆ T.link (H i)) ∧
      A ⊆ E.link r ∧ B ⊆ E.link s := by
  rcases le_total r s with hrs | hsr
  · exact bj7_ends_compact_of_le hP hn T hT H hH hrs hr hs hAc hAne hA hBc hBne hB
  · have hH' : IsChainMap (H ∘ Fin.rev) := fun i j hij => hH _ _ (by
      simp only [Fin.val_rev]; omega)
    obtain ⟨E, hEcov, hET, hEA, hEB⟩ := bj7_ends_compact_of_le hP hn T hT (H ∘ Fin.rev) hH'
      (r := Fin.rev r) (s := Fin.rev s) (Fin.rev_le_rev.2 hsr)
      (by simp [hr]) (by simp [hs]) hAc hAne (by simpa using hA) hBc hBne (by simpa using hB)
    refine ⟨E.reverse, fun z hz => ?_, fun i => ?_, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.1 (hEcov hz)
      exact mem_iUnion.2 ⟨Fin.rev k, by rw [Chain.reverse_link, Fin.rev_rev]; exact hk⟩
    · rw [Chain.reverse_link]
      have := hET (Fin.rev i)
      simp only [Function.comp, Fin.rev_rev] at this
      exact this
    · rw [Chain.reverse_link]; exact hEA
    · rw [Chain.reverse_link]; exact hEB

end Compact

/-! ### In a metric space -/

section Lift

variable {X : Type*} [MetricSpace X]

/-- **Bing–Jones, Theorem 7, second sentence, for chains of at least three links.** -/
theorem bj_theorem7_ends' {P : Set X} (hP : IsPseudoArc P) {n m : ℕ} (hn : 3 ≤ n)
    (D : Chain X n) (hDP : P ⊆ D.union) (hDp : ∀ j, (D.link j ∩ P).Nonempty) (H : Fin m → Fin n)
    (hH : IsChainMap H) {r s : Fin m} (hr : (H r).val = 0)
    (hs : (H s).val = n - 1) {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAP : A ⊆ P ∩ D.link (H r)) (hBP : B ⊆ P ∩ D.link (H s)) :
    ∃ E : Chain X m, IsBJChain E ∧ P ⊆ E.union ∧ (∀ i, (E.link i ∩ P).Nonempty) ∧
      (∀ i, E.link i ⊆ D.link (H i)) ∧ A ⊆ E.link r ∧ B ⊆ E.link s := by
  classical
  haveI : CompactSpace P := isCompact_iff_compactSpace.1 hP.1.1.1
  have hPS : IsPseudoArc (univ : Set P) :=
    isPseudoArc_subtype_of_image (by rw [Subtype.coe_image_univ]; exact hP)
  set T := traceChain hP.1.1.2.isPreconnected D hDP hDp
  -- enlarge `A`, `B` (as subsets of `P`) to nonempty compact sets
  obtain ⟨a0, ha0⟩ := T.link_nonempty (H r)
  obtain ⟨b0, hb0⟩ := T.link_nonempty (H s)
  set A' : Set P := Subtype.val ⁻¹' A ∪ {a0}
  set B' : Set P := Subtype.val ⁻¹' B ∪ {b0}
  have hA'c : IsCompact A' :=
    ((hA.preimage continuous_subtype_val).isCompact).union isCompact_singleton
  have hB'c : IsCompact B' :=
    ((hB.preimage continuous_subtype_val).isCompact).union isCompact_singleton
  have hA'T : A' ⊆ T.link (H r) := by
    rintro x (hx | hx)
    · exact (hAP hx).2
    · rw [mem_singleton_iff.1 hx]; exact ha0
  have hB'T : B' ⊆ T.link (H s) := by
    rintro x (hx | hx)
    · exact (hBP hx).2
    · rw [mem_singleton_iff.1 hx]; exact hb0
  obtain ⟨E, hEcov, hET, hEA, hEB⟩ := bj7_ends_compact hPS hn T (fun x _ => mem_iUnion.1 (hDP x.2)
    |>.elim fun j hj => mem_iUnion.2 ⟨j, hj⟩) H hH hr hs hA'c ⟨a0, Or.inr rfl⟩ hA'T hB'c
    ⟨b0, Or.inr rfl⟩ hB'T
  -- lift the links
  choose W hWo hWE using fun i => isOpen_induced_iff.1 (E.isOpen i)
  set V : Fin m → Set X := fun i => W i ∩ D.link (H i)
  have hVo : ∀ i, IsOpen (V i) := fun i => (hWo i).inter (D.isOpen _)
  have hmemE : ∀ i (x : P), x ∈ E.link i → (x : X) ∈ V i := fun i x hx =>
    ⟨show x ∈ Subtype.val ⁻¹' W i by rw [hWE i]; exact hx, hET i hx⟩
  have hmemV : ∀ i (x : X) (hx : x ∈ P), x ∈ V i → (⟨x, hx⟩ : P) ∈ E.link i := fun i x hx hV => by
    rw [← hWE i]; exact hV.1
  set C : Fin m → Set X := fun i => (if i = r then A else ∅) ∪ (if i = s then B else ∅)
  have hCV : ∀ i, C i ⊆ V i ∩ P := by
    intro i x hx
    rcases hx with hx | hx
    · split_ifs at hx with h
      · subst h
        exact ⟨hmemE _ ⟨x, (hAP hx).1⟩ (hEA (Or.inl hx)), (hAP hx).1⟩
      · exact absurd hx (notMem_empty x)
    · split_ifs at hx with h
      · subst h
        exact ⟨hmemE _ ⟨x, (hBP hx).1⟩ (hEB (Or.inl hx)), (hBP hx).1⟩
      · exact absurd hx (notMem_empty x)
  have hCc : ∀ i, IsCompact (C i) := by
    intro i
    refine IsCompact.union ?_ ?_
    · split_ifs
      exacts [hP.1.1.1.of_isClosed_subset hA (fun x hx => (hAP hx).1), isCompact_empty]
    · split_ifs
      exacts [hP.1.1.1.of_isClosed_subset hB (fun x hx => (hBP hx).1), isCompact_empty]
  obtain ⟨E', hBJ, hcov, hmeet, hsub⟩ := exists_bjChain_shrink' hP.1.1 V hVo
    (fun x hx => by
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hEcov (mem_univ (⟨x, hx⟩ : P)))
      exact mem_iUnion.2 ⟨i, hmemE i _ hi⟩)
    (fun i => by
      obtain ⟨x, hx⟩ := E.link_nonempty i
      exact ⟨x, hmemE i x hx, x.2⟩)
    C (fun i => ⟨hCc i, fun x hx => (hCV i hx).1⟩)
    (fun i j hij => by
      rw [union_eq_left.2 (hCV i), union_eq_left.2 (hCV j), Set.disjoint_left]
      rintro x ⟨hxi, hxP⟩ ⟨hxj, -⟩
      have := (E.adjacent i j).1 ⟨_, hmemV i x hxP hxi, hmemV j x hxP hxj⟩
      omega)
  refine ⟨E', hBJ, hcov, hmeet, fun i => subset_closure.trans ((hsub i).1.trans inter_subset_right),
    fun x hx => (hsub r).2 (Or.inl (by simp only; exact hx)),
    fun x hx => (hsub s).2 (Or.inr (by simp only; exact hx))⟩

end Lift

end HPC.BJ59
