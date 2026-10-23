import HPC.BJ59.Thm9D

/-!
# Batch 200, §5: Bing–Jones's chain `E′` (Theorem 9, second simplification, pp. 179–180)

Route: commission 200 §5, step 2 (numbering from 0), with the separation argued through a
Lebesgue number `λ` of `E` on `Q` instead of a convergent subsequence: `F` is a chain in
Bing–Jones's sense properly covering `Q` of mesh `μ = λ/5`. A link of `F` whose closure lies in
`e_k` only goes to `e′_{4k}`; one whose closure lies in `e_k ∩ e_{k+1}` goes to `e′_{4k+1}`,
`e′_{4k+3}` or `e′_{4k+2}` according as it meets a link of `e′_{4k}`, of `e′_{4k+4}`, or neither.
Two links joined through at most two further links cannot have points `a ∈ cl f − e_{k+1}`,
`b ∈ cl f′ − e_k` with `cl f ⊆ e_k`, `cl f′ ⊆ e_{k+1}`: both lie in the ball of radius `λ` about a
point of `Q ∩ f`, which is inside one link of `E` (`KL` below).
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Eside

variable {Y : Type*} [MetricSpace Y]

/-- The closure of a union of links of a chain over a class is the union of the closures. -/
theorem closure_biUnion_links {K : ℕ} (F : Chain Y K) (C : Fin K → Prop) :
    closure (⋃ (a : Fin K) (_ : C a), F.link a) = ⋃ (a : Fin K) (_ : C a), closure (F.link a) := by
  have h1 : (⋃ (a : Fin K) (_ : C a), F.link a) = ⋃ a : {a // C a}, F.link a := by
    ext z; simp
  have h2 : (⋃ (a : Fin K) (_ : C a), closure (F.link a)) = ⋃ a : {a // C a},
      closure (F.link a) := by ext z; simp
  rw [h1, h2, closure_iUnion_of_finite]

/-- **Bing–Jones's `E′`** (pp. 179–180, repaired as in commission 200 §5). -/
theorem bj9_Eside {Q : Set Y} (hQ : IsPseudoArc Q) {m : ℕ} (hm : 0 < m) (E : Chain Y m)
    (hEQ : Q ⊆ E.union)
    (hpr : ∀ i, ∃ q ∈ Q ∩ E.link i, ∀ j, j ≠ i → q ∉ closure (E.link j)) :
    ∃ E' : Chain Y (4 * m - 3), IsBJChain E' ∧ Q ⊆ E'.union ∧ (∀ j, (E'.link j ∩ Q).Nonempty) ∧
      ∀ (j : Fin (4 * m - 3)) (i : ℕ), Allowed j i → closure (E'.link j) ⊆ E.linkN i := by
  classical
  have hQc : IsCompact Q := hQ.1.1.1
  have hQconn : IsConnected Q := hQ.1.1.2
  obtain ⟨lam, hlam, hleb⟩ := lebesgue_number_lemma_of_metric hQc E.isOpen hEQ
  set μ := lam / 5 with hμdef
  have hμ : 0 < μ := by positivity
  obtain ⟨K, F, hFbj, hFε, hQF, hFQ⟩ := exists_fine_bjChain hQ.1 hμ hQconn.nonempty
  have hFd : ∀ f {x y}, x ∈ F.link f → y ∈ F.link f → dist x y < μ := fun f x y hx hy =>
    dist_lt_of_mem_link hFε f hx hy
  have hFdc : ∀ f {x y}, x ∈ closure (F.link f) → y ∈ closure (F.link f) → dist x y ≤ μ :=
    fun f x y hx hy => dist_le_of_mem_closure_of_forall
      (fun x hx y hy => (hFd f hx hy).le) hx hy
  have hself : ∀ f, (F.link f ∩ F.link f).Nonempty := fun f => by
    obtain ⟨x, hx⟩ := F.link_nonempty f; exact ⟨x, hx, hx⟩
  have hFsub : ∀ f, ∃ l : Fin m, closure (F.link f) ⊆ E.link l := by
    intro f
    obtain ⟨z, hz, hzQ⟩ := hFQ f
    obtain ⟨l, hl⟩ := hleb z hzQ
    exact ⟨l, fun x hx => hl (by rw [mem_ball]; linarith [hFdc f hx (subset_closure hz)])⟩
  -- the predicates
  set Sub : ℕ → Fin K → Prop := fun k f => closure (F.link f) ⊆ E.linkN k with hSub
  set Mid : ℕ → Fin K → Prop := fun k f => Sub k f ∧ ¬ Sub (k + 1) f ∧ (1 ≤ k → ¬ Sub (k - 1) f)
    with hMid
  set Two : ℕ → Fin K → Prop := fun k f => Sub k f ∧ Sub (k + 1) f with hTwo
  set MM : ℕ → Fin K → Prop := fun k f => ∃ g, Mid k g ∧ (F.link f ∩ F.link g).Nonempty
    with hMM
  set Cls : ℕ → Fin K → Prop := fun c f =>
    if c % 4 = 0 then Mid (c / 4) f
    else if c % 4 = 1 then Two (c / 4) f ∧ MM (c / 4) f
    else if c % 4 = 2 then Two (c / 4) f ∧ ¬ MM (c / 4) f ∧ ¬ MM (c / 4 + 1) f
    else Two (c / 4) f ∧ MM (c / 4 + 1) f ∧ ¬ MM (c / 4) f with hCls
  have hCls0 : ∀ c f, c % 4 = 0 → (Cls c f ↔ Mid (c / 4) f) := fun c f h => by
    simp only [hCls, if_pos h]
  have hCls1 : ∀ c f, c % 4 = 1 → (Cls c f ↔ Two (c / 4) f ∧ MM (c / 4) f) := fun c f h => by
    simp only [hCls, if_neg (show c % 4 ≠ 0 by omega), if_pos h]
  have hCls2 : ∀ c f, c % 4 = 2 → (Cls c f ↔ Two (c / 4) f ∧ ¬ MM (c / 4) f ∧
      ¬ MM (c / 4 + 1) f) := fun c f h => by
    simp only [hCls, if_neg (show c % 4 ≠ 0 by omega), if_neg (show c % 4 ≠ 1 by omega),
      if_pos h]
  have hCls3 : ∀ c f, c % 4 = 3 → (Cls c f ↔ Two (c / 4) f ∧ MM (c / 4 + 1) f ∧
      ¬ MM (c / 4) f) := fun c f h => by
    simp only [hCls, if_neg (show c % 4 ≠ 0 by omega), if_neg (show c % 4 ≠ 1 by omega),
      if_neg (show c % 4 ≠ 2 by omega)]
  -- lemmas
  have hSubAdj : ∀ k l f g, Sub k f → Sub l g → (F.link f ∩ F.link g).Nonempty →
      k ≤ l + 1 ∧ l ≤ k + 1 := by
    intro k l f g hf hg ⟨x, hxf, hxg⟩
    exact linkN_adj E (hf (subset_closure hxf)) (hg (subset_closure hxg))
  have hSublt : ∀ k f, Sub k f → k < m := by
    intro k f hf
    obtain ⟨x, hx⟩ := F.link_nonempty f
    exact lt_of_mem_linkN E (hf (subset_closure hx))
  have KL : ∀ k f1 g1 g2 f2, Sub k f1 → ¬ Sub (k + 1) f1 → Sub (k + 1) f2 → ¬ Sub k f2 →
      (F.link f1 ∩ F.link g1).Nonempty → (F.link g1 ∩ F.link g2).Nonempty →
      (F.link g2 ∩ F.link f2).Nonempty → False := by
    intro k f1 g1 g2 f2 h1 h1' h2 h2' ⟨w1, hw1f, hw1g⟩ ⟨w2, hw2g, hw2g'⟩ ⟨w3, hw3g, hw3f⟩
    obtain ⟨a, ha, ha'⟩ := not_subset.1 h1'
    obtain ⟨b, hb, hb'⟩ := not_subset.1 h2'
    obtain ⟨z, hz, hzQ⟩ := hFQ f1
    obtain ⟨l, hl⟩ := hleb z hzQ
    have hza : dist z a ≤ μ := hFdc f1 (subset_closure hz) ha
    have hzb : dist z b < 4 * μ := by
      have e1 := hFd f1 hz hw1f
      have e2 := hFd g1 hw1g hw2g
      have e3 := hFd g2 hw2g' hw3g
      have e4 := hFdc f2 (subset_closure hw3f) hb
      linarith [dist_triangle4 z w1 w2 w3, dist_triangle z w3 b]
    have hal : a ∈ E.linkN l.val := mem_linkN_of_mem E l (hl (by rw [mem_ball, dist_comm]; linarith))
    have hbl : b ∈ E.linkN l.val := mem_linkN_of_mem E l (hl (by rw [mem_ball, dist_comm]; linarith))
    have hak := h1 ha
    have hbk := h2 hb
    have e1 := linkN_adj E hal hak
    have e2 := linkN_adj E hbl hbk
    rcases (by omega : l.val = k ∨ l.val = k + 1) with e | e
    · exact hb' (e ▸ hbl)
    · exact ha' (e ▸ hal)
  -- separation
  have hsepC : ∀ a b c c', Cls c a → Cls c' b → (F.link a ∩ F.link b).Nonempty →
      c ≤ c' + 1 ∧ c' ≤ c + 1 := by
    -- Mid against Mid
    have MM0 : ∀ k k' f g, Mid k f → Mid k' g → (F.link f ∩ F.link g).Nonempty → k = k' := by
      intro k k' f g hf hg hfg
      have := hSubAdj _ _ f g hf.1 hg.1 hfg
      rcases (by omega : k = k' ∨ k' = k + 1 ∨ k = k' + 1) with e | e | e
      · exact e
      · subst e
        exact (KL k f f g g hf.1 hf.2.1 hg.1 (hg.2.2 (by omega)) (hself f) hfg (hself g)).elim
      · subst e
        exact (KL k' g g f f hg.1 hg.2.1 hf.1 (hf.2.2 (by omega)) (hself g)
          (by rw [inter_comm]; exact hfg) (hself f)).elim
    -- Mid against Two
    have MT : ∀ k k' f g c', Mid k f → Two k' g → Cls c' g → c' / 4 = k' → c' % 4 ≠ 0 →
        (F.link f ∩ F.link g).Nonempty → 4 * k ≤ c' + 1 ∧ c' ≤ 4 * k + 1 := by
      intro k k' f g c' hf hg hc hk hc0 hfg
      have e1 := hSubAdj _ _ f g hf.1 hg.1 hfg
      have e2 := hSubAdj _ _ f g hf.1 hg.2 hfg
      have hMMg : MM k g := ⟨f, hf, by rw [inter_comm]; exact hfg⟩
      rcases (by omega : k' = k ∨ k' + 1 = k) with e | e
      · subst e
        rcases (by omega : c' % 4 = 1 ∨ c' % 4 = 2 ∨ c' % 4 = 3) with h | h | h
        · omega
        · exact absurd (hk ▸ hMMg) ((hCls2 c' g h).1 hc).2.1
        · exact absurd (hk ▸ hMMg) ((hCls3 c' g h).1 hc).2.2
      · rcases (by omega : c' % 4 = 1 ∨ c' % 4 = 2 ∨ c' % 4 = 3) with h | h | h
        · obtain ⟨h0, hh, hhg⟩ := ((hCls1 c' g h).1 hc).2
          rw [hk] at hh
          have hnk : ¬ Sub k' f := by
            have := hf.2.2 (by omega)
            rwa [show k - 1 = k' by omega] at this
          have hsk : Sub (k' + 1) f := by rw [e]; exact hf.1
          exact (KL k' h0 g f f hh.1 hh.2.1 hsk hnk (by rw [inter_comm]; exact hhg)
            (by rw [inter_comm]; exact hfg) (hself f)).elim
        · have := ((hCls2 c' g h).1 hc).2.2
          rw [hk, e] at this
          exact absurd hMMg this
        · omega
    -- Two against Two
    have TT : ∀ k k' f g, Two k f → Two k' g → (F.link f ∩ F.link g).Nonempty → k = k' := by
      intro k k' f g hf hg hfg
      have e1 := hSubAdj _ _ f g hf.1 hg.2 hfg
      have e2 := hSubAdj _ _ f g hf.2 hg.1 hfg
      omega
    have T13 : ∀ k f g, MM k f → MM (k + 1) g → (F.link f ∩ F.link g).Nonempty → False := by
      intro k f g ⟨h, hh, hfh⟩ ⟨h', hh', hgh'⟩ hfg
      exact KL k h f g h' hh.1 hh.2.1 hh'.1 (hh'.2.2 (by omega))
        (by rw [inter_comm]; exact hfh) hfg hgh'
    intro a b c c' ha hb hab
    have hba : (F.link b ∩ F.link a).Nonempty := by rw [inter_comm]; exact hab
    rcases (by omega : c % 4 = 0 ∨ c % 4 ≠ 0) with hc | hc <;>
    rcases (by omega : c' % 4 = 0 ∨ c' % 4 ≠ 0) with hc' | hc'
    · have := MM0 _ _ a b ((hCls0 c a hc).1 ha) ((hCls0 c' b hc').1 hb) hab
      omega
    · have hTb : Two (c' / 4) b := by
        rcases (by omega : c' % 4 = 1 ∨ c' % 4 = 2 ∨ c' % 4 = 3) with h | h | h
        exacts [((hCls1 c' b h).1 hb).1, ((hCls2 c' b h).1 hb).1, ((hCls3 c' b h).1 hb).1]
      have := MT _ _ a b c' ((hCls0 c a hc).1 ha) hTb hb rfl hc' hab
      omega
    · have hTa : Two (c / 4) a := by
        rcases (by omega : c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3) with h | h | h
        exacts [((hCls1 c a h).1 ha).1, ((hCls2 c a h).1 ha).1, ((hCls3 c a h).1 ha).1]
      have := MT _ _ b a c ((hCls0 c' b hc').1 hb) hTa ha rfl hc hba
      omega
    · have hTa : Two (c / 4) a := by
        rcases (by omega : c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3) with h | h | h
        exacts [((hCls1 c a h).1 ha).1, ((hCls2 c a h).1 ha).1, ((hCls3 c a h).1 ha).1]
      have hTb : Two (c' / 4) b := by
        rcases (by omega : c' % 4 = 1 ∨ c' % 4 = 2 ∨ c' % 4 = 3) with h | h | h
        exacts [((hCls1 c' b h).1 hb).1, ((hCls2 c' b h).1 hb).1, ((hCls3 c' b h).1 hb).1]
      have hk := TT _ _ a b hTa hTb hab
      rcases (by omega : c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3) with h | h | h <;>
      rcases (by omega : c' % 4 = 1 ∨ c' % 4 = 2 ∨ c' % 4 = 3) with h' | h' | h'
      all_goals first
        | omega
        | (exfalso
           first
            | exact T13 _ a b ((hCls1 c a h).2 |> fun _ => ((hCls1 c a h).1 ha).2)
                (hk ▸ ((hCls3 c' b h').1 hb).2.1) hab
            | exact T13 _ b a ((hCls1 c' b h').1 hb).2
                ((show c / 4 + 1 = c' / 4 + 1 by omega) ▸ ((hCls3 c a h).1 ha).2.1) hba)
  -- cover
  have hcovC : ∀ f, ∃ c < 4 * m - 3, Cls c f := by
    intro f
    have hex : ∃ l, Sub l f := by
      obtain ⟨l, hl⟩ := hFsub f
      exact ⟨l.val, fun x hx => mem_linkN_of_mem E l (hl hx)⟩
    set k := Nat.find hex with hk
    have hkS : Sub k f := Nat.find_spec hex
    have hkm := hSublt k f hkS
    by_cases h2 : Sub (k + 1) f
    · have hk1 := hSublt (k + 1) f h2
      by_cases hm1 : MM k f
      · exact ⟨4 * k + 1, by omega, (hCls1 _ f (by omega)).2 (by
          rw [show (4 * k + 1) / 4 = k by omega]; exact ⟨⟨hkS, h2⟩, hm1⟩)⟩
      · by_cases hm2 : MM (k + 1) f
        · exact ⟨4 * k + 3, by omega, (hCls3 _ f (by omega)).2 (by
            rw [show (4 * k + 3) / 4 = k by omega]; exact ⟨⟨hkS, h2⟩, hm2, hm1⟩)⟩
        · exact ⟨4 * k + 2, by omega, (hCls2 _ f (by omega)).2 (by
            rw [show (4 * k + 2) / 4 = k by omega]; exact ⟨⟨hkS, h2⟩, hm1, hm2⟩)⟩
    · refine ⟨4 * k, by omega, (hCls0 _ f (by omega)).2 ?_⟩
      rw [show (4 * k) / 4 = k by omega]
      exact ⟨hkS, h2, fun h1 => Nat.find_min hex (by omega : k - 1 < k)⟩
  -- the end classes
  have hend : ∀ (i : Fin m) (q : Y), q ∈ E.link i → (∀ j, j ≠ i → q ∉ closure (E.link j)) →
      ∀ f, q ∈ F.link f → Mid i.val f := by
    intro i q hqi hq f hqf
    have hnot : ∀ k, k ≠ i.val → ¬ Sub k f := by
      intro k hk hS
      obtain ⟨hk', hqk⟩ := (mem_linkN_iff E).1 (hS (subset_closure hqf))
      exact hq ⟨k, hk'⟩ (fun h => hk (congrArg Fin.val h)) (subset_closure hqk)
    obtain ⟨l, hl⟩ := hFsub f
    have hli : l = i := by
      by_contra h
      exact hq l h (subset_closure (hl (subset_closure hqf)))
    refine ⟨fun x hx => mem_linkN_of_mem E i (hli ▸ hl hx), hnot _ (by omega),
      fun _ => hnot _ (by omega)⟩
  set i0 : Fin m := ⟨0, hm⟩
  set i1 : Fin m := ⟨m - 1, by omega⟩
  obtain ⟨q0, ⟨hq0Q, hq0E⟩, hq0⟩ := hpr i0
  obtain ⟨q1, ⟨hq1Q, hq1E⟩, hq1⟩ := hpr i1
  obtain ⟨f0, hf0⟩ := mem_iUnion.1 (hQF hq0Q)
  obtain ⟨f1, hf1⟩ := mem_iUnion.1 (hQF hq1Q)
  have hc0 : Cls 0 f0 := (hCls0 0 f0 rfl).2 (hend i0 q0 hq0E hq0 f0 hf0)
  have hc1 : Cls (4 * m - 3 - 1) f1 := by
    refine (hCls0 _ f1 (by omega)).2 ?_
    rw [show (4 * m - 3 - 1) / 4 = m - 1 by omega]
    exact hend i1 q1 hq1E hq1 f1 hf1
  obtain ⟨E', hE'bj, hQE', hE'Q, hE'link⟩ := chain_of_classes hQconn.isPreconnected F hFbj hQF
    hFQ Cls hcovC hsepC (by omega) ⟨f0, hc0⟩ ⟨f1, hc1⟩
  refine ⟨E', hE'bj, hQE', hE'Q, fun j i hji => ?_⟩
  rw [hE'link j, closure_biUnion_links]
  refine iUnion₂_subset fun f hf => ?_
  unfold Allowed at hji
  rcases (by omega : j.val % 4 = 0 ∨ j.val % 4 = 1 ∨ j.val % 4 = 2 ∨ j.val % 4 = 3) with
    hc | hc | hc | hc
  · have : i = j / 4 := by omega
    rw [this]; exact ((hCls0 _ f hc).1 hf).1
  · have : i = j / 4 := by omega
    rw [this]; exact ((hCls1 _ f hc).1 hf).1.1
  · have hT := ((hCls2 _ f hc).1 hf).1
    rcases (by omega : i = j / 4 ∨ i = j / 4 + 1) with e | e
    · rw [e]; exact hT.1
    · rw [e]; exact hT.2
  · have : i = j / 4 + 1 := by omega
    rw [this]; exact ((hCls3 _ f hc).1 hf).1.2

end Eside

end HPC.BJ59
