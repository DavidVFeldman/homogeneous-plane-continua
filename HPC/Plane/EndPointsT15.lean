import HPC.Plane.EndPointsAux

/-!
# Batch 85: the construction behind Bing 1951, Theorem 15

A nondegenerate snake-like continuum `M` carries a sequence of chains `C_i` covering `M` (every
link meeting `M`, mesh `→ 0`, the closure of every link of `C_{i+1}` inside a link of `C_i`)
together with index pairs `s_i + 2 ≤ t_i` such that the closures of the links `s_{i+1}`, `t_{i+1}`
lie in the links `s_i`, `t_i`, and the links of `C_{i+1}` between `s_{i+1}` and `t_{i+1}` have
closures in links of `C_i` between `s_i` and `t_i` (Bing's subchains `D_i`). The step is
`exists_next_level`; the index argument is a discrete intermediate value theorem.
-/

namespace HPC.Plane

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

/-- A discrete intermediate value theorem. -/
theorem int_ivt (f : ℕ → ℤ) {a b : ℕ} (hab : a ≤ b)
    (hstep : ∀ u, a ≤ u → u < b → |f (u + 1) - f u| ≤ 1) {c : ℤ} (hac : f a ≤ c)
    (hcb : c ≤ f b) : ∃ u, a ≤ u ∧ u ≤ b ∧ f u = c := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨a, le_rfl, le_rfl, le_antisymm hac hcb⟩
  | succ b hab ih =>
    by_cases h : c ≤ f b
    · obtain ⟨u, h1, h2, h3⟩ := ih (fun u h1 h2 => hstep u h1 (by omega)) h
      exact ⟨u, h1, by omega, h3⟩
    · push_neg at h
      have := hstep b hab (by omega)
      rw [abs_le] at this
      exact ⟨b + 1, by omega, le_rfl, by omega⟩

/-- A bounded set containing `z` has closure inside the closed ball about `z` of radius its
diameter. -/
theorem closure_subset_closedBall_diam {S : Set X} (hS : Bornology.IsBounded S) {z : X}
    (hz : z ∈ S) : closure S ⊆ closedBall z (diam S) :=
  closure_minimal (fun _ hw => mem_closedBall.mpr (dist_le_diam_of_mem hS hw hz)) isClosed_closedBall

/-- Chains of arbitrarily small mesh covering a connected set can be taken with every link
meeting it. -/
theorem exists_cover_meeting {M : Set X} (hMconn : IsPreconnected M) (hMne : M.Nonempty)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ M ⊆ D.union)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ M ⊆ D.union ∧ ∀ i, (D.link i ∩ M).Nonempty := by
  obtain ⟨n, D, hDε, hMD⟩ := hsnake ε hε
  obtain ⟨z, hz⟩ := hMne
  obtain ⟨i₀, hi₀, hzi₀⟩ := (mem_union_iff_linkN D).mp (hMD hz)
  obtain ⟨a, k, E, -, -, hakn, hlink, hcov, hmeet, -⟩ := exists_chain_of_weak (n := n) (linkN D)
    (isOpen_linkN D) (fun i j hij _ => disjoint_linkN D hij) hMconn
    (fun x hx => by
      obtain ⟨i, hi, hx⟩ := (mem_union_iff_linkN D).mp (hMD hx)
      exact mem_iUnion₂.mpr ⟨i, hi, hx⟩) hi₀ ⟨z, hzi₀, hz⟩
  refine ⟨k, E, fun t => ?_, hcov, hmeet⟩
  rw [hlink t, linkN_of_lt D (by omega)]
  exact hDε _

/-- The part of `M` in the closures of the links `s, …, t` of a chain of mesh `< δ`, all meeting
`M`, is `2δ`-chained. -/
theorem chainedAt_closure_range {M : Set X} {n : ℕ} (F : Chain X n) {δ : ℝ}
    (hF : IsEpsChain F δ) {s t : ℕ} (hst : s ≤ t) (ht : t < n)
    (hmeet : ∀ u (hu : u < n), s ≤ u → u ≤ t → (F.link ⟨u, hu⟩ ∩ M).Nonempty) :
    T13.ChainedAt (M ∩ ⋃ u, ⋃ (hu : u < n), ⋃ (_ : s ≤ u ∧ u ≤ t), closure (F.link ⟨u, hu⟩))
      (2 * δ) := by
  set A := M ∩ ⋃ u, ⋃ (hu : u < n), ⋃ (_ : s ≤ u ∧ u ≤ t), closure (F.link ⟨u, hu⟩)
  choose z hzF hzM using hmeet
  have hdist : ∀ (i : Fin n) (y w : X), y ∈ closure (F.link i) → w ∈ closure (F.link i) →
      dist y w < δ := fun i y w hy hw => by
    have := dist_le_diam_of_mem (hF i).1.closure hy hw
    rw [diam_closure] at this
    exact this.trans_lt (hF i).2
  have hzA : ∀ u (hu : u < n) (h1 : s ≤ u) (h2 : u ≤ t), z u hu h1 h2 ∈ A := fun u hu h1 h2 =>
    ⟨hzM u hu h1 h2, mem_iUnion₂.mpr ⟨u, hu, mem_iUnion.mpr ⟨⟨h1, h2⟩,
      subset_closure (hzF u hu h1 h2)⟩⟩⟩
  have side : ∀ W W' : Set X, A ⊆ W ∪ W' → (∀ x ∈ W, ∀ y ∈ W', 2 * δ < dist x y) →
      z s (by omega) le_rfl hst ∈ W → A ⊆ W := by
    intro W W' hcov hsep hzW
    have hδ : 0 < δ := lt_of_le_of_lt dist_nonneg
      (hdist ⟨s, by omega⟩ _ _ (subset_closure (hzF s (by omega) le_rfl hst))
        (subset_closure (hzF s (by omega) le_rfl hst)))
    -- a point of `A` close to a point of `W` lies in `W`
    have close : ∀ x ∈ W, ∀ y ∈ A, dist x y ≤ 2 * δ → y ∈ W := by
      intro x hx y hy hxy
      rcases hcov hy with h | h
      · exact h
      · have := hsep x hx y h; linarith
    have claim : ∀ d, ∀ (hd : s + d ≤ t), z (s + d) (by omega) (by omega) hd ∈ W := by
      intro d
      induction d with
      | zero => intro hd; simpa using hzW
      | succ d ih =>
        intro hd
        have hprev := ih (by omega)
        obtain ⟨w, hw1, hw2⟩ := (F.adjacent_iff ⟨s + d, by omega⟩ ⟨s + (d + 1), by omega⟩).mpr
          (by simp only; omega)
        refine close _ hprev _ (hzA _ _ _ _) ?_
        have h1 := hdist _ _ _ (subset_closure (hzF (s + d) (by omega) (by omega) (by omega)))
          (subset_closure hw1)
        have h2 := hdist _ _ _ (subset_closure hw2)
          (subset_closure (hzF (s + (d + 1)) (by omega) (by omega) hd))
        have := dist_triangle (z (s + d) (by omega) (by omega) (by omega)) w
          (z (s + (d + 1)) (by omega) (by omega) hd)
        linarith
    intro y hy
    obtain ⟨u, hu, ⟨h1, h2⟩, hyu⟩ : ∃ u, ∃ hu : u < n, (s ≤ u ∧ u ≤ t) ∧
        y ∈ closure (F.link ⟨u, hu⟩) := by
      obtain ⟨u, hu⟩ := mem_iUnion.mp hy.2
      obtain ⟨hu', hu⟩ := mem_iUnion.mp hu
      obtain ⟨hu'', hu⟩ := mem_iUnion.mp hu
      exact ⟨u, hu', hu'', hu⟩
    have hz := claim (u - s) (by omega)
    have e : s + (u - s) = u := by omega
    have hzu : z u hu h1 h2 ∈ W := by
      have : ∀ v (hv : v = u), z v (by omega) (by omega) (by omega) ∈ W → z u hu h1 h2 ∈ W := by
        intro v hv hzv; subst hv; exact hzv
      exact this _ e hz
    exact close _ hzu y hy (le_of_lt (lt_of_lt_of_le (hdist _ _ _
      (subset_closure (hzF u hu h1 h2)) hyu) (by linarith)))
  intro U V hcov hsep
  rcases hcov (hzA s (by omega) le_rfl hst) with h | h
  · exact Or.inl (side U V hcov hsep h)
  · exact Or.inr (side V U (hcov.trans (union_comm U V).le)
      (fun x hx y hy => by rw [dist_comm]; exact hsep y hy x hx) h)

/-- Links of a reversed chain, on natural-number indices. -/
theorem reverse_link_mk {n : ℕ} (C : Chain X n) {i : ℕ} (hi : i < n) :
    C.reverse.link ⟨i, hi⟩ = C.link ⟨n - 1 - i, by omega⟩ := by
  simp only [Chain.reverse_link]
  congr 1; ext; simp [Fin.val_rev]; omega

/-- **Bing's subchains stay between.** Let the closures of the links of `C'` lie in links of `C`,
the closures of the links `a < b` of `C'` in the links `s`, `t` of `C` (`s + 2 ≤ t`), and no link
strictly between `a` and `b` have closure in the link `s` or in the link `t`. Then `a + 2 ≤ b` and
every link of `C'` from `a` to `b` has closure in a link of `C` from `s` to `t`. -/
theorem refine_between {n n' : ℕ} (C : Chain X n) (C' : Chain X n') {s t : ℕ} (hst : s + 2 ≤ t)
    (htn : t < n) {a b : ℕ} (hab : a < b) (hbn : b < n')
    (hcl : ∀ u : Fin n', ∃ v : Fin n, closure (C'.link u) ⊆ C.link v)
    (ha : closure (C'.link ⟨a, by omega⟩) ⊆ C.link ⟨s, by omega⟩)
    (hb : closure (C'.link ⟨b, hbn⟩) ⊆ C.link ⟨t, htn⟩)
    (hmin : ∀ c (hc : c < n'), a < c → c < b →
      ¬ closure (C'.link ⟨c, hc⟩) ⊆ C.link ⟨s, by omega⟩ ∧
      ¬ closure (C'.link ⟨c, hc⟩) ⊆ C.link ⟨t, htn⟩) :
    a + 2 ≤ b ∧ ∀ u (hu : u < n'), a ≤ u → u ≤ b →
      ∃ v, ∃ hv : v < n, s ≤ v ∧ v ≤ t ∧ closure (C'.link ⟨u, hu⟩) ⊆ C.link ⟨v, hv⟩ := by
  classical
  have hdisj : ∀ (i j : ℕ) (hi : i < n) (hj : j < n), i + 2 ≤ j →
      C.link ⟨i, hi⟩ ∩ C.link ⟨j, hj⟩ = ∅ := by
    intro i j hi hj hij
    by_contra hne
    have := (C.adjacent_iff ⟨i, hi⟩ ⟨j, hj⟩).mp (Set.nonempty_iff_ne_empty.mpr hne)
    simp only at this; omega
  refine ⟨?_, ?_⟩
  · by_contra hlt
    have hb' : b = a + 1 := by omega
    subst hb'
    obtain ⟨w, hw1, hw2⟩ := (C'.adjacent_iff ⟨a, by omega⟩ ⟨a + 1, hbn⟩).mpr (by simp only; omega)
    have := hdisj s t (by omega) htn hst
    exact (Set.eq_empty_iff_forall_notMem.mp this) w ⟨ha (subset_closure hw1), hb (subset_closure hw2)⟩
  -- a choice of `C`-index for each link of `C'`, pinned at `a` and `b`
  set π : ℕ → ℕ := fun u => if u = a then s else if u = b then t else
    if h : u < n' then (hcl ⟨u, h⟩).choose.val else 0 with hπ
  have hπspec : ∀ u (hu : u < n'), ∃ hv : π u < n, closure (C'.link ⟨u, hu⟩) ⊆ C.link ⟨π u, hv⟩ := by
    intro u hu
    by_cases h1 : u = a
    · subst h1; simp only [hπ, if_true]; exact ⟨by omega, ha⟩
    by_cases h2 : u = b
    · subst h2; simp only [hπ, if_neg h1, if_true]; exact ⟨htn, hb⟩
    simp only [hπ, if_neg h1, if_neg h2, dif_pos hu]
    exact ⟨(hcl ⟨u, hu⟩).choose.isLt, (hcl ⟨u, hu⟩).choose_spec⟩
  have hπa : π a = s := by simp [hπ]
  have hπb : π b = t := by simp [hπ, show b ≠ a by omega]
  have hstep : ∀ u, a ≤ u → u < b → |(π (u + 1) : ℤ) - π u| ≤ 1 := by
    intro u _ hub
    obtain ⟨hv1, h1⟩ := hπspec u (by omega)
    obtain ⟨hv2, h2⟩ := hπspec (u + 1) (by omega)
    obtain ⟨w, hw1, hw2⟩ := (C'.adjacent_iff ⟨u, by omega⟩ ⟨u + 1, by omega⟩).mpr
      (by simp only; omega)
    have := (C.adjacent_iff ⟨π u, hv1⟩ ⟨π (u + 1), hv2⟩).mp
      ⟨w, h1 (subset_closure hw1), h2 (subset_closure hw2)⟩
    simp only at this
    rw [abs_le]; constructor <;> omega
  have hne : ∀ u (hu : u < n'), a < u → u < b → π u ≠ s ∧ π u ≠ t := by
    intro u hu h1 h2
    obtain ⟨hv, hsub⟩ := hπspec u hu
    obtain ⟨hs', ht'⟩ := hmin u hu h1 h2
    refine ⟨fun e => hs' ?_, fun e => ht' ?_⟩
    · convert hsub using 3; exact e.symm
    · convert hsub using 3; exact e.symm
  intro u hu hau hub
  obtain ⟨hv, hsub⟩ := hπspec u hu
  refine ⟨π u, hv, ?_, ?_, hsub⟩
  · by_contra hlt
    push_neg at hlt
    obtain ⟨w, hw1, hw2, hw3⟩ := int_ivt (fun v => (π v : ℤ)) hub
      (fun v h1 h2 => hstep v (by omega) h2) (c := s) (by simp only; omega)
      (by simp only [hπb]; omega)
    replace hw3 : (π w : ℤ) = s := hw3
    have hwb : w ≠ b := fun h => by rw [h, hπb] at hw3; omega
    have hwa : a < w := by
      rcases eq_or_lt_of_le hau with h | h
      · subst h; exfalso; rw [hπa] at hlt; omega
      · omega
    exact (hne w (by omega) hwa (by omega)).1 (by omega)
  · by_contra hlt
    push_neg at hlt
    obtain ⟨w, hw1, hw2, hw3⟩ := int_ivt (fun v => (π v : ℤ)) hau
      (fun v h1 h2 => hstep v h1 (by omega)) (c := t) (by simp only [hπa]; omega)
      (by simp only; omega)
    replace hw3 : (π w : ℤ) = t := hw3
    have hwa : w ≠ a := fun h => by rw [h, hπa] at hw3; omega
    have hwb : w < b := by
      rcases eq_or_lt_of_le hub with h | h
      · subst h; exfalso; rw [hπb] at hlt; omega
      · omega
    exact (hne w (by omega) (by omega) hwb).2 (by omega)

/-- **One level of Bing's construction.** From a chain `C` covering the compact connected set `M`
(every link meeting `M`) and indices `s + 2 ≤ t`, a finer chain `C'` of mesh `< ε` of the same
kind, with indices `s' + 2 ≤ t'`, such that the closures of the links `s'`, `t'` of `C'` lie in
the links `s`, `t` of `C`, and every link of `C'` from `s'` to `t'` has closure in a link of `C`
from `s` to `t`. -/
theorem exists_next_level {M : Set X} (hMc : IsCompact M) (hMconn : IsPreconnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ M ⊆ D.union)
    {n : ℕ} (C : Chain X n) (hMC : M ⊆ C.union) (hCM : ∀ i, (C.link i ∩ M).Nonempty)
    {s t : ℕ} (hst : s + 2 ≤ t) (htn : t < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n' : ℕ) (C' : Chain X n') (s' t' : ℕ) (_ : s' + 2 ≤ t') (ht' : t' < n'),
      IsEpsChain C' ε ∧ M ⊆ C'.union ∧ (∀ i, (C'.link i ∩ M).Nonempty) ∧
      closure (C'.link ⟨s', by omega⟩) ⊆ C.link ⟨s, by omega⟩ ∧
      closure (C'.link ⟨t', ht'⟩) ⊆ C.link ⟨t, htn⟩ ∧
      ∀ u (hu : u < n'), s' ≤ u → u ≤ t' →
        ∃ v, ∃ hv : v < n, s ≤ v ∧ v ≤ t ∧ closure (C'.link ⟨u, hu⟩) ⊆ C.link ⟨v, hv⟩ := by
  classical
  have hMne : M.Nonempty := by
    obtain ⟨z, -, hz⟩ := hCM ⟨s, by omega⟩; exact ⟨z, hz⟩
  obtain ⟨lam, hlam, hleb⟩ := lebesgue_number_lemma_of_metric hMc (fun i => C.isOpen i)
    (by simpa [Chain.union] using hMC)
  obtain ⟨y₀, hy₀C, hy₀M⟩ := hCM ⟨s, by omega⟩
  obtain ⟨y₁, hy₁C, hy₁M⟩ := hCM ⟨t, htn⟩
  obtain ⟨r₀, hr₀, hr₀C⟩ := Metric.isOpen_iff.mp (C.isOpen _) y₀ hy₀C
  obtain ⟨r₁, hr₁, hr₁C⟩ := Metric.isOpen_iff.mp (C.isOpen _) y₁ hy₁C
  set η := min (min ε (lam / 2)) (min (r₀ / 2) (r₁ / 2)) with hη
  have hη0 : 0 < η := lt_min (lt_min hε (by linarith)) (lt_min (by linarith) (by linarith))
  have hη1 : η ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hη2 : η ≤ lam / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hη3 : η ≤ r₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hη4 : η ≤ r₁ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨n', C', hC'ε, hMC', hC'M⟩ := exists_cover_meeting hMconn hMne hsnake hη0
  have hC'ε' : IsEpsChain C' ε := fun i => ⟨(hC'ε i).1, (hC'ε i).2.trans_le hη1⟩
  -- closures of small links around a point lie in a ball about it
  have hball : ∀ (u : Fin n') (z : X) (r : ℝ), z ∈ C'.link u → η ≤ r / 2 → 0 < r →
      closure (C'.link u) ⊆ ball z r := fun u z r hz hr hr0 =>
    (closure_subset_closedBall_diam (hC'ε u).1 hz).trans
      (closedBall_subset_ball (by have := (hC'ε u).2; linarith))
  have hcl : ∀ u : Fin n', ∃ v : Fin n, closure (C'.link u) ⊆ C.link v := by
    intro u
    obtain ⟨z, hzu, hzM⟩ := hC'M u
    obtain ⟨v, hv⟩ := hleb z hzM
    exact ⟨v, (hball u z lam hzu hη2 hlam).trans hv⟩
  obtain ⟨a₀, ha₀⟩ := mem_iUnion.mp (hMC' hy₀M)
  obtain ⟨b₀, hb₀⟩ := mem_iUnion.mp (hMC' hy₁M)
  have ha₀C : closure (C'.link a₀) ⊆ C.link ⟨s, by omega⟩ := (hball a₀ y₀ r₀ ha₀ hη3 hr₀).trans hr₀C
  have hb₀C : closure (C'.link b₀) ⊆ C.link ⟨t, htn⟩ := (hball b₀ y₁ r₁ hb₀ hη4 hr₁).trans hr₁C
  -- a pair of candidates at minimal distance
  set P := (Finset.univ ×ˢ Finset.univ : Finset (Fin n' × Fin n')).filter
    (fun x => closure (C'.link x.1) ⊆ C.link ⟨s, by omega⟩ ∧
      closure (C'.link x.2) ⊆ C.link ⟨t, htn⟩) with hP
  have hPne : P.Nonempty := ⟨(a₀, b₀), by simp [hP, ha₀C, hb₀C]⟩
  obtain ⟨⟨u₀, w₀⟩, hmemP, hminP⟩ := P.exists_min_image
    (fun x => (x.1.val - x.2.val) + (x.2.val - x.1.val)) hPne
  simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hmemP hminP
  obtain ⟨hu₀, hw₀⟩ := hmemP
  have hdisjC : C.link ⟨s, by omega⟩ ∩ C.link ⟨t, htn⟩ = ∅ := by
    by_contra hne
    have := (C.adjacent_iff ⟨s, by omega⟩ ⟨t, htn⟩).mp (Set.nonempty_iff_ne_empty.mpr hne)
    simp only at this; omega
  have hne₀ : u₀ ≠ w₀ := by
    intro e
    subst e
    obtain ⟨z, hz⟩ := C'.link_nonempty u₀
    exact (Set.eq_empty_iff_forall_notMem.mp hdisjC) z
      ⟨hu₀ (subset_closure hz), hw₀ (subset_closure hz)⟩
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne₀) with hlt | hgt
  · -- `u₀ < w₀`: use `C'` itself
    obtain ⟨hab, hbet⟩ := refine_between C C' hst htn hlt w₀.isLt hcl hu₀ hw₀
      (fun c hc h1 h2 => ⟨fun hs => by
          have := hminP (⟨c, hc⟩, w₀) ⟨hs, hw₀⟩; simp only at this; omega,
        fun ht => by
          have := hminP (u₀, ⟨c, hc⟩) ⟨hu₀, ht⟩; simp only at this; omega⟩)
    exact ⟨n', C', u₀, w₀, hab, w₀.isLt, hC'ε', hMC', hC'M, hu₀, hw₀, hbet⟩
  · -- `w₀ < u₀`: use the reverse of `C'`
    set R := C'.reverse
    have hRl : ∀ i (hi : i < n'), R.link ⟨i, hi⟩ = C'.link ⟨n' - 1 - i, by omega⟩ :=
      fun i hi => reverse_link_mk C' hi
    have hu₀' : closure (R.link ⟨n' - 1 - u₀.val, by omega⟩) ⊆ C.link ⟨s, by omega⟩ := by
      have e : (⟨n' - 1 - (n' - 1 - u₀.val), by omega⟩ : Fin n') = u₀ :=
        Fin.ext (by simp only; omega)
      rw [hRl, e]; exact hu₀
    have hw₀' : closure (R.link ⟨n' - 1 - w₀.val, by omega⟩) ⊆ C.link ⟨t, htn⟩ := by
      have e : (⟨n' - 1 - (n' - 1 - w₀.val), by omega⟩ : Fin n') = w₀ :=
        Fin.ext (by simp only; omega)
      rw [hRl, e]; exact hw₀
    obtain ⟨hab, hbet⟩ := refine_between C R hst htn (a := n' - 1 - u₀.val)
      (b := n' - 1 - w₀.val) (by omega) (by omega)
      (fun u => by
        obtain ⟨v, hv⟩ := hcl (Fin.rev u)
        exact ⟨v, by rw [Chain.reverse_link]; exact hv⟩)
      hu₀' hw₀'
      (fun c hc h1 h2 => by
        rw [hRl c hc]
        refine ⟨fun hs => ?_, fun ht => ?_⟩
        · have := hminP (⟨n' - 1 - c, by omega⟩, w₀) ⟨hs, hw₀⟩; simp only at this; omega
        · have := hminP (u₀, ⟨n' - 1 - c, by omega⟩) ⟨hu₀, ht⟩; simp only at this; omega)
    refine ⟨n', R, n' - 1 - u₀.val, n' - 1 - w₀.val, hab, by omega, fun i => ?_, ?_, fun i => ?_,
      hu₀', hw₀', hbet⟩
    · rw [Chain.reverse_link]; exact hC'ε' _
    · intro z hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hMC' hz)
      exact mem_iUnion.mpr ⟨Fin.rev i, by rw [Chain.reverse_link, Fin.rev_rev]; exact hi⟩
    · rw [Chain.reverse_link]; exact hC'M _

/-- One level of Bing's construction: a chain covering `M`, every link meeting `M`, with two
marked indices `s + 2 ≤ t`. -/
structure Level51 (M : Set X) where
  n : ℕ
  C : Chain X n
  s : ℕ
  t : ℕ
  hst : s + 2 ≤ t
  htn : t < n
  cov : M ⊆ C.union
  meet : ∀ i, (C.link i ∩ M).Nonempty

/-- **Bing's sequence of chains (Theorem 15).** For a nondegenerate compact connected `M` covered
by chains of arbitrarily small mesh: chains `C k` of mesh `< 1/(k+1)` covering `M`, every link
meeting `M`, with indices `s k + 2 ≤ t k`, the closures of the links `s (k+1)`, `t (k+1)` in the
links `s k`, `t k`, and the links from `s (k+1)` to `t (k+1)` having closures in links from `s k`
to `t k`. -/
theorem exists_level_sequence {M : Set X} (hMc : IsCompact M) (hMconn : IsPreconnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ M ⊆ D.union)
    (hnd : M.Nontrivial) :
    ∃ L : ℕ → Level51 M, (∀ k, IsEpsChain (L k).C (1 / ((k : ℝ) + 1))) ∧
      (∀ k, closure ((L (k + 1)).C.link ⟨(L (k + 1)).s, by
          have := (L (k + 1)).hst; have := (L (k + 1)).htn; omega⟩) ⊆
        (L k).C.link ⟨(L k).s, by have := (L k).hst; have := (L k).htn; omega⟩) ∧
      (∀ k, closure ((L (k + 1)).C.link ⟨(L (k + 1)).t, (L (k + 1)).htn⟩) ⊆
        (L k).C.link ⟨(L k).t, (L k).htn⟩) ∧
      (∀ k u (hu : u < (L (k + 1)).n), (L (k + 1)).s ≤ u → u ≤ (L (k + 1)).t →
        ∃ v, ∃ hv : v < (L k).n, (L k).s ≤ v ∧ v ≤ (L k).t ∧
          closure ((L (k + 1)).C.link ⟨u, hu⟩) ⊆ (L k).C.link ⟨v, hv⟩) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hnd
  have hdab : 0 < dist a b := dist_pos.mpr hab
  -- the first level
  have hL0 : ∃ L : Level51 M, IsEpsChain L.C 1 := by
    set ε₀ := min (dist a b / 3) 1
    have hε₀ : 0 < ε₀ := lt_min (by linarith) one_pos
    obtain ⟨n, C, hCε, hMC, hCM⟩ := exists_cover_meeting hMconn ⟨a, ha⟩ hsnake hε₀
    obtain ⟨ia, hia⟩ := mem_iUnion.mp (hMC ha)
    obtain ⟨ib, hib⟩ := mem_iUnion.mp (hMC hb)
    have hfar : ¬ (ia.val ≤ ib.val + 1 ∧ ib.val ≤ ia.val + 1) := by
      intro hclose
      have := C.dist_le_of_links (fun i => (hCε i).1) (fun i => (hCε i).2)
      rcases le_total ia.val ib.val with h | h
      · have h1 := this (ib.val - ia.val) ia ib (by omega) a hia b hib
        have h2 : ((ib.val - ia.val : ℕ) : ℝ) ≤ 1 := by
          have : ib.val - ia.val ≤ 1 := by omega
          exact_mod_cast this
        have h3 := min_le_left (dist a b / 3) 1
        nlinarith
      · have h1 := this (ia.val - ib.val) ib ia (by omega) b hib a hia
        have h2 : ((ia.val - ib.val : ℕ) : ℝ) ≤ 1 := by
          have : ia.val - ib.val ≤ 1 := by omega
          exact_mod_cast this
        have h3 := min_le_left (dist a b / 3) 1
        rw [dist_comm] at h1
        nlinarith
    refine ⟨⟨n, C, min ia.val ib.val, max ia.val ib.val, by omega, by omega, hMC, hCM⟩,
      fun i => ⟨(hCε i).1, (hCε i).2.trans_le (min_le_right _ _)⟩⟩
  obtain ⟨L0, hL0ε⟩ := hL0
  -- the step
  have step : ∀ (L : Level51 M) (k : ℕ), ∃ L' : Level51 M, IsEpsChain L'.C (1 / ((k : ℝ) + 2)) ∧
      closure (L'.C.link ⟨L'.s, by have := L'.hst; have := L'.htn; omega⟩) ⊆
        L.C.link ⟨L.s, by have := L.hst; have := L.htn; omega⟩ ∧
      closure (L'.C.link ⟨L'.t, L'.htn⟩) ⊆ L.C.link ⟨L.t, L.htn⟩ ∧
      ∀ u (hu : u < L'.n), L'.s ≤ u → u ≤ L'.t →
        ∃ v, ∃ hv : v < L.n, L.s ≤ v ∧ v ≤ L.t ∧ closure (L'.C.link ⟨u, hu⟩) ⊆ L.C.link ⟨v, hv⟩ := by
    intro L k
    obtain ⟨n', C', s', t', hst', htn', hC'ε, hMC', hC'M, hs, ht, hbet⟩ :=
      exists_next_level hMc hMconn hsnake L.C L.cov L.meet L.hst L.htn
        (ε := 1 / ((k : ℝ) + 2)) (by positivity)
    exact ⟨⟨n', C', s', t', hst', htn', hMC', hC'M⟩, hC'ε, hs, ht, hbet⟩
  choose next hnext using step
  set L : ℕ → Level51 M := fun k => Nat.rec L0 (fun k L => next L k) k with hL
  have hLsucc : ∀ k, L (k + 1) = next (L k) k := fun k => rfl
  refine ⟨L, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · cases k with
    | zero => simpa using hL0ε
    | succ k =>
      rw [hLsucc]
      have := (hnext (L k) k).1
      intro i
      refine ⟨(this i).1, (this i).2.trans_le (le_of_eq ?_)⟩
      push_cast; ring
  · exact (hnext (L k) k).2.1
  · exact (hnext (L k) k).2.2.1
  · exact (hnext (L k) k).2.2.2

end HPC.Plane
