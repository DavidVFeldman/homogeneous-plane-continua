import HPC.BJ59.Thm9Base

/-!
# Batch 200, §5: Bing–Jones, Theorem 9 (p. 179)

Route: commission 200 §5. After `bj9_base`, a sequence of pairs of chains `D_i`, `E_i` in
Bing–Jones's sense with the same number of links, each link with a private point, is built by
alternating half-steps: a fine chain on one side refines the other side's chain through a chain map
(`π`, onto by the private points), and Theorem 7 supplies the corresponding chain on the other side.
The homeomorphism of pp. 188–189 (`zigzag_homeomorph`, with `H_i` the identity) finishes.

* `BJ9Stage`: a matched pair of chains;
* `bj9_half`, `bj9_step`;
* `bj_theorem9` (verbatim).
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Thm9

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- An `ε`-chain refined (link by link) by another chain makes the latter an `ε`-chain. -/
theorem isEpsChain_of_refine {n k : ℕ} {F : Chain Y n} {G : Chain Y k} {δ : ℝ}
    (hF : IsEpsChain F δ) (π : Fin k → Fin n) (hG : ∀ a, G.link a ⊆ F.link (π a)) :
    IsEpsChain G δ := fun a =>
  ⟨(hF (π a)).1.subset (hG a), lt_of_le_of_lt (diam_mono (hG a) (hF (π a)).1) (hF (π a)).2⟩

/-- A chain map composed with a chain map. -/
theorem IsChainMap.comp' {k l n : ℕ} {f : Fin l → Fin n} {g : Fin k → Fin l} (hf : IsChainMap f)
    (hg : IsChainMap g) : IsChainMap (f ∘ g) := fun a b hab => hf _ _ (hg a b hab)

/-- **The half-step.** Given a chain `E` on `Q` with private points and a chain `D` properly covering
`P` with the same number of links, a fine chain `E′` on `Q` and a chain `D′` on `P` with the same
number of links, both in Bing–Jones's sense and with private points, refine `E` and `D` through a
common chain map. -/
theorem bj9_half {P : Set X} {Q : Set Y} (hP : IsPseudoArc P) (hQ : IsPseudoArc Q) {N : ℕ}
    (D : Chain X N) (E : Chain Y N) (hDP : P ⊆ D.union) (hEQ : Q ⊆ E.union)
    (hDp : ∀ j, (D.link j ∩ P).Nonempty)
    (hEpr : ∀ j, ∃ q ∈ Q ∩ E.link j, ∀ j', j' ≠ j → q ∉ closure (E.link j'))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K : ℕ) (D' : Chain X K) (E' : Chain Y K) (π : Fin K → Fin N), IsChainMap π ∧
      IsBJChain D' ∧ IsBJChain E' ∧ P ⊆ D'.union ∧ Q ⊆ E'.union ∧
      (∀ j, ∃ p ∈ P ∩ D'.link j, ∀ j', j' ≠ j → p ∉ closure (D'.link j')) ∧
      (∀ j, ∃ q ∈ Q ∩ E'.link j, ∀ j', j' ≠ j → q ∉ closure (E'.link j')) ∧
      IsEpsChain E' δ ∧ (∀ a, D'.link a ⊆ D.link (π a)) ∧ (∀ a, E'.link a ⊆ E.link (π a)) := by
  classical
  obtain ⟨lam, hlam, hleb⟩ := lebesgue_number_lemma_of_metric hQ.1.1.1 E.isOpen hEQ
  obtain ⟨K, F, hFbj, hFε, hQF, hFQ⟩ :=
    exists_fine_bjChain hQ.1 (lt_min hδ hlam) hQ.2.2.nonempty
  have hπ : ∀ a, ∃ i, F.link a ⊆ E.link i := by
    intro a
    obtain ⟨x, hxa, hxQ⟩ := hFQ a
    obtain ⟨i, hi⟩ := hleb x hxQ
    refine ⟨i, fun y hy => hi ?_⟩
    rw [mem_ball]
    exact lt_of_lt_of_le (dist_lt_of_mem_link hFε a hy hxa) (min_le_right _ _)
  choose π hπ using hπ
  have hπc : IsChainMap π := by
    intro a b hab
    obtain ⟨z, hza, hzb⟩ := (F.adjacent a b).2 hab
    exact (E.adjacent _ _).1 ⟨z, hπ a hza, hπ b hzb⟩
  have hπs : Function.Surjective π := by
    intro i
    obtain ⟨q, ⟨hqQ, hqi⟩, hqpr⟩ := hEpr i
    obtain ⟨a, ha⟩ := mem_iUnion.1 (hQF hqQ)
    refine ⟨a, ?_⟩
    by_contra hne
    exact hqpr (π a) hne (subset_closure (hπ a ha))
  obtain ⟨D1, hD1bj, hPD1, hD1P, hD1s⟩ := bj_theorem7 hP D hDP hDp π hπc hπs
  obtain ⟨D2, hD2bj, hPD2, hD2s, hD2pr⟩ :=
    exists_privatePoint_shrink hP.1.1 hP.2.2 D1 hD1bj hPD1 hD1P
  obtain ⟨F2, hF2bj, hQF2, hF2s, hF2pr⟩ :=
    exists_privatePoint_shrink hQ.1.1 hQ.2.2 F hFbj hQF hFQ
  refine ⟨K, D2, F2, π, hπc, hD2bj, hF2bj, hPD2, hQF2, hD2pr, hF2pr, ?_,
    fun a => (hD2s a).trans (hD1s a), fun a => (hF2s a).trans (hπ a)⟩
  have hFδ : IsEpsChain F δ := fun a => ⟨(hFε a).1, lt_of_lt_of_le (hFε a).2 (min_le_left _ _)⟩
  exact isEpsChain_of_refine hFδ id hF2s

/-- A matched pair of chains: chains in Bing–Jones's sense on `P` and `Q` with the same number of
links, covering, each link with a private point. -/
structure BJ9Stage (P : Set X) (Q : Set Y) where
  N : ℕ
  D : Chain X N
  E : Chain Y N
  hDbj : IsBJChain D
  hEbj : IsBJChain E
  hDP : P ⊆ D.union
  hEQ : Q ⊆ E.union
  hDpr : ∀ j, ∃ p ∈ P ∩ D.link j, ∀ j', j' ≠ j → p ∉ closure (D.link j')
  hEpr : ∀ j, ∃ q ∈ Q ∩ E.link j, ∀ j', j' ≠ j → q ∉ closure (E.link j')

omit [MetricSpace X] in
theorem meets_of_private {S : Set X} {n : ℕ} {L : Fin n → Set X} {cl : Set X → Set X}
    (h : ∀ j, ∃ p ∈ S ∩ L j, ∀ j', j' ≠ j → p ∉ cl (L j')) (j : Fin n) : (L j ∩ S).Nonempty := by
  obtain ⟨p, ⟨hpS, hpj⟩, -⟩ := h j
  exact ⟨p, hpj, hpS⟩

/-- **A full step**: both sides refined to mesh `δ` through a common chain map. -/
theorem bj9_step {P : Set X} {Q : Set Y} (hP : IsPseudoArc P) (hQ : IsPseudoArc Q)
    (S : BJ9Stage P Q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (T : BJ9Stage P Q) (π : Fin T.N → Fin S.N), IsChainMap π ∧ IsEpsChain T.D δ ∧
      IsEpsChain T.E δ ∧ (∀ a, T.D.link a ⊆ S.D.link (π a)) ∧
      (∀ a, T.E.link a ⊆ S.E.link (π a)) := by
  obtain ⟨K1, D1, E1, π1, hπ1, hD1bj, hE1bj, hPD1, hQE1, hD1pr, hE1pr, hE1ε, hD1s, hE1s⟩ :=
    bj9_half hP hQ S.D S.E S.hDP S.hEQ (meets_of_private S.hDpr) S.hEpr hδ
  obtain ⟨K2, E2, D2, π2, hπ2, hE2bj, hD2bj, hQE2, hPD2, hE2pr, hD2pr, hD2ε, hE2s, hD2s⟩ :=
    bj9_half hQ hP E1 D1 hQE1 hPD1 (meets_of_private hE1pr) hD1pr hδ
  refine ⟨⟨K2, D2, E2, hD2bj, hE2bj, hPD2, hQE2, hD2pr, hE2pr⟩, π1 ∘ π2, hπ1.comp' hπ2, hD2ε,
    isEpsChain_of_refine hE1ε π2 hE2s, fun a => (hD2s a).trans (hD1s _), fun a => (hE2s a).trans (hE1s _)⟩

/-- **Bing–Jones, Theorem 9** (p. 179). -/
theorem bj_theorem9 {P : Set X} {Q : Set Y} (hP : IsPseudoArc P) (hQ : IsPseudoArc Q) {n m : ℕ}
    (D : Chain X n) (E : Chain Y m) (hD : IsBJChain D) (hE : IsBJChain E)
    (hDP : P ⊆ D.union) (hDp : ∀ i, (D.link i ∩ P).Nonempty)
    (hEQ : Q ⊆ E.union) (hEq : ∀ j, (E.link j ∩ Q).Nonempty)
    (H : Fin n → Fin m) (hH : IsChainMap H)
    (hHo : ∀ j, ∃ i, H i = j ∧ ∃ p ∈ P ∩ D.link i, ∀ i', i' ≠ i → p ∉ closure (D.link i')) :
    ∃ h : P ≃ₜ Q, ∀ (i : Fin n) (p : P), (p : X) ∈ D.link i → (h p : Y) ∈ E.link (H i) := by
  classical
  obtain ⟨N0, D0, E0, hD0bj, hE0bj, hPD0, -, hQE0, -, hD0pr, hE0pr, hcl⟩ :=
    bj9_base hP hQ D E hD hE hDP hDp hEQ hEq H hH hHo
  let S0 : BJ9Stage P Q := ⟨N0, D0, E0, hD0bj, hE0bj, hPD0, hQE0, hD0pr, hE0pr⟩
  choose nxt π hπ hDε hEε hDs hEs using
    fun (S : BJ9Stage P Q) (k : ℕ) => bj9_step hP hQ S (δ := (1 / 2 : ℝ) ^ k) (by positivity)
  let seq : ℕ → BJ9Stage P Q := fun k => Nat.rec S0 (fun k S => nxt S k) k
  have hε : Tendsto (fun i : ℕ => (1 / 2 : ℝ) ^ i) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨h, hh⟩ := zigzag_homeomorph hP.1.1.1 hQ.1.1.1
    (n := fun i => (seq (i + 1)).N) (m := fun i => (seq (i + 1)).N)
    (fun i => (seq (i + 1)).D) (fun i => (seq (i + 1)).E)
    (fun i => (seq (i + 1)).hDP) (fun i => meets_of_private (seq (i + 1)).hDpr)
    (fun i => (seq (i + 1)).hEQ) (fun i => meets_of_private (seq (i + 1)).hEpr)
    (fun i => (seq (i + 1)).hEbj) hε (fun i => hDε (seq i) i) (fun i => hEε (seq i) i)
    (fun i => id) (fun i => π (seq (i + 1)) (i + 1))
    (fun i a b hab => hab) (fun i => Function.surjective_id) (fun i => hπ (seq (i + 1)) (i + 1))
    (fun i j => hDs (seq (i + 1)) (i + 1) j) (fun i j => hEs (seq (i + 1)) (i + 1) j)
  refine ⟨h, fun i p hpi => ?_⟩
  have h0 := (hh p (h p)).2 rfl 0
  obtain ⟨j, hpj, hqj⟩ := mem_closure_starImage h0
  have h1 := hcl i (π S0 0 j) p p.2 hpi (hDs S0 0 j hpj)
  exact h1 (closure_mono (hEs S0 0 j) hqj)

end Thm9

end HPC.BJ59
