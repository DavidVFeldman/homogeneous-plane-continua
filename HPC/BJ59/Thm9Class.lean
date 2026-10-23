import HPC.BJ59.Thm8Lib

/-!
# Batch 200, §5: tools for Theorem 9

* `mem_linkN_iff`;
* `IsBJChain.exists_uniform`: one positive distance for all pairs of nonadjacent links;
* `chain_of_classes`: links of a chain in Bing–Jones's sense sorted into classes `0, …, N − 1`,
  such that meeting links have adjacent classes and the end classes are hit, give a chain of `N`
  links (the unions of the classes) in Bing–Jones's sense; used for the consolidation `D″` and for
  the chains `D′`, `E′` of Bing–Jones's second simplification (pp. 179–180).
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Class

variable {X : Type*} [MetricSpace X]

theorem mem_linkN_iff {n : ℕ} (T : Chain X n) {j : ℕ} {x : X} :
    x ∈ T.linkN j ↔ ∃ h : j < n, x ∈ T.link ⟨j, h⟩ := by
  unfold HPC.Chain.linkN
  split_ifs with h
  · exact ⟨fun hx => ⟨h, hx⟩, fun ⟨_, hx⟩ => hx⟩
  · exact ⟨fun hx => absurd hx (notMem_empty x), fun ⟨h', _⟩ => absurd h' h⟩

theorem mem_linkN_of_mem {n : ℕ} (T : Chain X n) (j : Fin n) {x : X} (hx : x ∈ T.link j) :
    x ∈ T.linkN j.val := (mem_linkN_iff T).2 ⟨j.isLt, hx⟩

theorem lt_of_mem_linkN {n : ℕ} (T : Chain X n) {j : ℕ} {x : X} (hx : x ∈ T.linkN j) : j < n :=
  ((mem_linkN_iff T).1 hx).1

/-- Links of a chain whose `ℕ`-indices are not adjacent are disjoint; adjacency from a common
point. -/
theorem linkN_adj {n : ℕ} (T : Chain X n) {i j : ℕ} {x : X} (hi : x ∈ T.linkN i)
    (hj : x ∈ T.linkN j) : i ≤ j + 1 ∧ j ≤ i + 1 := by
  constructor
  · by_contra h; exact T.linkN_disj (by omega) hj hi
  · by_contra h; exact T.linkN_disj (by omega) hi hj

/-- **One separation constant** for a chain in Bing–Jones's sense. -/
theorem IsBJChain.exists_uniform {n : ℕ} {D : Chain X n} (hD : IsBJChain D) :
    ∃ δ > 0, ∀ i j : ℕ, i + 2 ≤ j → ∀ x ∈ D.linkN i, ∀ y ∈ D.linkN j, δ ≤ dist x y := by
  classical
  have hpair : ∀ p : Fin n × Fin n, ∃ δ > 0, 1 < ((p.1 : ℤ) - p.2).natAbs →
      ∀ x ∈ D.link p.1, ∀ y ∈ D.link p.2, δ ≤ dist x y := by
    intro p
    by_cases h : 1 < ((p.1 : ℤ) - p.2).natAbs
    · obtain ⟨δ, hδ, hd⟩ := hD p.1 p.2 h
      exact ⟨δ, hδ, fun _ => hd⟩
    · exact ⟨1, one_pos, fun h' => absurd h' h⟩
  choose δ hδ hδd using hpair
  obtain ⟨r, hr, hrle⟩ := exists_pos_forall_le δ hδ
  refine ⟨r, hr, fun i j hij x hx y hy => ?_⟩
  obtain ⟨hi, hx⟩ := (mem_linkN_iff D).1 hx
  obtain ⟨hj, hy⟩ := (mem_linkN_iff D).1 hy
  exact (hrle (⟨i, hi⟩, ⟨j, hj⟩)).trans (hδd (⟨i, hi⟩, ⟨j, hj⟩) (by simp only; omega) x hx y hy)

/-- **A chain from classes.** The links of a chain `G` in Bing–Jones's sense, covering a
preconnected `S` and each meeting it, sorted into classes `0, …, N − 1` (a link may a priori lie in
several), such that links that meet have adjacent classes and the two end classes are hit: the
unions of the classes form a chain of `N` links in Bing–Jones's sense covering `S`, each link
meeting `S`. -/
theorem chain_of_classes {S : Set X} (hS : IsPreconnected S) {K N : ℕ} (G : Chain X K)
    (hG : IsBJChain G) (hGS : S ⊆ G.union) (hGs : ∀ a, (G.link a ∩ S).Nonempty)
    (Cls : ℕ → Fin K → Prop) (hcov : ∀ a, ∃ c < N, Cls c a)
    (hsep : ∀ a b c c', Cls c a → Cls c' b → (G.link a ∩ G.link b).Nonempty →
      c ≤ c' + 1 ∧ c' ≤ c + 1)
    (hN : 0 < N) (h0 : ∃ a, Cls 0 a) (h1 : ∃ a, Cls (N - 1) a) :
    ∃ D : Chain X N, IsBJChain D ∧ S ⊆ D.union ∧ (∀ c, (D.link c ∩ S).Nonempty) ∧
      ∀ c : Fin N, D.link c = ⋃ (a : Fin K) (_ : Cls c a), G.link a := by
  classical
  set W : Fin N → Set X := fun c => ⋃ (a : Fin K) (_ : Cls c a), G.link a with hW
  have hWo : ∀ c, IsOpen (W c) := fun c => isOpen_iUnion fun a => isOpen_iUnion fun _ => G.isOpen a
  have hWcov : S ⊆ ⋃ c, W c := by
    intro x hx
    obtain ⟨a, ha⟩ := mem_iUnion.1 (hGS hx)
    obtain ⟨c, hcN, hc⟩ := hcov a
    exact mem_iUnion.2 ⟨⟨c, hcN⟩, mem_iUnion₂.2 ⟨a, hc, ha⟩⟩
  have hWdisj : ∀ c c' : Fin N, 1 < ((c : ℤ) - c').natAbs → W c ∩ W c' = ∅ := by
    intro c c' hcc
    refine eq_empty_of_forall_notMem fun x ⟨hxc, hxc'⟩ => ?_
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 hxc
    obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.1 hxc'
    have := hsep a b c c' ha hb ⟨x, hxa, hxb⟩
    omega
  have hWS0 : (W ⟨0, hN⟩ ∩ S).Nonempty := by
    obtain ⟨a, ha⟩ := h0
    obtain ⟨x, hx, hxS⟩ := hGs a
    exact ⟨x, mem_iUnion₂.2 ⟨a, ha, hx⟩, hxS⟩
  have hWS1 : (W ⟨N - 1, by omega⟩ ∩ S).Nonempty := by
    obtain ⟨a, ha⟩ := h1
    obtain ⟨x, hx, hxS⟩ := hGs a
    exact ⟨x, mem_iUnion₂.2 ⟨a, ha, hx⟩, hxS⟩
  have hWS : ∀ c, (W c ∩ S).Nonempty := fun c =>
    family_meets_all W hWo hWdisj hS hWcov ⟨0, hN⟩ ⟨N - 1, by omega⟩ hWS0 hWS1 c
      (Nat.zero_le _) (by have := c.isLt; simp only; omega)
  let D : Chain X N :=
    { link := W
      isOpen := hWo
      adjacent := fun i j => by
        constructor
        · intro h
          by_contra h'
          push_neg at h'
          rw [hWdisj i j h'] at h
          exact not_nonempty_empty h
        · intro h
          rcases lt_trichotomy i.val j.val with hlt | heq | hgt
          · exact adjacent_meet_of_cover hS W hWo hWcov hWS hWdisj i j (by omega)
          · have : i = j := Fin.ext heq
            subst this
            obtain ⟨x, hx, -⟩ := hWS i
            exact ⟨x, hx, hx⟩
          · rw [inter_comm]
            exact adjacent_meet_of_cover hS W hWo hWcov hWS hWdisj j i (by omega) }
  refine ⟨D, ?_, hWcov, hWS, fun c => rfl⟩
  -- Bing–Jones's sense
  intro c c' hcc
  have hpair : ∀ p : Fin K × Fin K, ∃ δ > 0, 1 < ((p.1 : ℤ) - p.2).natAbs →
      ∀ x ∈ G.link p.1, ∀ y ∈ G.link p.2, δ ≤ dist x y := by
    intro p
    by_cases h : 1 < ((p.1 : ℤ) - p.2).natAbs
    · obtain ⟨δ, hδ, hd⟩ := hG p.1 p.2 h
      exact ⟨δ, hδ, fun _ => hd⟩
    · exact ⟨1, one_pos, fun h' => absurd h' h⟩
  choose δ hδ hδd using hpair
  obtain ⟨r, hr, hrle⟩ := exists_pos_forall_le δ hδ
  refine ⟨r, hr, fun x hx y hy => ?_⟩
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 hx
  obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.1 hy
  have hab : 1 < ((a : ℤ) - b).natAbs := by
    by_contra h
    push_neg at h
    have := hsep a b c c' ha hb ((G.adjacent a b).2 h)
    omega
  exact (hrle (a, b)).trans (hδd (a, b) hab x hxa y hyb)

/-- **The consolidation** of a chain along a chain map onto. -/
theorem exists_consolidation {S : Set X} (hS : IsPreconnected S) (hSne : S.Nonempty) {n m : ℕ}
    (D : Chain X n) (hD : IsBJChain D) (hDS : S ⊆ D.union) (hDs : ∀ i, (D.link i ∩ S).Nonempty)
    (H : Fin n → Fin m) (hH : IsChainMap H) (hHs : Function.Surjective H) :
    ∃ D' : Chain X m, IsBJChain D' ∧ S ⊆ D'.union ∧ (∀ j, (D'.link j ∩ S).Nonempty) ∧
      ∀ j : Fin m, D'.link j = ⋃ (i : Fin n) (_ : (H i).val = j.val), D.link i := by
  obtain ⟨x0, hx0⟩ := hSne
  obtain ⟨i0, -⟩ := mem_iUnion.1 (hDS hx0)
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (H i0).isLt
  obtain ⟨a0, ha0⟩ := hHs ⟨0, hm⟩
  obtain ⟨a1, ha1⟩ := hHs ⟨m - 1, by omega⟩
  exact chain_of_classes hS D hD hDS hDs (fun c a => (H a).val = c)
    (fun a => ⟨(H a).val, (H a).isLt, rfl⟩)
    (fun a b c c' ha hb hab => by
      have := hH a b ((D.adjacent a b).1 hab)
      simp only at ha hb
      omega)
    hm ⟨a0, by simp [ha0]⟩ ⟨a1, by simp [ha1]⟩

end Class

end HPC.BJ59
