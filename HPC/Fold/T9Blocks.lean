import HPC.Fold.T9Fold

/-!
# Theorem 9: the consolidations `G₁`, `G₂` of Theorem 7 on subchains

Batch 82. For a subchain `E(a, c)` running from the first link of `D` to the last
(`exists_blocks_up`) or from the last to the first (`exists_blocks_down`), a block function on the
fine indices `a, …, c` following Bing's pattern, tight, with the end links in the end blocks.
-/

namespace HPC.Fold

open HPC.Chain

variable {X : Type*} [MetricSpace X]

theorem link_subset_ofBlocks {n p : ℕ} (E : Chain X n) {β : Fin n → Fin p} (hβ : IsBlockMap β)
    (t : Fin n) : E.link t ⊆ (E.ofBlocks β hβ).link (β t) := by
  intro x hx
  rw [ofBlocks_link]
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨t, rfl, hx⟩

theorem ofBlocks_link_subset {n p : ℕ} (E : Chain X n) {β : Fin n → Fin p} (hβ : IsBlockMap β)
    (j : Fin p) (S : Set X) (h : ∀ t, β t = j → E.link t ⊆ S) :
    (E.ofBlocks β hβ).link j ⊆ S := by
  intro x hx
  rw [ofBlocks_link] at hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  exact h t ht hxt

theorem link_congr {n : ℕ} (E : Chain X n) {a b : ℕ} (ha : a < n) (hb : b < n) (h : a = b) :
    E.link ⟨a, ha⟩ = E.link ⟨b, hb⟩ := by
  subst h; rfl

/-- `G₁`: a subchain from the first link of `D` to the last. -/
theorem exists_blocks_up {n m : ℕ} (hm : 3 ≤ m) {E : Chain X n} {D : Chain X m}
    (hcr : E.IsCrookedIn' D) (a c : ℕ) (hac : a ≤ c) (hc : c < n)
    (ha0 : E.link ⟨a, by omega⟩ ⊆ D.link ⟨0, by omega⟩)
    (hc1 : E.link ⟨c, hc⟩ ⊆ D.link ⟨m - 1, by omega⟩) :
    ∃ b : ℕ → ℕ, (∀ t, a ≤ t → t ≤ c → b t < z (m - 1)) ∧
      (∀ t, a ≤ t → t < c → (b (t + 1) : ℤ) - b t ≤ 1 ∧ (b t : ℤ) - b (t + 1) ≤ 1) ∧
      b a = 0 ∧ b c = z (m - 1) - 1 ∧
      (∀ t, a ≤ t → ∀ (hc' : t ≤ c), ∃ i : Fin m, (i : ℤ) = bingF (m - 1) (b t) ∧
        E.link ⟨t, by omega⟩ ⊆ D.link i) ∧
      (∀ t, a ≤ t → ∀ (hc' : t ≤ c) (i : Fin m), (E.link ⟨t, by omega⟩ ∩ D.link i).Nonempty →
        ∃ u' : ℕ, u' < z (m - 1) ∧ u' ≤ b t + 1 ∧ b t ≤ u' + 1 ∧
          (i : ℤ) = bingF (m - 1) u') := by
  have hle : (⟨a, by omega⟩ : Fin n) ≤ ⟨c, hc⟩ := by rw [Fin.le_def]; exact hac
  let F : Chain X (c - a + 1) := E.sub ⟨a, by omega⟩ ⟨c, hc⟩ hle
  have hF : F.IsCrookedIn' D := hcr.sub _ _ hle
  have key : ∀ k (hk : k < c - a + 1), F.link ⟨k, hk⟩ = E.link ⟨a + k, by omega⟩ :=
    fun _ _ => rfl
  obtain ⟨b', hlt, hlip, h0, hl, h1, h2⟩ := exists_nat_blocks_ends hm hF
    (by omega) (by rw [key]; exact ha0)
    (by rw [key, link_congr E _ hc (by omega)]; exact hc1)
  refine ⟨fun t => b' (t - a), fun t h1 h2 => hlt _ (by omega), fun t h1 h2 => ?_,
    by simp [h0], by simp only; rw [show c - a = c - a + 1 - 1 by omega, hl], fun t ha hc' => ?_,
    fun t ha hc' i hne => ?_⟩
  · have := hlip (t - a) (by omega)
    rw [show t - a + 1 = t + 1 - a by omega] at this
    exact this
  · obtain ⟨i, hi, hs⟩ := h1 (t - a) (by omega)
    rw [key, link_congr E (a := a + (t - a)) (b := t) _ (by omega) (by omega)] at hs
    exact ⟨i, hi, hs⟩
  · rw [link_congr E _ (show a + (t - a) < n by omega) (by omega)] at hne
    rw [← key (t - a) (by omega)] at hne
    exact h2 (t - a) (by omega) i hne

/-- `G₂`: a subchain from the last link of `D` to the first, read backwards. -/
theorem exists_blocks_down {n m : ℕ} (hm : 3 ≤ m) {E : Chain X n} {D : Chain X m}
    (hcr : E.IsCrookedIn' D) (a c : ℕ) (hac : a ≤ c) (hc : c < n)
    (ha1 : E.link ⟨a, by omega⟩ ⊆ D.link ⟨m - 1, by omega⟩)
    (hc0 : E.link ⟨c, hc⟩ ⊆ D.link ⟨0, by omega⟩) :
    ∃ b : ℕ → ℕ, (∀ t, a ≤ t → t ≤ c → b t < z (m - 1)) ∧
      (∀ t, a ≤ t → t < c → (b (t + 1) : ℤ) - b t ≤ 1 ∧ (b t : ℤ) - b (t + 1) ≤ 1) ∧
      b a = z (m - 1) - 1 ∧ b c = 0 ∧
      (∀ t, a ≤ t → ∀ (hc' : t ≤ c), ∃ i : Fin m, (i : ℤ) = bingF (m - 1) (b t) ∧
        E.link ⟨t, by omega⟩ ⊆ D.link i) ∧
      (∀ t, a ≤ t → ∀ (hc' : t ≤ c) (i : Fin m), (E.link ⟨t, by omega⟩ ∩ D.link i).Nonempty →
        ∃ u' : ℕ, u' < z (m - 1) ∧ u' ≤ b t + 1 ∧ b t ≤ u' + 1 ∧
          (i : ℤ) = bingF (m - 1) u') := by
  have hle : (⟨a, by omega⟩ : Fin n) ≤ ⟨c, hc⟩ := by rw [Fin.le_def]; exact hac
  let F : Chain X (c - a + 1) := (E.sub ⟨a, by omega⟩ ⟨c, hc⟩ hle).reverse
  have hF : F.IsCrookedIn' D := (hcr.sub _ _ hle).reverse_left
  have key : ∀ k (hk : k < c - a + 1), F.link ⟨k, hk⟩ = E.link ⟨c - k, by omega⟩ := by
    intro k hk
    show E.link _ = _
    exact link_congr E _ _ (by simp only [Fin.val_rev]; omega)
  obtain ⟨b', hlt, hlip, h0, hl, h1, h2⟩ := exists_nat_blocks_ends hm hF
    (by omega) (by rw [key, link_congr E _ hc (by omega)]; exact hc0)
    (by rw [key, link_congr E _ (show a < n by omega) (by omega)]; exact ha1)
  refine ⟨fun t => b' (c - t), fun t h1 h2 => hlt _ (by omega), fun t h1 h2 => ?_,
    by simp only; rw [show c - a = c - a + 1 - 1 by omega, hl], by simp [h0], fun t ha hc' => ?_,
    fun t ha hc' i hne => ?_⟩
  · have := hlip (c - (t + 1)) (by omega)
    rw [show c - (t + 1) + 1 = c - t by omega] at this
    simp only
    constructor <;> linarith [this.1, this.2]
  · obtain ⟨i, hi, hs⟩ := h1 (c - t) (by omega)
    rw [key, link_congr E (a := c - (c - t)) (b := t) _ (by omega) (by omega)] at hs
    exact ⟨i, hi, hs⟩
  · rw [link_congr E _ (show c - (c - t) < n by omega) (by omega)] at hne
    rw [← key (c - t) (by omega)] at hne
    exact h2 (c - t) (by omega) i hne

end HPC.Fold
