import HPC.Fold.T9Blocks
import HPC.Fold.Theorem4

/-!
# Theorem 9: the construction

Batch 82. Bing's proof in the block reading, for `r < t < s`:

* `G₁` (Theorem 7 on `E(0, r)`) and `G₂` (Theorem 7 on `E(r, s)` read backwards) are overlaid into
  one block function `γ` on `0, …, s` (Bing's `H`, whose links are the unions of corresponding
  links of `G₁` and `G₂`; Theorem 8's union clause is what makes it crooked);
* `H + E(s+1, n)` is the block consolidation of `E` by `foldMap m s γ`, crooked in `D`
  (`crooked_foldChain`);
* Theorem 4 on `H + E(s+1, n)`, with first block the position of `t`, gives `K`;
* `F`: the blocks of `G₁` before the position `v` of `t`, then the blocks of `K`.
-/

namespace HPC.Fold

open HPC.Chain

variable {X : Type*} [MetricSpace X]

theorem link_subset_unionRange {m : ℕ} (D : Chain X m) (i : Fin m) :
    D.link i ⊆ D.unionRange i.val 3 := by
  intro x hx
  rw [mem_unionRange]
  exact ⟨i.val, le_rfl, by omega, i.isLt, hx⟩

/-- **Theorem 9 for `r < t < s`.** -/
theorem theorem9_core {n m : ℕ} (hm : 3 ≤ m) {E : Chain X n} {D : Chain X m}
    (hcr : E.IsCrookedIn' D) (hn : 0 < n) (r s t : ℕ) (hrt : r < t) (hts : t < s) (hsn : s < n)
    (h0 : E.link ⟨0, hn⟩ ⊆ D.link ⟨0, by omega⟩)
    (hlast : E.link ⟨n - 1, by omega⟩ ⊆ D.link ⟨m - 1, by omega⟩)
    (hr : E.link ⟨r, by omega⟩ ⊆ D.link ⟨m - 1, by omega⟩)
    (hs : E.link ⟨s, hsn⟩ ⊆ D.link ⟨0, by omega⟩) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β ⟨0, hn⟩).val = 0 ∧ (β ⟨n - 1, by omega⟩).val = q - 1 ∧
      (∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 3) ∧
      ∀ u : Fin n, r ≤ u.val → β ⟨t, by omega⟩ ≤ β u := by
  have hZ3 : 3 ≤ z (m - 1) := z_three_le (m - 1) (by omega)
  have hsn1 : s < n - 1 := by
    by_contra hc
    obtain ⟨x, hx⟩ := E.link_nonempty ⟨s, hsn⟩
    have h2 := hlast (show x ∈ E.link ⟨n - 1, by omega⟩ by
      rw [link_congr E _ hsn (show n - 1 = s by omega)]; exact hx)
    have := (D.adjacent_iff ⟨0, by omega⟩ ⟨m - 1, by omega⟩).1 ⟨x, hs hx, h2⟩
    simp only at this; omega
  -- `G₁` and `G₂`
  obtain ⟨b1, b1lt, b1lip, b10, b1r, b1f, b1t⟩ := exists_blocks_up hm hcr 0 r (by omega)
    (by omega) h0 hr
  obtain ⟨b2, b2lt, b2lip, b2r, b2s, b2f, b2t⟩ := exists_blocks_down hm hcr r s (by omega) hsn hr hs
  -- the overlay `H`
  obtain ⟨γ, hγ⟩ : ∃ γ : ℕ → ℕ, ∀ u, γ u = if u ≤ r then b1 u else b2 u := ⟨_, fun _ => rfl⟩
  have γ1 : ∀ u, u ≤ r → γ u = b1 u := fun u h => by rw [hγ, if_pos h]
  have γ2 : ∀ u, r ≤ u → γ u = b2 u := fun u h => by
    rw [hγ]
    split_ifs with h'
    · have : u = r := by omega
      subst this; rw [b1r, b2r]
    · rfl
  have hγlt : ∀ u, u ≤ s → γ u < z (m - 1) := fun u hu => by
    rcases le_total u r with h | h
    · rw [γ1 u h]; exact b1lt u (Nat.zero_le _) h
    · rw [γ2 u h]; exact b2lt u h hu
  have hγ1 : ∀ u (hu : u ≤ s), ∃ i : Fin m, (i : ℤ) = bingF (m - 1) (γ u) ∧
      E.link ⟨u, by omega⟩ ⊆ D.link i := fun u hu => by
    rcases le_total u r with h | h
    · rw [γ1 u h]; exact b1f u (Nat.zero_le _) h
    · rw [γ2 u h]; exact b2f u h hu
  have hγ2 : ∀ u (hu : u ≤ s) (i : Fin m), (E.link ⟨u, by omega⟩ ∩ D.link i).Nonempty →
      ∃ u' : ℕ, u' < z (m - 1) ∧ u' ≤ γ u + 1 ∧ γ u ≤ u' + 1 ∧ (i : ℤ) = bingF (m - 1) u' :=
    fun u hu i hne => by
    rcases le_total u r with h | h
    · rw [γ1 u h]; exact b1t u (Nat.zero_le _) h i hne
    · rw [γ2 u h]; exact b2t u h hu i hne
  have hγlip : ∀ u, u < s → (γ (u + 1) : ℤ) - γ u ≤ 1 ∧ (γ u : ℤ) - γ (u + 1) ≤ 1 := by
    intro u hu
    rcases Nat.lt_or_ge u r with h | h
    · rw [γ1 u h.le, γ1 (u + 1) h]; exact b1lip u (Nat.zero_le _) h
    · rw [γ2 u h, γ2 (u + 1) (by omega)]; exact b2lip u h hu
  -- the folded chain `H + E(s+1, n)`
  have g1 : ∀ u, u ≤ s → foldMap m s γ u = z (m - 1) - 1 - γ u := fun u h => by
    unfold foldMap; rw [if_pos h]
  have g2 : ∀ u, s < u → foldMap m s γ u = z (m - 1) - 1 + (u - s) := fun u h => by
    unfold foldMap; rw [if_neg (by omega)]
  have hlt : ∀ u, u < n → foldMap m s γ u < z (m - 1) + (n - 1 - s) := fun u hu => by
    rcases le_or_gt u s with h | h
    · rw [g1 u h]; omega
    · rw [g2 u h]; omega
  have hglip : ∀ u, u + 1 < n → (foldMap m s γ (u + 1) : ℤ) - foldMap m s γ u ≤ 1 ∧
      (foldMap m s γ u : ℤ) - foldMap m s γ (u + 1) ≤ 1 := by
    intro u hu
    rcases Nat.lt_or_ge u s with h | h
    · rw [g1 u h.le, g1 (u + 1) h]
      have := hγlip u h; have := hγlt u h.le; have := hγlt (u + 1) h
      omega
    · rcases eq_or_lt_of_le h with e | e
      · rw [← e, g1 s le_rfl, g2 (s + 1) (by omega), γ2 s (by omega), b2s]
        omega
      · rw [g2 u e, g2 (u + 1) (by omega)]; omega
  have gr : foldMap m s γ r = 0 := by rw [g1 r (by omega), γ1 r le_rfl, b1r]; omega
  have gs : foldMap m s γ s = z (m - 1) - 1 := by rw [g1 s le_rfl, γ2 s (by omega), b2s]; rfl
  have gn : foldMap m s γ (n - 1) = z (m - 1) + (n - 1 - s) - 1 := by rw [g2 (n - 1) (by omega)]; omega
  have g0 : foldMap m s γ 0 = z (m - 1) - 1 := by rw [g1 0 (by omega), γ1 0 (by omega), b10]; rfl
  have gt : foldMap m s γ t = z (m - 1) - 1 - γ t := g1 t hts.le
  have hgsurj : ∀ j, j < z (m - 1) + (n - 1 - s) → ∃ u, u < n ∧ foldMap m s γ u = j := by
    intro j hj
    obtain ⟨u, hu1, hu2, hu3⟩ := nat_ivt (foldMap m s γ) r (n - 1 - r)
      (fun u h1 h2 => hglip u (by omega)) j (by
        left; rw [gr, show r + (n - 1 - r) = n - 1 by omega, gn]; omega)
    exact ⟨u, by omega, hu3⟩
  have hb := isBlockMap_natBlock (foldMap m s γ) hlt hglip hgsurj
  have hcr' := crooked_foldChain hm hcr hsn γ hγlt hγ1 hγ2 hs hlt hb
  -- `K`: Theorem 4 on `H + E(s+1, n)`
  have hin : ∀ u (hu : u < n), E.link ⟨u, hu⟩ ⊆
      (E.ofBlocks _ hb).link ⟨foldMap m s γ u, hlt u hu⟩ :=
    fun u hu => link_subset_ofBlocks E hb ⟨u, hu⟩
  have hvZ : γ t < z (m - 1) := hγlt t hts.le
  obtain ⟨q, β', hβ', hβ'0, hβ'1, hmesh⟩ := theorem4 (by omega) hm hcr'
    ⟨foldMap m s γ t, hlt t (by omega)⟩ ⟨z (m - 1) + (n - 1 - s) - 1, by omega⟩
    (by rw [Fin.le_def]; simp only; rw [gt]; omega)
    ⟨⟨z (m - 1) - 1, by omega⟩, by rw [Fin.le_def]; simp only; rw [gt]; omega,
      by rw [Fin.le_def]; simp only; omega, by
        obtain ⟨x, hx⟩ := E.link_nonempty ⟨s, hsn⟩
        refine ⟨x, ?_, hs hx⟩
        have := hin s hsn hx
        rwa [show (⟨foldMap m s γ s, hlt s hsn⟩ : Fin _) = ⟨z (m - 1) - 1, by omega⟩ from
          Fin.ext gs] at this⟩
    ⟨⟨z (m - 1) + (n - 1 - s) - 1, by omega⟩, by rw [Fin.le_def]; simp only; rw [gt]; omega,
      le_rfl, by
        obtain ⟨x, hx⟩ := E.link_nonempty ⟨n - 1, by omega⟩
        refine ⟨x, ?_, hlast hx⟩
        have := hin (n - 1) (by omega) hx
        rwa [show (⟨foldMap m s γ (n - 1), hlt (n - 1) (by omega)⟩ : Fin _) =
          ⟨z (m - 1) + (n - 1 - s) - 1, by omega⟩ from Fin.ext gn] at this⟩
  -- the composite block function of `K`
  obtain ⟨bF, hbF⟩ : ∃ bF : ℕ → ℕ, ∀ u (hu : u < n),
      bF u = (β' ⟨foldMap m s γ u, hlt u hu⟩).val :=
    ⟨fun u => if hu : u < n then (β' ⟨foldMap m s γ u, hlt u hu⟩).val else 0,
      fun u hu => by simp [hu]⟩
  have bFlt : ∀ u, u < n → bF u < q := fun u hu => by rw [hbF u hu]; exact (β' _).isLt
  have bFeq : ∀ u v (hu : u < n) (hv : v < n), foldMap m s γ u = foldMap m s γ v → bF u = bF v :=
    fun u v hu hv h => by rw [hbF u hu, hbF v hv]; congr 2; exact Fin.ext h
  have bFt : bF t = 0 := by rw [hbF t (by omega)]; exact hβ'0
  have bFn : bF (n - 1) = q - 1 := by
    rw [hbF _ (by omega)]
    rw [show (⟨foldMap m s γ (n - 1), hlt (n - 1) (by omega)⟩ : Fin _) =
      ⟨z (m - 1) + (n - 1 - s) - 1, by omega⟩ from Fin.ext gn]
    exact hβ'1
  have bFlip : ∀ u, u + 1 < n → (bF (u + 1) : ℤ) - bF u ≤ 1 ∧ (bF u : ℤ) - bF (u + 1) ≤ 1 := by
    intro u hu
    have hg := hglip u hu
    rcases (show foldMap m s γ (u + 1) = foldMap m s γ u ∨
        foldMap m s γ (u + 1) = foldMap m s γ u + 1 ∨
        foldMap m s γ u = foldMap m s γ (u + 1) + 1 by omega) with e | e | e
    · rw [bFeq (u + 1) u hu (by omega) e]; omega
    · have := hβ'.lip ⟨foldMap m s γ u, hlt u (by omega)⟩ ⟨foldMap m s γ (u + 1), hlt _ hu⟩ e
      rw [hbF u (by omega), hbF (u + 1) hu]; omega
    · have := hβ'.lip ⟨foldMap m s γ (u + 1), hlt _ hu⟩ ⟨foldMap m s γ u, hlt u (by omega)⟩ e
      rw [hbF u (by omega), hbF (u + 1) hu]; omega
  -- the position of `t`, and the boundary of the retained part of `G₁`
  set v := γ t with hv
  have bFv : ∀ u, u ≤ r → b1 u = v → bF u = 0 := by
    intro u hu h
    rw [bFeq u t (by omega) (by omega) (by rw [g1 u (by omega), gt, γ1 u hu, h]), bFt]
  -- the final block function
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ, ∀ u, F u = if u ≤ r ∧ b1 u < v then b1 u else v + bF u :=
    ⟨_, fun _ => rfl⟩
  have FG : ∀ u, u ≤ r → b1 u < v → F u = b1 u := fun u h1 h2 => by rw [hF, if_pos ⟨h1, h2⟩]
  have FR : ∀ u, ¬ (u ≤ r ∧ b1 u < v) → F u = v + bF u := fun u h => by rw [hF, if_neg h]
  have Flt : ∀ u, u < n → F u < v + q := by
    intro u hu
    by_cases h : u ≤ r ∧ b1 u < v
    · rw [FG u h.1 h.2]; have := bFlt u hu; omega
    · rw [FR u h]; have := bFlt u hu; omega
  have Flip : ∀ u, u + 1 < n → (F (u + 1) : ℤ) - F u ≤ 1 ∧ (F u : ℤ) - F (u + 1) ≤ 1 := by
    intro u hu
    have hbl := bFlip u hu
    by_cases h1 : u ≤ r ∧ b1 u < v <;> by_cases h2 : u + 1 ≤ r ∧ b1 (u + 1) < v
    · rw [FG u h1.1 h1.2, FG (u + 1) h2.1 h2.2]; exact b1lip u (Nat.zero_le _) (by omega)
    · rw [FG u h1.1 h1.2, FR (u + 1) h2]
      have hur : u + 1 ≤ r := by
        by_contra hc
        have : u = r := by omega
        rw [this, b1r] at h1; omega
      have := b1lip u (Nat.zero_le _) (by omega)
      have hb1 : b1 (u + 1) = v := by omega
      rw [bFv (u + 1) hur hb1]
      omega
    · rw [FR u h1, FG (u + 1) h2.1 h2.2]
      have := b1lip u (Nat.zero_le _) (by omega)
      have hb1 : b1 u = v := by omega
      rw [bFv u (by omega) hb1]
      omega
    · rw [FR u h1, FR (u + 1) h2]; omega
  have Fsurj : ∀ j, j < v + q → ∃ u, u < n ∧ F u = j := by
    intro j hj
    rcases Nat.lt_or_ge j v with h | h
    · obtain ⟨u, hu1, hu2, hu3⟩ := nat_ivt b1 0 r (fun u h1 h2 => b1lip u h1 (by omega)) j (by
        left; rw [b10, show 0 + r = r by omega, b1r]; omega)
      exact ⟨u, by omega, by rw [FG u (by omega) (by omega), hu3]⟩
    · obtain ⟨u, hu1, hu2, hu3⟩ := nat_ivt bF t (n - 1 - t) (fun u h1 h2 => bFlip u (by omega))
        (j - v) (by left; rw [bFt, show t + (n - 1 - t) = n - 1 by omega, bFn]; omega)
      exact ⟨u, by omega, by rw [FR u (by omega), hu3]; omega⟩
  have hβ := isBlockMap_natBlock F Flt Flip Fsurj
  have F0 : F 0 = 0 := by
    rcases Nat.eq_zero_or_pos v with h | h
    · rw [FR 0 (by omega), h, zero_add]
      rw [bFeq 0 t hn (by omega) (by rw [g0, gt]; omega), bFt]
    · rw [FG 0 (by omega) (by rw [b10]; exact h), b10]
  have Fn : F (n - 1) = v + q - 1 := by
    rw [FR _ (by omega), bFn]
    have := bFlt t (by omega)
    omega
  have Fge : ∀ u, r ≤ u → v ≤ F u := by
    intro u hu
    rw [FR u (by
      rintro ⟨h1, h2⟩
      have : u = r := by omega
      rw [this, b1r] at h2; omega)]
    omega
  have Ft : F t = v := by rw [FR t (by omega), bFt]; rfl
  refine ⟨v + q, natBlock F Flt, hβ, F0, Fn, fun j => ?_, fun u hu => ?_⟩
  · rcases Nat.lt_or_ge j.val v with hj | hj
    · refine ⟨(bingF (m - 1) j.val).toNat, ofBlocks_link_subset E hβ j _ (fun u hu => ?_)⟩
      simp only [natBlock, Fin.ext_iff] at hu
      have hG : u.val ≤ r ∧ b1 u.val < v := by
        by_contra hc
        rw [FR _ hc] at hu; omega
      rw [FG _ hG.1 hG.2] at hu
      obtain ⟨i, hi, hsub⟩ := b1f u.val (Nat.zero_le _) hG.1
      refine hsub.trans ((link_subset_unionRange D i).trans (le_of_eq ?_))
      congr 1; rw [hu] at hi; omega
    · obtain ⟨j', hj'⟩ := hmesh ⟨j.val - v, by have := j.isLt; omega⟩
      refine ⟨j', ofBlocks_link_subset E hβ j _ (fun u hu => ?_)⟩
      simp only [natBlock, Fin.ext_iff] at hu
      have hR : ¬ (u.val ≤ r ∧ b1 u.val < v) := by
        rintro hc
        rw [FG _ hc.1 hc.2] at hu; omega
      rw [FR _ hR] at hu
      refine (hin u.val u.isLt).trans ((link_subset_ofBlocks _ hβ' _).trans (le_of_eq ?_)
        |>.trans hj')
      congr 1; apply Fin.ext; rw [← hbF u.val u.isLt]; simp only; omega
  · simp only [natBlock, Fin.le_def]
    rw [Ft]; exact Fge u.val hu

end HPC.Fold
