import HPC.Fold.T7Assemble
import HPC.Fold.BingLocal

/-!
# Theorem 8: tightness and orientation

Batch 82. A chain with `z (m-1)` links crooked in `D` and following Bing's pattern meets only the
levels of its own and neighbouring positions (`tight_of_crooked`); hence the union of two such
chains, when it is a chain, is crooked (`crooked_union_of_bingF`). A block map of `Fin p` onto
itself is the identity or the reversal (`blockMap_self`).
-/

namespace HPC.Fold

open HPC.Chain

variable {X : Type*} [MetricSpace X]

/-- **Tightness.** A chain crooked in `D` whose links follow `bingF (m-1)` meets a link of `D`
only at the level of its own position or of a neighbouring one. -/
theorem tight_of_crooked {m : ℕ} {F : Chain X (z (m - 1))} {D : Chain X m}
    (hcr : F.IsCrookedIn' D)
    (h1 : ∀ u : Fin (z (m - 1)), ∃ i : Fin m, (i : ℤ) = bingF (m - 1) u ∧ F.link u ⊆ D.link i)
    (u : Fin (z (m - 1))) (l : Fin m) (hul : (F.link u ∩ D.link l).Nonempty) :
    ∃ u' : ℕ, u' < z (m - 1) ∧ u' ≤ u.val + 1 ∧ u.val ≤ u' + 1 ∧ (l : ℤ) = bingF (m - 1) u' := by
  have hsub : ∀ (w : Fin (z (m - 1))) (i : Fin m), (i : ℤ) = bingF (m - 1) w → F.link w ⊆ D.link i := by
    intro w i hi
    obtain ⟨i', hi', hsub'⟩ := h1 w
    have : i' = i := Fin.ext (by omega)
    rw [← this]; exact hsub'
  have hlip := bingF_lip (m - 1)
  have hflat := (bingF_local (m - 1)).1
  have hloc := (bingF_local (m - 1)).2
  have hle : ∀ w, bingF (m - 1) w ≤ (m : ℤ) - 1 := fun w => by
    have := bingF_le (m - 1) w; have := l.isLt; omega
  have hge : ∀ w, 0 ≤ bingF (m - 1) w := fun w => bingF_nonneg _ _
  have hZtop : bingF (m - 1) (z (m - 1) - 1) = (m : ℤ) - 1 := by
    rw [bingF_top _ _ le_rfl]; have := l.isLt; omega
  have hg0 : bingF (m - 1) 0 = 0 := bingF_zero _
  obtain ⟨i, hi, hFi⟩ := h1 u
  have hu := u.isLt
  have hil : ((i : ℤ) - (l : ℤ)).natAbs ≤ 1 := by
    rw [← D.adjacent]
    obtain ⟨x, hx1, hx2⟩ := hul
    exact ⟨x, hFi hx1, hx2⟩
  -- a neighbour of `u` inside the chain has a level one away from `u`'s
  have step : ∀ a b : ℕ, a + 1 = b → b < z (m - 1) → bingF (m - 1) b = bingF (m - 1) a + 1 ∨ bingF (m - 1) b = bingF (m - 1) a - 1 := by
    intro a b hab hb
    have h := hlip a; have hf := hflat a (Nat.zero_le _) (by omega)
    rw [hab] at h hf; rw [abs_le] at h
    omega
  have hlt : (l : ℤ) < m := by exact_mod_cast l.isLt
  rcases (show (l : ℤ) = i ∨ (l : ℤ) = i - 1 ∨ (l : ℤ) = i + 1 by omega) with e | e | e
  · exact ⟨u.val, hu, by omega, by omega, by rw [e, hi]⟩
  · -- `l` one below
    by_cases hA : 1 ≤ u.val ∧ bingF (m - 1) (u.val - 1) = l
    · exact ⟨u.val - 1, by omega, by omega, by omega, hA.2.symm⟩
    by_cases hB : u.val + 1 < z (m - 1) ∧ bingF (m - 1) (u.val + 1) = l
    · exact ⟨u.val + 1, hB.1, by omega, by omega, hB.2.symm⟩
    exfalso
    have hu0 : 1 ≤ u.val := by
      by_contra h0
      have : u.val = 0 := by omega
      rw [this, hg0] at hi; have := (l : ℕ).cast_nonneg (α := ℤ); omega
    have hu1 : u.val + 1 < z (m - 1) := by
      by_contra h0
      have hZu : u.val = z (m - 1) - 1 := by omega
      have := step (u.val - 1) u.val (by omega) hu
      rw [hZu] at this hi
      rw [show z (m - 1) - 1 - 1 = u.val - 1 by omega] at this
      have := hle (u.val - 1)
      apply hA; refine ⟨hu0, ?_⟩; omega
    have s1 := step (u.val - 1) u.val (by omega) hu
    have s2 := step u.val (u.val + 1) rfl hu1
    have ha : bingF (m - 1) (u.val - 1) = bingF (m - 1) u.val + 1 := by
      rcases s1 with h | h
      · exact absurd ⟨hu0, by omega⟩ hA
      · linarith
    have hb : bingF (m - 1) (u.val + 1) = bingF (m - 1) u.val + 1 := by
      rcases s2 with h | h
      · linarith
      · exact absurd ⟨hu1, by omega⟩ hB
    obtain ⟨j, hj, hjg, hjd⟩ : ∃ j : ℕ, j < z (m - 1) ∧ bingF (m - 1) j = bingF (m - 1) u.val + 2 ∧ (j + 2 = u.val ∨ j = u.val + 2) := by
      rcases (hloc u.val (by omega) (by omega)).1 ha hb with ⟨c, h⟩ | ⟨c, h⟩
      · exact ⟨u.val - 2, by omega, h, by omega⟩
      · exact ⟨u.val + 2, by omega, h, by omega⟩
    have hk : bingF (m - 1) j < m := by have := hle j; omega
    let k : Fin m := ⟨(bingF (m - 1) j).toNat, by omega⟩
    have hkv : ((k : ℕ) : ℤ) = bingF (m - 1) j := by simp only [k]; omega
    have hFj := hsub ⟨j, hj⟩ k hkv
    obtain ⟨y, hy⟩ := F.link_nonempty ⟨j, hj⟩
    obtain ⟨r, s, hbt, -, -⟩ := hcr.2 l k (by omega) u ⟨j, hj⟩ hul ⟨y, hy, hFj hy⟩
    unfold Between at hbt
    simp only [Fin.lt_def, gt_iff_lt] at hbt
    omega
  · -- `l` one above
    by_cases hA : 1 ≤ u.val ∧ bingF (m - 1) (u.val - 1) = l
    · exact ⟨u.val - 1, by omega, by omega, by omega, hA.2.symm⟩
    by_cases hB : u.val + 1 < z (m - 1) ∧ bingF (m - 1) (u.val + 1) = l
    · exact ⟨u.val + 1, hB.1, by omega, by omega, hB.2.symm⟩
    exfalso
    have hu1 : u.val + 1 < z (m - 1) := by
      by_contra h0
      have hZu : u.val = z (m - 1) - 1 := by omega
      rw [hZu, hZtop] at hi; omega
    have hu0 : 1 ≤ u.val := by
      by_contra h0
      have h0' : u.val = 0 := by omega
      have := step 0 1 rfl (by omega)
      rw [hg0] at this
      rw [h0', hg0] at hi
      have := hge 1
      apply hB; refine ⟨hu1, ?_⟩; rw [h0', zero_add]; omega
    have s1 := step (u.val - 1) u.val (by omega) hu
    have s2 := step u.val (u.val + 1) rfl hu1
    have ha : bingF (m - 1) (u.val - 1) = bingF (m - 1) u.val - 1 := by
      rcases s1 with h | h
      · linarith
      · exact absurd ⟨hu0, by omega⟩ hA
    have hb : bingF (m - 1) (u.val + 1) = bingF (m - 1) u.val - 1 := by
      rcases s2 with h | h
      · exact absurd ⟨hu1, by omega⟩ hB
      · linarith
    obtain ⟨j, hj, hjg, hjd⟩ : ∃ j : ℕ, j < z (m - 1) ∧ bingF (m - 1) j = bingF (m - 1) u.val - 2 ∧ (j + 2 = u.val ∨ j = u.val + 2) := by
      rcases (hloc u.val (by omega) (by omega)).2 ha hb with ⟨c, h⟩ | ⟨c, h⟩
      · exact ⟨u.val - 2, by omega, h, by omega⟩
      · exact ⟨u.val + 2, by omega, h, by omega⟩
    have hk : 0 ≤ bingF (m - 1) j := hge j
    let k : Fin m := ⟨(bingF (m - 1) j).toNat, by omega⟩
    have hkv : ((k : ℕ) : ℤ) = bingF (m - 1) j := by simp only [k]; omega
    have hFj := hsub ⟨j, hj⟩ k hkv
    obtain ⟨y, hy⟩ := F.link_nonempty ⟨j, hj⟩
    obtain ⟨r, s, hbt, -, -⟩ := hcr.2 k l (by omega) ⟨j, hj⟩ u ⟨y, hy, hFj hy⟩ hul
    unfold Between at hbt
    simp only [Fin.lt_def, gt_iff_lt] at hbt
    omega

/-- **Theorem 8, union clause.** If two chains with `z (m-1)` links are crooked in `D` and both
follow `bingF (m-1)`, a chain whose links are the unions of corresponding links is crooked in
`D`. -/
theorem crooked_union_of_bingF {m : ℕ} {F₁ F₂ C : Chain X (z (m - 1))} {D : Chain X m}
    (hc₁ : F₁.IsCrookedIn' D) (hc₂ : F₂.IsCrookedIn' D)
    (hf₁ : ∀ u : Fin (z (m - 1)), ∃ i : Fin m, (i : ℤ) = bingF (m - 1) u ∧ F₁.link u ⊆ D.link i)
    (hf₂ : ∀ u : Fin (z (m - 1)), ∃ i : Fin m, (i : ℤ) = bingF (m - 1) u ∧ F₂.link u ⊆ D.link i)
    (hC : ∀ u, C.link u = F₁.link u ∪ F₂.link u) : C.IsCrookedIn' D := by
  refine crooked_of_tight (fun u => ?_) (fun u l hul => ?_)
  · obtain ⟨i, hi, h1⟩ := hf₁ u
    obtain ⟨i', hi', h2⟩ := hf₂ u
    have : i' = i := Fin.ext (by omega)
    subst this
    exact ⟨i', hi, by rw [hC]; exact Set.union_subset h1 h2⟩
  · rw [hC, Set.union_inter_distrib_right] at hul
    rcases Set.union_nonempty.1 hul with h | h
    · exact tight_of_crooked hc₁ hf₁ u l h
    · exact tight_of_crooked hc₂ hf₂ u l h

/-- A block map of `Fin p` onto itself is the identity or the reversal. -/
theorem blockMap_self {p : ℕ} {β : Fin p → Fin p} (hβ : IsBlockMap β) :
    (∀ t, β t = t) ∨ (∀ t, (β t).val = p - 1 - t.val) := by
  have hinj : Function.Injective β := Finite.injective_iff_surjective.2 hβ.surj
  rcases Nat.lt_or_ge p 2 with hp | hp
  · left; intro t; apply Fin.ext; have := (β t).isLt; have := t.isLt; omega
  let G : ℕ → ℤ := fun t => if h : t < p then ((β ⟨t, h⟩ : ℕ) : ℤ) else 0
  have hG : ∀ t (h : t < p), G t = ((β ⟨t, h⟩ : ℕ) : ℤ) := fun t h => by simp [G, h]
  have hne : ∀ a b (ha : a < p) (hb : b < p), a ≠ b → G a ≠ G b := by
    intro a b ha hb hab e
    rw [hG a ha, hG b hb] at e
    have := hinj (Fin.ext (by exact_mod_cast e) : β ⟨a, ha⟩ = β ⟨b, hb⟩)
    exact hab (congrArg Fin.val this)
  have hstep : ∀ t, t + 1 < p → G (t + 1) - G t = 1 ∨ G (t + 1) - G t = -1 := by
    intro t ht
    have h1 := hβ.lip ⟨t, by omega⟩ ⟨t + 1, ht⟩ rfl
    have h2 := hne (t + 1) t ht (by omega) (by omega)
    rw [hG (t + 1) ht, hG t (by omega)] at h2 ⊢
    omega
  set c := G 1 - G 0 with hc
  have hlin : ∀ t, t < p → G t = G 0 + c * t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      match t, ih, ht with
      | 0, _, _ => simp
      | 1, _, _ => simp [hc]
      | t + 2, ih, ht =>
        have e1 := ih (t + 1) (by omega) (by omega)
        have e0 := ih t (by omega) (by omega)
        have s1 := hstep (t + 1) ht
        have n2 := hne (t + 2) t ht (by omega) (by omega)
        have hc1 : c = 1 ∨ c = -1 := by have := hstep 0 (by omega); simpa [hc] using this
        push_cast at e1 e0 ⊢
        rcases hc1 with h | h <;> rw [h] at e1 e0 ⊢ <;> rcases s1 with s | s <;>
          first | linarith | (exfalso; apply n2; linarith)
  have hc1 : c = 1 ∨ c = -1 := by have := hstep 0 (by omega); simpa [hc] using this
  have hbd : ∀ t, t < p → 0 ≤ G t ∧ G t ≤ p - 1 := fun t ht => by
    rw [hG t ht]; have := (β ⟨t, ht⟩).isLt; omega
  have e0 := hbd 0 (by omega)
  have eL := hbd (p - 1) (by omega)
  rw [hlin (p - 1) (by omega)] at eL
  push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at eL
  rcases hc1 with h | h
  · left; intro t
    apply Fin.ext
    have ht := hlin t.val t.isLt
    rw [hG t.val t.isLt, h, Fin.eta] at ht
    have h0 : G 0 = 0 := by rw [h] at eL; linarith
    omega
  · right; intro t
    have ht := hlin t.val t.isLt
    rw [hG t.val t.isLt, h, Fin.eta] at ht
    have h0 : G 0 = p - 1 := by rw [h] at eL; linarith
    have := t.isLt
    omega

end HPC.Fold
