import HPC.Plane.Theorem11Gen

/-!
# Batch 198, library: the order of links along an arc of continua (Bing–Jones, Theorem 2)

The combinatorial core of Bing–Jones's Theorem 2 (p. 174), for arbitrary sets: `order_core`.
The printed proof leaves one step (commission 198, §6): that `G(b, c)` meets the link `d_t` lying
between the links meeting `G(0, b)` and those meeting `G(c, 1)`. Here `d_t` meets neither, so (the
chain covering the whole space) it meets `G(b, c)`.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane

variable {X : Type*} [MetricSpace X]

/-- Two disjoint compact sets are a positive distance apart. -/
theorem exists_sep_of_disjoint {P Q : Set X} (hP : IsCompact P) (hQ : IsCompact Q)
    (hPQ : Disjoint P Q) : ∃ ε > 0, ∀ x ∈ P, ∀ y ∈ Q, ε ≤ dist x y := by
  rcases P.eq_empty_or_nonempty with rfl | hPne
  · exact ⟨1, one_pos, fun x hx => absurd hx (notMem_empty x)⟩
  rcases Q.eq_empty_or_nonempty with rfl | hQne
  · exact ⟨1, one_pos, fun x _ y hy => absurd hy (notMem_empty y)⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hP.exists_isMinOn hPne (continuous_infDist_pt Q).continuousOn
  refine ⟨infDist x₀ Q, ?_, fun x hx y hy => (hmin hx).trans (infDist_le_dist_of_mem hy)⟩
  exact (hQ.isClosed.notMem_iff_infDist_pos hQne).1 (Set.disjoint_left.1 hPQ hx₀)

/-- A link of diameter less than `ε` cannot meet two sets `ε` apart. -/
theorem not_meets_both {n : ℕ} {D : Chain X n} {ε : ℝ} (hD : IsEpsChain D ε) {P Q : Set X}
    (hPQ : ∀ x ∈ P, ∀ y ∈ Q, ε ≤ dist x y) (i : Fin n) :
    ¬ ((D.link i ∩ P).Nonempty ∧ (D.link i ∩ Q).Nonempty) := by
  rintro ⟨⟨x, hxi, hxP⟩, ⟨y, hyi, hyQ⟩⟩
  have := dist_le_diam_of_mem (hD i).1 hxi hyi
  linarith [hPQ x hxP y hyQ, (hD i).2]

/-- Two adjacent links of diameter less than `ε` cannot meet two sets `2ε` apart. -/
theorem not_meets_adjacent {n : ℕ} {D : Chain X n} {ε : ℝ} (hD : IsEpsChain D ε) {P Q : Set X}
    (hPQ : ∀ x ∈ P, ∀ y ∈ Q, 2 * ε ≤ dist x y) (i j : Fin n)
    (hij : ((i : ℤ) - j).natAbs ≤ 1) :
    ¬ ((D.link i ∩ P).Nonempty ∧ (D.link j ∩ Q).Nonempty) := by
  rintro ⟨⟨x, hxi, hxP⟩, ⟨y, hyj, hyQ⟩⟩
  obtain ⟨z, hzi, hzj⟩ := (D.adjacent i j).2 hij
  have h1 := dist_le_diam_of_mem (hD i).1 hxi hzi
  have h2 := dist_le_diam_of_mem (hD j).1 hzj hyj
  have := dist_triangle x z y
  linarith [hPQ x hxP y hyQ, (hD i).2, (hD j).2]

/-- **The core of Theorem 2.** Let `D` be an `ε`-chain covering `X`, `C₁`, `C₂`, `C₃` preconnected
sets covering `X` with `A₁ ⊆ C₁`, `A₃ ⊆ C₂`, such that no link meets both `C₁` and `C₂`, no two
adjacent links meet `C₁` and `C₂` respectively, and no link meets both `C₃` and `A₁` or both `C₃`
and `A₃`. If links `i < k` meet `A₁` and `A₃`, then every link `j` meeting `C₃` lies strictly
between them. -/
theorem order_core {n : ℕ} (D : Chain X n) (hcov : univ ⊆ D.union) {A₁ A₃ C₁ C₂ C₃ : Set X}
    (hC₁ : IsPreconnected C₁) (hC₂ : IsPreconnected C₂) (hC₃ : IsPreconnected C₃)
    (hA₁ : A₁ ⊆ C₁) (hA₃ : A₃ ⊆ C₂) (hC : ∀ x, x ∈ C₁ ∨ x ∈ C₂ ∨ x ∈ C₃)
    (h12 : ∀ l l' : Fin n, ((l : ℤ) - l').natAbs ≤ 1 →
      ¬ ((D.link l ∩ C₁).Nonempty ∧ (D.link l' ∩ C₂).Nonempty))
    (h13 : ∀ l : Fin n, ¬ ((D.link l ∩ A₁).Nonempty ∧ (D.link l ∩ C₃).Nonempty))
    (h33 : ∀ l : Fin n, ¬ ((D.link l ∩ C₃).Nonempty ∧ (D.link l ∩ A₃).Nonempty))
    {i j k : Fin n} (hik : i < k) (hi : (D.link i ∩ A₁).Nonempty)
    (hj : (D.link j ∩ C₃).Nonempty) (hk : (D.link k ∩ A₃).Nonempty) : i < j ∧ j < k := by
  have hsub : ∀ C : Set X, C ⊆ D.union := fun C => (subset_univ C).trans hcov
  have hi1 : (C₁ ∩ D.link i).Nonempty := by
    obtain ⟨x, hx, hxA⟩ := hi; exact ⟨x, hA₁ hxA, hx⟩
  have hk2 : (C₂ ∩ D.link k).Nonempty := by
    obtain ⟨x, hx, hxA⟩ := hk; exact ⟨x, hA₃ hxA, hx⟩
  obtain ⟨α, β, -, hαβ⟩ := exists_trim D hC₁ (by obtain ⟨x, hx, -⟩ := hi1; exact ⟨x, hx⟩) (hsub C₁)
  obtain ⟨γ, δ, -, hγδ⟩ := exists_trim D hC₂ (by obtain ⟨x, hx, -⟩ := hk2; exact ⟨x, hx⟩) (hsub C₂)
  have hiαβ := (hαβ i).1 hi1
  have hkγδ := (hγδ k).1 hk2
  have hβC : (C₁ ∩ D.link β).Nonempty := (hαβ β).2 ⟨by have := hiαβ.1; omega, le_refl _⟩
  have hγC : (C₂ ∩ D.link γ).Nonempty := (hγδ γ).2 ⟨le_refl _, by have := hkγδ.2; omega⟩
  have hswap : ∀ {l : Fin n} {S : Set X}, (S ∩ D.link l).Nonempty → (D.link l ∩ S).Nonempty :=
    fun h => by rwa [inter_comm]
  -- the gap between the two blocks
  have hgap : (β : ℕ) + 1 < γ := by
    by_contra hcon
    push_neg at hcon
    by_cases h1 : (γ : ℕ) + 1 < α
    · -- then `α` lies in `[γ, δ]`
      have hαC2 : (C₂ ∩ D.link α).Nonempty :=
        (hγδ α).2 ⟨by omega, by have := hiαβ.1; have := hkγδ.2; rw [Fin.lt_def] at hik; omega⟩
      have hαC1 : (C₁ ∩ D.link α).Nonempty := (hαβ α).2 ⟨le_refl _, by have := hiαβ.2; omega⟩
      exact h12 α α (by simp) ⟨hswap hαC1, hswap hαC2⟩
    · push_neg at h1
      by_cases h3 : (γ : ℕ) ≤ β
      · by_cases h2 : (α : ℕ) ≤ γ
        · exact h12 γ γ (by simp) ⟨hswap ((hαβ γ).2 ⟨h2, h3⟩), hswap hγC⟩
        · push_neg at h2
          exact h12 α γ (by omega) ⟨hswap ((hαβ α).2 ⟨le_refl _, by have := hiαβ.2; omega⟩),
            hswap hγC⟩
      · exact h12 β γ (by omega) ⟨hswap hβC, hswap hγC⟩
  have htn : (β : ℕ) + 1 < n := by have := γ.isLt; omega
  set t : Fin n := ⟨β + 1, htn⟩ with ht
  have htC1 : ¬ (C₁ ∩ D.link t).Nonempty := fun h => by
    have := (hαβ t).1 h; simp [ht] at this
  have htC2 : ¬ (C₂ ∩ D.link t).Nonempty := fun h => by
    have := (hγδ t).1 h; simp [ht] at this; omega
  have htC3 : (C₃ ∩ D.link t).Nonempty := by
    obtain ⟨z, hz⟩ := D.link_nonempty t
    rcases hC z with h | h | h
    · exact absurd ⟨z, h, hz⟩ htC1
    · exact absurd ⟨z, h, hz⟩ htC2
    · exact ⟨z, h, hz⟩
  have hjC : (C₃ ∩ D.link j).Nonempty := by rwa [inter_comm] at hj
  have hit : (i : ℕ) < t := by simp [ht]; have := hiαβ.2; omega
  have htk : (t : ℕ) < k := by simp [ht]; have := hkγδ.1; omega
  constructor
  · by_contra hji
    push_neg at hji
    have := meets_between D hC₃ (hsub C₃) hjC htC3 i (by
      rw [Fin.le_def] at hji; omega) (by rw [Fin.le_def] at hji; omega)
    exact h13 i ⟨hi, hswap this⟩
  · by_contra hkj
    push_neg at hkj
    have := meets_between D hC₃ (hsub C₃) hjC htC3 k (by
      rw [Fin.le_def] at hkj; omega) (by rw [Fin.le_def] at hkj; omega)
    exact h33 k ⟨hswap this, hk⟩

end HPC.BJ59
