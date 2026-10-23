import HPC.Fold.Theorem7

/-!
# Counterexamples to Theorem 8 as stated

Batch 82.

* `theorem8_skeleton_false`: the skeleton's form of Theorem 8 (both chains follow `bingPattern m`)
  fails for the reversed chain in a three-link chain of intervals of `ℝ`.
* `not_theorem8_literal`: Bing's Theorem 8 as printed. In a finite (discrete) subspace of `ℕ`,
  two chains `D₁`, `D₂` with `z 3 = 6` links (the minimum, `theorem7_minimal`) are crooked in a
  four-link chain `E`, have their end links in the end links of `E`, and follow `bingPattern 4`
  in `E` in the same direction; yet the unions of corresponding links do not form a chain (the
  second and fourth unions meet), and pairing them in opposite directions gives unions that do
  not refine `E`, so no chain of unions is crooked in `E`.
-/

namespace HPC.Fold

open HPC.Chain

section Skeleton

variable {X : Type*} [MetricSpace X]

/-- In a three-link chain every chain refining it is crooked in it (there are no two links of
`D` more than two apart). -/
theorem isCrookedIn'_three {p : ℕ} {F : Chain X p} {D : Chain X 3} (h : F.Refines D) :
    F.IsCrookedIn' D :=
  ⟨h, fun hh k hk => by have := k.isLt; omega⟩

/-- The reversal of a three-link chain, viewed as a chain with `z 2 = 3` links. -/
def revThree (D : Chain X 3) : Chain X (z (3 - 1)) := D.reverse

theorem revThree_link (D : Chain X 3) (i : Fin 3) : (revThree D).link i = D.link (Fin.rev i) :=
  rfl

theorem revThree_not_follows (D : Chain X 3) :
    ¬ (revThree D).FollowsPattern (bingPattern 3 (by omega)) D := by
  intro h
  have h0 := h ⟨0, by decide⟩
  have hv0 := bingPattern_val 3 (by omega) ⟨0, by decide⟩
  obtain ⟨x, hx⟩ := (revThree D).link_nonempty ⟨0, by decide⟩
  have := (D.adjacent_iff (Fin.rev ⟨0, by decide⟩) _).1 ⟨x, hx, h0 hx⟩
  simp only [Fin.val_rev] at this
  have h00 : bingF (3 - 1) ((⟨0, by decide⟩ : Fin (z (3 - 1))) : ℕ) = 0 := bingF_zero _
  omega

end Skeleton

/-- Three open intervals of `ℝ` forming a chain. -/
def D3 : Chain ℝ 3 where
  link := ![Set.Ioo 0 2, Set.Ioo 1 4, Set.Ioo 3 5]
  isOpen i := by fin_cases i <;> exact isOpen_Ioo
  adjacent := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [Set.Ioo_inter_Ioo, Set.nonempty_Ioo]

/-- **The skeleton's Theorem 8 is false.** Take `D` three intervals of `ℝ` and
`F₁ = F₂ = C = D` reversed: all hypotheses hold, but `F₁` does not follow `bingPattern 3`. -/
theorem theorem8_skeleton_false :
    ¬ ∀ (D : Chain ℝ 3) (F₁ F₂ : Chain ℝ (z (3 - 1))),
      F₁.IsCrookedIn' D → F₂.IsCrookedIn' D →
      (∃ t, F₁.link t ⊆ D.link ⟨0, by omega⟩) → (∃ t, F₁.link t ⊆ D.link ⟨3 - 1, by omega⟩) →
      (∃ t, F₂.link t ⊆ D.link ⟨0, by omega⟩) → (∃ t, F₂.link t ⊆ D.link ⟨3 - 1, by omega⟩) →
      ∀ C : Chain ℝ (z (3 - 1)), (∀ i, C.link i = F₁.link i ∪ F₂.link i) →
        F₁.FollowsPattern (bingPattern 3 (by omega)) D ∧
        F₂.FollowsPattern (bingPattern 3 (by omega)) D ∧ C.IsCrookedIn' D := by
  intro h
  have hcr : (revThree D3).IsCrookedIn' D3 :=
    isCrookedIn'_three (fun i => ⟨Fin.rev i, subset_rfl⟩)
  have hlo : ∃ t, (revThree D3).link t ⊆ D3.link ⟨0, by omega⟩ := ⟨⟨2, by decide⟩, subset_rfl⟩
  have hhi : ∃ t, (revThree D3).link t ⊆ D3.link ⟨3 - 1, by omega⟩ := ⟨⟨0, by decide⟩, subset_rfl⟩
  exact revThree_not_follows D3
    (h D3 _ _ hcr hcr hlo hhi hlo hhi (revThree D3) (fun i => (Set.union_self _).symm)).1

/-! ### Bing's literal statement -/

/-- The links of `E`: four finite sets of naturals. -/
def eL : Fin 4 → Finset ℕ := ![{0, 1, 10, 11}, {1, 2, 3, 4, 11, 12, 13, 14, 20},
  {2, 3, 4, 5, 12, 13, 14, 15}, {5, 6, 15, 16}]

/-- The links of `D₁`. -/
def aL : Fin 6 → Finset ℕ := ![{0, 1}, {1, 2, 20}, {2, 3}, {3, 4}, {4, 5}, {5, 6}]

/-- The links of `D₂`. -/
def bL : Fin 6 → Finset ℕ := ![{10, 11}, {11, 12}, {12, 13}, {13, 14, 20}, {14, 15}, {15, 16}]

/-- A chain whose links are given finite sets of naturals (every set is open in `ℕ`), provided
the adjacency pattern is right. -/
def finChain {n : ℕ} (L : Fin n → Finset ℕ)
    (h : ∀ i j : Fin n, (L i ∩ L j).Nonempty ↔ ((i : ℤ) - (j : ℤ)).natAbs ≤ 1) : Chain ℕ n where
  link i := (L i : Set ℕ)
  isOpen _ := isOpen_discrete _
  adjacent i j := by rw [← Finset.coe_inter, Finset.coe_nonempty]; exact h i j

/-- `E`, four links. -/
def E4 : Chain ℕ 4 := finChain eL (by decide)

/-- `D₁`, six links. -/
def D1 : Chain ℕ 6 := finChain aL (by decide)

/-- `D₂`, six links. -/
def D2 : Chain ℕ 6 := finChain bL (by decide)

theorem z_three : z 3 = 6 := rfl

theorem bingPattern_four_val (i : Fin 6) :
    ((bingPattern 4 (by omega) i : ℕ) : ℤ) = ![0, 1, 2, 1, 2, 3] i := by
  rw [bingPattern_val]
  fin_cases i <;> decide

theorem finChain_subset {n p : ℕ} {L : Fin n → Finset ℕ} {M : Fin p → Finset ℕ} {hL hM}
    (i : Fin n) (j : Fin p) (h : L i ⊆ M j) : (finChain L hL).link i ⊆ (finChain M hM).link j :=
  Finset.coe_subset.2 h

/-- The pattern levels of `bingPattern 4` with the right indices. -/
theorem bingPattern_four (i : Fin 6) :
    bingPattern 4 (by omega) i = (![0, 1, 2, 1, 2, 3] : Fin 6 → Fin 4) i := by
  apply Fin.ext
  have := bingPattern_four_val i
  fin_cases i <;> simp at this ⊢ <;> omega

theorem D1_follows : D1.FollowsPattern (bingPattern 4 (by omega)) E4 := by
  intro i
  rw [bingPattern_four]
  exact finChain_subset _ _ (by fin_cases i <;> decide)

theorem D2_follows : D2.FollowsPattern (bingPattern 4 (by omega)) E4 := by
  intro i
  rw [bingPattern_four]
  exact finChain_subset _ _ (by fin_cases i <;> decide)

/-- The two links of `E` more than two apart are the end links; a link of a chain following
`[0,1,2,1,2,3]` meeting `E₀` has index `0` or `1`, one meeting `E₃` has index `4` or `5`. -/
theorem crooked_of_follows {D : Chain ℕ 6} (hf : D.FollowsPattern (bingPattern 4 (by omega)) E4)
    (hl : ∀ i, (D.link i ∩ E4.link 0).Nonempty → i.val ≤ 1)
    (hh : ∀ i, (D.link i ∩ E4.link 3).Nonempty → 4 ≤ i.val) : D.IsCrookedIn' E4 := by
  refine ⟨fun i => ⟨_, hf i⟩, fun h k hk i j hi hj => ?_⟩
  have hh0 : h = 0 := Fin.ext (by have := k.isLt; simp; omega)
  have hk3 : k = 3 := Fin.ext (by have := k.isLt; simp; omega)
  subst hh0 hk3
  have h1 := hl i hi
  have h2 := hh j hj
  refine ⟨2, 3, Or.inl ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [Fin.lt_def]; simp; omega
  · decide
  · rw [Fin.lt_def]; simp; omega
  · have := hf 2; rw [bingPattern_four] at this; exact this
  · have := hf 3; rw [bingPattern_four] at this; exact this

theorem D1_crooked : D1.IsCrookedIn' E4 := by
  refine crooked_of_follows D1_follows (fun i hi => ?_) (fun i hi => ?_) <;>
  · simp only [D1, E4, finChain, ← Finset.coe_inter, Finset.coe_nonempty] at hi
    revert hi; revert i; decide

theorem D2_crooked : D2.IsCrookedIn' E4 := by
  refine crooked_of_follows D2_follows (fun i hi => ?_) (fun i hi => ?_) <;>
  · simp only [D2, E4, finChain, ← Finset.coe_inter, Finset.coe_nonempty] at hi
    revert hi; revert i; decide

/-- **Bing's Theorem 8 as printed fails.** `D₁`, `D₂` are crooked in `E`, have `z 3 = 6` links
(the fewest possible for a chain crooked in `E` with links in both end links,
`theorem7_minimal`), have their first links in `E₀` and last links in `E₃`, and follow
`bingPattern 4` in `E`; but the unions of corresponding links form no chain, and the unions of
oppositely corresponding links form no chain crooked in (indeed refining) `E`. -/
theorem not_theorem8_literal :
    z 3 = 6 ∧ ∃ (E : Chain ℕ 4) (D₁ D₂ : Chain ℕ 6),
      D₁.IsCrookedIn' E ∧ D₂.IsCrookedIn' E ∧
      D₁.link 0 ⊆ E.link 0 ∧ D₁.link 5 ⊆ E.link 3 ∧ D₂.link 0 ⊆ E.link 0 ∧ D₂.link 5 ⊆ E.link 3 ∧
      D₁.FollowsPattern (bingPattern 4 (by omega)) E ∧
      D₂.FollowsPattern (bingPattern 4 (by omega)) E ∧
      (¬ ∃ C : Chain ℕ 6, ∀ i, C.link i = D₁.link i ∪ D₂.link i) ∧
      (∀ C : Chain ℕ 6, (∀ i, C.link i = D₁.link i ∪ D₂.link (Fin.rev i)) →
        ¬ C.Refines E) := by
  refine ⟨rfl, E4, D1, D2, D1_crooked, D2_crooked, finChain_subset _ _ (by decide),
    finChain_subset _ _ (by decide), finChain_subset _ _ (by decide),
    finChain_subset _ _ (by decide), D1_follows, D2_follows, ?_, ?_⟩
  · rintro ⟨C, hC⟩
    have h20 : (20 : ℕ) ∈ C.link 1 ∩ C.link 3 := by
      rw [hC, hC]
      simp [D1, D2, finChain, aL, bL]
    have := (C.adjacent_iff 1 3).1 ⟨20, h20⟩
    simp at this
  · intro C hC hr
    obtain ⟨j, hj⟩ := hr 0
    rw [hC] at hj
    have h0 : (0 : ℕ) ∈ E4.link j := hj (Or.inl (by simp [D1, finChain, aL]))
    have h16 : (16 : ℕ) ∈ E4.link j := hj (Or.inr (by simp [D2, finChain, bL, Fin.rev]))
    simp only [E4, finChain, Finset.mem_coe] at h0 h16
    clear hj
    revert h0 h16; revert j; decide

end HPC.Fold
