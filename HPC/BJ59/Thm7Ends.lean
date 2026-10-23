import HPC.BJ59.Thm7

/-!
# Batch 199, library: Bing–Jones Theorem 7, second sentence, for `n ≥ 3` (commission 199, §6)

In the compact pseudo-arc `S`, given compact nonempty `A ⊆ T₀`, `B ⊆ T_{n−1}`:
* `collar_data`: a radius `ρ` with `{infDist · A ≤ 3ρ} ⊆ T₀` and a point `w ∈ T₀ ∩ T₁` with
  `infDist w A > 3ρ` (`T₀ ∩ T₁ ⊄ A`, or else `T₀` would be clopen);
* `exists_collar_chain`: a chain `M` of `n + 4` links refining `T` by
  `ψ = (0, 0, 0, 1, 2, …, n − 2, n − 1, n − 1, n − 1)`, in which `A` meets only the first link and
  `B` only the last. The collars `{infDist · A < 2ρ}`, `{ρ < infDist · A < 3ρ}`,
  `T₀ ∩ {infDist · A > 2ρ}`, `T₁ ∩ {infDist · A > 3ρ}` replace `T₀`, `T₁` (Bing–Jones's
  `U₀, U₁, U₂`, p. 177, built differently; this works for every `n ≥ 3`);
* the walk of `Thm7Fold` with two more copies of `r` in front and of `s` at the end
  (Bing–Jones's `y′`, `z′`), `bufIdx`, and the pattern `bufPat` in the collar chain; the rest
  (`bj7_ends_compact`, `bj_theorem7_ends'`) is in `Thm7Ends2.lean`.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane

variable {S : Type*} [MetricSpace S]

/-- The links of a chain, indexed by `ℕ` (empty beyond the length). -/
def _root_.HPC.Chain.linkN {n : ℕ} (T : Chain S n) (j : ℕ) : Set S :=
  if h : j < n then T.link ⟨j, h⟩ else ∅

theorem _root_.HPC.Chain.linkN_of_lt {n : ℕ} (T : Chain S n) {j : ℕ} (h : j < n) :
    T.linkN j = T.link ⟨j, h⟩ := dif_pos h

theorem _root_.HPC.Chain.linkN_disj {n : ℕ} (T : Chain S n) {i j : ℕ} (hij : i + 2 ≤ j) {x : S}
    (hi : x ∈ T.linkN i) (hj : x ∈ T.linkN j) : False := by
  unfold HPC.Chain.linkN at hi hj
  split_ifs at hi hj with h1 h2
  · have := (T.adjacent ⟨i, h1⟩ ⟨j, h2⟩).1 ⟨x, hi, hj⟩
    simp only at this
    omega
  all_goals simp_all

theorem _root_.HPC.Chain.isOpen_linkN {n : ℕ} (T : Chain S n) (j : ℕ) : IsOpen (T.linkN j) := by
  unfold HPC.Chain.linkN; split_ifs; exacts [T.isOpen _, isOpen_empty]

/-- **Collar data at the first link.** -/
theorem collar_data [ConnectedSpace S] {n : ℕ} (hn : 3 ≤ n) (T : Chain S n)
    (hT : univ ⊆ T.union) {A : Set S} (hAc : IsCompact A) (hAne : A.Nonempty)
    (hA : A ⊆ T.linkN 0) :
    ∃ ρ > 0, (∀ x, infDist x A ≤ 3 * ρ → x ∈ T.linkN 0) ∧
      ∃ w ∈ T.linkN 0 ∩ T.linkN 1, 3 * ρ < infDist w A := by
  -- a point of `T₀ ∩ T₁` outside `A`
  have hex : ((T.linkN 0 ∩ T.linkN 1) \ A).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, diff_eq_empty] at hne
    -- then `T₀` is clopen
    have hcl : closure (T.linkN 0) ⊆ T.linkN 0 := by
      intro b hb
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hT (mem_univ b))
      have hjN : b ∈ T.linkN j := by rwa [T.linkN_of_lt j.2]
      rcases (by omega : j.val = 0 ∨ j.val = 1 ∨ 2 ≤ j.val) with h | h | h
      · rwa [h] at hjN
      · rw [h] at hjN
        have := (T.isOpen_linkN 1).inter_closure ⟨hjN, hb⟩
        rw [inter_comm] at this
        exact hA ((closure_mono hne).trans hAc.isClosed.closure_subset this)
      · exfalso
        have hopen : IsOpen (T.linkN j) := T.isOpen_linkN j
        obtain ⟨y, hyj, hy0⟩ := mem_closure_iff.1 hb _ hopen hjN
        exact T.linkN_disj (by omega : 0 + 2 ≤ j.val) hy0 hyj
    have hclopen : IsClopen (T.linkN 0) :=
      ⟨closure_subset_iff_isClosed.1 hcl, T.isOpen_linkN 0⟩
    rcases isClopen_iff.1 hclopen with he | hu
    · obtain ⟨a, ha⟩ := hAne
      exact (he ▸ hA ha : a ∈ (∅ : Set S))
    · obtain ⟨y, hy⟩ := T.link_nonempty ⟨2, by omega⟩
      exact T.linkN_disj (by omega : 0 + 2 ≤ 2) (hu ▸ mem_univ y)
        (by rwa [T.linkN_of_lt (by omega : 2 < n)])
  obtain ⟨w, ⟨hw0, hw1⟩, hwA⟩ := hex
  obtain ⟨κ, hκ, hκT⟩ := hAc.exists_thickening_subset_open (T.isOpen_linkN 0) hA
  have hα : 0 < infDist w A := (hAc.isClosed.notMem_iff_infDist_pos hAne).1 hwA
  refine ⟨min (κ / 4) (infDist w A / 4), lt_min (by linarith) (by linarith), fun x hx => ?_,
    w, ⟨hw0, hw1⟩, ?_⟩
  · apply hκT
    rw [mem_thickening_iff_infDist_lt hAne]
    have := min_le_left (κ / 4) (infDist w A / 4)
    linarith
  · have := min_le_right (κ / 4) (infDist w A / 4)
    linarith

theorem _root_.HPC.Chain.linkN_reverse {n : ℕ} (T : Chain S n) {j : ℕ} (hj : j < n) :
    T.reverse.linkN j = T.linkN (n - 1 - j) := by
  rw [T.reverse.linkN_of_lt hj, T.linkN_of_lt (by omega), Chain.reverse_link]
  congr 1
  ext
  simp only [Fin.val_rev]
  omega

/-- The refinement map of the collar chain. -/
def collarψ (n l : ℕ) : ℕ := if l ≤ 2 then 0 else if l ≤ n then l - 2 else n - 1

/-- **The collar chain.** -/
theorem exists_collar_chain [ConnectedSpace S] {n : ℕ} (hn : 3 ≤ n) (T : Chain S n)
    (hT : univ ⊆ T.union) {A B : Set S} (hAc : IsCompact A) (hAne : A.Nonempty)
    (hA : A ⊆ T.linkN 0) (hBc : IsCompact B) (hBne : B.Nonempty) (hB : B ⊆ T.linkN (n - 1)) :
    ∃ M : Chain S (n + 4), univ ⊆ M.union ∧
      (∀ l : Fin (n + 4), M.link l ⊆ T.linkN (collarψ n l)) ∧
      (∀ a ∈ A, ∀ l : Fin (n + 4), a ∈ M.link l → l.val = 0) ∧
      (∀ b ∈ B, ∀ l : Fin (n + 4), b ∈ M.link l → l.val = n + 3) := by
  classical
  -- collar data at both ends
  obtain ⟨ρ, hρ, FA, wA, ⟨hwA0, hwA1⟩, hwAf⟩ := collar_data hn T hT hAc hAne hA
  have hTr : univ ⊆ T.reverse.union := fun x _ => by
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hT (mem_univ x))
    exact mem_iUnion.2 ⟨Fin.rev j, by rw [Chain.reverse_link, Fin.rev_rev]; exact hj⟩
  have hr0 : T.reverse.linkN 0 = T.linkN (n - 1) := by
    rw [T.linkN_reverse (by omega)]; rfl
  have hr1 : T.reverse.linkN 1 = T.linkN (n - 2) := by
    rw [T.linkN_reverse (by omega)]; congr 1
  obtain ⟨σ, hσ, FB, wB, ⟨hwB0, hwB1⟩, hwBf⟩ := collar_data hn T.reverse hTr hBc hBne (hr0 ▸ hB)
  rw [hr0] at FB hwB0
  rw [hr1] at hwB1
  set fA : S → ℝ := fun x => infDist x A
  set fB : S → ℝ := fun x => infDist x B
  have hfA : Continuous fA := continuous_infDist_pt A
  have hfB : Continuous fB := continuous_infDist_pt B
  have hdisj0 : ∀ x, x ∈ T.linkN 0 → x ∈ T.linkN (n - 1) → False := fun x h0 h1 =>
    T.linkN_disj (by omega : 0 + 2 ≤ n - 1) h0 h1
  -- the links, indexed by `ℕ`
  set ML : ℕ → Set S := fun l =>
    if l = 0 then {x | fA x < 2 * ρ}
    else if l = 1 then {x | ρ < fA x ∧ fA x < 3 * ρ}
    else if l = 2 then T.linkN 0 ∩ {x | 2 * ρ < fA x}
    else if l = n + 3 then {x | fB x < 2 * σ}
    else if l = n + 2 then {x | σ < fB x ∧ fB x < 3 * σ}
    else if l = n + 1 then T.linkN (n - 1) ∩ {x | 2 * σ < fB x}
    else T.linkN (l - 2) ∩ {x | (l = 3 → 3 * ρ < fA x) ∧ (l = n → 3 * σ < fB x)} with hML
  -- the links at the various indices
  have hML0 : ML 0 = {x | fA x < 2 * ρ} := by simp [hML]
  have hML1 : ML 1 = {x | ρ < fA x ∧ fA x < 3 * ρ} := by simp [hML]
  have hML2 : ML 2 = T.linkN 0 ∩ {x | 2 * ρ < fA x} := by simp [hML]
  have hMLn3 : ML (n + 3) = {x | fB x < 2 * σ} := by
    simp only [hML]; split_ifs <;> first | rfl | (exfalso; omega)
  have hMLn2 : ML (n + 2) = {x | σ < fB x ∧ fB x < 3 * σ} := by
    simp only [hML]; split_ifs <;> first | rfl | (exfalso; omega)
  have hMLn1 : ML (n + 1) = T.linkN (n - 1) ∩ {x | 2 * σ < fB x} := by
    simp only [hML]; split_ifs <;> first | rfl | (exfalso; omega)
  have hMLm : ∀ l, 3 ≤ l → l ≤ n → ML l = T.linkN (l - 2) ∩
      ({x | l = 3 → x ∈ {y | 3 * ρ < fA y}} ∩ {x | l = n → x ∈ {y | 3 * σ < fB y}}) := by
    intro l h3 hl
    simp only [hML]; split_ifs <;> first | rfl | (exfalso; omega)
  have hcases : ∀ l, l < n + 4 → l = 0 ∨ l = 1 ∨ l = 2 ∨ (3 ≤ l ∧ l ≤ n) ∨ l = n + 1 ∨
      l = n + 2 ∨ l = n + 3 := fun l hl => by omega
  have hψA : ∀ l, l ≤ 2 → collarψ n l = 0 := fun l hl => if_pos hl
  have hψm : ∀ l, 3 ≤ l → l ≤ n → collarψ n l = l - 2 := fun l h3 hl => by
    unfold collarψ; rw [if_neg (by omega), if_pos hl]
  have hψB : ∀ l, n < l → collarψ n l = n - 1 := fun l hl => by
    unfold collarψ; rw [if_neg (by omega), if_neg (by omega)]
  have isOpen_imp : ∀ (c : Prop) {U : Set S}, IsOpen U → IsOpen {x | c → x ∈ U} := by
    intro c U hU
    by_cases hc : c
    · simpa [hc] using hU
    · simp [hc]
  have hMLo : ∀ l, l < n + 4 → IsOpen (ML l) := by
    intro l hl
    rcases hcases l hl with rfl | rfl | rfl | ⟨h3, hl'⟩ | rfl | rfl | rfl
    · rw [hML0]; exact isOpen_lt hfA continuous_const
    · rw [hML1]; exact (isOpen_lt continuous_const hfA).inter (isOpen_lt hfA continuous_const)
    · rw [hML2]; exact (T.isOpen_linkN 0).inter (isOpen_lt continuous_const hfA)
    · rw [hMLm l h3 hl']
      exact (T.isOpen_linkN _).inter ((isOpen_imp _ (isOpen_lt continuous_const hfA)).inter
        (isOpen_imp _ (isOpen_lt continuous_const hfB)))
    · rw [hMLn1]; exact (T.isOpen_linkN _).inter (isOpen_lt continuous_const hfB)
    · rw [hMLn2]; exact (isOpen_lt continuous_const hfB).inter (isOpen_lt hfB continuous_const)
    · rw [hMLn3]; exact isOpen_lt hfB continuous_const
  -- membership in the old links
  have hsub : ∀ l x, l < n + 4 → x ∈ ML l → x ∈ T.linkN (collarψ n l) := by
    intro l x hl hx
    rcases hcases l hl with rfl | rfl | rfl | ⟨h3, hl'⟩ | rfl | rfl | rfl
    · rw [hψA 0 (by omega)]; rw [hML0] at hx; exact FA x (by have : fA x < 2 * ρ := hx; linarith)
    · rw [hψA 1 (by omega)]; rw [hML1] at hx; exact FA x hx.2.le
    · rw [hψA 2 (by omega)]; rw [hML2] at hx; exact hx.1
    · rw [hψm l h3 hl']; rw [hMLm l h3 hl'] at hx; exact hx.1
    · rw [hψB _ (by omega)]; rw [hMLn1] at hx; exact hx.1
    · rw [hψB _ (by omega)]; rw [hMLn2] at hx; exact FB x hx.2.le
    · rw [hψB _ (by omega)]; rw [hMLn3] at hx
      exact FB x (by have : fB x < 2 * σ := hx; linarith)
  -- nonadjacent links are disjoint
  have hdisj : ∀ l l' x, l + 2 ≤ l' → l' < n + 4 → x ∈ ML l → x ∈ ML l' → False := by
    intro l l' x hll' hl' hx hx'
    have hs := hsub l x (by omega) hx
    have hs' := hsub l' x hl' hx'
    by_cases hψ : collarψ n l + 2 ≤ collarψ n l'
    · exact T.linkN_disj hψ hs hs'
    have key : (l = 0 ∧ l' = 2) ∨ (l = 0 ∧ l' = 3) ∨ (l = 1 ∧ l' = 3) ∨ (l = n ∧ l' = n + 2) ∨
        (l = n ∧ l' = n + 3) ∨ (l = n + 1 ∧ l' = n + 3) := by
      unfold collarψ at hψ; split_ifs at hψ <;> omega
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hML0] at hx; rw [hML2] at hx'
      have h1 : fA x < 2 * ρ := hx; have h2 := hx'.2; simp only [mem_setOf_eq] at h2; linarith
    · rw [hML0] at hx; rw [hMLm 3 le_rfl hn] at hx'
      have h1 : fA x < 2 * ρ := hx; have h2 : 3 * ρ < fA x := hx'.2.1 rfl; linarith
    · rw [hML1] at hx; rw [hMLm 3 le_rfl hn] at hx'
      have h1 := hx.2; have h2 : 3 * ρ < fA x := hx'.2.1 rfl; linarith
    · rw [h1, hMLm n hn le_rfl] at hx; rw [h2, hMLn2] at hx'
      have h1 : 3 * σ < fB x := hx.2.2 rfl; have h2 := hx'.2; linarith
    · rw [h1, hMLm n hn le_rfl] at hx; rw [h2, hMLn3] at hx'
      have h1 : 3 * σ < fB x := hx.2.2 rfl; have h2 : fB x < 2 * σ := hx'; linarith
    · rw [h1, hMLn1] at hx; rw [h2, hMLn3] at hx'
      have h1 := hx.2; simp only [mem_setOf_eq] at h1; have h2 : fB x < 2 * σ := hx'; linarith
  -- the links cover
  have hcov : ∀ x, ∃ l, l < n + 4 ∧ x ∈ ML l := by
    intro x
    by_cases hA3 : fA x < 3 * ρ
    · by_cases hA2 : fA x < 2 * ρ
      · exact ⟨0, by omega, hML0 ▸ hA2⟩
      · exact ⟨1, by omega, hML1 ▸ ⟨by push_neg at hA2; linarith, hA3⟩⟩
    by_cases hB3 : fB x < 3 * σ
    · by_cases hB2 : fB x < 2 * σ
      · exact ⟨n + 3, by omega, hMLn3 ▸ hB2⟩
      · exact ⟨n + 2, by omega, hMLn2 ▸ ⟨by push_neg at hB2; linarith, hB3⟩⟩
    push_neg at hA3 hB3
    by_cases h0 : x ∈ T.linkN 0
    · exact ⟨2, by omega, hML2 ▸ ⟨h0, show 2 * ρ < fA x by linarith⟩⟩
    by_cases hl : x ∈ T.linkN (n - 1)
    · exact ⟨n + 1, by omega, hMLn1 ▸ ⟨hl, show 2 * σ < fB x by linarith⟩⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hT (mem_univ x))
    have hjN : x ∈ T.linkN j := by rwa [T.linkN_of_lt j.2]
    have hj0 : j.val ≠ 0 := fun h => h0 (h ▸ hjN)
    have hjl : j.val ≠ n - 1 := fun h => hl (h ▸ hjN)
    have hAx : 3 * ρ < fA x := lt_of_le_of_ne hA3 fun h => h0 (FA x h.symm.le)
    have hBx : 3 * σ < fB x := lt_of_le_of_ne hB3 fun h => hl (FB x h.symm.le)
    have := j.2
    refine ⟨j.val + 2, by omega, ?_⟩
    rw [hMLm (j.val + 2) (by omega) (by omega)]
    exact ⟨by simpa using hjN, fun _ => hAx, fun _ => hBx⟩
  -- every link is nonempty
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  have hfa : fA a = 0 := infDist_zero_of_mem ha
  have hfb : fB b = 0 := infDist_zero_of_mem hb
  have hwAB : 3 * σ < fB wA := lt_of_not_ge fun h => hdisj0 wA hwA0 (FB wA h)
  have hwBA : 3 * ρ < fA wB := lt_of_not_ge fun h => hdisj0 wB (FA wB h) hwB0
  have hne : ∀ l, l < n + 4 → (ML l).Nonempty := by
    intro l hl
    rcases hcases l hl with rfl | rfl | rfl | ⟨h3, hl'⟩ | rfl | rfl | rfl
    · exact ⟨a, hML0 ▸ (show fA a < 2 * ρ by rw [hfa]; linarith)⟩
    · obtain ⟨y, hy⟩ := intermediate_value_univ a wA hfA ⟨by rw [hfa]; linarith,
        (by linarith : 2 * ρ ≤ fA wA)⟩
      exact ⟨y, hML1 ▸ ⟨by rw [hy]; linarith, by rw [hy]; linarith⟩⟩
    · exact ⟨wA, hML2 ▸ ⟨hwA0, show 2 * ρ < fA wA by linarith⟩⟩
    · rw [hMLm l h3 hl']
      by_cases hl3 : l = 3
      · subst hl3
        exact ⟨wA, by simpa using hwA1, fun _ => hwAf, fun _ => hwAB⟩
      by_cases hln : l = n
      · subst hln
        exact ⟨wB, by simpa using hwB1, fun h => absurd h hl3, fun _ => hwBf⟩
      · obtain ⟨y, hy⟩ := T.link_nonempty ⟨l - 2, by omega⟩
        exact ⟨y, by rwa [T.linkN_of_lt (by omega)], fun h => absurd h hl3,
          fun h => absurd h hln⟩
    · exact ⟨wB, hMLn1 ▸ ⟨hwB0, show 2 * σ < fB wB by linarith⟩⟩
    · obtain ⟨y, hy⟩ := intermediate_value_univ b wB hfB ⟨by rw [hfb]; linarith,
        (by linarith : 2 * σ ≤ fB wB)⟩
      exact ⟨y, hMLn2 ▸ ⟨by rw [hy]; linarith, by rw [hy]; linarith⟩⟩
    · exact ⟨b, hMLn3 ▸ (show fB b < 2 * σ by rw [hfb]; linarith)⟩
  -- the chain
  set L : Fin (n + 4) → Set S := fun l => ML l.val
  have hLdisj : ∀ i j : Fin (n + 4), 1 < ((i : ℤ) - j).natAbs → L i ∩ L j = ∅ := by
    intro i j hij
    refine eq_empty_of_forall_notMem fun x ⟨hxi, hxj⟩ => ?_
    rcases (by omega : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) with h | h
    · exact hdisj _ _ x h j.2 hxi hxj
    · exact hdisj _ _ x h i.2 hxj hxi
  have hLcov : (univ : Set S) ⊆ ⋃ l, L l := fun x _ => by
    obtain ⟨l, hl, hx⟩ := hcov x
    exact mem_iUnion.2 ⟨⟨l, hl⟩, hx⟩
  have hLne : ∀ l : Fin (n + 4), (L l ∩ univ).Nonempty := fun l => by
    rw [inter_univ]; exact hne l l.2
  have hLo : ∀ l : Fin (n + 4), IsOpen (L l) := fun l => hMLo l l.2
  let M : Chain S (n + 4) :=
    { link := L
      isOpen := hLo
      adjacent := fun i j => by
        constructor
        · intro h
          by_contra h'
          push_neg at h'
          rw [hLdisj i j h'] at h
          exact not_nonempty_empty h
        · intro h
          rcases lt_trichotomy i.val j.val with hlt | heq | hgt
          · exact adjacent_meet_of_cover isPreconnected_univ L hLo hLcov hLne hLdisj i j
              (by omega)
          · have : i = j := Fin.ext heq
            subst this
            obtain ⟨x, hx, -⟩ := hLne i
            exact ⟨x, hx, hx⟩
          · rw [inter_comm]
            exact adjacent_meet_of_cover isPreconnected_univ L hLo hLcov hLne hLdisj j i
              (by omega) }
  refine ⟨M, hLcov, fun l x hx => hsub l x l.2 hx, fun a' ha' l hl => ?_, fun b' hb' l hl => ?_⟩
  · have hfa' : fA a' = 0 := infDist_zero_of_mem ha'
    have hs := hsub l a' l.2 hl
    have hl' : a' ∈ ML l.val := hl
    rcases hcases l l.2 with h | h | h | ⟨h3, hl''⟩ | h | h | h
    · exact h
    · rw [h, hML1] at hl'; linarith [hl'.1]
    · rw [h, hML2] at hl'; have := hl'.2; simp only [mem_setOf_eq] at this; linarith
    · exfalso
      by_cases hl3 : l.val = 3
      · rw [hMLm _ h3 hl''] at hl'; have := hl'.2.1 hl3; simp only [mem_setOf_eq] at this
        linarith
      · rw [hψm _ h3 hl''] at hs
        exact T.linkN_disj (by omega : 0 + 2 ≤ l.val - 2) (hA ha') hs
    all_goals
      exfalso
      rw [hψB _ (by omega)] at hs
      exact hdisj0 a' (hA ha') hs
  · have hfb' : fB b' = 0 := infDist_zero_of_mem hb'
    have hs := hsub l b' l.2 hl
    have hl' : b' ∈ ML l.val := hl
    rcases hcases l l.2 with h | h | h | ⟨h3, hl''⟩ | h | h | h
    rotate_left 3
    · exfalso
      by_cases hln : l.val = n
      · rw [hMLm _ h3 hl''] at hl'; have := hl'.2.2 hln; simp only [mem_setOf_eq] at this
        linarith
      · rw [hψm _ h3 hl''] at hs
        exact T.linkN_disj (by omega : l.val - 2 + 2 ≤ n - 1) hs (hB hb')
    · exfalso; rw [h, hMLn1] at hl'; have := hl'.2; simp only [mem_setOf_eq] at this; linarith
    · exfalso; rw [h, hMLn2] at hl'; linarith [hl'.1]
    · exact h
    all_goals
      exfalso
      rw [hψA _ (by omega)] at hs
      exact hdisj0 b' hs (hB hb')

/-! ### The walk with buffers at both ends -/

/-- The walk `r, r, (r, r − 1, …, 1, 0, 1, …, m − 1, m − 2, …, s), s, s`. -/
def bufIdx (m r s : ℕ) (k : ℕ) : ℕ :=
  if k < 2 then r else if k < unfoldLen m r s + 2 then unfoldIdx m r (k - 2) else s

theorem bufIdx_lt {m r s : ℕ} (hr : r < m) (hs : s < m) (k : ℕ) : bufIdx m r s k < m := by
  unfold bufIdx; split_ifs
  · exact hr
  · exact unfoldIdx_lt hr _
  · exact hs

theorem bufIdx_step {m r s : ℕ} (hrs : r ≤ s) (hs : s < m) (k : ℕ) :
    ((bufIdx m r s k : ℤ) - bufIdx m r s (k + 1) ≤ 1) ∧
      ((bufIdx m r s (k + 1) : ℤ) - bufIdx m r s k ≤ 1) := by
  unfold bufIdx unfoldIdx unfoldLen
  split_ifs <;> omega

/-- The buffered pattern in the collar chain. -/
def bufPat (n m r s : ℕ) (H : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 1 else if k = unfoldLen m r s + 3 then n + 3
  else if k = unfoldLen m r s + 2 then n + 2 else H (bufIdx m r s k) + 2

end HPC.BJ59
