import HPC.Fold.Recon122General
import HPC.Fold.T9Ends

/-!
# Bing 1948, Theorem 3 in Bing's two-link form, for chains

Batch 123 (COMMISSION-batch123.md, item 1). The bridge from the model of batch 122 to chains,
moved out of `HPC/Fold/Recon122.lean` so that `HPC/Fold/Theorem4.lean` can import it:

* `bHyp_of_crooked`, `chain_of_bconcl`: the transfer between chains crooked (1948) in a chain and
  the model `BHyp`/`BConcl` of `HPC/Fold/Recon122Model.lean` (moved verbatim from `Recon122.lean`;
  the names are unchanged, `HPC.Fold.Recon122.*`);
* `Theorem3Block`, `theorem3Block_holds` (moved, names unchanged);
* `HPC.Fold.theorem3_bing`: **Bing's Theorem 3 as printed without the only-clause**, as a theorem
  about chains with explicit arguments (the unfolding of `Theorem3Block`);
* `HPC.Fold.theorem3_end_of_bing`: the statement of `HPC.Fold.theorem3_end` (three-link form), from
  `theorem3_bing`; `theorem3_end` (`HPC/Fold/Theorem4.lean`) is proved by it.

This file imports `Recon122General` and the chain library, not `Theorem4`.
-/

namespace HPC.Fold.Recon122

open HPC HPC.Chain

universe u

/-! ## Two facts about refinements (copies of `HPC.Fold.Recon121` lemmas, which sit above
`Theorem4` in the import graph) -/

section Facts

variable {X : Type*} [MetricSpace X] {n k : ℕ}

private theorem link_subset_of_between {E : Chain X n} {D : Chain X k} (h : E.Refines D)
    (u : Fin n) (j : Fin k) (h1 : h.minIdx u ≤ j) (h2 : j ≤ h.maxIdx u) :
    E.link u ⊆ D.link j := by
  have hw := subset_adjacent_of_subset h u (minIdx_subset h u) (maxIdx_subset h u)
  have h1' := Fin.le_def.mp h1
  have h2' := Fin.le_def.mp h2
  rcases (by omega : j.val = (h.minIdx u).val ∨ j.val = (h.maxIdx u).val) with e | e
  · rw [show j = h.minIdx u from Fin.ext e]; exact minIdx_subset h u
  · rw [show j = h.maxIdx u from Fin.ext e]; exact maxIdx_subset h u

private theorem meets_of_forced {E : Chain X n} {D : Chain X k} (h : E.Refines D) {t u : Fin n}
    (hu : ((u : ℤ) - (t : ℤ)).natAbs ≤ 1) (j : Fin k) (h1 : h.minIdx u ≤ j)
    (h2 : j ≤ h.maxIdx u) : (E.link t ∩ D.link j).Nonempty := by
  obtain ⟨z, hz1, hz2⟩ := (E.adjacent u t).mpr hu
  exact ⟨z, hz2, link_subset_of_between h u j h1 h2 hz1⟩

end Facts

/-! ## The transfer from chains to the model (moved from `Recon122.lean`) -/

section Transfer

variable {X : Type*} [MetricSpace X] {n k : ℕ}

/-- The least coarse link containing the fine link `t` (`0` beyond the chain). -/
noncomputable def chainRho {E : Chain X n} {D : Chain X k} (h : E.Refines D) (t : ℕ) : ℕ :=
  if ht : t < n then (h.minIdx ⟨t, ht⟩ : ℕ) else 0

/-- The greatest coarse link containing the fine link `t` (`0` beyond the chain). -/
noncomputable def chainSig {E : Chain X n} {D : Chain X k} (h : E.Refines D) (t : ℕ) : ℕ :=
  if ht : t < n then (h.maxIdx ⟨t, ht⟩ : ℕ) else 0

/-- The true meeting table of a chain `E` with a chain `D`. -/
def chainT (E : Chain X n) (D : Chain X k) (t j : ℕ) : Prop :=
  ∃ (ht : t < n) (hj : j < k), (E.link ⟨t, ht⟩ ∩ D.link ⟨j, hj⟩).Nonempty

/-- **Every chain crooked (1948) in a chain satisfies the hypotheses of the model**, with its
`(minIdx, maxIdx)` and its true meeting table. -/
theorem bHyp_of_crooked {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) :
    BHyp n k (chainRho hcr.1) (chainSig hcr.1) (chainT E D) := by
  have href := hcr.1
  have hρ : ∀ t (ht : t < n), chainRho hcr.1 t = (href.minIdx ⟨t, ht⟩ : ℕ) :=
    fun t ht => by simp [chainRho, ht]
  have hσ : ∀ t (ht : t < n), chainSig hcr.1 t = (href.maxIdx ⟨t, ht⟩ : ℕ) :=
    fun t ht => by simp [chainSig, ht]
  -- containment in a coarse link, in terms of `(ρ, σ)`
  have hsub : ∀ t (ht : t < n) j (hj : j < k), chainRho hcr.1 t ≤ j → j ≤ chainSig hcr.1 t →
      E.link ⟨t, ht⟩ ⊆ D.link ⟨j, hj⟩ := by
    intro t ht j hj h1 h2
    rw [hρ t ht] at h1; rw [hσ t ht] at h2
    exact link_subset_of_between href _ ⟨j, hj⟩ (Fin.le_def.mpr h1) (Fin.le_def.mpr h2)
  have hin : ∀ t (ht : t < n) j (hj : j < k), E.link ⟨t, ht⟩ ⊆ D.link ⟨j, hj⟩ →
      chainRho hcr.1 t ≤ j ∧ j ≤ chainSig hcr.1 t := by
    intro t ht j hj hs
    rw [hρ t ht, hσ t ht]
    exact ⟨Fin.le_def.mp (minIdx_le href _ hs), Fin.le_def.mp (le_maxIdx href _ hs)⟩
  -- a meeting puts the level within one of `ρ` and of `σ`
  have hmeet : ∀ t (ht : t < n) j (hj : j < k), (E.link ⟨t, ht⟩ ∩ D.link ⟨j, hj⟩).Nonempty →
      chainSig hcr.1 t ≤ j + 1 ∧ j ≤ chainRho hcr.1 t + 1 := by
    intro t ht j hj ⟨z, hz1, hz2⟩
    have a := (D.adjacent_iff (href.maxIdx ⟨t, ht⟩) ⟨j, hj⟩).mp ⟨z, maxIdx_subset href _ hz1, hz2⟩
    have b := (D.adjacent_iff (href.minIdx ⟨t, ht⟩) ⟨j, hj⟩).mp ⟨z, minIdx_subset href _ hz1, hz2⟩
    simp only at a b
    rw [hρ t ht, hσ t ht]; omega
  have hle : ∀ t, t < n → chainRho hcr.1 t ≤ chainSig hcr.1 t := by
    intro t ht
    rw [hρ t ht, hσ t ht]
    exact Fin.le_def.mp (minIdx_le href _ (maxIdx_subset href _))
  have hlt : ∀ t, t < n → chainSig hcr.1 t < k := by
    intro t ht; rw [hσ t ht]; exact (href.maxIdx _).isLt
  refine ⟨hle, fun t ht => ?_, hlt, fun t ht => ?_, fun t ht j h1 h2 => ?_,
    fun t ht j h1 h2 => ?_, fun t ht j h1 h2 => ?_, fun t ht j hj => ?_,
    fun s t hst ht a b ha hb hab => ?_, fun s t hst ht a b ha hb hab => ?_⟩
  · have := subset_adjacent_of_subset href ⟨t, ht⟩ (minIdx_subset href _) (maxIdx_subset href _)
    rw [hρ t ht, hσ t ht]; omega
  · obtain ⟨z, hz1, hz2⟩ := (E.adjacent ⟨t, by omega⟩ ⟨t + 1, ht⟩).mpr (by simp)
    have a := (D.adjacent_iff (href.maxIdx ⟨t, by omega⟩) (href.minIdx ⟨t + 1, ht⟩)).mp
      ⟨z, maxIdx_subset href _ hz1, minIdx_subset href _ hz2⟩
    have b := (D.adjacent_iff (href.maxIdx ⟨t + 1, ht⟩) (href.minIdx ⟨t, by omega⟩)).mp
      ⟨z, maxIdx_subset href _ hz2, minIdx_subset href _ hz1⟩
    rw [hρ t (by omega), hσ t (by omega), hρ (t + 1) ht, hσ (t + 1) ht]; omega
  · have hj : j < k := by have := hlt t ht; omega
    obtain ⟨z, hz⟩ := E.link_nonempty ⟨t, ht⟩
    exact ⟨ht, hj, z, hz, hsub t ht j hj h1 h2 hz⟩
  · have hj : j < k := by have := hlt (t + 1) ht; omega
    refine ⟨by omega, hj, ?_⟩
    refine meets_of_forced href (t := ⟨t, by omega⟩) (u := ⟨t + 1, ht⟩) (by simp) ⟨j, hj⟩ ?_ ?_
    · rw [hρ (t + 1) ht] at h1; exact Fin.le_def.mpr h1
    · rw [hσ (t + 1) ht] at h2; exact Fin.le_def.mpr h2
  · have hj : j < k := by have := hlt t (by omega); omega
    refine ⟨ht, hj, ?_⟩
    refine meets_of_forced href (t := ⟨t + 1, ht⟩) (u := ⟨t, by omega⟩) (by simp) ⟨j, hj⟩ ?_ ?_
    · rw [hρ t (by omega)] at h1; exact Fin.le_def.mpr h1
    · rw [hσ t (by omega)] at h2; exact Fin.le_def.mpr h2
  · obtain ⟨_, hj', hne⟩ := hj
    exact hmeet t ht j hj' hne
  · obtain ⟨_, ha', hsa⟩ := ha
    obtain ⟨_, hb', htb⟩ := hb
    obtain ⟨r, r', hbet, hr, hr'⟩ :=
      hcr.2 ⟨a, ha'⟩ ⟨b, hb'⟩ (by simp only; omega) ⟨s, by omega⟩ ⟨t, ht⟩ hsa htb
    have hbet' : s < r.val ∧ r.val < r'.val ∧ r'.val < t := by
      rcases hbet with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact ⟨h1, h2, h3⟩
      · exact absurd (lt_trans h3 (lt_trans h2 h1)) (by simp [Fin.lt_def]; omega)
    have c1 := hin r.val r.isLt (b - 1) (by omega) (by simpa using hr)
    have c2 := hin r'.val r'.isLt (a + 1) (by omega) (by simpa using hr')
    exact ⟨r.val, r'.val, hbet'.1, hbet'.2.1, hbet'.2.2, c1.1, c1.2, c2.1, c2.2⟩
  · obtain ⟨_, ha', hsa⟩ := ha
    obtain ⟨_, hb', htb⟩ := hb
    obtain ⟨r, r', hbet, hr, hr'⟩ :=
      hcr.2 ⟨b, hb'⟩ ⟨a, ha'⟩ (by simp only; omega) ⟨t, ht⟩ ⟨s, by omega⟩ htb hsa
    have hbet' : s < r'.val ∧ r'.val < r.val ∧ r.val < t := by
      rcases hbet with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact absurd (lt_trans h1 (lt_trans h2 h3)) (by simp [Fin.lt_def]; omega)
      · exact ⟨h3, h2, h1⟩
    have c1 := hin r'.val r'.isLt (b + 1) (by omega) (by simpa using hr')
    have c2 := hin r.val r.isLt (a - 1) (by omega) (by simpa using hr)
    exact ⟨r'.val, r.val, hbet'.1, hbet'.2.1, hbet'.2.2, c1.1, c1.2, c2.1, c2.2⟩

/-- **From the model back to the chain**: a solution of `BConcl` for the data of `E` gives a block
consolidation with `E.link i` in the first block, every block in two adjacent links of `D`, and
Bing's end clause read with the true meetings. -/
theorem chain_of_bconcl {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (hk : 0 < k)
    (i : Fin n) (hc : BConcl n k (chainRho hcr.1) (chainSig hcr.1) (chainT E D) i) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β i).val = 0 ∧
      (∀ v, ∃ j : ℕ, (E.ofBlocks β hβ).link v ⊆ D.unionRange j 2) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, hk⟩).Nonempty ∨ (E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty) →
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange 0 2 ∨
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange (k - 2) 2) := by
  have hB := bHyp_of_crooked hcr
  obtain ⟨b, hb0, ⟨hlip, hwid⟩, hend⟩ := hc
  have hn : 0 < n := by have := i.isLt; omega
  obtain ⟨tm, htm, hmax⟩ : ∃ tm, tm < n ∧ ∀ t, t < n → b t ≤ b tm := by
    obtain ⟨x, hx, hxm⟩ := Finset.exists_max_image (Finset.range n) b ⟨0, by simp [hn]⟩
    exact ⟨x, Finset.mem_range.mp hx, fun t ht => hxm t (Finset.mem_range.mpr ht)⟩
  have hlt : ∀ t, t < n → b t < b tm + 1 := fun t ht => Nat.lt_succ_of_le (hmax t ht)
  have hlip' : ∀ t, t + 1 < n → (b (t + 1) : ℤ) - b t ≤ 1 ∧ (b t : ℤ) - b (t + 1) ≤ 1 := by
    intro t ht; have := hlip t (Nat.zero_le _) (by omega); omega
  have hsurj : ∀ j, j < b tm + 1 → ∃ t, t < n ∧ b t = j := by
    intro j hj
    have hj' := hmax tm htm
    rcases le_total i.val tm with hle | hle
    · obtain ⟨t, h1, h2, h3⟩ := nat_ivt b i.val (tm - i.val)
        (fun t h1 h2 => hlip' t (by omega)) j
        (Or.inl ⟨by rw [hb0]; omega, by rw [show i.val + (tm - i.val) = tm by omega]; omega⟩)
      exact ⟨t, by omega, h3⟩
    · obtain ⟨t, h1, h2, h3⟩ := nat_ivt b tm (i.val - tm)
        (fun t h1 h2 => hlip' t (by omega)) j
        (Or.inr ⟨by rw [show tm + (i.val - tm) = i.val by omega, hb0]; omega, by omega⟩)
      exact ⟨t, by omega, h3⟩
  have hβ := isBlockMap_natBlock b hlt hlip' hsurj
  have hblock : ∀ (v : Fin (b tm + 1)) (S : Set X), (∀ t : Fin n, b t = v → E.link t ⊆ S) →
      (E.ofBlocks _ hβ).link v ⊆ S := by
    intro v S hS x hx
    rw [natBlock_link] at hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    exact hS t ht hxt
  have hρ : ∀ t : Fin n, chainRho hcr.1 t = (hcr.1.minIdx t : ℕ) := fun t => by simp [chainRho]
  have hσ : ∀ t : Fin n, chainSig hcr.1 t = (hcr.1.maxIdx t : ℕ) := fun t => by simp [chainSig]
  refine ⟨b tm + 1, natBlock b hlt, hβ, by simp [natBlock, hb0], fun v => ?_, fun t ht hm => ?_⟩
  · obtain ⟨j, hj⟩ := hwid v.val
    refine ⟨j, hblock v _ fun t htv => ?_⟩
    obtain ⟨h1, h2⟩ := hj t (Nat.zero_le _) (by omega) htv
    have hw := hB.wid t t.isLt
    have hl := hB.le t t.isLt
    have e1 := hρ t
    have e2 := hσ t
    rw [e1, e2] at hw hl
    rw [e2] at h1
    rw [e1] at h2
    by_cases hjr : j ≤ (hcr.1.minIdx t : ℕ)
    · exact (minIdx_subset hcr.1 t).trans (link_subset_unionRange D _ (by omega) (by omega))
    · exact (maxIdx_subset hcr.1 t).trans (link_subset_unionRange D _ (by omega) (by omega))
  · have hT : chainT E D t.val 0 ∨ chainT E D t.val (k - 1) := by
      rcases hm with hm | hm
      · exact Or.inl ⟨t.isLt, hk, hm⟩
      · exact Or.inr ⟨t.isLt, by omega, hm⟩
    rcases hend t.val t.isLt ht hT with hb | hb
    · left
      refine hblock _ _ fun t' ht' => ?_
      have := hb t'.val t'.isLt (by simpa [natBlock] using ht')
      rw [hρ t'] at this
      exact (minIdx_subset hcr.1 t').trans (link_subset_unionRange D _ (by omega) (by omega))
    · right
      refine hblock _ _ fun t' ht' => ?_
      have := hb t'.val t'.isLt (by simpa [natBlock] using ht')
      rw [hσ t'] at this
      have := (hcr.1.maxIdx t').isLt
      exact (maxIdx_subset hcr.1 t').trans (link_subset_unionRange D _ (by omega) (by omega))

end Transfer

/-! ## Theorem 3 as printed, without the only-clause -/

/-- **Bing 1948, Theorem 3 as printed, without the clause "`d_i` is contained in only the first
link of `F`"**: `Theorem3LiteralOr` with its second conjunct (the only-clause) removed. -/
def Theorem3Block : Prop :=
  ∀ (X : Type u) [MetricSpace X] (n k : ℕ) (hk : 0 < k) (E : Chain X n) (D : Chain X k),
    E.IsCrookedIn' D → ∀ i : Fin n,
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β i).val = 0 ∧
      (∀ v, ∃ j : ℕ, (E.ofBlocks β hβ).link v ⊆ D.unionRange j 2) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, hk⟩).Nonempty ∨ (E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty) →
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange 0 2 ∨
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange (k - 2) 2)

end HPC.Fold.Recon122

namespace HPC.Fold

open HPC HPC.Chain HPC.Fold.Recon122

universe u

/-- **Bing 1948, Theorem 3** (p. 731), in Bing's two-link form with his end clause ("or"
reading), without the clause "`d_i` is contained in only the first link of `F`" (see
`HPC/Fold/Theorem4Two.lean`, `OnlyIn`, and REPORT-batch123, item 3). If `E` (Bing's `D`) is crooked
(1948 sense) in the chain `D` (Bing's `E`) and `i` is a link of `E`, then `E` has a block
consolidation in which `E.link i` lies in the first block, every block lies in the sum of two
adjacent links of `D`, and the block of an end link of `E` meeting the first or the last link of
`D` lies in the sum of the first two or of the last two links of `D`. Proved in batch 122 in the
model (`HPC.Fold.Recon122.bing_main`, Bing's induction with three repairs) and transferred here. -/
theorem theorem3_bing {X : Type*} [MetricSpace X] {n k : ℕ} (hk : 0 < k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β i).val = 0 ∧
      (∀ v, ∃ j : ℕ, (E.ofBlocks β hβ).link v ⊆ D.unionRange j 2) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, hk⟩).Nonempty ∨ (E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty) →
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange 0 2 ∨
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange (k - 2) 2) :=
  chain_of_bconcl hcr hk i (bing_main k n _ _ _ i (bHyp_of_crooked hcr) i.isLt)

/-- **Bing's Theorem 3 as printed holds, apart from the only-clause**, for every chain crooked
(1948) in a chain, in every metric space (`theorem3_bing`, as a `Prop`). -/
theorem Recon122.theorem3Block_holds : Theorem3Block.{u} :=
  fun _ _ _ _ hk _ _ hcr i => theorem3_bing hk hcr i

/-- Two adjacent links lie in three. -/
private theorem unionRange_two_three {X : Type*} [MetricSpace X] {k : ℕ} (D : Chain X k)
    {j j' : ℕ} (h1 : j' ≤ j) (h2 : j + 2 ≤ j' + 3) : D.unionRange j 2 ⊆ D.unionRange j' 3 := by
  intro x hx
  rw [mem_unionRange] at hx ⊢
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := hx
  exact ⟨a, by omega, by omega, ha3, ha4⟩

/-- **The statement of `HPC.Fold.theorem3_end`** (three-link form, end clause read respectively),
from `theorem3_bing`. With at least four coarse links Bing's "or" clause gives the respective one,
because a block meeting the first link of `D` does not lie in the last two; with three coarse links
the first three and the last three links of `D` are all of `D`. (The hypothesis `0 < n` of
`theorem3_end` is not needed.) -/
theorem theorem3_end_of_bing {X : Type*} [MetricSpace X] {n k : ℕ} (hk : 3 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧
      (∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange 0 3) ∧
        ((E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange (k - 3) 3)) := by
  obtain ⟨q, β, hβ, h0, hmain, hend⟩ := theorem3_bing (by omega : 0 < k) hcr i
  have hall : k = 3 → ∀ (S : Set X), S ⊆ E.union → S ⊆ D.unionRange 0 3 := by
    intro hk3 S hS x hx
    obtain ⟨t', ht'⟩ := Set.mem_iUnion.mp (hS hx)
    obtain ⟨j, hj⟩ := hcr.1 t'
    exact link_subset_unionRange D j (by omega) (by have := j.isLt; omega) (hj ht')
  have hsubU : ∀ v, (E.ofBlocks β hβ).link v ⊆ E.union := by
    intro v x hx
    simp only [ofBlocks_link, Set.mem_iUnion] at hx
    obtain ⟨t', -, hx'⟩ := hx
    exact Set.mem_iUnion.mpr ⟨t', hx'⟩
  refine ⟨q, β, hβ, h0, fun v => ?_, fun t ht => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · obtain ⟨j, hj⟩ := hmain v
    exact ⟨j, hj.trans (unionRange_two_three D le_rfl (by omega))⟩
  · by_cases hk3 : k = 3
    · exact hall hk3 _ (hsubU _)
    · rcases hend t ht (Or.inl hm) with h1 | h1
      · exact h1.trans (unionRange_two_three D le_rfl (by omega))
      · exfalso
        obtain ⟨z, hz1, hz2⟩ := hm
        have hzb : z ∈ (E.ofBlocks β hβ).link (β t) := by
          rw [ofBlocks_link]; exact Set.mem_biUnion (show β t = β t from rfl) hz1
        obtain ⟨a, ha1, ha2, ha3, ha4⟩ := mem_unionRange.mp (h1 hzb)
        have := (D.adjacent_iff ⟨a, ha3⟩ ⟨0, by omega⟩).mp ⟨z, ha4, hz2⟩
        simp only at this; omega
  · by_cases hk3 : k = 3
    · subst hk3; exact hall rfl _ (hsubU _)
    · rcases hend t ht (Or.inr hm) with h1 | h1
      · exfalso
        obtain ⟨z, hz1, hz2⟩ := hm
        have hzb : z ∈ (E.ofBlocks β hβ).link (β t) := by
          rw [ofBlocks_link]; exact Set.mem_biUnion (show β t = β t from rfl) hz1
        obtain ⟨a, ha1, ha2, ha3, ha4⟩ := mem_unionRange.mp (h1 hzb)
        have := (D.adjacent_iff ⟨a, ha3⟩ ⟨k - 1, by omega⟩).mp ⟨z, ha4, hz2⟩
        simp only at this; omega
      · exact h1.trans (unionRange_two_three D (by omega) (by omega))

end HPC.Fold
