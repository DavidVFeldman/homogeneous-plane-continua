import HPC.Fold.Theorem4Two
import HPC.Fold.Theorem3PairInduction

/-!
# Batch 124, item 1: the pair form of Theorem 3 and Bing's Theorem 3 as printed

COMMISSION-batch124.md, Q1–Q3.

* `HPC.Fold.theorem3_pair`: **the pair form of Theorem 3** for chains — two equal or adjacent links
  of `E` lying in a common link of `D` have a consolidation as in `theorem3_bing` with both in the
  first block. Proved in the model (`HPC.Fold.Recon122.pair_main`, files `Theorem3PairModel.lean`,
  `Theorem3PairInduction.lean`) and transferred here (`chain_of_bconclZ`). `theorem3Pair_holds`:
  the `Prop` `Theorem3Pair` of batch 123 holds.
* `onlyIn_of_no_common` (Q2): the only-clause holds, for **every** consolidation whose blocks lie in
  two adjacent links of `D`, at a link of `E` sharing a link of `D` with neither neighbour. (In
  particular the case "levels `a, a + 1, a + 2` in a row" of the commission is harmless: the two
  neighbours cannot lie in one block.)
* `HPC.Fold.theorem3_literal`: **Bing's Theorem 3 as printed, every clause** (Q3): by the pair form
  when `E.link i` shares a link of `D` with a neighbour (then `onlyIn_of_neighbour`), by
  `theorem3_bing` and `onlyIn_of_no_common` otherwise. `theorem3LiteralOr_holds`:
  `Theorem3LiteralOr` holds.
-/

namespace HPC.Fold.Recon122

open HPC HPC.Chain

variable {X : Type*} [MetricSpace X] {n k : ℕ}

/-- **From the model back to the chain, with a pair**: `chain_of_bconcl` keeping track of a second
link at time `0`. -/
theorem chain_of_bconclZ {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (hk : 0 < k)
    (i i' : Fin n) (hc : BConclZ n k (chainRho hcr.1) (chainSig hcr.1) (chainT E D) (pairZ i i')) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β i).val = 0 ∧ β i' = β i ∧
      (∀ v, ∃ j : ℕ, (E.ofBlocks β hβ).link v ⊆ D.unionRange j 2) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, hk⟩).Nonempty ∨ (E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty) →
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange 0 2 ∨
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange (k - 2) 2) := by
  have hB := bHyp_of_crooked hcr
  obtain ⟨b, hbZ, ⟨hlip, hwid⟩, hend⟩ := hc
  have hb0 : b i = 0 := hbZ i i.isLt (Or.inl rfl)
  have hb0' : b i' = 0 := hbZ i' i'.isLt (Or.inr rfl)
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
  refine ⟨b tm + 1, natBlock b hlt, hβ, by simp [natBlock, hb0],
    Fin.ext (by simp [natBlock, hb0, hb0']), fun v => ?_, fun t ht hm => ?_⟩
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

/-- Containment in a link of `D`, read with `(chainRho, chainSig)`. -/
theorem subset_link_iff {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (t : Fin n)
    (j : ℕ) (hj : j < k) :
    E.link t ⊆ D.link ⟨j, hj⟩ ↔ chainRho hcr.1 t ≤ j ∧ j ≤ chainSig hcr.1 t := by
  have hρ : chainRho hcr.1 t = (hcr.1.minIdx t : ℕ) := by simp [chainRho]
  have hσ : chainSig hcr.1 t = (hcr.1.maxIdx t : ℕ) := by simp [chainSig]
  rw [hρ, hσ]
  constructor
  · intro hs
    exact ⟨Fin.le_def.mp (minIdx_le hcr.1 _ hs), Fin.le_def.mp (le_maxIdx hcr.1 _ hs)⟩
  · rintro ⟨h1, h2⟩
    exact Recon121.link_subset_of_between hcr.1 t ⟨j, hj⟩ (Fin.le_def.mpr h1) (Fin.le_def.mpr h2)

/-- A link of `E` lying in exactly one link `e_a` of `D` and inside `e_j + e_{j+1}` has
`a ∈ {j, j + 1}`. -/
theorem single_in_two {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (t : Fin n)
    (hs : chainRho hcr.1 t = chainSig hcr.1 t) {j : ℕ} (hsub : E.link t ⊆ D.unionRange j 2) :
    chainRho hcr.1 t = j ∨ chainRho hcr.1 t = j + 1 := by
  have hB := bHyp_of_crooked hcr
  set a := chainRho hcr.1 t with ha
  have hak : a < k := by have := hB.lt t t.isLt; omega
  have hta : E.link t ⊆ D.link ⟨a, hak⟩ := (subset_link_iff hcr t a hak).mpr ⟨le_rfl, by omega⟩
  have key : ∀ x ∈ E.link t, ∃ j' : ℕ, ∃ hj' : j' < k, (j' = j ∨ j' = j + 1) ∧
      x ∈ D.link ⟨j', hj'⟩ ∧ j' ≤ a + 1 ∧ a ≤ j' + 1 := by
    intro x hx
    obtain ⟨j', h1, h2, hj', hx'⟩ := mem_unionRange.mp (hsub hx)
    have := (D.adjacent_iff ⟨a, hak⟩ ⟨j', hj'⟩).mp ⟨x, hta hx, hx'⟩
    simp only at this
    exact ⟨j', hj', by omega, hx', by omega, by omega⟩
  obtain ⟨x0, hx0⟩ := E.link_nonempty t
  obtain ⟨j0, hj0, -, -, -, -⟩ := key x0 hx0
  by_contra hne
  rcases (by omega : j + 2 ≤ a ∨ a + 1 ≤ j) with hc | hc
  · have hjk : j + 1 < k := by omega
    have : E.link t ⊆ D.link ⟨j + 1, hjk⟩ := by
      intro x hx
      obtain ⟨j', hj', h1, h2, h3, h4⟩ := key x hx
      have e : j' = j + 1 := by omega
      subst e; exact h2
    have := ((subset_link_iff hcr t (j + 1) hjk).mp this).1
    omega
  · have hjk : j < k := by
      obtain ⟨j', hj', h1, -, h3, -⟩ := key x0 hx0
      omega
    have : E.link t ⊆ D.link ⟨j, hjk⟩ := by
      intro x hx
      obtain ⟨j', hj', h1, h2, h3, h4⟩ := key x hx
      have e : j' = j := by omega
      subst e; exact h2
    have := ((subset_link_iff hcr t j hjk).mp this).2
    omega

end HPC.Fold.Recon122

namespace HPC.Fold

open HPC HPC.Chain HPC.Fold.Recon122

/-- **The pair form of Bing's Theorem 3** (COMMISSION-batch124 Q1): if `E` is crooked (1948) in
`D` and `E.link i`, `E.link i'` are equal or adjacent links lying in a common link of `D`, there is
a block consolidation as in `theorem3_bing` (first block containing `E.link i`, every block in two
adjacent links of `D`, Bing's end clause) with `E.link i'` in the first block too. -/
theorem theorem3_pair {X : Type*} [MetricSpace X] {n k : ℕ} (hk : 0 < k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i i' : Fin n)
    (hii' : ((i' : ℤ) - (i : ℤ)).natAbs ≤ 1)
    (hcom : ∃ j, E.link i ⊆ D.link j ∧ E.link i' ⊆ D.link j) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β i).val = 0 ∧ β i' = β i ∧
      (∀ v, ∃ j : ℕ, (E.ofBlocks β hβ).link v ⊆ D.unionRange j 2) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, hk⟩).Nonempty ∨ (E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty) →
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange 0 2 ∨
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange (k - 2) 2) := by
  obtain ⟨j, hj, hj'⟩ := hcom
  have h1 := (subset_link_iff hcr i j.val j.isLt).mp hj
  have h2 := (subset_link_iff hcr i' j.val j.isLt).mp hj'
  exact chain_of_bconclZ hcr hk i i' (pair_main k n _ _ _ i i' (bHyp_of_crooked hcr) i.isLt
    i'.isLt (by omega) (by omega) ⟨j.val, h1.1, h1.2, h2.1, h2.2⟩)

/-- **`Theorem3Pair` holds** (the open `Prop` of batch 123). -/
theorem theorem3Pair_holds : Theorem3Pair := by
  intro X _ n k hk E D hcr i i' hii' hcom
  exact theorem3_pair hk hcr i i' (by omega) hcom

/-- **The only-clause at a link sharing a link of `D` with neither neighbour** (COMMISSION-batch124
Q2): for every block consolidation whose blocks lie in two adjacent links of `D`. Such a link and
its neighbours each lie in exactly one link of `D`, the neighbours one level above or below; a block
in two adjacent links of `D` cannot contain one neighbour from above and one from below, so if
`E.link i` were inside another block it would be covered by neighbours all lying in one link of
`D`, which would then contain `E.link i` too. -/
theorem onlyIn_of_no_common {X : Type*} [MetricSpace X] {n k q : ℕ} {E : Chain X n}
    {D : Chain X k} (hcr : E.IsCrookedIn' D) {β : Fin n → Fin q} (hβ : IsBlockMap β)
    (hblk : ∀ v, ∃ j : ℕ, (E.ofBlocks β hβ).link v ⊆ D.unionRange j 2) (i : Fin n)
    (hno : ∀ t₀ : Fin n, ((t₀ : ℤ) - (i : ℤ)).natAbs = 1 →
      ¬ ∃ j, E.link i ⊆ D.link j ∧ E.link t₀ ⊆ D.link j) :
    OnlyIn E β hβ i := by
  intro v hv hsub
  have hB := bHyp_of_crooked hcr
  have hcov := Recon121.link_subset_neighbours E hβ hv hsub
  obtain ⟨j, hj⟩ := hblk v
  -- a neighbour shares no link of `D` with `E.link i`: both are single levels, one apart
  have hnb : ∀ t : Fin n, ((t : ℤ) - (i : ℤ)).natAbs = 1 →
      chainRho hcr.1 t = chainSig hcr.1 t ∧ chainRho hcr.1 i = chainSig hcr.1 i ∧
        (chainRho hcr.1 t + 1 = chainRho hcr.1 i ∨ chainRho hcr.1 t = chainRho hcr.1 i + 1) := by
    intro t ht
    have hadj : chainSig hcr.1 t ≤ chainRho hcr.1 i + 1 ∧
        chainSig hcr.1 i ≤ chainRho hcr.1 t + 1 := by
      rcases (by omega : t.val + 1 = i.val ∨ i.val + 1 = t.val) with e | e
      · have := hB.adj t.val (by omega); rw [e] at this; exact this
      · have := hB.adj i.val (by omega); rw [e] at this; exact ⟨this.2, this.1⟩
    have := hB.le t t.isLt; have := hB.le i i.isLt
    have := hB.wid t t.isLt; have := hB.wid i i.isLt
    have := hB.lt t t.isLt; have := hB.lt i i.isLt
    have hdis : ¬ (chainRho hcr.1 i ≤ chainSig hcr.1 t ∧ chainRho hcr.1 t ≤ chainSig hcr.1 i) := by
      rintro ⟨c1, c2⟩
      have hm : max (chainRho hcr.1 i) (chainRho hcr.1 t) < k := by omega
      exact hno t ht ⟨⟨max (chainRho hcr.1 i) (chainRho hcr.1 t), hm⟩,
        (subset_link_iff hcr i _ hm).mpr ⟨by omega, by omega⟩,
        (subset_link_iff hcr t _ hm).mpr ⟨by omega, by omega⟩⟩
    omega
  -- the neighbours in block `v` lie in `e_j + e_{j+1}`
  have hwin : ∀ t : Fin n, β t = v → ((t : ℤ) - (i : ℤ)).natAbs = 1 →
      chainRho hcr.1 t = j ∨ chainRho hcr.1 t = j + 1 := by
    intro t htv ht
    refine single_in_two hcr t (hnb t ht).1 (fun x hx => hj ?_)
    rw [ofBlocks_link]
    exact Set.mem_biUnion (show t ∈ {t | β t = v} from htv) hx
  -- so all of them lie in the same level `a`
  obtain ⟨x0, hx0⟩ := E.link_nonempty i
  have hx0' := hcov hx0
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx0'
  obtain ⟨t₁, ⟨hβt₁, ht₁⟩, -⟩ := hx0'
  have hsame : ∀ t : Fin n, β t = v → ((t : ℤ) - (i : ℤ)).natAbs = 1 →
      chainRho hcr.1 t = chainRho hcr.1 t₁ := by
    intro t htv ht
    have a1 := hnb t ht; have a2 := hnb t₁ ht₁
    have b1 := hwin t htv ht; have b2 := hwin t₁ hβt₁ ht₁
    omega
  have hak : chainRho hcr.1 t₁ < k := by have := hB.lt t₁ t₁.isLt; have := (hnb t₁ ht₁).1; omega
  have hlev : ∀ t : Fin n, β t = v → ((t : ℤ) - (i : ℤ)).natAbs = 1 →
      E.link t ⊆ D.link ⟨chainRho hcr.1 t₁, hak⟩ := by
    intro t htv ht
    have e := hsame t htv ht
    have := (hnb t ht).1
    exact (subset_link_iff hcr t _ hak).mpr ⟨by omega, by omega⟩
  have hi : E.link i ⊆ D.link ⟨chainRho hcr.1 t₁, hak⟩ := by
    intro x hx
    have hx' := hcov hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx'
    obtain ⟨t, ⟨htv, ht⟩, hxt⟩ := hx'
    exact hlev t htv ht hxt
  exact hno t₁ ht₁ ⟨_, hi, hlev t₁ hβt₁ ht₁⟩

/-- **Bing 1948, Theorem 3, as printed — every clause** (COMMISSION-batch124 Q3). If `E` (Bing's
`D`) is crooked (1948) in the chain `D` (Bing's `E`) and `i` is a link of `E`, then `E` has a block
consolidation in which `E.link i` lies in the first block **and in no other block**, every block
lies in the sum of two adjacent links of `D`, and the block of an end link of `E` meeting the first
or the last link of `D` lies in the sum of the first two or of the last two links of `D`. -/
theorem theorem3_literal {X : Type*} [MetricSpace X] {n k : ℕ} (hk : 0 < k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β i).val = 0 ∧
      (∀ v, v ≠ β i → ¬ E.link i ⊆ (E.ofBlocks β hβ).link v) ∧
      (∀ v, ∃ j : ℕ, (E.ofBlocks β hβ).link v ⊆ D.unionRange j 2) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, hk⟩).Nonempty ∨ (E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty) →
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange 0 2 ∨
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange (k - 2) 2) := by
  by_cases hA : ∃ t₀ : Fin n, ((t₀ : ℤ) - (i : ℤ)).natAbs = 1 ∧
      ∃ j, E.link i ⊆ D.link j ∧ E.link t₀ ⊆ D.link j
  · obtain ⟨t₀, ht₀, hj⟩ := hA
    obtain ⟨q, β, hβ, h0, hβt₀, hmain, hend⟩ := theorem3_pair hk hcr i t₀ (by omega) hj
    exact ⟨q, β, hβ, h0, onlyIn_of_neighbour E hβ ht₀ hβt₀, hmain, hend⟩
  · push_neg at hA
    obtain ⟨q, β, hβ, h0, hmain, hend⟩ := theorem3_bing hk hcr i
    refine ⟨q, β, hβ, h0, onlyIn_of_no_common hcr hβ hmain i (fun t₀ ht₀ => ?_), hmain, hend⟩
    rintro ⟨j, hj1, hj2⟩
    exact hA t₀ ht₀ j hj1 hj2

/-- **`Theorem3LiteralOr` holds**: Bing's Theorem 3 as printed (batch 121's `Prop`, Bing's own
\"or\" wording of the end clause), for chains in every metric space. -/
theorem Recon121.theorem3LiteralOr_holds : Recon121.Theorem3LiteralOr.{u} :=
  fun _ _ _ _ hk _ _ hcr i => theorem3_literal hk hcr i

end HPC.Fold
