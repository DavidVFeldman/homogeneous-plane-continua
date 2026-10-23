import HPC.Fold.Recon121
import HPC.Fold.Recon122General
import HPC.Fold.T9Ends
import HPC.Fold.Theorem3Bing

/-!
# Batch 122: Bing's induction for Theorem 3, closed

COMMISSION-batch122.md. Conventions as in `HPC.Fold.Recon121`: `E` is the fine chain (Bing's `D`),
`D` the coarse chain (Bing's `E`), a consolidation is a block consolidation `E.ofBlocks β hβ`.

* `HPC/Fold/Recon122Model.lean`, `Recon122Special.lean`, `Recon122General.lean`: Bing's Theorem 3
  in the faithful model with a meeting table (`BHyp`, `BConcl`), proved by Bing's induction with
  the seams of the special case closed (`bing_main`).
* This file: the statement of `theorem3_end` (`theorem3EndStmt_holds`; since batch 123 the
  transfer to chains, `bHyp_of_crooked`, `chain_of_bconcl`, and Bing's Theorem 3 as printed
  without the only-clause, `theorem3Block_holds`, live in `HPC/Fold/Theorem3Bing.lean`); the
  Props of the commission (`Theorem3Strong`, `SeamP`), and the batch-121 construction `Cbot` as a
  special case of the closed construction (`bingSpecialFCbot_eq_cutF`, `cbot_works_of_seamP`).
-/

namespace HPC.Fold.Recon122

open HPC HPC.Chain HPC.Fold.Recon121

universe u

/-! ## The transfer from chains to the model

Moved in batch 123 to `HPC/Fold/Theorem3Bing.lean` (names unchanged: `chainRho`, `chainSig`,
`chainT`, `bHyp_of_crooked`, `chain_of_bconcl`), so that `HPC/Fold/Theorem4.lean` can import it. -/

/-! ## Q3: the statements -/

/-! `Theorem3Block` (Theorem 3 as printed without the only-clause) and `theorem3Block_holds` moved
in batch 123 to `HPC/Fold/Theorem3Bing.lean`, names unchanged. -/

/-- **The strengthened statement of the commission (Q3)**, in the model: Bing's statement in the
block reading for every number of coarse links, with the meeting table as data. Batch 122 found
that the property `P` of the commission need not be carried through the induction (its `P` is
`True`): at `r ≥ 6` every consolidation `H` given by the induction hypothesis makes the `Cbot`
construction work (`seamP_of_endClause`, `cbot_works_of_seamP`), and at `r = 5` the
construction is explicit (`special_five`). -/
def Theorem3Strong : Prop := ∀ K, BingMain K

/-- **`Theorem3Strong` holds**: Bing's induction, with the seams closed. -/
theorem theorem3Strong_holds : Theorem3Strong := bing_main

/-- `Theorem3Strong → Theorem3Block`: the transfer from the model to chains. -/
theorem theorem3Block_of_strong : Theorem3Strong → Theorem3Block.{u} := by
  intro hS X _ n k hk E D hcr i
  exact chain_of_bconcl hcr hk i (hS k n _ _ _ i (bHyp_of_crooked hcr) i.isLt)

/-- `Theorem3LiteralOr → Theorem3Block` (drop the only-clause). -/
theorem theorem3Block_of_literalOr : Theorem3LiteralOr.{u} → Theorem3Block.{u} := by
  intro h X _ n k hk E D hcr i
  obtain ⟨q, β, hβ, h0, -, hmain, hend⟩ := h X n k hk E D hcr i
  exact ⟨q, β, hβ, h0, hmain, hend⟩

/-- `Theorem3Block → Theorem3EndStmt` (the proof of `theorem3EndStmt_of_literalOr` uses no
only-clause). -/
theorem theorem3EndStmt_of_block : Theorem3Block.{u} → Theorem3EndStmt.{u} := by
  intro h X _ n k _hn hk E D hcr i
  obtain ⟨q, β, hβ, h0, hmain, hend⟩ := h X n k (by omega) E D hcr i
  refine ⟨q, β, hβ, h0, fun v => ?_, fun t ht => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · obtain ⟨j, hj⟩ := hmain v
    exact ⟨j, hj.trans (unionRange_mono D le_rfl (by omega))⟩
  · by_cases hk3 : k = 3
    · subst hk3
      intro x hx
      obtain ⟨t', ht'⟩ := (show x ∈ E.union from by
        simp only [ofBlocks_link, Set.mem_iUnion] at hx
        obtain ⟨t', -, hx'⟩ := hx
        exact Set.mem_iUnion.mpr ⟨t', hx'⟩) |> Set.mem_iUnion.mp
      obtain ⟨j, hj⟩ := hcr.1 t'
      exact link_subset_unionRange D j (by omega) (by have := j.isLt; omega) (hj ht')
    · rcases hend t ht (Or.inl hm) with h1 | h1
      · exact h1.trans (unionRange_mono D le_rfl (by omega))
      · exfalso
        obtain ⟨z, hz1, hz2⟩ := hm
        have hzb : z ∈ (E.ofBlocks β hβ).link (β t) := by
          rw [ofBlocks_link]; exact Set.mem_biUnion (show β t = β t from rfl) hz1
        obtain ⟨a, ha1, ha2, ha3, ha4⟩ := mem_unionRange.mp (h1 hzb)
        have := (D.adjacent_iff ⟨a, ha3⟩ ⟨0, by omega⟩).mp ⟨z, ha4, hz2⟩
        simp only at this; omega
  · by_cases hk3 : k = 3
    · subst hk3
      intro x hx
      obtain ⟨t', ht'⟩ := (show x ∈ E.union from by
        simp only [ofBlocks_link, Set.mem_iUnion] at hx
        obtain ⟨t', -, hx'⟩ := hx
        exact Set.mem_iUnion.mpr ⟨t', hx'⟩) |> Set.mem_iUnion.mp
      obtain ⟨j, hj⟩ := hcr.1 t'
      exact link_subset_unionRange D j (by omega) (by have := j.isLt; omega) (hj ht')
    · rcases hend t ht (Or.inr hm) with h1 | h1
      · exfalso
        obtain ⟨z, hz1, hz2⟩ := hm
        have hzb : z ∈ (E.ofBlocks β hβ).link (β t) := by
          rw [ofBlocks_link]; exact Set.mem_biUnion (show β t = β t from rfl) hz1
        obtain ⟨a, ha1, ha2, ha3, ha4⟩ := mem_unionRange.mp (h1 hzb)
        have := (D.adjacent_iff ⟨a, ha3⟩ ⟨k - 1, by omega⟩).mp ⟨z, ha4, hz2⟩
        simp only at this; omega
      · exact h1.trans (unionRange_mono D (by omega) (by omega))

/-- `Theorem3Strong → Theorem3EndStmt`. -/
theorem theorem3EndStmt_of_strong : Theorem3Strong → Theorem3EndStmt.{u} :=
  fun h => theorem3EndStmt_of_block (theorem3Block_of_strong h)

/-- **The statement of `HPC.Fold.theorem3_end` holds** (OPEN.md item 1, closed in batch 123). Since
batch 123 an alias of `HPC.Fold.theorem3_end`, which is proved from `Theorem3Bing`. -/
theorem theorem3EndStmt_holds : Theorem3EndStmt.{u} :=
  fun _ _ _ _ hn hk _ _ hcr i => theorem3_end hn hk hcr i

/-- **`HPC.Fold.theorem3_end`, proved**: the statement of `HPC/Fold/Theorem4.lean`, verbatim. Since
batch 123 an alias of `HPC.Fold.theorem3_end`. -/
theorem theorem3_end' {X : Type u} [MetricSpace X] {n k : ℕ} (hn : 0 < n) (hk : 3 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧
      (∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange 0 3) ∧
        ((E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange (k - 3) 3)) :=
  theorem3_end hn hk hcr i

/-! ## Q1: the batch-121 construction `Cbot` and the property `P` -/

/-- **The seam property `P_s`** of a consolidation `H` of `D(1, h)` (fine links `0 … hh`): every
link in the block of `d_h` lies in the top `Cbot` group, i.e. in no link below `e₃` (`2 ≤ ρ`) and
reaching `e_{r−2}` (`K − 3 ≤ σ`). -/
def SeamP (K : ℕ) (ρ σ H : ℕ → ℕ) (hh : ℕ) : Prop :=
  ∀ t, t ≤ hh → H t = H hh → 2 ≤ ρ t ∧ K ≤ σ t + 3

/-- The batch-121 construction `Cbot` is the closed construction `cutF` cut at the block of `d_h`. -/
theorem bingSpecialFCbot_eq_cutF (K : ℕ) (ρ σ : ℕ → ℕ) (hh k : ℕ) (H : ℕ → ℕ) :
    bingSpecialFCbot K ρ σ hh k H = cutF K ρ σ 0 hh k (H hh) H := by
  funext t
  simp only [bingSpecialFCbot, cutF, cbotG, Nat.zero_le, true_and]

/-- **`Cbot` works for every `H` with the seam property** (special case, branch `d_i ∈ D(1, h)`,
every `r ≥ 5`): if `H` is a consolidation of `D(1, h)` with `d_i` in its first block, the block of
`d₀` in `e₁ + e₂` (Bing's end clause), and `SeamP`, then the batch-121 `F` (`bingSpecialFCbot`)
satisfies Bing's conclusion. -/
theorem cbot_works_of_seamP {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {i hh k : ℕ}
    (h : BHyp n K ρ σ T) (hs : SpecialHyp n K ρ σ T i) (hih : i ≤ hh) (hhk : hh ≤ k)
    (hk : k + 1 < n) (hkb : ρ k ≤ 1) (H : ℕ → ℕ) (hH0 : H i = 0) (hHc : PCons 0 hh ρ σ H)
    (hH0b : ∀ t, t ≤ hh → H t = H 0 → ρ t ≤ 1) (hP : SeamP K ρ σ H hh) :
    bingSpecialFCbot K ρ σ hh k H i = 0 ∧
      PCons 0 (n - 1) ρ σ (bingSpecialFCbot K ρ σ hh k H) ∧
      EndC n K ρ σ T (bingSpecialFCbot K ρ σ hh k H) := by
  obtain ⟨_, _, hlev, _, hρl⟩ := hs.facts h
  rw [bingSpecialFCbot_eq_cutF]
  exact cutF_spec h hs.hK hlev (by have := h.le 0 (by omega); omega) hρl H (Nat.zero_le _) hhk
    hk hkb (Nat.zero_le _) hih hH0 hHc (fun t _ ht hHt => hP t ht hHt)
    (fun h' => absurd h' (lt_irrefl 0)) le_rfl (fun _ _ t _ ht => hH0b t ht)

/-- **At `r ≥ 6` the seam property follows from Bing's end clause**: if `d_h` meets `e_{r−1}` and
`H` (from the induction hypothesis on `D(1, h)` inside `E(1, r − 1)`) satisfies the end clause at
`d_h`, then `H` has `SeamP`. So at `r ≥ 6` every `H` given by the induction hypothesis works. -/
theorem seamP_of_endClause {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {hh : ℕ}
    (h : BHyp n K ρ σ T) (hK : 6 ≤ K) (hhn : hh < n) (hht : K - 2 ≤ σ hh) (H : ℕ → ℕ)
    (hHe : (∀ t, t ≤ hh → H t = H hh → ρ t ≤ 1) ∨ (∀ t, t ≤ hh → H t = H hh → K - 2 ≤ σ t + 1)) :
    SeamP K ρ σ H hh := by
  rcases hHe with hb | hb
  · have := hb hh le_rfl rfl; have := h.wid hh hhn; omega
  · intro t ht h3; have := hb t ht h3; have := h.wid t (by omega); omega

end HPC.Fold.Recon122
