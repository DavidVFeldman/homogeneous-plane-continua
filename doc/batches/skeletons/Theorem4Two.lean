import HPC.Fold.Recon122

/-!
# Batch 123: Bing 1948, Theorem 4 in Bing's two-link form; the only-clauses

Skeleton. Every `sorry` is a work item; shapes may be adjusted with the change recorded. Save as
`HPC/Fold/Theorem4Two.lean`, add `import HPC.Fold.Theorem4Two` at the end of the root `HPC.lean`.
(The import of `Recon122` is a placeholder: if the bridge lemmas move in item 1 of the commission,
import their new home instead.)

**Theorem 4 (p. 733).** *If D = [d₁, d₂, ⋯, d_n] is a chain crooked in the chain E =
[e₁, e₂, ⋯, e_m] and D(r, s) is a subchain of D such that a link of D(r, s) intersects e₁ and a
link of D(r, s) intersects e_m, then there is a chain F such that F is a consolidation of D, each
element of F is a subset of the sum of two adjacent links of E, d_r is contained in only the first
link of F, and d_s is contained in only the last.*

*Proof* (Bing). Let D(h, k) be a subchain of D(r, s) such that d_h intersects e₁ and d_k
intersects e_m. For convenience, suppose that h < k and that d_r and d_s are links of D(1, h) and
D(k, n) respectively. By Theorem 3, there is a chain H which is a consolidation of D(1, h) such
that each link of H is a subset of the sum of two adjacent elements of E, d_r is contained in only
the first link of H, and any link of H containing d_h is a subset of either e₁ + e₂ or
e_{m−1} + e_m; also, there is a chain G such that G is a consolidation of D(k, n), each link of G
is a subset of the sum of two adjacent elements of E, d_s is contained in only the first link of
G, and any link of G containing d_k is a subset of e₁ + e₂ or e_{m−1} + e_m. Let h_u and g_v be
the first elements of H and G containing d_h and d_k respectively. Since the case of our theorem
where m ≤ 4 is easily established, we suppose that h_u and g_v are subsets of e₁ + e₂ and
e_{m−1} + e_m respectively. The required chain F is defined as follows: The first links of F are
the links of H(1, u − 1); the last links of F are the links of G(v − 1, 1); if D′ denotes the links
of D in neither H(1, u − 1) nor G(v − 1, 1), the sum of the links of D′ in e₁ + e₂ is a link of F,
the sum of the links of D′ in e₃ but not in e₂ is another link, ⋯, and the sum of the links of D′
in e_{m−1} + e_m is another link of F.

Conventions as in `HPC/Fold/Theorem4.lean`: `E` is the fine chain (Bing's D), `D` the coarse chain
(Bing's E); "a subset of the sum of two adjacent links" is `⊆ D.unionRange j 2`. The repository's
`theorem4` is the three-link form; this file states Bing's.
-/

namespace HPC.Fold

open HPC.Chain

/-! ### Theorem 4, two-link form (without the only-clauses) -/

/-- **Bing 1948, Theorem 4, two-link form** (block reading): if some link of `E` between `r` and
`s` meets the first link of `D` and some link between `r` and `s` meets the last, then `E` has a
block consolidation, every block in two adjacent links of `D`, in which `E.link r` is in the
first block and `E.link s` in the last. (Bing's proof, from `Theorem3Block` — the two-link
Theorem 3 with its end clause, batch 122 — with the general-case regrouping of Recon122; in the
model, `BConcl` on `D(1, h)` and on `D(k, n)` reversed, cut at the blocks of `d_h`, `d_k`, the
rest grouped by least level from the bottom. The case of few coarse links as Bing says, or by the
level grouping.) -/
theorem theorem4_two {X : Type*} [MetricSpace X] {n k : ℕ} (hk : 0 < k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (r s : Fin n) (hrs : r ≤ s)
    (hlow : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, hk⟩).Nonempty)
    (hhigh : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β r).val = 0 ∧ (β s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 2 := by
  sorry

/-- The three-link `theorem4` follows from the two-link one (a two-link window is a three-link
window). Not to replace `theorem4`; a consistency check. -/
theorem theorem4_of_two {X : Type*} [MetricSpace X] {n k : ℕ} (hn : 0 < n) (hk : 3 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (r s : Fin n) (hrs : r ≤ s)
    (hlow : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, by omega⟩).Nonempty)
    (hhigh : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' r).val = 0 ∧ (β' s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  sorry

/-! ### The only-clauses (reconnaissance; Props, no `sorry` beyond this skeleton's) -/

/-- Bing's clause "`d_i` is contained in only the first link of `F`", for a block map `β` with
`β i` the first block: `E.link i` lies in no other block. -/
def OnlyIn {X : Type*} [MetricSpace X] {n q : ℕ} (E : Chain X n) (β : Fin n → Fin q)
    (hβ : IsBlockMap β) (i : Fin n) : Prop :=
  ∀ v, v ≠ β i → ¬ E.link i ⊆ (E.ofBlocks β hβ).link v

/-- **Theorem 4 as printed**: `theorem4_two` with the only-clauses at `r` and `s`. Recorded as a
`Prop`; see the commission (item 3). -/
def Theorem4Literal : Prop :=
  ∀ (X : Type) [MetricSpace X] (n k : ℕ) (hk : 0 < k) (E : Chain X n) (D : Chain X k),
    E.IsCrookedIn' D → ∀ r s : Fin n, r ≤ s →
    (∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, hk⟩).Nonempty) →
    (∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty) →
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β r).val = 0 ∧ (β s).val = q - 1 ∧ OnlyIn E β hβ r ∧ OnlyIn E β hβ s ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 2

end HPC.Fold
