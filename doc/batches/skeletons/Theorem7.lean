import HPC.PseudoArc.Theorem13

/-!
# Bing 1948, Theorems 7, 8, 9 in full

Skeleton for batch 82 (save as `HPC/Fold/Theorem7.lean`; add `import HPC.Fold.Theorem7` to the root
`HPC.lean`). Statements only; every proof is `sorry` and is a work item. The shapes may be adjusted,
with the change recorded, provided the content of Bing's statements is preserved or a recorded
correction is made where his statement is false as written (COMMISSION-batch82.md §3).

Conventions: `E` fine (Bing's `D`), `D` coarse (Bing's `E`) with `m` links; Bing's pattern
`P(m)`, `(1, y(1)), …, (z(m−1), y(z(m−1)))`, is the level sequence `bingPath 0 (m − 1)` of
`HPC/Fold/OffCenter.lean` (its length is `z (m − 1)`, `bingPath_length`), read `0`-indexed.
-/

namespace HPC.Fold

open HPC.Chain

variable {X : Type*} [MetricSpace X]

/-- The canonical pattern of Bing's Theorem 7 as a map from `Fin (z (m-1))` to the links of an
`m`-link chain: position `i` goes to link `bingPath 0 (m-1)` at `i`. -/
def bingPattern (m : ℕ) (hm : 1 ≤ m) : Fin (z (m - 1)) → Fin m :=
  fun i => ⟨((bingPath 0 (m - 1 : ℤ)).get ⟨i.val, by
      rw [bingPath_length]; simpa using i.isLt⟩).toNat, by sorry⟩

/-- **Bing 1948, Theorem 7, in full** (block reading). If `E` is crooked in `D` (`m ≥ 3` links),
some link of `E` lies in the first link of `D` and some in the last, then `E` has a block
consolidation `F` with exactly `z (m − 1)` links, whose first link lies in `D.link 0`, whose last
lies in `D.link (m−1)`, which is crooked in `D`, and which follows the pattern `bingPattern m` in
`D`. (Minimality — no consolidation with fewer links has these properties — is `minimality`.) -/
theorem theorem7 {n m : ℕ} (hm : 3 ≤ m) {E : Chain X n} {D : Chain X m} (hcr : E.IsCrookedIn' D)
    (hlo : ∃ t, E.link t ⊆ D.link ⟨0, by omega⟩) (hhi : ∃ t, E.link t ⊆ D.link ⟨m - 1, by omega⟩) :
    ∃ (β : Fin n → Fin (z (m - 1))) (hβ : IsBlockMap β),
      (E.ofBlocks β hβ).IsCrookedIn' D ∧
      (E.ofBlocks β hβ).FollowsPattern (bingPattern m (by omega)) D := by
  sorry

/-- **Bing 1948, Theorem 8**, in the form its use in Theorem 9 needs (§3 of the commission says
why the literal statement is doubtful): two chains crooked in `D`, each with a link in each end
link of `D` and each with exactly `z (m−1)` links, both follow `bingPattern m` in `D`; and if the
unions of corresponding links form a chain, that chain is crooked in `D`. -/
theorem theorem8 {m : ℕ} (hm : 3 ≤ m) {D : Chain X m} (F₁ F₂ : Chain X (z (m - 1)))
    (h₁ : F₁.IsCrookedIn' D) (h₂ : F₂.IsCrookedIn' D)
    (hlo₁ : ∃ t, F₁.link t ⊆ D.link ⟨0, by omega⟩) (hhi₁ : ∃ t, F₁.link t ⊆ D.link ⟨m - 1, by omega⟩)
    (hlo₂ : ∃ t, F₂.link t ⊆ D.link ⟨0, by omega⟩) (hhi₂ : ∃ t, F₂.link t ⊆ D.link ⟨m - 1, by omega⟩)
    (C : Chain X (z (m - 1))) (hC : ∀ i, C.link i = F₁.link i ∪ F₂.link i) :
    F₁.FollowsPattern (bingPattern m (by omega)) D ∧ F₂.FollowsPattern (bingPattern m (by omega)) D ∧
    C.IsCrookedIn' D := by
  sorry

/-- **Bing 1948, Theorem 9** (block reading, three-link form for the mesh clause as in
`theorem4`). `E` crooked in `D`; `E.link 0 ⊆ D.link 0`, `E.link (n−1) ⊆ D.link (m−1)`,
`E.link r ⊆ D.link (m−1)`, `E.link s ⊆ D.link 0` with `r < s`. Then for every `t < s` there is a
block consolidation `F` of `E` whose first block contains `0`, whose last block contains `n−1`,
every block in three consecutive links of `D`, and such that every run of consecutive blocks
whose end blocks contain `t` and `n−1` contains all of `E.link r … E.link n−1` — Bing: "any
subchain of `F` whose end links contain `d_t` and `d_n` respectively contains `D(r, n)`". -/
theorem theorem9 {n m : ℕ} (hm : 3 ≤ m) {E : Chain X n} {D : Chain X m} (hcr : E.IsCrookedIn' D)
    (hn : 0 < n) (r s : Fin n) (hrs : r < s)
    (h0 : E.link ⟨0, hn⟩ ⊆ D.link ⟨0, by omega⟩)
    (hlast : E.link ⟨n - 1, by omega⟩ ⊆ D.link ⟨m - 1, by omega⟩)
    (hr : E.link r ⊆ D.link ⟨m - 1, by omega⟩) (hs : E.link s ⊆ D.link ⟨0, by omega⟩)
    (t : Fin n) (hts : t < s) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β ⟨0, hn⟩).val = 0 ∧ (β ⟨n - 1, by omega⟩).val = q - 1 ∧
      (∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 3) ∧
      ∀ u : Fin n, r ≤ u → β t ≤ β u := by
  sorry

end HPC.Fold
