import HPC.Plane.Organ98

/-!
# Batch 99: the last-link claim of Bing's Theorem 10 (Duke 1951), by Fugate's counting argument

Skeleton (save as `HPC/Plane/LastLink99.lean`; add `import HPC.Plane.LastLink99` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded. If `lastLink_of_minimal` closes, the `sorry` of `theorem10_1951`
(`HPC/Plane/EndPoints51.lean`) is to be replaced by a proof through `theorem10_1951_of_lastLink`
/ `theorem10_1951_of_lastLink'` (`Surgery91.lean`) — the one permitted edit to an existing file;
record it. `endPoint_of_condA`, `theorem13_1951` sufficiency and `theorem11_1951_of_T10` then lose
their `sorryAx` automatically.

Source: J. B. Fugate, *Decomposable chainable continua*, Trans. AMS 123 (1966), Lemma 1, pp.
461–463 (COMMISSION-batch99.md §1 transcribes the relevant paragraph). Fugate's chain `G` has the
distinguished set in its *last* link and proves the claim for its *first* link; Bing's `F` has
`p` in the first link and the claim concerns the last. The skeleton uses Bing's orientation.
-/

namespace HPC.Plane

open Set Topology

variable {X : Type*} [MetricSpace X]

/-- A **Theorem-10 chain for `K` from `p` refining `D`**: covers `K`, refines `D`, and `p` lies
in the first link and in the closure of no other. -/
def IsT10Chain {m : ℕ} (D : Chain X m) (K : Set X) (p : X) {k : ℕ} (F : Chain X k) : Prop :=
  ∃ hk : 0 < k, K ⊆ F.union ∧ F.Refines D ∧ p ∈ F.link ⟨0, hk⟩ ∧
    ∀ j : Fin k, j.val ≠ 0 → p ∉ closure (F.link j)

/-- **Discrete intermediate value for refinements.** If `F` refines `D`, a run of consecutive
links `F(u..v)` whose first link meets `D_a` and whose last meets `D_b` contains, for every index
`r` between `a` and `b`, a link lying in `D_r` — where "lying in" is witnessed by a choice of
`D`-index for each `F`-link, consecutive choices differing by at most one. -/
theorem exists_link_in_between {m k : ℕ} {D : Chain X m} {F : Chain X k} (hFD : F.Refines D)
    (idx : Fin k → Fin m) (hidx : ∀ i, F.link i ⊆ D.link (idx i))
    {u v : Fin k} (huv : u ≤ v) {r : Fin m} (hr : idx u ≤ r ∧ r ≤ idx v ∨ idx v ≤ r ∧ r ≤ idx u) :
    ∃ i : Fin k, u ≤ i ∧ i ≤ v ∧ idx i = r := by
  sorry

/-- **The last-link claim** (Bing: "the last link of `F` intersects `M''·(d₁ + d_m)` or else a
chain with fewer links than `F` with the required properties covers `M''`"; Fugate, Lemma 1,
p. 462). Let `K` be a continuum meeting every link of `D` (`m ≥ 2`), `p ∈ K`, and `F` a
Theorem-10 chain for `K` from `p` refining `D` **of least length** among such chains. Then the
last link of `F` meets `K ∩ (D_0 ∪ D_{m−1})` at a point other than `p`. -/
theorem lastLink_of_minimal {m : ℕ} (D : Chain X m) (hm : 2 ≤ m) {K : Set X}
    (hK : Fold.Q78.IsContinuum K) (hmeet : ∀ i, (D.link i ∩ K).Nonempty) {p : X} (hpK : p ∈ K)
    {k : ℕ} (F : Chain X k) (hF : IsT10Chain D K p F)
    (hmin : ∀ (k' : ℕ) (F' : Chain X k'), IsT10Chain D K p F' → k ≤ k') :
    ∃ y ∈ K, y ≠ p ∧ y ∈ F.link ⟨k - 1, hF.1⟩ ∧
      (y ∈ D.link ⟨0, by omega⟩ ∨ y ∈ D.link ⟨m - 1, by omega⟩) := by
  sorry

/-- A Theorem-10 chain of least length exists as soon as one exists (well-foundedness of `ℕ`). -/
theorem exists_minimal_T10Chain {m : ℕ} (D : Chain X m) (K : Set X) (p : X)
    (h : ∃ (k : ℕ) (F : Chain X k), IsT10Chain D K p F) :
    ∃ (k : ℕ) (F : Chain X k), IsT10Chain D K p F ∧
      ∀ (k' : ℕ) (F' : Chain X k'), IsT10Chain D K p F' → k ≤ k' := by
  sorry

/-- **Theorem 10** (Bing 1951, p. 659), assembled: minimal counterexample `M'` (Zorn, as in batch
85), `K = M''` from `exists_proper_meeting_all_links` (batch 91), a Theorem-10 chain for `K` from
the minimality of `M'` (proper subcontinua satisfy the theorem — note the chain must be made to
refine `D` and have `p` in the first link only: this is the induction hypothesis), a least one,
`lastLink_of_minimal`, then `theorem10_1951_of_lastLink` / `_of_lastLink'`. -/
theorem theorem10_1951' {M : Set X} (hM : Fold.Q78.IsContinuum M) {m : ℕ} (D : Chain X m)
    (hD : M ⊆ D.union) {p : X} (hp : CondA M p) :
    ∃ (n : ℕ) (E : Chain X n) (hn : 0 < n), M ⊆ E.union ∧ E.Refines D ∧
      p ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (E.link j) := by
  sorry

end HPC.Plane
