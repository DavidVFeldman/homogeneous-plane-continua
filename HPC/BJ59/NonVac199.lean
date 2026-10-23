import HPC.BJ59.BJ59B

/-!
# Batch 199: non-vacuity (commission 199, §9)

* `IsAtomicMap` on degenerate inputs: constant maps are atomic (`isAtomicMap_const`); the identity
  (`isAtomicMap_id`) and `Prod.snd` (`not_isAtomicMap_snd`) are in `HPC/BJ59/Atomic.lean`.
* `IsBJChain` on degenerate inputs: every chain of at most two links (`isBJChain_of_le_two`), and
  the three links `(0, 2)`, `(1, 3)`, `(2, 4)` of `ℝ`, a chain in the library's sense whose outer
  links are at distance `0` (`not_isBJChain_real3`).
* `bj_theorem7`, `bj_theorem7_ends`: all hypotheses met with `H = id`, `A`, `B` singletons
  (`nonvac_bj_theorem7_ends`).
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane

/-- Constant maps are atomic. -/
theorem isAtomicMap_const {X Y : Type*} [MetricSpace X] (y : Y) :
    IsAtomicMap (fun _ : X => y) := by
  intro y' L _ hL
  obtain ⟨x, -, hx⟩ := hL
  have : y = y' := hx
  subst this
  exact Or.inl fun z _ => rfl

/-- A chain of at most two links is a chain in Bing–Jones's sense (no two links are
nonadjacent). -/
theorem isBJChain_of_le_two {X : Type*} [MetricSpace X] {n : ℕ} (hn : n ≤ 2) (D : Chain X n) :
    IsBJChain D := by
  intro i j hij
  exfalso
  have := i.2; have := j.2
  omega

/-- The three links `(0, 2)`, `(1, 3)`, `(2, 4)` of `ℝ`. -/
def real3Chain : Chain ℝ 3 where
  link i := Ioo (i : ℝ) (i + 2)
  isOpen _ := isOpen_Ioo
  adjacent i j := by
    have hi := i.2; have hj := j.2
    constructor
    · rintro ⟨x, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
      have h5 : ((i : ℕ) : ℝ) < j + 2 := by linarith
      have h6 : ((j : ℕ) : ℝ) < i + 2 := by linarith
      have h5' : (i : ℕ) < j + 2 := by exact_mod_cast h5
      have h6' : (j : ℕ) < i + 2 := by exact_mod_cast h6
      omega
    · intro h
      refine ⟨max (i : ℝ) (j : ℝ) + 1 / 2, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · have := le_max_left (i : ℝ) (j : ℝ); linarith
      · have h' : (j : ℕ) ≤ i + 1 := by omega
        have h'' : ((j : ℕ) : ℝ) ≤ i + 1 := by exact_mod_cast h'
        rcases max_cases (i : ℝ) (j : ℝ) with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] <;> linarith
      · have := le_max_right (i : ℝ) (j : ℝ); linarith
      · have h' : (i : ℕ) ≤ j + 1 := by omega
        have h'' : ((i : ℕ) : ℝ) ≤ j + 1 := by exact_mod_cast h'
        rcases max_cases (i : ℝ) (j : ℝ) with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] <;> linarith

/-- `real3Chain` is a chain in the library's sense but not in Bing–Jones's: its outer links
`(0, 2)` and `(2, 4)` are disjoint at distance `0`. -/
theorem not_isBJChain_real3 : ¬ IsBJChain real3Chain := by
  intro h
  obtain ⟨δ, hδ, hd⟩ := h 0 2 (by decide)
  set e := min (δ / 4) (1 / 2)
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he1 : e ≤ 1 / 2 := min_le_right _ _
  have he2 : e ≤ δ / 4 := min_le_left _ _
  have hx : (2 - e : ℝ) ∈ real3Chain.link 0 := by
    show (2 - e : ℝ) ∈ Ioo ((0 : ℕ) : ℝ) ((0 : ℕ) + 2); norm_num; constructor <;> linarith
  have hy : (2 + e : ℝ) ∈ real3Chain.link 2 := by
    show (2 + e : ℝ) ∈ Ioo ((2 : ℕ) : ℝ) ((2 : ℕ) + 2); norm_num; constructor <;> linarith
  have := hd _ hx _ hy
  rw [Real.dist_eq, show (2 - e : ℝ) - (2 + e) = -(2 * e) by ring, abs_neg,
    abs_of_pos (by linarith)] at this
  linarith

/-- **Non-vacuity of Theorem 7**: a plane pseudo-arc, a chain of at least three links in
Bing–Jones's sense covering it, `H = id`, and singletons `A`, `B` meet every hypothesis of
`bj_theorem7` and `bj_theorem7_ends`, and the theorems apply. -/
theorem nonvac_bj_theorem7_ends : ∃ P : Set Pt, IsPseudoArc P ∧ ∃ n, ∃ _ : 3 ≤ n, ∃ D : Chain Pt n,
    IsBJChain D ∧ P ⊆ D.union ∧ (∀ j, (D.link j ∩ P).Nonempty) ∧ ∃ a b : Pt,
      ∃ E : Chain Pt n, IsBJChain E ∧ P ⊆ E.union ∧ (∀ i, (E.link i ∩ P).Nonempty) ∧
        (∀ i, E.link i ⊆ D.link i) ∧ {a} ⊆ E.link ⟨0, by omega⟩ ∧
        {b} ⊆ E.link ⟨n - 1, by omega⟩ := by
  obtain ⟨P, hP, n, hn, D, hD, hPD, hDP⟩ := nonvac_bj_chains
  refine ⟨P, hP, n, hn, D, hD, hPD, hDP, ?_⟩
  obtain ⟨a, haD, haP⟩ := hDP ⟨0, by omega⟩
  obtain ⟨b, hbD, hbP⟩ := hDP ⟨n - 1, by omega⟩
  obtain ⟨E, hE, hPE, hEP, hED, hA, hB⟩ := bj_theorem7_ends hP hn D hPD hDP id
    (fun i j h => h) Function.surjective_id (r := ⟨0, by omega⟩) (s := ⟨n - 1, by omega⟩) rfl rfl
    isClosed_singleton isClosed_singleton
    (singleton_subset_iff.2 ⟨haP, haD⟩) (singleton_subset_iff.2 ⟨hbP, hbD⟩)
  exact ⟨a, b, E, hE, hPE, hEP, hED, hA, hB⟩

end HPC.BJ59
