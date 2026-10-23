import HPC.PseudoArc.Theorem10

/-!
# Bing 1948, Theorems 5, 6 and 13: statements

Batch 79, target 3. Statements only: each theorem is a `def … : Prop`, so that this file adds no
`sorry`; the next batch proves `∀ Δ, Theorem5Statement Δ` and so on. The auxiliary notions the
statements need are defined here: the re-indexed description `Description.shift`, a pattern
between two indices (`IsPatternFromTo`), a consolidation of a set of links (`IsConsolidationOn`),
the composant of a point, and Bing's subchain `D_i(R, S)` (`IsSubchainFrom`).

Conventions. The repository's descriptions are indexed from `0`: Bing's `D_1, D_2, …` are
`Δ.D 0, Δ.D 1, …`, and Bing's link `d(i)_r` is `(Δ.D (i-1)).link (r-1)`. The mesh bound `1/i` is
the description's `ε i` (any bound tending to `0`). "The closure of each link is a compact subset
of a link" is `Δ.closure_subset` together with `[CompactSpace X]`, which is assumed where
compactness is used.

## `PatternFollowing` versus Theorem 6

`Description.PatternFollowing Δ` asks, for *every* level `i` and every pattern `x` in `Δ.D i`,
for a level `j > i` and a chain from `P` to `Q` consolidating `Δ.D j` and following `x` in
`Δ.D i`. Theorem 6 (`Theorem6Statement Δ`) is the same for level `0` only, and asks for some
level `j`, not necessarily `j > 0`. Re-indexing (`Δ.shift i`, whose level `j` is `Δ.D (i + j)`)
turns one into the other, with two differences recorded as proved statements below:

* `theorem6_shift_of_patternFollowing`: `PatternFollowing Δ` gives Theorem 6 for every shift of
  `Δ` (indeed with `0 < j`).
* `patternFollowing_of_theorem6Pos`: Theorem 6 for every shift, *with `0 < j`* (Bing's proof of
  Theorem 6 produces a deep level, so this is what it gives), gives `PatternFollowing Δ`.

So the only gap between Bing's Theorem 6 as stated and the hypothesis of Theorem 12 is the
requirement `j > i`, and Bing's statement is applied to every tail `D_i, D_{i+1}, …` of the
sequence, which is again a description.
-/

namespace HPC

open Set Metric

variable {X : Type*} [MetricSpace X]

namespace Description

variable {P Q : X}

/-- The tail of a description from level `i`: its level `j` is level `i + j` of `Δ`. -/
def shift (Δ : Description X P Q) (i : ℕ) : Description X P Q where
  n j := Δ.n (i + j)
  D j := Δ.D (i + j)
  isFrom j := Δ.isFrom (i + j)
  crooked j := Δ.crooked (i + j)
  closure_subset j := Δ.closure_subset (i + j)
  ε j := Δ.ε (i + j)
  ε_pos j := Δ.ε_pos (i + j)
  ε_tendsto := Δ.ε_tendsto.comp (Filter.tendsto_atTop_atTop_of_monotone
    (fun a b h => by omega) (fun b => ⟨b, by omega⟩))
  bdd j := Δ.bdd (i + j)
  diam_le j := Δ.diam_le (i + j)

@[simp] theorem shift_n (Δ : Description X P Q) (i j : ℕ) : (Δ.shift i).n j = Δ.n (i + j) := rfl

@[simp] theorem shift_D (Δ : Description X P Q) (i j : ℕ) : (Δ.shift i).D j = Δ.D (i + j) := rfl

/-! ## Theorem 6 -/

/-- **Bing 1948, Theorem 6** (statement). For every pattern `(1, x_1), …, (N, x_N)` in the first
chain `D_1` that starts at its first link and ends at its last (`IsPattern`, steps of at most
one), some `D_j` has a consolidation `E` which is a chain from `P` to `Q` and follows the pattern
in `D_1`. -/
def Theorem6Statement (Δ : Description X P Q) : Prop :=
  ∀ (N : ℕ) (x : Fin N → Fin (Δ.n 0)), IsPattern x →
    ∃ j, ∃ E : Chain X N, E.IsFrom P Q ∧ E.IsConsolidationOf (Δ.D j) ∧
      E.FollowsPattern x (Δ.D 0)

/-- Theorem 6 with a level `j > 0`, which is what Bing's proof produces. -/
def Theorem6PosStatement (Δ : Description X P Q) : Prop :=
  ∀ (N : ℕ) (x : Fin N → Fin (Δ.n 0)), IsPattern x →
    ∃ j, 0 < j ∧ ∃ E : Chain X N, E.IsFrom P Q ∧ E.IsConsolidationOf (Δ.D j) ∧
      E.FollowsPattern x (Δ.D 0)

/-- `PatternFollowing` gives Theorem 6 (with `j > 0`) for every tail of the description. -/
theorem theorem6_shift_of_patternFollowing (Δ : Description X P Q)
    (h : Δ.PatternFollowing) (i : ℕ) : Theorem6PosStatement (Δ.shift i) := by
  intro N x hx
  obtain ⟨j, hij, E, hE1, hE2, hE3⟩ := h i N x hx
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  exact ⟨d, by omega, E, hE1, hE2, hE3⟩

/-- Theorem 6 with `j > 0` for every tail of the description gives `PatternFollowing`. -/
theorem patternFollowing_of_theorem6Pos (Δ : Description X P Q)
    (h : ∀ i, Theorem6PosStatement (Δ.shift i)) : Δ.PatternFollowing := by
  intro i N x hx
  obtain ⟨d, hd, E, hE1, hE2, hE3⟩ := h i N x hx
  exact ⟨i + d, by omega, E, hE1, hE2, hE3⟩

/-! ## Theorem 5 -/

/-- A pattern `(1, x_1), …, (N, x_N)` from index `h` to index `k` (Bing p. 733): `x_1 = h`,
`x_N = k`, `h ≤ x_i ≤ k`, and consecutive values differ by at most one. -/
def IsPatternFromTo {N m : ℕ} (x : Fin N → Fin m) (h k : Fin m) : Prop :=
  ∃ hN : 0 < N, x ⟨0, hN⟩ = h ∧ x ⟨N - 1, by omega⟩ = k ∧ (∀ t, h ≤ x t ∧ x t ≤ k) ∧
    ∀ t t' : Fin N, t'.val = t.val + 1 → ((x t' : ℤ) - (x t : ℤ)).natAbs ≤ 1

/-- `E` is a consolidation of the links `D.link t`, `t ∈ S` (Bing: "a consolidation of the links
of `D_j` contained in …"): each of those links lies in a link of `E`, and each link of `E` is a
union of some of them. -/
def _root_.HPC.Chain.IsConsolidationOn {n m : ℕ} (E : Chain X m) (D : Chain X n)
    (S : Set (Fin n)) : Prop :=
  (∀ t ∈ S, ∃ e, D.link t ⊆ E.link e) ∧ ∀ e, ∃ T ⊆ S, E.link e = ⋃ t ∈ T, D.link t

/-- **Bing 1948, Theorem 5** (statement). Let `x` be a pattern from `h` to `k` in `D_1`.
Suppose the subchain `D_2(u, v)` is contained in the subchain `D_1(h, k)` (every link of
`D_2(u, v)` lies in a link of `D_1(h, k)`), and the closures of `d(2)_u` and `d(2)_v` are
disjoint subsets of `d(1)_h` and `d(1)_k`. Then for every `w` there are `j > w` and a chain `E`
following `x` in `D_1`, which is a consolidation of the links of `D_j` contained in
`D_2(u, v)`, no interior link of which meets `d(2)_u ∪ d(2)_v`.

Here "contained in `D_2(u, v)`" is read as "contained in a link of `D_2(u, v)`". -/
def Theorem5Statement (Δ : Description X P Q) : Prop :=
  ∀ (N : ℕ) (x : Fin N → Fin (Δ.n 0)) (h k : Fin (Δ.n 0)) (u v : Fin (Δ.n 1)),
    IsPatternFromTo x h k → u ≤ v →
    (∀ t : Fin (Δ.n 1), u ≤ t → t ≤ v → ∃ s : Fin (Δ.n 0), h ≤ s ∧ s ≤ k ∧
      (Δ.D 1).link t ⊆ (Δ.D 0).link s) →
    closure ((Δ.D 1).link u) ⊆ (Δ.D 0).link h →
    closure ((Δ.D 1).link v) ⊆ (Δ.D 0).link k →
    Disjoint (closure ((Δ.D 1).link u)) (closure ((Δ.D 1).link v)) →
    ∀ w : ℕ, ∃ j, w < j ∧ ∃ E : Chain X N,
      E.FollowsPattern x (Δ.D 0) ∧
      E.IsConsolidationOn (Δ.D j)
        {t | ∃ s : Fin (Δ.n 1), u ≤ s ∧ s ≤ v ∧ (Δ.D j).link t ⊆ (Δ.D 1).link s} ∧
      ∀ e : Fin N, 0 < e.val → e.val < N - 1 →
        Disjoint (E.link e) ((Δ.D 1).link u ∪ (Δ.D 1).link v)

end Description

/-! ## Theorem 13 and its two auxiliary notions -/

/-- The **composant** of `p` in `M`: the union of all proper subcontinua of `M` containing `p`. -/
def composant (M : Set X) (p : X) : Set X :=
  ⋃₀ {K | Fold.Q78.IsContinuum K ∧ K ⊆ M ∧ K ≠ M ∧ p ∈ K}

namespace Chain

/-- Bing's subchain `D(R, S)` (p. 740): the subchain of `D` from link `a` to link `b` (in
either order of the two points) is a chain from `R` to `S` — `R` lies in its first link and in
no other, `S` in its last and in no other. -/
def IsSubchainFrom {n : ℕ} (D : Chain X n) (a b : Fin n) (R S : X) : Prop :=
  ∃ hab : a ≤ b, (D.sub a b hab).IsFrom R S ∨ (D.sub a b hab).IsFrom S R

end Chain

namespace Description

variable {P Q : X}

/-- **Bing 1948, Theorem 13** (statement): the described continuum `M` is homogeneous — for any
two of its points there is a self-homeomorphism of `M` carrying the first to the second. The
theorem to be proved is `∀ Δ, Theorem13Statement Δ` under `[CompactSpace X]` (as for Theorem 12,
`Description.exists_homeomorph`). -/
def Theorem13Statement (Δ : Description X P Q) : Prop :=
  ∀ (P₁ P₂ : X) (h₁ : P₁ ∈ Δ.M) (h₂ : P₂ ∈ Δ.M), ∃ T : Δ.M ≃ₜ Δ.M, T ⟨P₁, h₁⟩ = ⟨P₂, h₂⟩

end Description

end HPC
