import HPC.Plane.Ingram68Star

/-!
# Batch 132, Part II: Ingram 1968 (decomposable circle-like continua) and the property (∗);
# Fugate's Corollary 1 proved

Source: W. T. Ingram, *Decomposable circle-like continua*, Fund. Math. 63 (1968), 193–198
(`doc/sources/ingram1968.pdf`); COMMISSION-batch132.md §3 transcribes his proofs. The batch
skeleton is kept as `doc/batches/skeletons/Ingram68-batch132.lean`.

## Route taken: the direct route

(∗) = `IngramStar S` is proved without circle-likeness (COMMISSION-batch132.md §2, "Alternative
route"):
* `HPC/Plane/Ingram68Core.lean`: the core lemma `isTriod_of_core` (a continuum `N` and three arms
  meeting `N`, pairwise meeting only inside `N`, none inside `N`, form a triod), which replaces
  every appeal to Sorgenfrey's theorem; Ingram's Lemma 1 (`ingram_lemma1`), Lemma 2
  (`ingram_lemma2`, irreducibility in the general form `eq_of_subset_of_split`), and the weak
  form (∗∗) (`ingramStarWeak_holds`).
* `HPC/Plane/Ingram68Star.lean`: (∗) itself (`ingramStar_holds`).
* This file: circular chains and circle-likeness, Nadler 12.51
  (`isSnakeLike_of_subset_circleLike`, proved), and `fugate_cor1`, `fugateU_holds`.

Not formalized (commented out below, with the obstruction): Sorgenfrey 1.8 in both forms,
Ingram's Lemma 3, Theorem 1 and Theorem 2(2). None is used by the route.
-/

namespace HPC.Plane

open Set Metric

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ### Circular chains and circle-likeness -/

/-- Cyclic distance on `Fin n`. -/
def cycDist {n : ℕ} (i j : Fin n) : ℕ := min ((i : ℤ) - j).natAbs (n - ((i : ℤ) - j).natAbs)

/-- A **circular chain** of length `n`: open links, `link i` meeting `link j` iff their cyclic
distance is at most `1` (Bing 1951, §1; Ingram's "circular chain"). For `n ≤ 3` every two links
meet. -/
structure CircChain (X : Type*) [MetricSpace X] (n : ℕ) where
  link : Fin n → Set X
  isOpen : ∀ i, IsOpen (link i)
  adjacent : ∀ i j : Fin n, (link i ∩ link j).Nonempty ↔ cycDist i j ≤ 1

/-- The union of the links. -/
def CircChain.union {X : Type*} [MetricSpace X] {n : ℕ} (D : CircChain X n) : Set X :=
  ⋃ i, D.link i

/-- An `ε`-circular chain: bounded links of diameter `< ε`. -/
def IsCircEpsChain {X : Type*} [MetricSpace X] {n : ℕ} (D : CircChain X n) (ε : ℝ) : Prop :=
  ∀ i, Bornology.IsBounded (D.link i) ∧ Metric.diam (D.link i) < ε

/-- **Circle-like** (circularly chainable): a continuum covered by an `ε`-circular chain for every
`ε > 0`. -/
def IsCircleLike {X : Type*} [MetricSpace X] (M : Set X) : Prop :=
  Fold.Q78.IsContinuum M ∧
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : CircChain X n), IsCircEpsChain D ε ∧ M ⊆ D.union

omit [CompactSpace S] in
/-- **Nadler 12.51.** A proper subcontinuum of a circle-like continuum is chainable. Pick
`x ∈ C ∖ Z` and `ε < infDist x Z`. In an `ε`-circular chain covering `C`, a link containing `x`
misses `Z`. The remaining links, read cyclically from the next index, form a chain covering `Z`
(the two neighbours of the removed link have cyclic distance `2` when `n ≥ 4`, and are
consecutive when `n = 3`). Degenerate `Z` is a point and is chainable directly. -/
theorem isSnakeLike_of_subset_circleLike {C Z : Set S} (hC : IsCircleLike C)
    (hZ : Fold.Q78.IsContinuum Z) (hZC : Z ⊆ C) (hne : Z ≠ C) : IsSnakeLike Z := by
  refine ⟨hZ, fun ε hε => ?_⟩
  obtain ⟨x, hxC, hxZ⟩ : ∃ x ∈ C, x ∉ Z := by
    by_contra h
    push_neg at h
    exact hne (Subset.antisymm hZC h)
  have hr : 0 < infDist x Z :=
    (hZ.1.isClosed.notMem_iff_infDist_pos hZ.2.nonempty).1 hxZ
  obtain ⟨n, D, hD, hCD⟩ := hC.2 (min ε (infDist x Z)) (lt_min hε hr)
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.1 (hCD hxC)
  -- the link through `x` misses `Z`
  have hmiss : ∀ z ∈ Z, z ∉ D.link i₀ := fun z hz hz' => by
    have h1 : dist x z ≤ diam (D.link i₀) := dist_le_diam_of_mem (hD i₀).1 hi₀ hz'
    have h2 : infDist x Z ≤ dist x z := infDist_le_dist_of_mem hz
    have h3 := (hD i₀).2
    have h4 := min_le_right ε (infDist x Z)
    linarith
  have hi₀n := i₀.isLt
  -- the remaining links, read cyclically from `i₀ + 1`
  let σ : Fin (n - 1) → Fin n := fun j =>
    ⟨if i₀.val + 1 + j.val < n then i₀.val + 1 + j.val else i₀.val + 1 + j.val - n, by
      have := j.isLt; split_ifs <;> omega⟩
  let D' : Chain S (n - 1) :=
    { link := fun j => D.link (σ j)
      isOpen := fun j => D.isOpen _
      adjacent := fun i j => by
        rw [D.adjacent]
        have hi := i.isLt
        have hj := j.isLt
        unfold cycDist
        simp only [σ]
        split_ifs <;> omega }
  refine ⟨n - 1, D', fun j => ⟨(hD (σ j)).1, (hD (σ j)).2.trans_le (min_le_left _ _)⟩,
    fun z hz => ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hCD (hZC hz))
  have hii : i.val ≠ i₀.val := fun h => hmiss z hz (Fin.ext h ▸ hi)
  have hin := i.isLt
  let j : Fin (n - 1) :=
    ⟨if i₀.val < i.val then i.val - i₀.val - 1 else i.val + n - i₀.val - 1, by split_ifs <;> omega⟩
  have hσj : σ j = i := Fin.ext (by simp only [σ, j]; split_ifs <;> omega)
  exact mem_iUnion.2 ⟨j, show z ∈ D.link (σ j) from hσj ▸ hi⟩

/-! ### Skeleton items not formalized (commented out, batch 132)

The five declarations below are the skeleton's Sorgenfrey 1.8 (two forms), Ingram's Lemma 3,
Theorem 1 and Theorem 2(2). They are kept verbatim, commented out, so that the build carries no
`sorry`. None of them is used: (∗) is proved by the direct route (`HPC/Plane/Ingram68Core.lean`,
`HPC/Plane/Ingram68Star.lean`), which replaces Ingram's appeals to Sorgenfrey in Lemmas 1 and 2 by
`isTriod_of_core`, and needs neither Lemma 3 nor Theorems 1 and 2. Status
(REPORT-batch132.md, OPEN.md):
* `exists_isTriod_of_isWeakTriod`, `not_three_of_isAtriodic` — open. The core construction gives
  a triod only when the three pairwise intersections lie in one continuum not containing the
  arms; for a general weak triod (not unicoherent) no such core is available.
* `ingram_lemma3` — open. The subcase `L₁ ⊄ K`, `L₂ ⊄ K` is a triod with core `K` (arms `L₁`,
  `L₂` and an arm of `B` at `K` missing `L`); the subcase `L₂ ⊆ K` needs a triod in `K ∪ H`,
  where `K ∩ H = (K ∩ L₁) ∪ L₂` is disconnected, i.e. Sorgenfrey's theorem in a
  non-unicoherent configuration.
* `ingram_theorem1`, `ingram_theorem2_circleLike` — not attempted (replaced by the direct route,
  COMMISSION-batch132.md §2 "Alternative route").
-/

/-
/-! ### Sorgenfrey: a weak triod contains a triod -/

/-- **Sorgenfrey 1944, Theorem 1.8** (Ingram's "[7], Theorem 1.8, p. 443"; Bennett–Fugate 1977,
p. 20: "each type 1 triod contains a type 3 triod"). Three continua with a common point, none
contained in the union of the other two: their union contains a triod. `IsWeakTriod` is
`SorgenfreyDefs.lean`'s (Nadler 11.24). Refutation candidate: check the hypotheses against
`isTriod_union_of_three` (which needs hereditary unicoherence and gives the union itself as the
triod); here only *containment* of a triod is claimed. -/
theorem exists_isTriod_of_isWeakTriod {X : Set S} (h : IsWeakTriod X) :
    ∃ T ⊆ X, IsTriod T := by
  sorry

/-- Restated for use: in an atriodic continuum, three subcontinua with a common point cannot all
be outside the union of the other two. -/
theorem not_three_of_isAtriodic {X P Q R : Set S} (hX : IsAtriodic X)
    (hP : Fold.Q78.IsContinuum P) (hQ : Fold.Q78.IsContinuum Q) (hR : Fold.Q78.IsContinuum R)
    (hPX : P ⊆ X) (hQX : Q ⊆ X) (hRX : R ⊆ X) (hcommon : (P ∩ Q ∩ R).Nonempty) :
    P ⊆ Q ∪ R ∨ Q ⊆ P ∪ R ∨ R ⊆ P ∪ Q := by
  sorry

/-! ### Ingram's Lemma 3 -/

/-- **Ingram, Lemma 3.** Suppose `A ∩ B` is the union of two disjoint continua `K`, `L`, and
`A ∪ B` is atriodic. If `H ⊆ A ∪ B` is a continuum that meets `A ∖ K` but not `L`, then `H ∩ A`
is a continuum. -/
theorem ingram_lemma3 {A B K L H : Set S} (hA : Fold.Q78.IsContinuum A)
    (hB : Fold.Q78.IsContinuum B) (hK : Fold.Q78.IsContinuum K) (hL : Fold.Q78.IsContinuum L)
    (hKL : Disjoint K L) (hAB : A ∩ B = K ∪ L) (hat : IsAtriodic (A ∪ B))
    (hH : Fold.Q78.IsContinuum H) (hHAB : H ⊆ A ∪ B) (hHA : (H ∩ (A \ K)).Nonempty)
    (hHL : Disjoint H L) : Fold.Q78.IsContinuum (H ∩ A) := by
  sorry

/-! ### Ingram's Theorem 1 -/

/-- **Ingram, Theorem 1.** If `H` and `K` are disjoint terminal subcontinua of the chainable
continuum `M`, `M` is irreducible about `H ∪ K`, and `ε > 0`, then there is an `ε`-chain
covering `M` whose first link has a point of `H` outside the closure of the other links, and
whose last link has a point of `K` outside the closure of the other links. (Same end-link
convention as `fugate_lemma1`. Ingram's proof uses Fugate's Lemma 1 and Cook's regular-chain
theorem; `exists_taut_epsChain` exists.) -/
theorem ingram_theorem1 {M H K : Set S} (hM : IsSnakeLike M) (hHt : IsTerminalSub M H)
    (hKt : IsTerminalSub M K) (hHK : Disjoint H K) (hirr : IrreducibleAbout M (H ∪ K))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (D : Chain S n) (hn : 0 < n), IsEpsChain D ε ∧ M ⊆ D.union ∧
      (H ∩ (D.link ⟨0, hn⟩ \ closure (⋃ j : Fin n, ⋃ (_ : j.val ≠ 0), D.link j))).Nonempty ∧
      (K ∩ (D.link ⟨n - 1, by omega⟩ \
        closure (⋃ j : Fin n, ⋃ (_ : j.val ≠ n - 1), D.link j))).Nonempty := by
  sorry

/-! ### Ingram's Theorem 2(2), sufficiency, and (∗) -/

/-- **Ingram, Theorem 2(2), sufficiency.** If `Y`, `A` are chainable continua that meet,
`Y ∪ A` is atriodic, and `Y ∩ A` is not connected, then `Y ∪ A` is circle-like. Ingram's
construction is in COMMISSION-batch132.md §3.5. -/
theorem ingram_theorem2_circleLike {Y A : Set S} (hY : IsSnakeLike Y) (hA : IsSnakeLike A)
    (hne : (Y ∩ A).Nonempty) (hat : IsAtriodic (Y ∪ A)) (hnc : ¬ IsConnected (Y ∩ A)) :
    IsCircleLike (Y ∪ A) := by
  sorry
-/

/-- **Fugate 1966, Corollary 1** (p. 467), as stated, every clause. A finite chain of
snake-like continua, consecutive ones meeting: the union is snake-like iff it is atriodic and
unicoherent. Fugate states it without proof. Proved from Theorem 1 and (∗)
(`fugate_cor1_of_ingramStar`, `ingramStar_holds`). (∗) rests on Ingram's Lemmas 1–2 and the
direct route (`Ingram68Core`, `Ingram68Star`); Ingram 1968 postdates Fugate 1966. The sorried
declaration of the same name in `Fugate66.lean` is deleted in this batch
(COMMISSION-batch132.md §2). -/
theorem fugate_cor1 {k : ℕ} (A : Fin (k + 1) → Set S) (hA : ∀ i, IsSnakeLike (A i))
    (hmeet : ∀ i : Fin k, (A i.castSucc ∩ A i.succ).Nonempty) :
    IsSnakeLike (⋃ i, A i) ↔ IsAtriodic (⋃ i, A i) ∧ IsUnicoherent (⋃ i, A i) :=
  fugate_cor1_of_ingramStar ingramStar_holds A hA hmeet

/-- **(U) holds.** -/
theorem fugateU_holds : FugateU S :=
  fugateU_of_ingramStar ingramStar_holds

end HPC.Plane
