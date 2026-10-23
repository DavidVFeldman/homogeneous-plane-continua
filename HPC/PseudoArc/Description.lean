import HPC.Chains.Basic
import HPC.Chains.Auxiliary

/-!
# Bing's description of a continuum by nested crooked chains

A `Description X P Q` is a sequence of chains from `P` to `Q` in a compact metric space `X`,
each crooked (1948 sense) in its predecessor, with closures of links nested and mesh
tending to zero. `Description.M` is the intersection of the unions. This file records the
elementary properties of a description that Theorem 12 consumes.

English proofs: COMMISSION.md §2.
-/

namespace HPC

open Set Metric

variable {X : Type*} [MetricSpace X]

namespace Chain

/-- A refinement covers no more than the chain it refines. -/
theorem union_subset_of_refines {n m : ℕ} {E : Chain X m} {D : Chain X n} (h : E.Refines D) :
    E.union ⊆ D.union := by
  intro z hz
  simp only [union, mem_iUnion] at hz ⊢
  obtain ⟨t, ht⟩ := hz
  obtain ⟨s, hs⟩ := h t
  exact ⟨s, hs ht⟩

/-- Every chain is a consolidation of itself. -/
theorem isConsolidationOf_self {n : ℕ} (D : Chain X n) : D.IsConsolidationOf D :=
  ⟨fun i => ⟨i, subset_rfl⟩, fun t => ⟨{t}, by simp⟩⟩

end Chain

/-- Bing 1948, "Description of M", p. 730, in the form Theorem 12 uses. -/
structure Description (X : Type*) [MetricSpace X] (P Q : X) where
  /-- number of links at level `i` -/
  n : ℕ → ℕ
  D : (i : ℕ) → Chain X (n i)
  isFrom : ∀ i, (D i).IsFrom P Q
  /-- (1) each level is crooked in the previous one, 1948 sense -/
  crooked : ∀ i, (D (i + 1)).IsCrookedIn' (D i)
  /-- (2) the closure of each link lies in a link of the level above -/
  closure_subset : ∀ i (t : Fin (n (i + 1))), ∃ s, closure ((D (i + 1)).link t) ⊆ (D i).link s
  /-- (3) a mesh bound tending to zero -/
  ε : ℕ → ℝ
  ε_pos : ∀ i, 0 < ε i
  ε_tendsto : Filter.Tendsto ε Filter.atTop (nhds 0)
  bdd : ∀ i (t : Fin (n i)), Bornology.IsBounded ((D i).link t)
  diam_le : ∀ i (t : Fin (n i)), Metric.diam ((D i).link t) ≤ ε i

namespace Description

variable {P Q : X} (Δ : Description X P Q)

/-- The continuum described: the intersection of the unions of the levels. -/
def M : Set X := ⋂ i, (Δ.D i).union

theorem P_mem_M : P ∈ Δ.M := by
  simp only [M, mem_iInter]
  intro i
  obtain ⟨hn, hP, -, -, -⟩ := Δ.isFrom i
  exact mem_iUnion.mpr ⟨_, hP⟩

theorem Q_mem_M : Q ∈ Δ.M := by
  simp only [M, mem_iInter]
  intro i
  obtain ⟨hn, -, hQ, -, -⟩ := Δ.isFrom i
  exact mem_iUnion.mpr ⟨_, hQ⟩

/-- A level whose mesh is below `dist P Q` has at least two links. (A single link could
contain both `P` and `Q` when the mesh is large; `IsFrom` does not forbid it.) -/
theorem two_le_n_of_lt (i : ℕ) (h : Δ.ε i < dist P Q) : 2 ≤ Δ.n i := by
  obtain ⟨hn, hP, hQ, -, -⟩ := Δ.isFrom i
  by_contra hcon
  have hlast : (⟨0, hn⟩ : Fin (Δ.n i)) = ⟨Δ.n i - 1, by omega⟩ := Fin.ext (by omega)
  rw [hlast] at hP
  have h1 := Metric.dist_le_diam_of_mem (Δ.bdd i ⟨Δ.n i - 1, by omega⟩) hP hQ
  have h2 := Δ.diam_le i ⟨Δ.n i - 1, by omega⟩
  linarith

/-- Deeper levels refine shallower ones. -/
theorem refines_of_le {i j : ℕ} (hij : i ≤ j) : (Δ.D j).Refines (Δ.D i) := by
  induction j, hij using Nat.le_induction with
  | base => intro t; exact ⟨t, subset_rfl⟩
  | succ j hij ih =>
      intro t
      obtain ⟨s, hs⟩ := Δ.closure_subset j t
      obtain ⟨u, hu⟩ := ih s
      exact ⟨u, (subset_closure.trans hs).trans hu⟩

/-- The closure of a deeper level's union lies in a shallower level's union. -/
theorem closure_union_subset {i j : ℕ} (hij : i < j) :
    closure (Δ.D j).union ⊆ (Δ.D i).union := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hij' : i ≤ j := by omega
  have hclosed : IsClosed (⋃ t, closure ((Δ.D (j + 1)).link t)) :=
    isClosed_iUnion_of_finite fun t => isClosed_closure
  have hsub : closure (Δ.D (j + 1)).union ⊆ ⋃ t, closure ((Δ.D (j + 1)).link t) := by
    refine closure_minimal ?_ hclosed
    intro z hz
    simp only [Chain.union, mem_iUnion] at hz ⊢
    obtain ⟨t, ht⟩ := hz
    exact ⟨t, subset_closure ht⟩
  refine hsub.trans ?_
  refine iUnion_subset fun t => ?_
  obtain ⟨s, hs⟩ := Δ.closure_subset j t
  refine hs.trans ?_
  obtain ⟨u, hu⟩ := Δ.refines_of_le hij' s
  exact hu.trans (subset_iUnion _ u)

/-- `M` is closed, hence compact when `X` is. -/
theorem isClosed_M : IsClosed Δ.M := by
  have key : Δ.M = ⋂ i, closure ((Δ.D (i + 1)).union) := by
    refine Subset.antisymm ?_ ?_
    · intro z hz
      simp only [M, mem_iInter] at hz ⊢
      exact fun i => subset_closure (hz (i + 1))
    · intro z hz
      simp only [M, mem_iInter] at hz ⊢
      exact fun i => Δ.closure_union_subset (Nat.lt_succ_self i) (hz i)
  rw [key]
  exact isClosed_iInter fun _ => isClosed_closure

theorem isCompact_M [CompactSpace X] : IsCompact Δ.M := Δ.isClosed_M.isCompact

/-- Every deeper level is crooked (1948 sense) in every shallower one. Batch-1 T5. -/
theorem crooked_of_lt {i j : ℕ} (hij : i < j) : (Δ.D j).IsCrookedIn' (Δ.D i) :=
  Chain.isCrookedIn'_of_refines (Δ.refines_of_le hij) (Δ.crooked i)

/-- The *closure*-refinement map from level `i+1` to level `i` — the index `s` with
`closure (link t) ⊆ (D i).link s` supplied by `closure_subset` — sends the first link to the
first and the last to the last, and moves by at most one between adjacent indices; hence it
hits every index of level `i`. So every link of level `i` contains the closure of a link of
level `i+1`. -/
theorem exists_closure_link_subset (i : ℕ) (s : Fin (Δ.n i)) :
    ∃ t : Fin (Δ.n (i + 1)), closure ((Δ.D (i + 1)).link t) ⊆ (Δ.D i).link s := by
  classical
  choose χ hχ using Δ.closure_subset i
  have hsub : ∀ t, (Δ.D (i + 1)).link t ⊆ (Δ.D i).link (χ t) :=
    fun t => subset_closure.trans (hχ t)
  obtain ⟨hn1, hP1, hQ1, -, -⟩ := Δ.isFrom (i + 1)
  obtain ⟨hn, -, -, hPu, hQu⟩ := Δ.isFrom i
  have h0 : χ ⟨0, hn1⟩ = ⟨0, hn⟩ := hPu _ (hsub _ hP1)
  have hlast : χ ⟨Δ.n (i + 1) - 1, by omega⟩ = ⟨Δ.n i - 1, by omega⟩ := hQu _ (hsub _ hQ1)
  rcases Nat.eq_zero_or_pos s.val with hs0 | hs0
  · refine ⟨⟨0, hn1⟩, ?_⟩
    have : s = ⟨0, hn⟩ := Fin.ext (by omega)
    rw [this, ← h0]
    exact hχ _
  · obtain ⟨x, y, -, hx, -⟩ :=
      Chain.exists_value_between χ hsub (r := ⟨Δ.n (i + 1) - 1, by omega⟩) (s := ⟨0, hn1⟩)
        (p := s) (q := ⟨0, hn⟩) (by rw [hlast]; have := s.isLt; simp only []; omega)
        (by rw [h0]) (by simp only []; omega)
    exact ⟨x, by rw [← hx]; exact hχ x⟩

/-- **Every link of every level meets `M`.** Needed for condition (2) of Theorem 11; not
stated by Bing. Nested closures of links, by `exists_closure_link_subset`, and compactness. -/
theorem link_inter_M_nonempty [CompactSpace X] (i : ℕ) (s : Fin (Δ.n i)) :
    ((Δ.D i).link s ∩ Δ.M).Nonempty := by
  classical
  choose g hg using fun (k : ℕ) (u : Fin (Δ.n (i + k))) => Δ.exists_closure_link_subset (i + k) u
  set F : (k : ℕ) → Fin (Δ.n (i + k)) :=
    fun k => Nat.rec (motive := fun k => Fin (Δ.n (i + k))) s (fun k u => g k u) k with hF
  set K : ℕ → Set X := fun k => closure ((Δ.D (i + k)).link (F k)) with hK
  have hstep : ∀ k, K (k + 1) ⊆ (Δ.D (i + k)).link (F k) := fun k => hg k (F k)
  have hnested : ∀ k, K (k + 1) ⊆ K k := fun k => (hstep k).trans subset_closure
  have hne : ∀ k, (K k).Nonempty :=
    fun k => ((Δ.D (i + k)).link_nonempty (F k)).mono subset_closure
  have hclosed : ∀ k, IsClosed (K k) := fun k => isClosed_closure
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hnested
    hne (hclosed 0).isCompact hclosed
  simp only [mem_iInter] at hz
  have hz0 : z ∈ (Δ.D i).link s := hstep 0 (hz 1)
  refine ⟨z, hz0, ?_⟩
  have hzi : z ∈ (Δ.D i).union := mem_iUnion.mpr ⟨s, hz0⟩
  simp only [M, mem_iInter]
  intro j
  rcases le_or_gt i j with hij | hij
  · obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
    exact mem_iUnion.mpr ⟨F k, hstep k (hz (k + 1))⟩
  · exact Chain.union_subset_of_refines (Δ.refines_of_le hij.le) hzi

/-- Every level covers `M`. -/
theorem M_subset_union (i : ℕ) : Δ.M ⊆ (Δ.D i).union := iInter_subset _ i

/-- `M` is bounded: it is covered by the finitely many links of any level. -/
theorem isBounded_M : Bornology.IsBounded Δ.M := by
  refine Bornology.IsBounded.subset ?_ (Δ.M_subset_union 0)
  exact Bornology.isBounded_iUnion.mpr fun i => Δ.bdd 0 i

/-- The number of links tends to infinity when `P ≠ Q`. Batch-1 T7 with `diam M ≥ dist P Q`. -/
theorem n_tendsto_atTop (hPQ : P ≠ Q) : Filter.Tendsto Δ.n Filter.atTop Filter.atTop := by
  have hd : 0 < dist P Q := dist_pos.mpr hPQ
  have hdiam : dist P Q ≤ Metric.diam Δ.M :=
    Metric.dist_le_diam_of_mem Δ.isBounded_M Δ.P_mem_M Δ.Q_mem_M
  have hbound : ∀ i, dist P Q ≤ (Δ.n i : ℝ) * (2 * Δ.ε i) := by
    intro i
    refine hdiam.trans ?_
    refine Chain.diam_le_length_mul Δ.isBounded_M (Δ.D i) (Δ.M_subset_union i) (2 * Δ.ε i)
      (Δ.bdd i) fun t => ?_
    have := Δ.diam_le i t
    have := Δ.ε_pos i
    linarith
  rw [← tendsto_natCast_atTop_iff (R := ℝ)]
  refine Filter.tendsto_atTop.mpr fun b => ?_
  have hb : (0 : ℝ) < |b| + 1 := by positivity
  have hev : ∀ᶠ i in Filter.atTop, Δ.ε i < dist P Q / (2 * (|b| + 1)) :=
    Filter.Tendsto.eventually_lt_const (by positivity) Δ.ε_tendsto
  filter_upwards [hev] with i hi
  have h1 := hbound i
  have h2 := Δ.ε_pos i
  have h3 : 2 * Δ.ε i * (|b| + 1) < dist P Q := by
    rw [lt_div_iff₀ (by positivity)] at hi
    linarith
  have h4 : (b : ℝ) ≤ |b| := le_abs_self b
  nlinarith

/-- Given a consolidation `Y` of some level `j` and `δ > 0`, some deeper level refines `Y` and
has mesh at most `δ`. -/
theorem exists_level_refining {m : ℕ} {Y : Chain X m} {j : ℕ}
    (hY : Y.IsConsolidationOf (Δ.D j)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k, j ≤ k ∧ (Δ.D k).Refines Y ∧ Δ.ε k ≤ δ := by
  have hev : ∀ᶠ k in Filter.atTop, Δ.ε k < δ :=
    Filter.Tendsto.eventually_lt_const hδ Δ.ε_tendsto
  obtain ⟨k, hk1, hk2⟩ := (hev.and (Filter.eventually_ge_atTop j)).exists
  exact ⟨k, hk2, (Δ.refines_of_le hk2).trans hY.1, hk1.le⟩

/-- A pattern in a chain of `m` links: starts at the first link, ends at the last, steps by at
most one. -/
def IsPattern {N m : ℕ} (x : Fin N → Fin m) : Prop :=
  ∃ hN : 0 < N, ∃ hm : 0 < m,
    x ⟨0, hN⟩ = ⟨0, hm⟩ ∧ x ⟨N - 1, by omega⟩ = ⟨m - 1, by omega⟩ ∧
    ∀ t : Fin N, ∀ t' : Fin N, t'.val = t.val + 1 → ((x t' : ℤ) - (x t : ℤ)).natAbs ≤ 1

/-- **Pattern following** (Bing 1948, Theorem 6), stated as a property of a description:
for every level `i` and every pattern in `D i`, some deeper level has a consolidation from
`P` to `Q` following the pattern in `D i`. This is the hypothesis under which Theorem 12 is
proved in batch 3; it is to be discharged in a later batch. -/
def PatternFollowing : Prop :=
  ∀ (i N : ℕ) (x : Fin N → Fin (Δ.n i)), IsPattern x →
    ∃ j, i < j ∧ ∃ E : Chain X N, E.IsFrom P Q ∧ E.IsConsolidationOf (Δ.D j) ∧
      E.FollowsPattern x (Δ.D i)

end Description

end HPC
