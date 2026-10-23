import Mathlib
import HPC.Chains.Auxiliary

/-!
# Chains: definitions and elementary crookedness lemmas

Batch 1 of the homogeneous-plane-continua development. English proofs for every theorem
are in COMMISSION.md §3, keyed by the same T-numbers. Statements are the specification;
proofs are the work.
-/

namespace HPC

open Set

variable {X : Type*} [MetricSpace X]

/-- **D1.** A chain of length `n`: open links, with `link i` meeting `link j` iff `|i - j| ≤ 1`.
Links are not assumed connected. Taking `i = j` in `adjacent` shows every link is nonempty. -/
structure Chain (X : Type*) [MetricSpace X] (n : ℕ) where
  link : Fin n → Set X
  isOpen : ∀ i, IsOpen (link i)
  adjacent : ∀ i j : Fin n, (link i ∩ link j).Nonempty ↔ ((i : ℤ) - (j : ℤ)).natAbs ≤ 1

namespace Chain

variable {n m l : ℕ}

/-- **D2.** The union of the links. -/
def union (D : Chain X n) : Set X := ⋃ i, D.link i

/-- Every link of a chain is nonempty (from `adjacent` with `i = j`). Part of **T1**. -/
theorem link_nonempty (D : Chain X n) (i : Fin n) : (D.link i).Nonempty := by
  have h := (D.adjacent i i).mpr (by simp)
  simpa using h

/-- Adjacency, restated on the natural-number values of the indices. -/
theorem adjacent_iff (D : Chain X n) (i j : Fin n) :
    (D.link i ∩ D.link j).Nonempty ↔ (i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1) := by
  rw [D.adjacent]
  omega

/-- **D3.** The subchain from index `i` to index `j` (inclusive), for `i ≤ j`.
Part of **T1**: this is a chain. -/
def sub (D : Chain X n) (i j : Fin n) (hij : i ≤ j) : Chain X (j.val - i.val + 1) where
  link t := D.link ⟨i.val + t.val, by omega⟩
  isOpen t := D.isOpen _
  adjacent := by
    intro t u
    rw [D.adjacent_iff]
    simp only []
    omega

/-- Part of **T1**: the union of a subchain lies in the union of the chain. -/
theorem sub_union_subset (D : Chain X n) (i j : Fin n) (hij : i ≤ j) :
    (D.sub i j hij).union ⊆ D.union := by
  intro z hz
  simp only [union, mem_iUnion] at hz ⊢
  obtain ⟨t, ht⟩ := hz
  exact ⟨_, ht⟩

/-- **D4.** A chain from `P` to `Q`: `P` in the first link only, `Q` in the last link only. -/
def IsFrom (D : Chain X n) (P Q : X) : Prop :=
  ∃ hn : 0 < n,
    P ∈ D.link ⟨0, hn⟩ ∧ Q ∈ D.link ⟨n - 1, by omega⟩ ∧
    (∀ i, P ∈ D.link i → i = ⟨0, hn⟩) ∧ (∀ i, Q ∈ D.link i → i = ⟨n - 1, by omega⟩)

/-- **D5.** `E` refines `D`: every link of `E` lies inside some link of `D`.
Bing: "D contains E". -/
def Refines (E : Chain X m) (D : Chain X n) : Prop :=
  ∀ i, ∃ j, E.link i ⊆ D.link j

/-- **D6.** `F` is a consolidation of `D`: `D` refines `F` and every link of `F` is a union of
links of `D`. -/
def IsConsolidationOf (F : Chain X m) (D : Chain X n) : Prop :=
  D.Refines F ∧ ∀ t, ∃ S : Set (Fin n), F.link t = ⋃ i ∈ S, D.link i

/-- **D7.** `D` follows the pattern `x` in `E`: `D.link i ⊆ E.link (x i)`. -/
def FollowsPattern (D : Chain X n) (x : Fin n → Fin m) (E : Chain X m) : Prop :=
  ∀ i, D.link i ⊆ E.link (x i)

/-- The three-piece order condition shared by both crookedness definitions:
`r` and `s` lie strictly between `i` and `j`, with `r` nearer `i`. -/
def Between (i r s j : Fin m) : Prop :=
  (i < r ∧ r < s ∧ s < j) ∨ (i > r ∧ r > s ∧ s > j)

/-- **D8.** Crookedness, 1951 form (Bing, *Concerning hereditarily indecomposable continua*, §2).
For links of `E` *contained in* `D.link h` and `D.link k` with `k - h > 2`, there are links of
`E` between them, in reversed order, contained in `D.link (k-1)` and `D.link (h+1)`. -/
def IsCrookedIn (E : Chain X m) (D : Chain X n) : Prop :=
  E.Refines D ∧
  ∀ (h k : Fin n) (_hk : h.val + 2 < k.val),
    ∀ (i j : Fin m), E.link i ⊆ D.link h → E.link j ⊆ D.link k →
      ∃ (r s : Fin m), Between i r s j ∧
        E.link r ⊆ D.link ⟨k.val - 1, by omega⟩ ∧
        E.link s ⊆ D.link ⟨h.val + 1, by omega⟩

/-- **D9.** Crookedness, 1948 form (Bing, *A homogeneous indecomposable plane continuum*, §1).
Same conclusion as `IsCrookedIn`, but the hypothesis is that the links of `E` *meet*
`D.link h` and `D.link k` rather than lie inside them. Bing's phrasing via a decomposition
`E(i,j) = E(i,r) ∪ E(r,s) ∪ E(s,j)` with `(s-r)(j-i) > 0` is the same condition as `Between`. -/
def IsCrookedIn' (E : Chain X m) (D : Chain X n) : Prop :=
  E.Refines D ∧
  ∀ (h k : Fin n) (_hk : h.val + 2 < k.val),
    ∀ (i j : Fin m), (E.link i ∩ D.link h).Nonempty → (E.link j ∩ D.link k).Nonempty →
      ∃ (r s : Fin m), Between i r s j ∧
        E.link r ⊆ D.link ⟨k.val - 1, by omega⟩ ∧
        E.link s ⊆ D.link ⟨h.val + 1, by omega⟩

/-! ### Auxiliary machinery for refinements

These lemmas are not part of the commissioned statement list; they are the tools used in the
proofs of T2, T4 and T5. -/

/-- A choice of refining index: `E.link i ⊆ D.link (refineIdx h i)`. -/
noncomputable def refineIdx {E : Chain X m} {D : Chain X n} (h : E.Refines D) (i : Fin m) :
    Fin n := (h i).choose

theorem refineIdx_subset {E : Chain X m} {D : Chain X n} (h : E.Refines D) (i : Fin m) :
    E.link i ⊆ D.link (refineIdx h i) := (h i).choose_spec

theorem Refines.trans {F : Chain X l} {E : Chain X m} {D : Chain X n}
    (hFE : F.Refines E) (hED : E.Refines D) : F.Refines D := by
  intro i
  obtain ⟨u, hu⟩ := hFE i
  obtain ⟨v, hv⟩ := hED u
  exact ⟨v, hu.trans hv⟩

/-- A refinement map is `1`-Lipschitz on adjacent indices: links of `F` that meet are sent to
links of `E` that meet, hence to indices at distance at most one. -/
theorem pattern_lipschitz {F : Chain X l} {E : Chain X m} {φ : Fin l → Fin m}
    (hφ : ∀ t, F.link t ⊆ E.link (φ t)) (i j : Fin l)
    (hij : (F.link i ∩ F.link j).Nonempty) : ((φ i : ℤ) - (φ j : ℤ)).natAbs ≤ 1 := by
  refine (E.adjacent _ _).mp ?_
  obtain ⟨z, hz1, hz2⟩ := hij
  exact ⟨z, hφ i hz1, hφ j hz2⟩

/-- **Transfer of the `Between` condition along a refinement.**  If every link of `F` lies in the
link of `E` named by `φ`, and `r`, `s` lie between `φ i` and `φ j` in the sense of `Between`,
then `φ` takes the values `r` and `s` at two indices lying between `i` and `j`, in the
corresponding order.  This is the discrete intermediate value theorem
`HPC.exists_step_between_gen` transported to chains. -/
theorem exists_between_of_pattern {F : Chain X l} {E : Chain X m} (φ : Fin l → Fin m)
    (hφ : ∀ t, F.link t ⊆ E.link (φ t)) {i j : Fin l} {r s : Fin m}
    (hb : Between (φ i) r s (φ j)) :
    ∃ x y : Fin l, Between i x y j ∧ φ x = r ∧ φ y = s := by
  have hl : 0 < l := i.pos
  set c : ℕ → Fin l := fun t => ⟨min t (l - 1), by omega⟩ with hc
  set g : ℕ → ℤ := fun t => ((φ (c t) : Fin m) : ℤ) with hg
  have hcval : ∀ t : Fin l, c t.val = t := by
    intro t
    have : min t.val (l - 1) = t.val := by omega
    exact Fin.ext (by simpa [hc] using this)
  have hstep : ∀ t, |g (t + 1) - g t| ≤ 1 := by
    intro t
    have hadj : (F.link (c (t + 1)) ∩ F.link (c t)).Nonempty := by
      rw [F.adjacent_iff]
      simp only [hc]
      omega
    have h := pattern_lipschitz hφ (c (t + 1)) (c t) hadj
    rw [abs_le]
    simp only [hg]
    omega
  have hbz : (g i.val < (r : ℤ) ∧ (r : ℤ) < (s : ℤ) ∧ (s : ℤ) < g j.val) ∨
      (g j.val < (s : ℤ) ∧ (s : ℤ) < (r : ℤ) ∧ (r : ℤ) < g i.val) := by
    have hi : g i.val = ((φ i : Fin m) : ℤ) := by rw [hg]; simp only [hcval i]
    have hj : g j.val = ((φ j : Fin m) : ℤ) := by rw [hg]; simp only [hcval j]
    rw [hi, hj]
    rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
    · exact Or.inr ⟨by exact_mod_cast h3, by exact_mod_cast h2, by exact_mod_cast h1⟩
  obtain ⟨x, y, hbn, hx, hy⟩ := exists_step_between_gen hstep hbz
  simp only [BetweenN] at hbn
  have hil := i.isLt
  have hjl := j.isLt
  have hxl : x < l := by rcases hbn with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega
  have hyl : y < l := by rcases hbn with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega
  have hcx : c x = ⟨x, hxl⟩ := Fin.ext (by simp only [hc]; omega)
  have hcy : c y = ⟨y, hyl⟩ := Fin.ext (by simp only [hc]; omega)
  refine ⟨⟨x, hxl⟩, ⟨y, hyl⟩, ?_, ?_, ?_⟩
  · rcases hbn with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h3, h2, h1⟩
  · have : ((φ ⟨x, hxl⟩ : Fin m) : ℤ) = (r : ℤ) := by rw [← hx, hg]; simp only [hcx]
    exact Fin.ext (by exact_mod_cast this)
  · have : ((φ ⟨y, hyl⟩ : Fin m) : ℤ) = (s : ℤ) := by rw [← hy, hg]; simp only [hcy]
    exact Fin.ext (by exact_mod_cast this)

/-- Reversing the roles of the two ends of a `Between` configuration. -/
theorem Between.symm {i r s j : Fin m} (h : Between i r s j) : Between j s r i := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inr ⟨h3, h2, h1⟩
  · exact Or.inl ⟨h3, h2, h1⟩

/-- **Interpolation along a chain.**  If every link of `F` lies in the link of `D` named by
`χ`, the index `χ r` is at least `p` and the index `χ s` is at most `q < p`, then `χ` takes the
values `p` and `q` at two indices in the closed interval from `r` to `s`, the value `p` first.
This is the one-sided discrete intermediate value theorem `HPC.exists_step_le_between_gen`
transported to chains. -/
theorem exists_value_between {F : Chain X l} {D : Chain X n} (χ : Fin l → Fin n)
    (hχ : ∀ t, F.link t ⊆ D.link (χ t)) {r s : Fin l} {p q : Fin n}
    (hp : (p : ℕ) ≤ ((χ r : Fin n) : ℕ)) (hq : ((χ s : Fin n) : ℕ) ≤ (q : ℕ))
    (hqp : (q : ℕ) < (p : ℕ)) :
    ∃ x y : Fin l, ((r ≤ x ∧ x < y ∧ y ≤ s) ∨ (s ≤ y ∧ y < x ∧ x ≤ r)) ∧ χ x = p ∧ χ y = q := by
  have hl : 0 < l := r.pos
  set c : ℕ → Fin l := fun t => ⟨min t (l - 1), by omega⟩ with hc
  set g : ℕ → ℤ := fun t => ((χ (c t) : Fin n) : ℤ) with hg
  have hcval : ∀ t : Fin l, c t.val = t := by
    intro t
    have : min t.val (l - 1) = t.val := by omega
    exact Fin.ext (by simpa [hc] using this)
  have hstep : ∀ t, |g (t + 1) - g t| ≤ 1 := by
    intro t
    have hadj : (F.link (c (t + 1)) ∩ F.link (c t)).Nonempty := by
      rw [F.adjacent_iff]
      simp only [hc]
      omega
    have hlip := pattern_lipschitz hχ (c (t + 1)) (c t) hadj
    rw [abs_le]
    simp only [hg]
    omega
  have hgr : g r.val = ((χ r : Fin n) : ℤ) := by rw [hg]; simp only [hcval r]
  have hgs : g s.val = ((χ s : Fin n) : ℤ) := by rw [hg]; simp only [hcval s]
  obtain ⟨x, y, hxy, hgx, hgy⟩ :=
    exists_step_le_between_gen (g := g) hstep (i := r.val) (j := s.val) (p := (p : ℤ))
      (q := (q : ℤ)) (by exact_mod_cast hqp) (by rw [hgr]; exact_mod_cast hp)
      (by rw [hgs]; exact_mod_cast hq)
  have hrl := r.isLt
  have hsl := s.isLt
  have hxl : x < l := by rcases hxy with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega
  have hyl : y < l := by rcases hxy with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega
  have hcx : c x = ⟨x, hxl⟩ := Fin.ext (by simp only [hc]; omega)
  have hcy : c y = ⟨y, hyl⟩ := Fin.ext (by simp only [hc]; omega)
  refine ⟨⟨x, hxl⟩, ⟨y, hyl⟩, ?_, ?_, ?_⟩
  · rcases hxy with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2, h3⟩
  · have hval : ((χ ⟨x, hxl⟩ : Fin n) : ℤ) = (p : ℤ) := by rw [← hgx, hg]; simp only [hcx]
    exact Fin.ext (by exact_mod_cast hval)
  · have hval : ((χ ⟨y, hyl⟩ : Fin n) : ℤ) = (q : ℤ) := by rw [← hgy, hg]; simp only [hcy]
    exact Fin.ext (by exact_mod_cast hval)

/-- If a link of `E` inside `D.link h` and a link of `E` inside `D.link k` are at distance at
most two in `E`, then `h` and `k` are at distance at most two in `D`. -/
theorem index_dist_le_of_subset {E : Chain X m} {D : Chain X n} (hED : E.Refines D)
    {a b : Fin m} {h k : Fin n} (ha : E.link a ⊆ D.link h) (hb : E.link b ⊆ D.link k)
    (hab : ((a : ℤ) - (b : ℤ)).natAbs ≤ 2) : ((h : ℤ) - (k : ℤ)).natAbs ≤ 2 := by
  by_cases h1 : ((a : ℤ) - (b : ℤ)).natAbs ≤ 1
  · obtain ⟨z, hz1, hz2⟩ := (E.adjacent a b).mpr h1
    have := (D.adjacent h k).mp ⟨z, ha hz1, hb hz2⟩
    omega
  · have hal := a.isLt
    have hbl := b.isLt
    have hcl : min a.val b.val + 1 < m := by omega
    set c : Fin m := ⟨min a.val b.val + 1, hcl⟩ with hcdef
    have hca : ((c : ℤ) - (a : ℤ)).natAbs ≤ 1 := by simp only [hcdef]; omega
    have hcb : ((c : ℤ) - (b : ℤ)).natAbs ≤ 1 := by simp only [hcdef]; omega
    obtain ⟨z1, hz11, hz12⟩ := (E.adjacent c a).mpr hca
    obtain ⟨z2, hz21, hz22⟩ := (E.adjacent c b).mpr hcb
    have k1 := (D.adjacent (refineIdx hED c) h).mp ⟨z1, refineIdx_subset hED c hz11, ha hz12⟩
    have k2 := (D.adjacent (refineIdx hED c) k).mp ⟨z2, refineIdx_subset hED c hz21, hb hz22⟩
    omega

/-- **T2.** The 1948 notion implies the 1951 notion. -/
theorem IsCrookedIn'.isCrookedIn {E : Chain X m} {D : Chain X n} (h : E.IsCrookedIn' D) :
    E.IsCrookedIn D := by
  obtain ⟨hR, hC⟩ := h
  refine ⟨hR, ?_⟩
  intro a b hab i j hi hj
  refine hC a b hab i j ?_ ?_
  · obtain ⟨z, hz⟩ := E.link_nonempty i
    exact ⟨z, hz, hi hz⟩
  · obtain ⟨z, hz⟩ := E.link_nonempty j
    exact ⟨z, hz, hj hz⟩

/-- **T4** (Bing 1948, Theorem 1). Crookedness passes down a consolidation. -/
theorem isCrookedIn'_of_isConsolidationOf {D : Chain X n} {E : Chain X m} {F : Chain X l}
    (hDE : D.IsConsolidationOf E) (hFE : F.IsCrookedIn' E) : F.IsCrookedIn' D := by
  classical
  obtain ⟨hED, hDblocks⟩ := hDE
  obtain ⟨hFER, hFEC⟩ := hFE
  have hFD : F.Refines D := hFER.trans hED
  refine ⟨hFD, ?_⟩
  intro h k hk i j hi hj
  -- a link of `E` inside `D.link h` meeting `F.link i`, and one inside `D.link k` meeting
  -- `F.link j`
  have hpick : ∀ (t : Fin n) (x : Fin l), (F.link x ∩ D.link t).Nonempty →
      ∃ a : Fin m, E.link a ⊆ D.link t ∧ (F.link x ∩ E.link a).Nonempty := by
    intro t x hx
    obtain ⟨z, hz1, hz2⟩ := hx
    obtain ⟨S, hS⟩ := hDblocks t
    rw [hS] at hz2
    simp only [Set.mem_iUnion, exists_prop] at hz2
    obtain ⟨a, haS, hza⟩ := hz2
    exact ⟨a, by rw [hS]; exact Set.subset_biUnion_of_mem haS, ⟨z, hz1, hza⟩⟩
  obtain ⟨a, ha, hai⟩ := hpick h i hi
  obtain ⟨b, hb, hbj⟩ := hpick k j hj
  -- those two links of `E` are more than two apart
  have hab : ¬((a : ℤ) - (b : ℤ)).natAbs ≤ 2 := by
    intro hcon
    have := index_dist_le_of_subset hED ha hb hcon
    omega
  -- crookedness of `F` in `E` applied to that pair
  obtain ⟨r, s, hbtw, ⟨b', hb'b, hrb'⟩, a', ha'a, hsa'⟩ :
      ∃ r s : Fin l, Between i r s j ∧
        (∃ b' : Fin m, ((b' : ℤ) - (b : ℤ)).natAbs ≤ 1 ∧ F.link r ⊆ E.link b') ∧
        (∃ a' : Fin m, ((a' : ℤ) - (a : ℤ)).natAbs ≤ 1 ∧ F.link s ⊆ E.link a') := by
    have hal := a.isLt
    have hbl := b.isLt
    rcases lt_or_gt_of_ne (show a.val ≠ b.val by omega) with hlt | hgt
    · obtain ⟨r, s, hbtw, hr, hs⟩ := hFEC a b (by omega) i j hai hbj
      exact ⟨r, s, hbtw, ⟨⟨b.val - 1, by omega⟩, by simp only []; omega, hr⟩,
        ⟨⟨a.val + 1, by omega⟩, by simp only []; omega, hs⟩⟩
    · obtain ⟨r, s, hbtw, hr, hs⟩ := hFEC b a (by omega) j i hbj hai
      exact ⟨s, r, hbtw.symm, ⟨⟨b.val + 1, by omega⟩, by simp only []; omega, hs⟩,
        ⟨⟨a.val - 1, by omega⟩, by simp only []; omega, hr⟩⟩
  -- the `D`-indices of those two links of `E`
  have hψ : ∀ c, E.link c ⊆ D.link (refineIdx hED c) := refineIdx_subset hED
  have hPk : ((refineIdx hED b' : ℤ) - (k : ℤ)).natAbs ≤ 1 := by
    obtain ⟨z, hz1, hz2⟩ := (E.adjacent b' b).mpr hb'b
    exact (D.adjacent _ _).mp ⟨z, hψ b' hz1, hb hz2⟩
  have hQh : ((refineIdx hED a' : ℤ) - (h : ℤ)).natAbs ≤ 1 := by
    obtain ⟨z, hz1, hz2⟩ := (E.adjacent a' a).mpr ha'a
    exact (D.adjacent _ _).mp ⟨z, hψ a' hz1, ha hz2⟩
  -- a refinement map for `F` in `D` with prescribed values at `r` and `s`
  have hrs : r ≠ s := by
    rcases hbtw with ⟨-, h2, -⟩ | ⟨-, h2, -⟩
    · exact ne_of_lt h2
    · exact ne_of_gt h2
  set χ : Fin l → Fin n := fun t =>
    if t = r then refineIdx hED b' else if t = s then refineIdx hED a' else refineIdx hFD t
    with hχdef
  have hχr : χ r = refineIdx hED b' := by simp [hχdef]
  have hχs : χ s = refineIdx hED a' := by simp [hχdef, hrs.symm]
  have hχ : ∀ t, F.link t ⊆ D.link (χ t) := by
    intro t
    by_cases h1 : t = r
    · subst h1
      rw [hχr]
      exact hrb'.trans (hψ b')
    · by_cases h2 : t = s
      · subst h2
        rw [hχs]
        exact hsa'.trans (hψ a')
      · have : χ t = refineIdx hFD t := by simp [hχdef, h1, h2]
        rw [this]
        exact refineIdx_subset hFD t
  -- interpolate: `F` reaches `D.link (k-1)` and then `D.link (h+1)` between `r` and `s`
  have hkv := k.isLt
  have hhv := h.isLt
  obtain ⟨x, y, hxy, hx, hy⟩ :=
    exists_value_between χ hχ (r := r) (s := s) (p := ⟨k.val - 1, by omega⟩)
      (q := ⟨h.val + 1, by omega⟩) (by rw [hχr]; simp only []; omega)
      (by rw [hχs]; simp only []; omega) (by simp only []; omega)
  refine ⟨x, y, ?_, ?_, ?_⟩
  · rcases hbtw with ⟨t1, t2, t3⟩ | ⟨t1, t2, t3⟩ <;> rcases hxy with ⟨u1, u2, u3⟩ | ⟨u1, u2, u3⟩
    · exact Or.inl ⟨lt_of_lt_of_le t1 u1, u2, lt_of_le_of_lt u3 t3⟩
    · exact absurd t2 (not_lt.mpr (u1.trans ((u2.le).trans u3)))
    · exact absurd t2 (not_lt.mpr (u1.trans ((u2.le).trans u3)))
    · exact Or.inr ⟨lt_of_le_of_lt u3 t1, u2, lt_of_lt_of_le t3 u1⟩
  · rw [← hx]
    exact hχ x
  · rw [← hy]
    exact hχ y

/-- **T5** (Bing 1948, Theorem 2). Crookedness passes down a refinement. -/
theorem isCrookedIn'_of_refines {D : Chain X n} {E : Chain X m} {F : Chain X l}
    (hFE : F.Refines E) (hED : E.IsCrookedIn' D) : F.IsCrookedIn' D := by
  obtain ⟨hER, hEC⟩ := hED
  refine ⟨hFE.trans hER, ?_⟩
  intro a b hab i j hi hj
  have hφ : ∀ t, F.link t ⊆ E.link (refineIdx hFE t) := refineIdx_subset hFE
  have hu : (E.link (refineIdx hFE i) ∩ D.link a).Nonempty := by
    obtain ⟨z, hz1, hz2⟩ := hi
    exact ⟨z, hφ i hz1, hz2⟩
  have hv : (E.link (refineIdx hFE j) ∩ D.link b).Nonempty := by
    obtain ⟨z, hz1, hz2⟩ := hj
    exact ⟨z, hφ j hz1, hz2⟩
  obtain ⟨r, s, hb, hr, hs⟩ := hEC a b hab _ _ hu hv
  obtain ⟨x, y, hbxy, hx, hy⟩ := exists_between_of_pattern (refineIdx hFE) hφ hb
  exact ⟨x, y, hbxy, (hφ x).trans (hx ▸ hr), (hφ y).trans (hy ▸ hs)⟩

/-- **T5′** (Bing 1948, Corollary to Theorem 2). -/
theorem isCrookedIn'_of_isConsolidationOf' {D : Chain X n} {E : Chain X m} {F : Chain X l}
    (hED : E.IsCrookedIn' D) (hEF : E.IsConsolidationOf F) : F.IsCrookedIn' D :=
  isCrookedIn'_of_refines hEF.1 hED

/-- **T6.** A chain from `P` to `Q` of length `n` consolidates, still from `P` to `Q`, to any
length `m` with `2 ≤ m ≤ n`. -/
theorem exists_consolidation_isFrom (D : Chain X n) (P Q : X) (hD : D.IsFrom P Q)
    (m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    ∃ F : Chain X m, F.IsFrom P Q ∧ F.IsConsolidationOf D := by
  classical
  obtain ⟨hn, hP, hQ, hPu, hQu⟩ := hD
  have hm0 : 0 < m := by omega
  -- the block map: index `i` of `D` goes to block `min i (m-1)`, so the blocks are the
  -- singletons `{0}, …, {m-2}` followed by the tail `{m-1, …, n-1}`
  set blk : Fin n → Fin m := fun i => ⟨min i.val (m - 1), by omega⟩ with hblk
  set rep : Fin m → Fin n := fun t => ⟨t.val, by omega⟩ with hrep
  have hblkval : ∀ i : Fin n, (blk i).val = min i.val (m - 1) := fun i => rfl
  have hblkrep : ∀ t, blk (rep t) = t := by
    intro t
    have := t.isLt
    exact Fin.ext (by simp only [hblkval, hrep]; omega)
  set L : Fin m → Set X := fun t => ⋃ i ∈ {i : Fin n | blk i = t}, D.link i with hL
  have hmemL : ∀ (t : Fin m) (i : Fin n), blk i = t → D.link i ⊆ L t := by
    intro t i hi
    exact Set.subset_biUnion_of_mem (u := fun i => D.link i) hi
  have hLmem : ∀ (t : Fin m) (z : X), z ∈ L t → ∃ i, blk i = t ∧ z ∈ D.link i := by
    intro t z hz
    simp only [hL, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hz
    obtain ⟨i, hi, hz⟩ := hz
    exact ⟨i, hi, hz⟩
  have hFchain : ∀ t u : Fin m, (L t ∩ L u).Nonempty ↔ ((t : ℤ) - (u : ℤ)).natAbs ≤ 1 := by
    intro t u
    constructor
    · rintro ⟨z, hz1, hz2⟩
      obtain ⟨i, hi, hzi⟩ := hLmem t z hz1
      obtain ⟨j, hj, hzj⟩ := hLmem u z hz2
      have h1 := (D.adjacent_iff i j).mp ⟨z, hzi, hzj⟩
      have h2 : t.val = min i.val (m - 1) := by rw [← hi]
      have h3 : u.val = min j.val (m - 1) := by rw [← hj]
      omega
    · intro h
      have hadj : (D.link (rep t) ∩ D.link (rep u)).Nonempty := by
        rw [D.adjacent_iff]
        simp only [hrep]
        omega
      obtain ⟨z, hz1, hz2⟩ := hadj
      exact ⟨z, hmemL t (rep t) (hblkrep t) hz1, hmemL u (rep u) (hblkrep u) hz2⟩
  refine ⟨⟨L, fun t => isOpen_biUnion fun i _ => D.isOpen i, hFchain⟩, ?_, ?_⟩
  · have hblk0 : blk ⟨0, hn⟩ = ⟨0, hm0⟩ := Fin.ext (by simp only [hblkval]; omega)
    have hblkend : blk ⟨n - 1, by omega⟩ = ⟨m - 1, by omega⟩ :=
      Fin.ext (by simp only [hblkval]; omega)
    refine ⟨hm0, hmemL _ _ hblk0 hP, hmemL _ _ hblkend hQ, ?_, ?_⟩
    · intro t ht
      obtain ⟨i, hi, hPi⟩ := hLmem t P ht
      rw [← hi, hPu i hPi, hblk0]
    · intro t ht
      obtain ⟨i, hi, hQi⟩ := hLmem t Q ht
      rw [← hi, hQu i hQi, hblkend]
  · exact ⟨fun i => ⟨blk i, hmemL _ i rfl⟩, fun t => ⟨{i : Fin n | blk i = t}, rfl⟩⟩

/-- **T7.** A chain of bounded links of diameter `< ε` covering a set `A` has at least
`diam A / ε` links. Stated in the weak form `diam A ≤ n * ε`, which is all later use needs.
Boundedness of the links is required because `Metric.diam` of an unbounded set is `0`. -/
theorem diam_le_length_mul {A : Set X} (_hA : Bornology.IsBounded A)
    (D : Chain X n) (hcov : A ⊆ D.union) (ε : ℝ)
    (hb : ∀ i, Bornology.IsBounded (D.link i)) (hε : ∀ i, Metric.diam (D.link i) < ε) :
    Metric.diam A ≤ n * ε := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hA0 : A = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      have := hcov hz
      simp only [union, Set.mem_iUnion] at this
      obtain ⟨i, -⟩ := this
      exact absurd i.isLt (by omega)
    simp [hA0]
  · have hε0 : 0 < ε := lt_of_le_of_lt Metric.diam_nonneg (hε ⟨0, hn⟩)
    -- walking along the chain from link `p` to link `q` costs at most `(d+1)ε`
    have key : ∀ d : ℕ, ∀ (p q : Fin n) (a b : X), ((p : ℤ) - (q : ℤ)).natAbs ≤ d →
        a ∈ D.link p → b ∈ D.link q → dist a b ≤ (d + 1) * ε := by
      intro d
      induction d with
      | zero =>
        intro p q a b hd ha hbq
        have hpq : p = q := Fin.ext (by omega)
        subst hpq
        have h1 := Metric.dist_le_diam_of_mem (hb p) ha hbq
        have h2 := hε p
        push_cast
        linarith
      | succ d ih =>
        intro p q a b hd ha hbq
        by_cases hle : ((p : ℤ) - (q : ℤ)).natAbs ≤ d
        · have h1 := ih p q a b hle ha hbq
          have h2 : ((d : ℝ) + 1) * ε ≤ ((d : ℝ) + 1 + 1) * ε := by nlinarith
          push_cast
          push_cast at h1
          linarith
        · rcases lt_or_gt_of_ne (show p.val ≠ q.val by omega) with hpq | hpq
          · have hq1 : q.val - 1 < n := by omega
            obtain ⟨z, hz1, hz2⟩ := (D.adjacent_iff ⟨q.val - 1, hq1⟩ q).mpr (by simp; omega)
            have h1 := ih p ⟨q.val - 1, hq1⟩ a z (by simp; omega) ha hz1
            have h2 := Metric.dist_le_diam_of_mem (hb q) hz2 hbq
            have h3 := hε q
            have h4 := dist_triangle a z b
            push_cast
            push_cast at h1
            linarith
          · have hq1 : q.val + 1 < n := by omega
            obtain ⟨z, hz1, hz2⟩ := (D.adjacent_iff ⟨q.val + 1, hq1⟩ q).mpr (by simp; omega)
            have h1 := ih p ⟨q.val + 1, hq1⟩ a z (by simp; omega) ha hz1
            have h2 := Metric.dist_le_diam_of_mem (hb q) hz2 hbq
            have h3 := hε q
            have h4 := dist_triangle a z b
            push_cast
            push_cast at h1
            linarith
    refine Metric.diam_le_of_forall_dist_le (by positivity) fun a ha b hbA => ?_
    obtain ⟨p, hp⟩ : ∃ p, a ∈ D.link p := by
      have := hcov ha; simpa [union] using this
    obtain ⟨q, hq⟩ : ∃ q, b ∈ D.link q := by
      have := hcov hbA; simpa [union] using this
    have hd : ((p : ℤ) - (q : ℤ)).natAbs ≤ n - 1 := by
      have := p.isLt; have := q.isLt; omega
    have := key (n - 1) p q a b hd hp hq
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        have : (1 : ℕ) ≤ n := hn
        push_cast [Nat.cast_sub this]
        ring
      rw [this]; ring
    rw [hcast] at this
    exact this

end Chain

end HPC
