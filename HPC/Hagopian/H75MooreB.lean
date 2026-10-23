import HPC.Hagopian.H75MooreA
import HPC.Hagopian.H75Triod
import HPC.Plane.Enc2
import HPC.Jones.Jones49Why
import HPC.Plane.Theorem11Nec

/-!
# Batch 155, item C: Moore's triod theorem, part B — the two cases and the theorem

Moore 1962, Theorem 84 (p. 222), along Moore's own two cases:

* **Separating cores** (Moore's Theorem 73, `countable_of_separating`). If uncountably many of
  mutually disjoint connected sets `Kᵢ` contained closed sets `Zᵢ ⊊ Kᵢ` separating the plane, two of
  them, `i ≠ j`, would share a small ball `Q` meeting `Kᵢ` and `Kⱼ` and missing `Zᵢ ∪ Zⱼ`, and a
  point `o` lying in a component of `Zᵢᶜ` and of `Zⱼᶜ` not containing `Q`. Then those two components
  contain each other, so coincide, and their common frontier lies in `Zᵢ ∩ Zⱼ = ∅`: a nonempty proper
  clopen set of the plane.
* **Non-separating cores** (Moore's Theorems 79, 78 and 76, `countable_of_nonseparating`). A
  non-separating core is enclosed by a simple closed polygon whose closed inside misses three chosen
  points of the three legs (`enclose_holds`, the polygonal form of Moore's Theorem 18). By a
  countable pigeonhole, uncountably many triods have their cores inside one polygon `J` and three
  leg points outside it. Each such triod contains a continuum in the closed inside meeting `J` in a
  point of each leg (boundary bumping, `exists_cross_continuum`). The positions of the three points
  on `J` lie in three disjoint rational parameter intervals; two triods with the same intervals
  contradict the interlacing lemma (`interlace_three`, Moore's Theorem 76).

`moore_triod_theorem` is the statement of the skeleton; `mooreTriodStatement` is the proposition
`MooreTriodStatement` taken as the hypothesis `hmoore` by the supporting lemmas of Lemma 1 and
Theorem 1.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane

/-! ### Case 1: separating cores (Moore's Theorem 73) -/

/-- The component of `Zᵢᶜ` at `o` lies in the component of `Zⱼᶜ` at `o`, when `Zⱼ` lies in a
connected set `Kⱼ` disjoint from `Kᵢ ⊇ Zᵢ` that meets a set `Q` disjoint from that component. -/
theorem comp_subset_comp {Zi Zj Ki Kj Q : Set Pt} {o pj : Pt} (hZjK : Zj ⊆ Kj)
    (hKj : IsPreconnected Kj) (hKij : Disjoint Ki Kj) (hZiK : Zi ⊆ Ki) (hpj : pj ∈ Kj)
    (hpQ : pj ∈ Q) (hdis : Disjoint Q (connectedComponentIn Ziᶜ o)) :
    connectedComponentIn Ziᶜ o ⊆ connectedComponentIn Zjᶜ o := by
  by_cases ho : o ∈ Ziᶜ
  · have hKjZ : Kj ⊆ Ziᶜ := fun z hz hzi => disjoint_left.1 hKij (hZiK hzi) hz
    have hKjc : Kj ⊆ connectedComponentIn Ziᶜ pj := hKj.subset_connectedComponentIn hpj hKjZ
    have hcZ : connectedComponentIn Ziᶜ o ⊆ Zjᶜ := by
      intro z hz hzj
      have h1 : z ∈ connectedComponentIn Ziᶜ pj := hKjc (hZjK hzj)
      have : pj ∈ connectedComponentIn Ziᶜ o := by
        rw [connectedComponentIn_eq hz, ← connectedComponentIn_eq h1]
        exact mem_connectedComponentIn (hKjZ hpj)
      exact disjoint_left.1 hdis hpQ this
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ho) hcZ
  · rw [connectedComponentIn_eq_empty ho]; exact empty_subset _

/-- A small ball of the dense sequence `u` about a given point, inside a given ball. -/
theorem exists_seq_ball {u : ℕ → Pt} (hu : DenseRange u) (p : Pt) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ d : ℕ × ℕ, p ∈ ball (u d.1) (1 / ((d.2 : ℝ) + 1)) ∧
      ball (u d.1) (1 / ((d.2 : ℝ) + 1)) ⊆ ball p ρ := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hρ)
  have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨m, hm⟩ := hu.exists_dist_lt p hpos
  refine ⟨(m, n), ?_, ?_⟩
  · exact hm
  · intro z hz
    rw [mem_ball] at hz ⊢
    dsimp only at hz
    have := dist_triangle z (u m) p
    have h2 : dist (u m) p < 1 / ((n : ℝ) + 1) := by rw [dist_comm]; exact hm
    linarith

/-- **Moore's Theorem 73** (p. 217), in the form used: mutually disjoint connected sets `Kᵢ`, each
containing a closed set `Zᵢ ≠ Kᵢ` that separates the plane, are countably many. -/
theorem countable_of_separating {ι : Type*} (K Z : ι → Set Pt) (hZ : ∀ i, IsClosed (Z i))
    (hsep : ∀ i, SeparatesPlane (Z i)) (hZK : ∀ i, Z i ⊆ K i) (hK : ∀ i, IsPreconnected (K i))
    (hne : ∀ i, (K i \ Z i).Nonempty) (hd : Pairwise (Function.onFun Disjoint K)) :
    Countable ι := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq Pt
  set Bl : ℕ × ℕ → Set Pt := fun d => ball (u d.1) (1 / ((d.2 : ℝ) + 1)) with hBl
  have hdata : ∀ i, ∃ d : (ℕ × ℕ) × ℕ, (K i ∩ Bl d.1).Nonempty ∧ Bl d.1 ⊆ (Z i)ᶜ ∧
      u d.2 ∉ Z i ∧ Disjoint (Bl d.1) (connectedComponentIn (Z i)ᶜ (u d.2)) := by
    intro i
    obtain ⟨p, hpK, hpZ⟩ := hne i
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (hZ i).isOpen_compl p hpZ
    obtain ⟨d, hpd, hdsub⟩ := exists_seq_ball hu p hρ
    have hQZ : Bl d ⊆ (Z i)ᶜ := hdsub.trans hball
    have hQc : Bl d ⊆ connectedComponentIn (Z i)ᶜ p :=
      (convex_ball _ _).isPreconnected.subset_connectedComponentIn hpd hQZ
    obtain ⟨w, hwZ, hwp⟩ : ∃ w ∈ (Z i)ᶜ, w ∉ connectedComponentIn (Z i)ᶜ p := by
      by_contra hcon
      push_neg at hcon
      apply hsep i
      have : connectedComponentIn (Z i)ᶜ p = (Z i)ᶜ :=
        subset_antisymm (connectedComponentIn_subset _ _) hcon
      rw [← this]
      exact isConnected_connectedComponentIn_iff.2 hpZ
    have hWo : IsOpen (connectedComponentIn (Z i)ᶜ w) :=
      (hZ i).isOpen_compl.connectedComponentIn
    obtain ⟨m, hm⟩ := hu.exists_mem_open hWo ⟨w, mem_connectedComponentIn hwZ⟩
    refine ⟨(d, m), ⟨p, hpK, hpd⟩, hQZ, connectedComponentIn_subset _ _ hm, ?_⟩
    rw [disjoint_left]
    intro z hzQ hzo
    have h1 := hQc hzQ
    apply hwp
    rw [connectedComponentIn_eq h1, ← connectedComponentIn_eq hzo, ← connectedComponentIn_eq hm]
    exact mem_connectedComponentIn hwZ
  choose d hdK hdZ hdo hddis using hdata
  by_contra hc
  obtain ⟨i, j, hdij, hij⟩ : ∃ i j, d i = d j ∧ i ≠ j := by
    by_contra hcon
    push_neg at hcon
    exact hc (Function.Injective.countable fun i j h => hcon i j h)
  obtain ⟨pi, hpiK, hpiQ⟩ := hdK i
  obtain ⟨pj, hpjK, hpjQ⟩ := hdK j
  have hdisj := hddis j
  rw [← hdij] at hpjQ hdisj
  have h1 : connectedComponentIn (Z i)ᶜ (u (d i).2) ⊆ connectedComponentIn (Z j)ᶜ (u (d i).2) :=
    comp_subset_comp (hZK j) (hK j) (hd hij) (hZK i) hpjK hpjQ (hddis i)
  have h2 : connectedComponentIn (Z j)ᶜ (u (d i).2) ⊆ connectedComponentIn (Z i)ᶜ (u (d i).2) :=
    comp_subset_comp (hZK i) (hK i) (hd hij.symm) (hZK j) hpiK hpiQ hdisj
  set O := connectedComponentIn (Z i)ᶜ (u (d i).2) with hOdef
  have hOeq : O = connectedComponentIn (Z j)ᶜ (u (d i).2) := subset_antisymm h1 h2
  have hfr : frontier O = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro z hz
    have hzi : z ∈ Z i := mem_of_mem_frontier_comp (hZ i) hz
    rw [hOeq] at hz
    have hzj : z ∈ Z j := mem_of_mem_frontier_comp (hZ j) hz
    exact disjoint_left.1 (hd hij) (hZK i hzi) (hZK j hzj)
  have hcl : IsClopen O := isClopen_iff_frontier_eq_empty.2 hfr
  rcases isClopen_iff.1 hcl with h | h
  · have : u (d i).2 ∈ O := mem_connectedComponentIn (hdo i)
    rw [h] at this; exact this
  · have : pi ∈ O := by rw [h]; exact mem_univ _
    exact disjoint_left.1 (hddis i) hpiQ this

/-! ### Case 2: non-separating cores (Moore's Theorems 79, 78, 76) -/

/-- The data of a triod in the plane: a continuum `T`, a subcontinuum `Z` (the core) and the three
mutually separated pieces of `T \ Z`. `IsTriodSet T` is `∃ Z A B C, TriodData T Z A B C`. -/
def TriodData (T Z A B C : Set Pt) : Prop :=
  Fold.Q78.IsContinuum T ∧ Fold.Q78.IsContinuum Z ∧ Z ⊆ T ∧ A.Nonempty ∧ B.Nonempty ∧
    C.Nonempty ∧ T \ Z = A ∪ B ∪ C ∧ Disjoint (closure A) B ∧ Disjoint A (closure B) ∧
    Disjoint (closure A) C ∧ Disjoint A (closure C) ∧ Disjoint (closure B) C ∧
    Disjoint B (closure C)

/-- **A leg reaching the boundary.** If `T = Z ∪ P ∪ R` with `P`, `R` separated, the core `Z` inside
the open set `D` and a point of `P` outside `closure D`, then a continuum of `T ∩ closure D` through a
given point of `Z` meets `closure D \ D` in a point of `P` (boundary bumping applied to the leg
`Z ∪ P`). -/
theorem exists_leg {T Z P R D J : Set Pt} (hT : IsCompact T) (hTc : IsPreconnected T)
    (hZ : IsConnected Z) (hZc : IsCompact Z) (hTdec : T = Z ∪ P ∪ R)
    (h1 : Disjoint (closure P) R) (h2 : Disjoint P (closure R)) (hDo : IsOpen D)
    (hcl : closure D = D ∪ J) (hZD : Z ⊆ D) {a : Pt} (ha : a ∈ P) (haD : a ∉ closure D) {z : Pt}
    (hz : z ∈ Z) :
    ∃ K : Set Pt, IsCompact K ∧ IsConnected K ∧ K ⊆ T ∧ K ⊆ closure D ∧ z ∈ K ∧
      ∃ q ∈ K, q ∈ J ∧ q ∈ P := by
  have hPT : P ⊆ T := fun w hw => by rw [hTdec]; exact Or.inl (Or.inr hw)
  have hZT : Z ⊆ T := fun w hw => by rw [hTdec]; exact Or.inl (Or.inl hw)
  set L := Z ∪ P with hLdef
  have hL : IsPreconnected L :=
    isPreconnected_union_of_separated hTc hZ.isPreconnected hZ.nonempty hTdec h1 h2
  have hPcl : closure P ⊆ Z ∪ P := by
    intro w hw
    have hwT : w ∈ T := hT.isClosed.closure_subset_iff.2 hPT hw
    rw [hTdec] at hwT
    rcases hwT with hw' | hw'
    · exact hw'
    · exact (disjoint_left.1 h1 hw hw').elim
  have hLT : L ⊆ T := union_subset hZT hPT
  have hLcl : IsClosed L := by
    apply isClosed_of_closure_subset
    rw [closure_union, hZc.isClosed.closure_eq]
    exact union_subset subset_union_left hPcl
  have hLc : IsCompact L := hT.of_isClosed_subset hLcl hLT
  set F := L ∩ closure D with hFdef
  have hFc : IsCompact F := hLc.inter_right isClosed_closure
  have hFne : F ≠ L := fun h => by
    have : a ∈ F := by rw [h]; exact Or.inr ha
    exact haD this.2
  have hzF : z ∈ F := ⟨Or.inl hz, subset_closure (hZD hz)⟩
  obtain ⟨K, hKc, hKconn, hKF, hzK, q, hqK, hqcl⟩ :=
    HPC.Jones.exists_continuum_bump_compact hL hFc inter_subset_left hFne hzF
  have hqD : q ∉ D := by
    have hsub : L \ F ⊆ Dᶜ := fun w hw hwD => hw.2 ⟨hw.1, subset_closure hwD⟩
    have := closure_mono hsub hqcl
    rwa [hDo.isClosed_compl.closure_eq] at this
  have hqcD : q ∈ closure D := (hKF hqK).2
  rw [hcl] at hqcD
  have hqJ : q ∈ J := hqcD.resolve_left hqD
  have hqP : q ∈ P := by
    rcases (hKF hqK).1 with h | h
    · exact (hqD (hZD h)).elim
    · exact h
  exact ⟨K, hKc, hKconn, fun w hw => hLT (hKF hw).1, fun w hw => (hKF hw).2, hzK, q, hqK, hqJ, hqP⟩

/-- **The continuum crossing to the boundary** (the continuum Moore takes in Theorem 84: a
subcontinuum of the closed inside containing points of the boundary on all three legs). -/
theorem exists_cross_continuum {T Z A B C D J : Set Pt} (h : TriodData T Z A B C)
    (hDo : IsOpen D) (hcl : closure D = D ∪ J) (hZD : Z ⊆ D) {a b c : Pt} (ha : a ∈ A)
    (haD : a ∉ closure D) (hb : b ∈ B) (hbD : b ∉ closure D) (hc : c ∈ C) (hcD : c ∉ closure D) :
    ∃ x : Set Pt, IsCompact x ∧ IsConnected x ∧ x ⊆ T ∧ x ⊆ D ∪ J ∧ (∃ q ∈ x, q ∈ J ∧ q ∈ A) ∧
      (∃ q ∈ x, q ∈ J ∧ q ∈ B) ∧ (∃ q ∈ x, q ∈ J ∧ q ∈ C) := by
  obtain ⟨⟨hT, hTc⟩, ⟨hZc, hZ⟩, hZT, -, -, -, heq, d1, d2, d3, d4, d5, d6⟩ := h
  obtain ⟨z, hz⟩ := hZ.nonempty
  have hdec : ∀ {P Q R : Set Pt}, T \ Z = P ∪ Q ∪ R → T = Z ∪ P ∪ (Q ∪ R) := by
    intro P Q R hPQR
    ext w; constructor
    · intro hw
      by_cases hwZ : w ∈ Z
      · exact Or.inl (Or.inl hwZ)
      · have : w ∈ T \ Z := ⟨hw, hwZ⟩
        rw [hPQR] at this
        rcases this with (h | h) | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    · rintro ((h | h) | h | h)
      · exact hZT h
      all_goals
        have : w ∈ T \ Z := by rw [hPQR]; simp [h]
        exact this.1
  have heqB : T \ Z = B ∪ A ∪ C := by rw [heq]; ac_rfl
  have heqC : T \ Z = C ∪ A ∪ B := by rw [heq]; ac_rfl
  have hDJ : closure D ⊆ D ∪ J := hcl.le
  obtain ⟨KA, hKAc, hKAconn, hKAT, hKAD, hzA, qa, hqaK, hqaJ, hqaA⟩ :=
    exists_leg hT hTc.isPreconnected hZ hZc (hdec heq)
      (by rw [disjoint_union_right]; exact ⟨d1, d3⟩)
      (by rw [closure_union, disjoint_union_right]; exact ⟨d2, d4⟩) hDo hcl hZD ha haD hz
  obtain ⟨KB, hKBc, hKBconn, hKBT, hKBD, hzB, qb, hqbK, hqbJ, hqbB⟩ :=
    exists_leg hT hTc.isPreconnected hZ hZc (hdec heqB)
      (by rw [disjoint_union_right]; exact ⟨d2.symm, d5⟩)
      (by rw [closure_union, disjoint_union_right]; exact ⟨d1.symm, d6⟩) hDo hcl hZD hb hbD hz
  obtain ⟨KC, hKCc, hKCconn, hKCT, hKCD, hzC, qc, hqcK, hqcJ, hqcC⟩ :=
    exists_leg hT hTc.isPreconnected hZ hZc (hdec heqC)
      (by rw [disjoint_union_right]; exact ⟨d4.symm, d6.symm⟩)
      (by rw [closure_union, disjoint_union_right]; exact ⟨d3.symm, d5.symm⟩) hDo hcl hZD hc hcD hz
  refine ⟨KA ∪ KB ∪ KC, (hKAc.union hKBc).union hKCc,
    ((hKAconn.union ⟨z, hzA, hzB⟩ hKBconn).union ⟨z, Or.inl hzA, hzC⟩ hKCconn),
    union_subset (union_subset hKAT hKBT) hKCT,
    union_subset (union_subset (hKAD.trans hDJ) (hKBD.trans hDJ)) (hKCD.trans hDJ),
    ⟨qa, Or.inl (Or.inl hqaK), hqaJ, hqaA⟩, ⟨qb, Or.inl (Or.inr hqbK), hqbJ, hqbB⟩,
    ⟨qc, Or.inr hqcK, hqcJ, hqcC⟩⟩

/-- Three distinct reals lie in three pairwise ordered open intervals with rational ends. -/
theorem exists_rat_intervals (p : Fin 3 → ℝ) (hp : Function.Injective p) :
    ∃ l r : Fin 3 → ℚ, (∀ k, (l k : ℝ) < p k ∧ p k < r k) ∧
      ∀ k k', k ≠ k' → (r k : ℝ) ≤ l k' ∨ (r k' : ℝ) ≤ l k := by
  set δ := min (min |p 0 - p 1| |p 0 - p 2|) |p 1 - p 2| / 3 with hδ
  have hne : ∀ k k' : Fin 3, k ≠ k' → 0 < |p k - p k'| := fun k k' h =>
    abs_pos.2 (sub_ne_zero.2 (hp.ne h))
  have hδpos : 0 < δ := by
    have := hne 0 1 (by decide); have := hne 0 2 (by decide); have := hne 1 2 (by decide)
    positivity
  have hgap : ∀ k k' : Fin 3, k ≠ k' → 3 * δ ≤ |p k - p k'| := by
    have e1 : 3 * δ ≤ |p 0 - p 1| := by
      rw [hδ]; have := min_le_left (min |p 0 - p 1| |p 0 - p 2|) |p 1 - p 2|
      have := min_le_left |p 0 - p 1| |p 0 - p 2|; linarith
    have e2 : 3 * δ ≤ |p 0 - p 2| := by
      rw [hδ]; have := min_le_left (min |p 0 - p 1| |p 0 - p 2|) |p 1 - p 2|
      have := min_le_right |p 0 - p 1| |p 0 - p 2|; linarith
    have e3 : 3 * δ ≤ |p 1 - p 2| := by
      rw [hδ]; have := min_le_right (min |p 0 - p 1| |p 0 - p 2|) |p 1 - p 2|; linarith
    intro k k' h
    fin_cases k <;> fin_cases k' <;>
      first
      | exact (h rfl).elim
      | exact e1
      | exact e2
      | exact e3
      | (rw [abs_sub_comm]; exact e1)
      | (rw [abs_sub_comm]; exact e2)
      | (rw [abs_sub_comm]; exact e3)
  have hl : ∀ k, ∃ q : ℚ, p k - δ < q ∧ (q : ℝ) < p k := fun k =>
    exists_rat_btwn (by linarith)
  have hr : ∀ k, ∃ q : ℚ, p k < q ∧ (q : ℝ) < p k + δ := fun k =>
    exists_rat_btwn (by linarith)
  choose l hl1 hl2 using hl
  choose r hr1 hr2 using hr
  refine ⟨l, r, fun k => ⟨hl2 k, hr1 k⟩, fun k k' h => ?_⟩
  have hg := hgap k k' h
  rcases le_or_gt (p k) (p k') with hle | hlt
  · left
    rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hg
    linarith [hr2 k, hl1 k']
  · right
    rw [abs_of_pos (by linarith)] at hg
    linarith [hr2 k', hl1 k]

theorem injective_vec3 {a b c : ℝ} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro k k' h
  fin_cases k <;> fin_cases k' <;> simp_all [eq_comm]

/-- An uncountable domain has an uncountable fibre over a countable codomain. -/
theorem exists_uncountable_fiber {ι β : Type*} [Countable β] (f : ι → β) (hι : ¬ Countable ι) :
    ∃ b, ¬ (f ⁻¹' {b}).Countable := by
  by_contra h
  push_neg at h
  apply hι
  have : (univ : Set ι).Countable := by
    have : (univ : Set ι) = ⋃ b, f ⁻¹' {b} := by ext i; simp
    rw [this]; exact countable_iUnion h
  exact countable_univ_iff.1 this

/-- **Moore's Theorems 79, 78 and 76**, the case of non-separating cores: mutually disjoint triods
whose cores do not separate the plane are countably many. -/
theorem countable_of_nonseparating {ι : Type*} (T Z A B C : ι → Set Pt)
    (h : ∀ i, TriodData (T i) (Z i) (A i) (B i) (C i)) (hns : ∀ i, ¬ SeparatesPlane (Z i))
    (hd : Pairwise (Function.onFun Disjoint T)) : Countable ι := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq Pt
  set Bl : ℕ × ℕ → Set Pt := fun d => ball (u d.1) (1 / ((d.2 : ℝ) + 1)) with hBl
  -- Stage 1: for each triod, an enclosing polygon and countable data
  have hst1 : ∀ i, ∃ J : Set Pt, IsSimpleClosedPolygon J ∧
      ∃ (F : Finset (ℕ × ℕ)) (da db dc : ℕ × ℕ),
      (Z i ⊆ ⋃ d ∈ F, Bl d) ∧ (∀ d ∈ F, Bl d ⊆ polyInterior J) ∧
      (A i ∩ Bl da).Nonempty ∧ Disjoint (Bl da) (closure (polyInterior J)) ∧
      (B i ∩ Bl db).Nonempty ∧ Disjoint (Bl db) (closure (polyInterior J)) ∧
      (C i ∩ Bl dc).Nonempty ∧ Disjoint (Bl dc) (closure (polyInterior J)) := by
    intro i
    obtain ⟨-, ⟨hZc, hZ⟩, -, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, heq, -⟩ := h i
    have hnotZ : ∀ {w}, w ∈ A i ∪ B i ∪ C i → w ∉ Z i := fun hw => by
      rw [← heq] at hw; exact hw.2
    have hball : ∀ w ∉ Z i, ∃ r > 0, closedBall w r ⊆ (Z i)ᶜ := fun w hw => by
      obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hZc.isClosed.isOpen_compl w hw
      exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hsub⟩
    obtain ⟨ra, hra, hsa⟩ := hball a (hnotZ (Or.inl (Or.inl ha)))
    obtain ⟨rb, hrb, hsb⟩ := hball b (hnotZ (Or.inl (Or.inr hb)))
    obtain ⟨rc, hrc, hsc⟩ := hball c (hnotZ (Or.inr hc))
    set G := (closedBall a ra ∪ closedBall b rb ∪ closedBall c rc)ᶜ with hGdef
    have hGo : IsOpen G :=
      ((isClosed_closedBall.union isClosed_closedBall).union isClosed_closedBall).isOpen_compl
    have hZG : Z i ⊆ G := by
      intro w hw hw'
      rcases hw' with (h1 | h1) | h1
      · exact hsa h1 hw
      · exact hsb h1 hw
      · exact hsc h1 hw
    obtain ⟨J, hJ, -, hZJ, hJG⟩ := enclose_holds (Z i) ⟨hZc, hZ⟩ (hns i) G hGo hZG
    obtain ⟨-, hDo, -⟩ := planeFacts_holds.split hJ
    have hfar : ∀ {w r}, closedBall w r ⊆ Gᶜ → Disjoint (ball w r) (closure (polyInterior J)) := by
      intro w r hwr
      have : closure (polyInterior J) ⊆ (ball w r)ᶜ := by
        apply closure_minimal _ isOpen_ball.isClosed_compl
        intro z hz hzb
        exact hwr (ball_subset_closedBall hzb) (hJG hz)
      exact disjoint_left.2 fun z hz hz' => this hz' hz
    have hcover : ∀ z ∈ Z i, ∃ d : ℕ × ℕ, z ∈ Bl d ∧ Bl d ⊆ polyInterior J := fun z hz => by
      obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hDo z (hZJ hz)
      obtain ⟨d, hd1, hd2⟩ := exists_seq_ball hu z hε
      exact ⟨d, hd1, hd2.trans hsub⟩
    obtain ⟨t, ht⟩ := hZc.elim_finite_subcover
      (fun d : {d : ℕ × ℕ // Bl d ⊆ polyInterior J} => Bl d.1) (fun _ => isOpen_ball)
      (fun z hz => by
        obtain ⟨d, hd1, hd2⟩ := hcover z hz
        exact mem_iUnion.2 ⟨⟨d, hd2⟩, hd1⟩)
    obtain ⟨da, hda1, hda2⟩ := exists_seq_ball hu a hra
    obtain ⟨db, hdb1, hdb2⟩ := exists_seq_ball hu b hrb
    obtain ⟨dc, hdc1, hdc2⟩ := exists_seq_ball hu c hrc
    have hGc : ∀ {w r}, closedBall w r ⊆ closedBall a ra ∪ closedBall b rb ∪ closedBall c rc →
        closedBall w r ⊆ Gᶜ := fun hw => by rw [hGdef, compl_compl]; exact hw
    refine ⟨J, hJ, t.map (Function.Embedding.subtype _), da, db, dc, ?_, ?_, ⟨a, ha, hda1⟩,
      (hfar (hGc fun z hz => Or.inl (Or.inl hz))).mono_left hda2, ⟨b, hb, hdb1⟩,
      (hfar (hGc fun z hz => Or.inl (Or.inr hz))).mono_left hdb2, ⟨c, hc, hdc1⟩,
      (hfar (hGc fun z hz => Or.inr hz)).mono_left hdc2⟩
    · intro z hz
      obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.1 (ht hz)
      exact mem_iUnion₂.2 ⟨d.1, Finset.mem_map_of_mem _ hd, hzd⟩
    · intro d hd
      obtain ⟨d', -, rfl⟩ := Finset.mem_map.1 hd
      exact d'.2
  choose Jf hJf F da db dc hcov hFsub hAa hda hBb hdb hCc hdc using hst1
  by_contra hcount
  obtain ⟨δ, hδ⟩ := exists_uncountable_fiber (fun i => (F i, da i, db i, dc i)) hcount
  set S := (fun i => (F i, da i, db i, dc i)) ⁻¹' {δ} with hSdef
  obtain ⟨i0, hi0⟩ : S.Nonempty := by
    by_contra hem
    rw [not_nonempty_iff_eq_empty] at hem
    exact hδ (hem ▸ countable_empty)
  set J := Jf i0 with hJdef
  set D := polyInterior J with hDdef
  obtain ⟨E, hDo, hEo, hcovJ, hDE, -, hfr, -, hJE, hEc, -⟩ := planeFacts_holds.split (hJf i0)
  have hcl : closure D = D ∪ J := by
    rw [closure_eq_interior_union_frontier, hDo.interior_eq, hfr]
  have hmem : ∀ j ∈ S, F j = F i0 ∧ da j = da i0 ∧ db j = db i0 ∧ dc j = dc i0 := by
    intro j hj
    have h1 : (F j, da j, db j, dc j) = δ := hj
    have h2 : (F i0, da i0, db i0, dc i0) = δ := hi0
    rw [← h2] at h1
    simp only [Prod.mk.injEq] at h1
    exact h1
  have hZD : ∀ j ∈ S, Z j ⊆ D := fun j hj z hz => by
    have := hcov j hz
    rw [(hmem j hj).1] at this
    obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.1 this
    exact hFsub i0 d hd hzd
  obtain ⟨γ, hγ, hγJ, hinj, hper⟩ := exists_loop_param (hJf i0)
  -- Stage 2: for each triod of the fibre, the crossing continuum and its parameter intervals
  have hst2 : ∀ j ∈ S, ∃ x : Set Pt, IsCompact x ∧ IsConnected x ∧ x ⊆ T j ∧ x ⊆ D ∪ J ∧
      ∃ p : Fin 3 → ℝ, (∀ k, p k ∈ Ico (0:ℝ) 2) ∧ (∀ k, γ (p k) ∈ x) ∧
      ∃ l r : Fin 3 → ℚ, (∀ k, (l k : ℝ) < p k ∧ p k < r k) ∧
        ∀ k k', k ≠ k' → (r k : ℝ) ≤ l k' ∨ (r k' : ℝ) ≤ l k := by
    intro j hj
    obtain ⟨a, haA, hab⟩ := hAa j
    obtain ⟨b, hbB, hbb⟩ := hBb j
    obtain ⟨c, hcC, hcb⟩ := hCc j
    rw [(hmem j hj).2.1] at hab
    rw [(hmem j hj).2.2.1] at hbb
    rw [(hmem j hj).2.2.2] at hcb
    obtain ⟨x, hxc, hxconn, hxT, hxD, ⟨qa, hqax, hqaJ, hqaA⟩, ⟨qb, hqbx, hqbJ, hqbB⟩,
      ⟨qc, hqcx, hqcJ, hqcC⟩⟩ := exists_cross_continuum (h j) hDo hcl (hZD j hj) haA
        (disjoint_left.1 (hda i0) hab) hbB (disjoint_left.1 (hdb i0) hbb) hcC
        (disjoint_left.1 (hdc i0) hcb)
    obtain ⟨ta, hta, hγa⟩ := exists_param_of_mem hγJ hper hqaJ
    obtain ⟨tb, htb, hγb⟩ := exists_param_of_mem hγJ hper hqbJ
    obtain ⟨tc, htc, hγc⟩ := exists_param_of_mem hγJ hper hqcJ
    obtain ⟨-, -, -, -, -, -, -, -, d2, -, d4, -, d6⟩ := h j
    have e1 : ta ≠ tb := fun h' => by
      have : qa = qb := by rw [← hγa, ← hγb, h']
      exact disjoint_left.1 (d2.mono_right subset_closure) hqaA (this ▸ hqbB)
    have e2 : ta ≠ tc := fun h' => by
      have : qa = qc := by rw [← hγa, ← hγc, h']
      exact disjoint_left.1 (d4.mono_right subset_closure) hqaA (this ▸ hqcC)
    have e3 : tb ≠ tc := fun h' => by
      have : qb = qc := by rw [← hγb, ← hγc, h']
      exact disjoint_left.1 (d6.mono_right subset_closure) hqbB (this ▸ hqcC)
    obtain ⟨l, r, hlr, hord⟩ := exists_rat_intervals ![ta, tb, tc] (injective_vec3 e1 e2 e3)
    refine ⟨x, hxc, hxconn, hxT, hxD, ![ta, tb, tc], fun k => ?_, fun k => ?_, l, r, hlr, hord⟩
    · fin_cases k
      · exact hta
      · exact htb
      · exact htc
    · fin_cases k
      · simpa [hγa] using hqax
      · simpa [hγb] using hqbx
      · simpa [hγc] using hqcx
  choose! x hxc hxconn hxT hxD p hp hpx l r hlr hord using hst2
  obtain ⟨j, hj, k, hk, hjk, hne⟩ : ∃ j ∈ S, ∃ k ∈ S, (l j, r j) = (l k, r k) ∧ j ≠ k := by
    by_contra hcon
    push_neg at hcon
    apply hδ
    have : Countable S := Function.Injective.countable
      (f := fun j : S => (l j, r j)) fun a b hab => Subtype.ext (hcon a a.2 b b.2 hab)
    exact countable_coe_iff.1 this
  simp only [Prod.mk.injEq] at hjk
  obtain ⟨hl, hr⟩ := hjk
  have hdisj : Disjoint (x j) (x k) := (hd hne).mono (hxT j hj) (hxT k hk)
  refine interlace_three (P := fun t => γ t ∈ x j) (Q := fun t => γ t ∈ x k)
    (fun s u t v hs hsu hut htv hv h1 h2 h3 h4 => interlace_param hγ hγJ hinj hper hDo hEo hEc
      hcovJ hDE (fun w hw => hJE w hw) (hxc j hj) (hxconn j hj) (hxconn k hk).isPreconnected
      (hxD j hj) (hxD k hk) hdisj hs hsu hut htv hv h1 h2 h3 h4)
    (fun s u t v hs hsu hut htv hv h1 h2 h3 h4 => interlace_param hγ hγJ hinj hper hDo hEo hEc
      hcovJ hDE (fun w hw => hJE w hw) (hxc k hk) (hxconn k hk) (hxconn j hj).isPreconnected
      (hxD k hk) (hxD j hj) hdisj.symm hs hsu hut htv hv h1 h2 h3 h4)
    (p j) (p k) (hp j hj) (hp k hk) (hpx j hj) (hpx k hk) (fun i heq => ?_) (fun a b hab => ?_)
  · have : γ (p j i) ∈ x k := by rw [heq]; exact hpx k hk i
    exact disjoint_left.1 hdisj (hpx j hj i) this
  · have ha1 := hlr j hj a
    have hb1 := hlr j hj b
    have ha2 := hlr k hk a
    have hb2 := hlr k hk b
    rw [← hl, ← hr] at ha2 hb2
    rcases hord j hj a b hab with h' | h'
    · left
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [ha1.1, ha1.2, hb1.1, hb1.2, ha2.1, ha2.2, hb2.1, hb2.2]
    · right
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [ha1.1, ha1.2, hb1.1, hb1.2, ha2.1, ha2.2, hb2.1, hb2.2]

/-! ### The theorem -/

theorem isTriodSet_iff_triodData {T : Set Pt} : IsTriodSet T ↔ ∃ Z A B C, TriodData T Z A B C := by
  constructor
  · rintro ⟨h1, Z, h2, h3, A, B, C, h4⟩
    exact ⟨Z, A, B, C, h1, h2, h3, h4⟩
  · rintro ⟨Z, A, B, C, h1, h2, h3, h4⟩
    exact ⟨h1, Z, h2, h3, A, B, C, h4⟩

/-- **Moore's triod theorem** (Moore 1962, Theorem 84, p. 222): every family of mutually disjoint
triods in the plane is countable. -/
theorem moore_triod_theorem' {ι : Type*} (T : ι → Set Pt) (hT : ∀ i, IsTriodSet (T i))
    (hd : Pairwise (Function.onFun Disjoint T)) : Countable ι := by
  choose Z A B C hdat using fun i => isTriodSet_iff_triodData.1 (hT i)
  set S := {i | SeparatesPlane (Z i)} with hSdef
  have h1 : S.Countable := by
    have : Countable S := countable_of_separating (fun i : S => T i) (fun i : S => Z i)
      (fun i => (hdat i).2.1.1.isClosed) (fun i => i.2) (fun i => (hdat i).2.2.1)
      (fun i => (hdat i).1.2.isPreconnected)
      (fun i => by
        obtain ⟨-, -, -, ⟨w, hw⟩, -, -, heq, -⟩ := hdat i
        have : w ∈ T i \ Z i := by rw [heq]; exact Or.inl (Or.inl hw)
        exact ⟨w, this⟩)
      (fun i j hij => hd (fun h => hij (Subtype.ext h)))
    exact countable_coe_iff.1 this
  have h2 : Sᶜ.Countable := by
    have : Countable (Sᶜ : Set ι) := countable_of_nonseparating (fun i : (Sᶜ : Set ι) => T i)
      (fun i => Z i) (fun i => A i) (fun i => B i) (fun i => C i) (fun i => hdat i)
      (fun i => i.2) (fun i j hij => hd (fun h => hij (Subtype.ext h)))
    exact countable_coe_iff.1 this
  have : (univ : Set ι).Countable := by rw [← union_compl_self S]; exact h1.union h2
  exact countable_univ_iff.1 this

/-- `MooreTriodStatement` holds. -/
theorem mooreTriodStatement : MooreTriodStatement := fun _ T hT hd => moore_triod_theorem' T hT hd

end HPC.Hagopian
