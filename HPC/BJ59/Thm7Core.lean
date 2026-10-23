import HPC.BJ59.Thm7Fold
import HPC.Hagopian.H75Composants
import HPC.PseudoArc.PatGeom
import HPC.PseudoArc.Uniqueness
import HPC.Plane.PA51Crook
import HPC.Plane.PA51Pre
import HPC.Plane.PseudoArc51

/-!
# Batch 199, library: Bing–Jones Theorem 7 (first sentence) in a compact pseudo-arc
(commission 199, §6)

In a compact space `S` which is a pseudo-arc:
* `exists_not_mem_composant_of_isOpen`: every nonempty open set has a point outside the composant
  of a given point (composants are dense and pairwise disjoint);
* `exists_chain_isFrom`: a chain covering `S` shrinks (link by link) to one from `p` to `q`, with
  `p`, `q` in different composants (closed balls about `p`, `q` removed from the neighbouring
  links);
* `prependDesc`: a description of `S` whose level `0` is a given chain from `p` to `q` (Bing–Jones
  assume such a sequence without comment, p. 177), and `exists_follow_pattern` (Bing 1948
  Theorem 6 for it);
* `bj7_compact`: the first sentence of Theorem 7 in `S`.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane

variable {S : Type*} [MetricSpace S]

/-! ### Composants -/

theorem composant_univ_eq_jones (p : S) :
    composant (univ : Set S) p = Jones.composant p := by
  ext y
  simp only [composant, mem_sUnion, mem_setOf_eq, Jones.composant]
  constructor
  · rintro ⟨K, ⟨hK, -, hKu, hpK⟩, hyK⟩; exact ⟨K, hK, hKu, hpK, hyK⟩
  · rintro ⟨K, hK, hKu, hpK, hyK⟩; exact ⟨K, ⟨hK, subset_univ K, hKu, hpK⟩, hyK⟩

/-- A connected nontrivial `T₁` space has no isolated points: a nonempty open set has a point other
than any given point. -/
theorem exists_ne_mem_of_isOpen [ConnectedSpace S] [Nontrivial S] {U : Set S} (hU : IsOpen U)
    (hne : U.Nonempty) (z : S) : ∃ y ∈ U, y ≠ z := by
  obtain ⟨x, hx⟩ := hne
  by_cases hxz : x = z
  · subst hxz
    by_contra h
    push_neg at h
    have hU1 : U = {x} := Subset.antisymm (fun y hy => h y hy) (singleton_subset_iff.2 hx)
    have hcl : IsClopen ({x} : Set S) := ⟨isClosed_singleton, hU1 ▸ hU⟩
    obtain ⟨a, b, hab⟩ := exists_pair_ne S
    rcases isClopen_iff.1 hcl with h' | h'
    · exact (singleton_ne_empty x) h'
    · have ha : a ∈ ({x} : Set S) := h' ▸ mem_univ a
      have hb : b ∈ ({x} : Set S) := h' ▸ mem_univ b
      exact hab ((mem_singleton_iff.1 ha).trans (mem_singleton_iff.1 hb).symm)
  · exact ⟨x, hx, hxz⟩

theorem not_isDecomposableSpace_of_pa (hP : IsPseudoArc (univ : Set S)) :
    ¬ Jones.IsDecomposableSpace S := by
  rintro ⟨H, K, hH, hK, hHu, hKu, hHK⟩
  rcases (hP.2.1 univ subset_rfl hP.1.1).2 H K hH hK (subset_univ _) (subset_univ _) hHK with h | h
  · exact hHu h
  · exact hKu h

theorem mem_composant_univ_self [Nontrivial S] (p : S) : p ∈ composant (univ : Set S) p := by
  rw [composant_univ_eq_jones]
  obtain ⟨a, b, hab⟩ := exists_pair_ne S
  refine ⟨{p}, ⟨isCompact_singleton, isConnected_singleton⟩, fun h => ?_, rfl, rfl⟩
  have ha : a ∈ ({p} : Set S) := h ▸ mem_univ a
  have hb : b ∈ ({p} : Set S) := h ▸ mem_univ b
  exact hab ((mem_singleton_iff.1 ha).trans (mem_singleton_iff.1 hb).symm)

/-- Links of a chain whose indices differ by more than one are disjoint. -/
theorem chain_not_mem_of_far {n : ℕ} (T : Chain S n) {i j : Fin n}
    (hij : 1 < ((i : ℤ) - j).natAbs) {x : S} (hi : x ∈ T.link i) : x ∉ T.link j := fun hj => by
  have := (T.adjacent i j).1 ⟨x, hi, hj⟩
  omega

/-- A ball about `p` inside an open set and missing a given point `w ≠ p`. -/
theorem exists_closedBall_subset_not_mem {U : Set S} (hU : IsOpen U) {p w : S} (hp : p ∈ U)
    (hwp : w ≠ p) : ∃ ρ > 0, closedBall p ρ ⊆ U ∧ w ∉ closedBall p ρ := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU p hp
  have hd : 0 < dist w p := dist_pos.2 hwp
  refine ⟨min (ε / 2) (dist w p / 2), lt_min (by linarith) (by linarith),
    (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))).trans hεU,
    fun h => ?_⟩
  have := mem_closedBall.1 h
  have := min_le_right (ε / 2) (dist w p / 2)
  linarith

variable [CompactSpace S]

/-- **Points outside a composant in every open set.** -/
theorem exists_not_mem_composant_of_isOpen (hP : IsPseudoArc (univ : Set S)) (p : S) {O : Set S}
    (hO : IsOpen O) (hOne : O.Nonempty) : ∃ q ∈ O, q ∉ composant (univ : Set S) p := by
  haveI : ConnectedSpace S := connectedSpace_iff_univ.2 hP.1.1.2
  haveI : Nontrivial S := nontrivial_univ_iff.1 hP.2.2
  obtain ⟨r, -, hr⟩ := exists_not_mem_composant hP (mem_univ p)
  obtain ⟨q, hqO, hqr⟩ := (HPC.Hagopian.composant_dense' r).inter_open_nonempty O hO hOne
  refine ⟨q, hqO, fun hq => ?_⟩
  rw [composant_univ_eq_jones] at hq hr
  have hrr : r ∈ Jones.composant r := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne S
    refine ⟨{r}, ⟨isCompact_singleton, isConnected_singleton⟩, fun h => ?_, rfl, rfl⟩
    have ha : a ∈ ({r} : Set S) := h ▸ mem_univ a
    have hb : b ∈ ({r} : Set S) := h ▸ mem_univ b
    exact hab ((mem_singleton_iff.1 ha).trans (mem_singleton_iff.1 hb).symm)
  rcases HPC.Hagopian.composant_eq_or_disjoint' (not_isDecomposableSpace_of_pa hP) p r with h | h
  · exact hr (h ▸ hrr)
  · exact Set.disjoint_left.1 h hq hqr

/-- **A chain from `p` to `q`, with `p`, `q` in different composants**, inside a given chain
covering the pseudo-arc `S`: remove a closed ball about `p ∈ T₀` from `T₁` and one about
`q ∈ T_{n−1}` from `T_{n−2}`. -/
theorem exists_chain_isFrom (hP : IsPseudoArc (univ : Set S)) {n : ℕ} (T : Chain S n)
    (hT : univ ⊆ T.union) :
    ∃ T' : Chain S n, (∀ j, T'.link j ⊆ T.link j) ∧ univ ⊆ T'.union ∧
      ∃ p q, T'.IsFrom p q ∧ p ≠ q ∧ q ∉ composant (univ : Set S) p := by
  haveI : ConnectedSpace S := connectedSpace_iff_univ.2 hP.1.1.2
  haveI : Nontrivial S := nontrivial_univ_iff.1 hP.2.2
  obtain ⟨x₀⟩ : Nonempty S := inferInstance
  have hn : 0 < n := by
    obtain ⟨i, -⟩ := mem_iUnion.1 (hT (mem_univ x₀))
    exact i.pos
  rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
  · obtain ⟨q, -, hq⟩ := exists_not_mem_composant_of_isOpen hP x₀ isOpen_univ univ_nonempty
    have hpq : x₀ ≠ q := fun h => hq (h ▸ mem_composant_univ_self x₀)
    have hmem : ∀ x : S, x ∈ T.link 0 := fun x => by
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hT (mem_univ x))
      rwa [Subsingleton.elim i 0] at hi
    exact ⟨T, fun _ => subset_rfl, hT, x₀, q, ⟨hn, hmem x₀, hmem q,
      fun i _ => Subsingleton.elim _ _, fun i _ => Subsingleton.elim _ _⟩, hpq, hq⟩
  -- the indices
  set i0 : Fin n := ⟨0, hn⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set il : Fin n := ⟨n - 1, by omega⟩
  set il2 : Fin n := ⟨n - 2, by omega⟩
  -- `p`, `w`, the ball `Bp`
  obtain ⟨p, hp⟩ := T.link_nonempty i0
  obtain ⟨w, ⟨hw0, hw1⟩, hwp⟩ := exists_ne_mem_of_isOpen ((T.isOpen i0).inter (T.isOpen i1))
    ((T.adjacent i0 i1).2 (by simp [i0, i1])) p
  obtain ⟨ρ, hρ, hBp0, hwBp⟩ := exists_closedBall_subset_not_mem (T.isOpen i0) hp hwp
  set Bp := closedBall p ρ
  have hpBp : p ∈ Bp := mem_closedBall_self hρ.le
  -- far from `T₀`
  have hfar0 : ∀ {j : Fin n} {x : S}, x ∈ T.link j → x ∈ Bp → j.val ≤ 1 := fun {j x} hj hx => by
    by_contra h
    exact chain_not_mem_of_far T (i := i0) (j := j) (by simp [i0]; omega) (hBp0 hx) hj
  -- `q`
  set O := T.link il \ Bp
  have hO : IsOpen O := (T.isOpen il).sdiff isClosed_closedBall
  have hOne : O.Nonempty := by
    by_cases h2 : n = 2
    · exact ⟨w, by simpa [il, i1, h2] using hw1, hwBp⟩
    · obtain ⟨x, hx⟩ := T.link_nonempty il
      exact ⟨x, hx, fun hxB => by have := hfar0 hx hxB; simp [il] at this; omega⟩
  obtain ⟨q, ⟨hqT, hqBp⟩, hq⟩ := exists_not_mem_composant_of_isOpen hP p hO hOne
  -- `w'`, the ball `Bq`
  have hO' : IsOpen ((T.link il2 ∩ T.link il) \ Bp) :=
    ((T.isOpen il2).inter (T.isOpen il)).sdiff isClosed_closedBall
  have hO'ne : ((T.link il2 ∩ T.link il) \ Bp).Nonempty := by
    by_cases h2 : n = 2
    · exact ⟨w, ⟨by simpa [il2, h2] using hw0, by simpa [il, h2] using hw1⟩, hwBp⟩
    · obtain ⟨x, hx2, hxl⟩ := (T.adjacent il2 il).2 (by simp [il2, il]; omega)
      exact ⟨x, ⟨hx2, hxl⟩, fun hxB => by have := hfar0 hxl hxB; simp [il] at this; omega⟩
  obtain ⟨w', ⟨⟨hw'2, hw'l⟩, hw'Bp⟩, hw'q⟩ := exists_ne_mem_of_isOpen hO' hO'ne q
  obtain ⟨ρ', hρ', hBqO, hw'Bq⟩ := exists_closedBall_subset_not_mem hO ⟨hqT, hqBp⟩ hw'q
  set Bq := closedBall q ρ'
  have hqBq : q ∈ Bq := mem_closedBall_self hρ'.le
  have hBpBq : ∀ x, x ∈ Bp → x ∉ Bq := fun x hx hx' => (hBqO hx').2 hx
  have hfarl : ∀ {j : Fin n} {x : S}, x ∈ T.link j → x ∈ Bq → n - 2 ≤ j.val := fun {j x} hj hx => by
    by_contra h
    exact chain_not_mem_of_far T (i := il) (j := j) (by simp [il]; omega) (hBqO hx).1 hj
  -- the new links
  set R : Fin n → Set S := fun j => {x | (j.val = 1 ∧ x ∈ Bp) ∨ (j.val = n - 2 ∧ x ∈ Bq)}
  have hRc : ∀ j, IsClosed (R j) := fun j => by
    show IsClosed ({_x : S | j.val = 1} ∩ Bp ∪ {_x : S | j.val = n - 2} ∩ Bq)
    exact (isClosed_const.inter isClosed_closedBall).union (isClosed_const.inter isClosed_closedBall)
  set L : Fin n → Set S := fun j => T.link j \ R j
  have hLo : ∀ j, IsOpen (L j) := fun j => (T.isOpen j).sdiff (hRc j)
  have hLT : ∀ j, L j ⊆ T.link j := fun j => diff_subset
  have hcov : ∀ x : S, ∃ j, x ∈ L j := fun x => by
    by_cases hxp : x ∈ Bp
    · refine ⟨i0, hBp0 hxp, ?_⟩
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · simp [i0] at h
      · exact hBpBq x hxp h
    by_cases hxq : x ∈ Bq
    · refine ⟨il, (hBqO hxq).1, ?_⟩
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact hxp h
      · simp [il] at h; omega
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hT (mem_univ x))
    exact ⟨j, hj, by rintro (⟨-, h⟩ | ⟨-, h⟩); exacts [hxp h, hxq h]⟩
  have hLne : ∀ j, (L j ∩ univ).Nonempty := fun j => by
    rw [inter_univ]
    by_cases h1 : j.val = 1
    · have hj : j = i1 := Fin.ext h1
      refine ⟨w, hj ▸ hw1, ?_⟩
      rintro (⟨-, h⟩ | ⟨h, h'⟩)
      · exact hwBp h
      · have := hfarl hw0 h'; simp [i0] at this; omega
    by_cases h2 : j.val = n - 2
    · have hj : j = il2 := Fin.ext h2
      refine ⟨w', hj ▸ hw'2, ?_⟩
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact h1 h
      · exact hw'Bq h
    · obtain ⟨x, hx⟩ := T.link_nonempty j
      exact ⟨x, hx, by rintro (⟨h, -⟩ | ⟨h, -⟩); exacts [h1 h, h2 h]⟩
  have hLdisj : ∀ i j : Fin n, 1 < ((i : ℤ) - j).natAbs → L i ∩ L j = ∅ := fun i j hij =>
    eq_empty_of_forall_notMem fun x hx => chain_not_mem_of_far T hij (hLT i hx.1) (hLT j hx.2)
  let T' : Chain S n :=
    { link := L
      isOpen := hLo
      adjacent := fun i j => by
        constructor
        · intro h
          by_contra h'
          push_neg at h'
          rw [hLdisj i j h'] at h
          exact not_nonempty_empty h
        · intro h
          rcases lt_trichotomy i.val j.val with hlt | heq | hgt
          · exact adjacent_meet_of_cover isPreconnected_univ L hLo
              (fun x _ => mem_iUnion.2 (hcov x)) hLne hLdisj i j (by omega)
          · have : i = j := Fin.ext heq
            subst this
            obtain ⟨x, hx, -⟩ := hLne i
            exact ⟨x, hx, hx⟩
          · rw [inter_comm]
            exact adjacent_meet_of_cover isPreconnected_univ L hLo
              (fun x _ => mem_iUnion.2 (hcov x)) hLne hLdisj j i (by omega) }
  refine ⟨T', hLT, fun x _ => mem_iUnion.2 (hcov x), p, q, ⟨hn, ?_, ?_, ?_, ?_⟩,
    fun h => hqBp (h ▸ hpBp), hq⟩
  · refine ⟨hp, ?_⟩
    rintro (⟨h, -⟩ | ⟨-, h⟩)
    · simp at h
    · exact hBpBq p hpBp h
  · refine ⟨hqT, ?_⟩
    rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact hqBp h
    · simp at h; omega
  · intro i ⟨hpi, hpR⟩
    have h := hfar0 hpi hpBp
    apply Fin.ext
    show i.val = 0
    by_contra h0
    exact hpR (Or.inl ⟨by omega, hpBp⟩)
  · intro i ⟨hqi, hqR⟩
    have h := hfarl hqi hqBq
    apply Fin.ext
    show i.val = n - 1
    by_contra h0
    have := i.2
    exact hqR (Or.inr ⟨by omega, hqBq⟩)

/-! ### A description with a prescribed first level -/

section Prepend

variable {p q : S}

/-- The link counts of `T` followed by the tail of `Δ` from level `k`. -/
def prependN (n : ℕ) (Δ : Description S p q) (k : ℕ) : ℕ → ℕ
  | 0 => n
  | i + 1 => Δ.n (k + i)

/-- The levels of `T` followed by the tail of `Δ` from level `k`. -/
def prependD {n : ℕ} (T : Chain S n) (Δ : Description S p q) (k : ℕ) :
    (i : ℕ) → Chain S (prependN n Δ k i)
  | 0 => T
  | i + 1 => Δ.D (k + i)

/-- The mesh bounds. -/
def prependε (e0 : ℝ) (Δ : Description S p q) (k : ℕ) : ℕ → ℝ
  | 0 => e0
  | i + 1 => Δ.ε (k + i)

/-- **The description `T, D_k, D_{k+1}, …`** (Bing–Jones p. 177: "a sequence of chains from `p₁`
to `p₂` such that … `D = D₁`", assumed there without comment). -/
noncomputable def prependDesc {n : ℕ} (T : Chain S n) (Δ : Description S p q) (k : ℕ)
    (hT : T.IsFrom p q) (hcr : (Δ.D k).IsCrookedIn' T)
    (hcl : ∀ t, ∃ s, closure ((Δ.D k).link t) ⊆ T.link s) (e0 : ℝ) (he0 : 0 < e0)
    (hbdd : ∀ t, Bornology.IsBounded (T.link t)) (hdiam : ∀ t, diam (T.link t) ≤ e0) :
    Description S p q where
  n := prependN n Δ k
  D := prependD T Δ k
  isFrom i := match i with
    | 0 => hT
    | i + 1 => Δ.isFrom (k + i)
  crooked i := match i with
    | 0 => hcr
    | i + 1 => Δ.crooked (k + i)
  closure_subset i := match i with
    | 0 => hcl
    | i + 1 => Δ.closure_subset (k + i)
  ε := prependε e0 Δ k
  ε_pos i := match i with
    | 0 => he0
    | i + 1 => Δ.ε_pos (k + i)
  ε_tendsto := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    exact Δ.ε_tendsto.comp (Filter.tendsto_atTop_atTop_of_monotone
      (fun a b h => by omega) (fun b => ⟨b, by omega⟩))
  bdd i := match i with
    | 0 => hbdd
    | i + 1 => Δ.bdd (k + i)
  diam_le i := match i with
    | 0 => hdiam
    | i + 1 => Δ.diam_le (k + i)

end Prepend

/-- **Following a pattern in a given chain** (Bing 1948 Theorem 6 for the description
`T, D_k, D_{k+1}, …`). -/
theorem exists_follow_pattern (hP : IsPseudoArc (univ : Set S)) {n : ℕ} (T : Chain S n)
    (hT : univ ⊆ T.union) {p q : S} (hTpq : T.IsFrom p q) (hpq : p ≠ q)
    (hcomp : q ∉ composant (univ : Set S) p) {N : ℕ} (x : Fin N → Fin n)
    (hx : Description.IsPattern x) :
    ∃ E : Chain S N, univ ⊆ E.union ∧ E.FollowsPattern x T := by
  have hHI : ∀ K : Set S, Fold.Q78.IsContinuum K → Fold.Q78.IsIndecomposable K :=
    fun K hK => hP.2.1 K (subset_univ K) hK
  obtain ⟨Δ0, hΔ0⟩ := PA51.exists_description_univ hHI hP.1.2 hpq hcomp
  -- a Lebesgue number of `T`, and a level from which every link closure lies in a link of `T`
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_univ T.isOpen hT
  obtain ⟨k0, hk0⟩ := (Δ0.ε_tendsto.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ / 2))).exists_forall_of_atTop
  have hcl : ∀ k, k0 ≤ k → ∀ t, ∃ s, closure ((Δ0.D k).link t) ⊆ T.link s := by
    intro k hk t
    obtain ⟨y, hy⟩ := (Δ0.D k).link_nonempty t
    obtain ⟨s, hs⟩ := hleb y (mem_univ y)
    refine ⟨s, (closure_minimal (fun z hz => ?_) isClosed_closedBall).trans
      ((closedBall_subset_ball (by linarith [hk0 k hk] :
        Δ0.ε k < δ)).trans hs)⟩
    rw [mem_closedBall, dist_comm]
    exact (dist_le_diam_of_mem (Δ0.bdd k t) hy hz).trans (Δ0.diam_le k t)
  -- crookedness eventually
  have hcov : ∀ x : S, ∃ l, x ∈ T.link l := fun x => mem_iUnion.1 (hT (mem_univ x))
  have hev := PA51.eventually_crookedIn hHI T hcov (fun m => Δ0.D (k0 + m))
    (fun m t => by
      obtain ⟨s, hs⟩ := hcl (k0 + m) (by omega) t
      exact ⟨s, subset_closure.trans hs⟩)
    (fun m => Δ0.ε (k0 + m)) (fun m => (Δ0.ε_pos _).le)
    (Δ0.ε_tendsto.comp (Filter.tendsto_atTop_atTop_of_monotone
      (fun a b h => by omega) (fun b => ⟨b, by omega⟩)))
    (fun m t => Δ0.bdd _ t) (fun m t => Δ0.diam_le _ t)
  obtain ⟨m0, hm0⟩ := hev.exists
  set k := k0 + m0
  -- the bound for level `0`
  obtain ⟨e0, he0, he0'⟩ : ∃ e0 : ℝ, 0 < e0 ∧ ∀ t, diam (T.link t) ≤ e0 := by
    refine ⟨diam (univ : Set S) + 1, by linarith [diam_nonneg (s := (univ : Set S))], fun t => ?_⟩
    exact (diam_mono (subset_univ _) isBounded_of_compactSpace).trans (by linarith)
  set Δ := prependDesc T Δ0 k hTpq hm0 (hcl k (by omega)) e0 he0
    (fun _ => isBounded_of_compactSpace) he0'
  obtain ⟨j, -, E, -, hEcons, hEfol⟩ := Description.theorem6Pos_of_ne Δ hpq N x hx
  refine ⟨E, fun z _ => ?_, hEfol⟩
  have hM : z ∈ Δ.M := by
    simp only [Description.M, mem_iInter]
    intro i
    match i with
    | 0 => exact hT (mem_univ z)
    | i + 1 => exact Δ0.M_subset_union (k + i) (hΔ0 ▸ mem_univ z)
  exact Description.M_subset_consolidation Δ hEcons hM

/-- The case `r ≤ s` of `bj7_compact`. -/
theorem bj7_compact_of_le (hP : IsPseudoArc (univ : Set S)) {n m : ℕ} (T : Chain S n)
    (hT : univ ⊆ T.union) (H : Fin m → Fin n) (hH : IsChainMap H) {r s : Fin m} (hrs : r ≤ s)
    (hr : (H r).val = 0) (hs : (H s).val = n - 1) :
    ∃ E : Chain S m, univ ⊆ E.union ∧ ∀ i, E.link i ⊆ T.link (H i) := by
  obtain ⟨T', hT'T, hT'cov, p, q, hfrom, hpq, hcomp⟩ := exists_chain_isFrom hP T hT
  obtain ⟨E', hE'cov, hE'fol⟩ := exists_follow_pattern hP T' hT'cov hfrom hpq hcomp
    (H ∘ unfoldFin r s r.2) (isPattern_unfold H hH hrs hr hs)
  refine ⟨foldChain E' (unfoldFin r s r.2) (unfoldFin_adj r s r.2) (unfoldMain r s)
    (unfoldFin_main r s r.2) (unfoldMain_adj r s), fun z _ => ?_, fun i z hz => ?_⟩
  · obtain ⟨k, hk⟩ := mem_iUnion.1 (hE'cov (mem_univ z))
    exact mem_iUnion.2 ⟨_, link_subset_foldChain E' _ _ _ _ _ k hk⟩
  · rw [foldChain_link] at hz
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 hz
    have := hT'T _ (hE'fol k hzk)
    simp only [Function.comp] at this
    rwa [hk] at this

/-- **Bing–Jones Theorem 7, first sentence, in a compact pseudo-arc** (without Bing–Jones's
positive-distance condition on the conclusion). -/
theorem bj7_compact (hP : IsPseudoArc (univ : Set S)) {n m : ℕ} (T : Chain S n)
    (hT : univ ⊆ T.union) (H : Fin m → Fin n) (hH : IsChainMap H)
    (hHs : Function.Surjective H) :
    ∃ E : Chain S m, univ ⊆ E.union ∧ ∀ i, E.link i ⊆ T.link (H i) := by
  obtain ⟨x₀⟩ : Nonempty S := ⟨hP.2.2.nonempty.some⟩
  have hn : 0 < n := by
    obtain ⟨i, -⟩ := mem_iUnion.1 (hT (mem_univ x₀))
    exact i.pos
  obtain ⟨r, hr⟩ := hHs ⟨0, hn⟩
  obtain ⟨s, hs⟩ := hHs ⟨n - 1, by omega⟩
  rcases le_total r s with hrs | hsr
  · exact bj7_compact_of_le hP T hT H hH hrs (by rw [hr]) (by rw [hs])
  · -- reverse the indices of the domain
    have hH' : IsChainMap (H ∘ Fin.rev) := fun i j hij => hH _ _ (by
      simp only [Fin.val_rev]; omega)
    obtain ⟨E, hEcov, hET⟩ := bj7_compact_of_le hP T hT (H ∘ Fin.rev) hH'
      (r := Fin.rev r) (s := Fin.rev s) (Fin.rev_le_rev.2 hsr)
      (by simp [hr]) (by simp [hs])
    refine ⟨E.reverse, fun z hz => ?_, fun i => ?_⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.1 (hEcov hz)
      exact mem_iUnion.2 ⟨Fin.rev k, by rw [Chain.reverse_link, Fin.rev_rev]; exact hk⟩
    · rw [Chain.reverse_link]
      have := hET (Fin.rev i)
      simp only [Function.comp, Fin.rev_rev] at this
      exact this

end HPC.BJ59
