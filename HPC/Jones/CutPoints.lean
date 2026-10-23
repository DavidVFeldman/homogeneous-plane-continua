import HPC.Jones.Theorem13
import HPC.PseudoArc.T13Topo

/-!
# Batch 135: Jones 1948, Theorems 11, 12, 14–19 and the corollaries

Existence of weak cut points (§3), totally non-aposyndetic continua with one weak cut point (§4),
continua without weak cut points (§5).

Shape changes against the skeleton (each recorded at the statement):

* `theorem11`: `hzD : z ∉ D` dropped (it follows from `h2`).
* `totallyNonApos_exists_weakCutPoint`: `[Nonempty X]` dropped (`ConnectedSpace` gives it).
* `theorem16`, `theorem17_cor`: `[Nontrivial X]` dropped (the weak cut point `p` gives three
  distinct points).
* `theorem17`: `hp : IsWeakCutPoint p` dropped (unused).
-/

namespace HPC.Jones

open Set Topology Filter Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

omit [ConnectedSpace X] in
/-- **Theorem 11.** Let `z ∈ X` and `D` open (nonempty). Suppose `X` is non-aposyndetic at
every point of `D`, but aposyndetic at each point of `D` with respect to `z`. Then `D` contains a
point `x`, and `X` a point `y`, such that `y` cuts `x` from `z`.

*Shape change:* the skeleton's `hzD : z ∉ D` is dropped: it follows from `h2`. Connectedness of
`X` is not used. Jones's proof
(Baire, then Theorem 6) is followed, with `M₀` the closed set of points at distance `≥ 1/(n+1)`
from a point of a small closed ball at which `X` is not aposyndetic with respect to them. -/
theorem theorem11 {z : X} {D : Set X} (hD : IsOpen D) (hDne : D.Nonempty)
    (h1 : ∀ x ∈ D, ¬ AposyndeticAt x) (h2 : ∀ x ∈ D, AposAt x z) :
    ∃ x ∈ D, ∃ y, CutsPts y x z := by
  set F : ℕ → Set X := fun n => Prod.fst '' ({p : X × X | ¬ AposAt p.1 p.2} ∩
    {p : X × X | 1 / ((n : ℝ) + 1) ≤ dist p.1 p.2}) with hF
  have hFcl : ∀ n, IsClosed (F n) := fun n => isClosed_fst_image
    (isClosed_setOf_not_aposAt.inter (isClosed_le continuous_const continuous_dist))
  have hcov : D ⊆ ⋃ n, F n := by
    intro x hx
    have hx' := h1 x hx
    simp only [AposyndeticAt, not_forall] at hx'
    obtain ⟨y, hyx, hna⟩ := hx'
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.mpr (Ne.symm hyx))
    exact mem_iUnion.mpr ⟨n, (x, y), ⟨hna, hn.le⟩, rfl⟩
  obtain ⟨n, A, r, hr, hball⟩ := exists_ball_subset_of_closed_cover hD hDne hFcl hcov
  set δ := min (r / 2) (1 / (3 * ((n : ℝ) + 1))) with hδdef
  have hδ : 0 < δ := lt_min (half_pos hr) (by positivity)
  have hδr : δ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hδ3 : 3 * δ ≤ 1 / ((n : ℝ) + 1) := by
    have h1 : δ ≤ 1 / (3 * ((n : ℝ) + 1)) := min_le_right _ _
    have h2 : 1 / (3 * ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) / 3 := by field_simp
    rw [h2] at h1
    linarith
  set M₀ : Set X := Prod.snd '' ({p : X × X | p.1 ∈ closedBall A δ} ∩
    ({p : X × X | ¬ AposAt p.1 p.2} ∩ {p : X × X | 1 / ((n : ℝ) + 1) ≤ dist p.1 p.2}))
    with hM₀def
  have hM₀ : IsClosed M₀ := isClosed_snd_image ((isClosed_closedBall.preimage continuous_fst).inter
    (isClosed_setOf_not_aposAt.inter (isClosed_le continuous_const continuous_dist)))
  have hdisj : Disjoint (ball A δ) M₀ := by
    rw [Set.disjoint_left]
    rintro w hw ⟨⟨x, y⟩, ⟨hx, -, hd⟩, rfl⟩
    have hx' : dist x A ≤ δ := hx
    have hd' : 1 / ((n : ℝ) + 1) ≤ dist x y := hd
    have hw' : dist y A < δ := hw
    have htri : dist x y ≤ dist x A + dist A y := dist_triangle _ _ _
    rw [dist_comm A y] at htri
    linarith
  have hzM : z ∉ M₀ := by
    rintro ⟨⟨x, y⟩, ⟨hx, hna, -⟩, rfl⟩
    exact hna (h2 x (hball (closedBall_subset_ball hδr hx)).1)
  have hcover : ∀ x ∈ ball A δ, ∃ y ∈ M₀, ¬ AposAt x y := by
    intro x hx
    obtain ⟨⟨x', y⟩, ⟨hna, hd⟩, hx'⟩ := (hball (ball_subset_ball hδr.le hx)).2
    simp only at hx'
    subst hx'
    exact ⟨y, ⟨(x', y), ⟨ball_subset_closedBall hx, hna, hd⟩, rfl⟩, hna⟩
  obtain ⟨x₀, hx₀, y₀, -, hcut⟩ :=
    theorem6 isOpen_ball ⟨A, mem_ball_self hδ⟩ hM₀ hdisj hcover hzM
  exact ⟨x₀, (hball (ball_subset_ball hδr.le hx₀)).1, y₀, hcut⟩

omit [CompactSpace X] [ConnectedSpace X] in
/-- A point at which `X` is non-aposyndetic has a point other than itself. -/
theorem exists_ne_of_not_aposyndeticAt {x : X} (h : ¬ AposyndeticAt x) : ∃ w, w ≠ x := by
  simp only [AposyndeticAt, not_forall] at h
  obtain ⟨w, hw, -⟩ := h
  exact ⟨w, hw⟩

/-- **Theorem 12.** If `D` is open (nonempty) and `X` is non-aposyndetic at every point of `D`,
then `D` contains a point `x`, and `X` points `y`, `z`, such that `y` cuts `x` from `z`.
Indecomposable case: `z` outside the composant of `x` (`T13.exists_not_mem_proper_subcontinua`),
`y` any third point. Decomposable case: Theorem 10 and Theorem 11. -/
theorem theorem12 {D : Set X} (hD : IsOpen D) (hDne : D.Nonempty)
    (h : ∀ x ∈ D, ¬ AposyndeticAt x) : ∃ x ∈ D, ∃ y z, CutsPts y x z := by
  by_cases hdec : IsDecomposableSpace X
  · have hno : ¬ ∃ D' : Set X, IsOpen D' ∧ D'.Nonempty ∧ ∀ x ∈ D', ∀ y, y ≠ x → ¬ AposAt x y :=
      fun h' => theorem10.mpr h' hdec
    push_neg at hno
    obtain ⟨p, hpD, z, -, H, U, hH, hU, hpU, hUH, hzH⟩ := hno D hD hDne
    obtain ⟨x, hx, y, hcut⟩ := theorem11 (hD.inter hU) ⟨p, hpD, hpU⟩ (fun x hx => h x hx.1)
      (fun x hx => ⟨H, U, hH, hU, hx.2, hUH, hzH⟩)
    exact ⟨x, hx.1, y, z, hcut⟩
  · have hI : Fold.Q78.IsIndecomposable (univ : Set X) := by
      by_contra hI
      exact hdec (isDecomposableSpace_iff_not_isIndecomposable.mpr hI)
    obtain ⟨x, hx⟩ := hDne
    obtain ⟨w, hwx⟩ := exists_ne_of_not_aposyndeticAt (h x hx)
    haveI : Nontrivial X := ⟨⟨w, x, hwx⟩⟩
    obtain ⟨z, -, hz⟩ :=
      T13.exists_not_mem_proper_subcontinua (M := (univ : Set X)) hI (mem_univ x)
    have hxz : x ≠ z := by
      rintro rfl
      refine hz {x} ⟨isCompact_singleton, isConnected_singleton⟩ (subset_univ _) (fun he => ?_)
        rfl rfl
      have : w ∈ ({x} : Set X) := he ▸ mem_univ w
      exact hwx this
    obtain ⟨y, hyx, hyz⟩ := exists_ne_ne x z
    refine ⟨x, hx, y, z, fun e => hyx e.symm, fun e => hyz e.symm, hxz, fun K hK hxK hzK => ?_⟩
    by_contra hyK
    exact hz K hK (subset_univ _) (fun he => hyK (he ▸ mem_univ y)) hxK hzK

/-- **Corollary (p. 409).** A totally non-aposyndetic continuum contains a weak cut point.

*Shape change:* the skeleton's `[Nonempty X]` is dropped: `ConnectedSpace X` includes it. -/
theorem totallyNonApos_exists_weakCutPoint (h : TotallyNonAposyndetic X) :
    ∃ p : X, IsWeakCutPoint p := by
  obtain ⟨x, -, y, z, hcut⟩ := theorem12 isOpen_univ univ_nonempty (fun x _ => h x)
  exact ⟨y, x, z, hcut⟩

/-- **Theorem 14.** If for each `p` there is `q` such that `X` is not aposyndetic at `q` with
respect to `p`, then the weak cut points are dense. (\"Follows immediately from Theorem 13.\") -/
theorem theorem14 (h : ∀ p : X, ∃ q, q ≠ p ∧ ¬ AposAt q p) :
    Dense {p : X | IsWeakCutPoint p} := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨x, -, y, hyU, z, -, hcut⟩ := theorem13 hU hUne (fun p _ => h p)
  exact ⟨y, hyU, x, z, hcut⟩

/-- **Theorem 15.** If `X` is not semi-locally-connected at any point of the open set `U`, then
the weak cut points are dense in `U`. (Theorem 0 turns the hypothesis into that of Theorem 13,
applied to each open subset of `U`.) -/
theorem theorem15 {U : Set X} (hU : IsOpen U) (h : ∀ x ∈ U, ¬ SemiLocConnAt x) :
    U ⊆ closure {p : X | IsWeakCutPoint p} := by
  intro x hx
  rw [_root_.mem_closure_iff]
  intro O hO hxO
  have hno : ∀ p ∈ O ∩ U, ∃ o, o ≠ p ∧ ¬ AposAt o p := by
    intro p hp
    have := h p hp.2
    rw [theorem0] at this
    push_neg at this
    exact this
  obtain ⟨a, -, y, hyD, b, -, hcut⟩ := theorem13 (hO.inter hU) ⟨x, hxO, hx⟩ hno
  exact ⟨y, hyD.1, a, b, hcut⟩

/-- **Corollary (Theorem 15).** If `X` is semi-locally-connected at no point, then its weak cut
points are dense. -/
theorem theorem15_cor (h : ∀ x : X, ¬ SemiLocConnAt x) : Dense {p : X | IsWeakCutPoint p} := by
  have := theorem15 isOpen_univ (fun x _ => h x)
  exact fun x => this (mem_univ x)

omit [CompactSpace X] [ConnectedSpace X] in
/-- A weak cut point gives three distinct points. -/
theorem nontrivial_of_isWeakCutPoint {p : X} (hp : IsWeakCutPoint p) : Nontrivial X := by
  obtain ⟨x, -, hxp, -⟩ := hp
  exact ⟨⟨x, p, hxp⟩⟩

omit [CompactSpace X] in
/-- **Theorem 16.** If `X` has only one weak cut point `p`, the composant of `p` is `X`.
(Jones writes \"the composant of `M` containing `P`\"; `P` is the cut point.)

*Shape change:* the skeleton's `[Nontrivial X]` is dropped: the weak cut point `p` already gives
three distinct points. Proof as printed: for `x ≠ p` and a third point `y`, `y` does not cut `x`
from `p`, so `X − y` contains a continuum containing `p` and `x`. -/
theorem theorem16 {p : X} (hp : IsWeakCutPoint p)
    (honly : ∀ q, IsWeakCutPoint q → q = p) : composant p = univ := by
  haveI := nontrivial_of_isWeakCutPoint hp
  refine eq_univ_of_forall fun x => ?_
  by_cases hxp : x = p
  · subst hxp
    obtain ⟨c, hc⟩ := exists_ne x
    refine ⟨{x}, ⟨isCompact_singleton, isConnected_singleton⟩, fun he => ?_, rfl, rfl⟩
    have : c ∈ ({x} : Set X) := he ▸ mem_univ c
    exact hc this
  · obtain ⟨y, hyx, hyp⟩ := exists_ne_ne x p
    have hncut : ¬ CutsPts y x p := fun hc => hyp (honly y ⟨x, p, hc⟩)
    simp only [CutsPts, not_and, not_forall] at hncut
    obtain ⟨K, hK, hxK, hpK, hyK⟩ :=
      hncut (fun e => hyx e.symm) (fun e => hyp e.symm) hxp
    exact ⟨K, hK, fun he => hyK (he ▸ mem_univ y), hpK, hxK⟩

omit [ConnectedSpace X] in
/-- **Theorem 17.** If `X` is totally non-aposyndetic with only one weak cut point `p`, then `X` is
non-aposyndetic at each point of `X − p` with respect to `p`. (Proof as printed, via Theorem 11.)

*Shape change:* the skeleton's `hp : IsWeakCutPoint p` is dropped: it is not used. Connectedness
of `X` is not used either. -/
theorem theorem17 (htn : TotallyNonAposyndetic X) {p : X}
    (honly : ∀ q, IsWeakCutPoint q → q = p) : ∀ x, x ≠ p → ¬ AposAt x p := by
  rintro x - ⟨H, U, hH, hU, hxU, hUH, hpH⟩
  obtain ⟨x', -, y, hcut⟩ := theorem11 hU ⟨x, hxU⟩ (fun x' _ => htn x')
    (fun x' hx' => ⟨H, U, hH, hU, hx', hUH, hpH⟩)
  have hyp : y = p := honly y ⟨x', p, hcut⟩
  exact hcut.2.1 hyp.symm

/-- **Corollary (Theorem 17).** Under the same hypotheses, `X` is not semi-locally-connected at
`p`.

*Shape change:* the skeleton's `[Nontrivial X]` is dropped: `hp` gives a point other than `p`. -/
theorem theorem17_cor (htn : TotallyNonAposyndetic X) {p : X}
    (hp : IsWeakCutPoint p) (honly : ∀ q, IsWeakCutPoint q → q = p) : ¬ SemiLocConnAt p := by
  rw [theorem0]
  intro h
  obtain ⟨x, -, hxp, -⟩ := hp
  exact theorem17 htn honly x hxp (h x hxp)

/-- **Theorem 18.** If `X` contains no weak cut point, the set of points at which `X` is both
aposyndetic and semi-locally-connected is a dense `G_δ`. (Theorems 4 and 5 make its complement an
`F_σ`; by Theorems 12 and 15 the closed pieces have empty interior; Baire.) -/
theorem theorem18 (h : ∀ p : X, ¬ IsWeakCutPoint p) :
    IsGδ {x : X | AposyndeticAt x ∧ SemiLocConnAt x} ∧
      Dense {x : X | AposyndeticAt x ∧ SemiLocConnAt x} := by
  obtain ⟨F, hFc, hFeq⟩ := theorem4 (X := X)
  obtain ⟨G, hGc, hGeq⟩ := theorem5 (X := X)
  have hF' : ∀ i, F i ⊆ {x | ¬ AposyndeticAt x} := fun i => hFeq ▸ subset_iUnion F i
  have hG' : ∀ i, G i ⊆ {x | ¬ SemiLocConnAt x} := fun i => hGeq ▸ subset_iUnion G i
  have hS : {x : X | AposyndeticAt x ∧ SemiLocConnAt x} = ⋂ i, ((F i)ᶜ ∩ (G i)ᶜ) := by
    ext x
    simp only [mem_setOf_eq, mem_iInter, mem_inter_iff, mem_compl_iff]
    constructor
    · rintro ⟨ha, hs⟩ i
      exact ⟨fun hx => hF' i hx ha, fun hx => hG' i hx hs⟩
    · intro hall
      refine ⟨?_, ?_⟩
      · by_contra hna
        have : x ∈ ⋃ i, F i := hFeq ▸ hna
        obtain ⟨i, hi⟩ := mem_iUnion.mp this
        exact (hall i).1 hi
      · by_contra hna
        have : x ∈ ⋃ i, G i := hGeq ▸ hna
        obtain ⟨i, hi⟩ := mem_iUnion.mp this
        exact (hall i).2 hi
  have hWe : {p : X | IsWeakCutPoint p} = ∅ := eq_empty_of_forall_notMem h
  have hopen : ∀ i, IsOpen ((F i)ᶜ ∩ (G i)ᶜ) := fun i =>
    (hFc i).isOpen_compl.inter (hGc i).isOpen_compl
  have hFd : ∀ i, Dense (F i)ᶜ := fun i => by
    rw [← interior_eq_empty_iff_dense_compl]
    by_contra hne
    obtain ⟨x, -, y, z, hcut⟩ := theorem12 isOpen_interior (nonempty_iff_ne_empty.mpr hne)
      (fun x hx => hF' i (interior_subset hx))
    exact h y ⟨x, z, hcut⟩
  have hGd : ∀ i, Dense (G i)ᶜ := fun i => by
    rw [← interior_eq_empty_iff_dense_compl]
    by_contra hne
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hne
    have := theorem15 isOpen_interior (fun x hx => hG' i (interior_subset hx)) hx
    rw [hWe, closure_empty] at this
    exact this
  rw [hS]
  exact ⟨IsGδ.iInter_of_isOpen hopen, dense_iInter_of_isOpen hopen fun i =>
    (hFd i).inter_of_isOpen_left (hGd i) (hFc i).isOpen_compl⟩

/-- **Theorem 19.** If the open set `U` (nonempty) contains no weak cut point, `U` contains a
point at which `X` is semi-locally-connected. (\"Follows from Theorem 15.\") -/
theorem theorem19 {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty)
    (h : ∀ p ∈ U, ¬ IsWeakCutPoint p) : ∃ x ∈ U, SemiLocConnAt x := by
  by_contra hno
  push_neg at hno
  obtain ⟨x, hx⟩ := hUne
  have hcl := theorem15 hU hno hx
  obtain ⟨p, hpU, hp⟩ := _root_.mem_closure_iff.mp hcl U hU hx
  exact h p hpU hp

end HPC.Jones
