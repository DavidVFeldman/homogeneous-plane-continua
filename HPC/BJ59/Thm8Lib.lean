import HPC.BJ59.BJ59B
import HPC.BJ59.Step1b
import HPC.BJ59.Private

/-!
# Batch 200, §4: tools for Theorem 8

* `family_meets_all`: a preconnected set covered by open sets indexed by `Fin m`, nonadjacent ones
  disjoint, meeting the sets `u` and `v`, meets every set between them;
* `isBJChain_foldChain`: folding keeps chains in Bing–Jones's sense;
* `exists_deep_radius`: an open set meeting every fibre of an open map onto `[0, 1]` contains a
  ball of a fixed radius about a point of each fibre (commission 200 §4, step 1);
* `bj_cut`: Bing–Jones's Theorem 4 for an open set over an interval `(α, β)`, with the two closed
  pieces located: the piece through `g₀` lies over `[0, β)`, the one through `g₁` over `(α, 1]`
  (commission 200 §4, step 4).
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Thm8Lib

variable {X : Type*} [MetricSpace X]

/-- A preconnected set covered by open sets indexed by `Fin m`, nonadjacent ones disjoint, and
meeting the sets `u` and `v`, meets every set between them. -/
theorem family_meets_all {m : ℕ} (W : Fin m → Set X) (hW : ∀ i, IsOpen (W i))
    (hdisj : ∀ i j : Fin m, 1 < ((i : ℤ) - j).natAbs → W i ∩ W j = ∅)
    {S : Set X} (hS : IsPreconnected S) (hcov : S ⊆ ⋃ i, W i) (u v : Fin m)
    (hu : (W u ∩ S).Nonempty) (hv : (W v ∩ S).Nonempty) (k : Fin m)
    (huk : u.val ≤ k.val) (hkv : k.val ≤ v.val) : (W k ∩ S).Nonempty := by
  by_contra hno
  rw [not_nonempty_iff_eq_empty] at hno
  have hku : u.val < k.val := by
    rcases eq_or_lt_of_le huk with h | h
    · have : u = k := Fin.ext h
      subst this; rw [hno] at hu; exact absurd hu not_nonempty_empty
    · exact h
  have hkv' : k.val < v.val := by
    rcases eq_or_lt_of_le hkv with h | h
    · have : k = v := Fin.ext h
      subst this; rw [hno] at hv; exact absurd hv not_nonempty_empty
    · exact h
  set A : Set X := ⋃ (j : Fin m) (_ : j.val < k.val), W j
  set B : Set X := ⋃ (j : Fin m) (_ : k.val < j.val), W j
  have hA : IsOpen A := isOpen_iUnion fun j => isOpen_iUnion fun _ => hW j
  have hB : IsOpen B := isOpen_iUnion fun j => isOpen_iUnion fun _ => hW j
  have hSAB : S ⊆ A ∪ B := by
    intro x hx
    obtain ⟨j, hxj⟩ := mem_iUnion.1 (hcov hx)
    rcases lt_trichotomy j.val k.val with h | h | h
    · exact Or.inl (mem_iUnion₂.2 ⟨j, h, hxj⟩)
    · have : j = k := Fin.ext h
      subst this
      exact absurd (⟨x, hxj, hx⟩ : (W j ∩ S).Nonempty) (by rw [hno]; exact not_nonempty_empty)
    · exact Or.inr (mem_iUnion₂.2 ⟨j, h, hxj⟩)
  obtain ⟨a, hau, haS⟩ := hu
  obtain ⟨b, hbv, hbS⟩ := hv
  obtain ⟨x, -, hxA, hxB⟩ := hS A B hA hB hSAB ⟨a, haS, mem_iUnion₂.2 ⟨u, hku, hau⟩⟩
    ⟨b, hbS, mem_iUnion₂.2 ⟨v, hkv', hbv⟩⟩
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hxA
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hxB
  have := hdisj i j (by omega)
  exact (this ▸ (⟨hxi, hxj⟩ : x ∈ W i ∩ W j) : x ∈ (∅ : Set X))

/-- **Folding keeps chains in Bing–Jones's sense.** -/
theorem isBJChain_foldChain {N m : ℕ} (E : Chain X N) (hE : IsBJChain E) (π : Fin N → Fin m)
    (hπ : ∀ k l : Fin N, ((k : ℤ) - l).natAbs ≤ 1 → ((π k : ℤ) - π l).natAbs ≤ 1)
    (main : Fin m → Fin N) (hmain : ∀ i, π (main i) = i)
    (hmainadj : ∀ i j : Fin m, ((i : ℤ) - j).natAbs ≤ 1 → ((main i : ℤ) - main j).natAbs ≤ 1) :
    IsBJChain (foldChain E π hπ main hmain hmainadj) := by
  classical
  intro i j hij
  have hpair : ∀ p : Fin N × Fin N, ∃ δ > 0, 1 < ((p.1 : ℤ) - p.2).natAbs →
      ∀ x ∈ E.link p.1, ∀ y ∈ E.link p.2, δ ≤ dist x y := by
    intro p
    by_cases h : 1 < ((p.1 : ℤ) - p.2).natAbs
    · obtain ⟨δ, hδ, hd⟩ := hE p.1 p.2 h
      exact ⟨δ, hδ, fun _ => hd⟩
    · exact ⟨1, one_pos, fun h' => absurd h' h⟩
  choose δ hδ hδd using hpair
  obtain ⟨r, hr, hrle⟩ := exists_pos_forall_le δ hδ
  refine ⟨r, hr, fun x hx y hy => ?_⟩
  rw [foldChain_link] at hx hy
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx
  obtain ⟨l, hl, hyl⟩ := mem_iUnion₂.1 hy
  have hkl : 1 < ((k : ℤ) - l).natAbs := by
    by_contra h
    push_neg at h
    have := hπ k l h
    rw [hk, hl] at this
    omega
  exact (hrle (k, l)).trans (hδd (k, l) hkl x hxk y hyl)

/-- **Deep points** (commission 200 §4, step 1): an open set meeting every fibre of an open map of
a compact space onto `[0, 1]` contains a ball of a fixed radius `3ρ` about a point of each
fibre. -/
theorem exists_deep_radius [CompactSpace X] {f : X → unitInterval} (hfo : IsOpenMap f)
    {d : Set X} (hd : IsOpen d) (hdf : ∀ t, (d ∩ f ⁻¹' {t}).Nonempty) :
    ∃ ρ > 0, ∀ t, ∃ y ∈ f ⁻¹' {t}, ball y (3 * ρ) ⊆ d := by
  classical
  choose y hyd hyf using hdf
  choose r hr hrd using fun t => Metric.isOpen_iff.1 hd (y t) (hyd t)
  set O : unitInterval → Set unitInterval := fun t => f '' ball (y t) (r t / 4)
  have hO : ∀ t, IsOpen (O t) := fun t => hfo _ isOpen_ball
  have htO : ∀ t, t ∈ O t := fun t => ⟨y t, mem_ball_self (by linarith [hr t]), hyf t⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO fun t _ => mem_iUnion.2 ⟨t, htO t⟩
  obtain ⟨ρ, hρ, hρle⟩ := exists_pos_forall_le (fun t : {t // t ∈ s} => r t / 4)
    fun t => by simp only; linarith [hr t]
  refine ⟨ρ, hρ, fun t' => ?_⟩
  obtain ⟨t, hts, ht'⟩ := mem_iUnion₂.1 (hs (mem_univ t'))
  obtain ⟨y', hy', hy'f⟩ := ht'
  refine ⟨y', hy'f, fun z hz => hrd t ?_⟩
  have h1 : ρ ≤ r t / 4 := hρle ⟨t, hts⟩
  rw [mem_ball] at hz hy' ⊢
  linarith [dist_triangle z y' (y t)]

/-- **Theorem 4 over an interval**: an open set `V` over `(α, β)` separates `X − V` into closed
pieces containing `g₀` and `g₁`, the first over `[0, β)` and the second over `(α, 1]`. -/
theorem bj_cut [CompactSpace X] {f : X → unitInterval} (hf : IsArcOfContinua f)
    (hS : IsSnakeLike (univ : Set X)) {V : Set X} (hV : IsOpen V) (hVne : V.Nonempty)
    {α β : ℝ} (hα : 0 < α) (hβ : β < 1) (hVf : ∀ x ∈ V, α < f x ∧ (f x : ℝ) < β) :
    ∃ L R : Set X, IsClosed L ∧ IsClosed R ∧ Disjoint L R ∧ L ∪ R = Vᶜ ∧
      (∀ x ∈ L, (f x : ℝ) < β) ∧ (∀ x ∈ R, α < (f x : ℝ)) := by
  have hV01 : Disjoint V (f ⁻¹' {0, 1}) := by
    rw [Set.disjoint_left]
    intro x hx h01
    have := hVf x hx
    rcases h01 with h | h
    · rw [h] at this; simp at this; linarith
    · rw [h] at this; simp at this; linarith
  obtain ⟨L, R, hL, hR, hLR, hLRV, h0, h1⟩ := bj_theorem4 hf hS hV hVne hV01
  have hfib : ∀ t, IsPreconnected (f ⁻¹' {t}) := fun t => (hf.2.2 t).2.isPreconnected
  obtain ⟨z, hz⟩ := hVne
  have hαβ := hVf z hz
  have hαz : α ≤ 1 := by have := (f z).2.2; linarith [hαβ.1]
  have hβz : 0 ≤ β := by have := (f z).2.1; linarith [hαβ.2]
  refine ⟨L, R, hL, hR, hLR, hLRV, fun x hxL => ?_, fun x hxR => ?_⟩
  · by_contra hx
    push_neg at hx
    set b : unitInterval := ⟨β, hβz, hβ.le⟩
    have hS' := isPreconnected_preimage_Icc hf.1 hf.2.1 hfib b 1
    have hsub : f ⁻¹' Icc b 1 ⊆ L ∪ R := by
      rw [hLRV]
      intro w hw hwV
      have h1 : (b : ℝ) ≤ f w := hw.1
      linarith [(hVf w hwV).2]
    obtain ⟨w1, hw1⟩ := hf.2.1 1
    obtain ⟨w, -, hwL, hwR⟩ := isPreconnected_closed_iff.1 hS' L R hL hR hsub
      ⟨x, ⟨show b ≤ f x from hx, (f x).2.2⟩, hxL⟩
      ⟨w1, ⟨by rw [hw1]; exact b.2.2, by rw [hw1]⟩, h1 hw1⟩
    exact Set.disjoint_left.1 hLR hwL hwR
  · by_contra hx
    push_neg at hx
    set a : unitInterval := ⟨α, hα.le, hαz⟩
    have hS' := isPreconnected_preimage_Icc hf.1 hf.2.1 hfib 0 a
    have hsub : f ⁻¹' Icc 0 a ⊆ L ∪ R := by
      rw [hLRV]
      intro w hw hwV
      have h1 : (f w : ℝ) ≤ a := hw.2
      linarith [(hVf w hwV).1]
    obtain ⟨w0, hw0⟩ := hf.2.1 0
    obtain ⟨w, -, hwL, hwR⟩ := isPreconnected_closed_iff.1 hS' L R hL hR hsub
      ⟨w0, ⟨by rw [hw0], by rw [hw0]; exact a.2.1⟩, h0 hw0⟩
      ⟨x, ⟨(f x).2.1, show f x ≤ a from hx⟩, hxR⟩
    exact Set.disjoint_left.1 hLR hwL hwR

/-- **The sets `U_A ⊇ cl U′_A`** of commission 200 §4 (steps 1 and 7): inside an open set meeting
every fibre (and not everything), an open set with closure in it and a smaller set, with compact
closure inside the first, still meeting every fibre. -/
theorem exists_deep_sets [CompactSpace X] {f : X → unitInterval} (hfo : IsOpenMap f)
    {d : Set X} (hd : IsOpen d) (hdf : ∀ t, (d ∩ f ⁻¹' {t}).Nonempty) (hdc : dᶜ.Nonempty) :
    ∃ U U' : Set X, IsOpen U ∧ closure U ⊆ d ∧ closure U' ⊆ U ∧ IsCompact (closure U') ∧
      ∀ t, (U' ∩ f ⁻¹' {t}).Nonempty := by
  obtain ⟨ρ, hρ, hdeep⟩ := exists_deep_radius hfo hd hdf
  refine ⟨{z | ρ < infDist z dᶜ}, {z | 2 * ρ < infDist z dᶜ},
    isOpen_lt continuous_const (continuous_infDist_pt _), ?_, ?_, isClosed_closure.isCompact,
    fun t => ?_⟩
  · refine (closure_minimal (t := {z | ρ ≤ infDist z dᶜ}) (fun z (hz : ρ < infDist z dᶜ) => (le_of_lt hz : ρ ≤ infDist z dᶜ))
      (isClosed_le continuous_const (continuous_infDist_pt _))).trans ?_
    intro z hz
    by_contra hzd
    have := infDist_zero_of_mem (show z ∈ dᶜ from hzd)
    simp only [mem_setOf_eq] at hz
    linarith
  · refine (closure_minimal (t := {z | 2 * ρ ≤ infDist z dᶜ}) (fun z (hz : 2 * ρ < infDist z dᶜ) => (le_of_lt hz : 2 * ρ ≤ infDist z dᶜ))
      (isClosed_le continuous_const (continuous_infDist_pt _))).trans ?_
    intro z hz
    simp only [mem_setOf_eq] at hz ⊢
    linarith
  · obtain ⟨y, hyf, hyb⟩ := hdeep t
    refine ⟨y, ?_, hyf⟩
    show 2 * ρ < infDist y dᶜ
    have : 3 * ρ ≤ infDist y dᶜ := by
      by_contra h
      push_neg at h
      obtain ⟨z, hz, hdz⟩ := (infDist_lt_iff hdc).1 h
      exact hz (hyb (by rw [mem_ball, dist_comm]; exact hdz))
    linarith

end Thm8Lib

end HPC.BJ59
