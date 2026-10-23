import HPC.Jones.Jones49Chain

/-!
# Batch 150: the separating point-order theorem for an open set

For an open set `R` of a locally compact separable metric space, all but countably many separating
points of `R` (in the sense of batch 149's `IsSepPointOf p R`) are of order `2`
(`countable_sepPoint_not_hasOrder_two`). This is the core of Whyburn's (8.4), (8.41) and (9.2).

Proof. Each separating point `p` comes with a separation `R − p = A ∪ B` (open, disjoint) and points
`a ∈ A`, `b ∈ B` of the component of `R` containing `p`; choose basic open sets `U ∋ a`, `W ∋ b`
with `U ⊆ A`, `W ⊆ B`. For a fixed pair `(U, W)` the separating points not of order `≤ 2` with this
pair (`sepT R U W`) lie in one component of `R` (`sepT_mem_component`) and form a separation chain
(`SepChain`, `Jones49Chain.lean`), which is countable (`SepChain.countable_of_not_orderLE_two`).
There are countably many pairs `(U, W)`. Finally a separating point is never of order `≤ 1`
(`not_orderLE_one_of_isSepPointOf`).
-/

namespace HPC.Jones

open Set Topology Metric

section Sep

variable {X : Type*} [MetricSpace X]

/-- Order `≤ m` implies order `≤ n` for `m ≤ n`. -/
theorem OrderLE.mono {p : X} {m n : ℕ} (hmn : m ≤ n) (h : OrderLE p m) : OrderLE p n := by
  intro U hU
  obtain ⟨V, hVo, hpV, hVU, hfin, hcard⟩ := h U hU
  exact ⟨V, hVo, hpV, hVU, hfin, hcard.trans hmn⟩

/-- One side of a separation `R − q = A ∪ B` of an open... (any) set, cut down to a preconnected
`Q ∋ q` inside `R`, together with `q`, is preconnected. -/
theorem isPreconnected_diff_side {R Q A B : Set X} {q : X} (hQ : IsPreconnected Q) (hqQ : q ∈ Q)
    (hQR : Q ⊆ R) (hA : IsOpen A) (hB : IsOpen B) (hcov : A ∪ B = R \ {q})
    (hd : Disjoint A B) : IsPreconnected (Q \ B) := by
  have hqB : q ∉ B := fun h => by
    have : q ∈ A ∪ B := Or.inr h
    rw [hcov] at this; exact this.2 rfl
  have h := isPreconnected_side (A := A) (B := B) hQ hqQ hA hB
    (fun z hz => by rw [hcov]; exact ⟨hQR hz.1, hz.2⟩) (fun z _ hzA => disjoint_left.1 hd hzA)
  rwa [diff_singleton_eq_self hqB] at h

/-- A preconnected subset of `R` meeting both sides of a separation of `R − p` contains `p`. -/
theorem mem_of_isPreconnected_meets_sides {R D A B : Set X} {p : X} (hD : IsPreconnected D)
    (hDR : D ⊆ R) (hA : IsOpen A) (hB : IsOpen B) (hcov : A ∪ B = R \ {p}) (hd : Disjoint A B)
    {z w : X} (hzD : z ∈ D) (hzA : z ∈ A) (hwD : w ∈ D) (hwB : w ∈ B) : p ∈ D := by
  by_contra hpD
  have hsub : D ⊆ A ∪ B := fun v hv => by
    rw [hcov]; exact ⟨hDR hv, fun h => hpD (h ▸ hv)⟩
  have := hD.subset_left_of_subset_union hA hB hd hsub ⟨z, hzD, hzA⟩
  exact disjoint_left.1 hd (this hwD) hwB

/-- The separating points of `R` not of order `≤ 2` whose separation puts `U` and `W` on the two
sides, with `U` and `W` meeting the component of `R` containing the point. -/
def sepT (R U W : Set X) : Set X :=
  {p ∈ R | ¬ OrderLE p 2 ∧ ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ A ∪ B = R \ {p} ∧ Disjoint A B ∧
    U ⊆ A ∧ W ⊆ B ∧ (U ∩ connectedComponentIn R p).Nonempty ∧
    (W ∩ connectedComponentIn R p).Nonempty}

/-- Whyburn's (8.1)–(8.2), in the form needed: the points of `sepT R U W` lie in one component
of `R`. -/
theorem sepT_mem_component {R U W : Set X} {p q : X} (hp : p ∈ sepT R U W)
    (hq : q ∈ sepT R U W) : p ∈ connectedComponentIn R q := by
  obtain ⟨-, -, Ap, Bp, hApo, hBpo, hcovp, hdp, hUAp, hWBp, -, -⟩ := hp
  obtain ⟨hqR, -, Aq, Bq, hAqo, hBqo, hcovq, hdq, hUAq, hWBq, ⟨a, haU, haQ⟩, ⟨b, hbW, hbQ⟩⟩ := hq
  by_cases hpq : p = q
  · subst hpq; exact mem_connectedComponentIn hqR
  have hqRp : q ∈ Ap ∪ Bp := by rw [hcovp]; exact ⟨hqR, Ne.symm hpq⟩
  have hQ := isPreconnected_connectedComponentIn (F := R) (x := q)
  have hqQ := mem_connectedComponentIn hqR
  have hQR := connectedComponentIn_subset R q
  rcases hqRp with h | h
  · -- `q ∈ A p`: use the `B`-side of `q`, which contains `b ∈ W ⊆ B p`
    have hD := isPreconnected_diff_side hQ hqQ hQR hBqo hAqo (by rw [union_comm]; exact hcovq)
      hdq.symm
    exact (mem_of_isPreconnected_meets_sides hD (diff_subset.trans hQR) hApo hBpo hcovp hdp
      ⟨hqQ, fun hh => by
        have : q ∈ Aq ∪ Bq := Or.inl hh
        rw [hcovq] at this; exact this.2 rfl⟩ h
      ⟨hbQ, disjoint_right.1 hdq (hWBq hbW)⟩ (hWBp hbW)).1
  · have hD := isPreconnected_diff_side hQ hqQ hQR hAqo hBqo hcovq hdq
    exact (mem_of_isPreconnected_meets_sides hD (diff_subset.trans hQR) hApo hBpo hcovp hdp
      ⟨haQ, disjoint_left.1 hdq (hUAq haU)⟩ (hUAp haU)
      ⟨hqQ, fun hh => by
        have : q ∈ Aq ∪ Bq := Or.inr hh
        rw [hcovq] at this; exact this.2 rfl⟩ h).1

/-- For a fixed pair `(U, W)`, the set `sepT R U W` is countable. -/
theorem countable_sepT [LocallyCompactSpace X] [SecondCountableTopology X] {R : Set X}
    (hR : IsOpen R) (U W : Set X) : (sepT R U W).Countable := by
  rcases (sepT R U W).eq_empty_or_nonempty with h | ⟨p0, hp0⟩
  · rw [h]; exact countable_empty
  have hex : ∀ p ∈ sepT R U W, ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ A ∪ B = R \ {p} ∧
      Disjoint A B ∧ U ⊆ A ∧ W ⊆ B ∧ (U ∩ connectedComponentIn R p).Nonempty ∧
      (W ∩ connectedComponentIn R p).Nonempty := fun p hp => hp.2.2
  choose! A B hAo hBo hun hdisj hUA hWB hU hW using hex
  have hQ : ∀ p ∈ sepT R U W, connectedComponentIn R p = connectedComponentIn R p0 :=
    fun p hp => (connectedComponentIn_eq (sepT_mem_component hp hp0)).symm
  have hp0R : p0 ∈ R := hp0.1
  let C : SepChain X :=
    { R := R
      Q := connectedComponentIn R p0
      T := sepT R U W
      A := A
      B := B
      isOpen_A := hAo
      isOpen_B := hBo
      union_eq := hun
      disj := hdisj
      preconn := isPreconnected_connectedComponentIn
      Q_sub := connectedComponentIn_subset _ _
      T_sub := fun p hp => by rw [← hQ p hp]; exact mem_connectedComponentIn hp.1
      closed_in := closure_inter_connectedComponentIn_subset hp0R
      Q_max := fun D hD hDR ⟨z, hzD, hzQ⟩ => by
        rw [connectedComponentIn_eq hzQ]
        exact hD.subset_connectedComponentIn hzD hDR
      commonA := fun p hp q hq => by
        obtain ⟨a, haU, haQ⟩ := hU p hp
        rw [hQ p hp] at haQ
        exact ⟨a, ⟨haQ, hUA p hp haU⟩, hUA q hq haU⟩
      commonB := fun p hp q hq => by
        obtain ⟨b, hbW, hbQ⟩ := hW p hp
        rw [hQ p hp] at hbQ
        exact ⟨b, ⟨hbQ, hWB p hp hbW⟩, hWB q hq hbW⟩ }
  exact C.countable_of_not_orderLE_two hR fun p hp => hp.2.1

/-- **All but countably many separating points of an open set are of order `≤ 2`.** -/
theorem countable_sepPoint_not_orderLE_two [LocallyCompactSpace X]
    [TopologicalSpace.SeparableSpace X] {R : Set X} (hR : IsOpen R) :
    {p | IsSepPointOf p R ∧ ¬ OrderLE p 2}.Countable := by
  haveI : SecondCountableTopology X := inferInstance
  set 𝓑 := TopologicalSpace.countableBasis X
  have hB := TopologicalSpace.isBasis_countableBasis X
  have hc : (⋃ U ∈ 𝓑, ⋃ W ∈ 𝓑, sepT R U W).Countable :=
    (TopologicalSpace.countable_countableBasis X).biUnion fun U _ =>
      (TopologicalSpace.countable_countableBasis X).biUnion fun W _ => countable_sepT hR U W
  refine hc.mono ?_
  rintro p ⟨⟨hpR, A, B, hA, hB', hcov, hdisj, ⟨a, haA, haQ, hap⟩, ⟨b, hbB, hbQ, hbp⟩⟩, hno⟩
  have hRp : IsOpen (R \ {p}) := hR.sdiff isClosed_singleton
  have hQR := connectedComponentIn_subset R p
  have haA' : a ∈ A ∩ (R \ {p}) := ⟨haA, hQR haQ, hap⟩
  have hbB' : b ∈ B ∩ (R \ {p}) := ⟨hbB, hQR hbQ, hbp⟩
  obtain ⟨U, hU𝓑, haU, hUA⟩ := hB.exists_subset_of_mem_open haA' (hA.inter hRp)
  obtain ⟨W, hW𝓑, hbW, hWB⟩ := hB.exists_subset_of_mem_open hbB' (hB'.inter hRp)
  refine mem_biUnion hU𝓑 (mem_biUnion hW𝓑 ⟨hpR, hno, A ∩ (R \ {p}), B ∩ (R \ {p}),
    hA.inter hRp, hB'.inter hRp, ?_, hdisj, hUA, hWB, ⟨a, haU, haQ⟩, ⟨b, hbW, hbQ⟩⟩)
  ext z
  constructor
  · rintro (h | h)
    · exact h.2
    · exact h.2
  · intro hz
    rcases hcov hz with h | h
    · exact Or.inl ⟨h, hz⟩
    · exact Or.inr ⟨h, hz⟩

/-- **A separating point is not of order `≤ 1`.** Both sides of the separation, with `p`, are
preconnected and reach points other than `p`; a small open set about `p` has a frontier point on
each side. -/
theorem not_orderLE_one_of_isSepPointOf {p : X} {R : Set X} (h : IsSepPointOf p R) :
    ¬ OrderLE p 1 := by
  obtain ⟨hpR, A, B, hA, hB, hcov, hdisj, ⟨a, haA, haQ, hap⟩, ⟨b, hbB, hbQ, hbp⟩⟩ := h
  set Q := connectedComponentIn R p
  have hQR : Q ⊆ R := connectedComponentIn_subset R p
  have hpQ : p ∈ Q := mem_connectedComponentIn hpR
  have hQ : IsPreconnected Q := isPreconnected_connectedComponentIn
  have hcovQ : Q \ {p} ⊆ A ∪ B := fun z hz => hcov ⟨hQR hz.1, hz.2⟩
  have hd : ∀ z ∈ Q \ {p}, z ∈ A → z ∉ B := fun z hz hzA hzB =>
    disjoint_left.1 hdisj ⟨hzA, hQR hz.1, hz.2⟩ ⟨hzB, hQR hz.1, hz.2⟩
  have hDa := isPreconnected_side hQ hpQ hA hB hcovQ hd
  have hDb := isPreconnected_side (A := B) (B := A) hQ hpQ hB hA
    (fun z hz => (hcovQ hz).symm) (fun z hz hzB hzA => hd z hz hzA hzB)
  have hpDa : p ∈ Q \ (B \ {p}) := ⟨hpQ, fun h => h.2 rfl⟩
  have hpDb : p ∈ Q \ (A \ {p}) := ⟨hpQ, fun h => h.2 rfl⟩
  have haDa : a ∈ Q \ (B \ {p}) := ⟨haQ, fun h => hd a ⟨haQ, hap⟩ haA h.1⟩
  have hbDb : b ∈ Q \ (A \ {p}) := ⟨hbQ, fun h => hd b ⟨hbQ, hbp⟩ h.1 hbB⟩
  intro hord
  set r := min (dist a p) (dist b p) / 2
  have hr : 0 < r := half_pos (lt_min (dist_pos.2 hap) (dist_pos.2 hbp))
  obtain ⟨V, hVo, hpV, hVU, hfin, hcard⟩ := hord (ball p r) (ball_mem_nhds p hr)
  have haV : a ∉ V := fun h => by
    have := hVU h; rw [mem_ball] at this
    have : dist a p ≤ r := this.le
    have h2 : r < dist a p := by
      have := min_le_left (dist a p) (dist b p)
      have : 0 < dist a p := dist_pos.2 hap
      simp only [r]; linarith
    linarith
  have hbV : b ∉ V := fun h => by
    have := hVU h; rw [mem_ball] at this
    have : dist b p ≤ r := this.le
    have h2 : r < dist b p := by
      have := min_le_right (dist a p) (dist b p)
      have : 0 < dist b p := dist_pos.2 hbp
      simp only [r]; linarith
    linarith
  have hfp : ∀ {z}, z ∈ frontier V → z ≠ p := by
    rintro z hz rfl
    rw [hVo.frontier_eq] at hz; exact hz.2 hpV
  obtain ⟨u, ⟨huQ, huB⟩, huF⟩ := meets_frontier_of_isPreconnected hDa hpDa hpV haDa haV
  obtain ⟨v, ⟨hvQ, hvA⟩, hvF⟩ := meets_frontier_of_isPreconnected hDb hpDb hpV hbDb hbV
  have hup := hfp huF
  have hvp := hfp hvF
  have huA : u ∈ A := (hcovQ ⟨huQ, hup⟩).resolve_right fun h => huB ⟨h, hup⟩
  have hvB : v ∈ B := (hcovQ ⟨hvQ, hvp⟩).resolve_left fun h => hvA ⟨h, hvp⟩
  have huv : u ≠ v := by
    rintro rfl; exact hd u ⟨huQ, hup⟩ huA hvB
  have h2 : ({u, v} : Set X).ncard ≤ (frontier V).ncard := by
    refine ncard_le_ncard ?_ hfin
    intro z hz
    rcases hz with rfl | rfl
    · exact huF
    · exact hvF
  rw [ncard_pair huv] at h2
  omega

/-- A separating point of order `≤ 2` is of order `2`. -/
theorem hasOrder_two_of_isSepPointOf {p : X} {R : Set X} (h : IsSepPointOf p R)
    (h2 : OrderLE p 2) : HasOrder p 2 :=
  ⟨h2, fun m hm hm' => not_orderLE_one_of_isSepPointOf h (hm'.mono (by omega))⟩

/-- **Whyburn's separating point-order theorem for an open set.** -/
theorem countable_sepPoint_not_hasOrder_two [LocallyCompactSpace X]
    [TopologicalSpace.SeparableSpace X] {R : Set X} (hR : IsOpen R) :
    {p | IsSepPointOf p R ∧ ¬ HasOrder p 2}.Countable :=
  (countable_sepPoint_not_orderLE_two hR).mono fun p hp =>
    (⟨hp.1, fun h2 => hp.2 (hasOrder_two_of_isSepPointOf hp.1 h2)⟩ :
      IsSepPointOf p R ∧ ¬ OrderLE p 2)

/-! ### Whyburn's definitions, recorded (Ch. I and Ch. III §2) -/

/-- Whyburn's **generalized continuum** (*Analytic Topology*, Ch. I): a locally compact, separable,
connected metric space. (Recorded; (3.2) is used here for compact metric continua.) -/
def IsGeneralizedContinuum (Y : Type*) [MetricSpace Y] : Prop :=
  LocallyCompactSpace Y ∧ TopologicalSpace.SeparableSpace Y ∧ ConnectedSpace Y

/-- Whyburn's **potential order `≤ n` relative to a collection `𝒬`** (Ch. III §2, p. 45): a closed
set `X₀` has potential order `≤ n` in `X` relative to `𝒬` if there are open sets
`U₁ ⊃ Ū₂ ⊃ U₂ ⊃ Ū₃ ⊃ ⋯` with `X₀ = ⋂ Uᵢ` and each `F(Uᵢ)` contained in the sum of at most `n`
elements of `𝒬`. (Recorded; not used in the proofs of batch 150.) -/
def PotentialOrderLE (𝒬 : Set (Set X)) (X₀ : Set X) (n : ℕ) : Prop :=
  IsClosed X₀ ∧ ∃ U : ℕ → Set X, (∀ i, IsOpen (U i)) ∧ (∀ i, closure (U (i + 1)) ⊆ U i) ∧
    X₀ = ⋂ i, U i ∧ ∀ i, ∃ s : Finset (Set X), (↑s : Set (Set X)) ⊆ 𝒬 ∧ s.card ≤ n ∧
      frontier (U i) ⊆ ⋃₀ (↑s : Set (Set X))

end Sep

end HPC.Jones
