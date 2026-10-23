import HPC.Hagopian.Hagopian84C

/-!
# Batch 188: Hagopian 1984 V — the decomposition `𝔇`; claims (5)–(6); `hagopian84_decomp`

Built from the commission-188 skeleton (`doc/batches/skeletons/Hagopian84D.lean`). There is no
`sorry` in this file or its imports. Every item of the skeleton is proved, in the skeleton's shapes
(the helper lemmas added here are marked as such).

Source: Hagopian 1984 (`doc/sources/hagopian1984.pdf`), pp. 343–344. Route: commission 188.
Indexing as in `Hagopian84B.lean`: links `P 0, …, P 4` (the paper's `P₁, …, P₅`), `P 2` is the
paper's `P₃`, `midUnion P = ⋃𝒫′`. A *strand* is the closure of a component of `midUnion P`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## Small helpers (added) -/

section Helpers

variable {M : Set Pt}

/-- (Added.) `⋃𝒫′ ⊆ ⋃𝒫`. -/
theorem midUnion_subset_iUnion84 {Q : Fin 5 → Set M} : midUnion Q ⊆ ⋃ i, Q i := by
  rintro y ((h | h) | h)
  · exact mem_iUnion.2 ⟨1, h⟩
  · exact mem_iUnion.2 ⟨2, h⟩
  · exact mem_iUnion.2 ⟨3, h⟩

/-- (Added.) A point of `⋃𝒫 ∖ Cl(P 0 ∪ P 4)` lies in `⋃𝒫′`. -/
theorem mem_midUnion_of_diff84 {Q : Fin 5 → Set M} {x : M}
    (hx : x ∈ (⋃ i, Q i) \ closure (Q 0 ∪ Q 4)) : x ∈ midUnion Q := by
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx.1
  have h04 : x ∉ Q 0 ∪ Q 4 := fun h => hx.2 (subset_closure h)
  fin_cases i
  · exact absurd (Or.inl hi) h04
  · exact Or.inl (Or.inl hi)
  · exact Or.inl (Or.inr hi)
  · exact Or.inr hi
  · exact absurd (Or.inr hi) h04

/-- (Added.) The end layers of a continuum running straight through `𝒬` lie in `Cl(Q 0 ∪ Q 4)`. -/
theorem endlayers_subset_closure84 {G : Set M} {d : G → unitInterval} {Q : Fin 5 → Set M}
    (hrs : RunsStraight d Q) : layer d 0 ∪ layer d 1 ⊆ closure (Q 0 ∪ Q 4) := by
  rintro v (hv | hv)
  · exact subset_closure (Or.inl (hrs.2.1 hv).1)
  · exact subset_closure (Or.inr (hrs.2.2.1 hv).1)

end Helpers

/-! ## §2. The transfer lemma -/

section Transfer

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- (Added; commission 188 §2, step 4.) For two distinct layers `c⁻¹(s)`, `c⁻¹(r)` of a type λ
continuum, the piece between them has a minimal admissible map `d` with `d⁻¹(0) = c⁻¹(s)` and
`d⁻¹(1) = c⁻¹(r)` (`minimalAdmissible_restrict`, reversed by `unitInterval.symm` when `r < s`). -/
theorem exists_piece_between84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {G : Set M} {c : G → unitInterval} (hc : IsMinimalAdmissible G c) {r s : unitInterval}
    (hrs : r ≠ s) :
    ∃ (F : Set M) (d : F → unitInterval), IsMinimalAdmissible F d ∧ layer d 0 = layer c s ∧
      layer d 1 = layer c r := by
  rcases lt_or_gt_of_ne hrs with h | h
  · obtain ⟨e, he, hel⟩ := minimalAdmissible_restrict hX hi hc h
    refine ⟨_, unitInterval.symm ∘ e, he.symm_comp, ?_, ?_⟩
    · rw [layer_symm_comp, unitInterval.symm_zero, hel, restrictParam_one]
    · rw [layer_symm_comp, unitInterval.symm_one, hel, restrictParam_zero]
  · obtain ⟨e, he, hel⟩ := minimalAdmissible_restrict hX hi hc h
    exact ⟨_, e, he, by rw [hel, restrictParam_zero], by rw [hel, restrictParam_one]⟩

/-- **§2, the transfer lemma** (replaces "by (2), (3), and Lemma 7" and "by (3) and Lemma 7",
p. 344). `𝒫` a normal regular chain; `Q` a free normal regular chain whose union misses `Cl P 2`
(Hagopian's (2)). A member `Z` of `Ω(𝒫)` through a point `z` of `midUnion Q` is the layer through
`z` of the strand of `Q` through `z`.

*Proof* (commission 188 §2): `Z = c⁻¹(r)` for the map `c` given by regularity; the strand meets
`P 2` in a layer `c⁻¹(s) ⊆ P 2`, which misses `⋃Q ∋ z`, so `s ≠ r`; the piece between the two
layers (`exists_piece_between84`) has end layer `c⁻¹(s)` missing `midUnion Q` and other end layer
`Z`; Lemma 16′ for `Q` (`strand_layer_of_extension`, `u = 1`, `y = z`). Uses (2), not (3). -/
theorem omega_layer_of_mem_mid (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P Q : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hr : IsRegular5 P)
    (hQ : IsChain5 Q) (hQn : IsNormal5 Q) (hQf : IsFree5 Q) (hQr : IsRegular5 Q)
    (h2 : (⋃ i, Q i) ⊆ (closure (P 2))ᶜ) {Z : Set M} (hZ : Z ∈ Omega5 P) {z : M} (hzZ : z ∈ Z)
    (hz : z ∈ midUnion Q) :
    ∃ c' : closure (connectedComponentIn (midUnion Q) z) → unitInterval,
      IsMinimalAdmissible (closure (connectedComponentIn (midUnion Q) z)) c' ∧
        ∃ t, Z = layer c' t := by
  obtain ⟨x, hx, d₀, hd₀, t₀, rfl⟩ := hZ
  obtain ⟨c, hc, hcs⟩ := hr x hx
  obtain ⟨r, hr'⟩ := exists_layer_eq_of_minimal hd₀ hc t₀
  obtain ⟨p, hpG, hp2⟩ := (strand_meets_P2_P0 hP hn hr hx).1
  have hps : p ∈ layer c (c ⟨p, hpG⟩) := mem_layer_self84 c ⟨p, hpG⟩
  have hs2 : layer c (c ⟨p, hpG⟩) ⊆ P 2 := layer_subset_link hc.2.1 hP.isOpen hcs ⟨p, hps, hp2⟩
  have hQP : ∀ y ∈ midUnion Q, y ∉ closure (P 2) := fun y hy => h2 (midUnion_subset_iUnion84 hy)
  have hzr : z ∈ layer c r := hr' ▸ hzZ
  have hrs : r ≠ c ⟨p, hpG⟩ := by
    intro h
    rw [h] at hzr
    exact hQP z hz (subset_closure (hs2 hzr))
  obtain ⟨F, d, hd, hd0, hd1⟩ := exists_piece_between84 hX hi hc hrs
  have hdis : Disjoint (layer d 0) (midUnion Q) := by
    rw [hd0, disjoint_left]
    intro y hy hyQ
    exact hQP y hyQ (subset_closure (hs2 hy))
  obtain ⟨c', hc', t, ht⟩ := strand_layer_of_extension hX hi hQ hQn hQf hQr hd hdis (u := 1)
    (y := z) (by rw [hd1]; exact hzr) hz
  exact ⟨c', hc', t, by rw [hr', ← hd1, ht]⟩

/-- **§2, second part**: if moreover `z ∉ Cl(Q 0 ∪ Q 4)`, then `Z ∈ Δ(Q)`
(`strand_layer_mem_delta` for `Q`). -/
theorem omega_mem_delta_of_mem_mid (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P Q : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hr : IsRegular5 P)
    (hQ : IsChain5 Q) (hQn : IsNormal5 Q) (hQf : IsFree5 Q) (hQr : IsRegular5 Q)
    (h2 : (⋃ i, Q i) ⊆ (closure (P 2))ᶜ) {Z : Set M} (hZ : Z ∈ Omega5 P) {z : M} (hzZ : z ∈ Z)
    (hz : z ∈ midUnion Q) (hz0 : z ∉ closure (Q 0 ∪ Q 4)) : Z ∈ Delta5 Q := by
  obtain ⟨c', hc', t, rfl⟩ :=
    omega_layer_of_mem_mid hX hi hP hn hr hQ hQn hQf hQr h2 hZ hzZ hz
  exact strand_layer_mem_delta hQ hQr hz hz0 hc' hzZ

end Transfer

/-! ## §3. The data, `𝔇`, disjointness -/

/-- **§3.1, the data of p. 343 after the finite subcover** (`hagopian84_cover`): the chain `𝒫`
(Lemma 13), finitely many `Zᵢ ∈ Ω(𝒫)∖Δ(𝒫)` (`S`) with their chains `𝒫(Zᵢ)` (`Q`), and the cover.
A structure standing for constructed data: non-vacuity note required (discharged by
`exists_coverData84`). -/
structure CoverData84 (M : Set Pt) [CompactSpace M] [ConnectedSpace M] where
  P : Fin 5 → Set M
  hP : IsChain5 P
  hPf : IsFree5 P
  hPn : IsNormal5 P
  hPr : IsRegular5 P
  S : Finset (Set M)
  Q : Set M → Fin 5 → Set M
  hQ : ∀ Z ∈ S, Z ∈ Omega5 P ∧ Z ∉ Delta5 P ∧ IsChain5 (Q Z) ∧ IsFree5 (Q Z) ∧
    IsNormal5 (Q Z) ∧ IsRegular5 (Q Z) ∧ Z ∈ Delta5 (Q Z) ∧ (⋃ i, Q Z i) ⊆ (closure (P 2))ᶜ ∧
    closure (Q Z 0 ∪ Q Z 4) ⊆ ⋃₀ Delta5 P
  cover : ∀ y : M, y ∈ ⋃₀ Delta5 P ∨ ∃ Z ∈ S, y ∈ ⋃₀ Delta5 (Q Z)

section Decomp

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§3.1**: the data exist (a type λ continuum by `hagopian75_exists_typeA'`; Lemma 13 with
`ε = 1`, `A = ∅`, `B = M`; `hagopian84_cover`). -/
theorem exists_coverData84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (hH : ¬ IsHereditarilyIndecomposable (univ : Set M)) : Nonempty (CoverData84 M) := by
  have hK : ∃ K : Set M, Fold.Q78.IsContinuum K ∧ ¬ Fold.Q78.IsIndecomposable K := by
    by_contra hcon
    push_neg at hcon
    exact hH fun K _ hK => hcon K hK
  obtain ⟨K, hK, hKd⟩ := hK
  obtain ⟨E, -, hirr, k, hadm, hvoid⟩ := hagopian75_exists_typeA' hX hi hK hKd
  have hE : IsMinimalAdmissible E k := ⟨hirr, hadm, hvoid⟩
  obtain ⟨P, hP, hPf, hPn, hPr, -⟩ := hagopian84_lemma13 hX hi hE one_pos isClosed_empty
    (empty_disjoint _) isOpen_univ (subset_univ _)
  obtain ⟨S, Q, hQ, hcov⟩ := hagopian84_cover hX hi hP hPn hPf hPr
  exact ⟨⟨P, hP, hPf, hPn, hPr, S, Q, hQ, hcov⟩⟩

/-- **§3.2, `𝔇`** (p. 343: "For convenience we define `𝒫(Z₀)` to be `𝒫`"; "Let `𝔇` be
`⋃{Δ(𝒫(Zᵢ)): 0 ≤ i ≤ n}`"). -/
def CoverData84.members (D : CoverData84 M) : Set (Set M) :=
  Delta5 D.P ∪ ⋃ Z ∈ D.S, Delta5 (D.Q Z)

/-- **§3.3**: every point lies in a member. -/
theorem CoverData84.exists_mem (D : CoverData84 M) (y : M) : ∃ A ∈ D.members, y ∈ A := by
  rcases D.cover y with ⟨A, hA, hyA⟩ | ⟨Z, hZ, A, hA, hyA⟩
  · exact ⟨A, Or.inl hA, hyA⟩
  · exact ⟨A, Or.inr (mem_iUnion₂.2 ⟨Z, hZ, hA⟩), hyA⟩

/-- (Added.) Every member of `𝔇` is a member of `Δ(R)` for one of the chains `R` (`𝒫` or some
`𝒫(Zᵢ)`), and `Δ(R) ⊆ 𝔇`. -/
theorem CoverData84.exists_chain_of_mem (D : CoverData84 M) {A : Set M} (hA : A ∈ D.members) :
    ∃ R : Fin 5 → Set M, IsChain5 R ∧ IsFree5 R ∧ IsRegular5 R ∧ A ∈ Delta5 R ∧
      Delta5 R ⊆ D.members := by
  rcases hA with hA | hA
  · exact ⟨D.P, D.hP, D.hPf, D.hPr, hA, fun B hB => Or.inl hB⟩
  · obtain ⟨Z, hZ, hA⟩ := mem_iUnion₂.1 hA
    obtain ⟨-, -, hQ, hQf, -, hQr, -⟩ := D.hQ Z hZ
    exact ⟨D.Q Z, hQ, hQf, hQr, hA, fun B hB => Or.inr (mem_iUnion₂.2 ⟨Z, hZ, hB⟩)⟩

/-- (Added; commission 188 §3.4, case (b).) A member of `Δ(𝒫(Zᵢ))` meeting a member `Y` of `Δ(𝒫)`
equals `Y`: the common point lies in `midUnion 𝒫(Zᵢ)` outside `Cl(P(Zᵢ) 0 ∪ P(Zᵢ) 4)`, so the
transfer lemma puts `Y` in `Δ(𝒫(Zᵢ))`; then `delta5_partition` for `𝒫(Zᵢ)`. -/
theorem CoverData84.eq_of_meet_delta (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) {Z : Set M} (hZS : Z ∈ D.S) {A Y : Set M} (hA : A ∈ Delta5 (D.Q Z))
    (hY : Y ∈ Delta5 D.P) (hAY : (A ∩ Y).Nonempty) : A = Y := by
  obtain ⟨-, -, hQ, hQf, hQn, hQr, -, h2, -⟩ := D.hQ Z hZS
  obtain ⟨x, hxA, hxY⟩ := hAY
  have hx : x ∈ (⋃ i, D.Q Z i) \ closure (D.Q Z 0 ∪ D.Q Z 4) := by
    rw [← (delta5_partition hQ hQr).1]
    exact ⟨A, hA, hxA⟩
  have hYQ := omega_mem_delta_of_mem_mid hX hi D.hP D.hPn D.hPr hQ hQn hQf hQr h2 hY.1 hxY
    (mem_midUnion_of_diff84 hx) hx.2
  exact (delta5_partition hQ hQr).2 A hA Y hYQ ⟨x, hxA, hxY⟩

/-- **§3.4, disjointness** (pp. 343–344: "We must show that `𝔇` is a decomposition of `M`. Since
`𝒞` covers `M`, it suffices to show that the elements of `𝔇` are disjoint."). Route: commission
188 §3.4 (cases (a)–(c); §2 in place of Lemma 7; Lemma 3 as printed in the last case). -/
theorem CoverData84.members_disjoint (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) {A B : Set M} (hA : A ∈ D.members) (hB : B ∈ D.members)
    (hAB : (A ∩ B).Nonempty) : A = B := by
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact (delta5_partition D.hP D.hPr).2 A hA B hB hAB
  · obtain ⟨Z, hZ, hB⟩ := mem_iUnion₂.1 hB
    exact (D.eq_of_meet_delta hX hi hZ hB hA (by rwa [inter_comm])).symm
  · obtain ⟨Z, hZ, hA⟩ := mem_iUnion₂.1 hA
    exact D.eq_of_meet_delta hX hi hZ hA hB hAB
  · obtain ⟨Z, hZ, hA⟩ := mem_iUnion₂.1 hA
    obtain ⟨Z', hZ', hB⟩ := mem_iUnion₂.1 hB
    by_cases hAm : (A ∩ ⋃₀ Delta5 D.P).Nonempty
    · obtain ⟨y, hyA, Y, hY, hyY⟩ := hAm
      have hAY := D.eq_of_meet_delta hX hi hZ hA hY ⟨y, hyA, hyY⟩
      subst hAY
      exact (D.eq_of_meet_delta hX hi hZ' hB hY (by rwa [inter_comm])).symm
    by_cases hBm : (B ∩ ⋃₀ Delta5 D.P).Nonempty
    · obtain ⟨y, hyB, Y, hY, hyY⟩ := hBm
      have hBY := D.eq_of_meet_delta hX hi hZ' hB hY ⟨y, hyB, hyY⟩
      subst hBY
      exact D.eq_of_meet_delta hX hi hZ hA hY hAB
    -- Hagopian's last case: `A ∪ B` misses `⋃Δ(𝒫)`; Lemma 3 with `h` the identity
    have hQ := D.hQ Z hZ
    have hQ' := D.hQ Z' hZ'
    obtain ⟨_, _, d, hd, hrs, s, hs0, hs1, rfl⟩ := delta_regular_rep hQ.2.2.2.2.2.1 hA
    obtain ⟨_, _, d', hd', hrs', u, -, -, rfl⟩ := delta_regular_rep hQ'.2.2.2.2.2.1 hB
    have hid : ∀ S : Set M, (Homeomorph.refl M) '' S = S := fun S => by ext; simp
    have key := hagopian76_lemma3 hX hi hd hd' hs0 hs1 (Homeomorph.refl M)
      (by rw [hid, inter_comm]; exact hAB) ?_ ?_
    · rwa [hid] at key
    · rw [hid, disjoint_left]
      intro v hvB hve
      exact hBm ⟨v, hvB, hQ.2.2.2.2.2.2.2.2 (endlayers_subset_closure84 hrs hve)⟩
    · rw [hid, disjoint_left]
      intro v hvA hve
      exact hAm ⟨v, hvA, hQ'.2.2.2.2.2.2.2.2 (endlayers_subset_closure84 hrs' hve)⟩

/-- **§3.5, the relation**: `x ~ y` iff some member of `𝔇` contains both. -/
def CoverData84.rel (D : CoverData84 M) (x y : M) : Prop :=
  ∃ A ∈ D.members, x ∈ A ∧ y ∈ A

/-- **§3.5**: the relation is an equivalence (3.3 and 3.4). -/
def CoverData84.setoid (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) : Setoid M where
  r := D.rel
  iseqv := by
    refine ⟨fun x => ?_, fun {x y} hxy => ?_, fun {x y z} hxy hyz => ?_⟩
    · obtain ⟨A, hA, hxA⟩ := D.exists_mem x
      exact ⟨A, hA, hxA, hxA⟩
    · obtain ⟨A, hA, hx, hy⟩ := hxy
      exact ⟨A, hA, hy, hx⟩
    · obtain ⟨A, hA, hx, hy⟩ := hxy
      obtain ⟨B, hB, hy', hz⟩ := hyz
      exact ⟨A, hA, hx, (D.members_disjoint hX hi hA hB ⟨y, hy, hy'⟩) ▸ hz⟩

/-- (Added.) Unfolding the setoid. -/
theorem CoverData84.setoid_iff {hX : IsHomogeneous M} {hi : ¬ IsDecomposableSpace M}
    (D : CoverData84 M) {x y : M} :
    D.setoid hX hi x y ↔ D.rel x y := Iff.rfl

/-- **§3.5**: the class of `x` is the member through `x`. -/
theorem CoverData84.cls_eq (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) {x : M} {A : Set M} (hA : A ∈ D.members) (hx : x ∈ A) :
    cls (D.setoid hX hi) x = A := by
  ext y
  simp only [cls, mem_setOf_eq, CoverData84.setoid_iff]
  constructor
  · rintro ⟨B, hB, hyB, hxB⟩
    rwa [D.members_disjoint hX hi hB hA ⟨x, hxB, hx⟩] at hyB
  · intro hy
    exact ⟨A, hA, hy, hx⟩

/-! ## §4. Claims (5) and (6) -/

/-- **§4.1, claim (5) for `i = 0`** (p. 344: "(5) for each integer `i` (`0 ≤ i ≤ n`),
`Ω(𝒫(Zᵢ)) ⊂ 𝔇`"), in full.

*Proof* (commission 188 §4.1): a member `Z ∉ Δ(𝒫)` lies in `Cl P 0` or `Cl P 4`
(`omega_not_delta_side`), so a point of it is covered by some `⋃Δ(𝒫(Zᵢ))`; the transfer lemma. -/
theorem CoverData84.omega_subset_members (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) : Omega5 D.P ⊆ D.members := by
  intro Z hZ
  by_cases hZd : Z ∈ Delta5 D.P
  · exact Or.inl hZd
  obtain ⟨hside, -⟩ := omega_not_delta_side D.hP D.hPn D.hPr hZ hZd
  have hZ' := hZ
  obtain ⟨x, hx, d, hd, t, rfl⟩ := hZ'
  obtain ⟨z, hz⟩ := layer_nonempty' hd.2.1 t
  have hzc : z ∈ closure (D.P 0 ∪ D.P 4) := by
    rcases hside with h | h
    · exact closure_mono subset_union_left (h hz)
    · exact closure_mono subset_union_right (h hz)
  rcases D.cover z with h | ⟨Y, hYS, A, hA, hzA⟩
  · rw [(delta5_partition D.hP D.hPr).1] at h
    exact absurd hzc h.2
  · obtain ⟨-, -, hQ, hQf, hQn, hQr, -, h2, -⟩ := D.hQ Y hYS
    have hzA' : z ∈ (⋃ i, D.Q Y i) \ closure (D.Q Y 0 ∪ D.Q Y 4) := by
      rw [← (delta5_partition hQ hQr).1]
      exact ⟨A, hA, hzA⟩
    exact Or.inr (mem_iUnion₂.2 ⟨Y, hYS, omega_mem_delta_of_mem_mid hX hi D.hP D.hPn D.hPr hQ
      hQn hQf hQr h2 hZ hz (mem_midUnion_of_diff84 hzA') hzA'.2⟩)

/-- **§4.2, claim (5) for `i ≥ 1`**, for members inside `⋃𝒫(Zᵢ)′`.

*Proof* (commission 188 §4.2): if `W ∉ Δ(Q)`, then `W ⊆ Cl(Q 0 ∪ Q 4) ⊆ ⋃Δ(𝒫)` by (3); for `w ∈ W`
and `Y ∈ Δ(𝒫)` through `w`, the transfer lemma makes `Y` the layer through `w` of the strand of `Q`
through `w`; `W ⊆ midUnion Q` puts `W` inside the component it comes from, which is therefore the
component through `w`; so `W = Y`. -/
theorem CoverData84.omega_mem_members (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) {Z : Set M} (hZS : Z ∈ D.S) {W : Set M} (hW : W ∈ Omega5 (D.Q Z))
    (hWm : W ⊆ midUnion (D.Q Z)) : W ∈ D.members := by
  obtain ⟨-, -, hQ, hQf, hQn, hQr, -, h2, h3⟩ := D.hQ Z hZS
  by_cases hWd : W ∈ Delta5 (D.Q Z)
  · exact Or.inr (mem_iUnion₂.2 ⟨Z, hZS, hWd⟩)
  obtain ⟨hside, -⟩ := omega_not_delta_side hQ hQn hQr hW hWd
  obtain ⟨x, hx, d, hd, t, hWt⟩ := hW
  obtain ⟨w, hw⟩ := layer_nonempty' hd.2.1 t
  rw [← hWt] at hw
  have hwc : w ∈ closure (D.Q Z 0 ∪ D.Q Z 4) := by
    rcases hside with h | h
    · exact closure_mono subset_union_left (h hw)
    · exact closure_mono subset_union_right (h hw)
  obtain ⟨Y, hY, hwY⟩ := h3 hwc
  obtain ⟨c', hc', t', hYt⟩ :=
    omega_layer_of_mem_mid hX hi D.hP D.hPn D.hPr hQ hQn hQf hQr h2 hY.1 hwY (hWm hw)
  have hWK : W ⊆ connectedComponentIn (midUnion (D.Q Z)) x := by
    have hWG : W ⊆ closure (connectedComponentIn (midUnion (D.Q Z)) x) :=
      hWt ▸ layer_subset_set d t
    have hpc : IsPreconnected (connectedComponentIn (midUnion (D.Q Z)) x ∪ W) :=
      isPreconnected_connectedComponentIn.subset_closure subset_union_left
        (union_subset subset_closure hWG)
    exact subset_union_right.trans (hpc.subset_connectedComponentIn
      (Or.inl (mem_connectedComponentIn hx)) (union_subset (connectedComponentIn_subset _ _) hWm))
  have hcc : connectedComponentIn (midUnion (D.Q Z)) x =
      connectedComponentIn (midUnion (D.Q Z)) w := connectedComponentIn_eq (hWK hw)
  have hWY : W = Y := by
    rw [hWt, hYt]
    exact layer_eq_of_common_point (congrArg closure hcc) hd hc' (hWt ▸ hw) (hYt ▸ hwY)
  exact Or.inl (hWY ▸ hY)

/-- (Added; commission 188 §4.3.) For a free normal regular chain `R` there is `δ > 0` such that a
`δ`-homeomorphism maps each member of `Δ(R)` onto a member of `Ω(R)` inside `midUnion R` (Lemma 15
and the `η` of `delta5_dist_pos`). -/
theorem delta_translate_small84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {R : Fin 5 → Set M} (hR : IsChain5 R) (hn : IsNormal5 R) (hf : IsFree5 R)
    (hr : IsRegular5 R) :
    ∃ δ > 0, ∀ A ∈ Delta5 R, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      h '' A ∈ Omega5 R ∧ h '' A ⊆ midUnion R := by
  obtain ⟨ε, hε, h15⟩ := hagopian84_lemma15 hX hi hR hn hf hr
  obtain ⟨η, hη, hηd⟩ := delta5_dist_pos hR hf hr
  refine ⟨min ε η, lt_min hε hη, fun A hA h hh =>
    ⟨h15 A hA h fun v => (hh v).trans_le (min_le_left _ _), ?_⟩⟩
  rintro _ ⟨v, hv, rfl⟩
  by_contra hm
  exact absurd ((hh v).trans_le (min_le_right _ _)) (not_lt.2 (hηd v ⟨A, hA, hv⟩ (h v) hm))

omit [CompactSpace M] [ConnectedSpace M] in
/-- (Added.) A common positive radius for finitely many downward-closed conditions. -/
theorem exists_pos_forall_finset84 {ι : Type*} (S : Finset ι) (p : ι → ℝ → Prop)
    (hmono : ∀ i δ δ', 0 < δ' → δ' ≤ δ → p i δ → p i δ') (h : ∀ i ∈ S, ∃ δ > 0, p i δ) :
    ∃ δ > 0, ∀ i ∈ S, p i δ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S _ ih =>
    obtain ⟨δ₁, h₁, hp₁⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨δ₂, h₂, hp₂⟩ := h a (Finset.mem_insert_self a S)
    refine ⟨min δ₁ δ₂, lt_min h₁ h₂, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hmono _ _ _ (lt_min h₁ h₂) (min_le_right _ _) hp₂
    · exact hmono _ _ _ (lt_min h₁ h₂) (min_le_left _ _) (hp₁ i hi)

/-- **§4.3, claim (6)** (p. 344: "(6) if `Z ∈ 𝔇` and `h` is a δ-homeomorphism of `M` onto `M`, then
`h[Z] ∈ 𝔇`"). `δ` also below the `η` of `delta5_dist_pos` for each chain (commission 188 §4.3). -/
theorem CoverData84.invariant (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) → ∀ A ∈ D.members, h '' A ∈ D.members := by
  obtain ⟨δ₀, hδ₀, hP⟩ := delta_translate_small84 hX hi D.hP D.hPn D.hPf D.hPr
  obtain ⟨δ₁, hδ₁, hQ⟩ := exists_pos_forall_finset84 D.S
    (fun Z δ => ∀ A ∈ Delta5 (D.Q Z), ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      h '' A ∈ Omega5 (D.Q Z) ∧ h '' A ⊆ midUnion (D.Q Z))
    (fun _ _ _ _ hle hp A hA h hh => hp A hA h fun v => (hh v).trans_le hle)
    (fun Z hZ => by
      obtain ⟨-, -, hQ, hQf, hQn, hQr, -⟩ := D.hQ Z hZ
      exact delta_translate_small84 hX hi hQ hQn hQf hQr)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun h hh A hA => ?_⟩
  rcases hA with hA | hA
  · exact D.omega_subset_members hX hi (hP A hA h fun v => (hh v).trans_le (min_le_left _ _)).1
  · obtain ⟨Z, hZ, hA⟩ := mem_iUnion₂.1 hA
    obtain ⟨h1, h2⟩ := hQ Z hZ A hA h fun v => (hh v).trans_le (min_le_right _ _)
    exact D.omega_mem_members hX hi hZ h1 h2

/-! ## §5. The package -/

/-- **§5.1–§5.5**: `𝔇` is a Jones decomposition (usc from Lemma 14; connected, proper classes;
invariance from (6); the arc from `exists_interval_in_delta`). -/
theorem CoverData84.isJonesDecomp (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) : IsJonesDecomp84 (D.setoid hX hi) := by
  have hlayer : ∀ A ∈ D.members, ∃ (G : Set M) (d : G → unitInterval),
      IsMinimalAdmissible G d ∧ ∃ t, A = layer d t := by
    intro A hA
    obtain ⟨R, -, -, -, ⟨⟨x, -, d, hd, t, hAt⟩, -⟩, -⟩ := D.exists_chain_of_mem hA
    exact ⟨_, d, hd, t, hAt⟩
  have hcomp : ∀ A ∈ D.members, IsCompact A := by
    intro A hA
    obtain ⟨G, d, hd, t, rfl⟩ := hlayer A hA
    exact (isClosed_layer hd.isCompact hd.2.1.1 t).isCompact
  refine ⟨⟨fun x => ?_, fun x U hU hxU => ?_⟩, fun x => ?_, fun x => ?_, ?_, ?_⟩
  · -- closed classes
    obtain ⟨A, hA, hxA⟩ := D.exists_mem x
    rw [D.cls_eq hX hi hA hxA]
    exact (hcomp A hA).isClosed
  · -- upper semicontinuity, from Lemma 14
    refine ⟨{z | cls (D.setoid hX hi) z ⊆ U}, ?_, fun y hy => ?_, fun z hz => hz⟩
    · rw [Metric.isOpen_iff]
      intro z₀ hz₀
      obtain ⟨A, hA, hzA⟩ := D.exists_mem z₀
      rw [mem_setOf_eq, D.cls_eq hX hi hA hzA] at hz₀
      obtain ⟨R, hR, hRf, hRr, hAR, hRm⟩ := D.exists_chain_of_mem hA
      obtain ⟨ε, hε, hεU⟩ := (hcomp A hA).exists_thickening_subset_open hU hz₀
      obtain ⟨δ, hδ, h14⟩ := hagopian84_lemma14 hX hi hR hRf hRr A hAR z₀ hzA ε hε
      obtain ⟨δ', hδ', hball⟩ :=
        Metric.isOpen_iff.1 (isOpen_sUnion_delta5 hR hRr) z₀ ⟨A, hAR, hzA⟩
      refine ⟨min δ δ', lt_min hδ hδ', fun z hz => ?_⟩
      obtain ⟨A', hA', hzA'⟩ := hball (ball_subset_ball (min_le_right _ _) hz)
      rw [mem_setOf_eq, D.cls_eq hX hi (hRm hA') hzA']
      have hd : dist z₀ z < δ := by
        rw [dist_comm]
        exact lt_of_lt_of_le (mem_ball.1 hz) (min_le_left _ _)
      exact (h14 A' hA' z hzA' hd).2.trans hεU
    · obtain ⟨A, hA, hxA⟩ := D.exists_mem x
      rw [D.cls_eq hX hi hA hxA] at hy hxU
      rw [mem_setOf_eq, D.cls_eq hX hi hA hy]
      exact hxU
  · -- connected classes
    obtain ⟨A, hA, hxA⟩ := D.exists_mem x
    rw [D.cls_eq hX hi hA hxA]
    obtain ⟨G, d, hd, t, rfl⟩ := hlayer A hA
    exact ⟨layer_nonempty' hd.2.1 t, layer_isPreconnected' hd.2.1 t⟩
  · -- proper classes
    obtain ⟨A, hA, hxA⟩ := D.exists_mem x
    rw [D.cls_eq hX hi hA hxA]
    obtain ⟨R, hR, -, -, hAR, -⟩ := D.exists_chain_of_mem hA
    obtain ⟨p, hp, -⟩ := (hR.inter_iff 0 0).2 (by decide)
    intro hAu
    exact disjoint_left.1 hAR.2 (hAu ▸ mem_univ p) (subset_closure (Or.inl hp))
  · -- invariance, from (6)
    obtain ⟨δ, hδ, hinv⟩ := D.invariant hX hi
    refine ⟨δ, hδ, fun h hh x y hxy => ?_⟩
    rw [CoverData84.setoid_iff] at hxy ⊢
    obtain ⟨A, hA, hx, hy⟩ := hxy
    exact ⟨h '' A, hinv h hh A hA, mem_image_of_mem h hx, mem_image_of_mem h hy⟩
  · -- the arc of classes
    obtain ⟨x, hx1, -⟩ := (D.hP.inter_iff 1 2).2 (by decide)
    have hx : x ∈ midUnion D.P := Or.inl (Or.inl hx1)
    obtain ⟨c, hc, hcs⟩ := D.hPr x hx
    obtain ⟨a, b, hab, hint⟩ := exists_interval_in_delta D.hP D.hPn hx hc hcs
    obtain ⟨e, he, hel⟩ := minimalAdmissible_restrict hX hi hc hab
    have hmem : ∀ t, layer e t ∈ D.members := fun t =>
      Or.inl (hel t ▸ hint _ (restrictParam_mem a b hab.le t))
    refine ⟨_, e, he.isCompact, he.2.1.1, he.2.1.2.1, fun y z => ?_⟩
    rw [CoverData84.setoid_iff]
    constructor
    · intro hyz
      exact ⟨layer e (e y), hmem _, mem_layer_self84 e y, hyz ▸ mem_layer_self84 e z⟩
    · rintro ⟨A, hA, hyA, hzA⟩
      rw [D.members_disjoint hX hi hA (hmem (e y)) ⟨y, hyA, mem_layer_self84 e y⟩] at hzA
      obtain ⟨w, hw, hwz⟩ := hzA
      rw [← Subtype.ext hwz]
      exact hw.symm

open Classical in
/-- **§5.8, the printed closedness of `⋃𝔅`** (p. 343: "it follows that `⋃𝔅` is a closed open subset
of `M`. Hence `𝔅` covers `M`"): for any choice as in `exists_finite_cover84`, `⋃𝔅 = M` (so `⋃𝔅` is
closed). The statement is a corollary of the finite cover; the printed reason is not used. -/
theorem sUnion_cover84_eq_univ {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P)
    (hf : IsFree5 P) (hr : IsRegular5 P) (Q : Set M → Fin 5 → Set M)
    (hQ : ∀ Z ∈ Omega5 P, Z ∉ Delta5 P → IsChain5 (Q Z) ∧ IsFree5 (Q Z) ∧ IsRegular5 (Q Z) ∧
      Z ∈ Delta5 (Q Z) ∧ closure (Q Z 0 ∪ Q Z 4) ⊆ ⋃₀ Delta5 P) :
    ⋃₀ Delta5 P ∪ (⋃ Z ∈ Omega5 P \ Delta5 P, ⋃₀ Delta5 (Q Z)) = univ := by
  obtain ⟨S, hS, hcov⟩ := exists_finite_cover84 hP hn hf hr Q hQ
  refine eq_univ_of_forall fun y => ?_
  rcases hcov y with h | ⟨Z, hZ, h⟩
  · exact Or.inl h
  · exact Or.inr (mem_iUnion₂.2 ⟨Z, hS Z hZ, h⟩)

end Decomp

/-- **§5.6, Theorem 1 of 1984 with `N = M`, in the form used** (`Hagopian84Decomp`). -/
theorem hagopian84_decomp : Hagopian84Decomp := by
  refine hagopian84Decomp_of_package ?_
  intro M _ _ hX hi hH
  exact ⟨_, (Classical.choice (exists_coverData84 hX hi hH)).isJonesDecomp hX hi⟩

/-- **§5.7, Theorem 1 of 1976 on the 1984 route**, from the arc step alone. -/
theorem hagopian76_theorem1_jones (hA : NoArcIndecHomPlane) : Hagopian76Thm1 :=
  hagopian76_theorem1_of_jones hagopian84_decomp hA

end HPC.Hagopian
