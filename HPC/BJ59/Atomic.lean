import HPC.BJ59.BJ59A

/-!
# Batch 199: atomic maps; atomic arcs of snake-like hereditarily indecomposable continua are
# snake-like (commission 199, §§2–3)

* `IsAtomicMap`, `IsAtomicCircPAMap` (Domokos–Prajs 2022, p. 13);
* `subset_fibre_or_saturated` (the saturation lemma) and the tests `isAtomicMap_id`,
  `not_isAtomicMap_snd`;
* `condB_preimage_Icc`, `isHereditarilyUnicoherent_of_atomic`, `isSnakeLike_of_atomic'`: Bing's
  proof of 1951 Theorem 11 (as in `theorem11_1951`) with the fibres in place of Bing's layers;
* `isSnakeLike_of_atomic`: the case of pseudo-arc fibres.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.HO16

/-! ## §2. Atomic maps -/

section Atomic

variable {X Y : Type*} [MetricSpace X]

/-- **Atomic** (Domokos–Prajs p. 13): every fibre is terminal, i.e. a continuum that meets a fibre
lies in it or contains it. Domokos–Prajs also ask the fibres to be continua; that is a separate
hypothesis wherever it is used. -/
def IsAtomicMap (f : X → Y) : Prop :=
  ∀ (y : Y) (L : Set X), Fold.Q78.IsContinuum L → (L ∩ f ⁻¹' {y}).Nonempty →
    L ⊆ f ⁻¹' {y} ∨ f ⁻¹' {y} ⊆ L

/-- **An open atomic map onto the circle with pseudo-arc fibres** (the right-hand side of
Domokos–Prajs Theorem 6.1): `IsCircPAMap` with atomicity in place of circle-likeness. -/
structure IsAtomicCircPAMap (f : X → Circle) : Prop where
  cont : Continuous f
  isOpenMap : IsOpenMap f
  surj : Function.Surjective f
  fib : ∀ z, IsPseudoArc (f ⁻¹' {z})
  atomic : IsAtomicMap f

/-- **The saturation lemma**: a continuum lies in a fibre of an atomic map, or it is the full
preimage of its image. -/
theorem subset_fibre_or_saturated {f : X → Y} (hf : IsAtomicMap f) {L : Set X}
    (hL : Fold.Q78.IsContinuum L) : (∃ y, L ⊆ f ⁻¹' {y}) ∨ f ⁻¹' (f '' L) = L := by
  by_cases h : ∃ y, L ⊆ f ⁻¹' {y}
  · exact Or.inl h
  · push_neg at h
    refine Or.inr (Subset.antisymm (fun x hx => ?_) (subset_preimage_image f L))
    obtain ⟨l, hl, hlx⟩ := hx
    rcases hf (f l) L hL ⟨l, hl, rfl⟩ with h' | h'
    · exact absurd h' (h (f l))
    · exact h' (show f x = f l from hlx.symm)

/-- In the second case of the saturation lemma, a continuum contains every fibre it meets. -/
theorem fibre_subset_of_saturated {f : X → Y} {L : Set X} (hL : f ⁻¹' (f '' L) = L) {x : X}
    (hx : x ∈ L) : f ⁻¹' {f x} ⊆ L := fun z hz => hL ▸ ⟨x, hx, (show f z = f x from hz).symm⟩

/-- Test: the identity is atomic. -/
theorem isAtomicMap_id : IsAtomicMap (id : X → X) := by
  intro y L _ ⟨x, hxL, hx⟩
  right
  intro z hz
  have h1 : z = y := hz
  have h2 : x = y := hx
  rw [h1, ← h2]; exact hxL

/-- Test: a product projection is not atomic. -/
theorem not_isAtomicMap_snd :
    ¬ IsAtomicMap (Prod.snd : unitInterval × unitInterval → unitInterval) := by
  intro h
  have hL : Fold.Q78.IsContinuum (({0} : Set unitInterval) ×ˢ (univ : Set unitInterval)) :=
    ⟨isCompact_singleton.prod isCompact_univ, isConnected_singleton.prod isConnected_univ⟩
  rcases h 0 _ hL ⟨(0, 0), ⟨rfl, mem_univ _⟩, rfl⟩ with h' | h'
  · have : ((0 : unitInterval), (1 : unitInterval)) ∈
        (Prod.snd : unitInterval × unitInterval → unitInterval) ⁻¹' {0} :=
      h' ⟨rfl, mem_univ _⟩
    exact one_ne_zero (show (1 : unitInterval) = 0 from this)
  · have := (h' (show ((1 : unitInterval), (0 : unitInterval)) ∈
        (Prod.snd : unitInterval × unitInterval → unitInterval) ⁻¹' {0} from rfl)).1
    exact one_ne_zero (show (1 : unitInterval) = 0 from this)

end Atomic

/-! ## §3. Atomic arcs are snake-like -/

section Arc

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- Two preconnected subsets of `[0, 1]` with a common point that is a lower (or upper) bound for
both are nested. -/
theorem nested_of_common_bound {I J : Set unitInterval} (hI : IsPreconnected I)
    (hJ : IsPreconnected J) {a : unitInterval} (haI : a ∈ I) (haJ : a ∈ J)
    (hb : (∀ x ∈ I, a ≤ x) ∧ (∀ x ∈ J, a ≤ x) ∨ (∀ x ∈ I, x ≤ a) ∧ (∀ x ∈ J, x ≤ a)) :
    I ⊆ J ∨ J ⊆ I := by
  by_contra hne
  push_neg at hne
  obtain ⟨⟨x, hxI, hxJ⟩, ⟨y, hyJ, hyI⟩⟩ := hne.imp not_subset.1 not_subset.1
  rcases hb with ⟨hI', hJ'⟩ | ⟨hI', hJ'⟩
  · rcases le_total x y with hxy | hxy
    · exact hxJ (hJ.Icc_subset haJ hyJ ⟨hI' x hxI, hxy⟩)
    · exact hyI (hI.Icc_subset haI hxI ⟨hJ' y hyJ, hxy⟩)
  · rcases le_total x y with hxy | hxy
    · exact hyI (hI.Icc_subset hxI haI ⟨hxy, hJ' y hyJ⟩)
    · exact hxJ (hJ.Icc_subset hyJ haJ ⟨hxy, hI' x hxI⟩)

/-- **Terminal points.** A point of an end fibre of `f ⁻¹' [a, b]` satisfies Bing's condition B
there. -/
theorem condB_preimage_Icc {f : X → unitInterval} (hc : Continuous f)
    (hHI : ∀ t, IsHereditarilyIndecomposable (f ⁻¹' {t})) (ha : IsAtomicMap f)
    {a b : unitInterval} (hab : a ≤ b) {μ : X} (hμ : f μ = a ∨ f μ = b) :
    CondB (f ⁻¹' Icc a b) μ := by
  have hμS : μ ∈ f ⁻¹' Icc a b := by
    rcases hμ with h | h <;> simp only [mem_preimage, mem_Icc, h, le_refl, hab, and_self]
  refine ⟨hμS, fun H K hHS hKS hH hK hμH hμK => ?_⟩
  -- each of `H`, `K` lies in the fibre of `μ` or is saturated
  have key : ∀ {L : Set X}, Fold.Q78.IsContinuum L → μ ∈ L →
      L ⊆ f ⁻¹' {f μ} ∨ f ⁻¹' (f '' L) = L := fun {L} hL hμL => by
    rcases subset_fibre_or_saturated ha hL with ⟨y, hy⟩ | h
    · left
      have : f μ = y := hy hμL
      rw [this]; exact hy
    · exact Or.inr h
  rcases key hH hμH with hHF | hHs <;> rcases key hK hμK with hKF | hKs
  · -- both in the fibre: hereditary indecomposability
    have hU : Fold.Q78.IsContinuum (H ∪ K) := isContinuum_union hH hK ⟨μ, hμH, hμK⟩
    rcases (hHI (f μ) (H ∪ K) (union_subset hHF hKF) hU).2 H K hH hK subset_union_left
      subset_union_right rfl with h | h
    · right; rw [h]; exact subset_union_right
    · left; rw [h]; exact subset_union_left
  · left; exact hHF.trans (fibre_subset_of_saturated hKs hμK)
  · right; exact hKF.trans (fibre_subset_of_saturated hHs hμH)
  · -- both saturated: the images are nested intervals with the common end `f μ`
    have hb : (∀ x ∈ f '' H, f μ ≤ x) ∧ (∀ x ∈ f '' K, f μ ≤ x) ∨
        (∀ x ∈ f '' H, x ≤ f μ) ∧ (∀ x ∈ f '' K, x ≤ f μ) := by
      rcases hμ with h | h
      · left
        exact ⟨fun _ ⟨z, hz, e⟩ => e ▸ h ▸ (hHS hz).1, fun _ ⟨z, hz, e⟩ => e ▸ h ▸ (hKS hz).1⟩
      · right
        exact ⟨fun _ ⟨z, hz, e⟩ => e ▸ h ▸ (hHS hz).2, fun _ ⟨z, hz, e⟩ => e ▸ h ▸ (hKS hz).2⟩
    rcases nested_of_common_bound (hH.2.2.image f hc.continuousOn) (hK.2.2.image f hc.continuousOn)
      (mem_image_of_mem f hμH) (mem_image_of_mem f hμK) hb with h | h
    · left; rw [← hHs, ← hKs]; exact preimage_mono h
    · right; rw [← hHs, ← hKs]; exact preimage_mono h

/-- The fibres of a map whose fibres are continua are preconnected, and their union is everything. -/
theorem isPreconnected_preimage_of_fibres {f : X → unitInterval} (hc : Continuous f)
    (hfib : ∀ t, Fold.Q78.IsContinuum (f ⁻¹' {t})) {I : Set unitInterval}
    (hI : IsPreconnected I) : IsPreconnected (f ⁻¹' I) :=
  isPreconnected_preimage_of_monotone' hc (fun t => (hfib t).2.2) hI
    (fun t _ => (hfib t).2.nonempty.imp fun _ h => h)

/-- **Hereditary unicoherence.** -/
theorem isHereditarilyUnicoherent_of_atomic {f : X → unitInterval} (hc : Continuous f)
    (hfib : ∀ t, IsSnakeLike (f ⁻¹' {t})) (ha : IsAtomicMap f) :
    IsHereditarilyUnicoherent (univ : Set X) := by
  intro K _ hK hnt H L hH hL hHL
  -- `H ∩ L` is nonempty since `K` is connected
  have hne : (H ∩ L).Nonempty := by
    have := hK.2.2
    rw [isPreconnected_closed_iff] at this
    obtain ⟨x, hxK, hxH, hxL⟩ := this H L hH.1.isClosed hL.1.isClosed hHL.symm.subset
      (by obtain ⟨h, hh⟩ := hH.2.nonempty; exact ⟨h, hHL ▸ Or.inl hh, hh⟩)
      (by obtain ⟨l, hl⟩ := hL.2.nonempty; exact ⟨l, hHL ▸ Or.inr hl, hl⟩)
    exact ⟨x, hxH, hxL⟩
  by_cases hKF : ∃ y, K ⊆ f ⁻¹' {y}
  · obtain ⟨y, hy⟩ := hKF
    exact isHereditarilyUnicoherent_of_isSnakeLike (hfib y) K hy hK hnt H L hH hL hHL
  push_neg at hKF
  -- a piece inside a fibre lies in the other piece
  have side : ∀ {H L : Set X}, Fold.Q78.IsContinuum L → H ∪ L = K → (H ∩ L).Nonempty →
      ∀ y, H ⊆ f ⁻¹' {y} → H ⊆ L := fun {H L} hL hHL hne y hy => by
    obtain ⟨x, hxH, hxL⟩ := hne
    rcases ha y L hL ⟨x, hxL, hy hxH⟩ with h | h
    · exact absurd (hHL ▸ union_subset hy h) (hKF y)
    · exact hy.trans h
  rcases subset_fibre_or_saturated ha hH with ⟨y, hy⟩ | hHs
  · rw [inter_eq_left.2 (side hL hHL hne y hy)]; exact hH.2
  rcases subset_fibre_or_saturated ha hL with ⟨y, hy⟩ | hLs
  · rw [inter_eq_right.2 (side hH (by rw [union_comm]; exact hHL) (by rwa [inter_comm]) y hy)]
    exact hL.2
  refine ⟨hne, ?_⟩
  rw [← hHs, ← hLs, ← preimage_inter]
  refine isPreconnected_preimage_of_fibres hc (fun t => (hfib t).1) ?_
  have h1 := hH.2.2.image f hc.continuousOn
  have h2 := hL.2.2.image f hc.continuousOn
  rw [isPreconnected_iff_ordConnected] at h1 h2 ⊢
  exact inferInstance

/-- The whole space is a continuum when it maps onto `[0, 1]` with continuum fibres. -/
theorem isContinuum_univ_of_fibres {f : X → unitInterval} (hc : Continuous f)
    (hfib : ∀ t, Fold.Q78.IsContinuum (f ⁻¹' {t})) : Fold.Q78.IsContinuum (univ : Set X) := by
  refine ⟨isCompact_univ, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := (hfib 0).2.nonempty; exact ⟨x, mem_univ x⟩
  · have := isPreconnected_preimage_of_fibres hc hfib isPreconnected_univ
    rwa [preimage_univ] at this

/-- **An atomic arc of snake-like hereditarily indecomposable continua is snake-like**, by Bing's
proof of 1951 Theorem 11 (`exists_minimal_notCoverable`, `fugate_lemma1`,
`epsCoverable_of_halves`). Openness is not needed. -/
theorem isSnakeLike_of_atomic' {f : X → unitInterval} (hc : Continuous f)
    (hfib : ∀ t, IsSnakeLike (f ⁻¹' {t}) ∧ IsHereditarilyIndecomposable (f ⁻¹' {t}))
    (ha : IsAtomicMap f) : IsSnakeLike (univ : Set X) := by
  have hcont : ∀ t, Fold.Q78.IsContinuum (f ⁻¹' {t}) := fun t => (hfib t).1.1
  refine ⟨isContinuum_univ_of_fibres hc hcont, fun ε hε => ?_⟩
  by_contra hnot
  obtain ⟨S', -, hS', hnc, hmin⟩ :=
    exists_minimal_notCoverable (isContinuum_univ_of_fibres hc hcont) hε hnot
  -- `S'` lies in no fibre
  have hSF : ∀ y, ¬ S' ⊆ f ⁻¹' {y} := fun y hy => by
    obtain ⟨n, D, hD, hcov⟩ := (hfib y).1.2 ε hε
    exact hnc ⟨n, D, hD, hy.trans hcov⟩
  have hSs : f ⁻¹' (f '' S') = S' := (subset_fibre_or_saturated ha hS').resolve_left
    (fun ⟨y, hy⟩ => hSF y hy)
  -- `f '' S' = [a, b]` with `a < b`
  set I := f '' S' with hIdef
  have hIc : IsCompact I := hS'.1.image hc
  have hIne : I.Nonempty := hS'.2.nonempty.image f
  have hIp : IsPreconnected I := hS'.2.2.image f hc.continuousOn
  set a := sInf I
  set b := sSup I
  have haI : a ∈ I := hIc.sInf_mem hIne
  have hbI : b ∈ I := hIc.sSup_mem hIne
  have hII : I = Icc a b := Subset.antisymm
    (fun x hx => ⟨csInf_le hIc.bddBelow hx, le_csSup hIc.bddAbove hx⟩) (hIp.Icc_subset haI hbI)
  have hab : a < b := by
    refine lt_of_le_of_ne (csInf_le hIc.bddBelow hbI) fun e => hSF a fun x hx => ?_
    have : f x ∈ Icc a b := hII ▸ mem_image_of_mem f hx
    exact le_antisymm (e ▸ this.2) this.1
  have hab' : (a : ℝ) < b := hab
  set c : unitInterval := ⟨((a : ℝ) + b) / 2, by
    constructor <;> [linarith [a.2.1, b.2.1]; linarith [a.2.2, b.2.2]]⟩
  have hac : a < c := show (a : ℝ) < ((a : ℝ) + b) / 2 by linarith
  have hcb : c < b := show ((a : ℝ) + b) / 2 < b by linarith
  have hS'eq : S' = f ⁻¹' Icc a b := by rw [← hII, hSs]
  set A := f ⁻¹' Icc a c
  set C := f ⁻¹' Icc c b
  have hAC : A ∪ C = S' := by
    rw [hS'eq, ← preimage_union, Icc_union_Icc_eq_Icc hac.le hcb.le]
  have hAiC : A ∩ C = f ⁻¹' {c} := by
    rw [← preimage_inter, Icc_inter_Icc, max_eq_right hac.le, min_eq_left hcb.le, Icc_self]
  have hcontI : ∀ {u v : unitInterval}, u ≤ v → Fold.Q78.IsContinuum (f ⁻¹' Icc u v) :=
    fun {u v} huv => ⟨(isClosed_Icc.preimage hc).isCompact,
      (hcont u).2.nonempty.mono (preimage_mono (singleton_subset_iff.2 ⟨le_rfl, huv⟩)),
      isPreconnected_preimage_of_fibres hc hcont isPreconnected_Icc⟩
  have hA : Fold.Q78.IsContinuum A := hcontI hac.le
  have hC : Fold.Q78.IsContinuum C := hcontI hcb.le
  obtain ⟨μ, hμ⟩ := (hcont c).2.nonempty
  have hμc : f μ = c := hμ
  have hAS : A ⊆ S' := hAC ▸ subset_union_left
  have hCS : C ⊆ S' := hAC ▸ subset_union_right
  have hAne : A ≠ S' := fun e => by
    obtain ⟨x, hx⟩ := (hcont b).2.nonempty
    have hfx : f x = b := hx
    have hxS : x ∈ S' := hS'eq ▸ (show f x ∈ Icc a b by rw [hfx]; exact ⟨hab.le, le_rfl⟩)
    have : f x ≤ c := (e ▸ hxS : x ∈ A).2
    rw [show f x = b from hx] at this
    exact absurd this (not_le.2 hcb)
  have hCne : C ≠ S' := fun e => by
    obtain ⟨x, hx⟩ := (hcont a).2.nonempty
    have hfx : f x = a := hx
    have hxS : x ∈ S' := hS'eq ▸ (show f x ∈ Icc a b by rw [hfx]; exact ⟨le_rfl, hab.le⟩)
    have : c ≤ f x := (e ▸ hxS : x ∈ C).1
    rw [show f x = a from hx] at this
    exact absurd this (not_le.2 hac)
  have hHI : ∀ t, IsHereditarilyIndecomposable (f ⁻¹' {t}) := fun t => (hfib t).2
  have hBA : CondB A μ := condB_preimage_Icc hc hHI ha hac.le (Or.inr hμc)
  have hBC : CondB C μ := condB_preimage_Icc hc hHI ha hcb.le (Or.inl hμc)
  have chain : ∀ {K : Set X}, Fold.Q78.IsContinuum K → K ⊆ S' → K ≠ S' → CondB K μ →
      ∃ (x : ℕ) (E : Chain X x) (hx : 0 < x), IsEpsChain E ε ∧ K ⊆ E.union ∧
        μ ∈ E.link ⟨x - 1, by omega⟩ := by
    intro K hK hKS hKne hB
    obtain ⟨m, D, hD, hKD⟩ := hmin K hKS hK hKne
    obtain ⟨n, F, hn, hKF, hFD, z, hz, hzF, -⟩ := fugate_lemma1 hK
      ((isTerminalSub_singleton_iff _ _).mpr hB) D hKD
    rw [mem_singleton_iff] at hz
    subst hz
    exact ⟨n, F, hn, isEpsChain_of_refines hFD hD, hKF, hzF⟩
  have hclaim1 : ∀ Q : Set X, Fold.Q78.IsContinuum Q → Q ⊆ C → (Q ∩ (A ∩ C)).Nonempty →
      ¬ Q ⊆ A ∩ C → A ∩ C ⊆ Q := by
    intro Q hQ _ hm hn
    rw [hAiC] at hm hn ⊢
    exact (ha c Q hQ hm).resolve_left hn
  exact hnc (epsCoverable_of_halves hS'
    ((isHereditarilyUnicoherent_of_atomic hc (fun t => (hfib t).1) ha).mono (subset_univ _))
    hA hC hAC ⟨⟨hμc ▸ hac.le, hμc ▸ le_rfl⟩, ⟨hμc ▸ le_rfl, hμc ▸ hcb.le⟩⟩ hclaim1 hε
    (chain hA hAS hAne hBA) (chain hC hCS hCne hBC))

/-- The case of pseudo-arc fibres (the step Domokos–Prajs take from Hagopian–Marsh–Prajs,
Proposition 6). -/
theorem isSnakeLike_of_atomic {f : X → unitInterval} (hc : Continuous f)
    (hfib : ∀ t, IsPseudoArc (f ⁻¹' {t})) (ha : IsAtomicMap f) :
    IsSnakeLike (univ : Set X) :=
  isSnakeLike_of_atomic' hc (fun t => ⟨(hfib t).1, (hfib t).2.1⟩) ha

end Arc


/-- Non-vacuity of `isSnakeLike_of_atomic'` and `isHereditarilyUnicoherent_of_atomic`: the identity
of `[0, 1]`. -/
theorem nonvac_isSnakeLike_of_atomic' :
    Continuous (id : unitInterval → unitInterval) ∧
      (∀ t : unitInterval, IsSnakeLike ((id : unitInterval → unitInterval) ⁻¹' {t}) ∧
        IsHereditarilyIndecomposable ((id : unitInterval → unitInterval) ⁻¹' {t})) ∧
      IsAtomicMap (id : unitInterval → unitInterval) := by
  refine ⟨continuous_id, fun t => ⟨⟨⟨isCompact_singleton, isConnected_singleton⟩,
    fun ε hε => epsCoverable_singleton t hε⟩, fun K hK hKc => ?_⟩, isAtomicMap_id⟩
  have : K = {t} := (Set.Nonempty.subset_singleton_iff hKc.2.nonempty).1 hK
  rw [this]; exact isIndecomposable_singleton t

end HPC.BJ59
