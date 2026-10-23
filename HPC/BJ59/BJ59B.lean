import HPC.BJ59.AtomicCircle
import HPC.BJ59.BJChains
import HPC.BJ59.Thm7
import HPC.BJ59.Thm7Ends2

/-!
# Batch 199: Part G, II — the circle-likeness step (Domokos–Prajs 2022, Theorem 6.1);
# Bing–Jones Theorems 7 and 9

The skeleton of commission 199. §§2–3 are in `HPC/BJ59/Atomic.lean` and §4 in
`HPC/BJ59/AtomicCircle.lean` and `HPC/BJ59/CircleLike.lean` (the statements verbatim, except where a
shape change is recorded at the statement); §§5–6 are here, except `IsBJChain` and
`exists_bjChain_shrink` (in `HPC/BJ59/BJChains.lean`).

Sources: A. Domokos and J. R. Prajs, *The Planck boundary within the hyperspace of the circle of
pseudo-arcs*, arXiv:2203.15906v1 (2022), §6 (`doc/sources/domokos-prajs2022.pdf`); R. H. Bing and
F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959), §§4–5
(`doc/sources/bing-jones1959.pdf`; PDF page `n` is journal page `169 + n`). Route: commission 199.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.HO16

/- OPEN (batch 199, optional item of commission 199 §4): Domokos–Prajs's "one can easily show
that X is atriodic" (p. 14). Not attempted in this batch: the route of commission §4 (three
saturated continua whose images are arcs of the circle pairwise meeting exactly in one arc or
point) needs facts about subcontinua of the circle not developed here. The theorem is not used by
any route in this batch (Domokos–Prajs use it only for Hagopian–Marsh–Prajs Proposition 6, which
§3 replaces). See `OPEN.md`.

/-! **Domokos–Prajs (optional)**, p. 14: "one can easily show that X is atriodic". -/
theorem isAtriodic_of_atomic {X : Type*} [MetricSpace X] [CompactSpace X] {f : X → Circle}
    (hf : IsAtomicCircPAMap f) : IsAtriodic (univ : Set X) := by
  sorry
-/

/-! ## §5. The decomposable case and the classification -/

/-- **The decomposable case without circle-likeness**: a decomposable homogeneous plane continuum
is a simple closed curve or has an open atomic map onto the circle with pseudo-arc fibres. -/
theorem circle_or_atomic_of_decomposable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]
    (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    Nonempty (M ≃ₜ Circle) ∨ ∃ f : M → Circle, IsAtomicCircPAMap f := by
  obtain ⟨hcd, ⟨e⟩, -⟩ := jones55_theorem2' hX hd
  set q : M → Circle := fun x => e (Quotient.mk _ x)
  have hqc : Continuous q := e.continuous.comp continuous_quotient_mk'
  have hqs : Function.Surjective q := e.surjective.comp Quotient.mk_surjective
  have hfib : ∀ x : M, q ⁻¹' {q x} = Lset x := fun x => by
    ext y
    simp only [mem_preimage, mem_singleton_iff, q, e.injective.eq_iff]
    rw [mk_eq_mk_iff_mem_cls, cls_lSetoid hX]
  by_cases hap : IsAposyndetic M
  · left
    have hinj : Function.Injective q := fun x y h => by
      have : y ∈ q ⁻¹' {q x} := h.symm
      rw [hfib, Lset_eq_singleton_of_isAposyndetic hap] at this
      exact this.symm
    exact ⟨hqc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective q ⟨hinj, hqs⟩)⟩
  · right
    refine ⟨q, hqc, e.isOpenMap.comp (isOpenMap_quotient_mk_of_continuous hcd), hqs,
      fun z => ?_, fun z L hL hm => ?_⟩
    · obtain ⟨x, rfl⟩ := hqs z
      rw [hfib]
      exact isPseudoArc_Lset' hX hd x (jones55_elements hX hap x x).1
    · -- atomicity: Jones's elements are terminal (`jones55_c`)
      obtain ⟨x, rfl⟩ := hqs z
      rw [hfib] at hm ⊢
      by_cases h : L ⊆ Lset x
      · exact Or.inl h
      · obtain ⟨y, hyL, hy⟩ := not_subset.1 h
        exact Or.inr (jones55_c hX hL hm ⟨y, hyL, hy⟩)

/-- **`HOCircleLike`**, from Bing–Jones Theorem 10 and a plane circle of pseudo-arcs. -/
theorem hoCircleLike (h10 : BJThm10) (hEx : BJPlaneExample) : HOCircleLike := by
  intro M hc hk hX hd
  rcases circle_or_atomic_of_decomposable hX hd with he | ⟨f, hf⟩
  · obtain ⟨e⟩ := he
    exact isCircleLike_univ_of_homeomorph e isCircleLike_circle
  · obtain ⟨C, hC⟩ := hEx
    exact (isCircleOfPA_of_atomic h10 hf hC).1

/-- **The classification, with Domokos–Prajs's third class**; Theorem 10 is the only named input. -/
theorem ho16_classification_atomic (h10 : BJThm10) (M : Set Pt) [CompactSpace M]
    [ConnectedSpace M] (hnt : (univ : Set M).Nontrivial) :
    IsHomogeneous M ↔ Nonempty (M ≃ₜ Circle) ∨ IsPseudoArc (univ : Set M) ∨
      ∃ f : M → Circle, IsAtomicCircPAMap f := by
  constructor
  · intro hX
    by_cases hd : IsDecomposableSpace M
    · rcases circle_or_atomic_of_decomposable hX hd with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl ((ho16_indec_homogeneous_iff M hnt).1 ⟨hX, hd⟩))
  · rintro (he | h | ⟨f, hf⟩)
    · obtain ⟨e⟩ := he
      exact IsHomogeneous.of_homeomorph e.symm isHomogeneous_circle
    · exact (ho16_pseudoArc_indec_homogeneous M h).1
    · exact isHomogeneous_of_atomic h10 hf

/-- **The classification with Bing–Jones's third class**, from Theorem 10 and §7. -/
theorem ho16_classification₂ (h10 : BJThm10) (hEx : BJPlaneExample) (M : Set Pt)
    [CompactSpace M] [ConnectedSpace M] (hnt : (univ : Set M).Nontrivial) :
    IsHomogeneous M ↔ Nonempty (M ≃ₜ Circle) ∨ IsPseudoArc (univ : Set M) ∨ IsCircleOfPA M := by
  exact ho16_classification h10 (hoCircleLike h10 hEx) M hnt

/-- **The classification of homogeneous plane continua**, from Theorem 10 and §7. -/
theorem ho16_classification_plane₂ (h10 : BJThm10) (hEx : BJPlaneExample) :
    ∃ C₁ C₂ C₃ : Set Pt,
      (Nonempty (C₁ ≃ₜ Circle) ∧ IsPseudoArc C₂ ∧ IsCircleOfPA C₃) ∧
      (IsHomogeneous C₁ ∧ IsHomogeneous C₂ ∧ IsHomogeneous C₃) ∧
      (IsEmpty (C₁ ≃ₜ C₂) ∧ IsEmpty (C₁ ≃ₜ C₃) ∧ IsEmpty (C₂ ≃ₜ C₃)) ∧
      ∀ M : Set Pt, IsCompact M → IsConnected M → M.Nontrivial →
        (IsHomogeneous M ↔ Nonempty (M ≃ₜ C₁) ∨ Nonempty (M ≃ₜ C₂) ∨ Nonempty (M ≃ₜ C₃)) := by
  exact ho16_classification_plane h10 (hoCircleLike h10 hEx) hEx

/-- Non-vacuity of §4: under the two named inputs, the plane circle of pseudo-arcs carries an open
atomic map onto the circle with pseudo-arc fibres. -/
theorem nonvac_atomic (h10 : BJThm10) (hEx : BJPlaneExample) :
    ∃ C : Set Pt, ∃ f : C → Circle, IsAtomicCircPAMap f := by
  obtain ⟨C, hC⟩ := hEx
  obtain ⟨f, hf⟩ := isCircleOfPA_iff.1 hC
  haveI := hf.compactSpace
  haveI : ConnectedSpace C :=
    { isPreconnected_univ := hf.circ.1.2.isPreconnected
      toNonempty := ⟨hf.circ.1.2.nonempty.some⟩ }
  rcases circle_or_atomic_of_decomposable (isHomogeneous_of_isCircleOfPA h10 hC)
    (isDecomposableSpace_of_isCircPAMap hf) with hψ | h
  · -- a circle of pseudo-arcs is not a simple closed curve: a fibre would be a proper pseudo-arc
    -- in the circle
    exfalso
    obtain ⟨ψ⟩ := hψ
    set F : Set C := f ⁻¹' {1}
    have hK : IsPseudoArc (ψ '' F) := isPseudoArc_of_homeomorph (hf.fib 1) (ψ.image F)
    refine not_isPseudoArc_of_ne_univ_circle (fun hu => ?_) hK
    obtain ⟨x, hx⟩ := hf.surj (Circle.exp Real.pi)
    obtain ⟨y, hy, hyx⟩ : ψ x ∈ ψ '' F := hu ▸ mem_univ _
    have : y = x := ψ.injective hyx
    subst this
    have h1 : f y = 1 := hy
    rw [hx] at h1
    exact circle_exp_pi_ne_one h1
  · exact ⟨C, h⟩

/-! ## §6. Chains in Bing–Jones's sense; Theorems 7 and 9 -/

section Chains

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- **Bing–Jones, Theorem 7** (pp. 176–177), first sentence. The hypothesis on `D` is the library's
(weaker) notion of chain; the conclusion is a chain in Bing–Jones's sense. -/
theorem bj_theorem7 {P : Set X} (hP : IsPseudoArc P) {n m : ℕ} (D : Chain X n)
    (hDP : P ⊆ D.union) (hDp : ∀ j, (D.link j ∩ P).Nonempty) (H : Fin m → Fin n)
    (hH : IsChainMap H) (hHs : Function.Surjective H) :
    ∃ E : Chain X m, IsBJChain E ∧ P ⊆ E.union ∧ (∀ i, (E.link i ∩ P).Nonempty) ∧
      ∀ i, E.link i ⊆ D.link (H i) := by
  exact bj_theorem7' hP D hDP hDp H hH hHs

/-- **Bing–Jones, Theorem 7, second sentence**, for chains of at least three links, reading
"closed sets in P·d₁" as subsets of `P·d₁` closed in the space (commission 199 §6). The
surjectivity hypothesis `hHs` of the skeleton turned out to be unnecessary (`H` meets the first and
last links at `r`, `s` and is a chain map, hence is onto); it is kept as stated. -/
theorem bj_theorem7_ends {P : Set X} (hP : IsPseudoArc P) {n m : ℕ} (hn : 3 ≤ n) (D : Chain X n)
    (hDP : P ⊆ D.union) (hDp : ∀ j, (D.link j ∩ P).Nonempty) (H : Fin m → Fin n)
    (hH : IsChainMap H) (hHs : Function.Surjective H) {r s : Fin m} (hr : (H r).val = 0)
    (hs : (H s).val = n - 1) {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAP : A ⊆ P ∩ D.link (H r)) (hBP : B ⊆ P ∩ D.link (H s)) :
    ∃ E : Chain X m, IsBJChain E ∧ P ⊆ E.union ∧ (∀ i, (E.link i ∩ P).Nonempty) ∧
      (∀ i, E.link i ⊆ D.link (H i)) ∧ A ⊆ E.link r ∧ B ⊆ E.link s :=
  bj_theorem7_ends' hP hn D hDP hDp H hH hr hs hA hB hAP hBP

/- OPEN (batch 199): Bing–Jones Theorem 9 (p. 179), the stretch item of commission 199 §6.
It needs the back-and-forth construction of a homeomorphism from two sequences of chains with
pattern maps (Bing–Jones pp. 179–180), resting on Theorem 7 and its second sentence (both proved
in this batch, `bj_theorem7`, `bj_theorem7_ends`); not attempted. See `OPEN.md`.

/-! **Bing–Jones, Theorem 9** (p. 179). -/
theorem bj_theorem9 {P : Set X} {Q : Set Y} (hP : IsPseudoArc P) (hQ : IsPseudoArc Q) {n m : ℕ}
    (D : Chain X n) (E : Chain Y m) (hD : IsBJChain D) (hE : IsBJChain E)
    (hDP : P ⊆ D.union) (hDp : ∀ i, (D.link i ∩ P).Nonempty)
    (hEQ : Q ⊆ E.union) (hEq : ∀ j, (E.link j ∩ Q).Nonempty)
    (H : Fin n → Fin m) (hH : IsChainMap H)
    (hHo : ∀ j, ∃ i, H i = j ∧ ∃ p ∈ P ∩ D.link i, ∀ i', i' ≠ i → p ∉ closure (D.link i')) :
    ∃ h : P ≃ₜ Q, ∀ (i : Fin n) (p : P), (p : X) ∈ D.link i → (h p : Y) ∈ E.link (H i) := by
  sorry
-/

end Chains

/-- **The second sentence of Theorem 7 as printed fails for a chain of one link**: a plane
pseudo-arc `P`, `D` one link, `X` three links mapped onto it, `A = B = {p}`, `r = 1`, `s = 3`
(Bing–Jones's indices). -/
theorem bj_theorem7_ends_printed_false : ¬ ∀ (P : Set Pt), IsPseudoArc P → ∀ (n m : ℕ)
    (D : Chain Pt n), P ⊆ D.union → (∀ j, (D.link j ∩ P).Nonempty) →
    ∀ H : Fin m → Fin n, IsChainMap H → Function.Surjective H →
    ∀ r s : Fin m, (H r).val = 0 → (H s).val = n - 1 → ∀ A B : Set Pt, IsClosed A → IsClosed B →
      A ⊆ P ∩ D.link (H r) → B ⊆ P ∩ D.link (H s) →
      ∃ E : Chain Pt m, P ⊆ E.union ∧ (∀ i, (E.link i ∩ P).Nonempty) ∧
        (∀ i, E.link i ⊆ D.link (H i)) ∧ A ⊆ E.link r ∧ B ⊆ E.link s := by
  intro h
  obtain ⟨P, hP⟩ := isPseudoArc_plane
  obtain ⟨p, hp⟩ := hP.2.2.nonempty
  obtain ⟨E, -, -, -, hA, hB⟩ := h P hP 1 3 (oneLinkChain Pt)
    (fun x _ => mem_iUnion.2 ⟨0, mem_univ x⟩) (fun _ => ⟨p, mem_univ p, hp⟩)
    (fun _ => 0) (fun _ _ _ => by simp) (fun j => ⟨0, Subsingleton.elim _ _⟩) 0 2 rfl rfl
    {p} {p} isClosed_singleton isClosed_singleton
    (singleton_subset_iff.2 ⟨hp, mem_univ p⟩) (singleton_subset_iff.2 ⟨hp, mem_univ p⟩)
  have := (E.adjacent 0 2).1 ⟨p, hA rfl, hB rfl⟩
  simp at this

/-- A nondegenerate snake-like continuum is properly covered by a chain in Bing–Jones's sense with
at least three links. -/
theorem exists_bjChain_three {X : Type*} [MetricSpace X] {P : Set X} (hP : IsSnakeLike P)
    (hnt : P.Nontrivial) : ∃ n, 3 ≤ n ∧ ∃ D : Chain X n,
      IsBJChain D ∧ P ⊆ D.union ∧ ∀ j, (D.link j ∩ P).Nonempty := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnt
  have hd : 0 < dist a b := dist_pos.2 hab
  obtain ⟨n, D, hDε, hPD, hDP⟩ := exists_cover_meeting hP.1.2.isPreconnected hP.1.2.nonempty
    hP.2 (by linarith : 0 < dist a b / 3)
  have hn : 3 ≤ n := by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hPD ha)
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hPD hb)
    by_contra hlt
    have := i.2; have := j.2
    have hij : ((i : ℤ) - j).natAbs ≤ 1 := by omega
    have := D.dist_le_of_mem_links' (fun t => (hDε t).1) (fun t => (hDε t).2.le) 1 i j
      (by exact_mod_cast hij) hi hj
    push_cast at this
    linarith
  obtain ⟨D', hBJ, hPD', hD'P, -⟩ := exists_bjChain_shrink hP.1 D hPD hDP (fun _ => ∅)
    (fun _ => ⟨isCompact_empty, empty_subset _⟩)
  exact ⟨n, hn, D', hBJ, hPD', hD'P⟩

/-- Non-vacuity of §6: a plane pseudo-arc with a chain of at least three links properly covering
it, in Bing–Jones's sense. -/
theorem nonvac_bj_chains : ∃ P : Set Pt, IsPseudoArc P ∧ ∃ n, 3 ≤ n ∧ ∃ D : Chain Pt n,
    IsBJChain D ∧ P ⊆ D.union ∧ ∀ j, (D.link j ∩ P).Nonempty := by
  obtain ⟨P, hP⟩ := isPseudoArc_plane
  exact ⟨P, hP, exists_bjChain_three hP.1 hP.2.2⟩

end HPC.BJ59
