import HPC.Jones.Jones48
import HPC.Plane.Arcs48

/-!
# Batch 136, item D: the core of Jones 1955, Theorem 1

F. B. Jones, *On a certain type of homogeneous plane continuum*, Proc. AMS 6 (1955), 735–740.
Notation (p. 736): `L_x` is `x` together with all points `y` such that `M` is not aposyndetic at
`y` with respect to `x`; `U_x = M − L_x` (`aposSet x`). The definitions `Lset`, `CutsFrom`,
`lRel`, `lSetoid` are the skeleton's (§5), unchanged.

**The decisive step is not Jones's.** Jones obtains (b) and (c) of his Theorem 1 through the sets
`H`, `N_o`, the claims (9)–(12), and the case argument "`N_o + U_o ≠ M`" with `d(q)`, `E_n`, `M₀`
(pp. 737–738). Here both follow from one consequence of the Effros theorem
(`HPC.Effros.effros_homogeneous`, batch 134):

* `aposAt_of_isContinuum_interior` (**spreading**): in a homogeneous compact metric space, if a
  continuum `K` with nonempty interior contains `o` and misses `x`, then `X` is aposyndetic at `o`
  with respect to `x`. (Move `K` by all homeomorphisms `ε`-close to the identity; the closure of the
  union is a continuum, since each image meets `K` in its interior, it still misses `x`, and by
  Effros it contains a ball about `o`.)

Then:

* `not_aposAt_trans`: non-aposyndesis is transitive;
* `aposSet_eq_of_not_aposAt`: `y ∈ L_x ⇒ U_y = U_x` (transitivity gives `U_x ⊆ U_y`, then the
  Lemma of Jones 1951);
* `mem_Lset_iff_Lset_eq` (Theorem 1 (b)) and `Lset_subset_of_meets` (Theorem 1 (c)).

Neither uses decomposability; (b) and (c) hold in every homogeneous compact metric space. Jones's
claims (1)–(12) are kept as named lemmas `jones55_claim1` … `jones55_claim12`, in his numbering;
(1)–(10) by Jones's arguments, (11) and (12) from (c) (they replace Jones's transfinite sequence of
closed sets and his use of (11) in (12)). The characterization `N_o = L_o` and the properties
(a)–(f) of p. 739 follow.
-/

namespace HPC.Jones

open Set Topology Filter Metric

/-! ### Spreading (Effros) -/

section Spread

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Spreading.** In a homogeneous compact metric space, if a continuum `K` with nonempty interior
contains `o` and misses `x`, then `X` is aposyndetic at `o` with respect to `x`. -/
theorem aposAt_of_isContinuum_interior (hX : IsHomogeneous X) {K : Set X}
    (hK : Fold.Q78.IsContinuum K) (hint : (interior K).Nonempty) {o x : X} (ho : o ∈ K)
    (hx : x ∉ K) : AposAt o x := by
  obtain ⟨b, hb⟩ := hint
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp isOpen_interior b hb
  have hd : 0 < infDist x K := (hK.1.isClosed.notMem_iff_infDist_pos ⟨o, ho⟩).mp hx
  set ε := min ε₀ (infDist x K / 2) with hεdef
  have hε : 0 < ε := lt_min hε₀ (half_pos hd)
  obtain ⟨δ, hδ, hEff⟩ := HPC.Effros.effros_homogeneous hX hε
  set S : Set (X ≃ₜ X) := {h | ∀ z, dist (h z) z < ε}
  set 𝒞 : Set (Set X) := (fun h : X ≃ₜ X => K ∪ h '' K) '' S
  set Z : Set X := closure (⋃₀ 𝒞)
  have hpre : IsPreconnected (⋃₀ 𝒞) := by
    refine isPreconnected_sUnion o 𝒞 ?_ ?_
    · rintro _ ⟨h, -, rfl⟩
      exact Or.inl ho
    · rintro _ ⟨h, hS, rfl⟩
      have hhb : h b ∈ K := by
        refine interior_subset (hball ?_)
        exact lt_of_lt_of_le (hS b) (min_le_left _ _)
      exact hK.2.isPreconnected.union (h b) hhb ⟨b, interior_subset hb, rfl⟩
        (hK.2.isPreconnected.image _ h.continuous.continuousOn)
  have hZsub : Z ⊆ {z | infDist z K ≤ ε} := by
    refine closure_minimal ?_ (isClosed_le (continuous_infDist_pt K) continuous_const)
    rintro z ⟨_, ⟨h, hS, rfl⟩, hz⟩
    rcases hz with hz | ⟨k, hk, rfl⟩
    · show infDist z K ≤ ε
      rw [infDist_zero_of_mem hz]
      exact hε.le
    · show infDist (h k) K ≤ ε
      exact (infDist_le_dist_of_mem hk).trans (hS k).le
  have hxZ : x ∉ Z := by
    intro hxZ
    have h1 : infDist x K ≤ ε := hZsub hxZ
    have h2 : ε ≤ infDist x K / 2 := min_le_right _ _
    linarith
  have hballZ : ball o δ ⊆ Z := by
    intro y hy
    obtain ⟨h, hho, hS⟩ := hEff o y (by rw [dist_comm]; exact hy)
    refine subset_closure ⟨K ∪ h '' K, ⟨h, hS, rfl⟩, Or.inr ⟨o, ho, hho⟩⟩
  refine ⟨Z, ball o δ, ⟨isClosed_closure.isCompact, ?_⟩, isOpen_ball, mem_ball_self hδ, hballZ,
    hxZ⟩
  exact ⟨⟨o, hballZ (mem_ball_self hδ)⟩, hpre.closure⟩

/-- **Non-aposyndesis is transitive** in a homogeneous compact metric space. -/
theorem not_aposAt_trans (hX : IsHomogeneous X) {x y z : X} (hzy : ¬ AposAt z y)
    (hyx : ¬ AposAt y x) : ¬ AposAt z x := by
  rintro ⟨K, V, hK, hV, hzV, hVK, hxK⟩
  have hyK : y ∈ K := by
    by_contra hyK
    exact hzy ⟨K, V, hK, hV, hzV, hVK, hyK⟩
  exact hyx (aposAt_of_isContinuum_interior hX hK
    ⟨z, interior_maximal hVK hV hzV⟩ hyK hxK)

/-- If `X` is not aposyndetic at `y` with respect to `x`, then `U_y = U_x`. -/
theorem aposSet_eq_of_not_aposAt (hX : IsHomogeneous X) {x y : X} (h : ¬ AposAt y x) :
    aposSet y = aposSet x := by
  have hsub : aposSet x ⊆ aposSet y := by
    intro z hz
    rw [aposSet_eq] at hz ⊢
    by_contra hzy
    exact not_aposAt_trans hX hzy h hz
  by_contra hne
  exact jones51_lemma hX (ssubset_iff_subset_ne.mpr ⟨hsub, fun he => hne he.symm⟩)

omit [CompactSpace X] in
/-- Homeomorphisms preserve "cuts". -/
theorem CutsPts.image (T : X ≃ₜ X) {p x y : X} (h : CutsPts p x y) :
    CutsPts (T p) (T x) (T y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun e => h1 (T.injective e), fun e => h2 (T.injective e),
    fun e => h3 (T.injective e), fun K hK hxK hyK => ?_⟩
  have := h4 (T.symm '' K) (isContinuum_image_homeomorph T.symm hK) ⟨T x, hxK, by simp⟩
    ⟨T y, hyK, by simp⟩
  obtain ⟨w, hw, hwp⟩ := this
  rw [← hwp, T.apply_symm_apply]
  exact hw

end Spread

/-! ### Definitions (skeleton §5) -/

section Jones55

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- `L_x`. -/
def Lset (x : X) : Set X := insert x {y | y ≠ x ∧ ¬ AposAt y x}

/-- **`p` cuts `o` from `S`** (Jones 1955, used from (6) on): every continuum containing `o` and a
point of `S` contains `p`. The convention for `p = o` and for `o ∈ S` is to be read from the text
and recorded; `p ≠ o` is included here. -/
def CutsFrom (p o : X) (S : Set X) : Prop :=
  p ≠ o ∧ ∀ K : Set X, Fold.Q78.IsContinuum K → o ∈ K → (K ∩ S).Nonempty → p ∈ K

/-- The decomposition `G = {L_x}` as a relation. -/
def lRel (x y : X) : Prop := Lset x = Lset y

def lSetoid (X : Type*) [MetricSpace X] [CompactSpace X] [ConnectedSpace X] : Setoid X where
  r := lRel
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-! ### Elementary facts about `L_x` -/

omit [CompactSpace X] [ConnectedSpace X] in
theorem mem_Lset_iff {x y : X} : y ∈ Lset x ↔ ¬ AposAt y x := by
  by_cases hy : y = x
  · subst hy
    simp [Lset, not_aposAt_self]
  · simp [Lset, hy]

omit [CompactSpace X] [ConnectedSpace X] in
theorem Lset_eq_setOf (x : X) : Lset x = {y | ¬ AposAt y x} := by
  ext y
  exact mem_Lset_iff

omit [CompactSpace X] [ConnectedSpace X] in
theorem mem_Lset_self (x : X) : x ∈ Lset x := mem_insert x _

omit [CompactSpace X] [ConnectedSpace X] in
theorem notMem_aposSet_self (x : X) : x ∉ aposSet x := fun h => h.1 rfl

omit [CompactSpace X] [ConnectedSpace X] in
theorem Lset_compl (x : X) : (Lset x)ᶜ = aposSet x := by
  ext y
  rw [mem_compl_iff, mem_Lset_iff, not_not, aposSet_eq]
  rfl

omit [CompactSpace X] [ConnectedSpace X] in
theorem Lset_eq_compl (x : X) : Lset x = (aposSet x)ᶜ := by
  rw [← Lset_compl, compl_compl]

omit [CompactSpace X] [ConnectedSpace X] in
theorem isClosed_Lset (x : X) : IsClosed (Lset x) := by
  rw [Lset_eq_setOf]
  exact isClosed_not_aposAt_left x

/-- Each `L_x` is a continuum (Jones 1948, Theorem 3). -/
theorem isContinuum_Lset (x : X) : Fold.Q78.IsContinuum (Lset x) := by
  have h := theorem3 x
  rwa [setOf_theorem3_eq, ← Lset_eq_setOf] at h

omit [CompactSpace X] [ConnectedSpace X] in
theorem Lset_homeomorph (T : X ≃ₜ X) (x : X) : Lset (T x) = T '' Lset x := by
  rw [Lset_eq_compl, Lset_eq_compl, aposSet_homeomorph, T.image_compl]

/-! ### Theorem 1 (b) and (c), for every homogeneous compact metric continuum -/

omit [ConnectedSpace X] in
/-- **Theorem 1 (b), general form.** In a homogeneous compact metric continuum, `y ∈ L_x` iff
`L_y = L_x`. -/
theorem mem_Lset_iff_Lset_eq (hX : IsHomogeneous X) {x y : X} :
    y ∈ Lset x ↔ Lset y = Lset x := by
  constructor
  · intro h
    rw [Lset_eq_compl, Lset_eq_compl, aposSet_eq_of_not_aposAt hX (mem_Lset_iff.mp h)]
  · intro h
    rw [← h]
    exact mem_Lset_self y

omit [ConnectedSpace X] in
/-- **Theorem 1 (c), general form.** In a homogeneous compact metric continuum, a subcontinuum
meeting `L_x` and its complement contains `L_x`. -/
theorem Lset_subset_of_meets (hX : IsHomogeneous X) {x : X} {K : Set X}
    (hK : Fold.Q78.IsContinuum K) (h1 : (K ∩ Lset x).Nonempty) (h2 : (K \ Lset x).Nonempty) :
    Lset x ⊆ K := by
  obtain ⟨a, haK, hax⟩ := h1
  obtain ⟨b, hbK, hbx⟩ := h2
  intro y hy
  by_contra hyK
  have hLy : Lset y = Lset x := (mem_Lset_iff_Lset_eq hX).mp hy
  have hby : AposAt b y := by
    have : b ∉ Lset y := hLy ▸ hbx
    rwa [mem_Lset_iff, not_not] at this
  obtain ⟨B, O, hB, hO, hbO, hOB, hyB⟩ := hby
  have hK' : Fold.Q78.IsContinuum (K ∪ B) :=
    ⟨hK.1.union hB.1, IsConnected.union ⟨b, hbK, hOB hbO⟩ hK.2 hB.2⟩
  have hint : (interior (K ∪ B)).Nonempty :=
    ⟨b, interior_maximal (hOB.trans subset_union_right) hO hbO⟩
  have hay : AposAt a y := aposAt_of_isContinuum_interior hX hK' hint (Or.inl haK)
    (fun h => h.elim hyK hyB)
  exact (mem_Lset_iff.mp (hLy ▸ hax)) hay

/-! ### Tools for the claims -/

omit [CompactSpace X] in
/-- An open set in a nondegenerate continuum is a single point only if empty. -/
theorem isOpen_nontrivial_of_nonempty [Nontrivial X] {U : Set X} (hU : IsOpen U)
    (hne : U.Nonempty) : U.Nontrivial := by
  obtain ⟨z, hz⟩ := hne
  by_contra hnt
  have hUz : U = {z} := (not_nontrivial_iff.mp hnt).eq_singleton_of_mem hz
  have hclopen : IsClopen ({z} : Set X) := ⟨isClosed_singleton, hUz ▸ hU⟩
  rcases isClopen_iff.mp hclopen with h | h
  · exact singleton_ne_empty z h
  · obtain ⟨w, hw⟩ := exists_ne z
    exact hw (by simpa using (h ▸ mem_univ w : w ∈ ({z} : Set X)))

/-- **Claim (3), Bing's form transferred.** In a homogeneous nondegenerate compact metric
continuum, no point cuts two nonempty open sets from each other: some continuum meets both and
misses the point. (Bing 1948, Corollary 2, `HPC.Plane.arcs_corollary2`, and homogeneity. Bing's
`Cuts` asks `A ⊄ R`; for a nonempty open `A` and `R = {p}` this holds since `{p}` is not open.) -/
theorem exists_continuum_meets_of_open [Nontrivial X] (hX : IsHomogeneous X) (p : X)
    {D E : Set X} (hD : IsOpen D) (hE : IsOpen E) (hDne : D.Nonempty) (hEne : E.Nonempty) :
    ∃ K : Set X, Fold.Q78.IsContinuum K ∧ p ∉ K ∧ (K ∩ D).Nonempty ∧ (K ∩ E).Nonempty := by
  obtain ⟨p₀, -, -, -, -, hp₀, -⟩ := HPC.Plane.arcs_corollary2 (S := X) (M := univ)
    ⟨isCompact_univ, isConnected_univ⟩ nontrivial_univ
  obtain ⟨T, hT⟩ := hX p₀ p
  have hD' : IsOpen (T ⁻¹' D) := hD.preimage T.continuous
  have hE' : IsOpen (T ⁻¹' E) := hE.preimage T.continuous
  have hDne' : (T ⁻¹' D ∩ univ).Nonempty := by
    obtain ⟨d, hd⟩ := hDne
    exact ⟨T.symm d, by simpa using hd, mem_univ _⟩
  have hEne' : (T ⁻¹' E ∩ univ).Nonempty := by
    obtain ⟨e, he⟩ := hEne
    exact ⟨T.symm e, by simpa using he, mem_univ _⟩
  have hnot := hp₀ _ _ hD' hE' hDne' hEne'
  have hns : ∀ A : Set X, IsOpen A → (A ∩ univ).Nonempty → ¬ (A ∩ univ ⊆ {p₀}) := by
    intro A hA hAne hsub
    have h1 : (A ∩ univ).Nontrivial := isOpen_nontrivial_of_nonempty (hA.inter isOpen_univ) hAne
    obtain ⟨u, hu, v, hv, huv⟩ := h1
    exact huv ((mem_singleton_iff.mp (hsub hu)).trans (mem_singleton_iff.mp (hsub hv)).symm)
  unfold HPC.Plane.Cuts at hnot
  push_neg at hnot
  obtain ⟨K, hK, -, hKD, hKE, hKp⟩ := hnot ⟨univ, ⟨isCompact_univ, isConnected_univ⟩,
    subset_univ _, by simpa using hDne', by simpa using hEne'⟩ (hns _ hD' hDne')
    (hns _ hE' hEne')
  refine ⟨T '' K, isContinuum_image_homeomorph T hK, ?_, ?_, ?_⟩
  · rintro ⟨k, hk, hkp⟩
    rw [← hT] at hkp
    exact (eq_empty_iff_forall_notMem.mp hKp) k ⟨hk, mem_singleton_iff.mpr (T.injective hkp)⟩
  · obtain ⟨k, hk, hkD, -⟩ := hKD
    exact ⟨T k, mem_image_of_mem _ hk, hkD⟩
  · obtain ⟨k, hk, hkE, -⟩ := hKE
    exact ⟨T k, mem_image_of_mem _ hk, hkE⟩

/-- **Claim (5), continuum form.** Two points of `U_p` lie in a continuum missing `p`. -/
theorem exists_continuum_of_mem_aposSet [Nontrivial X] (hX : IsHomogeneous X) {p a b : X}
    (ha : a ∈ aposSet p) (hb : b ∈ aposSet p) :
    ∃ K : Set X, Fold.Q78.IsContinuum K ∧ a ∈ K ∧ b ∈ K ∧ p ∉ K := by
  rw [aposSet_eq] at ha hb
  obtain ⟨A, V, hA, hV, haV, hVA, hpA⟩ := ha
  obtain ⟨B, W, hB, hW, hbW, hWB, hpB⟩ := hb
  obtain ⟨K, hK, hpK, ⟨u, huK, huV⟩, ⟨v, hvK, hvW⟩⟩ :=
    exists_continuum_meets_of_open hX p hV hW ⟨a, haV⟩ ⟨b, hbW⟩
  refine ⟨A ∪ K ∪ B, ⟨(hA.1.union hK.1).union hB.1, ?_⟩, Or.inl (Or.inl (hVA haV)),
    Or.inr (hWB hbW), ?_⟩
  · exact IsConnected.union ⟨v, Or.inr hvK, hWB hvW⟩
      (IsConnected.union ⟨u, hVA huV, huK⟩ hA.2 hK.2) hB.2
  · rintro ((h | h) | h)
    · exact hpA h
    · exact hpK h
    · exact hpB h

omit [CompactSpace X] [ConnectedSpace X] in
/-- Homeomorphisms preserve `CutsFrom`, with the set moved. -/
theorem CutsFrom.image (T : X ≃ₜ X) {p o : X} {S : Set X} (h : CutsFrom p o S) :
    CutsFrom (T p) (T o) (T '' S) := by
  refine ⟨fun e => h.1 (T.injective e), fun K hK hoK hKS => ?_⟩
  obtain ⟨_, hk, ⟨s, hs, rfl⟩⟩ := hKS
  have := h.2 (T.symm '' K) (isContinuum_image_homeomorph T.symm hK) ⟨T o, hoK, by simp⟩
    ⟨s, ⟨T s, hk, by simp⟩, hs⟩
  obtain ⟨w, hw, hwp⟩ := this
  rw [← hwp, T.apply_symm_apply]
  exact hw

/-! ### Jones's claims (1)–(12) -/

omit [CompactSpace X] [ConnectedSpace X] in
/-- **(1)** If no element `L_x` is degenerate, `M` is totally nonaposyndetic. (With homogeneity,
"no `L_x` degenerate" is "`M` not aposyndetic".) -/
theorem jones55_claim1 (hX : IsHomogeneous X) (hna : ¬ IsAposyndetic X) :
    TotallyNonAposyndetic X := by
  intro x hx
  unfold IsAposyndetic at hna
  push_neg at hna
  obtain ⟨a, b, hab, hn⟩ := hna
  obtain ⟨T, hT⟩ := hX a x
  refine hn ?_
  have := hx (T b) (fun e => hab (T.injective (e.trans hT.symm)).symm)
  rw [← hT] at this
  exact (aposAt_homeomorph_iff T).mp this

/-- **(2)** Every point of `M` is a cut point (footnote 3: a weak cut point, `IsWeakCutPoint`):
Jones 1948 p. 409 Corollary and homogeneity. -/
theorem jones55_claim2 (hX : IsHomogeneous X) (hna : ¬ IsAposyndetic X) (p : X) :
    IsWeakCutPoint p := by
  obtain ⟨p₀, a, b, hcut⟩ := totallyNonApos_exists_weakCutPoint (jones55_claim1 hX hna)
  obtain ⟨T, hT⟩ := hX p₀ p
  exact ⟨T a, T b, hT ▸ hcut.image T⟩

/-- **(3)** No point of `M` cuts two (rel.) open subsets of `M` from each other. -/
theorem jones55_claim3 [Nontrivial X] (hX : IsHomogeneous X) (p : X) {D E : Set X}
    (hD : IsOpen D) (hE : IsOpen E) (hDne : D.Nonempty) (hEne : E.Nonempty) :
    ∃ K : Set X, Fold.Q78.IsContinuum K ∧ p ∉ K ∧ (K ∩ D).Nonempty ∧ (K ∩ E).Nonempty :=
  exists_continuum_meets_of_open hX p hD hE hDne hEne

/-- A decomposable continuum is nondegenerate. -/
theorem nontrivial_of_isDecomposableSpace (hd : IsDecomposableSpace X) : Nontrivial X := by
  obtain ⟨x, y, hxy, -⟩ := theorem8.mp hd
  exact ⟨⟨x, y, hxy⟩⟩

/-- In a decomposable homogeneous continuum each `U_p` is nonempty. -/
theorem aposSet_nonempty (hX : IsHomogeneous X) (hd : IsDecomposableSpace X) (p : X) :
    (aposSet p).Nonempty := by
  obtain ⟨x, y, -, hxy⟩ := theorem8.mp hd
  obtain ⟨T, hT⟩ := hX y p
  refine ⟨T x, ?_⟩
  rw [aposSet_eq, ← hT]
  exact hxy.image T

/-- **(4)** For each `p`, `U_p` is a nondegenerate (rel.) open subset of `M`. -/
theorem jones55_claim4 (hX : IsHomogeneous X) (hd : IsDecomposableSpace X) (p : X) :
    IsOpen (aposSet p) ∧ (aposSet p).Nontrivial := by
  haveI := nontrivial_of_isDecomposableSpace hd
  exact ⟨isOpen_aposSet p,
    isOpen_nontrivial_of_nonempty (isOpen_aposSet p) (aposSet_nonempty hX hd p)⟩

/-- **(5)** `p` does not cut any two points of `U_p` from each other. -/
theorem jones55_claim5 [Nontrivial X] (hX : IsHomogeneous X) {p a b : X} (ha : a ∈ aposSet p)
    (hb : b ∈ aposSet p) : ¬ CutsPts p a b := by
  intro hc
  obtain ⟨K, hK, haK, hbK, hpK⟩ := exists_continuum_of_mem_aposSet hX ha hb
  exact hpK (hc.2.2.2 K hK haK hbK)

/-- If `p` cuts `o` from one point of `U_p`, it cuts `o` from all of `U_p`. -/
theorem cutsFrom_of_cutsPts [Nontrivial X] (hX : IsHomogeneous X) {p o z : X}
    (hz : z ∈ aposSet p) (hc : CutsPts p o z) : CutsFrom p o (aposSet p) := by
  refine ⟨hc.1.symm, fun K hK hoK ⟨u, huK, hu⟩ => ?_⟩
  by_contra hpK
  obtain ⟨E, hE, huE, hzE, hpE⟩ := exists_continuum_of_mem_aposSet hX hu hz
  refine hpK ?_
  have h := hc.2.2.2 (K ∪ E) ⟨hK.1.union hE.1, IsConnected.union ⟨u, huK, huE⟩ hK.2 hE.2⟩
    (Or.inl hoK) (Or.inr hzE)
  exact h.elim id (fun h' => absurd h' hpE)

/-- **(6)** Each `p` cuts some point `o` from every point of `U_p`. -/
theorem jones55_claim6 (hX : IsHomogeneous X) (hd : IsDecomposableSpace X)
    (hna : ¬ IsAposyndetic X) (p : X) : ∃ o, CutsFrom p o (aposSet p) := by
  haveI := nontrivial_of_isDecomposableSpace hd
  obtain ⟨a, b, hc⟩ := jones55_claim2 hX hna p
  by_contra hno
  push_neg at hno
  -- neither `a` nor `b` is cut from `U_p` by `p`
  have hcont : ∀ w, ¬ CutsFrom p w (aposSet p) → w ≠ p →
      ∃ K : Set X, Fold.Q78.IsContinuum K ∧ w ∈ K ∧ (K ∩ aposSet p).Nonempty ∧ p ∉ K := by
    intro w hw hwp
    unfold CutsFrom at hw
    push_neg at hw
    obtain ⟨K, hK, hwK, hKU, hpK⟩ := hw (Ne.symm hwp)
    exact ⟨K, hK, hwK, hKU, hpK⟩
  obtain ⟨A, hA, haA, ⟨u, huA, hu⟩, hpA⟩ := hcont a (hno a) hc.1
  obtain ⟨B, hB, hbB, ⟨v, hvB, hv⟩, hpB⟩ := hcont b (hno b) hc.2.1
  obtain ⟨E, hE, huE, hvE, hpE⟩ := exists_continuum_of_mem_aposSet hX hu hv
  have hK : Fold.Q78.IsContinuum (A ∪ E ∪ B) :=
    ⟨(hA.1.union hE.1).union hB.1, IsConnected.union ⟨v, Or.inr hvE, hvB⟩
      (IsConnected.union ⟨u, huA, huE⟩ hA.2 hE.2) hB.2⟩
  have := hc.2.2.2 _ hK (Or.inl (Or.inl haA)) (Or.inr hbB)
  rcases this with (h | h) | h
  · exact hpA h
  · exact hpE h
  · exact hpB h

/-- **(7)** For each `o` there is `p` cutting `o` from every point of `U_p`. -/
theorem jones55_claim7 (hX : IsHomogeneous X) (hd : IsDecomposableSpace X)
    (hna : ¬ IsAposyndetic X) (o : X) : ∃ p, CutsFrom p o (aposSet p) := by
  obtain ⟨o₀, hc⟩ := jones55_claim6 hX hd hna o
  obtain ⟨T, hT⟩ := hX o₀ o
  refine ⟨T o, ?_⟩
  have := hc.image T
  rwa [← aposSet_homeomorph, hT] at this

omit [ConnectedSpace X] in
/-- **(8)** If `p` cuts `o` from every point of `U_p`, then `U_p = U_o` (every point of `U_p` is a
point of `U_o`, then the Lemma of Jones 1951). -/
theorem jones55_claim8 (hX : IsHomogeneous X) {p o : X} (hc : CutsFrom p o (aposSet p)) :
    aposSet p = aposSet o := by
  have hsub : aposSet p ⊆ aposSet o := by
    intro z hz
    have hz' := hz
    rw [aposSet_eq] at hz ⊢
    obtain ⟨K, V, hK, hV, hzV, hVK, hpK⟩ := hz
    refine ⟨K, V, hK, hV, hzV, hVK, fun hoK => hpK (hc.2 K hK hoK ⟨z, hVK hzV, hz'⟩)⟩
  by_contra hne
  exact jones51_lemma hX (ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)

/-- **(9)** With `H = {x | U_x = U}`: a point `w` cut from a point of `U` by a point of `H` is in
`H`. -/
theorem jones55_claim9 [Nontrivial X] (hX : IsHomogeneous X) {U : Set X} {x w z : X}
    (hx : aposSet x = U) (hz : z ∈ U) (hc : CutsPts x w z) : aposSet w = U := by
  rw [← hx] at hz ⊢
  exact (jones55_claim8 hX (cutsFrom_of_cutsPts hX hz hc)).symm ▸ rfl

omit [ConnectedSpace X] in
/-- **(10)** `H = {x | U_x = U}` is closed. -/
theorem jones55_claim10 (hX : IsHomogeneous X) (U : Set X) : IsClosed {x : X | aposSet x = U} := by
  refine isClosed_iff_clusterPt.mpr fun y hy => ?_
  -- `U_y ⊆ U`
  have hsub : aposSet y ⊆ U := by
    intro z hz
    rw [aposSet_eq] at hz
    have hopen : IsOpen {w : X | AposAt z w} := isOpen_aposAt_right z
    obtain ⟨w, hwz, hwH⟩ := (clusterPt_principal_iff.mp hy) _ (hopen.mem_nhds hz)
    rw [← show aposSet w = U from hwH, aposSet_eq]
    exact hwz
  rcases (eq_or_ne U ∅) with hU | hU
  · show aposSet y = U
    rw [hU]
    exact subset_empty_iff.mp (hU ▸ hsub)
  · obtain ⟨w, -, hwH⟩ := (clusterPt_principal_iff.mp hy) _ univ_mem
    have hwH : aposSet w = U := hwH
    by_contra hne
    exact jones51_lemma hX (ssubset_iff_subset_ne.mpr ⟨hwH ▸ hsub, fun he => hne (he.trans hwH)⟩)

/-- Jones's `N_o` (p. 737): `o` together with the points `x` of `H` that cut `o` from `U`. -/
def Nset (U : Set X) (o : X) : Set X := insert o {x | aposSet x = U ∧ CutsFrom x o U}

omit [ConnectedSpace X] in
/-- **(11)** If a point `p` of `H` cuts a point `o` of `H` from `U`, then `o` cuts `p` from `U`.

*Proof change:* Jones builds an uncountable well-ordered decreasing sequence of distinct closed sets
`N_{o_i}`. Here (11) is read off from Theorem 1 (c) (`Lset_subset_of_meets`): `p ∈ L_o`, and a
continuum through `p` meeting `U = M − L_o` contains `L_o ∋ o`. -/
theorem jones55_claim11 (hX : IsHomogeneous X) {U : Set X} {o p : X} (ho : aposSet o = U)
    (hp : aposSet p = U) (hc : CutsFrom p o U) : CutsFrom o p U := by
  refine ⟨hc.1.symm, fun K hK hpK hKU => ?_⟩
  have hpL : p ∈ Lset o := by
    rw [Lset_eq_compl, mem_compl_iff, ho, ← hp]
    exact notMem_aposSet_self p
  have hsub := Lset_subset_of_meets hX hK ⟨p, hpK, hpL⟩ (by
    obtain ⟨u, huK, huU⟩ := hKU
    refine ⟨u, huK, ?_⟩
    rw [Lset_eq_compl, notMem_compl_iff, ho]
    exact huU)
  exact hsub (mem_Lset_self o)

/-- `L_o` has empty interior in a decomposable homogeneous continuum. -/
theorem interior_Lset_eq_empty (hX : IsHomogeneous X) (hd : IsDecomposableSpace X) (o : X) :
    interior (Lset o) = ∅ := by
  haveI := nontrivial_of_isDecomposableSpace hd
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hne
  obtain ⟨w, hw, hwx⟩ := (isOpen_nontrivial_of_nonempty isOpen_interior ⟨x, hx⟩).exists_ne x
  have hD : IsOpen (interior (Lset o) \ {x}) := isOpen_interior.sdiff isClosed_singleton
  obtain ⟨K, hK, hxK, ⟨d, hdK, hdD⟩, ⟨u, huK, huU⟩⟩ :=
    exists_continuum_meets_of_open hX x hD (isOpen_aposSet o) ⟨w, hw, hwx⟩
      (aposSet_nonempty hX hd o)
  have hsub := Lset_subset_of_meets hX hK ⟨d, hdK, interior_subset hdD.1⟩
    ⟨u, huK, by rw [Lset_eq_compl, notMem_compl_iff]; exact huU⟩
  exact hxK (hsub (interior_subset hx))

/-- **(12)** `U` is dense in `M` (for `U = U_o`).

*Proof change:* Jones argues from (3), (10), (11) and Theorem 6 of 1948. Here: `M − U_o = L_o`, and
`L_o` has no interior, because a point `x` of an open subset `D` of `L_o` would cut the open sets
`D − x` and `U_o` from each other (Theorem 1 (c)), contrary to (3). -/
theorem jones55_claim12 (hX : IsHomogeneous X) (hd : IsDecomposableSpace X) (o : X) :
    Dense (aposSet o) := by
  rw [← Lset_compl, ← interior_eq_empty_iff_dense_compl]
  exact interior_Lset_eq_empty hX hd o

/-! ### `N_o = L_o` and the properties (a)–(f) of p. 739 -/

omit [ConnectedSpace X] in
/-- **`N_o = M − U_o = L_o`** (p. 738: "It follows from the preceding paragraph that for each
point `o` of `M`, `N_o = M − U_o`"). Proved from (b) and (c); Jones's case argument with `d(q)`,
`E_n`, `M₀` is not used. -/
theorem Nset_eq_Lset (hX : IsHomogeneous X) (o : X) : Nset (aposSet o) o = Lset o := by
  ext x
  by_cases hxo : x = o
  · subst hxo
    exact ⟨fun _ => mem_Lset_self x, fun _ => mem_insert x _⟩
  constructor
  · rintro (h | ⟨hx, -⟩)
    · exact absurd h hxo
    · rw [Lset_eq_compl, mem_compl_iff, ← hx]
      exact notMem_aposSet_self x
  · intro hx
    refine Or.inr ⟨?_, hxo, fun K hK hoK hKU => ?_⟩
    · rw [← Lset_compl, ← Lset_compl, (mem_Lset_iff_Lset_eq hX).mp hx]
    · obtain ⟨u, huK, huU⟩ := hKU
      exact Lset_subset_of_meets hX hK ⟨o, hoK, mem_Lset_self o⟩
        ⟨u, huK, by rw [Lset_eq_compl, notMem_compl_iff]; exact huU⟩ hx

omit [MetricSpace X] [CompactSpace X] [ConnectedSpace X] in
theorem eq_insert_of_forall_ne {α : Type*} {o : α} {L S : Set α} (ho : o ∈ L)
    (h : ∀ x, x ≠ o → (x ∈ L ↔ x ∈ S)) : L = insert o S := by
  ext x
  by_cases hxo : x = o
  · subst hxo
    exact ⟨fun _ => mem_insert x _, fun _ => ho⟩
  · rw [h x hxo, mem_insert_iff, or_iff_right hxo]

/-- **The characterization of `N_o` without `H`** (p. 737): `N_o` is `o` together with the points
`x` that cut `o` from `U_o`; and also `o` together with the points `x` that `o` cuts from `U_o`.
(Jones derives the first from (4) and (12), as here, and the second from (11).) -/
theorem Nset_characterization (hX : IsHomogeneous X) (hd : IsDecomposableSpace X) (o : X) :
    Nset (aposSet o) o = insert o {x | CutsFrom x o (aposSet o)} ∧
      Nset (aposSet o) o = insert o {x | CutsFrom o x (aposSet o)} := by
  haveI := nontrivial_of_isDecomposableSpace hd
  rw [Nset_eq_Lset hX]
  have hnotU : ∀ x : X, x ∉ aposSet x := notMem_aposSet_self
  refine ⟨eq_insert_of_forall_ne (mem_Lset_self o) fun x hxo => ⟨fun hx => ?_, fun hc => ?_⟩,
    eq_insert_of_forall_ne (mem_Lset_self o) fun x hxo => ⟨fun hx => ?_, fun hc => ?_⟩⟩
  · refine ⟨hxo, fun K hK hoK ⟨u, huK, huU⟩ => ?_⟩
    exact Lset_subset_of_meets hX hK ⟨o, hoK, mem_Lset_self o⟩
      ⟨u, huK, by rw [Lset_eq_compl, notMem_compl_iff]; exact huU⟩ hx
  · obtain ⟨z, hzx, hzo⟩ := (jones55_claim12 hX hd o).inter_open_nonempty _ (isOpen_aposSet x)
      (aposSet_nonempty hX hd x)
    have hcut : CutsPts x o z := ⟨Ne.symm hxo, fun e => hnotU x (e ▸ hzx),
      fun e => hnotU o (e ▸ hzo), fun K hK hoK hzK => hc.2 K hK hoK ⟨z, hzK, hzo⟩⟩
    have he := jones55_claim8 hX (cutsFrom_of_cutsPts hX hzx hcut)
    rw [Lset_eq_compl, mem_compl_iff, ← he]
    exact hnotU x
  · refine ⟨Ne.symm hxo, fun K hK hxK ⟨u, huK, huU⟩ => ?_⟩
    exact Lset_subset_of_meets hX hK ⟨x, hxK, hx⟩
      ⟨u, huK, by rw [Lset_eq_compl, notMem_compl_iff]; exact huU⟩ (mem_Lset_self o)
  · by_contra hx
    have hxU : x ∈ aposSet o := by rwa [Lset_eq_compl, notMem_compl_iff] at hx
    exact hxo (mem_singleton_iff.mp
      (hc.2 {x} ⟨isCompact_singleton, isConnected_singleton⟩ rfl ⟨x, rfl, hxU⟩)).symm

omit [ConnectedSpace X] in
/-- **Property (a)** (p. 739): for `g = L_o`, `N_o = g`. -/
theorem jones55_prop_a (hX : IsHomogeneous X) (o : X) : Nset (aposSet o) o = Lset o :=
  Nset_eq_Lset hX o

omit [ConnectedSpace X] in
/-- **Property (b)** (p. 739): for each point `x` of `g = L_o`, `U_x = U(g)`. -/
theorem jones55_prop_b (hX : IsHomogeneous X) {o x : X} (hx : x ∈ Lset o) :
    aposSet x = aposSet o := by
  rw [← Lset_compl, ← Lset_compl, (mem_Lset_iff_Lset_eq hX).mp hx]

omit [ConnectedSpace X] in
/-- **Property (c)** (p. 739): for each point `x` of `g = L_o`, `N_x = g`. -/
theorem jones55_prop_c (hX : IsHomogeneous X) {o x : X} (hx : x ∈ Lset o) :
    Nset (aposSet x) x = Lset o := by
  rw [Nset_eq_Lset hX, (mem_Lset_iff_Lset_eq hX).mp hx]

omit [ConnectedSpace X] in
/-- **Property (d)** (p. 739): if `x ≠ y` are points of `g = L_o`, `x` cuts `y` from `U(g)`. -/
theorem jones55_prop_d (hX : IsHomogeneous X) {o x y : X} (hx : x ∈ Lset o) (hy : y ∈ Lset o)
    (hxy : x ≠ y) : CutsFrom x y (aposSet o) := by
  refine ⟨hxy, fun K hK hyK ⟨u, huK, huU⟩ => ?_⟩
  exact Lset_subset_of_meets hX hK ⟨y, hyK, hy⟩
    ⟨u, huK, by rw [Lset_eq_compl, notMem_compl_iff]; exact huU⟩ hx

omit [CompactSpace X] [ConnectedSpace X] in
/-- **Property (e)** (p. 739): `M − g = U(g)`. -/
theorem jones55_prop_e (o : X) : (Lset o)ᶜ = aposSet o := Lset_compl o

omit [ConnectedSpace X] in
/-- **Property (f)** (p. 739): a subcontinuum meeting `g` and `U(g)` contains `g`. -/
theorem jones55_prop_f (hX : IsHomogeneous X) {o : X} {K : Set X} (hK : Fold.Q78.IsContinuum K)
    (h1 : (K ∩ Lset o).Nonempty) (h2 : (K ∩ aposSet o).Nonempty) : Lset o ⊆ K := by
  refine Lset_subset_of_meets hX hK h1 ?_
  obtain ⟨u, huK, huU⟩ := h2
  exact ⟨u, huK, by rw [Lset_eq_compl, notMem_compl_iff]; exact huU⟩

end Jones55

end HPC.Jones
