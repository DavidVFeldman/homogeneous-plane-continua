import HPC.Moore.M25B5

/-!
# Batch 146, items D, E, G: Moore 1925, Theorems 9, 10 and 12 (pp. 421–422)

* **Theorem 9** (no arc of elements separates `G`). Moore gives only "an argument largely similar
  to that used in the proof of Lemma 8" of P.C.S., "with the help of Theorems 2 and 6". The
  argument formalized: every complementary domain of the arc `K` has unbounded point set, so all
  of them are "the" unbounded one (`m25_unbounded_unique`) and `G − K` is connected. If the domain
  `D` of `x` were bounded, let `E` be the unbounded complementary domain of `∂D` and `K' = ∂E`
  (the outer boundary of `D`). By Theorem 2, `K'` is a continuum and `K' − r` is connected for every
  `r ∈ K'`. `K'` has two elements at least: it is nonempty and not a single element, since `D` and
  `E` are disjoint and `E` would otherwise be all of `G − K'` (`G − r` is connected). As
  `K' ⊆ ∂D ⊆ K`, Theorem 6 makes `K'` an arc, whose interior elements disconnect it.
  The case of an unbounded complementary domain of `K` with `G − K` still disconnected is excluded
  because the argument shows that *no* complementary domain is bounded, and two unbounded ones
  coincide.
* **Theorem 10**: `circle_char` (Moore 1920, Theorem 4), in the compact metrizable `J`.
* **Theorem 12**: Moore's proof, as printed.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

variable {r : Setoid Pt}

section M25B

variable (hG : MooreDecomp r)
include hG

/-- The complement of an element is connected. -/
theorem isConnected_compl_singleton_quot (p : Quotient r) : IsConnected ({p}ᶜ : Set (Quotient r)) := by
  obtain ⟨z, rfl⟩ := Quotient.mk_surjective p
  have h := hG.nonsep z
  unfold SeparatesPlane at h
  rw [not_not, ← ptsOf_singleton] at h
  rw [← image_ptsOf ({Quotient.mk r z}ᶜ : Set (Quotient r)), ptsOf_compl]
  exact h.image _ continuous_mk.continuousOn

/-- A compact set of elements has bounded point set. -/
theorem isBounded_ptsOf_of_isCompact {H : Set (Quotient r)} (hH : IsCompact H) :
    Bornology.IsBounded (ptsOf r H) :=
  ((isProperMap_mk hG).isCompact_preimage hH).isBounded

/-- The closure of a set of elements with bounded point set has bounded point set. -/
theorem isBounded_ptsOf_closure {D : Set (Quotient r)} (hD : Bornology.IsBounded (ptsOf r D)) :
    Bornology.IsBounded (ptsOf r (closure D)) := by
  have hc : IsCompact (Quotient.mk r '' closure (ptsOf r D)) :=
    (hD.isCompact_closure).image continuous_mk
  refine (isBounded_ptsOf_of_isCompact hG hc).subset (ptsOf_mono ?_)
  refine closure_minimal ?_ (isClosedMap_mk_plane hG _ isClosed_closure)
  intro q hq
  obtain ⟨y, hy⟩ := ptsOf_singleton_nonempty q
  exact ⟨y, subset_closure (ptsOf_mono (singleton_subset_iff.2 hq) hy), hy⟩

omit hG in
/-- A bounded set of elements is not everything. -/
theorem ne_univ_of_isBounded {D : Set (Quotient r)} (hD : Bornology.IsBounded (ptsOf r D)) :
    D ≠ univ := by
  rintro rfl
  exact NormedSpace.unbounded_univ ℝ Pt hD

/-- The point set of the frontier of `D` is bounded if that of `D` is. -/
theorem isBounded_ptsOf_frontier {D : Set (Quotient r)} (hD : Bornology.IsBounded (ptsOf r D)) :
    Bornology.IsBounded (ptsOf r (frontier D)) :=
  (isBounded_ptsOf_closure hG hD).subset (ptsOf_mono frontier_subset_closure)

/-- **Theorem 9** (p. 421). If `pq` is a simple continuous arc of elements, then `G − pq` is
connected. ("With the help of Theorems 2 and 6 the following theorem may be established by an
argument largely similar to that used in the proof of Lemma 8 of" P.C.S.) -/
theorem m25_theorem9 {p q : Quotient r} {K : Set (Quotient r)} (hK : IsArcElt p q K) :
    IsConnected Kᶜ := by
  haveI := locallyConnectedSpace_quot hG
  haveI := t1Space_quot hG
  haveI := quotient_metrizable_plane hG
  have hKcl : IsClosed K := hK.2.1
  have hKb : Bornology.IsBounded (ptsOf r K) := hK.2.2.2.1
  obtain ⟨y0, hy0, hy0b, hy0u⟩ := m25_unbounded_unique hKb
  -- every complementary domain of `K` is unbounded
  have key : ∀ x ∉ K, ¬ Bornology.IsBounded (ptsOf r (connectedComponentIn Kᶜ x)) := by
    intro x hx hDb
    set D := connectedComponentIn Kᶜ x with hDdef
    have hDo : IsOpen D := hKcl.isOpen_compl.connectedComponentIn
    have hxD : x ∈ D := mem_connectedComponentIn hx
    have hDK : D ⊆ Kᶜ := connectedComponentIn_subset _ _
    have hfrD : frontier D ⊆ K := fun z hz => by
      simpa using frontier_connectedComponentIn_subset hKcl.isOpen_compl x hz
    have hfrDb : Bornology.IsBounded (ptsOf r (frontier D)) := hKb.subset (ptsOf_mono hfrD)
    obtain ⟨y, hy, hyb, -⟩ := m25_unbounded_unique hfrDb
    set E := connectedComponentIn (frontier D)ᶜ y with hEdef
    have hEo : IsOpen E := isClosed_frontier.isOpen_compl.connectedComponentIn
    have hyE : y ∈ E := mem_connectedComponentIn hy
    have hEc : IsConnected E := isConnected_connectedComponentIn_iff.2 hy
    have hEfD : E ⊆ (frontier D)ᶜ := connectedComponentIn_subset _ _
    set K' := frontier E with hK'def
    have hK'D : K' ⊆ frontier D := fun z hz => by
      simpa using frontier_connectedComponentIn_subset isClosed_frontier.isOpen_compl y hz
    have hK'K : K' ⊆ K := hK'D.trans hfrD
    -- `D` and `E` are disjoint
    have hDE : Disjoint D E := by
      rw [disjoint_left]
      intro z hzD hzE
      have hsub : E ⊆ D := subset_of_preconnected_of_disjoint_frontier hEc.isPreconnected hDo
        ⟨z, hzE, hzD⟩ (disjoint_left.2 fun w hwE hwf => hEfD hwE hwf)
      exact hyb (hDb.subset (ptsOf_mono hsub))
    -- `K'` has an element
    have hK'ne : K'.Nonempty := by
      rw [hK'def, nonempty_frontier_iff]
      refine ⟨⟨y, hyE⟩, fun hE => ?_⟩
      exact disjoint_left.1 hDE hxD (hE ▸ mem_univ x)
    obtain ⟨p', hp'⟩ := hK'ne
    have h2 := m25_theorem2 hG hKcl hK.2.2.1 hKb hx hDb hy hyb hp'
    -- `K'` has two elements
    have hK'n : K'.Nontrivial := by
      by_contra hsing
      rw [not_nontrivial_iff] at hsing
      have hK'eq : K' = {p'} := hsing.eq_singleton_of_mem hp'
      have hEK' : E ⊆ {p'}ᶜ := fun z hzE hz => by
        rw [← hK'eq] at hz; rw [hK'def, hEo.frontier_eq] at hz; exact hz.2 hzE
      have hsub : {p'}ᶜ ⊆ E := subset_of_preconnected_of_disjoint_frontier
        (isConnected_compl_singleton_quot hG p').isPreconnected hEo
        ⟨y, hEK' hyE, hyE⟩ (by rw [← hK'def, hK'eq]; exact disjoint_compl_left)
      have hxp' : x ≠ p' := fun e => hDK hxD (hK'K (e ▸ hp'))
      exact disjoint_left.1 hDE hxD (hsub hxp')
    -- `K'` is an arc (Theorem 6), and its interior elements disconnect it
    obtain ⟨a, b, hab⟩ := m25_theorem6 hG hK hK'K h2.1 h2.2.1 hK'n
    obtain ⟨f, hf, hrange, hf0, hf1⟩ := hab.isCutArc.exists_embedding
    set u : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
    have hu0 : u ≠ 0 := fun e => by
      have := congrArg Subtype.val e; norm_num [u] at this
    have hu1 : u ≠ 1 := fun e => by
      have := congrArg Subtype.val e; norm_num [u] at this
    have hfu : f u ∈ K' := hrange ▸ mem_range_self u
    exact hab.2.2.2.2.2.2 (f u) hfu (fun e => hu0 (hf.injective (e.trans hf0.symm)))
      (fun e => hu1 (hf.injective (e.trans hf1.symm)))
      (m25_theorem2 hG hKcl hK.2.2.1 hKb hx hDb hy hyb hfu).2.2
  -- hence `G − K` is the unbounded complementary domain
  have heq : Kᶜ = connectedComponentIn Kᶜ y0 := by
    apply subset_antisymm _ (connectedComponentIn_subset _ _)
    intro z hz
    rw [← hy0u z hz (key z hz)]
    exact mem_connectedComponentIn hz
  rw [heq]
  exact isConnected_connectedComponentIn_iff.2 hy0

/-- **Theorem 10** (p. 421), for the corrected simple closed curve. ("In view of results established
above Theorem 10 is a consequence of Theorem 4 of" Moore 1920.) -/
theorem m25_theorem10 {J : Set (Quotient r)} (hJ : IsSCCElt J) {p q : Quotient r} (hp : p ∈ J)
    (hq : q ∈ J) (hpq : p ≠ q) :
    ∃ a b, IsArcElt p q a ∧ IsArcElt p q b ∧ a ∪ b = J ∧ a ∩ b = {p, q} := by
  haveI := quotient_metrizable_plane hG
  obtain ⟨hJcl, hJc, -, hJb, h2⟩ := hJ
  obtain ⟨a, b, ha, hb, hab, hab'⟩ :=
    circle_char (isCompact_of_isClosed_bounded hJcl hJb) hJc h2 hp hq hpq
  have haJ : a ⊆ J := hab ▸ subset_union_left
  have hbJ : b ⊆ J := hab ▸ subset_union_right
  exact ⟨a, b, ha.isArcElt ha.2.1.isClosed (hJb.subset (ptsOf_mono haJ)),
    hb.isArcElt hb.2.1.isClosed (hJb.subset (ptsOf_mono hbJ)), hab, hab'⟩

/-- **Theorem 12** (p. 422). If `D₁` and `D₂` are bounded domains of elements, `D₁` has a connected
boundary, and the boundary of `D₂` is a subset of `D₁`, then `D₂ ⊆ D₁`. -/
theorem m25_theorem12 {D₁ D₂ : Set (Quotient r)} (h₁ : IsOpen D₁ ∧ IsConnected D₁)
    (h₂ : IsOpen D₂ ∧ IsConnected D₂) (hb₁ : Bornology.IsBounded (ptsOf r D₁))
    (hb₂ : Bornology.IsBounded (ptsOf r D₂)) (hB₁ : IsConnected (frontier D₁))
    (hB₂ : frontier D₂ ⊆ D₁) : D₂ ⊆ D₁ := by
  haveI := locallyConnectedSpace_quot hG
  -- "Since `D₂` is bounded it has at least one boundary element"
  obtain ⟨b, hb⟩ : (frontier D₂).Nonempty :=
    nonempty_frontier_iff.2 ⟨h₂.2.nonempty, ne_univ_of_isBounded hb₂⟩
  -- "Hence `D₁` contains at least one element of `D₂`"
  have hD12 : (D₂ ∩ D₁).Nonempty := by
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 (frontier_subset_closure hb) D₁ h₁.1 (hB₂ hb)
    exact ⟨z, hz2, hz1⟩
  by_contra hnot
  -- "It follows that `D₂` contains an element of `B₁`"
  have hB₁D₂ : (frontier D₁ ∩ D₂).Nonempty := by
    by_contra hemp
    exact hnot (subset_of_preconnected_of_disjoint_frontier h₂.2.isPreconnected h₁.1 hD12
      (disjoint_left.2 fun z hzD hzf => hemp ⟨z, hzf, hzD⟩))
  -- "But `B₁` is connected and contains no point of the boundary of `D₂`. Hence `B₁ ⊆ D₂`"
  have hB₁sub : frontier D₁ ⊆ D₂ := subset_of_preconnected_of_disjoint_frontier
    hB₁.isPreconnected h₂.1 hB₁D₂ (disjoint_left.2 fun z hz1 hz2 => by
      have := hB₂ hz2; rw [h₁.1.frontier_eq] at hz1; exact hz1.2 this)
  -- `E`, the unbounded complementary domain of `B₁`
  have hB₁b := isBounded_ptsOf_frontier hG hb₁
  obtain ⟨y, hy, hyb, -⟩ := m25_unbounded_unique hB₁b
  set E := connectedComponentIn (frontier D₁)ᶜ y with hEdef
  have hEo : IsOpen E := isClosed_frontier.isOpen_compl.connectedComponentIn
  have hEc : IsConnected E := isConnected_connectedComponentIn_iff.2 hy
  have hEB : E ⊆ (frontier D₁)ᶜ := connectedComponentIn_subset _ _
  have hfrE : frontier E ⊆ frontier D₁ := fun z hz => by
    simpa using frontier_connectedComponentIn_subset isClosed_frontier.isOpen_compl y hz
  -- "Thus `D₂` contains the boundary of `E`. Therefore `D₂` contains an element of `E`"
  obtain ⟨b', hb'⟩ : (frontier E).Nonempty := by
    refine nonempty_frontier_iff.2 ⟨⟨y, mem_connectedComponentIn hy⟩, fun hE => ?_⟩
    obtain ⟨w, hw⟩ := hB₁.nonempty
    exact hEB (hE ▸ mem_univ w) hw
  have hD2E : (E ∩ D₂).Nonempty := by
    obtain ⟨z, hz1, hz2⟩ :=
      mem_closure_iff.1 (frontier_subset_closure hb') D₂ h₂.1 (hB₁sub (hfrE hb'))
    exact ⟨z, hz2, hz1⟩
  -- `E` misses `D₁` (else `E ⊆ D₁` would be bounded), hence the boundary of `D₂`
  have hED1 : Disjoint E D₁ := by
    rw [disjoint_left]
    intro z hzE hzD
    have hsub : E ⊆ D₁ := subset_of_preconnected_of_disjoint_frontier hEc.isPreconnected h₁.1
      ⟨z, hzE, hzD⟩ (disjoint_left.2 fun w hwE hwf => hEB hwE hwf)
    exact hyb (hb₁.subset (ptsOf_mono hsub))
  -- "But `E` is connected and contains no point of the boundary of `D₂`. Hence `E ⊆ D₂`"
  have hsub : E ⊆ D₂ := subset_of_preconnected_of_disjoint_frontier hEc.isPreconnected h₂.1 hD2E
    (disjoint_left.2 fun z hzE hzf => disjoint_left.1 hED1 hzE (hB₂ hzf))
  exact hyb (hb₂.subset (ptsOf_mono hsub))

end M25B

end HPC.Moore
