import HPC.Moore.M25B9
import HPC.Moore.Mullikin

/-!
# Batch 146, item F: Moore 1925, Theorem 11 (pp. 421–422)

Moore's proof, for the corrected simple closed curve `J`:

* Theorem 10 gives arcs `a`, `b` from `p` to `q` with `a ∪ b = J`, `a ∩ b = {p, q}`; by Theorem 9
  neither separates `G`, so neither `ā` nor `b̄` separates `S` (`not_separatesPlane_ptsOf`).
* Mullikin's theorem (`mullikin_theorem5`, with `K₁ = p̄`, `K₂ = q̄`) splits `S − J̄` into two
  domains `D₁`, `D₂`. "Clearly `I` and `E` are domains of elements of `G` and `I + E = G − J`": each
  element off `J̄` is connected, so lies in `D₁` or in `D₂` (`ptsOf_image_eq_of_split`).
* "It is easy to see that one of these domains is bounded and the other one is unbounded": two
  unbounded complementary domains coincide (`m25_unbounded_unique`), and two bounded ones would
  make the plane bounded.
* `J` is the boundary of each (`frontier_eq_of_scc`). Here Moore's step "It easily follows, with
  the help of Theorems 10 and 6, that `B` is a simple continuous arc" has a gap (ledger check 4):
  Theorem 6 needs `B` connected. The repair of the commission is used: if `x ∈ J − B`, then two
  arcs of `J` from `x` (Theorem 10) give elements `p₁`, `q₁` near `x` on either side such that the
  sub-arc `C` of `J` through `x` between them misses `B`; by Theorem 10 again and irreducibility, `C`
  is one of the two arcs of `J` from `p₁` to `q₁`, and the other one, `A`, contains `B` and misses
  `x`. Then `G − A = I ∪ (E ∪ (J − A))` with `I` and `(cl I)ᶜ` separating it, against Theorem 9.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

variable {r : Setoid Pt}

/-- In a set split into two disjoint open pieces, the component of a point of a preconnected piece
is that piece. -/
theorem connectedComponentIn_eq_of_split {X : Type*} [TopologicalSpace X] {S A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B) (hS : S = A ∪ B) (hAc : IsPreconnected A)
    {x : X} (hx : x ∈ A) : connectedComponentIn S x = A := by
  apply subset_antisymm
  · have hsub : connectedComponentIn S x ⊆ A ∪ B := hS ▸ connectedComponentIn_subset _ _
    rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_connectedComponentIn A B hA hB
      hsub (by rw [disjoint_iff_inter_eq_empty.1 hAB, inter_empty]) with h | h
    · exact h
    · exact absurd (h (mem_connectedComponentIn (hS ▸ Or.inl hx)))
        (disjoint_left.1 hAB hx)
  · exact hAc.subset_connectedComponentIn hx (hS ▸ subset_union_left)

section M25B

variable (hG : MooreDecomp r)
include hG

/-- A piece of a split of the complement of a saturated set into two disjoint open sets is
saturated. -/
theorem ptsOf_image_eq_of_split {J : Set (Quotient r)} {U V : Set Pt} (hUo : IsOpen U)
    (hVo : IsOpen V) (hUV : Disjoint U V) (hUVeq : U ∪ V = (ptsOf r J)ᶜ) :
    ptsOf r (Quotient.mk r '' U) = U := by
  apply subset_antisymm _ (fun z hz => ⟨z, hz, rfl⟩)
  rintro z ⟨w, hwU, hwz⟩
  have hel : elt r w ⊆ U ∪ V := by
    intro y hy
    rw [hUVeq]
    intro hyJ
    have hwJ : w ∈ (ptsOf r J)ᶜ := hUVeq ▸ Or.inl hwU
    apply hwJ
    show Quotient.mk r w ∈ J
    have : Quotient.mk r y = Quotient.mk r w := Quotient.sound hy
    rw [← this]; exact hyJ
  rcases isPreconnected_iff_subset_of_disjoint.1 (hG.connected w).isPreconnected U V hUo hVo hel
    (by rw [disjoint_iff_inter_eq_empty.1 hUV, inter_empty]) with h | h
  · exact h (Quotient.exact hwz.symm : r z w)
  · exact absurd (h (mem_elt_self w)) (disjoint_left.1 hUV hwU)

/-- **`J` is the boundary of each complementary domain** (the repaired step of Moore's proof). -/
theorem frontier_eq_of_scc {J : Set (Quotient r)} (hJ : IsSCCElt J) {I : Set (Quotient r)}
    (hIo : IsOpen I) (hIne : I.Nonempty) (hIJ : Disjoint I J) (hfr : frontier I ⊆ J) :
    frontier I = J := by
  haveI := quotient_metrizable_plane hG
  refine subset_antisymm hfr fun x hxJ => ?_
  by_contra hxB
  obtain ⟨q₀, hq₀J, hq₀x⟩ := hJ.2.2.1.exists_ne x
  obtain ⟨a₀, b₀, ha₀, hb₀, hab₀, hab₀'⟩ := m25_theorem10 hG hJ hxJ hq₀J hq₀x.symm
  obtain ⟨f, hf, hfr', hf0, hf1⟩ := ha₀.isCutArc.exists_embedding
  obtain ⟨g, hg, hgr', hg0, hg1⟩ := hb₀.isCutArc.exists_embedding
  have hsmall : ∀ {h : unitInterval → Quotient r}, Continuous h → h 0 = x →
      ∃ ε > 0, ∀ t : unitInterval, (t : ℝ) < ε → h t ∉ frontier I := by
    intro h hc h0
    have hmem : h ⁻¹' (frontier I)ᶜ ∈ 𝓝 (0 : unitInterval) :=
      hc.continuousAt.preimage_mem_nhds (isClosed_frontier.isOpen_compl.mem_nhds (by
        rw [mem_compl_iff, h0]; exact hxB))
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
    refine ⟨ε, hε, fun t ht => hball ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq]
    show |(t : ℝ) - 0| < ε
    rw [sub_zero, abs_of_nonneg t.2.1]
    exact ht
  obtain ⟨ε₁, hε₁, h₁⟩ := hsmall hf.continuous hf0
  obtain ⟨ε₂, hε₂, h₂⟩ := hsmall hg.continuous hg0
  set σ : ℝ := min (min ε₁ ε₂ / 2) (1 / 2) with hσ
  have hσpos : 0 < σ := lt_min (by positivity) (by norm_num)
  have hσ1 : σ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hσε₁ : σ < ε₁ := lt_of_le_of_lt (min_le_left _ _)
    (by have := min_le_left ε₁ ε₂; linarith)
  have hσε₂ : σ < ε₂ := lt_of_le_of_lt (min_le_left _ _)
    (by have := min_le_right ε₁ ε₂; linarith)
  set s : unitInterval := ⟨σ, hσpos.le, hσ1.le⟩
  have hs0 : s ≠ 0 := fun e => hσpos.ne' (congrArg Subtype.val e)
  have hs1 : s ≠ 1 := fun e => hσ1.ne (congrArg Subtype.val e)
  have hs0' : (0 : unitInterval) < s := lt_of_le_of_ne unitInterval.nonneg' (Ne.symm hs0)
  have hfB : ∀ t ∈ Icc (0 : unitInterval) s, f t ∉ frontier I := fun t ht =>
    h₁ t (lt_of_le_of_lt (show (t : ℝ) ≤ σ from ht.2) hσε₁)
  have hgB : ∀ t ∈ Icc (0 : unitInterval) s, g t ∉ frontier I := fun t ht =>
    h₂ t (lt_of_le_of_lt (show (t : ℝ) ≤ σ from ht.2) hσε₂)
  have ha₀J : a₀ ⊆ J := hab₀ ▸ subset_union_left
  have hb₀J : b₀ ⊆ J := hab₀ ▸ subset_union_right
  have hfJ : ∀ t, f t ∈ J := fun t => ha₀J (hfr' ▸ mem_range_self t)
  have hgJ : ∀ t, g t ∈ J := fun t => hb₀J (hgr' ▸ mem_range_self t)
  -- `f t = g t'` only at the ends
  have hfg : ∀ t t', f t = g t' → (t = 0 ∧ t' = 0) ∨ (t = 1 ∧ t' = 1) := by
    intro t t' e
    have hmem : f t ∈ a₀ ∩ b₀ := ⟨hfr' ▸ mem_range_self t, e ▸ hgr' ▸ mem_range_self t'⟩
    rw [hab₀'] at hmem
    rcases hmem with h | h
    · left
      refine ⟨hf.injective (h.trans hf0.symm), hg.injective ?_⟩
      rw [← e, h, hg0]
    · rw [mem_singleton_iff] at h
      right
      refine ⟨hf.injective (h.trans hf1.symm), hg.injective ?_⟩
      rw [← e, h, hg1]
  set p₁ := f s
  set q₁ := g s
  have hp₁q₁ : p₁ ≠ q₁ := fun e => by
    rcases hfg s s e with ⟨h, -⟩ | ⟨h, -⟩
    · exact hs0 h
    · exact hs1 h
  obtain ⟨a, b, ha, hb, hab, hab'⟩ := m25_theorem10 hG hJ (hfJ s) (hgJ s) hp₁q₁
  set C' := f '' Ico 0 s ∪ g '' Ico 0 s with hC'
  set C := f '' Icc 0 s ∪ g '' Icc 0 s with hC
  have h0Ico : (0 : unitInterval) ∈ Ico 0 s := ⟨le_rfl, hs0'⟩
  have hC'c : IsPreconnected C' := by
    refine IsPreconnected.union x ⟨0, h0Ico, hf0⟩ ⟨0, h0Ico, hg0⟩ ?_ ?_
    · exact isPreconnected_Ico.image _ hf.continuous.continuousOn
    · exact isPreconnected_Ico.image _ hg.continuous.continuousOn
  have hC'sub : C' ⊆ J \ {p₁, q₁} := by
    rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · refine ⟨hfJ t, ?_⟩
      rintro (h | h)
      · exact ht.2.ne (hf.injective h)
      · rcases hfg t s h with ⟨-, h'⟩ | ⟨-, h'⟩
        · exact hs0 h'
        · exact hs1 h'
    · refine ⟨hgJ t, ?_⟩
      rintro (h | h)
      · rcases hfg s t h.symm with ⟨h', -⟩ | ⟨h', -⟩
        · exact hs0 h'
        · exact hs1 h'
      · exact ht.2.ne (hg.injective h)
  have hCC' : C ⊆ insert p₁ (insert q₁ C') := by
    rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · by_cases hts : t = s
      · exact Or.inl (by rw [hts])
      · exact Or.inr (Or.inr (Or.inl ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 hts⟩, rfl⟩))
    · by_cases hts : t = s
      · exact Or.inr (Or.inl (by rw [hts]))
      · exact Or.inr (Or.inr (Or.inr ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 hts⟩, rfl⟩))
  have hCconn : IsConnected C := by
    refine ⟨⟨x, Or.inl ⟨0, ⟨le_rfl, hs0'.le⟩, hf0⟩⟩, ?_⟩
    refine IsPreconnected.union x ⟨0, ⟨le_rfl, hs0'.le⟩, hf0⟩ ⟨0, ⟨le_rfl, hs0'.le⟩, hg0⟩ ?_ ?_
    · exact isPreconnected_Icc.image _ hf.continuous.continuousOn
    · exact isPreconnected_Icc.image _ hg.continuous.continuousOn
  have hxC' : x ∈ C' := Or.inl ⟨0, h0Ico, hf0⟩
  -- the half of `J` containing `C'` is `C`; the other half contains the boundary and misses `x`
  have claim : ∀ a b : Set (Quotient r), IsArcElt p₁ q₁ a → IsArcElt p₁ q₁ b → a ∪ b = J →
      a ∩ b = {p₁, q₁} → C' ⊆ a → frontier I ⊆ b ∧ x ∉ b := by
    intro a b ha hb hab hab' hC'a
    have hCa : C ⊆ a := hCC'.trans (insert_subset ha.2.2.2.2.1
      (insert_subset ha.2.2.2.2.2.1 hC'a))
    have hCeq : C = a := by
      by_contra hne
      exact ha.isCutArc.irreducible C hCa hne (Or.inl ⟨s, ⟨hs0'.le, le_rfl⟩, rfl⟩)
        (Or.inr ⟨s, ⟨hs0'.le, le_rfl⟩, rfl⟩) hCconn
    refine ⟨fun z hz => ?_, fun hxb => ?_⟩
    · rcases (hab ▸ hfr hz : z ∈ a ∪ b) with hza | hzb
      · rw [← hCeq] at hza
        rcases hza with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
        · exact absurd hz (hfB t ht)
        · exact absurd hz (hgB t ht)
      · exact hzb
    · have : x ∈ a ∩ b := ⟨hC'a hxC', hxb⟩
      rw [hab'] at this
      exact (hC'sub hxC').2 this
  have hsep : C' ⊆ a \ {p₁, q₁} ∨ C' ⊆ b \ {p₁, q₁} := by
    refine subset_side_of_isPreconnected hC'c ?_ ?_ ?_
    · intro z hz
      obtain ⟨hzJ, hzpq⟩ := hC'sub hz
      rcases (hab ▸ hzJ : z ∈ a ∪ b) with h | h
      · exact Or.inl ⟨h, hzpq⟩
      · exact Or.inr ⟨h, hzpq⟩
    · rw [disjoint_left]
      intro z hz hz'
      have hza : z ∈ a := closure_minimal diff_subset ha.2.1 hz
      have : z ∈ a ∩ b := ⟨hza, hz'.1⟩
      rw [hab'] at this
      exact hz'.2 this
    · rw [disjoint_left]
      intro z hz hz'
      have hzb : z ∈ b := closure_minimal diff_subset hb.2.1 hz'
      have : z ∈ a ∩ b := ⟨hz.1, hzb⟩
      rw [hab'] at this
      exact hz.2 this
  have haJ : a ⊆ J := hab ▸ subset_union_left
  have hbJ : b ⊆ J := hab ▸ subset_union_right
  obtain ⟨A, hA, hAJ, hBA, hxA⟩ : ∃ A, IsArcElt p₁ q₁ A ∧ A ⊆ J ∧ frontier I ⊆ A ∧ x ∉ A := by
    rcases hsep with h | h
    · exact ⟨b, hb, hbJ, claim a b ha hb hab hab' (h.trans diff_subset)⟩
    · exact ⟨a, ha, haJ, claim b a hb ha (by rw [union_comm]; exact hab)
        (by rw [inter_comm, hab', pair_comm]) (h.trans diff_subset)⟩
  -- `G − A` is disconnected, against Theorem 9
  have hAc := (m25_theorem9 hG hA).isPreconnected
  rw [isPreconnected_iff_subset_of_disjoint] at hAc
  obtain ⟨i, hi⟩ := hIne
  have hiA : i ∉ A := fun hiA => disjoint_left.1 hIJ hi (hAJ hiA)
  have hxI : x ∉ closure I := by
    intro hxc
    have hxI : x ∉ I := fun hxI => disjoint_left.1 hIJ hxI hxJ
    exact hxB ⟨hxc, by rw [hIo.interior_eq]; exact hxI⟩
  rcases hAc I (closure I)ᶜ hIo isClosed_closure.isOpen_compl (fun z hzA => by
      by_cases hzI : z ∈ I
      · exact Or.inl hzI
      · refine Or.inr fun hzc => hzA (hBA ⟨hzc, by rw [hIo.interior_eq]; exact hzI⟩))
      (eq_empty_iff_forall_notMem.2 fun z hz => hz.2.2 (subset_closure hz.2.1)) with h | h
  · exact disjoint_left.1 hIJ (h hxA) hxJ
  · exact h hiA (subset_closure hi)

/-- **Theorem 11** (pp. 421–422), for the corrected simple closed curve: `G − J` is the sum of two
domains, only one of which is bounded, and `J` is the boundary of each. -/
theorem m25_theorem11 {J : Set (Quotient r)} (hJ : IsSCCElt J) :
    ∃ I E : Set (Quotient r), IsOpen I ∧ IsConnected I ∧ IsOpen E ∧ IsConnected E ∧
      Disjoint I E ∧ I ∪ E = Jᶜ ∧ Bornology.IsBounded (ptsOf r I) ∧
      ¬ Bornology.IsBounded (ptsOf r E) ∧ frontier I = J ∧ frontier E = J := by
  haveI := t1Space_quot hG
  obtain ⟨hJcl, -, hJn, hJb, -⟩ := id hJ
  obtain ⟨p, hp, q, hq, hpq⟩ := hJn
  obtain ⟨a, b, ha, hb, hab, hab'⟩ := m25_theorem10 hG hJ hp hq hpq
  have hcpt : ∀ {H : Set (Quotient r)}, IsClosed H → Bornology.IsBounded (ptsOf r H) →
      IsCompact (ptsOf r H) := fun hH hb =>
    Metric.isCompact_of_isClosed_isBounded (isClosed_iff_ptsOf.1 hH) hb
  have hK : ptsOf r a ∩ ptsOf r b = ptsOf r {p} ∪ ptsOf r {q} := by
    ext z
    have := congrArg (fun S => Quotient.mk r z ∈ S) hab'
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at this
    simp only [mem_inter_iff, mem_union, mem_ptsOf, mem_singleton_iff]
    exact Iff.of_eq this
  have hd : Disjoint (ptsOf r {p}) (ptsOf r {q}) := by
    rw [disjoint_left]
    intro z hzp hzq
    exact hpq ((mem_singleton_iff.1 hzp).symm.trans (mem_singleton_iff.1 hzq))
  obtain ⟨U, V, hUo, hUc, hVo, hVc, hUV, hUVeq⟩ := mullikin_theorem5 (hcpt ha.2.1 ha.2.2.2.1)
    (isConnected_ptsOf hG ha.2.2.1) (hcpt hb.2.1 hb.2.2.2.1) (isConnected_ptsOf hG hb.2.2.1)
    (not_separatesPlane_ptsOf hG (m25_theorem9 hG ha))
    (not_separatesPlane_ptsOf hG (m25_theorem9 hG hb)) hK
    (isClosed_iff_ptsOf.1 isClosed_singleton) (isConnected_ptsOf_singleton hG p)
    (isClosed_iff_ptsOf.1 isClosed_singleton) (isConnected_ptsOf_singleton hG q) hd
  have hUVeq' : U ∪ V = (ptsOf r J)ᶜ := by
    rw [hUVeq, ← hab]; rfl
  have hUs := ptsOf_image_eq_of_split hG hUo hVo hUV hUVeq'
  have hVs := ptsOf_image_eq_of_split hG hVo hUo hUV.symm (by rw [union_comm]; exact hUVeq')
  set I₀ := Quotient.mk r '' U with hI₀
  set E₀ := Quotient.mk r '' V with hE₀
  have hIo : IsOpen I₀ := isOpen_iff_ptsOf.2 (hUs ▸ hUo)
  have hEo : IsOpen E₀ := isOpen_iff_ptsOf.2 (hVs ▸ hVo)
  have hIc : IsConnected I₀ := hUc.image _ continuous_mk.continuousOn
  have hEc : IsConnected E₀ := hVc.image _ continuous_mk.continuousOn
  have hmemI : ∀ z : Pt, Quotient.mk r z ∈ I₀ ↔ z ∈ U := fun z => by
    rw [← mem_ptsOf, hUs]
  have hmemE : ∀ z : Pt, Quotient.mk r z ∈ E₀ ↔ z ∈ V := fun z => by
    rw [← mem_ptsOf, hVs]
  have hIE : Disjoint I₀ E₀ := by
    rw [disjoint_left]
    rintro w hwI hwE
    obtain ⟨z, rfl⟩ := Quotient.mk_surjective w
    exact disjoint_left.1 hUV ((hmemI z).1 hwI) ((hmemE z).1 hwE)
  have hIEJ : I₀ ∪ E₀ = Jᶜ := by
    ext w
    obtain ⟨z, rfl⟩ := Quotient.mk_surjective w
    rw [mem_union, hmemI, hmemE, ← mem_union, hUVeq']
    rfl
  have hIJ : Disjoint I₀ J := by
    rw [disjoint_left]; intro w hw hwJ
    have : w ∈ Jᶜ := hIEJ ▸ Or.inl hw
    exact this hwJ
  have hEJ : Disjoint E₀ J := by
    rw [disjoint_left]; intro w hw hwJ
    have : w ∈ Jᶜ := hIEJ ▸ Or.inr hw
    exact this hwJ
  have hfrI : frontier I₀ ⊆ J := by
    intro w hw
    by_contra hwJ
    rcases (hIEJ ▸ hwJ : w ∈ I₀ ∪ E₀) with h | h
    · rw [hIo.frontier_eq] at hw; exact hw.2 h
    · obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 (frontier_subset_closure hw) E₀ hEo h
      exact disjoint_left.1 hIE hz2 hz1
  have hfrE : frontier E₀ ⊆ J := by
    intro w hw
    by_contra hwJ
    rcases (hIEJ ▸ hwJ : w ∈ I₀ ∪ E₀) with h | h
    · obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 (frontier_subset_closure hw) I₀ hIo h
      exact disjoint_left.1 hIE hz1 hz2
    · rw [hEo.frontier_eq] at hw; exact hw.2 h
  have hfI := frontier_eq_of_scc hG hJ hIo hIc.nonempty hIJ hfrI
  have hfE := frontier_eq_of_scc hG hJ hEo hEc.nonempty hEJ hfrE
  -- one domain is bounded and the other one unbounded
  have hnotboth : ¬ (¬ Bornology.IsBounded (ptsOf r I₀) ∧ ¬ Bornology.IsBounded (ptsOf r E₀)) := by
    rintro ⟨h1, h2⟩
    obtain ⟨y, -, -, hyu⟩ := m25_unbounded_unique hJb
    obtain ⟨i, hi⟩ := hIc.nonempty
    obtain ⟨e, he⟩ := hEc.nonempty
    have hcI : connectedComponentIn Jᶜ i = I₀ :=
      connectedComponentIn_eq_of_split hIo hEo hIE hIEJ.symm hIc.isPreconnected hi
    have hcE : connectedComponentIn Jᶜ e = E₀ :=
      connectedComponentIn_eq_of_split hEo hIo hIE.symm (by rw [union_comm]; exact hIEJ.symm)
        hEc.isPreconnected he
    have hiJ : i ∉ J := disjoint_left.1 hIJ hi
    have heJ : e ∉ J := disjoint_left.1 hEJ he
    have := (hyu i hiJ (hcI ▸ h1)).trans (hyu e heJ (hcE ▸ h2)).symm
    rw [hcI, hcE] at this
    exact disjoint_left.1 hIE hi (this ▸ hi)
  have hnotboth' : ¬ (Bornology.IsBounded (ptsOf r I₀) ∧ Bornology.IsBounded (ptsOf r E₀)) := by
    rintro ⟨h1, h2⟩
    apply NormedSpace.unbounded_univ ℝ Pt
    have : (univ : Set Pt) = ptsOf r I₀ ∪ ptsOf r E₀ ∪ ptsOf r J := by
      ext z
      simp only [mem_univ, mem_union, mem_ptsOf, true_iff]
      by_cases hz : Quotient.mk r z ∈ J
      · exact Or.inr hz
      · exact Or.inl (show Quotient.mk r z ∈ I₀ ∪ E₀ by rw [hIEJ]; exact hz)
    rw [this]
    exact (h1.union h2).union hJb
  by_cases hIb : Bornology.IsBounded (ptsOf r I₀)
  · exact ⟨I₀, E₀, hIo, hIc, hEo, hEc, hIE, hIEJ, hIb, fun h => hnotboth' ⟨hIb, h⟩, hfI, hfE⟩
  · have hEb : Bornology.IsBounded (ptsOf r E₀) := by
      by_contra h; exact hnotboth ⟨hIb, h⟩
    exact ⟨E₀, I₀, hEo, hEc, hIo, hIc, hIE.symm, by rw [union_comm]; exact hIEJ, hEb, hIb, hfE,
      hfI⟩

end M25B

end HPC.Moore
