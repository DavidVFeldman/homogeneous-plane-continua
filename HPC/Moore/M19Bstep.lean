import HPC.Moore.M19A

/-!
# Moore 1919, the step in the proof of Theorem B (batch 140, item B)

`m19_B_step`: an arc `PQ` of the closed curve `L` lying within the closed curve `J` can be
replaced by an arc from `P` to `Q` lying within `J` and, except for its ends, within `L`.
Moore: "It is easy to see, with the aid of Theorems 43 and 40, that there exists an arc `AₙZₙBₙ`
that lies entirely within `J` and, except for its endpoints, is also entirely within `L`" (p. 172).
The proof given here does not use Theorem 43: it uses batch 138's `accessible` (the accessibility
lemma behind Theorems 32, 39, 40) in the open set `I − K₂`, where `K₂` is the other arc of `L`
from `P` to `Q`.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

namespace Gen

variable {X : Type*} [TopologicalSpace X]

/-- **The tail of an arc in an open set.** If the arc `FH` ends at a point `H` of the open set
`O`, a connected nonempty piece of it, lying in `O` and not containing `H`, has `H` as a limit
point. -/
theorem TArc.tail_in_open {F H : X} {γ : Set X} (hγ : TArc F H γ) {O : Set X} (hO : IsOpen O)
    (hH : H ∈ O) : ∃ C ⊆ γ ∩ O, IsPreconnected C ∧ C.Nonempty ∧ H ∉ C ∧ H ∈ closure C := by
  obtain ⟨-, g, hg, rfl, -, rfl⟩ := hγ
  have hV : g ⁻¹' O ∈ 𝓝 (1 : unitInterval) := hg.continuous.continuousAt.preimage_mem_nhds
    (hO.mem_nhds hH)
  obtain ⟨l, hl, hlV⟩ := (mem_nhdsLE_iff_exists_Ioc_subset' (a := 1) (l' := 0) (by simp)).mp
    (mem_nhdsWithin_of_mem_nhds hV)
  have hl1 : l < 1 := hl
  obtain ⟨r, hlr, hr1⟩ := exists_between hl1
  refine ⟨g '' Ioo l 1, ?_, isPreconnected_Ioo.image _ hg.continuous.continuousOn,
    ⟨g r, r, ⟨hlr, hr1⟩, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨mem_range_self u, hlV ⟨hu.1, hu.2.le⟩⟩
  · rintro ⟨u, hu, e⟩
    exact hu.2.ne (hg.injective e)
  · have h1 : (1 : unitInterval) ∈ closure (Ioo l 1) := by
      rw [closure_Ioo hl1.ne]; exact ⟨hl1.le, le_rfl⟩
    exact image_closure_subset_closure_image hg.continuous ⟨1, h1, rfl⟩

end Gen

variable {S : Type*} {σ : Space S}

/-- The step in the proof of Theorem B (p. 172): "It is easy to see, with the aid of Theorems 43
and 40, that there exists an arc `AₙZ̄ₙBₙ` that lies entirely within `J` and, except for its
endpoints, is also entirely within `L`." The data: an arc `K = AₙZₙBₙ` of `L` lying entirely
within `J`. *Axioms used: 1–8.*
**Proof replaced** (Theorem 43 is not used): `K₂` is the other arc of `L` from `P` to `Q`, so
`O = I − K₂` is open, contains the open arc `K`, and `O − K = I − L`. A point `H` of the open arc
`K` is reached from the interior `I_L` of `L` by an arc (`Gen.exists_access`), whose last piece
lies in `O − K` and so in one component `Q` of `O − K`, contained in `I_L`. Batch 138's
`accessible`, applied to `K` parametrized in both directions, joins a point of `Q` to `Q` and to
`P` by arcs lying, except for their ends, in `Q`. Their union contains the arc sought.
**Shape change:** the axioms are made explicit. -/
theorem m19_B_step (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
    {J I L IL : Set S} (hJ : σ.IsInteriorOf J I) (hL : σ.IsInteriorOf L IL)
    {P Q : S} {K : Set S} (hK : σ.IsArc P Q K) (hKL : K ⊆ L) (hKI : K ⊆ I) :
    ∃ K', σ.IsArc P Q K' ∧ K' ⊆ I ∧ openArc P Q K' ⊆ IL := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  have harc := arcConn h1 h3 h4 h51 h2
  obtain ⟨hIo, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hJ
  obtain ⟨hILo, hILc, hILne, hfrL, hELo, -, -, -, -, hdisL, -, hcomplL, -, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hL
  -- the other arc `K₂` of `L` from `P` to `Q`
  obtain ⟨C₁, C₂, hC₁, hC₂, hCi, hCu, huniq⟩ :=
    fa_scc_two_arcs h1 h3 h4 h51 hL.1 (hKL hK.left_mem) (hKL hK.right_mem) hK.1
  obtain ⟨K₂, hK₂, hKK₂, hKK₂u⟩ : ∃ K₂, σ.IsArc P Q K₂ ∧ K ∩ K₂ = {P, Q} ∧ K ∪ K₂ = L := by
    rcases huniq K hKL hK with rfl | rfl
    · exact ⟨C₂, hC₂, hCi, hCu⟩
    · exact ⟨C₁, hC₁, by rw [inter_comm, hCi], by rw [union_comm, hCu]⟩
  rw [isArc_iff_tarc h1 h3 h4 h51] at hK hK₂
  have hK₂c : IsClosed K₂ := hK₂.isClosed
  set O := I \ K₂ with hOdef
  have hOo : IsOpen O := hIo.sdiff hK₂c
  obtain ⟨hPQ, f, hf, hfr, hf0, hf1⟩ := hK
  have hinj := hf.injective
  -- the open arc `K` lies in `O`
  have hfO : ∀ u ∈ Ioo (0 : unitInterval) 1, f u ∈ O := by
    intro u hu
    refine ⟨hKI (hfr ▸ mem_range_self u), fun h => ?_⟩
    have : f u ∈ K ∩ K₂ := ⟨hfr ▸ mem_range_self u, h⟩
    rw [hKK₂, ← hf0, ← hf1] at this
    rcases this with e | e
    · exact hu.1.ne' (hinj e)
    · exact hu.2.ne (hinj e)
  have hOK : O \ range f = I \ L := by
    rw [hfr, ← hKK₂u]
    ext x; simp only [hOdef, mem_diff, mem_union, not_or]; tauto
  -- a point `H` of the open arc reached from `I_L`
  set m : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩ with hm
  have hm0 : (0 : unitInterval) < m := by rw [hm]; exact Subtype.mk_lt_mk.mpr (by norm_num)
  have hm1 : m < 1 := by rw [hm]; exact Subtype.mk_lt_mk.mpr (by norm_num)
  obtain ⟨F, hF⟩ := hILne
  have hzL : f m ∈ frontier IL := hfrL ▸ hKL (hfr ▸ mem_range_self m)
  obtain ⟨H, ⟨hHfr, hHO⟩, γ, hγ, hγIL⟩ :=
    exists_access harc hILo hILc hF hzL (hOo.mem_nhds (hfO m ⟨hm0, hm1⟩))
  have hHL : H ∈ L := hfrL ▸ hHfr
  obtain ⟨u, hu, rfl⟩ : ∃ u ∈ Ioo (0 : unitInterval) 1, f u = H := by
    have hHK : H ∈ K := by
      rcases hKK₂u ▸ hHL with h | h
      · exact h
      · exact absurd h hHO.2
    rw [← hfr] at hHK
    obtain ⟨u, rfl⟩ := hHK
    refine ⟨u, ⟨lt_of_le_of_ne nonneg' fun e => ?_, lt_of_le_of_ne le_one' fun e => ?_⟩, rfl⟩
    · exact hHO.2 (by rw [← e, hf0]; exact (hKK₂.symm.subset.trans inter_subset_right) (Or.inl rfl))
    · exact hHO.2 (by rw [e, hf1]; exact (hKK₂.symm.subset.trans inter_subset_right) (Or.inr rfl))
  -- the last piece of `γ` lies in one component `Qc` of `O − K`
  obtain ⟨C, hCγO, hCc, ⟨x₀, hx₀C⟩, hHC, hHcl⟩ := hγ.tail_in_open hOo hHO
  have hCOK : C ⊆ O \ range f := by
    intro x hx
    refine ⟨(hCγO hx).2, ?_⟩
    have hxIL : x ∈ IL := hγIL ⟨(hCγO hx).1, fun e => hHC (mem_singleton_iff.mp e ▸ hx)⟩
    rw [hfr]
    exact fun h => disjoint_left.mp hdisL hxIL (hKL h)
  set Qc := connectedComponentIn (O \ range f) x₀ with hQc
  have hCQ : C ⊆ Qc := hCc.subset_connectedComponentIn hx₀C hCOK
  have hx₀ : x₀ ∈ O \ range f := hCOK hx₀C
  have hQIL : Qc ⊆ IL := by
    have hQL : Qc ⊆ IL ∪ (closure IL)ᶜ := by
      intro x hx
      have hx' := connectedComponentIn_subset _ _ hx
      rw [hOK] at hx'
      rw [← hcomplL]; exact hx'.2
    rcases isPreconnected_connectedComponentIn.subset_or_subset hILo hELo
        (disjoint_compl_right.mono_left subset_closure) hQL with h | h
    · exact h
    · exfalso
      have hx₀IL : x₀ ∈ IL := hγIL ⟨(hCγO hx₀C).1, fun e => hHC (mem_singleton_iff.mp e ▸ hx₀C)⟩
      exact h (mem_connectedComponentIn hx₀) (subset_closure hx₀IL)
  have hQO : Qc ⊆ O := (connectedComponentIn_subset _ _).trans diff_subset
  have hadj : f u ∈ closure Qc := closure_mono hCQ hHcl
  -- the arcs from `x₀` to `Q` and to `P`
  obtain ⟨τ₁, hτ₁, hτ₁Q⟩ := accessible h1 h2 h3 h4 h5 h6 h7 h8 hf hOo (t₀ := 0)
    (zero_lt_one' unitInterval) hfO hx₀ ⟨u, hu, hadj⟩
  set f' := f ∘ unitInterval.symm with hf'
  have hf'e : IsEmbedding f' :=
    hf.comp (unitInterval.symmHomeomorph.isEmbedding)
  have hf'r : range f' = range f := by
    rw [hf', range_comp, unitInterval.symm_involutive.surjective.range_eq, image_univ]
  have hf'O : ∀ v ∈ Ioo (0 : unitInterval) 1, f' v ∈ O := by
    intro v hv
    refine hfO _ ⟨?_, ?_⟩
    · rw [← unitInterval.symm_one]; exact unitInterval.symm_lt_symm.mpr hv.2
    · rw [← unitInterval.symm_zero]; exact unitInterval.symm_lt_symm.mpr hv.1
  have hsu : unitInterval.symm u ∈ Ioo (0 : unitInterval) 1 := by
    refine ⟨?_, ?_⟩
    · rw [← unitInterval.symm_one]; exact unitInterval.symm_lt_symm.mpr hu.2
    · rw [← unitInterval.symm_zero]; exact unitInterval.symm_lt_symm.mpr hu.1
  obtain ⟨τ₂, hτ₂, hτ₂P⟩ := accessible h1 h2 h3 h4 h5 h6 h7 h8 hf'e hOo (t₀ := 0)
    (zero_lt_one' unitInterval) hf'O (by rw [hf'r]; exact hx₀)
    ⟨unitInterval.symm u, hsu, by
      rw [hf'r]; simp only [hf', Function.comp, unitInterval.symm_symm]; exact hadj⟩
  rw [hf'r] at hτ₂P
  have hf'1 : f' 1 = P := by simp [hf', hf0]
  rw [hf'1] at hτ₂ hτ₂P
  rw [hf1] at hτ₁ hτ₁Q
  obtain ⟨K', hK'sub, hK'⟩ := hτ₂.symm.join hτ₁.symm ⟨x₀, hτ₂.left_mem, hτ₁.left_mem⟩ hPQ
  refine ⟨K', (isArc_iff_tarc h1 h3 h4 h51).mpr hK', ?_, ?_⟩
  · intro x hx
    rcases hK'sub hx with h | h
    · rcases hτ₂P h with rfl | h
      · exact hKI (hfr ▸ ⟨0, hf0⟩)
      · exact (hQO h).1
    · rcases hτ₁Q h with rfl | h
      · exact hKI (hfr ▸ ⟨1, hf1⟩)
      · exact (hQO h).1
  · rintro x ⟨hx, hxPQ⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hxPQ
    rcases hK'sub hx with h | h
    · rcases hτ₂P h with rfl | h
      · exact absurd rfl hxPQ.1
      · exact hQIL h
    · rcases hτ₁Q h with rfl | h
      · exact absurd rfl hxPQ.2
      · exact hQIL h

end HPC.Moore
