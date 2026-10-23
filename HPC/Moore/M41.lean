import HPC.Moore.M41Half

/-!
# Moore, F.A. (1916), Theorems 41 and 42 (batch 140, item A)

**Theorem 41** (p. 155). If the interiors `I₁`, `I₂` of the closed curves `J₁`, `J₂` meet, there is a
closed curve `J ⊆ J₁ + J₂` whose interior contains `I₁ + I₂`.

Case I (`J₁ ∩ J₂` at most one point) and the first sub-case of Case II (`J₂ ⊆ I₁'`) were proved in
batch 139 (`fa_theorem41_caseI`, `fa_theorem41_of_subset`). Case II proper is
`fa_theorem41_caseII`. Moore's last sentence, "It may be proved that `J` is a closed curve
satisfying the requirements of Theorem 41" (p. 156), is supplied as follows (commission check 4).

1. `V`: a component of `S − (I₁' + I₂')` whose closure is not compact
   (`Gen.exists_unbounded_component`). Its boundary lies on `J₁ + J₂`, and `V` misses the interior
   of every closed curve missing `V` (`Gen.disjoint_of_unbounded`).
2. `O`: a point of `J₂` without `J₁` that is a limit point of `V` (otherwise `V` would be the
   exterior of `J₁`, and `J₂ ⊆ I₁'`). The chord of `J₂` through `O` lies in `V'` (`chord_side`), and
   gives a second such point `O'`.
3. `J₂` is split at `O`, `O'` into two arcs; on each, every arc of `J₂` cut off by a chord of `J₁`
   lying in `V'` is replaced by that chord (`half_replace`, which rests on Theorem 27 through
   `pocket`, and on Theorem A of 1919 through `chords_null` and `Gen.arc_replace`). The two results
   are arcs from `O` to `O'` meeting only in `O`, `O'`: their union `J` is a closed curve on
   `J₁ + J₂`, and it contains the boundary of `V` (every point of `J₁` without `J₂` on that boundary
   lies on a chord of `J₁` in `V'`, `chord_through`, `chord_side`).
4. `V` is then the exterior of `J`, and so `J` is the boundary of `V`; `I₁ + I₂` misses `J` and the
   exterior, so it lies in the interior (`curve_of_frontier_subset`).

Moore's own `J` is built from the arcs of Theorem 38 (the outermost pocket through each point);
the curve here is the same one (the boundary of `V`), reached without Theorem 38.

**Theorem 42** follows by batch 139's `fa_theorem42_of_41`.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-- Every compact set lies in the interior of a compact set (the closures of regions are compact).
*Axioms used: 1, 4.* -/
theorem exists_compact_superset_moore (h1 : σ.Axiom1) (h4 : σ.Axiom4) {K : Set S}
    (hK : @IsCompact S σ.topology K) :
    ∃ N, @IsCompact S σ.topology N ∧ K ⊆ @interior S σ.topology N := by
  letI := σ.topology
  haveI : WeaklyLocallyCompactSpace S := ⟨fun x => by
    obtain ⟨Kseq, hKr, hKcov, -⟩ := id h1
    obtain ⟨n, -, hn⟩ := hKcov 0 x
    exact ⟨closure (Kseq n), isCompact_closure_region h1 h4 (hKr n),
      Filter.mem_of_superset ((isOpen_region (hKr n)).mem_nhds hn) subset_closure⟩⟩
  exact exists_compact_superset hK

section Th41

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)

include h1 h2 h3 h4 h5 h7 h8 in
/-- **The last step of Case II.** A closed curve `J ⊆ J₁ + J₂` containing the boundary of the
unbounded component `V` of `S − (I₁' + I₂')` has `V` as its exterior, and its interior contains
`I₁ + I₂`. *Axioms used: 1–5, 7, 8.* -/
theorem curve_of_frontier_subset {J₁ J₂ I₁ I₂ V J : Set S} (hI₁ : σ.IsInteriorOf J₁ I₁)
    (hI₂ : σ.IsInteriorOf J₂ I₂) (hVo : @IsOpen S σ.topology V)
    (hV : @IsPreconnected S σ.topology V) (hVne : V.Nonempty)
    (hVnc : ¬ @IsCompact S σ.topology (@closure S σ.topology V))
    (hVI₁ : Disjoint V (@closure S σ.topology I₁)) (hVI₂ : Disjoint V (@closure S σ.topology I₂))
    (hJ : @TSCC S σ.topology J) (hJsub : J ⊆ J₁ ∪ J₂) (hfrJ : @frontier S σ.topology V ⊆ J) :
    ∃ I, σ.IsInteriorOf J I ∧ I₁ ∪ I₂ ⊆ I := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have hJs : σ.IsSCC J := (isSCC_iff_tscc h1 h3 h4 h51).mpr hJ
  obtain ⟨I, hI, -⟩ := existsUnique_interior h1 h3 h4 h5 h7 h8 hJs
  obtain ⟨-, -, -, -, -, hEc, -, hfrE, -, hdisIJ, hdisEJ, hcompl, -, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hI
  obtain ⟨hI₁o, -, -, hfr₁, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI₁
  obtain ⟨hI₂o, -, -, hfr₂, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI₂
  have hVJ : Disjoint V J := by
    refine disjoint_left.mpr fun x hx hxJ => ?_
    rcases hJsub hxJ with h | h
    · exact disjoint_left.mp hVI₁ hx (frontier_subset_closure (hfr₁.symm ▸ h))
    · exact disjoint_left.mp hVI₂ hx (frontier_subset_closure (hfr₂.symm ▸ h))
  have hVI : Disjoint V I := disjoint_of_unbounded (fun R hR => isCompact_closure_region h1 h4 hR)
    ((isInteriorOf_iff h1 h3 h4 h51).mp hI) hV hVnc hVJ
  have hVE : V ⊆ (closure I)ᶜ := by
    intro x hx
    have : x ∈ Jᶜ := fun h => disjoint_left.mp hVJ hx h
    rw [hcompl] at this
    exact this.resolve_left fun h => disjoint_left.mp hVI hx h
  have hEV : (closure I)ᶜ ⊆ V := by
    have hsub : (closure I)ᶜ ⊆ V ∪ (closure V)ᶜ := fun x hx => by
      by_cases hxc : x ∈ closure V
      · left
        by_contra hxV
        exact disjoint_left.mp hdisEJ hx (hfrJ ⟨hxc, by rwa [hVo.interior_eq]⟩)
      · exact Or.inr hxc
    obtain ⟨v, hv⟩ := hVne
    exact hEc.subset_left_of_subset_union hVo isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) hsub ⟨v, hVE hv, hv⟩
  have hVeq : V = (closure I)ᶜ := subset_antisymm hVE hEV
  have hfr : frontier V = J := hVeq ▸ hfrE
  refine ⟨I, hI, fun x hx => ?_⟩
  have hxV : x ∉ closure V := by
    rcases hx with h | h
    · exact fun hc => disjoint_left.mp ((hVI₁.mono_right subset_closure).closure_left hI₁o) hc h
    · exact fun hc => disjoint_left.mp ((hVI₂.mono_right subset_closure).closure_left hI₂o) hc h
  have hxJ : x ∈ Jᶜ := fun h => hxV (frontier_subset_closure (hfr.symm ▸ h))
  rw [hcompl] at hxJ
  exact hxJ.resolve_right fun h => hxV (subset_closure (hVeq.symm ▸ h))

include h1 h2 h3 h4 h5 h6 h7 h8

/-- **Theorem 41, Case II** (`J₁ ∩ J₂` has two points and `J₂` has a point without `J₁`).
*Axioms used: 1–8.* -/
theorem fa_theorem41_caseII {J₁ J₂ I₁ I₂ : Set S} (hI₁ : σ.IsInteriorOf J₁ I₁)
    (hI₂ : σ.IsInteriorOf J₂ I₂) (hmeet : (I₁ ∩ I₂).Nonempty) {y y' : S} (hy : y ∈ J₁ ∩ J₂)
    (hy' : y' ∈ J₁ ∩ J₂) (hyy : y ≠ y') (hs2 : ¬ J₂ ⊆ I₁ ∪ J₁) :
    ∃ J I, J ⊆ J₁ ∪ J₂ ∧ σ.IsInteriorOf J I ∧ I₁ ∪ I₂ ⊆ I := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨hI₁o, hI₁c, -, hfr₁, hE₁o, hE₁c, -, hfrE₁, hcl₁, -, -, hcompl₁, hJ₁cpt, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hI₁
  obtain ⟨hI₂o, hI₂c, -, hfr₂, hE₂o, hE₂c, -, hfrE₂, hcl₂, -, -, hcompl₂, hJ₂cpt, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hI₂
  have hJ₁cl : J₁ ⊆ closure I₁ := hfr₁ ▸ frontier_subset_closure
  have hJ₂cl : J₂ ⊆ closure I₂ := hfr₂ ▸ frontier_subset_closure
  have hJ₁c : IsClosed J₁ := hJ₁cpt.isClosed
  have hJ₂c : IsClosed J₂ := hJ₂cpt.isClosed
  -- 1. the unbounded component `V`
  set K := closure I₁ ∪ closure I₂ with hKdef
  have hKc : IsClosed K := isClosed_closure.union isClosed_closure
  have hKcpt : IsCompact K :=
    (isCompact_closure_region h1 h4 hI₁.2.1).union (isCompact_closure_region h1 h4 hI₂.2.1)
  obtain ⟨N, hN, hKN⟩ := exists_compact_superset_moore h1 h4 hKcpt
  have hE₂nc : ¬ IsCompact (closure (closure I₂)ᶜ) := fun h =>
    not_isCompact_univ h1 h5 (((isCompact_closure_region h1 h4 hI₂.2.1).union h).of_isClosed_subset
      isClosed_univ fun x _ => by
        by_cases hx : x ∈ closure I₂
        · exact Or.inl hx
        · exact Or.inr (subset_closure hx))
  have hE₂K : (closure (closure I₂)ᶜ ∩ K).Nonempty :=
    ⟨y, frontier_subset_closure (hfrE₂.symm ▸ hy.2), Or.inr (hJ₂cl hy.2)⟩
  obtain ⟨x₀, hx₀K, hVnc⟩ := exists_unbounded_component hKc hN hKN hE₂c hE₂nc hE₂K
  set V := connectedComponentIn Kᶜ x₀ with hVdef
  have hVo : IsOpen V := hKc.isOpen_compl.connectedComponentIn
  have hVc : IsPreconnected V := isPreconnected_connectedComponentIn
  have hx₀V : x₀ ∈ V := mem_connectedComponentIn hx₀K
  have hVK : V ⊆ Kᶜ := connectedComponentIn_subset _ _
  have hfrV : frontier V ⊆ K := frontier_connectedComponentIn_subset hKc x₀
  have hVI₁ : Disjoint V (closure I₁) := disjoint_left.mpr fun x hx h => hVK hx (Or.inl h)
  have hVI₂ : Disjoint V (closure I₂) := disjoint_left.mpr fun x hx h => hVK hx (Or.inr h)
  have hVJ₁ : Disjoint V J₁ := hVI₁.mono_right hJ₁cl
  have hVJ₂ : Disjoint V J₂ := hVI₂.mono_right hJ₂cl
  have hclI₁ : Disjoint (closure V) I₁ := (hVI₁.mono_right subset_closure).closure_left hI₁o
  have hclI₂ : Disjoint (closure V) I₂ := (hVI₂.mono_right subset_closure).closure_left hI₂o
  have hfrV' : ∀ z ∈ closure V, z ∉ V → z ∈ J₁ ∨ z ∈ J₂ := by
    intro z hz hzV
    have hzK : z ∈ K := hfrV ⟨hz, by rwa [hVo.interior_eq]⟩
    rcases hzK with h | h
    · rw [hcl₁] at h
      rcases h with h | h
      · exact absurd h (disjoint_left.mp hclI₁ hz)
      · exact Or.inl h
    · rw [hcl₂] at h
      rcases h with h | h
      · exact absurd h (disjoint_left.mp hclI₂ hz)
      · exact Or.inr h
  have hcl₂V : closure V ∩ ((closure I₂)ᶜ \ J₁) ⊆ V := by
    rintro z ⟨hz, hzE, hzJ⟩
    by_contra hzV
    rcases hfrV' z hz hzV with h | h
    · exact hzJ h
    · exact hzE (hJ₂cl h)
  have hcl₁V : closure V ∩ ((closure I₁)ᶜ \ J₂) ⊆ V := by
    rintro z ⟨hz, hzE, hzJ⟩
    by_contra hzV
    rcases hfrV' z hz hzV with h | h
    · exact hzE (hJ₁cl h)
    · exact hzJ h
  have hVsub₂ : V ⊆ (closure I₂)ᶜ \ J₁ := fun x hx =>
    ⟨fun h => disjoint_left.mp hVI₂ hx h, fun h => disjoint_left.mp hVJ₁ hx h⟩
  have hVsub₁ : V ⊆ (closure I₁)ᶜ \ J₂ := fun x hx =>
    ⟨fun h => disjoint_left.mp hVI₁ hx h, fun h => disjoint_left.mp hVJ₂ hx h⟩
  -- 2. the points `O` and `O'`
  obtain ⟨O, hOV, hOJ₁, hOJ₂⟩ : ∃ O ∈ closure V, O ∉ J₁ ∧ O ∈ J₂ := by
    by_contra hno
    push_neg at hno
    apply hs2
    have hE₁V : (closure I₁)ᶜ ⊆ V := by
      have hsub : (closure I₁)ᶜ ⊆ V ∪ (closure V)ᶜ := fun x hx => by
        by_cases hxc : x ∈ closure V
        · left
          by_contra hxV
          rcases hfrV' x hxc hxV with h | h
          · exact hx (hJ₁cl h)
          · exact hno x hxc (fun h' => hx (hJ₁cl h')) h
        · exact Or.inr hxc
      exact hE₁c.subset_left_of_subset_union hVo isClosed_closure.isOpen_compl
        (disjoint_compl_right.mono_left subset_closure) hsub ⟨x₀, (hVsub₁ hx₀V).1, hx₀V⟩
    intro z hz
    by_contra hz'
    rw [← hcl₁] at hz'
    exact disjoint_left.mp hVJ₂ (hE₁V hz') hz
  have hOE₁ : O ∈ (closure I₁)ᶜ := by
    intro h
    rw [hcl₁] at h
    rcases h with h | h
    · exact disjoint_left.mp hclI₁ hOV h
    · exact hOJ₁ h
  obtain ⟨p, q, d, hd, hdJ, hp, hq, hOd, hdJ₁⟩ :=
    chord_through h1 h3 h4 h51 hI₂.1 hJ₁c hOJ₂ hOJ₁ ⟨hy.2, hy.1⟩ ⟨hy'.2, hy'.1⟩ hyy
  have hdE : d \ {p, q} ⊆ (closure I₁)ᶜ := by
    have hsub : d \ {p, q} ⊆ I₁ ∪ (closure I₁)ᶜ := fun z hz => by
      have : z ∈ J₁ᶜ := fun h => disjoint_left.mp hdJ₁ hz h
      rwa [hcompl₁] at this
    rcases hd.isPreconnected_diff.subset_or_subset hI₁o hE₁o
      (disjoint_compl_right.mono_left subset_closure) hsub with h | h
    · exact absurd (subset_closure (h hOd)) hOE₁
    · exact h
  have hdV : d ⊆ closure V := chord_side h1 h2 h3 h4 h5 h6 h7 h8 hI₂.1 hE₁o hd hdJ hdE hVo hVc
    hVsub₁ hcl₁V ⟨O, hOd, hOV⟩
  obtain ⟨O', hO'd, hO'O⟩ : ∃ O' ∈ d \ {p, q}, O' ≠ O := by
    obtain ⟨Γ₁, Γ₂, hΓ₁, hΓ₂, hΓu, hΓi⟩ :=
      hd.split hOd.1 (fun e => hOJ₁ (e ▸ hp)) (fun e => hOJ₁ (e ▸ hq))
    obtain ⟨z, hz, hzpO⟩ := hΓ₁.nonempty_diff
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzpO
    refine ⟨z, ⟨hΓu ▸ Or.inl hz, ?_⟩, hzpO.2⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨hzpO.1, fun hzq => ?_⟩
    have : z ∈ Γ₁ ∩ Γ₂ := ⟨hz, hzq ▸ hΓ₂.right_mem⟩
    rw [hΓi] at this
    exact hzpO.2 this
  have hO'J₁ : O' ∉ J₁ := fun h => disjoint_left.mp hdJ₁ hO'd h
  have hO'J₂ : O' ∈ J₂ := hdJ hO'd.1
  have hO'V : O' ∈ closure V := hdV hO'd.1
  -- 3. the two arcs of `J₂` from `O` to `O'`, and the replacements
  obtain ⟨D₁, D₂, hD₁, hD₂, hDi, hDu⟩ :=
    exists_two_arcs_of_isSCC h1 h3 h4 h51 hI₂.1 hOJ₂ hO'J₂ hO'O.symm
  rw [isArc_iff_tarc h1 h3 h4 h51] at hD₁ hD₂
  have hJ₁V : ¬ J₁ ⊆ closure V := by
    intro h
    apply hs2
    have hI₂I₁ : I₂ ⊆ I₁ := conn_sub_of_frontier hI₂c
      (by rw [hfr₁]; exact disjoint_left.mpr fun x hx hxJ => disjoint_left.mp hclI₂ (h hxJ) hx)
      (by rwa [inter_comm] at hmeet)
    intro z hz
    rw [← hcl₁]
    exact closure_mono hI₂I₁ (hJ₂cl hz)
  have hE₂J₂ : Disjoint ((closure I₂)ᶜ) J₂ := disjoint_compl_left_iff_subset.mpr hJ₂cl
  -- the replacement on one arc
  have half : ∀ D, TArc O O' D → D ⊆ J₂ → ∃ D', TArc O O' D' ∧
      (∀ x ∈ D', x ∈ D ∨ ∃ Z a b, TArc a b Z ∧ a ∈ D ∧ b ∈ D ∧ Z ⊆ J₁ ∧
        Z \ {a, b} ⊆ (closure I₂)ᶜ ∧ x ∈ Z ∧ Z ⊆ D') ∧
      (∀ Z a b, TArc a b Z → a ∈ D → b ∈ D → Z ⊆ J₁ → Z ⊆ closure V →
        Z \ {a, b} ⊆ (closure I₂)ᶜ → Z ⊆ D') ∧
      closure V ∩ D ⊆ D' := by
    rintro D ⟨-, f, hf, rfl, hf0, hf1⟩ hDJ
    obtain ⟨D', hD', hD'sub, hD'Z, hD'V⟩ := half_replace h1 h2 h3 h4 h5 h7 h8 hI₁.1 hI₂ hf hDJ
      hVc hVnc hVJ₁ hVJ₂ (hf0 ▸ hOV) (hf0 ▸ hOJ₁) hJ₁V
    rw [hf0, hf1] at hD'
    refine ⟨D', hD', fun x hx => ?_, fun Z a b hZ ha hb hZJ hZV hZE => ?_, hD'V⟩
    · rcases hD'sub hx with h | ⟨Z, ⟨u, v, huv, hZ, hZJ, hZV, hZE⟩, hxZ⟩
      · exact Or.inl h
      · exact Or.inr ⟨Z, f u, f v, hZ, mem_range_self _, mem_range_self _, hZJ, hZE, hxZ,
          hD'Z Z u v huv hZ hZJ hZV hZE⟩
    · obtain ⟨u, rfl⟩ := ha
      obtain ⟨v, rfl⟩ := hb
      rcases lt_trichotomy u v with huv | huv | huv
      · exact hD'Z Z u v huv hZ hZJ hZV hZE
      · exact absurd (congrArg f huv) hZ.ne
      · exact hD'Z Z v u huv hZ.symm hZJ hZV (by rwa [pair_comm])
  have hD₁J : D₁ ⊆ J₂ := hDu ▸ subset_union_left
  have hD₂J : D₂ ⊆ J₂ := hDu ▸ subset_union_right
  obtain ⟨D₁', hD₁', hD₁'sub, hD₁'Z, hD₁'V⟩ := half D₁ hD₁ hD₁J
  obtain ⟨D₂', hD₂', hD₂'sub, hD₂'Z, hD₂'V⟩ := half D₂ hD₂ hD₂J
  -- a point of a replaced arc on `J₂` is on the original arc
  have onJ₂ : ∀ {D D' : Set S}, (∀ x ∈ D', x ∈ D ∨ ∃ Z a b, TArc a b Z ∧ a ∈ D ∧ b ∈ D ∧
      Z ⊆ J₁ ∧ Z \ {a, b} ⊆ (closure I₂)ᶜ ∧ x ∈ Z ∧ Z ⊆ D') → ∀ x ∈ D', x ∈ J₂ → x ∈ D := by
    intro D D' hsub x hx hxJ
    rcases hsub x hx with h | ⟨Z, a, b, -, ha, hb, -, hZE, hxZ, -⟩
    · exact h
    · by_contra hxD
      have hxab : x ∉ ({a, b} : Set S) := by
        rintro (h | h)
        · exact hxD (h ▸ ha)
        · exact hxD ((mem_singleton_iff.mp h) ▸ hb)
      exact disjoint_left.mp hE₂J₂ (hZE ⟨hxZ, hxab⟩) hxJ
  have hOOJ : ∀ x ∈ D₁ ∩ D₂, x ∉ J₁ := by
    intro x hx hxJ
    rw [hDi] at hx
    rcases hx with h | h
    · exact hOJ₁ (h ▸ hxJ)
    · exact hO'J₁ ((mem_singleton_iff.mp h) ▸ hxJ)
  have hint : D₁' ∩ D₂' = {O, O'} := by
    have hgen : ∀ x ∈ D₁' ∩ D₂', x ∈ J₂ → x ∈ ({O, O'} : Set S) := fun x hx hxJ => by
      rw [← hDi]
      exact ⟨onJ₂ hD₁'sub x hx.1 hxJ, onJ₂ hD₂'sub x hx.2 hxJ⟩
    apply subset_antisymm
    · intro x hx
      by_cases hxJ : x ∈ J₂
      · exact hgen x hx hxJ
      exfalso
      rcases hD₁'sub x hx.1 with h | ⟨Z₁, a₁, b₁, hZ₁, ha₁, hb₁, hZ₁J, hZ₁E, hxZ₁, hZ₁D⟩
      · exact hxJ (hD₁J h)
      rcases hD₂'sub x hx.2 with h | ⟨Z₂, a₂, b₂, hZ₂, ha₂, hb₂, hZ₂J, hZ₂E, hxZ₂, hZ₂D⟩
      · exact hxJ (hD₂J h)
      have hx₁ : x ∈ Z₁ \ {a₁, b₁} := ⟨hxZ₁, by
        rintro (h | h)
        · exact hxJ (h ▸ hD₁J ha₁)
        · exact hxJ ((mem_singleton_iff.mp h) ▸ hD₁J hb₁)⟩
      have hx₂ : x ∈ Z₂ \ {a₂, b₂} := ⟨hxZ₂, by
        rintro (h | h)
        · exact hxJ (h ▸ hD₂J ha₂)
        · exact hxJ ((mem_singleton_iff.mp h) ▸ hD₂J hb₂)⟩
      have s1 := chord_subset h1 h3 h4 h51 hI₁.1 hZ₁ hZ₂ hZ₁J hZ₂J (hD₁J ha₁) (hD₁J hb₁)
        (hE₂J₂.mono_left hZ₂E) ⟨x, hx₁, hx₂⟩
      have ha₂D : a₂ ∈ D₁' ∩ D₂' := ⟨hZ₁D (s1 hZ₂.left_mem), hZ₂D hZ₂.left_mem⟩
      have := hgen a₂ ha₂D (hD₂J ha₂)
      rw [← hDi] at this
      exact hOOJ a₂ this (hZ₂J hZ₂.left_mem)
    · rintro x (rfl | h)
      · exact ⟨hD₁'.left_mem, hD₂'.left_mem⟩
      · rw [mem_singleton_iff.mp h]; exact ⟨hD₁'.right_mem, hD₂'.right_mem⟩
  -- 4. the curve `J`
  have hsubJ : ∀ {D D' : Set S}, D ⊆ J₂ → (∀ x ∈ D', x ∈ D ∨ ∃ Z a b, TArc a b Z ∧ a ∈ D ∧
      b ∈ D ∧ Z ⊆ J₁ ∧ Z \ {a, b} ⊆ (closure I₂)ᶜ ∧ x ∈ Z ∧ Z ⊆ D') → D' ⊆ J₁ ∪ J₂ := by
    intro D D' hDJ hsub x hx
    rcases hsub x hx with h | ⟨Z, a, b, -, -, -, hZJ, -, hxZ, -⟩
    · exact Or.inr (hDJ h)
    · exact Or.inl (hZJ hxZ)
  have hfrJ : frontier V ⊆ D₁' ∪ D₂' := by
    intro z hz
    have hzc : z ∈ closure V := hz.1
    have hzV : z ∉ V := by have := hz.2; rwa [hVo.interior_eq] at this
    by_cases hzJ₂ : z ∈ J₂
    · rw [← hDu] at hzJ₂
      rcases hzJ₂ with h | h
      · exact Or.inl (hD₁'V ⟨hzc, h⟩)
      · exact Or.inr (hD₂'V ⟨hzc, h⟩)
    have hzJ₁ : z ∈ J₁ := (hfrV' z hzc hzV).resolve_right hzJ₂
    have hzE₂ : z ∈ (closure I₂)ᶜ := by
      rw [hcl₂]
      rintro (h | h)
      · exact disjoint_left.mp hclI₂ hzc h
      · exact hzJ₂ h
    obtain ⟨a, b, Z, hZ, hZJ, ha, hb, hzZ, hZJ₂⟩ :=
      chord_through h1 h3 h4 h51 hI₁.1 hJ₂c hzJ₁ hzJ₂ hy hy' hyy
    have hZE : Z \ {a, b} ⊆ (closure I₂)ᶜ := by
      have hsub : Z \ {a, b} ⊆ I₂ ∪ (closure I₂)ᶜ := fun w hw => by
        have : w ∈ J₂ᶜ := fun h => disjoint_left.mp hZJ₂ hw h
        rwa [hcompl₂] at this
      rcases hZ.isPreconnected_diff.subset_or_subset hI₂o hE₂o
        (disjoint_compl_right.mono_left subset_closure) hsub with h | h
      · exact absurd (subset_closure (h hzZ)) hzE₂
      · exact h
    have hZV : Z ⊆ closure V := chord_side h1 h2 h3 h4 h5 h6 h7 h8 hI₁.1 hE₂o hZ hZJ hZE hVo hVc
      hVsub₂ hcl₂V ⟨z, hzZ, hzc⟩
    -- the arc `C` of `J₂` from `a` to `b` not containing `O`
    have haJ₁ : a ∈ J₁ := hZJ hZ.left_mem
    have hbJ₁ : b ∈ J₁ := hZJ hZ.right_mem
    obtain ⟨C₁, C₂, hC₁, hC₂, hCi, hCu⟩ :=
      exists_two_arcs_of_isSCC h1 h3 h4 h51 hI₂.1 ha hb hZ.ne
    rw [isArc_iff_tarc h1 h3 h4 h51] at hC₁ hC₂
    obtain ⟨C, hC, hCJ, hOC⟩ : ∃ C, TArc a b C ∧ C ⊆ J₂ ∧ O ∉ C := by
      by_cases hO1 : O ∈ C₁
      · refine ⟨C₂, hC₂, hCu ▸ subset_union_right, fun hO2 => ?_⟩
        have : O ∈ C₁ ∩ C₂ := ⟨hO1, hO2⟩
        rw [hCi] at this
        rcases this with h | h
        · exact hOJ₁ (h ▸ haJ₁)
        · exact hOJ₁ ((mem_singleton_iff.mp h) ▸ hbJ₁)
      · exact ⟨C₁, hC₁, hCu ▸ subset_union_left, hO1⟩
    have hpk := pocket h1 h2 h3 h4 h5 h7 h8 hI₂ hZ hZE hC hCJ hOJ₂ hOC hVc hVnc
      (hVJ₁.mono_right hZJ) hVJ₂ hOV
    have hO'C : O' ∉ C := by
      intro h
      refine disjoint_left.mp hpk ⟨h, ?_⟩ hO'V
      rintro (e | e)
      · exact hO'J₁ (e ▸ haJ₁)
      · exact hO'J₁ ((mem_singleton_iff.mp e) ▸ hbJ₁)
    -- `C` lies on `D₁` or on `D₂`
    have hCsub : C ⊆ D₂ᶜ ∪ D₁ᶜ := by
      intro w hw
      by_contra hc
      simp only [mem_union, mem_compl_iff, not_or, not_not] at hc
      have : w ∈ D₁ ∩ D₂ := ⟨hc.2, hc.1⟩
      rw [hDi] at this
      rcases this with h | h
      · exact hOC (h ▸ hw)
      · exact hO'C ((mem_singleton_iff.mp h) ▸ hw)
    have hCe : C ∩ (D₂ᶜ ∩ D₁ᶜ) = ∅ := by
      ext w
      simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
      intro hw hw2 hw1
      have : w ∈ J₂ := hCJ hw
      rw [← hDu] at this
      rcases this with h | h
      exacts [hw1 h, hw2 h]
    rcases (isPreconnected_iff_subset_of_disjoint.mp hC.isPreconnected) _ _
      hD₂.isClosed.isOpen_compl hD₁.isClosed.isOpen_compl hCsub hCe with h | h
    · have hCD : C ⊆ D₁ := fun w hw => by
        have : w ∈ J₂ := hCJ hw
        rw [← hDu] at this
        exact this.resolve_right (h hw)
      exact Or.inl (hD₁'Z Z a b hZ (hCD hC.left_mem) (hCD hC.right_mem) hZJ hZV hZE hzZ.1)
    · have hCD : C ⊆ D₂ := fun w hw => by
        have : w ∈ J₂ := hCJ hw
        rw [← hDu] at this
        exact this.resolve_left (h hw)
      exact Or.inr (hD₂'Z Z a b hZ (hCD hC.left_mem) (hCD hC.right_mem) hZJ hZV hZE hzZ.1)
  have hJ : TSCC (D₁' ∪ D₂') := ⟨O, O', D₁', D₂', hD₁', hD₂', hint, rfl⟩
  have hJsub : D₁' ∪ D₂' ⊆ J₁ ∪ J₂ := union_subset (hsubJ hD₁J hD₁'sub) (hsubJ hD₂J hD₂'sub)
  obtain ⟨I, hI, hII⟩ := curve_of_frontier_subset h1 h2 h3 h4 h5 h7 h8 hI₁ hI₂ hVo hVc
    ⟨x₀, hx₀V⟩ hVnc hVI₁ hVI₂ hJ hJsub hfrJ
  exact ⟨D₁' ∪ D₂', I, hJsub, hI, hII⟩

/-- **Theorem 41** (p. 155). If the interiors `I₁`, `I₂` of the closed curves `J₁`, `J₂` meet, there
is a closed curve `J ⊆ J₁ + J₂` whose interior contains `I₁ + I₂`. *Axioms used: 1–8.*
**Shape change:** the axioms are made explicit. -/
theorem fa_theorem41 {J₁ J₂ I₁ I₂ : Set S} (h₁ : σ.IsInteriorOf J₁ I₁)
    (h₂ : σ.IsInteriorOf J₂ I₂) (hmeet : (I₁ ∩ I₂).Nonempty) :
    ∃ J I, J ⊆ J₁ ∪ J₂ ∧ σ.IsInteriorOf J I ∧ I₁ ∪ I₂ ⊆ I := by
  by_cases hsing : (J₁ ∩ J₂).Subsingleton
  · exact fa_theorem41_caseI h1 h2 h3 h4 h5 h7 h₁ h₂ hmeet hsing
  by_cases hs2 : J₂ ⊆ I₁ ∪ J₁
  · obtain ⟨J, I, hJ, hI, hsub⟩ := fa_theorem41_of_subset h1 h3 h4 h5 h7 h₂ h₁ hs2
    exact ⟨J, I, by rwa [union_comm], hI, by rwa [union_comm]⟩
  obtain ⟨y, hy, y', hy', hyy⟩ := Set.not_subsingleton_iff.mp hsing
  exact fa_theorem41_caseII h1 h2 h3 h4 h5 h6 h7 h8 h₁ h₂ hmeet hy hy' hyy hs2

/-- **Theorem 42** (p. 156). If the union of the interiors of a finite nonempty set `G` of closed
curves is connected, there is a closed curve on the curves of `G` whose interior contains all their
interiors. *Axioms used: 1–8.* From `fa_theorem42_of_41` (batch 139) and `fa_theorem41`.
**Shape change:** the axioms are made explicit. -/
theorem fa_theorem42 (G : Finset (Set S × Set S)) (hG : ∀ p ∈ G, σ.IsInteriorOf p.1 p.2)
    (hne : G.Nonempty) (hconn : σ.IsConn (⋃ p ∈ G, p.2)) :
    ∃ J I, σ.IsInteriorOf J I ∧ J ⊆ ⋃ p ∈ G, p.1 ∧ ∀ p ∈ G, p.2 ⊆ I :=
  fa_theorem42_of_41 h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7
    (fun _ _ _ _ h₁ h₂ hm => fa_theorem41 h1 h2 h3 h4 h5 h6 h7 h8 h₁ h₂ hm) G hG hne hconn

end Th41

end HPC.Moore
