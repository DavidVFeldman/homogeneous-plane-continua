import HPC.Moore.M25C13

/-!
# Batch 147, item C: Moore 1925, Theorems 15–18 (p. 423)

Moore gives no proofs, only pointers: Theorems 15 and 16 are \"closely analogous\" to F.A. Theorems 24
and 25, and Theorems 17 and 18 follow by \"a method similar to\" (\"analogous to\") the proofs of F.A.
Theorems 26 and 27. Batch 138 proved F.A. 24–27 in a topological form (`Gen.th24_sub`,
`Gen.th24_ext`, `Gen.th24_disj`, `Gen.th25`, `Gen.th26`, `Gen.th27`) for a Hausdorff, locally
connected space and a family `reg` of open sets. They are applied here to the quotient with `reg`
the restricted regions; the hypotheses are supplied in `M25CInt.lean`:

| hypothesis of `Gen.th2x` | source |
|---|---|
| members open, preconnected; exteriors preconnected | Theorem 11 (`sccInterior_spec`) |
| `Th21Prop` (F.A. Theorem 21) | Theorem 11 alone (`th21Prop_restricted`) |
| `ArcConn` (F.A. Theorem 15) | `m25_fa_theorem15` (`arcConn_quot`) |
| `Ax8Prop` (Axiom 8) | Theorem 11 and `isSCCElt_iff_tscc` |
| compact closures; noncompact space | bounded point sets (`isCompact_closure_restricted`) |

So each pointer amounts to: the F.A. proof, read in the space of elements, with the F.A. axioms it
uses replaced by Theorem 11 (and Theorem 10 for the arcs of a closed curve). Moore's remark that
F.A. Theorem 21 \"may be easily proved with the help of Theorem 11\" (p. 423) is right as it stands:
`th21Prop_restricted` uses Theorem 11 and not Theorem 12.

**Theorem 18, reading of `x`, `y`.** F.A. Theorem 27 is phrased with points `C`, `D` of the two arcs
(\"`A` and `B` separate `C` and `D` on `J`\"), and its conclusions (`D` without `AXBCA`, `C` within
`AXBDA`) are about those points. Moore's 1925 statement uses the letters `x`, `y` of the arcs `pxq`,
`pyq` in the same role. The skeleton reads them as all elements of the arcs other than `p`, `q`.
The condition does not depend on the choice: `pyq − p − q` is connected and misses `pxq + pzq`, so it
lies wholly in the interior or wholly in the exterior of that curve (`diff_subset_int_or_ext`), and
likewise for `pxq − p − q`.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane Gen

variable {r : Setoid Pt}

section M25C15

variable (hG : MooreDecomp r)
include hG

omit hG in
/-- Two arcs from `p` to `q`, the open part of the second missing the first, meet in `{p, q}`. -/
theorem inter_eq_pair_of_diff {p q : Quotient r} {X Z : Set (Quotient r)} (hX : IsArcElt p q X)
    (hZ : IsArcElt p q Z) (h : ∀ z ∈ Z \ {p, q}, z ∉ X) : X ∩ Z = {p, q} := by
  apply subset_antisymm
  · rintro z ⟨hzX, hzZ⟩
    by_contra hz
    exact h z ⟨hzZ, hz⟩ hzX
  · rintro z (rfl | rfl)
    · exact ⟨hX.2.2.2.2.1, hZ.2.2.2.2.1⟩
    · exact ⟨hX.2.2.2.2.2.1, hZ.2.2.2.2.2.1⟩

/-- `TInt` for `sccInterior (X ∪ Z)`, with the union written `Z ∪ X`. -/
theorem tInt_comm {X Z : Set (Quotient r)} (h : IsSCCElt (X ∪ Z)) :
    TInt (restrictedRegions r) (Z ∪ X) (sccInterior (X ∪ Z)) := by
  have := tInt_sccInterior hG h
  rw [union_comm X Z] at this ⊢
  exact this

/-- The open part of an arc missing a closed curve lies in its interior or in its exterior. -/
theorem diff_subset_int_or_ext {p q : Quotient r} {Y J : Set (Quotient r)} (hJ : IsSCCElt J)
    (hY : IsArcElt p q Y) (hYJ : ∀ y ∈ Y \ {p, q}, y ∉ J) :
    Y \ {p, q} ⊆ sccInterior J ∨ Y \ {p, q} ⊆ sccExterior J := by
  haveI := t2Space_quot hG
  obtain ⟨hIo, -, -, -, hEo, -, -, -, hdis, hu⟩ := sccInterior_spec hG hJ
  refine ((isArcElt_iff_tarc hG).1 hY).isPreconnected_diff.subset_or_subset hIo hEo hdis ?_
  rw [hu]; exact hYJ

/-- The setting of Theorems 15, 16: the curves `J₁ = pxq + pzq`, `J₂ = pyq + pzq`. -/
theorem setting_int {p q : Quotient r} {X Y Z : Set (Quotient r)} (hX : IsArcElt p q X)
    (hY : IsArcElt p q Y) (hZ : IsArcElt p q Z) (hXY : X ∩ Y = {p, q})
    (hZJ : ∀ z ∈ Z \ {p, q}, z ∉ X ∪ Y) :
    X ∩ Z = {p, q} ∧ Y ∩ Z = {p, q} ∧ IsSCCElt (X ∪ Y) ∧ IsSCCElt (X ∪ Z) ∧
      IsSCCElt (Y ∪ Z) := by
  have hXZ := inter_eq_pair_of_diff hX hZ fun z hz hzX => hZJ z hz (Or.inl hzX)
  have hYZ := inter_eq_pair_of_diff hY hZ fun z hz hzY => hZJ z hz (Or.inr hzY)
  exact ⟨hXZ, hYZ, isSCCElt_union hG hX hY hXY, isSCCElt_union hG hX hZ hXZ,
    isSCCElt_union hG hY hZ hYZ⟩

/-- **Theorem 15** (p. 423). `pxq`, `pyq` arcs from `p` to `q` with only `p`, `q` in common,
`J = pxq + pyq`, `R` its interior, `pzq` an arc all of whose elements except `p`, `q` lie in `R`;
`J₁ = pxq + pzq`, `J₂ = pyq + pzq`. Then (1) the interior `R₁` of `J₁` is a subset of `R`; (2) `pyq`
is, except for `p` and `q`, in the exterior of `R₁`; (3) `R₁` and the interior `R₂` of `J₂` are
disjoint. (\"Closely analogous\" to F.A. Theorem 24.) -/
theorem m25_theorem15 {p q : Quotient r} {X Y Z : Set (Quotient r)} (hX : IsArcElt p q X)
    (hY : IsArcElt p q Y) (hZ : IsArcElt p q Z) (hXY : X ∩ Y = {p, q})
    (hZR : Z \ {p, q} ⊆ sccInterior (X ∪ Y)) :
    sccInterior (X ∪ Z) ⊆ sccInterior (X ∪ Y) ∧ Y \ {p, q} ⊆ sccExterior (X ∪ Z) ∧
      Disjoint (sccInterior (X ∪ Z)) (sccInterior (Y ∪ Z)) := by
  haveI := t2Space_quot hG
  obtain ⟨-, -, hJ, hJ₁, hJ₂⟩ := setting_int hG hX hY hZ hXY fun z hz => (hZR hz).1
  have hR := tInt_sccInterior hG hJ
  have hR₁ := tInt_comm hG hJ₁
  have hR₂ := tInt_comm hG hJ₂
  have hpJ : p ∈ X ∪ Y := Or.inl hX.2.2.2.2.1
  have hqJ : q ∈ X ∪ Y := Or.inl hX.2.2.2.2.2.1
  have h21 := th21Prop_restricted hG
  have hopen := isOpen_restricted hG
  have hR₁R := th24_sub h21 hR hpJ hqJ subset_union_left hZR hR₁
  have hR₂R := th24_sub h21 hR hpJ hqJ subset_union_right hZR hR₂
  have hext := th24_ext hopen hR subset_union_right hXY hZR hR₁ hR₁R
  refine ⟨hR₁R, by rwa [compl_closure_sccInterior hG hJ₁] at hext, ?_⟩
  exact th24_disj hopen (isPreconnected_restricted hG) hR subset_union_left hR₁ hR₂ hR₂R hext
    ((isArcElt_iff_tarc hG).1 hY).nonempty_diff

/-- **Theorem 16** (p. 423). Under the hypothesis of Theorem 15, `R` is the sum of `R₁`, `R₂` and
`pzq − (p + q)`. (\"Closely parallel\" to F.A. Theorem 25.) -/
theorem m25_theorem16 {p q : Quotient r} {X Y Z : Set (Quotient r)} (hX : IsArcElt p q X)
    (hY : IsArcElt p q Y) (hZ : IsArcElt p q Z) (hXY : X ∩ Y = {p, q})
    (hZR : Z \ {p, q} ⊆ sccInterior (X ∪ Y)) :
    sccInterior (X ∪ Y) = sccInterior (X ∪ Z) ∪ sccInterior (Y ∪ Z) ∪ (Z \ {p, q}) := by
  haveI := t2Space_quot hG
  haveI := locallyConnectedSpace_quot hG
  obtain ⟨-, -, hJ, hJ₁, hJ₂⟩ := setting_int hG hX hY hZ hXY fun z hz => (hZR hz).1
  have h := th25 (isOpen_restricted hG) (isPreconnected_restricted hG) (th21Prop_restricted hG)
    (arcConn_quot hG) (ax8Prop_restricted hG) (ext_restricted hG) (tInt_sccInterior hG hJ)
    ((isArcElt_iff_tarc hG).1 hX) ((isArcElt_iff_tarc hG).1 hY) hXY rfl
    ((isArcElt_iff_tarc hG).1 hZ) hZR (tInt_comm hG hJ₁) (tInt_comm hG hJ₂)
  rw [h]
  ext x; simp only [mem_union]; tauto

/-- **Theorem 17** (p. 423). Three arcs from `p` to `q`, no two with a common element except `p`,
`q`: the interiors of the three closed curves they form in pairs are not mutually exclusive. (\"A method
similar to that used in F.A. to prove Theorem 26.\") -/
theorem m25_theorem17 {p q : Quotient r} {X Y Z : Set (Quotient r)} (hX : IsArcElt p q X)
    (hY : IsArcElt p q Y) (hZ : IsArcElt p q Z) (hXY : X ∩ Y = {p, q}) (hXZ : X ∩ Z = {p, q})
    (hYZ : Y ∩ Z = {p, q}) :
    ¬ (Disjoint (sccInterior (X ∪ Y)) (sccInterior (X ∪ Z)) ∧
      Disjoint (sccInterior (X ∪ Y)) (sccInterior (Y ∪ Z)) ∧
      Disjoint (sccInterior (X ∪ Z)) (sccInterior (Y ∪ Z))) := by
  haveI := t2Space_quot hG
  haveI := locallyConnectedSpace_quot hG
  have h := th26 (isOpen_restricted hG) (isPreconnected_restricted hG) (th21Prop_restricted hG)
    (arcConn_quot hG) (ax8Prop_restricted hG) (ext_restricted hG)
    (isCompact_closure_restricted hG) (not_isCompact_univ_quot hG)
    ((isArcElt_iff_tarc hG).1 hX) ((isArcElt_iff_tarc hG).1 hY) ((isArcElt_iff_tarc hG).1 hZ)
    hXY hXZ hYZ (tInt_sccInterior hG (isSCCElt_union hG hX hZ hXZ))
    (tInt_sccInterior hG (isSCCElt_union hG hX hY hXY))
    (tInt_sccInterior hG (isSCCElt_union hG hY hZ hYZ))
  rintro ⟨h1, h2, h3⟩
  rcases h with h | h | h
  · exact (not_disjoint_iff_nonempty_inter.2 h) h1.symm
  · exact (not_disjoint_iff_nonempty_inter.2 h) h3
  · exact (not_disjoint_iff_nonempty_inter.2 h) h2

/-- **Theorem 18** (pp. 423–424). `pxq`, `pyq` arcs with only their extremities in common, `J` the
curve they form, `pzq` an arc lying, except for its extremities, in the exterior of `J`;
`J₁ = pxq + pzq`, `J₂ = pyq + pzq`. Then \"(1) either `y` is without `J₁` … or `x` is in the exterior of
`J₂`, (2) if `y` is without `J₁` then `x` is in the interior of `J₂` and the interior of `J₂` is the sum
of the interior of `J`, the interior of `J₁` and the set of elements `pxq − (p + q)`\".

*Reading.* `x` and `y` are not introduced; they are read as the arcs' elements other than `p`, `q`
(all of them; the condition does not depend on the choice, see the module docstring), and
\"without\" as \"in the exterior of\". (\"A method analogous to that used in F.A. to prove Theorem
27.\") -/
theorem m25_theorem18 {p q : Quotient r} {X Y Z : Set (Quotient r)} (hX : IsArcElt p q X)
    (hY : IsArcElt p q Y) (hZ : IsArcElt p q Z) (hXY : X ∩ Y = {p, q})
    (hZE : Z \ {p, q} ⊆ sccExterior (X ∪ Y)) :
    (Y \ {p, q} ⊆ sccExterior (X ∪ Z) ∨ X \ {p, q} ⊆ sccExterior (Y ∪ Z)) ∧
      (Y \ {p, q} ⊆ sccExterior (X ∪ Z) →
        X \ {p, q} ⊆ sccInterior (Y ∪ Z) ∧
          sccInterior (Y ∪ Z) = sccInterior (X ∪ Y) ∪ sccInterior (X ∪ Z) ∪ (X \ {p, q})) := by
  haveI := t2Space_quot hG
  haveI := locallyConnectedSpace_quot hG
  obtain ⟨hXZ, hYZ, hJ, hJ₁, hJ₂⟩ := setting_int hG hX hY hZ hXY fun z hz => (hZE hz).1
  have hX' := (isArcElt_iff_tarc hG).1 hX
  have hY' := (isArcElt_iff_tarc hG).1 hY
  have hZE' : Z \ {p, q} ⊆ (closure (sccInterior (X ∪ Y)))ᶜ := by
    rw [compl_closure_sccInterior hG hJ]; exact hZE
  have h27 : ∀ C ∈ X \ {p, q}, ∀ D ∈ Y \ {p, q}, _ := fun C hC D hD =>
    th27 (isOpen_restricted hG) (isPreconnected_restricted hG) (th21Prop_restricted hG)
      (arcConn_quot hG) (ax8Prop_restricted hG) (ext_restricted hG)
      (isCompact_closure_restricted hG) (not_isCompact_univ_quot hG) (tInt_sccInterior hG hJ)
      hX' hY' hXY rfl hC hD ((isArcElt_iff_tarc hG).1 hZ) hZE' (tInt_comm hG hJ₁)
      (tInt_comm hG hJ₂)
  rw [compl_closure_sccInterior hG hJ₁, compl_closure_sccInterior hG hJ₂] at h27
  -- each open arc lies wholly inside or wholly outside the other curve
  have hYside := diff_subset_int_or_ext hG hJ₁ hY fun y hy hyJ =>
    hyJ.elim (fun h => hy.2 (hXY ▸ ⟨h, hy.1⟩)) (fun h => hy.2 (hYZ ▸ ⟨hy.1, h⟩))
  have hXside := diff_subset_int_or_ext hG hJ₂ hX fun y hy hyJ =>
    hyJ.elim (fun h => hy.2 (hXY ▸ ⟨hy.1, h⟩)) (fun h => hy.2 (hXZ ▸ ⟨hy.1, h⟩))
  obtain ⟨C, hC⟩ := hX'.nonempty_diff
  obtain ⟨D, hD⟩ := hY'.nonempty_diff
  have hdis₁ := (sccInterior_spec hG hJ₁).2.2.2.2.2.2.2.2.1
  have hdis₂ := (sccInterior_spec hG hJ₂).2.2.2.2.2.2.2.2.1
  refine ⟨?_, fun hYE => ?_⟩
  · rcases (h27 C hC D hD).1 with h | h
    · left
      exact hYside.resolve_left fun hsub => disjoint_left.1 hdis₁ (hsub hD) h
    · right
      exact hXside.resolve_left fun hsub => disjoint_left.1 hdis₂ (hsub hC) h
  · have hall : ∀ C ∈ X \ {p, q}, C ∈ sccInterior (Y ∪ Z) := fun C hC =>
      ((h27 C hC D hD).2 (hYE hD)).1
    refine ⟨hall, ?_⟩
    rw [((h27 C hC D hD).2 (hYE hD)).2]
    ext x; simp only [mem_union]; tauto

end M25C15

end HPC.Moore
