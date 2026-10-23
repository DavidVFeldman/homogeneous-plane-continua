import HPC.Moore.FA6

/-!
# Batch 139 skeleton: Moore, F.A. §7, Theorems 35–43 (pp. 150–157)

Save as `HPC/Moore/FA7.lean` (splitting under `HPC/Moore/` is expected); add `import HPC.Moore.FA7`
at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be adjusted, each change
recorded at the statement and in the report.

Transcribed from page images at 200 dpi. Moore's section heading: "Consequences of Axioms 2–5, 8
and Theorems 5, 15, 20, 33, and 34". Theorems 44–52 are not commissioned (not used by Moore 1919 or
Moore 1925).

Conventions (as in §6):
* "closed curve", "Jordan curve" and "closed Jordan curve" all mean simple closed curve;
* "within `J`" means in the interior of `J`, and "without `J`" means in the exterior of that
  interior. Batch 138's `IsInteriorOf` and `existsUnique_interior` give "the interior";
* "`J` encloses `O`" means `O` is within `J`.
-/

namespace HPC.Moore

open Set Topology

variable {S : Type*} {σ : Space S}

section Sec7

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **Theorem 35.** Every region contains at least one simple closed curve. **Check:** the empty
region refutes the printed form (`withEmpty`); `hne` added. -/
theorem fa_theorem35 {R : Set S} (hR : R ∈ σ.region) (hne : R.Nonempty) :
    ∃ J ⊆ R, σ.IsSCC J := by
  sorry

/-- **Theorem 36.** If `O` is a point of a region `R`, there is a simple closed curve lying in `R`
and enclosing `O`. -/
theorem fa_theorem36 {R : Set S} (hR : R ∈ σ.region) {O : S} (hO : O ∈ R) :
    ∃ J ⊆ R, ∃ I, σ.IsInteriorOf J I ∧ O ∈ I := by
  sorry

/-- Unnumbered, used by Moore 1925 Theorem 19 ("whose interior contains `p` and is a subset of
`R`"): the interior in Theorem 36 lies in `R` (Theorem 21: its boundary `J` lies in `R ⊆ R′`). -/
theorem fa_theorem36_interior_subset {R : Set S} (hR : R ∈ σ.region) {O : S} (hO : O ∈ R) :
    ∃ J ⊆ R, ∃ I, σ.IsInteriorOf J I ∧ O ∈ I ∧ I ⊆ R := by
  sorry

/-- Footnote to the proof of Theorem 37 (p. 152, unnumbered): "Two arcs of a closed curve can have
no point in common unless one of them contains an endpoint of the other one." -/
theorem fa_arcs_of_scc_meet {C : Set S} (hC : σ.IsSCC C) {A B A' B' : S} {K K' : Set S}
    (hK : σ.IsArc A B K) (hKC : K ⊆ C) (hK' : σ.IsArc A' B' K') (hK'C : K' ⊆ C)
    (hmeet : (K ∩ K').Nonempty) : A ∈ K' ∨ B ∈ K' ∨ A' ∈ K ∨ B' ∈ K := by
  sorry

/-- **Theorem 37.** `J`, `C` closed curves; `O` on `J` but not on `C`; `A₁ ≠ A₂` common to `C` and
`J`; `A₁XA₂` an arc on `C` whose open part is within `J`. Let `T` be the arc `A₁OA₂` of `J`, with
`T₁ = A₁O` and `T₂ = A₂O` its intervals. Then there are `O₁, O₂ ≠ O` with
(1) `O₁ ∈ T₁`, `O₂ ∈ T₂`;
(2) an arc `O₁YO₂` on `C` whose open part is within `J`;
(3) if `B₁ ∈ O₁O`, `B₂ ∈ O₂O` are joined by an arc on `C` whose open part is within `J`, then
`B₁ = O₁` and `B₂ = O₂`. -/
theorem fa_theorem37 {J C I : Set S} (hJ : σ.IsInteriorOf J I) (hC : σ.IsSCC C) {O A₁ A₂ : S}
    (hO : O ∈ J) (hOC : O ∉ C) (hA₁ : A₁ ∈ C ∩ J) (hA₂ : A₂ ∈ C ∩ J) (hA : A₁ ≠ A₂)
    {X : Set S} (hX : σ.IsArc A₁ A₂ X) (hXC : X ⊆ C) (hXI : openArc A₁ A₂ X ⊆ I)
    {T T₁ T₂ : Set S} (hT : σ.IsArc A₁ A₂ T) (hTJ : T ⊆ J) (hOT : O ∈ T)
    (hT₁ : σ.IsArc A₁ O T₁ ∧ T₁ ⊆ T) (hT₂ : σ.IsArc A₂ O T₂ ∧ T₂ ⊆ T) :
    ∃ O₁ O₂ : S, O₁ ≠ O ∧ O₂ ≠ O ∧ O₁ ∈ T₁ ∧ O₂ ∈ T₂ ∧
      (∃ Y, σ.IsArc O₁ O₂ Y ∧ Y ⊆ C ∧ openArc O₁ O₂ Y ⊆ I) ∧
      ∀ B₁ B₂ : S, ∀ U₁ U₂ : Set S, σ.IsArc O₁ O U₁ → U₁ ⊆ T₁ → σ.IsArc O₂ O U₂ → U₂ ⊆ T₂ →
        B₁ ∈ U₁ → B₂ ∈ U₂ →
        (∃ Z, σ.IsArc B₁ B₂ Z ∧ Z ⊆ C ∧ openArc B₁ B₂ Z ⊆ I) → B₁ = O₁ ∧ B₂ = O₂ := by
  sorry

/-- **Theorem 38.** The exterior analogue of Theorem 37 (p. 153). As printed: `J`, `C` closed curves,
`O` on `J` but not on `C`, `A₁ ≠ A₂` common to `C` and `J`, `A₁XA₂` an arc on `C` such that the
interior of the closed curve `A₁XA₂OA₁` is a subset of the exterior of `J`. Then there are
`O₁, O₂ ≠ O` such that (1) on the interval `O₁OO₂` of `J`, `O` is between `O₁` and `A₂` and between
`O₂` and `A₁`; (2) there is on `C` an arc `O₁YO₂` such that its open part and the interior of
`O₁YO₂OO₁` lie in the exterior of `J`; (3) if the exterior of `J` contains the open arc `B₁ZB₂` and
the interior of `B₁ZB₂OB₁`, where `B₁`, `B₂` are on the arc of `J` from `O₁` to `O₂` not containing
`O`, and `B₁ZB₂` is an arc of `C`, then `B₁ = O₁` and `B₂ = O₂`.
**The shape is left to you.** Model it on `fa_theorem37`, and record how you resolved
"`A₁XA₂OA₁`" (which arc of `J` from `A₂` to `A₁` through `O`) and the reading of (1) and (3).
(Proof: "analogous", none printed.) -/
theorem fa_theorem38 : True := by
  sorry

/-- **Theorem 39.** If `O` is on the closed curve `J`, every point not on `J` can be joined to `O` by
an arc having no point except `O` in common with `J`. -/
theorem fa_theorem39 {J : Set S} (hJ : σ.IsSCC J) {O P : S} (hO : O ∈ J) (hP : P ∉ J) :
    ∃ K, σ.IsArc P O K ∧ K ∩ J = {O} := by
  sorry

/-- **Theorem 40.** If `A`, `B` are two points of a closed curve `J`, they can be joined by arcs `AXB`
and `AYB` with the open arc `AXB` within `J` and the open arc `AYB` without `J`. (**No proof
printed.** Theorems 45 and 46 and Moore 1919 use it.) -/
theorem fa_theorem40 {J I : Set S} (hJ : σ.IsInteriorOf J I) {A B : S} (hA : A ∈ J) (hB : B ∈ J)
    (hAB : A ≠ B) :
    ∃ X Y : Set S, σ.IsArc A B X ∧ σ.IsArc A B Y ∧ openArc A B X ⊆ I ∧
      openArc A B Y ⊆ σ.ext I := by
  sorry

/-- **Theorem 41.** If `J₁`, `J₂` are closed curves whose interiors `I₁`, `I₂` have a point `O` in
common, there is a closed curve `J ⊆ J₁ ∪ J₂` whose interior `I` contains `I₁ ∪ I₂`. (Proof
sketched; the final step is "It may be proved that `J` is a closed curve satisfying the
requirements of Theorem 41", with no proof given.) -/
theorem fa_theorem41 {J₁ J₂ I₁ I₂ : Set S} (h₁ : σ.IsInteriorOf J₁ I₁) (h₂ : σ.IsInteriorOf J₂ I₂)
    (hmeet : (I₁ ∩ I₂).Nonempty) :
    ∃ J I, J ⊆ J₁ ∪ J₂ ∧ σ.IsInteriorOf J I ∧ I₁ ∪ I₂ ⊆ I := by
  sorry

/-- **Theorem 42.** If the union of the interiors of a finite set `G` of closed curves is connected,
there is a closed curve `J` whose points all lie on curves of `G` and whose interior contains the
interiors of all the curves of `G`. (**No proof printed**; induction on `G` by Theorem 41 is the
evident route. Check that connectedness of the union gives an ordering in which each new interior
meets the previous union.) -/
theorem fa_theorem42 (G : Finset (Set S × Set S)) (hG : ∀ p ∈ G, σ.IsInteriorOf p.1 p.2)
    (hne : G.Nonempty) (hconn : σ.IsConn (⋃ p ∈ G, p.2)) :
    ∃ J I, σ.IsInteriorOf J I ∧ J ⊆ ⋃ p ∈ G, p.1 ∧ ∀ p ∈ G, p.2 ⊆ I := by
  sorry

/-- **Theorem 43.** If the point `O` of the closed curve `J` is within every curve of the finite set
`G` of closed curves, and the interior of `J` is not a subset of the interior of any curve of `G`,
then there are curves `J₁`, `J₂` containing `O` such that (1) every point of `J₁` or `J₂` belongs to
`J` or to some curve of `G`; (2) every point within `J₁` is without `J`, and every point within `J₂`
is within `J`; (3) every point within `J₁` or within `J₂` is within every curve of `G`.
(**No proof printed.**) **Check:** the empty `G` makes the hypotheses hold vacuously; decide whether
`G` must be nonempty. -/
theorem fa_theorem43 {J I : Set S} (hJ : σ.IsInteriorOf J I) {O : S} (hO : O ∈ J)
    (G : Finset (Set S × Set S)) (hG : ∀ p ∈ G, σ.IsInteriorOf p.1 p.2)
    (hOG : ∀ p ∈ G, O ∈ p.2) (hnot : ∀ p ∈ G, ¬ I ⊆ p.2) :
    ∃ J₁ I₁ J₂ I₂, σ.IsInteriorOf J₁ I₁ ∧ σ.IsInteriorOf J₂ I₂ ∧ O ∈ J₁ ∧ O ∈ J₂ ∧
      J₁ ∪ J₂ ⊆ J ∪ ⋃ p ∈ G, p.1 ∧ I₁ ⊆ σ.ext I ∧ I₂ ⊆ I ∧
      ∀ p ∈ G, I₁ ∪ I₂ ⊆ p.2 := by
  sorry

end Sec7

end HPC.Moore
