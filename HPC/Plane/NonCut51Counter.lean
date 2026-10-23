import HPC.Plane.NonCut51

/-!
# Batch 94, §3 Q2: the reverse inclusion fails

`bingElt_subtype_subset` (`HPC/Plane/NonCut51.lean`) proves that the element of `x` computed in a
subcontinuum `S'` lies in the element of `x` computed in `S`. The reverse inclusion
`bingElt (x : S) ∩ S' ⊆ (element of x in S')` is false. The simplest witness is on batch 92's
example `S₀` (which satisfies `BingS`, `bingS_S₀`), with `S'` the bar `B = [0, 2] × {0}` and
`x = p₀ = (1/2, 0)`: in `S₀` the element of `p₀` is the whole bar (batch 93, `bingElt_bar`), while
in the arc `B` the continuum `[0, 3/4] × {0}` contains `[0, 5/8] × {0}` interiorly, which contains
`p₀` interiorly, so the element of `p₀` in `B` misses `q₀ = (1, 0)`.
-/

namespace HPC.Plane.Counter92

open Set Topology

/-- The bar `B = [0, 2] × {0}` of `S₀`. -/
def barSet : Set S₀ := {z | z.1.2 = 0}

/-- The initial segment `[0, m] × {0}` of the bar. -/
def barLe (m : ℝ) : Set S₀ := {z | z.1.2 = 0 ∧ z.1.1 ≤ m}

lemma isContinuum_barLe {m : ℝ} (hm : 0 ≤ m) : Fold.Q78.IsContinuum (barLe m) := by
  have hcl : IsClosed (barLe m) :=
    (isClosed_eq continuous_hgt continuous_const).inter (isClosed_le continuous_xc continuous_const)
  exact ⟨hcl.isCompact, ⟨⟨bar (x := 0) le_rfl (by norm_num), by simp [bar], by simpa [bar]⟩,
    (crit_bar_le m).isPreconnected⟩⟩

lemma barLe_two : barLe 2 = barSet := by
  ext z
  exact ⟨fun h => h.1, fun h => ⟨h, x_le_two z⟩⟩

lemma isContinuum_barSet : Fold.Q78.IsContinuum barSet :=
  barLe_two ▸ isContinuum_barLe (by norm_num)

/-- In the bar, as a subcontinuum of `S₀`, the element of `p₀` misses `q₀`. -/
lemma q₀_notMem_bingElt_bar :
    haveI : CompactSpace barSet := isCompact_iff_compactSpace.mp isContinuum_barSet.1
    (⟨q₀, by simp [barSet, q₀, bar]⟩ : barSet) ∉
      bingElt (⟨p₀, by simp [barSet, p₀, bar]⟩ : barSet) := by
  haveI : CompactSpace barSet := isCompact_iff_compactSpace.mp isContinuum_barSet.1
  have hsub : ∀ m, barLe m ∩ barSet = barLe m := fun m => inter_eq_left.mpr fun z hz => hz.1
  have c : ∀ {m : ℝ}, 0 ≤ m → Fold.Q78.IsContinuum (((↑) : barSet → S₀) ⁻¹' barLe m) :=
    fun hm => isContinuum_preimage_val (by rw [hsub]; exact isContinuum_barLe hm)
  have cx : Continuous fun z : barSet => (z : S₀).1.1 := continuous_xc.comp continuous_subtype_val
  -- `{x < m}` is an open subset of the preimage of `barLe m`
  have hopen : ∀ m : ℝ, {z : barSet | (z : S₀).1.1 < m} ⊆
      interior (((↑) : barSet → S₀) ⁻¹' barLe m) := fun m =>
    interior_maximal (fun z hz => ⟨z.2, le_of_lt hz⟩) (isOpen_lt cx continuous_const)
  have hN : ContainsNested (((↑) : barSet → S₀) ⁻¹' barLe (3 / 4))
      (⟨p₀, by simp [barSet, p₀, bar]⟩ : barSet) := by
    refine ⟨_, c (m := 5 / 8) (by norm_num), fun z hz => hopen _ ?_, hopen _ ?_⟩
    · show (z : S₀).1.1 < 3 / 4
      have : (z : S₀).1.1 ≤ 5 / 8 := hz.2
      linarith
    · show p₀.1.1 < 5 / 8
      simp [p₀, bar]; norm_num
  intro h
  have := bingElt_subset (c (m := 3 / 4) (by norm_num)) hN h
  have h2 : q₀.1.1 ≤ 3 / 4 := this.2
  simp [q₀, bar] at h2
  norm_num at h2

/-- **The reverse of `bingElt_subtype_subset` fails** (§3 Q2). On `S₀` (a space satisfying
`BingS`, `bingS_S₀`) with the subcontinuum `S' = [0, 2] × {0}` and `x = (1/2, 0)`, the element of
`x` in `S` meets `S'` in a point outside the element of `x` computed in `S'`. -/
theorem bingElt_subtype_reverse_false :
    haveI : CompactSpace barSet := isCompact_iff_compactSpace.mp isContinuum_barSet.1
    ¬ bingElt p₀ ∩ barSet ⊆
      ((↑) : barSet → S₀) '' bingElt (⟨p₀, by simp [barSet, p₀, bar]⟩ : barSet) := by
  intro h
  have hq : q₀ ∈ bingElt p₀ ∩ barSet := by
    have hq0 : q₀.1.2 = 0 := by simp [q₀, bar]
    refine ⟨?_, hq0⟩
    rw [bingElt_bar (b := p₀) (by simp [p₀, bar])]
    exact hq0
  obtain ⟨z, hz, hzq⟩ := h hq
  have : z = ⟨q₀, by simp [barSet, q₀, bar]⟩ := Subtype.ext hzq
  exact q₀_notMem_bingElt_bar (this ▸ hz)

end HPC.Plane.Counter92
