import HPC.Span.OT82A
import HPC.Span.OT82Strip
import HPC.Span.OT82Order

/-!
# Batch 192: Theorem C II — the strip theorem; `OTThm32`; Theorem C

The skeleton of commission 192, split under `HPC/Span/`:
* `HPC/Span/OT82Parity.lean` — §3 (parity tools);
* `HPC/Span/OT82Zero.lean` — §4 (a common zero on a rectangle);
* `HPC/Span/OT82Strip.lean` — §5 (strips; `plPath`, `stripPoly`, the strip lemma);
* `HPC/Span/OT82Order.lean` — §6 (`crossing_traces_separated`);
* this file — §7 (`ot82_theorem32 : OTThm32`, `theoremC : TheoremC`).

Source: Oversteegen–Tymchatyn 1982, §2 and Theorems 3.1–3.2
(`doc/sources/oversteegen-tymchatyn1982.pdf`; transcriptions in `doc/notes/ot82.md`). Route:
commission 192, which replaces Lemma 2.3, Lemma 2.4, Remark 2.5 and the zero-set continua of
Theorem 2.7 by a common-zero lemma and chains.

Nothing in this file or the four files above is `sorry`.
-/

namespace HPC.Span

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Hagopian

/-! ## §7. Theorem 3.2 (strip form) and Theorem C (commission §7) -/

/-- If an uncountable set is covered by countably many pieces, one piece is uncountable. -/
theorem exists_not_countable_of_cover {ι : Type*} {J : Set ι} (hJ : ¬ J.Countable)
    {P : ι → ℕ → Prop} (hP : ∀ i ∈ J, ∃ n, P i n) : ∃ n, ¬ {i ∈ J | P i n}.Countable := by
  by_contra h
  push_neg at h
  refine hJ ((countable_iUnion h).mono fun i hi => ?_)
  obtain ⟨n, hn⟩ := hP i hi
  exact mem_iUnion.2 ⟨n, hi, hn⟩

/-- Two disjoint sets, one compact and the other closed, are a positive distance apart. -/
theorem exists_pos_sep {A B : Set Pt} (hA : IsCompact A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ δ > 0, ∀ u ∈ A, ∀ v ∈ B, δ ≤ dist u v := by
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · exact ⟨1, one_pos, fun u hu => hu.elim⟩
  rcases B.eq_empty_or_nonempty with rfl | hBne
  · exact ⟨1, one_pos, fun u _ v hv => hv.elim⟩
  obtain ⟨u₀, hu₀, hmin⟩ := hA.exists_isMinOn hAne (continuous_infDist_pt B).continuousOn
  refine ⟨infDist u₀ B, (hB.notMem_iff_infDist_pos hBne).1 (disjoint_left.1 hAB hu₀),
    fun u hu v hv => (hmin hu).trans (infDist_le_dist_of_mem hv)⟩

/-- Three elements of a strict total order: one lies between the other two. -/
theorem exists_between_three {ι : Type*} (R : ι → ι → Prop)
    (htot : ∀ i j, i ≠ j → R i j ∨ R j i) {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ p q r, (p = i ∨ p = j ∨ p = k) ∧ (q = i ∨ q = j ∨ q = k) ∧ (r = i ∨ r = j ∨ r = k) ∧
      R p q ∧ R q r := by
  rcases htot i j hij with h1 | h1 <;> rcases htot j k hjk with h2 | h2
  · exact ⟨i, j, k, by simp, by simp, by simp, h1, h2⟩
  · rcases htot i k hik with h3 | h3
    · exact ⟨i, k, j, by simp, by simp, by simp, h3, h2⟩
    · exact ⟨k, i, j, by simp, by simp, by simp, h3, h1⟩
  · rcases htot i k hik with h3 | h3
    · exact ⟨j, i, k, by simp, by simp, by simp, h1, h3⟩
    · exact ⟨j, k, i, by simp, by simp, by simp, h2, h3⟩
  · exact ⟨k, j, i, by simp, by simp, by simp, h2, h1⟩

/-- **O–T Theorem 3.2, strip form.** Statement as in the skeleton. Departure in the proof
(commission §7): the scale is `1/(n+1)` instead of `1/n` (so `n = 0` is allowed) and the cluster
radius is `ρ = 1/(n+1)/4` instead of `1/(16n)`; only `3ρ < 1/(n+1)` is used. -/
theorem ot82_theorem32 : OTThm32 := by
  intro Y _ _ _ X x y hX hxX ι K h hK hdisj hh
  by_contra hJ
  set J := {i | SurjSpanPos (h i '' X)}
  -- step 1: one scale
  have hstep1 : ∀ i ∈ J, ∃ n : ℕ,
      (∃ Z ⊆ (h i '' X) ×ˢ (h i '' X), Fold.Q78.IsContinuum Z ∧ Prod.fst '' Z = h i '' X ∧
        Prod.snd '' Z = h i '' X ∧ ∀ p ∈ Z, 1 / ((n : ℝ) + 1) ≤ dist p.1 p.2) ∧
      ∀ z ∈ X, (h i z).1 + 1 / ((n : ℝ) + 1) ≤ (h i y).1 := by
    intro i hi
    obtain ⟨Z, hZW, hZ, hoff, hZ1, hZ2⟩ := hi
    obtain ⟨zm, hzm, hzmin⟩ := hZ.1.exists_isMinOn hZ.2.nonempty
      (continuous_fst.dist continuous_snd).continuousOn
    have hα : 0 < dist zm.1 zm.2 := dist_pos.2 (hoff zm hzm)
    obtain ⟨xm, hxm, hxmax⟩ := hX.1.exists_isMaxOn ⟨x, hxX⟩
      ((continuous_fst.comp (hh i).1).continuousOn)
    have hg : 0 < (h i y).1 - (h i xm).1 := sub_pos.2 ((hh i).2.2.2 xm hxm)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hα hg)
    refine ⟨n, ⟨Z, hZW, hZ, hZ1, hZ2, fun p hp => ?_⟩, fun z hz => ?_⟩
    · exact (hn.le.trans (min_le_left _ _)).trans (hzmin hp)
    · have h1 : (h i z).1 ≤ (h i xm).1 := hxmax hz
      have h2 := hn.le.trans (min_le_right _ _)
      linarith
  obtain ⟨n, hJ₁⟩ := exists_not_countable_of_cover hJ hstep1
  set J₁ := {i ∈ J | (∃ Z ⊆ (h i '' X) ×ˢ (h i '' X), Fold.Q78.IsContinuum Z ∧
      Prod.fst '' Z = h i '' X ∧ Prod.snd '' Z = h i '' X ∧
      ∀ p ∈ Z, 1 / ((n : ℝ) + 1) ≤ dist p.1 p.2) ∧
    ∀ z ∈ X, (h i z).1 + 1 / ((n : ℝ) + 1) ≤ (h i y).1}
  have hn1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  set ρ : ℝ := 1 / ((n : ℝ) + 1) / 4
  have hρ : 0 < ρ := by positivity
  -- step 2: clustering
  have hstep2 : ∀ i ∈ J₁, ∃ m : ℕ, ∀ c c' : Y, dist c c' < 1 / ((m : ℝ) + 1) →
      dist (h i c) (h i c') < ρ := by
    intro i _
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.1
      (CompactSpace.uniformContinuous_of_continuous (hh i).1) ρ hρ
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    exact ⟨m, fun c c' hcc' => hδ' (hcc'.trans hm)⟩
  obtain ⟨m, hJ₂⟩ := exists_not_countable_of_cover hJ₁ hstep2
  set J₂ := {i ∈ J₁ | ∀ c c' : Y, dist c c' < 1 / ((m : ℝ) + 1) → dist (h i c) (h i c') < ρ}
  obtain ⟨N, hNf, hNcov⟩ := Metric.totallyBounded_iff.1 (isCompact_univ (X := Y)).totallyBounded
    (1 / ((m : ℝ) + 1)) (by positivity)
  haveI : Fintype N := hNf.fintype
  set Φ : ι → (N → Pt) := fun i c => h i c
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (N → Pt)
  have hcov3 : ∀ i ∈ J₂, ∃ d ∈ D, dist (Φ i) d < ρ / 2 := by
    intro i _
    obtain ⟨d, hd, hdist⟩ := Metric.mem_closure_iff.1 (hDd.closure_eq ▸ mem_univ (Φ i)) (ρ / 2)
      (by positivity)
    exact ⟨d, hd, hdist⟩
  obtain ⟨J₃, hJ₃J₂, hJ₃, hJ₃close⟩ : ∃ J₃ ⊆ J₂, ¬ J₃.Countable ∧
      ∀ i ∈ J₃, ∀ j ∈ J₃, dist (Φ i) (Φ j) < ρ := by
    by_contra hno
    push_neg at hno
    have hcount : ∀ d ∈ D, {i ∈ J₂ | dist (Φ i) d < ρ / 2}.Countable := by
      intro d _
      by_contra hd
      have := hno {i ∈ J₂ | dist (Φ i) d < ρ / 2} (fun i hi => hi.1) hd
      obtain ⟨i, hi, j, hj, hij⟩ := this
      have := dist_triangle_right (Φ i) (Φ j) d
      linarith [hi.2, hj.2]
    refine hJ₂ ((hDc.biUnion hcount).mono fun i hi => ?_)
    obtain ⟨d, hd, hdist⟩ := hcov3 i hi
    exact mem_biUnion hd ⟨hi, hdist⟩
  have hclose : ∀ i ∈ J₃, ∀ j ∈ J₃, ∀ c : Y, dist (h i c) (h j c) < 3 * ρ := by
    intro i hi j hj c
    obtain ⟨c', hc'N, hcc'⟩ := mem_iUnion₂.1 (hNcov (mem_univ c))
    have h1 := (hJ₃J₂ hi).2 c c' hcc'
    have h2 := (hJ₃J₂ hj).2 c' c (by rw [dist_comm]; exact hcc')
    have h3 : dist (h i c') (h j c') < ρ :=
      lt_of_le_of_lt (dist_le_pi_dist (Φ i) (Φ j) ⟨c', hc'N⟩) (hJ₃close i hi j hj)
    calc dist (h i c) (h j c) ≤ dist (h i c) (h i c') + dist (h i c') (h j c') +
          dist (h j c') (h j c) := dist_triangle4 _ _ _ _
      _ < ρ + ρ + ρ := by gcongr
      _ = 3 * ρ := by ring
  -- step 3: order
  set R : ι → ι → Prop := fun i j =>
    ∀ z ∈ K i, ∀ z' ∈ K j, z.1 = 0 → z'.1 = 0 → z.2 < z'.2
  have htot : ∀ i j, i ≠ j → R i j ∨ R j i := fun i j hij =>
    (crossing_traces_separated zero_lt_one (hK i).1 (hK j).1 (hK i).2.1 (hK j).2.1 (hK i).2.2.1
      (hK i).2.2.2 (hK j).2.2.1 (hK j).2.2.2 (hdisj hij)).imp id
      (fun h z hz z' hz' h0 h0' => h z' hz' z hz h0' h0)
  have hxK : ∀ i, h i x ∈ K i := fun i => (hh i).2.1 (mem_range_self x)
  have hinf : J₃.Infinite := fun hfin => hJ₃ hfin.countable
  obtain ⟨i, hi, j, hj, hij⟩ := hinf.nontrivial
  obtain ⟨k, ⟨hk, hki⟩, hkj⟩ : ∃ k, (k ∈ J₃ ∧ k ≠ i) ∧ k ≠ j := by
    obtain ⟨k, hk, hk'⟩ := (hinf.diff (toFinite {i, j})).nonempty
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hk'
    exact ⟨k, ⟨hk, hk'.1⟩, hk'.2⟩
  obtain ⟨i₁, i₂, i₃, h₁, h₂, h₃, h12, h23⟩ :=
    exists_between_three R htot hij (Ne.symm hkj) (Ne.symm hki)
  have hmem : ∀ l, (l = i ∨ l = j ∨ l = k) → l ∈ J₃ := by
    rintro l (rfl | rfl | rfl) <;> assumption
  have hi₁ := hmem i₁ h₁
  have hi₂ := hmem i₂ h₂
  have hi₃ := hmem i₃ h₃
  have hne12 : i₁ ≠ i₂ := by
    rintro rfl; exact lt_irrefl _ (h12 _ (hxK i₁) _ (hxK i₁) (hh i₁).2.2.1 (hh i₁).2.2.1)
  have hne23 : i₂ ≠ i₃ := by
    rintro rfl; exact lt_irrefl _ (h23 _ (hxK i₂) _ (hxK i₂) (hh i₂).2.2.1 (hh i₂).2.2.1)
  -- step 4: the strip
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := exists_pos_sep (hK i₂).1.1 (hK i₁).1.1.isClosed
    (hdisj hne12.symm)
  obtain ⟨δ₃, hδ₃, hδ₃'⟩ := exists_pos_sep (hK i₂).1.1 (hK i₃).1.1.isClosed (hdisj hne23)
  set ρ₀ := min δ₁ δ₃
  have hρ₀ : 0 < ρ₀ := lt_min hδ₁ hδ₃
  obtain ⟨η₁, hη₁, hη₁'⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous (hh i₁).1) ρ₀ hρ₀
  obtain ⟨η₃, hη₃, hη₃'⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous (hh i₃).1) ρ₀ hρ₀
  obtain ⟨s, c, hc0, hcs, -, hcd⟩ := exists_eps_chain (isPreconnected_univ (α := Y))
    (lt_min hη₁ hη₃) (mem_univ x) (mem_univ y)
  have hxy : x ≠ y := by
    rintro rfl; exact lt_irrefl _ ((hh i₁).2.2.2 x hxX)
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · exact absurd (hc0.symm.trans hcs) hxy
    · exact h
  set a : Fin (s + 1) → Pt := fun l => h i₁ (c l)
  set b : Fin (s + 1) → Pt := fun l => h i₃ (c l)
  set W := h i₂ '' X
  have hWK : W ⊆ K i₂ := fun _ ⟨z, _, hz⟩ => hz ▸ (hh i₂).2.1 (mem_range_self z)
  have hstripK : ∀ l, ∀ z ∈ K l, 0 ≤ z.1 := fun l z hz => ((hK l).2.1 hz).1.1
  have hfinExt : ∀ (l : ι) (q : ℕ), q ≤ s →
      finExt (fun r : Fin (s + 1) => h l (c r)) q = h l (c q) := fun l q hq => by
    rw [finExt_of_le _ hq]
  -- the path through the `h l (c q)` stays within `ρ₀` of `K l`
  have hpathK : ∀ l, (∀ c c' : Y, dist c c' < min η₁ η₃ → dist (h l c) (h l c') < ρ₀) →
      ∀ t ∈ Icc (0 : ℝ) 1, ∃ v ∈ K l,
        dist (plPath (fun r : Fin (s + 1) => h l (c r)) t) v < ρ₀ := by
    intro l hl t ht
    obtain ⟨q, hq, μ, hμ, -, hpl⟩ := plPath_eq_piece hs ht
    rw [hpl, hfinExt l q hq.le, hfinExt l (q + 1) hq]
    refine ⟨h l (c q), (hh l).2.1 (mem_range_self _), lt_of_le_of_lt
      (dist_le_of_mem_segment_left ⟨1 - μ, μ, by linarith [hμ.2], hμ.1, by ring, rfl⟩)
      (hl _ _ (hcd q hq))⟩
  have hl₁ : ∀ c c' : Y, dist c c' < min η₁ η₃ → dist (h i₁ c) (h i₁ c') < ρ₀ :=
    fun c c' hcc' => hη₁' (lt_of_lt_of_le hcc' (min_le_left _ _))
  have hl₃ : ∀ c c' : Y, dist c c' < min η₁ η₃ → dist (h i₃ c) (h i₃ c') < ρ₀ :=
    fun c c' hcc' => hη₃' (lt_of_lt_of_le hcc' (min_le_right _ _))
  -- step 5: the hypotheses of the strip lemma
  have ha0 : a 0 = h i₁ x := by simp only [a, Fin.val_zero, hc0]
  have hb0 : b 0 = h i₃ x := by simp only [b, Fin.val_zero, hc0]
  have haL : a (Fin.last s) = h i₁ y := by simp only [a, Fin.val_last, hcs]
  have hbL : b (Fin.last s) = h i₃ y := by simp only [b, Fin.val_last, hcs]
  obtain ⟨⟨Z, hZW, hZ, hZ1, hZ2, hZd⟩, hgap⟩ := (hJ₃J₂ hi₂).1.2
  obtain ⟨p, hp, hpd⟩ := strip_lemma hs a b (ε := 3 * ρ)
    (fun l => (hclose i₁ hi₁ i₃ hi₃ (c l)).le)
    (by rw [ha0]; exact (hh i₁).2.2.1) (by rw [hb0]; exact (hh i₃).2.2.1)
    (fun l => hstripK i₁ _ ((hh i₁).2.1 (mem_range_self _)))
    (fun l => hstripK i₃ _ ((hh i₃).2.1 (mem_range_self _)))
    ⟨hX.1.image (hh i₂).1, hX.2.image _ (hh i₂).1.continuousOn⟩
    (fun z hz => hstripK i₂ z (hWK hz))
    ⟨h i₂ x, mem_image_of_mem _ hxX, (hh i₂).2.2.1⟩
    (by
      intro z hz hz0
      rw [ha0, hb0]
      refine mem_openSegment_vertical (hh i₁).2.2.1 (hh i₃).2.2.1 hz0 (Or.inl ⟨?_, ?_⟩)
      · exact h12 _ (hxK i₁) _ (hWK hz) (hh i₁).2.2.1 hz0
      · exact h23 _ (hWK hz) _ (hxK i₃) hz0 (hh i₃).2.2.1)
    (by
      rw [disjoint_left]
      rintro w hw ⟨t, ht, rfl⟩
      obtain ⟨v, hv, hdv⟩ := hpathK i₁ hl₁ t ht
      have := hδ₁' _ (hWK hw) v hv
      linarith [min_le_left δ₁ δ₃])
    (by
      rw [disjoint_left]
      rintro w hw ⟨t, ht, rfl⟩
      obtain ⟨v, hv, hdv⟩ := hpathK i₃ hl₃ t ht
      have := hδ₃' _ (hWK hw) v hv
      linarith [min_le_right δ₁ δ₃])
    (by
      rw [disjoint_left, haL, hbL]
      rintro w ⟨z, hz, rfl⟩ hw
      have hg := hgap z hz
      have hy1 := fst_lt_of_dist_lt (hclose i₂ hi₂ i₁ hi₁ y)
      have hy3 := fst_lt_of_dist_lt (hclose i₂ hi₂ i₃ hi₃ y)
      obtain ⟨h1, -⟩ := mem_segment_coords hw
      have := h1.1
      have hρ' : 3 * ρ < 1 / ((n : ℝ) + 1) := by simp only [ρ]; linarith
      rcases le_total (h i₁ y).1 (h i₃ y).1 with hle | hle
      · rw [min_eq_left hle] at this; linarith
      · rw [min_eq_right hle] at this; linarith)
    Z hZW hZ hZ1 hZ2
  -- step 6: the contradiction
  have := hZd p hp
  have hρ' : 3 * ρ < 1 / ((n : ℝ) + 1) := by simp only [ρ]; linarith
  linarith

/-- **Theorem C** (Hoehn–Oversteegen 2016, p. 180): every homogeneous indecomposable plane
continuum has span zero. -/
theorem theoremC : TheoremC :=
  theoremC_of_thm32 ot82_theorem32

end HPC.Span
