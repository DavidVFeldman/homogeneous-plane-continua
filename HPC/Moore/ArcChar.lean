import Mathlib

/-!
# The arc characterization (batch 137, item E)

`isIrreducibleConnected_iff_arc`: in a metrizable space, a compact connected set `C` containing
`A ≠ B` with no connected proper subset containing both (an *irreducible continuum* between `A`
and `B`) is the image of an embedding of `[0, 1]` with `0 ↦ A`, `1 ↦ B`; and conversely.

This replaces Lennes's Theorems 2–9 (F.A. §5, p. 139: "it is possible to prove …", no proofs
printed). The proof is the standard one, carried out in the subspace `Y = C`:

* **Cut points.** If `{p}ᶜ = U ⊔ V` (open, disjoint) then `insert p U` is connected
  (`ac_insert_isPreconnected`). Hence, by irreducibility, every `p ≠ a, b` cuts `Y` into a
  connected open piece containing `a` and one containing `b` (`ac_cut`), and `{a}ᶜ`, `{b}ᶜ` are
  connected.
* **The order.** `x ≺ y` iff `x` lies in the component of `{y}ᶜ` containing `a`. This is a strict
  total order whose open rays are open sets.
* **The map to `[0, 1]`.** A countable dense subset gives, by Cantor's back-and-forth theorem, an
  order isomorphism of a countable dense suborder with `ℚ ∩ (0, 1)`; its supremum extension
  `F : Y → [0, 1]` is strictly increasing, continuous, and onto (by connectedness); a continuous
  bijection from a compact space to a Hausdorff space is a homeomorphism.

*No axioms of Moore's enter: this file uses Mathlib only.*
-/

namespace HPC.Moore

open Set Topology

section Cut

variable {Y : Type*} [TopologicalSpace Y]

/-- If `{p}ᶜ` is the union of disjoint open sets `U`, `V`, then `insert p U` is preconnected. -/
theorem ac_insert_isPreconnected [ConnectedSpace Y] {p : Y} {U V : Set Y} (hU : IsOpen U)
    (hV : IsOpen V) (hUV : Disjoint U V) (hUVp : U ∪ V = {p}ᶜ) :
    IsPreconnected (insert p U) := by
  have key : ∀ u v : Set Y, IsOpen u → IsOpen v → insert p U ⊆ u ∪ v → p ∈ u →
      (insert p U ∩ v).Nonempty → (insert p U ∩ (u ∩ v)).Nonempty := by
    intro u v hu hv hsub hpu hne
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hpv : p ∉ v := fun hpv => (eq_empty_iff_forall_notMem.mp hemp) p
      ⟨mem_insert _ _, hpu, hpv⟩
    -- `U ∩ v` is clopen
    have h1 : U ∩ v = (V ∪ u)ᶜ := by
      ext x
      simp only [mem_inter_iff, mem_compl_iff, mem_union, not_or]
      constructor
      · rintro ⟨hxU, hxv⟩
        refine ⟨fun hxV => hUV.ne_of_mem hxU hxV rfl, fun hxu => ?_⟩
        exact (eq_empty_iff_forall_notMem.mp hemp) x ⟨mem_insert_of_mem _ hxU, hxu, hxv⟩
      · rintro ⟨hxV, hxu⟩
        have hxp : x ≠ p := by rintro rfl; exact hxu hpu
        have hxU : x ∈ U := by
          have : x ∈ U ∪ V := by rw [hUVp]; exact hxp
          exact this.resolve_right hxV
        refine ⟨hxU, ?_⟩
        rcases hsub (mem_insert_of_mem _ hxU) with h | h
        · exact absurd h hxu
        · exact h
    have hclopen : IsClopen (U ∩ v) := by
      refine ⟨?_, hU.inter hv⟩
      rw [h1]; exact (hV.union hu).isClosed_compl
    rcases isClopen_iff.mp hclopen with h | h
    · obtain ⟨x, hx, hxv⟩ := hne
      rcases hx with rfl | hx
      · exact hpv hxv
      · exact (eq_empty_iff_forall_notMem.mp h) x ⟨hx, hxv⟩
    · have : p ∈ U ∩ v := h ▸ mem_univ p
      exact hpv this.2
  intro u v hu hv hsub hu' hv'
  by_cases hpu : p ∈ u
  · exact key u v hu hv hsub hpu hv'
  · have hpv : p ∈ v := (hsub (mem_insert p U)).resolve_left hpu
    have := key v u hv hu (by rwa [union_comm]) hpv hu'
    rwa [inter_comm u v]

/-- An open set that is not preconnected splits into two disjoint nonempty open sets. -/
theorem ac_split_of_not_isPreconnected {s : Set Y} (hs : IsOpen s) (h : ¬ IsPreconnected s) :
    ∃ U V : Set Y, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = s ∧ U.Nonempty ∧ V.Nonempty := by
  simp only [IsPreconnected, not_forall, exists_prop] at h
  obtain ⟨u, v, hu, hv, hsub, hsu, hsv, hemp⟩ := h
  refine ⟨s ∩ u, s ∩ v, hs.inter hu, hs.inter hv, ?_, ?_, hsu, hsv⟩
  · rw [Set.disjoint_left]
    rintro x ⟨hxs, hxu⟩ ⟨-, hxv⟩
    exact hemp ⟨x, hxs, hxu, hxv⟩
  · rw [← inter_union_distrib_left]; exact inter_eq_left.mpr hsub

variable [ConnectedSpace Y] {a b : Y}

/-- The basic contradiction: if `{p}ᶜ = U₂ ⊔ W` (open, disjoint), `U₂ ≠ ∅` and `insert p W`
contains `a` and `b`, irreducibility fails. -/
theorem ac_G (hirr : ∀ H : Set Y, IsPreconnected H → a ∈ H → b ∈ H → H = univ) {p : Y}
    {U₂ W : Set Y} (hU₂ : IsOpen U₂) (hW : IsOpen W) (hd : Disjoint U₂ W) (hu : U₂ ∪ W = {p}ᶜ)
    (hne : U₂.Nonempty) (ha : a ∈ insert p W) (hb : b ∈ insert p W) : False := by
  have := hirr _ (ac_insert_isPreconnected hW hU₂ hd.symm (by rwa [union_comm])) ha hb
  obtain ⟨x, hx⟩ := hne
  have hxp : x ≠ p := by
    have : x ∈ U₂ ∪ W := mem_union_left _ hx
    rw [hu] at this; exact this
  have : x ∈ insert p W := this ▸ mem_univ x
  rcases this with h | h
  · exact hxp h
  · exact hd.ne_of_mem hx h rfl

variable [T1Space Y]

/-- `{b}ᶜ` is preconnected. -/
theorem ac_compl_isPreconnected (hirr : ∀ H : Set Y, IsPreconnected H → a ∈ H → b ∈ H → H = univ)
    (hab : a ≠ b) : IsPreconnected ({b}ᶜ : Set Y) := by
  by_contra h
  obtain ⟨U, V, hU, hV, hd, hu, hUn, hVn⟩ := ac_split_of_not_isPreconnected isOpen_compl_singleton h
  have ha : a ∈ U ∪ V := by rw [hu]; exact hab
  rcases ha with ha | ha
  · exact ac_G hirr hV hU hd.symm (by rwa [union_comm]) hVn (mem_insert_of_mem _ ha)
      (mem_insert _ _)
  · exact ac_G hirr hU hV hd hu hUn (mem_insert_of_mem _ ha) (mem_insert _ _)

/-- Every `p ≠ a, b` cuts `Y` into a connected open set containing `a` and a connected open set
containing `b`. -/
theorem ac_cut (hirr : ∀ H : Set Y, IsPreconnected H → a ∈ H → b ∈ H → H = univ) {p : Y}
    (hpa : p ≠ a) (hpb : p ≠ b) :
    ∃ U V : Set Y, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = {p}ᶜ ∧ IsPreconnected U ∧
      IsPreconnected V ∧ a ∈ U ∧ b ∈ V := by
  have hnot : ¬ IsPreconnected ({p}ᶜ : Set Y) := by
    intro h
    have := hirr _ h hpa.symm hpb.symm
    exact (this ▸ mem_univ p : p ∈ ({p}ᶜ : Set Y)) rfl
  obtain ⟨U, V, hU, hV, hd, hu, hUn, hVn⟩ := ac_split_of_not_isPreconnected isOpen_compl_singleton
    hnot
  have claim : ∀ U V : Set Y, IsOpen U → IsOpen V → Disjoint U V → U ∪ V = {p}ᶜ → U.Nonempty →
      V.Nonempty → a ∈ U → ∃ U V : Set Y, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = {p}ᶜ ∧
        IsPreconnected U ∧ IsPreconnected V ∧ a ∈ U ∧ b ∈ V := by
    intro U V hU hV hd hu hUn hVn ha
    have hb : b ∈ V := by
      have : b ∈ U ∪ V := by rw [hu]; exact hpb.symm
      refine this.resolve_left fun hb => ?_
      exact ac_G hirr hV hU hd.symm (by rwa [union_comm]) hVn (mem_insert_of_mem _ ha)
        (mem_insert_of_mem _ hb)
    refine ⟨U, V, hU, hV, hd, hu, ?_, ?_, ha, hb⟩
    · by_contra hc
      obtain ⟨U₁, U₂, hU₁, hU₂, hd', hu', hU₁n, hU₂n⟩ := ac_split_of_not_isPreconnected hU hc
      have sub : ∀ U₁ U₂ : Set Y, IsOpen U₁ → IsOpen U₂ → Disjoint U₁ U₂ → U₁ ∪ U₂ = U →
          U₂.Nonempty → a ∈ U₁ → False := by
        intro U₁ U₂ hU₁ hU₂ hd' hu' hU₂n ha1
        refine ac_G hirr (p := p) (W := U₁ ∪ V) hU₂ (hU₁.union hV) ?_ ?_ hU₂n
          (mem_insert_of_mem _ (mem_union_left _ ha1)) (mem_insert_of_mem _ (mem_union_right _ hb))
        · refine disjoint_union_right.mpr ⟨hd'.symm, ?_⟩
          exact hd.mono_left (hu' ▸ subset_union_right)
        · rw [← hu, ← hu']; ext x; simp only [mem_union]; tauto
      have : a ∈ U₁ ∪ U₂ := hu' ▸ ha
      rcases this with h | h
      · exact sub U₁ U₂ hU₁ hU₂ hd' hu' hU₂n h
      · exact sub U₂ U₁ hU₂ hU₁ hd'.symm (by rwa [union_comm]) hU₁n h
    · by_contra hc
      obtain ⟨V₁, V₂, hV₁, hV₂, hd', hu', hV₁n, hV₂n⟩ := ac_split_of_not_isPreconnected hV hc
      have sub : ∀ V₁ V₂ : Set Y, IsOpen V₁ → IsOpen V₂ → Disjoint V₁ V₂ → V₁ ∪ V₂ = V →
          V₂.Nonempty → b ∈ V₁ → False := by
        intro V₁ V₂ hV₁ hV₂ hd' hu' hV₂n hb1
        refine ac_G hirr (p := p) (W := U ∪ V₁) hV₂ (hU.union hV₁) ?_ ?_ hV₂n
          (mem_insert_of_mem _ (mem_union_left _ ha)) (mem_insert_of_mem _ (mem_union_right _ hb1))
        · refine disjoint_union_right.mpr ⟨?_, hd'.symm⟩
          exact (hd.mono_right (hu' ▸ subset_union_right)).symm
        · rw [← hu, ← hu']; ext x; simp only [mem_union]; tauto
      have : b ∈ V₁ ∪ V₂ := hu' ▸ hb
      rcases this with h | h
      · exact sub V₁ V₂ hV₁ hV₂ hd' hu' hV₂n h
      · exact sub V₂ V₁ hV₂ hV₁ hd'.symm (by rwa [union_comm]) hV₁n h
  have ha : a ∈ U ∪ V := by rw [hu]; exact hpa.symm
  rcases ha with ha | ha
  · exact claim U V hU hV hd hu hUn hVn ha
  · exact claim V U hV hU hd.symm (by rwa [union_comm]) hVn hUn ha

end Cut

section OrderMap

variable {Y : Type*} [TopologicalSpace Y] [ConnectedSpace Y] [LinearOrder Y]

/-- In a connected space with a linear order whose open rays are open, the order is dense. -/
theorem ac_exists_between (hIio : ∀ y : Y, IsOpen (Iio y)) (hIoi : ∀ y : Y, IsOpen (Ioi y))
    {x y : Y} (hxy : x < y) : ∃ z, x < z ∧ z < y := by
  by_contra h
  push_neg at h
  have heq : Iic x = Iio y := by
    ext z
    simp only [mem_Iic, mem_Iio]
    exact ⟨fun hz => hz.trans_lt hxy, fun hz => not_lt.mp fun hxz => (h z hxz).not_gt hz⟩
  have hclopen : IsClopen (Iic x) := ⟨by rw [← compl_Ioi]; exact (hIoi x).isClosed_compl,
    heq ▸ hIio y⟩
  rcases isClopen_iff.mp hclopen with h' | h'
  · exact (eq_empty_iff_forall_notMem.mp h') x le_rfl
  · have : y ∈ Iic x := h' ▸ mem_univ y
    exact absurd (this : y ≤ x) (not_le.mpr hxy)

/-- **The map to `[0, 1]`.** A compact connected separable space with a linear order whose open
rays are open, with least element `a` and greatest element `b ≠ a`, maps onto `[0, 1]` by a
continuous strictly increasing `F` with `F a = 0`, `F b = 1`. -/
theorem ac_exists_strictMono [TopologicalSpace.SeparableSpace Y]
    (hIio : ∀ y : Y, IsOpen (Iio y)) (hIoi : ∀ y : Y, IsOpen (Ioi y)) {a b : Y}
    (ha : ∀ x, a ≤ x) (hb : ∀ x, x ≤ b) (hab : a ≠ b) :
    ∃ F : Y → ℝ, Continuous F ∧ StrictMono F ∧ F a = 0 ∧ F b = 1 ∧ range F = Icc 0 1 := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense Y
  have hbtw : ∀ x y : Y, x < y → ∃ d ∈ D, x < d ∧ d < y := by
    intro x y hxy
    obtain ⟨z, hxz, hzy⟩ := ac_exists_between hIio hIoi hxy
    obtain ⟨d, hdD, hd⟩ := hDd.exists_mem_open ((hIoi x).inter (hIio y)) ⟨z, hxz, hzy⟩
    exact ⟨d, hdD, hd.1, hd.2⟩
  set D' : Set Y := {d ∈ D | a < d ∧ d < b} with hD'
  have hbtw' : ∀ x y : Y, x < y → ∃ d ∈ D', x < d ∧ d < y := by
    intro x y hxy
    obtain ⟨d, hdD, hxd, hdy⟩ := hbtw x y hxy
    exact ⟨d, ⟨hdD, (ha x).trans_lt hxd, hdy.trans_le (hb y)⟩, hxd, hdy⟩
  have hablt : a < b := lt_of_le_of_ne (ha b) hab
  haveI : Countable D' := (hDc.mono fun d hd => hd.1).to_subtype
  haveI : DenselyOrdered D' := ⟨fun x y hxy => by
    obtain ⟨d, hd, h1, h2⟩ := hbtw' x y hxy
    exact ⟨⟨d, hd⟩, h1, h2⟩⟩
  haveI : NoMinOrder D' := ⟨fun x => by
    obtain ⟨d, hd, h1, h2⟩ := hbtw' a x x.2.2.1
    exact ⟨⟨d, hd⟩, h2⟩⟩
  haveI : NoMaxOrder D' := ⟨fun x => by
    obtain ⟨d, hd, h1, h2⟩ := hbtw' x b x.2.2.2
    exact ⟨⟨d, hd⟩, h1⟩⟩
  haveI : Nonempty D' := by
    obtain ⟨d, hd, -⟩ := hbtw' a b hablt
    exact ⟨⟨d, hd⟩⟩
  haveI : Nonempty (Ioo (0 : ℚ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  obtain ⟨e⟩ := Order.iso_of_countable_dense D' (Ioo (0 : ℚ) 1)
  set g : D' → ℝ := fun d => (((e d : Ioo (0 : ℚ) 1) : ℚ) : ℝ) with hg
  have hgmono : StrictMono g := fun x y hxy => by
    simp only [hg, Rat.cast_lt]; exact e.strictMono hxy
  have hgpos : ∀ d, 0 < g d := fun d => by simp only [hg, Rat.cast_pos]; exact (e d).2.1
  have hglt : ∀ d, g d < 1 := fun d => by
    simp only [hg]; exact_mod_cast (e d).2.2
  have hgsymm : ∀ (q : ℚ) (hq : q ∈ Ioo (0 : ℚ) 1), g (e.symm ⟨q, hq⟩) = q := by
    intro q hq; simp [hg]
  set F : Y → ℝ := fun x => sSup (insert 0 (g '' {d | (d : Y) < x})) with hF
  have hbdd : ∀ x, BddAbove (insert (0 : ℝ) (g '' {d | (d : Y) < x})) := fun x =>
    ⟨1, by
      rintro t (rfl | ⟨d, -, rfl⟩)
      · exact zero_le_one
      · exact (hglt d).le⟩
  have hF0 : ∀ x, 0 ≤ F x := fun x => le_csSup (hbdd x) (mem_insert _ _)
  have hF1 : ∀ x, F x ≤ 1 := fun x => csSup_le (insert_nonempty _ _) (by
      rintro t (rfl | ⟨d, -, rfl⟩)
      · exact zero_le_one
      · exact (hglt d).le)
  have hFge : ∀ (x : Y) (d : D'), (d : Y) < x → g d ≤ F x := fun x d hd =>
    le_csSup (hbdd x) (mem_insert_of_mem _ ⟨d, hd, rfl⟩)
  have hFmono : Monotone F := fun x y hxy => csSup_le_csSup (hbdd y) (insert_nonempty _ _)
    (insert_subset_insert (image_mono fun d (hd : (d : Y) < x) => hd.trans_le hxy))
  -- lower bound criterion
  have hlow : ∀ (x : Y) (t : ℝ), t ≤ 1 →
      (∀ (q : ℚ) (hq : q ∈ Ioo (0 : ℚ) 1), (q : ℝ) < t → ((e.symm ⟨q, hq⟩ : D') : Y) < x) →
      t ≤ F x := by
    intro x t ht1 h
    by_contra hlt
    push_neg at hlt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hq0 : (0 : ℝ) < q := (hF0 x).trans_lt hq1
    have hqI : q ∈ Ioo (0 : ℚ) 1 := ⟨by exact_mod_cast hq0, by
      have : (q : ℝ) < 1 := hq2.trans_le ht1
      exact_mod_cast this⟩
    have := hFge x _ (h q hqI hq2)
    rw [hgsymm] at this
    linarith
  have hFeq : ∀ d : D', F d = g d := by
    intro d
    refine le_antisymm (csSup_le (insert_nonempty _ _) ?_) (hlow d (g d) (hglt d).le ?_)
    · rintro t (rfl | ⟨d', hd', rfl⟩)
      · exact (hgpos d).le
      · exact (hgmono hd').le
    · intro q hq hqd
      have : e.symm ⟨q, hq⟩ < d := by
        rw [OrderIso.symm_apply_lt]
        show (q : ℚ) < ((e d : Ioo (0 : ℚ) 1) : ℚ)
        have h' : (q : ℝ) < (((e d : Ioo (0 : ℚ) 1) : ℚ) : ℝ) := hqd
        exact_mod_cast h'
      exact this
  have hFa : F a = 0 := by
    refine le_antisymm (csSup_le (insert_nonempty _ _) ?_) (hF0 a)
    rintro t (rfl | ⟨d, hd, rfl⟩)
    · exact le_rfl
    · exact absurd (hd : (d : Y) < a) (not_lt.mpr (ha _))
  have hFb : F b = 1 := le_antisymm (hF1 b) (hlow b 1 le_rfl fun q hq _ => (e.symm ⟨q, hq⟩).2.2.2)
  have hFsm : StrictMono F := by
    intro x y hxy
    obtain ⟨d₁, hd₁, hxd₁, hd₁y⟩ := hbtw' x y hxy
    obtain ⟨d₂, hd₂, hd₁d₂, hd₂y⟩ := hbtw' d₁ y hd₁y
    calc F x ≤ F d₁ := hFmono hxd₁.le
      _ = g ⟨d₁, hd₁⟩ := hFeq ⟨d₁, hd₁⟩
      _ < g ⟨d₂, hd₂⟩ := hgmono hd₁d₂
      _ = F d₂ := (hFeq ⟨d₂, hd₂⟩).symm
      _ ≤ F y := hFmono hd₂y.le
  have hFcont : Continuous F := by
    rw [OrderTopology.topology_eq_generate_intervals (α := ℝ), continuous_generateFrom_iff]
    rintro s ⟨t, rfl | rfl⟩
    · -- `{x | t < F x}`
      by_cases ht : t < 0
      · convert isOpen_univ
        ext x; simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
        exact ht.trans_le (hF0 x)
      push_neg at ht
      rw [isOpen_iff_forall_mem_open]
      intro x (hx : t < F x)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hx
      have hqI : q ∈ Ioo (0 : ℚ) 1 := ⟨by exact_mod_cast ht.trans_lt hq1, by
        have : (q : ℝ) < 1 := hq2.trans_le (hF1 x)
        exact_mod_cast this⟩
      set d := e.symm ⟨q, hqI⟩
      have hFd : F d = q := by rw [hFeq, hgsymm]
      refine ⟨Ioi (d : Y), fun z (hz : (d : Y) < z) => ?_, hIoi _, ?_⟩
      · show t < F z
        have := hFsm hz
        rw [hFd] at this
        exact hq1.trans this
      · show (d : Y) < x
        by_contra hle
        push_neg at hle
        have := hFmono hle
        rw [hFd] at this
        linarith
    · -- `{x | F x < t}`
      by_cases ht : 1 < t
      · convert isOpen_univ
        ext x; simp only [mem_preimage, mem_Iio, mem_univ, iff_true]
        exact (hF1 x).trans_lt ht
      push_neg at ht
      rw [isOpen_iff_forall_mem_open]
      intro x (hx : F x < t)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hx
      have hqI : q ∈ Ioo (0 : ℚ) 1 := ⟨by exact_mod_cast (hF0 x).trans_lt hq1, by
        have : (q : ℝ) < 1 := hq2.trans_le ht
        exact_mod_cast this⟩
      set d := e.symm ⟨q, hqI⟩
      have hFd : F d = q := by rw [hFeq, hgsymm]
      refine ⟨Iio (d : Y), fun z (hz : z < (d : Y)) => ?_, hIio _, ?_⟩
      · show F z < t
        have := hFsm hz
        rw [hFd] at this
        exact this.trans hq2
      · show x < (d : Y)
        by_contra hle
        push_neg at hle
        have := hFmono hle
        rw [hFd] at this
        linarith
  refine ⟨F, hFcont, hFsm, hFa, hFb, ?_⟩
  apply subset_antisymm
  · rintro _ ⟨x, rfl⟩; exact ⟨hF0 x, hF1 x⟩
  · have := (isPreconnected_range hFcont).Icc_subset (mem_range_self a) (mem_range_self b)
    rwa [hFa, hFb] at this

end OrderMap

section IrrOrder

variable {Y : Type*} [TopologicalSpace Y]

/-- `acL x y`: the component of `{y}ᶜ` containing `x`. With `x = a` it is the set of points
"before" `y`; with `x = b`, the set of points "after" `y`. -/
def acL (x y : Y) : Set Y := connectedComponentIn ({y}ᶜ) x

theorem acL_subset (x y : Y) : acL x y ⊆ {y}ᶜ := connectedComponentIn_subset _ _

theorem acL_eq_of_split {p x : Y} {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    (hd : Disjoint U V) (hu : U ∪ V = {p}ᶜ) (hUc : IsPreconnected U) (hx : x ∈ U) :
    acL x p = U := by
  have hsub : acL x p ⊆ U ∪ V := by rw [hu]; exact acL_subset x p
  have hxp : x ∈ ({p}ᶜ : Set Y) := by rw [← hu]; exact mem_union_left V hx
  apply subset_antisymm
  · exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hU hV hd hsub
      ⟨x, mem_connectedComponentIn hxp, hx⟩
  · exact hUc.subset_connectedComponentIn hx (by rw [← hu]; exact subset_union_left)

/-- A preconnected set containing `x` and missing `z` lies in `acL x z`. -/
theorem acL_absorb {T : Set Y} (hT : IsPreconnected T) {x z : Y} (hx : x ∈ T) (hz : z ∉ T) :
    T ⊆ acL x z :=
  hT.subset_connectedComponentIn hx fun w hw (hwz : w = z) => hz (hwz ▸ hw)

theorem acL_mem_insert_a (a y : Y) : a ∈ insert y (acL a y) := by
  by_cases h : y = a
  · exact h ▸ mem_insert y _
  · exact mem_insert_of_mem _ (mem_connectedComponentIn (Ne.symm h))

theorem acL_mem_insert_b (b y : Y) : b ∈ insert y (acL b y) := by
  by_cases h : y = b
  · exact h ▸ mem_insert y _
  · exact mem_insert_of_mem _ (mem_connectedComponentIn (Ne.symm h))

variable [ConnectedSpace Y] [T1Space Y] {a b : Y}

theorem acL_facts (hirr : ∀ H : Set Y, IsPreconnected H → a ∈ H → b ∈ H → H = univ)
    (hab : a ≠ b) (y : Y) :
    IsOpen (acL a y) ∧ IsOpen (acL b y) ∧ Disjoint (acL a y) (acL b y) ∧
      IsPreconnected (insert y (acL a y)) ∧ IsPreconnected (insert y (acL b y)) ∧
      (y ≠ a → y ≠ b → acL a y ∪ acL b y = {y}ᶜ) := by
  have hirr' : ∀ H : Set Y, IsPreconnected H → b ∈ H → a ∈ H → H = univ :=
    fun H h h1 h2 => hirr H h h2 h1
  by_cases hya : y = a
  · subst hya
    have h1 : acL y y = ∅ := connectedComponentIn_eq_empty (by simp)
    have h2 : acL b y = {y}ᶜ :=
      (ac_compl_isPreconnected hirr' hab.symm).connectedComponentIn hab.symm
    rw [h1, h2]
    refine ⟨isOpen_empty, isOpen_compl_singleton, by simp, ?_, ?_, fun h => absurd rfl h⟩
    · simpa using isPreconnected_singleton
    · rw [show insert y ({y}ᶜ : Set Y) = univ by ext z; by_cases z = y <;> simp [*]]
      exact isPreconnected_univ
  by_cases hyb : y = b
  · subst hyb
    have h1 : acL y y = ∅ := connectedComponentIn_eq_empty (by simp)
    have h2 : acL a y = {y}ᶜ := (ac_compl_isPreconnected hirr hab).connectedComponentIn hab
    rw [h1, h2]
    refine ⟨isOpen_compl_singleton, isOpen_empty, by simp, ?_, ?_,
      fun _ h => absurd rfl h⟩
    · rw [show insert y ({y}ᶜ : Set Y) = univ by ext z; by_cases z = y <;> simp [*]]
      exact isPreconnected_univ
    · simpa using isPreconnected_singleton
  obtain ⟨U, V, hU, hV, hd, hu, hUc, hVc, haU, hbV⟩ := ac_cut hirr hya hyb
  have hL : acL a y = U := acL_eq_of_split hU hV hd hu hUc haU
  have hR : acL b y = V := acL_eq_of_split hV hU hd.symm (by rwa [union_comm]) hVc hbV
  rw [hL, hR]
  exact ⟨hU, hV, hd, ac_insert_isPreconnected hU hV hd hu,
    ac_insert_isPreconnected hV hU hd.symm (by rwa [union_comm]), fun _ _ => hu⟩

variable (hirr : ∀ H : Set Y, IsPreconnected H → a ∈ H → b ∈ H → H = univ) (hab : a ≠ b)
include hirr hab

theorem acL_asymm {x y : Y} (hxy : x ∈ acL a y) (hyx : y ∈ acL a x) : False := by
  obtain ⟨-, -, hdx, -, hRx, -⟩ := acL_facts hirr hab x
  obtain ⟨-, -, hdy, -, -, -⟩ := acL_facts hirr hab y
  have hyT : y ∉ insert x (acL b x) := by
    rintro (h | h)
    · exact acL_subset a y (h ▸ hxy : y ∈ acL a y) rfl
    · exact hdx.ne_of_mem hyx h rfl
  have := acL_absorb hRx (acL_mem_insert_b b x) hyT (mem_insert x _)
  exact hdy.ne_of_mem hxy this rfl

theorem acL_trans {x y z : Y} (hxy : x ∈ acL a y) (hyz : y ∈ acL a z) : x ∈ acL a z := by
  obtain ⟨-, -, -, hLy, -, -⟩ := acL_facts hirr hab y
  have hzT : z ∉ insert y (acL a y) := by
    rintro (h | h)
    · exact acL_subset a z (h ▸ hyz : z ∈ acL a z) rfl
    · exact acL_asymm hirr hab h hyz
  exact acL_absorb hLy (acL_mem_insert_a a y) hzT (mem_insert_of_mem _ hxy)

theorem acL_total {y z : Y} (hyz : y ≠ z) : y ∈ acL a z ∨ z ∈ acL a y := by
  by_cases hza : z = a
  · subst hza; exact Or.inr (mem_connectedComponentIn (Ne.symm hyz))
  by_cases hya : y = a
  · subst hya; exact Or.inl (mem_connectedComponentIn hyz)
  by_cases hzb : z = b
  · subst hzb
    left
    rw [show acL a z = {z}ᶜ from (ac_compl_isPreconnected hirr hab).connectedComponentIn hab]
    exact hyz
  by_cases hyb : y = b
  · subst hyb
    right
    rw [show acL a y = {y}ᶜ from (ac_compl_isPreconnected hirr hab).connectedComponentIn hab]
    exact Ne.symm hyz
  obtain ⟨-, -, hdz, hLz, -, hu⟩ := acL_facts hirr hab z
  have : y ∈ acL a z ∪ acL b z := by rw [hu hza hzb]; exact hyz
  rcases this with h | h
  · exact Or.inl h
  · right
    have hyT : y ∉ insert z (acL a z) := by
      rintro (h' | h')
      · exact hyz h'
      · exact hdz.ne_of_mem h' h rfl
    exact acL_absorb hLz (acL_mem_insert_a a z) hyT (mem_insert z _)

theorem acL_ray {x y : Y} : x ∈ acL b y ↔ y ∈ acL a x := by
  obtain ⟨-, -, hdy, -, -, hu⟩ := acL_facts hirr hab y
  constructor
  · intro hx
    have hxy : y ≠ x := fun h => acL_subset b y hx h.symm
    rcases acL_total hirr hab hxy with h | h
    · exact h
    · exact absurd hx (hdy.ne_of_mem h · rfl)
  · intro h
    have hxy : x ≠ y := fun h' => acL_subset a x h h'.symm
    by_cases hya : y = a
    · subst hya
      rw [show acL b y = {y}ᶜ from
        (ac_compl_isPreconnected (fun H h h1 h2 => hirr H h h2 h1) hab.symm).connectedComponentIn
          hab.symm]
      exact hxy
    by_cases hyb : y = b
    · subst hyb
      exfalso
      obtain ⟨-, -, hdx, -, -, -⟩ := acL_facts hirr hab x
      have := acL_absorb isPreconnected_singleton (mem_singleton y)
        (fun h' => hxy (mem_singleton_iff.mp h')) (mem_singleton y)
      exact hdx.ne_of_mem h this rfl
    have : x ∈ acL a y ∪ acL b y := by rw [hu hya hyb]; exact hxy
    exact this.resolve_left fun h' => acL_asymm hirr hab h' h

/-- **An irreducible continuum is an arc** (in the subspace form): a compact, connected, separable
T1 space, irreducible between `a ≠ b`, is homeomorphic to `[0, 1]` with `0 ↦ a`, `1 ↦ b`. -/
theorem ac_homeomorph [CompactSpace Y] [TopologicalSpace.SeparableSpace Y] :
    ∃ h : unitInterval ≃ₜ Y, h 0 = a ∧ h 1 = b := by
  classical
  haveI : IsStrictTotalOrder Y (fun x y => x ∈ acL a y) :=
    { trichotomous := fun x y h1 h2 => by
        by_contra hxy
        rcases acL_total hirr hab hxy with h | h
        exacts [h1 h, h2 h]
      irrefl := fun x h => acL_subset a x h rfl
      trans := fun x y z => acL_trans hirr hab }
  letI : LinearOrder Y := linearOrderOfSTO (fun x y => x ∈ acL a y)
  have hlt : ∀ x y : Y, x < y ↔ x ∈ acL a y := fun x y => Iff.rfl
  have hIio : ∀ y : Y, IsOpen (Iio y) := fun y => by
    have : Iio y = acL a y := by ext x; exact hlt x y
    rw [this]; exact (acL_facts hirr hab y).1
  have hIoi : ∀ y : Y, IsOpen (Ioi y) := fun y => by
    have : Ioi y = acL b y := by ext x; exact (hlt y x).trans (acL_ray hirr hab).symm
    rw [this]; exact (acL_facts hirr hab y).2.1
  have ha : ∀ x : Y, a ≤ x := fun x => by
    rcases eq_or_ne x a with h | h
    · exact h ▸ le_rfl
    · exact ((hlt a x).mpr (mem_connectedComponentIn (Ne.symm h))).le
  have hb : ∀ x : Y, x ≤ b := fun x => by
    rcases eq_or_ne x b with h | h
    · exact h ▸ le_rfl
    · refine ((hlt x b).mpr ?_).le
      rw [show acL a b = {b}ᶜ from (ac_compl_isPreconnected hirr hab).connectedComponentIn hab]
      exact h
  obtain ⟨F, hFc, hFs, hFa, hFb, hFr⟩ := ac_exists_strictMono hIio hIoi ha hb hab
  have hmem : ∀ x, F x ∈ unitInterval := fun x => by
    show F x ∈ Icc 0 1; rw [← hFr]; exact mem_range_self x
  set G : Y → unitInterval := fun x => ⟨F x, hmem x⟩ with hG
  have hGc : Continuous G := hFc.subtype_mk hmem
  have hGb : Function.Bijective G := by
    refine ⟨fun x y hxy => hFs.injective (congrArg Subtype.val hxy), fun t => ?_⟩
    obtain ⟨x, hx⟩ : t.1 ∈ range F := hFr ▸ t.2
    exact ⟨x, Subtype.ext hx⟩
  set h := hGc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective G hGb)
  refine ⟨h.symm, ?_, ?_⟩
  · rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext hFa.symm
  · rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext hFb.symm

end IrrOrder

/-- **Arc characterization (topological form).** In a metrizable space, a compact connected set
containing `A ≠ B` with no connected proper subset containing both is the image of an embedding
of `[0, 1]` with `0 ↦ A` and `1 ↦ B`; and conversely. -/
theorem isIrreducibleConnected_iff_arc {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] {A B : X} (hAB : A ≠ B) {C : Set X} :
    (IsCompact C ∧ IsConnected C ∧ A ∈ C ∧ B ∈ C ∧
        ∀ H ⊆ C, H ≠ C → A ∈ H → B ∈ H → ¬ IsConnected H) ↔
      ∃ f : unitInterval → X, IsEmbedding f ∧ range f = C ∧ f 0 = A ∧ f 1 = B := by
  constructor
  · rintro ⟨hCc, hCconn, hA, hB, hirr⟩
    haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc
    haveI : ConnectedSpace C := Subtype.connectedSpace hCconn
    have hirr' : ∀ H : Set C, IsPreconnected H → (⟨A, hA⟩ : C) ∈ H → (⟨B, hB⟩ : C) ∈ H →
        H = univ := by
      intro H hH hAH hBH
      by_contra hne
      have hsub : Subtype.val '' H ⊆ C := fun _ ⟨x, _, hx⟩ => hx ▸ x.2
      refine hirr _ hsub ?_ ⟨_, hAH, rfl⟩ ⟨_, hBH, rfl⟩
        ⟨⟨A, _, hAH, rfl⟩, IsInducing.subtypeVal.isPreconnected_image.mpr hH⟩
      intro heq
      apply hne
      ext x
      simp only [mem_univ, iff_true]
      have : (x : X) ∈ Subtype.val '' H := by rw [heq]; exact x.2
      obtain ⟨y, hy, hyx⟩ := this
      exact Subtype.ext hyx ▸ hy
    obtain ⟨h, h0, h1⟩ := ac_homeomorph hirr' (by simpa using hAB)
    refine ⟨Subtype.val ∘ h, IsEmbedding.subtypeVal.comp h.isEmbedding, ?_, by simp [h0],
      by simp [h1]⟩
    rw [range_comp, h.range_coe, image_univ, Subtype.range_coe]
  · rintro ⟨f, hf, rfl, rfl, rfl⟩
    refine ⟨isCompact_range hf.continuous, isConnected_range hf.continuous, mem_range_self _,
      mem_range_self _, fun H hHC hne h0 h1 hH => hne ?_⟩
    have hpre : IsPreconnected (f ⁻¹' H) := by
      rw [← hf.isInducing.isPreconnected_image, image_preimage_eq_of_subset hHC]
      exact hH.isPreconnected
    apply subset_antisymm hHC
    rintro _ ⟨t, rfl⟩
    have h0' : (0 : unitInterval) ∈ f ⁻¹' H := h0
    have h1' : (1 : unitInterval) ∈ f ⁻¹' H := h1
    exact hpre.Icc_subset h0' h1' ⟨t.2.1, t.2.2⟩

end HPC.Moore
