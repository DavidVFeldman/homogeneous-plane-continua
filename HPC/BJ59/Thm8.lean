import HPC.BJ59.Thm8Lib

/-!
# Batch 200, §4: Bing–Jones Theorem 8 (p. 177)

Route: commission 200 §4.

* `bj_theorem8_ends`: the case `H(y₀) = d₀`, `H(y_{m−1}) = d_{n−1}` (steps 1–7: the sets `U_A`,
  `U_B`; the chains `E(a)` of Theorem 7 on single fibres; the neighbourhoods `I_a`, here the
  complements of the images of closed "bad" sets; a Lebesgue number and a uniform grid of `T`
  segments in place of a minimal subcover; the cover `U₀, …, U_{T−1}` from Theorem 4 at the
  `T − 1` cuts; the links `e_k = ⋃ᵢ e(a_i)_k ∩ U_i ∩ f⁻¹(I_{a_i})`; a final shrinking);
* `bj_theorem8_le`: the general case with `r ≤ s`, by folding along the walk;
* `bj_theorem8` (statement verbatim from the skeleton): reversing `D` when `s < r`.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Thm8

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Theorem 8, the case `H(y₀) = d₀`, `H(y_{m−1}) = d_{n−1}`** (commission 200 §4, steps
1–7). -/
theorem bj_theorem8_ends {f : X → unitInterval} (hf : IsContArcPA f)
    (hS : IsSnakeLike (univ : Set X)) {n m : ℕ} (hn : 3 ≤ n) (D : Chain X n)
    (hD : univ ⊆ D.union) (hDf : ∀ t j, (D.link j ∩ f ⁻¹' {t}).Nonempty) (hm : 0 < m)
    (H : Fin m → Fin n) (hH : IsChainMap H) (h0 : (H ⟨0, hm⟩).val = 0)
    (hlast : (H ⟨m - 1, by omega⟩).val = n - 1) :
    ∃ E : Chain X m, IsBJChain E ∧ univ ⊆ E.union ∧ (∀ t i, (E.link i ∩ f ⁻¹' {t}).Nonempty) ∧
      ∀ i, E.link i ⊆ D.link (H i) := by
  classical
  obtain ⟨hfc, hfo, hfs, hfp⟩ := hf
  have hfa : IsArcOfContinua f := ⟨hfc, hfs, fun t => (hfp t).1.1⟩
  have hfib : ∀ t, IsPreconnected (f ⁻¹' {t}) := fun t => (hfp t).1.1.2.isPreconnected
  have hfr : Continuous fun x => (f x : ℝ) := continuous_subtype_val.comp hfc
  set i0 : Fin m := ⟨0, hm⟩ with hi0
  set i1 : Fin m := ⟨m - 1, by omega⟩ with hi1
  set d0 : Fin n := ⟨0, by omega⟩ with hd0
  set d1 : Fin n := ⟨n - 1, by omega⟩ with hd1
  have hH0 : H i0 = d0 := Fin.ext h0
  have hH1 : H i1 = d1 := Fin.ext hlast
  have hm2 : 2 ≤ m := by
    by_contra h
    have e : i0 = i1 := Fin.ext (by simp only [hi0, hi1]; omega)
    rw [e] at h0
    omega
  have hd01 : ∀ x, x ∈ D.link d0 → x ∉ D.link d1 := by
    intro x h0' h1'
    have := (D.adjacent_iff d0 d1).1 ⟨x, h0', h1'⟩
    simp only [hd0, hd1] at this
    omega
  -- step 1: the sets `U_A`, `U_B`
  obtain ⟨UA, UA', hUAo, hUAd, hUA'UA, hUA'c, hUA'f⟩ := exists_deep_sets hfo (D.isOpen d0)
    (fun t => hDf t d0) (by obtain ⟨x, hx⟩ := D.link_nonempty d1; exact ⟨x, fun h => hd01 x h hx⟩)
  obtain ⟨UB, UB', hUBo, hUBd, hUB'UB, hUB'c, hUB'f⟩ := exists_deep_sets hfo (D.isOpen d1)
    (fun t => hDf t d1) (by obtain ⟨x, hx⟩ := D.link_nonempty d0; exact ⟨x, hd01 x hx⟩)
  -- step 2: the chains `E(a)`
  have hEa : ∀ a : unitInterval, ∃ E : Chain X m, IsBJChain E ∧ f ⁻¹' {a} ⊆ E.union ∧
      (∀ i, E.link i ⊆ D.link (H i)) ∧ closure UA ∩ f ⁻¹' {a} ⊆ E.link i0 ∧
      closure UB ∩ f ⁻¹' {a} ⊆ E.link i1 := by
    intro a
    obtain ⟨E, hE1, hE2, -, hE4, hE5, hE6⟩ := bj_theorem7_ends' (hfp a) hn D
      (fun x _ => hD (mem_univ x)) (fun j => hDf a j) H hH (r := i0) (s := i1) h0 hlast
      (isClosed_closure.inter (isClosed_singleton.preimage hfc))
      (isClosed_closure.inter (isClosed_singleton.preimage hfc))
      (fun x hx => ⟨hx.2, by rw [hH0]; exact hUAd hx.1⟩)
      (fun x hx => ⟨hx.2, by rw [hH1]; exact hUBd hx.1⟩)
    exact ⟨E, hE1, hE2, hE4, hE5, hE6⟩
  choose Ea hEabj hEacov hEaD hEaA hEaB using hEa
  -- step 3: the neighbourhoods `I_a`
  set Kb : unitInterval → Set X := fun a => (Ea a).unionᶜ ∪ (closure UA \ (Ea a).link i0) ∪
    (closure UB \ (Ea a).link i1)
  have hKb : ∀ a, IsClosed (Kb a) := fun a =>
    (((isOpen_iUnion fun i => (Ea a).isOpen i).isClosed_compl).union
      (isClosed_closure.sdiff ((Ea a).isOpen i0))).union (isClosed_closure.sdiff ((Ea a).isOpen i1))
  set O : unitInterval → Set unitInterval := fun a => (f '' Kb a)ᶜ
  have hOo : ∀ a, IsOpen (O a) := fun a => (hfc.isClosedMap _ (hKb a)).isOpen_compl
  have haO : ∀ a, a ∈ O a := by
    rintro a ⟨z, hz, hza⟩
    rcases hz with (hz | hz) | hz
    · exact hz (hEacov a hza)
    · exact hz.2 (hEaA a ⟨hz.1, hza⟩)
    · exact hz.2 (hEaB a ⟨hz.1, hza⟩)
  have hgood : ∀ a x, f x ∈ O a → x ∈ (Ea a).union ∧ (x ∈ closure UA → x ∈ (Ea a).link i0) ∧
      (x ∈ closure UB → x ∈ (Ea a).link i1) := by
    intro a x hx
    have hxK : x ∉ Kb a := fun h => hx ⟨x, h, rfl⟩
    refine ⟨?_, fun hxA => ?_, fun hxB => ?_⟩
    · by_contra h; exact hxK (Or.inl (Or.inl h))
    · by_contra h; exact hxK (Or.inl (Or.inr ⟨hxA, h⟩))
    · by_contra h; exact hxK (Or.inr ⟨hxB, h⟩)
  -- a Lebesgue number and a grid of `T` segments, overlapping by `η`
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_univ (X := unitInterval))
    hOo (fun t _ => mem_iUnion.2 ⟨t, haO t⟩)
  obtain ⟨T, hT⟩ := exists_nat_gt (2 / δ)
  have hTpos : (0 : ℝ) < T := lt_trans (by positivity) hT
  have hT1 : 1 ≤ T := by
    have : 0 < T := by exact_mod_cast hTpos
    omega
  have h2T : 2 / (T : ℝ) < δ := by
    rw [div_lt_iff₀ hTpos]
    rw [div_lt_iff₀ hδ] at hT
    linarith
  set η : ℝ := 1 / (4 * T) with hηdef
  have hη : 0 < η := by positivity
  have h4η : 4 * η = 1 / T := by rw [hηdef]; field_simp
  have hpt : ∀ i : Fin T, (0 : ℝ) ≤ (i : ℝ) / T ∧ (i : ℝ) / T ≤ 1 := fun i =>
    ⟨by positivity, by rw [div_le_one hTpos]; exact_mod_cast i.isLt.le⟩
  choose a ha using fun i : Fin T => hleb ⟨(i : ℝ) / T, hpt i⟩ (mem_univ _)
  have hseg : ∀ (i : Fin T) (t : unitInterval), (i : ℝ) / T - η < t →
      (t : ℝ) < ((i : ℝ) + 1) / T + η → t ∈ O (a i) := by
    intro i t h1 h2
    apply ha i
    rw [mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
    have e : ((i : ℝ) + 1) / T = i / T + 1 / T := by ring
    have e2 : 2 / (T : ℝ) = 1 / T + 1 / T := by ring
    constructor <;> simp only <;> linarith
  have hpick : ∀ t : unitInterval, ∃ i : Fin T, (i : ℝ) / T - η < t ∧
      (t : ℝ) < ((i : ℝ) + 1) / T + η := by
    intro t
    set k := min ⌊(t : ℝ) * T⌋₊ (T - 1) with hk
    refine ⟨⟨k, by omega⟩, ?_, ?_⟩
    · show (k : ℝ) / T - η < t
      have h1 : (k : ℝ) ≤ t * T := le_trans (by exact_mod_cast min_le_left _ _)
        (Nat.floor_le (by have := t.2.1; positivity))
      have : (k : ℝ) / T ≤ t := by rw [div_le_iff₀ hTpos]; exact h1
      linarith
    · show (t : ℝ) < ((k : ℝ) + 1) / T + η
      rcases le_total ⌊(t : ℝ) * T⌋₊ (T - 1) with h | h
      · have hk' : k = ⌊(t : ℝ) * T⌋₊ := min_eq_left h
        have h3 := Nat.lt_floor_add_one ((t : ℝ) * T)
        rw [← hk'] at h3
        have : (t : ℝ) < ((k : ℝ) + 1) / T := by rw [lt_div_iff₀ hTpos]; linarith
        linarith
      · have hk' : k = T - 1 := min_eq_right h
        have e : ((k : ℝ) + 1) = T := by
          rw [hk']; rw [Nat.cast_sub hT1]; push_cast; ring
        have : ((k : ℝ) + 1) / T = 1 := by rw [e, div_self hTpos.ne']
        have := t.2.2
        linarith
  -- step 4: the cuts
  set UAB : Set X := UA ∪ UB
  set V : ℕ → Set X := fun c => UAB ∩ {x | (c : ℝ) / T - η < f x ∧ (f x : ℝ) < c / T + η}
  have hVU : ∀ c, V c ⊆ UAB := fun c => inter_subset_left
  have hcut : ∀ c : ℕ, ∃ L R : Set X, 1 ≤ c → c + 1 ≤ T → IsClosed L ∧ IsClosed R ∧
      Disjoint L R ∧ L ∪ R = (V c)ᶜ ∧ (∀ x ∈ L, (f x : ℝ) < c / T + η) ∧
      (∀ x ∈ R, (c : ℝ) / T - η < f x) := by
    intro c
    by_cases hc : 1 ≤ c ∧ c + 1 ≤ T
    · have hcT : (1 : ℝ) ≤ c := by exact_mod_cast hc.1
      have hcT' : (c : ℝ) + 1 ≤ T := by exact_mod_cast hc.2
      have hα : 0 < (c : ℝ) / T - η := by
        have : 1 / (T : ℝ) ≤ c / T := div_le_div_of_nonneg_right hcT hTpos.le
        linarith
      have hβ : (c : ℝ) / T + η < 1 := by
        have : (c : ℝ) / T ≤ 1 - 1 / T := by
          rw [le_sub_iff_add_le, ← add_div, div_le_one hTpos]; exact hcT'
        linarith
      have hVo : IsOpen (V c) := (hUAo.union hUBo).inter
        ((isOpen_lt continuous_const hfr).inter (isOpen_lt hfr continuous_const))
      have hVne : (V c).Nonempty := by
        have hc01 : (0 : ℝ) ≤ c / T ∧ (c : ℝ) / T ≤ 1 := ⟨by positivity, by linarith⟩
        obtain ⟨y, hy, hyf⟩ := hUA'f ⟨(c : ℝ) / T, hc01⟩
        refine ⟨y, Or.inl (hUA'UA (subset_closure hy)), ?_, ?_⟩ <;>
          (rw [show f y = ⟨(c : ℝ) / T, hc01⟩ from hyf]; simp only; linarith)
      obtain ⟨L, R, h1, h2, h3, h4, h5, h6⟩ := bj_cut hfa hS hVo hVne hα hβ fun x hx => hx.2
      exact ⟨L, R, fun _ _ => ⟨h1, h2, h3, h4, h5, h6⟩⟩
    · exact ⟨∅, ∅, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose L R hLR using hcut
  set Lc : ℕ → Set X := fun c => if 1 ≤ c ∧ c + 1 ≤ T then L c else ∅ with hLc
  set Rc : ℕ → Set X := fun c => if 1 ≤ c ∧ c + 1 ≤ T then R c else ∅ with hRc
  have hLcc : ∀ c, IsClosed (Lc c) := by
    intro c; simp only [hLc]; split_ifs with h
    exacts [(hLR c h.1 h.2).1, isClosed_empty]
  have hRcc : ∀ c, IsClosed (Rc c) := by
    intro c; simp only [hRc]; split_ifs with h
    exacts [(hLR c h.1 h.2).2.1, isClosed_empty]
  -- outside `U_A ∪ U_B`, each point is in `L c` or `R c`
  have hLorR : ∀ c x, 1 ≤ c → c + 1 ≤ T → x ∉ UAB → x ∈ L c ∨ x ∈ R c := by
    intro c x h1 h2 hx
    have : x ∈ L c ∪ R c := by rw [(hLR c h1 h2).2.2.2.1]; exact fun h => hx (hVU c h)
    exact this
  set Ui : Fin T → Set X := fun i => ((Lc i)ᶜ ∩ (Rc (i + 1))ᶜ) ∪ UAB with hUi
  have hUio : ∀ i, IsOpen (Ui i) := fun i =>
    ((hLcc i).isOpen_compl.inter (hRcc _).isOpen_compl).union (hUAo.union hUBo)
  have hUcov : ∀ x, x ∉ UAB → ∃ i, x ∈ Ui i := by
    intro x hx
    by_cases hex : ∃ c, 1 ≤ c ∧ c + 1 ≤ T ∧ x ∈ L c
    · have hc := Nat.find_spec hex
      refine ⟨⟨Nat.find hex - 1, by omega⟩, Or.inl ⟨?_, ?_⟩⟩
      · show x ∉ Lc (Nat.find hex - 1)
        simp only [hLc]
        split_ifs with h
        · exact fun hxL => Nat.find_min hex (by omega : Nat.find hex - 1 < Nat.find hex)
            ⟨h.1, h.2, hxL⟩
        · exact notMem_empty x
      · show x ∉ Rc (Nat.find hex - 1 + 1)
        rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]
        simp only [hRc, if_pos (⟨hc.1, hc.2.1⟩ : 1 ≤ Nat.find hex ∧ Nat.find hex + 1 ≤ T)]
        exact fun hxR => Set.disjoint_left.1 (hLR _ hc.1 hc.2.1).2.2.1 hc.2.2 hxR
    · push_neg at hex
      refine ⟨⟨T - 1, by omega⟩, Or.inl ⟨?_, ?_⟩⟩
      · show x ∉ Lc (T - 1)
        simp only [hLc]
        split_ifs with h
        · exact hex _ h.1 h.2
        · exact notMem_empty x
      · show x ∉ Rc (T - 1 + 1)
        simp only [hRc]
        rw [if_neg (by omega)]
        exact notMem_empty x
  have hUover : ∀ i k : Fin T, i < k → ∀ x ∈ Ui i, x ∈ Ui k → x ∈ UAB := by
    intro i k hik x hxi hxk
    by_contra hx
    have hxi' := hxi.resolve_right hx
    have hxk' := hxk.resolve_right hx
    have hik' : i.val < k.val := hik
    have hc1 : 1 ≤ i.val + 1 ∧ i.val + 1 + 1 ≤ T := ⟨by omega, by omega⟩
    have hc2 : 1 ≤ k.val ∧ k.val + 1 ≤ T := ⟨by omega, by omega⟩
    have hxL : x ∈ L (i + 1) := by
      rcases hLorR _ x hc1.1 hc1.2 hx with h | h
      · exact h
      · exact absurd (by simp only [hRc, if_pos hc1]; exact h) hxi'.2
    have hxR : x ∈ R k := by
      rcases hLorR _ x hc2.1 hc2.2 hx with h | h
      · exact absurd (by simp only [hLc, if_pos hc2]; exact h) hxk'.1
      · exact h
    rcases eq_or_lt_of_le (show i.val + 1 ≤ k.val by omega) with h | h
    · rw [h] at hxL
      exact Set.disjoint_left.1 (hLR _ hc2.1 hc2.2).2.2.1 hxL hxR
    · have h1 := (hLR _ hc1.1 hc1.2).2.2.2.2.1 x hxL
      have h2 := (hLR _ hc2.1 hc2.2).2.2.2.2.2 x hxR
      have h3 : ((i.val + 1 : ℕ) : ℝ) + 1 ≤ k.val := by exact_mod_cast h
      have h4 : ((i.val + 1 : ℕ) : ℝ) / T + 1 / T ≤ (k.val : ℝ) / T := by
        rw [← add_div]; exact div_le_div_of_nonneg_right h3 hTpos.le
      linarith
  have hUloc : ∀ (i : Fin T) x, x ∈ Ui i → x ∉ UAB →
      (i : ℝ) / T - η < f x ∧ (f x : ℝ) < ((i : ℝ) + 1) / T + η := by
    intro i x hxi hx
    have hxi' := hxi.resolve_right hx
    constructor
    · by_cases hi : 1 ≤ i.val
      · have hc : 1 ≤ i.val ∧ i.val + 1 ≤ T := ⟨hi, i.isLt⟩
        rcases hLorR _ x hc.1 hc.2 hx with h | h
        · exact absurd (by simp only [hLc, if_pos hc]; exact h) hxi'.1
        · exact (hLR _ hc.1 hc.2).2.2.2.2.2 x h
      · have : i.val = 0 := by omega
        rw [this]
        have := (f x).2.1
        simp only [Nat.cast_zero, zero_div, zero_sub]
        linarith
    · by_cases hi : i.val + 1 + 1 ≤ T
      · have hc : 1 ≤ i.val + 1 ∧ i.val + 1 + 1 ≤ T := ⟨by omega, hi⟩
        rcases hLorR _ x hc.1 hc.2 hx with h | h
        · have := (hLR _ hc.1 hc.2).2.2.2.2.1 x h
          push_cast at this
          exact this
        · exact absurd (by simp only [hRc, if_pos hc]; exact h) hxi'.2
      · have hiT : (i : ℝ) + 1 = T := by
          have : i.val + 1 = T := by omega
          exact_mod_cast this
        rw [hiT, div_self hTpos.ne']
        have := (f x).2.2
        linarith
  -- step 5: the links
  set W : Fin m → Set X := fun k => ⋃ i : Fin T, (Ea (a i)).link k ∩ Ui i ∩ f ⁻¹' O (a i)
    with hW
  have hWo : ∀ k, IsOpen (W k) := fun k => isOpen_iUnion fun i =>
    (((Ea (a i)).isOpen k).inter (hUio i)).inter ((hOo _).preimage hfc)
  have hWD : ∀ k, W k ⊆ D.link (H k) := by
    intro k x hx
    obtain ⟨i, ⟨⟨hk, -⟩, -⟩⟩ := mem_iUnion.1 hx
    exact hEaD _ k hk
  have hUAW : UA ⊆ W i0 := by
    intro x hx
    obtain ⟨i, h1, h2⟩ := hpick (f x)
    have hO := hseg i (f x) h1 h2
    exact mem_iUnion.2 ⟨i, ⟨(hgood _ x hO).2.1 (subset_closure hx), Or.inr (Or.inl hx)⟩, hO⟩
  have hUBW : UB ⊆ W i1 := by
    intro x hx
    obtain ⟨i, h1, h2⟩ := hpick (f x)
    have hO := hseg i (f x) h1 h2
    exact mem_iUnion.2 ⟨i, ⟨(hgood _ x hO).2.2 (subset_closure hx), Or.inr (Or.inr hx)⟩, hO⟩
  have hWcov : ∀ x, x ∈ ⋃ k, W k := by
    intro x
    by_cases hx : x ∈ UAB
    · rcases hx with hA | hB
      · exact mem_iUnion.2 ⟨i0, hUAW hA⟩
      · exact mem_iUnion.2 ⟨i1, hUBW hB⟩
    · obtain ⟨i, hxi⟩ := hUcov x hx
      obtain ⟨h1, h2⟩ := hUloc i x hxi hx
      have hO := hseg i (f x) h1 h2
      obtain ⟨k, hk⟩ := mem_iUnion.1 (hgood _ x hO).1
      exact mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨i, ⟨hk, hxi⟩, hO⟩⟩
  have hWdisj : ∀ k l : Fin m, 1 < ((k : ℤ) - l).natAbs → W k ∩ W l = ∅ := by
    intro k l hkl
    refine eq_empty_of_forall_notMem fun x ⟨hxk, hxl⟩ => ?_
    obtain ⟨i, ⟨⟨hk, hi⟩, hOi⟩⟩ := mem_iUnion.1 hxk
    obtain ⟨j, ⟨⟨hl, hj⟩, hOj⟩⟩ := mem_iUnion.1 hxl
    by_cases hij : i = j
    · subst hij
      have := ((Ea (a i)).adjacent k l).1 ⟨x, hk, hl⟩
      omega
    · have hxU : x ∈ UAB := by
        rcases lt_or_gt_of_ne hij with h | h
        exacts [hUover i j h x hi hj, hUover j i h x hj hi]
      rcases hxU with hA | hB
      · have h1 := ((Ea (a i)).adjacent_iff k i0).1 ⟨x, hk, (hgood _ x hOi).2.1 (subset_closure hA)⟩
        have h2 := ((Ea (a j)).adjacent_iff l i0).1 ⟨x, hl, (hgood _ x hOj).2.1 (subset_closure hA)⟩
        simp only [hi0] at h1 h2
        omega
      · have h1 := ((Ea (a i)).adjacent_iff k i1).1 ⟨x, hk, (hgood _ x hOi).2.2 (subset_closure hB)⟩
        have h2 := ((Ea (a j)).adjacent_iff l i1).1 ⟨x, hl, (hgood _ x hOj).2.2 (subset_closure hB)⟩
        simp only [hi1] at h1 h2
        have := k.isLt
        have := l.isLt
        omega
  -- step 6: each fibre meets each link
  have hWf : ∀ t k, (W k ∩ f ⁻¹' {t}).Nonempty := by
    intro t k
    refine family_meets_all W hWo hWdisj (hfib t) (fun x _ => hWcov x) i0 i1 ?_ ?_ k
      (by simp only [hi0]; omega) (by simp only [hi1]; omega)
    · obtain ⟨y, hy, hyf⟩ := hUA'f t
      exact ⟨y, hUAW (hUA'UA (subset_closure hy)), hyf⟩
    · obtain ⟨y, hy, hyf⟩ := hUB'f t
      exact ⟨y, hUBW (hUB'UB (subset_closure hy)), hyf⟩
  have hX1 : f ⁻¹' Icc 0 1 = univ := by
    ext x; simp only [mem_preimage, mem_Icc, mem_univ, iff_true]
    exact ⟨unitInterval.nonneg', unitInterval.le_one'⟩
  have hXc : IsPreconnected (univ : Set X) := by
    rw [← hX1]; exact isPreconnected_preimage_Icc hfc hfs hfib 0 1
  have hWK : ∀ k, (W k ∩ univ).Nonempty := fun k => by
    obtain ⟨x, hx, -⟩ := hWf 0 k
    exact ⟨x, hx, mem_univ x⟩
  let E0 : Chain X m :=
    { link := W
      isOpen := hWo
      adjacent := fun i j => by
        constructor
        · intro h
          by_contra h'
          push_neg at h'
          rw [hWdisj i j h'] at h
          exact not_nonempty_empty h
        · intro h
          rcases lt_trichotomy i.val j.val with hlt | heq | hgt
          · exact adjacent_meet_of_cover hXc W hWo (fun x _ => hWcov x) hWK hWdisj i j (by omega)
          · have : i = j := Fin.ext heq
            subst this
            obtain ⟨x, hx, -⟩ := hWK i
            exact ⟨x, hx, hx⟩
          · rw [inter_comm]
            exact adjacent_meet_of_cover hXc W hWo (fun x _ => hWcov x) hWK hWdisj j i
              (by omega) }
  -- step 7: shrink to a chain in Bing–Jones's sense, keeping `cl U′_A`, `cl U′_B`
  have hXcont : Fold.Q78.IsContinuum (univ : Set X) := by
    obtain ⟨x0, -⟩ := hfs 0
    exact ⟨isCompact_univ, ⟨x0, mem_univ x0⟩, hXc⟩
  set C : Fin m → Set X := fun k => if k = i0 then closure UA' else if k = i1 then closure UB'
    else ∅ with hC
  have hi01 : i0 ≠ i1 := fun h => by
    have := congrArg Fin.val h
    simp only [hi0, hi1] at this
    omega
  have hCk : ∀ k, IsCompact (C k) ∧ C k ⊆ E0.link k := by
    intro k
    simp only [hC]
    split_ifs with h1 h2
    · subst h1; exact ⟨hUA'c, hUA'UA.trans hUAW⟩
    · subst h2; exact ⟨hUB'c, hUB'UB.trans hUBW⟩
    · exact ⟨isCompact_empty, empty_subset _⟩
  obtain ⟨E', hE'bj, hE'cov, -, hE'⟩ := exists_bjChain_shrink hXcont E0
    (fun x _ => hWcov x) hWK C hCk
  have hC0 : closure UA' ⊆ E'.link i0 := by
    have := (hE' i0).2
    simp only [hC, if_pos rfl] at this
    exact this
  have hC1 : closure UB' ⊆ E'.link i1 := by
    have := (hE' i1).2
    simp only [hC, if_neg hi01.symm] at this
    exact this
  refine ⟨E', hE'bj, hE'cov, fun t k => ?_, fun k => (subset_closure.trans (hE' k).1).trans
    (hWD k)⟩
  refine meets_all_of_meets_ends E' (hfib t) i0 i1 ?_ ?_ ?_ k (by simp only [hi0]; omega)
    (by simp only [hi1]; omega)
  · intro z _
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hE'cov (mem_univ z))
    exact mem_iUnion₂.2 ⟨j, ⟨by simp only [hi0]; omega, by simp only [hi1]; omega⟩, hj⟩
  · obtain ⟨y, hy, hyf⟩ := hUA'f t
    exact ⟨y, hC0 (subset_closure hy), hyf⟩
  · obtain ⟨y, hy, hyf⟩ := hUB'f t
    exact ⟨y, hC1 (subset_closure hy), hyf⟩

/-- **Theorem 8, general case with `r ≤ s`**, by folding along the walk
`r, r − 1, …, 0, 1, …, m − 1, m − 2, …, s`. -/
theorem bj_theorem8_le {f : X → unitInterval} (hf : IsContArcPA f)
    (hS : IsSnakeLike (univ : Set X)) {n m : ℕ} (hn : 3 ≤ n) (D : Chain X n)
    (hD : univ ⊆ D.union) (hDf : ∀ t j, (D.link j ∩ f ⁻¹' {t}).Nonempty)
    (H : Fin m → Fin n) (hH : IsChainMap H) {r s : Fin m} (hrs : r ≤ s) (hr : (H r).val = 0)
    (hs : (H s).val = n - 1) :
    ∃ E : Chain X m, IsBJChain E ∧ univ ⊆ E.union ∧ (∀ t i, (E.link i ∩ f ⁻¹' {t}).Nonempty) ∧
      ∀ i, E.link i ⊆ D.link (H i) := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) r.isLt
  have hL : 0 < unfoldLen m r s := by unfold unfoldLen; omega
  set π := unfoldFin (m := m) r s r.2 with hπ
  set H' : Fin (unfoldLen m r s) → Fin n := H ∘ π
  have hH' : IsChainMap H' := fun k l hkl => hH _ _ (unfoldFin_adj r s r.2 k l hkl)
  have h0 : (H' ⟨0, hL⟩).val = 0 := by
    have : π ⟨0, hL⟩ = r := Fin.ext (unfoldIdx_zero m r hm)
    simp only [H', Function.comp, this, hr]
  have h1 : (H' ⟨unfoldLen m r s - 1, by omega⟩).val = n - 1 := by
    have : π ⟨unfoldLen m r s - 1, by omega⟩ = s := Fin.ext (unfoldIdx_last hrs s.2)
    simp only [H', Function.comp, this, hs]
  obtain ⟨E', hE'bj, hE'cov, hE'f, hE'D⟩ := bj_theorem8_ends hf hS hn D hD hDf hL H' hH' h0 h1
  set E := foldChain E' π (unfoldFin_adj r s r.2) (unfoldMain r s) (unfoldFin_main r s r.2)
    (unfoldMain_adj r s)
  refine ⟨E, isBJChain_foldChain E' hE'bj _ _ _ _ _, fun x _ => ?_, fun t i => ?_, fun i => ?_⟩
  · obtain ⟨k, hk⟩ := mem_iUnion.1 (hE'cov (mem_univ x))
    exact mem_iUnion.2 ⟨_, link_subset_foldChain E' _ _ _ _ _ k hk⟩
  · obtain ⟨x, hx, hxf⟩ := hE'f t (unfoldMain r s i)
    refine ⟨x, ?_, hxf⟩
    have := link_subset_foldChain E' π (unfoldFin_adj r s r.2) (unfoldMain r s)
      (unfoldFin_main r s r.2) (unfoldMain_adj r s) (unfoldMain r s i) hx
    have e : π (unfoldMain r s i) = i := unfoldFin_main r s r.2 i
    rwa [e] at this
  · intro x hx
    rw [foldChain_link] at hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx
    have := hE'D k hxk
    simp only [H', Function.comp] at this
    rwa [hk] at this

/-- **Bing–Jones, Theorem 8** (p. 177), for continuous snake-like arcs of pseudo-arcs and chains of
at least three links. `D` is a chain in the library's sense; the conclusion is a chain in
Bing–Jones's sense. -/
theorem bj_theorem8 {f : X → unitInterval} (hf : IsContArcPA f) (hS : IsSnakeLike (univ : Set X))
    {n m : ℕ} (hn : 3 ≤ n) (D : Chain X n) (hD : univ ⊆ D.union)
    (hDf : ∀ t j, (D.link j ∩ f ⁻¹' {t}).Nonempty)
    (H : Fin m → Fin n) (hH : IsChainMap H) (hHs : Function.Surjective H) :
    ∃ E : Chain X m, IsBJChain E ∧ univ ⊆ E.union ∧ (∀ t i, (E.link i ∩ f ⁻¹' {t}).Nonempty) ∧
      ∀ i, E.link i ⊆ D.link (H i) := by
  obtain ⟨r, hr⟩ := hHs ⟨0, by omega⟩
  obtain ⟨s, hs⟩ := hHs ⟨n - 1, by omega⟩
  rcases le_total r s with hrs | hsr
  · exact bj_theorem8_le hf hS hn D hD hDf H hH hrs (by rw [hr]) (by rw [hs])
  · -- reverse `D`
    set H'' : Fin m → Fin n := fun i => Fin.rev (H i)
    have hH'' : IsChainMap H'' := by
      intro i j hij
      have := hH i j hij
      simp only [H'', Fin.val_rev]
      have := (H i).isLt
      have := (H j).isLt
      omega
    have hDr : univ ⊆ D.reverse.union := by
      intro x _
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hD (mem_univ x))
      exact mem_iUnion.2 ⟨Fin.rev j, by rw [Chain.reverse_link, Fin.rev_rev]; exact hj⟩
    have hDrf : ∀ t j, (D.reverse.link j ∩ f ⁻¹' {t}).Nonempty := fun t j => by
      rw [Chain.reverse_link]; exact hDf t _
    obtain ⟨E, hE1, hE2, hE3, hE4⟩ := bj_theorem8_le hf hS hn D.reverse hDr hDrf H'' hH'' hsr
      (by simp only [H'', Fin.val_rev, hs]; try omega) (by simp only [H'', Fin.val_rev, hr]; try omega)
    refine ⟨E, hE1, hE2, hE3, fun i => ?_⟩
    have := hE4 i
    simp only [H'', Chain.reverse_link, Fin.rev_rev] at this
    exact this

end Thm8

end HPC.BJ59
