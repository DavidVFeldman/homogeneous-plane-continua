import HPC.Moore.M25Plane
import HPC.Plane.Surgery91
import HPC.Jones.Jones49EArc

/-!
# Batch 165, item A.3: the crossing lemma

`rect_crossing_aux` (commission 165 §1, step 3), by the first route of the commission: a clopen split
of `K` (`exists_clopen_split`), then Janiszewski (`janiszewski_compact`) for
`A = K_b ∪ (lower frame)` and `B = K_t ∪ (upper frame)`, then an arc in the complement
(`exists_tarc_of_isOpen_plane`), cut at the last visit to the left edge and the following first
visit to the right edge.

The frame is a `U` open to the left: a block `[a − 2, b + 2] × [−2, 0]` below the rectangle and a
column `[b + 1, b + 2] × [0, c]` to its right (both in `A`), and a block `[a − 2, b + 2] × [c, c + 2]`
above it (in `B`). `A ∩ B` is the segment `[b + 1, b + 2] × {c}`. The two points are
`x = (a − 1/2, c/2)` and `y = (b + 1/2, c/2)`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Moore HPC.Moore.Gen HPC.Jones

/-- **The clopen split** of `K` (commission 165 §1, step 3). -/
theorem rect_split {a b c : ℝ} (hab : a < b) {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (hKR : K ⊆ Icc a b ×ˢ Icc 0 c) (hbot : Icc a b ×ˢ {0} ⊆ K)
    (hno : ∀ C ⊆ K, IsConnected C → (C ∩ Icc a b ×ˢ {c}).Nonempty →
      (C ∩ Icc a b ×ˢ {0}).Nonempty → False) :
    ∃ H Kt : Set (ℝ × ℝ), IsCompact H ∧ IsCompact Kt ∧ H ∪ Kt = K ∧ Disjoint H Kt ∧
      Icc a b ×ˢ {0} ⊆ H ∧ Disjoint H (Icc a b ×ˢ {c}) := by
  have hKc : IsCompact K := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hK hKR
  have hp0 : ((a, 0) : ℝ × ℝ) ∈ Icc a b ×ˢ ({0} : Set ℝ) := ⟨⟨le_rfl, hab.le⟩, rfl⟩
  have hp : ((a, 0) : ℝ × ℝ) ∈ K := hbot hp0
  have hTc : IsClosed (Icc a b ×ˢ ({c} : Set ℝ)) := isClosed_Icc.prod isClosed_singleton
  have hbotc : IsConnected (Icc a b ×ˢ ({0} : Set ℝ)) :=
    (isConnected_Icc hab.le).prod isConnected_singleton
  obtain ⟨H, Kt, hH, hKt, hU, hD, hpH, hHO⟩ := exists_clopen_split hKc hp hTc.isOpen_compl
    (fun A hA hAK hpA => by
      intro z hzA hzT
      exact hno (A ∪ Icc a b ×ˢ {0}) (union_subset hAK hbot)
        ⟨⟨z, Or.inl hzA⟩, IsPreconnected.union (a, 0) hpA hp0 hA hbotc.2⟩
        ⟨z, Or.inl hzA, hzT⟩ ⟨(a, 0), Or.inr hp0, hp0⟩)
  refine ⟨H, Kt, hH, hKt, hU, hD, ?_, ?_⟩
  · have := (isPreconnected_iff_subset_of_disjoint_closed.1 hbotc.2) H Kt hH.isClosed
      hKt.isClosed (hU ▸ hbot) (by rw [hD.inter_eq, inter_empty])
    rcases this with h | h
    · exact h
    · exact absurd (h hp0) (disjoint_left.1 hD hpH)
  · exact disjoint_left.2 fun z hz hzT => hHO hz hzT

/-- A "staple": two vertical segments joined by a horizontal one. -/
theorem staple_isPreconnected {x₁ x₂ lo hi e : ℝ} (hx : x₁ ≤ x₂) (hlo : lo ≤ e) (hhi : e ≤ hi) :
    IsPreconnected (({x₁} : Set ℝ) ×ˢ Icc lo hi ∪ Icc x₁ x₂ ×ˢ ({e} : Set ℝ) ∪
      ({x₂} : Set ℝ) ×ˢ Icc lo hi) := by
  have h1 : IsPreconnected (({x₁} : Set ℝ) ×ˢ Icc lo hi) :=
    isPreconnected_singleton.prod isPreconnected_Icc
  have h2 : IsPreconnected (Icc x₁ x₂ ×ˢ ({e} : Set ℝ)) :=
    isPreconnected_Icc.prod isPreconnected_singleton
  have h3 : IsPreconnected (({x₂} : Set ℝ) ×ˢ Icc lo hi) :=
    isPreconnected_singleton.prod isPreconnected_Icc
  have m1 : (x₁, e) ∈ ({x₁} : Set ℝ) ×ˢ Icc lo hi := ⟨rfl, hlo, hhi⟩
  have m2 : (x₁, e) ∈ Icc x₁ x₂ ×ˢ ({e} : Set ℝ) := ⟨⟨le_rfl, hx⟩, rfl⟩
  have m3 : (x₂, e) ∈ Icc x₁ x₂ ×ˢ ({e} : Set ℝ) := ⟨⟨hx, le_rfl⟩, rfl⟩
  have m4 : (x₂, e) ∈ ({x₂} : Set ℝ) ×ˢ Icc lo hi := ⟨rfl, hlo, hhi⟩
  have h12 := IsPreconnected.union (x₁, e) m1 m2 h1 h2
  exact IsPreconnected.union (x₂, e) (Or.inr m3) m4 h12 h3

/-- **The arc around the frame** (Janiszewski). -/
theorem frame_arc {a b c : ℝ} (hab : a < b) (hc : 0 < c) {H Kt : Set (ℝ × ℝ)} (hH : IsCompact H)
    (hKt : IsCompact Kt) (hHR : H ⊆ Icc a b ×ˢ Icc 0 c) (hKtR : Kt ⊆ Icc a b ×ˢ Icc 0 c)
    (hD : Disjoint H Kt) (hbotH : Icc a b ×ˢ {0} ⊆ H) (hHT : Disjoint H (Icc a b ×ˢ {c})) :
    ∃ C : Set (ℝ × ℝ), TArc ((a - 1 / 2, c / 2) : ℝ × ℝ) (b + 1 / 2, c / 2) C ∧
      Disjoint C (H ∪ Icc (a - 2) (b + 2) ×ˢ Icc (-2) 0 ∪ Icc (b + 1) (b + 2) ×ˢ Icc 0 c ∪
        (Kt ∪ Icc (a - 2) (b + 2) ×ˢ Icc c (c + 2))) := by
  set P : Set (ℝ × ℝ) := Icc (a - 2) (b + 2) ×ˢ Icc (-2) 0 with hP
  set Rc : Set (ℝ × ℝ) := Icc (b + 1) (b + 2) ×ˢ Icc 0 c with hRc
  set T : Set (ℝ × ℝ) := Icc (a - 2) (b + 2) ×ˢ Icc c (c + 2) with hT
  set x : ℝ × ℝ := (a - 1 / 2, c / 2) with hx
  set y : ℝ × ℝ := (b + 1 / 2, c / 2) with hy
  have hAc : IsCompact (H ∪ P ∪ Rc) :=
    (hH.union (isCompact_Icc.prod isCompact_Icc)).union (isCompact_Icc.prod isCompact_Icc)
  have hBc : IsCompact (Kt ∪ T) := hKt.union (isCompact_Icc.prod isCompact_Icc)
  have hAB : (H ∪ P ∪ Rc) ∩ (Kt ∪ T) = Icc (b + 1) (b + 2) ×ˢ {c} := by
    apply Subset.antisymm
    · rintro z ⟨((hz | hz) | hz), (hz' | hz')⟩
      · exact absurd hz' (disjoint_left.1 hD hz)
      · exfalso
        obtain ⟨⟨h1, h2⟩, -, h4⟩ := hHR hz
        obtain ⟨-, h5, -⟩ := hz'
        exact disjoint_left.1 hHT hz ⟨⟨h1, h2⟩, le_antisymm h4 h5⟩
      · exfalso
        obtain ⟨⟨h1, h2⟩, h3, -⟩ := hKtR hz'
        obtain ⟨-, -, h5⟩ := hz
        exact disjoint_left.1 hD (hbotH ⟨⟨h1, h2⟩, le_antisymm h5 h3⟩) hz'
      · exfalso
        obtain ⟨-, -, h5⟩ := hz
        obtain ⟨-, h6, -⟩ := hz'
        linarith
      · exfalso
        obtain ⟨⟨h1, -⟩, -⟩ := hz
        obtain ⟨⟨-, h2⟩, -⟩ := hKtR hz'
        linarith
      · obtain ⟨⟨h1, h2⟩, -, h4⟩ := hz
        obtain ⟨-, h5, -⟩ := hz'
        exact ⟨⟨h1, h2⟩, le_antisymm h4 h5⟩
    · rintro z ⟨⟨h1, h2⟩, h3⟩
      have h3' : z.2 = c := h3
      refine ⟨Or.inr ⟨⟨h1, h2⟩, ?_, ?_⟩, Or.inr ⟨⟨?_, h2⟩, ?_, ?_⟩⟩ <;>
        first | (rw [h3']; linarith) | linarith
  have hABc : IsConnected ((H ∪ P ∪ Rc) ∩ (Kt ∪ T)) := by
    rw [hAB]; exact (isConnected_Icc (by linarith)).prod isConnected_singleton
  -- points of `H`, `Kt`
  have hHx : ∀ z ∈ H, a ≤ z.1 ∧ z.1 ≤ b ∧ 0 ≤ z.2 ∧ z.2 ≤ c := fun z hz => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hHR hz; exact ⟨h1, h2, h3, h4⟩
  have hKtx : ∀ z ∈ Kt, a ≤ z.1 ∧ z.1 ≤ b ∧ 0 ≤ z.2 ∧ z.2 ≤ c := fun z hz => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hKtR hz; exact ⟨h1, h2, h3, h4⟩
  -- the staple over the top misses `A`
  set SA : Set (ℝ × ℝ) := ({a - 1 / 2} : Set ℝ) ×ˢ Icc (c / 2) (c + 3) ∪
    Icc (a - 1 / 2) (b + 1 / 2) ×ˢ ({c + 3} : Set ℝ) ∪ ({b + 1 / 2} : Set ℝ) ×ˢ Icc (c / 2) (c + 3)
  have hSA : IsPreconnected SA := staple_isPreconnected (by linarith) (by linarith) le_rfl
  have hSAA : SA ⊆ (H ∪ P ∪ Rc)ᶜ := by
    rintro z ((⟨h1, h2, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨h1, h2, h3⟩) ((hz | ⟨-, -, hz⟩) | ⟨⟨hz, -⟩, -⟩)
    all_goals
      first
      | (have h1' : z.1 = _ := h1; have := hHx z hz; linarith)
      | (have h3' : z.2 = _ := h3; have := hHx z hz; linarith)
      | (have h1' : z.1 = _ := h1; linarith)
      | (have h3' : z.2 = _ := h3; linarith)
  -- the staple below misses `B`
  set SB : Set (ℝ × ℝ) := ({a - 1 / 2} : Set ℝ) ×ˢ Icc (-3) (c / 2) ∪
    Icc (a - 1 / 2) (b + 1 / 2) ×ˢ ({-3} : Set ℝ) ∪ ({b + 1 / 2} : Set ℝ) ×ˢ Icc (-3) (c / 2)
  have hSB : IsPreconnected SB := staple_isPreconnected (by linarith) le_rfl (by linarith)
  have hSBB : SB ⊆ (Kt ∪ T)ᶜ := by
    rintro z ((⟨h1, h2, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨h1, h2, h3⟩) (hz | ⟨-, hz, -⟩)
    all_goals
      first
      | (have h1' : z.1 = _ := h1; have := hKtx z hz; linarith)
      | (have h3' : z.2 = _ := h3; have := hKtx z hz; linarith)
      | (have h3' : z.2 = _ := h3; linarith)
      | linarith
  have hxSA : x ∈ SA :=
    Or.inl (Or.inl ⟨rfl, show c / 2 ≤ c / 2 by linarith, show c / 2 ≤ c + 3 by linarith⟩)
  have hySA : y ∈ SA := Or.inr ⟨rfl, show c / 2 ≤ c / 2 by linarith, show c / 2 ≤ c + 3 by linarith⟩
  have hxSB : x ∈ SB :=
    Or.inl (Or.inl ⟨rfl, show -3 ≤ c / 2 by linarith, show c / 2 ≤ c / 2 by linarith⟩)
  have hySB : y ∈ SB := Or.inr ⟨rfl, show -3 ≤ c / 2 by linarith, show c / 2 ≤ c / 2 by linarith⟩
  have hsepA : ¬ SeparatesPts (H ∪ P ∪ Rc) x y := fun h =>
    h.2.2 ((hSA.subset_connectedComponentIn hxSA hSAA) hySA)
  have hsepB : ¬ SeparatesPts (Kt ∪ T) x y := fun h =>
    h.2.2 ((hSB.subset_connectedComponentIn hxSB hSBB) hySB)
  have hsep := janiszewski_compact hAc hBc (Or.inl hABc) hsepA hsepB
  have hxAB : x ∈ (H ∪ P ∪ Rc ∪ (Kt ∪ T))ᶜ := by
    rintro (h | h)
    · exact hSAA hxSA h
    · exact hSBB hxSB h
  have hyAB : y ∈ (H ∪ P ∪ Rc ∪ (Kt ∪ T))ᶜ := by
    rintro (h | h)
    · exact hSAA hySA h
    · exact hSBB hySB h
  have hyW : y ∈ connectedComponentIn (H ∪ P ∪ Rc ∪ (Kt ∪ T))ᶜ x := by
    by_contra hn
    exact hsep ⟨hxAB, hyAB, hn⟩
  have hopen : IsOpen (H ∪ P ∪ Rc ∪ (Kt ∪ T))ᶜ := (hAc.union hBc).isClosed.isOpen_compl
  have hxy : x ≠ y := by
    intro h
    have := congrArg Prod.fst h
    simp only [hx, hy] at this
    linarith
  obtain ⟨C, hCW, hC⟩ := exists_tarc_of_isOpen_plane hopen.connectedComponentIn
    (isConnected_connectedComponentIn_iff.2 hxAB) (mem_connectedComponentIn hxAB) hyW hxy
  exact ⟨C, hC, disjoint_left.2 fun z hz => connectedComponentIn_subset _ _ (hCW hz)⟩

/-- **Cutting the arc** at the last visit to the left edge and the following first visit to the
right edge. -/
theorem arc_cut {a b c : ℝ} (hab : a < b) (hc : 0 < c) {K : Set (ℝ × ℝ)} {f : unitInterval → ℝ × ℝ}
    (hf : IsEmbedding f) (hf0 : f 0 = (a - 1 / 2, c / 2)) (hf1 : f 1 = (b + 1 / 2, c / 2))
    (hfK : ∀ t, f t ∉ K ∪ Icc (a - 2) (b + 2) ×ˢ Icc (-2) 0 ∪ Icc (b + 1) (b + 2) ×ˢ Icc 0 c ∪
        Icc (a - 2) (b + 2) ×ˢ Icc c (c + 2)) :
    ∃ (r s : ℝ × ℝ) (I : Set (ℝ × ℝ)), TArc r s I ∧ I ⊆ (Icc a b ×ˢ Ioc 0 c) \ K ∧
      r.1 = a ∧ s.1 = b ∧ I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {r, s} := by
  set g : unitInterval → ℝ := fun t => (f t).1 with hg
  have hgc : Continuous g := continuous_fst.comp hf.continuous
  have hg0 : g 0 = a - 1 / 2 := by simp [hg, hf0]
  have hg1 : g 1 = b + 1 / 2 := by simp [hg, hf1]
  -- the last visit to the left edge
  set S1 : Set unitInterval := {t | g t ≤ a} with hS1
  have hS1c : IsClosed S1 := isClosed_le hgc continuous_const
  have hS1n : S1.Nonempty := ⟨0, by show g 0 ≤ a; rw [hg0]; linarith⟩
  set t1 := sSup S1 with ht1d
  have ht1 : t1 ∈ S1 := hS1c.isCompact.sSup_mem hS1n
  have hle1 : ∀ t ∈ S1, t ≤ t1 := fun t ht => le_csSup (OrderTop.bddAbove S1) ht
  have hga : g t1 = a := by
    obtain ⟨s, ⟨hs1, -⟩, hs⟩ := intermediate_value_Icc (unitInterval.le_one' : t1 ≤ 1) hgc.continuousOn
      ⟨(ht1 : g t1 ≤ a), by rw [hg1]; linarith⟩
    have : s ≤ t1 := hle1 s (show g s ≤ a by rw [hs])
    rw [← le_antisymm this hs1, hs]
  have hge1 : ∀ t, t1 ≤ t → a ≤ g t := fun t ht => by
    by_contra h
    push_neg at h
    have := le_antisymm (hle1 t h.le) ht
    rw [this, hga] at h
    exact lt_irrefl _ h
  have hgt1 : ∀ t, t1 < t → a < g t := fun t ht => by
    by_contra h
    push_neg at h
    exact absurd (hle1 t h) (not_le.2 ht)
  -- the first visit to the right edge after it
  set S2 : Set unitInterval := {t | t1 ≤ t ∧ b ≤ g t} with hS2
  have hS2c : IsClosed S2 :=
    (isClosed_le continuous_const continuous_id).inter (isClosed_le continuous_const hgc)
  have hS2n : S2.Nonempty := ⟨1, unitInterval.le_one', by show b ≤ g 1; rw [hg1]; linarith⟩
  set t2 := sInf S2 with ht2d
  have ht2 : t2 ∈ S2 := hS2c.isCompact.sInf_mem hS2n
  have hle2 : ∀ t ∈ S2, t2 ≤ t := fun t ht => csInf_le (OrderBot.bddBelow S2) ht
  have hgb : g t2 = b := by
    obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := intermediate_value_Icc ht2.1 hgc.continuousOn
      ⟨by rw [hga]; exact hab.le, ht2.2⟩
    have : t2 ≤ s := hle2 s ⟨hs1, by rw [hs]⟩
    rw [← le_antisymm hs2 this, hs]
  have hlt2 : ∀ t, t1 ≤ t → t < t2 → g t < b := fun t ht ht' => by
    by_contra h
    push_neg at h
    exact absurd (hle2 t ⟨ht, h⟩) (not_le.2 ht')
  have h12 : t1 < t2 := lt_of_le_of_ne ht2.1 fun h => by
    have := hgb; rw [← h, hga] at this; linarith
  -- after `t1` the arc stays inside the frame
  have hgood : ∀ t, t1 ≤ t → f t ∈ Ioo (a - 1) (b + 1) ×ˢ Ioo 0 c := by
    set u : Set (ℝ × ℝ) := Ioo (a - 1) (b + 1) ×ˢ Ioo 0 c
    set v : Set (ℝ × ℝ) := (Iic (b + 2) ×ˢ Icc (-2) (c + 2))ᶜ
    have hs : IsPreconnected (f '' Icc t1 1) := isPreconnected_Icc.image f hf.continuous.continuousOn
    have huv : f '' Icc t1 1 ⊆ u ∪ v := by
      rintro _ ⟨t, ⟨ht, -⟩, rfl⟩
      have hat := hge1 t ht
      by_cases hbox : f t ∈ Iic (b + 2) ×ˢ Icc (-2) (c + 2)
      · left
        obtain ⟨h1, h2, h3⟩ := hbox
        have h1' : (f t).1 ≤ b + 2 := h1
        have hat' : a ≤ (f t).1 := hat
        have h4 : 0 < (f t).2 := by
          by_contra h; push_neg at h
          exact hfK t (Or.inl (Or.inl (Or.inr ⟨⟨by linarith, h1'⟩, h2, h⟩)))
        have h5 : (f t).2 < c := by
          by_contra h; push_neg at h
          exact hfK t (Or.inr ⟨⟨by linarith, h1'⟩, h, h3⟩)
        have h6 : (f t).1 < b + 1 := by
          by_contra h; push_neg at h
          exact hfK t (Or.inl (Or.inr ⟨⟨h, h1'⟩, h4.le, h5.le⟩))
        exact ⟨⟨by linarith, h6⟩, h4, h5⟩
      · exact Or.inr hbox
    have hd : f '' Icc t1 1 ∩ (u ∩ v) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro z ⟨-, ⟨h1, h2⟩, hv⟩
      exact hv ⟨show z.1 ≤ b + 2 by linarith [h1.2], show -2 ≤ z.2 by linarith [h2.1],
        show z.2 ≤ c + 2 by linarith [h2.2]⟩
    rcases isPreconnected_iff_subset_of_disjoint.1 hs u v (isOpen_Ioo.prod isOpen_Ioo)
      (isClosed_Iic.prod isClosed_Icc).isOpen_compl huv hd with h | h
    · intro t ht; exact h ⟨t, ⟨ht, unitInterval.le_one'⟩, rfl⟩
    · exfalso
      have h1 := h ⟨1, ⟨unitInterval.le_one', le_rfl⟩, rfl⟩
      rw [hf1] at h1
      exact h1 ⟨show b + 1 / 2 ≤ b + 2 by linarith, by linarith, by linarith⟩
  refine ⟨f t1, f t2, f '' Icc t1 t2, TArc.image_Icc hf h12, ?_, hga, hgb, ?_⟩
  · rintro _ ⟨t, ⟨ht, ht'⟩, rfl⟩
    obtain ⟨-, h2, h3⟩ := hgood t ht
    refine ⟨⟨⟨hge1 t ht, ?_⟩, h2, h3.le⟩, fun hK => hfK t (Or.inl (Or.inl (Or.inl hK)))⟩
    rcases eq_or_lt_of_le ht' with h | h
    · show g t ≤ b; rw [h, hgb]
    · exact (hlt2 t ht h).le
  · apply Subset.antisymm
    · rintro _ ⟨⟨t, ⟨ht, ht'⟩, rfl⟩, h1, -⟩
      rcases eq_or_lt_of_le ht with h | h
      · rw [h]; exact Or.inl rfl
      rcases eq_or_lt_of_le ht' with h' | h'
      · rw [h']; exact Or.inr rfl
      exfalso
      have ha := hgt1 t h
      have hb := hlt2 t ht h'
      rcases h1 with h1 | h1
      · exact absurd (show g t = a from h1) ha.ne'
      · exact absurd (show g t = b from h1) hb.ne
    · rintro _ (rfl | rfl)
      · obtain ⟨-, h2, h3⟩ := hgood t1 le_rfl
        exact ⟨⟨t1, ⟨le_rfl, ht2.1⟩, rfl⟩, Or.inl hga, h2.le, h3.le⟩
      · obtain ⟨-, h2, h3⟩ := hgood t2 ht2.1
        exact ⟨⟨t2, ⟨ht2.1, le_rfl⟩, rfl⟩, Or.inr hgb, h2.le, h3.le⟩

/-- **The crossing lemma** (commission 165 §1, step 3). -/
theorem rect_crossing_aux {a b c : ℝ} (hab : a < b) (hc : 0 < c) {K : Set (ℝ × ℝ)}
    (hK : IsClosed K) (hKR : K ⊆ Icc a b ×ˢ Icc 0 c) (hbot : Icc a b ×ˢ {0} ⊆ K)
    (hno : ∀ C ⊆ K, IsConnected C → (C ∩ Icc a b ×ˢ {c}).Nonempty →
      (C ∩ Icc a b ×ˢ {0}).Nonempty → False) :
    ∃ (r s : ℝ × ℝ) (I : Set (ℝ × ℝ)), TArc r s I ∧ I ⊆ (Icc a b ×ˢ Ioc 0 c) \ K ∧
      r.1 = a ∧ s.1 = b ∧ I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {r, s} := by
  obtain ⟨H, Kt, hH, hKt, hU, hD, hbotH, hHT⟩ := rect_split hab hK hKR hbot hno
  have hHR : H ⊆ Icc a b ×ˢ Icc 0 c := fun z hz => hKR (hU ▸ Or.inl hz)
  have hKtR : Kt ⊆ Icc a b ×ˢ Icc 0 c := fun z hz => hKR (hU ▸ Or.inr hz)
  obtain ⟨C, ⟨-, f, hf, hfC, hf0, hf1⟩, hCd⟩ := frame_arc hab hc hH hKt hHR hKtR hD hbotH hHT
  refine arc_cut hab hc hf hf0 hf1 fun t ht => ?_
  have hft : f t ∈ C := hfC ▸ mem_range_self t
  apply disjoint_left.1 hCd hft
  rw [← hU] at ht
  rcases ht with (((h | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

end HPC.Hagopian
