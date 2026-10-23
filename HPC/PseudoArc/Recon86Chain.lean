import HPC.PseudoArc.Recon86
import HPC.Fold.Theorem4Pair

/-!
# Batch 86: `P'` and `R` are opposite end points of `W` (commission §1.3 Q3 (b))

`Description.exists_chain_from_of_irreducible`: if `W ⊆ M` is irreducible between the distinct
points `P'` and `R` of `M`, then for every `ε > 0` there is a chain **from `P'` to `R`** (in the
repository's strong sense `IsFrom`: `P'` in the first link only, `R` in the last link only)
covering `W`, every link of which is a union of links of one level `D_k` and has all its points
within `ε` of each other. So Q3 (b) holds, and the chain can be taken to consist of unions of links
of a deep `D_k`.

The proof: the links of `D_k` meeting `W` form an interval `[a', c']` (`Chain.meet_ordConnected`);
by the window property (`window_of_irreducible`) they refine the stretch `[lo, hi]` of a coarser
level `D_{L'}` swept by the subchain `D_k(P', R)`, whose ends it meets; Theorem 4 in its paired
form (`theorem4_pair`) then folds `D_k(a', c')` with the links of `P'` in the first block and those
of `R` in the last.
-/

namespace HPC

open Set Metric

variable {X : Type*} [MetricSpace X]

namespace Chain

theorem mem_ofBlocks_link {n p : ℕ} (E : Chain X n) {β : Fin n → Fin p} (hβ : IsBlockMap β)
    (u : Fin p) (x : X) : x ∈ (E.ofBlocks β hβ).link u ↔ ∃ t, β t = u ∧ x ∈ E.link t := by
  rw [ofBlocks_link]
  simp only [mem_iUnion, mem_setOf_eq, exists_prop]

/-- Points of links at most two apart in a chain of mesh `δ` are within `3δ`. -/
theorem dist_le_of_near {n : ℕ} (D : Chain X n) {δ : ℝ}
    (hbdd : ∀ t, Bornology.IsBounded (D.link t)) (hdiam : ∀ t, diam (D.link t) ≤ δ)
    {i i' : Fin n} (hii : i.val ≤ i'.val + 2 ∧ i'.val ≤ i.val + 2) {x y : X}
    (hx : x ∈ D.link i) (hy : y ∈ D.link i') : dist x y ≤ 3 * δ := by
  have hδ : 0 ≤ δ := le_trans diam_nonneg (hdiam i)
  have hd : ∀ t, ∀ z ∈ D.link t, ∀ w ∈ D.link t, dist z w ≤ δ := fun t z hz w hw =>
    (dist_le_diam_of_mem (hbdd t) hz hw).trans (hdiam t)
  have hmeet : ∀ j j' : Fin n, j.val ≤ j'.val + 1 → j'.val ≤ j.val + 1 →
      ∃ z, z ∈ D.link j ∧ z ∈ D.link j' := fun j j' h1 h2 => by
    obtain ⟨z, hz⟩ := (D.adjacent_iff j j').mpr ⟨h1, h2⟩
    exact ⟨z, hz.1, hz.2⟩
  by_cases h1 : i.val ≤ i'.val + 1 ∧ i'.val ≤ i.val + 1
  · obtain ⟨z, hz, hz'⟩ := hmeet i i' h1.1 h1.2
    have := dist_triangle x z y
    have := hd i x hx z hz
    have := hd i' z hz' y hy
    linarith
  · -- two apart: go through the middle link
    have hm : (i.val + i'.val) / 2 < n := by omega
    set m : Fin n := ⟨(i.val + i'.val) / 2, hm⟩
    obtain ⟨z, hz, hzm⟩ := hmeet i m (by simp only [m]; omega) (by simp only [m]; omega)
    obtain ⟨w, hwm, hw⟩ := hmeet m i' (by simp only [m]; omega) (by simp only [m]; omega)
    have := dist_triangle4 x z w y
    have := hd i x hx z hz
    have := hd m z hzm w hwm
    have := hd i' w hw y hy
    linarith

/-- **Theorem 4, paired, read as a chain from `A` to `B`.** If `E` is crooked in `C` (at least
three links), `A` lies in `E.link a` and in no later link up to `b`, `B` lies in `E.link b` and in
no earlier link from `a`, `b ≥ a + 2`, and the links from `a` to `b` meet the first and the last
link of `C`, then a block consolidation of `E`, every block in three consecutive links of `C`, is a
chain from `A` to `B`. -/
theorem exists_blocks_isFrom {m nC : ℕ} {E : Chain X m} {C : Chain X nC} (hC : 3 ≤ nC)
    (hcr : E.IsCrookedIn' C) {A B : X} {a b : Fin m} (hab : a.val + 2 ≤ b.val)
    (hA : A ∈ E.link a) (hB : B ∈ E.link b)
    (hAu : ∀ u : Fin m, a < u → u ≤ b → A ∉ E.link u)
    (hBu : ∀ u : Fin m, a ≤ u → u < b → B ∉ E.link u)
    (hlow : ∃ h : Fin m, a ≤ h ∧ h ≤ b ∧ (E.link h ∩ C.link ⟨0, by omega⟩).Nonempty)
    (hhigh : ∃ h : Fin m, a ≤ h ∧ h ≤ b ∧ (E.link h ∩ C.link ⟨nC - 1, by omega⟩).Nonempty) :
    ∃ (q : ℕ) (β : Fin m → Fin q) (hβ : IsBlockMap β),
      (E.ofBlocks β hβ).IsFrom A B ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ C.unionRange j 3 := by
  classical
  -- the links containing `A` are `a` and possibly `a - 1`
  have hAnear : ∀ u : Fin m, A ∈ E.link u → u.val + 1 = a.val ∨ u = a := by
    intro u hu
    have hadj := (E.adjacent_iff u a).mp ⟨A, hu, hA⟩
    rcases lt_trichotomy u.val a.val with h | h | h
    · left; omega
    · right; exact Fin.ext h
    · exfalso
      exact hAu u (Fin.lt_def.mpr h) (Fin.le_def.mpr (by omega)) hu
  have hBnear : ∀ u : Fin m, B ∈ E.link u → u.val = b.val + 1 ∨ u = b := by
    intro u hu
    have hadj := (E.adjacent_iff u b).mp ⟨B, hu, hB⟩
    rcases lt_trichotomy u.val b.val with h | h | h
    · exfalso
      exact hBu u (Fin.le_def.mpr (by omega)) (Fin.lt_def.mpr h) hu
    · right; exact Fin.ext h
    · left; omega
  obtain ⟨r, hra, hAr, hAr'⟩ : ∃ r : Fin m, r.val ≤ a.val ∧ A ∈ E.link r ∧
      ∀ u : Fin m, A ∈ E.link u → u = r ∨ u.val = r.val + 1 := by
    by_cases h : ∃ u : Fin m, u.val + 1 = a.val ∧ A ∈ E.link u
    · obtain ⟨u0, hu0, hAu0⟩ := h
      refine ⟨u0, by omega, hAu0, fun u hu => ?_⟩
      rcases hAnear u hu with h' | h'
      · left; exact Fin.ext (by omega)
      · right; rw [h']; omega
    · refine ⟨a, le_rfl, hA, fun u hu => ?_⟩
      rcases hAnear u hu with h' | h'
      · exact absurd ⟨u, h', hu⟩ h
      · left; exact h'
  obtain ⟨s, hsb, hBs, hBs'⟩ : ∃ s : Fin m, b.val ≤ s.val ∧ B ∈ E.link s ∧
      ∀ u : Fin m, B ∈ E.link u → u = s ∨ u.val + 1 = s.val := by
    by_cases h : ∃ u : Fin m, u.val = b.val + 1 ∧ B ∈ E.link u
    · obtain ⟨u0, hu0, hBu0⟩ := h
      refine ⟨u0, by omega, hBu0, fun u hu => ?_⟩
      rcases hBnear u hu with h' | h'
      · left; exact Fin.ext (by omega)
      · right; rw [h']; omega
    · refine ⟨b, le_rfl, hB, fun u hu => ?_⟩
      rcases hBnear u hu with h' | h'
      · exact absurd ⟨u, h', hu⟩ h
      · left; exact h'
  have hbm := b.isLt
  have hsm := s.isLt
  set r' : Fin m := ⟨r.val + 1, by omega⟩ with hr'
  set s' : Fin m := ⟨s.val - 1, by omega⟩ with hs'
  obtain ⟨hl, hal, hlb, hlm⟩ := hlow
  obtain ⟨hh, hah, hhb, hhm⟩ := hhigh
  obtain ⟨q, β, hβ, h0, h0', h1', h1, hblk⟩ := Fold.theorem4_pair hC hcr r r' s' s rfl
    (by simp only [hs']; omega) (Fin.le_def.mpr (by simp only [hr', hs']; omega))
    ⟨hl, Fin.le_def.mpr (by rw [Fin.le_def] at hal; omega),
      Fin.le_def.mpr (by rw [Fin.le_def] at hlb; omega), hlm⟩
    ⟨hh, Fin.le_def.mpr (by rw [Fin.le_def] at hah; omega),
      Fin.le_def.mpr (by rw [Fin.le_def] at hhb; omega), hhm⟩
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (β a).isLt
  refine ⟨q, β, hβ, ⟨hq, ?_, ?_, ?_, ?_⟩, hblk⟩
  · exact (mem_ofBlocks_link E hβ _ _).mpr ⟨r, Fin.ext h0, hAr⟩
  · exact (mem_ofBlocks_link E hβ _ _).mpr ⟨s, Fin.ext h1, hBs⟩
  · intro u hu
    obtain ⟨t, rfl, ht⟩ := (mem_ofBlocks_link E hβ _ _).mp hu
    rcases hAr' t ht with h | h
    · rw [h]; exact Fin.ext h0
    · have : t = r' := Fin.ext h
      rw [this]; exact Fin.ext h0'
  · intro u hu
    obtain ⟨t, rfl, ht⟩ := (mem_ofBlocks_link E hβ _ _).mp hu
    rcases hBs' t ht with h | h
    · rw [h]; exact Fin.ext h1
    · have : t = s' := Fin.ext (by simp only [hs']; omega)
      rw [this]; exact Fin.ext h1'

end Chain

namespace Description

variable {P Q : X}

/-- **`P'` and `R` are opposite end points of `W`** (commission §1.3 Q3 (b)). If `W ⊆ M` is
irreducible between the distinct points `P'` and `R` of `M`, then for every `ε > 0` some level
`D_k` has a chain from `P'` to `R` covering `W`, each link a union of links of `D_k` and of
`dist`-spread at most `ε`. -/
theorem exists_chain_from_of_irreducible [CompactSpace X] (Δ : Description X P Q) {P' R : X}
    (hP' : P' ∈ Δ.M) (hR : R ∈ Δ.M) (hPR : P' ≠ R) {W : Set X} (hW : W ⊆ Δ.M)
    (hWirr : IsIrreducibleBetween W P' R) {ε : ℝ} (hε : 0 < ε) :
    ∃ k N, ∃ F : Chain X N, F.IsFrom P' R ∧ W ⊆ F.union ∧
      (∀ u, ∃ S : Set (Fin (Δ.n k)), F.link u = ⋃ i ∈ S, (Δ.D k).link i) ∧
      ∀ u, ∀ x ∈ F.link u, ∀ y ∈ F.link u, dist x y ≤ ε := by
  classical
  have hd : 0 < dist P' R := dist_pos.mpr hPR
  have hPW : P' ∈ W := hWirr.2.1
  have hRW : R ∈ W := hWirr.2.2.1
  have hWc : IsPreconnected W := hWirr.1.2.isPreconnected
  -- the coarse level `L'`
  obtain ⟨L', hL'⟩ := (Metric.tendsto_atTop.mp Δ.ε_tendsto) (min (ε / 3) (dist P' R / 2))
    (lt_min (by linarith) (by linarith))
  have hεL : Δ.ε L' < min (ε / 3) (dist P' R / 2) := by
    have := hL' L' le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_pos (Δ.ε_pos L')] at this
  have hεL1 : Δ.ε L' < ε / 3 := lt_of_lt_of_le hεL (min_le_left _ _)
  have hεL2 : Δ.ε L' < dist P' R / 2 := lt_of_lt_of_le hεL (min_le_right _ _)
  -- the fine level `k`
  obtain ⟨Nw, hNw⟩ := Δ.window_of_irreducible hP' hR hPR hW hWirr L'
  obtain ⟨K2, hK2⟩ := (Metric.tendsto_atTop.mp Δ.ε_tendsto) (dist P' R / 2) (by linarith)
  set k := max (max Nw (L' + 1)) K2 with hk
  have hkN : Nw ≤ k := le_trans (le_max_left _ _) (le_max_left _ _)
  have hLk : L' < k := lt_of_lt_of_le (Nat.lt_succ_self _)
    (le_trans (le_max_right _ _) (le_max_left _ _))
  have hεk : Δ.ε k < dist P' R / 2 := by
    have := hK2 k (le_max_right _ _)
    rwa [Real.dist_eq, sub_zero, abs_of_pos (Δ.ε_pos k)] at this
  have hbddk := Δ.bdd k
  have hdk : ∀ t, ∀ x ∈ (Δ.D k).link t, ∀ y ∈ (Δ.D k).link t, dist x y ≤ Δ.ε k :=
    fun t x hx y hy => (dist_le_diam_of_mem (Δ.bdd k t) hx hy).trans (Δ.diam_le k t)
  have hdL : ∀ t, ∀ x ∈ (Δ.D L').link t, ∀ y ∈ (Δ.D L').link t, dist x y ≤ Δ.ε L' :=
    fun t x hx y hy => (dist_le_diam_of_mem (Δ.bdd L' t) hx hy).trans (Δ.diam_le L' t)
  -- the subchain from `P'` to `R`
  obtain ⟨a, b, hsub⟩ := Δ.exists_isSubchainFrom_of_lt hP' hR (by linarith : Δ.ε k < dist P' R)
  obtain ⟨hab, hends⟩ := hsub.ends
  have hWD : W ⊆ (Δ.D k).union := hW.trans (Δ.M_subset_union k)
  -- the links from `a` to `b` are at least two apart
  have hab2 : a.val + 2 ≤ b.val := by
    by_contra hcon
    have hadj := (Δ.D k).adjacent_iff a b
    obtain ⟨z, hza, hzb⟩ := hadj.mpr ⟨by rw [Fin.le_def] at hab; omega, by omega⟩
    have key : ∀ x ∈ (Δ.D k).link a, ∀ y ∈ (Δ.D k).link b, dist x y ≤ 2 * Δ.ε k :=
      fun x hx y hy => by
        have := dist_triangle x z y
        have := hdk a x hx z hza
        have := hdk b z hzb y hy
        linarith
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := key _ h1 _ h2; linarith
    · have := key _ h1 _ h2; rw [dist_comm] at this; linarith
  -- the interval of links meeting `W`
  set Sw : Finset (Fin (Δ.n k)) := Finset.univ.filter fun u => ((Δ.D k).link u ∩ W).Nonempty
  have haS : a ∈ Sw := by
    simp only [Sw, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨P', h1, hPW⟩
    · exact ⟨R, h1, hRW⟩
  have hbS : b ∈ Sw := by
    simp only [Sw, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hends with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact ⟨R, h2, hRW⟩
    · exact ⟨P', h2, hPW⟩
  set a' := Sw.min' ⟨a, haS⟩
  set c' := Sw.max' ⟨a, haS⟩
  have ha'S : a' ∈ Sw := Sw.min'_mem _
  have hc'S : c' ∈ Sw := Sw.max'_mem _
  have ha'a : a' ≤ a := Sw.min'_le a haS
  have hbc' : b ≤ c' := Sw.le_max' b hbS
  have hac : a' ≤ c' := ha'a.trans (hab.trans hbc')
  have hmeetI : ∀ u : Fin (Δ.n k), a' ≤ u → u ≤ c' → ((Δ.D k).link u ∩ W).Nonempty := by
    intro u h1 h2
    have e1 : ((Δ.D k).link a' ∩ W).Nonempty := by
      simpa [Sw] using ha'S
    have e2 : ((Δ.D k).link c' ∩ W).Nonempty := by
      simpa [Sw] using hc'S
    exact (Δ.D k).meet_ordConnected hWc hWD h1 h2 e1 e2
  have hSwI : ∀ u : Fin (Δ.n k), ((Δ.D k).link u ∩ W).Nonempty → a' ≤ u ∧ u ≤ c' := by
    intro u hu
    have huS : u ∈ Sw := by simp only [Sw, Finset.mem_filter, Finset.mem_univ, true_and]; exact hu
    exact ⟨Sw.min'_le u huS, Sw.le_max' u huS⟩
  -- the coarse stretch swept by the subchain
  set T : Finset (Fin (Δ.n L')) := Finset.univ.filter fun s =>
    ∃ v : Fin (Δ.n k), a ≤ v ∧ v ≤ b ∧ (Δ.D k).link v ⊆ (Δ.D L').link s
  have hrefkL := Δ.refines_of_le hLk.le
  have hTne : T.Nonempty := by
    obtain ⟨s, hs⟩ := hrefkL a
    exact ⟨s, by simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact
      ⟨a, le_rfl, hab, hs⟩⟩
  set lo := T.min' hTne
  set hi := T.max' hTne
  have hloT : lo ∈ T := T.min'_mem _
  have hhiT : hi ∈ T := T.max'_mem _
  have hlohi : lo ≤ hi := T.min'_le_max' hTne
  have hTmem : ∀ s : Fin (Δ.n L'), s ∈ T → lo ≤ s ∧ s ≤ hi := fun s hs =>
    ⟨T.min'_le s hs, T.le_max' s hs⟩
  -- the stretch has at least three links
  have hlohi2 : lo.val + 2 ≤ hi.val := by
    by_contra hcon
    obtain ⟨s1, hs1⟩ := hrefkL a
    obtain ⟨s2, hs2⟩ := hrefkL b
    have h1T : s1 ∈ T := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨a, le_rfl, hab, hs1⟩
    have h2T : s2 ∈ T := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨b, hab, le_rfl, hs2⟩
    obtain ⟨l1, u1⟩ := hTmem s1 h1T
    obtain ⟨l2, u2⟩ := hTmem s2 h2T
    rw [Fin.le_def] at l1 u1 l2 u2
    obtain ⟨z, hz1, hz2⟩ := ((Δ.D L').adjacent_iff s1 s2).mpr ⟨by omega, by omega⟩
    have key : ∀ x ∈ (Δ.D k).link a, ∀ y ∈ (Δ.D k).link b, dist x y ≤ 2 * Δ.ε L' :=
      fun x hx y hy => by
        have := dist_triangle x z y
        have := hdL s1 x (hs1 hx) z hz1
        have := hdL s2 z hz2 y (hs2 hy)
        linarith
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := key _ h1 _ h2; linarith
    · have := key _ h1 _ h2; rw [dist_comm] at this; linarith
  -- the fine chain `E` and the coarse chain `C`
  set E := (Δ.D k).sub a' c' hac with hE
  set C := (Δ.D L').sub lo hi hlohi with hC
  have hElink : ∀ t : Fin (c'.val - a'.val + 1),
      E.link t = (Δ.D k).link ⟨a'.val + t.val, by have := t.isLt; have := c'.isLt; omega⟩ :=
    fun _ => rfl
  have hClink : ∀ t : Fin (hi.val - lo.val + 1),
      C.link t = (Δ.D L').link ⟨lo.val + t.val, by have := t.isLt; have := hi.isLt; omega⟩ :=
    fun _ => rfl
  have hEref : E.Refines C := by
    intro t
    have ht := t.isLt
    have hc'l := c'.isLt
    set u : Fin (Δ.n k) := ⟨a'.val + t.val, by omega⟩ with hu
    have hmu := hmeetI u (Fin.le_def.mpr (by simp only [hu]; omega))
      (Fin.le_def.mpr (by simp only [hu]; omega))
    obtain ⟨v, hav, hvb, s, hus, hvs⟩ := hNw k hkN a b hsub u hmu
    have hsT : s ∈ T := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨v, hav, hvb, hvs⟩
    obtain ⟨hls, hsh⟩ := hTmem s hsT
    rw [Fin.le_def] at hls hsh
    refine ⟨⟨s.val - lo.val, by omega⟩, ?_⟩
    rw [hElink, hClink]
    have : (⟨lo.val + (s.val - lo.val), by have := hi.isLt; omega⟩ : Fin (Δ.n L')) = s :=
      Fin.ext (by simp only; omega)
    rw [this]
    exact hus
  have hcrE : E.IsCrookedIn' C :=
    ((Δ.crooked_of_lt hLk).sub a' c' hac).restrict lo hi hlohi hEref
  have hnC : 3 ≤ hi.val - lo.val + 1 := by omega
  -- indices of `a`, `b` in `E`
  rw [Fin.le_def] at ha'a hbc' hab
  have hc'l := c'.isLt
  set aE : Fin (c'.val - a'.val + 1) := ⟨a.val - a'.val, by omega⟩ with haE
  set bE : Fin (c'.val - a'.val + 1) := ⟨b.val - a'.val, by omega⟩ with hbE
  have hEa : E.link aE = (Δ.D k).link a := by
    rw [hElink]; congr 1; ext; simp only [haE]; omega
  have hEb : E.link bE = (Δ.D k).link b := by
    rw [hElink]; congr 1; ext; simp only [hbE]; omega
  have hab2E : aE.val + 2 ≤ bE.val := by simp only [haE, hbE]; omega
  -- the ends of the stretch are met between `a` and `b`
  have hlowE : ∃ h : Fin (c'.val - a'.val + 1), aE ≤ h ∧ h ≤ bE ∧
      (E.link h ∩ C.link ⟨0, by omega⟩).Nonempty := by
    obtain ⟨v, hav, hvb, hvs⟩ : ∃ v : Fin (Δ.n k), a ≤ v ∧ v ≤ b ∧
        (Δ.D k).link v ⊆ (Δ.D L').link lo := by
      simpa [T] using hloT
    rw [Fin.le_def] at hav hvb
    refine ⟨⟨v.val - a'.val, by omega⟩, Fin.le_def.mpr (by simp only [haE]; omega),
      Fin.le_def.mpr (by simp only [hbE]; omega), ?_⟩
    have hEv : E.link ⟨v.val - a'.val, by omega⟩ = (Δ.D k).link v := by
      rw [hElink]; congr 1; ext; simp only; omega
    have hC0 : C.link ⟨0, by omega⟩ = (Δ.D L').link lo := by
      rw [hClink]; congr 1
    rw [hEv, hC0]
    obtain ⟨z, hz⟩ := (Δ.D k).link_nonempty v
    exact ⟨z, hz, hvs hz⟩
  have hhighE : ∃ h : Fin (c'.val - a'.val + 1), aE ≤ h ∧ h ≤ bE ∧
      (E.link h ∩ C.link ⟨hi.val - lo.val + 1 - 1, by omega⟩).Nonempty := by
    obtain ⟨v, hav, hvb, hvs⟩ : ∃ v : Fin (Δ.n k), a ≤ v ∧ v ≤ b ∧
        (Δ.D k).link v ⊆ (Δ.D L').link hi := by
      simpa [T] using hhiT
    rw [Fin.le_def] at hav hvb
    refine ⟨⟨v.val - a'.val, by omega⟩, Fin.le_def.mpr (by simp only [haE]; omega),
      Fin.le_def.mpr (by simp only [hbE]; omega), ?_⟩
    have hEv : E.link ⟨v.val - a'.val, by omega⟩ = (Δ.D k).link v := by
      rw [hElink]; congr 1; ext; simp only; omega
    have hCl : C.link ⟨hi.val - lo.val + 1 - 1, by omega⟩ = (Δ.D L').link hi := by
      rw [hClink]; congr 1; ext; simp only; omega
    rw [hEv, hCl]
    obtain ⟨z, hz⟩ := (Δ.D k).link_nonempty v
    exact ⟨z, hz, hvs hz⟩
  -- the exclusion hypotheses, read in `E`
  obtain ⟨hab', hor⟩ := hsub
  have hsublink : ∀ t : Fin (b.val - a.val + 1),
      ((Δ.D k).sub a b hab').link t = (Δ.D k).link ⟨a.val + t.val, by
        have := t.isLt; have := b.isLt; omega⟩ := fun _ => rfl
  have hEsub : ∀ (Z : X) (u : Fin (c'.val - a'.val + 1)), aE ≤ u → u ≤ bE → Z ∈ E.link u →
      ∃ i : Fin (b.val - a.val + 1), i.val = u.val - aE.val ∧
        Z ∈ ((Δ.D k).sub a b hab').link i := by
    intro Z u h1 h2 hZ
    have h1' := Fin.le_def.mp h1
    have h2' := Fin.le_def.mp h2
    simp only [haE, hbE] at h1' h2'
    refine ⟨⟨u.val - (a.val - a'.val), by omega⟩, rfl, ?_⟩
    rw [hElink] at hZ
    rw [hsublink]
    have e : (⟨a.val + (u.val - (a.val - a'.val)), by have := b.isLt; omega⟩ : Fin (Δ.n k)) =
        ⟨a'.val + u.val, by have := u.isLt; omega⟩ := Fin.ext (by simp only; omega)
    rw [e]; exact hZ
  -- the general facts about a block consolidation of `E`
  have hfinal : ∀ (q : ℕ) (β : Fin (c'.val - a'.val + 1) → Fin q) (hβ : Chain.IsBlockMap β),
      (∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ C.unionRange j 3) →
      W ⊆ (E.ofBlocks β hβ).union ∧
      (∀ u, ∃ S : Set (Fin (Δ.n k)), (E.ofBlocks β hβ).link u = ⋃ i ∈ S, (Δ.D k).link i) ∧
      ∀ u, ∀ x ∈ (E.ofBlocks β hβ).link u, ∀ y ∈ (E.ofBlocks β hβ).link u, dist x y ≤ ε := by
    intro q β hβ hblk
    refine ⟨fun w hw => ?_, fun u => ?_, fun u x hx y hy => ?_⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hWD hw)
      obtain ⟨h1, h2⟩ := hSwI i ⟨w, hi, hw⟩
      rw [Fin.le_def] at h1 h2
      set t : Fin (c'.val - a'.val + 1) := ⟨i.val - a'.val, by omega⟩
      have hEt : E.link t = (Δ.D k).link i := by
        rw [hElink]; congr 1; ext; simp only [t]; omega
      refine mem_iUnion.mpr ⟨β t, (Chain.mem_ofBlocks_link E hβ _ _).mpr ⟨t, rfl, ?_⟩⟩
      rw [hEt]; exact hi
    · refine ⟨{i | ∃ t : Fin (c'.val - a'.val + 1), β t = u ∧ i.val = a'.val + t.val}, ?_⟩
      ext x
      rw [Chain.mem_ofBlocks_link]
      simp only [mem_iUnion, mem_setOf_eq, exists_prop]
      constructor
      · rintro ⟨t, htu, hxt⟩
        exact ⟨⟨a'.val + t.val, by have := t.isLt; omega⟩, ⟨t, htu, rfl⟩, by
          rw [hElink] at hxt; exact hxt⟩
      · rintro ⟨i, ⟨t, htu, hit⟩, hxi⟩
        refine ⟨t, htu, ?_⟩
        rw [hElink]
        have : (⟨a'.val + t.val, by have := t.isLt; omega⟩ : Fin (Δ.n k)) = i := Fin.ext hit.symm
        rw [this]; exact hxi
    · obtain ⟨j, hj⟩ := hblk u
      obtain ⟨j1, hj1, hj1', hj1l, hx1⟩ := Chain.mem_unionRange.mp (hj hx)
      obtain ⟨j2, hj2, hj2', hj2l, hy2⟩ := Chain.mem_unionRange.mp (hj hy)
      have hCb : ∀ t, Bornology.IsBounded (C.link t) := fun t => by
        rw [hClink]; exact Δ.bdd L' _
      have hCd : ∀ t, diam (C.link t) ≤ Δ.ε L' := fun t => by
        rw [hClink]; exact Δ.diam_le L' _
      have := Chain.dist_le_of_near C hCb hCd (i := ⟨j1, hj1l⟩) (i' := ⟨j2, hj2l⟩)
        ⟨by simp only; omega, by simp only; omega⟩ hx1 hy2
      linarith
  rcases hor with hfrom | hfrom
  · -- `P'` at the low end
    obtain ⟨hn0, hP0, hRl, hPu, hRu⟩ := hfrom
    obtain ⟨q, β, hβ, hF, hblk⟩ := Chain.exists_blocks_isFrom hnC hcrE hab2E
      (by rw [hEa]; simpa [Chain.sub] using hP0)
      (by
        rw [hEb]
        have e : (⟨a.val + (b.val - a.val + 1 - 1), by omega⟩ : Fin (Δ.n k)) = b :=
          Fin.ext (by simp only; omega)
        have h' : R ∈ (Δ.D k).link ⟨a.val + (b.val - a.val + 1 - 1), by omega⟩ := hRl
        rw [e] at h'
        exact h')
      (fun u h1 h2 hPu' => by
        obtain ⟨i, hi, hPi⟩ := hEsub P' u h1.le h2 hPu'
        have := congrArg Fin.val (hPu i hPi)
        have h1' := Fin.lt_def.mp h1
        simp only [haE] at h1' hi this
        omega)
      (fun u h1 h2 hRu' => by
        obtain ⟨i, hi, hRi⟩ := hEsub R u h1 h2.le hRu'
        have := congrArg Fin.val (hRu i hRi)
        have h2' := Fin.lt_def.mp h2
        simp only [haE, hbE] at h2' hi this
        omega)
      hlowE hhighE
    obtain ⟨h1, h2, h3⟩ := hfinal q β hβ hblk
    exact ⟨k, q, E.ofBlocks β hβ, hF, h1, h2, h3⟩
  · -- `R` at the low end: fold from `R` to `P'` and reverse
    obtain ⟨hn0, hR0, hPl, hRu, hPu⟩ := hfrom
    obtain ⟨q, β, hβ, hF, hblk⟩ := Chain.exists_blocks_isFrom hnC hcrE hab2E
      (by rw [hEa]; simpa [Chain.sub] using hR0)
      (by
        rw [hEb]
        have e : (⟨a.val + (b.val - a.val + 1 - 1), by omega⟩ : Fin (Δ.n k)) = b :=
          Fin.ext (by simp only; omega)
        have h' : P' ∈ (Δ.D k).link ⟨a.val + (b.val - a.val + 1 - 1), by omega⟩ := hPl
        rw [e] at h'
        exact h')
      (fun u h1 h2 hRu' => by
        obtain ⟨i, hi, hRi⟩ := hEsub R u h1.le h2 hRu'
        have := congrArg Fin.val (hRu i hRi)
        have h1' := Fin.lt_def.mp h1
        simp only [haE] at h1' hi this
        omega)
      (fun u h1 h2 hPu' => by
        obtain ⟨i, hi, hPi⟩ := hEsub P' u h1 h2.le hPu'
        have := congrArg Fin.val (hPu i hPi)
        have h2' := Fin.lt_def.mp h2
        simp only [haE, hbE] at h2' hi this
        omega)
      hlowE hhighE
    obtain ⟨h1, h2, h3⟩ := hfinal q β hβ hblk
    refine ⟨k, q, (E.ofBlocks β hβ).reverse, hF.reverse, fun w hw => ?_, fun u => ?_,
      fun u x hx y hy => ?_⟩
    · obtain ⟨u, hu⟩ := mem_iUnion.mp (h1 hw)
      refine mem_iUnion.mpr ⟨Fin.rev u, ?_⟩
      rw [Chain.reverse_link, Fin.rev_rev]; exact hu
    · obtain ⟨S, hS⟩ := h2 (Fin.rev u)
      exact ⟨S, by rw [Chain.reverse_link]; exact hS⟩
    · rw [Chain.reverse_link] at hx hy
      exact h3 _ x hx y hy

end Description

end HPC
