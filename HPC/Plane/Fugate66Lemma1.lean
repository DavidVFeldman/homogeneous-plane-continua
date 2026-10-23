import HPC.Plane.Fugate66

/-!
# Batch 100: Fugate's Lemma 1 for terminal subcontinua (Bing's Theorem 10 for sets)

Bing's surgery (batch 91) with condition B replaced by the separation property it actually uses
(`surgery_of_sep`), the composant step for a terminal subcontinuum
(`exists_proper_superset_meeting_all_links`), the end-link case (`t10Chain_of_mem_first`), and the
induction of batch 99 run with a terminal subcontinuum `A` in place of the point `p`
(`lemma1_aux`). See `REPORT-batch100.md`, item 4.
-/

namespace HPC.Plane

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- **Bing's surgery, with the separation property in place of condition B.** As
`theorem10_1951_of_lastLink` (batch 91), whose proof is repeated verbatim, except that condition B
at `p` is replaced by what the proof uses: every subcontinuum of `M` through `p` missing `y` lies
in `K`. -/
theorem surgery_of_sep {M : Set X} (hM : Fold.Q78.IsContinuum M) {m : ℕ}
    (D : Chain X m) (hD : M ⊆ D.union) {p : X} (hpM : p ∈ M) {K : Set X}
    {k : ℕ} (F : Chain X k) (hk : 0 < k)
    (hKF : K ⊆ F.union) (hFD : F.Refines D) (hp0 : p ∈ F.link ⟨0, hk⟩)
    (hpF : ∀ j : Fin k, j.val ≠ 0 → p ∉ closure (F.link j)) (hm : 0 < m) {y : X}
    (hyF : y ∈ F.link ⟨k - 1, by omega⟩) (hyD : y ∈ D.link ⟨0, hm⟩) (hyp : y ≠ p)
    (hsep : ∀ C : Set X, C ⊆ M → Fold.Q78.IsContinuum C → p ∈ C → y ∉ C → C ⊆ K) :
    ∃ (n : ℕ) (E : Chain X n) (hn : 0 < n), M ⊆ E.union ∧ E.Refines D ∧
      p ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (E.link j) := by
  classical
  -- the cut `N`, a small ball about `y`
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp ((F.isOpen _).inter (D.isOpen _)) y ⟨hyF, hyD⟩
  set s := min (r / 2) (dist y p / 2) with hs_def
  have hs : 0 < s := lt_min (half_pos hr) (half_pos (dist_pos.mpr hyp))
  set N := ball y s with hN_def
  have hNo : IsOpen N := isOpen_ball
  have hclN : closure N ⊆ F.link ⟨k - 1, by omega⟩ ∩ D.link ⟨0, hm⟩ := by
    refine closure_ball_subset_closedBall.trans fun z hz => hrsub ?_
    rw [mem_closedBall] at hz
    rw [mem_ball]
    have : s ≤ r / 2 := min_le_left _ _
    linarith
  have hpN : p ∉ closure N := by
    intro h
    have h1 := closure_ball_subset_closedBall h
    rw [mem_closedBall, dist_comm] at h1
    have h2 : s ≤ dist y p / 2 := min_le_right _ _
    have h3 := dist_pos.mpr hyp
    linarith
  have hyN : y ∈ N := mem_ball_self hs
  -- the component of `p` in `M ∖ N` lies in `K`, hence in `F.union`; split `M ∖ N` along it
  set S := M \ N with hS_def
  have hSc : IsCompact S := hM.1.diff hNo
  have hpS : p ∈ S := ⟨hpM, fun h => hpN (subset_closure h)⟩
  have hFo : IsOpen F.union := isOpen_iUnion F.isOpen
  obtain ⟨H, Kc, hHc, hKcc, hHK, hdisj, hpH, hHF⟩ := exists_clopen_split hSc hpS hFo
    (fun A hA hAS hpA => by
      have hclA : closure A ⊆ S := closure_minimal hAS (hM.1.isClosed.sdiff hNo)
      have hcont : Fold.Q78.IsContinuum (closure A) :=
        ⟨hM.1.of_isClosed_subset isClosed_closure (hclA.trans diff_subset),
          (show IsConnected A from ⟨⟨p, hpA⟩, hA⟩).closure⟩
      exact subset_closure.trans ((hsep _ (hclA.trans diff_subset) hcont (subset_closure hpA)
        (fun hy => (hclA hy).2 hyN)).trans hKF))
  -- disjoint open neighbourhoods, the second with closure missing `p`
  obtain ⟨δ, hδ, hδd⟩ := hdisj.exists_thickenings hHc hKcc.isClosed
  set U := thickening δ H with hU_def
  set V := thickening (δ / 2) Kc with hV_def
  have hUo : IsOpen U := isOpen_thickening
  have hVo : IsOpen V := isOpen_thickening
  have hHU : H ⊆ U := self_subset_thickening hδ H
  have hKV : Kc ⊆ V := self_subset_thickening (half_pos hδ) Kc
  have hUV : Disjoint U V := hδd.mono_right (thickening_mono (half_le_self hδ.le) Kc)
  have hpV : p ∉ closure V := by
    intro h
    have h1 : closure V ⊆ cthickening (δ / 2) Kc := closure_thickening_subset_cthickening _ _
    have h2 : cthickening (δ / 2) Kc ⊆ thickening δ Kc :=
      cthickening_subset_thickening' hδ (half_lt_self hδ) Kc
    exact Set.disjoint_left.mp hδd (self_subset_thickening hδ H hpH) (h2 (h1 h))
  -- the weak chain: `F ∩ U` (last link merged with `N`), then `D ∩ V` (minus `cl N` after `d_1`)
  set L : ℕ → Set X := fun i =>
    if i < k - 1 then linkN F i ∩ U
    else if i = k - 1 then (linkN F i ∩ U) ∪ N
    else if i = k then linkN D 0 ∩ V
    else (linkN D (i - k) ∩ V) \ closure N with hL_def
  have hNF : N ⊆ linkN F (k - 1) := by
    rw [linkN_of_lt F (by omega)]
    exact fun z hz => (hclN (subset_closure hz)).1
  have hLF : ∀ i, i < k → L i ⊆ linkN F i := by
    intro i hi
    simp only [hL_def]
    split_ifs with h1 h2
    · exact inter_subset_left
    · rw [h2]; exact union_subset inter_subset_left hNF
    · omega
    · omega
  have hLD : ∀ i, k ≤ i → L i ⊆ linkN D (i - k) ∩ V := by
    intro i hi
    simp only [hL_def]
    split_ifs with h1 h2 h3
    · omega
    · omega
    · rw [h3, Nat.sub_self]
    · exact diff_subset
  have hLo : ∀ i, IsOpen (L i) := by
    intro i
    simp only [hL_def]
    split_ifs
    · exact (isOpen_linkN F i).inter hUo
    · exact ((isOpen_linkN F i).inter hUo).union hNo
    · exact (isOpen_linkN D 0).inter hVo
    · exact ((isOpen_linkN D _).inter hVo).sdiff isClosed_closure
  have hweak : ∀ i j, i + 2 ≤ j → j < k + m → Disjoint (L i) (L j) := by
    intro i j hij hj
    by_cases hjk : j < k
    · exact (disjoint_linkN F hij).mono (hLF i (by omega)) (hLF j hjk)
    push_neg at hjk
    by_cases hik : k ≤ i
    · exact (disjoint_linkN D (show i - k + 2 ≤ j - k by omega)).mono
        ((hLD i hik).trans inter_subset_left) ((hLD j hjk).trans inter_subset_left)
    push_neg at hik
    by_cases hik' : i < k - 1
    · have hLi : L i ⊆ U := by
        simp only [hL_def, if_pos hik']; exact inter_subset_right
      exact hUV.mono hLi ((hLD j hjk).trans inter_subset_right)
    · have hi : i = k - 1 := by omega
      have hLi : L i = (linkN F i ∩ U) ∪ N := by
        simp only [hL_def, if_neg hik', if_pos hi]
      have hLj : L j = (linkN D (j - k) ∩ V) \ closure N := by
        simp only [hL_def, if_neg (show ¬ j < k - 1 by omega), if_neg (show j ≠ k - 1 by omega),
          if_neg (show j ≠ k by omega)]
      rw [hLi, hLj, Set.disjoint_left]
      rintro x (hx | hx) hxj
      · exact Set.disjoint_left.mp hUV hx.2 hxj.1.2
      · exact hxj.2 (subset_closure hx)
  have hcov : M ⊆ ⋃ i, ⋃ (_ : i < k + m), L i := by
    intro x hx
    by_cases hxN : x ∈ N
    · refine mem_iUnion₂.mpr ⟨k - 1, by omega, ?_⟩
      simp only [hL_def, if_neg (show ¬ k - 1 < k - 1 by omega)]
      exact Or.inr hxN
    have hxS : x ∈ H ∪ Kc := by rw [hHK]; exact ⟨hx, hxN⟩
    rcases hxS with hxH | hxK
    · obtain ⟨i, hi, hxi⟩ := (mem_union_iff_linkN F).mp (hHF hxH)
      refine mem_iUnion₂.mpr ⟨i, by omega, ?_⟩
      simp only [hL_def]
      split_ifs with h1 h2
      · exact ⟨hxi, hHU hxH⟩
      · exact Or.inl ⟨hxi, hHU hxH⟩
      · omega
      · omega
    · obtain ⟨j, hj, hxj⟩ := (mem_union_iff_linkN D).mp (hD hx)
      by_cases hd1 : j = 0 ∨ x ∈ closure N
      · refine mem_iUnion₂.mpr ⟨k, by omega, ?_⟩
        simp only [hL_def, if_neg (show ¬ k < k - 1 by omega), if_neg (show k ≠ k - 1 by omega)]
        refine ⟨?_, hKV hxK⟩
        rcases hd1 with h | h
        · rw [← h]; exact hxj
        · rw [linkN_of_lt D hm]; exact (hclN h).2
      · push_neg at hd1
        refine mem_iUnion₂.mpr ⟨k + j, by omega, ?_⟩
        simp only [hL_def, if_neg (show ¬ k + j < k - 1 by omega),
          if_neg (show k + j ≠ k - 1 by omega), if_neg (show k + j ≠ k by omega),
          Nat.add_sub_cancel_left]
        exact ⟨⟨hxj, hKV hxK⟩, hd1.2⟩
  have hpL0 : p ∈ L 0 := by
    have hpF0 : p ∈ linkN F 0 := by rw [linkN_of_lt F hk]; exact hp0
    simp only [hL_def]
    split_ifs with h1 h2
    · exact ⟨hpF0, hHU hpH⟩
    · exact Or.inl ⟨hpF0, hHU hpH⟩
    · omega
    · omega
  obtain ⟨a, n, E, ha, hn, hnle, hEL, hME, -, -⟩ := exists_chain_of_weak L hLo hweak
    hM.2.isPreconnected hcov (show 0 < k + m by omega) ⟨p, hpL0, hpM⟩
  have ha0 : a = 0 := by omega
  subst ha0
  have hn0 : 0 < n := by omega
  refine ⟨n, E, hn0, hME, fun t => ?_, ?_, fun j hj => ?_⟩
  · rw [hEL t, zero_add]
    by_cases htk : t.val < k
    · obtain ⟨i, hi⟩ := hFD ⟨t.val, htk⟩
      refine ⟨i, (hLF t htk).trans ?_⟩
      rw [linkN_of_lt F htk]; exact hi
    · push_neg at htk
      have htm : t.val - k < m := by have := t.isLt; omega
      refine ⟨⟨t.val - k, htm⟩, (hLD t htk).trans ?_⟩
      rw [linkN_of_lt D htm]; exact inter_subset_left
  · rw [hEL, zero_add]; exact hpL0
  · rw [hEL, zero_add]
    intro hcl
    by_cases hjk : j.val < k
    · have hsub : L j ⊆ F.link ⟨j.val, hjk⟩ := by
        rw [← linkN_of_lt F hjk]; exact hLF j hjk
      exact hpF ⟨j.val, hjk⟩ hj (closure_mono hsub hcl)
    · push_neg at hjk
      exact hpV (closure_mono ((hLD j hjk).trans inter_subset_right) hcl)

/-- **The surgery, mirror form**: the point lies in the **last** link of `D`. -/
theorem surgery_of_sep' {M : Set X} (hM : Fold.Q78.IsContinuum M) {m : ℕ}
    (D : Chain X m) (hD : M ⊆ D.union) {p : X} (hpM : p ∈ M) {K : Set X}
    {k : ℕ} (F : Chain X k) (hk : 0 < k)
    (hKF : K ⊆ F.union) (hFD : F.Refines D) (hp0 : p ∈ F.link ⟨0, hk⟩)
    (hpF : ∀ j : Fin k, j.val ≠ 0 → p ∉ closure (F.link j)) (hm : 0 < m) {y : X}
    (hyF : y ∈ F.link ⟨k - 1, by omega⟩) (hyD : y ∈ D.link ⟨m - 1, by omega⟩) (hyp : y ≠ p)
    (hsep : ∀ C : Set X, C ⊆ M → Fold.Q78.IsContinuum C → p ∈ C → y ∉ C → C ⊆ K) :
    ∃ (n : ℕ) (E : Chain X n) (hn : 0 < n), M ⊆ E.union ∧ E.Refines D ∧
      p ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (E.link j) := by
  have hDr : M ⊆ D.reverse.union := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hD hx)
    refine mem_iUnion.mpr ⟨Fin.rev i, ?_⟩
    rw [Chain.reverse_link, Fin.rev_rev]; exact hi
  have hyDr : y ∈ D.reverse.link ⟨0, hm⟩ := by
    rw [Chain.reverse_link]
    have : Fin.rev (⟨0, hm⟩ : Fin m) = ⟨m - 1, by omega⟩ := Fin.ext (by simp [Fin.val_rev])
    rw [this]; exact hyD
  have hFDr : F.Refines D.reverse := hFD.reverse_right
  obtain ⟨n, E, hn, hME, hED, h0, hj⟩ := surgery_of_sep hM D.reverse hDr hpM
    F hk hKF hFDr hp0 hpF hm hyF hyDr hyp hsep
  refine ⟨n, E, hn, hME, ?_, h0, hj⟩
  have := hED.reverse_right
  rwa [Chain.reverse_reverse] at this

/-- **The end-link case.** If `p ∈ M` lies in the first link of a chain `D` covering the continuum
`M`, removing a small closed ball about `p` from the other links (and trimming) gives a
Theorem-10 chain for `M` from `p` refining `D`. -/
theorem t10Chain_of_mem_first {M : Set X} (hM : Fold.Q78.IsContinuum M) {m : ℕ} (D : Chain X m)
    (hD : M ⊆ D.union) {p : X} (hpM : p ∈ M) (hm : 0 < m) (hp0 : p ∈ D.link ⟨0, hm⟩) :
    ∃ (n : ℕ) (E : Chain X n), IsT10Chain D M p E := by
  classical
  obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.mp (D.isOpen ⟨0, hm⟩) p hp0
  set B := closedBall p (ρ / 2) with hB_def
  have hBD : B ⊆ D.link ⟨0, hm⟩ := fun z hz =>
    hρD (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (half_lt_self hρ)))
  set L : ℕ → Set X := fun i => if i = 0 then linkN D 0 else linkN D i \ B with hL_def
  have hLsub : ∀ i, L i ⊆ linkN D i := fun i => by
    simp only [hL_def]; split_ifs with h
    · rw [h]
    · exact diff_subset
  have hLo : ∀ i, IsOpen (L i) := fun i => by
    simp only [hL_def]; split_ifs
    · exact isOpen_linkN D 0
    · exact (isOpen_linkN D i).sdiff isClosed_closedBall
  have hweak : ∀ i j, i + 2 ≤ j → j < m → Disjoint (L i) (L j) := fun i j hij _ =>
    (disjoint_linkN D hij).mono (hLsub i) (hLsub j)
  have hcov : M ⊆ ⋃ i, ⋃ (_ : i < m), L i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := (mem_union_iff_linkN D).mp (hD hx)
    by_cases hxB : x ∈ B
    · refine mem_iUnion₂.mpr ⟨0, hm, ?_⟩
      simp only [hL_def, if_pos rfl, linkN_of_lt D hm]
      exact hBD hxB
    · refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
      simp only [hL_def]; split_ifs with h
      · rw [← h]; exact hxi
      · exact ⟨hxi, hxB⟩
  have hL0 : L 0 = D.link ⟨0, hm⟩ := by simp only [hL_def, if_pos rfl, linkN_of_lt D hm]
  obtain ⟨a, k, E', ha, hk, hakm, hE'L, hME', -, -⟩ := exists_chain_of_weak L hLo hweak
    hM.2.isPreconnected hcov hm (by rw [hL0]; exact ⟨p, hp0, hpM⟩)
  have ha0 : a = 0 := by omega
  subst ha0
  have hk0 : 0 < k := by omega
  refine ⟨k, E', hk0, hME', fun t => ⟨⟨t.val, by omega⟩, ?_⟩, ?_, fun j hj => ?_⟩
  · rw [hE'L t, zero_add, ← linkN_of_lt D]; exact hLsub _
  · rw [hE'L, zero_add, hL0]; exact hp0
  · intro hcl
    have hsub : E'.link j ⊆ {z | ρ / 2 < dist z p} := by
      intro z hz
      rw [hE'L j, zero_add] at hz
      simp only [hL_def, if_neg hj] at hz
      have := hz.2
      rw [hB_def, mem_closedBall, not_le] at this
      exact this
    have hopen : IsOpen {z | dist z p < ρ / 2} := isOpen_lt (continuous_id.dist continuous_const)
      continuous_const
    have hp' : p ∈ {z | dist z p < ρ / 2} := by
      simp only [mem_setOf_eq, dist_self]; exact half_pos hρ
    obtain ⟨z, hz, hzE⟩ := mem_closure_iff.mp hcl _ hopen hp'
    have h1 := hsub hzE
    simp only [mem_setOf_eq] at h1 hz
    linarith

/-- The end-link case, mirror form: `p` in the last link of `D`. -/
theorem t10Chain_of_mem_last {M : Set X} (hM : Fold.Q78.IsContinuum M) {m : ℕ} (D : Chain X m)
    (hD : M ⊆ D.union) {p : X} (hpM : p ∈ M) (hm : 0 < m) (hp0 : p ∈ D.link ⟨m - 1, by omega⟩) :
    ∃ (n : ℕ) (E : Chain X n), IsT10Chain D M p E := by
  have hDr : M ⊆ D.reverse.union := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hD hx)
    refine mem_iUnion.mpr ⟨Fin.rev i, ?_⟩
    rw [Chain.reverse_link, Fin.rev_rev]; exact hi
  have hpDr : p ∈ D.reverse.link ⟨0, hm⟩ := by
    rw [Chain.reverse_link]
    have : Fin.rev (⟨0, hm⟩ : Fin m) = ⟨m - 1, by omega⟩ := Fin.ext (by simp [Fin.val_rev])
    rw [this]; exact hp0
  obtain ⟨n, E, hn, hME, hED, h0, hj⟩ := t10Chain_of_mem_first hM D.reverse hDr hpM hm hpDr
  refine ⟨n, E, hn, hME, ?_, h0, hj⟩
  have := hED.reverse_right
  rwa [Chain.reverse_reverse] at this

/-- Terminality passes to intermediate subcontinua. -/
theorem IsTerminalSub.mono {M W A : Set X} (h : IsTerminalSub M A) (hW : A ⊆ W) (hWM : W ⊆ M) :
    IsTerminalSub W A :=
  ⟨h.1, hW, fun K L hK hL hKW hLW hKA hLA =>
    h.2.2 K L hK hL (hKW.trans hWM) (hLW.trans hWM) hKA hLA⟩

/-- **The composant step for a terminal subcontinuum** (replacing Fugate's use of Lemma 3 and of
the density of a composant): if `A` is a proper terminal subcontinuum of `M` and every link of `D`
meets `M`, some proper subcontinuum of `M` containing `A` meets every link. For each link, boundary
bumping gives a subcontinuum through a point of `A` meeting the link and missing a point outside
`A`; by terminality the sets `A ∪ K_i` are nested, and the largest is the required one. No
atriodicity, hereditary unicoherence or irreducibility is needed. -/
theorem exists_proper_superset_meeting_all_links {M A : Set X} (hM : Fold.Q78.IsContinuum M)
    (hT : IsTerminalSub M A) (hAne : A ≠ M) {m : ℕ} (D : Chain X m)
    (hmeet : ∀ i, (D.link i ∩ M).Nonempty) :
    ∃ K : Set X, A ⊆ K ∧ K ⊆ M ∧ K ≠ M ∧ Fold.Q78.IsContinuum K ∧
      ∀ i, (D.link i ∩ K).Nonempty := by
  classical
  obtain ⟨hA, hAM, hter⟩ := hT
  obtain ⟨a, haA⟩ := hA.2.nonempty
  have hK : ∀ i : Fin m, ∃ K : Set X, Fold.Q78.IsContinuum K ∧ K ⊆ M ∧ a ∈ K ∧
      (D.link i ∩ (A ∪ K)).Nonempty ∧ A ∪ K ≠ M := by
    intro i
    by_cases hiA : (D.link i ∩ A).Nonempty
    · refine ⟨A, hA, hAM, haA, hiA.mono (inter_subset_inter_right _ subset_union_left), ?_⟩
      rwa [union_self]
    · obtain ⟨x, hxD, hxM⟩ := hmeet i
      have hxA : x ∉ A := fun h => hiA ⟨x, hxD, h⟩
      have hax : 0 < dist a x := dist_pos.mpr fun e => hxA (e ▸ haA)
      obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.mp (D.isOpen i) x hxD
      set s := min (r / 2) (dist a x) with hs_def
      have hs : 0 < s := lt_min (half_pos hr) hax
      obtain ⟨K, hKc, hKM, haK, z, hzK, hz⟩ := exists_subcontinuum_meeting_closedBall hM (hAM haA)
        hxM hs (min_le_right _ _)
      refine ⟨K, hKc, hKM.trans diff_subset, haK, ⟨z, hrD ?_, Or.inr hzK⟩, fun e => ?_⟩
      · rw [mem_ball]
        have := mem_closedBall.mp hz
        have : s ≤ r / 2 := min_le_left _ _
        linarith
      · have : x ∈ A ∪ K := e ▸ hxM
        rcases this with h | h
        · exact hxA h
        · exact (hKM h).2 (mem_ball_self hs)
  choose K hKc hKM haK hKD hKne using hK
  by_cases hm : m = 0
  · subst hm
    exact ⟨A, subset_rfl, hAM, hAne, hA, fun i => i.elim0⟩
  -- the sets `A ∪ K i` are nested
  have htot : ∀ i j, A ∪ K i ⊆ A ∪ K j ∨ A ∪ K j ⊆ A ∪ K i := fun i j => by
    rcases hter (K i) (K j) (hKc i) (hKc j) (hKM i) (hKM j) ⟨a, haK i, haA⟩ ⟨a, haK j, haA⟩
      with h | h
    · exact Or.inl (union_subset subset_union_left h)
    · exact Or.inr (union_subset subset_union_left (h.trans (union_comm _ _).subset))
  have hmax : ∀ s : Finset (Fin m), s.Nonempty → ∃ i₀ ∈ s, ∀ j ∈ s, A ∪ K j ⊆ A ∪ K i₀ := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro h; exact absurd h Finset.not_nonempty_empty
    | insert j s hjs ih =>
      intro _
      by_cases hs : s.Nonempty
      · obtain ⟨i₀, hi₀, hmx⟩ := ih hs
        rcases htot j i₀ with h | h
        · exact ⟨i₀, Finset.mem_insert_of_mem hi₀, fun l hl => by
            rcases Finset.mem_insert.mp hl with rfl | hl
            · exact h
            · exact hmx l hl⟩
        · exact ⟨j, Finset.mem_insert_self _ _, fun l hl => by
            rcases Finset.mem_insert.mp hl with rfl | hl
            · exact subset_rfl
            · exact (hmx l hl).trans h⟩
      · rw [Finset.not_nonempty_iff_eq_empty] at hs
        subst hs
        exact ⟨j, Finset.mem_insert_self _ _, fun l hl => by
          rw [Finset.mem_insert] at hl
          rcases hl with rfl | hl
          · exact subset_rfl
          · exact absurd hl (Finset.notMem_empty _)⟩
  obtain ⟨i₀, -, hmx⟩ := hmax Finset.univ ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  refine ⟨A ∪ K i₀, subset_union_left, union_subset hAM (hKM i₀), hKne i₀,
    isContinuum_union hA (hKc i₀) ⟨a, haA, haK i₀⟩, fun i => ?_⟩
  exact (hKD i).mono (inter_subset_inter_right _ (hmx i (Finset.mem_univ _)))

/-- **Lemma 1, the induction** (batch 99's `theorem10_aux` with the terminal subcontinuum `A` in
place of the point `p`). Strong induction on the length of `D`; a minimal counterexample
`M' ⊇ A` (Zorn) meets every link of `D`, misses `A` in its end links (else
`t10Chain_of_mem_first`/`_last`), and contains a proper subcontinuum `K ⊇ A` meeting every link
(`exists_proper_superset_meeting_all_links`); `K` has a Theorem-10 chain from some `a ∈ A`, a least
one has its last link through a point `y ∈ K ∩ (D_0 ∪ D_{m-1})`, so `y ∉ A`, and the surgery
(`surgery_of_sep`, with the separation property from terminality) gives one for `M'`. -/
theorem lemma1_aux (A : Set X) : ∀ (m : ℕ) (D : Chain X m) (M : Set X),
    Fold.Q78.IsContinuum M → M ⊆ D.union → IsTerminalSub M A →
    ∃ p ∈ A, ∃ (n : ℕ) (E : Chain X n), IsT10Chain D M p E := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro D M hM hD hT
  have hA := hT.1
  obtain ⟨a₀, ha₀⟩ := hA.2.nonempty
  by_contra hfail
  set S : Set (Set X) := {W | W ⊆ M ∧ Fold.Q78.IsContinuum W ∧ A ⊆ W ∧
    ¬ ∃ p ∈ A, ∃ (n : ℕ) (E : Chain X n), IsT10Chain D W p E} with hS
  obtain ⟨M', -, hM'min⟩ := zorn_superset_nonempty S (fun c hcS hch hne => by
    refine ⟨⋂₀ c, ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩, fun W hW => sInter_subset_of_mem hW⟩
    · obtain ⟨W, hW⟩ := hne
      exact (sInter_subset_of_mem hW).trans (hcS hW).1
    · obtain ⟨W, hW⟩ := hne
      exact (hcS hW).2.1.1.of_isClosed_subset
        (isClosed_sInter fun W hW => (hcS hW).2.1.1.isClosed) (sInter_subset_of_mem hW)
    · exact ⟨⟨a₀, mem_sInter.mpr fun W hW => (hcS hW).2.2.1 ha₀⟩,
        isPreconnected_sInter_chain' hne hch (fun W hW => (hcS hW).2.1.1)
          (fun W hW => (hcS hW).2.1.2.isPreconnected)⟩
    · exact fun x hx => mem_sInter.mpr fun W hW => (hcS hW).2.2.1 hx
    · rintro ⟨p, hpA, n, E, hn, hcov, hrest⟩
      haveI : Nonempty c := hne.to_subtype
      obtain ⟨⟨W, hWc⟩, hW⟩ := exists_subset_nhds_of_isCompact'
        (V := fun i : c => (i : Set X)) (U := E.union)
        (fun i j => by
          rcases hch.total i.2 j.2 with h | h
          · exact ⟨i, le_rfl, h⟩
          · exact ⟨j, h, le_rfl⟩)
        (fun i => (hcS i.2).2.1.1) (fun i => (hcS i.2).2.1.1.isClosed)
        (fun x hx => (isOpen_iUnion E.isOpen).mem_nhds
          (hcov (by rw [sInter_eq_iInter]; simpa using hx)))
      exact (hcS hWc).2.2.2 ⟨p, hpA, n, E, hn, hW, hrest⟩) M ⟨subset_rfl, hM, hT.2.1, hfail⟩
  obtain ⟨hM'M, hM'c, hAM', hM'fail⟩ := hM'min.1
  have hT' : IsTerminalSub M' A := hT.mono hAM' hM'M
  have hM'D : M' ⊆ D.union := hM'M.trans hD
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp (hM'D (hAM' ha₀))
  have hm0 : 0 < m := i₀.pos
  have hloc : ∀ x ∈ M', ∃ i : Fin m, x ∈ D.link i := fun x hx => mem_iUnion.mp (hM'D hx)
  -- `A` misses the two end links of `D`
  have hA0 : ∀ x ∈ A, x ∉ D.link ⟨0, hm0⟩ := fun x hx hx0 => by
    obtain ⟨n, E, hE⟩ := t10Chain_of_mem_first hM'c D hM'D (hAM' hx) hm0 hx0
    exact hM'fail ⟨x, hx, n, E, hE⟩
  have hA1 : ∀ x ∈ A, x ∉ D.link ⟨m - 1, by omega⟩ := fun x hx hx1 => by
    obtain ⟨n, E, hE⟩ := t10Chain_of_mem_last hM'c D hM'D (hAM' hx) hm0 hx1
    exact hM'fail ⟨x, hx, n, E, hE⟩
  -- `m ≥ 2`
  have hm2 : 2 ≤ m := by
    by_contra hm2
    have : i₀ = ⟨0, hm0⟩ := Fin.ext (by have := i₀.isLt; omega)
    exact hA0 a₀ ha₀ (this ▸ hi₀)
  -- `M'` meets the two end links of `D`
  have hend0 : (M' ∩ D.link ⟨0, hm0⟩).Nonempty := by
    by_contra h0
    rw [not_nonempty_iff_eq_empty] at h0
    have hle : (⟨1, by omega⟩ : Fin m) ≤ ⟨m - 1, by omega⟩ := Fin.mk_le_mk.mpr (by omega)
    obtain ⟨p, hpA, n, E, hn, hcovE, hED, hrest⟩ := IH _ (by simp only []; omega)
      (D.sub ⟨1, by omega⟩ ⟨m - 1, by omega⟩ hle) M' hM'c
      (subset_sub_union D hle fun x hx => by
        obtain ⟨i, hi⟩ := hloc x hx
        refine ⟨i, ?_, by simp only []; omega, hi⟩
        by_contra h
        have : i = ⟨0, hm0⟩ := Fin.ext (by simp only [] at h ⊢; omega)
        exact (eq_empty_iff_forall_notMem.mp h0) x ⟨hx, this ▸ hi⟩) hT'
    exact hM'fail ⟨p, hpA, n, E, hn, hcovE, refines_of_refines_sub hED, hrest⟩
  have hend1 : (M' ∩ D.link ⟨m - 1, by omega⟩).Nonempty := by
    by_contra h0
    rw [not_nonempty_iff_eq_empty] at h0
    have hle : (⟨0, by omega⟩ : Fin m) ≤ ⟨m - 2, by omega⟩ := Fin.mk_le_mk.mpr (by omega)
    obtain ⟨p, hpA, n, E, hn, hcovE, hED, hrest⟩ := IH _ (by simp only []; omega)
      (D.sub ⟨0, by omega⟩ ⟨m - 2, by omega⟩ hle) M' hM'c
      (subset_sub_union D hle fun x hx => by
        obtain ⟨i, hi⟩ := hloc x hx
        refine ⟨i, by simp only []; omega, ?_, hi⟩
        by_contra h
        have : i = ⟨m - 1, by omega⟩ := Fin.ext (by have := i.isLt; simp only [] at h ⊢; omega)
        exact (eq_empty_iff_forall_notMem.mp h0) x ⟨hx, this ▸ hi⟩) hT'
    exact hM'fail ⟨p, hpA, n, E, hn, hcovE, refines_of_refines_sub hED, hrest⟩
  -- hence every link
  have hmeet : ∀ i, (D.link i ∩ M').Nonempty := by
    intro i
    rw [inter_comm]
    by_cases hi0 : i.val = 0
    · rwa [show i = ⟨0, hm0⟩ from Fin.ext hi0]
    by_cases hi1 : i.val = m - 1
    · rwa [show i = ⟨m - 1, by omega⟩ from Fin.ext hi1]
    exact D.inter_link_nonempty_between hM'c.2.isPreconnected hM'D
      (show (⟨0, hm0⟩ : Fin m) < i from Fin.mk_lt_mk.mpr (by omega))
      (show i < ⟨m - 1, by omega⟩ from Fin.lt_def.mpr (by simp only []; omega)) hend0 hend1
  -- `A ≠ M'`, since `M'` meets the first link and `A` does not
  have hAne : A ≠ M' := by
    rintro rfl
    obtain ⟨x, hxM, hx0⟩ := hend0
    exact hA0 x hxM hx0
  -- a proper subcontinuum `K ⊇ A` meeting every link
  obtain ⟨K, hAK, hKM, hKne, hKc, hKmeet⟩ :=
    exists_proper_superset_meeting_all_links hM'c hT' hAne D hmeet
  have hKnt : K.Nontrivial := by
    obtain ⟨z, hz0, hzK⟩ := hKmeet ⟨0, hm0⟩
    exact ⟨z, hzK, a₀, hAK ha₀, fun e => hA0 a₀ ha₀ (e ▸ hz0)⟩
  -- `K` has a Theorem-10 chain from a point of `A`, by minimality of `M'`
  have hKT : ∃ p ∈ A, ∃ (n : ℕ) (E : Chain X n), IsT10Chain D K p E := by
    by_contra hKT
    exact hKne (Subset.antisymm hKM (hM'min.2 ⟨hKM.trans hM'M, hKc, hAK, hKT⟩ hKM))
  obtain ⟨a, haA, hKTa⟩ := hKT
  obtain ⟨k, F, hF, hmin⟩ := exists_minimal_T10Chain D K a hKTa
  obtain ⟨y, hyK, hya, hyF, hyD⟩ := lastLink_of_minimal D hm2 hKnt hKmeet F hF hmin
  obtain ⟨hk, hKF, hFD, ha0, haF⟩ := hF
  have hyA : y ∉ A := fun h => hyD.elim (hA0 y h) (hA1 y h)
  -- the separation property, from terminality
  have hsep : ∀ C : Set X, C ⊆ M' → Fold.Q78.IsContinuum C → a ∈ C → y ∉ C → C ⊆ K := by
    intro C hCM hC haC hyC
    rcases hT'.2.2 C K hC hKc hCM hKM ⟨a, haC, haA⟩ ⟨a, hAK haA, haA⟩ with h | h
    · exact h.trans (union_subset hAK subset_rfl)
    · exact absurd (h hyK) (by rintro (h' | h'); exacts [hyC h', hyA h'])
  rcases hyD with hyD | hyD
  · obtain ⟨n, E, hn, h⟩ := surgery_of_sep hM'c D hM'D (hAM' haA) F hk hKF hFD ha0 haF hm0 hyF
      hyD hya hsep
    exact hM'fail ⟨a, haA, n, E, hn, h⟩
  · obtain ⟨n, E, hn, h⟩ := surgery_of_sep' hM'c D hM'D (hAM' haA) F hk hKF hFD ha0 haF hm0 hyF
      hyD hya hsep
    exact hM'fail ⟨a, haA, n, E, hn, h⟩

/-- **Fugate, Lemma 1** (Bing's Theorem 10 for terminal subcontinua). `A` terminal in the
continuum `M`, `E` a chain covering `M`: some chain `F` covering `M` and refining `E` has its last
link meeting `A` outside the closure of the other links.

Shape change from the skeleton: the hypotheses that `M` is atriodic and hereditarily unicoherent
are not used and have been removed (the composant step uses terminality directly, see
`exists_proper_superset_meeting_all_links`); the ambient space need not be compact. Tautness is
treated separately (`exists_taut_epsChain`). -/
theorem fugate_lemma1 {M A : Set X} (hM : Fold.Q78.IsContinuum M) (hA : IsTerminalSub M A)
    {m : ℕ} (E : Chain X m) (hE : M ⊆ E.union) :
    ∃ (n : ℕ) (F : Chain X n) (hn : 0 < n), M ⊆ F.union ∧ F.Refines E ∧
      (A ∩ (F.link ⟨n - 1, by omega⟩ \
        closure (⋃ j : Fin n, ⋃ (_ : j.val ≠ n - 1), F.link j))).Nonempty := by
  obtain ⟨p, hpA, n, G, hn, hMG, hGE, hp0, hpG⟩ := lemma1_aux A m E M hM hE hA
  have hrev0 : Fin.rev (⟨n - 1, by omega⟩ : Fin n) = ⟨0, hn⟩ :=
    Fin.ext (by simp only [Fin.val_rev]; omega)
  refine ⟨n, G.reverse, hn, fun x hx => ?_, hGE.reverse_left, p, hpA, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.mp (hMG hx)
    refine mem_iUnion.mpr ⟨Fin.rev i, ?_⟩
    rw [Chain.reverse_link, Fin.rev_rev]; exact hi
  · rw [Chain.reverse_link, hrev0]; exact hp0
  · -- `p` has a neighbourhood missing every link of `G` but the first
    have hnb : ∀ j : Fin n, j.val ≠ 0 → ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ Disjoint U (G.link j) :=
      fun j hj => by
        have := hpG j hj
        rw [_root_.mem_closure_iff] at this
        push_neg at this
        obtain ⟨U, hU, hpU, hUG⟩ := this
        exact ⟨U, hU, hpU, Set.disjoint_iff_inter_eq_empty.mpr hUG⟩
    classical
    choose! U hUo hpU hUG using hnb
    set V : Set X := ⋂ j ∈ (Finset.univ.filter fun j : Fin n => j.val ≠ 0), U j with hV_def
    have hVo : IsOpen V := isOpen_biInter_finset fun j hj => hUo j (Finset.mem_filter.mp hj).2
    have hpV : p ∈ V := mem_iInter₂.mpr fun j hj => hpU j (Finset.mem_filter.mp hj).2
    intro hcl
    obtain ⟨z, hzV, hz⟩ := _root_.mem_closure_iff.mp hcl V hVo hpV
    obtain ⟨j, hz⟩ := mem_iUnion.mp hz
    obtain ⟨hj, hz⟩ := mem_iUnion.mp hz
    rw [Chain.reverse_link] at hz
    have hj' : (Fin.rev j).val ≠ 0 := by rw [Fin.val_rev]; omega
    exact Set.disjoint_left.mp (hUG _ hj') (mem_iInter₂.mp hzV _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hj'⟩)) hz

/-- **Exact containment for any compact set** (the skeleton's `ContainedExactly`): if `A` is a
nonempty compact subset of the connected set `M` and `E` covers `M`, some chain refining `E` and
covering `M` contains `A` exactly in a final segment. Take the largest `s` with `A` inside the links
`E_s, E_{s+1}, …`, remove a closed neighbourhood of `A` from the earlier links (it is covered by the
later ones) and trim. -/
theorem exists_containedExactly {M A : Set X} (hM : IsPreconnected M) (hA : IsCompact A)
    (hAne : A.Nonempty) (hAM : A ⊆ M) {m : ℕ} (E : Chain X m) (hE : M ⊆ E.union) :
    ∃ (n : ℕ) (F : Chain X n) (s : ℕ), M ⊆ F.union ∧ F.Refines E ∧ ContainedExactly F A s := by
  classical
  set P : ℕ → Prop := fun s => A ⊆ ⋃ (i : Fin m) (_ : s ≤ i.val), E.link i with hP_def
  have hP0 : P 0 := fun x hx => by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hE (hAM hx))
    exact mem_iUnion₂.mpr ⟨i, Nat.zero_le _, hi⟩
  have hPbig : ∀ s, m ≤ s → ¬ P s := fun s hs hPs => by
    obtain ⟨x, hx⟩ := hAne
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.mp (hPs hx)
    exact absurd i.isLt (by omega)
  set s := Nat.findGreatest P m with hs_def
  have hPs : P s := Nat.findGreatest_spec (P := P) (Nat.zero_le m) hP0
  have hsm : s < m := by
    by_contra h
    exact hPbig s (by omega) hPs
  have hgreat : ∀ s', s < s' → ¬ P s' := fun s' hs' => by
    by_cases h : s' ≤ m
    · exact Nat.findGreatest_is_greatest hs' h
    · exact hPbig s' (by omega)
  -- a closed neighbourhood `C` of `A` inside the later links
  set U : Set X := ⋃ (i : Fin m) (_ : s ≤ i.val), E.link i with hU_def
  have hUo : IsOpen U := isOpen_iUnion fun i => isOpen_iUnion fun _ => E.isOpen i
  obtain ⟨δ, hδ, hδU⟩ := hA.exists_thickening_subset_open hUo hPs
  set C := cthickening (δ / 2) A with hC_def
  have hCU : C ⊆ U := (cthickening_subset_thickening' hδ (half_lt_self hδ) A).trans hδU
  set L : ℕ → Set X := fun i => if i < s then linkN E i \ C else linkN E i with hL_def
  have hLsub : ∀ i, L i ⊆ linkN E i := fun i => by
    simp only [hL_def]; split_ifs
    · exact diff_subset
    · exact subset_rfl
  have hLo : ∀ i, IsOpen (L i) := fun i => by
    simp only [hL_def]; split_ifs
    · exact (isOpen_linkN E i).sdiff isClosed_cthickening
    · exact isOpen_linkN E i
  have hweak : ∀ i j, i + 2 ≤ j → j < m → Disjoint (L i) (L j) := fun i j hij _ =>
    (disjoint_linkN E hij).mono (hLsub i) (hLsub j)
  have hLlate : ∀ i, s ≤ i → L i = linkN E i := fun i hi => by
    simp only [hL_def, if_neg (show ¬ i < s by omega)]
  have hlate : ∀ x ∈ U, ∃ i, s ≤ i ∧ i < m ∧ x ∈ L i := fun x hx => by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact ⟨i, hi, i.isLt, by rw [hLlate i hi, linkN_of_lt E i.isLt]; exact hxi⟩
  have hcov : M ⊆ ⋃ i, ⋃ (_ : i < m), L i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := (mem_union_iff_linkN E).mp (hE hx)
    by_cases his : i < s
    · by_cases hxC : x ∈ C
      · obtain ⟨j, -, hj, hxj⟩ := hlate x (hCU hxC)
        exact mem_iUnion₂.mpr ⟨j, hj, hxj⟩
      · refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
        simp only [hL_def, if_pos his]
        exact ⟨hxi, hxC⟩
    · exact mem_iUnion₂.mpr ⟨i, hi, by rw [hLlate i (by omega)]; exact hxi⟩
  -- a point of `A` in `E_s` and in no later link
  obtain ⟨x₀, hx₀A, hx₀⟩ := not_subset.mp (hgreat (s + 1) (by omega))
  have hx₀s : x₀ ∈ L s := by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hPs hx₀A)
    have : i.val = s := by
      by_contra hne
      exact hx₀ (mem_iUnion₂.mpr ⟨i, by omega, hxi⟩)
    rw [hLlate s le_rfl, ← this, linkN_of_lt E i.isLt]; exact hxi
  obtain ⟨a, k, F, has, hsk, hakm, hFL, hMF, -, hrange⟩ := exists_chain_of_weak L hLo hweak hM hcov
    hsm ⟨x₀, hx₀s, hAM hx₀A⟩
  refine ⟨k, F, s - a, hMF, fun t => ⟨⟨a + t.val, by omega⟩, ?_⟩, by omega, ?_, ?_, ?_⟩
  · rw [hFL t, ← linkN_of_lt E]; exact hLsub _
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hPs hx)
    have hxL : x ∈ L i := by rw [hLlate i hi, linkN_of_lt E i.isLt]; exact hxi
    obtain ⟨h1, h2⟩ := hrange i i.isLt ⟨x, hxL, hAM hx⟩
    refine mem_iUnion₂.mpr ⟨⟨i.val - a, by omega⟩, by simp only []; omega, ?_⟩
    rw [hFL]
    convert hxL using 2
    simp only []; omega
  · intro s' hs' hsub
    refine hgreat (a + s') (by omega) fun x hx => ?_
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp (hsub hx)
    rw [hFL t] at hxt
    have := hLsub _ hxt
    rw [linkN_of_lt E (show a + t.val < m by omega)] at this
    exact mem_iUnion₂.mpr ⟨⟨a + t.val, by omega⟩, by simp only []; omega, this⟩
  · rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hxA, hxcl⟩
    have hsub : (⋃ (t : Fin k) (_ : t.val < s - a), F.link t) ⊆ (thickening (δ / 2) A)ᶜ := by
      intro z hz
      obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hz
      rw [hFL t] at hzt
      simp only [hL_def, if_pos (show a + t.val < s by omega)] at hzt
      exact fun h => hzt.2 (thickening_subset_cthickening _ _ h)
    exact closure_minimal hsub isOpen_thickening.isClosed_compl hxcl
      (self_subset_thickening (half_pos hδ) A hxA)

/-- **Fugate, Lemma 2**, in the skeleton's form: `A` terminal in the continuum `M`, `E` covering
`M`; some chain refining `E` and covering `M` contains `A` exactly in a final segment.

Shape change: the skeleton's hypotheses that `M` is atriodic and hereditarily unicoherent are not
used and have been removed. Of terminality only "`A` is a nonempty compact subset of `M`" is used
(`exists_containedExactly`): the skeleton's `ContainedExactly` does not force the segment to be the
part of the chain where `A` lives at an *end* (REPORT-batch100.md, item 4). -/
theorem fugate_lemma2 {M A : Set X} (hM : Fold.Q78.IsContinuum M) (hA : IsTerminalSub M A)
    {m : ℕ} (E : Chain X m) (hE : M ⊆ E.union) :
    ∃ (n : ℕ) (F : Chain X n) (s : ℕ), M ⊆ F.union ∧ F.Refines E ∧ ContainedExactly F A s :=
  exists_containedExactly hM.2.isPreconnected hA.1.1 hA.1.2.nonempty hA.2.1 E hE

end HPC.Plane
