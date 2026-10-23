import HPC.Plane.Composant91
import HPC.Chains.Consolidation

/-!
# Batch 91: Bing's surgery for Theorem 10 (Duke 1951, p. 659), formally

Bing's proof of Theorem 10 ends with a surgery: a chain `F` covering a subcontinuum `M''` through
`p` (refining `D`, `p` in its first link and in the closure of no other) is extended to a chain
covering `M`, by cutting `M` at a small open set `N` near a point of `M''` in the last link of `F`
and in the end link `d_1` of `D`, separating `M ∖ N` into a clopen piece `H` (containing the
component of `p`, hence covered by `F`) and the rest `K` (covered by `D`).

`theorem10_1951_of_lastLink` proves the surgery in a form that needs less than Bing's text:

* `M''` need **not** be proper and need **not** meet every link of `D`;
* the point `y` need only lie in `M'' ∩ f_k ∩ d_1` and differ from `p` — it may lie in the closure
  of `f_{k-1}` and of `d_2`: the last link of `F` is merged with `N`, and `cl N` is removed from
  the links `d_2, d_3, …` of the `D`-part;
* only condition B (which follows from condition A) is used.

`theorem10_1951_of_lastLink'` is the mirror form (the last link of `D` instead of the first).
So Theorem 10 follows from Bing's unestablished sentence in the following form: **some**
subcontinuum `M''` through `p` has a chain `F` with the properties of Theorem 10 whose last link
meets `M'' ∩ (d_1 ∪ d_m)` at a point other than `p`.
-/

namespace HPC.Plane

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- **Separating a compact set along the component of a point.** If every preconnected subset of
the compact set `S` through `p` lies in the open set `O`, then `S` splits into two disjoint compact
pieces, the one containing `p` inside `O`. (In the compact space `S` the component of `p` is the
intersection of the clopen sets containing it; by compactness one of them lies in `O`.) -/
theorem exists_clopen_split {S : Set X} (hS : IsCompact S) {p : X} (hp : p ∈ S) {O : Set X}
    (hO : IsOpen O) (hC : ∀ A : Set X, IsPreconnected A → A ⊆ S → p ∈ A → A ⊆ O) :
    ∃ H K : Set X, IsCompact H ∧ IsCompact K ∧ H ∪ K = S ∧ Disjoint H K ∧ p ∈ H ∧ H ⊆ O := by
  classical
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  set p' : S := ⟨p, hp⟩
  have hcomp : Subtype.val '' connectedComponent p' ⊆ O :=
    hC _ (isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn)
      (by rintro _ ⟨z, -, rfl⟩; exact z.2) ⟨p', mem_connectedComponent, rfl⟩
  set Z : Set S := (Subtype.val ⁻¹' O)ᶜ with hZ_def
  have hZc : IsCompact Z := ((hO.preimage continuous_subtype_val).isClosed_compl).isCompact
  have hCZ : Z ∩ ⋂ s : { s : Set S // IsClopen s ∧ p' ∈ s }, (s : Set S) = ∅ := by
    rw [← connectedComponent_eq_iInter_isClopen]
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hzZ hzC
    exact hzZ (hcomp ⟨z, hzC, rfl⟩)
  obtain ⟨u, hu⟩ := hZc.elim_finite_subfamily_closed
    (fun s : { s : Set S // IsClopen s ∧ p' ∈ s } => (s : Set S)) (fun s => s.2.1.isClosed) hCZ
  set W : Set S := ⋂ i ∈ u, (i : Set S) with hW_def
  have hW : IsClopen W := isClopen_biInter_finset fun i _ => i.2.1
  have hpW : p' ∈ W := mem_iInter₂.mpr fun i _ => i.2.2
  refine ⟨Subtype.val '' W, Subtype.val '' Wᶜ, hW.isClosed.isCompact.image continuous_subtype_val,
    hW.compl.isClosed.isCompact.image continuous_subtype_val, ?_, ?_, ⟨p', hpW, rfl⟩, ?_⟩
  · rw [← image_union, union_compl_self, image_univ, Subtype.range_coe]
  · rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    rw [Subtype.val_injective hab] at hb
    exact hb ha
  · rintro _ ⟨z, hz, rfl⟩
    by_contra hzO
    have : z ∈ Z ∩ W := ⟨hzO, hz⟩
    rw [hu] at this
    exact this

/-- **Bing's surgery** (Duke 1951, p. 659), with the point in the **first** link of `D`. If `p`
satisfies condition B in the continuum `M`, `D` covers `M`, and some subcontinuum `K ∋ p` of `M`
has a chain `F` refining `D`, covering `K`, with `p` in its first link and in the closure of no
other, whose last link contains a point `y ≠ p` of `K` lying in the first link of `D`, then the
conclusion of Theorem 10 holds for `M`. -/
theorem theorem10_1951_of_lastLink {M : Set X} (hM : Fold.Q78.IsContinuum M) {m : ℕ}
    (D : Chain X m) (hD : M ⊆ D.union) {p : X} (hp : CondB M p) {K : Set X} (hKM : K ⊆ M)
    (hK : Fold.Q78.IsContinuum K) (hpK : p ∈ K) {k : ℕ} (F : Chain X k) (hk : 0 < k)
    (hKF : K ⊆ F.union) (hFD : F.Refines D) (hp0 : p ∈ F.link ⟨0, hk⟩)
    (hpF : ∀ j : Fin k, j.val ≠ 0 → p ∉ closure (F.link j)) (hm : 0 < m) {y : X} (hyK : y ∈ K)
    (hyF : y ∈ F.link ⟨k - 1, by omega⟩) (hyD : y ∈ D.link ⟨0, hm⟩) (hyp : y ≠ p) :
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
  have hpS : p ∈ S := ⟨hp.1, fun h => hpN (subset_closure h)⟩
  have hFo : IsOpen F.union := isOpen_iUnion F.isOpen
  obtain ⟨H, Kc, hHc, hKcc, hHK, hdisj, hpH, hHF⟩ := exists_clopen_split hSc hpS hFo
    (fun A hA hAS hpA => by
      have hclA : closure A ⊆ S := closure_minimal hAS (hM.1.isClosed.sdiff hNo)
      have hcont : Fold.Q78.IsContinuum (closure A) :=
        ⟨hM.1.of_isClosed_subset isClosed_closure (hclA.trans diff_subset),
          (show IsConnected A from ⟨⟨p, hpA⟩, hA⟩).closure⟩
      rcases hp.2 _ _ (hclA.trans diff_subset) hKM hcont hK (subset_closure hpA) hpK with h | h
      · exact subset_closure.trans (h.trans hKF)
      · exact absurd hyN (hclA (h hyK)).2)
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
    hM.2.isPreconnected hcov (show 0 < k + m by omega) ⟨p, hpL0, hp.1⟩
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

/-- **Bing's surgery**, mirror form: the point lies in the **last** link of `D`. -/
theorem theorem10_1951_of_lastLink' {M : Set X} (hM : Fold.Q78.IsContinuum M) {m : ℕ}
    (D : Chain X m) (hD : M ⊆ D.union) {p : X} (hp : CondB M p) {K : Set X} (hKM : K ⊆ M)
    (hK : Fold.Q78.IsContinuum K) (hpK : p ∈ K) {k : ℕ} (F : Chain X k) (hk : 0 < k)
    (hKF : K ⊆ F.union) (hFD : F.Refines D) (hp0 : p ∈ F.link ⟨0, hk⟩)
    (hpF : ∀ j : Fin k, j.val ≠ 0 → p ∉ closure (F.link j)) (hm : 0 < m) {y : X} (hyK : y ∈ K)
    (hyF : y ∈ F.link ⟨k - 1, by omega⟩) (hyD : y ∈ D.link ⟨m - 1, by omega⟩) (hyp : y ≠ p) :
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
  obtain ⟨n, E, hn, hME, hED, h0, hj⟩ := theorem10_1951_of_lastLink hM D.reverse hDr hp hKM hK hpK
    F hk hKF hFDr hp0 hpF hm hyK hyF hyDr hyp
  refine ⟨n, E, hn, hME, ?_, h0, hj⟩
  have := hED.reverse_right
  rwa [Chain.reverse_reverse] at this

end HPC.Plane
