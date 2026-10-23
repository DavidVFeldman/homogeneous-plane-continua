import HPC.Plane.Snake51
import HPC.PseudoArc.Theorem14
import HPC.Plane.EndPointsT15

/-!
# Bing 1951, §4 Theorem 10 and §5 (end points of snake-like continua)

Batch 85. The skeleton's seven statements; `theorem10_1951` and `endPoint_of_condA` now live in
`LastLink99.lean`, where they are proved (batches 99–100). Shape changes from the skeleton: the
hypothesis `hM : IsContinuum M` was unused and has been removed from `condB_of_condA`,
`condB_of_endPoint` and `exists_not_endPoint_of_not_HI`; `theorem14_1951` keeps `IsSnakeLike M`
but uses only its continuum part. See `REPORT-batch85.md`.

`IsSnakeLike`, `IsEpsChain` are from `Snake51.lean`; `IsIrreducibleBetween` from
`PseudoArc/Theorem14.lean`; `Fold.Q78.IsContinuum`, `IsIndecomposable` from `Fold/Questions78.lean`.
Bing's "chain from `p` to `q`" is `Chain.IsFrom p q`. Conditions A, B, C are stated for a point
`p` of a set `M`.
-/

namespace HPC.Plane

open Set Filter Topology

variable {X : Type*} [MetricSpace X]

/-- **Condition A** (Bing 1951, p. 659): each nondegenerate subcontinuum of `M` containing `p` is
irreducible from `p` to some other point. -/
def CondA (M : Set X) (p : X) : Prop :=
  p ∈ M ∧ ∀ W : Set X, W ⊆ M → Fold.Q78.IsContinuum W → W.Nontrivial → p ∈ W →
    ∃ q, q ≠ p ∧ IsIrreducibleBetween W p q

/-- **Condition B**: of two subcontinua of `M` containing `p`, one contains the other. -/
def CondB (M : Set X) (p : X) : Prop :=
  p ∈ M ∧ ∀ H K : Set X, H ⊆ M → K ⊆ M → Fold.Q78.IsContinuum H → Fold.Q78.IsContinuum K →
    p ∈ H → p ∈ K → H ⊆ K ∨ K ⊆ H

/-- **Condition C — end point**: for every `ε > 0` there is an `ε`-chain covering `M` in which
only the first link contains `p`. -/
def IsEndPoint (M : Set X) (p : X) : Prop :=
  p ∈ M ∧ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (E : Chain X n) (hn : 0 < n), IsEpsChain E ε ∧ M ⊆ E.union ∧
    p ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ E.link j

/-- **Opposite end points**: for every `ε > 0` there is an `ε`-chain from `p` to `q` covering `M`. -/
def OppositeEndPoints (M : Set X) (p q : X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (E : Chain X n), IsEpsChain E ε ∧ M ⊆ E.union ∧ E.IsFrom p q

/-- Hereditarily indecomposable: every subcontinuum is indecomposable. -/
def IsHereditarilyIndecomposable (M : Set X) : Prop :=
  ∀ K : Set X, K ⊆ M → Fold.Q78.IsContinuum K → Fold.Q78.IsIndecomposable K

/-- **Theorem 12, direction A ⇒ B** (the other direction rests on an external result). The
skeleton's hypothesis that `M` is a continuum is not needed and has been removed. -/
theorem condB_of_condA {M : Set X} {p : X} (hp : CondA M p) :
    CondB M p := by
  refine ⟨hp.1, fun H K hHM hKM hH hK hpH hpK => ?_⟩
  by_contra hne
  rw [not_or, not_subset, not_subset] at hne
  obtain ⟨⟨h, hhH, hhK⟩, ⟨k, hkK, hkH⟩⟩ := hne
  have hU : Fold.Q78.IsContinuum (H ∪ K) :=
    ⟨hH.1.union hK.1, IsConnected.union ⟨p, hpH, hpK⟩ hH.2 hK.2⟩
  have hnt : (H ∪ K).Nontrivial :=
    ⟨h, Or.inl hhH, k, Or.inr hkK, fun e => hhK (e ▸ hkK)⟩
  obtain ⟨q, -, hirr⟩ := hp.2 (H ∪ K) (union_subset hHM hKM) hU hnt (Or.inl hpH)
  rcases hirr.2.2.1 with hq | hq
  · have := hirr.2.2.2 H hH subset_union_left hpH hq
    exact hkH (this ▸ Or.inr hkK)
  · have := hirr.2.2.2 K hK subset_union_right hpK hq
    exact hhK (this ▸ Or.inl hhH)

/-- The chain argument behind Theorem 13's necessity (COMMISSION-batch85.md §3.4): if `p` lies in
the first link of an `ε`-chain covering `M`, and `H`, `K` are subcontinua of `M` through `p`, then
either every point of `K` is within `ε` of `H` or every point of `H` is within `ε` of `K`
(stated here for the two given points `k ∈ K`, `h ∈ H`). -/
theorem endPoint_aux {M : Set X} {n : ℕ} (E : Chain X n) (hn : 0 < n)
    {ε : ℝ} (hE : IsEpsChain E ε) (hME : M ⊆ E.union) {p : X} (hp0 : p ∈ E.link ⟨0, hn⟩)
    {H K : Set X} (hH : Fold.Q78.IsContinuum H) (hK : Fold.Q78.IsContinuum K) (hHM : H ⊆ M)
    (hKM : K ⊆ M) (hpH : p ∈ H) (hpK : p ∈ K) {h k : X} (hhH : h ∈ H) (hkK : k ∈ K)
    (hεK : ε ≤ Metric.infDist h K) (hεH : ε ≤ Metric.infDist k H) : False := by
  classical
  -- every link up to one meeting `A` (preconnected, through `p`) meets `A`
  have key : ∀ {A : Set X}, Fold.Q78.IsContinuum A → A ⊆ M → p ∈ A → ∀ i : Fin n,
      (E.link i ∩ A).Nonempty → ∀ j : Fin n, j ≤ i → (A ∩ E.link j).Nonempty := by
    intro A hA hAM hpA i hi j hji
    rcases Nat.eq_zero_or_pos j.val with h0 | h0
    · exact ⟨p, hpA, by rwa [show j = ⟨0, hn⟩ from Fin.ext h0]⟩
    rcases lt_or_eq_of_le hji with hlt | heq
    · exact E.inter_link_nonempty_between hA.2.isPreconnected (hAM.trans hME)
        (show (⟨0, hn⟩ : Fin n) < j from Fin.lt_def.mpr h0) hlt ⟨p, hpA, hp0⟩
        (by obtain ⟨z, hz1, hz2⟩ := hi; exact ⟨z, hz2, hz1⟩)
    · subst heq; obtain ⟨z, hz1, hz2⟩ := hi; exact ⟨z, hz2, hz1⟩
  have close : ∀ {A : Set X} {x : X} (j : Fin n), x ∈ E.link j → (A ∩ E.link j).Nonempty →
      Metric.infDist x A < ε := by
    intro A x j hx ⟨y, hyA, hy⟩
    exact (Metric.infDist_le_dist_of_mem hyA).trans_lt
      ((Metric.dist_le_diam_of_mem (hE j).1 hx hy).trans_lt (hE j).2)
  obtain ⟨i, hi, hmax⟩ := (Finset.univ.filter
    (fun i => (E.link i ∩ (H ∪ K)).Nonempty)).exists_max_image id
    ⟨⟨0, hn⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨p, hp0, Or.inl hpH⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, id] at hi hmax
  have locate : ∀ x ∈ M, ∃ j : Fin n, x ∈ E.link j := fun x hx => by
    simpa [Chain.union] using hME hx
  obtain ⟨z, hzi, hzHK⟩ := hi
  rcases hzHK with hzH | hzK
  · obtain ⟨j, hj⟩ := locate k (hKM hkK)
    have hji : j ≤ i := hmax j ⟨k, hj, Or.inr hkK⟩
    have := close j hj (key hH hHM hpH i ⟨z, hzi, hzH⟩ j hji)
    linarith
  · obtain ⟨j, hj⟩ := locate h (hHM hhH)
    have hji : j ≤ i := hmax j ⟨h, hj, Or.inl hhH⟩
    have := close j hj (key hK hKM hpK i ⟨z, hzi, hzK⟩ j hji)
    linarith

/-- **Theorem 13, necessity**: an end point satisfies condition B. (COMMISSION-batch85.md §3.4.)
The skeleton's hypothesis that `M` is a continuum is not needed and has been removed. -/
theorem condB_of_endPoint {M : Set X} {p : X} (hp : IsEndPoint M p) :
    CondB M p := by
  refine ⟨hp.1, fun H K hHM hKM hH hK hpH hpK => ?_⟩
  by_contra hne
  rw [not_or, not_subset, not_subset] at hne
  obtain ⟨⟨h, hhH, hhK⟩, ⟨k, hkK, hkH⟩⟩ := hne
  have dK := (hK.1.isClosed.notMem_iff_infDist_pos ⟨p, hpK⟩).mp hhK
  have dH := (hH.1.isClosed.notMem_iff_infDist_pos ⟨p, hpH⟩).mp hkH
  obtain ⟨n, E, hn, hE, hME, hp0, -⟩ := hp.2 (min (Metric.infDist h K) (Metric.infDist k H))
    (lt_min dK dH)
  exact endPoint_aux E hn hE hME hp0 hH hK hHM hKM hpH hpK hhH hkK
    (min_le_left _ _) (min_le_right _ _)

/-- **Bing 1951, Theorem 14.** A snake-like continuum irreducible between two of its end points
has them as opposite end points. -/
theorem theorem14_1951 {M : Set X} (hM : IsSnakeLike M) {p q : X} (hp : IsEndPoint M p)
    (hq : IsEndPoint M q) (hirr : IsIrreducibleBetween M p q) : OppositeEndPoints M p q := by
  classical
  have hMc : Fold.Q78.IsContinuum M := hM.1
  intro ε hε
  by_cases hpq : p = q
  · -- degenerate case: `M = {p}`, one small link
    subst hpq
    have hMp : M = {p} := (hirr.2.2.2 {p} ⟨isCompact_singleton, isConnected_singleton⟩
      (singleton_subset_iff.mpr hirr.2.1) rfl rfl).symm
    have hmem : p ∈ Metric.ball p (ε / 3) := Metric.mem_ball_self (by linarith)
    refine ⟨1, ⟨fun _ => Metric.ball p (ε / 3), fun _ => Metric.isOpen_ball, ?_⟩, ?_, ?_, ?_⟩
    · intro i j
      rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
      simp only [inter_self, sub_self, Int.natAbs_zero, zero_le_one, iff_true]
      exact ⟨p, hmem⟩
    · intro i
      refine ⟨Metric.isBounded_ball, ?_⟩
      have := Metric.diam_ball (x := p) (by linarith : (0 : ℝ) ≤ ε / 3)
      simp only
      linarith
    · rw [hMp]; intro z hz; rw [mem_singleton_iff] at hz; subst hz
      exact mem_iUnion.mpr ⟨0, hmem⟩
    · exact ⟨one_pos, hmem, hmem, fun i _ => Subsingleton.elim _ _,
        fun i _ => Subsingleton.elim _ _⟩
  have hdpq : 0 < dist p q := dist_pos.mpr hpq
  have hpM : p ∈ M := hirr.2.1
  have hqM : q ∈ M := hirr.2.2.1
  -- the chain `D'` at `q`: an `ε'`-chain with `q` in its last link only, every link meeting `M`
  set ε' := min ε (dist p q / 2) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by linarith)
  obtain ⟨n, D, hn, hDε, hMD, hq0, hqj⟩ := hq.2 ε' hε'pos
  obtain ⟨k, D', hk, hD'D, hMD', hD'meet, hqlast, hqonly⟩ :=
    exists_chain_last_only D hMc.2.isPreconnected hMD hqM hn hq0 hqj
  have hD'ε : ∀ t, Bornology.IsBounded (D'.link t) ∧ Metric.diam (D'.link t) < ε' := fun t => by
    obtain ⟨s, hs⟩ := hD'D t; rw [hs]; exact hDε s
  have hk2 : 2 ≤ k := by
    by_contra hk2
    obtain ⟨t, ht⟩ := mem_iUnion.mp (hMD' hpM)
    have e : t = ⟨k - 1, by omega⟩ := Fin.ext (by have := t.isLt; simp only; omega)
    rw [e] at ht
    have h1 := Metric.dist_le_diam_of_mem (hD'ε _).1 ht hqlast
    have h2 := (hD'ε ⟨k - 1, by omega⟩).2
    have h3 := min_le_right ε (dist p q / 2)
    linarith
  have hq0' : q ∉ D'.link ⟨0, hk⟩ := fun h => by have := hqonly _ h; simp only at this; omega
  -- a point `x` of `M` in the first link of `D'`, other than `p` and `q`
  obtain ⟨x, hxO, hxM, hxp⟩ : ∃ x ∈ D'.link ⟨0, hk⟩, x ∈ M ∧ x ≠ p := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨z, hzO, hzM⟩ := hD'meet ⟨0, hk⟩
    have hp0 : p ∈ D'.link ⟨0, hk⟩ := hcon z hzO hzM ▸ hzO
    obtain ⟨w, hwM, hwO, hwp⟩ := hMc.2.isPreconnected (D'.link ⟨0, hk⟩) {p}ᶜ (D'.isOpen _)
      isOpen_compl_singleton
      (fun y _ => by
        by_cases h : y = p
        · exact Or.inl (h ▸ hp0)
        · exact Or.inr h)
      ⟨z, hzM, hzO⟩ ⟨q, hqM, fun h => hpq h.symm⟩
    exact hwp (hcon w hwO hwM)
  -- Bing's `δ`, and a fine chain `F` at `p`
  obtain ⟨δ, hδ, hδprop⟩ := exists_delta_link_between hMc hirr (D'.isOpen ⟨0, hk⟩) hxM hxO hxp
    (fun h => hq0' (h ▸ hxO))
  obtain ⟨nF, F, hnF, hFε, hMF, hpF0, hpFj⟩ := hp.2 (min δ ε) (lt_min hδ hε)
  obtain ⟨j, hj0, hjO, hjq⟩ := hδprop nF F hnF
    (fun i => ⟨(hFε i).1, (hFε i).2.trans_le (min_le_left _ _)⟩) hMF hpF0
  -- the new chain: `f_0, …, f_{j-1}`, then `f_j ∪ (N' ∩ d'_0)`, `N' ∩ d'_1`, …, `N' ∩ d'_{k-1}`
  set N' : Set X := ⋃ (l : Fin nF) (_ : j < l), F.link l with hN'
  have hN'o : IsOpen N' := isOpen_iUnion fun l => isOpen_iUnion fun _ => F.isOpen l
  set G : ℕ → Set X := fun i => if i < j.val then linkN F i else
    if i = j.val then F.link j ∪ (N' ∩ D'.link ⟨0, hk⟩) else N' ∩ linkN D' (i - j.val) with hG
  have hG_lt : ∀ i, i < j.val → G i = linkN F i := fun i h => by simp only [hG, if_pos h]
  have hG_eq : G j.val = F.link j ∪ (N' ∩ D'.link ⟨0, hk⟩) := by
    simp only [hG, lt_irrefl, if_false, if_true]
  have hG_gt : ∀ i, j.val < i → G i = N' ∩ linkN D' (i - j.val) := fun i h => by
    simp only [hG, if_neg (by omega : ¬ i < j.val), if_neg (by omega : ¬ i = j.val)]
  have hGo : ∀ i, IsOpen (G i) := by
    intro i
    rcases lt_trichotomy i j.val with h | h | h
    · rw [hG_lt i h]; exact isOpen_linkN F i
    · rw [h, hG_eq]; exact (F.isOpen j).union (hN'o.inter (D'.isOpen _))
    · rw [hG_gt i h]; exact hN'o.inter (isOpen_linkN D' _)
  have hGD : ∀ i, j.val ≤ i → G i ⊆ linkN D' (i - j.val) := by
    intro i hi
    rcases eq_or_lt_of_le hi with h | h
    · rw [← h, hG_eq, Nat.sub_self, linkN_of_lt D' hk]
      exact union_subset hjO inter_subset_right
    · rw [hG_gt i h]; exact inter_subset_right
  have hGFN : ∀ i, j.val ≤ i → G i ⊆ linkN F j.val ∪ N' := by
    intro i hi
    rw [linkN_fin]
    rcases eq_or_lt_of_le hi with h | h
    · rw [← h, hG_eq]; exact union_subset_union_right _ inter_subset_left
    · rw [hG_gt i h]; exact inter_subset_left.trans subset_union_right
  have hFN : ∀ a, a < j.val → Disjoint (linkN F a) N' := by
    intro a ha
    rw [Set.disjoint_left]
    intro y hya hyN
    obtain ⟨ha', hya⟩ := (mem_linkN F).mp hya
    obtain ⟨l, hl⟩ := mem_iUnion.mp hyN
    obtain ⟨hjl, hyl⟩ := mem_iUnion.mp hl
    have := (F.adjacent_iff ⟨a, ha'⟩ l).mp ⟨y, hya, hyl⟩
    have : j.val < l.val := hjl
    simp only at *
    omega
  have hweak : ∀ i i', i + 2 ≤ i' → i' < j.val + k → Disjoint (G i) (G i') := by
    intro i i' hii' _
    by_cases hi : i < j.val
    · rw [hG_lt i hi]
      by_cases hi' : i' < j.val
      · rw [hG_lt i' hi']; exact disjoint_linkN F hii'
      · rcases eq_or_lt_of_le (not_lt.mp hi') with h | h
        · refine Disjoint.mono_right (hGFN i' (by omega)) (disjoint_union_right.mpr
            ⟨disjoint_linkN F (by omega), hFN i hi⟩)
        · rw [hG_gt i' h]; exact (hFN i hi).mono_right inter_subset_left
    · exact Disjoint.mono (hGD i (by omega)) (hGD i' (by omega)) (disjoint_linkN D' (by omega))
  have hcov : M ⊆ ⋃ i, ⋃ (_ : i < j.val + k), G i := by
    intro y hy
    obtain ⟨l, hl⟩ := mem_iUnion.mp (hMF hy)
    rcases lt_trichotomy l.val j.val with h | h | h
    · exact mem_iUnion₂.mpr ⟨l.val, by omega, by rw [hG_lt _ h, linkN_fin]; exact hl⟩
    · refine mem_iUnion₂.mpr ⟨j.val, by omega, ?_⟩
      rw [hG_eq]; left
      have e : l = j := Fin.ext h
      exact e ▸ hl
    · have hyN : y ∈ N' := mem_iUnion₂.mpr ⟨l, h, hl⟩
      obtain ⟨t, ht⟩ := mem_iUnion.mp (hMD' hy)
      by_cases ht0 : t.val = 0
      · refine mem_iUnion₂.mpr ⟨j.val, by omega, ?_⟩
        rw [hG_eq]; right
        have e : t = ⟨0, hk⟩ := Fin.ext ht0
        exact ⟨hyN, e ▸ ht⟩
      · refine mem_iUnion₂.mpr ⟨j.val + t.val, by omega, ?_⟩
        rw [hG_gt _ (by omega), Nat.add_sub_cancel_left, linkN_fin]
        exact ⟨hyN, ht⟩
  have hpG : p ∈ G 0 := by rw [hG_lt 0 hj0, linkN_of_lt F hnF]; exact hpF0
  obtain ⟨a, k₀, E, ha0, hak0, hakle, hElink, hME, -, hrange⟩ :=
    exists_chain_of_weak (n := j.val + k) G hGo hweak hMc.2.isPreconnected hcov
      (i₀ := 0) (by omega) ⟨p, hpG, hpM⟩
  obtain rfl : a = 0 := by omega
  have hqG : q ∈ G (j.val + k - 1) := by
    rw [hG_gt _ (by omega), show j.val + k - 1 - j.val = k - 1 by omega, linkN_of_lt D' (by omega)]
    refine ⟨?_, hqlast⟩
    obtain ⟨l, hl⟩ := mem_iUnion.mp (hMF hqM)
    exact mem_iUnion₂.mpr ⟨l, hjq l hl, hl⟩
  have hk₀ : k₀ = j.val + k := by
    have := (hrange (j.val + k - 1) (by omega) ⟨q, hqG, hqM⟩).2
    omega
  subst hk₀
  have hE : ∀ t : Fin (j.val + k), E.link t = G t := fun t => by rw [hElink t, zero_add]
  refine ⟨j.val + k, E, fun t => ?_, hME, ⟨by omega, ?_, ?_, fun t ht => ?_, fun t ht => ?_⟩⟩
  · rw [hE t]
    by_cases ht : t.val < j.val
    · rw [hG_lt _ ht, linkN_of_lt F (by omega)]
      exact ⟨(hFε _).1, (hFε _).2.trans_le (min_le_right _ _)⟩
    · have hsub := hGD t (by omega)
      rw [linkN_of_lt D' (show t.val - j.val < k by omega)] at hsub
      exact ⟨(hD'ε _).1.subset hsub, ((Metric.diam_mono hsub (hD'ε _).1).trans_lt
        (hD'ε _).2).trans_le (min_le_left _ _)⟩
  · rw [hE]; exact hpG
  · rw [hE]; exact hqG
  · rw [hE t] at ht
    apply Fin.ext
    by_contra hne
    by_cases htj : t.val < j.val
    · rw [hG_lt _ htj, linkN_of_lt F (by omega)] at ht
      exact hpFj _ hne ht
    · rcases hGFN t (by omega) ht with h | h
      · rw [linkN_fin] at h; exact hpFj j (by omega) h
      · obtain ⟨l, hl⟩ := mem_iUnion.mp h
        obtain ⟨hjl, hpl⟩ := mem_iUnion.mp hl
        have : j.val < l.val := hjl
        exact hpFj l (by omega) hpl
  · rw [hE t] at ht
    apply Fin.ext
    simp only
    by_cases htj : t.val < j.val
    · rw [hG_lt _ htj, linkN_of_lt F (by omega)] at ht
      have := hjq _ ht
      have : j.val < t.val := this
      omega
    · have hsub := hGD t (by omega)
      rw [linkN_of_lt D' (show t.val - j.val < k by omega)] at hsub
      have := hqonly _ (hsub ht)
      simp only at this
      omega

/-- **Bing 1951, Theorem 15**, with the nondegeneracy implicit in Bing's construction made
explicit: a nondegenerate snake-like continuum contains a nondegenerate snake-like continuum with
two distinct opposite end points. -/
theorem theorem15_1951 {M : Set X} (hM : IsSnakeLike M) (hnd : M.Nontrivial) :
    ∃ N : Set X, N ⊆ M ∧ IsSnakeLike N ∧ N.Nontrivial ∧
      ∃ p q : X, p ≠ q ∧ OppositeEndPoints N p q := by
  classical
  obtain ⟨⟨hMc, hMconn⟩, hsnake⟩ := hM
  obtain ⟨L, hLε, hLs, hLt, hLbet⟩ :=
    exists_level_sequence hMc hMconn.isPreconnected hsnake hnd
  have hsn : ∀ k, (L k).s < (L k).n := fun k => by
    have := (L k).hst; have := (L k).htn; omega
  -- `K k`: the part of `M` in the closures of Bing's subchain `D_k`
  set K : ℕ → Set X := fun k => M ∩ ⋃ u, ⋃ (hu : u < (L k).n),
    ⋃ (_ : (L k).s ≤ u ∧ u ≤ (L k).t), closure ((L k).C.link ⟨u, hu⟩) with hK
  have hmemK : ∀ k y, y ∈ K k ↔ y ∈ M ∧ ∃ u, ∃ hu : u < (L k).n, ((L k).s ≤ u ∧ u ≤ (L k).t) ∧
      y ∈ closure ((L k).C.link ⟨u, hu⟩) := by
    intro k y
    simp only [hK, mem_inter_iff, mem_iUnion, exists_prop]
  set P : ℕ → Set X := fun k => M ∩ closure ((L k).C.link ⟨(L k).s, hsn k⟩) with hP
  set Q : ℕ → Set X := fun k => M ∩ closure ((L k).C.link ⟨(L k).t, (L k).htn⟩) with hQ
  have hKsucc : ∀ k, K (k + 1) ⊆ K k := by
    intro k y hy
    obtain ⟨hyM, u, hu, ⟨h1, h2⟩, hyu⟩ := (hmemK _ y).mp hy
    obtain ⟨v, hv, h3, h4, hsub⟩ := hLbet k u hu h1 h2
    exact (hmemK k y).mpr ⟨hyM, v, hv, ⟨h3, h4⟩, subset_closure (hsub hyu)⟩
  have hKanti : Antitone K := antitone_nat_of_succ_le hKsucc
  have hPK : ∀ k, P k ⊆ K k := fun k y hy =>
    (hmemK k y).mpr ⟨hy.1, (L k).s, hsn k, ⟨le_rfl, by have := (L k).hst; omega⟩, hy.2⟩
  have hQK : ∀ k, Q k ⊆ K k := fun k y hy =>
    (hmemK k y).mpr ⟨hy.1, (L k).t, (L k).htn, ⟨by have := (L k).hst; omega, le_rfl⟩, hy.2⟩
  have hPsucc : ∀ k, P (k + 1) ⊆ P k := fun k y hy => ⟨hy.1, subset_closure (hLs k hy.2)⟩
  have hQsucc : ∀ k, Q (k + 1) ⊆ Q k := fun k y hy => ⟨hy.1, subset_closure (hLt k hy.2)⟩
  have hPne : ∀ k, (P k).Nonempty := fun k => by
    obtain ⟨z, hz1, hz2⟩ := (L k).meet ⟨(L k).s, hsn k⟩; exact ⟨z, hz2, subset_closure hz1⟩
  have hQne : ∀ k, (Q k).Nonempty := fun k => by
    obtain ⟨z, hz1, hz2⟩ := (L k).meet ⟨(L k).t, (L k).htn⟩; exact ⟨z, hz2, subset_closure hz1⟩
  have hPcl : ∀ k, IsClosed (P k) := fun k => hMc.isClosed.inter isClosed_closure
  have hQcl : ∀ k, IsClosed (Q k) := fun k => hMc.isClosed.inter isClosed_closure
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed P hPsucc
    hPne (hMc.of_isClosed_subset (hPcl 0) inter_subset_left) hPcl
  obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Q hQsucc
    hQne (hMc.of_isClosed_subset (hQcl 0) inter_subset_left) hQcl
  have hp' : ∀ k, p ∈ P k := mem_iInter.mp hp
  have hq' : ∀ k, q ∈ Q k := mem_iInter.mp hq
  have hKcl : ∀ k, IsClosed (K k) := by
    intro k
    have e : (⋃ u, ⋃ (hu : u < (L k).n), ⋃ (_ : (L k).s ≤ u ∧ u ≤ (L k).t),
        closure ((L k).C.link ⟨u, hu⟩)) =
        ⋃ u ∈ {u : Fin (L k).n | (L k).s ≤ u.val ∧ u.val ≤ (L k).t}, closure ((L k).C.link u) := by
      ext y
      simp only [mem_iUnion, mem_setOf_eq, exists_prop]
      constructor
      · rintro ⟨u, hu, h, hy⟩; exact ⟨⟨u, hu⟩, h, hy⟩
      · rintro ⟨u, h, hy⟩; exact ⟨u.val, u.isLt, h, hy⟩
    show IsClosed (M ∩ _)
    rw [e]
    exact hMc.isClosed.inter ((Set.toFinite _).isClosed_biUnion fun _ _ => isClosed_closure)
  set N : Set X := ⋂ k, K k with hN
  have hNM : N ⊆ M := fun y hy => (mem_iInter.mp hy 0).1
  have hpN : p ∈ N := mem_iInter.mpr fun k => hPK k (hp' k)
  have hqN : q ∈ N := mem_iInter.mpr fun k => hQK k (hq' k)
  have hpq : p ≠ q := by
    intro e
    have h1 := hLs 0 (hp' 1).2
    have h2 := hLt 0 (hq' 1).2
    rw [e] at h1
    have := ((L 0).C.adjacent_iff _ _).mp ⟨q, h1, h2⟩
    simp only at this
    have := (L 0).hst
    omega
  -- `N` is a continuum: the limit of the finely chained sets `K k`
  have hNlim : T13.limSup univ K = N := by
    apply Subset.antisymm
    · intro y hy
      refine mem_iInter.mpr fun k => ?_
      have := T13.limSup_subset_closure k hy
      refine closure_minimal ?_ (hKcl k) this
      intro z hz
      obtain ⟨j, -, hj, hz⟩ : ∃ j, j ∈ (univ : Set ℕ) ∧ k ≤ j ∧ z ∈ K j := by
        obtain ⟨j, hj⟩ := mem_iUnion.mp hz
        obtain ⟨hj', hj⟩ := mem_iUnion.mp hj
        obtain ⟨hkj, hj⟩ := mem_iUnion.mp hj
        exact ⟨j, hj', hkj, hj⟩
      exact hKanti hj hz
    · intro y hy
      refine mem_iInter.mpr fun k => subset_closure ?_
      exact mem_iUnion₂.mpr ⟨k, mem_univ _, mem_iUnion.mpr ⟨le_rfl, mem_iInter.mp hy k⟩⟩
  have hch : ∀ k ∈ (univ : Set ℕ), T13.ChainedAt (K k) (2 * (1 / ((k : ℝ) + 1))) := by
    intro k _
    exact chainedAt_closure_range (L k).C (hLε k) (by have := (L k).hst; omega) (L k).htn
      (fun u hu _ _ => (L k).meet ⟨u, hu⟩)
  have hε0 : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ))
  have hNpre : IsPreconnected N := hNlim ▸ isPreconnected_limSup_of_compact hMc
    (fun k _ => inter_subset_left) hε0 hch (R := p) (fun k _ => hPK k (hp' k)) infinite_univ
  have hNc : IsCompact N := hMc.of_isClosed_subset (isClosed_iInter hKcl) hNM
  refine ⟨N, hNM, ⟨⟨hNc, ⟨p, hpN⟩, hNpre⟩, fun ε hε => ?_⟩, ⟨p, hpN, q, hqN, hpq⟩, p, q, hpq, ?_⟩
  · obtain ⟨n, D, h1, h2⟩ := hsnake ε hε
    exact ⟨n, D, h1, hNM.trans h2⟩
  -- opposite end points: Bing's subchain `D_k`, with the closures of the end links of `D_{k+1}`
  -- removed from the other links
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  set C := (L k).C with hC
  set s := (L k).s with hs
  set t := (L k).t with ht
  have hst : s + 2 ≤ t := (L k).hst
  have htn : t < (L k).n := (L k).htn
  set P' := closure ((L (k + 1)).C.link ⟨(L (k + 1)).s, hsn (k + 1)⟩) with hP'
  set Q' := closure ((L (k + 1)).C.link ⟨(L (k + 1)).t, (L (k + 1)).htn⟩) with hQ'
  have hP'C : P' ⊆ linkN C s := by rw [linkN_of_lt C (hsn k)]; exact hLs k
  have hQ'C : Q' ⊆ linkN C t := by rw [linkN_of_lt C htn]; exact hLt k
  have hCst : Disjoint (linkN C s) (linkN C t) := disjoint_linkN C hst
  have hpP' : p ∈ P' := (hp' (k + 1)).2
  have hqQ' : q ∈ Q' := (hq' (k + 1)).2
  set G : ℕ → Set X := fun j => linkN C (s + j) \
    ((if j = 0 then ∅ else P') ∪ (if j = t - s then ∅ else Q')) with hG
  have hGo : ∀ j, IsOpen (G j) := by
    intro j
    refine (isOpen_linkN C _).sdiff (IsClosed.union ?_ ?_)
    · split_ifs
      · exact isClosed_empty
      · exact isClosed_closure
    · split_ifs
      · exact isClosed_empty
      · exact isClosed_closure
  have hGsub : ∀ j, G j ⊆ linkN C (s + j) := fun j => diff_subset
  have hweak : ∀ i j, i + 2 ≤ j → j < t - s + 1 → Disjoint (G i) (G j) := fun i j hij _ =>
    (disjoint_linkN C (by omega)).mono (hGsub i) (hGsub j)
  have hG0 : ∀ y, y ∈ linkN C s → y ∉ Q' → y ∈ G 0 := by
    intro y hy hyQ
    refine ⟨by simpa using hy, ?_⟩
    rintro (h | h)
    · simp at h
    · rw [if_neg (by omega)] at h; exact hyQ h
  have hGl : ∀ y, y ∈ linkN C t → y ∉ P' → y ∈ G (t - s) := by
    intro y hy hyP
    refine ⟨by rwa [show s + (t - s) = t by omega], ?_⟩
    rintro (h | h)
    · rw [if_neg (by omega)] at h; exact hyP h
    · simp at h
  have hpG : p ∈ G 0 := hG0 p (hP'C hpP') (fun h => Set.disjoint_left.mp hCst (hP'C hpP') (hQ'C h))
  have hqG : q ∈ G (t - s) :=
    hGl q (hQ'C hqQ') (fun h => Set.disjoint_left.mp hCst (hP'C h) (hQ'C hqQ'))
  have hcov : N ⊆ ⋃ j, ⋃ (_ : j < t - s + 1), G j := by
    intro y hy
    obtain ⟨-, u, hu, ⟨h1, h2⟩, hyu⟩ := (hmemK (k + 1) y).mp (mem_iInter.mp hy (k + 1))
    obtain ⟨v, hv, h3, h4, hsub⟩ := hLbet k u hu h1 h2
    have hyv : y ∈ linkN C v := by rw [linkN_of_lt C hv]; exact hsub hyu
    by_cases hyP : y ∈ P'
    · exact mem_iUnion₂.mpr ⟨0, by omega,
        hG0 y (hP'C hyP) (fun h => Set.disjoint_left.mp hCst (hP'C hyP) (hQ'C h))⟩
    by_cases hyQ : y ∈ Q'
    · exact mem_iUnion₂.mpr ⟨t - s, by omega,
        hGl y (hQ'C hyQ) (fun h => Set.disjoint_left.mp hCst (hP'C h) (hQ'C hyQ))⟩
    refine mem_iUnion₂.mpr ⟨v - s, by omega, ?_, ?_⟩
    · rwa [show s + (v - s) = v by omega]
    · rintro (h | h)
      · split_ifs at h
        · exact h
        · exact hyP h
      · split_ifs at h
        · exact h
        · exact hyQ h
  obtain ⟨a, k₀, E, ha0, hak0, hakle, hElink, hNE, -, hrange⟩ :=
    exists_chain_of_weak (n := t - s + 1) G hGo hweak hNpre hcov (i₀ := 0) (by omega) ⟨p, hpG, hpN⟩
  obtain rfl : a = 0 := by omega
  have hk₀ : k₀ = t - s + 1 := by
    have := (hrange (t - s) (by omega) ⟨q, hqG, hqN⟩).2
    omega
  subst hk₀
  have hE : ∀ j : Fin (t - s + 1), E.link j = G j := fun j => by rw [hElink j, zero_add]
  refine ⟨t - s + 1, E, fun j => ?_, hNE, ⟨by omega, ?_, ?_, fun j hj => ?_, fun j hj => ?_⟩⟩
  · rw [hE j]
    have hsub := hGsub j
    rw [linkN_of_lt C (show s + j.val < (L k).n by omega)] at hsub
    exact ⟨((hLε k) _).1.subset hsub,
      ((Metric.diam_mono hsub ((hLε k) _).1).trans_lt ((hLε k) _).2).trans hk⟩
  · rw [hE]; exact hpG
  · rw [hE]; simp only [Nat.add_sub_cancel]; exact hqG
  · rw [hE j] at hj
    apply Fin.ext
    by_contra hne
    refine hj.2 (Or.inl ?_)
    rw [if_neg hne]; exact hpP'
  · rw [hE j] at hj
    apply Fin.ext
    simp only [Nat.add_sub_cancel]
    by_contra hne
    refine hj.2 (Or.inr ?_)
    rw [if_neg hne]; exact hqQ'

/-- **Theorem 16, the self-contained half of sufficiency**: if the continuum `M` is not
hereditarily indecomposable, some point of `M` is not an end point of `M`. (With Theorem 1 of
Bing's *Concerning hereditarily indecomposable continua* — external — this gives Bing's
Theorem 16.) The skeleton's hypothesis that `M` is a continuum is not needed and has been
removed. -/
theorem exists_not_endPoint_of_not_HI {M : Set X}
    (h : ¬ IsHereditarilyIndecomposable M) : ∃ p ∈ M, ¬ IsEndPoint M p := by
  simp only [IsHereditarilyIndecomposable, Fold.Q78.IsIndecomposable, not_forall, not_and,
    exists_prop] at h
  obtain ⟨K, hKM, hK, hdec⟩ := h
  have hdec := hdec hK
  push_neg at hdec
  obtain ⟨A, B, hA, hB, hAK, hBK, hAB, hAne, hBne⟩ := hdec
  obtain ⟨p, hpK, hpA, hpB⟩ := isPreconnected_closed_iff.mp hK.2.isPreconnected A B
    hA.1.isClosed hB.1.isClosed hAB.symm.subset
    (by obtain ⟨a, ha⟩ := hA.2.nonempty; exact ⟨a, hAK ha, ha⟩)
    (by obtain ⟨b, hb⟩ := hB.2.nonempty; exact ⟨b, hBK hb, hb⟩)
  refine ⟨p, hKM hpK, fun hp => ?_⟩
  rcases (condB_of_endPoint hp).2 A B (hAK.trans hKM) (hBK.trans hKM) hA hB hpA hpB with
    h | h
  · exact hBne (by rw [← hAB, union_eq_right.mpr h])
  · exact hAne (by rw [← hAB, union_eq_left.mpr h])

end HPC.Plane
