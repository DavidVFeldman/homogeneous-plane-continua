import HPC.Plane.Fugate66Lemma1

/-!
# Batch 101: Fugate's Definition 5 (corrected) and Lemma 2 (corrected)

`ContainedExactly'` is Fugate's Definition 5 with its clause (2) in full: `A` is in no proper
subchain of `F(j..k)`. (The skeleton's gloss "equivalently `A` meets `F_j` and `F_k`" is weaker:
`A` may meet `F_k` only inside `F_{k-1}`; the faithful form — `A` has a point of `F_j` outside
`F_{j+1}, …, F_k`, and a point of `F_k` outside `F_j, …, F_{k-1}` — is what Theorem 1 uses.)

`fugate_lemma2'` is Lemma 2 in this form, from batch 100's `fugate_lemma1`; `fugate_lemma2'_taut`
adds that the chain can be taken taut (Fugate's clause (3) "if `E` is taut so is `G`" is replaced
by the stronger "`G` is taut", via the shrinking `exists_taut_shrink`).
-/

namespace HPC.Plane

open Set Metric

variable {S : Type*} [MetricSpace S]

/-- **Fugate, Definition 5** (0-indexed): `A` is *contained exactly* in the subchain `F(j..k)`:
(1) `A ⊆ F*(j..k)`; (2) `A` lies in no proper subchain of `F(j..k)`, i.e. `A` has a point of `F_j`
in no other link of `F(j..k)` and a point of `F_k` in no other link of `F(j..k)`; (3) `A` misses
the closures of `F*(0..j−1)` and `F*(k+1..n−1)`. -/
def ContainedExactly' {n : ℕ} (F : Chain S n) (A : Set S) (j k : ℕ) : Prop :=
  ∃ (hjk : j ≤ k) (hkn : k < n),
    A ⊆ ⋃ (i : Fin n) (_ : j ≤ i.val ∧ i.val ≤ k), F.link i ∧
    (A ∩ (F.link ⟨j, by omega⟩ \ ⋃ (i : Fin n) (_ : j < i.val ∧ i.val ≤ k), F.link i)).Nonempty ∧
    (A ∩ (F.link ⟨k, hkn⟩ \ ⋃ (i : Fin n) (_ : j ≤ i.val ∧ i.val < k), F.link i)).Nonempty ∧
    A ∩ closure (⋃ (i : Fin n) (_ : i.val < j), F.link i) = ∅ ∧
    A ∩ closure (⋃ (i : Fin n) (_ : k < i.val), F.link i) = ∅

/-- **Exact containment in a final segment**, keeping a point of `A` that lies in the last link
only. As batch 100's `exists_containedExactly` (largest `s` with `A ⊆ E*(s..)`, a closed
neighbourhood of `A` removed from the earlier links, trimming); the last link survives the
trimming because it meets `A`. -/
theorem exists_containedExactly_last {M A : Set S} (hM : IsPreconnected M) (hA : IsCompact A)
    (hAM : A ⊆ M) {m : ℕ} (E : Chain S m) (hE : M ⊆ E.union) (hm : 0 < m) {x₁ : S}
    (hx₁A : x₁ ∈ A) (hx₁ : x₁ ∈ E.link ⟨m - 1, by omega⟩)
    (hx₁o : ∀ i : Fin m, i.val ≠ m - 1 → x₁ ∉ E.link i) :
    ∃ (n : ℕ) (F : Chain S n) (s : ℕ), M ⊆ F.union ∧ F.Refines E ∧
      ContainedExactly' F A s (n - 1) := by
  classical
  set P : ℕ → Prop := fun s => A ⊆ ⋃ (i : Fin m) (_ : s ≤ i.val), E.link i with hP_def
  have hP0 : P 0 := fun x hx => by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hE (hAM hx))
    exact mem_iUnion₂.mpr ⟨i, Nat.zero_le _, hi⟩
  have hPbig : ∀ s, m ≤ s → ¬ P s := fun s hs hPs => by
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.mp (hPs hx₁A)
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
  set U : Set S := ⋃ (i : Fin m) (_ : s ≤ i.val), E.link i with hU_def
  have hUo : IsOpen U := isOpen_iUnion fun i => isOpen_iUnion fun _ => E.isOpen i
  obtain ⟨δ, hδ, hδU⟩ := hA.exists_thickening_subset_open hUo hPs
  set C := cthickening (δ / 2) A with hC_def
  have hCU : C ⊆ U := (cthickening_subset_thickening' hδ (half_lt_self hδ) A).trans hδU
  set L : ℕ → Set S := fun i => if i < s then linkN E i \ C else linkN E i with hL_def
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
  obtain ⟨x₀, hx₀A, hx₀⟩ := not_subset.mp (hgreat (s + 1) (by omega))
  have hx₀s : x₀ ∈ L s := by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hPs hx₀A)
    have : i.val = s := by
      by_contra hne
      exact hx₀ (mem_iUnion₂.mpr ⟨i, by omega, hxi⟩)
    rw [hLlate s le_rfl, ← this, linkN_of_lt E i.isLt]; exact hxi
  have hx₁L : x₁ ∈ L (m - 1) := by
    have hs1 : s ≤ m - 1 := by omega
    rw [hLlate _ hs1, linkN_of_lt E (by omega)]; exact hx₁
  obtain ⟨a, k, F, has, hsk, hakm, hFL, hMF, -, hrange⟩ := exists_chain_of_weak L hLo hweak hM hcov
    hsm ⟨x₀, hx₀s, hAM hx₀A⟩
  have hlast := hrange (m - 1) (by omega) ⟨x₁, hx₁L, hAM hx₁A⟩
  have hak : a + k = m := by omega
  have hk : 0 < k := by omega
  -- membership in a link of `F` gives membership in the corresponding link of `E`
  have hFE : ∀ (t : Fin k) {x : S}, x ∈ F.link t → x ∈ E.link ⟨a + t.val, by omega⟩ := by
    intro t x hx
    rw [hFL t] at hx
    have := hLsub _ hx
    rwa [linkN_of_lt E (show a + t.val < m by omega)] at this
  refine ⟨k, F, s - a, hMF, fun t => ⟨⟨a + t.val, by omega⟩, fun x hx => hFE t hx⟩,
    by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hPs hx)
    have hxL : x ∈ L i := by rw [hLlate i hi, linkN_of_lt E i.isLt]; exact hxi
    obtain ⟨h1, h2⟩ := hrange i i.isLt ⟨x, hxL, hAM hx⟩
    refine mem_iUnion₂.mpr ⟨⟨i.val - a, by omega⟩, ⟨by simp only []; omega, by simp only []; omega⟩,
      ?_⟩
    rw [hFL]
    convert hxL using 2
    simp only []; omega
  · refine ⟨x₀, hx₀A, ?_, ?_⟩
    · rw [hFL]; convert hx₀s using 2; simp only []; omega
    · intro hx
      obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
      exact hx₀ (mem_iUnion₂.mpr ⟨_, by simp only []; omega, hFE t hxt⟩)
  · refine ⟨x₁, hx₁A, ?_, ?_⟩
    · rw [hFL]; convert hx₁L using 2; simp only []; omega
    · intro hx
      obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
      exact hx₁o _ (by simp only []; omega) (hFE t hxt)
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
  · have : (⋃ (t : Fin k) (_ : k - 1 < t.val), F.link t) = ∅ := by
      ext x
      simp only [mem_iUnion, mem_empty_iff_false, iff_false, not_exists]
      intro t ht; omega
    rw [this, closure_empty, inter_empty]

/-- **Fugate, Lemma 2 (corrected)**: `A` terminal in the continuum `M`, `E` a chain covering `M`;
some chain `F` covering `M` and refining `E` contains `A` exactly (Definition 5 in full) in a final
segment `F(s..n−1)`. From `fugate_lemma1` (a point of `A` in the last link only) and
`exists_containedExactly_last`.

Shape change: the hypotheses that `M` is atriodic and hereditarily unicoherent, present in
Fugate's statement, are not needed (as for batch 100's `fugate_lemma1`). -/
theorem fugate_lemma2'_aux {M A : Set S} (hM : Fold.Q78.IsContinuum M) (hA : IsTerminalSub M A)
    {m : ℕ} (E : Chain S m) (hE : M ⊆ E.union) :
    ∃ (n : ℕ) (F : Chain S n) (s : ℕ), M ⊆ F.union ∧ F.Refines E ∧
      ContainedExactly' F A s (n - 1) := by
  obtain ⟨n, G, hn, hMG, hGE, x₁, hx₁A, hx₁, hx₁cl⟩ := fugate_lemma1 hM hA E hE
  obtain ⟨k, F, s, hMF, hFG, hex⟩ := exists_containedExactly_last hM.2.isPreconnected hA.1.1
    hA.2.1 G hMG hn hx₁A hx₁ (fun i hi hxi => hx₁cl (subset_closure (mem_iUnion₂.mpr ⟨i, hi, hxi⟩)))
  refine ⟨k, F, s, hMF, fun t => ?_, hex⟩
  obtain ⟨u, hu⟩ := hFG t
  obtain ⟨v, hv⟩ := hGE u
  exact ⟨v, hu.trans hv⟩

section Taut

variable [CompactSpace S]

/-- **Shrinking a chain to a taut one** (the construction of batch 100's `exists_taut_epsChain`,
from a given chain): the links shrink to open sets with closures inside the old links, still
covering the closed set `M` and containing prescribed points `x i ∈ D_i`; nonadjacent closures are
then disjoint, so the new chain is taut. -/
theorem exists_taut_shrink {M : Set S} (hM : IsClosed M) {n : ℕ} (D : Chain S n)
    (hMD : M ⊆ D.union) (x : Fin n → S) (hx : ∀ i, x i ∈ D.link i) :
    ∃ W : Chain S n, (∀ i, closure (W.link i) ⊆ D.link i) ∧ (∀ i, x i ∈ W.link i) ∧
      M ⊆ W.union ∧ IsTaut W := by
  classical
  obtain ⟨V, hMV, hVo, hVD⟩ := exists_subset_iUnion_closure_subset hM
    (u := D.link) D.isOpen (fun x _ => Set.toFinite _) hMD
  have small : ∀ (U : Set S), IsOpen U → ∀ x ∈ U, ∃ Q : Set S, IsOpen Q ∧ x ∈ Q ∧ closure Q ⊆ U :=
    fun U hU x hx => by
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
      exact ⟨ball x (r / 2), isOpen_ball, mem_ball_self (half_pos hr),
        closure_ball_subset_closedBall.trans ((closedBall_subset_ball (half_lt_self hr)).trans hrU)⟩
  have hC : ∀ i : Fin n, ∃ Q : Set S, IsOpen Q ∧ x i ∈ Q ∧ closure Q ⊆ D.link i :=
    fun i => small _ (D.isOpen i) (x i) (hx i)
  choose C hCo hCx hCD using hC
  have hB : ∀ j : ℕ, ∃ Q : Set S, IsOpen Q ∧ (∀ h : j + 1 < n, Q.Nonempty ∧
      closure Q ⊆ D.link ⟨j, by omega⟩ ∩ D.link ⟨j + 1, h⟩) ∧ (n ≤ j + 1 → Q = ∅) := fun j => by
    by_cases h : j + 1 < n
    · obtain ⟨x, hx⟩ := (D.adjacent_iff ⟨j, by omega⟩ ⟨j + 1, h⟩).mpr (by simp only []; omega)
      obtain ⟨Q, hQ, hxQ, hQD⟩ := small _ ((D.isOpen _).inter (D.isOpen _)) x hx
      exact ⟨Q, hQ, fun _ => ⟨⟨x, hxQ⟩, hQD⟩, fun h' => absurd h (by omega)⟩
    · exact ⟨∅, isOpen_empty, fun h' => absurd h' h, fun _ => rfl⟩
  choose B hBo hBD hBe using hB
  have hBsub : ∀ (j : ℕ) (i : Fin n), (i.val = j ∨ i.val = j + 1) → closure (B j) ⊆ D.link i := by
    intro j i hij
    by_cases h : j + 1 < n
    · rcases hij with hij | hij
      · exact (hBD j h).2.trans (inter_subset_left.trans (by rw [show i = ⟨j, by omega⟩ from
          Fin.ext hij]))
      · exact (hBD j h).2.trans (inter_subset_right.trans (by rw [show i = ⟨j + 1, h⟩ from
          Fin.ext hij]))
    · rw [hBe j (by omega), closure_empty]; exact empty_subset _
  set W : Fin n → Set S := fun i => V i ∪ C i ∪ B i.val ∪ B (i.val - 1) with hW_def
  have hWo : ∀ i, IsOpen (W i) := fun i =>
    (((hVo i).union (hCo i)).union (hBo _)).union (hBo _)
  have hWD : ∀ i, closure (W i) ⊆ D.link i := fun i => by
    simp only [hW_def, closure_union]
    exact union_subset (union_subset (union_subset (hVD i) (hCD i)) (hBsub _ i (Or.inl rfl)))
      (hBsub _ i (by omega))
  have hWx : ∀ i, x i ∈ W i := fun i => Or.inl (Or.inl (Or.inr (hCx i)))
  have hadj : ∀ i j : Fin n, (W i ∩ W j).Nonempty ↔ ((i : ℤ) - (j : ℤ)).natAbs ≤ 1 := by
    intro i j
    constructor
    · intro h
      exact (D.adjacent i j).mp (h.mono (inter_subset_inter (subset_closure.trans (hWD i))
        (subset_closure.trans (hWD j))))
    · intro h
      rcases (show i = j ∨ j.val = i.val + 1 ∨ i.val = j.val + 1 by
        rcases lt_trichotomy i.val j.val with h' | h' | h'
        · right; left; omega
        · left; exact Fin.ext h'
        · right; right; omega) with e | e | e
      · subst e
        exact ⟨x i, hWx i, hWx i⟩
      · obtain ⟨x, hx⟩ := (hBD i.val (by omega)).1
        refine ⟨x, Or.inl (Or.inr hx), Or.inr ?_⟩
        rw [show j.val - 1 = i.val by omega]; exact hx
      · obtain ⟨x, hx⟩ := (hBD j.val (by omega)).1
        refine ⟨x, Or.inr ?_, Or.inl (Or.inr hx)⟩
        rw [show i.val - 1 = j.val by omega]; exact hx
  refine ⟨⟨W, hWo, hadj⟩, hWD, hWx, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hMV hx)
    exact mem_iUnion.mpr ⟨i, Or.inl (Or.inl (Or.inl hi))⟩
  · intro i j hij
    refine infDist'_pos ⟨x i, hWx i⟩ ⟨x j, hWx j⟩ ?_
    refine Set.disjoint_left.mpr fun x hxi hxj => ?_
    have := (D.adjacent i j).mp ⟨x, hWD i hxi, hWD j hxj⟩
    omega

/-- **Fugate, Lemma 2 (corrected), taut form**: as `fugate_lemma2'_aux`, and the chain is taut.
(Fugate's clause (3), "if `E` is taut so is `G`", is replaced by "`G` is taut": shrink the chain
by `exists_taut_shrink`, keeping the two witness points of Definition 5 (2).) -/
theorem fugate_lemma2'_taut {M A : Set S} (hM : Fold.Q78.IsContinuum M) (hA : IsTerminalSub M A)
    {m : ℕ} (E : Chain S m) (hE : M ⊆ E.union) :
    ∃ (n : ℕ) (F : Chain S n) (s : ℕ), M ⊆ F.union ∧ F.Refines E ∧
      ContainedExactly' F A s (n - 1) ∧ IsTaut F := by
  classical
  obtain ⟨n, F, s, hMF, hFE, hsn, hn, hAcov, ⟨y₁, hy₁A, hy₁, hy₁o⟩, ⟨y₂, hy₂A, hy₂, hy₂o⟩, hcl1,
    -⟩ := fugate_lemma2'_aux hM hA E hE
  set x : Fin n → S := fun i => if i.val = s then y₁ else if i.val = n - 1 then y₂ else
    (F.link_nonempty i).some with hx_def
  have hx : ∀ i, x i ∈ F.link i := fun i => by
    simp only [hx_def]
    split_ifs with h1 h2
    · rw [show i = ⟨s, by omega⟩ from Fin.ext h1]; exact hy₁
    · rw [show i = ⟨n - 1, hn⟩ from Fin.ext h2]; exact hy₂
    · exact (F.link_nonempty i).some_mem
  obtain ⟨W, hWF, hWx, hMW, hWt⟩ := exists_taut_shrink hM.1.isClosed F hMF x hx
  have hWF' : ∀ i, W.link i ⊆ F.link i := fun i => subset_closure.trans (hWF i)
  have hxs : x ⟨s, by omega⟩ = y₁ := by simp [hx_def]
  have hcl1W : A ∩ closure (⋃ (i : Fin n) (_ : i.val < s), W.link i) = ∅ :=
    eq_empty_of_subset_empty (hcl1 ▸ inter_subset_inter_right _
      (closure_mono (iUnion₂_mono fun i _ => hWF' i)))
  refine ⟨n, W, s, hMW, fun i => ?_, ⟨hsn, hn, ?_, ⟨y₁, hy₁A, ?_, ?_⟩, ?_, hcl1W, ?_⟩, hWt⟩
  · obtain ⟨j, hj⟩ := hFE i
    exact ⟨j, (hWF' i).trans hj⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hMW (hA.2.1 hz))
    refine mem_iUnion₂.mpr ⟨i, ⟨?_, by omega⟩, hi⟩
    by_contra h
    have : z ∈ A ∩ closure (⋃ (i : Fin n) (_ : i.val < s), W.link i) :=
      ⟨hz, subset_closure (mem_iUnion₂.mpr ⟨i, by omega, hi⟩)⟩
    rw [hcl1W] at this; exact this
  · rw [← hxs]; exact hWx _
  · intro h
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp h
    exact hy₁o (mem_iUnion₂.mpr ⟨i, hi, hWF' i hzi⟩)
  · by_cases hs : s = n - 1
    · refine ⟨y₁, hy₁A, ?_, ?_⟩
      · have : x ⟨n - 1, hn⟩ = y₁ := by simp [hx_def, hs]
        rw [← this]; exact hWx _
      · intro h
        obtain ⟨i, hi, -⟩ := mem_iUnion₂.mp h
        omega
    · refine ⟨y₂, hy₂A, ?_, ?_⟩
      · have : x ⟨n - 1, hn⟩ = y₂ := by
          simp [hx_def, Ne.symm hs]
        rw [← this]; exact hWx _
      · intro h
        obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp h
        exact hy₂o (mem_iUnion₂.mpr ⟨i, hi, hWF' i hzi⟩)
  · have : (⋃ (t : Fin n) (_ : n - 1 < t.val), W.link t) = ∅ := by
      ext z
      simp only [mem_iUnion, mem_empty_iff_false, iff_false, not_exists]
      intro t ht; omega
    rw [this, closure_empty, inter_empty]

end Taut

end HPC.Plane
