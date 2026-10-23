import HPC.Plane.Fugate66BLemma2

/-!
# Batch 101: Fugate's Lemma 4 (the fitting), in ℕ-indexed form

`fugate_lemma4_weak` is Fugate's Lemma 4 with the two chains replaced by finite families of open
sets indexed by `ℕ` (empty past the end) that are *weak chains* (nonadjacent members disjoint) —
in fact taut: nonadjacent closures are disjoint. Fugate's cut links need not still form chains (the
cut `E_i = G_i − Cl F*(1,k−1)` may lose its overlap with `E_{i+1}`); the weak form records exactly
what the proof of Theorem 1 uses, and trimming (`exists_chain_of_weak`) turns weak chains into
chains where chains are needed. All data of Lemma 4 are kept (`Fit`).
-/

namespace HPC.Plane

open Set Metric Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

omit [CompactSpace S] in
theorem infDist'_le {U V : Set S} {u v : S} (hu : u ∈ U) (hv : v ∈ V) :
    IsTaut.infDist' U V ≤ dist u v := by
  unfold IsTaut.infDist'
  refine (ciInf_le ⟨0, ?_⟩ (⟨u, hu⟩ : U)).trans (ciInf_le ⟨0, ?_⟩ (⟨v, hv⟩ : V))
  · rintro _ ⟨x, rfl⟩; exact Real.iInf_nonneg fun y => dist_nonneg
  · rintro _ ⟨y, rfl⟩; exact dist_nonneg

omit [CompactSpace S] in
/-- Sets at positive distance have disjoint closures. -/
theorem disjoint_closure_of_infDist'_pos {U V : Set S} (h : 0 < IsTaut.infDist' U V) :
    Disjoint (closure U) (closure V) := by
  rw [Set.disjoint_left]
  intro x hxU hxV
  obtain ⟨u, hu, hux⟩ := Metric.mem_closure_iff.mp hxU (IsTaut.infDist' U V / 2) (half_pos h)
  obtain ⟨v, hv, hvx⟩ := Metric.mem_closure_iff.mp hxV (IsTaut.infDist' U V / 2) (half_pos h)
  have h1 := infDist'_le hu hv
  have h2 := dist_triangle u x v
  have h3 := dist_comm u x
  linarith

omit [CompactSpace S] in
/-- In a taut chain nonadjacent links have disjoint closures (ℕ-indexed). -/
theorem IsTaut.disjoint_closure_linkN {n : ℕ} {F : Chain S n} (hF : IsTaut F) {i l : ℕ}
    (h : i + 2 ≤ l) : Disjoint (closure (linkN F i)) (closure (linkN F l)) := by
  by_cases hl : l < n
  · rw [linkN_of_lt F (by omega : i < n), linkN_of_lt F hl]
    exact disjoint_closure_of_infDist'_pos (hF _ _ (Or.inr (by simp only []; omega)))
  · rw [show linkN F l = ∅ from dif_neg hl, closure_empty]; exact disjoint_empty _

omit [CompactSpace S] in
theorem mem_closure_biUnion_lt {X : ℕ → Set S} {k : ℕ} {x : S}
    (hx : x ∈ closure (⋃ l, ⋃ (_ : l < k), X l)) : ∃ l < k, x ∈ closure (X l) := by
  have : (⋃ l, ⋃ (_ : l < k), X l) = ⋃ l ∈ Set.Iio k, X l := rfl
  rw [this, (Set.finite_Iio k).closure_biUnion] at hx
  simpa using hx

omit [CompactSpace S] in
theorem mem_closure_biUnion_add_two_le {X : ℕ → Set S} {k : ℕ} {x : S}
    (hx : x ∈ closure (⋃ l, ⋃ (_ : l + 2 ≤ k), X l)) : ∃ l, l + 2 ≤ k ∧ x ∈ closure (X l) := by
  have : (⋃ l, ⋃ (_ : l + 2 ≤ k), X l) = ⋃ l ∈ {l | l + 2 ≤ k}, X l := rfl
  have hfin : ({l | l + 2 ≤ k} : Set ℕ).Finite :=
    (Set.finite_Iio k).subset (fun l hl => by simp only [mem_setOf_eq] at hl; simp only [mem_Iio]; omega)
  rw [this, hfin.closure_biUnion] at hx
  simpa using hx

omit [CompactSpace S] in
theorem linkN_small {n : ℕ} {D : Chain S n} {ε : ℝ} (hD : IsEpsChain D ε) (hε : 0 < ε) (i : ℕ) :
    Bornology.IsBounded (linkN D i) ∧ diam (linkN D i) < ε := by
  by_cases hi : i < n
  · rw [linkN_of_lt D hi]; exact hD _
  · rw [show linkN D i = ∅ from dif_neg hi]; simpa using hε

/-- **The data of Fugate's Lemma 4**, ℕ-indexed (0-indexed as the skeleton; `E i = ∅` for `i ≥ m`,
`F i = ∅` for `i ≥ n`). Clauses (1)–(6) of Lemma 4, with tautness stated as disjointness of
nonadjacent closures and Definition 5 spelled out. -/
structure Fit (A B : Set S) (ε : ℝ) (m n j k t : ℕ) (E F : ℕ → Set S) : Prop where
  openE : ∀ i, IsOpen (E i)
  openF : ∀ i, IsOpen (F i)
  smallE : ∀ i, Bornology.IsBounded (E i) ∧ diam (E i) < ε
  smallF : ∀ i, Bornology.IsBounded (F i) ∧ diam (F i) < ε
  tautE : ∀ i l, i + 2 ≤ l → Disjoint (closure (E i)) (closure (E l))
  tautF : ∀ i l, i + 2 ≤ l → Disjoint (closure (F i)) (closure (F l))
  endE : ∀ i, m ≤ i → E i = ∅
  endF : ∀ i, n ≤ i → F i = ∅
  covA : A ⊆ ⋃ i, E i
  covB : B ⊆ ⋃ i, F i
  jm : j < m
  kn : k < n
  jt : j ≤ t
  tm : t < m
  exE_first : ∃ c ∈ A ∩ B, c ∈ E j ∧ ∀ i, j < i → c ∉ E i
  exE_last : ∃ c ∈ A ∩ B, c ∈ E (m - 1) ∧ ∀ i, i < m - 1 → c ∉ E i
  exE_cl : A ∩ B ∩ closure (⋃ i, ⋃ (_ : i < j), E i) = ∅
  exF_first : ∃ c ∈ A ∩ B, c ∈ F k ∧ ∀ i, k < i → c ∉ F i
  exF_last : ∃ c ∈ A ∩ B, c ∈ F (n - 1) ∧ ∀ i, i < n - 1 → c ∉ F i
  exF_cl : A ∩ B ∩ closure (⋃ i, ⋃ (_ : i < k), F i) = ∅
  refine : ∀ i, k ≤ i → i < n → ∃ i', j ≤ i' ∧ i' < m ∧ closure (F i) ⊆ E i'
  four : ∀ i l, i < j → Disjoint (closure (E i)) (F l)
  five : ∀ l i, l + 2 ≤ k → Disjoint (closure (F l)) (E i)
  sixA : 1 ≤ k → Disjoint (closure (F (k - 1))) A
  sixt : 1 ≤ k → ∀ i, i ≠ t → Disjoint (closure (F (k - 1))) (E i)

/-- **Fugate, Lemma 4, ℕ-indexed form.** `A`, `B` snake-like, `A ∩ B` terminal in both: for every
`ε > 0` there are families `E`, `F` with all the data of Lemma 4 (`Fit`). Fugate's proof: `G` a
taut `ε`-chain of `A` with `A ∩ B ⊆ᵉ G(j..m−1)` (`fugate_lemma2'_taut`); a Lebesgue number `δ` of
the cover of `A ∩ B` by `G_j − Cl G*(0..j−1), G_{j+1}, …`; `H` a taut `ε''`-chain of `B`,
`ε'' = min(ε, δ)/2`, with `A ∩ B ⊆ᵉ H(k..n−1)`; every link of `H(k..n−1)` meets `A ∩ B`, so its
closure lies in a link of `G(j..m−1)` and misses `Cl G*(0..j−1)`; `t` with `Cl H_k ⊆ G_t`;
disjoint open `S ⊇ A − B`, `T ⊇ B − A`; `F_i = H_i ∩ T` (`i < k`), `F_i = H_i` (`i ≥ k`);
`E_i = G_i ∩ S` (`i < j`), `E_i = G_i − Cl F*(0..k−1)` (`i ≥ j`, `i ≠ t`),
`E_t = G_t − Cl F*(0..k−2)`.

Fugate's Lemma 2 needs no hereditary unicoherence or atriodicity here (batch 100), and his `b`
(the least distance between nonadjacent links of `G`) is not needed. -/
theorem fugate_lemma4_weak {A B : Set S} (hA : IsSnakeLike A) (hB : IsSnakeLike B)
    (hTA : IsTerminalSub A (A ∩ B)) (hTB : IsTerminalSub B (A ∩ B)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n j k t : ℕ) (E F : ℕ → Set S), Fit A B ε m n j k t E F := by
  classical
  set C := A ∩ B with hC_def
  -- the chain `G` for `A`
  obtain ⟨m₀, G₀, hG₀ε, hAG₀⟩ := hA.2 ε hε
  obtain ⟨m, G, j, hAG, hGG₀, hGex, hGt⟩ := fugate_lemma2'_taut hA.1 hTA G₀ hAG₀
  have hGε : IsEpsChain G ε := isEpsChain_of_refines hGG₀ hG₀ε
  obtain ⟨hjm1, hm1, hCG, ⟨cj, hcjC, hcj, hcjo⟩, ⟨cm, hcmC, hcm, hcmo⟩, hCGcl, -⟩ := hGex
  set Gcl := closure (⋃ (i : Fin m) (_ : i.val < j), G.link i) with hGcl
  -- a Lebesgue number
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (s := C)
    (c := fun i : Fin m => if j ≤ i.val then G.link i \ Gcl else ∅) hTA.1.1
    (fun i => by
      dsimp only
      split_ifs
      exacts [(G.isOpen i).sdiff isClosed_closure, isOpen_empty])
    (fun x hx => by
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hCG hx)
      refine mem_iUnion.mpr ⟨i, ?_⟩
      simp only [if_pos hi.1]
      exact ⟨hxi, fun h => (eq_empty_iff_forall_notMem.mp hCGcl) x ⟨hx, h⟩⟩)
  -- the chain `H` for `B`
  set ε₂ := min ε δ / 2 with hε₂
  have hε₂pos : 0 < ε₂ := by have := lt_min hε hδ; rw [hε₂]; linarith
  have hε₂ε : ε₂ < ε := by have := min_le_left ε δ; rw [hε₂]; linarith
  have hε₂δ : ε₂ < δ := by have := min_le_right ε δ; rw [hε₂]; linarith
  obtain ⟨n₀, H₀, hH₀ε, hBH₀⟩ := hB.2 ε₂ hε₂pos
  obtain ⟨n, H, k, hBH, hHH₀, hHex, hHt⟩ := fugate_lemma2'_taut hB.1 hTB H₀ hBH₀
  have hHε : IsEpsChain H ε₂ := isEpsChain_of_refines hHH₀ hH₀ε
  obtain ⟨hkn1, hn1, hCH, ⟨ck, hckC, hck, hcko⟩, ⟨cn, hcnC, hcn, hcno⟩, hCHcl, -⟩ := hHex
  -- every link of `H(k..n−1)` meets `A ∩ B`
  have hHmeet : ∀ i : Fin n, k ≤ i.val → (C ∩ H.link i).Nonempty := by
    intro i hi
    rcases eq_or_lt_of_le hi with h | h
    · exact ⟨ck, hckC, by rwa [show i = ⟨k, by omega⟩ from Fin.ext h.symm]⟩
    rcases eq_or_lt_of_le (show i.val ≤ n - 1 by omega) with h' | h'
    · exact ⟨cn, hcnC, by rwa [show i = ⟨n - 1, hn1⟩ from Fin.ext h']⟩
    exact H.inter_link_nonempty_between hTB.1.2.isPreconnected
      (fun x hx => by
        obtain ⟨i, -, hi⟩ := mem_iUnion₂.mp (hCH hx); exact mem_iUnion.mpr ⟨i, hi⟩)
      (show (⟨k, by omega⟩ : Fin n) < i from Fin.lt_def.mpr h)
      (show i < ⟨n - 1, hn1⟩ from Fin.lt_def.mpr h') ⟨ck, hckC, hck⟩ ⟨cn, hcnC, hcn⟩
  -- so its closure lies in a link of `G(j..m−1)` and misses `Cl G*(0..j−1)`
  have hHfit : ∀ i : Fin n, k ≤ i.val →
      ∃ i' : Fin m, j ≤ i'.val ∧ closure (H.link i) ⊆ G.link i' \ Gcl := by
    intro i hi
    obtain ⟨c, hcC, hci⟩ := hHmeet i hi
    obtain ⟨i', hi'⟩ := hleb c hcC
    by_cases hji : j ≤ i'.val
    · refine ⟨i', hji, ?_⟩
      have h1 : H.link i ⊆ closedBall c ε₂ := fun y hy =>
        mem_closedBall.mpr ((dist_le_diam_of_mem (hHε i).1 hy hci).trans (hHε i).2.le)
      have h2 : closure (H.link i) ⊆ closedBall c ε₂ := closure_minimal h1 isClosed_closedBall
      have := h2.trans ((closedBall_subset_ball hε₂δ).trans hi')
      simpa [if_pos hji] using this
    · simp only [if_neg hji] at hi'
      exact absurd (hi' (mem_ball_self hδ)) (notMem_empty _)
  obtain ⟨t', htj, htfit⟩ := hHfit ⟨k, by omega⟩ le_rfl
  set t := t'.val with ht_def
  -- separating `A − B` from `B − A`
  obtain ⟨S₁, T₁, hS₁, hT₁, hAS₁, hBT₁, hST⟩ : SeparatedNhds (A \ B) (B \ A) :=
    separatedNhds_iff_disjoint.mpr (completely_normal
      (Set.disjoint_left.mpr fun x hx hx' =>
        hx'.2 (closure_minimal diff_subset hA.1.1.isClosed hx))
      (Set.disjoint_left.mpr fun x hx hx' =>
        hx.2 (closure_minimal diff_subset hB.1.1.isClosed hx')))
  have hST' : Disjoint S₁ (closure T₁) := hST.closure_right hS₁
  have hST'' : Disjoint (closure S₁) T₁ := hST.closure_left hT₁
  -- the families
  set Fl : ℕ → Set S := fun i => if i < k then linkN H i ∩ T₁ else linkN H i with hFl
  set Cl := closure (⋃ l, ⋃ (_ : l < k), Fl l) with hCl
  set Cl2 := closure (⋃ l, ⋃ (_ : l + 2 ≤ k), Fl l) with hCl2
  set El : ℕ → Set S := fun i => if i < j then linkN G i ∩ S₁ else
    if i = t then linkN G i \ Cl2 else linkN G i \ Cl with hEl
  have hFlsub : ∀ i, Fl i ⊆ linkN H i := fun i => by
    simp only [hFl]; split_ifs
    · exact inter_subset_left
    · exact subset_rfl
  have hElsub : ∀ i, El i ⊆ linkN G i := fun i => by
    simp only [hEl]; split_ifs
    · exact inter_subset_left
    · exact diff_subset
    · exact diff_subset
  have hFlT : ∀ i, i < k → Fl i ⊆ T₁ := fun i hi => by
    simp only [hFl, if_pos hi]; exact inter_subset_right
  have hFllate : ∀ i, k ≤ i → Fl i = linkN H i := fun i hi => by
    simp only [hFl, if_neg (show ¬ i < k by omega)]
  have hElS : ∀ i, i < j → El i ⊆ S₁ := fun i hi => by
    simp only [hEl, if_pos hi]; exact inter_subset_right
  have hElCl2 : ∀ i, j ≤ i → Disjoint (El i) Cl2 := fun i hi => by
    simp only [hEl, if_neg (show ¬ i < j by omega)]
    split_ifs
    · exact disjoint_sdiff_left
    · exact disjoint_sdiff_left.mono_right (closure_mono (iUnion₂_mono' fun l hl =>
        ⟨l, by omega, subset_rfl⟩))
  have hElCl : ∀ i, j ≤ i → i ≠ t → Disjoint (El i) Cl := fun i hi hit => by
    simp only [hEl, if_neg (show ¬ i < j by omega), if_neg hit]
    exact disjoint_sdiff_left
  have hCl2Cl : Cl2 ⊆ Cl := closure_mono (iUnion₂_mono' fun l hl => ⟨l, by omega, subset_rfl⟩)
  -- `A ∩ B` misses the early links
  have hCGearly : ∀ i, i < j → Disjoint C (linkN G i) := fun i hi =>
    Set.disjoint_left.mpr fun x hxC hxG => by
      obtain ⟨h, hx⟩ := (mem_linkN G).mp hxG
      exact (eq_empty_iff_forall_notMem.mp hCGcl) x
        ⟨hxC, subset_closure (mem_iUnion₂.mpr ⟨⟨i, h⟩, hi, hx⟩)⟩
  have hCHearly : ∀ i, i < k → Disjoint C (closure (linkN H i)) := fun i hi =>
    Set.disjoint_left.mpr fun x hxC hxH => by
      refine (eq_empty_iff_forall_notMem.mp hCHcl) x ⟨hxC, closure_mono ?_ hxH⟩
      intro y hy
      obtain ⟨h, hy⟩ := (mem_linkN H).mp hy
      exact mem_iUnion₂.mpr ⟨⟨i, h⟩, hi, hy⟩
  -- the removed set misses `A`
  have hFlA : ∀ l, l < k → Disjoint (closure (Fl l)) A := fun l hl =>
    Set.disjoint_left.mpr fun x hxF hxA => by
      by_cases hxB : x ∈ B
      · exact Set.disjoint_left.mp (hCHearly l hl) ⟨hxA, hxB⟩
          (closure_mono (hFlsub l) hxF)
      · exact Set.disjoint_left.mp hST' (hAS₁ ⟨hxA, hxB⟩) (closure_mono (hFlT l hl) hxF)
  have hClA : Disjoint Cl A := Set.disjoint_left.mpr fun x hx hxA => by
    obtain ⟨l, hl, hxl⟩ := mem_closure_biUnion_lt hx
    exact Set.disjoint_left.mp (hFlA l hl) hxl hxA
  have hClH : ∀ i, k + 1 ≤ i → Disjoint (closure (linkN H i)) Cl := fun i hi =>
    Set.disjoint_left.mpr fun x hxi hx => by
      obtain ⟨l, hl, hxl⟩ := mem_closure_biUnion_lt hx
      exact Set.disjoint_left.mp (hHt.disjoint_closure_linkN (show l + 2 ≤ i by omega))
        (closure_mono (hFlsub l) hxl) hxi
  have hCl2H : ∀ i, k ≤ i → Disjoint (closure (linkN H i)) Cl2 := fun i hi =>
    Set.disjoint_left.mpr fun x hxi hx => by
      obtain ⟨l, hl, hxl⟩ := mem_closure_biUnion_add_two_le hx
      exact Set.disjoint_left.mp (hHt.disjoint_closure_linkN (show l + 2 ≤ i by omega))
        (closure_mono (hFlsub l) hxl) hxi
  refine ⟨m, n, j, k, t, El, Fl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega,
    htj, t'.isLt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- openE
    intro i
    simp only [hEl]; split_ifs
    · exact (isOpen_linkN G i).inter hS₁
    · exact (isOpen_linkN G i).sdiff isClosed_closure
    · exact (isOpen_linkN G i).sdiff isClosed_closure
  · -- openF
    intro i
    simp only [hFl]; split_ifs
    · exact (isOpen_linkN H i).inter hT₁
    · exact isOpen_linkN H i
  · -- smallE
    intro i
    have := linkN_small hGε hε i
    exact ⟨this.1.subset (hElsub i), (diam_mono (hElsub i) this.1).trans_lt this.2⟩
  · -- smallF
    intro i
    have := linkN_small hHε hε₂pos i
    exact ⟨this.1.subset (hFlsub i), ((diam_mono (hFlsub i) this.1).trans_lt this.2).trans hε₂ε⟩
  · -- tautE
    intro i l hil
    exact (hGt.disjoint_closure_linkN hil).mono (closure_mono (hElsub i))
      (closure_mono (hElsub l))
  · -- tautF
    intro i l hil
    exact (hHt.disjoint_closure_linkN hil).mono (closure_mono (hFlsub i))
      (closure_mono (hFlsub l))
  · -- endE
    intro i hi
    exact eq_empty_of_subset_empty ((hElsub i).trans (by rw [show linkN G i = ∅ from
      dif_neg (by omega)]))
  · -- endF
    intro i hi
    exact eq_empty_of_subset_empty ((hFlsub i).trans (by rw [show linkN H i = ∅ from
      dif_neg (by omega)]))
  · -- covA
    intro x hxA
    obtain ⟨i, hi, hxi⟩ := (mem_union_iff_linkN G).mp (hAG hxA)
    refine mem_iUnion.mpr ⟨i, ?_⟩
    by_cases hij : i < j
    · simp only [hEl, if_pos hij]
      refine ⟨hxi, hAS₁ ⟨hxA, fun hxB => ?_⟩⟩
      exact Set.disjoint_left.mp (hCGearly i hij) ⟨hxA, hxB⟩ hxi
    · have hxCl : x ∉ Cl := fun h => Set.disjoint_left.mp hClA h hxA
      simp only [hEl, if_neg hij]
      split_ifs
      · exact ⟨hxi, fun h => hxCl (hCl2Cl h)⟩
      · exact ⟨hxi, hxCl⟩
  · -- covB
    intro x hxB
    obtain ⟨i, hi, hxi⟩ := (mem_union_iff_linkN H).mp (hBH hxB)
    refine mem_iUnion.mpr ⟨i, ?_⟩
    by_cases hik : i < k
    · simp only [hFl, if_pos hik]
      refine ⟨hxi, hBT₁ ⟨hxB, fun hxA => ?_⟩⟩
      exact Set.disjoint_left.mp (hCHearly i hik) ⟨hxA, hxB⟩ (subset_closure hxi)
    · rw [hFllate i (by omega)]; exact hxi
  · -- exE_first
    refine ⟨cj, hcjC, ?_, fun i hji hci => ?_⟩
    · have hcCl : cj ∉ Cl := fun h => Set.disjoint_left.mp hClA h hcjC.1
      have hcG : cj ∈ linkN G j := by rw [linkN_of_lt G (by omega)]; exact hcj
      simp only [hEl, if_neg (lt_irrefl j)]
      split_ifs
      · exact ⟨hcG, fun h => hcCl (hCl2Cl h)⟩
      · exact ⟨hcG, hcCl⟩
    · obtain ⟨h, hc⟩ := (mem_linkN G).mp (hElsub i hci)
      exact hcjo (mem_iUnion₂.mpr ⟨⟨i, h⟩, ⟨hji, by simp only []; omega⟩, hc⟩)
  · -- exE_last
    refine ⟨cm, hcmC, ?_, fun i hi hci => ?_⟩
    · have hcCl : cm ∉ Cl := fun h => Set.disjoint_left.mp hClA h hcmC.1
      have hcG : cm ∈ linkN G (m - 1) := by rw [linkN_of_lt G (by omega)]; exact hcm
      simp only [hEl, if_neg (show ¬ m - 1 < j by omega)]
      split_ifs
      · exact ⟨hcG, fun h => hcCl (hCl2Cl h)⟩
      · exact ⟨hcG, hcCl⟩
    · have hcG := hElsub i hci
      by_cases hij : i < j
      · exact Set.disjoint_left.mp (hCGearly i hij) hcmC hcG
      · obtain ⟨h, hc⟩ := (mem_linkN G).mp hcG
        exact hcmo (mem_iUnion₂.mpr ⟨⟨i, h⟩, ⟨by simp only []; omega, hi⟩, hc⟩)
  · -- exE_cl
    refine eq_empty_of_subset_empty (hCGcl ▸ inter_subset_inter_right _ (closure_mono ?_))
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    obtain ⟨h, hx⟩ := (mem_linkN G).mp (hElsub i hxi)
    exact mem_iUnion₂.mpr ⟨⟨i, h⟩, hi, hx⟩
  · -- exF_first
    refine ⟨ck, hckC, ?_, fun i hki hci => ?_⟩
    · rw [hFllate k le_rfl, linkN_of_lt H (by omega)]; exact hck
    · obtain ⟨h, hc⟩ := (mem_linkN H).mp (hFlsub i hci)
      exact hcko (mem_iUnion₂.mpr ⟨⟨i, h⟩, ⟨hki, by simp only []; omega⟩, hc⟩)
  · -- exF_last
    refine ⟨cn, hcnC, ?_, fun i hi hci => ?_⟩
    · rw [hFllate (n - 1) (by omega), linkN_of_lt H (by omega)]; exact hcn
    · have hcH := hFlsub i hci
      by_cases hik : i < k
      · exact Set.disjoint_left.mp (hCHearly i hik) hcnC (subset_closure hcH)
      · obtain ⟨h, hc⟩ := (mem_linkN H).mp hcH
        exact hcno (mem_iUnion₂.mpr ⟨⟨i, h⟩, ⟨by simp only []; omega, hi⟩, hc⟩)
  · -- exF_cl
    refine eq_empty_of_subset_empty (hCHcl ▸ inter_subset_inter_right _ (closure_mono ?_))
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    obtain ⟨h, hx⟩ := (mem_linkN H).mp (hFlsub i hxi)
    exact mem_iUnion₂.mpr ⟨⟨i, h⟩, hi, hx⟩
  · -- refine
    intro i hki hin
    rw [hFllate i hki, linkN_of_lt H hin]
    rcases eq_or_lt_of_le hki with h | h
    · subst h
      refine ⟨t, htj, t'.isLt, fun x hx => ?_⟩
      have hx' := htfit hx
      simp only [hEl, if_neg (show ¬ t < j by omega)]
      refine ⟨by rw [linkN_of_lt G t'.isLt]; exact hx'.1, fun hx2 => ?_⟩
      exact Set.disjoint_left.mp (hCl2H k le_rfl) (by rwa [linkN_of_lt H hin]) hx2
    · obtain ⟨i', hji', hfit⟩ := hHfit ⟨i, hin⟩ hki
      refine ⟨i', hji', i'.isLt, fun x hx => ?_⟩
      have hx' := hfit hx
      have hxG : x ∈ linkN G i' := by rw [linkN_of_lt G i'.isLt]; exact hx'.1
      have hxH : x ∈ closure (linkN H i) := by rwa [linkN_of_lt H hin]
      simp only [hEl, if_neg (show ¬ i'.val < j by omega)]
      split_ifs
      · exact ⟨hxG, fun h2 => Set.disjoint_left.mp (hClH i (by omega)) hxH (hCl2Cl h2)⟩
      · exact ⟨hxG, fun h2 => Set.disjoint_left.mp (hClH i (by omega)) hxH h2⟩
  · -- four
    intro i l hij
    have hcl : closure (El i) ⊆ closure S₁ := closure_mono (hElS i hij)
    by_cases hlk : l < k
    · exact (hST''.mono_right (hFlT l hlk)).mono_left hcl
    · rw [hFllate l (by omega)]
      by_cases hln : l < n
      · obtain ⟨i', -, hfit⟩ := hHfit ⟨l, hln⟩ (by simp only []; omega)
        rw [linkN_of_lt H hln]
        refine Set.disjoint_left.mpr fun x hx hxH => (hfit (subset_closure hxH)).2 ?_
        refine closure_mono ?_ (closure_mono (hElsub i) hx)
        intro y hy
        obtain ⟨h, hy⟩ := (mem_linkN G).mp hy
        exact mem_iUnion₂.mpr ⟨⟨i, h⟩, hij, hy⟩
      · rw [show linkN H l = ∅ from dif_neg hln]; exact disjoint_empty _
  · -- five
    intro l i hlk
    have hFl2 : closure (Fl l) ⊆ Cl2 :=
      closure_mono (subset_iUnion₂_of_subset l hlk subset_rfl)
    by_cases hij : i < j
    · exact Set.disjoint_left.mpr fun x hx hxE =>
        Set.disjoint_left.mp hST' (hElS i hij hxE) (closure_mono (hFlT l (by omega)) hx)
    · exact ((hElCl2 i (by omega)).mono_right hFl2).symm
  · -- sixA
    intro hk
    exact hFlA (k - 1) (by omega)
  · -- sixt
    intro hk i hit
    have hFk : closure (Fl (k - 1)) ⊆ Cl :=
      closure_mono (subset_iUnion₂_of_subset (k - 1) (by omega) subset_rfl)
    by_cases hij : i < j
    · exact Set.disjoint_left.mpr fun x hx hxE =>
        Set.disjoint_left.mp hST' (hElS i hij hxE) (closure_mono (hFlT (k - 1) (by omega)) hx)
    · exact ((hElCl i (by omega) hit).mono_right hFk).symm

end HPC.Plane
