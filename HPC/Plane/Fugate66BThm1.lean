import HPC.Plane.Fugate66BLemma4
import HPC.Plane.Fugate66BHU

/-!
# Batch 101: Fugate's Theorem 1, sufficiency

From the data of Lemma 4 (`Fit`), the two-case construction of Fugate (pp. 466–467) of a weak
`ε`-chain covering `A ∪ B` (Case i: `E ⊕ F(k−1..0)`; Case ii: the chain `𝒢`, after Claims 2–3 and
the separation of `D`), turned into a chain by trimming (`isSnakeLike_of_weak`).
-/

namespace HPC.Plane

open Set Metric Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

omit [CompactSpace S] in
/-- **Snake-likeness from weak chains.** A continuum which, for every `ε > 0`, is covered by a
finite family of open sets of diameter `< ε` with nonadjacent members disjoint, is snake-like
(trim the family to a chain with `exists_chain_of_weak`). -/
theorem isSnakeLike_of_weak {M : Set S} (hM : Fold.Q78.IsContinuum M)
    (h : ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (L : ℕ → Set S), (∀ i, IsOpen (L i)) ∧
      (∀ i, Bornology.IsBounded (L i) ∧ diam (L i) < ε) ∧
      (∀ i l, i + 2 ≤ l → l < N → Disjoint (L i) (L l)) ∧ M ⊆ ⋃ i, ⋃ (_ : i < N), L i) :
    IsSnakeLike M := by
  refine ⟨hM, fun ε hε => ?_⟩
  obtain ⟨N, L, hLo, hLs, hLw, hML⟩ := h ε hε
  obtain ⟨x, hx⟩ := hM.2.nonempty
  obtain ⟨i₀, hi₀, hxi⟩ := mem_iUnion₂.mp (hML hx)
  obtain ⟨a, k, E, -, -, -, hEL, hME, -, -⟩ :=
    exists_chain_of_weak L hLo hLw hM.2.isPreconnected hML hi₀ ⟨x, hxi, hx⟩
  exact ⟨k, E, fun t => by rw [hEL t]; exact hLs _, hME⟩

omit [CompactSpace S] in
/-- A preconnected set covered by a weak chain, meeting its members `a ≤ r ≤ b`, meets member
`r`. -/
theorem meets_between_of_weak {n : ℕ} {F : ℕ → Set S} (hFo : ∀ i, IsOpen (F i))
    (hw : ∀ i l, i + 2 ≤ l → Disjoint (F i) (F l)) {Z : Set S} (hZ : IsPreconnected Z)
    (hcov : Z ⊆ ⋃ i, ⋃ (_ : i < n), F i) {a b r : ℕ} (har : a ≤ r) (hrb : r ≤ b) (hbn : b < n)
    (ha : (F a ∩ Z).Nonempty) (hb : (F b ∩ Z).Nonempty) : (F r ∩ Z).Nonempty := by
  by_contra hr
  rw [not_nonempty_iff_eq_empty] at hr
  rcases eq_or_lt_of_le har with rfl | har'
  · exact (nonempty_iff_ne_empty.mp ha) hr
  rcases eq_or_lt_of_le hrb with rfl | hrb'
  · exact (nonempty_iff_ne_empty.mp hb) hr
  refine weak_split hFo hZ (c₁ := r) (c₂ := r + 1) (n := n)
    (fun i l hi hl _ => hw i l (by omega)) ?_ ⟨by omega, har'⟩ ⟨hbn, by omega⟩ ha hb
  intro z hz
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcov hz)
  rcases lt_trichotomy i r with h | rfl | h
  · exact Or.inl (mem_iUnion₂.mpr ⟨i, ⟨hi, h⟩, hzi⟩)
  · exact absurd hr (nonempty_iff_ne_empty.mp ⟨z, hzi, hz⟩)
  · exact Or.inr (mem_iUnion₂.mpr ⟨i, ⟨hi, by omega⟩, hzi⟩)

omit [CompactSpace S] in
/-- Hereditary unicoherence passes to subsets. -/
theorem IsHereditarilyUnicoherent.mono {T U : Set S} (h : IsHereditarilyUnicoherent T)
    (hUT : U ⊆ T) : IsHereditarilyUnicoherent U := fun K hKU hK hnt =>
  h K (hKU.trans hUT) hK hnt

section FitCases

variable {A B : Set S} {ε : ℝ} {m n j k t : ℕ} {E F : ℕ → Set S}

omit [CompactSpace S] in
theorem Fit.lt_m (hf : Fit A B ε m n j k t E F) {x : S} {i : ℕ} (hx : x ∈ E i) : i < m := by
  by_contra h; rw [hf.endE i (by omega)] at hx; exact hx

omit [CompactSpace S] in
theorem Fit.lt_n (hf : Fit A B ε m n j k t E F) {x : S} {i : ℕ} (hx : x ∈ F i) : i < n := by
  by_contra h; rw [hf.endF i (by omega)] at hx; exact hx

omit [CompactSpace S] in
theorem Fit.weakE (hf : Fit A B ε m n j k t E F) (i l : ℕ) (h : i + 2 ≤ l) :
    Disjoint (E i) (E l) := (hf.tautE i l h).mono subset_closure subset_closure

omit [CompactSpace S] in
theorem Fit.weakF (hf : Fit A B ε m n j k t E F) (i l : ℕ) (h : i + 2 ≤ l) :
    Disjoint (F i) (F l) := (hf.tautF i l h).mono subset_closure subset_closure

/-- The conclusion shape of the three cases: a weak `ε`-chain covering `A ∪ B`. -/
def WeakCover (X : Set S) (ε : ℝ) : Prop :=
  ∃ (N : ℕ) (L : ℕ → Set S), (∀ i, IsOpen (L i)) ∧
    (∀ i, Bornology.IsBounded (L i) ∧ diam (L i) < ε) ∧
    (∀ i l, i + 2 ≤ l → l < N → Disjoint (L i) (L l)) ∧ X ⊆ ⋃ i, ⋃ (_ : i < N), L i

omit [CompactSpace S] in
/-- `k = 0`: `B ⊆ F*(k..n−1) ⊆ E*`, and `E` itself covers `A ∪ B`. -/
theorem Fit.weakCover_k0 (hf : Fit A B ε m n j k t E F) (hk : k = 0) : WeakCover (A ∪ B) ε := by
  refine ⟨m, E, hf.openE, hf.smallE, fun i l h _ => hf.weakE i l h, ?_⟩
  rintro x (hxA | hxB)
  · obtain ⟨i, hi⟩ := mem_iUnion.mp (hf.covA hxA)
    exact mem_iUnion₂.mpr ⟨i, hf.lt_m hi, hi⟩
  · obtain ⟨l, hl⟩ := mem_iUnion.mp (hf.covB hxB)
    obtain ⟨i', -, hi'm, hsub⟩ := hf.refine l (by omega) (hf.lt_n hl)
    exact mem_iUnion₂.mpr ⟨i', hi'm, hsub (subset_closure hl)⟩

omit [CompactSpace S] in
/-- **Case i** (`Cl F_{k−1}` meets no link of `E` but the last): `E ⊕ F(k−1..0)`. -/
theorem Fit.weakCover_case_i (hf : Fit A B ε m n j k t E F) (hk : 1 ≤ k)
    (hci : ∀ i, i < m - 1 → Disjoint (closure (F (k - 1))) (E i)) : WeakCover (A ∪ B) ε := by
  classical
  have hm := hf.jm
  set L : ℕ → Set S := fun p => if p < m then E p else F (m + k - 1 - p) with hL
  have hLE : ∀ p, p < m → L p = E p := fun p hp => by simp only [hL, if_pos hp]
  have hLF : ∀ p, m ≤ p → L p = F (m + k - 1 - p) := fun p hp => by
    simp only [hL, if_neg (show ¬ p < m by omega)]
  refine ⟨m + k, L, fun p => ?_, fun p => ?_, fun p q hpq hqN => ?_, ?_⟩
  · simp only [hL]; split_ifs
    · exact hf.openE p
    · exact hf.openF _
  · simp only [hL]; split_ifs
    · exact hf.smallE p
    · exact hf.smallF _
  · by_cases hq : q < m
    · rw [hLE p (by omega), hLE q hq]; exact hf.weakE p q hpq
    by_cases hp : m ≤ p
    · rw [hLF p hp, hLF q (by omega)]; exact (hf.weakF _ _ (by omega)).symm
    · rw [hLE p (by omega), hLF q (by omega)]
      by_cases hqm : q = m
      · subst hqm
        rw [show q + k - 1 - q = k - 1 by omega]
        exact ((hci p (by omega)).mono_left subset_closure).symm
      · exact ((hf.five _ p (by omega)).mono_left subset_closure).symm
  · rintro x (hxA | hxB)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hf.covA hxA)
      have := hf.lt_m hi
      exact mem_iUnion₂.mpr ⟨i, by omega, by rw [hLE i this]; exact hi⟩
    · obtain ⟨l, hl⟩ := mem_iUnion.mp (hf.covB hxB)
      by_cases hkl : k ≤ l
      · obtain ⟨i', -, hi'm, hsub⟩ := hf.refine l hkl (hf.lt_n hl)
        exact mem_iUnion₂.mpr ⟨i', by omega, by rw [hLE i' hi'm]; exact hsub (subset_closure hl)⟩
      · refine mem_iUnion₂.mpr ⟨m + k - 1 - l, by omega, ?_⟩
        rw [hLF _ (by omega), show m + k - 1 - (m + k - 1 - l) = l by omega]
        exact hl

/-- **Case ii** (`Cl F_{k−1}` misses the last link of `E`): Fugate's chain
`𝒢 = E(0..j−1) ⊕ E(j..m−2) ∩ S ⊕ E'_{m−1} ⊕ F(r−1..k) ∩ T ⊕ (F_{k−1} ∩ T) ∪ (F_{k−1} − Cl E*) ⊕
F(k−2..0)`, with `r` the least index `≥ k` such that `Cl F_r ⊄ E*(j..m−2)`,
`E'_{m−1} = E_{m−1} − Cl F*(k..r−2)`, `D = (A ∪ B) ∩ (Cl E*(j..m−2) − E'_{m−1})`, and `S`, `T`
separating the two closed parts of `D` given by Claim 3 and Moore's theorem. Hereditary
unicoherence and atriodicity of `A ∪ B` enter only in Claim 3. -/
theorem Fit.weakCover_case_ii (hf : Fit A B ε m n j k t E F) (hA : Fold.Q78.IsContinuum A)
    (hB : Fold.Q78.IsContinuum B) (hhu : IsHereditarilyUnicoherent (A ∪ B))
    (hat : IsAtriodic (A ∪ B)) (hk : 1 ≤ k)
    (hFm : Disjoint (closure (F (k - 1))) (E (m - 1))) : WeakCover (A ∪ B) ε := by
  classical
  have hjm := hf.jm
  set U₁ : Set S := ⋃ l, ⋃ (_ : j ≤ l ∧ l < m - 1), E l with hU₁
  obtain ⟨c, hcC, hcm, hco⟩ := hf.exE_last
  have hcU₁ : c ∉ U₁ := fun h => by
    obtain ⟨l, hl, hcl⟩ := mem_iUnion₂.mp h
    exact hco l hl.2 hcl
  -- the index `r`
  have hex : ∃ r, k ≤ r ∧ r < n ∧ ¬ closure (F r) ⊆ U₁ := by
    obtain ⟨l, hcl⟩ := mem_iUnion.mp (hf.covB hcC.2)
    have hkl : k ≤ l := by
      by_contra h
      exact (eq_empty_iff_forall_notMem.mp hf.exF_cl) c
        ⟨hcC, subset_closure (mem_iUnion₂.mpr ⟨l, by omega, hcl⟩)⟩
    exact ⟨l, hkl, hf.lt_n hcl, fun h => hcU₁ (h (subset_closure hcl))⟩
  set r := Nat.find hex with hr_def
  obtain ⟨hkr, hrn, hrU⟩ := Nat.find_spec hex
  have hbefore : ∀ i, k ≤ i → i < r → closure (F i) ⊆ U₁ := fun i hki hir => by
    by_contra h
    exact Nat.find_min hex hir ⟨hki, by omega, h⟩
  have hFrE : closure (F r) ⊆ E (m - 1) := by
    obtain ⟨i', hji', hi'm, hsub⟩ := hf.refine r hkr hrn
    by_cases h : i' < m - 1
    · exact absurd (hsub.trans (subset_iUnion₂_of_subset i' ⟨hji', h⟩ subset_rfl)) hrU
    · rwa [show i' = m - 1 by omega] at hsub
  -- the modified last link `E'`
  set K₂ : Set S := ⋃ l, ⋃ (_ : k ≤ l ∧ l + 2 ≤ r), closure (F l) with hK₂
  have hK₂c : IsClosed K₂ := by
    have : K₂ = ⋃ l ∈ {l | k ≤ l ∧ l + 2 ≤ r}, closure (F l) := rfl
    rw [this]
    exact ((Set.finite_Iio r).subset (fun l hl => by
      simp only [mem_setOf_eq] at hl; simp only [mem_Iio]; omega)).isClosed_biUnion
      fun l _ => isClosed_closure
  have hK₂U : K₂ ⊆ U₁ := iUnion₂_subset fun l hl => hbefore l hl.1 (by omega)
  set E' := E (m - 1) \ K₂ with hE'
  have hE'o : IsOpen E' := (hf.openE _).sdiff hK₂c
  have hcE' : c ∈ E' := ⟨hcm, fun h => hcU₁ (hK₂U h)⟩
  have hFrE' : F r ⊆ E' := fun x hx => ⟨hFrE (subset_closure hx), fun h => by
    obtain ⟨l, hl, hxl⟩ := mem_iUnion₂.mp h
    exact Set.disjoint_left.mp (hf.tautF l r (by omega)) hxl (subset_closure hx)⟩
  -- `D`, and its two closed parts
  set V : Set S := ⋃ l, ⋃ (_ : k - 1 ≤ l ∧ l ≤ r - 1), F l with hV
  have hVo : IsOpen V := isOpen_iUnion fun l => isOpen_iUnion fun _ => hf.openF l
  set D := (A ∪ B) ∩ (closure U₁ \ E') with hD
  have hDc : IsClosed D :=
    (hA.1.isClosed.union hB.1.isClosed).inter (isClosed_closure.sdiff hE'o)
  set P := D ∩ closure (F (k - 1)) with hP
  set Q := D \ V with hQ
  have hEclF : ∀ l, l + 2 ≤ k → ∀ x ∈ closure U₁, x ∉ F l := fun l hl x hx hxF => by
    obtain ⟨y, hyF, hyU⟩ := _root_.mem_closure_iff.mp hx (F l) (hf.openF l) hxF
    obtain ⟨i, -, hyE⟩ := mem_iUnion₂.mp hyU
    exact Set.disjoint_left.mp (hf.five l i hl) (subset_closure hyF) hyE
  -- **Claim 3**: no connected subset of `D` meets both `P` and `Q`
  have claim3 : ∀ Z ⊆ D, IsPreconnected Z → (Z ∩ P).Nonempty → (Z ∩ Q).Nonempty → False := by
    rintro Z hZD hZ ⟨p, hpZ, hpP⟩ ⟨q, hqZ, hqQ⟩
    set M := closure Z with hM
    have hMD : M ⊆ D := closure_minimal hZD hDc
    have hMc : Fold.Q78.IsContinuum M :=
      ⟨isClosed_closure.isCompact, ⟨p, subset_closure hpZ⟩, hZ.closure⟩
    have hMAB : M ⊆ A ∪ B := hMD.trans inter_subset_left
    have hpM : p ∈ M := subset_closure hpZ
    have hqM : q ∈ M := subset_closure hqZ
    have hpA : p ∉ A := fun h => Set.disjoint_left.mp (hf.sixA hk) hpP.2 h
    have hpB : p ∈ B := (hMAB hpM).resolve_left hpA
    have hcM : c ∉ M := fun h => (hMD h).2.2 hcE'
    -- `M ⊆ B`, else Sorgenfrey's triod
    have hMB : M ⊆ B := by
      intro a haM
      by_contra haB
      have haA : a ∈ A := (hMAB haM).resolve_right haB
      have hMA := isContinuum_inter_of_hu hhu hMc hA hMAB subset_union_left ⟨a, haM, haA⟩
      have hMB' := isContinuum_inter_of_hu hhu hMc hB hMAB subset_union_right ⟨p, hpM, hpB⟩
      have hCc := isContinuum_inter_of_hu hhu hA hB subset_union_left subset_union_right ⟨c, hcC⟩
      obtain ⟨z, hzM, hzA, hzB⟩ := inter_nonempty_of_cover hMc.2.isPreconnected hA.1.isClosed
        hB.1.isClosed hMAB ⟨a, haM, haA⟩ ⟨p, hpM, hpB⟩
      have hsub : M ∩ A ∪ M ∩ B ∪ A ∩ B ⊆ A ∪ B :=
        union_subset (union_subset (inter_subset_right.trans subset_union_left)
          (inter_subset_right.trans subset_union_right)) (inter_subset_left.trans subset_union_left)
      have hT := isTriod_union_of_three hMA hMB' hCc ⟨z, ⟨hzM, hzA⟩, hzM, hzB⟩
        ⟨z, ⟨hzM, hzB⟩, hzA, hzB⟩ ⟨z, ⟨hzM, hzA⟩, hzA, hzB⟩
        (fun h => by
          rcases h ⟨haM, haA⟩ with h' | h'
          · exact haB h'.2
          · exact haB h'.2)
        (fun h => by
          rcases h ⟨hpM, hpB⟩ with h' | h'
          · exact hpA h'.2
          · exact hpA h'.1)
        (fun h => by
          rcases h hcC with h' | h'
          · exact hcM h'.1
          · exact hcM h'.1)
        (hhu.mono hsub)
      exact hat _ hsub hT
    have hMF : M ⊆ ⋃ i, ⋃ (_ : i < n), F i := fun x hx => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hf.covB (hMB hx))
      exact mem_iUnion₂.mpr ⟨i, hf.lt_n hi, hi⟩
    have hMlow : ∀ x ∈ M, ∀ l, l + 2 ≤ k → x ∉ F l := fun x hx l hl =>
      hEclF l hl x (hMD hx).2.1
    -- the link of `F` through `p`
    obtain ⟨lp, hpl⟩ := mem_iUnion.mp (hf.covB hpB)
    have hlp1 : k - 1 ≤ lp := by
      by_contra h
      exact hMlow p hpM lp (by omega) hpl
    have hlp2 : lp ≤ k := by
      by_contra h
      exact Set.disjoint_left.mp (hf.tautF (k - 1) lp (by omega)) hpP.2 (subset_closure hpl)
    -- the link of `F` through `q`
    obtain ⟨lq, hql⟩ := mem_iUnion.mp (hf.covB (hMB hqM))
    have hlq : r ≤ lq := by
      by_contra h
      have h1 : k - 1 ≤ lq := by
        by_contra h'
        exact hMlow q hqM lq (by omega) hql
      exact hqQ.2 (mem_iUnion₂.mpr ⟨lq, ⟨h1, by omega⟩, hql⟩)
    obtain ⟨y, hyF, hyM⟩ := meets_between_of_weak hf.openF hf.weakF hMc.2.isPreconnected hMF
      (a := lp) (b := lq) (r := r) (by omega) hlq (hf.lt_n hql) ⟨p, hpl, hpM⟩ ⟨q, hql, hqM⟩
    exact (hMD hyM).2.2 (hFrE' hyF)
  -- Moore's theorem and normality
  obtain ⟨H₀, L₀, hH₀, hL₀, hHL, hHLd, hPH, hQL⟩ := exists_closed_split_of_no_connected
    hDc.isCompact (hDc.inter isClosed_closure) (hDc.sdiff hVo) inter_subset_left diff_subset claim3
  obtain ⟨δ, hδ, hδd⟩ := hHLd.exists_thickenings hH₀.isCompact hL₀
  set T₂ := thickening (δ / 2) H₀ with hT₂
  set S₂ := thickening (δ / 2) L₀ with hS₂
  have hclsub : ∀ X : Set S, closure (thickening (δ / 2) X) ⊆ thickening δ X := fun X =>
    (closure_thickening_subset_cthickening _ _).trans
      (cthickening_subset_thickening' hδ (half_lt_self hδ) X)
  have hST2 : Disjoint S₂ T₂ :=
    (hδd.mono ((subset_closure).trans (hclsub H₀)) ((subset_closure).trans (hclsub L₀))).symm
  have hDST : D ⊆ S₂ ∪ T₂ := fun x hx => by
    rw [← hHL] at hx
    rcases hx with h | h
    · exact Or.inr (self_subset_thickening (half_pos hδ) _ h)
    · exact Or.inl (self_subset_thickening (half_pos hδ) _ h)
  have hQS : Q ⊆ S₂ := hQL.trans (self_subset_thickening (half_pos hδ) _)
  have hPT : P ⊆ T₂ := hPH.trans (self_subset_thickening (half_pos hδ) _)
  have hS₂o : IsOpen S₂ := isOpen_thickening
  have hT₂o : IsOpen T₂ := isOpen_thickening
  -- the chain `𝒢`
  set Eall : Set S := ⋃ i, ⋃ (_ : i < m), E i with hEall
  set L : ℕ → Set S := fun p => if p < j then E p else if p < m - 1 then E p ∩ S₂ else
    if p = m - 1 then E' else if k ≤ m + r - 1 - p then F (m + r - 1 - p) ∩ T₂ else
    if m + r - 1 - p = k - 1 then (F (k - 1) ∩ T₂) ∪ (F (k - 1) \ closure Eall) else
    F (m + r - 1 - p) with hL
  have hL1 : ∀ p, p < j → L p = E p := fun p hp => by simp only [hL, if_pos hp]
  have hL2 : ∀ p, j ≤ p → p < m - 1 → L p = E p ∩ S₂ := fun p hp hp' => by
    simp only [hL, if_neg (show ¬ p < j by omega), if_pos hp']
  have hL3 : L (m - 1) = E' := by
    simp only [hL, if_neg (show ¬ m - 1 < j by omega), if_neg (lt_irrefl (m - 1)), ↓reduceIte]
  have hL4 : ∀ p, m ≤ p → k ≤ m + r - 1 - p → L p = F (m + r - 1 - p) ∩ T₂ := fun p hp h => by
    simp only [hL, if_neg (show ¬ p < j by omega), if_neg (show ¬ p < m - 1 by omega),
      if_neg (show ¬ p = m - 1 by omega), if_pos h]
  have hL5 : ∀ p, m ≤ p → m + r - 1 - p = k - 1 →
      L p = (F (k - 1) ∩ T₂) ∪ (F (k - 1) \ closure Eall) := fun p hp h => by
    simp only [hL, if_neg (show ¬ p < j by omega), if_neg (show ¬ p < m - 1 by omega),
      if_neg (show ¬ p = m - 1 by omega), if_neg (show ¬ k ≤ m + r - 1 - p by omega), if_pos h]
  have hL6 : ∀ p, m ≤ p → m + r - 1 - p + 2 ≤ k → L p = F (m + r - 1 - p) := fun p hp h => by
    simp only [hL, if_neg (show ¬ p < j by omega), if_neg (show ¬ p < m - 1 by omega),
      if_neg (show ¬ p = m - 1 by omega), if_neg (show ¬ k ≤ m + r - 1 - p by omega),
      if_neg (show ¬ m + r - 1 - p = k - 1 by omega)]
  have hLE : ∀ p, p < m → L p ⊆ E p := fun p hp => by
    by_cases h1 : p < j
    · rw [hL1 p h1]
    by_cases h2 : p < m - 1
    · rw [hL2 p (by omega) h2]; exact inter_subset_left
    · rw [show p = m - 1 by omega, hL3]; exact diff_subset
  have hLF : ∀ p, m ≤ p → L p ⊆ F (m + r - 1 - p) := fun p hp => by
    by_cases h1 : k ≤ m + r - 1 - p
    · rw [hL4 p hp h1]; exact inter_subset_left
    by_cases h2 : m + r - 1 - p = k - 1
    · rw [hL5 p hp h2, ← h2]; exact union_subset inter_subset_left diff_subset
    · rw [hL6 p hp (by omega)]
  refine ⟨m + r, L, fun p => ?_, fun p => ?_, fun p q hpq hqN => ?_, ?_⟩
  · -- open
    simp only [hL]
    split_ifs
    · exact hf.openE p
    · exact (hf.openE p).inter hS₂o
    · exact hE'o
    · exact (hf.openF _).inter hT₂o
    · exact ((hf.openF _).inter hT₂o).union ((hf.openF _).sdiff isClosed_closure)
    · exact hf.openF _
  · -- small
    by_cases hp : p < m
    · have := hf.smallE p
      exact ⟨this.1.subset (hLE p hp), (diam_mono (hLE p hp) this.1).trans_lt this.2⟩
    · have := hf.smallF (m + r - 1 - p)
      exact ⟨this.1.subset (hLF p (by omega)),
        (diam_mono (hLF p (by omega)) this.1).trans_lt this.2⟩
  · -- nonadjacent members are disjoint
    by_cases hq : q < m
    · exact (hf.weakE p q hpq).mono (hLE p (by omega)) (hLE q hq)
    by_cases hp : m ≤ p
    · exact (hf.weakF _ _ (by omega)).symm.mono (hLF p hp) (hLF q (by omega))
    set u := m + r - 1 - q with hu
    have hLq := hLF q (by omega)
    by_cases hpj : p < j
    · rw [hL1 p hpj]
      exact ((hf.four p u hpj).mono subset_closure hLq)
    by_cases hpm : p < m - 1
    · rw [hL2 p (by omega) hpm]
      by_cases h1 : k ≤ u
      · rw [hL4 q (by omega) h1]
        exact hST2.mono inter_subset_right inter_subset_right
      by_cases h2 : u = k - 1
      · rw [hL5 q (by omega) h2]
        refine disjoint_union_right.mpr ⟨hST2.mono inter_subset_right inter_subset_right, ?_⟩
        refine Set.disjoint_left.mpr fun x hx hx' => hx'.2 (subset_closure ?_)
        exact mem_iUnion₂.mpr ⟨p, by omega, hx.1⟩
      · rw [hL6 q (by omega) (by omega)]
        exact (hf.five u p (by omega)).symm.mono inter_subset_left subset_closure
    · rw [show p = m - 1 by omega, hL3]
      by_cases h1 : k ≤ u
      · rw [hL4 q (by omega) h1]
        refine Set.disjoint_left.mpr fun x hx hx' => hx.2 ?_
        exact mem_iUnion₂.mpr ⟨u, ⟨h1, by omega⟩, subset_closure hx'.1⟩
      by_cases h2 : u = k - 1
      · refine (hFm.symm.mono diff_subset subset_closure).mono_right ?_
        rw [← h2]; exact hLq
      · rw [hL6 q (by omega) (by omega)]
        exact (hf.five u (m - 1) (by omega)).symm.mono diff_subset subset_closure
  · -- covering
    have hpos : ∀ l, l ≤ r - 1 → m + r - 1 - (m + r - 1 - l) = l := fun l hl => by omega
    have hcovE : ∀ x ∈ A ∪ B, ∀ i, x ∈ E i → x ∈ ⋃ p, ⋃ (_ : p < m + r), L p := by
      intro x hx i hxi
      have him := hf.lt_m hxi
      by_cases hij : i < j
      · exact mem_iUnion₂.mpr ⟨i, by omega, by rw [hL1 i hij]; exact hxi⟩
      by_cases hxE' : x ∈ E'
      · exact mem_iUnion₂.mpr ⟨m - 1, by omega, by rw [hL3]; exact hxE'⟩
      have hxU : x ∈ U₁ := by
        by_cases him1 : i < m - 1
        · exact mem_iUnion₂.mpr ⟨i, ⟨by omega, him1⟩, hxi⟩
        · rw [show i = m - 1 by omega] at hxi
          by_contra hxU
          exact hxE' ⟨hxi, fun h => hxU (hK₂U h)⟩
      have hxD : x ∈ D := ⟨hx, subset_closure hxU, hxE'⟩
      rcases hDST hxD with hS | hT
      · obtain ⟨l, hl, hxl⟩ := mem_iUnion₂.mp hxU
        exact mem_iUnion₂.mpr ⟨l, by omega, by rw [hL2 l hl.1 hl.2]; exact ⟨hxl, hS⟩⟩
      · have hxV : x ∈ V := by
          by_contra h
          exact Set.disjoint_left.mp hST2 (hQS ⟨hxD, h⟩) hT
        obtain ⟨l, hl, hxl⟩ := mem_iUnion₂.mp hxV
        refine mem_iUnion₂.mpr ⟨m + r - 1 - l, by omega, ?_⟩
        by_cases hkl : k ≤ l
        · rw [hL4 _ (by omega) (by rw [hpos l hl.2]; exact hkl), hpos l hl.2]
          exact ⟨hxl, hT⟩
        · rw [hL5 _ (by omega) (by rw [hpos l hl.2]; omega)]
          rw [show l = k - 1 by omega] at hxl
          exact Or.inl ⟨hxl, hT⟩
    rintro x (hxA | hxB)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hf.covA hxA)
      exact hcovE x (Or.inl hxA) i hi
    obtain ⟨l, hl⟩ := mem_iUnion.mp (hf.covB hxB)
    by_cases hkl : k ≤ l
    · obtain ⟨i', -, -, hsub⟩ := hf.refine l hkl (hf.lt_n hl)
      exact hcovE x (Or.inr hxB) i' (hsub (subset_closure hl))
    by_cases hl2 : l + 2 ≤ k
    · refine mem_iUnion₂.mpr ⟨m + r - 1 - l, by omega, ?_⟩
      rw [hL6 _ (by omega) (by rw [hpos l (by omega)]; exact hl2), hpos l (by omega)]
      exact hl
    have hlk : l = k - 1 := by omega
    rw [hlk] at hl
    refine mem_iUnion₂.mpr ⟨m + r - 1 - (k - 1), by omega, ?_⟩
    rw [hL5 _ (by omega) (by omega)]
    by_cases hxcl : x ∈ closure Eall
    · left
      refine ⟨hl, hPT ⟨⟨Or.inr hxB, ?_, fun h => ?_⟩, subset_closure hl⟩⟩
      · obtain ⟨i, him, hxi⟩ := mem_closure_biUnion_lt hxcl
        by_cases hij : i < j
        · exact absurd hl (Set.disjoint_left.mp (hf.four i (k - 1) hij) hxi)
        by_cases him1 : i < m - 1
        · exact closure_mono (subset_iUnion₂_of_subset i ⟨by omega, him1⟩ subset_rfl) hxi
        · rw [show i = m - 1 by omega] at hxi
          obtain ⟨y, hyF, hyE⟩ := _root_.mem_closure_iff.mp hxi (F (k - 1)) (hf.openF _) hl
          exact absurd hyE (Set.disjoint_left.mp hFm (subset_closure hyF))
      · exact Set.disjoint_left.mp hFm (subset_closure hl) h.1
    · exact Or.inr ⟨hl, hxcl⟩

end FitCases

/-- **Fugate, Theorem 1, sufficiency, with `A ∪ B` hereditarily unicoherent.** From Claim 1
(batch 100), Lemma 4 (`fugate_lemma4_weak`) and the three cases `k = 0`, Case i, Case ii. -/
theorem fugate_theorem1_sufficiency_hu {A B : Set S} (hA : IsSnakeLike A) (hB : IsSnakeLike B)
    (hAB : (A ∩ B).Nonempty) (hat : IsAtriodic (A ∪ B))
    (hhu : IsHereditarilyUnicoherent (A ∪ B)) : IsSnakeLike (A ∪ B) := by
  by_cases hBA : B ⊆ A
  · rwa [union_eq_left.mpr hBA]
  by_cases hAB' : A ⊆ B
  · rwa [union_eq_right.mpr hAB']
  have hU : Fold.Q78.IsContinuum (A ∪ B) := isContinuum_union hA.1 hB.1 hAB
  have hu : IsUnicoherent (A ∪ B) := by
    obtain ⟨a, haA, haB⟩ := not_subset.mp hAB'
    obtain ⟨b, hbB, -⟩ := not_subset.mp hBA
    exact hhu _ subset_rfl hU ⟨a, Or.inl haA, b, Or.inr hbB, fun h => haB (h ▸ hbB)⟩
  have hTA : IsTerminalSub A (A ∩ B) := inter_isTerminalSub_of_union hA.1
    (isHereditarilyUnicoherent_of_isSnakeLike hA) hB.1 hAB hat hu hBA
  have hTB : IsTerminalSub B (A ∩ B) := by
    have := inter_isTerminalSub_of_union hB.1 (isHereditarilyUnicoherent_of_isSnakeLike hB) hA.1
      (by rwa [inter_comm]) (by rwa [union_comm]) (by rwa [union_comm]) hAB'
    rwa [inter_comm] at this
  refine isSnakeLike_of_weak hU fun ε hε => ?_
  obtain ⟨m, n, j, k, t, E, F, hf⟩ := fugate_lemma4_weak hA hB hTA hTB hε
  by_cases hk : k = 0
  · exact hf.weakCover_k0 hk
  by_cases hci : ∀ i, i < m - 1 → Disjoint (closure (F (k - 1))) (E i)
  · exact hf.weakCover_case_i (by omega) hci
  push_neg at hci
  obtain ⟨i, hi, hni⟩ := hci
  have hit : i = t := by
    by_contra h
    exact hni (hf.sixt (by omega) i h)
  exact hf.weakCover_case_ii hA.1 hB.1 hhu hat (by omega) (hf.sixt (by omega) (m - 1) (by omega))

/-- **Fugate, Theorem 1, sufficiency** (Fugate's hypotheses): `A ∪ B` atriodic and unicoherent.
Hereditary unicoherence of `A ∪ B` follows (`isHereditarilyUnicoherent_union`: `A`, `B` are
hereditarily unicoherent and `A ∩ B` is connected by unicoherence). -/
theorem fugate_theorem1_sufficiency_of_unicoherent {A B : Set S} (hA : IsSnakeLike A)
    (hB : IsSnakeLike B) (hAB : (A ∩ B).Nonempty) (hat : IsAtriodic (A ∪ B))
    (hu : IsUnicoherent (A ∪ B)) : IsSnakeLike (A ∪ B) :=
  fugate_theorem1_sufficiency_hu hA hB hAB hat (isHereditarilyUnicoherent_union hA.1 hB.1
    (isHereditarilyUnicoherent_of_isSnakeLike hA) (isHereditarilyUnicoherent_of_isSnakeLike hB)
    (hu A B hA.1 hB.1 rfl))

end HPC.Plane
