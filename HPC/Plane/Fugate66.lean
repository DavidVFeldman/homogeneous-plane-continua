import HPC.Plane.LastLink99

/-!
# Batch 100: Fugate 1966 — terminal subcontinua, Lemma 1 in general, Lemma 3, Theorem 1 (gluing),
# Corollaries 1–2

Source: J. B. Fugate, *Decomposable chainable continua*, Trans. Amer. Math. Soc. 123 (1966),
460–468. Definitions 3–5, Lemmas 1–4, Theorem 1, Corollaries 1–2 (COMMISSION-batch100.md §1
transcribes them). `IsAtriodic`, `IsUnicoherent`, `IsHereditarilyUnicoherent`, `IsTriod` are
batch 92's (Bing's definitions, over a compact metric space `S`).

Status of the items and the shape changes are recorded in `REPORT-batch100.md`.
-/

namespace HPC.Plane

open Set Topology Metric

variable {S : Type*} [MetricSpace S]

/-! ## Definitions -/

/-- **Fugate, Definition 4.** `A` is a *terminal subcontinuum* of `M`: for subcontinua `K`, `L` of
`M` both meeting `A`, `K ⊆ A ∪ L` or `L ⊆ K ∪ A`. (Degenerate `A = {p}`: Bing's condition B.) -/
def IsTerminalSub (M A : Set S) : Prop :=
  Fold.Q78.IsContinuum A ∧ A ⊆ M ∧
    ∀ K L : Set S, Fold.Q78.IsContinuum K → Fold.Q78.IsContinuum L → K ⊆ M → L ⊆ M →
      (K ∩ A).Nonempty → (L ∩ A).Nonempty → K ⊆ A ∪ L ∨ L ⊆ K ∪ A

theorem isContinuum_singleton' (p : S) : Fold.Q78.IsContinuum ({p} : Set S) :=
  ⟨isCompact_singleton, isConnected_singleton⟩

/-- **Definition 4 at a point is condition B.** Shape change: the skeleton's hypothesis that `M`
is a continuum is not used and has been removed. -/
theorem isTerminalSub_singleton_iff (M : Set S) (p : S) :
    IsTerminalSub M {p} ↔ CondB M p := by
  constructor
  · rintro ⟨-, hpM, hT⟩
    refine ⟨singleton_subset_iff.mp hpM, fun H K hHM hKM hH hK hpH hpK => ?_⟩
    rcases hT H K hH hK hHM hKM ⟨p, hpH, rfl⟩ ⟨p, hpK, rfl⟩ with h | h
    · exact Or.inl fun x hx => (h hx).elim (fun e => (mem_singleton_iff.mp e) ▸ hpK) id
    · exact Or.inr fun x hx => (h hx).elim id (fun e => (mem_singleton_iff.mp e) ▸ hpH)
  · rintro ⟨hpM, hB⟩
    refine ⟨isContinuum_singleton' p, singleton_subset_iff.mpr hpM,
      fun K L hK hL hKM hLM hKA hLA => ?_⟩
    obtain ⟨_, hpK, rfl⟩ := hKA
    obtain ⟨_, hpL, hpL'⟩ := hLA
    rw [mem_singleton_iff] at hpL'
    subst hpL'
    rcases hB K L hKM hLM hK hL hpK hpL with h | h
    · exact Or.inl (h.trans subset_union_right)
    · exact Or.inr (h.trans subset_union_left)

/-! ## Triods -/

/-- **Fugate, Definition 1** (a triod, Sorgenfrey's form), as transcribed in the skeleton: the
common part `A ∩ B ∩ D` is *not* required to be connected. -/
def IsFugateTriod (X : Set S) : Prop :=
  Fold.Q78.IsContinuum X ∧ ∃ A B D : Set S, Fold.Q78.IsContinuum A ∧ Fold.Q78.IsContinuum B ∧
    Fold.Q78.IsContinuum D ∧ A ≠ X ∧ B ≠ X ∧ D ≠ X ∧ X = A ∪ B ∪ D ∧
    A ∩ B = A ∩ B ∩ D ∧ B ∩ D = A ∩ B ∩ D ∧ A ∩ D = A ∩ B ∩ D ∧
    A ∩ B ∩ D ≠ A ∧ A ∩ B ∩ D ≠ B ∧ A ∩ B ∩ D ≠ D

/-- **Sorgenfrey's triod** (Sorgenfrey 1944, the definition Fugate cites): `IsFugateTriod` with the
common part `A ∩ B ∩ D` a continuum. -/
def IsSorgenfreyTriod (X : Set S) : Prop :=
  Fold.Q78.IsContinuum X ∧ ∃ A B D : Set S, Fold.Q78.IsContinuum A ∧ Fold.Q78.IsContinuum B ∧
    Fold.Q78.IsContinuum D ∧ A ≠ X ∧ B ≠ X ∧ D ≠ X ∧ X = A ∪ B ∪ D ∧
    A ∩ B = A ∩ B ∩ D ∧ B ∩ D = A ∩ B ∩ D ∧ A ∩ D = A ∩ B ∩ D ∧
    A ∩ B ∩ D ≠ A ∧ A ∩ B ∩ D ≠ B ∧ A ∩ B ∩ D ≠ D ∧ Fold.Q78.IsContinuum (A ∩ B ∩ D)

theorem IsSorgenfreyTriod.isFugateTriod {X : Set S} (h : IsSorgenfreyTriod X) :
    IsFugateTriod X := by
  obtain ⟨hX, A, B, D, hA, hB, hD, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := h
  exact ⟨hX, A, B, D, hA, hB, hD, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- **A piece of the complement of a subcontinuum, with the subcontinuum, is connected** (a
special case of boundary bumping). `M` connected and closed, `N ⊆ M` connected, nonempty and
closed, `M ∖ N = A ∪ R` with `A`, `R` separated: then `N ∪ A` is preconnected. -/
theorem isPreconnected_union_piece {M N A R : Set S} (hM : IsPreconnected M) (hMc : IsClosed M)
    (hN : IsPreconnected N) (hNc : IsClosed N) (hNne : N.Nonempty) (hNM : N ⊆ M) (hcov : M \ N = A ∪ R)
    (hAR : Disjoint (closure A) R) (hRA : Disjoint A (closure R)) : IsPreconnected (N ∪ A) := by
  have hAM : A ⊆ M := fun x hx => (hcov.symm ▸ (Or.inl hx : x ∈ A ∪ R) : x ∈ M \ N).1
  have hMsplit : ∀ x ∈ M, x ∈ N ∨ x ∈ A ∨ x ∈ R := fun x hx => by
    by_cases hxN : x ∈ N
    · exact Or.inl hxN
    · have : x ∈ A ∪ R := hcov ▸ ⟨hx, hxN⟩
      exact Or.inr this
  -- the key step, for one orientation
  have key : ∀ u v : Set S, IsClosed u → IsClosed v → N ∪ A ⊆ u ∪ v → (N ∪ A) ∩ (u ∩ v) = ∅ →
      N ⊆ u → N ∪ A ⊆ u := by
    intro u v hu hv hcuv hdisj hNu
    have hNv : ∀ x ∈ N, x ∉ v := fun x hx hxv => by
      have : x ∈ (N ∪ A) ∩ (u ∩ v) := ⟨Or.inl hx, hNu hx, hxv⟩
      rw [hdisj] at this; exact this
    have hclA : closure A ⊆ N ∪ A := fun x hx => by
      have hxM : x ∈ M := closure_minimal hAM hMc hx
      rcases hMsplit x hxM with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (Set.disjoint_left.mp hAR hx)
    have hNAc : IsClosed (N ∪ A) := by
      have : N ∪ A = N ∪ closure A :=
        Subset.antisymm (union_subset_union_right _ subset_closure)
          (union_subset subset_union_left hclA)
      rw [this]; exact hNc.union isClosed_closure
    have hAv : ∀ x ∈ A, x ∉ v := by
      rcases isPreconnected_iff_subset_of_disjoint_closed.mp hM ((N ∪ A) ∩ v)
        (((N ∪ A) ∩ u) ∪ closure R) (hNAc.inter hv) ((hNAc.inter hu).union isClosed_closure)
        (fun x hx => by
          rcases hMsplit x hx with h | h | h
          · exact Or.inr (Or.inl ⟨Or.inl h, hNu h⟩)
          · rcases hcuv (Or.inr h : x ∈ N ∪ A) with h' | h'
            · exact Or.inr (Or.inl ⟨Or.inr h, h'⟩)
            · exact Or.inl ⟨Or.inr h, h'⟩
          · exact Or.inr (Or.inr (subset_closure h)))
        (by
          rw [eq_empty_iff_forall_notMem]
          rintro x ⟨-, ⟨hxNA, hxv⟩, hx2⟩
          rcases hx2 with ⟨-, hxu⟩ | hxR
          · have : x ∈ (N ∪ A) ∩ (u ∩ v) := ⟨hxNA, hxu, hxv⟩
            rw [hdisj] at this; exact this
          · rcases hxNA with hxN | hxA
            · exact hNv x hxN hxv
            · exact Set.disjoint_left.mp hRA hxA hxR) with h | h
      · obtain ⟨y, hy⟩ := hNne
        exact absurd (h (hNM hy)).2 (hNv y hy)
      · intro x hxA hxv
        rcases h (hAM hxA) with ⟨-, hxu⟩ | hxR
        · have : x ∈ (N ∪ A) ∩ (u ∩ v) := ⟨Or.inr hxA, hxu, hxv⟩
          rw [hdisj] at this; exact this
        · exact Set.disjoint_left.mp hRA hxA hxR
    intro x hx
    rcases hx with hxN | hxA
    · exact hNu hxN
    · exact (hcuv (Or.inr hxA)).resolve_right (hAv x hxA)
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hcuv hdisj
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hN u v hu hv
    (subset_union_left.trans hcuv) (by
      rw [eq_empty_iff_forall_notMem]; intro x hx
      have : x ∈ (N ∪ A) ∩ (u ∩ v) := ⟨Or.inl hx.1, hx.2⟩
      rw [hdisj] at this; exact this) with h | h
  · exact Or.inl (key u v hu hv hcuv hdisj h)
  · exact Or.inr (key v u hv hu (by rwa [union_comm v u]) (by rwa [inter_comm v u]) h)

/-- **Bing's triod is Sorgenfrey's triod.** From `X ∖ N = A ∪ B ∪ C` (mutually separated) the three
continua are `N ∪ A`, `N ∪ B`, `N ∪ C`, with common part `N`. -/
theorem isSorgenfreyTriod_of_isTriod {X : Set S} (h : IsTriod X) : IsSorgenfreyTriod X := by
  obtain ⟨hX, N, hN, hNX, A, B, C, hA, hB, hC, hcov, h1, h2, h3, h4, h5, h6⟩ := h
  have mem : ∀ x, x ∈ A ∪ B ∪ C → x ∈ X ∧ x ∉ N := fun x hx => by
    have : x ∈ X \ N := hcov ▸ hx; exact this
  have hAX : ∀ x ∈ A, x ∈ X ∧ x ∉ N := fun x hx => mem x (Or.inl (Or.inl hx))
  have hBX : ∀ x ∈ B, x ∈ X ∧ x ∉ N := fun x hx => mem x (Or.inl (Or.inr hx))
  have hCX : ∀ x ∈ C, x ∈ X ∧ x ∉ N := fun x hx => mem x (Or.inr hx)
  have dAB : ∀ x ∈ A, x ∉ B := fun x hx hx' => Set.disjoint_left.mp h1 (subset_closure hx) hx'
  have dAC : ∀ x ∈ A, x ∉ C := fun x hx hx' => Set.disjoint_left.mp h3 (subset_closure hx) hx'
  have dBC : ∀ x ∈ B, x ∉ C := fun x hx hx' => Set.disjoint_left.mp h5 (subset_closure hx) hx'
  have piece : ∀ P R : Set S, X \ N = P ∪ R → Disjoint (closure P) R → Disjoint P (closure R) →
      Fold.Q78.IsContinuum (N ∪ P) := fun P R hPR hd1 hd2 => by
    have hc := isPreconnected_union_piece hX.2.isPreconnected hX.1.isClosed hN.2.isPreconnected
      hN.1.isClosed hN.2.nonempty hNX hPR hd1 hd2
    have hPX : P ⊆ X := fun x hx => (hPR.symm ▸ (Or.inl hx : x ∈ P ∪ R) : x ∈ X \ N).1
    have hcl : IsClosed (N ∪ P) := by
      have : N ∪ P = N ∪ closure P := by
        refine Subset.antisymm (union_subset_union_right _ subset_closure)
          (union_subset subset_union_left fun x hx => ?_)
        have hxX : x ∈ X := closure_minimal hPX hX.1.isClosed hx
        by_cases hxN : x ∈ N
        · exact Or.inl hxN
        · have : x ∈ P ∪ R := hPR ▸ ⟨hxX, hxN⟩
          rcases this with h | h
          · exact Or.inr h
          · exact absurd h (Set.disjoint_left.mp hd1 hx)
      rw [this]; exact hN.1.isClosed.union isClosed_closure
    exact ⟨hX.1.of_isClosed_subset hcl (union_subset hNX hPX),
      ⟨hN.2.nonempty.mono subset_union_left, hc⟩⟩
  have cA := piece A (B ∪ C) (by rw [hcov, union_assoc])
    (by rw [Set.disjoint_union_right]; exact ⟨h1, h3⟩)
    (by rw [closure_union, Set.disjoint_union_right]; exact ⟨h2, h4⟩)
  have cB := piece B (A ∪ C) (by rw [hcov]; ext x; simp only [mem_union]; tauto)
    (by rw [Set.disjoint_union_right]; exact ⟨h2.symm, h5⟩)
    (by rw [closure_union, Set.disjoint_union_right]; exact ⟨h1.symm, h6⟩)
  have cC := piece C (A ∪ B) (by rw [hcov]; ext x; simp only [mem_union]; tauto)
    (by rw [Set.disjoint_union_right]; exact ⟨h4.symm, h6.symm⟩)
    (by rw [closure_union, Set.disjoint_union_right]; exact ⟨h3.symm, h5.symm⟩)
  have hNeq : (N ∪ A) ∩ (N ∪ B) ∩ (N ∪ C) = N := by
    ext x
    simp only [mem_inter_iff, mem_union]
    constructor
    · rintro ⟨⟨h1 | h1, h2 | h2⟩, h3 | h3⟩ <;> first | assumption | exact absurd h2 (dAB x h1)
    · intro hx; exact ⟨⟨Or.inl hx, Or.inl hx⟩, Or.inl hx⟩
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  obtain ⟨c, hc⟩ := hC
  refine ⟨hX, N ∪ A, N ∪ B, N ∪ C, cA, cB, cC, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    have : b ∈ N ∪ A := e ▸ (hBX b hb).1
    rcases this with h | h
    · exact (hBX b hb).2 h
    · exact dAB b h hb
  · intro e
    have : a ∈ N ∪ B := e ▸ (hAX a ha).1
    rcases this with h | h
    · exact (hAX a ha).2 h
    · exact dAB a ha h
  · intro e
    have : a ∈ N ∪ C := e ▸ (hAX a ha).1
    rcases this with h | h
    · exact (hAX a ha).2 h
    · exact dAC a ha h
  · ext x
    simp only [mem_union]
    constructor
    · intro hx
      by_cases hxN : x ∈ N
      · exact Or.inl (Or.inl (Or.inl hxN))
      · have : x ∈ A ∪ B ∪ C := hcov ▸ ⟨hx, hxN⟩
        rcases this with (h | h) | h
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr h)
    · rintro (((h | h) | h | h) | h | h)
      all_goals first
        | exact hNX h
        | exact (hAX _ h).1
        | exact (hBX _ h).1
        | exact (hCX _ h).1
  · rw [hNeq]; ext x; simp only [mem_inter_iff, mem_union]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩ <;> first | assumption | exact absurd h2 (dAB x h1)
    · intro hx; exact ⟨Or.inl hx, Or.inl hx⟩
  · rw [hNeq]; ext x; simp only [mem_inter_iff, mem_union]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩ <;> first | assumption | exact absurd h2 (dBC x h1)
    · intro hx; exact ⟨Or.inl hx, Or.inl hx⟩
  · rw [hNeq]; ext x; simp only [mem_inter_iff, mem_union]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩ <;> first | assumption | exact absurd h2 (dAC x h1)
    · intro hx; exact ⟨Or.inl hx, Or.inl hx⟩
  · rw [hNeq]; intro e
    exact (hAX a ha).2 (e ▸ (Or.inr ha : a ∈ N ∪ A))
  · rw [hNeq]; intro e
    exact (hBX b hb).2 (e ▸ (Or.inr hb : b ∈ N ∪ B))
  · rw [hNeq]; intro e
    exact (hCX c hc).2 (e ▸ (Or.inr hc : c ∈ N ∪ C))
  · rw [hNeq]; exact hN

/-- **Sorgenfrey's triod is Bing's triod**: `N = A ∩ B ∩ D`, pieces `A ∖ N`, `B ∖ N`, `D ∖ N`. -/
theorem isTriod_of_isSorgenfreyTriod {X : Set S} (h : IsSorgenfreyTriod X) : IsTriod X := by
  obtain ⟨hX, A, B, D, hA, hB, hD, -, -, -, hcov, e1, e2, e3, n1, n2, n3, hN⟩ := h
  set N := A ∩ B ∩ D with hN_def
  have ne : ∀ P : Set S, N ⊆ P → N ≠ P → (P \ N).Nonempty := fun P hsub hne => by
    by_contra h
    rw [not_nonempty_iff_eq_empty, diff_eq_empty] at h
    exact hne (Subset.antisymm hsub h)
  have sep : ∀ P Q : Set S, IsClosed P → P ∩ Q = N → Disjoint (closure (P \ N)) (Q \ N) := by
    intro P Q hP hPQ
    refine Set.disjoint_left.mpr fun x hx hx' => hx'.2 ?_
    have : x ∈ P ∩ Q := ⟨closure_minimal diff_subset hP hx, hx'.1⟩
    rwa [hPQ] at this
  have iBA : B ∩ A = N := by rw [inter_comm]; exact e1
  have iDB : D ∩ B = N := by rw [inter_comm]; exact e2
  have iDA : D ∩ A = N := by rw [inter_comm]; exact e3
  refine ⟨hX, N, hN, ?_, A \ N, B \ N, D \ N, ne A (fun x hx => hx.1.1) n1,
    ne B (fun x hx => hx.1.2) n2, ne D (fun x hx => hx.2) n3, ?_,
    sep A B hA.1.isClosed e1, (sep B A hB.1.isClosed iBA).symm,
    sep A D hA.1.isClosed e3, (sep D A hD.1.isClosed iDA).symm,
    sep B D hB.1.isClosed e2, (sep D B hD.1.isClosed iDB).symm⟩
  · rw [hcov]; exact fun x hx => Or.inl (Or.inl hx.1.1)
  · rw [hcov]; ext x; simp only [mem_diff, mem_union]; tauto

/-- **Bing's and Sorgenfrey's triods coincide.** -/
theorem isSorgenfreyTriod_iff_isTriod {X : Set S} : IsSorgenfreyTriod X ↔ IsTriod X :=
  ⟨isTriod_of_isSorgenfreyTriod, isSorgenfreyTriod_of_isTriod⟩

/-- **Bing's triod ⇒ the skeleton's Fugate triod** (the direction of `isFugateTriod_iff_isTriod`
that holds). -/
theorem isFugateTriod_of_isTriod {X : Set S} (h : IsTriod X) : IsFugateTriod X :=
  (isSorgenfreyTriod_of_isTriod h).isFugateTriod

/-- In a hereditarily unicoherent continuum two intersecting subcontinua meet in a continuum. -/
theorem isContinuum_inter_of_hu {T H K : Set S} (hT : IsHereditarilyUnicoherent T)
    (hH : Fold.Q78.IsContinuum H) (hK : Fold.Q78.IsContinuum K) (hHT : H ⊆ T) (hKT : K ⊆ T)
    (hne : (H ∩ K).Nonempty) : Fold.Q78.IsContinuum (H ∩ K) := by
  refine ⟨hH.1.inter_right hK.1.isClosed, ?_⟩
  by_cases hnt : (H ∪ K).Nontrivial
  · exact hT (H ∪ K) (union_subset hHT hKT) (isContinuum_union hH hK hne) hnt H K hH hK rfl
  · rw [Set.not_nontrivial_iff] at hnt
    exact ⟨hne, (hnt.anti (inter_subset_left.trans subset_union_left)).isPreconnected⟩

/-- **The skeleton's Fugate triod ⇒ Bing's triod, for hereditarily unicoherent `X`**: there the
common part `A ∩ B ∩ D = A ∩ B` is a continuum. (Without hereditary unicoherence this direction
fails: the θ-curve, REPORT-batch100.md.) -/
theorem isTriod_of_isFugateTriod_of_hu {X : Set S} (h : IsFugateTriod X)
    (hu : IsHereditarilyUnicoherent X) : IsTriod X := by
  obtain ⟨hX, A, B, D, hA, hB, hD, n1, n2, n3, hcov, e1, e2, e3, m1, m2, m3⟩ := h
  have hAX : A ⊆ X := hcov ▸ (subset_union_left.trans subset_union_left)
  have hBX : B ⊆ X := hcov ▸ (subset_union_right.trans subset_union_left)
  -- the common part is nonempty: else `X = A ⊔ (B ∪ D)`
  have hne : (A ∩ B).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hAD : A ∩ D = ∅ := by rw [e3, ← e1, hemp]
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hX.2.isPreconnected A (B ∪ D)
      hA.1.isClosed (hB.1.isClosed.union hD.1.isClosed) (by rw [hcov, union_assoc])
      (by rw [inter_union_distrib_left, hemp, hAD, union_empty, inter_empty]) with h | h
    · exact n1 (Subset.antisymm hAX h)
    · obtain ⟨a, ha⟩ := hA.2.nonempty
      rcases h (hAX ha) with hb | hd
      · have : a ∈ A ∩ B := ⟨ha, hb⟩; rw [hemp] at this; exact this
      · have : a ∈ A ∩ D := ⟨ha, hd⟩; rw [hAD] at this; exact this
  have hc := isContinuum_inter_of_hu hu hA hB hAX hBX hne
  exact isTriod_of_isSorgenfreyTriod ⟨hX, A, B, D, hA, hB, hD, n1, n2, n3, hcov, e1, e2, e3, m1,
    m2, m3, e1 ▸ hc⟩

-- Commented-out statement `isFugateTriod_iff_isTriod` removed in batch 103; see `LEDGER.md`.

-- Commented-out statement `isTriod_union_of_three` removed in batch 103; see `LEDGER.md`.

/-- **The triod from three continua with a connected core.** Three pairwise intersecting
continua, none contained in the union of the other two, whose pairwise intersections have a
continuum as union: their union is a triod (core `N`, pieces `A ∖ (B ∪ D)`, …). -/
theorem isTriod_union_of_three_of_core {A B D : Set S} (hA : Fold.Q78.IsContinuum A)
    (hB : Fold.Q78.IsContinuum B) (hD : Fold.Q78.IsContinuum D)
    (hAB : (A ∩ B).Nonempty) (hBD : (B ∩ D).Nonempty)
    (nA : ¬ A ⊆ B ∪ D) (nB : ¬ B ⊆ A ∪ D) (nD : ¬ D ⊆ A ∪ B)
    (hH₀ : Fold.Q78.IsContinuum ((A ∩ B) ∪ (B ∩ D) ∪ (D ∩ A))) : IsTriod (A ∪ B ∪ D) := by
  set T := A ∪ B ∪ D with hT_def
  set H₀ := (A ∩ B) ∪ (B ∩ D) ∪ (D ∩ A) with hH₀_def
  have hT : Fold.Q78.IsContinuum T :=
    isContinuum_union (isContinuum_union hA hB hAB) hD
      (hBD.mono (inter_subset_inter_left _ subset_union_right))
  simp only [not_subset, mem_union, not_or] at nA nB nD
  obtain ⟨a, ha, haB, haD⟩ := nA
  obtain ⟨b, hb, hbA, hbD⟩ := nB
  obtain ⟨c, hc, hcA, hcB⟩ := nD
  have cl1 : closure (A \ (B ∪ D)) ⊆ A := closure_minimal diff_subset hA.1.isClosed
  have cl2 : closure (B \ (A ∪ D)) ⊆ B := closure_minimal diff_subset hB.1.isClosed
  have cl3 : closure (D \ (A ∪ B)) ⊆ D := closure_minimal diff_subset hD.1.isClosed
  refine ⟨hT, H₀, hH₀, ?_, A \ (B ∪ D), B \ (A ∪ D), D \ (A ∪ B), ⟨a, ha, by simp [haB, haD]⟩,
    ⟨b, hb, by simp [hbA, hbD]⟩, ⟨c, hc, by simp [hcA, hcB]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    simp only [hH₀_def, hT_def, mem_union, mem_inter_iff] at hy ⊢
    tauto
  · ext y
    simp only [hH₀_def, hT_def, mem_diff, mem_union, mem_inter_iff]
    tauto
  · exact Set.disjoint_left.mpr fun y hy hy' => hy'.2 (Or.inl (cl1 hy))
  · exact Set.disjoint_left.mpr fun y hy hy' => hy.2 (Or.inl (cl2 hy'))
  · exact Set.disjoint_left.mpr fun y hy hy' => hy'.2 (Or.inl (cl1 hy))
  · exact Set.disjoint_left.mpr fun y hy hy' => hy.2 (Or.inr (cl3 hy'))
  · exact Set.disjoint_left.mpr fun y hy hy' => hy'.2 (Or.inr (cl2 hy))
  · exact Set.disjoint_left.mpr fun y hy hy' => hy.2 (Or.inr (cl3 hy'))

/-- **Sorgenfrey's lemma** (Fugate's "[8, p. 440]"), corrected form: three continua, pairwise
intersecting, none contained in the union of the other two, whose union is **hereditarily
unicoherent** — their union is a triod. (Batch 92's property 3, with `BingS` replaced by the
hereditary unicoherence of the union.) -/
theorem isTriod_union_of_three {A B D : Set S} (hA : Fold.Q78.IsContinuum A)
    (hB : Fold.Q78.IsContinuum B) (hD : Fold.Q78.IsContinuum D)
    (hAB : (A ∩ B).Nonempty) (hBD : (B ∩ D).Nonempty) (hAD : (A ∩ D).Nonempty)
    (nA : ¬ A ⊆ B ∪ D) (nB : ¬ B ⊆ A ∪ D) (nD : ¬ D ⊆ A ∪ B)
    (hu : IsHereditarilyUnicoherent (A ∪ B ∪ D)) : IsTriod (A ∪ B ∪ D) := by
  set T := A ∪ B ∪ D with hT_def
  have hAT : A ⊆ T := subset_union_left.trans subset_union_left
  have hBT : B ⊆ T := subset_union_right.trans subset_union_left
  have hDT : D ⊆ T := subset_union_right
  have hT : Fold.Q78.IsContinuum T :=
    isContinuum_union (isContinuum_union hA hB hAB) hD
      (hBD.mono (inter_subset_inter_left _ subset_union_right))
  simp only [not_subset, mem_union, not_or] at nA nB nD
  obtain ⟨a, ha, haB, haD⟩ := nA
  obtain ⟨b, hb, hbA, hbD⟩ := nB
  obtain ⟨c, hc, hcA, hcB⟩ := nD
  have hnt : T.Nontrivial := ⟨a, hAT ha, b, hBT hb, fun e => hbA (e ▸ ha)⟩
  have hcommon : (A ∩ B ∩ D).Nonempty := by
    have hu' := hu T subset_rfl hT hnt (A ∪ B) D (isContinuum_union hA hB hAB) hD rfl
    rw [union_inter_distrib_right] at hu'
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hd : (A ∩ D) ∩ (B ∩ D) = ∅ := by
      rw [← hne]; ext x; simp only [mem_inter_iff]; tauto
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hu'.2 (A ∩ D) (B ∩ D)
      (hA.1.isClosed.inter hD.1.isClosed) (hB.1.isClosed.inter hD.1.isClosed) subset_rfl
      (by rw [hd, inter_empty]) with h | h
    · obtain ⟨x, hx⟩ := hBD
      have hx' : x ∈ (A ∩ D) ∩ (B ∩ D) := ⟨h (Or.inr hx), hx⟩
      rw [hd] at hx'; exact hx'
    · obtain ⟨x, hx⟩ := hAD
      have hx' : x ∈ (A ∩ D) ∩ (B ∩ D) := ⟨hx, h (Or.inl hx)⟩
      rw [hd] at hx'; exact hx'
  obtain ⟨x, ⟨hxA, hxB⟩, hxD⟩ := hcommon
  set H₀ := (A ∩ B) ∪ (B ∩ D) ∪ (D ∩ A) with hH₀_def
  have hH₀ : Fold.Q78.IsContinuum H₀ := by
    have c12 := isContinuum_inter_of_hu hu hA hB hAT hBT hAB
    have c23 := isContinuum_inter_of_hu hu hB hD hBT hDT hBD
    have c31 := isContinuum_inter_of_hu hu hD hA hDT hAT ⟨x, hxD, hxA⟩
    exact isContinuum_union (isContinuum_union c12 c23 ⟨x, ⟨hxA, hxB⟩, ⟨hxB, hxD⟩⟩) c31
      ⟨x, Or.inl ⟨hxA, hxB⟩, ⟨hxD, hxA⟩⟩
  exact isTriod_union_of_three_of_core hA hB hD hAB hBD (by simpa only [not_subset, mem_union,
    not_or] using ⟨a, ha, haB, haD⟩) (by simpa only [not_subset, mem_union, not_or] using
    ⟨b, hb, hbA, hbD⟩) (by simpa only [not_subset, mem_union, not_or] using ⟨c, hc, hcA, hcB⟩) hH₀

/-! ## Lemma 3 -/

theorem _root_.HPC.IsIrreducibleBetween.symm {W : Set S} {p q : S}
    (h : IsIrreducibleBetween W p q) :
    IsIrreducibleBetween W q p :=
  ⟨h.1, h.2.2.1, h.2.1, fun K hK hKW hq hp => h.2.2.2 K hK hKW hp hq⟩

/-- **Fugate, Lemma 3, (⇐)**, which needs no hypothesis on `M`: if for every subcontinuum `B` of
`M` meeting `A` the continuum `A ∪ B` is irreducible between a point of `A` and some point, then
`A` is terminal. -/
theorem isTerminalSub_of_irreducible {M A : Set S} (hA : Fold.Q78.IsContinuum A) (hAM : A ⊆ M)
    (h : ∀ B : Set S, Fold.Q78.IsContinuum B → B ⊆ M → (B ∩ A).Nonempty →
      ∃ p q : S, p ∈ A ∧ IsIrreducibleBetween (A ∪ B) p q) : IsTerminalSub M A := by
  refine ⟨hA, hAM, fun K L hK hL hKM hLM hKA hLA => ?_⟩
  by_contra hno
  rw [not_or] at hno
  obtain ⟨h1, h2⟩ := hno
  have hAK : Fold.Q78.IsContinuum (A ∪ K) := isContinuum_union hA hK (by rwa [inter_comm])
  have hAL : Fold.Q78.IsContinuum (A ∪ L) := isContinuum_union hA hL (by rwa [inter_comm])
  have hB : Fold.Q78.IsContinuum (A ∪ K ∪ L) :=
    isContinuum_union hAK hL (by obtain ⟨y, hyL, hyA⟩ := hLA; exact ⟨y, Or.inl hyA, hyL⟩)
  obtain ⟨p, q, hpA, hirr⟩ := h (A ∪ K ∪ L) hB (union_subset (union_subset hAM hKM) hLM)
    (by obtain ⟨y, hyA⟩ := hA.2.nonempty; exact ⟨y, Or.inl (Or.inl hyA), hyA⟩)
  have heq : A ∪ (A ∪ K ∪ L) = A ∪ K ∪ L := by
    rw [← union_assoc, ← union_assoc, union_self]
  rw [heq] at hirr
  rcases hirr.2.2.1 with (hq | hq) | hq
  · exact h2 (by
      have := hirr.2.2.2 (A ∪ K) hAK subset_union_left (Or.inl hpA) (Or.inl hq)
      intro y hy
      have : y ∈ A ∪ K := this ▸ (Or.inr hy : y ∈ A ∪ K ∪ L)
      rcases this with h | h
      · exact Or.inr h
      · exact Or.inl h)
  · exact h2 (by
      have := hirr.2.2.2 (A ∪ K) hAK subset_union_left (Or.inl hpA) (Or.inr hq)
      intro y hy
      have : y ∈ A ∪ K := this ▸ (Or.inr hy : y ∈ A ∪ K ∪ L)
      rcases this with h | h
      · exact Or.inr h
      · exact Or.inl h)
  · exact h1 (by
      have := hirr.2.2.2 (A ∪ L) hAL
        (union_subset (subset_union_left.trans subset_union_left) subset_union_right)
        (Or.inl hpA) (Or.inr hq)
      intro y hy
      exact this ▸ (Or.inl (Or.inr hy) : y ∈ A ∪ K ∪ L))

/-- **Fugate, Lemma 3, (⇒)**, conditional on Sorgenfrey's theorem for the subcontinua of `M`
(hypothesis `hirr`, which `exists_irreducibleBetween_of_atriodic` supplies when `M` is atriodic
and hereditarily unicoherent). -/
theorem irreducible_of_isTerminalSub {M A : Set S}
    (hirr : ∀ W ⊆ M, Fold.Q78.IsContinuum W → W.Nontrivial → ∃ p q : S, IsIrreducibleBetween W p q)
    (hT : IsTerminalSub M A) : ∀ B : Set S, Fold.Q78.IsContinuum B → B ⊆ M → (B ∩ A).Nonempty →
      ∃ p q : S, p ∈ A ∧ IsIrreducibleBetween (A ∪ B) p q := by
  obtain ⟨hA, hAM, hter⟩ := hT
  intro B hB hBM hBA
  set W := A ∪ B with hW
  have hWc : Fold.Q78.IsContinuum W := isContinuum_union hA hB (by rwa [inter_comm])
  have hWM : W ⊆ M := union_subset hAM hBM
  obtain ⟨r, hrA⟩ := hA.2.nonempty
  by_cases hnt : W.Nontrivial
  swap
  · rw [not_nontrivial_iff] at hnt
    refine ⟨r, r, hrA, hWc, Or.inl hrA, Or.inl hrA, fun K _ hKW hrK _ =>
      Subset.antisymm hKW fun y hy => (hnt hy (Or.inl hrA)) ▸ hrK⟩
  obtain ⟨p, q, hpq⟩ := hirr W hWM hWc hnt
  by_cases hpA : p ∈ A
  · exact ⟨p, q, hpA, hpq⟩
  by_cases hqA : q ∈ A
  · exact ⟨q, p, hqA, hpq.symm⟩
  by_cases hrp : IsIrreducibleBetween W r p
  · exact ⟨r, p, hrA, hrp⟩
  by_cases hrq : IsIrreducibleBetween W r q
  · exact ⟨r, q, hrA, hrq⟩
  have notirr : ∀ s, s ∈ W → ¬ IsIrreducibleBetween W r s →
      ∃ L, Fold.Q78.IsContinuum L ∧ L ⊆ W ∧ r ∈ L ∧ s ∈ L ∧ L ≠ W := fun s hs hn => by
    by_contra hno
    push_neg at hno
    exact hn ⟨hWc, Or.inl hrA, hs, fun K hK hKW hrK hsK => hno K hK hKW hrK hsK⟩
  obtain ⟨L, hL, hLW, hrL, hpL, hLne⟩ := notirr p hpq.2.1 hrp
  obtain ⟨Y, hY, hYW, hrY, hqY, hYne⟩ := notirr q hpq.2.2.1 hrq
  rcases hter L Y hL hY (hLW.trans hWM) (hYW.trans hWM) ⟨r, hrL, hrA⟩ ⟨r, hrY, hrA⟩ with h | h
  · have hpY : p ∈ Y := (h hpL).resolve_left hpA
    exact (hYne (hpq.2.2.2 Y hY hYW hpY hqY)).elim
  · have hqL : q ∈ L := (h hqY).resolve_right hqA
    exact (hLne (hpq.2.2.2 L hL hLW hpL hqL)).elim

variable [CompactSpace S]

-- `exists_irreducibleBetween_of_atriodic` and `isTerminalSub_iff_irreducible` (Fugate's Lemma 3):
-- proved in `HPC/Plane/Sorgenfrey.lean` (batch 103: the sorried versions were deleted here).

/-! ## Lemma 1 (general) and Lemma 2 -/

/-! **Fugate, Lemma 1** (`fugate_lemma1`) is proved in `HPC/Plane/Fugate66Lemma1.lean`, which
imports this file. -/

/-- `A` is *contained exactly* in the subchain `F(s..n−1)` (Fugate, Definition 5): `A` lies in its
union, in no proper subchain's union, and misses the closure of the other links. -/
def ContainedExactly {n : ℕ} (F : Chain S n) (A : Set S) (s : ℕ) : Prop :=
  s < n ∧ A ⊆ ⋃ (i : Fin n) (_ : s ≤ i.val), F.link i ∧
    (∀ s' : ℕ, s < s' → ¬ A ⊆ ⋃ (i : Fin n) (_ : s' ≤ i.val), F.link i) ∧
    (A ∩ closure (⋃ (i : Fin n) (_ : i.val < s), F.link i)) = ∅

/-! **Fugate, Lemma 2** (`fugate_lemma2`) is proved in `HPC/Plane/Fugate66Lemma1.lean`. -/

/-! ## Theorem 1 and its corollaries -/

/-- **Fugate, Theorem 1, necessity** (batch 96): a snake-like union is atriodic and unicoherent.
The hypotheses on `A`, `B` are not needed. -/
theorem fugate_theorem1_necessity {A B : Set S} (h : IsSnakeLike (A ∪ B)) :
    IsAtriodic (A ∪ B) ∧ IsUnicoherent (A ∪ B) :=
  ⟨isAtriodic_of_isSnakeLike h, isUnicoherent_of_isSnakeLike h⟩

omit [CompactSpace S] in
/-- **Fugate, Theorem 1, Claim 1**: if `A` is hereditarily unicoherent, `A ∪ B` is atriodic and
unicoherent and `B ⊄ A`, then `A ∩ B` is a terminal subcontinuum of `A`. (If `K`, `L ⊆ A` meeting
`A ∩ B` violated terminality, `K ∪ (A ∩ B)`, `L ∪ (A ∩ B)` and `B` would form a triod in `A ∪ B`;
their core is `(K ∪ (A ∩ B)) ∩ (L ∪ (A ∩ B))`, a continuum since `A` is hereditarily unicoherent.) -/
theorem inter_isTerminalSub_of_union {A B : Set S} (hA : Fold.Q78.IsContinuum A)
    (hAhu : IsHereditarilyUnicoherent A) (hB : Fold.Q78.IsContinuum B) (hAB : (A ∩ B).Nonempty)
    (hat : IsAtriodic (A ∪ B)) (hu : IsUnicoherent (A ∪ B)) (hBA : ¬ B ⊆ A) :
    IsTerminalSub A (A ∩ B) := by
  have hI : Fold.Q78.IsContinuum (A ∩ B) := ⟨hA.1.inter_right hB.1.isClosed, hu A B hA hB rfl⟩
  refine ⟨hI, inter_subset_left, fun K L hK hL hKA hLA hKI hLI => ?_⟩
  by_contra hno
  rw [not_or, not_subset, not_subset] at hno
  obtain ⟨⟨k, hkK, hk⟩, ⟨l, hlL, hl⟩⟩ := hno
  simp only [mem_union, not_or] at hk hl
  set K' := K ∪ (A ∩ B) with hK'_def
  set L' := L ∪ (A ∩ B) with hL'_def
  have hK' : Fold.Q78.IsContinuum K' := isContinuum_union hK hI hKI
  have hL' : Fold.Q78.IsContinuum L' := isContinuum_union hL hI hLI
  have hK'A : K' ⊆ A := union_subset hKA inter_subset_left
  have hL'A : L' ⊆ A := union_subset hLA inter_subset_left
  obtain ⟨x, hx⟩ := hAB
  have hcore : (K' ∩ L') ∪ (L' ∩ B) ∪ (B ∩ K') = K' ∩ L' := by
    refine Subset.antisymm (union_subset (union_subset subset_rfl ?_) ?_)
      (subset_union_left.trans subset_union_left)
    · rintro y ⟨hyL, hyB⟩
      exact ⟨Or.inr ⟨hL'A hyL, hyB⟩, Or.inr ⟨hL'A hyL, hyB⟩⟩
    · rintro y ⟨hyB, hyK⟩
      exact ⟨Or.inr ⟨hK'A hyK, hyB⟩, Or.inr ⟨hK'A hyK, hyB⟩⟩
  have hT := isTriod_union_of_three_of_core hK' hL' hB ⟨x, Or.inr hx, Or.inr hx⟩
    ⟨x, Or.inr hx, hx.2⟩
    (fun h => by
      rcases h (Or.inl hkK) with (h' | h') | h'
      · exact hk.2 h'
      · exact hk.1 h'
      · exact hk.1 ⟨hKA hkK, h'⟩)
    (fun h => by
      rcases h (Or.inl hlL) with (h' | h') | h'
      · exact hl.1 h'
      · exact hl.2 h'
      · exact hl.2 ⟨hLA hlL, h'⟩)
    (fun h => hBA (h.trans (union_subset hK'A hL'A)))
    (by rw [hcore]; exact isContinuum_inter_of_hu hAhu hK' hL' hK'A hL'A ⟨x, Or.inr hx, Or.inr hx⟩)
  exact hat _ (union_subset (union_subset (hK'A.trans subset_union_left)
    (hL'A.trans subset_union_left)) subset_union_right) hT

-- `fugate_theorem1_sufficiency` and `fugate_theorem1` (Fugate's Theorem 1): proved in
-- `HPC/Plane/Fugate66B.lean` (batch 103: the sorried versions were deleted here).

/-- **Corollary 1, necessity.** -/
theorem fugate_cor1_necessity {ι : Type*} (A : ι → Set S) (h : IsSnakeLike (⋃ i, A i)) :
    IsAtriodic (⋃ i, A i) ∧ IsUnicoherent (⋃ i, A i) :=
  ⟨isAtriodic_of_isSnakeLike h, isUnicoherent_of_isSnakeLike h⟩

-- `fugate_cor1` (Fugate's Corollary 1): proved in `HPC/Plane/Ingram68.lean` (batch 132).

/-- **The atriodicity step of Corollary 2.** A continuum all of whose proper subcontinua are
snake-like is atriodic. A proper triod would be snake-like; and if `M` itself were a triod
`A ∪ B ∪ D` (Sorgenfrey form, common part `N`), a subcontinuum `K` with `N ⊊ K ⊊ D` (boundary
bumping from a point of `N` towards a point of `D ∖ N`) gives the proper triod `A ∪ B ∪ K`. -/
theorem isAtriodic_of_proper_snakeLike {M : Set S}
    (hsub : ∀ K ⊆ M, Fold.Q78.IsContinuum K → K ≠ M → IsSnakeLike K) : IsAtriodic M := by
  intro T hTM hT
  by_cases hTne : T ≠ M
  · exact isAtriodic_of_isSnakeLike (hsub T hTM hT.1 hTne) T subset_rfl hT
  push_neg at hTne
  subst hTne
  obtain ⟨hX, A, B, D, hA, hB, hD, -, -, -, hcov, e1, e2, e3, m1, m2, m3, hN⟩ :=
    isSorgenfreyTriod_of_isTriod hT
  set N := A ∩ B ∩ D with hN_def
  have hAX : A ⊆ T := hcov ▸ (subset_union_left.trans subset_union_left)
  have hBX : B ⊆ T := hcov ▸ (subset_union_right.trans subset_union_left)
  have hDX : D ⊆ T := hcov ▸ subset_union_right
  have pick : ∀ P : Set S, N ⊆ P → N ≠ P → ∃ x ∈ P, x ∉ N := fun P hsub hne => by
    by_contra h
    push_neg at h
    exact hne (Subset.antisymm hsub h)
  obtain ⟨x, hxD, hxN⟩ := pick D (fun y hy => hy.2) m3
  obtain ⟨a, haA, haN⟩ := pick A (fun y hy => hy.1.1) m1
  obtain ⟨b, hbB, hbN⟩ := pick B (fun y hy => hy.1.2) m2
  obtain ⟨p, hpN⟩ := hN.2.nonempty
  have hr : 0 < infDist x N :=
    (hN.1.isClosed.notMem_iff_infDist_pos ⟨p, hpN⟩).mp hxN
  set s := infDist x N / 2 with hs_def
  have hs : 0 < s := half_pos hr
  have hspx : s ≤ dist p x := by
    have := infDist_le_dist_of_mem (x := x) hpN
    rw [dist_comm] at this
    linarith
  obtain ⟨K₀, hK₀, hK₀D, hpK₀, z, hzK₀, hz⟩ :=
    exists_subcontinuum_meeting_closedBall hD hpN.2 hxD hs hspx
  have hzN : z ∉ N := fun h => by
    have h1 := infDist_le_dist_of_mem (x := x) h
    have h2 := mem_closedBall.mp hz
    rw [dist_comm] at h2
    linarith
  set K := N ∪ K₀ with hK_def
  have hKc : Fold.Q78.IsContinuum K := isContinuum_union hN hK₀ ⟨p, hpN, hpK₀⟩
  have hKD : K ⊆ D := union_subset (fun y hy => hy.2) (hK₀D.trans diff_subset)
  have hxK : x ∉ K := by
    rintro (h | h)
    · exact hxN h
    · exact (hK₀D h).2 (mem_ball_self hs)
  -- intersections with `D` lie in `N`
  have hAD : ∀ y, y ∈ A → y ∈ D → y ∈ N := fun y hy hy' => by
    have : y ∈ A ∩ D := ⟨hy, hy'⟩; rwa [e3] at this
  have hBD : ∀ y, y ∈ B → y ∈ D → y ∈ N := fun y hy hy' => by
    have : y ∈ B ∩ D := ⟨hy, hy'⟩; rwa [e2] at this
  have hAB : ∀ y, y ∈ A → y ∈ B → y ∈ N := fun y hy hy' => by
    have : y ∈ A ∩ B := ⟨hy, hy'⟩; rwa [e1] at this
  have hNK : N ⊆ K := subset_union_left
  have hcommon : A ∩ B ∩ K = N := by
    ext y; constructor
    · rintro ⟨⟨hyA, hyB⟩, -⟩; exact hAB y hyA hyB
    · intro hy; exact ⟨⟨hy.1.1, hy.1.2⟩, hNK hy⟩
  set T' := A ∪ B ∪ K with hT'_def
  have hT'c : Fold.Q78.IsContinuum T' :=
    isContinuum_union (isContinuum_union hA hB ⟨p, hpN.1.1, hpN.1.2⟩) hKc
      ⟨p, Or.inl hpN.1.1, hNK hpN⟩
  have hTT : IsTriod T' := isTriod_of_isSorgenfreyTriod ⟨hT'c, A, B, K, hA, hB, hKc,
    fun e => hbN (hAB b (e ▸ (Or.inl (Or.inr hbB) : b ∈ T')) hbB),
    fun e => haN (hAB a haA (e ▸ (Or.inl (Or.inl haA) : a ∈ T'))),
    fun e => haN (hAD a haA (hKD (e ▸ (Or.inl (Or.inl haA) : a ∈ T')))), rfl,
    by rw [hcommon]; ext y; exact ⟨fun h => hAB y h.1 h.2, fun h => ⟨h.1.1, h.1.2⟩⟩,
    by rw [hcommon]; ext y; exact ⟨fun h => hBD y h.1 (hKD h.2), fun h => ⟨h.1.2, hNK h⟩⟩,
    by rw [hcommon]; ext y; exact ⟨fun h => hAD y h.1 (hKD h.2), fun h => ⟨h.1.1, hNK h⟩⟩,
    by rw [hcommon]; exact fun e => haN (e ▸ haA),
    by rw [hcommon]; exact fun e => hbN (e ▸ hbB),
    by rw [hcommon]; exact fun e => hzN (e ▸ (Or.inr hzK₀ : z ∈ K)),
    by rw [hcommon]; exact hN⟩
  have hT'T : T' ⊆ T := union_subset (union_subset hAX hBX) (hKD.trans hDX)
  have hT'ne : T' ≠ T := fun e => by
    have : x ∈ T' := e ▸ hDX hxD
    rcases this with (h | h) | h
    · exact hxN (hAD x h hxD)
    · exact hxN (hBD x h hxD)
    · exact hxK h
  exact isAtriodic_of_isSnakeLike (hsub T' hT'T hT'c hT'ne) T' subset_rfl hTT

/-- **Corollary 2, from Theorem 1.** A decomposable unicoherent continuum all of whose proper
subcontinua are snake-like is snake-like, given the sufficiency half of Theorem 1 (hypothesis
`hT1`). -/
theorem fugate_cor2_of_theorem1
    (hT1 : ∀ A B : Set S, IsSnakeLike A → IsSnakeLike B → (A ∩ B).Nonempty →
      IsAtriodic (A ∪ B) → IsUnicoherent (A ∪ B) → IsSnakeLike (A ∪ B))
    {M : Set S} (hM : Fold.Q78.IsContinuum M) (hu : IsUnicoherent M)
    (hdec : ∃ A B : Set S, Fold.Q78.IsContinuum A ∧ Fold.Q78.IsContinuum B ∧ A ≠ M ∧ B ≠ M ∧
      A ∪ B = M)
    (hsub : ∀ K ⊆ M, Fold.Q78.IsContinuum K → K ≠ M → IsSnakeLike K) : IsSnakeLike M := by
  obtain ⟨A, B, hA, hB, hAM, hBM, hAB⟩ := hdec
  have hAsub : A ⊆ M := hAB ▸ subset_union_left
  have hBsub : B ⊆ M := hAB ▸ subset_union_right
  have hne : (A ∩ B).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hM.2.isPreconnected A B
      hA.1.isClosed hB.1.isClosed hAB.symm.subset (by rw [hemp, inter_empty]) with h | h
    · exact hAM (Subset.antisymm hAsub h)
    · exact hBM (Subset.antisymm hBsub h)
  have := hT1 A B (hsub A hAsub hA hAM) (hsub B hBsub hB hBM) hne
    (hAB ▸ isAtriodic_of_proper_snakeLike hsub) (hAB ▸ hu)
  rwa [hAB] at this

-- `fugate_cor2` (Fugate's Corollary 2): proved in `HPC/Plane/Fugate66B.lean` (batch 103: the sorried
-- version was deleted here).

/-! ## Tautness (Fugate §2, Barrett) -/

/-- A chain is *taut* when nonadjacent links are at positive distance. -/
noncomputable def IsTaut {n : ℕ} (F : Chain S n) : Prop :=
  ∀ i j : Fin n, 1 < (i.val : ℤ) - j.val ∨ 1 < (j.val : ℤ) - i.val →
    0 < infDist' (F.link i) (F.link j)
where infDist' (U V : Set S) : ℝ := ⨅ (x : U) (y : V), dist x.1 y.1

/-- Two nonempty sets with disjoint closures (in a compact metric space) are at positive
distance. -/
theorem infDist'_pos {U V : Set S} (hU : U.Nonempty) (hV : V.Nonempty)
    (hUV : Disjoint (closure U) (closure V)) : 0 < IsTaut.infDist' U V := by
  haveI : Nonempty U := hU.to_subtype
  haveI : Nonempty V := hV.to_subtype
  have hK : IsCompact (closure U ×ˢ closure V) :=
    isClosed_closure.isCompact.prod isClosed_closure.isCompact
  obtain ⟨x0, hx0⟩ := hU
  obtain ⟨y0, hy0⟩ := hV
  obtain ⟨q, hq, hmin⟩ := hK.exists_isMinOn ⟨(x0, y0), subset_closure hx0, subset_closure hy0⟩
    (continuous_dist.continuousOn)
  have hpos : 0 < dist q.1 q.2 :=
    dist_pos.mpr fun e => Set.disjoint_left.mp hUV hq.1 (e ▸ hq.2)
  refine lt_of_lt_of_le hpos (le_ciInf fun x => le_ciInf fun y => ?_)
  exact hmin (show ((x : S), (y : S)) ∈ closure U ×ˢ closure V from
    ⟨subset_closure x.2, subset_closure y.2⟩)

/-- **Barrett's Proposition 1** (as used by Fugate): a snake-like continuum has, for each `ε`, a
taut `ε`-chain covering it with every link meeting it. Proof: shrink the links of an `ε`-chain
whose links meet `M` to open sets with closures inside the links, and add small balls to keep
adjacent links meeting; nonadjacent closures are then disjoint compact sets. -/
theorem exists_taut_epsChain {M : Set S} (hM : IsSnakeLike M) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (F : Chain S n), IsEpsChain F ε ∧ M ⊆ F.union ∧ IsTaut F ∧
      ∀ i, (F.link i ∩ M).Nonempty := by
  classical
  obtain ⟨n, D, hDε, hMD, hmeet⟩ := exists_cover_meeting hM.1.2.isPreconnected hM.1.2.nonempty
    hM.2 hε
  -- shrink
  obtain ⟨V, hMV, hVo, hVD⟩ := exists_subset_iUnion_closure_subset hM.1.1.isClosed
    (u := D.link) D.isOpen (fun x _ => Set.toFinite _) hMD
  -- a small open set around a point, with closure inside an open set
  have small : ∀ (U : Set S), IsOpen U → ∀ x ∈ U, ∃ Q : Set S, IsOpen Q ∧ x ∈ Q ∧ closure Q ⊆ U :=
    fun U hU x hx => by
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
      exact ⟨ball x (r / 2), isOpen_ball, mem_ball_self (half_pos hr),
        closure_ball_subset_closedBall.trans ((closedBall_subset_ball (half_lt_self hr)).trans hrU)⟩
  -- the point balls `C i`
  have hC : ∀ i : Fin n, ∃ Q : Set S, IsOpen Q ∧ (Q ∩ M).Nonempty ∧ closure Q ⊆ D.link i :=
    fun i => by
      obtain ⟨x, hxD, hxM⟩ := hmeet i
      obtain ⟨Q, hQ, hxQ, hQD⟩ := small _ (D.isOpen i) x hxD
      exact ⟨Q, hQ, ⟨x, hxQ, hxM⟩, hQD⟩
  choose C hCo hCM hCD using hC
  -- the edge balls `B j`, for `j + 1 < n`
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
  have hWne : ∀ i, (W i ∩ M).Nonempty := fun i =>
    (hCM i).mono (inter_subset_inter_left _
      (subset_union_right.trans (subset_union_left.trans subset_union_left)))
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
        obtain ⟨x, hx, -⟩ := hWne i
        exact ⟨x, hx, hx⟩
      · obtain ⟨x, hx⟩ := (hBD i.val (by omega)).1
        refine ⟨x, Or.inl (Or.inr hx), Or.inr ?_⟩
        rw [show j.val - 1 = i.val by omega]; exact hx
      · obtain ⟨x, hx⟩ := (hBD j.val (by omega)).1
        refine ⟨x, Or.inr ?_, Or.inl (Or.inr hx)⟩
        rw [show i.val - 1 = j.val by omega]; exact hx
  refine ⟨n, ⟨W, hWo, hadj⟩, ?_, ?_, ?_, hWne⟩
  · exact isEpsChain_of_refines (fun i => ⟨i, subset_closure.trans (hWD i)⟩) hDε
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hMV hx)
    exact mem_iUnion.mpr ⟨i, Or.inl (Or.inl (Or.inl hi))⟩
  · intro i j hij
    refine infDist'_pos ((hWne i).mono inter_subset_left) ((hWne j).mono inter_subset_left) ?_
    refine Set.disjoint_left.mpr fun x hxi hxj => ?_
    have := (D.adjacent i j).mp ⟨x, hWD i hxi, hWD j hxj⟩
    omega

end HPC.Plane
