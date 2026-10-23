import Mathlib

/-!
# Batch 81: point-set topology for Theorem 13

Two independent tools, stated for subsets of a metric space.

* **Limits of finely chained sets are connected** (`HPC.T13.isPreconnected_limSup`). A set is
  `ε`-chained (`ChainedAt`) if it cannot be split between two sets at distance more than `ε`
  apart. The topological limit superior of sets `A k` (`k` in an infinite index set) that are
  `ε_k`-chained with `ε_k → 0` and all contain a common point is connected. This replaces the
  "limiting set is a continuum" step of Bing's proof (links of a chain need not be connected).
* **Indecomposable continua** (`HPC.T13.false_of_interior`): a proper subcontinuum of an
  indecomposable continuum has empty interior relative to it. The proof uses only a clopen form of
  boundary bumping (`HPC.T13.clopen_meets_closure_diff`), with no components.
-/

namespace HPC.T13

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

/-- `A` is `ε`-chained: whenever `A` is covered by two sets whose points are more than `ε`
apart, `A` lies in one of them. -/
def ChainedAt (A : Set X) (ε : ℝ) : Prop :=
  ∀ U V : Set X, A ⊆ U ∪ V → (∀ x ∈ U, ∀ y ∈ V, ε < dist x y) → A ⊆ U ∨ A ⊆ V

/-- The topological limit superior of the sets `A k`, `k ∈ I`. -/
def limSup (I : Set ℕ) (A : ℕ → Set X) : Set X :=
  ⋂ N : ℕ, closure (⋃ k ∈ I, ⋃ (_ : N ≤ k), A k)

theorem isClosed_limSup (I : Set ℕ) (A : ℕ → Set X) : IsClosed (limSup I A) :=
  isClosed_iInter fun _ => isClosed_closure

theorem mem_limSup {I : Set ℕ} {A : ℕ → Set X} (hI : I.Infinite) {R : X}
    (hR : ∀ k ∈ I, R ∈ A k) : R ∈ limSup I A := by
  simp only [limSup, mem_iInter]
  intro N
  obtain ⟨k, hk, hNk⟩ := hI.exists_gt N
  exact subset_closure (mem_iUnion₂.mpr ⟨k, hk, mem_iUnion.mpr ⟨hNk.le, hR k hk⟩⟩)

theorem limSup_subset_closure {I : Set ℕ} {A : ℕ → Set X} (N : ℕ) :
    limSup I A ⊆ closure (⋃ k ∈ I, ⋃ (_ : N ≤ k), A k) :=
  iInter_subset (fun N => closure (⋃ k ∈ I, ⋃ (_ : N ≤ k), A k)) N

/-- One half of the connectedness argument: if the common point lies in the closed set `u`,
the whole limit superior does. -/
theorem limSup_subset_of_mem [CompactSpace X] {I : Set ℕ} {A : ℕ → Set X} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hch : ∀ k ∈ I, ChainedAt (A k) (ε k)) {R : X}
    (hR : ∀ k ∈ I, R ∈ A k) {u v : Set X} (hu : IsClosed u) (hv : IsClosed v)
    (hsub : limSup I A ⊆ u ∪ v) (hdisj : Disjoint u v) (hRu : R ∈ u) : limSup I A ⊆ u := by
  obtain ⟨δ, hδ, hδd⟩ := hdisj.exists_thickenings hu.isCompact hv
  set U' := thickening (δ / 2) u
  set V' := thickening (δ / 2) v
  have hsep : ∀ x ∈ U', ∀ y ∈ V', δ / 2 ≤ dist x y := by
    intro x hx y hy
    by_contra hlt
    push_neg at hlt
    rw [mem_thickening_iff] at hx hy
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    have h1 : y ∈ thickening δ u :=
      mem_thickening_iff.mpr ⟨a, ha, by linarith [dist_triangle y x a, dist_comm x y]⟩
    have h2 : y ∈ thickening δ v := mem_thickening_iff.mpr ⟨b, hb, by linarith⟩
    exact (hδd.le_bot ⟨h1, h2⟩ : _)
  -- eventually the closures lie in `U' ∪ V'`
  set C : ℕ → Set X := fun N => closure (⋃ k ∈ I, ⋃ (_ : N ≤ k), A k) with hC
  have hCanti : ∀ N N', N ≤ N' → C N' ⊆ C N := by
    intro N N' h
    refine closure_mono ?_
    intro z hz
    simp only [mem_iUnion] at hz ⊢
    obtain ⟨k, hk, hk', hz⟩ := hz
    exact ⟨k, hk, le_trans h hk', hz⟩
  have hopen : IsOpen (U' ∪ V') := isOpen_thickening.union isOpen_thickening
  obtain ⟨N1, hN1⟩ : ∃ N, C N ⊆ U' ∪ V' := by
    refine exists_subset_nhds_of_isCompact' (V := C) ?_ (fun N => isClosed_closure.isCompact)
      (fun N => isClosed_closure) ?_
    · intro i j
      exact ⟨max i j, hCanti _ _ (le_max_left _ _), hCanti _ _ (le_max_right _ _)⟩
    · intro x hx
      refine hopen.mem_nhds ?_
      have : x ∈ limSup I A := hx
      rcases hsub this with h | h
      · exact Or.inl (self_subset_thickening (by linarith) _ h)
      · exact Or.inr (self_subset_thickening (by linarith) _ h)
  obtain ⟨N2, hN2⟩ : ∃ N, ∀ k, N ≤ k → ε k < δ / 2 := by
    have := (hε.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 2 by linarith)))
    exact eventually_atTop.mp this
  have hAk : ∀ k ∈ I, max N1 N2 ≤ k → A k ⊆ U' := by
    intro k hk hNk
    have hAC : A k ⊆ U' ∪ V' := by
      refine subset_trans ?_ hN1
      intro z hz
      exact subset_closure (mem_iUnion₂.mpr ⟨k, hk, mem_iUnion.mpr ⟨le_of_max_le_left hNk, hz⟩⟩)
    rcases hch k hk U' V' hAC (fun x hx y hy =>
        lt_of_lt_of_le (hN2 k (le_of_max_le_right hNk)) (hsep x hx y hy)) with h | h
    · exact h
    · exfalso
      have hRU : R ∈ U' := self_subset_thickening (by linarith) _ hRu
      have := hsep R hRU R (h (hR k hk))
      simp at this
      linarith
  have hCN : C (max N1 N2) ⊆ thickening δ u := by
    refine subset_trans (closure_mono ?_) (subset_trans (closure_thickening_subset_cthickening (δ / 2) u)
      (cthickening_subset_thickening' hδ (by linarith) u))
    intro z hz
    simp only [mem_iUnion] at hz
    obtain ⟨k, hk, hk', hz⟩ := hz
    exact hAk k hk hk' hz
  intro z hz
  rcases hsub hz with h | h
  · exact h
  · exfalso
    have h1 : z ∈ thickening δ u := hCN (limSup_subset_closure _ hz)
    have h2 : z ∈ thickening δ v := self_subset_thickening hδ _ h
    exact (hδd.le_bot ⟨h1, h2⟩ : _)

/-- **Limits of finely chained sets are connected.** -/
theorem isPreconnected_limSup [CompactSpace X] {I : Set ℕ} {A : ℕ → Set X} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hch : ∀ k ∈ I, ChainedAt (A k) (ε k)) {R : X}
    (hR : ∀ k ∈ I, R ∈ A k) (hI : I.Infinite) : IsPreconnected (limSup I A) := by
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed (isClosed_limSup I A)]
  intro u v hu hv hsub hdisj
  rcases hsub (mem_limSup hI hR) with h | h
  · exact Or.inl (limSup_subset_of_mem hε hch hR hu hv hsub hdisj h)
  · exact Or.inr (limSup_subset_of_mem hε hch hR hv hu (hsub.trans (union_comm u v).le)
      hdisj.symm h)

/-! ## Indecomposable continua -/

/-- **Boundary bumping, clopen form.** A nonempty subset `W` of a proper subset `L` of a
connected set `M`, closed and relatively open in `L`, meets the closure of `M \ L`. -/
theorem clopen_meets_closure_diff {M L W : Set X} (hM : IsPreconnected M) (hLM : L ⊆ M)
    (hLne : L ≠ M) (hWL : W ⊆ L) (hW : IsClosed W) {O : Set X} (hO : IsOpen O)
    (hWO : W = L ∩ O) (hWne : W.Nonempty) : (W ∩ closure (M \ L)).Nonempty := by
  by_contra hcon
  rw [not_nonempty_iff_eq_empty] at hcon
  obtain ⟨w, hw⟩ := hWne
  obtain ⟨x, hxM, hxL⟩ : ∃ x ∈ M, x ∉ L := by
    by_contra h
    push_neg at h
    exact hLne (Subset.antisymm hLM h)
  have hu : IsOpen (O ∩ (closure (M \ L))ᶜ) := hO.inter isClosed_closure.isOpen_compl
  obtain ⟨z, hzM, hzu, hzv⟩ := hM _ _ hu hW.isOpen_compl
    (by
      intro y hy
      by_cases hyW : y ∈ W
      · left
        refine ⟨?_, fun hc => ?_⟩
        · rw [hWO] at hyW; exact hyW.2
        · have : y ∈ W ∩ closure (M \ L) := ⟨hyW, hc⟩
          rw [hcon] at this; exact this
      · exact Or.inr hyW)
    ⟨w, hLM (hWL hw), (by rw [hWO] at hw; exact hw.2), fun hc => by
      have : w ∈ W ∩ closure (M \ L) := ⟨hw, hc⟩
      rw [hcon] at this; exact this⟩
    ⟨x, hxM, fun hxW => hxL (hWL hxW)⟩
  apply hzv
  rw [hWO]
  refine ⟨?_, hzu.1⟩
  by_contra hzL
  exact hzu.2 (subset_closure ⟨hzM, hzL⟩)

/-- A continuum: nonempty, compact, connected. (Same as `HPC.Fold.Q78.IsContinuum`.) -/
def IsCont (K : Set X) : Prop := IsCompact K ∧ IsConnected K

/-- Indecomposable (same as `HPC.Fold.Q78.IsIndecomposable`). -/
def IsIndec (K : Set X) : Prop :=
  IsCont K ∧ ∀ A B : Set X, IsCont A → IsCont B → A ⊆ K → B ⊆ K → A ∪ B = K → A = K ∨ B = K

/-- The union of a closed connected set `K` with a closed relatively open subset `L₁` of `L`,
where every nonempty closed relatively open subset of `L` meets `K`, is connected. -/
theorem isPreconnected_union_clopen {K L L₁ : Set X} (hK : IsPreconnected K) (hKc : IsClosed K)
    (hL₁ : IsClosed L₁) (hL₁L : L₁ ⊆ L) {O₁ : Set X} (hO₁ : IsOpen O₁) (hL₁O : L₁ = L ∩ O₁)
    (hmeet : ∀ W, W ⊆ L → IsClosed W → ∀ O, IsOpen O → W = L ∩ O → W.Nonempty →
      (W ∩ K).Nonempty) :
    IsPreconnected (K ∪ L₁) := by
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed (hKc.union hL₁)]
  intro u v hu hv hsub hdisj
  have key : ∀ u v : Set X, IsClosed u → IsClosed v → K ∪ L₁ ⊆ u ∪ v → Disjoint u v →
      K ⊆ u → K ∪ L₁ ⊆ u := by
    intro u v hu hv hsub hdisj hKu
    refine union_subset hKu ?_
    intro x hx
    by_contra hxu
    have hW : (L₁ ∩ v) = L ∩ (O₁ ∩ uᶜ) := by
      ext y
      constructor
      · rintro ⟨hy1, hy2⟩
        rw [hL₁O] at hy1
        exact ⟨hy1.1, hy1.2, fun hyu => hdisj.le_bot ⟨hyu, hy2⟩⟩
      · rintro ⟨hyL, hyO, hyu⟩
        have hy1 : y ∈ L₁ := by rw [hL₁O]; exact ⟨hyL, hyO⟩
        refine ⟨hy1, ?_⟩
        rcases hsub (Or.inr hy1) with h | h
        · exact absurd h hyu
        · exact h
    have hxv : x ∈ L₁ ∩ v := by
      rcases hsub (Or.inr hx) with h | h
      · exact absurd h hxu
      · exact ⟨hx, h⟩
    obtain ⟨y, ⟨-, hyv⟩, hyK⟩ := hmeet (L₁ ∩ v) (inter_subset_left.trans hL₁L)
      (hL₁.inter hv) _ (hO₁.inter hu.isOpen_compl) hW ⟨x, hxv⟩
    exact hdisj.le_bot ⟨hKu hyK, hyv⟩
  have hK' := (isPreconnected_iff_subset_of_fully_disjoint_closed hKc).mp hK u v hu hv
    (subset_union_left.trans hsub) hdisj
  rcases hK' with h | h
  · exact Or.inl (key u v hu hv hsub hdisj h)
  · refine Or.inr (key v u hv hu (hsub.trans (union_comm u v).le) hdisj.symm h)

/-- **A proper subcontinuum of an indecomposable continuum has empty interior** relative to the
continuum: no open set `O` meets `M` inside `K`. -/
theorem false_of_interior {M K O : Set X} (hM : IsIndec M) (hK : IsCont K) (hKM : K ⊆ M)
    (hKne : K ≠ M) (hO : IsOpen O) (hOM : (O ∩ M).Nonempty) (hOK : O ∩ M ⊆ K) : False := by
  have hMc : IsClosed M := hM.1.1.isClosed
  have hKc : IsClosed K := hK.1.isClosed
  set L := closure (M \ K) with hLdef
  have hLM : L ⊆ M := closure_minimal diff_subset hMc
  have hLc : IsClosed L := isClosed_closure
  obtain ⟨x, hxM, hxK⟩ : ∃ x ∈ M, x ∉ K := by
    by_contra h
    push_neg at h
    exact hKne (Subset.antisymm hKM h)
  have hxL : x ∈ L := subset_closure ⟨hxM, hxK⟩
  have hLne : L ≠ M := by
    obtain ⟨z, hzO, hzM⟩ := hOM
    intro hLeq
    have hzL : z ∈ L := hLeq ▸ hzM
    obtain ⟨y, hyO, hyM, hyK⟩ := mem_closure_iff.mp hzL O hO hzO
    exact hyK (hOK ⟨hyO, hyM⟩)
  have hcl : closure (M \ L) ⊆ K := by
    refine closure_minimal ?_ hKc
    rintro y ⟨hyM, hyL⟩
    by_contra hyK
    exact hyL (subset_closure ⟨hyM, hyK⟩)
  have hmeet : ∀ W, W ⊆ L → IsClosed W → ∀ O, IsOpen O → W = L ∩ O → W.Nonempty →
      (W ∩ K).Nonempty := by
    intro W hWL hW O hO hWO hWne
    obtain ⟨y, hyW, hy⟩ :=
      clopen_meets_closure_diff hM.1.2.isPreconnected hLM hLne hWL hW hO hWO hWne
    exact ⟨y, hyW, hcl hy⟩
  have hunion : K ∪ L = M := by
    refine Subset.antisymm (union_subset hKM hLM) ?_
    intro y hy
    by_cases hyK : y ∈ K
    · exact Or.inl hyK
    · exact Or.inr (subset_closure ⟨hy, hyK⟩)
  have hKnonempty := hK.2.nonempty
  by_cases hLpc : IsPreconnected L
  · rcases hM.2 K L hK ⟨hM.1.1.of_isClosed_subset hLc hLM, ⟨x, hxL⟩, hLpc⟩ hKM hLM hunion with h | h
    · exact hKne h
    · exact hLne h
  · rw [isPreconnected_closed_iff] at hLpc
    push_neg at hLpc
    obtain ⟨t, t', ht, ht', hLtt, ⟨a, haL, hat⟩, ⟨b, hbL, hbt'⟩, hempty⟩ := hLpc
    have hL1 : L ∩ t = L ∩ t'ᶜ := by
      ext y
      constructor
      · rintro ⟨hyL, hyt⟩
        exact ⟨hyL, fun hyt' => (hempty ▸ (⟨hyL, hyt, hyt'⟩ : y ∈ L ∩ (t ∩ t')) : y ∈ (∅ : Set X))⟩
      · rintro ⟨hyL, hyt'⟩
        rcases hLtt hyL with h | h
        · exact ⟨hyL, h⟩
        · exact absurd h hyt'
    have hL2 : L ∩ t' = L ∩ tᶜ := by
      ext y
      constructor
      · rintro ⟨hyL, hyt'⟩
        exact ⟨hyL, fun hyt => (hempty ▸ (⟨hyL, hyt, hyt'⟩ : y ∈ L ∩ (t ∩ t')) : y ∈ (∅ : Set X))⟩
      · rintro ⟨hyL, hyt⟩
        rcases hLtt hyL with h | h
        · exact absurd h hyt
        · exact ⟨hyL, h⟩
    have hcont : ∀ s : Set X, IsClosed s → ∀ O, IsOpen O → L ∩ s = L ∩ O →
        IsCont (K ∪ (L ∩ s)) := by
      intro s hs O hO hsO
      have hcl' : IsClosed (K ∪ (L ∩ s)) := hKc.union (hLc.inter hs)
      exact ⟨hM.1.1.of_isClosed_subset hcl' (union_subset hKM (inter_subset_left.trans hLM)),
        ⟨hKnonempty.mono subset_union_left,
          isPreconnected_union_clopen hK.2.isPreconnected hKc (hLc.inter hs) inter_subset_left
            hO hsO hmeet⟩⟩
    -- a point of `M \ K` outside `t` (resp. `t'`)
    have hout : ∀ s s' : Set X, IsClosed s → L ∩ s' = L ∩ sᶜ → (L ∩ s').Nonempty →
        ∃ y ∈ M, y ∉ K ∧ y ∉ s := by
      intro s s' hs hss' ⟨z, hz⟩
      rw [hss'] at hz
      obtain ⟨y, hys, hyM, hyK⟩ := mem_closure_iff.mp hz.1 sᶜ hs.isOpen_compl hz.2
      exact ⟨y, hyM, hyK, hys⟩
    have hU1 : K ∪ (L ∩ t) ≠ M := by
      obtain ⟨y, hyM, hyK, hyt⟩ := hout t t' ht hL2 ⟨b, hbL, hbt'⟩
      intro heq
      rw [← heq] at hyM
      rcases hyM with h | h
      · exact hyK h
      · exact hyt h.2
    have hU2 : K ∪ (L ∩ t') ≠ M := by
      obtain ⟨y, hyM, hyK, hyt⟩ := hout t' t ht' hL1 ⟨a, haL, hat⟩
      intro heq
      rw [← heq] at hyM
      rcases hyM with h | h
      · exact hyK h
      · exact hyt h.2
    have hU : (K ∪ (L ∩ t)) ∪ (K ∪ (L ∩ t')) = M := by
      rw [← hunion]
      ext y
      constructor
      · rintro ((h | h) | (h | h))
        · exact Or.inl h
        · exact Or.inr h.1
        · exact Or.inl h
        · exact Or.inr h.1
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · rcases hLtt h with h' | h'
          · exact Or.inl (Or.inr ⟨h, h'⟩)
          · exact Or.inr (Or.inr ⟨h, h'⟩)
    rcases hM.2 _ _ (hcont t ht _ ht'.isOpen_compl hL1) (hcont t' ht' _ ht.isOpen_compl hL2)
      (union_subset hKM (inter_subset_left.trans hLM))
      (union_subset hKM (inter_subset_left.trans hLM)) hU with h | h
    · exact hU1 h
    · exact hU2 h

/-- **Some point of an indecomposable continuum lies in no proper subcontinuum through `p`**
(so the composant of `p` is not everything). Proper subcontinua through `p` all lie in one of
countably many proper subcontinua (components of `M ∖ b`, `b` a basic open set meeting `M`), each
of which has empty interior in `M`; Baire. -/
theorem exists_not_mem_proper_subcontinua [CompactSpace X] {M : Set X} (hM : IsIndec M) {p : X}
    (hp : p ∈ M) : ∃ y ∈ M, ∀ K, IsCont K → K ⊆ M → K ≠ M → p ∈ K → y ∉ K := by
  by_contra hcon
  push_neg at hcon
  have hMc : IsClosed M := hM.1.1.isClosed
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis X
  set B' := {b ∈ B | (b ∩ M).Nonempty}
  have hB'c : B'.Countable := hBc.mono (fun b hb => hb.1)
  haveI : Countable B' := hB'c.to_subtype
  set C : B' → Set X := fun b => connectedComponentIn (M \ b.1) p with hCdef
  have hCsub : ∀ b, C b ⊆ M \ b.1 := fun b => connectedComponentIn_subset _ _
  have hCclosed : ∀ b, IsClosed (C b) := by
    intro b
    have hF : IsClosed (M \ b.1) := hMc.sdiff (hB.isOpen b.2.1)
    by_cases hpb : p ∈ M \ b.1
    · have : closure (C b) ⊆ C b :=
        (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
          (subset_closure (mem_connectedComponentIn hpb))
          (closure_minimal (connectedComponentIn_subset _ _) hF)
      exact closure_subset_iff_isClosed.mp this
    · simp only [hCdef, connectedComponentIn_eq_empty hpb, isClosed_empty]
  have hcover : ∀ y ∈ M, ∃ b, y ∈ C b := by
    intro y hy
    obtain ⟨K, hK, hKM, hKne, hpK, hyK⟩ := hcon y hy
    obtain ⟨x, hxM, hxK⟩ : ∃ x ∈ M, x ∉ K := by
      by_contra h
      push_neg at h
      exact hKne (Subset.antisymm hKM h)
    obtain ⟨b, hbB, hxb, hbK⟩ := hB.exists_subset_of_mem_open hxK hK.1.isClosed.isOpen_compl
    refine ⟨(⟨b, ⟨hbB, ⟨x, hxb, hxM⟩⟩⟩ : B'), ?_⟩
    exact hK.2.isPreconnected.subset_connectedComponentIn hpK
      (F := M \ b) (fun z hz => ⟨hKM hz, fun hzb => hbK hzb hz⟩) hyK
  haveI : CompactSpace M := isCompact_iff_compactSpace.mp hM.1.1
  haveI : Nonempty M := ⟨⟨p, hp⟩⟩
  obtain ⟨b, hb⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun b => (Subtype.val : M → X) ⁻¹' C b)
    (fun b => (hCclosed b).preimage continuous_subtype_val)
    (by
      ext ⟨y, hy⟩
      simp only [mem_iUnion, mem_preimage, mem_univ, iff_true]
      exact hcover y hy)
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp
    (isOpen_interior (s := (Subtype.val : M → X) ⁻¹' C b))
  obtain ⟨⟨z, hzM⟩, hz⟩ := hb
  have hzO : z ∈ O := by
    have : (⟨z, hzM⟩ : M) ∈ (Subtype.val : M → X) ⁻¹' O := by rw [hOeq]; exact hz
    exact this
  have hOC : O ∩ M ⊆ C b := by
    rintro y ⟨hyO, hyM⟩
    have : (⟨y, hyM⟩ : M) ∈ interior ((Subtype.val : M → X) ⁻¹' C b) := by
      rw [← hOeq]; exact hyO
    exact interior_subset (s := (Subtype.val : M → X) ⁻¹' C b) this
  obtain ⟨x, hxb, hxM⟩ := b.2.2
  refine false_of_interior hM ⟨(hCclosed b).isCompact, ⟨⟨z, hOC ⟨hzO, hzM⟩⟩,
    isPreconnected_connectedComponentIn⟩⟩ (fun y hy => (hCsub b hy).1) ?_ hO ⟨z, hzO, hzM⟩ hOC
  intro heq
  have : x ∈ C b := heq ▸ hxM
  exact (hCsub b this).2 hxb

end HPC.T13
