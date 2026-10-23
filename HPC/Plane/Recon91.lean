import HPC.Plane.Most51
import HPC.Plane.Windows91
import HPC.Plane.Composant91
import HPC.Plane.Surgery91

/-!
# Batch 91: Bing's windows for Pacific Theorem 3; reconnaissance on Duke 1951 Theorem 10

Skeleton (save as `HPC/Plane/Recon91.lean`; add `import HPC.Plane.Recon91` to the root `HPC.lean`).
`theorem10_1951` itself lives in `HPC/Plane/EndPoints51.lean` and is the target of §2 of
the commission; its strongest proved form goes here under a new name if the statement there is
not reached.

**Batch 91 delivery.**
* `theorem3_HIC_bing`: Theorem 3 with **Bing's own chain**: his sequence `n_i` (`Mono.bingSeq`,
  strictly increasing until it reaches the last link) and his windows `D(n_{3k+1}, n_{3k+5})`, the
  last running to `n_j`. `theorem3_HIC_windows` (the skeleton's statement, unchanged) follows from
  it. The combinatorics are in `HPC/Plane/Windows91.lean`.
* `exists_proper_meeting_all_links` (Q1): **proved**, not refuted — composants are dense
  (`HPC/Plane/Composant91.lean`, boundary bumping). Shape change: the unused hypothesis
  `hD : M ⊆ D.union` is removed.
* `theorem10_1951_of_step` is equivalent to `theorem10_1951` once Q1 is proved; it is kept only in
  a comment. Proved forms of Theorem 10: `theorem10_1951_of_endPoint` (for end points) and Bing's
  surgery, `theorem10_1951_of_lastLink` / `theorem10_1951_of_lastLink'`
  (`HPC/Plane/Surgery91.lean`), which derive Theorem 10 from the existence of a subcontinuum
  through `p` with a Theorem-10 chain whose last link meets it in `d_1 ∪ d_m` off `p`.
-/

namespace HPC.Plane

open Set

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- The fibre of `f` (inside `M`) over `y` meets link `i` of the chain `C` (links indexed by `ℕ`;
false for `i ≥ m`). -/
def fibreMeets (f : X → Y) (M : Set X) {m : ℕ} (C : Chain X m) (y : Y) (i : ℕ) : Prop :=
  ∃ h : i < m, (C.link ⟨i, h⟩ ∩ (M ∩ f ⁻¹' {y})).Nonempty

/-- **Bing's window** `D(a, b)`: the points of `M'` whose fibre lies in `c(a) ∪ ⋯ ∪ c(b)`. -/
def bingWindow (f : X → Y) (M : Set X) (M' : Set Y) {m : ℕ} (C : Chain X m) (a b : ℕ) : Set Y :=
  {y | y ∈ M' ∧ M ∩ f ⁻¹' {y} ⊆ ⋃ (i : Fin m) (_ : a ≤ i.val ∧ i.val ≤ b), C.link i}

/-- **Bing 1951 (Pacific J. Math.), Theorem 3, with Bing's chain** (Nadler 12.13). For a monotone
map `f` of the chainable continuum `M` onto `M'` and `ε > 0` there is a chain `C` covering `M`,
every link meeting `M`, such that, with Bing's sequence `n_k = bingSeq (fibreMeets f M C) m k`
(`n_0 = 0`, `n_{k+1}` the last link met by a fibre meeting link `n_k`), strictly increasing up to
`n_J = m - 1`, and `K = (J - 2) / 3`, the windows `D(n_{3k}, n_{3k+4})` (`k < K`) and
`D(n_{3K}, n_J)` are exactly the traces on `M'` of the links of an `ε`-chain of `Y` covering `M'`.
(Indices from `0`: Bing's `D(n_{3k+1}, n_{3k+5})`.) -/
theorem theorem3_HIC_bing {f : X → Y} {M : Set X} {M' : Set Y} (hM : IsSnakeLike M)
    (hf : IsMonotoneMap f M M') {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (C : Chain X m), M ⊆ C.union ∧ (∀ i, (C.link i ∩ M).Nonempty) ∧
      ∃ J K : ℕ, Mono.bingSeq (fibreMeets f M C) m J = m - 1 ∧
        (∀ k < J, Mono.bingSeq (fibreMeets f M C) m k < Mono.bingSeq (fibreMeets f M C) m (k + 1)) ∧
        K = (J - 2) / 3 ∧
        ∃ E : Chain Y (K + 1), IsEpsChain E ε ∧ M' ⊆ E.union ∧
          ∀ k : Fin (K + 1), E.link k ∩ M' = bingWindow f M M' C
            (Mono.bingSeq (fibreMeets f M C) m (3 * k.val))
            (if k.val = K then Mono.bingSeq (fibreMeets f M C) m J
              else Mono.bingSeq (fibreMeets f M C) m (3 * k.val + 4)) := by
  classical
  obtain ⟨hfc, hfM, hfib⟩ := hf
  have hMc : IsCompact M := hM.1.1
  have hM'c : IsCompact M' := hfM ▸ hMc.image_of_continuousOn hfc
  have hM'conn : IsConnected M' := hfM ▸ hM.1.2.image f hfc
  haveI : Nonempty M' := hM'conn.nonempty.to_subtype
  haveI : PreconnectedSpace M' := Subtype.preconnectedSpace hM'conn.isPreconnected
  set η := ε / 8 with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hunif⟩ : ∃ δ > 0, ∀ x ∈ M, ∀ x' ∈ M, dist x x' < δ → dist (f x) (f x') < η :=
    Metric.uniformContinuousOn_iff.mp (hMc.uniformContinuousOn_of_continuous hfc) η hη
  obtain ⟨n, C, hCε, hMC, hCmeet⟩ :=
    exists_cover_meeting hM.1.2.isPreconnected hM.1.2.nonempty hM.2 (half_pos hδ)
  -- fibres, the links they meet, and Bing's sets `D(p, q)`
  set F : M' → Set X := fun y => M ∩ f ⁻¹' {(y : Y)} with hF_def
  set R : M' → ℕ → Prop := fun y i => ∃ h : i < n, (C.link ⟨i, h⟩ ∩ F y).Nonempty with hR_def
  set U : ℕ → ℕ → Set X := fun p q => ⋃ (i : Fin n) (_ : p ≤ i.val ∧ i.val ≤ q), C.link i
    with hU_def
  set G : ℕ → ℕ → Set M' := fun p q => {y | F y ⊆ U p q} with hG_def
  have hFne : ∀ y : M', (F y).Nonempty := fun y => (hfib y y.2).nonempty
  have hFC : ∀ y : M', F y ⊆ C.union := fun y => inter_subset_left.trans hMC
  have hlink : ∀ x ∈ C.union, ∃ i : Fin n, x ∈ C.link i := fun x hx => mem_iUnion.mp hx
  have hUo : ∀ p q, IsOpen (U p q) := fun p q => isOpen_biUnion fun i _ => C.isOpen i
  -- adjacent links share a fibre (connectedness of `M`)
  have hR6 : ∀ i, i + 1 < n → ∃ y : M', R y i ∧ R y (i + 1) := by
    intro i hi
    obtain ⟨x₁, hx₁C, hx₁M⟩ := hCmeet ⟨i, by omega⟩
    obtain ⟨x₂, hx₂C, hx₂M⟩ := hCmeet ⟨i + 1, hi⟩
    obtain ⟨x, hxM, hx1, hx2⟩ := hM.1.2.isPreconnected (U 0 i) (U (i + 1) n) (hUo _ _) (hUo _ _)
      (fun x hx => by
        obtain ⟨j, hj⟩ := hlink x (hMC hx)
        by_cases hji : j.val ≤ i
        · exact Or.inl (mem_biUnion (x := j) ⟨Nat.zero_le _, hji⟩ hj)
        · exact Or.inr (mem_biUnion (x := j) ⟨by omega, j.isLt.le⟩ hj))
      ⟨x₁, hx₁M, mem_biUnion (x := ⟨i, by omega⟩) ⟨Nat.zero_le _, le_rfl⟩ hx₁C⟩
      ⟨x₂, hx₂M, mem_biUnion (x := ⟨i + 1, hi⟩) ⟨le_rfl, hi.le⟩ hx₂C⟩
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx1
    obtain ⟨j', hj', hxj'⟩ := mem_iUnion₂.mp hx2
    have hadj := (C.adjacent_iff j j').mp ⟨x, hxj, hxj'⟩
    have e1 : j = ⟨i, by omega⟩ := Fin.ext (show j.val = i by omega)
    have e2 : j' = ⟨i + 1, hi⟩ := Fin.ext (show j'.val = i + 1 by omega)
    rw [e1] at hxj
    rw [e2] at hxj'
    have hy : f x ∈ M' := hfM ▸ mem_image_of_mem f hxM
    exact ⟨⟨f x, hy⟩, ⟨by omega, x, hxj, hxM, rfl⟩, ⟨hi, x, hxj', hxM, rfl⟩⟩
  obtain ⟨J, K, hJ, hJlt, hK, D, hDcov, hDlink, hDdiam⟩ := Mono.exists_bing_windows (n := n)
    (η := η) R G
    (fun y i h => h.1)
    (fun y => by
      obtain ⟨x, hx⟩ := hFne y
      obtain ⟨i, hi⟩ := hlink x (hFC y hx)
      exact ⟨i.val, i.isLt, x, hi, hx⟩)
    (fun y i j k ⟨hi, hxi⟩ ⟨hk, hxk⟩ hij hjk => by
      refine ⟨by omega, ?_⟩
      exact Chain.meet_ordConnected C (hfib y y.2).isPreconnected (hFC y)
        (i := ⟨i, hi⟩) (k := ⟨k, hk⟩) (Fin.mk_le_mk.mpr hij) (Fin.mk_le_mk.mpr hjk) hxi hxk)
    (fun i hi => by
      obtain ⟨x, hxC, hxM⟩ := hCmeet ⟨i, hi⟩
      have hy : f x ∈ M' := hfM ▸ mem_image_of_mem f hxM
      exact ⟨⟨f x, hy⟩, hi, x, hxC, hxM, rfl⟩)
    (fun y y' i i' ⟨hi, x, hxC, hxM, hxy⟩ ⟨hi', x', hxC', hxM', hxy'⟩ h1 h2 => by
      obtain ⟨w, hw, hw'⟩ := (C.adjacent_iff ⟨i, hi⟩ ⟨i', hi'⟩).mpr ⟨h1, h2⟩
      have d1 : dist x w ≤ Metric.diam (C.link ⟨i, hi⟩) :=
        Metric.dist_le_diam_of_mem (hCε _).1 hxC hw
      have d2 : dist w x' ≤ Metric.diam (C.link ⟨i', hi'⟩) :=
        Metric.dist_le_diam_of_mem (hCε _).1 hw' hxC'
      have e1 := (hCε ⟨i, hi⟩).2
      have e2 := (hCε ⟨i', hi'⟩).2
      have hxx' : dist x x' < δ := by
        linarith [dist_triangle x w x']
      have := hunif x hxM x' hxM' hxx'
      rw [Subtype.dist_eq]
      rw [mem_preimage, mem_singleton_iff] at hxy hxy'
      rwa [← hxy, ← hxy'])
    hR6
    (fun p q => by
      have hK : IsCompact (M \ U p q) := hMc.diff (hUo p q)
      have hKc : IsClosed (f '' (M \ U p q)) :=
        (hK.image_of_continuousOn (hfc.mono diff_subset)).isClosed
      have : G p q = (Subtype.val ⁻¹' (f '' (M \ U p q)))ᶜ := by
        ext y
        simp only [hG_def, hF_def, mem_setOf_eq, mem_compl_iff, mem_preimage, mem_image,
          mem_diff, not_exists, not_and, subset_def, mem_inter_iff, mem_singleton_iff]
        constructor
        · intro h x ⟨hxM, hxU⟩ hxy
          exact hxU (h x ⟨hxM, hxy⟩)
        · intro h x ⟨hxM, hxy⟩
          by_contra hxU
          exact h x ⟨hxM, hxU⟩ hxy
      rw [this]
      exact (hKc.preimage continuous_subtype_val).isOpen_compl)
    (fun y p q h x hx => by
      obtain ⟨i, hi⟩ := hlink x (hFC y hx)
      exact mem_biUnion (x := i) (h i.val ⟨i.isLt, x, hi, hx⟩) hi)
    (fun y p q hy => by
      obtain ⟨x, hx⟩ := hFne y
      obtain ⟨i, hpq, hxi⟩ := mem_iUnion₂.mp (hy hx)
      exact ⟨i.val, ⟨i.isLt, x, hxi, hx⟩, hpq⟩)
    (fun y p q p' q' hy hy' hqp => by
      obtain ⟨x, hx⟩ := hFne y
      obtain ⟨i, hpq, hxi⟩ := mem_iUnion₂.mp (hy hx)
      obtain ⟨i', hpq', hxi'⟩ := mem_iUnion₂.mp (hy' hx)
      have := (C.adjacent_iff i i').mp ⟨x, hxi, hxi'⟩
      omega)
  -- Bing's sequence computed in `M'` is the one computed in `Y`
  have hseq : ∀ k, Mono.bingSeq R n k = Mono.bingSeq (fibreMeets f M C) n k :=
    Mono.bingSeq_congr R (fibreMeets f M C) n (fun i j => by
      constructor
      · rintro ⟨y, h1, h2⟩; exact ⟨y.1, h1, h2⟩
      · rintro ⟨y, h1, h2⟩
        have h1' := h1
        unfold fibreMeets at h1'
        obtain ⟨-, x, -, hxM, hxy⟩ := h1'
        have hy : y ∈ M' := by
          rw [mem_preimage, mem_singleton_iff] at hxy
          exact hxy ▸ hfM ▸ mem_image_of_mem f hxM
        exact ⟨⟨y, hy⟩, h1, h2⟩)
  -- lift the chain of the space `M'` to `Y`
  have hM'cl : IsClosed M' := hM'c.isClosed
  refine ⟨n, C, hMC, hCmeet, J, K, by rw [← hseq]; exact hJ,
    fun k hk => by rw [← hseq, ← hseq]; exact hJlt k hk, hK,
    PA51.liftChain hM'cl D η hη, fun j => ?_, fun y hy => ?_, fun k => ?_⟩
  · refine ⟨PA51.isBounded_ext M' η (hDdiam j).1, ?_⟩
    calc Metric.diam ((PA51.liftChain hM'cl D η hη).link j)
        ≤ Metric.diam (D.link j) + 2 * η := PA51.diam_ext_le M' hη.le (hDdiam j).1
      _ ≤ 5 * η + 2 * η := by linarith [(hDdiam j).2]
      _ < ε := by rw [hη_def]; linarith
  · obtain ⟨j, hj⟩ := mem_iUnion.mp (hDcov (mem_univ (⟨y, hy⟩ : M')))
    exact mem_iUnion.mpr ⟨j, (PA51.mem_ext_iff hM'cl (D.isOpen j) hη ⟨y, hy⟩).mpr hj⟩
  · ext y
    constructor
    · rintro ⟨hyE, hy⟩
      have h := (PA51.mem_ext_iff hM'cl (D.isOpen k) hη ⟨y, hy⟩).mp hyE
      rw [hDlink k] at h
      refine ⟨hy, ?_⟩
      have h' : F ⟨y, hy⟩ ⊆ U _ _ := h
      split_ifs at h' ⊢ <;> simpa only [hseq] using h'
    · rintro ⟨hy, hsub⟩
      refine ⟨(PA51.mem_ext_iff hM'cl (D.isOpen k) hη ⟨y, hy⟩).mpr ?_, hy⟩
      rw [hDlink k]
      show F ⟨y, hy⟩ ⊆ U _ _
      split_ifs at hsub ⊢ <;> simpa only [hseq] using hsub

/-- **Bing's windows** (Pacific J. Math. Theorem 3, Nadler 12.13): for a monotone map `f` of a
chainable continuum `M` onto `M'`, with `δ` from uniform continuity for `ε/5`, a `δ`-chain `C`
covering `M` with every link meeting `M`, the indices `n₁ = 0 < n₂ < ⋯` defined by
`n_{i+1} = max {j : some fibre meets c(n_i) and c(j)}`, and the windows
`D(a, b) = {y ∈ M' : fibre y ⊆ c(a) ∪ ⋯ ∪ c(b)}` taken as `D(n_{3k+1}, n_{3k+5})` (last one to the end),
form an `ε`-chain of `M'` covering `M'`. Stated through its conclusion; the report records the
exact form of the chain it proves (COMMISSION-batch91.md §1). Proved from `theorem3_HIC_bing`,
which names the windows exactly. -/
theorem theorem3_HIC_windows {f : X → Y} {M : Set X} {M' : Set Y} (hM : IsSnakeLike M)
    (hf : IsMonotoneMap f M M') {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (E : Chain Y n), IsEpsChain E ε ∧ M' ⊆ E.union ∧
      -- each link of `E` is a window of Bing's form: the points of `M'` whose fibre lies in the
      -- union of a run of consecutive links of a chain covering `M`
      ∃ (m : ℕ) (C : Chain X m), M ⊆ C.union ∧ ∀ u : Fin n, ∃ a b : ℕ, a ≤ b ∧ b < m ∧
        E.link u ∩ M' = {y | y ∈ M' ∧ M ∩ f ⁻¹' {y} ⊆ ⋃ (i : Fin m) (_ : a ≤ i.val ∧ i.val ≤ b), C.link i} := by
  obtain ⟨m, C, hMC, hCmeet, J, K, hJ, hJlt, hK, E, hEε, hM'E, hE⟩ := theorem3_HIC_bing hM hf hε
  set N := Mono.bingSeq (fibreMeets f M C) m with hN_def
  have hm : 0 < m := by
    obtain ⟨x, hx⟩ := hM.1.2.nonempty
    obtain ⟨i, -⟩ := mem_iUnion.mp (hMC hx)
    exact lt_of_le_of_lt (Nat.zero_le _) i.isLt
  -- Bing's sequence is monotone and ends at `m - 1`
  have hmono : ∀ k k', k ≤ k' → k' ≤ J → N k ≤ N k' := by
    intro k k' h h'
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      have := hJlt (k + d) (by omega)
      have := ih (by omega) (by omega)
      rw [← add_assoc]; omega
  refine ⟨K + 1, E, hEε, hM'E, m, C, hMC, fun u => ?_⟩
  have hu := u.isLt
  refine ⟨N (3 * u.val), if u.val = K then N J else N (3 * u.val + 4), ?_, ?_, hE u⟩
  · split_ifs with h
    · exact hmono _ _ (by omega) le_rfl
    · exact hmono _ _ (by omega) (by omega)
  · split_ifs with h
    · rw [hJ]; omega
    · have := hmono (3 * u.val + 4) J (by omega) le_rfl
      rw [hJ] at this; omega

/-- **The step of Bing's proof of Duke 1951 Theorem 10** (p. 659): "`M` contains a proper
subcontinuum `M''` that contains `p` and intersects each element of `D`". **Proved** (Q1): the
proper subcontinua through `p` are nested (condition B, from condition A) and their union, the
composant of `p`, is dense (boundary bumping, `exists_proper_subcontinuum_meeting`); the largest
of finitely many of them, one meeting each link, meets every link. The `sin(1/x)` candidate of
the commission does not refute it: a link is open, and an open set meeting the limit bar meets the
curve, so a long enough arc of the curve from `p` meets every link.

Shape change: the skeleton's hypothesis `hD : M ⊆ D.union` is not used and has been removed. -/
theorem exists_proper_meeting_all_links {M : Set X} (hM : Fold.Q78.IsContinuum M)
    (hnd : M.Nontrivial) {p : X} (hp : CondA M p) {m : ℕ} (D : Chain X m)
    (hmeet : ∀ i, (D.link i ∩ M).Nonempty) :
    ∃ K : Set X, K ⊆ M ∧ K ≠ M ∧ Fold.Q78.IsContinuum K ∧ p ∈ K ∧ ∀ i, (D.link i ∩ K).Nonempty :=
  exists_proper_meeting_all_links_of_condB hM hnd (condB_of_condA hp) D hmeet

-- Commented-out statement `theorem10_1951_of_step` removed in batch 103; see `LEDGER.md`.

/-- **Theorem 10 for end points** (Q4, the weakest of the listed forms; circular for Theorem 13,
which it does not serve, but a statement): if `p` is an end point of the continuum `M` (condition
C), every chain `D` covering `M` has a refinement `E` covering `M` with `p` in its first link and in
the closure of no other link. A fine end-point chain (mesh below a Lebesgue number of `D`) refines
`D`; removing a small closed ball about `p` from all links but the first and trimming the resulting
weak chain to the links meeting `M` keeps `p` away from the closures of the other links. -/
theorem theorem10_1951_of_endPoint {M : Set X} (hM : Fold.Q78.IsContinuum M) {m : ℕ}
    (D : Chain X m) (hD : M ⊆ D.union) {p : X} (hp : IsEndPoint M p) :
    ∃ (n : ℕ) (E : Chain X n) (hn : 0 < n), M ⊆ E.union ∧ E.Refines D ∧
      p ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (E.link j) := by
  classical
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hM.1 D.isOpen hD
  obtain ⟨n, E, hn, hEε, hME, hp0, hpj⟩ := hp.2 δ hδ
  obtain ⟨ρ, hρ, hρE⟩ := Metric.isOpen_iff.mp (E.isOpen ⟨0, hn⟩) p hp0
  set B := Metric.closedBall p (ρ / 2) with hB_def
  have hBE : B ⊆ E.link ⟨0, hn⟩ := fun z hz =>
    hρE (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (half_lt_self hρ)))
  set L : ℕ → Set X := fun i => if i = 0 then linkN E 0 else linkN E i \ B with hL_def
  have hLsub : ∀ i, L i ⊆ linkN E i := fun i => by
    simp only [hL_def]; split_ifs with h
    · rw [h]
    · exact diff_subset
  have hLo : ∀ i, IsOpen (L i) := fun i => by
    simp only [hL_def]; split_ifs
    · exact isOpen_linkN E 0
    · exact (isOpen_linkN E i).sdiff Metric.isClosed_closedBall
  have hweak : ∀ i j, i + 2 ≤ j → j < n → Disjoint (L i) (L j) := fun i j hij _ =>
    (disjoint_linkN E hij).mono (hLsub i) (hLsub j)
  have hcov : M ⊆ ⋃ i, ⋃ (_ : i < n), L i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := (mem_union_iff_linkN E).mp (hME hx)
    by_cases hxB : x ∈ B
    · refine mem_iUnion₂.mpr ⟨0, hn, ?_⟩
      simp only [hL_def, if_pos rfl, linkN_of_lt E hn]
      exact hBE hxB
    · refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
      simp only [hL_def]; split_ifs with h
      · rw [← h]; exact hxi
      · exact ⟨hxi, hxB⟩
  have hL0 : L 0 = E.link ⟨0, hn⟩ := by simp only [hL_def, if_pos rfl, linkN_of_lt E hn]
  obtain ⟨a, k, E', ha, hk, -, hE'L, hME', hE'meet, -⟩ := exists_chain_of_weak L hLo hweak
    hM.2.isPreconnected hcov hn (by rw [hL0]; exact ⟨p, hp0, hp.1⟩)
  have ha0 : a = 0 := by omega
  subst ha0
  have hk0 : 0 < k := by omega
  refine ⟨k, E', hk0, hME', fun t => ?_, ?_, fun j hj => ?_⟩
  · -- a link of `E'` meets `M` and lies in a link of `E`, of diameter `< δ`
    obtain ⟨x, hxE', hxM⟩ := hE'meet t
    have hsub : E'.link t ⊆ linkN E t := by rw [hE'L t, zero_add]; exact hLsub _
    obtain ⟨ht, -⟩ := (mem_linkN E).mp (hsub hxE')
    obtain ⟨i, hi⟩ := hleb x hxM
    refine ⟨i, fun z hz => hi (Metric.mem_ball.mpr ?_)⟩
    have hz' := hsub hz
    have hx' := hsub hxE'
    rw [linkN_of_lt E ht] at hz' hx'
    exact lt_of_le_of_lt (Metric.dist_le_diam_of_mem (hEε _).1 hz' hx') (hEε _).2
  · rw [hE'L, zero_add, hL0]; exact hp0
  · intro hcl
    have hsub : E'.link j ⊆ {z | ρ / 2 ≤ dist z p} := by
      intro z hz
      rw [hE'L j, zero_add] at hz
      simp only [hL_def, if_neg hj] at hz
      have := hz.2
      rw [hB_def, Metric.mem_closedBall, not_le] at this
      exact this.le
    have hclosed : IsClosed {z | ρ / 2 ≤ dist z p} := isClosed_le continuous_const
      (continuous_id.dist continuous_const)
    have := closure_minimal hsub hclosed hcl
    simp only [mem_setOf_eq, dist_self] at this
    linarith

end HPC.Plane
