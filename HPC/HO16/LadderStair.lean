import HPC.HO16.LadderPiece

/-!
# Batch 197: a ladder carries a stairwell structure (geometry)

The global half of commission 197 §3: from the per-edge facts of `LadderParam.lean` and
`LadderPiece.lean` to (S1)–(S5) for the sheets of a ladder. The end set of a sheet is computed with
two closed sets of "gaps" (`gapA`, `gapB`): every point of `G` outside `π(Sᵢ)` lies in one of them,
the closure of a component of `G \ π(Sᵢ)` lies in one of them, and they meet `π(Sᵢ)` only in
`π(αᵢ)`, resp. `π(αᵢ₊₁)`. This replaces the case analysis of components in H–O's (S4) argument
(p. 198) by a labelling of the gaps; the parity of the vertex lists enters through `e_ends`.
-/

namespace HPC.HO16

open Set Topology Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The decomposition -/

section Decomp

variable {G : Set E} {S : Finset (E × E)}

theorem segment_subset_of_mem (hG : G = ⋃ s ∈ S, segment ℝ s.1 s.2) {s : E × E} (hs : s ∈ S) :
    segment ℝ s.1 s.2 ⊆ G := by
  rw [hG]; exact subset_biUnion_of_mem (u := fun s : E × E => segment ℝ s.1 s.2) hs

theorem lineMap_mem_of_mem (hG : G = ⋃ s ∈ S, segment ℝ s.1 s.2) {s : E × E} (hs : s ∈ S)
    {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1) : AffineMap.lineMap s.1 s.2 μ ∈ G :=
  segment_subset_of_mem hG hs (by rw [segment_eq_image_lineMap]; exact ⟨μ, hμ, rfl⟩)

theorem exists_param_of_mem (hG : G = ⋃ s ∈ S, segment ℝ s.1 s.2) {x : E} (hx : x ∈ G) :
    ∃ s ∈ S, ∃ μ ∈ Icc (0 : ℝ) 1, AffineMap.lineMap s.1 s.2 μ = x := by
  rw [hG] at hx
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx
  rw [segment_eq_image_lineMap] at hxs
  obtain ⟨μ, hμ, rfl⟩ := hxs
  exact ⟨s, hs, μ, hμ, rfl⟩

theorem lineMap_eq_left_iff {a b : E} (hab : a ≠ b) {μ : ℝ} :
    AffineMap.lineMap a b μ = a ↔ μ = 0 := by
  constructor
  · intro h
    exact lineMap_inj hab (h.trans (AffineMap.lineMap_apply_zero a b).symm)
  · rintro rfl; exact AffineMap.lineMap_apply_zero a b

theorem lineMap_eq_right_iff {a b : E} (hab : a ≠ b) {μ : ℝ} :
    AffineMap.lineMap a b μ = b ↔ μ = 1 := by
  constructor
  · intro h
    exact lineMap_inj hab (h.trans (AffineMap.lineMap_apply_one a b).symm)
  · rintro rfl; exact AffineMap.lineMap_apply_one a b

/-- An interior point of an edge lies on no other edge. -/
theorem eq_of_lineMap_mem_segment (hne : ∀ s ∈ S, s.1 ≠ s.2) (hdis : PairwiseEndpoints S)
    {s s' : E × E} (hs : s ∈ S) (hs' : s' ∈ S) {μ : ℝ} (hμ : μ ∈ Ioo (0 : ℝ) 1)
    (hx : AffineMap.lineMap s.1 s.2 μ ∈ segment ℝ s'.1 s'.2) : s' = s := by
  by_contra h
  have hx0 : AffineMap.lineMap s.1 s.2 μ ∈ segment ℝ s.1 s.2 := by
    rw [segment_eq_image_lineMap]; exact ⟨μ, Ioo_subset_Icc_self hμ, rfl⟩
  rcases (hdis s hs s' hs' (Ne.symm h) ⟨hx0, hx⟩).1 with h1 | h1
  · exact hμ.1.ne' ((lineMap_eq_left_iff (hne s hs)).1 h1)
  · exact hμ.2.ne ((lineMap_eq_right_iff (hne s hs)).1 (Set.mem_singleton_iff.1 h1))

/-- Near an interior point of an edge, `G` is that edge. -/
theorem exists_ball_param (hne : ∀ s ∈ S, s.1 ≠ s.2) (hdis : PairwiseEndpoints S)
    {s : E × E} (hs : s ∈ S) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ z ∈ ball (AffineMap.lineMap s.1 s.2 a) r, ∀ s' ∈ S, ∀ ν ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap s'.1 s'.2 ν = z → s' = s ∧ |ν - a| < η := by
  classical
  set C := ⋃ s' ∈ S.erase s, segment ℝ s'.1 s'.2
  have hC : IsClosed C := isClosed_biUnion_segment _
  have hxC : AffineMap.lineMap s.1 s.2 a ∉ C := by
    intro h
    obtain ⟨s', hs', hx⟩ := mem_iUnion₂.1 h
    exact Finset.ne_of_mem_erase hs' (eq_of_lineMap_mem_segment hne hdis hs
      (Finset.mem_of_mem_erase hs') ha hx)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hC.isOpen_compl _ hxC
  have hd : 0 < dist s.1 s.2 := dist_pos.2 (hne s hs)
  refine ⟨min r₁ (η * dist s.1 s.2), lt_min hr₁ (mul_pos hη hd), ?_⟩
  intro z hz s' hs' ν hν hzν
  have hss : s' = s := by
    by_contra h
    have hzC : z ∈ C := mem_iUnion₂.2 ⟨s', Finset.mem_erase.2 ⟨h, hs'⟩, by
      rw [← hzν, segment_eq_image_lineMap]; exact ⟨ν, hν, rfl⟩⟩
    exact hball (ball_subset_ball (min_le_left _ _) hz) hzC
  subst hss
  refine ⟨rfl, ?_⟩
  have h1 : dist z (AffineMap.lineMap s'.1 s'.2 a) < η * dist s'.1 s'.2 :=
    lt_of_lt_of_le hz (min_le_right _ _)
  rw [← hzν, dist_lineMap_lineMap, Real.dist_eq] at h1
  exact lt_of_mul_lt_mul_right h1 hd.le

end Decomp

/-! ### Reading off a ladder -/

section Ladder

variable {G : Set E} {S : Finset (E × E)} {y : E → List ℝ} {ev : E × E → Option (ℕ × ℝ × ℝ)}

theorem IsLadder.ne (hL : IsLadder G S y ev) : ∀ s ∈ S, s.1 ≠ s.2 := hL.1

theorem IsLadder.G_eq (hL : IsLadder G S y ev) : G = ⋃ s ∈ S, segment ℝ s.1 s.2 := hL.2.1

theorem IsLadder.dis (hL : IsLadder G S y ev) : PairwiseEndpoints S := hL.2.2.1

theorem IsLadder.evOK (hL : IsLadder G S y ev) {s : E × E} (hs : s ∈ S) :
    EvOK (y s.1).length (ev s) := by
  rcases he : ev s with _ | ⟨m, lam, h⟩
  · trivial
  · obtain ⟨-, h1, h2, h3, -⟩ := hL.2.2.2.2.2 s hs m lam h he
    exact ⟨h1, h2, h3.1, h3.2⟩

theorem IsLadder.eJ2_eq (hL : IsLadder G S y ev) {s : E × E} (hs : s ∈ S) :
    eJ2 (y s.1).length (ev s) = (y s.2).length := by
  rcases he : ev s with _ | ⟨m, lam, h⟩
  · exact hL.2.2.2.2.1 s hs he
  · exact (hL.2.2.2.2.2 s hs m lam h he).1.symm

theorem IsLadder.piece_subset (hL : IsLadder G S y ev) {s : E × E} (hs : s ∈ S) (i : ℕ) :
    ladderPiece y s (ev s) i ⊆ G ×ˢ Icc 0 1 := by
  refine (ladderPiece_subset (hL.evOK hs) (fun t ht => Ioo_subset_Icc_self
    ((hL.2.2.2.1 s hs).2.2.1 t ht)) (fun t ht => Ioo_subset_Icc_self
    ((hL.2.2.2.1 s hs).2.2.2 t ht)) (fun m lam h he => Ioo_subset_Icc_self
    (hL.2.2.2.2.2 s hs m lam h he).2.2.2.2)).trans ?_
  exact prod_mono (segment_subset_of_mem hL.G_eq hs) subset_rfl

/-- The points of `αᵢ`. -/
def ladderAlphaSet (S : Finset (E × E)) (y : E → List ℝ) (ev : E × E → Option (ℕ × ℝ × ℝ))
    (i : ℕ) : Set (E × ℝ) :=
  ⋃ s ∈ S, ladderAlpha y s (ev s) i

/-- The gaps of the `i`-th sheet with ends in `αᵢ`. -/
def gapA (S : Finset (E × E)) (y : E → List ℝ) (ev : E × E → Option (ℕ × ℝ × ℝ)) (i : ℕ) :
    Set E :=
  ⋃ s ∈ S, AffineMap.lineMap s.1 s.2 '' eQA (y s.1).length (ev s) i

/-- The gaps of the `i`-th sheet with ends in `αᵢ₊₁`. -/
def gapB (S : Finset (E × E)) (y : E → List ℝ) (ev : E × E → Option (ℕ × ℝ × ℝ)) (i : ℕ) :
    Set E :=
  ⋃ s ∈ S, AffineMap.lineMap s.1 s.2 '' eQB (y s.1).length (ev s) i

theorem image_fst_ladderSheet (hL : IsLadder G S y ev) (i : ℕ) :
    Prod.fst '' ladderSheet S y ev i =
      ⋃ s ∈ S, AffineMap.lineMap s.1 s.2 '' eP (y s.1).length (ev s) i := by
  simp only [ladderSheet, image_iUnion₂]
  exact iUnion₂_congr fun s hs => image_fst_ladderPiece (hL.evOK hs)

theorem image_fst_ladderAlphaSet (i : ℕ) :
    Prod.fst '' ladderAlphaSet S y ev i =
      ⋃ s ∈ S, AffineMap.lineMap s.1 s.2 '' eA (y s.1).length (ev s) i := by
  simp only [ladderAlphaSet, image_iUnion₂]
  exact iUnion₂_congr fun s _ => image_fst_ladderAlpha _ _ _ _

theorem mem_image_fst_ladderSheet (hL : IsLadder G S y ev) {i : ℕ} {z : E} :
    z ∈ Prod.fst '' ladderSheet S y ev i ↔
      ∃ s ∈ S, ∃ μ ∈ eP (y s.1).length (ev s) i, AffineMap.lineMap s.1 s.2 μ = z := by
  rw [image_fst_ladderSheet hL]
  simp only [mem_iUnion₂, mem_image, exists_prop]

theorem ladderSheet_subset (hL : IsLadder G S y ev) (i : ℕ) :
    ladderSheet S y ev i ⊆ G ×ˢ Icc 0 1 :=
  iUnion₂_subset fun _ hs => hL.piece_subset hs i

/-- (S1): `π` is injective on a sheet. -/
theorem injOn_fst_ladderSheet (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) :
    InjOn Prod.fst (ladderSheet S y ev i) := by
  intro p hp q hq hpq
  obtain ⟨s, hs, hps⟩ := mem_iUnion₂.1 hp
  obtain ⟨s', hs', hqs⟩ := mem_iUnion₂.1 hq
  by_cases hss : s = s'
  · subst hss
    exact injOn_fst_ladderPiece (hL.ne s hs) (hL.evOK hs) hi hps hqs hpq
  · have hpseg : p.1 ∈ segment ℝ s.1 s.2 := by
      have := ladderPiece_subset (hL.evOK hs) (i := i) (fun t ht => Ioo_subset_Icc_self
        ((hL.2.2.2.1 s hs).2.2.1 t ht)) (fun t ht => Ioo_subset_Icc_self
        ((hL.2.2.2.1 s hs).2.2.2 t ht)) (fun m lam h he => Ioo_subset_Icc_self
        (hL.2.2.2.2.2 s hs m lam h he).2.2.2.2) hps
      exact this.1
    have hqseg : q.1 ∈ segment ℝ s'.1 s'.2 := by
      have := ladderPiece_subset (hL.evOK hs') (i := i) (fun t ht => Ioo_subset_Icc_self
        ((hL.2.2.2.1 s' hs').2.2.1 t ht)) (fun t ht => Ioo_subset_Icc_self
        ((hL.2.2.2.1 s' hs').2.2.2 t ht)) (fun m lam h he => Ioo_subset_Icc_self
        (hL.2.2.2.2.2 s' hs' m lam h he).2.2.2.2) hqs
      exact this.1
    rw [hpq] at hpseg
    obtain ⟨h1, h2⟩ := hL.dis s hs s' hs' hss ⟨hpseg, hqseg⟩
    have hval : ∀ v : E, ((v = s.1 ∨ v = s.2) ∧ (v = s'.1 ∨ v = s'.2)) → q.1 = v →
        p = (v, ladderY y v i) ∧ q = (v, ladderY y v i) := by
      rintro v ⟨hv1, hv2⟩ hqv
      constructor
      · rcases hv1 with rfl | rfl
        · exact ladderPiece_snd_of_fst (hL.ne s hs) (hL.evOK hs) hps (hpq.trans hqv)
        · exact ladderPiece_snd_of_snd (hL.ne s hs) (hL.evOK hs) hps (hpq.trans hqv)
      · rcases hv2 with rfl | rfl
        · exact ladderPiece_snd_of_fst (hL.ne s' hs') (hL.evOK hs') hqs hqv
        · exact ladderPiece_snd_of_snd (hL.ne s' hs') (hL.evOK hs') hqs hqv
    have hv : (q.1 = s.1 ∨ q.1 = s.2) ∧ (q.1 = s'.1 ∨ q.1 = s'.2) := by
      refine ⟨?_, ?_⟩
      · rcases h1 with h | h
        · exact Or.inl h
        · exact Or.inr (Set.mem_singleton_iff.1 h)
      · rcases h2 with h | h
        · exact Or.inl h
        · exact Or.inr (Set.mem_singleton_iff.1 h)
    obtain ⟨e1, e2⟩ := hval q.1 hv rfl
    rw [e1, e2]

theorem IsLadder.isPLGraph (hL : IsLadder G S y ev) : IsPLGraph G :=
  ⟨S, hL.ne, hL.G_eq, hL.dis⟩

theorem isCompact_ladderSheet (S : Finset (E × E)) (y : E → List ℝ)
    (ev : E × E → Option (ℕ × ℝ × ℝ)) (i : ℕ) : IsCompact (ladderSheet S y ev i) :=
  S.isCompact_biUnion fun s _ => isCompact_ladderPiece y s (ev s) i

theorem isCompact_image_fst_ladderSheet (S : Finset (E × E)) (y : E → List ℝ)
    (ev : E × E → Option (ℕ × ℝ × ℝ)) (i : ℕ) : IsCompact (Prod.fst '' ladderSheet S y ev i) :=
  (isCompact_ladderSheet S y ev i).image continuous_fst

theorem isPLGraph_image_fst_ladderSheet (hL : IsLadder G S y ev) (i : ℕ) :
    IsPLGraph (Prod.fst '' ladderSheet S y ev i) := by
  rw [image_fst_ladderSheet hL]
  have := IsPLGraph.biUnion_finite (s := (S : Set (E × E))) S.finite_toSet
    (f := fun s => AffineMap.lineMap s.1 s.2 '' eP (y s.1).length (ev s) i)
    fun s hs => isPLGraph_image_eP (hL.ne s hs) (hL.evOK hs)
  simpa using this

/-- (S1): each sheet is straight. -/
theorem isStraight_ladderSheet (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) :
    IsStraight G (ladderSheet S y ev i) :=
  ⟨ladderSheet_subset hL i, (isCompact_ladderSheet S y ev i).isClosed,
    injOn_fst_ladderSheet hL hi, isPLGraph_image_fst_ladderSheet hL i⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem length_le_ladderHeight {s : E × E} (hs : s ∈ S) :
    (y s.1).length ≤ ladderHeight S y ∧ (y s.2).length ≤ ladderHeight S y := by
  have := Finset.le_sup (f := fun s : E × E => max (y s.1).length (y s.2).length) hs
  exact ⟨(le_max_left _ _).trans this, (le_max_right _ _).trans this⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem exists_ladderHeight (hS : S.Nonempty) :
    ∃ s ∈ S, ladderHeight S y = max (y s.1).length (y s.2).length :=
  Finset.exists_mem_eq_sup S hS _

theorem odd_ladderHeight (hL : IsLadder G S y ev) (hS : S.Nonempty) : Odd (ladderHeight S y) := by
  obtain ⟨s, hs, h⟩ := exists_ladderHeight (y := y) hS
  rw [h]
  rcases le_total (y s.1).length (y s.2).length with h' | h'
  · rw [max_eq_right h']; exact (hL.2.2.2.1 s hs).2.1
  · rw [max_eq_left h']; exact (hL.2.2.2.1 s hs).1

/-- (S1): the sheets of index `1, …, k` are non-empty. -/
theorem ladderSheet_nonempty (hL : IsLadder G S y ev) (hS : S.Nonempty) {i : ℕ} (hi : 1 ≤ i)
    (hik : i ≤ ladderHeight S y) : (ladderSheet S y ev i).Nonempty := by
  obtain ⟨s, hs, h⟩ := exists_ladderHeight (y := y) hS
  rw [h] at hik
  rcases le_total (y s.2).length (y s.1).length with h' | h'
  · rw [max_eq_left h'] at hik
    exact ⟨_, mem_iUnion₂.2 ⟨s, hs, mem_ladderPiece_fst (hL.evOK hs) hi hik⟩⟩
  · rw [max_eq_right h'] at hik
    exact ⟨_, mem_iUnion₂.2 ⟨s, hs, mem_ladderPiece_snd (hL.evOK hs) hi
      (by rw [hL.eJ2_eq hs]; exact hik)⟩⟩

theorem eQA_sub {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) : eQA j e i ⊆ Icc 0 1 := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp only [eQA]; split_ifs <;> simp
  · obtain ⟨hm, hmj, hl0, hl1⟩ := he
    have hz := zU_pos (j := j) (m := m) hl0
    have r1 := zz_lr j m lam (i - 1)
    have r2 := zz_lr j m lam (i - 2)
    have l1 := zzL_ge (j := j) (m := m) hl0 (i - 1)
    simp only [eQA, wQA]
    refine union_subset (union_subset (union_subset (union_subset ?_ ?_) ?_) ?_) ?_ <;>
      split_ifs with c <;> try exact empty_subset _
    · have := zz_lam (j := j) (m := m) (c := i - 2) hl0 (by omega) (by omega)
      exact Icc_subset_Icc (by linarith) (by linarith)
    · exact Icc_subset_Icc (by linarith) hl1.le
    · exact Icc_subset_Icc le_rfl hl1.le
    · have := zz_lam (j := j) (m := m) (c := i - 2) hl0 (by omega) (by omega)
      exact Icc_subset_Icc le_rfl (by linarith)
    · exact subset_rfl

theorem eQB_sub {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) : eQB j e i ⊆ Icc 0 1 := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp only [eQB]; split_ifs <;> simp
  · obtain ⟨hm, hmj, hl0, hl1⟩ := he
    have hz := zU_pos (j := j) (m := m) hl0
    have r0 := zz_lr j m lam i
    have r1 := zz_lr j m lam (i - 1)
    have l0 := zzL_ge (j := j) (m := m) hl0 i
    simp only [eQB, wQB]
    refine union_subset (union_subset (union_subset (union_subset ?_ ?_) ?_) ?_) ?_ <;>
      split_ifs with c <;> try exact empty_subset _
    · have := zz_lam (j := j) (m := m) (c := i - 1) hl0 (by omega) (by omega)
      exact Icc_subset_Icc (by linarith) (by linarith)
    · exact Icc_subset_Icc (by linarith) hl1.le
    · exact Icc_subset_Icc le_rfl hl1.le
    · have := zz_lam (j := j) (m := m) (c := i - 1) hl0 (by omega) (by omega)
      exact Icc_subset_Icc le_rfl (by linarith)
    · exact subset_rfl

theorem eA_sub_Ioo {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) : eA j e i ⊆ Ioo 0 1 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rcases e with _ | ⟨m, lam, h⟩
    · simp [eA]
    · have := he.1
      simp only [eA, wA]
      simp (disch := omega) only [if_neg, union_empty]
      exact empty_subset _
  · exact e_A_sub he hi

theorem isClosed_gapA (S : Finset (E × E)) (y : E → List ℝ) (ev : E × E → Option (ℕ × ℝ × ℝ))
    (i : ℕ) : IsClosed (gapA S y ev i) :=
  (S.isCompact_biUnion fun _ _ => (isCompact_eQA _ _ i).image
    AffineMap.lineMap_continuous).isClosed

theorem isClosed_gapB (S : Finset (E × E)) (y : E → List ℝ) (ev : E × E → Option (ℕ × ℝ × ℝ))
    (i : ℕ) : IsClosed (gapB S y ev i) :=
  (S.isCompact_biUnion fun _ _ => (isCompact_eQB _ _ i).image
    AffineMap.lineMap_continuous).isClosed

theorem gapA_subset (hL : IsLadder G S y ev) (i : ℕ) : gapA S y ev i ⊆ G := by
  refine iUnion₂_subset fun s hs => ?_
  rintro _ ⟨a, ha, rfl⟩
  exact lineMap_mem_of_mem hL.G_eq hs (eQA_sub (hL.evOK hs) ha)

theorem gapB_subset (hL : IsLadder G S y ev) (i : ℕ) : gapB S y ev i ⊆ G := by
  refine iUnion₂_subset fun s hs => ?_
  rintro _ ⟨a, ha, rfl⟩
  exact lineMap_mem_of_mem hL.G_eq hs (eQB_sub (hL.evOK hs) ha)

/-- Every point of `G` is on the sheet or in a gap. -/
theorem subset_sheet_union_gaps (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) :
    G ⊆ Prod.fst '' ladderSheet S y ev i ∪ gapA S y ev i ∪ gapB S y ev i := by
  intro x hx
  obtain ⟨s, hs, μ, hμ, rfl⟩ := exists_param_of_mem hL.G_eq hx
  rcases e_cover (hL.evOK hs) hi hμ with (h | h) | h
  · exact Or.inl (Or.inl ((mem_image_fst_ladderSheet hL).2 ⟨s, hs, μ, h, rfl⟩))
  · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨s, hs, μ, h, rfl⟩))
  · exact Or.inr (mem_iUnion₂.2 ⟨s, hs, μ, h, rfl⟩)

/-- A common point of two different edges is an end of both. -/
theorem vertex_of_two (hL : IsLadder G S y ev) {s s' : E × E} (hs : s ∈ S) (hs' : s' ∈ S)
    (hss : s ≠ s') {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : AffineMap.lineMap s.1 s.2 a = AffineMap.lineMap s'.1 s'.2 b) :
    ((a = 0 ∧ AffineMap.lineMap s.1 s.2 a = s.1) ∨ (a = 1 ∧ AffineMap.lineMap s.1 s.2 a = s.2)) ∧
    ((b = 0 ∧ AffineMap.lineMap s.1 s.2 a = s'.1) ∨
      (b = 1 ∧ AffineMap.lineMap s.1 s.2 a = s'.2)) := by
  have h1 : AffineMap.lineMap s.1 s.2 a ∈ segment ℝ s.1 s.2 := by
    rw [segment_eq_image_lineMap]; exact ⟨a, ha, rfl⟩
  have h2 : AffineMap.lineMap s.1 s.2 a ∈ segment ℝ s'.1 s'.2 := by
    rw [hab, segment_eq_image_lineMap]; exact ⟨b, hb, rfl⟩
  obtain ⟨k1, k2⟩ := hL.dis s hs s' hs' hss ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · rcases k1 with k | k
    · exact Or.inl ⟨(lineMap_eq_left_iff (hL.ne s hs)).1 k, k⟩
    · have k := Set.mem_singleton_iff.1 k
      exact Or.inr ⟨(lineMap_eq_right_iff (hL.ne s hs)).1 k, k⟩
  · rcases k2 with k | k
    · exact Or.inl ⟨(lineMap_eq_left_iff (hL.ne s' hs')).1 (hab ▸ k), k⟩
    · have k := Set.mem_singleton_iff.1 k
      exact Or.inr ⟨(lineMap_eq_right_iff (hL.ne s' hs')).1 (hab ▸ k), k⟩

/-- The label of a vertex in a gap of the `i`-th sheet: `j(v) < i`, and the parity of `i - j(v)`
is `0` for `gapA`, `1` for `gapB`. -/
theorem vertex_label (hL : IsLadder G S y ev) {s : E × E} (hs : s ∈ S) {i : ℕ} (hi : 1 ≤ i)
    {a : ℝ} {v : E} (hv : (a = 0 ∧ v = s.1) ∨ (a = 1 ∧ v = s.2)) :
    (a ∈ eQA (y s.1).length (ev s) i → (y v).length < i ∧ (i - (y v).length) % 2 = 0) ∧
    (a ∈ eQB (y s.1).length (ev s) i → (y v).length < i ∧ (i - (y v).length) % 2 = 1) ∧
    (a ∈ eP (y s.1).length (ev s) i → i ≤ (y v).length) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := e_ends (hL.evOK hs) hi
  rw [hL.eJ2_eq hs] at h3 h4 h6
  rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨h1, h2, h5⟩
  · exact ⟨h3, h4, h6⟩

theorem vertex_label_of_two (hL : IsLadder G S y ev) {s s' : E × E} (hs : s ∈ S) (hs' : s' ∈ S)
    (hss : s ≠ s') {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : AffineMap.lineMap s.1 s.2 a = AffineMap.lineMap s'.1 s'.2 b) {i : ℕ} (hi : 1 ≤ i) :
    ∃ v : E,
    (a ∈ eQA (y s.1).length (ev s) i → (y v).length < i ∧ (i - (y v).length) % 2 = 0) ∧
    (a ∈ eQB (y s.1).length (ev s) i → (y v).length < i ∧ (i - (y v).length) % 2 = 1) ∧
    (a ∈ eP (y s.1).length (ev s) i → i ≤ (y v).length) ∧
    (b ∈ eQA (y s'.1).length (ev s') i → (y v).length < i ∧ (i - (y v).length) % 2 = 0) ∧
    (b ∈ eQB (y s'.1).length (ev s') i → (y v).length < i ∧ (i - (y v).length) % 2 = 1) ∧
    (b ∈ eP (y s'.1).length (ev s') i → i ≤ (y v).length) := by
  obtain ⟨k1, k2⟩ := vertex_of_two hL hs hs' hss ha hb hab
  have l1 := vertex_label hL hs hi (a := a) (v := AffineMap.lineMap s.1 s.2 a) (by
    rcases k1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨e1, e2⟩
    · exact Or.inr ⟨e1, e2⟩)
  have l2 := vertex_label hL hs' hi (a := b) (v := AffineMap.lineMap s.1 s.2 a) (by
    rcases k2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨e1, e2⟩
    · exact Or.inr ⟨e1, e2⟩)
  exact ⟨_, l1.1, l1.2.1, l1.2.2, l2.1, l2.2.1, l2.2.2⟩

theorem gap_inter_sheet (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) {x : E} {s s' : E × E}
    (hs : s ∈ S) (hs' : s' ∈ S) {a b : ℝ} (ha : a ∈ eQA (y s.1).length (ev s) i ∪
      eQB (y s.1).length (ev s) i)
    (hb : b ∈ eP (y s'.1).length (ev s') i) (hxa : AffineMap.lineMap s.1 s.2 a = x)
    (hxb : AffineMap.lineMap s'.1 s'.2 b = x) : s = s' ∧ a = b := by
  have hb' := e_P_sub (hL.evOK hs') hb
  have ha' : a ∈ Icc (0 : ℝ) 1 := by
    rcases ha with ha | ha
    · exact eQA_sub (hL.evOK hs) ha
    · exact eQB_sub (hL.evOK hs) ha
  by_cases hss : s = s'
  · subst hss
    exact ⟨rfl, lineMap_inj (hL.ne s hs) (hxa.trans hxb.symm)⟩
  · exfalso
    obtain ⟨v, l1, l2, -, -, -, l6⟩ :=
      vertex_label_of_two hL hs hs' hss ha' hb' (hxa.trans hxb.symm) hi
    have := l6 hb
    rcases ha with ha | ha
    · have := (l1 ha).1; omega
    · have := (l2 ha).1; omega

theorem gapA_inter_sheet (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) :
    gapA S y ev i ∩ Prod.fst '' ladderSheet S y ev i ⊆ Prod.fst '' ladderAlphaSet S y ev i := by
  rintro x ⟨hxA, hxT⟩
  obtain ⟨s, hs, a, ha, hxa⟩ := mem_iUnion₂.1 hxA
  obtain ⟨s', hs', b, hb, hxb⟩ := (mem_image_fst_ladderSheet hL).1 hxT
  obtain ⟨rfl, rfl⟩ := gap_inter_sheet hL hi hs hs' (Or.inl ha) hb hxa hxb
  rw [image_fst_ladderAlphaSet]
  exact mem_iUnion₂.2 ⟨s, hs, a, e_QA_P (hL.evOK hs) hi ⟨ha, hb⟩, hxa⟩

theorem gapB_inter_sheet (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) :
    gapB S y ev i ∩ Prod.fst '' ladderSheet S y ev i ⊆
      Prod.fst '' ladderAlphaSet S y ev (i + 1) := by
  rintro x ⟨hxB, hxT⟩
  obtain ⟨s, hs, a, ha, hxa⟩ := mem_iUnion₂.1 hxB
  obtain ⟨s', hs', b, hb, hxb⟩ := (mem_image_fst_ladderSheet hL).1 hxT
  obtain ⟨rfl, rfl⟩ := gap_inter_sheet hL hi hs hs' (Or.inr ha) hb hxa hxb
  rw [image_fst_ladderAlphaSet]
  exact mem_iUnion₂.2 ⟨s, hs, a, e_QB_P (hL.evOK hs) hi ⟨ha, hb⟩, hxa⟩

theorem disjoint_gapA_gapB (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) :
    Disjoint (gapA S y ev i) (gapB S y ev i) := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  obtain ⟨s, hs, a, ha, hxa⟩ := mem_iUnion₂.1 hxA
  obtain ⟨s', hs', b, hb, hxb⟩ := mem_iUnion₂.1 hxB
  by_cases hss : s = s'
  · subst hss
    have := lineMap_inj (hL.ne s hs) (hxa.trans hxb.symm)
    subst this
    exact Set.disjoint_left.1 (e_QA_QB (hL.evOK hs) hi) ha hb
  · obtain ⟨v, l1, -, -, -, l5, -⟩ := vertex_label_of_two hL hs hs' hss
      (eQA_sub (hL.evOK hs) ha) (eQB_sub (hL.evOK hs') hb) (hxa.trans hxb.symm) hi
    have := (l1 ha).2
    have := (l5 hb).2
    omega

end Ladder

end

end HPC.HO16
