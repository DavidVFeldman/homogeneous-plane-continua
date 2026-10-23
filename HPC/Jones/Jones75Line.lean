import HPC.Jones.Jones75Arcs

/-!
# Jones 1975 I (batch 189), part 2: arc components and lines

Commission 189 §2.3–§2.4 (skeleton `Jones75A.lean` §2, split).

* arc components (`arcComp`): an equivalence relation, preserved by homeomorphisms;
* rays: the arcs from `x` containing a fixed arc `C₀ = [x, c]` form a chain (`rayArcs_total`),
  with no largest member (`JonesSetting.extend`) and a countable cofinal subsequence
  (`JonesSetting.exists_ray_seq`), cut into consecutive pieces (`RayChain`);
* gluing countably many arcs along `ℤ` into a continuous injection of `ℝ` (`glue_line`);
* **every arc component is a line** (`JonesSetting.exists_line`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen unitInterval

section General

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]

/-- The arc component of `x`: `x` together with every arc containing `x`. -/
def arcComp (x : Y) : Set Y :=
  insert x (⋃₀ {A | (∃ a b : Y, TArc a b A) ∧ x ∈ A})

/-- A *line*: a continuous injection of `ℝ` onto an arc component. -/
def IsLine (ℓ : ℝ → Y) : Prop :=
  Continuous ℓ ∧ Function.Injective ℓ ∧ range ℓ = arcComp (ℓ 0)

/-! ### Arc components -/

omit [CompactSpace Y] in
theorem mem_arcComp_self (x : Y) : x ∈ arcComp x := mem_insert _ _

omit [CompactSpace Y] in
theorem subset_arcComp {x a b : Y} {A : Set Y} (hA : TArc a b A) (hx : x ∈ A) :
    A ⊆ arcComp x := fun _ hy => Or.inr ⟨A, ⟨⟨a, b, hA⟩, hx⟩, hy⟩

omit [CompactSpace Y] in
theorem mem_arcComp_comm {x y : Y} (h : y ∈ arcComp x) : x ∈ arcComp y := by
  rcases h with rfl | ⟨A, ⟨⟨a, b, hA⟩, hx⟩, hy⟩
  · exact mem_arcComp_self _
  · exact subset_arcComp hA hy hx

omit [CompactSpace Y] in
theorem mem_arcComp_trans {x y z : Y} (hxy : y ∈ arcComp x) (hyz : z ∈ arcComp y) :
    z ∈ arcComp x := by
  rcases hxy with rfl | ⟨A, ⟨⟨a, b, hA⟩, hxA⟩, hyA⟩
  · exact hyz
  rcases hyz with rfl | ⟨B, ⟨⟨a', b', hB⟩, hyB⟩, hzB⟩
  · exact subset_arcComp hA hxA hyA
  by_cases hxz : x = z
  · subst hxz; exact mem_arcComp_self _
  by_cases hxy : x = y
  · subst hxy; exact subset_arcComp hB hyB hzB
  by_cases hyz : y = z
  · subst hyz; exact subset_arcComp hA hxA hyA
  obtain ⟨A', -, hA'⟩ := hA.exists_sub hxA hyA hxy
  obtain ⟨B', -, hB'⟩ := hB.exists_sub hyB hzB hyz
  obtain ⟨G, -, hG⟩ := hA'.join hB'.symm ⟨y, hA'.right_mem, hB'.left_mem⟩ hxz
  exact subset_arcComp hG hG.left_mem hG.right_mem

omit [CompactSpace Y] in
theorem arcComp_eq_of_mem {x y : Y} (h : y ∈ arcComp x) : arcComp y = arcComp x :=
  Subset.antisymm (fun _ hz => mem_arcComp_trans h hz)
    (fun _ hz => mem_arcComp_trans (mem_arcComp_comm h) hz)

omit [CompactSpace Y] in
theorem image_arcComp_subset (h : Y ≃ₜ Y) (x : Y) : h '' arcComp x ⊆ arcComp (h x) := by
  rintro _ ⟨y, hy | ⟨A, ⟨⟨a, b, hA⟩, hxA⟩, hyA⟩, rfl⟩
  · rw [hy]; exact mem_arcComp_self _
  · exact subset_arcComp (TArc.image_homeomorph hA h) (mem_image_of_mem h hxA) (mem_image_of_mem h hyA)

omit [CompactSpace Y] in
theorem image_arcComp (h : Y ≃ₜ Y) (x : Y) : h '' arcComp x = arcComp (h x) := by
  refine Subset.antisymm (image_arcComp_subset h x) fun z hz => ?_
  have := image_arcComp_subset h.symm (h x) (mem_image_of_mem _ hz)
  rw [Homeomorph.symm_apply_apply] at this
  exact ⟨_, this, h.apply_symm_apply z⟩

/-! ### Rays -/

/-- The arcs from `x` containing `C₀`. -/
def rayArcs (x : Y) (C₀ : Set Y) : Set (Set Y) := {B | (∃ e, TArc x e B) ∧ C₀ ⊆ B}

theorem JonesSetting.rayArcs_total (S : JonesSetting Y) {x c : Y} {C₀ : Set Y}
    (hC₀ : TArc x c C₀) {B B' : Set Y} (hB : B ∈ rayArcs x C₀) (hB' : B' ∈ rayArcs x C₀) :
    B ⊆ B' ∨ B' ⊆ B := by
  obtain ⟨⟨e, he⟩, h⟩ := hB
  obtain ⟨⟨e', he'⟩, h'⟩ := hB'
  exact S.nested he he' ⟨x, ⟨h hC₀.left_mem, h' hC₀.left_mem⟩, c,
    ⟨h hC₀.right_mem, h' hC₀.right_mem⟩, hC₀.ne⟩

/-- **No largest arc** (commission 189 §2.3, step 2): an arc from `x` extends beyond its other
end point. -/
theorem JonesSetting.extend (S : JonesSetting Y) {x e : Y} {B : Set Y} (hB : TArc x e B) :
    ∃ e' B', TArc x e' B' ∧ B ⊆ B' ∧ B ≠ B' := by
  obtain ⟨u, v, A, hA, heA, heu, hev⟩ := S.exists_arc_through e
  obtain ⟨p, q, hW⟩ := S.union_arc hB hA ⟨e, hB.right_mem, heA⟩
  obtain ⟨-, f, hf, hW, -, -⟩ := hW
  obtain ⟨s, t, hst, hBs, hBe⟩ := sub_arc_param hf hB (hW ▸ subset_union_left)
  obtain ⟨s₂, t₂, hst₂, hAs, hAe⟩ := sub_arc_param hf hA (hW ▸ subset_union_right)
  obtain ⟨τ, hτ, hτe⟩ : e ∈ f '' Icc s₂ t₂ := hAs ▸ heA
  have hne₁ : f s₂ ≠ e := by
    rcases hAe with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · exact heu.symm
    · exact hev.symm
  have hne₂ : f t₂ ≠ e := by
    rcases hAe with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1]
    · exact hev.symm
    · exact heu.symm
  have hτ₁ : s₂ < τ := lt_of_le_of_ne hτ.1 fun h => hne₁ (h ▸ hτe)
  have hτ₂ : τ < t₂ := lt_of_le_of_ne hτ.2 fun h => hne₂ (h ▸ hτe)
  rcases hBe with ⟨hx, he⟩ | ⟨he, hx⟩
  · have ht : t = τ := hf.injective (he.trans hτe.symm)
    refine ⟨f t₂, f '' Icc s t₂, hx ▸ TArc.image_Icc hf (hst.trans (ht ▸ hτ₂)), ?_, ?_⟩
    · rw [hBs]; exact image_mono (Icc_subset_Icc le_rfl (ht ▸ hτ₂).le)
    · intro h
      have : f t₂ ∈ B := h ▸ ⟨t₂, ⟨(hst.trans (ht ▸ hτ₂)).le, le_rfl⟩, rfl⟩
      rw [hBs] at this
      obtain ⟨w, hw, hwe⟩ := this
      have := hf.injective hwe
      exact absurd hw.2 (by rw [this, not_le, ht]; exact hτ₂)
  · have hs : s = τ := hf.injective (he.trans hτe.symm)
    refine ⟨f s₂, f '' Icc s₂ t, hx ▸ (TArc.image_Icc hf ((hs ▸ hτ₁).trans hst)).symm, ?_, ?_⟩
    · rw [hBs]; exact image_mono (Icc_subset_Icc (hs ▸ hτ₁).le le_rfl)
    · intro h
      have : f s₂ ∈ B := h ▸ ⟨s₂, ⟨le_rfl, ((hs ▸ hτ₁).trans hst).le⟩, rfl⟩
      rw [hBs] at this
      obtain ⟨w, hw, hwe⟩ := this
      have := hf.injective hwe
      exact absurd hw.1 (by rw [this, not_le, hs]; exact hτ₁)

/-- **Countable cofinality** (commission 189 §2.3, step 3): a strictly increasing sequence of
arcs from `x` containing `C₀`, whose union is the ray. -/
theorem JonesSetting.exists_ray_seq (S : JonesSetting Y) {x c : Y} {C₀ : Set Y}
    (hC₀ : TArc x c C₀) :
    ∃ B : ℕ → Set Y, (∀ n, B n ∈ rayArcs x C₀) ∧ (∀ n, B n ⊆ B (n + 1)) ∧
      (∀ n, B n ≠ B (n + 1)) ∧ ⋃ n, B n = ⋃₀ rayArcs x C₀ := by
  set 𝒞 := rayArcs x C₀ with h𝒞
  have hext : ∀ B ∈ 𝒞, ∃ B' ∈ 𝒞, B ⊆ B' ∧ B ≠ B' := fun B ⟨⟨e, he⟩, h⟩ => by
    obtain ⟨e', B', h', hBB', hne⟩ := S.extend he
    exact ⟨B', ⟨⟨e', h'⟩, h.trans hBB'⟩, hBB', hne⟩
  choose! ext hext𝒞 hextsub hextne using hext
  have hC₀𝒞 : C₀ ∈ 𝒞 := ⟨⟨c, hC₀⟩, subset_rfl⟩
  obtain ⟨D, hDR, hDc, hRD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (⋃₀ 𝒞)).exists_countable_dense_subset
  have hDne : D.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have := hRD (subset_sUnion_of_mem hC₀𝒞 hC₀.left_mem)
    rw [h, closure_empty] at this
    exact this
  obtain ⟨d, rfl⟩ := hDc.exists_eq_range hDne
  have hE : ∀ n, ∃ E ∈ 𝒞, d n ∈ E := fun n => hDR (mem_range_self n)
  choose E hE𝒞 hdE using hE
  have hmax : ∀ B ∈ 𝒞, ∀ B' ∈ 𝒞, ∃ B'' ∈ 𝒞, B ⊆ B'' ∧ B' ⊆ B'' := fun B hB B' hB' => by
    rcases S.rayArcs_total hC₀ hB hB' with h | h
    · exact ⟨B', hB', h, subset_rfl⟩
    · exact ⟨B, hB, subset_rfl, h⟩
  choose! mx hmx𝒞 hmx1 hmx2 using hmax
  let B : ℕ → Set Y := fun n => Nat.rec (ext C₀) (fun n Bn => ext (mx Bn (E n))) n
  have hBs : ∀ n, B (n + 1) = ext (mx (B n) (E n)) := fun n => rfl
  have hB𝒞 : ∀ n, B n ∈ 𝒞 := by
    intro n
    induction n with
    | zero => exact hext𝒞 _ hC₀𝒞
    | succ n ih => rw [hBs]; exact hext𝒞 _ (hmx𝒞 _ ih _ (hE𝒞 n))
  have hmx𝒞' : ∀ n, mx (B n) (E n) ∈ 𝒞 := fun n => hmx𝒞 _ (hB𝒞 n) _ (hE𝒞 n)
  have hBsub : ∀ n, B n ⊆ B (n + 1) := fun n => by
    rw [hBs]; exact (hmx1 _ (hB𝒞 n) _ (hE𝒞 n)).trans (hextsub _ (hmx𝒞' n))
  have hBne : ∀ n, B n ≠ B (n + 1) := fun n h => by
    apply hextne _ (hmx𝒞' n)
    refine Subset.antisymm (hextsub _ (hmx𝒞' n)) ?_
    rw [← hBs, ← h]
    exact hmx1 _ (hB𝒞 n) _ (hE𝒞 n)
  have hEsub : ∀ n, E n ⊆ B (n + 1) := fun n => by
    rw [hBs]; exact (hmx2 _ (hB𝒞 n) _ (hE𝒞 n)).trans (hextsub _ (hmx𝒞' n))
  have hcof : ∀ B' ∈ 𝒞, ∃ n, B' ⊆ B n := by
    intro B' hB'
    by_contra hno
    push_neg at hno
    have hle : ∀ n, B n ⊆ B' := fun n =>
      (S.rayArcs_total hC₀ hB' (hB𝒞 n)).resolve_left (hno n)
    obtain ⟨⟨e', he'⟩, -⟩ := hB'
    have hdB' : range d ⊆ B' := by
      rintro _ ⟨n, rfl⟩; exact hle (n + 1) (hEsub n (hdE n))
    have hR : ⋃₀ 𝒞 ⊆ B' := hRD.trans (closure_minimal hdB' he'.isClosed)
    exact hextne B' ⟨⟨e', he'⟩, (hle 0).trans' (hext𝒞 _ hC₀𝒞).2⟩
      (Subset.antisymm (hextsub _ ⟨⟨e', he'⟩, (hle 0).trans' (hext𝒞 _ hC₀𝒞).2⟩)
        ((subset_sUnion_of_mem (hext𝒞 _ ⟨⟨e', he'⟩, (hle 0).trans' (hext𝒞 _ hC₀𝒞).2⟩)).trans
          hR))
  refine ⟨B, hB𝒞, hBsub, hBne, Subset.antisymm (iUnion_subset fun n =>
    subset_sUnion_of_mem (hB𝒞 n)) ?_⟩
  rintro y ⟨B', hB', hyB'⟩
  obtain ⟨n, hn⟩ := hcof B' hB'
  exact mem_iUnion.2 ⟨n, hn hyB'⟩

omit [CompactSpace Y] in
/-- The piece of a larger arc from `x` beyond a smaller one. -/
theorem piece_of_sub {x e e' : Y} {B B' : Set Y} (hB : TArc x e B) (hB' : TArc x e' B')
    (hsub : B ⊆ B') (hne : B ≠ B') :
    ∃ φ : I → Y, IsEmbedding φ ∧ φ 0 = e ∧ φ 1 = e' ∧ range φ ∩ B = {e} ∧
      B' = B ∪ range φ := by
  obtain ⟨-, f, hf, rfl, hf0, hf1⟩ := hB'
  obtain ⟨s, t, hst, hBst, hend⟩ := sub_arc_param hf hB hsub
  have hs : s = 0 ∧ f t = e := by
    rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hf.injective (h1.trans hf0.symm), h2⟩
    · exfalso
      have := hf.injective (h2.trans hf0.symm)
      exact absurd hst (by rw [this]; exact not_lt.mpr nonneg')
  obtain ⟨rfl, hft⟩ := hs
  have ht1 : t < 1 := lt_of_le_of_ne le_one' fun h => hne (by rw [hBst, h, image_Icc_zero_one])
  have hemb : IsEmbedding (affI t 1 ht1.le) :=
    ((continuous_affI t 1 ht1.le).isClosedEmbedding (affI_injective ht1)).isEmbedding
  have hrange : range (f ∘ affI t 1 ht1.le) = f '' Icc t 1 := by
    rw [range_comp, range_affI ht1]
  refine ⟨f ∘ affI t 1 ht1.le, hf.comp hemb, ?_, ?_, ?_, ?_⟩
  · simp only [Function.comp, affI_zero, hft]
  · simp only [Function.comp, affI_one, hf1]
  · rw [hrange, hBst, inter_comm, image_Icc_inter_image_Icc hf.injective hst.le ht1.le, hft]
  · rw [hrange, hBst, ← image_union, Icc_union_Icc_eq_Icc hst.le ht1.le, image_Icc_zero_one]

/-- A ray cut into consecutive arcs `φ k` from `q k` to `q (k + 1)`, starting at `x`. -/
structure RayChain (Y : Type*) [TopologicalSpace Y] (x : Y) where
  q : ℕ → Y
  φ : ℕ → I → Y
  emb : ∀ k, IsEmbedding (φ k)
  start : ∀ k, φ k 0 = q k
  stop : ∀ k, φ k 1 = q (k + 1)
  q0 : q 0 = x
  disj : ∀ j k, j < k → range (φ j) ∩ range (φ k) ⊆ {q k}
  disj2 : ∀ j k, j + 1 < k → range (φ j) ∩ range (φ k) = ∅

omit [CompactSpace Y] in
theorem RayChain.eq_zero_of_mem {x : Y} (ρ : RayChain Y x) {k : ℕ} (h : ρ.q 0 ∈ range (ρ.φ k)) :
    k = 0 := by
  by_contra hk
  have h0 : ρ.q 0 ∈ range (ρ.φ 0) := ⟨0, ρ.start 0⟩
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1 : k = 1 := by omega
    subst hk1
    have := ρ.disj 0 1 (by omega) ⟨h0, h⟩
    rw [mem_singleton_iff, ← ρ.start 0, ← ρ.stop 0] at this
    have := congrArg Subtype.val ((ρ.emb 0).injective this)
    simp at this
  · have := ρ.disj2 0 k (by omega)
    exact (eq_empty_iff_forall_notMem.mp this) _ ⟨h0, h⟩

omit [CompactSpace Y] in
theorem RayChain.param_eq_one {x : Y} (ρ : RayChain Y x) {j k : ℕ} (hjk : j < k) {u v : I}
    (h : ρ.φ j u = ρ.φ k v) : k = j + 1 ∧ u = 1 := by
  have hmem := ρ.disj j k hjk ⟨⟨u, rfl⟩, ⟨v, h.symm⟩⟩
  have hk : k = j + 1 := by
    by_contra hne
    have := ρ.disj2 j k (by omega)
    exact (eq_empty_iff_forall_notMem.mp this) _ ⟨⟨u, rfl⟩, ⟨v, h.symm⟩⟩
  refine ⟨hk, ?_⟩
  subst hk
  rw [mem_singleton_iff, ← ρ.stop j] at hmem
  exact (ρ.emb j).injective hmem

theorem JonesSetting.exists_rayChain (S : JonesSetting Y) {x c : Y} {C₀ : Set Y}
    (hC₀ : TArc x c C₀) : ∃ ρ : RayChain Y x, ⋃ k, range (ρ.φ k) = ⋃₀ rayArcs x C₀ := by
  obtain ⟨B, hB𝒞, hBsub, hBne, hBun⟩ := S.exists_ray_seq hC₀
  have hp : ∀ n, ∃ e, TArc x e (B n) := fun n => (hB𝒞 n).1
  choose p hp using hp
  obtain ⟨-, φ₀, hφ₀, hφ₀r, hφ₀0, hφ₀1⟩ := hp 0
  have hpc : ∀ n, ∃ ψ : I → Y, IsEmbedding ψ ∧ ψ 0 = p n ∧ ψ 1 = p (n + 1) ∧
      range ψ ∩ B n = {p n} ∧ B (n + 1) = B n ∪ range ψ := fun n =>
    piece_of_sub (hp n) (hp (n + 1)) (hBsub n) (hBne n)
  choose ψ hψ hψ0 hψ1 hψint hψun using hpc
  have hmono : Monotone B := monotone_nat_of_le_succ hBsub
  let q : ℕ → Y := fun k => Nat.casesOn k x p
  let φ : ℕ → I → Y := fun k => Nat.casesOn k φ₀ ψ
  have hφB : ∀ k n, k ≤ n → range (φ k) ⊆ B n := by
    intro k n hkn
    cases k with
    | zero => exact hφ₀r.symm ▸ hmono (Nat.zero_le n)
    | succ m =>
      exact (hψun m ▸ subset_union_right : range (ψ m) ⊆ B (m + 1)).trans (hmono hkn)
  have hint : ∀ m, range (φ (m + 1)) ∩ B m = {q (m + 1)} := hψint
  have hdisj : ∀ j k, j < k → range (φ j) ∩ range (φ k) ⊆ {q k} := by
    intro j k hjk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [← hint m, inter_comm]
    exact inter_subset_inter_right _ (hφB j m (by omega))
  refine ⟨⟨q, φ, fun k => ?_, fun k => ?_, fun k => ?_, rfl, hdisj, fun j k hjk => ?_⟩, ?_⟩
  · cases k with
    | zero => exact hφ₀
    | succ m => exact hψ m
  · cases k with
    | zero => exact hφ₀0
    | succ m => exact hψ0 m
  · cases k with
    | zero => exact hφ₀1
    | succ m => exact hψ1 m
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [eq_empty_iff_forall_notMem]
    intro z hz
    have hzq := hdisj j (m + 2) (by omega) hz
    rw [mem_singleton_iff] at hzq
    have h1 : q (m + 2) ∈ range (φ (m + 1)) ∩ B m :=
      ⟨⟨1, hψ1 m⟩, hφB j m (by omega) (hzq ▸ hz.1)⟩
    rw [hint m, mem_singleton_iff] at h1
    have h2 : ψ m 1 = ψ m 0 := (hψ1 m).trans (h1.trans (hψ0 m).symm)
    have := congrArg Subtype.val ((hψ m).injective h2)
    simp at this
  · rw [← hBun]
    apply Subset.antisymm
    · exact iUnion_subset fun k => (hφB k k le_rfl).trans (subset_iUnion B k)
    · refine iUnion_subset fun n => ?_
      induction n with
      | zero => exact hφ₀r ▸ subset_iUnion (fun k => range (φ k)) 0
      | succ m ih =>
        rw [hψun m]
        exact union_subset ih (subset_iUnion (fun k => range (φ k)) (m + 1))

/-- The two rays at `x` meet only in `x`. -/
theorem JonesSetting.ray_inter (S : JonesSetting Y) {x a c : Y} {Γ₁ Γ₂ : Set Y}
    (h₁ : TArc x a Γ₁) (h₂ : TArc x c Γ₂) (hint : Γ₁ ∩ Γ₂ = {x}) :
    ⋃₀ rayArcs x Γ₂ ∩ ⋃₀ rayArcs x Γ₁ ⊆ {x} := by
  rintro y ⟨⟨B, ⟨⟨e, he⟩, hB2⟩, hyB⟩, ⟨B', ⟨⟨e', he'⟩, hB1⟩, hyB'⟩⟩
  by_contra hyx
  have hint' : Γ₂ ∩ Γ₁ = {x} := by rw [inter_comm]; exact hint
  rcases S.nested he he' ⟨x, ⟨he.left_mem, he'.left_mem⟩, y, ⟨hyB, hyB'⟩,
    fun h => hyx h.symm⟩ with h | h
  · exact TArc.no_fork he'.symm h₂ h₁ hint' (hB2.trans h) hB1
  · exact TArc.no_fork he.symm h₂ h₁ hint' hB2 (hB1.trans h)

/-- The arc component of `x` is the union of the two rays at `x`. -/
theorem JonesSetting.arcComp_eq_rays (S : JonesSetting Y) {x a c : Y} {Γ₁ Γ₂ : Set Y}
    (h₁ : TArc x a Γ₁) (h₂ : TArc x c Γ₂) (hint : Γ₁ ∩ Γ₂ = {x}) :
    arcComp x = ⋃₀ rayArcs x Γ₂ ∪ ⋃₀ rayArcs x Γ₁ := by
  apply Subset.antisymm
  · intro y hy
    have hx2 : x ∈ ⋃₀ rayArcs x Γ₂ := ⟨Γ₂, ⟨⟨c, h₂⟩, subset_rfl⟩, h₂.left_mem⟩
    rcases hy with rfl | ⟨E, ⟨⟨u, v, hE⟩, hxE⟩, hyE⟩
    · exact Or.inl hx2
    by_cases hyx : y = x
    · subst hyx; exact Or.inl hx2
    obtain ⟨G, -, hG⟩ := hE.exists_sub hxE hyE (Ne.symm hyx)
    have key : ∀ {e : Y} {Γ : Set Y}, TArc x e Γ → (G ∩ Γ).Nontrivial →
        y ∈ ⋃₀ rayArcs x Γ := by
      intro e Γ hΓ hnt
      rcases S.nested hG hΓ hnt with h | h
      · exact ⟨Γ, ⟨⟨e, hΓ⟩, subset_rfl⟩, h hG.right_mem⟩
      · exact ⟨G, ⟨⟨y, hG⟩, h⟩, hG.right_mem⟩
    by_cases n2 : (G ∩ Γ₂).Nontrivial
    · exact Or.inl (key h₂ n2)
    by_cases n1 : (G ∩ Γ₁).Nontrivial
    · exact Or.inr (key h₁ n1)
    exfalso
    have sub : ∀ {Γ : Set Y}, x ∈ Γ → ¬ (G ∩ Γ).Nontrivial → G ∩ Γ ⊆ {x} := fun hx hn z hz => by
      by_contra hzx
      exact hn ⟨x, ⟨hG.left_mem, hx⟩, z, hz, fun e => hzx e.symm⟩
    exact S.no_three_arms hG h₁ h₂ hG.left_mem h₁.left_mem h₂.left_mem (sub h₁.left_mem n1)
      (sub h₂.left_mem n2) hint.subset
  · rintro y (⟨B, ⟨⟨e, he⟩, -⟩, hyB⟩ | ⟨B, ⟨⟨e, he⟩, -⟩, hyB⟩) <;>
      exact subset_arcComp he he.left_mem hyB

end General

/-! ### Gluing arcs along `ℤ` -/

section Glue

variable {Z : Type*} [TopologicalSpace Z]

/-- The fractional part, as a point of `[0, 1]`. -/
noncomputable def fractI (s : ℝ) : I := ⟨Int.fract s, Int.fract_nonneg s, (Int.fract_lt_one s).le⟩

/-- The map `s ↦ Φ ⌊s⌋ (fract s)`. -/
noncomputable def rayGlue (Φ : ℤ → I → Z) (s : ℝ) : Z := Φ ⌊s⌋ (fractI s)

omit [TopologicalSpace Z] in
theorem rayGlue_eqOn {Φ : ℤ → I → Z} (hlink : ∀ k, Φ k 1 = Φ (k + 1) 0) (k : ℤ) :
    EqOn (rayGlue Φ) (fun s => Φ k (projIcc 0 1 zero_le_one (s - k))) (Icc (k : ℝ) (k + 1)) := by
  intro s hs
  rcases lt_or_eq_of_le hs.2 with h | h
  · have hfl : ⌊s⌋ = k := Int.floor_eq_iff.mpr ⟨hs.1, h⟩
    simp only [rayGlue, hfl]
    congr 1
    rw [projIcc_of_mem zero_le_one ⟨by linarith [hs.1], by linarith⟩]
    apply Subtype.ext
    simp [fractI, Int.fract, hfl]
  · have hfl : ⌊s⌋ = k + 1 := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    simp only [rayGlue, hfl]
    have h0 : fractI s = 0 := by
      apply Subtype.ext
      simp only [fractI, Int.fract, hfl, Set.Icc.coe_zero]
      push_cast; linarith
    have h1 : projIcc (0 : ℝ) 1 zero_le_one (s - k) = 1 := by
      rw [show s - k = 1 by linarith]; exact projIcc_right _
    rw [h0, h1, hlink]

theorem continuous_rayGlue {Φ : ℤ → I → Z} (hc : ∀ k, Continuous (Φ k))
    (hlink : ∀ k, Φ k 1 = Φ (k + 1) 0) : Continuous (rayGlue Φ) := by
  refine LocallyFinite.continuous (f := fun k : ℤ => Icc (k : ℝ) (k + 1)) ?_ ?_
    (fun _ => isClosed_Icc) fun k => ?_
  · intro s
    refine ⟨Ioo (s - 1) (s + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    refine (Set.finite_Icc (⌊s⌋ - 2) (⌊s⌋ + 2)).subset ?_
    rintro k ⟨z, ⟨hz1, hz2⟩, hz3, hz4⟩
    have h1 := Int.floor_le s
    have h2 := Int.lt_floor_add_one s
    have hk1 : (k : ℝ) < ⌊s⌋ + 2 := by linarith
    have hk2 : (⌊s⌋ : ℝ) - 2 < k := by linarith
    constructor
    · have : ⌊s⌋ - 2 < k := by exact_mod_cast hk2
      omega
    · have : k < ⌊s⌋ + 2 := by exact_mod_cast hk1
      omega
  · refine eq_univ_of_forall fun s => mem_iUnion.2 ⟨⌊s⌋, Int.floor_le s, (Int.lt_floor_add_one s).le⟩
  · refine ContinuousOn.congr ?_ (rayGlue_eqOn hlink k)
    exact ((hc k).comp (continuous_projIcc.comp (continuous_id.sub continuous_const))).continuousOn

omit [TopologicalSpace Z] in
theorem rayGlue_injective {Φ : ℤ → I → Z} (hinj : ∀ k, Function.Injective (Φ k))
    (hdisj : ∀ j k, j < k → ∀ u v, Φ j u = Φ k v → u = 1) : Function.Injective (rayGlue Φ) := by
  have hlt : ∀ s : ℝ, fractI s ≠ 1 := fun s h => by
    have := congrArg Subtype.val h
    simp only [fractI, Set.Icc.coe_one] at this
    exact (Int.fract_lt_one s).ne this
  intro s t h
  simp only [rayGlue] at h
  rcases lt_trichotomy ⌊s⌋ ⌊t⌋ with hst | hst | hst
  · exact absurd (hdisj _ _ hst _ _ h) (hlt s)
  · rw [hst] at h
    have := congrArg Subtype.val (hinj _ h)
    simp only [fractI] at this
    rw [← Int.floor_add_fract s, ← Int.floor_add_fract t, this, hst]
  · exact absurd (hdisj _ _ hst _ _ h.symm) (hlt t)

omit [TopologicalSpace Z] in
theorem range_rayGlue {Φ : ℤ → I → Z} (hlink : ∀ k, Φ k 1 = Φ (k + 1) 0) :
    range (rayGlue Φ) = ⋃ k, range (Φ k) := by
  apply Subset.antisymm
  · rintro _ ⟨s, rfl⟩; exact mem_iUnion.2 ⟨⌊s⌋, mem_range_self _⟩
  · intro z hz
    obtain ⟨k, u, rfl⟩ := mem_iUnion.1 hz
    rcases lt_or_eq_of_le (le_one' : u ≤ 1) with hu | rfl
    · have hu' : (u : ℝ) < 1 := hu
      have hfl : ⌊(k : ℝ) + u⌋ = k := Int.floor_eq_iff.mpr ⟨by linarith [u.2.1], by linarith⟩
      refine ⟨k + u, ?_⟩
      simp only [rayGlue, hfl]
      congr 1
      apply Subtype.ext
      simp [fractI, Int.fract, hfl]
    · refine ⟨(k : ℝ) + 1, ?_⟩
      have hfl : ⌊(k : ℝ) + 1⌋ = k + 1 := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      simp only [rayGlue, hfl, hlink]
      congr 1
      apply Subtype.ext
      simp [fractI, Int.fract, hfl]

omit [TopologicalSpace Z] in
theorem rayGlue_zero (Φ : ℤ → I → Z) : rayGlue Φ 0 = Φ 0 0 := by
  simp only [rayGlue, Int.floor_zero]
  congr 1
  apply Subtype.ext
  simp [fractI]

end Glue

/-! ### Every arc component is a line -/

section General

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]

/-- The pieces of the line: the forward ray for `k ≥ 0`, the backward ray reversed for `k < 0`. -/
noncomputable def lineΦ (φp φm : ℕ → I → Y) (k : ℤ) : I → Y :=
  if 0 ≤ k then φp k.toNat else φm (-k - 1).toNat ∘ σ

/-- **§2.3, every arc component is a line** (Jones (d), first sentence, for both rays at a
point). -/
theorem JonesSetting.exists_line (S : JonesSetting Y) (x : Y) :
    ∃ ℓ : ℝ → Y, IsLine ℓ ∧ ℓ 0 = x := by
  obtain ⟨a, c, A, hA, hxA, hxa, hxc⟩ := S.exists_arc_through x
  obtain ⟨Γ₁, Γ₂, h₁, h₂, -, hint⟩ := hA.split hxA hxa hxc
  obtain ⟨ρp, hρp⟩ := S.exists_rayChain h₂
  obtain ⟨ρm, hρm⟩ := S.exists_rayChain h₁.symm
  have hcap := S.ray_inter h₁.symm h₂ hint
  have hcomp := S.arcComp_eq_rays h₁.symm h₂ hint
  set Φ := lineΦ ρp.φ ρm.φ with hΦ
  have hΦp : ∀ n : ℕ, Φ n = ρp.φ n := fun n => by
    simp only [hΦ, lineΦ, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]
  have hΦm : ∀ m : ℕ, Φ (-(m : ℤ) - 1) = ρm.φ m ∘ σ := fun m => by
    simp only [hΦ, lineΦ, if_neg (show ¬ (0 : ℤ) ≤ -(m : ℤ) - 1 by omega),
      show -(-(m : ℤ) - 1) - 1 = m by ring, Int.toNat_natCast]
  have hcases : ∀ k : ℤ, (∃ n : ℕ, k = n) ∨ ∃ m : ℕ, k = -(m : ℤ) - 1 := fun k => by
    rcases le_or_gt 0 k with h | h
    · exact Or.inl ⟨k.toNat, by omega⟩
    · exact Or.inr ⟨(-k - 1).toNat, by omega⟩
  have hlink : ∀ k, Φ k 1 = Φ (k + 1) 0 := by
    intro k
    rcases hcases k with ⟨n, rfl⟩ | ⟨m, rfl⟩
    · rw [hΦp, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, hΦp, ρp.stop,
        ρp.start]
    · rcases m with _ | m
      · rw [show -((0 : ℕ) : ℤ) - 1 + 1 = ((0 : ℕ) : ℤ) by simp, hΦp, hΦm, Function.comp,
          symm_one, ρm.start, ρp.start, ρm.q0, ρp.q0]
      · rw [show -((m + 1 : ℕ) : ℤ) - 1 + 1 = -(m : ℤ) - 1 by push_cast; ring, hΦm, hΦm,
          Function.comp, Function.comp, symm_one, symm_zero, ρm.start, ρm.stop]
  have hcont : ∀ k, Continuous (Φ k) := by
    intro k
    rcases hcases k with ⟨n, rfl⟩ | ⟨m, rfl⟩
    · rw [hΦp]; exact (ρp.emb n).continuous
    · rw [hΦm]; exact (ρm.emb m).continuous.comp continuous_symm
  have hinj : ∀ k, Function.Injective (Φ k) := by
    intro k
    rcases hcases k with ⟨n, rfl⟩ | ⟨m, rfl⟩
    · rw [hΦp]; exact (ρp.emb n).injective
    · rw [hΦm]; exact (ρm.emb m).injective.comp symm_involutive.injective
  have hrange : ∀ k, range (Φ k) ⊆ ⋃₀ rayArcs x Γ₂ ∪ ⋃₀ rayArcs x Γ₁ := by
    intro k
    rcases hcases k with ⟨n, rfl⟩ | ⟨m, rfl⟩
    · rw [hΦp, ← hρp]; exact (subset_iUnion (fun k => range (ρp.φ k)) n).trans subset_union_left
    · rw [hΦm, range_comp_symm, ← hρm]
      exact (subset_iUnion (fun k => range (ρm.φ k)) m).trans subset_union_right
  have hdisj : ∀ j k, j < k → ∀ u v, Φ j u = Φ k v → u = 1 := by
    intro j k hjk u v h
    rcases hcases j with ⟨a', rfl⟩ | ⟨a', rfl⟩ <;> rcases hcases k with ⟨b', rfl⟩ | ⟨b', rfl⟩
    · rw [hΦp, hΦp] at h
      exact (ρp.param_eq_one (by exact_mod_cast hjk) h).2
    · exfalso; omega
    · rw [hΦm, hΦp] at h
      have hx : Φ (-(a' : ℤ) - 1) u ∈ ⋃₀ rayArcs x Γ₂ ∩ ⋃₀ rayArcs x Γ₁ := by
        refine ⟨?_, ?_⟩
        · rw [hΦm, h, ← hρp]; exact mem_iUnion.2 ⟨b', mem_range_self _⟩
        · rw [hΦm, ← hρm]; exact mem_iUnion.2 ⟨a', mem_range_self _⟩
      have hxq := hcap hx
      rw [hΦm, mem_singleton_iff] at hxq
      have hxq' : ρm.φ a' (σ u) = ρm.q 0 := by rw [ρm.q0]; exact hxq
      have ha0 : a' = 0 := ρm.eq_zero_of_mem ⟨_, hxq'⟩
      subst ha0
      rw [← ρm.start] at hxq'
      have := (ρm.emb 0).injective hxq'
      rw [← symm_one] at this
      exact symm_involutive.injective this
    · rw [hΦm, hΦm] at h
      have hba : b' < a' := by omega
      obtain ⟨-, h1⟩ := ρm.param_eq_one hba h.symm
      have := ρm.param_eq_one hba h.symm
      obtain ⟨rfl, -⟩ := this
      have hq := ρm.disj b' (b' + 1) (by omega) ⟨⟨σ v, rfl⟩, ⟨σ u, h⟩⟩
      rw [mem_singleton_iff, ← ρm.start] at hq
      have := (ρm.emb _).injective (h.trans hq)
      rw [← symm_one] at this
      exact symm_involutive.injective this
  refine ⟨rayGlue Φ, ⟨continuous_rayGlue hcont hlink, rayGlue_injective hinj hdisj, ?_⟩, ?_⟩
  · have h0 : rayGlue Φ 0 = x := by
      rw [rayGlue_zero, show (0 : ℤ) = ((0 : ℕ) : ℤ) by simp, hΦp, ρp.start, ρp.q0]
    rw [h0, range_rayGlue hlink, hcomp]
    apply Subset.antisymm (iUnion_subset hrange)
    rintro y (hy | hy)
    · rw [← hρp] at hy
      obtain ⟨n, hn⟩ := mem_iUnion.1 hy
      exact mem_iUnion.2 ⟨n, (hΦp n).symm ▸ hn⟩
    · rw [← hρm] at hy
      obtain ⟨m, hm⟩ := mem_iUnion.1 hy
      refine mem_iUnion.2 ⟨-(m : ℤ) - 1, ?_⟩
      rw [hΦm, range_comp_symm]; exact hm
  · rw [rayGlue_zero, show (0 : ℤ) = ((0 : ℕ) : ℤ) by simp, hΦp, ρp.start, ρp.q0]

end General

end HPC.Hagopian
