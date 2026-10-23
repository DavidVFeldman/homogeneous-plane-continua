import HPC.BJ59.ChainOps

/-!
# Batch 198, library: the chain of Bing–Jones's Theorem 3, assembled

Bing–Jones's construction (p. 175), repaired at both junctions (commission 198, §6). Given a fine
chain `F = f₀, …, f_{N−1}` covering the space, two coarse chains `E₀` (the links meeting `g₀`,
oriented so that `f_v` lies in its last link) and `E₁` (the links meeting `g₁`, oriented so that
`f_w` lies in its first link), with `A = f₀ + ⋯ + f_v` covered by `E₀` and `B = f_w + ⋯ + f_{N−1}`
covered by `E₁`, the chain is

  `A·e⁰₀, …, A·e⁰_{n₀−1}, A·e⁰_{n₀} + f_{v+1}, f_{v+2}, …, f_{w−2}, B·e¹₀ + f_{w−1}, B·e¹₁, …`.

Bing–Jones's chain has `A·e⁰_{n₀}` and `f_{v+1}` as separate links; but `A·e⁰_{n₀−1}` can meet
`f_{v+1}` (through `f_v`). Since `f_{v+1}` meets `A` only inside `f_v ⊆ e⁰_{n₀}`, merging `f_{v+1}`
into the last `A`-link repairs the chain; likewise at the other junction.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane

variable {X : Type*} [MetricSpace X]

/-! ### Unions of initial and final segments of a chain -/

/-- `f₀ + ⋯ + f_α`. -/
def lowUnion {N : ℕ} (F : Chain X N) (α : ℕ) : Set X := ⋃ (k : Fin N) (_ : (k : ℕ) ≤ α), F.link k

/-- `f_β + ⋯ + f_{N−1}`. -/
def highUnion {N : ℕ} (F : Chain X N) (β : ℕ) : Set X := ⋃ (k : Fin N) (_ : β ≤ (k : ℕ)), F.link k

theorem isOpen_lowUnion {N : ℕ} (F : Chain X N) (α : ℕ) : IsOpen (lowUnion F α) :=
  isOpen_iUnion fun k => isOpen_iUnion fun _ => F.isOpen k

theorem isOpen_highUnion {N : ℕ} (F : Chain X N) (β : ℕ) : IsOpen (highUnion F β) :=
  isOpen_iUnion fun k => isOpen_iUnion fun _ => F.isOpen k

theorem link_subset_lowUnion {N : ℕ} (F : Chain X N) {k : Fin N} {α : ℕ} (h : (k : ℕ) ≤ α) :
    F.link k ⊆ lowUnion F α := fun _ hx => mem_iUnion₂.2 ⟨k, h, hx⟩

theorem link_subset_highUnion {N : ℕ} (F : Chain X N) {k : Fin N} {β : ℕ} (h : β ≤ (k : ℕ)) :
    F.link k ⊆ highUnion F β := fun _ hx => mem_iUnion₂.2 ⟨k, h, hx⟩

theorem lowUnion_mono {N : ℕ} (F : Chain X N) {α α' : ℕ} (h : α ≤ α') :
    lowUnion F α ⊆ lowUnion F α' := fun _ hx => by
  obtain ⟨k, hk, hx⟩ := mem_iUnion₂.1 hx; exact mem_iUnion₂.2 ⟨k, hk.trans h, hx⟩

theorem highUnion_anti {N : ℕ} (F : Chain X N) {β β' : ℕ} (h : β' ≤ β) :
    highUnion F β ⊆ highUnion F β' := fun _ hx => by
  obtain ⟨k, hk, hx⟩ := mem_iUnion₂.1 hx; exact mem_iUnion₂.2 ⟨k, h.trans hk, hx⟩

theorem disjoint_lowUnion_highUnion {N : ℕ} (F : Chain X N) {α β : ℕ} (h : α + 2 ≤ β) :
    Disjoint (lowUnion F α) (highUnion F β) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx
  obtain ⟨k', hk', hxk'⟩ := mem_iUnion₂.1 hx'
  have := (F.adjacent k k').1 ⟨x, hxk, hxk'⟩
  omega

/-- `f_{v+1}` meets `f₀ + ⋯ + f_v` only inside `f_v`. -/
theorem link_inter_lowUnion_subset {N : ℕ} (F : Chain X N) {v : ℕ} {k kv : Fin N}
    (hk : (k : ℕ) = v + 1) (hkv : (kv : ℕ) = v) : F.link k ∩ lowUnion F v ⊆ F.link kv := by
  rintro x ⟨hx, hx'⟩
  obtain ⟨l, hl, hxl⟩ := mem_iUnion₂.1 hx'
  have := (F.adjacent k l).1 ⟨x, hx, hxl⟩
  have : l = kv := Fin.ext (by omega)
  exact this ▸ hxl

/-- `f_{w−1}` meets `f_w + ⋯` only inside `f_w`. -/
theorem link_inter_highUnion_subset {N : ℕ} (F : Chain X N) {w : ℕ} {k kw : Fin N}
    (hk : (k : ℕ) + 1 = w) (hkw : (kw : ℕ) = w) : F.link k ∩ highUnion F w ⊆ F.link kw := by
  rintro x ⟨hx, hx'⟩
  obtain ⟨l, hl, hxl⟩ := mem_iUnion₂.1 hx'
  have := (F.adjacent k l).1 ⟨x, hx, hxl⟩
  have : l = kw := Fin.ext (by omega)
  exact this ▸ hxl

/-! ### `ε`-chains -/

theorem isEpsChain_mono {n : ℕ} {D : Chain X n} {ε ε' : ℝ} (h : IsEpsChain D ε) (hε : ε ≤ ε') :
    IsEpsChain D ε' := fun i => ⟨(h i).1, (h i).2.trans_le hε⟩

theorem isEpsChain_reverse {n : ℕ} {D : Chain X n} {ε : ℝ} (h : IsEpsChain D ε) :
    IsEpsChain D.reverse ε := fun i => h (Fin.rev i)

theorem isEpsChain_sub {n : ℕ} {D : Chain X n} {ε : ℝ} (h : IsEpsChain D ε) (i j : Fin n)
    (hij : i ≤ j) : IsEpsChain (D.sub i j hij) ε := fun _ => h _

theorem isEpsChain_chainRestrict {n : ℕ} {D : Chain X n} {ε : ℝ} (h : IsEpsChain D ε) (S : Set X)
    (hS hne hc) : IsEpsChain (chainRestrict D S hS hne hc) ε := fun i =>
  ⟨(h i).1.subset inter_subset_right,
    (diam_mono inter_subset_right (h i).1).trans_lt (h i).2⟩

theorem isEpsChain_chainMergeLast {n : ℕ} {D : Chain X (n + 1)} {δ γ : ℝ} (h : IsEpsChain D δ)
    {T : Set X} (hTb : Bornology.IsBounded T) (hTd : diam T < γ)
    (hmeet : (D.link (Fin.last n) ∩ T).Nonempty) (hT hdisj) :
    IsEpsChain (chainMergeLast D T hT hdisj) (δ + γ) := by
  have hγ : 0 < γ := lt_of_le_of_lt diam_nonneg hTd
  intro k
  by_cases hk : k = Fin.last n
  · subst hk
    rw [chainMergeLast_link_last]
    refine ⟨(h _).1.union hTb, ?_⟩
    calc diam (D.link (Fin.last n) ∪ T) ≤ diam (D.link (Fin.last n)) + diam T :=
          diam_union' hmeet
      _ < δ + γ := add_lt_add (h _).2 hTd
  · rw [chainMergeLast_link_of_ne _ _ _ _ hk]
    exact ⟨(h k).1, (h k).2.trans (by linarith)⟩

/-! ### Restricting to the links meeting a connected set -/

theorem restrict_hne {n : ℕ} {E : Chain X n} {g S : Set X} (hgS : g ⊆ S)
    (hgE : ∀ k, (g ∩ E.link k).Nonempty) (k : Fin n) : (S ∩ E.link k).Nonempty := by
  obtain ⟨x, hxg, hxk⟩ := hgE k; exact ⟨x, hgS hxg, hxk⟩

theorem restrict_hc {n : ℕ} {E : Chain X n} {g S : Set X} (hg : IsPreconnected g) (hgS : g ⊆ S)
    (hgU : g ⊆ E.union) (hgE : ∀ k, (g ∩ E.link k).Nonempty) (k k' : Fin n)
    (hk : (k' : ℕ) = k + 1) : (S ∩ (E.link k ∩ E.link k')).Nonempty := by
  have hk1 : (k : ℕ) + 1 < n := hk ▸ k'.isLt
  obtain ⟨x, hxg, hx⟩ := consec_meet E hg hgU hgE k hk1
  have e1 : k' = ⟨k + 1, hk1⟩ := Fin.ext hk
  subst e1
  exact ⟨x, hgS hxg, hx⟩

/-! ### The assembly -/

/-- **The chain of Theorem 3, assembled** (see the module docstring). -/
theorem chain_assembly {N n₀ n₁ : ℕ} (F : Chain X N) (E₀ : Chain X (n₀ + 1))
    (E₁ : Chain X (n₁ + 1)) {g₀ g₁ : Set X} {δ γ ε : ℝ} (hF : IsEpsChain F γ)
    (hFcov : univ ⊆ F.union) (hE₀ : IsEpsChain E₀ δ) (hE₁ : IsEpsChain E₁ δ) (hδγ : δ + γ ≤ ε)
    (hγ : γ ≤ ε) {v w : ℕ} (hvw : v + 4 ≤ w) (hwN : w < N)
    (hA : lowUnion F v ⊆ E₀.union) (hB : highUnion F w ⊆ E₁.union)
    (hv : ∀ k : Fin N, (k : ℕ) = v → F.link k ⊆ E₀.link (Fin.last n₀))
    (hw : ∀ k : Fin N, (k : ℕ) = w → F.link k ⊆ E₁.link 0)
    (hg₀ : IsPreconnected g₀) (hg₀A : g₀ ⊆ lowUnion F v) (hg₀E : ∀ k, (g₀ ∩ E₀.link k).Nonempty)
    (hg₁ : IsPreconnected g₁) (hg₁B : g₁ ⊆ highUnion F w)
    (hg₁E : ∀ k, (g₁ ∩ E₁.link k).Nonempty) :
    ∃ (m : ℕ) (D : Chain X (m + 1)), IsEpsChain D ε ∧ univ ⊆ D.union ∧
      (D.link 0 ∩ g₀).Nonempty ∧ (D.link (Fin.last m) ∩ g₁).Nonempty := by
  set A := lowUnion F v with hAdef
  set B := highUnion F w with hBdef
  have hδ : 0 ≤ δ := le_trans diam_nonneg (hE₀ 0).2.le
  -- indices
  set fv : Fin N := ⟨v, by omega⟩
  set fv1 : Fin N := ⟨v + 1, by omega⟩
  set fv2 : Fin N := ⟨v + 2, by omega⟩
  set fw2 : Fin N := ⟨w - 2, by omega⟩
  set fw1 : Fin N := ⟨w - 1, by omega⟩
  set fw : Fin N := ⟨w, hwN⟩
  have hadj : ∀ k k' : Fin N, (k' : ℕ) = k + 1 → (F.link k ∩ F.link k').Nonempty :=
    fun k k' h => (F.adjacent k k').2 (by omega)
  -- the `A`-part
  let PA := chainRestrict E₀ A (isOpen_lowUnion F v) (restrict_hne hg₀A hg₀E)
    (restrict_hc hg₀ hg₀A (hg₀A.trans hA) hg₀E)
  have hdisjA : ∀ k : Fin (n₀ + 1), (k : ℕ) + 2 ≤ n₀ → Disjoint (F.link fv1) (PA.link k) := by
    intro k hk
    rw [Set.disjoint_left]
    rintro x hx ⟨hxA, hxk⟩
    have hxv := link_inter_lowUnion_subset F (k := fv1) (kv := fv) rfl rfl ⟨hx, hxA⟩
    have := (E₀.adjacent (Fin.last n₀) k).1 ⟨x, hv fv rfl hxv, hxk⟩
    simp at this; omega
  let PA' := chainMergeLast PA (F.link fv1) (F.isOpen _) hdisjA
  have hPA'sub : ∀ a, PA'.link a ⊆ lowUnion F (v + 1) := fun a =>
    (chainMergeLast_link_subset _ _ _ _ a).trans (union_subset
      (inter_subset_left.trans (lowUnion_mono F (by omega))) (link_subset_lowUnion F le_rfl))
  have hPA'sub' : ∀ a, a ≠ Fin.last n₀ → PA'.link a ⊆ A := fun a ha => by
    rw [chainMergeLast_link_of_ne _ _ _ _ ha]; exact inter_subset_left
  -- the middle part
  have hv2w2 : fv2 ≤ fw2 := by rw [Fin.le_def]; simp [fv2, fw2]; omega
  let M := F.sub fv2 fw2 hv2w2
  have hMlink : ∀ b, M.link b = F.link ⟨v + 2 + b, by have := b.isLt; simp [fv2, fw2] at this; omega⟩ :=
    fun b => rfl
  have hMlen : (fw2 : ℕ) - fv2 + 1 = w - v - 3 := by simp [fv2, fw2]; omega
  have hMsub : ∀ b, M.link b ⊆ highUnion F (v + 2) ∩ lowUnion F (w - 2) := fun b => by
    rw [hMlink]
    have := b.isLt
    exact subset_inter (link_subset_highUnion F (by simp)) (link_subset_lowUnion F (by
      simp [fv2, fw2] at this ⊢; omega))
  have hMsub0 : ∀ b, b ≠ 0 → M.link b ⊆ highUnion F (v + 3) := fun b hb => by
    rw [hMlink]
    have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
    exact link_subset_highUnion F (by simp; omega)
  have hMsubL : ∀ b, b ≠ Fin.last _ → M.link b ⊆ lowUnion F (w - 3) := fun b hb => by
    rw [hMlink]
    have h1 : (b : ℕ) ≠ (fw2 : ℕ) - fv2 := fun h => hb (Fin.ext h)
    have h2 := b.isLt
    exact link_subset_lowUnion F (by simp [fv2, fw2] at h1 h2 ⊢; omega)
  have hmeet1 : (PA'.link (Fin.last n₀) ∩ M.link 0).Nonempty := by
    obtain ⟨x, hx1, hx2⟩ := hadj fv1 fv2 rfl
    refine ⟨x, ?_, ?_⟩
    · rw [chainMergeLast_link_last]; exact Or.inr hx1
    · rw [hMlink]; exact hx2
  have hdisj1 : ∀ a b, (a ≠ Fin.last n₀ ∨ b ≠ 0) → Disjoint (PA'.link a) (M.link b) := by
    rintro a b (ha | hb)
    · exact ((disjoint_lowUnion_highUnion F (le_refl (v + 2))).mono (hPA'sub' a ha)
        ((hMsub b).trans inter_subset_left))
    · exact (disjoint_lowUnion_highUnion F (by omega : v + 1 + 2 ≤ v + 3)).mono (hPA'sub a)
        (hMsub0 b hb)
  let D1 := chainAppend PA' M hmeet1 hdisj1
  -- the `B`-part
  let PB := chainRestrict E₁ B (isOpen_highUnion F w) (restrict_hne hg₁B hg₁E)
    (restrict_hc hg₁ hg₁B (hg₁B.trans hB) hg₁E)
  have hdisjB : ∀ k : Fin (n₁ + 1), (k : ℕ) + 2 ≤ n₁ →
      Disjoint (F.link fw1) (PB.reverse.link k) := by
    intro k hk
    rw [Set.disjoint_left]
    rintro x hx ⟨hxB, hxk⟩
    have hxw := link_inter_highUnion_subset F (k := fw1) (kw := fw) (by show w - 1 + 1 = w; omega) rfl
      ⟨hx, hxB⟩
    have := (E₁.adjacent 0 (Fin.rev k)).1 ⟨x, hw fw rfl hxw, hxk⟩
    simp [Fin.val_rev] at this; omega
  let PB'' := chainMergeLast PB.reverse (F.link fw1) (F.isOpen _) hdisjB
  let PB' := PB''.reverse
  have hPB'sub : ∀ b, PB'.link b ⊆ highUnion F (w - 1) := fun b => by
    show PB''.link (Fin.rev b) ⊆ _
    refine (chainMergeLast_link_subset _ _ _ _ _).trans (union_subset ?_ ?_)
    · exact inter_subset_left.trans (highUnion_anti F (by omega))
    · exact link_subset_highUnion F le_rfl
  have hPB'sub0 : ∀ b, b ≠ 0 → PB'.link b ⊆ B := fun b hb => by
    show PB''.link (Fin.rev b) ⊆ _
    have : Fin.rev b ≠ Fin.last n₁ := fun h => hb (by rw [← Fin.rev_rev b, h, Fin.rev_last])
    rw [chainMergeLast_link_of_ne _ _ _ _ this]
    exact inter_subset_left
  have hPB'0 : F.link fw1 ⊆ PB'.link 0 := by
    show F.link fw1 ⊆ PB''.link (Fin.rev 0)
    rw [Fin.rev_zero, chainMergeLast_link_last]; exact subset_union_right
  -- second junction
  have hD1last : ∀ a : Fin ((n₀ + 1) + ((fw2 : ℕ) - fv2 + 1)),
      (a : ℕ) = n₀ + 1 + ((fw2 : ℕ) - fv2) → D1.link a = F.link fw2 := by
    intro a ha
    have : a = Fin.natAdd (n₀ + 1) (Fin.last ((fw2 : ℕ) - fv2)) := Fin.ext (by simp; omega)
    subst this
    rw [chainAppend_link_right, hMlink]
    congr 1; ext; simp [fv2, fw2]; omega
  have hmeet2 : (D1.link (Fin.last _) ∩ PB'.link 0).Nonempty := by
    rw [hD1last _ (by simp [Nat.add_eq])]
    obtain ⟨x, hx1, hx2⟩ := hadj fw2 fw1 (by simp [fw1, fw2]; omega)
    exact ⟨x, hx1, hPB'0 hx2⟩
  have hD1sub : ∀ a, D1.link a ⊆ lowUnion F (w - 2) := fun a => by
    refine Fin.addCases (m := n₀ + 1) (n := (fw2 : ℕ) - fv2 + 1) (fun a => ?_) (fun b => ?_) a
    · rw [chainAppend_link_left]; exact (hPA'sub a).trans (lowUnion_mono F (by omega))
    · rw [chainAppend_link_right]; exact (hMsub b).trans inter_subset_right
  have hD1subL : ∀ a, a ≠ Fin.last _ → D1.link a ⊆ lowUnion F (w - 3) := fun a => by
    refine Fin.addCases (m := n₀ + 1) (n := (fw2 : ℕ) - fv2 + 1) (fun a ha => ?_)
      (fun b hb => ?_) a
    · rw [chainAppend_link_left]; exact (hPA'sub a).trans (lowUnion_mono F (by omega))
    · rw [chainAppend_link_right]
      refine hMsubL b fun hb' => hb ?_
      rw [hb']; exact Fin.ext (by simp [Nat.add_eq])
  have hdisj2 : ∀ a b, (a ≠ Fin.last _ ∨ b ≠ 0) → Disjoint (D1.link a) (PB'.link b) := by
    rintro a b (ha | hb)
    · exact (disjoint_lowUnion_highUnion F (by omega : w - 3 + 2 ≤ w - 1)).mono (hD1subL a ha)
        (hPB'sub b)
    · exact (disjoint_lowUnion_highUnion F (by omega : w - 2 + 2 ≤ w)).mono (hD1sub a)
        (hPB'sub0 b hb)
  let D := chainAppend D1 PB' hmeet2 hdisj2
  -- the properties
  have hPAeps : IsEpsChain PA' ε := by
    have h1 := isEpsChain_chainMergeLast (δ := δ) (γ := γ)
      (isEpsChain_chainRestrict hE₀ A _ _ _) (hF fv1).1 (hF fv1).2 (by
        obtain ⟨x, hx, hx'⟩ := hadj fv fv1 rfl
        exact ⟨x, ⟨link_subset_lowUnion F le_rfl hx, hv fv rfl hx⟩, hx'⟩) (F.isOpen _) hdisjA
    exact isEpsChain_mono h1 hδγ
  have hMeps : IsEpsChain M ε := isEpsChain_mono (isEpsChain_sub hF _ _ _) hγ
  have hPBeps : IsEpsChain PB' ε := by
    refine isEpsChain_reverse (isEpsChain_mono ?_ hδγ)
    refine isEpsChain_chainMergeLast (δ := δ) (γ := γ)
      (isEpsChain_reverse (isEpsChain_chainRestrict hE₁ B _ _ _)) (hF fw1).1 (hF fw1).2 ?_
      (F.isOpen _) hdisjB
    obtain ⟨x, hx, hx'⟩ := hadj fw1 fw (by show w = w - 1 + 1; omega)
    refine ⟨x, ?_, hx⟩
    show x ∈ PB.link (Fin.rev (Fin.last n₁))
    rw [Fin.rev_last]
    exact ⟨link_subset_highUnion F le_rfl hx', hw fw rfl hx'⟩
  refine ⟨_, D, isEpsChain_chainAppend (isEpsChain_chainAppend hPAeps hMeps) hPBeps, ?_, ?_, ?_⟩
  · intro x _
    rw [chainAppend_union, chainAppend_union]
    obtain ⟨k, hk⟩ := exists_link_of_mem_union (hFcov (mem_univ x))
    rcases le_or_gt (k : ℕ) v with h | h
    · obtain ⟨t, ht⟩ := exists_link_of_mem_union (hA (link_subset_lowUnion F h hk))
      refine Or.inl (Or.inl (mem_iUnion.2 ⟨t, subset_chainMergeLast_link _ _ _ _ t ?_⟩))
      exact ⟨link_subset_lowUnion F h hk, ht⟩
    rcases eq_or_lt_of_le (show v + 1 ≤ (k : ℕ) by omega) with h' | h'
    · refine Or.inl (Or.inl (mem_iUnion.2 ⟨Fin.last n₀, ?_⟩))
      rw [chainMergeLast_link_last]
      have : k = fv1 := Fin.ext h'.symm
      exact Or.inr (this ▸ hk)
    rcases le_or_gt (k : ℕ) (w - 2) with h'' | h''
    · refine Or.inl (Or.inr (mem_iUnion.2 ⟨⟨k - (v + 2), by simp [fv2, fw2]; omega⟩, ?_⟩))
      rw [hMlink]
      have : (⟨v + 2 + (k - (v + 2)), by omega⟩ : Fin N) = k := Fin.ext (by simp; omega)
      rw [this]; exact hk
    rcases eq_or_lt_of_le (show w - 1 ≤ (k : ℕ) by omega) with h3 | h3
    · have : k = fw1 := Fin.ext h3.symm
      exact Or.inr (mem_iUnion.2 ⟨0, hPB'0 (this ▸ hk)⟩)
    · have hkB : x ∈ B := link_subset_highUnion F (by omega) hk
      obtain ⟨t, ht⟩ := exists_link_of_mem_union (hB hkB)
      refine Or.inr (mem_iUnion.2 ⟨t, ?_⟩)
      show x ∈ PB''.link (Fin.rev t)
      refine subset_chainMergeLast_link _ _ _ _ _ ?_
      show x ∈ PB.link (Fin.rev (Fin.rev t))
      rw [Fin.rev_rev]
      exact ⟨hkB, ht⟩
  · obtain ⟨x, hxg, hx0⟩ := hg₀E 0
    refine ⟨x, ?_, hxg⟩
    have e0 : (0 : Fin _) = Fin.castAdd (n₁ + 1) (Fin.castAdd ((fw2 : ℕ) - fv2 + 1) (0 : Fin (n₀ + 1))) :=
      Fin.ext (by simp)
    rw [e0, chainAppend_link_left, chainAppend_link_left]
    exact subset_chainMergeLast_link _ _ _ _ _ ⟨hg₀A hxg, hx0⟩
  · obtain ⟨x, hxg, hx0⟩ := hg₁E (Fin.last n₁)
    refine ⟨x, ?_, hxg⟩
    have key : x ∈ D.link (Fin.natAdd _ (Fin.last n₁)) := by
      rw [chainAppend_link_right]
      show x ∈ PB''.link (Fin.rev (Fin.last n₁))
      rw [Fin.rev_last]
      refine subset_chainMergeLast_link _ _ _ _ _ ?_
      show x ∈ PB.link (Fin.rev 0)
      rw [Fin.rev_zero]
      exact ⟨hg₁B hxg, hx0⟩
    convert key using 2

end HPC.BJ59
