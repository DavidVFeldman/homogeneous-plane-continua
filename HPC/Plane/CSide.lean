import HPC.Plane.Joints
import HPC.Chains.Basic
import HPC.Fold.BingCrook

/-!
# Covering chains of a snake-like continuum

Batch 84 (COMMISSION-batch84.md §3.5, the `C`-side of Theorem 4). A chain covering `M` *minimally*
(no proper subchain covers) has every link meeting `M` (connectedness), and every refinement
pattern into it is onto. From a Lebesgue number of the cover, a fine enough covering chain
refines it by an `N`-slow pattern with unit steps.
-/

namespace HPC.Plane

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- `C` covers `M`, and neither the links before `k` nor the links after `k` cover `M`. -/
def MinCover {m : ℕ} (C : Chain X m) (M : Set X) : Prop :=
  M ⊆ C.union ∧ ∀ k : Fin m, ¬ M ⊆ (⋃ j : Fin m, ⋃ (_ : j < k), C.link j) ∧
    ¬ M ⊆ (⋃ j : Fin m, ⋃ (_ : k < j), C.link j)

/-- Points of links `i`, `i'` of a chain of mesh `< μ` are within `(|i - i'| + 1) μ`. -/
theorem _root_.HPC.Chain.dist_le_of_links {n : ℕ} (D : Chain X n) {μ : ℝ}
    (hb : ∀ i, Bornology.IsBounded (D.link i)) (hd : ∀ i, diam (D.link i) < μ) :
    ∀ (k : ℕ) (i i' : Fin n), i.val + k = i'.val → ∀ y ∈ D.link i, ∀ y' ∈ D.link i',
      dist y y' ≤ (k + 1) * μ := by
  intro k
  induction k with
  | zero =>
      intro i i' h y hy y' hy'
      have : i = i' := Fin.ext (by omega)
      subst this
      have := dist_le_diam_of_mem (hb i) hy hy'
      have := hd i
      simp; linarith
  | succ k ih =>
      intro i i' h y hy y' hy'
      have hlt : i'.val - 1 < n := by omega
      obtain ⟨w, hw1, hw2⟩ := (D.adjacent_iff ⟨i'.val - 1, hlt⟩ i').mpr (by simp only; omega)
      have h1 := ih i ⟨i'.val - 1, hlt⟩ (by simp only; omega) y hy w hw1
      have h2 := dist_le_diam_of_mem (hb i') hw2 hy'
      have h3 := hd i'
      have := dist_triangle y w y'
      push_cast; nlinarith

/-- Symmetric form. -/
theorem _root_.HPC.Chain.dist_le_of_links' {n : ℕ} (D : Chain X n) {μ : ℝ}
    (hb : ∀ i, Bornology.IsBounded (D.link i)) (hd : ∀ i, diam (D.link i) < μ)
    (i i' : Fin n) {y y' : X} (hy : y ∈ D.link i) (hy' : y' ∈ D.link i') :
    dist y y' ≤ ((((i : ℤ) - i').natAbs : ℕ) + 1) * μ := by
  rcases le_total i.val i'.val with h | h
  · have := D.dist_le_of_links hb hd (i'.val - i.val) i i' (by omega) y hy y' hy'
    have e : ((i : ℤ) - i').natAbs = i'.val - i.val := by omega
    rw [e]; exact this
  · have := D.dist_le_of_links hb hd (i.val - i'.val) i' i (by omega) y' hy' y hy
    have e : ((i : ℤ) - i').natAbs = i.val - i'.val := by omega
    rw [dist_comm, e]; exact this

/-- In a minimal cover of a connected set, every link meets it. -/
theorem MinCover.meets {m : ℕ} {C : Chain X m} {M : Set X} (h : MinCover C M)
    (hM : IsConnected M) (k : Fin m) : (C.link k ∩ M).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  obtain ⟨hcov, hmin⟩ := h
  set U := ⋃ j : Fin m, ⋃ (_ : j < k), C.link j
  set V := ⋃ j : Fin m, ⋃ (_ : k < j), C.link j
  have hU : IsOpen U := isOpen_iUnion fun j => isOpen_iUnion fun _ => C.isOpen j
  have hV : IsOpen V := isOpen_iUnion fun j => isOpen_iUnion fun _ => C.isOpen j
  have hUV : M ⊆ U ∪ V := by
    intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov hz)
    rcases lt_trichotomy j k with c | c | c
    · left; exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨c, hj⟩⟩
    · subst c
      exact absurd (show z ∈ C.link j ∩ M from ⟨hj, hz⟩) (by rw [hne]; simp)
    · right; exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨c, hj⟩⟩
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro z hzU hzV
    obtain ⟨j, hj⟩ := mem_iUnion.mp hzU
    obtain ⟨hjk, hj⟩ := mem_iUnion.mp hj
    obtain ⟨j', hj'⟩ := mem_iUnion.mp hzV
    obtain ⟨hkj, hj'⟩ := mem_iUnion.mp hj'
    have := (C.adjacent_iff j j').mp ⟨z, hj, hj'⟩
    rw [Fin.lt_def] at hjk hkj
    omega
  obtain ⟨z, hz⟩ := hM.nonempty
  rcases hUV hz with hzU | hzV
  · exact (hmin k).1 (hM.isPreconnected.subset_left_of_subset_union hU hV hdisj hUV ⟨z, hz, hzU⟩)
  · exact (hmin k).2 (hM.isPreconnected.subset_right_of_subset_union hU hV hdisj hUV ⟨z, hz, hzV⟩)

/-- Every chain covering a nonempty set contains a minimal covering subchain. -/
theorem exists_minCover {n : ℕ} (E : Chain X n) {M : Set X} (hM : M.Nonempty) (hcov : M ⊆ E.union) :
    ∃ (m : ℕ) (C : Chain X m), MinCover C M ∧ ∀ j, ∃ i, C.link j = E.link i := by
  classical
  have hn : 0 < n := by
    obtain ⟨z, hz⟩ := hM
    obtain ⟨j, -⟩ := mem_iUnion.mp (hcov hz)
    exact Nat.pos_of_ne_zero fun h => by subst h; exact j.elim0
  let Good : ℕ → Prop := fun L => ∃ a b : ℕ, ∃ (_ : a ≤ b) (_ : b < n), b - a = L ∧
    M ⊆ ⋃ (j : Fin n), ⋃ (_ : a ≤ j.val ∧ j.val ≤ b), E.link j
  have hex : ∃ L, Good L := ⟨n - 1, 0, n - 1, Nat.zero_le _, by omega, by omega, by
    intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov hz)
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨⟨Nat.zero_le _, by omega⟩, hj⟩⟩⟩
  obtain ⟨a, b, hab, hb, hL, hcovab⟩ := Nat.find_spec hex
  have hmin : ∀ L, L < Nat.find hex → ¬ Good L := fun L hL => Nat.find_min hex hL
  refine ⟨b - a + 1, E.sub ⟨a, by omega⟩ ⟨b, hb⟩ (by simp [Fin.le_def]; omega), ⟨?_, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcovab hz)
    obtain ⟨⟨h1, h2⟩, hj⟩ := mem_iUnion.mp hj
    refine mem_iUnion.mpr ⟨⟨j.val - a, by omega⟩, ?_⟩
    simp only [Chain.sub]
    convert hj using 3
    omega
  · intro k
    constructor
    · intro hsub
      rcases Nat.eq_zero_or_pos k.val with hk | hk
      · obtain ⟨z, hz⟩ := hM
        obtain ⟨j, hj⟩ := mem_iUnion.mp (hsub hz)
        obtain ⟨hjk, -⟩ := mem_iUnion.mp hj
        rw [Fin.lt_def] at hjk; omega
      · refine hmin (k.val - 1) (by omega) ⟨a, a + k.val - 1, by omega, by omega, by omega, ?_⟩
        intro z hz
        obtain ⟨j, hj⟩ := mem_iUnion.mp (hsub hz)
        obtain ⟨hjk, hj⟩ := mem_iUnion.mp hj
        rw [Fin.lt_def] at hjk
        refine mem_iUnion.mpr ⟨⟨a + j.val, by omega⟩, mem_iUnion.mpr ⟨⟨Nat.le_add_right _ _, show a + j.val ≤ a + k.val - 1 by omega⟩, ?_⟩⟩
        simpa [Chain.sub] using hj
    · intro hsub
      rcases Nat.lt_or_ge k.val (b - a) with hk | hk
      · refine hmin (b - a - k.val - 1) (by omega) ⟨a + k.val + 1, b, by omega, hb, by omega, ?_⟩
        intro z hz
        obtain ⟨j, hj⟩ := mem_iUnion.mp (hsub hz)
        obtain ⟨hjk, hj⟩ := mem_iUnion.mp hj
        rw [Fin.lt_def] at hjk
        have := j.isLt
        refine mem_iUnion.mpr ⟨⟨a + j.val, by omega⟩, mem_iUnion.mpr ⟨⟨by simp; omega, by simp; omega⟩, ?_⟩⟩
        simpa [Chain.sub] using hj
      · obtain ⟨z, hz⟩ := hM
        obtain ⟨j, hj⟩ := mem_iUnion.mp (hsub hz)
        obtain ⟨hjk, -⟩ := mem_iUnion.mp hj
        rw [Fin.lt_def] at hjk
        have := j.isLt; omega
  · intro j
    exact ⟨_, rfl⟩

/-- Refinement patterns into a minimal cover are onto. -/
theorem surj_of_minCover {m m' : ℕ} {C : Chain X m} {M : Set X} (hC : MinCover C M)
    {C' : Chain X m'} (hcov : M ⊆ C'.union) (x : Fin m' → Fin m)
    (hx : ∀ t, C'.link t ⊆ C.link (x t)) (hstep : Joints.UnitSteps x) : Function.Surjective x := by
  intro k
  by_contra hk
  push_neg at hk
  have hside : (∀ t, x t < k) ∨ (∀ t, k < x t) := by
    by_contra hc
    push_neg at hc
    obtain ⟨⟨t2, h2⟩, ⟨t1, h1⟩⟩ := hc
    have h1' : x t1 < k := lt_of_le_of_ne h1 (hk t1)
    have h2' : k < x t2 := lt_of_le_of_ne h2 (fun e => hk t2 e.symm)
    have hlip : ∀ u, |Joints.xe x (u + 1) - Joints.xe x u| ≤ 1 := Joints.xe_step hstep
    have hm' : 0 < m' := Nat.pos_of_ne_zero fun h => by subst h; exact t1.elim0
    obtain ⟨s, hs1, hs2, hs3⟩ := HPC.Fold.exists_eq_of_lip (Joints.xe x) hlip
      (max t1.val t2.val - min t1.val t2.val) (min t1.val t2.val) (k : ℤ) (by
        have e1 : Joints.xe x t1.val = (x t1 : ℤ) := Joints.xe_of_lt t1.isLt
        have e2 : Joints.xe x t2.val = (x t2 : ℤ) := Joints.xe_of_lt t2.isLt
        rw [Fin.lt_def] at h1' h2'
        rcases le_total t1.val t2.val with c | c
        · rw [min_eq_left c, max_eq_right c, show t1.val + (t2.val - t1.val) = t2.val by omega]
          left; rw [e1, e2]; exact ⟨by omega, by omega⟩
        · rw [min_eq_right c, max_eq_left c, show t2.val + (t1.val - t2.val) = t1.val by omega]
          right; rw [e1, e2]; exact ⟨by omega, by omega⟩)
    have hsn : s < m' := by
      have := t1.isLt; have := t2.isLt
      rcases le_total t1.val t2.val with c | c
      · rw [min_eq_left c, max_eq_right c] at hs2; omega
      · rw [min_eq_right c, max_eq_left c] at hs2; omega
    rw [Joints.xe_of_lt hsn] at hs3
    exact hk ⟨s, hsn⟩ (Fin.ext (by exact_mod_cast hs3))
  rcases hside with h | h
  · refine (hC.2 k).1 (fun z hz => ?_)
    obtain ⟨t, ht⟩ := mem_iUnion.mp (hcov hz)
    exact mem_iUnion.mpr ⟨x t, mem_iUnion.mpr ⟨h t, hx t ht⟩⟩
  · refine (hC.2 k).2 (fun z hz => ?_)
    obtain ⟨t, ht⟩ := mem_iUnion.mp (hcov hz)
    exact mem_iUnion.mpr ⟨x t, mem_iUnion.mpr ⟨h t, hx t ht⟩⟩

/-- **The refinement step on the `C`-side.** A minimal cover `C` of a continuum `M` which is
covered by chains of arbitrarily small mesh is refined by a minimal cover of mesh `< ε`, along a
pattern that is onto, has unit steps and is `N`-slow. -/
theorem refine_step {m : ℕ} {C : Chain X m} {M : Set X} (hC : MinCover C M) (hMc : IsCompact M)
    (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (N : ℕ) (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m' : ℕ) (C' : Chain X m') (x : Fin m' → Fin m), MinCover C' M ∧
      (∀ i, Bornology.IsBounded (C'.link i) ∧ diam (C'.link i) < ε) ∧
      (∀ t, C'.link t ⊆ C.link (x t)) ∧ Joints.UnitSteps x ∧ Joints.Slow x N ∧
      Function.Surjective x := by
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hMc C.isOpen hC.1
  set μ := min ε (δ / (N + 2)) with hμ
  have hμ0 : 0 < μ := lt_min hε (by positivity)
  obtain ⟨n, E, hE, hEcov⟩ := hsnake μ hμ0
  obtain ⟨m', C', hC', hlinks⟩ := exists_minCover E hMconn.nonempty hEcov
  have hb : ∀ i, Bornology.IsBounded (C'.link i) := fun i => by
    obtain ⟨j, hj⟩ := hlinks i; rw [hj]; exact (hE j).1
  have hd : ∀ i, diam (C'.link i) < μ := fun i => by
    obtain ⟨j, hj⟩ := hlinks i; rw [hj]; exact (hE j).2
  have hp : ∀ a : Fin m', ∃ p ∈ M, p ∈ C'.link a := fun a => by
    obtain ⟨p, h1, h2⟩ := hC'.meets hMconn a; exact ⟨p, h2, h1⟩
  choose p hpM hpC using hp
  have hk : ∀ a : Fin m', ∃ k : Fin m, ball (p a) δ ⊆ C.link k := fun a => hleb (p a) (hpM a)
  choose x hx using hk
  -- links within `N` of `a` lie in the `δ`-ball around `p a`
  have hball : ∀ a i : Fin m', ((a : ℤ) - i).natAbs ≤ N → C'.link i ⊆ ball (p a) δ := by
    intro a i hai y hy
    rw [mem_ball]
    have h1 := C'.dist_le_of_links' hb hd i a hy (hpC a)
    have h2 : (((((i : ℤ) - a).natAbs : ℕ) : ℝ) + 1) ≤ N + 1 := by
      have : ((i : ℤ) - a).natAbs ≤ N := by omega
      have : ((((i : ℤ) - a).natAbs : ℕ) : ℝ) ≤ N := by exact_mod_cast this
      linarith
    have h3 : μ ≤ δ / (N + 2) := min_le_right _ _
    have h4 : ((N : ℝ) + 1) * (δ / (N + 2)) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
    calc dist y (p a) ≤ (((((i : ℤ) - a).natAbs : ℕ) : ℝ) + 1) * μ := h1
      _ ≤ (N + 1) * (δ / (N + 2)) := mul_le_mul h2 h3 hμ0.le (by positivity)
      _ < δ := h4
  have hsub : ∀ t, C'.link t ⊆ C.link (x t) := fun t =>
    (hball t t (by simp)).trans (hx t)
  have hnear : ∀ a a' : Fin m', ((a : ℤ) - a').natAbs ≤ N → ((x a : ℤ) - x a').natAbs ≤ 1 := by
    intro a a' h
    obtain ⟨y, hy⟩ := C'.link_nonempty a
    refine (C.adjacent (x a) (x a')).mp ⟨y, hx a (hball a a (by simp) hy), ?_⟩
    exact hx a' (hball a' a (by omega) hy)
  have hstep : Joints.UnitSteps x := fun t t' h => hnear t' t (by omega) |>.trans (by omega) |> fun _ => by
    have := hnear t' t (by omega); omega
  refine ⟨m', C', x, hC', fun i => ⟨hb i, (hd i).trans_le (min_le_left _ _)⟩, hsub, hstep, ?_,
    surj_of_minCover hC hC'.1 x hsub hstep⟩
  intro s s' h
  by_contra hc
  push_neg at hc
  have := hnear s s' (by omega)
  omega

end HPC.Plane
