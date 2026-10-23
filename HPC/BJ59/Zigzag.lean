import HPC.BJ59.BJChains
import HPC.BJ59.Defs

/-!
# Batch 200, §2: Bing–Jones's homeomorphism of pp. 188–189

The skeleton's `starImage`, `zigzag_homeomorph` and `zigzag_fibre` (statements verbatim), with
library lemmas. Route: commission 200 §2.

* `starImage D E H p` is Bing–Jones's `H_i d(p, i)`;
* nested (`starImage_succ_subset`), small (`starImage_dist_le`), meeting `Q`;
* `h p` is the one point of `Q` in every `closure (H_i d(p, i))`; continuity, injectivity (here the
  chains `E i` are chains in Bing–Jones's sense), surjectivity, and compactness give the
  homeomorphism.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Zigzag

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- `H_i d(p, i)` of p. 188: the union of the images under `H` of the links of `D` that contain
`p`. -/
def starImage {n m : ℕ} (D : Chain X n) (E : Chain Y m) (H : Fin n → Fin m) (p : X) : Set Y :=
  ⋃ (j : Fin n) (_ : p ∈ D.link j), E.link (H j)

theorem mem_starImage {n m : ℕ} {D : Chain X n} {E : Chain Y m} {H : Fin n → Fin m} {p : X}
    {y : Y} : y ∈ starImage D E H p ↔ ∃ j, p ∈ D.link j ∧ y ∈ E.link (H j) := by
  simp [starImage]

/-- The closure of `H d(p)` is the union of the closures of its links. -/
theorem mem_closure_starImage {n m : ℕ} {D : Chain X n} {E : Chain Y m} {H : Fin n → Fin m}
    {p : X} {y : Y} (hy : y ∈ closure (starImage D E H p)) :
    ∃ j, p ∈ D.link j ∧ y ∈ closure (E.link (H j)) := by
  have heq : starImage D E H p = ⋃ j : {j : Fin n // p ∈ D.link j}, E.link (H j) := by
    ext z; simp [starImage]
  rw [heq, closure_iUnion_of_finite] at hy
  obtain ⟨⟨j, hj⟩, hz⟩ := mem_iUnion.1 hy
  exact ⟨j, hj, hz⟩

/-- A distance bound on a set passes to its closure. -/
theorem dist_le_of_mem_closure_of_forall {S T : Set Y} {C : ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ T, dist x y ≤ C) {x y : Y} (hx : x ∈ closure S) (hy : y ∈ closure T) :
    dist x y ≤ C := by
  have hcl : IsClosed {z : Y × Y | dist z.1 z.2 ≤ C} :=
    isClosed_le (continuous_fst.dist continuous_snd) continuous_const
  have hsub : S ×ˢ T ⊆ {z : Y × Y | dist z.1 z.2 ≤ C} := fun z hz => h _ hz.1 _ hz.2
  have := closure_minimal hsub hcl
  rw [closure_prod_eq] at this
  exact this (show (x, y) ∈ closure S ×ˢ closure T from ⟨hx, hy⟩)

/-- A lower distance bound on two sets passes to their closures. -/
theorem le_dist_of_mem_closure_of_forall {S T : Set Y} {C : ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ T, C ≤ dist x y) {x y : Y} (hx : x ∈ closure S) (hy : y ∈ closure T) :
    C ≤ dist x y := by
  have hcl : IsClosed {z : Y × Y | C ≤ dist z.1 z.2} :=
    isClosed_le continuous_const (continuous_fst.dist continuous_snd)
  have hsub : S ×ˢ T ⊆ {z : Y × Y | C ≤ dist z.1 z.2} := fun z hz => h _ hz.1 _ hz.2
  have := closure_minimal hsub hcl
  rw [closure_prod_eq] at this
  exact this (show (x, y) ∈ closure S ×ˢ closure T from ⟨hx, hy⟩)

/-- In a chain in Bing–Jones's sense, links whose closures meet are adjacent. -/
theorem IsBJChain.adjacent_of_closure {m : ℕ} {E : Chain Y m} (hE : IsBJChain E) {a b : Fin m}
    {y : Y} (ha : y ∈ closure (E.link a)) (hb : y ∈ closure (E.link b)) :
    ((a : ℤ) - b).natAbs ≤ 1 := by
  by_contra hab
  push_neg at hab
  obtain ⟨δ, hδ, hd⟩ := hE a b hab
  have := le_dist_of_mem_closure_of_forall hd ha hb
  rw [dist_self] at this
  linarith

/-- Two points of an `ε`-chain lying in adjacent links are less than `2ε` apart. -/
theorem dist_lt_of_adjacent {n : ℕ} {D : Chain X n} {ε : ℝ} (hD : IsEpsChain D ε) {a b : Fin n}
    (hab : ((a : ℤ) - b).natAbs ≤ 1) {x y : X} (hx : x ∈ D.link a) (hy : y ∈ D.link b) :
    dist x y < 2 * ε := by
  obtain ⟨w, hwa, hwb⟩ := (D.adjacent a b).2 hab
  have h1 := dist_le_diam_of_mem (hD a).1 hx hwa
  have h2 := dist_le_diam_of_mem (hD b).1 hwb hy
  linarith [dist_triangle x w y, (hD a).2, (hD b).2]

/-- `H d(p)` has diameter at most `2ε`. -/
theorem starImage_dist_le {n m : ℕ} {D : Chain X n} {E : Chain Y m} {H : Fin n → Fin m}
    (hH : IsChainMap H) {ε : ℝ} (hE : IsEpsChain E ε) (p : X) :
    ∀ x ∈ starImage D E H p, ∀ y ∈ starImage D E H p, dist x y ≤ 2 * ε := by
  intro x hx y hy
  obtain ⟨j, hj, hxj⟩ := mem_starImage.1 hx
  obtain ⟨j', hj', hyj⟩ := mem_starImage.1 hy
  have h1 : ((j : ℤ) - j').natAbs ≤ 1 := (D.adjacent j j').1 ⟨p, hj, hj'⟩
  exact (dist_lt_of_adjacent hE (hH j j' h1) hxj hyj).le

/-- Step 1 of p. 188: the sets `H_i d(p, i)` decrease, by Conditions B and B′. -/
theorem starImage_succ_subset {n m : ℕ → ℕ} {D : ∀ i, Chain X (n i)} {E : ∀ i, Chain Y (m i)}
    {H : ∀ i, Fin (n i) → Fin (m i)} {K : ∀ i, Fin (m (i + 1)) → Fin (n i)}
    (hB : ∀ i j, (D (i + 1)).link j ⊆ (D i).link (K i (H (i + 1) j)))
    (hB' : ∀ i j, (E (i + 1)).link j ⊆ (E i).link (H i (K i j))) (i : ℕ) (p : X) :
    starImage (D (i + 1)) (E (i + 1)) (H (i + 1)) p ⊆ starImage (D i) (E i) (H i) p := by
  intro y hy
  obtain ⟨j, hj, hyj⟩ := mem_starImage.1 hy
  exact mem_starImage.2 ⟨K i (H (i + 1) j), hB i j hj, hB' i _ hyj⟩

theorem starImage_antitone {n m : ℕ → ℕ} {D : ∀ i, Chain X (n i)} {E : ∀ i, Chain Y (m i)}
    {H : ∀ i, Fin (n i) → Fin (m i)} {K : ∀ i, Fin (m (i + 1)) → Fin (n i)}
    (hB : ∀ i j, (D (i + 1)).link j ⊆ (D i).link (K i (H (i + 1) j)))
    (hB' : ∀ i j, (E (i + 1)).link j ⊆ (E i).link (H i (K i j))) (p : X) :
    Antitone fun i => starImage (D i) (E i) (H i) p :=
  antitone_nat_of_succ_le fun i => starImage_succ_subset hB hB' i p

/-- A number bounded by `c * ε i` for all `i`, with `ε i → 0`, is at most `0`. -/
theorem le_zero_of_le_mul_tendsto {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {d c : ℝ}
    (h : ∀ i, d ≤ c * ε i) : d ≤ 0 := by
  have := ge_of_tendsto' (hε.const_mul c) h
  simpa using this

/-- **Bing–Jones, pp. 188–189, "Definition of homeomorphism h"**, abstracted from Theorem 10:
chains `D i` on `P` and `E i` on `Q` with meshes tending to zero, chain maps `H i` of `D i` onto
`E i` and `K i` of `E (i + 1)` into `D i`, and Conditions B and B′. The homeomorphism is
characterized by `h p ∈ closure (H_i d(p, i))` for every `i`. Only the chains `E i` are assumed
to be chains in Bing–Jones's sense. -/
theorem zigzag_homeomorph {P : Set X} {Q : Set Y} (hP : IsCompact P) (hQ : IsCompact Q)
    {n m : ℕ → ℕ} (D : ∀ i, Chain X (n i)) (E : ∀ i, Chain Y (m i))
    (hDP : ∀ i, P ⊆ (D i).union) (hDp : ∀ i j, ((D i).link j ∩ P).Nonempty)
    (hEQ : ∀ i, Q ⊆ (E i).union) (hEq : ∀ i j, ((E i).link j ∩ Q).Nonempty)
    (hEbj : ∀ i, IsBJChain (E i))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hDε : ∀ i, IsEpsChain (D i) (ε i)) (hEε : ∀ i, IsEpsChain (E i) (ε i))
    (H : ∀ i, Fin (n i) → Fin (m i)) (K : ∀ i, Fin (m (i + 1)) → Fin (n i))
    (hH : ∀ i, IsChainMap (H i)) (hHs : ∀ i, Function.Surjective (H i))
    (hK : ∀ i, IsChainMap (K i))
    (hB : ∀ i j, (D (i + 1)).link j ⊆ (D i).link (K i (H (i + 1) j)))
    (hB' : ∀ i j, (E (i + 1)).link j ⊆ (E i).link (H i (K i j))) :
    ∃ h : P ≃ₜ Q, ∀ (p : P) (q : Q),
      (∀ i, (q : Y) ∈ closure (starImage (D i) (E i) (H i) p)) ↔ q = h p := by
  classical
  set S : ℕ → X → Set Y := fun i p => starImage (D i) (E i) (H i) p with hSdef
  have hSd : ∀ i p, ∀ x ∈ closure (S i p), ∀ y ∈ closure (S i p), dist x y ≤ 2 * ε i :=
    fun i p x hx y hy =>
      dist_le_of_mem_closure_of_forall (starImage_dist_le (hH i) (hEε i) p) hx hy
  -- the sets `closure (S i p) ∩ Q` have a common point
  have hne : ∀ p ∈ P, (⋂ i, closure (S i p) ∩ Q).Nonempty := by
    intro p hp
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
      (fun i => inter_subset_inter_left _ (closure_mono (starImage_succ_subset hB hB' i p)))
      (fun i => ?_) (hQ.inter_left isClosed_closure) (fun i => isClosed_closure.inter hQ.isClosed)
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hDP i hp)
    obtain ⟨q, hq, hqQ⟩ := hEq i (H i j)
    exact ⟨q, subset_closure (mem_starImage.2 ⟨j, hj, hq⟩), hqQ⟩
  -- uniqueness
  have huniq : ∀ p (x y : Y), (∀ i, x ∈ closure (S i p)) → (∀ i, y ∈ closure (S i p)) →
      x = y := by
    intro p x y hx hy
    have : dist x y ≤ 0 := le_zero_of_le_mul_tendsto hε fun i => hSd i p x (hx i) y (hy i)
    exact dist_le_zero.1 this
  let F : P → Q := fun p => ⟨(hne p p.2).some, (mem_iInter.1 (hne p p.2).some_mem 0).2⟩
  have hF : ∀ p : P, ∀ i, (F p : Y) ∈ closure (S i p) := fun p i =>
    (mem_iInter.1 (hne p p.2).some_mem i).1
  have hFchar : ∀ (p : P) (q : Q), (∀ i, (q : Y) ∈ closure (S i p)) ↔ q = F p := by
    intro p q
    constructor
    · intro hq
      exact Subtype.ext (huniq p _ _ hq (hF p))
    · rintro rfl; exact hF p
  -- continuity
  have hFc : Continuous F := by
    rw [Metric.continuous_iff]
    intro b η hη
    obtain ⟨i, hi⟩ := ((hε.const_mul 4).eventually (gt_mem_nhds (by simpa using hη))).exists
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hDP i b.2)
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 ((D i).isOpen j) b hj
    refine ⟨δ, hδ, fun a hab => ?_⟩
    have ha : (a : X) ∈ (D i).link j := hball (by rwa [Subtype.dist_eq] at hab)
    obtain ⟨w, hw⟩ := (E i).link_nonempty (H i j)
    have hwa : w ∈ S i a := mem_starImage.2 ⟨j, ha, hw⟩
    have hwb : w ∈ S i b := mem_starImage.2 ⟨j, hj, hw⟩
    have h1 := hSd i a _ (hF a i) w (subset_closure hwa)
    have h2 := hSd i b _ (hF b i) w (subset_closure hwb)
    rw [Subtype.dist_eq]
    linarith [dist_triangle (F a : Y) w (F b), dist_comm (F b : Y) w]
  -- injectivity
  have hFi : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    refine dist_le_zero.1 (le_zero_of_le_mul_tendsto hε (c := 2) fun k => ?_)
    have hya := hF a (k + 1)
    have hyb := hF b (k + 1)
    rw [hab] at hya
    obtain ⟨j, hj, hyj⟩ := mem_closure_starImage hya
    obtain ⟨j', hj', hyj'⟩ := mem_closure_starImage hyb
    have h1 := (hEbj (k + 1)).adjacent_of_closure hyj hyj'
    have h2 := hK k _ _ h1
    exact (dist_lt_of_adjacent (hDε k) h2 (hB k j hj) (hB k j' hj')).le
  -- surjectivity
  have hFs : Function.Surjective F := by
    haveI : CompactSpace P := isCompact_iff_compactSpace.1 hP
    intro q
    have hcl : IsClosed (range fun p => (F p : Y)) :=
      (isCompact_range (continuous_subtype_val.comp hFc)).isClosed
    have hmem : (q : Y) ∈ closure (range fun p => (F p : Y)) := by
      rw [Metric.mem_closure_iff]
      intro η hη
      obtain ⟨i, hi⟩ := ((hε.const_mul 2).eventually (gt_mem_nhds (by simpa using hη))).exists
      obtain ⟨c, hc⟩ := mem_iUnion.1 (hEQ i q.2)
      obtain ⟨j, rfl⟩ := hHs i c
      obtain ⟨p, hpj, hpP⟩ := hDp i j
      refine ⟨F ⟨p, hpP⟩, mem_range_self _, ?_⟩
      have := hSd i p q (subset_closure (mem_starImage.2 ⟨j, hpj, hc⟩)) _ (hF ⟨p, hpP⟩ i)
      linarith
    rw [hcl.closure_eq] at hmem
    obtain ⟨p, hp⟩ := hmem
    exact ⟨p, Subtype.ext hp⟩
  haveI : CompactSpace P := isCompact_iff_compactSpace.1 hP
  let e : P ≃ Q := Equiv.ofBijective F ⟨hFi, hFs⟩
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := e) hFc, fun p q => ?_⟩
  exact hFchar p q

/-- **Condition A of p. 188, in the form used**: if each link of `D i` through `p` goes to a link
of `E i` that meets the fibre over the same point, the homeomorphism preserves fibres. -/
theorem zigzag_fibre {P : Set X} {Q : Set Y}
    {n m : ℕ → ℕ} (D : ∀ i, Chain X (n i)) (E : ∀ i, Chain Y (m i))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hEε : ∀ i, IsEpsChain (E i) (ε i))
    (H : ∀ i, Fin (n i) → Fin (m i))
    {T : Type*} (φ : X → T) (ψ : Y → T) (hψ : ∀ t, IsClosed (Q ∩ ψ ⁻¹' {t}))
    (hA : ∀ i (j : Fin (n i)) (p : X), p ∈ P → p ∈ (D i).link j →
      ∃ q ∈ Q, q ∈ (E i).link (H i j) ∧ ψ q = φ p)
    (h : P ≃ₜ Q) (hh : ∀ (p : P) (q : Q),
      (∀ i, (q : Y) ∈ closure (starImage (D i) (E i) (H i) p)) ↔ q = h p) :
    ∀ p : P, ψ (h p) = φ p := by
  intro p
  have hp := (hh p (h p)).2 rfl
  have key : ∀ i, ∃ q ∈ Q ∩ ψ ⁻¹' {φ p}, dist (h p : Y) q ≤ ε i := by
    intro i
    obtain ⟨j, hj, hyj⟩ := mem_closure_starImage (hp i)
    obtain ⟨q, hqQ, hqj, hψq⟩ := hA i j p p.2 hj
    refine ⟨q, ⟨hqQ, hψq⟩, ?_⟩
    have : ∀ x ∈ (E i).link (H i j), ∀ y ∈ (E i).link (H i j), dist x y ≤ ε i :=
      fun x hx y hy => (dist_le_diam_of_mem (hEε i _).1 hx hy).trans (hEε i _).2.le
    exact dist_le_of_mem_closure_of_forall this hyj (subset_closure hqj)
  have hmem : (h p : Y) ∈ closure (Q ∩ ψ ⁻¹' {φ p}) := by
    rw [Metric.mem_closure_iff]
    intro η hη
    obtain ⟨i, hi⟩ := (hε.eventually (gt_mem_nhds hη)).exists
    obtain ⟨q, hq, hd⟩ := key i
    exact ⟨q, hq, by linarith⟩
  rw [(hψ (φ p)).closure_eq] at hmem
  exact hmem.2

end Zigzag

end HPC.BJ59
