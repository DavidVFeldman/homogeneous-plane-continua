import HPC.HO16.LadderDefs

/-!
# Batch 197: the parameter calculus of a ladder edge

Over an edge `s` of a ladder, every piece of a sheet lies over a closed interval of parameters of
`s`. This file computes, for the `i`-th sheet over one edge, the set of parameters it covers
(`eP`), the parameters of the points of `αᵢ` on the edge (`eA`), and the two families of gaps
(`eQA`, the gaps whose ends lie in `αᵢ`, and `eQB`, those whose ends lie in `αᵢ₊₁`), and proves
the one-dimensional facts behind (S2)–(S5) (commission 197 §3). Everything here is about real
intervals; the geometry is in `LadderStair.lean`.
-/

namespace HPC.HO16

open Set

/-- Disjunctive linear goals: pick a disjunct, split conjunctions, close by `linarith`. -/
syntax "lsolve" : tactic
macro_rules
  | `(tactic| lsolve) => `(tactic| first | (refine Or.inl ?_; lsolve) | (refine Or.inr ?_; lsolve) | (refine And.intro ?_ ?_ <;> lsolve) | linarith)

noncomputable section

/-- The unit of the parameter grid of a wedge edge. -/
def zU (j m : ℕ) (lam : ℝ) : ℝ := lam / (2 * ((j - m : ℕ) : ℝ) + 3)

/-- A radius below every gap of the parameter grid of a wedge edge. -/
def wδ (j m : ℕ) (lam : ℝ) : ℝ := min (zU j m lam) (1 - lam) / 2

/-- The five parameter intervals of the `i`-th sheet on a wedge edge. -/
def wI (j m : ℕ) (lam : ℝ) (i : ℕ) : ℕ → Set ℝ
  | 0 => if 1 ≤ i ∧ i < m ∧ i ≤ j then Icc 0 1 else ∅
  | 1 => if m ≤ i ∧ i ≤ j then Icc 0 (zzR j m lam i) else ∅
  | 2 => if m + 1 ≤ i ∧ i ≤ j + 1 then Icc (zzL j m lam (i - 1)) (zzR j m lam (i - 1)) else ∅
  | 3 => if m + 2 ≤ i ∧ i ≤ j + 2 then Icc (zzL j m lam (i - 2)) 1 else ∅
  | _ => if i = m ∨ i = m + 1 then Icc lam 1 else ∅

def wP (j m : ℕ) (lam : ℝ) (i : ℕ) : Set ℝ :=
  wI j m lam i 0 ∪ wI j m lam i 1 ∪ wI j m lam i 2 ∪ wI j m lam i 3 ∪ wI j m lam i 4

def wA (j m : ℕ) (lam : ℝ) (i : ℕ) : Set ℝ :=
  (if m + 1 ≤ i ∧ i ≤ j + 1 then {zzR j m lam (i - 1)} else ∅) ∪
  (if m + 2 ≤ i ∧ i ≤ j + 2 then {zzL j m lam (i - 2)} else ∅) ∪
  (if i = m + 1 then {lam} else ∅)

def wQB (j m : ℕ) (lam : ℝ) (i : ℕ) : Set ℝ :=
  (if m + 1 ≤ i ∧ i ≤ j then Icc (zzR j m lam i) (zzL j m lam (i - 1)) else ∅) ∪
  (if i = m ∧ i ≤ j then Icc (zzR j m lam i) lam else ∅) ∪
  (if i = m ∧ i = j + 1 then Icc 0 lam else ∅) ∪
  (if m + 1 ≤ i ∧ i = j + 1 then Icc 0 (zzL j m lam (i - 1)) else ∅) ∪
  (if j + 2 < i ∧ (i - j) % 2 = 1 then Icc 0 1 else ∅)

def wQA (j m : ℕ) (lam : ℝ) (i : ℕ) : Set ℝ :=
  (if m + 2 ≤ i ∧ i ≤ j + 1 then Icc (zzR j m lam (i - 1)) (zzL j m lam (i - 2)) else ∅) ∪
  (if i = m + 1 ∧ i ≤ j + 1 then Icc (zzR j m lam (i - 1)) lam else ∅) ∪
  (if i = m + 1 ∧ i = j + 2 then Icc 0 lam else ∅) ∪
  (if m + 2 ≤ i ∧ i = j + 2 then Icc 0 (zzL j m lam (i - 2)) else ∅) ∪
  (if j + 2 < i ∧ (i - j) % 2 = 0 then Icc 0 1 else ∅)

theorem zU_pos {j m : ℕ} {lam : ℝ} (hl : 0 < lam) : 0 < zU j m lam := by
  unfold zU; positivity

theorem zz_lr (j m : ℕ) (lam : ℝ) (c : ℕ) : zzR j m lam c = zzL j m lam c + zU j m lam := by
  unfold zzR zzL zU; ring

theorem zzL_ge {j m : ℕ} {lam : ℝ} (hl : 0 < lam) (c : ℕ) : zU j m lam ≤ zzL j m lam c := by
  have hD : (0 : ℝ) < 2 * ((j - m : ℕ) : ℝ) + 3 := by positivity
  unfold zzL zU
  rw [div_le_div_iff_of_pos_right hD]
  have : (0 : ℝ) ≤ ((j - c : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem zz_step {j m c c' : ℕ} (lam : ℝ) (hc' : c' = c + 1) (hcj : c' ≤ j) :
    zzL j m lam c = zzR j m lam c' + zU j m lam := by
  have hc : ((j - c : ℕ) : ℝ) = ((j - c' : ℕ) : ℝ) + 1 := by
    norm_cast; omega
  unfold zzL zzR zU
  rw [hc]; ring

theorem zz_lam {j m c : ℕ} {lam : ℝ} (hl : 0 < lam) (hmc : m ≤ c) (hcj : c ≤ j) :
    zzR j m lam c + zU j m lam ≤ lam := by
  have hD : (0 : ℝ) < 2 * ((j - m : ℕ) : ℝ) + 3 := by positivity
  have hc : ((j - c : ℕ) : ℝ) ≤ ((j - m : ℕ) : ℝ) := Nat.cast_le.2 (by omega)
  unfold zzR zU
  rw [← add_div, div_le_iff₀ hD]
  nlinarith

theorem zU_le {j m : ℕ} {lam : ℝ} (hl : 0 < lam) : 3 * zU j m lam ≤ lam := by
  have hD : (0 : ℝ) < 2 * ((j - m : ℕ) : ℝ) + 3 := by positivity
  have : (0 : ℝ) ≤ ((j - m : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold zU
  rw [← mul_div_assoc, div_le_iff₀ hD]
  nlinarith

theorem zzR_grid {j m c : ℕ} (lam : ℝ) (hc : c ≤ j) :
    zzR j m lam c = zU j m lam * (2 * ((j : ℝ) - c) + 2) := by
  unfold zzR zU; rw [Nat.cast_sub hc]; ring

theorem zzL_grid {j m c : ℕ} (lam : ℝ) (hc : c ≤ j) :
    zzL j m lam c = zU j m lam * (2 * ((j : ℝ) - c) + 1) := by
  unfold zzL zU; rw [Nat.cast_sub hc]; ring

theorem lam_grid {j m : ℕ} {lam : ℝ} (hm : m ≤ j) :
    lam = zU j m lam * (2 * ((j : ℝ) - m) + 3) := by
  have hD : (2 * ((j : ℝ) - m) + 3) ≠ 0 := by
    have : (m : ℝ) ≤ j := Nat.cast_le.2 hm
    linarith
  unfold zU; rw [Nat.cast_sub hm, div_mul_cancel₀ _ hD]

theorem wδ_pos {j m : ℕ} {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) : 0 < wδ j m lam := by
  unfold wδ
  have := zU_pos (j := j) (m := m) hl0
  have : 0 < min (zU j m lam) (1 - lam) := lt_min this (by linarith)
  linarith

theorem wδ_le {j m : ℕ} {lam : ℝ} : 2 * wδ j m lam ≤ zU j m lam ∧ 2 * wδ j m lam ≤ 1 - lam := by
  unfold wδ
  constructor <;> [have := min_le_left (zU j m lam) (1 - lam); have := min_le_right (zU j m lam) (1 - lam)] <;> linarith

theorem wcases {i m j : ℕ} (hi : 1 ≤ i) (hm : 1 ≤ m) (hmj : m ≤ j + 1) :
    i < m ∨ (i = m ∧ i ≤ j) ∨ (i = m ∧ i = j + 1) ∨ (i = m + 1 ∧ i ≤ j) ∨
    (i = m + 1 ∧ i = j + 1) ∨ (i = m + 1 ∧ i = j + 2) ∨ (m + 2 ≤ i ∧ i ≤ j) ∨
    (m + 2 ≤ i ∧ i = j + 1) ∨ (m + 2 ≤ i ∧ i = j + 2) ∨ (j + 2 < i ∧ (i - j) % 2 = 0) ∨
    (j + 2 < i ∧ (i - j) % 2 = 1) := by
  omega


syntax "zzfacts" : tactic
set_option hygiene false in
macro_rules | `(tactic| zzfacts) => `(tactic|
  (have := zU_pos (j := j) (m := m) hl0
   have := zz_lr j m lam i
   have := zz_lr j m lam (i - 1)
   have := zz_lr j m lam (i - 2)
   have := zzL_ge (j := j) (m := m) hl0 i
   have := zzL_ge (j := j) (m := m) hl0 (i - 1)
   have := zzL_ge (j := j) (m := m) hl0 (i - 2)
   have := zz_lr j m lam (i + 1)
   have := zzL_ge (j := j) (m := m) hl0 (i + 1)
   have := zU_le (j := j) (m := m) hl0
   try have := zz_step (j := j) (m := m) (c := i) (c' := i + 1) lam (by omega) (by omega)
   try have := zz_lam (j := j) (m := m) (c := i + 1) hl0 (by omega) (by omega)
   try have := zz_step (j := j) (m := m) (c := i - 1) (c' := i) lam (by omega) (by omega)
   try have := zz_step (j := j) (m := m) (c := i - 2) (c' := i - 1) lam (by omega) (by omega)
   try have := zz_lam (j := j) (m := m) (c := i) hl0 (by omega) (by omega)
   try have := zz_lam (j := j) (m := m) (c := i - 1) hl0 (by omega) (by omega)
   try have := zz_lam (j := j) (m := m) (c := i - 2) hl0 (by omega) (by omega)))

syntax "cstep" term "," term : tactic
macro_rules | `(tactic| cstep $x, $a) => `(tactic|
  first | (rcases le_or_gt $x $a with hc | hc; · lsolve) | skip)

syntax "wsimp" : tactic
set_option hygiene false in
macro_rules | `(tactic| wsimp) => `(tactic|
  simp (disch := omega) only [wP, wI, wA, wQA, wQB, if_pos, if_neg, union_empty, empty_union,
      mem_union, mem_Icc, mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, false_or, or_false,
      Nat.add_sub_cancel, show i + 1 - 2 = i - 1 by omega, false_and, and_false] at *)

set_option maxHeartbeats 4000000 in
theorem w_cover {i m j : ℕ} {lam : ℝ} (hi : 1 ≤ i) (hm : 1 ≤ m) (hmj : m ≤ j + 1)
    (hl0 : 0 < lam) (hl1 : lam < 1) :
    Icc 0 1 ⊆ wP j m lam i ∪ wQA j m lam i ∪ wQB j m lam i := by
  intro μ ⟨h0, h1⟩
  rcases wcases hi hm hmj with h|h|h|h|h|h|h|h|h|h|h <;> wsimp <;> zzfacts <;>
  cstep μ, zzR j m lam i <;> cstep μ, zzL j m lam (i - 1) <;> cstep μ, zzR j m lam (i - 1) <;>
  cstep μ, zzL j m lam (i - 2) <;> cstep μ, lam <;> lsolve

set_option maxHeartbeats 4000000 in
theorem w_QA_P {i m j : ℕ} {lam : ℝ} (hi : 1 ≤ i) (hm : 1 ≤ m) (hmj : m ≤ j + 1)
    (hl0 : 0 < lam) (hl1 : lam < 1) :
    wQA j m lam i ∩ wP j m lam i ⊆ wA j m lam i := by
  intro μ hμ
  rcases wcases hi hm hmj with h|h|h|h|h|h|h|h|h|h|h <;> wsimp <;> zzfacts <;>
  casesm* _ ∨ _, _ ∧ _ <;> first | (exfalso; linarith) | lsolve

set_option maxHeartbeats 4000000 in
theorem w_QB_P {i m j : ℕ} {lam : ℝ} (hi : 1 ≤ i) (hm : 1 ≤ m) (hmj : m ≤ j + 1)
    (hl0 : 0 < lam) (hl1 : lam < 1) :
    wQB j m lam i ∩ wP j m lam i ⊆ wA j m lam (i + 1) := by
  intro μ hμ
  rcases wcases hi hm hmj with h|h|h|h|h|h|h|h|h|h|h <;> wsimp <;> zzfacts <;>
  casesm* _ ∨ _, _ ∧ _ <;> first | (exfalso; linarith) | lsolve

set_option maxHeartbeats 4000000 in
theorem w_QA_QB {i m j : ℕ} {lam : ℝ} (hi : 1 ≤ i) (hm : 1 ≤ m) (hmj : m ≤ j + 1)
    (hl0 : 0 < lam) (hl1 : lam < 1) : Disjoint (wQA j m lam i) (wQB j m lam i) := by
  rw [Set.disjoint_left]
  intro μ hA hB
  rcases wcases hi hm hmj with h|h|h|h|h|h|h|h|h|h|h <;> wsimp <;> zzfacts <;>
  casesm* _ ∨ _, _ ∧ _ <;> linarith

set_option maxHeartbeats 4000000 in
theorem w_A_sub {i m j : ℕ} {lam : ℝ} (hi : 1 ≤ i) (hm : 1 ≤ m) (hmj : m ≤ j + 1)
    (hl0 : 0 < lam) (hl1 : lam < 1) : wA j m lam i ⊆ Ioo 0 1 := by
  intro μ hμ
  rw [mem_Ioo]
  rcases wcases hi hm hmj with h|h|h|h|h|h|h|h|h|h|h <;> wsimp <;> zzfacts <;>
  casesm* _ ∨ _, _ ∧ _ <;> subst μ <;> constructor <;> linarith

set_option maxHeartbeats 4000000 in
theorem w_ends {i m j : ℕ} {lam : ℝ} (hi : 1 ≤ i) (hm : 1 ≤ m) (hmj : m ≤ j + 1)
    (hl0 : 0 < lam) (hl1 : lam < 1) :
    ((0 : ℝ) ∈ wQA j m lam i → j < i ∧ (i - j) % 2 = 0) ∧
    ((0 : ℝ) ∈ wQB j m lam i → j < i ∧ (i - j) % 2 = 1) ∧
    ((1 : ℝ) ∈ wQA j m lam i → j + 2 < i ∧ (i - j) % 2 = 0) ∧
    ((1 : ℝ) ∈ wQB j m lam i → j + 2 < i ∧ (i - j) % 2 = 1) ∧
    ((0 : ℝ) ∈ wP j m lam i → i ≤ j) ∧ ((1 : ℝ) ∈ wP j m lam i → i ≤ j + 2) := by
  rcases wcases hi hm hmj with h|h|h|h|h|h|h|h|h|h|h <;> wsimp <;> zzfacts <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try intro h') <;>
  casesm* _ ∨ _, _ ∧ _, False <;> first | trivial | omega | (exfalso; linarith)

syntax "gside" : tactic
set_option hygiene false in
macro_rules | `(tactic| gside) => `(tactic|
  (intro μ hμ1 hμ2; refine ⟨⟨by linarith, by linarith⟩, fun hP => ?_⟩;
   casesm* _ ∨ _, _ ∧ _, False <;> linarith))

set_option maxHeartbeats 4000000 in
theorem w_gap {i m j : ℕ} {lam : ℝ} (hi : 1 ≤ i) (hm : 1 ≤ m) (hmj : m ≤ j + 1)
    (hl0 : 0 < lam) (hl1 : lam < 1) {a : ℝ} (ha : a ∈ wA j m lam i ∪ wA j m lam (i + 1)) :
    (∀ μ, a < μ → μ < a + 2 * wδ j m lam → μ ∈ Ioo 0 1 ∧ μ ∉ wP j m lam i) ∨
    (∀ μ, a - 2 * wδ j m lam < μ → μ < a → μ ∈ Ioo 0 1 ∧ μ ∉ wP j m lam i) := by
  have hδ := wδ_pos (j := j) (m := m) hl0 hl1
  have hδ' := wδ_le (j := j) (m := m) (lam := lam)
  simp only [mem_Ioo]
  rcases wcases hi hm hmj with h|h|h|h|h|h|h|h|h|h|h <;> wsimp <;> zzfacts <;>
  casesm* _ ∨ _, _ ∧ _, False <;> subst a <;> first | (left; gside) | (right; gside)

set_option maxHeartbeats 4000000 in
theorem w_S3 {i m j : ℕ} {lam : ℝ} (hi : 1 ≤ i) (hm : 1 ≤ m) (hmj : m ≤ j + 1)
    (hl0 : 0 < lam) (hl1 : lam < 1) {a : ℝ} (ha : a ∈ wA j m lam (i + 1)) {μ : ℝ}
    (hμ : |μ - a| < 2 * wδ j m lam) : μ ∈ wP j m lam i ↔ μ ∈ wP j m lam (i + 1) := by
  have hδ := wδ_pos (j := j) (m := m) hl0 hl1
  have hδ' := wδ_le (j := j) (m := m) (lam := lam)
  rw [abs_lt] at hμ
  obtain ⟨hμ1, hμ2⟩ := hμ
  rcases (show i + 1 ≤ j ∨ i = j ∨ i = j + 1 ∨ j + 2 ≤ i by omega) with hj | hj | hj | hj <;>
  rcases wcases hi hm hmj with h|h|h|h|h|h|h|h|h|h|h <;> wsimp <;> zzfacts <;>
  casesm* _ ∨ _, _ ∧ _, False <;> subst a <;> constructor <;> intro hP <;>
  casesm* _ ∨ _, _ ∧ _, False <;> first | (exfalso; linarith) | lsolve

set_option maxHeartbeats 4000000 in
theorem w_I_disj {i m j : ℕ} {lam : ℝ} (hi : 1 ≤ i) (hm : 1 ≤ m) (hmj : m ≤ j + 1)
    (hl0 : 0 < lam) (hl1 : lam < 1) {k k' : ℕ} (hk : k < k') (hk' : k' < 5) {μ : ℝ}
    (h1 : μ ∈ wI j m lam i k) (h2 : μ ∈ wI j m lam i k') : False := by
  interval_cases k' <;> interval_cases k <;>
  rcases wcases hi hm hmj with h|h|h|h|h|h|h|h|h|h|h <;> wsimp <;> zzfacts <;>
  casesm* _ ∨ _, _ ∧ _, False <;> linarith

theorem w_A_grid {i m j : ℕ} {lam : ℝ} (hm : 1 ≤ m) (hmj : m ≤ j) {a : ℝ}
    (ha : a ∈ wA j m lam i) :
    a = zU j m lam * (2 * ((j : ℝ) - i) + 4) ∨ a = zU j m lam * (2 * ((j : ℝ) - i) + 5) := by
  simp only [wA, mem_union] at ha
  rcases ha with (ha | ha) | ha
  · split_ifs at ha with h
    · rw [mem_singleton_iff] at ha
      left
      rw [ha, zzR_grid lam (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    · exact absurd ha (notMem_empty _)
  · split_ifs at ha with h
    · rw [mem_singleton_iff] at ha
      right
      rw [ha, zzL_grid lam (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    · exact absurd ha (notMem_empty _)
  · split_ifs at ha with h
    · rw [mem_singleton_iff] at ha
      right
      rw [ha]; conv_lhs => rw [lam_grid (lam := lam) hmj]
      rw [h]; push_cast; ring
    · exact absurd ha (notMem_empty _)

theorem w_A_idx {i m j : ℕ} {lam : ℝ} (hmj : ¬ m ≤ j) {a : ℝ} (ha : a ∈ wA j m lam i) :
    i = m + 1 := by
  simp only [wA, mem_union] at ha
  rcases ha with (ha | ha) | ha <;> split_ifs at ha with hc <;>
    first | omega | exact absurd ha (notMem_empty _)

theorem int_of_real_eq {a b : ℕ} {c : ℤ} (h : 2 * (a : ℝ) - 2 * b = c) :
    2 * (a : ℤ) - 2 * b = c := by
  exact_mod_cast h

theorem w_A_disj {i i' m j : ℕ} {lam : ℝ} (hm : 1 ≤ m) (hl0 : 0 < lam) (hii : i ≠ i') :
    Disjoint (wA j m lam i) (wA j m lam i') := by
  rw [Set.disjoint_left]
  intro a h1 h2
  by_cases hmj : m ≤ j
  · have hU := zU_pos (j := j) (m := m) hl0
    have key : ∀ p q : ℝ, zU j m lam * p = zU j m lam * q → p = q := fun p q h =>
      mul_left_cancel₀ hU.ne' h
    rcases w_A_grid hm hmj h1 with e1 | e1 <;> rcases w_A_grid hm hmj h2 with e2 | e2
    · have := key _ _ (e1.symm.trans e2)
      have := int_of_real_eq (a := i') (b := i) (c := 0) (by push_cast; linarith)
      omega
    · have := key _ _ (e1.symm.trans e2)
      have := int_of_real_eq (a := i') (b := i) (c := 1) (by push_cast; linarith)
      omega
    · have := key _ _ (e1.symm.trans e2)
      have := int_of_real_eq (a := i) (b := i') (c := 1) (by push_cast; linarith)
      omega
    · have := key _ _ (e1.symm.trans e2)
      have := int_of_real_eq (a := i') (b := i) (c := 0) (by push_cast; linarith)
      omega
  · exact hii ((w_A_idx hmj h1).trans (w_A_idx hmj h2).symm)


/-! ### Both kinds of edges -/

/-- The parameters covered by the `i`-th sheet over an edge with event `e` and `j` curves at its
first end. -/
def eP (j : ℕ) : Option (ℕ × ℝ × ℝ) → ℕ → Set ℝ
  | none, i => if 1 ≤ i ∧ i ≤ j then Icc 0 1 else ∅
  | some (m, lam, _), i => wP j m lam i

/-- The parameters of the points of `αᵢ` over the edge. -/
def eA (j : ℕ) : Option (ℕ × ℝ × ℝ) → ℕ → Set ℝ
  | none, _ => ∅
  | some (m, lam, _), i => wA j m lam i

/-- Gaps of the `i`-th sheet whose ends lie in `αᵢ`. -/
def eQA (j : ℕ) : Option (ℕ × ℝ × ℝ) → ℕ → Set ℝ
  | none, i => if j < i ∧ (i - j) % 2 = 0 then Icc 0 1 else ∅
  | some (m, lam, _), i => wQA j m lam i

/-- Gaps of the `i`-th sheet whose ends lie in `αᵢ₊₁`. -/
def eQB (j : ℕ) : Option (ℕ × ℝ × ℝ) → ℕ → Set ℝ
  | none, i => if j < i ∧ (i - j) % 2 = 1 then Icc 0 1 else ∅
  | some (m, lam, _), i => wQB j m lam i

/-- The number of curves at the second end. -/
def eJ2 (j : ℕ) : Option (ℕ × ℝ × ℝ) → ℕ
  | none => j
  | some _ => j + 2

/-- The admissible events on an edge with `j` curves at its first end. -/
def EvOK (j : ℕ) : Option (ℕ × ℝ × ℝ) → Prop
  | none => True
  | some (m, lam, _) => 1 ≤ m ∧ m ≤ j + 1 ∧ 0 < lam ∧ lam < 1

/-- The radius of the local statements. -/
def eδ (j : ℕ) : Option (ℕ × ℝ × ℝ) → ℝ
  | none => 1 / 4
  | some (m, lam, _) => wδ j m lam

theorem eδ_pos {j : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) : 0 < eδ j e := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp [eδ]
  · exact wδ_pos he.2.2.1 he.2.2.2

theorem e_cover {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hi : 1 ≤ i) :
    Icc 0 1 ⊆ eP j e i ∪ eQA j e i ∪ eQB j e i := by
  rcases e with _ | ⟨m, lam, h⟩
  · intro μ hμ
    simp only [eP, eQA, eQB]
    rcases Nat.mod_two_eq_zero_or_one (i - j) with hp | hp <;>
    by_cases hij : i ≤ j <;> simp (disch := omega) only [if_pos, if_neg, mem_union] <;> simp_all
  · exact w_cover hi he.1 he.2.1 he.2.2.1 he.2.2.2

theorem e_QA_P {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hi : 1 ≤ i) :
    eQA j e i ∩ eP j e i ⊆ eA j e i := by
  rcases e with _ | ⟨m, lam, h⟩
  · rintro μ ⟨h1, h2⟩
    simp only [eQA, eP] at h1 h2
    split_ifs at h1 h2 <;> first | omega | simp_all
  · exact w_QA_P hi he.1 he.2.1 he.2.2.1 he.2.2.2

theorem e_QB_P {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hi : 1 ≤ i) :
    eQB j e i ∩ eP j e i ⊆ eA j e (i + 1) := by
  rcases e with _ | ⟨m, lam, h⟩
  · rintro μ ⟨h1, h2⟩
    simp only [eQB, eP] at h1 h2
    split_ifs at h1 h2 <;> first | omega | simp_all
  · exact w_QB_P hi he.1 he.2.1 he.2.2.1 he.2.2.2

theorem e_QA_QB {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hi : 1 ≤ i) :
    Disjoint (eQA j e i) (eQB j e i) := by
  rcases e with _ | ⟨m, lam, h⟩
  · rw [Set.disjoint_left]
    intro μ h1 h2
    simp only [eQA, eQB] at h1 h2
    split_ifs at h1 h2 <;> first | omega | simp_all
  · exact w_QA_QB hi he.1 he.2.1 he.2.2.1 he.2.2.2

theorem e_A_sub {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hi : 1 ≤ i) :
    eA j e i ⊆ Ioo 0 1 := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp [eA]
  · exact w_A_sub hi he.1 he.2.1 he.2.2.1 he.2.2.2

theorem e_A_finite (j : ℕ) (e : Option (ℕ × ℝ × ℝ)) (i : ℕ) : (eA j e i).Finite := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp [eA]
  · simp only [eA, wA]
    refine ((Finite.union ?_ ?_).union ?_) <;> split_ifs <;> simp

theorem e_ends {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hi : 1 ≤ i) :
    ((0 : ℝ) ∈ eQA j e i → j < i ∧ (i - j) % 2 = 0) ∧
    ((0 : ℝ) ∈ eQB j e i → j < i ∧ (i - j) % 2 = 1) ∧
    ((1 : ℝ) ∈ eQA j e i → eJ2 j e < i ∧ (i - eJ2 j e) % 2 = 0) ∧
    ((1 : ℝ) ∈ eQB j e i → eJ2 j e < i ∧ (i - eJ2 j e) % 2 = 1) ∧
    ((0 : ℝ) ∈ eP j e i → i ≤ j) ∧ ((1 : ℝ) ∈ eP j e i → i ≤ eJ2 j e) := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp only [eQA, eQB, eP, eJ2]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h' <;> split_ifs at h' <;> first | omega | simp_all
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := w_ends hi he.1 he.2.1 he.2.2.1 he.2.2.2 (lam := lam)
    simp only [eQA, eQB, eP, eJ2]
    refine ⟨h1, h2, fun h' => ?_, fun h' => ?_, h5, h6⟩
    · have := h3 h'; omega
    · have := h4 h'; omega

theorem e_gap {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hi : 1 ≤ i) {a : ℝ}
    (ha : a ∈ eA j e i ∪ eA j e (i + 1)) :
    (∀ μ, a < μ → μ < a + 2 * eδ j e → μ ∈ Ioo 0 1 ∧ μ ∉ eP j e i) ∨
    (∀ μ, a - 2 * eδ j e < μ → μ < a → μ ∈ Ioo 0 1 ∧ μ ∉ eP j e i) := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp [eA] at ha
  · exact w_gap hi he.1 he.2.1 he.2.2.1 he.2.2.2 ha

theorem e_S3 {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hi : 1 ≤ i) {a : ℝ}
    (ha : a ∈ eA j e (i + 1)) {μ : ℝ} (hμ : |μ - a| < 2 * eδ j e) :
    μ ∈ eP j e i ↔ μ ∈ eP j e (i + 1) := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp [eA] at ha
  · exact w_S3 hi he.1 he.2.1 he.2.2.1 he.2.2.2 ha hμ

theorem e_A_disj {j i i' : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hii : i ≠ i') :
    Disjoint (eA j e i) (eA j e i') := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp [eA]
  · exact w_A_disj he.1 he.2.2.1 hii

theorem e_A_one {j : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) : eA j e 1 = ∅ := by
  rcases e with _ | ⟨m, lam, h⟩
  · rfl
  · have := he.1
    simp only [eA, wA]
    simp (disch := omega) only [if_neg, union_empty]

theorem e_A_top {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hi : eJ2 j e < i) :
    eA j e i = ∅ := by
  rcases e with _ | ⟨m, lam, h⟩
  · rfl
  · have := he.2.1
    simp only [eJ2] at hi
    simp only [eA, wA]
    simp (disch := omega) only [if_neg, union_empty]

theorem e_P_sub {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) : eP j e i ⊆ Icc 0 1 := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp only [eP]; split_ifs <;> simp
  · obtain ⟨hm, hmj, hl0, hl1⟩ := he
    intro μ hμ
    simp only [eP, wP, wI, mem_union] at hμ
    have h1 := zzL_ge (j := j) (m := m) hl0 (i - 1)
    have h2 := zzL_ge (j := j) (m := m) hl0 (i - 2)
    have h3 := zU_pos (j := j) (m := m) hl0
    rcases hμ with (((h | h) | h) | h) | h <;> split_ifs at h with hc <;>
      first | exact absurd h (notMem_empty _) | skip
    · exact h
    · rw [mem_Icc] at h ⊢
      have := zz_lam (j := j) (m := m) (c := i) hl0 hc.1 hc.2
      constructor <;> linarith
    · rw [mem_Icc] at h ⊢
      have := zz_lam (j := j) (m := m) (c := i - 1) hl0 (by omega) (by omega)
      constructor <;> linarith
    · rw [mem_Icc] at h ⊢; constructor <;> linarith
    · rw [mem_Icc] at h ⊢; constructor <;> linarith

end

end HPC.HO16
