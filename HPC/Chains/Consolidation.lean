import HPC.Chains.Basic
import HPC.Chains.Auxiliary

/-!
# Consolidation infrastructure

Block consolidations as an explicit block map, chain reversal, crookedness of and in
subchains, the minimal and maximal index maps of a refinement, the monotone grouping lemma,
the easy case of Bing 1948 Theorem 4, and a counterexample showing that the strong reading
of "contained in only the first link" is false.

English proofs: COMMISSION-batch4.md §3.
-/

namespace HPC

open Set

/-- The increasing case of `exists_adjacent_cross`. -/
theorem exists_adjacent_cross_mono {g : ℕ → ℤ} (hstep : ∀ t, |g (t + 1) - g t| ≤ 1) {a b : ℕ}
    {p : ℤ} (hab : a ≤ b) (h1 : g a ≤ p) (h2 : p + 1 ≤ g b) :
    ∃ t, a ≤ t ∧ t + 1 ≤ b ∧ g t = p ∧ g (t + 1) = p + 1 := by
  classical
  have hstep' : ∀ t, g (t + 1) - g t ≤ 1 ∧ -(1 : ℤ) ≤ g (t + 1) - g t := fun t =>
    ⟨(abs_le.mp (hstep t)).2, (abs_le.mp (hstep t)).1⟩
  have hex : ∃ t, a ≤ t ∧ p + 1 ≤ g t := ⟨b, hab, h2⟩
  set y := Nat.find hex with hy
  obtain ⟨hay, hgy⟩ : a ≤ y ∧ p + 1 ≤ g y := Nat.find_spec hex
  have hyb : y ≤ b := Nat.find_le ⟨hab, h2⟩
  have hay' : a < y := by
    rcases hay.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hgy) (by omega)
  have hmin := Nat.find_min hex (m := y - 1) (by omega)
  rw [not_and_or] at hmin
  have hs := hstep' (y - 1)
  have hy1 : y - 1 + 1 = y := by omega
  rw [hy1] at hs
  refine ⟨y - 1, by omega, by omega, ?_, ?_⟩
  · rcases hmin with hm | hm <;> omega
  · rw [hy1]; rcases hmin with hm | hm <;> omega

/-- A discrete crossing lemma: a function on `ℕ` moving by at most one at each step and
passing from a value `≤ p` to a value `≥ p + 1` has two *adjacent* indices, between the two
given ones, carrying the values `p` and `p + 1` (in one order or the other). -/
theorem exists_adjacent_cross {g : ℕ → ℤ} (hstep : ∀ t, |g (t + 1) - g t| ≤ 1) {a b : ℕ}
    {p : ℤ} (h1 : g a ≤ p) (h2 : p + 1 ≤ g b) :
    ∃ t, min a b ≤ t ∧ t + 1 ≤ max a b ∧
      ((g t = p ∧ g (t + 1) = p + 1) ∨ (g t = p + 1 ∧ g (t + 1) = p)) := by
  rcases le_total a b with hab | hab
  · obtain ⟨t, h3, h4, h5, h6⟩ := exists_adjacent_cross_mono hstep hab h1 h2
    exact ⟨t, by omega, by omega, Or.inl ⟨h5, h6⟩⟩
  · have hstep2 : ∀ t, |(-g) (t + 1) - (-g) t| ≤ 1 := by
      intro t
      have h := hstep t
      rw [abs_sub_comm] at h
      simpa [show -g (t + 1) + g t = g t - g (t + 1) by ring] using h
    obtain ⟨t, h3, h4, h5, h6⟩ :=
      exists_adjacent_cross_mono (g := -g) (p := -(p + 1)) hstep2 hab (by simpa using h2)
        (by simpa using h1)
    have e5 : -g t = -(p + 1) := h5
    have e6 : -g (t + 1) = -(p + 1) + 1 := h6
    exact ⟨t, by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩

variable {X : Type*} [MetricSpace X]

namespace Chain

variable {n m p : ℕ}

/-! ## Block consolidations -/

/-- A block map: a surjection `β : Fin n → Fin p` moving by at most one between adjacent
indices. -/
structure IsBlockMap (β : Fin n → Fin p) : Prop where
  surj : Function.Surjective β
  lip : ∀ t t' : Fin n, t'.val = t.val + 1 → ((β t' : ℤ) - (β t : ℤ)).natAbs ≤ 1

/-- The links of the block consolidation satisfy the adjacency condition of a chain. -/
theorem blockLink_adjacent (D : Chain X n) {β : Fin n → Fin p} (hβ : IsBlockMap β)
    (u u' : Fin p) :
    (((⋃ t ∈ {t | β t = u}, D.link t) ∩ ⋃ t ∈ {t | β t = u'}, D.link t).Nonempty) ↔
      ((u : ℤ) - (u' : ℤ)).natAbs ≤ 1 := by
  have hmem : ∀ (v : Fin p) (t : Fin n) (z : X), β t = v → z ∈ D.link t →
      z ∈ ⋃ t ∈ {t | β t = v}, D.link t := by
    intro v t z hv hz
    exact Set.mem_biUnion (show t ∈ {t | β t = v} from hv) hz
  have hmem' : ∀ (v : Fin p) (z : X), z ∈ (⋃ t ∈ {t | β t = v}, D.link t) →
      ∃ t, β t = v ∧ z ∈ D.link t := by
    intro v z hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hz
    exact hz
  -- the essential case: two consecutive blocks meet
  have key : ∀ u u' : Fin p, u'.val = u.val + 1 →
      (((⋃ t ∈ {t | β t = u}, D.link t) ∩ ⋃ t ∈ {t | β t = u'}, D.link t).Nonempty) := by
    intro u u' huu'
    obtain ⟨t₀, ht₀⟩ := hβ.surj u
    obtain ⟨t₁, ht₁⟩ := hβ.surj u'
    have hn : 0 < n := t₀.pos
    set c : ℕ → Fin n := fun x => ⟨min x (n - 1), by omega⟩ with hc
    set G : ℕ → ℤ := fun x => ((β (c x) : Fin p) : ℤ) with hG
    have hcval : ∀ t : Fin n, c t.val = t := by
      intro t
      have := t.isLt
      exact Fin.ext (by simp only [hc]; omega)
    have hGstep : ∀ x, |G (x + 1) - G x| ≤ 1 := by
      intro x
      by_cases hx : x + 1 ≤ n - 1
      · have hsucc : (c (x + 1)).val = (c x).val + 1 := by simp only [hc]; omega
        have hlip := hβ.lip (c x) (c (x + 1)) hsucc
        rw [abs_le]
        simp only [hG]
        omega
      · have heq : c (x + 1) = c x := Fin.ext (by simp only [hc]; omega)
        simp [hG, heq]
    have hGt₀ : G t₀.val = (u : ℕ) := by simp only [hG, hcval t₀, ht₀]
    have hGt₁ : G t₁.val = (u' : ℕ) := by simp only [hG, hcval t₁, ht₁]
    obtain ⟨t, htmin, htmax, hcase⟩ :=
      exists_adjacent_cross hGstep (a := t₀.val) (b := t₁.val) (p := ((u : ℕ) : ℤ))
        (by rw [hGt₀]) (by rw [hGt₁]; omega)
    have ht₀l := t₀.isLt
    have ht₁l := t₁.isLt
    have hcv : (c t).val = t := by simp only [hc]; omega
    have hcv1 : (c (t + 1)).val = t + 1 := by simp only [hc]; omega
    obtain ⟨z, hz1, hz2⟩ := (D.adjacent_iff (c t) (c (t + 1))).mpr (by omega)
    have hval : ∀ x : ℕ, ∀ v : Fin p, G x = ((v : ℕ) : ℤ) → β (c x) = v := by
      intro x v hx
      simp only [hG] at hx
      exact Fin.ext (by exact_mod_cast hx)
    rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine ⟨z, hmem u (c t) z (hval t u e1) hz1, hmem u' (c (t + 1)) z ?_ hz2⟩
      exact hval (t + 1) u' (by rw [e2]; omega)
    · refine ⟨z, hmem u (c (t + 1)) z (hval (t + 1) u e2) hz2, hmem u' (c t) z ?_ hz1⟩
      exact hval t u' (by rw [e1]; omega)
  constructor
  · rintro ⟨z, hz1, hz2⟩
    obtain ⟨t, ht, hzt⟩ := hmem' u z hz1
    obtain ⟨t', ht', hzt'⟩ := hmem' u' z hz2
    have hadj := (D.adjacent_iff t t').mp ⟨z, hzt, hzt'⟩
    rcases eq_or_ne t.val t'.val with heq | hne
    · have : t = t' := Fin.ext heq
      subst this
      simp [← ht, ← ht']
    · rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hβ.lip t t' (by omega)
        rw [ht, ht'] at this
        omega
      · have := hβ.lip t' t (by omega)
        rw [ht, ht'] at this
        omega
  · intro hle
    rcases lt_trichotomy u.val u'.val with hlt | heq | hgt
    · exact key u u' (by omega)
    · have : u = u' := Fin.ext heq
      subst this
      obtain ⟨t, ht⟩ := hβ.surj u
      obtain ⟨z, hz⟩ := D.link_nonempty t
      exact ⟨z, hmem u t z ht hz, hmem u t z ht hz⟩
    · obtain ⟨z, hz1, hz2⟩ := key u' u (by omega)
      exact ⟨z, hz2, hz1⟩

/-- The chain whose `u`-th link is the union of the links of `D` in block `u`. -/
def ofBlocks (D : Chain X n) (β : Fin n → Fin p) (hβ : IsBlockMap β) : Chain X p where
  link u := ⋃ t ∈ {t | β t = u}, D.link t
  isOpen _ := isOpen_biUnion fun t _ => D.isOpen t
  adjacent u u' := blockLink_adjacent D hβ u u'

theorem ofBlocks_link (D : Chain X n) (β : Fin n → Fin p) (hβ : IsBlockMap β) (u : Fin p) :
    (D.ofBlocks β hβ).link u = ⋃ t ∈ {t | β t = u}, D.link t := rfl

/-- `ofBlocks` is a consolidation in the sense of batch-1 D6. -/
theorem ofBlocks_isConsolidationOf (D : Chain X n) (β : Fin n → Fin p) (hβ : IsBlockMap β) :
    (D.ofBlocks β hβ).IsConsolidationOf D :=
  ⟨fun t => ⟨β t, Set.subset_biUnion_of_mem (u := fun t => D.link t) (show β t = β t from rfl)⟩,
    fun u => ⟨{t | β t = u}, rfl⟩⟩

/-!
Note: the converse — that every consolidation in the sense of batch-1 D6 arises from a block
map — is false, because D6 does not require the blocks to partition the index set. From this
batch on, Theorems 3–5 are stated for block consolidations (`ofBlocks`). D6 remains in use
only where it already is (Theorem 12), where only its consequences were needed.
-/

/-! ## Reversal -/

/-- The reverse of a chain. -/
def reverse (D : Chain X n) : Chain X n where
  link i := D.link (Fin.rev i)
  isOpen i := D.isOpen _
  adjacent i j := by
    rw [D.adjacent_iff]
    have hi := i.isLt
    have hj := j.isLt
    rw [Fin.val_rev, Fin.val_rev]
    omega

@[simp] theorem reverse_link (D : Chain X n) (i : Fin n) :
    D.reverse.link i = D.link (Fin.rev i) := rfl

theorem reverse_reverse (D : Chain X n) : D.reverse.reverse = D := by
  cases D with
  | mk link isOpen adjacent =>
    have : (fun i => link (Fin.rev (Fin.rev i))) = link := by
      funext i; rw [Fin.rev_rev]
    simp only [reverse, this]

theorem Refines.reverse_left {E : Chain X m} {D : Chain X n} (h : E.Refines D) :
    E.reverse.Refines D := fun i => h (Fin.rev i)

theorem Refines.reverse_right {E : Chain X m} {D : Chain X n} (h : E.Refines D) :
    E.Refines D.reverse := by
  intro i
  obtain ⟨j, hj⟩ := h i
  exact ⟨Fin.rev j, by rw [reverse_link, Fin.rev_rev]; exact hj⟩

/-- Crookedness (1948 sense) is unaffected by reversing the fine chain. -/
theorem IsCrookedIn'.reverse_left {E : Chain X m} {D : Chain X n} (h : E.IsCrookedIn' D) :
    E.reverse.IsCrookedIn' D := by
  obtain ⟨hR, hC⟩ := h
  refine ⟨hR.reverse_left, ?_⟩
  intro a b hab i j hi hj
  rw [reverse_link] at hi hj
  obtain ⟨r, s, hbtw, hr, hs⟩ := hC a b hab (Fin.rev i) (Fin.rev j) hi hj
  refine ⟨Fin.rev r, Fin.rev s, ?_, by rw [reverse_link, Fin.rev_rev]; exact hr,
    by rw [reverse_link, Fin.rev_rev]; exact hs⟩
  have hlt : ∀ x y : Fin m, x < y → Fin.rev y < Fin.rev x := by
    intro x y hxy
    have hx := x.isLt
    have hy := y.isLt
    have hxy' : x.val < y.val := hxy
    show (Fin.rev y).val < (Fin.rev x).val
    simp only [Fin.val_rev]
    omega
  rcases hbtw with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine Or.inr ⟨?_, hlt _ _ h2, ?_⟩
    · have g := hlt _ _ h1
      rwa [Fin.rev_rev] at g
    · have g := hlt _ _ h3
      rwa [Fin.rev_rev] at g
  · refine Or.inl ⟨?_, hlt _ _ h2, ?_⟩
    · have g := hlt _ _ h1
      rwa [Fin.rev_rev] at g
    · have g := hlt _ _ h3
      rwa [Fin.rev_rev] at g

/-- Crookedness (1948 sense) is unaffected by reversing the coarse chain. -/
theorem IsCrookedIn'.reverse_right {E : Chain X m} {D : Chain X n} (h : E.IsCrookedIn' D) :
    E.IsCrookedIn' D.reverse := by
  obtain ⟨hR, hC⟩ := h
  refine ⟨hR.reverse_right, ?_⟩
  intro a b hab i j hi hj
  have hal := a.isLt
  have hbl := b.isLt
  rw [reverse_link] at hi hj
  have hva := Fin.val_rev a
  have hvb := Fin.val_rev b
  have hrev : (Fin.rev b).val + 2 < (Fin.rev a).val := by omega
  obtain ⟨r, s, hbtw, hr, hs⟩ := hC (Fin.rev b) (Fin.rev a) hrev j i hj hi
  refine ⟨s, r, hbtw.symm, ?_, ?_⟩
  · rw [reverse_link]
    have heq : Fin.rev (⟨b.val - 1, by omega⟩ : Fin n) = ⟨(Fin.rev b).val + 1, by omega⟩ :=
      Fin.ext (by simp only [Fin.val_rev]; omega)
    rw [heq]
    exact hs
  · rw [reverse_link]
    have heq : Fin.rev (⟨a.val + 1, by omega⟩ : Fin n) = ⟨(Fin.rev a).val - 1, by omega⟩ :=
      Fin.ext (by simp only [Fin.val_rev]; omega)
    rw [heq]
    exact hr

/-! ## Subchains -/

/-- A subchain of a crooked chain is crooked in the same coarse chain. -/
theorem IsCrookedIn'.sub {E : Chain X m} {D : Chain X n} (h : E.IsCrookedIn' D)
    (i j : Fin m) (hij : i ≤ j) : (E.sub i j hij).IsCrookedIn' D := by
  obtain ⟨hR, hC⟩ := h
  have hij' : i.val ≤ j.val := hij
  have hjl := j.isLt
  have hsublink : ∀ t : Fin (j.val - i.val + 1),
      (E.sub i j hij).link t = E.link ⟨i.val + t.val, by have := t.isLt; omega⟩ := fun _ => rfl
  refine ⟨fun t => ?_, ?_⟩
  · rw [hsublink]
    exact hR _
  intro a b hab c d hc hd
  rw [hsublink] at hc hd
  obtain ⟨r, s, hbtw, hr, hs⟩ := hC a b hab _ _ hc hd
  have hcl := c.isLt
  have hdl := d.isLt
  have hbtwv : (i.val + c.val < r.val ∧ r.val < s.val ∧ s.val < i.val + d.val) ∨
      (i.val + c.val > r.val ∧ r.val > s.val ∧ s.val > i.val + d.val) := by
    rcases hbtw with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2, h3⟩
  have hrb : i.val ≤ r.val ∧ r.val ≤ j.val := by omega
  have hsb : i.val ≤ s.val ∧ s.val ≤ j.val := by omega
  refine ⟨⟨r.val - i.val, by omega⟩, ⟨s.val - i.val, by omega⟩, ?_, ?_, ?_⟩
  · rcases hbtwv with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨by simp only [Fin.lt_def]; omega, by simp only [Fin.lt_def]; omega,
        by simp only [Fin.lt_def]; omega⟩
    · exact Or.inr ⟨by simp only [Fin.lt_def, gt_iff_lt]; omega,
        by simp only [Fin.lt_def, gt_iff_lt]; omega, by simp only [Fin.lt_def, gt_iff_lt]; omega⟩
  · rw [hsublink]
    have : (⟨i.val + (r.val - i.val), by omega⟩ : Fin m) = r := Fin.ext (by simp; omega)
    rw [this]
    exact hr
  · rw [hsublink]
    have : (⟨i.val + (s.val - i.val), by omega⟩ : Fin m) = s := Fin.ext (by simp; omega)
    rw [this]
    exact hs

/-- If `E` is crooked in `D` and every link of `E` lies in a link of the subchain `D.sub a b`,
then `E` is crooked in `D.sub a b`. -/
theorem IsCrookedIn'.restrict {E : Chain X m} {D : Chain X n} (h : E.IsCrookedIn' D)
    (a b : Fin n) (hab : a ≤ b) (hE : E.Refines (D.sub a b hab)) :
    E.IsCrookedIn' (D.sub a b hab) := by
  obtain ⟨-, hC⟩ := h
  have hab' : a.val ≤ b.val := hab
  have hbl := b.isLt
  have hsublink : ∀ t : Fin (b.val - a.val + 1),
      (D.sub a b hab).link t = D.link ⟨a.val + t.val, by have := t.isLt; omega⟩ := fun _ => rfl
  refine ⟨hE, ?_⟩
  intro hh k hk i j hi hj
  have hhl := hh.isLt
  have hkl := k.isLt
  rw [hsublink] at hi hj
  obtain ⟨r, s, hbtw, hr, hs⟩ :=
    hC ⟨a.val + hh.val, by omega⟩ ⟨a.val + k.val, by omega⟩ (by simp only []; omega) i j hi hj
  refine ⟨r, s, hbtw, ?_, ?_⟩
  · rw [hsublink]
    have : (⟨a.val + (k.val - 1), by omega⟩ : Fin n) = ⟨a.val + k.val - 1, by omega⟩ :=
      Fin.ext (by simp only []; omega)
    rw [this]
    exact hr
  · rw [hsublink]
    have : (⟨a.val + (hh.val + 1), by omega⟩ : Fin n) = ⟨a.val + hh.val + 1, by omega⟩ :=
      Fin.ext (by simp only []; omega)
    rw [this]
    exact hs

/-! ## Minimal and maximal index of a refinement -/

variable {E : Chain X m} {D : Chain X n}

/-- A link lies in at most two links of a coarser chain, and those are adjacent. The
hypothesis that `E` refines `D` is not needed: the two containments are enough. -/
theorem subset_adjacent_of_subset (_h : E.Refines D) (t : Fin m) {j j' : Fin n}
    (hj : E.link t ⊆ D.link j) (hj' : E.link t ⊆ D.link j') :
    ((j : ℤ) - (j' : ℤ)).natAbs ≤ 1 := by
  obtain ⟨z, hz⟩ := E.link_nonempty t
  exact (D.adjacent j j').mp ⟨z, hj hz, hj' hz⟩

/-- The indices of links of `D` containing `E.link t` form a nonempty set of naturals. -/
theorem minIdx_set_nonempty (h : E.Refines D) (t : Fin m) :
    {j : ℕ | ∃ hj : j < n, E.link t ⊆ D.link ⟨j, hj⟩}.Nonempty := by
  obtain ⟨j, hj⟩ := h t
  exact ⟨j.val, j.isLt, hj⟩

/-- The least index of a link of `D` containing `E.link t`. -/
noncomputable def Refines.minIdx (h : E.Refines D) (t : Fin m) : Fin n :=
  ⟨sInf {j : ℕ | ∃ hj : j < n, E.link t ⊆ D.link ⟨j, hj⟩},
    Exists.elim (Nat.sInf_mem (minIdx_set_nonempty h t)) fun hj _ => hj⟩

theorem minIdx_subset (h : E.Refines D) (t : Fin m) : E.link t ⊆ D.link (h.minIdx t) := by
  obtain ⟨hj, hsub⟩ := Nat.sInf_mem (minIdx_set_nonempty h t)
  exact hsub

theorem minIdx_le (h : E.Refines D) (t : Fin m) {j : Fin n} (hj : E.link t ⊆ D.link j) :
    h.minIdx t ≤ j := by
  have hmem : (j : ℕ) ∈ {j : ℕ | ∃ hj : j < n, E.link t ⊆ D.link ⟨j, hj⟩} := ⟨j.isLt, hj⟩
  exact Nat.sInf_le hmem

/-- The greatest index of a link of `D` containing `E.link t`. -/
noncomputable def Refines.maxIdx (h : E.Refines D) (t : Fin m) : Fin n :=
  Fin.rev (h.reverse_right.minIdx t)

theorem maxIdx_subset (h : E.Refines D) (t : Fin m) : E.link t ⊆ D.link (h.maxIdx t) :=
  minIdx_subset h.reverse_right t

theorem le_maxIdx (h : E.Refines D) (t : Fin m) {j : Fin n} (hj : E.link t ⊆ D.link j) :
    j ≤ h.maxIdx t := by
  have h2 : E.link t ⊆ D.reverse.link (Fin.rev j) := by
    rw [reverse_link, Fin.rev_rev]; exact hj
  have h3 := minIdx_le h.reverse_right t h2
  have g := Fin.rev_le_rev.mpr h3
  rwa [Fin.rev_rev] at g

/-- `minIdx` moves by at most one between adjacent links. -/
theorem minIdx_lip (h : E.Refines D) (t t' : Fin m) (htt' : t'.val = t.val + 1) :
    ((h.minIdx t' : ℤ) - (h.minIdx t : ℤ)).natAbs ≤ 1 := by
  obtain ⟨z, hz1, hz2⟩ := (E.adjacent_iff t' t).mpr (by omega)
  exact (D.adjacent _ _).mp ⟨z, minIdx_subset h t' hz1, minIdx_subset h t hz2⟩

theorem maxIdx_lip (h : E.Refines D) (t t' : Fin m) (htt' : t'.val = t.val + 1) :
    ((h.maxIdx t' : ℤ) - (h.maxIdx t : ℤ)).natAbs ≤ 1 := by
  obtain ⟨z, hz1, hz2⟩ := (E.adjacent_iff t' t).mpr (by omega)
  exact (D.adjacent _ _).mp ⟨z, maxIdx_subset h t' hz1, maxIdx_subset h t hz2⟩

/-- A link meeting `D.link j` has minimal index within one of `j`. -/
theorem minIdx_near_of_inter (h : E.Refines D) (t : Fin m) (j : Fin n)
    (hne : (E.link t ∩ D.link j).Nonempty) :
    ((h.minIdx t : ℤ) - (j : ℤ)).natAbs ≤ 1 := by
  obtain ⟨z, hz1, hz2⟩ := hne
  exact (D.adjacent _ _).mp ⟨z, minIdx_subset h t hz1, hz2⟩

/-! ## The monotone grouping -/

/-- The group of a coarse index `j` in a chain of `n ≥ 4` links: `0` for `j ≤ 1`, `j − 1`
for `2 ≤ j ≤ n − 3`, and `n − 3` for `j ≥ n − 2`. Groups `0` and `n − 3` are the doubled ends. -/
def group (n : ℕ) (j : ℕ) : ℕ := min (j - 1) (n - 3)

/-- **The monotone grouping lemma**, in existential form: the block map used to prove it is
the one produced here, and `monoBlocks` is a choice of it. -/
theorem Refines.exists_monoBlocks (h : E.Refines D) (hn : 4 ≤ n) :
    ∃ (p : ℕ) (β : Fin m → Fin p) (hβ : IsBlockMap β),
      (∀ u : Fin p, ∃ j : Fin n, ∃ hj : j.val + 1 < n,
          (E.ofBlocks β hβ).link u ⊆ D.link j ∪ D.link ⟨j.val + 1, hj⟩) ∧
      (∀ t, (h.minIdx t).val ≤ 1 → (β t).val = 0) ∧
      (∀ t, n - 2 ≤ (h.minIdx t).val → (β t).val = p - 1) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨0, fun t => t.elim0, ⟨fun b => b.elim0, fun t => t.elim0⟩, fun u => u.elim0,
      fun t => t.elim0, fun t => t.elim0⟩
  -- the group of the minimal index
  set gn : Fin m → ℕ := fun t => group n (h.minIdx t).val with hgn
  have hgnle : ∀ t, gn t ≤ n - 3 := fun t => by simp only [hgn, group]; omega
  have hglip : ∀ t t' : Fin m, t'.val = t.val + 1 → gn t' ≤ gn t + 1 ∧ gn t ≤ gn t' + 1 := by
    intro t t' htt'
    have hl := minIdx_lip h t t' htt'
    simp only [hgn, group]
    omega
  have hune : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  obtain ⟨t₀, -, ht₀⟩ := Finset.exists_min_image Finset.univ gn hune
  obtain ⟨t₁, -, ht₁⟩ := Finset.exists_max_image Finset.univ gn hune
  have hg₀ : ∀ t, gn t₀ ≤ gn t := fun t => ht₀ t (Finset.mem_univ _)
  have hg₁ : ∀ t, gn t ≤ gn t₁ := fun t => ht₁ t (Finset.mem_univ _)
  set g₀ := gn t₀ with hg₀def
  set g₁ := gn t₁ with hg₁def
  have hg₀₁ : g₀ ≤ g₁ := hg₀ t₁
  set P : ℕ := g₁ - g₀ + 1 with hP
  set β : Fin m → Fin P := fun t => ⟨gn t - g₀, by have := hg₁ t; omega⟩ with hβdef
  have hbval : ∀ t, (β t).val = gn t - g₀ := fun _ => rfl
  -- the index walk used for surjectivity
  set c : ℕ → Fin m := fun x => ⟨min x (m - 1), by omega⟩ with hc
  set G : ℕ → ℤ := fun x => (gn (c x) : ℤ) with hG
  have hcval : ∀ t : Fin m, c t.val = t := by
    intro t
    have := t.isLt
    exact Fin.ext (by simp only [hc]; omega)
  have hGstep : ∀ x, |G (x + 1) - G x| ≤ 1 := by
    intro x
    by_cases hx : x + 1 ≤ m - 1
    · have hsucc : (c (x + 1)).val = (c x).val + 1 := by simp only [hc]; omega
      have := hglip (c x) (c (x + 1)) hsucc
      rw [abs_le]
      simp only [hG]
      omega
    · have heq : c (x + 1) = c x := Fin.ext (by simp only [hc]; omega)
      simp [hG, heq]
  have hattained : ∀ v : ℕ, g₀ ≤ v → v ≤ g₁ → ∃ t, gn t = v := by
    intro v hv0 hv1
    rcases eq_or_lt_of_le hv0 with heq | hlt
    · exact ⟨t₀, by omega⟩
    · have hGa : G t₀.val ≤ (v : ℤ) - 1 := by simp only [hG, hcval t₀]; omega
      have hGb : ((v : ℤ) - 1) + 1 ≤ G t₁.val := by simp only [hG, hcval t₁]; omega
      obtain ⟨x, -, -, hcase⟩ := exists_adjacent_cross hGstep hGa hGb
      rcases hcase with ⟨-, e2⟩ | ⟨e1, -⟩
      · refine ⟨c (x + 1), ?_⟩
        have : (gn (c (x + 1)) : ℤ) = (v : ℤ) := by simp only [hG] at e2; omega
        exact_mod_cast this
      · refine ⟨c x, ?_⟩
        have : (gn (c x) : ℤ) = (v : ℤ) := by simp only [hG] at e1; omega
        exact_mod_cast this
  have hsurj : Function.Surjective β := by
    intro u
    have hul := u.isLt
    obtain ⟨t, ht⟩ := hattained (u.val + g₀) (by omega) (by omega)
    exact ⟨t, Fin.ext (by rw [hbval]; omega)⟩
  have hβlip : ∀ t t' : Fin m, t'.val = t.val + 1 → ((β t' : ℤ) - (β t : ℤ)).natAbs ≤ 1 := by
    intro t t' htt'
    have h1 := hglip t t' htt'
    have h2 := hg₀ t
    have h3 := hg₀ t'
    have e1 := hbval t
    have e2 := hbval t'
    omega
  refine ⟨P, β, ⟨hsurj, hβlip⟩, ?_, ?_, ?_⟩
  · -- every block lies in two adjacent links of `D`
    intro u
    have hul := u.isLt
    have hvle : u.val + g₀ ≤ n - 3 := by have := hgnle t₁; omega
    have hmemval : ∀ t, β t = u → gn t = u.val + g₀ := by
      intro t ht
      have := hg₀ t
      have e := hbval t
      rw [ht] at e
      omega
    have hlink : ∀ t, E.link t ⊆ D.link (h.minIdx t) := fun t => minIdx_subset h t
    set v := u.val + g₀ with hv
    rcases Nat.eq_zero_or_pos v with hv0 | hv0
    · refine ⟨⟨0, by omega⟩, by simp only []; omega, ?_⟩
      refine Set.iUnion₂_subset fun t ht => ?_
      have hgt : gn t = 0 := by rw [hmemval t ht]; omega
      have ha : (h.minIdx t).val ≤ 1 := by
        simp only [hgn, group] at hgt; omega
      refine (hlink t).trans ?_
      rcases Nat.lt_or_ge (h.minIdx t).val 1 with h1 | h1
      · have : h.minIdx t = ⟨0, by omega⟩ := Fin.ext (by simp only []; omega)
        rw [this]
        exact Set.subset_union_left
      · have : h.minIdx t = ⟨0 + 1, by omega⟩ := Fin.ext (by simp only []; omega)
        rw [this]
        exact Set.subset_union_right
    rcases Nat.lt_or_ge v (n - 3) with hvlt | hvge
    · refine ⟨⟨v + 1, by omega⟩, by simp only []; omega, ?_⟩
      refine Set.iUnion₂_subset fun t ht => ?_
      have hgt : gn t = v := hmemval t ht
      have ha : (h.minIdx t).val = v + 1 := by
        simp only [hgn, group] at hgt; omega
      refine (hlink t).trans ?_
      have : h.minIdx t = ⟨v + 1, by omega⟩ := Fin.ext (by simp only []; omega)
      rw [this]
      exact Set.subset_union_left
    · refine ⟨⟨n - 2, by omega⟩, by simp only []; omega, ?_⟩
      refine Set.iUnion₂_subset fun t ht => ?_
      have hgt : gn t = v := hmemval t ht
      have ha : n - 2 ≤ (h.minIdx t).val := by
        simp only [hgn, group] at hgt; omega
      have hal := (h.minIdx t).isLt
      refine (hlink t).trans ?_
      rcases Nat.lt_or_ge (h.minIdx t).val (n - 1) with h1 | h1
      · have : h.minIdx t = ⟨n - 2, by omega⟩ := Fin.ext (by simp only []; omega)
        rw [this]
        exact Set.subset_union_left
      · have : h.minIdx t = ⟨n - 2 + 1, by omega⟩ := Fin.ext (by simp only []; omega)
        rw [this]
        exact Set.subset_union_right
  · -- links whose minimal index is at most one are in the first block
    intro t ht
    have hgt : gn t = 0 := by simp only [hgn, group]; omega
    have := hg₀ t
    have e := hbval t
    omega
  · -- links whose minimal index is at least `n - 2` are in the last block
    intro t ht
    have hgt : gn t = n - 3 := by simp only [hgn, group]; omega
    have h1 := hg₁ t
    have h2 := hgnle t₁
    have e := hbval t
    omega

/-- The block map of the monotone grouping: each link goes to the group of its minimal
index, shifted so that the blocks used form `Fin p`. -/
noncomputable def Refines.monoBlocks (h : E.Refines D) (hn : 4 ≤ n) :
    Σ p : ℕ, { β : Fin m → Fin p // IsBlockMap β } :=
  ⟨(h.exists_monoBlocks hn).choose,
    ⟨(h.exists_monoBlocks hn).choose_spec.choose,
      (h.exists_monoBlocks hn).choose_spec.choose_spec.choose⟩⟩

/-- **The monotone grouping lemma.** For `E` refining `D` with `n ≥ 4` links, the
monotone grouping is a block consolidation whose every block lies in two adjacent links of
`D`; links with minimal index `≤ 1` all go to the first block, and links with minimal index
`≥ n − 2` all go to the last. No crookedness is needed. -/
theorem monoBlocks_spec (h : E.Refines D) (hn : 4 ≤ n) :
    let ⟨p, β, hβ⟩ := h.monoBlocks hn
    (∀ u : Fin p, ∃ j : Fin n, ∃ hj : j.val + 1 < n,
        (E.ofBlocks β hβ).link u ⊆ D.link j ∪ D.link ⟨j.val + 1, hj⟩) ∧
    (∀ t, (h.minIdx t).val ≤ 1 → (β t).val = 0) ∧
    (∀ t, n - 2 ≤ (h.minIdx t).val → (β t).val = p - 1) :=
  (h.exists_monoBlocks hn).choose_spec.choose_spec.choose_spec

/-- **Bing 1948, Theorem 4, the easy case.** If `d_r` itself meets `D.link 0` and `d_s` itself
meets the last link of `D`, then some block consolidation of `E` with blocks in two adjacent
links of `D` has `d_r` in the first block and `d_s` in the last. Crookedness is not used. -/
theorem exists_blocks_first_last (h : E.Refines D) (hn : 4 ≤ n) (r s : Fin m)
    (hr : (E.link r ∩ D.link ⟨0, by omega⟩).Nonempty)
    (hs : (E.link s ∩ D.link ⟨n - 1, by omega⟩).Nonempty) :
    ∃ p : ℕ, ∃ β : Fin m → Fin p, ∃ hβ : IsBlockMap β,
      (∀ u : Fin p, ∃ j : Fin n, ∃ hj : j.val + 1 < n,
          (E.ofBlocks β hβ).link u ⊆ D.link j ∪ D.link ⟨j.val + 1, hj⟩) ∧
      (β r).val = 0 ∧ (β s).val = p - 1 := by
  obtain ⟨p, β, hβ, hblocks, hfirst, hlast⟩ := h.exists_monoBlocks hn
  have hrl : (h.minIdx r).val ≤ 1 := by
    have := minIdx_near_of_inter h r ⟨0, by omega⟩ hr
    simp only [] at this
    omega
  have hsl : n - 2 ≤ (h.minIdx s).val := by
    have := minIdx_near_of_inter h s ⟨n - 1, by omega⟩ hs
    have := (h.minIdx s).isLt
    simp only [] at *
    omega
  exact ⟨p, β, hβ, hblocks, hfirst r hrl, hlast s hsl⟩

end Chain

/-! ## The strong reading of "contained in only the first link" is false -/

section Counterexample

/-- Five open intervals. -/
def Ecx : Chain ℝ 5 where
  link := ![Ioo 0 2, Ioo 1 4, Ioo 3 6, Ioo 5 8, Ioo 7 9]
  isOpen i := by fin_cases i <;> exact isOpen_Ioo
  adjacent := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [Set.Ioo_inter_Ioo, Set.nonempty_Ioo]

/-- Three open intervals: `d₀ ⊆ e₁` not meeting `e₀` nor inside `e₂`; `d₁ ⊆ e₂`;
`d₂ ⊆ e₃` not meeting `e₄` nor inside `e₂`. -/
def Dcx : Chain ℝ 3 where
  link := ![Ioo 2.2 3.5, Ioo 3.2 5.8, Ioo 5.5 6.8]
  isOpen i := by fin_cases i <;> exact isOpen_Ioo
  adjacent := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [Set.Ioo_inter_Ioo, Set.nonempty_Ioo]

theorem Dcx_refines : Dcx.Refines Ecx := by
  intro i
  fin_cases i
  · exact ⟨1, by
      show Ioo (2.2 : ℝ) 3.5 ⊆ Ioo 1 4
      exact Set.Ioo_subset_Ioo (by norm_num) (by norm_num)⟩
  · exact ⟨2, by
      show Ioo (3.2 : ℝ) 5.8 ⊆ Ioo 3 6
      exact Set.Ioo_subset_Ioo (by norm_num) (by norm_num)⟩
  · exact ⟨3, by
      show Ioo (5.5 : ℝ) 6.8 ⊆ Ioo 5 8
      exact Set.Ioo_subset_Ioo (by norm_num) (by norm_num)⟩

/-- Every link of `Dcx` lies in the interval `(2.2, 6.8)`. -/
theorem Dcx_mem_bounds (i : Fin 3) (z : ℝ) (hz : z ∈ Dcx.link i) : 2.2 < z ∧ z < 6.8 := by
  fin_cases i
  · have hz' : z ∈ Ioo (2.2 : ℝ) 3.5 := hz
    exact ⟨hz'.1, by have := hz'.2; norm_num at this ⊢; linarith⟩
  · have hz' : z ∈ Ioo (3.2 : ℝ) 5.8 := hz
    exact ⟨by have := hz'.1; norm_num at this ⊢; linarith,
      by have := hz'.2; norm_num at this ⊢; linarith⟩
  · have hz' : z ∈ Ioo (5.5 : ℝ) 6.8 := hz
    exact ⟨by have := hz'.1; norm_num at this ⊢; linarith, hz'.2⟩

/-- `Dcx` is crooked in `Ecx` in the 1948 sense, vacuously: no link of `Dcx` meets `e₀` or
`e₄`, and those are the only coarse indices at distance `> 2`. -/
theorem Dcx_isCrookedIn' : Dcx.IsCrookedIn' Ecx := by
  refine ⟨Dcx_refines, ?_⟩
  intro hh k hk i j hi hj
  exfalso
  have hhl := hh.isLt
  have hkl := k.isLt
  rcases (show hh.val = 0 ∨ k.val = 4 by omega) with h0 | h4
  · obtain ⟨z, hz1, hz2⟩ := hi
    have hb := Dcx_mem_bounds i z hz1
    have hhe : hh = (0 : Fin 5) := Fin.ext (by simpa using h0)
    rw [hhe] at hz2
    have hz2' : z ∈ Ioo (0 : ℝ) 2 := hz2
    have := hz2'.2
    have := hb.1
    norm_num at *
    linarith
  · obtain ⟨z, hz1, hz2⟩ := hj
    have hb := Dcx_mem_bounds j z hz1
    have hke : k = (4 : Fin 5) := Fin.ext (by simpa using h4)
    rw [hke] at hz2
    have hz2' : z ∈ Ioo (7 : ℝ) 9 := hz2
    have := hz2'.1
    have := hb.2
    norm_num at *
    linarith

/-- **No block consolidation of `Dcx` with blocks inside two adjacent links of `Ecx` puts all
three links in one block.** So the strong reading of Bing's Theorem 3 — the middle link
disjoint from every block but the first — is false: it would force the neighbors into the
first block. -/
theorem not_exists_strong_first_block :
    ¬ ∃ (p : ℕ) (β : Fin 3 → Fin p) (hβ : Chain.IsBlockMap β),
      (∀ u : Fin p, ∃ j : Fin 5, ∃ hj : j.val + 1 < 5,
          (Dcx.ofBlocks β hβ).link u ⊆ Ecx.link j ∪ Ecx.link ⟨j.val + 1, hj⟩) ∧
      β 0 = β 1 ∧ β 1 = β 2 := by
  rintro ⟨p, β, hβ, hblocks, h01, h12⟩
  have m1 : (2.3 : ℝ) ∈ (Dcx.ofBlocks β hβ).link (β 0) := by
    refine Set.mem_biUnion (show (0 : Fin 3) ∈ {t | β t = β 0} from rfl) ?_
    show (2.3 : ℝ) ∈ Ioo (2.2 : ℝ) 3.5
    norm_num
  have m2 : (6.7 : ℝ) ∈ (Dcx.ofBlocks β hβ).link (β 0) := by
    refine Set.mem_biUnion (show (2 : Fin 3) ∈ {t | β t = β 0} from ?_) ?_
    · show β 2 = β 0
      rw [← h12, ← h01]
    · show (6.7 : ℝ) ∈ Ioo (5.5 : ℝ) 6.8
      norm_num
  obtain ⟨j, hj, hsub⟩ := hblocks (β 0)
  fin_cases j
  · have a2 : (6.7 : ℝ) ∈ Ioo (0 : ℝ) 2 ∪ Ioo (1 : ℝ) 4 := hsub m2
    rcases a2 with hx | hx <;> (have := hx.2; norm_num at this)
  · have a2 : (6.7 : ℝ) ∈ Ioo (1 : ℝ) 4 ∪ Ioo (3 : ℝ) 6 := hsub m2
    rcases a2 with hx | hx <;> (have := hx.2; norm_num at this)
  · have a1 : (2.3 : ℝ) ∈ Ioo (3 : ℝ) 6 ∪ Ioo (5 : ℝ) 8 := hsub m1
    rcases a1 with hx | hx <;> (have := hx.1; norm_num at this)
  · have a1 : (2.3 : ℝ) ∈ Ioo (5 : ℝ) 8 ∪ Ioo (7 : ℝ) 9 := hsub m1
    rcases a1 with hx | hx <;> (have := hx.1; norm_num at this)
  · exact absurd hj (by decide)

end Counterexample

end HPC
