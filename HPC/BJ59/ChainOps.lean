import HPC.BJ59.Arc

/-!
# Batch 198, library: operations on chains

Three ways of making chains from chains, used for Bing–Jones's Theorem 3:

* `chainRestrict D S`: the links `S ∩ d_k`, when these are non-empty and consecutive ones meet;
* `chainMergeLast D T`: the last link enlarged by an open set `T` missing all links but the last two;
* `chainAppend D₁ D₂`: the concatenation, when only the last link of `D₁` meets the first of `D₂`.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane

variable {X : Type*} [MetricSpace X]

/-- The links `S ∩ d_k` of a chain, for an open `S` meeting every link and every intersection of
consecutive links. -/
def chainRestrict {n : ℕ} (D : Chain X n) (S : Set X) (hS : IsOpen S)
    (hne : ∀ k, (S ∩ D.link k).Nonempty)
    (hc : ∀ k k' : Fin n, (k' : ℕ) = k + 1 → (S ∩ (D.link k ∩ D.link k')).Nonempty) :
    Chain X n where
  link k := S ∩ D.link k
  isOpen k := hS.inter (D.isOpen k)
  adjacent i j := by
    constructor
    · rintro ⟨x, ⟨-, hi⟩, ⟨-, hj⟩⟩; exact (D.adjacent i j).1 ⟨x, hi, hj⟩
    · intro h
      rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
      · obtain ⟨x, hS, hi, hj⟩ := hc i j (by omega)
        exact ⟨x, ⟨hS, hi⟩, ⟨hS, hj⟩⟩
      · have : i = j := Fin.ext hij
        subst this
        obtain ⟨x, hx⟩ := hne i
        exact ⟨x, hx, hx⟩
      · obtain ⟨x, hS, hj, hi⟩ := hc j i (by omega)
        exact ⟨x, ⟨hS, hi⟩, ⟨hS, hj⟩⟩

@[simp] theorem chainRestrict_link {n : ℕ} (D : Chain X n) (S : Set X) (hS : IsOpen S) (hne hc)
    (k : Fin n) : (chainRestrict D S hS hne hc).link k = S ∩ D.link k := rfl

open Classical in
/-- The last link of a chain enlarged by an open set `T` that misses every link but the last
two. -/
noncomputable def chainMergeLast {n : ℕ} (D : Chain X (n + 1)) (T : Set X) (hT : IsOpen T)
    (hdisj : ∀ k : Fin (n + 1), (k : ℕ) + 2 ≤ n → Disjoint T (D.link k)) : Chain X (n + 1) where
  link k := if k = Fin.last n then D.link k ∪ T else D.link k
  isOpen k := by
    split_ifs
    · exact (D.isOpen k).union hT
    · exact D.isOpen k
  adjacent i j := by
    have key : ∀ i j : Fin (n + 1), i = Fin.last n →
        (((D.link i ∪ T) ∩ D.link j).Nonempty ↔ ((i : ℤ) - j).natAbs ≤ 1) := by
      intro i j hi
      constructor
      · rintro ⟨x, hx | hx, hj⟩
        · exact (D.adjacent i j).1 ⟨x, hx, hj⟩
        · by_contra hcon
          have hjn : (j : ℕ) + 2 ≤ n := by
            have := congrArg Fin.val hi; simp at this; omega
          exact Set.disjoint_left.1 (hdisj j hjn) hx hj
      · intro h
        obtain ⟨x, hx, hx'⟩ := (D.adjacent i j).2 h
        exact ⟨x, Or.inl hx, hx'⟩
    by_cases hi : i = Fin.last n <;> by_cases hj : j = Fin.last n
    · subst hi; subst hj
      simp only [if_true]
      constructor
      · intro; simp
      · intro
        obtain ⟨x, hx⟩ := D.link_nonempty (Fin.last n)
        exact ⟨x, Or.inl hx, Or.inl hx⟩
    · subst hi
      simp only [hj, if_true, if_false]
      exact key _ j rfl
    · subst hj
      simp only [hi, if_true, if_false]
      rw [inter_comm, key _ i rfl]; omega
    · simp only [hi, hj, if_false]
      exact D.adjacent i j

theorem chainMergeLast_link_last {n : ℕ} (D : Chain X (n + 1)) (T : Set X) (hT hdisj) :
    (chainMergeLast D T hT hdisj).link (Fin.last n) = D.link (Fin.last n) ∪ T := by
  simp [chainMergeLast]

theorem chainMergeLast_link_of_ne {n : ℕ} (D : Chain X (n + 1)) (T : Set X) (hT hdisj)
    {k : Fin (n + 1)} (hk : k ≠ Fin.last n) :
    (chainMergeLast D T hT hdisj).link k = D.link k := by
  simp [chainMergeLast, hk]

theorem chainMergeLast_link_subset {n : ℕ} (D : Chain X (n + 1)) (T : Set X) (hT hdisj)
    (k : Fin (n + 1)) : (chainMergeLast D T hT hdisj).link k ⊆ D.link k ∪ T := by
  by_cases hk : k = Fin.last n
  · subst hk; rw [chainMergeLast_link_last]
  · rw [chainMergeLast_link_of_ne _ _ _ _ hk]; exact subset_union_left

theorem subset_chainMergeLast_link {n : ℕ} (D : Chain X (n + 1)) (T : Set X) (hT hdisj)
    (k : Fin (n + 1)) : D.link k ⊆ (chainMergeLast D T hT hdisj).link k := by
  by_cases hk : k = Fin.last n
  · subst hk; rw [chainMergeLast_link_last]; exact subset_union_left
  · rw [chainMergeLast_link_of_ne _ _ _ _ hk]

/-- The concatenation of two chains, when the last link of the first meets the first link of the
second and all other pairs of links are disjoint. -/
def chainAppend {p q : ℕ} (D₁ : Chain X (p + 1)) (D₂ : Chain X (q + 1))
    (hmeet : (D₁.link (Fin.last p) ∩ D₂.link 0).Nonempty)
    (hdisj : ∀ a b, (a ≠ Fin.last p ∨ b ≠ 0) → Disjoint (D₁.link a) (D₂.link b)) :
    Chain X ((p + 1) + (q + 1)) where
  link := Fin.append D₁.link D₂.link
  isOpen k := by
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k
    · rw [Fin.append_left]; exact D₁.isOpen a
    · rw [Fin.append_right]; exact D₂.isOpen b
  adjacent i j := by
    have cross : ∀ (a : Fin (p + 1)) (b : Fin (q + 1)),
        (D₁.link a ∩ D₂.link b).Nonempty ↔
          (((Fin.castAdd (q + 1) a : Fin _) : ℤ) - (Fin.natAdd (p + 1) b : Fin _)).natAbs ≤ 1 := by
      intro a b
      simp only [Fin.val_castAdd, Fin.val_natAdd]
      constructor
      · intro h
        by_cases hab : a = Fin.last p ∧ b = 0
        · obtain ⟨rfl, rfl⟩ := hab; simp
        · rw [not_and_or] at hab
          exact absurd h (Set.disjoint_iff_inter_eq_empty.1 (hdisj a b hab) ▸ not_nonempty_empty)
      · intro h
        have ha : a = Fin.last p := Fin.ext (by have := a.isLt; simp; omega)
        have hb : b = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
        subst ha; subst hb; exact hmeet
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
      refine Fin.addCases (fun a' => ?_) (fun b' => ?_) j
    · simp only [Fin.append_left, Fin.val_castAdd]; exact D₁.adjacent a a'
    · simp only [Fin.append_left, Fin.append_right]; exact cross a b'
    · simp only [Fin.append_left, Fin.append_right]
      rw [inter_comm, cross a' b]; omega
    · simp only [Fin.append_right, Fin.val_natAdd]
      rw [D₂.adjacent b b']; omega

theorem chainAppend_link_left {p q : ℕ} (D₁ : Chain X (p + 1)) (D₂ : Chain X (q + 1)) (hmeet hdisj)
    (a : Fin (p + 1)) : (chainAppend D₁ D₂ hmeet hdisj).link (Fin.castAdd (q + 1) a) = D₁.link a :=
  Fin.append_left _ _ _

theorem chainAppend_link_right {p q : ℕ} (D₁ : Chain X (p + 1)) (D₂ : Chain X (q + 1)) (hmeet hdisj)
    (b : Fin (q + 1)) : (chainAppend D₁ D₂ hmeet hdisj).link (Fin.natAdd (p + 1) b) = D₂.link b :=
  Fin.append_right _ _ _

theorem chainAppend_union {p q : ℕ} (D₁ : Chain X (p + 1)) (D₂ : Chain X (q + 1)) (hmeet hdisj) :
    (chainAppend D₁ D₂ hmeet hdisj).union = D₁.union ∪ D₂.union := by
  ext x
  simp only [Chain.union, mem_iUnion, mem_union]
  constructor
  · rintro ⟨k, hk⟩
    induction k using Fin.addCases with
    | left a => exact Or.inl ⟨a, by rwa [chainAppend_link_left] at hk⟩
    | right b => exact Or.inr ⟨b, by rwa [chainAppend_link_right] at hk⟩
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · exact ⟨Fin.castAdd _ a, by rwa [chainAppend_link_left]⟩
    · exact ⟨Fin.natAdd _ b, by rwa [chainAppend_link_right]⟩

theorem isEpsChain_chainAppend {p q : ℕ} {D₁ : Chain X (p + 1)} {D₂ : Chain X (q + 1)} {hmeet hdisj}
    {ε : ℝ} (h₁ : IsEpsChain D₁ ε) (h₂ : IsEpsChain D₂ ε) :
    IsEpsChain (chainAppend D₁ D₂ hmeet hdisj) ε := by
  intro k
  induction k using Fin.addCases with
  | left a => rw [chainAppend_link_left]; exact h₁ a
  | right b => rw [chainAppend_link_right]; exact h₂ b

end HPC.BJ59
