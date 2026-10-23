import HPC.Plane.Tree67

/-!
# Batch 133, helpers: the nerve of a tree chain

Graph theory for `TreeLikeNS.lean` (`exists_leaf`). Links `A, B` of a collection `H` are
*adjacent in `H`* (`LAdj H A B`) if both are in `H` and they meet; `H` is *chain-connected*
(`ChainConn H`) if any two of its links are joined by a chain of adjacent links of `H`.

* `exists_chainConn_card`: a coherent collection has chain-connected subcollections of every
  size `n + 1 ≤ G.card` (grow one link at a time, using coherence).
* `isCoherent_of_chainConn`: chain-connected collections are coherent.
* `no_two_nbrs`: in a collection with no circular subcollection, a link `C` outside a
  chain-connected subcollection `H` meets at most one link of `H`. A shortest chain of `H` whose
  two distinct ends meet `C` is chordless, its inner links miss `C`, and together with `C` it is a
  circular chain (`circularChain_of_minimal`).
-/

namespace HPC.Plane

open Set

open scoped Classical

/-- Adjacency within `H`: both links in `H`, and they meet. -/
def LAdj (H : Finset (Set Pt)) (A B : Set Pt) : Prop := A ∈ H ∧ B ∈ H ∧ (A ∩ B).Nonempty

/-- `H` is chain-connected: any two links of `H` are joined by a chain of adjacent links of `H`. -/
def ChainConn (H : Finset (Set Pt)) : Prop :=
  ∀ A ∈ H, ∀ B ∈ H, Relation.ReflTransGen (LAdj H) A B

theorem exists_seq_of_reflTransGen {H : Finset (Set Pt)} {A B : Set Pt} (hA : A ∈ H)
    (h : Relation.ReflTransGen (LAdj H) A B) :
    ∃ (k : ℕ) (P : ℕ → Set Pt), P 0 = A ∧ P k = B ∧ (∀ t ≤ k, P t ∈ H) ∧
      ∀ t < k, (P t ∩ P (t + 1)).Nonempty := by
  induction h with
  | refl => exact ⟨0, fun _ => A, rfl, rfl, fun _ _ => hA, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨k, P, h0, hk, hH, hadj⟩ := ih
    refine ⟨k + 1, fun t => if t ≤ k then P t else c, by simp [h0], by simp, ?_, ?_⟩
    · intro t ht
      by_cases h : t ≤ k
      · simp only [h, if_true]; exact hH t h
      · simp only [h, if_false]; exact hbc.2.1
    · intro t ht
      by_cases h : t + 1 ≤ k
      · simp only [h, if_true, show t ≤ k by omega]; exact hadj t (by omega)
      · have htk : t = k := by omega
        subst htk
        simp only [le_refl, if_true, show ¬ t + 1 ≤ t by omega, if_false, hk]
        exact hbc.2.2

/-- Chain-connected collections are coherent. -/
theorem isCoherent_of_chainConn {H : Finset (Set Pt)} (hH : ChainConn H) : IsCoherent H := by
  intro H' hsub hne
  obtain ⟨X, hX⟩ := hne
  obtain ⟨Y, hYH, hYn⟩ := Finset.exists_of_ssubset hsub
  have key : ∀ Y, Relation.ReflTransGen (LAdj H) X Y → Y ∉ H' →
      ∃ A ∈ H', ∃ B ∈ H \ H', (A ∩ B).Nonempty := by
    intro Y h
    induction h with
    | refl => intro h; exact absurd hX h
    | @tail b c _ hbc ih =>
      intro hc
      by_cases hb : b ∈ H'
      · exact ⟨b, hb, c, Finset.mem_sdiff.2 ⟨hbc.2.1, hc⟩, hbc.2.2⟩
      · exact ih hb
  exact key Y (hH X (hsub.1 hX) Y hYH) hYn

/-- A coherent collection has a chain-connected subcollection of each size `n + 1 ≤ G.card`. -/
theorem exists_chainConn_card {G : Finset (Set Pt)} (hG : IsCoherent G) :
    ∀ n, n < G.card → ∃ H ⊆ G, H.card = n + 1 ∧ ChainConn H := by
  intro n
  induction n with
  | zero =>
    intro h
    obtain ⟨A, hA⟩ := Finset.card_pos.1 h
    refine ⟨{A}, by simpa using hA, by simp, ?_⟩
    intro X hX Y hY
    rw [Finset.mem_singleton] at hX hY
    subst hX; subst hY; exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro h
    obtain ⟨H, hHG, hcard, hconn⟩ := ih (by omega)
    have hss : H ⊂ G := Finset.ssubset_iff_subset_ne.2 ⟨hHG, fun e => by rw [e] at hcard; omega⟩
    obtain ⟨X, hX, C, hC, hXC⟩ := hG H hss (Finset.card_pos.1 (by omega))
    rw [Finset.mem_sdiff] at hC
    refine ⟨insert C H, Finset.insert_subset hC.1 hHG,
      by rw [Finset.card_insert_of_notMem hC.2, hcard], ?_⟩
    have hmono : ∀ A B, Relation.ReflTransGen (LAdj H) A B →
        Relation.ReflTransGen (LAdj (insert C H)) A B := fun A B h =>
      Relation.ReflTransGen.mono (fun a b hab => ⟨Finset.mem_insert_of_mem hab.1,
        Finset.mem_insert_of_mem hab.2.1, hab.2.2⟩) h
    have hCX : LAdj (insert C H) C X :=
      ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hX, by rw [inter_comm]; exact hXC⟩
    have hXC' : LAdj (insert C H) X C :=
      ⟨Finset.mem_insert_of_mem hX, Finset.mem_insert_self _ _, hXC⟩
    intro A hA B hB
    rw [Finset.mem_insert] at hA hB
    rcases hA with rfl | hA <;> rcases hB with rfl | hB
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head hCX (hmono _ _ (hconn X hX B hB))
    · exact (hmono _ _ (hconn A hA X hX)).tail hXC'
    · exact hmono _ _ (hconn A hA B hB)

/-- A chain `P 0, …, P k` of links of `H` whose two distinct ends meet `C`. -/
def EndsMeet (H : Finset (Set Pt)) (C : Set Pt) (k : ℕ) (P : ℕ → Set Pt) : Prop :=
  (∀ t ≤ k, P t ∈ H) ∧ (∀ t < k, (P t ∩ P (t + 1)).Nonempty) ∧ (C ∩ P 0).Nonempty ∧
    (C ∩ P k).Nonempty ∧ P 0 ≠ P k

/-- A shortest chain of `H` with distinct ends meeting `C ∉ H`, closed up by `C`, is a circular
chain. -/
theorem circularChain_of_minimal {H : Finset (Set Pt)} {C : Set Pt} (hCH : C ∉ H) {k : ℕ}
    {P : ℕ → Set Pt} (hP : EndsMeet H C k P) (hmin : ∀ k' < k, ∀ P', ¬ EndsMeet H C k' P') :
    IsCircularChain (Finset.univ.image fun i : Fin (k + 2) =>
      if i.val = 0 then C else P (i.val - 1)) := by
  obtain ⟨hH, hadj, hC0, hCk, hne0⟩ := hP
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; exact absurd rfl hne0
    · exact h
  have hnon : ∀ t ≤ k, (P t).Nonempty := by
    intro t ht
    rcases Nat.lt_or_ge t k with h | h
    · obtain ⟨z, hz⟩ := hadj t h; exact ⟨z, hz.1⟩
    · obtain ⟨z, hz⟩ := hadj (k - 1) (by omega)
      have : k - 1 + 1 = t := by omega
      rw [this] at hz; exact ⟨z, hz.2⟩
  have hCi : ∀ i, 0 < i → i < k → ¬ (C ∩ P i).Nonempty := by
    intro i hi0 hik hCi
    by_cases hPi : P i = P 0
    · apply hmin (k - i) (by omega) (fun t => P (t + i))
      refine ⟨fun t ht => hH _ (by omega), fun t ht => ?_, by simpa using hCi, ?_, ?_⟩
      · have := hadj (t + i) (by omega)
        rwa [show t + i + 1 = t + 1 + i by ring] at this
      · show (C ∩ P (k - i + i)).Nonempty
        rwa [Nat.sub_add_cancel hik.le]
      · simp only [zero_add, Nat.sub_add_cancel hik.le, hPi]; exact hne0
    · exact hmin i hik P ⟨fun t ht => hH t (by omega), fun t ht => hadj t (by omega), hC0, hCi,
        Ne.symm hPi⟩
  have hchord : ∀ i j, i + 2 ≤ j → j ≤ k → ¬ (P i ∩ P j).Nonempty := by
    intro i j hij hjk hPij
    set s := j - i - 1 with hs
    apply hmin (k - s) (by omega) (fun t => if t ≤ i then P t else P (t + s))
    refine ⟨fun t ht => ?_, fun t ht => ?_, ?_, ?_, ?_⟩
    · by_cases h : t ≤ i
      · simp only [h, if_true]; exact hH t (by omega)
      · simp only [h, if_false]; exact hH _ (by omega)
    · rcases lt_trichotomy t i with h | h | h
      · simp only [show t ≤ i by omega, show t + 1 ≤ i by omega, if_true]; exact hadj t (by omega)
      · subst h
        simp only [le_refl, if_true, show ¬ t + 1 ≤ t by omega, if_false]
        rwa [show t + 1 + s = j by omega]
      · simp only [show ¬ t ≤ i by omega, show ¬ t + 1 ≤ i by omega, if_false]
        have := hadj (t + s) (by omega)
        rwa [show t + s + 1 = t + 1 + s by ring] at this
    · simpa using hC0
    · simp only [show ¬ k - s ≤ i by omega, if_false, Nat.sub_add_cancel (show s ≤ k by omega)]
      exact hCk
    · simp only [zero_le, if_true, show ¬ k - s ≤ i by omega, if_false,
        Nat.sub_add_cancel (show s ≤ k by omega)]
      exact hne0
  have hcons : ∀ i < k, P i ≠ P (i + 1) := by
    intro i hik he
    rcases Nat.lt_or_ge (i + 1) k with h | h
    · apply hchord i (i + 2) le_rfl (by omega)
      rw [he]; exact hadj (i + 1) h
    · rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; apply hne0; rw [he]; congr 1; omega
      · apply hchord (i - 1) (i + 1) (by omega) (by omega)
        rw [← he]
        have := hadj (i - 1) (by omega)
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)] at this
  have hinj : ∀ i ≤ k, ∀ j ≤ k, P i = P j → i = j := by
    have : ∀ i j, i < j → j ≤ k → P i ≠ P j := by
      intro i j hij hjk he
      rcases Nat.lt_or_ge (i + 1) j with h | h
      · apply hchord i j (by omega) hjk
        rw [he, inter_self]; exact hnon j hjk
      · have : j = i + 1 := by omega
        subst this; exact hcons i (by omega) he
    intro i hi j hj he
    rcases lt_trichotomy i j with h | h | h
    · exact absurd he (this i j h hj)
    · exact h
    · exact absurd he.symm (this j i h hi)
  have hPC : ∀ t ≤ k, P t ≠ C := fun t ht he => hCH (he ▸ hH t ht)
  have hCne : C.Nonempty := by obtain ⟨z, hz⟩ := hC0; exact ⟨z, hz.1⟩
  refine ⟨k + 2, by omega, _, ?_, rfl, ?_⟩
  · intro i j hij
    simp only at hij
    apply Fin.ext
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · omega
    · rw [if_pos hi, if_neg hj] at hij; exact absurd hij.symm (hPC _ (by omega))
    · rw [if_neg hi, if_pos hj] at hij; exact absurd hij (hPC _ (by omega))
    · rw [if_neg hi, if_neg hj] at hij
      have := hinj _ (by omega) _ (by omega) hij
      omega
  · intro i j
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · rw [if_pos hi, if_pos hj, inter_self]
      simp only [hCne, true_iff]; left; omega
    · rw [if_pos hi, if_neg hj]
      constructor
      · intro h
        by_cases h1 : j.val - 1 = 0
        · left; omega
        · by_cases h2 : j.val - 1 = k
          · right; left; omega
          · exact absurd h (hCi _ (by omega) (by omega))
      · intro h
        have : j.val - 1 = 0 ∨ j.val - 1 = k := by omega
        rcases this with h' | h'
        · rw [h']; exact hC0
        · rw [h']; exact hCk
    · rw [if_neg hi, if_pos hj, inter_comm]
      constructor
      · intro h
        by_cases h1 : i.val - 1 = 0
        · left; omega
        · by_cases h2 : i.val - 1 = k
          · right; right; omega
          · exact absurd h (hCi _ (by omega) (by omega))
      · intro h
        have : i.val - 1 = 0 ∨ i.val - 1 = k := by omega
        rcases this with h' | h'
        · rw [h']; exact hC0
        · rw [h']; exact hCk
    · rw [if_neg hi, if_neg hj]
      constructor
      · intro h
        left
        by_contra hc
        rcases Nat.lt_or_ge i.val j.val with hl | hl
        · exact hchord (i.val - 1) (j.val - 1) (by omega) (by omega) h
        · exact hchord (j.val - 1) (i.val - 1) (by omega) (by omega) (by rwa [inter_comm])
      · intro h
        have : i.val = j.val ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val := by omega
        rcases this with h' | h' | h'
        · rw [h', inter_self]; exact hnon _ (by omega)
        · have := hadj (i.val - 1) (by omega)
          rwa [show i.val - 1 + 1 = j.val - 1 by omega] at this
        · have := hadj (j.val - 1) (by omega)
          rw [show j.val - 1 + 1 = i.val - 1 by omega] at this
          rwa [inter_comm]

/-- **A link outside a chain-connected subcollection meets at most one of its links**, when no
subcollection is a circular chain. -/
theorem no_two_nbrs {G H : Finset (Set Pt)} (hcirc : ∀ G' ⊆ G, ¬ IsCircularChain G')
    (hHG : H ⊆ G) (hH : ChainConn H) {C : Set Pt} (hC : C ∈ G) (hCH : C ∉ H) {B₁ B₂ : Set Pt}
    (h1 : B₁ ∈ H) (h2 : B₂ ∈ H) (hne : B₁ ≠ B₂) (hC1 : (C ∩ B₁).Nonempty)
    (hC2 : (C ∩ B₂).Nonempty) : False := by
  have hex : ∃ k, ∃ P, EndsMeet H C k P := by
    obtain ⟨k, P, h0, hk, hmem, hadj⟩ := exists_seq_of_reflTransGen h1 (hH B₁ h1 B₂ h2)
    exact ⟨k, P, hmem, hadj, h0 ▸ hC1, hk ▸ hC2, by rw [h0, hk]; exact hne⟩
  obtain ⟨P, hP⟩ := Nat.find_spec hex
  have hmin : ∀ k' < Nat.find hex, ∀ P', ¬ EndsMeet H C k' P' := fun k' hk' P' hP' =>
    Nat.find_min hex hk' ⟨P', hP'⟩
  refine hcirc _ ?_ (circularChain_of_minimal hCH hP hmin)
  intro X hX
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hX
  by_cases hi : i.val = 0
  · simp only [hi, if_true]; exact hC
  · simp only [hi, if_false]; exact hHG (hP.1 _ (by omega))

end HPC.Plane
