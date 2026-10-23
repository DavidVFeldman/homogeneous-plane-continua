import HPC.Plane.Fugate66Cor1
import HPC.Plane.SorgenfreyDefs

/-!
# Batch 132, Part I: Fugate's Corollary 1 from Theorem 1 and the property (∗)

The batch skeleton is kept as `doc/batches/skeletons/Fugate66Cor1Proof-batch132.lean`; every
`sorry` is proved, with the shape changes recorded in the docstrings (`IngramStarWeak` added;
`hp` dropped from `isHereditarilyUnicoherent_partial`; the induction runs over interval unions
`chainUnion`).

The argument is `doc/notes/fugate-cor1-proof.md`, a hand proof never checked before this batch;
no error was found in it. The property (∗) (`IngramStar`) is a hypothesis here. It is proved in
Part II (`ingramStar_holds`, `HPC/Plane/Ingram68Star.lean`) by the direct route through Ingram
1968, Lemmas 1 and 2, and `fugate_cor1` is in `HPC/Plane/Ingram68.lean`.

## The argument

Strong induction on the number of pieces. Let `p` be least with `U_p = A₀ ∪ ⋯ ∪ A_p` not
unicoherent; then `1 ≤ p < k`. Put `Y = U_{p−1}` (chainable), `A = A_p`, `C = Y ∪ A`,
`B = A_{p+1} ∪ ⋯ ∪ A_k`. Then `Y ∩ A` is not connected; write `Y ∩ A = H ⊔ K`.

* Unicoherence of `X` applied to `X = Y ∪ (A ∪ B)` and `X = (Y ∪ B) ∪ A` makes
  `M₁ = Y ∩ (A ∪ B)` and `M₂ = A ∩ (Y ∪ B)` continua with `M₁ ∩ M₂ = H ⊔ K`. So `M₁ ∪ M₂ ⊆ C`
  is not unicoherent, and by (∗) `M₁ ∪ M₂ = C`. Hence `X = Y ∪ B = A ∪ B`.
* Unicoherence of `X` on these two decompositions makes `Y ∩ B` and `A ∩ B` continua meeting in
  `(H ∩ B) ⊔ (K ∩ B)`, both parts nonempty. So `C ∩ B` is not unicoherent, and by (∗)
  `C ∩ B = C`, i.e. `C ⊆ B` (`subset_of_unicoherent_absorb`).
* So `X = B`, a chain of fewer pieces. By induction `X` is chainable, hence hereditarily
  unicoherent, contradicting `C ⊆ X`.

`subset_of_unicoherent_absorb` uses no chainability and no atriodicity: only the unicoherence of
`Y ∪ A ∪ B` and (∗) for `Y ∪ A`.
-/

namespace HPC.Plane

open Set

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **The property (∗)** (Ingram 1968; there via Theorem 2(2) and Nadler 12.51). Suppose `Y` and `A` are
chainable and meet, `Y ∪ A` is atriodic, and `Y ∩ A` is not connected. Then every proper
subcontinuum of `Y ∪ A` is unicoherent. Proved in Part II as `ingramStar_holds`. -/
def IngramStar (S : Type*) [MetricSpace S] [CompactSpace S] : Prop :=
  ∀ Y A : Set S, IsSnakeLike Y → IsSnakeLike A → (Y ∩ A).Nonempty → IsAtriodic (Y ∪ A) →
    ¬ IsConnected (Y ∩ A) →
    ∀ M ⊆ Y ∪ A, Fold.Q78.IsContinuum M → M ≠ Y ∪ A → IsUnicoherent M

/-- **The property (∗∗)**, the consequence of (∗) actually used in Steps 4–5 (shape addition,
batch 132). Suppose `Y` and `A` are chainable and meet, `Y ∪ A` is atriodic, and `Y ∩ A` is not
connected. If `P ⊆ Y` and `Q ⊆ A` are continua meeting in a nonempty disconnected set, then
`P ∪ Q = Y ∪ A`. (∗) implies (∗∗) (`ingramStarWeak_of_ingramStar`): `P ∪ Q` is a subcontinuum of
`Y ∪ A` that is not unicoherent. -/
def IngramStarWeak (S : Type*) [MetricSpace S] [CompactSpace S] : Prop :=
  ∀ Y A : Set S, IsSnakeLike Y → IsSnakeLike A → (Y ∩ A).Nonempty → IsAtriodic (Y ∪ A) →
    ¬ IsConnected (Y ∩ A) →
    ∀ P Q : Set S, Fold.Q78.IsContinuum P → Fold.Q78.IsContinuum Q → P ⊆ Y → Q ⊆ A →
      (P ∩ Q).Nonempty → ¬ IsConnected (P ∩ Q) → P ∪ Q = Y ∪ A

omit [CompactSpace S] in
/-- A nonempty compact set that is not connected splits into two disjoint nonempty closed sets.
(`isPreconnected_iff_subset_of_disjoint_fun`, `exists_separated_of_not_isPreconnected`, or
directly.) -/
theorem exists_split_of_not_isConnected {T : Set S} (hT : IsClosed T) (hne : T.Nonempty)
    (hT' : ¬ IsConnected T) :
    ∃ H K : Set S, IsClosed H ∧ IsClosed K ∧ H.Nonempty ∧ K.Nonempty ∧ Disjoint H K ∧
      T = H ∪ K := by
  have hpc : ¬ IsPreconnected T := fun h => hT' ⟨hne, h⟩
  obtain ⟨P, Q, hP, hQ, hTPQ, hPQ, hPQ'⟩ := exists_separated_of_not_isPreconnected hpc
  have hcP : closure P ⊆ T := closure_minimal (hTPQ ▸ subset_union_left) hT
  have hcQ : closure Q ⊆ T := closure_minimal (hTPQ ▸ subset_union_right) hT
  have eP : closure P = P := by
    refine Subset.antisymm (fun x hx => ?_) subset_closure
    rcases (hTPQ ▸ hcP hx : x ∈ P ∪ Q) with h | h
    · exact h
    · exact absurd h (disjoint_left.mp hPQ hx)
  have eQ : closure Q = Q := by
    refine Subset.antisymm (fun x hx => ?_) subset_closure
    rcases (hTPQ ▸ hcQ hx : x ∈ P ∪ Q) with h | h
    · exact absurd hx (disjoint_left.mp hPQ' h)
    · exact h
  refine ⟨P, Q, eP ▸ isClosed_closure, eQ ▸ isClosed_closure, hP, hQ, ?_, hTPQ⟩
  rw [← eP]; exact hPQ

omit [CompactSpace S] in
/-- A union of two disjoint nonempty closed sets is not preconnected. -/
theorem not_isPreconnected_of_split {H K : Set S} (hH : IsClosed H) (hK : IsClosed K)
    (hHne : H.Nonempty) (hKne : K.Nonempty) (hHK : Disjoint H K) : ¬ IsPreconnected (H ∪ K) := by
  intro h
  rw [isPreconnected_iff_subset_of_disjoint_closed] at h
  rcases h H K hH hK Subset.rfl (by rw [hHK.inter_eq, inter_empty]) with h' | h'
  · obtain ⟨x, hx⟩ := hKne
    exact disjoint_left.mp hHK (h' (Or.inr hx)) hx
  · obtain ⟨x, hx⟩ := hHne
    exact disjoint_left.mp hHK hx (h' (Or.inl hx))

omit [CompactSpace S] in
/-- A continuum that is the union of two continua meeting in a disconnected set is not
unicoherent. -/
theorem not_isUnicoherent_of_split {P Q : Set S} (hP : Fold.Q78.IsContinuum P)
    (hQ : Fold.Q78.IsContinuum Q) (hPQ : ¬ IsConnected (P ∩ Q)) : ¬ IsUnicoherent (P ∪ Q) :=
  fun hu => hPQ (hu P Q hP hQ rfl)

omit [CompactSpace S] in
/-- A closed connected set in a compact space is a continuum. -/
private theorem isContinuum_of_isClosed_isConnected [CompactSpace S] {T : Set S}
    (hT : IsClosed T) (hc : IsConnected T) : Fold.Q78.IsContinuum T :=
  ⟨hT.isCompact, hc⟩

/-- **(∗) implies (∗∗).** -/
theorem ingramStarWeak_of_ingramStar (hstar : IngramStar S) : IngramStarWeak S := by
  intro Y A hY hA hne hat hnc P Q hP hQ hPY hQA hPQne hPQ
  by_contra hne'
  exact not_isUnicoherent_of_split hP hQ hPQ
    (hstar Y A hY hA hne hat hnc (P ∪ Q) (union_subset_union hPY hQA)
      (isContinuum_union hP hQ hPQne) hne')

/-- **Steps 3–5 of the proof: absorption, from (∗∗).** Suppose `Y`, `A`, `B` are continua, `A`
meets `B`, `Y ∩ A` is nonempty and not connected, and `Y ∪ A ∪ B` is unicoherent. Suppose also
that whenever `P ⊆ Y` and `Q ⊆ A` are continua meeting in a nonempty disconnected set,
`P ∪ Q = Y ∪ A`. Then `Y ∪ A ⊆ B`. -/
theorem subset_of_unicoherent_absorb' {Y A B : Set S}
    (hY : Fold.Q78.IsContinuum Y) (hA : Fold.Q78.IsContinuum A) (hB : Fold.Q78.IsContinuum B)
    (hAB : (A ∩ B).Nonempty) (hYAne : (Y ∩ A).Nonempty) (hYA : ¬ IsConnected (Y ∩ A))
    (hX : IsUnicoherent (Y ∪ A ∪ B))
    (hweak : ∀ P Q : Set S, Fold.Q78.IsContinuum P → Fold.Q78.IsContinuum Q → P ⊆ Y → Q ⊆ A →
      (P ∩ Q).Nonempty → ¬ IsConnected (P ∩ Q) → P ∪ Q = Y ∪ A) :
    Y ∪ A ⊆ B := by
  obtain ⟨H, K, hHc, hKc, hHne, hKne, hHK, hYAHK⟩ :=
    exists_split_of_not_isConnected (hY.1.isClosed.inter hA.1.isClosed) hYAne hYA
  have hHYA : H ⊆ Y ∩ A := hYAHK ▸ subset_union_left
  have hKYA : K ⊆ Y ∩ A := hYAHK ▸ subset_union_right
  -- Step 3
  have hAuB : Fold.Q78.IsContinuum (A ∪ B) := isContinuum_union hA hB hAB
  have hM₁ : IsConnected (Y ∩ (A ∪ B)) :=
    hX Y (A ∪ B) hY hAuB (by rw [union_assoc])
  have hM₁eq : Y ∩ (A ∪ B) = H ∪ (K ∪ (Y ∩ B)) := by
    rw [inter_union_distrib_left, hYAHK, union_assoc]
  have meetB : ∀ {H K : Set S}, IsClosed H → IsClosed K → H.Nonempty → K.Nonempty →
      Disjoint H K → Y ∩ A = H ∪ K → (H ∩ B).Nonempty := by
    intro H K hHc hKc hHne hKne hHK hYAHK
    by_contra hHB
    rw [not_nonempty_iff_eq_empty] at hHB
    have e : Y ∩ (A ∪ B) = H ∪ (K ∪ (Y ∩ B)) := by
      rw [inter_union_distrib_left, hYAHK, union_assoc]
    refine not_isPreconnected_of_split hHc (hKc.union (hY.1.isClosed.inter hB.1.isClosed)) hHne
      (hKne.mono subset_union_left) ?_ (e ▸ hM₁.isPreconnected)
    rw [disjoint_union_right]
    refine ⟨hHK, disjoint_left.mpr fun x hxH hxYB => ?_⟩
    have : x ∈ H ∩ B := ⟨hxH, hxYB.2⟩
    rw [hHB] at this; exact this
  have hHB : (H ∩ B).Nonempty := meetB hHc hKc hHne hKne hHK hYAHK
  have hKB : (K ∩ B).Nonempty :=
    meetB hKc hHc hKne hHne hHK.symm (by rw [hYAHK, union_comm])
  have hYB : (Y ∩ B).Nonempty := by
    obtain ⟨x, hxH, hxB⟩ := hHB; exact ⟨x, (hHYA hxH).1, hxB⟩
  have hYuB : Fold.Q78.IsContinuum (Y ∪ B) := isContinuum_union hY hB hYB
  have hM₂ : IsConnected ((Y ∪ B) ∩ A) :=
    hX (Y ∪ B) A hYuB hA (by rw [union_right_comm])
  -- Step 4
  have hM₁c : Fold.Q78.IsContinuum (Y ∩ (A ∪ B)) :=
    isContinuum_of_isClosed_isConnected (hY.1.isClosed.inter hAuB.1.isClosed) hM₁
  have hM₂c : Fold.Q78.IsContinuum ((Y ∪ B) ∩ A) :=
    isContinuum_of_isClosed_isConnected (hYuB.1.isClosed.inter hA.1.isClosed) hM₂
  have hMM : (Y ∩ (A ∪ B)) ∩ ((Y ∪ B) ∩ A) = Y ∩ A := by
    ext x; simp only [mem_inter_iff, mem_union]; tauto
  have hM := hweak _ _ hM₁c hM₂c inter_subset_left inter_subset_right (hMM ▸ hYAne)
    (hMM ▸ hYA)
  have hYAB : Y ∪ A ⊆ (Y ∩ A) ∪ B := by
    rw [← hM]
    rintro x (⟨hxY, hxA | hxB⟩ | ⟨hxY | hxB, hxA⟩)
    · exact Or.inl ⟨hxY, hxA⟩
    · exact Or.inr hxB
    · exact Or.inl ⟨hxY, hxA⟩
    · exact Or.inr hxB
  have hX₁ : Y ∪ B = Y ∪ A ∪ B := by
    refine Subset.antisymm (union_subset_union_left _ subset_union_left) (union_subset ?_ ?_)
    · intro x hx
      rcases hYAB hx with h | h
      · exact Or.inl h.1
      · exact Or.inr h
    · exact subset_union_right
  have hX₂ : A ∪ B = Y ∪ A ∪ B := by
    refine Subset.antisymm (union_subset_union_left _ subset_union_right) (union_subset ?_ ?_)
    · intro x hx
      rcases hYAB hx with h | h
      · exact Or.inl h.2
      · exact Or.inr h
    · exact subset_union_right
  -- Step 5
  have hDY : IsConnected (Y ∩ B) := hX Y B hY hB hX₁
  have hDA : IsConnected (A ∩ B) := hX A B hA hB hX₂
  have hDYc : Fold.Q78.IsContinuum (Y ∩ B) :=
    isContinuum_of_isClosed_isConnected (hY.1.isClosed.inter hB.1.isClosed) hDY
  have hDAc : Fold.Q78.IsContinuum (A ∩ B) :=
    isContinuum_of_isClosed_isConnected (hA.1.isClosed.inter hB.1.isClosed) hDA
  have hDD : (Y ∩ B) ∩ (A ∩ B) = (H ∩ B) ∪ (K ∩ B) := by
    rw [← union_inter_distrib_right, ← hYAHK]
    ext x; simp only [mem_inter_iff]; tauto
  have hDDne : ((Y ∩ B) ∩ (A ∩ B)).Nonempty := hDD ▸ hHB.mono subset_union_left
  have hDDnc : ¬ IsConnected ((Y ∩ B) ∩ (A ∩ B)) := by
    rw [hDD]
    exact fun h => not_isPreconnected_of_split (hHc.inter hB.1.isClosed)
      (hKc.inter hB.1.isClosed) hHB hKB
      (hHK.mono inter_subset_left inter_subset_left) h.isPreconnected
  have hD := hweak _ _ hDYc hDAc inter_subset_left inter_subset_left hDDne hDDnc
  rw [← hD]
  exact union_subset inter_subset_right inter_subset_right

/-- **Steps 3–5 of the proof: absorption.** Suppose `Y`, `A`, `B` are continua, `A` meets `B`,
`Y ∩ A` is nonempty and not connected, and `Y ∪ A ∪ B` is unicoherent. Suppose also that every
proper subcontinuum of `Y ∪ A` is unicoherent. Then `Y ∪ A ⊆ B`.

Proof (fugate-cor1-proof.md, Steps 3–5).
* `M₁ := Y ∩ (A ∪ B)` is connected, from `X = Y ∪ (A ∪ B)`. Each part of the split
  `Y ∩ A = H ⊔ K` meets `B`. So `Y ∪ B` is a continuum, and `M₂ := A ∩ (Y ∪ B)` is connected,
  from `X = (Y ∪ B) ∪ A`.
* `M₁ ∩ M₂ = Y ∩ A` is not connected (`not_isUnicoherent_of_split`), so `M₁ ∪ M₂ = Y ∪ A`.
  Hence `X = Y ∪ B = A ∪ B`.
* `Y ∩ B` and `A ∩ B` are connected and meet in the disconnected set `Y ∩ A ∩ B`. So
  `(Y ∪ A) ∩ B` is not unicoherent, hence equals `Y ∪ A`.

(Proved through `subset_of_unicoherent_absorb'`, which only uses the consequence (∗∗) of the
hypothesis `hstar`.) -/
theorem subset_of_unicoherent_absorb {Y A B : Set S}
    (hY : Fold.Q78.IsContinuum Y) (hA : Fold.Q78.IsContinuum A) (hB : Fold.Q78.IsContinuum B)
    (hAB : (A ∩ B).Nonempty) (hYAne : (Y ∩ A).Nonempty) (hYA : ¬ IsConnected (Y ∩ A))
    (hX : IsUnicoherent (Y ∪ A ∪ B))
    (hstar : ∀ M ⊆ Y ∪ A, Fold.Q78.IsContinuum M → M ≠ Y ∪ A → IsUnicoherent M) :
    Y ∪ A ⊆ B := by
  refine subset_of_unicoherent_absorb' hY hA hB hAB hYAne hYA hX ?_
  intro P Q hP hQ hPY hQA hPQne hPQ
  by_contra hne'
  exact not_isUnicoherent_of_split hP hQ hPQ
    (hstar (P ∪ Q) (union_subset_union hPY hQA) (isContinuum_union hP hQ hPQne) hne')

/-! ### Chains indexed by intervals of `ℕ`

For the induction, a chain is a sequence `A : ℕ → Set S` of snake-like continua with consecutive
terms meeting, and the pieces are the interval unions `chainUnion A a b = A a ∪ ⋯ ∪ A b`. This
replaces the re-indexing of the tail `A_{p+1}, …, A_k` as a `Fin (k - p)`-chain. -/

/-- `A a ∪ ⋯ ∪ A b`. -/
def chainUnion (A : ℕ → Set S) (a b : ℕ) : Set S := ⋃ l, ⋃ (_ : a ≤ l ∧ l ≤ b), A l

omit [MetricSpace S] [CompactSpace S] in
theorem mem_chainUnion {A : ℕ → Set S} {a b : ℕ} {x : S} :
    x ∈ chainUnion A a b ↔ ∃ l, (a ≤ l ∧ l ≤ b) ∧ x ∈ A l := by
  simp [chainUnion]

omit [MetricSpace S] [CompactSpace S] in
theorem subset_chainUnion {A : ℕ → Set S} {a b l : ℕ} (h1 : a ≤ l) (h2 : l ≤ b) :
    A l ⊆ chainUnion A a b := fun _ hx => mem_chainUnion.mpr ⟨l, ⟨h1, h2⟩, hx⟩

omit [MetricSpace S] [CompactSpace S] in
theorem chainUnion_mono {A : ℕ → Set S} {a b a' b' : ℕ} (h1 : a' ≤ a) (h2 : b ≤ b') :
    chainUnion A a b ⊆ chainUnion A a' b' := fun _ hx => by
  obtain ⟨l, ⟨hl1, hl2⟩, hx⟩ := mem_chainUnion.mp hx
  exact mem_chainUnion.mpr ⟨l, ⟨by omega, by omega⟩, hx⟩

omit [MetricSpace S] [CompactSpace S] in
theorem chainUnion_self (A : ℕ → Set S) (a : ℕ) : chainUnion A a a = A a := by
  ext x
  rw [mem_chainUnion]
  constructor
  · rintro ⟨l, ⟨h1, h2⟩, hx⟩
    rwa [show l = a by omega] at hx
  · intro hx; exact ⟨a, ⟨le_rfl, le_rfl⟩, hx⟩

omit [MetricSpace S] [CompactSpace S] in
theorem chainUnion_split (A : ℕ → Set S) {a b c : ℕ} (h1 : a ≤ c + 1) (h2 : c ≤ b) :
    chainUnion A a b = chainUnion A a c ∪ chainUnion A (c + 1) b := by
  ext x
  simp only [mem_union, mem_chainUnion]
  constructor
  · rintro ⟨l, ⟨hl1, hl2⟩, hx⟩
    rcases Nat.lt_or_ge c l with h | h
    · exact Or.inr ⟨l, ⟨by omega, hl2⟩, hx⟩
    · exact Or.inl ⟨l, ⟨hl1, h⟩, hx⟩
  · rintro (⟨l, ⟨hl1, hl2⟩, hx⟩ | ⟨l, ⟨hl1, hl2⟩, hx⟩)
    · exact ⟨l, ⟨hl1, by omega⟩, hx⟩
    · exact ⟨l, ⟨by omega, hl2⟩, hx⟩

omit [MetricSpace S] [CompactSpace S] in
theorem chainUnion_succ (A : ℕ → Set S) {a b : ℕ} (h : a ≤ b + 1) :
    chainUnion A a (b + 1) = chainUnion A a b ∪ A (b + 1) := by
  rw [chainUnion_split A h (Nat.le_succ b), chainUnion_self]

section IntervalChains

variable {A : ℕ → Set S} (hA : ∀ i, IsSnakeLike (A i)) (hm : ∀ i, (A i ∩ A (i + 1)).Nonempty)
include hA hm

omit hA [MetricSpace S] [CompactSpace S] in
theorem inter_chainUnion_nonempty {a b : ℕ} (hab : a ≤ b) :
    (chainUnion A a b ∩ A (b + 1)).Nonempty := by
  obtain ⟨x, hx1, hx2⟩ := hm b
  exact ⟨x, subset_chainUnion hab le_rfl hx1, hx2⟩

omit [CompactSpace S] in
theorem isContinuum_chainUnion {a b : ℕ} (hab : a ≤ b) :
    Fold.Q78.IsContinuum (chainUnion A a b) := by
  induction b, hab using Nat.le_induction with
  | base => rw [chainUnion_self]; exact (hA a).1
  | succ b hab ih =>
    rw [chainUnion_succ A (by omega)]
    exact isContinuum_union ih (hA _).1 (inter_chainUnion_nonempty hm hab)

/-- Fugate's Corollary 1 under hereditary unicoherence (`fugate_cor1'`), for interval unions. -/
theorem isSnakeLike_chainUnion_of_hu {a b : ℕ} (hab : a ≤ b)
    (hat : IsAtriodic (chainUnion A a b)) (hhu : IsHereditarilyUnicoherent (chainUnion A a b)) :
    IsSnakeLike (chainUnion A a b) := by
  induction b, hab using Nat.le_induction with
  | base => rw [chainUnion_self]; exact hA a
  | succ b hab ih =>
    have e := chainUnion_succ A (a := a) (b := b) (by omega)
    have hsub : chainUnion A a b ⊆ chainUnion A a (b + 1) := chainUnion_mono le_rfl (by omega)
    rw [e] at hat hhu ⊢
    exact fugate_theorem1_sufficiency_hu (ih (hat.mono (e ▸ hsub)) (hhu.mono (e ▸ hsub)))
      (hA _) (inter_chainUnion_nonempty hm hab) hat hhu

/-- **Step 1 for interval unions.** If every partial union `A a ∪ ⋯ ∪ A q`, `a ≤ q ≤ p`, is
unicoherent, then `A a ∪ ⋯ ∪ A p` is hereditarily unicoherent. -/
theorem isHereditarilyUnicoherent_chainUnion {a p : ℕ} (hap : a ≤ p)
    (hu : ∀ q, a ≤ q → q ≤ p → IsUnicoherent (chainUnion A a q)) :
    IsHereditarilyUnicoherent (chainUnion A a p) := by
  induction p, hap using Nat.le_induction with
  | base => rw [chainUnion_self]; exact isHereditarilyUnicoherent_of_isSnakeLike (hA a)
  | succ p hap ih =>
    have e := chainUnion_succ A (a := a) (b := p) (by omega)
    rw [e]
    refine isHereditarilyUnicoherent_union (isContinuum_chainUnion hA hm hap) (hA _).1
      (ih fun q h1 h2 => hu q h1 (by omega)) (isHereditarilyUnicoherent_of_isSnakeLike (hA _)) ?_
    exact hu (p + 1) (by omega) le_rfl _ _ (isContinuum_chainUnion hA hm hap) (hA _).1 e.symm

/-- **Steps 1–6 for interval unions, from (∗∗).** Strong induction on `b - a`. -/
theorem isSnakeLike_chainUnion_of_ingramStarWeak (hstar : IngramStarWeak S) :
    ∀ n a b, b - a = n → a ≤ b → IsAtriodic (chainUnion A a b) →
      IsUnicoherent (chainUnion A a b) → IsSnakeLike (chainUnion A a b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn hab hat hu
  classical
  by_cases hall : ∀ q, a ≤ q → q ≤ b → IsUnicoherent (chainUnion A a q)
  · exact isSnakeLike_chainUnion_of_hu hA hm hab hat
      (isHereditarilyUnicoherent_chainUnion hA hm hab hall)
  push_neg at hall
  have hex : ∃ q, a ≤ q ∧ q ≤ b ∧ ¬ IsUnicoherent (chainUnion A a q) := hall
  obtain ⟨hap, hpb, hpu⟩ := Nat.find_spec hex
  have hmin : ∀ q, a ≤ q → q < Nat.find hex → IsUnicoherent (chainUnion A a q) := by
    intro q h1 h2
    by_contra h
    exact Nat.find_min hex h2 ⟨h1, by omega, h⟩
  generalize Nat.find hex = p at hap hpb hpu hmin
  have hpa : p ≠ a := by
    intro h
    apply hpu
    rw [h, chainUnion_self]
    exact isUnicoherent_of_isSnakeLike (hA a)
  have hpb' : p ≠ b := by
    intro h; rw [h] at hpu; exact hpu hu
  obtain ⟨r, hr⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  have har : a ≤ r := by omega
  have hrb : r + 2 ≤ b := by omega
  set Y := chainUnion A a r with hY_def
  have eC : chainUnion A a (r + 1) = Y ∪ A (r + 1) := chainUnion_succ A (by omega)
  have hCsub : chainUnion A a (r + 1) ⊆ chainUnion A a b := chainUnion_mono le_rfl (by omega)
  have hYsub : Y ⊆ chainUnion A a b := chainUnion_mono le_rfl (by omega)
  have hYhu : IsHereditarilyUnicoherent Y :=
    isHereditarilyUnicoherent_chainUnion hA hm har fun q h1 h2 => hmin q h1 (by omega)
  have hYs : IsSnakeLike Y := isSnakeLike_chainUnion_of_hu hA hm har (hat.mono hYsub) hYhu
  have hYA : (Y ∩ A (r + 1)).Nonempty := inter_chainUnion_nonempty hm har
  have hpu' : ¬ IsUnicoherent (chainUnion A a (r + 1)) := hr ▸ hpu
  have hYAnc : ¬ IsConnected (Y ∩ A (r + 1)) := by
    intro hc
    apply hpu'
    refine isUnicoherent_of_isSnakeLike (isSnakeLike_chainUnion_of_hu hA hm (by omega)
      (hat.mono hCsub) ?_)
    rw [eC]
    exact isHereditarilyUnicoherent_union hYs.1 (hA _).1 hYhu
      (isHereditarilyUnicoherent_of_isSnakeLike (hA _)) hc
  set B := chainUnion A (r + 2) b with hB_def
  have hBc : Fold.Q78.IsContinuum B := isContinuum_chainUnion hA hm hrb
  have hAB : (A (r + 1) ∩ B).Nonempty := by
    obtain ⟨x, hx1, hx2⟩ := hm (r + 1)
    exact ⟨x, hx1, subset_chainUnion le_rfl hrb hx2⟩
  have eX : chainUnion A a b = Y ∪ A (r + 1) ∪ B := by
    rw [chainUnion_split A (c := r + 1) (by omega) (by omega), eC]
  have habs : Y ∪ A (r + 1) ⊆ B := by
    refine subset_of_unicoherent_absorb' hYs.1 (hA _).1 hBc hAB hYA hYAnc (eX ▸ hu) ?_
    exact hstar Y (A (r + 1)) hYs (hA _) hYA (eC ▸ hat.mono hCsub) hYAnc
  have eXB : chainUnion A a b = B := by
    rw [eX]; exact union_eq_right.mpr habs
  have hatB : IsAtriodic B := eXB ▸ hat
  have huB : IsUnicoherent B := eXB ▸ hu
  have hBs : IsSnakeLike B := ih (b - (r + 2)) (by omega) (r + 2) b rfl hrb hatB huB
  rw [eXB]
  exact hBs

end IntervalChains

/-- The `ℕ`-indexed extension of a `Fin (k + 1)`-chain: `A' n = A (min n k)`. -/
def finChainExt {k : ℕ} (A : Fin (k + 1) → Set S) (n : ℕ) : Set S :=
  A ⟨min n k, Nat.lt_succ_of_le (min_le_right n k)⟩

omit [CompactSpace S] in
theorem finChainExt_snake {k : ℕ} {A : Fin (k + 1) → Set S} (hA : ∀ i, IsSnakeLike (A i)) :
    ∀ n, IsSnakeLike (finChainExt A n) := fun _ => hA _

omit [CompactSpace S] in
theorem finChainExt_meet {k : ℕ} {A : Fin (k + 1) → Set S} (hA : ∀ i, IsSnakeLike (A i))
    (hmeet : ∀ i : Fin k, (A i.castSucc ∩ A i.succ).Nonempty) :
    ∀ n, (finChainExt A n ∩ finChainExt A (n + 1)).Nonempty := by
  intro n
  rcases Nat.lt_or_ge n k with h | h
  · have := hmeet ⟨n, h⟩
    unfold finChainExt
    convert this using 3 <;> simp [Fin.ext_iff] <;> omega
  · unfold finChainExt
    have e : (⟨min (n + 1) k, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (k + 1)) =
        ⟨min n k, Nat.lt_succ_of_le (min_le_right _ _)⟩ := Fin.ext (by simp only; omega)
    rw [e, inter_self]
    exact (hA _).1.2.nonempty

omit [MetricSpace S] [CompactSpace S] in
theorem finChainExt_partial {k : ℕ} (A : Fin (k + 1) → Set S) (p : ℕ) :
    (⋃ (l : Fin (k + 1)) (_ : l.val ≤ p), A l) = chainUnion (finChainExt A) 0 p := by
  ext x
  simp only [mem_iUnion, exists_prop, mem_chainUnion, finChainExt]
  constructor
  · rintro ⟨l, hl, hx⟩
    refine ⟨l.val, ⟨Nat.zero_le _, hl⟩, ?_⟩
    convert hx using 2; ext; simp; omega
  · rintro ⟨l, ⟨-, hl⟩, hx⟩
    exact ⟨_, by simp; omega, hx⟩

omit [MetricSpace S] [CompactSpace S] in
theorem finChainExt_union {k : ℕ} (A : Fin (k + 1) → Set S) :
    (⋃ i, A i) = chainUnion (finChainExt A) 0 k := by
  rw [← finChainExt_partial A k]
  ext x
  simp only [mem_iUnion, exists_prop]
  exact ⟨fun ⟨l, hx⟩ => ⟨l, by omega, hx⟩, fun ⟨l, _, hx⟩ => ⟨l, hx⟩⟩

/-- **Step 1: the partial unions.** If every partial union `A₀ ∪ ⋯ ∪ A_q` with `q ≤ p` is
unicoherent, then `A₀ ∪ ⋯ ∪ A_p` is hereditarily unicoherent (`isHereditarilyUnicoherent_union`,
induction on `q`). State it with the partial-union function you find convenient; `fugate_cor1'`
uses `U p := ⋃ (l : Fin (k + 1)) (_ : l.val ≤ p), A l`. (Shape change: the skeleton's hypothesis
`hp : p ≤ k` is not needed and has been removed; for `p ≥ k` the partial union is the whole
union.) -/
theorem isHereditarilyUnicoherent_partial {k : ℕ} (A : Fin (k + 1) → Set S)
    (hA : ∀ i, IsSnakeLike (A i)) (hmeet : ∀ i : Fin k, (A i.castSucc ∩ A i.succ).Nonempty)
    {p : ℕ}
    (hu : ∀ q ≤ p, IsUnicoherent (⋃ (l : Fin (k + 1)) (_ : l.val ≤ q), A l)) :
    IsHereditarilyUnicoherent (⋃ (l : Fin (k + 1)) (_ : l.val ≤ p), A l) := by
  rw [finChainExt_partial A p]
  refine isHereditarilyUnicoherent_chainUnion (finChainExt_snake hA)
    (finChainExt_meet hA hmeet) (Nat.zero_le _) fun q _ hq => ?_
  rw [← finChainExt_partial A q]
  exact hu q hq

/-- **Corollary 1, sufficiency, under (∗∗).** -/
theorem fugateCor1Sufficiency_of_ingramStarWeak (hstar : IngramStarWeak S) :
    FugateCor1Sufficiency S := by
  intro k A hA hmeet hat hu
  rw [finChainExt_union A] at hat hu ⊢
  exact isSnakeLike_chainUnion_of_ingramStarWeak (finChainExt_snake hA)
    (finChainExt_meet hA hmeet) hstar _ 0 k rfl (Nat.zero_le _) hat hu

/-- **Corollary 1, sufficiency, under (∗).** Strong induction on `k`, Steps 1–6 of
fugate-cor1-proof.md. (Shape change: the induction runs over interval unions
`chainUnion A a b` of an `ℕ`-indexed chain, `isSnakeLike_chainUnion_of_ingramStarWeak`, instead
of re-indexing a tail as a `Fin (k - p)`-chain; and only the consequence (∗∗) of (∗) is used.) -/
theorem fugateCor1Sufficiency_of_ingramStar (hstar : IngramStar S) : FugateCor1Sufficiency S :=
  fugateCor1Sufficiency_of_ingramStarWeak (ingramStarWeak_of_ingramStar hstar)

/-- **Corollary 1 as stated, under (∗).** -/
theorem fugate_cor1_of_ingramStar (hstar : IngramStar S) {k : ℕ} (A : Fin (k + 1) → Set S)
    (hA : ∀ i, IsSnakeLike (A i)) (hmeet : ∀ i : Fin k, (A i.castSucc ∩ A i.succ).Nonempty) :
    IsSnakeLike (⋃ i, A i) ↔ IsAtriodic (⋃ i, A i) ∧ IsUnicoherent (⋃ i, A i) :=
  ⟨fugate_cor1_necessity A, fun h =>
    fugateCor1Sufficiency_of_ingramStar hstar k A hA hmeet h.1 h.2⟩

/-- **(U) holds under (∗)** (`fugateU_iff_cor1Sufficiency`). -/
theorem fugateU_of_ingramStar (hstar : IngramStar S) : FugateU S :=
  fugateU_iff_cor1Sufficiency.mpr (fugateCor1Sufficiency_of_ingramStar hstar)

end HPC.Plane
