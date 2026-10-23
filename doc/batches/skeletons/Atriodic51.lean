import HPC.Plane.Recon91

/-!
# Bing 1951 (*Snake-like continua*), §4, part one: atriodic hereditarily unicoherent hereditarily
# decomposable continua — the six properties and Theorem 8

Skeleton for batch 92 (save as `HPC/Plane/Atriodic51.lean`; add `import HPC.Plane.Atriodic51` to
the root `HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted
with the change recorded; `theorem8_1951` keeps its conclusion.

Throughout, `S` is a compact metric space which is itself the continuum (Bing: "we suppose that
`S` is all of the space"); "continuum" means `Fold.Q78.IsContinuum` (nonempty compact connected).
`A` contains `B` *interiorly* means `B ⊆ interior A`.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- A *triod*: a continuum `M` containing a subcontinuum `N` such that `M \ N` is the union of
three mutually separated nonempty sets (Bing 1951, §1). -/
def IsTriod (M : Set S) : Prop :=
  Fold.Q78.IsContinuum M ∧ ∃ N : Set S, Fold.Q78.IsContinuum N ∧ N ⊆ M ∧
    ∃ A B C : Set S, A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧ M \ N = A ∪ B ∪ C ∧
      Disjoint (closure A) B ∧ Disjoint A (closure B) ∧ Disjoint (closure A) C ∧
      Disjoint A (closure C) ∧ Disjoint (closure B) C ∧ Disjoint B (closure C)

/-- *Atriodic*: contains no triod. -/
def IsAtriodic (M : Set S) : Prop := ∀ T ⊆ M, ¬ IsTriod T

/-- *Unicoherent*: whenever the continuum is the union of two subcontinua, their intersection is
connected. -/
def IsUnicoherent (M : Set S) : Prop :=
  ∀ H K : Set S, Fold.Q78.IsContinuum H → Fold.Q78.IsContinuum K → H ∪ K = M → IsConnected (H ∩ K)

/-- *Hereditarily unicoherent*: every nondegenerate subcontinuum is unicoherent. -/
def IsHereditarilyUnicoherent (M : Set S) : Prop :=
  ∀ K ⊆ M, Fold.Q78.IsContinuum K → K.Nontrivial → IsUnicoherent K

/-- *Hereditarily decomposable*: every nondegenerate subcontinuum is the union of two proper
subcontinua. -/
def IsHereditarilyDecomposable (M : Set S) : Prop :=
  ∀ K ⊆ M, Fold.Q78.IsContinuum K → K.Nontrivial →
    ∃ A B : Set S, Fold.Q78.IsContinuum A ∧ Fold.Q78.IsContinuum B ∧ A ≠ K ∧ B ≠ K ∧ A ∪ B = K

/-- **Bing's standing hypothesis for §4**: the whole space is a nondegenerate (compact) continuum,
atriodic, hereditarily unicoherent and hereditarily decomposable. -/
structure BingS (S : Type*) [MetricSpace S] [CompactSpace S] : Prop where
  connected : ConnectedSpace S
  nontrivial : Nontrivial S
  atriodic : IsAtriodic (univ : Set S)
  hu : IsHereditarilyUnicoherent (univ : Set S)
  hd : IsHereditarilyDecomposable (univ : Set S)

/-- A set `A` *separates* `B` from `C` in `S`: `B` and `C` lie in different components of
`S \ A` — stated as: `S \ A` is the union of two separated sets, one containing `B`, the other `C`
(Bing: "one of them separates the other two from each other in `S`"). -/
def Separates (A B C : Set S) : Prop :=
  Disjoint A B ∧ Disjoint A C ∧ ∃ U V : Set S, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
    (univ : Set S) \ A ⊆ U ∪ V ∧ B ⊆ U ∧ C ⊆ V

variable (hS : BingS S)

/-- **Property 1.** The intersection of a nonempty family of subcontinua with nonempty
intersection is a continuum. -/
theorem prop1_inter_continuum (hS : BingS S) {𝒦 : Set (Set S)} (h𝒦 : 𝒦.Nonempty)
    (hc : ∀ K ∈ 𝒦, Fold.Q78.IsContinuum K) (hne : (⋂₀ 𝒦).Nonempty) :
    Fold.Q78.IsContinuum (⋂₀ 𝒦) := by
  sorry

/-- **Property 2.** The complement of a subcontinuum has at most two components (stated as: no
three nonempty mutually separated pieces); the complement of the union of two intersecting
subcontinua has at most three. -/
theorem prop2_components (hS : BingS S) {H : Set S} (hH : Fold.Q78.IsContinuum H) :
    ¬ ∃ A B C : Set S, A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧ (univ : Set S) \ H = A ∪ B ∪ C ∧
      Disjoint (closure A) B ∧ Disjoint A (closure B) ∧ Disjoint (closure A) C ∧
      Disjoint A (closure C) ∧ Disjoint (closure B) C ∧ Disjoint B (closure C) := by
  sorry

/-- **Property 3.** If three subcontinua pairwise intersect, one lies in the union of the other
two. -/
theorem prop3_one_in_union (hS : BingS S) {H₁ H₂ H₃ : Set S}
    (h₁ : Fold.Q78.IsContinuum H₁) (h₂ : Fold.Q78.IsContinuum H₂) (h₃ : Fold.Q78.IsContinuum H₃)
    (h₁₂ : (H₁ ∩ H₂).Nonempty) (h₂₃ : (H₂ ∩ H₃).Nonempty) (h₁₃ : (H₁ ∩ H₃).Nonempty) :
    H₁ ⊆ H₂ ∪ H₃ ∨ H₂ ⊆ H₁ ∪ H₃ ∨ H₃ ⊆ H₁ ∪ H₂ := by
  sorry

/-- **Property 4.** Of three mutually exclusive subcontinua with interior points, one separates
the other two. -/
theorem prop4_separates (hS : BingS S) {H₁ H₂ H₃ : Set S}
    (h₁ : Fold.Q78.IsContinuum H₁) (h₂ : Fold.Q78.IsContinuum H₂) (h₃ : Fold.Q78.IsContinuum H₃)
    (hi₁ : (interior H₁).Nonempty) (hi₂ : (interior H₂).Nonempty) (hi₃ : (interior H₃).Nonempty)
    (d₁₂ : Disjoint H₁ H₂) (d₂₃ : Disjoint H₂ H₃) (d₁₃ : Disjoint H₁ H₃) :
    Separates H₁ H₂ H₃ ∨ Separates H₂ H₁ H₃ ∨ Separates H₃ H₁ H₂ := by
  sorry

/-- **Property 5.** Two mutually exclusive subcontinua with interior points are separated by a
subcontinuum with interior points. -/
theorem prop5_exists_separating (hS : BingS S) {H₁ H₂ : Set S}
    (h₁ : Fold.Q78.IsContinuum H₁) (h₂ : Fold.Q78.IsContinuum H₂)
    (hi₁ : (interior H₁).Nonempty) (hi₂ : (interior H₂).Nonempty) (d : Disjoint H₁ H₂) :
    ∃ K : Set S, Fold.Q78.IsContinuum K ∧ (interior K).Nonempty ∧ Separates K H₁ H₂ := by
  sorry

/-- **Property 6.** Between a continuum and a continuum it contains interiorly there is a third,
contained interiorly in the first and containing the second interiorly. -/
theorem prop6_between (hS : BingS S) {H₁ H₂ : Set S}
    (h₁ : Fold.Q78.IsContinuum H₁) (h₂ : Fold.Q78.IsContinuum H₂)
    (hi₂ : (interior H₂).Nonempty) (h₂₁ : H₂ ⊆ interior H₁) :
    ∃ H₃ : Set S, Fold.Q78.IsContinuum H₃ ∧ H₃ ⊆ interior H₁ ∧ H₂ ⊆ interior H₃ := by
  sorry

/-- **The elements of Bing's decomposition**: `g p` is the intersection of all continua containing
`p` interiorly. -/
def gElt (p : S) : Set S := ⋂₀ {H : Set S | Fold.Q78.IsContinuum H ∧ p ∈ interior H}

/-- **Theorem 8** (Bing 1951, p. 658), with (a) in the form Bing proves it. The collection
`G = {g p}`: its members are continua, they partition `S`, the collection is upper semicontinuous
(for every `p` and open `U ⊇ g p`, the union of the `g q` lying in `U` is open), (a) of any three
distinct members one separates the other two, (b) no member has interior points, (c) if `r`, `s` lie
in different *end* members (members that separate no two others) then the only subcontinuum
containing both is `S`. -/
theorem theorem8_1951 (hS : BingS S) :
    (∀ p, Fold.Q78.IsContinuum (gElt p)) ∧
    (∀ p, p ∈ gElt p) ∧ (∀ p q, q ∈ gElt p → gElt p = gElt q) ∧
    (∀ p (U : Set S), IsOpen U → gElt p ⊆ U → IsOpen (⋃ q ∈ {q | gElt q ⊆ U}, gElt q)) ∧
    (∀ p q r, gElt p ≠ gElt q → gElt q ≠ gElt r → gElt p ≠ gElt r →
      Separates (gElt p) (gElt q) (gElt r) ∨ Separates (gElt q) (gElt p) (gElt r) ∨
        Separates (gElt r) (gElt p) (gElt q)) ∧
    (∀ p, interior (gElt p) = ∅) ∧
    (∀ r s, (∀ q q', gElt q ≠ gElt r → gElt q' ≠ gElt r → gElt q ≠ gElt q' →
        ¬ Separates (gElt r) (gElt q) (gElt q')) →
      (∀ q q', gElt q ≠ gElt s → gElt q' ≠ gElt s → gElt q ≠ gElt q' →
        ¬ Separates (gElt s) (gElt q) (gElt q')) →
      gElt r ≠ gElt s →
      ∀ M : Set S, Fold.Q78.IsContinuum M → r ∈ M → s ∈ M → M = univ) := by
  sorry

/-- **The decomposition space is an arc** (Bing's "arc with respect to its elements"): the
quotient of `S` by `p ~ q ⇔ g p = g q` is homeomorphic to `[0, 1]`. Expected to need the non-cut
point characterization of the arc (Nadler 6.17), not in Mathlib; may be left `sorry` with the
partial results recorded (COMMISSION-batch92.md §3.7). -/
theorem isArc_of_separatesPairs (hS : BingS S) :
    Nonempty (Quotient (Setoid.ker (gElt (S := S))) ≃ₜ unitInterval) := by
  sorry

end HPC.Plane
