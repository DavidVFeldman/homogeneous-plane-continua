import Mathlib

/-!
# Moore, F.A. (1916), §2: primitives, definitions and axioms (batch 137, item A)

Verbatim from the batch-137 skeleton (`doc/batches/skeletons/MooreFA.lean`, §1), transcribed from
the page images of R. L. Moore, *On the foundations of plane analysis situs*, Trans. AMS 17 (1916),
pp. 132–139. No definition has been changed. Moore's primitives are kept: a type `S` of points and
a class `σ.region` of subsets called regions.

Notation. Moore writes `M'` for `M` plus its boundary (`cl`), `M + N` for union, `M − N` for
difference, "region about `P`" for "region containing `P`", and "without `R`" for "in the
exterior of `R`".
-/

namespace HPC.Moore

open Set

/-! ## §1. Primitives and definitions (F.A. §2, p. 132) -/

/-- A *space* in Moore's sense: points (the type `S`) and a class of subsets called regions. -/
structure Space (S : Type*) where
  region : Set (Set S)

variable {S : Type*} (σ : Space S)

namespace Space

/-- `P` is a *limit point* of `M`: every region containing `P` contains a point of `M` other than
`P`. -/
def IsLimitPt (P : S) (M : Set S) : Prop :=
  ∀ R ∈ σ.region, P ∈ R → ∃ x ∈ M, x ∈ R ∧ x ≠ P

/-- The *boundary* of `M`: the points `X` such that every region containing `X` contains a point
of `M` and a point not in `M`. -/
def bdry (M : Set S) : Set S :=
  {X | ∀ R ∈ σ.region, X ∈ R → (R ∩ M).Nonempty ∧ (R \ M).Nonempty}

/-- `M'`: `M` together with its boundary. -/
def cl (M : Set S) : Set S := M ∪ σ.bdry M

/-- The *exterior* of `M` is `S − M'` (Moore defines it for a region). -/
def ext (M : Set S) : Set S := (σ.cl M)ᶜ

/-- *Connected*: however `M` is divided into two mutually exclusive subsets, one of them contains
a limit point of the other.
**Implicit hypothesis (to record):** the two parts must be nonempty. Otherwise the split
`M = M ∪ ∅` would make every set disconnected. -/
def IsConn (M : Set S) : Prop :=
  ∀ A B : Set S, A ∪ B = M → Disjoint A B → A.Nonempty → B.Nonempty →
    (∃ x ∈ A, σ.IsLimitPt x B) ∨ (∃ x ∈ B, σ.IsLimitPt x A)

/-- A set of regions `K` *covers* `M`. -/
def Covers (K : Set (Set S)) (M : Set S) : Prop := K ⊆ σ.region ∧ M ⊆ ⋃₀ K

/-- The *Heine–Borel property*. Moore says "for every infinite set of regions covering `M`";
finite covers are trivially their own finite subcovers. -/
def HeineBorel (M : Set S) : Prop :=
  ∀ K : Set (Set S), σ.Covers K M → ∃ F : Finset (Set S), ↑F ⊆ K ∧ M ⊆ ⋃₀ ↑F

/-- *Closed* (p. 135): contains all its limit points. -/
def IsClosedM (M : Set S) : Prop := ∀ P, σ.IsLimitPt P M → P ∈ M

/-- *Bounded* (p. 135): contained in `(R₁ + ⋯ + Rₙ)'` for finitely many regions. -/
def IsBoundedM (M : Set S) : Prop :=
  ∃ F : Finset (Set S), ↑F ⊆ σ.region ∧ M ⊆ σ.cl (⋃₀ ↑F)

/-- *Domain* (p. 136): a connected set each point of which lies in a region inside the set. -/
def IsDomain (M : Set S) : Prop :=
  σ.IsConn M ∧ ∀ P ∈ M, ∃ R ∈ σ.region, P ∈ R ∧ R ⊆ M

/-- *Simple continuous arc from `A` to `B`* (p. 136, after Lennes 1911, p. 308): a bounded,
closed, connected set containing `A` and `B` and containing no connected proper subset that
contains both. -/
def IsArc (A B : S) (C : Set S) : Prop :=
  A ≠ B ∧ σ.IsBoundedM C ∧ σ.IsClosedM C ∧ σ.IsConn C ∧ A ∈ C ∧ B ∈ C ∧
    ∀ H ⊆ C, H ≠ C → A ∈ H → B ∈ H → ¬ σ.IsConn H

/-- *Simple closed curve* (p. 139, after Lennes p. 314): the union of two arcs from `A` to `B`
with only `A` and `B` in common. -/
def IsSCC (J : Set S) : Prop :=
  ∃ A B : S, ∃ C₁ C₂ : Set S, σ.IsArc A B C₁ ∧ σ.IsArc A B C₂ ∧ C₁ ∩ C₂ = {A, B} ∧
    J = C₁ ∪ C₂

/-- *Sequential limit point* (p. 134). -/
def IsSeqLimit (P : S) (u : ℕ → S) : Prop :=
  ∀ R ∈ σ.region, P ∈ R → ∃ δ : ℕ, ∀ n > δ, u n ∈ R

/-- *Simple chain from `A` to `B`* (p. 134): regions `R₀ … R_{n-1}` (0-indexed here) with `A` only
in the first, `B` only in the last, and `Rᵢ ∩ Rⱼ ≠ ∅` (`i < j`) iff `j = i + 1`. -/
def IsSimpleChain (A B : S) (R : List (Set S)) : Prop :=
  A ≠ B ∧ R ≠ [] ∧ (∀ X ∈ R, X ∈ σ.region) ∧
    (∀ i (h : i < R.length), A ∈ R.get ⟨i, h⟩ ↔ i = 0) ∧
    (∀ i (h : i < R.length), B ∈ R.get ⟨i, h⟩ ↔ i + 1 = R.length) ∧
    (∀ i j (hi : i < R.length) (hj : j < R.length), i < j →
      ((R.get ⟨i, hi⟩ ∩ R.get ⟨j, hj⟩).Nonempty ↔ j = i + 1))

/-! ### The axioms (pp. 132–133). Transcribed from the page image; the overbars matter:
`P̄`, `R̄`, `K̄`, `L̄` are second objects, not closures. -/

/-- **Axiom 1.** There is a sequence of regions `K₁, K₂, …` such that (1) every point lies in `Kₙ`
for arbitrarily large `n`; (2) if `P` and `P̄` are distinct points of a region `R`, then for all
large `n`, `Kₙ ∋ P` implies `Kₙ' ⊆ R − P̄`. -/
def Axiom1 : Prop :=
  ∃ K : ℕ → Set S, (∀ n, K n ∈ σ.region) ∧ (∀ (m : ℕ) (P : S), ∃ n > m, P ∈ K n) ∧
    ∀ R ∈ σ.region, ∀ P ∈ R, ∀ P' ∈ R, P ≠ P' →
      ∃ δ : ℕ, ∀ n > δ, P ∈ K n → σ.cl (K n) ⊆ R \ {P'}

/-- **Axiom 2.** Every region is connected. -/
def Axiom2 : Prop := ∀ R ∈ σ.region, σ.IsConn R

/-- **Axiom 3.** If `R` is a region, `S − R'` is connected. -/
def Axiom3 : Prop := ∀ R ∈ σ.region, σ.IsConn (σ.ext R)

/-- **Axiom 4.** If `R` is a region, `R'` has the Heine–Borel property. -/
def Axiom4 : Prop := ∀ R ∈ σ.region, σ.HeineBorel (σ.cl R)

/-- **Axiom 5.** There is an infinite set of points with no limit point. -/
def Axiom5 : Prop := ∃ M : Set S, M.Infinite ∧ ∀ P, ¬ σ.IsLimitPt P M

/-- **Axiom 5₁** (footnote p. 133): there exist at least three points. -/
def Axiom5₁ : Prop := ∃ a b c : S, a ≠ b ∧ b ≠ c ∧ a ≠ c

/-- **Axiom 6.** If `R`, `R̄` are regions and `P ∈ R̄` is on the boundary of `R`, then there are
regions `K`, `K̄` in `R̄` with `P ∈ K̄`, `K ⊆ R`, and every boundary point of `R` in `K̄` a boundary
point of `K`. -/
def Axiom6 : Prop :=
  ∀ R ∈ σ.region, ∀ R' ∈ σ.region, ∀ P ∈ R', P ∈ σ.bdry R →
    ∃ K ∈ σ.region, ∃ K' ∈ σ.region, K ⊆ R' ∧ K' ⊆ R' ∧ P ∈ K' ∧ K ⊆ R ∧
      σ.bdry R ∩ K' ⊆ σ.bdry K

/-- **Axiom 7.** As Axiom 6, with `L ⊆ S − R'` in place of `K ⊆ R`. -/
def Axiom7 : Prop :=
  ∀ R ∈ σ.region, ∀ R' ∈ σ.region, ∀ P ∈ R', P ∈ σ.bdry R →
    ∃ L ∈ σ.region, ∃ L' ∈ σ.region, L ⊆ R' ∧ L' ⊆ R' ∧ P ∈ L' ∧ L ⊆ σ.ext R ∧
      σ.bdry R ∩ L' ⊆ σ.bdry L

/-- **Axiom 8.** Every simple closed curve is the boundary of at least one region. -/
def Axiom8 : Prop := ∀ J, σ.IsSCC J → ∃ R ∈ σ.region, σ.bdry R = J

end Space

end HPC.Moore
