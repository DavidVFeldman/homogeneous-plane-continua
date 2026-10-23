import HPC.Moore.FA7

/-!
# Batch 140 skeleton: F.A. Theorems 41–43 completed; Moore 1919, Theorems A and B

Save as `HPC/Moore/M19AB.lean` (splitting under `HPC/Moore/` is expected); add
`import HPC.Moore.M19AB` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be
adjusted, each change recorded at the statement and in the report.

Source: R. L. Moore, *Concerning a set of postulates for plane analysis situs*, Trans. AMS 20
(1919), 169–178 (`moore1919.pdf`, new; save as `doc/sources/moore1919.pdf`), pp. 170–172,
transcribed from page images at 200 dpi. "Numbered theorems are theorems in my paper *On the
foundations of plane analysis situs*" (footnote §, p. 170).

Definitions from the 1919 footnotes:
* p. 170, †: "If `X` and `Y` are two points of a closed curve `J`, there are just two arcs that lie
  wholly on `J` and have [`X` and `Y`] as endpoints. Each of these arcs is called an *interval* of
  `J`. An interval minus its endpoints is a *segment*." (Printed "have `A` and `B` as endpoints",
  a slip for `X` and `Y`; record it.)
* p. 171, ‡: "can be properly joined to `A₁`" means "is identical with `A₁` or can be joined to
  `A₁` by an arc of `L` that lies entirely within `J`".
-/

namespace HPC.Moore

open Set Topology

variable {S : Type*} {σ : Space S}

/-- A *segment* of the closed curve `J` (1919, p. 170): an interval of `J` minus its endpoints. -/
def Space.IsSegmentOf (σ : Space S) (J T : Set S) : Prop :=
  ∃ X Y : S, ∃ K : Set S, σ.IsArc X Y K ∧ K ⊆ J ∧ T = openArc X Y K

/-- Two arcs *have a segment in common*: some nondegenerate sub-arc's open part lies in both. -/
def Space.ShareSegment (σ : Space S) (K K' : Set S) : Prop :=
  ∃ X Y : S, ∃ T : Set S, σ.IsArc X Y T ∧ openArc X Y T ⊆ K ∩ K'

section M19

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-! ### Part A: F.A. Theorems 41–43 (left open in batch 139) -/

/-- **F.A. Theorem 41** (in full; Case II was open). -/
theorem fa_theorem41 {J₁ J₂ I₁ I₂ : Set S} (h₁ : σ.IsInteriorOf J₁ I₁)
    (h₂ : σ.IsInteriorOf J₂ I₂) (hmeet : (I₁ ∩ I₂).Nonempty) :
    ∃ J I, J ⊆ J₁ ∪ J₂ ∧ σ.IsInteriorOf J I ∧ I₁ ∪ I₂ ⊆ I := by
  sorry

/-- **F.A. Theorem 42** (unconditional, from `fa_theorem42_of_41`). -/
theorem fa_theorem42 (G : Finset (Set S × Set S)) (hG : ∀ p ∈ G, σ.IsInteriorOf p.1 p.2)
    (hne : G.Nonempty) (hconn : σ.IsConn (⋃ p ∈ G, p.2)) :
    ∃ J I, σ.IsInteriorOf J I ∧ J ⊆ ⋃ p ∈ G, p.1 ∧ ∀ p ∈ G, p.2 ⊆ I := by
  sorry

/-- **F.A. Theorem 43**, corrected (`G` nonempty). Either prove it, or leave it open and prove the
weaker statements 1919 actually draws from it (`m19_B_step`, and the arc in footnote * of p. 174,
see the commission). -/
theorem fa_theorem43 {J I : Set S} (hJ : σ.IsInteriorOf J I) {O : S} (hO : O ∈ J)
    (G : Finset (Set S × Set S)) (hGne : G.Nonempty) (hG : ∀ p ∈ G, σ.IsInteriorOf p.1 p.2)
    (hOG : ∀ p ∈ G, O ∈ p.2) (hnot : ∀ p ∈ G, ¬ I ⊆ p.2) :
    ∃ J₁ I₁ J₂ I₂, σ.IsInteriorOf J₁ I₁ ∧ σ.IsInteriorOf J₂ I₂ ∧ O ∈ J₁ ∧ O ∈ J₂ ∧
      J₁ ∪ J₂ ⊆ J ∪ ⋃ p ∈ G, p.1 ∧ I₁ ⊆ σ.ext I ∧ I₂ ⊆ I ∧
      ∀ p ∈ G, I₁ ∪ I₂ ⊆ p.2 := by
  sorry

/-! ### Part B: Moore 1919, Theorems A and B -/

/-- **Theorem A** (p. 170). If `L` is a simple closed curve and `M`, `N` are disjoint closed sets,
there is no infinite set of arcs `G` such that (1) each lies on `L`, (2) each contains a point of
`M` and a point of `N`, (3) no two have a segment in common. ("Infinite set" is rendered as an
injective sequence.) -/
theorem m19_theoremA {L : Set S} (hL : σ.IsSCC L) {M N : Set S} (hM : σ.IsClosedM M)
    (hN : σ.IsClosedM N) (hMN : Disjoint M N) :
    ¬ ∃ f : ℕ → Set S, Function.Injective f ∧
      (∀ n, (∃ a b, σ.IsArc a b (f n)) ∧ f n ⊆ L ∧ (f n ∩ M).Nonempty ∧ (f n ∩ N).Nonempty) ∧
      ∀ i j, i ≠ j → ¬ σ.ShareSegment (f i) (f j) := by
  sorry

/-- The step in the proof of Theorem B (p. 172): "It is easy to see, with the aid of Theorems 43 and
40, that there exists an arc `AₙZ̄ₙBₙ` that lies entirely within `J` and, except for its endpoints,
is also entirely within `L`." The data: an arc `K = AₙZₙBₙ` of `L` lying entirely within `J`. -/
theorem m19_B_step {J I L IL : Set S} (hJ : σ.IsInteriorOf J I) (hL : σ.IsInteriorOf L IL)
    {P Q : S} {K : Set S} (hK : σ.IsArc P Q K) (hKL : K ⊆ L) (hKI : K ⊆ I) :
    ∃ K', σ.IsArc P Q K' ∧ K' ⊆ I ∧ openArc P Q K' ⊆ IL := by
  sorry

/-- **Theorem B** (p. 170). If `J`, `L` are simple closed curves and `A ≠ B` are points of `J`, each
either not on `L` or on some segment common to `J` and `L`, there is an arc from `A` to `B` lying,
except for its endpoints, within `J` and having only finitely many points in common with `L`. -/
theorem m19_theoremB {J I L : Set S} (hJ : σ.IsInteriorOf J I) (hL : σ.IsSCC L) {A B : S}
    (hA : A ∈ J) (hB : B ∈ J) (hAB : A ≠ B)
    (hA' : A ∉ L ∨ ∃ T, σ.IsSegmentOf J T ∧ σ.IsSegmentOf L T ∧ A ∈ T)
    (hB' : B ∉ L ∨ ∃ T, σ.IsSegmentOf J T ∧ σ.IsSegmentOf L T ∧ B ∈ T) :
    ∃ K, σ.IsArc A B K ∧ openArc A B K ⊆ I ∧ (K ∩ L).Finite := by
  sorry

end M19

end HPC.Moore
