import HPC.Moore.FA

/-!
# Batch 138 skeleton: Moore, F.A. §6, Theorems 20–34 (pp. 140–150)

Save as `HPC/Moore/FA6.lean` (splitting under `HPC/Moore/` is expected); add `import HPC.Moore.FA6`
at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be adjusted, each change
recorded at the statement and in the report.

Transcribed from page images at 200 dpi. Moore's section heading: "Consequences of Axioms 2–8 and
Theorems 5 and 15". Theorem 5 uses Axiom 1, so the section carries Axioms 1–8. Record, for each
theorem, the axioms actually used.

**Moore's conventions in §6** (to be implemented by the definitions below):
* "closed curve" means simple closed curve (footnote p. 141);
* `AXB` with a bar beneath means the arc minus its endpoints (footnote p. 141): `openArc`;
* "the interior of `J`": **never defined in F.A.** It is used from the proof of Theorem 23 on.
  The intended meaning is the region whose boundary is `J`. It exists by Axiom 8 and is unique
  by Theorem 21; record this as an unnumbered gap. Here it is `IsInteriorOf J R`;
* "within `J`" means in the interior; "without `J`" means in the exterior of the interior;
* "`ACB`" is the arc from `A` to `B` through `C`; "`AXBCA`" is the closed curve formed by `AXB`
  and `ACB`;
* "`A` and `B` separate `C` and `D` on `J`" (p. 140): `SeparatesOn`.
-/

namespace HPC.Moore

open Set Topology

variable {S : Type*} (σ : Space S)

/-- The arc minus its endpoints (Moore's underlined `AXB`). It does not depend on the regions. -/
def openArc (A B : S) (C : Set S) : Set S := C \ {A, B}

namespace Space

/-- `R` is *the interior of* the closed curve `J`: a region with boundary `J`. -/
def IsInteriorOf (J R : Set S) : Prop := σ.IsSCC J ∧ R ∈ σ.region ∧ σ.bdry R = J

/-- `A`, `B` separate `C`, `D` on `J`, witnessed by the two arcs `C₁ = ACB` and `C₂ = ADB`. -/
def SeparatesOn (J : Set S) (A B C D : S) (C₁ C₂ : Set S) : Prop :=
  σ.IsArc A B C₁ ∧ σ.IsArc A B C₂ ∧ C₁ ∩ C₂ = {A, B} ∧ C₁ ∪ C₂ = J ∧
    C ∈ openArc A B C₁ ∧ D ∈ openArc A B C₂

/-- Points of the arc `K` (from `K₀` to `K₁`) in a given order: `pts` is the image of an increasing
list of parameters under a parametrization `f` with `f 0 = K₀`, `f 1 = K₁`. -/
def InOrder (K : Set S) (K₀ K₁ : S) (pts : List S) : Prop :=
  ∃ f : unitInterval → S, @IsEmbedding _ _ _ σ.topology f ∧ range f = K ∧ f 0 = K₀ ∧ f 1 = K₁ ∧
    ∃ ts : List unitInterval, ts.Pairwise (· < ·) ∧ pts = ts.map f

end Space

section Sec6

variable {σ} (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- Unnumbered (the convention "the interior of `J`"): every closed curve has exactly one interior.
Existence is Axiom 8; uniqueness is Theorem 21 applied both ways. -/
theorem existsUnique_interior {J : Set S} (hJ : σ.IsSCC J) : ∃! R, σ.IsInteriorOf J R := by
  sorry

/-- **Theorem 20.** Every point of the boundary of a region is a limit point of its exterior.
("Can easily be proved with the help of Axiom 7"; no proof printed.) -/
theorem fa_theorem20 {R : Set S} (hR : R ∈ σ.region) {P : S} (hP : P ∈ σ.bdry R) :
    σ.IsLimitPt P (σ.ext R) := by
  sorry

/-- **Theorem 21.** If `K`, `R` are regions and the boundary of `R` lies in `K'`, then `R ⊆ K`. -/
theorem fa_theorem21 {K R : Set S} (hK : K ∈ σ.region) (hR : R ∈ σ.region)
    (h : σ.bdry R ⊆ σ.cl K) : R ⊆ K := by
  sorry

/-- **Theorem 22.** The set of all points is connected. ("Can be easily proved with the help of
Theorem 19, Axioms 2 and 3 and Theorem 20.") -/
theorem fa_theorem22 : σ.IsConn univ := by
  sorry

/-- **Theorem 23.** No region is a subset of an arc. **Check:** the empty region (batch 137,
`withEmpty`) refutes the printed statement; `hne` is added. -/
theorem fa_theorem23 {R : Set S} (hR : R ∈ σ.region) (hne : R.Nonempty) {A B : S} {C : Set S}
    (hC : σ.IsArc A B C) : ¬ R ⊆ C := by
  sorry

/-- **Theorem 24.** If `A`, `B` separate `C`, `D` on `J` (arcs `ACB`, `ADB`), `R` is the interior of
`J`, and `AXB` is an arc whose open part lies in `R`, then
(1) `R₁`, the interior of `AXBCA`, lies in `R`; (2) the open arc `ADB` is without `R₁`;
(3) `R₁ ∩ R₂ = ∅`, where `R₂` is the interior of `AXBDA`. -/
theorem fa_theorem24 {J R : Set S} (hR : σ.IsInteriorOf J R) {A B C D : S} {C₁ C₂ : Set S}
    (hsep : σ.SeparatesOn J A B C D C₁ C₂) {X : Set S} (hX : σ.IsArc A B X)
    (hXR : openArc A B X ⊆ R) {R₁ R₂ : Set S} (hR₁ : σ.IsInteriorOf (X ∪ C₁) R₁)
    (hR₂ : σ.IsInteriorOf (X ∪ C₂) R₂) :
    R₁ ⊆ R ∧ openArc A B C₂ ⊆ σ.ext R₁ ∧ Disjoint R₁ R₂ := by
  sorry

/-- **Theorem 25.** Under the hypothesis of Theorem 24, `R = AXB (open) + R₁ + R₂`. -/
theorem fa_theorem25 {J R : Set S} (hR : σ.IsInteriorOf J R) {A B C D : S} {C₁ C₂ : Set S}
    (hsep : σ.SeparatesOn J A B C D C₁ C₂) {X : Set S} (hX : σ.IsArc A B X)
    (hXR : openArc A B X ⊆ R) {R₁ R₂ : Set S} (hR₁ : σ.IsInteriorOf (X ∪ C₁) R₁)
    (hR₂ : σ.IsInteriorOf (X ∪ C₂) R₂) :
    R = openArc A B X ∪ R₁ ∪ R₂ := by
  sorry

/-- **Theorem 26.** If `ACB`, `ADB`, `AFB` are three arcs, no two with a common point other than `A`
and `B`, then the interiors of `ACBFA`, `ACBDA`, `ADBFA` are not mutually exclusive (some two of
them meet). -/
theorem fa_theorem26 {A B : S} {K₁ K₂ K₃ : Set S} (hK₁ : σ.IsArc A B K₁) (hK₂ : σ.IsArc A B K₂)
    (hK₃ : σ.IsArc A B K₃) (h12 : K₁ ∩ K₂ = {A, B}) (h13 : K₁ ∩ K₃ = {A, B})
    (h23 : K₂ ∩ K₃ = {A, B}) {R R₁ R₂ : Set S} (hR : σ.IsInteriorOf (K₁ ∪ K₃) R)
    (hR₁ : σ.IsInteriorOf (K₁ ∪ K₂) R₁) (hR₂ : σ.IsInteriorOf (K₂ ∪ K₃) R₂) :
    (R ∩ R₁).Nonempty ∨ (R ∩ R₂).Nonempty ∨ (R₁ ∩ R₂).Nonempty := by
  sorry

/-- **Theorem 27.** If `A`, `B` separate `C`, `D` on `J` and the open arc `AXB` is without `J`, then
(1) `D` is without `AXBCA` or `C` is without `AXBDA`; (2) if `D` is without `AXBCA`, then `C` is
within `AXBDA`, and the interior of `AXBDA` is the open arc `ACB` + the interior of `ACBDA` (= `J`)
+ the interior of `AXBCA`. -/
theorem fa_theorem27 {J R : Set S} (hR : σ.IsInteriorOf J R) {A B C D : S} {C₁ C₂ : Set S}
    (hsep : σ.SeparatesOn J A B C D C₁ C₂) {X : Set S} (hX : σ.IsArc A B X)
    (hXR : openArc A B X ⊆ σ.ext R) {R₁ R₂ : Set S} (hR₁ : σ.IsInteriorOf (X ∪ C₁) R₁)
    (hR₂ : σ.IsInteriorOf (X ∪ C₂) R₂) :
    (D ∈ σ.ext R₁ ∨ C ∈ σ.ext R₂) ∧
      (D ∈ σ.ext R₁ → C ∈ R₂ ∧ R₂ = openArc A B C₁ ∪ R ∪ R₁) := by
  sorry

/-- **Theorem 28.** If `O` is on the closed curve `J`, `R̄` is a region about `O`, and `M` is the
interior or the exterior of `J`, there is an arc `AXB` with `A`, `B` on `J`, the open arc `AXB` in
`M ∩ R̄`, and, of the two arcs into which `A`, `B` divide `J`, the one containing `O` in `R̄`. -/
theorem fa_theorem28 {J R : Set S} (hR : σ.IsInteriorOf J R) {O : S} (hO : O ∈ J)
    {R' : Set S} (hR' : R' ∈ σ.region) (hOR' : O ∈ R') {M : Set S} (hM : M = R ∨ M = σ.ext R) :
    ∃ A B : S, ∃ X C₁ C₂ : Set S, σ.IsArc A B X ∧ openArc A B X ⊆ M ∩ R' ∧
      σ.IsArc A B C₁ ∧ σ.IsArc A B C₂ ∧ C₁ ∩ C₂ = {A, B} ∧ C₁ ∪ C₂ = J ∧ O ∈ C₁ ∧ C₁ ⊆ R' := by
  sorry

/-- **Theorem 29.** If `A`, `B` separate `C`, `D` on `J`, and the open arcs `AXB`, `CYD` are both
within or both without `J`, then they meet. -/
theorem fa_theorem29 {J R : Set S} (hR : σ.IsInteriorOf J R) {A B C D : S} {C₁ C₂ : Set S}
    (hsep : σ.SeparatesOn J A B C D C₁ C₂) {X Y : Set S} (hX : σ.IsArc A B X) (hY : σ.IsArc C D Y)
    (hin : (openArc A B X ⊆ R ∧ openArc C D Y ⊆ R) ∨
      (openArc A B X ⊆ σ.ext R ∧ openArc C D Y ⊆ σ.ext R)) :
    (openArc A B X ∩ openArc C D Y).Nonempty := by
  sorry

/-- **Theorem 30.** Under the hypothesis of Theorem 29, the interiors of `AXBDA` and `CYDBC` meet.
(No proof printed.) `DBC` is the arc of `J` from `D` to `C` through `B`; the shape of that datum is
left to you. -/
theorem fa_theorem30 {J R : Set S} (hR : σ.IsInteriorOf J R) {A B C D : S} {C₁ C₂ : Set S}
    (hsep : σ.SeparatesOn J A B C D C₁ C₂) {X Y : Set S} (hX : σ.IsArc A B X) (hY : σ.IsArc C D Y)
    (hin : (openArc A B X ⊆ R ∧ openArc C D Y ⊆ R) ∨
      (openArc A B X ⊆ σ.ext R ∧ openArc C D Y ⊆ σ.ext R))
    {DBC : Set S} (hDBC : σ.IsArc D C DBC ∧ DBC ⊆ J ∧ B ∈ DBC)
    {R₁ R₂ : Set S} (hR₁ : σ.IsInteriorOf (X ∪ C₂) R₁) (hR₂ : σ.IsInteriorOf (Y ∪ DBC) R₂) :
    (R₁ ∩ R₂).Nonempty := by
  sorry

/-- **Theorem 31.** If `CD` is an arc, `B` a point of `CD`, `BX` an arc meeting `CD` only in `B`, and
`R` a region containing `B`, then there is in `R` an arc `EFG` such that (1) `E`, `G` are on `CD` in
the order `C E B G D`; (2) the segment `EBG` of `CD` lies in `R`; (3) the open arc `EFG` misses
`CD`; (4) on `BX` there is a point `H` such that the segment `BH` of `BX`, except `B`, is within
the closed curve `EFGBE`. **Check:** the order `C E B G D` requires `B ≠ C, D`; it is added. -/
theorem fa_theorem31 {C D B Xp : S} {K L : Set S} (hK : σ.IsArc C D K) (hB : B ∈ openArc C D K)
    (hL : σ.IsArc B Xp L) (hKL : K ∩ L = {B}) {R : Set S} (hR : R ∈ σ.region) (hBR : B ∈ R) :
    ∃ E G : S, ∃ F seg : Set S, σ.IsArc E G F ∧ F ⊆ R ∧ σ.InOrder K C D [C, E, B, G, D] ∧
      σ.IsArc E G seg ∧ seg ⊆ K ∧ B ∈ seg ∧ seg ⊆ R ∧ Disjoint (openArc E G F) K ∧
      ∃ H : S, ∃ BH : Set S, σ.IsArc B H BH ∧ BH ⊆ L ∧
        ∃ I, σ.IsInteriorOf (F ∪ seg) I ∧ BH \ {B} ⊆ I := by
  sorry

/-- **Theorem 32.** If, in a domain `H`, `AB` is an arc, `A₁`, `D`, `B₁` are on `AB` in the order
`A A₁ D B₁ B`, `A₁X₁B₁` is an arc meeting `AB` only in `A₁`, `B₁`, and `C` is in the interior `R` of
the closed curve `A₁X₁B₁DA₁`, then there is, in `H`, an arc `CB` meeting `AB` only in `B`.
**Check:** the statement does not say that `A₁X₁B₁` or `R` lies in `H`; if `C ∉ H`, the conclusion
fails. Determine the intended hypothesis (the proof works in `H` throughout) and record it. The
skeleton assumes `X₁ ⊆ H` and `R ⊆ H`. -/
theorem fa_theorem32 {Hd : Set S} (hH : σ.IsDomain Hd) {A B A₁ D B₁ : S} {K : Set S}
    (hK : σ.IsArc A B K) (hKH : K ⊆ Hd) (hord : σ.InOrder K A B [A, A₁, D, B₁, B])
    {X₁ : Set S} (hX₁ : σ.IsArc A₁ B₁ X₁) (hX₁K : X₁ ∩ K = {A₁, B₁}) (hX₁H : X₁ ⊆ Hd)
    {seg : Set S} (hseg : σ.IsArc A₁ B₁ seg ∧ seg ⊆ K ∧ D ∈ seg)
    {R : Set S} (hR : σ.IsInteriorOf (X₁ ∪ seg) R) (hRH : R ⊆ Hd) {C : S} (hC : C ∈ R) :
    ∃ CB : Set S, σ.IsArc C B CB ∧ CB ⊆ Hd ∧ CB ∩ K = {B} := by
  sorry

/-- **Theorem 33.** If `A` is on the boundary of a region `R`, `B` is in `R`, and `AB` is an arc
whose open part (indeed `AB − A`) lies in `R`, then `R − (AB − A)` is connected. (Printed with an
unbalanced parenthesis: "`R − AB − A)`".) Moore gives two proofs: one when the boundary of `R` is a
closed curve (pp. 148–150), and one for any region (p. 150, after J. R. Kline). Formalize the
second; record whether the first is needed later. -/
theorem fa_theorem33 {R : Set S} (hR : R ∈ σ.region) {A B : S} (hA : A ∈ σ.bdry R) (hB : B ∈ R)
    {K : Set S} (hK : σ.IsArc A B K) (hKR : K \ {A} ⊆ R) : σ.IsConn (R \ (K \ {A})) := by
  sorry

/-- **Theorem 34.** If `J` is a closed curve and `AB` is an arc lying wholly in `R`, the interior of
`J`, then `R − AB` is connected. **Check:** printed "If `J` is a Jordan *arc*". Since `R` is "the
interior of `J`", this must be a misprint for closed curve. Also: the second proof (p. 150) treats
any region `R`; state that general form too (`fa_theorem34_region`). -/
theorem fa_theorem34 {J R : Set S} (hR : σ.IsInteriorOf J R) {A B : S} {K : Set S}
    (hK : σ.IsArc A B K) (hKR : K ⊆ R) : σ.IsConn (R \ K) := by
  sorry

theorem fa_theorem34_region {R : Set S} (hR : R ∈ σ.region) {A B : S} {K : Set S}
    (hK : σ.IsArc A B K) (hKR : K ⊆ R) : σ.IsConn (R \ K) := by
  sorry

end Sec6

end HPC.Moore
