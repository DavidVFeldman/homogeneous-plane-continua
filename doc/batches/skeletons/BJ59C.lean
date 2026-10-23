import HPC.BJ59.BJ59B

/-!
# Batch 200 skeleton: Part G, III — Bing–Jones's homeomorphism of pp. 188–189, private points,
# Step 1(b), Theorem 8 and its corollary, Theorem 9

Save as `HPC/BJ59/BJ59C.lean` (splitting under `HPC/BJ59/` is expected); add
`import HPC.BJ59.BJ59C` at the end of `HPC.lean`. Adjust the imports as needed. Every `sorry` is a
work item. Unproved items are commented out with an `OPEN` note, as before. Library lemmas beyond
those stated here are left to you. Section numbers follow commission 200.

Source: R. H. Bing and F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959),
§§4–6 (`doc/sources/bing-jones1959.pdf`; PDF page `n` is journal page `169 + n`). Route:
commission 200.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.HO16

/-! ## §2. The homeomorphism of pp. 188–189 -/

section Zigzag

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- `H_i d(p, i)` of p. 188: the union of the images under `H` of the links of `D` that contain
`p`. -/
def starImage {n m : ℕ} (D : Chain X n) (E : Chain Y m) (H : Fin n → Fin m) (p : X) : Set Y :=
  ⋃ (j : Fin n) (_ : p ∈ D.link j), E.link (H j)

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
  sorry

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
  sorry

end Zigzag

/-! ## §3. Private points; Step 1(b) of Theorem 10 -/

section Private

variable {X : Type*} [MetricSpace X]

/-- **Interior links have private points.** In a chain in Bing–Jones's sense properly covering a
connected set, each interior link contains a point of the set outside the closures of the other
links. -/
theorem exists_privatePoint_interior {P : Set X} (hP : IsConnected P) {n : ℕ} (D : Chain X n)
    (hD : IsBJChain D) (hDP : P ⊆ D.union) (hDp : ∀ i, (D.link i ∩ P).Nonempty) (i : Fin n)
    (hi : 0 < i.val) (hin : i.val + 1 < n) :
    ∃ p ∈ P ∩ D.link i, ∀ j, j ≠ i → p ∉ closure (D.link j) := by
  sorry

/-- **Private points.** A chain in Bing–Jones's sense properly covering a non-degenerate continuum
can be shrunk, link by link, so that each link contains a point of the continuum outside the
closures of the other links. (Compactness is not used; the hypothesis may be weakened.) -/
theorem exists_privatePoint_shrink {K : Set X} (hK : Fold.Q78.IsContinuum K) (hKn : K.Nontrivial)
    {n : ℕ} (D : Chain X n) (hD : IsBJChain D) (hKD : K ⊆ D.union)
    (hDK : ∀ i, (D.link i ∩ K).Nonempty) :
    ∃ D' : Chain X n, IsBJChain D' ∧ K ⊆ D'.union ∧ (∀ i, D'.link i ⊆ D.link i) ∧
      ∀ i, ∃ p ∈ K ∩ D'.link i, ∀ j, j ≠ i → p ∉ closure (D'.link j) := by
  sorry

end Private

/-- **Bing–Jones p. 182, Step 1(b)**, for any chain covering a continuous arc of continua: over a
short enough interval, a covering subchain from which neither end link can be dropped has every
link meeting every fibre. For the connected set `f ⁻¹' Icc a b` this is Bing–Jones's "irreducibly
covers" (p. 172). -/
theorem bj_step1b {X : Type*} [MetricSpace X] [CompactSpace X] {f : X → unitInterval}
    (hf : IsArcOfContinua f) (hfo : IsOpenMap f) {N : ℕ} (E : Chain X N) (hE : univ ⊆ E.union) :
    ∃ δ > 0, ∀ a b : unitInterval, a ≤ b → (b : ℝ) - a ≤ δ → ∀ u v : ℕ, u ≤ v →
      f ⁻¹' Icc a b ⊆ ⋃ (k : Fin N) (_ : u ≤ k.val ∧ k.val ≤ v), E.link k →
      ¬ f ⁻¹' Icc a b ⊆ ⋃ (k : Fin N) (_ : u + 1 ≤ k.val ∧ k.val ≤ v), E.link k →
      ¬ f ⁻¹' Icc a b ⊆ ⋃ (k : Fin N) (_ : u ≤ k.val ∧ k.val + 1 ≤ v), E.link k →
      ∀ x ∈ Icc a b, ∀ k : Fin N, u ≤ k.val → k.val ≤ v → (E.link k ∩ f ⁻¹' {x}).Nonempty := by
  sorry

/-! ## §4. Theorem 8 and its corollary -/

section Thm8

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Bing–Jones, Theorem 8** (p. 177), for continuous snake-like arcs of pseudo-arcs and chains of
at least three links. `D` is a chain in the library's sense; the conclusion is a chain in
Bing–Jones's sense. -/
theorem bj_theorem8 {f : X → unitInterval} (hf : IsContArcPA f) (hS : IsSnakeLike (univ : Set X))
    {n m : ℕ} (hn : 3 ≤ n) (D : Chain X n) (hD : univ ⊆ D.union)
    (hDf : ∀ t j, (D.link j ∩ f ⁻¹' {t}).Nonempty)
    (H : Fin m → Fin n) (hH : IsChainMap H) (hHs : Function.Surjective H) :
    ∃ E : Chain X m, IsBJChain E ∧ univ ⊆ E.union ∧ (∀ t i, (E.link i ∩ f ⁻¹' {t}).Nonempty) ∧
      ∀ i, E.link i ⊆ D.link (H i) := by
  sorry

/-- **Corollary to Theorem 8** (p. 178), with `D(r, s)` an abstract chain of `ℓ` indices mapped
onto `E` by `H₁`, and the arc `Q(i/k, (i+1)/k)` reparametrized as the whole space. The
irreducibility of `F` is not assumed. -/
theorem bj_theorem8_cor {f : X → unitInterval} (hf : IsContArcPA f)
    (hS : IsSnakeLike (univ : Set X)) {n ℓ : ℕ} (hn : 3 ≤ n) (E : Chain X n)
    (hE : univ ⊆ E.union) (hEf : ∀ t j, (E.link j ∩ f ⁻¹' {t}).Nonempty)
    (H₁ : Fin ℓ → Fin n) (hH₁ : IsChainMap H₁) (hH₁s : Function.Surjective H₁) :
    ∃ ε > 0, ∀ (N : ℕ) (F : Chain X N), IsEpsChain F ε → univ ⊆ F.union →
      ∃ R : Fin N → Fin ℓ, IsChainMap R ∧ Function.Surjective R ∧
        (∀ j, F.link j ⊆ E.link (H₁ (R j))) ∧
        ∀ (t : unitInterval) (v w : ℕ) (hw : w < N), v ≤ w →
          f ⁻¹' {t} ⊆ ⋃ (k : Fin N) (_ : v ≤ k.val ∧ k.val ≤ w), F.link k →
          ∀ d : Fin ℓ, ∃ k : ℕ, ∃ hk : k + 2 ≤ w, v ≤ k ∧
            ∀ (c : ℕ) (hc : c ≤ 2), R ⟨k + c, by omega⟩ = d := by
  sorry

end Thm8

/-! ## §5. Theorem 9 -/

section Thm9

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- **Bing–Jones's two simplifications** (pp. 179–180), as one lemma: a pair of chains with the
same number of links, matched by index, whose correspondence refines `H` with closures. -/
theorem bj9_base {P : Set X} {Q : Set Y} (hP : IsPseudoArc P) (hQ : IsPseudoArc Q) {n m : ℕ}
    (D : Chain X n) (E : Chain Y m) (hD : IsBJChain D) (hE : IsBJChain E)
    (hDP : P ⊆ D.union) (hDp : ∀ i, (D.link i ∩ P).Nonempty)
    (hEQ : Q ⊆ E.union) (hEq : ∀ j, (E.link j ∩ Q).Nonempty)
    (H : Fin n → Fin m) (hH : IsChainMap H)
    (hHo : ∀ j, ∃ i, H i = j ∧ ∃ p ∈ P ∩ D.link i, ∀ i', i' ≠ i → p ∉ closure (D.link i')) :
    ∃ (N : ℕ) (D' : Chain X N) (E' : Chain Y N), IsBJChain D' ∧ IsBJChain E' ∧
      P ⊆ D'.union ∧ (∀ j, (D'.link j ∩ P).Nonempty) ∧
      Q ⊆ E'.union ∧ (∀ j, (E'.link j ∩ Q).Nonempty) ∧
      (∀ j, ∃ p ∈ P ∩ D'.link j, ∀ j', j' ≠ j → p ∉ closure (D'.link j')) ∧
      (∀ j, ∃ q ∈ Q ∩ E'.link j, ∀ j', j' ≠ j → q ∉ closure (E'.link j')) ∧
      ∀ (i : Fin n) (j : Fin N) (p : X), p ∈ P → p ∈ D.link i → p ∈ D'.link j →
        closure (E'.link j) ⊆ E.link (H i) := by
  sorry

/-- **Bing–Jones, Theorem 9** (p. 179). -/
theorem bj_theorem9 {P : Set X} {Q : Set Y} (hP : IsPseudoArc P) (hQ : IsPseudoArc Q) {n m : ℕ}
    (D : Chain X n) (E : Chain Y m) (hD : IsBJChain D) (hE : IsBJChain E)
    (hDP : P ⊆ D.union) (hDp : ∀ i, (D.link i ∩ P).Nonempty)
    (hEQ : Q ⊆ E.union) (hEq : ∀ j, (E.link j ∩ Q).Nonempty)
    (H : Fin n → Fin m) (hH : IsChainMap H)
    (hHo : ∀ j, ∃ i, H i = j ∧ ∃ p ∈ P ∩ D.link i, ∀ i', i' ≠ i → p ∉ closure (D.link i')) :
    ∃ h : P ≃ₜ Q, ∀ (i : Fin n) (p : P), (p : X) ∈ D.link i → (h p : Y) ∈ E.link (H i) := by
  sorry

end Thm9

/-! ## §6. Two small items -/

/-- **Domokos–Prajs, Theorem 6.1, both directions**, given Bing–Jones Theorem 10 and a plane circle
of pseudo-arcs. -/
theorem dp22_theorem61_iff (h10 : BJThm10) (hEx : BJPlaneExample) {X : Type} [MetricSpace X]
    [CompactSpace X] : IsCircleOfPA X ↔ ∃ f : X → Circle, IsAtomicCircPAMap f := by
  sorry

/-- **Theorem 7's printed reduction fails for three links** (`LEDGER.md` BJ.19 (e)): the link `V`
playing `U₂` (`P·(d₂ − d₁) ⊂ U₂`) meets the link `U` playing `U_{n+1}` (`U ⊆ d₃`,
`P·(d₃ − d₂) ⊂ U`, `U` meeting `P`), though their places in `D′` are not adjacent. Links are
numbered from 1 in this comment: `d_k` is `D.link (k - 1)`. -/
theorem bj_theorem7_proof_n3 {X : Type*} [MetricSpace X] {P : Set X} (hP : IsConnected P)
    (D : Chain X 3) (hDP : P ⊆ D.union) (hDp : ∀ j, (D.link j ∩ P).Nonempty)
    {V U : Set X} (hU : IsOpen U) (hUd : U ⊆ D.link 2)
    (hV : P ∩ (D.link 1 \ D.link 0) ⊆ V) (hUP : P ∩ (D.link 2 \ D.link 1) ⊆ U)
    (hUne : (U ∩ P).Nonempty) : (V ∩ U).Nonempty := by
  sorry

/-! ## §8. Non-vacuity -/

/-- `zigzag_homeomorph` with a non-degenerate witness: `P = Q = [0, 1]`, `D i = E i`, `H i` the
identity. One choice: with `N i = 2 * 3 ^ i`, the links of `D i` are the intervals of radius
`3 / (4 * N i)` about `k / N i` (`k = 0, …, N i`), and `K i` sends `k` to the integer nearest
`k / 3`. (Halving the index does not work: a link of the finer chain can straddle two links.) -/
theorem nonvac_zigzag : ∃ (n : ℕ → ℕ) (D : ∀ i, Chain unitInterval (n i))
    (K : ∀ i, Fin (n (i + 1)) → Fin (n i)), (∀ i, univ ⊆ (D i).union) ∧
    (∀ i j, ((D i).link j).Nonempty) ∧ (∀ i, IsBJChain (D i)) ∧
    (∀ i, IsEpsChain (D i) (1 / 2 ^ i)) ∧ (∀ i, IsChainMap (K i)) ∧
    ∀ i j, (D (i + 1)).link j ⊆ (D i).link (K i j) := by
  sorry

end HPC.BJ59
