import HPC.Moore.M19CD2

/-!
# Moore 1919, Theorem E, steps 1–3: the nested double rulings `β₁, β₂, …` (batch 143, item A)

Moore's proof of Theorem E (p. 176) begins: "there exists, about each point `P` of `ABCDA` plus its
interior, a fundamental region of subscript greater than `n`" (Axiom 1 (1)); by Theorem D (region
form) there is a double ruling `β₁` each of whose subdivisions lies in one of these regions; each
subdivision of `β₁` is ruled in the same way, giving `β₂ ⊇ β₁`; "this process may be continued".

`nested_rulings` is this process, for any sequence of covers by regions: the `k`-th double ruling
has every subdivision inside a region of the `k`-th cover, contains every arc of the previous one,
and each of its subdivisions lies in a subdivision of the previous one. The continuation step is
`doubleRuling_refine` (batch 141) applied with Theorem D in region form (`m19_theoremD_regions`,
batch 142) on each subdivision. `nested_rulings_fund` is Moore's instance: the `k`-th cover is the
set of fundamental regions of subscript greater than `k`.
-/

namespace HPC.Moore

open Set Topology

variable {S : Type*} {σ : Space S}

/-- A stage of the process: a double ruling with its numbers of arcs. -/
abbrev Space.RulingStage (σ : Space S) {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}
    (q : σ.Quad J I A B C D sAB sBC sCD sDA) : Type _ :=
  (n : ℕ) × (m : ℕ) × σ.DoubleRuling q n m

section M19ESeq

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **The nested double rulings** (Theorem E, steps 1–3, \"This process may be continued\").
For any sequence of covers `𝒢 k` of the space by regions there is a sequence of double rulings
`R k` of `ABCDA` such that every subdivision of `R k` lies in a region of `𝒢 k`, every arc of
`R k` is an arc of `R (k + 1)`, and every subdivision of `R (k + 1)` lies in a subdivision of
`R k`. *Axioms used: 1–8.* -/
theorem nested_rulings (q : σ.Quad J I A B C D sAB sBC sCD sDA) (𝒢 : ℕ → Set (Set S))
    (h𝒢 : ∀ k, 𝒢 k ⊆ σ.region) (hcov : ∀ k (P : S), ∃ V ∈ 𝒢 k, P ∈ V) :
    ∃ R : ℕ → σ.RulingStage q,
      (∀ k, ∀ U ∈ (R k).2.2.cells, ∃ V ∈ 𝒢 k, U ⊆ V) ∧
      (∀ k i, ∃ i', (R (k + 1)).2.2.arcX i' = (R k).2.2.arcX i) ∧
      (∀ k j, ∃ j', (R (k + 1)).2.2.arcY j' = (R k).2.2.arcY j) ∧
      (∀ k, ∀ U ∈ (R (k + 1)).2.2.cells, ∃ V ∈ (R k).2.2.cells, U ⊆ V) := by
  classical
  have hGood : ∀ k, ∀ U V : Set S, U ⊆ V → (∃ W ∈ 𝒢 k, V ⊆ W) → ∃ W ∈ 𝒢 k, U ⊆ W :=
    fun k U V hUV ⟨W, hW, hVW⟩ => ⟨W, hW, hUV.trans hVW⟩
  have init : ∃ s : σ.RulingStage q, ∀ U ∈ s.2.2.cells, ∃ V ∈ 𝒢 0, U ⊆ V := by
    obtain ⟨n, m, R, hR⟩ := m19_theoremD_regions h1 h2 h3 h4 h5 h6 h7 h8 q (𝒢 0) (h𝒢 0)
      (fun P _ => hcov 0 P)
    exact ⟨⟨n, m, R⟩, hR⟩
  have step : ∀ (k : ℕ) (s : σ.RulingStage q), ∃ s' : σ.RulingStage q,
      (∀ U ∈ s'.2.2.cells, ∃ V ∈ 𝒢 (k + 1), U ⊆ V) ∧
      (∀ i, ∃ i', s'.2.2.arcX i' = s.2.2.arcX i) ∧
      (∀ j, ∃ j', s'.2.2.arcY j' = s.2.2.arcY j) ∧
      (∀ U ∈ s'.2.2.cells, ∃ V ∈ s.2.2.cells, U ⊆ V) := by
    rintro k ⟨n, m, R⟩
    obtain ⟨n', m', R', hX, hY, hU⟩ := doubleRuling_refine h1 h2 h3 h4 h5 h6 h7 h8
      (hGood (k + 1)) q R (fun q' _ => m19_theoremD_regions h1 h2 h3 h4 h5 h6 h7 h8 q'
        (𝒢 (k + 1)) (h𝒢 _) (fun P _ => hcov (k + 1) P))
    exact ⟨⟨n', m', R'⟩, fun U hU' => (hU U hU').1, hX, hY, fun U hU' => (hU U hU').2⟩
  obtain ⟨s₀, hs₀⟩ := init
  choose F hF using step
  let R : ℕ → σ.RulingStage q := fun k => Nat.rec s₀ (fun k s => F k s) k
  have hR0 : R 0 = s₀ := rfl
  have hRs : ∀ k, R (k + 1) = F k (R k) := fun k => rfl
  refine ⟨R, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · cases k with
    | zero => rw [hR0]; exact hs₀
    | succ k => rw [hRs]; exact (hF k (R k)).1
  · rw [hRs]; exact (hF k (R k)).2.1
  · rw [hRs]; exact (hF k (R k)).2.2.1
  · rw [hRs]; exact (hF k (R k)).2.2.2

/-- **Moore's instance** (Theorem E, first sentence of the proof): the `k`-th double ruling has
each subdivision inside a fundamental region (of the fixed sequence `K` of Axiom 1) of subscript
greater than `k`. *Axioms used: 1–8.* -/
theorem nested_rulings_fund (q : σ.Quad J I A B C D sAB sBC sCD sDA) {K : ℕ → Set S}
    (hK : σ.IsFund K) :
    ∃ R : ℕ → σ.RulingStage q,
      (∀ k, ∀ U ∈ (R k).2.2.cells, ∃ l > k, U ⊆ K l) ∧
      (∀ k i, ∃ i', (R (k + 1)).2.2.arcX i' = (R k).2.2.arcX i) ∧
      (∀ k j, ∃ j', (R (k + 1)).2.2.arcY j' = (R k).2.2.arcY j) ∧
      (∀ k, ∀ U ∈ (R (k + 1)).2.2.cells, ∃ V ∈ (R k).2.2.cells, U ⊆ V) := by
  obtain ⟨R, hR, hX, hY, hU⟩ := nested_rulings h1 h2 h3 h4 h5 h6 h7 h8 q
    (fun k => K '' Ioi k) (fun k => by rintro _ ⟨l, -, rfl⟩; exact hK.1 l)
    (fun k P => by obtain ⟨l, hl, hP⟩ := hK.2.1 k P; exact ⟨K l, ⟨l, hl, rfl⟩, hP⟩)
  refine ⟨R, fun k U hU' => ?_, hX, hY, hU⟩
  obtain ⟨_, ⟨l, hl, rfl⟩, hUl⟩ := hR k U hU'
  exact ⟨l, hl, hUl⟩

end M19ESeq

end HPC.Moore
