import HPC.PseudoArc.Statements79
import HPC.PseudoArc.T13Chains

/-!
# Batch 115: gluing the three pieces of Bing's follower `E_1 + E_2 + E_3`

Auxiliary file for `HPC/PseudoArc/Thm14.lean` (COMMISSION-batch115.md, item 3). Bing's proof of
Theorem 14 (p. 741) makes the level side follow a tracked pattern by applying Theorem 5 three
times, on the stretches `P → R`, `R → A`, `A → Q` of a deep level `D` (here with junction indices
`r` and `α`), and joins the three chains: link `n` of the result is `E_1(n) ∪ E_2(ρ' − n) ∪ E_3(n)`
for `n ≤ ρ'` and `E_3(n)` beyond. Bing does not check that this is a chain from `P` to `Q`; this
file does, in terms of chains only (`Chain.threePiece`).

Cross-intersections: two links of the fine level `F` from different stretches meet only inside a
junction link of `D` (the stretches `P → R` and `A → Q` are at least two links of `D` apart), and
Theorem 5's end clauses put every link of `F` meeting a junction link into the end link of each
piece at that junction — index `ρ'` of the result for the junction `r`, index `0` for `α`.
-/

namespace HPC

open Set

variable {X : Type*} [MetricSpace X]

namespace Chain

/-- A point of a link of a consolidation on `S` lies in a link of `F` with index in `S` that is
contained in that link. -/
theorem IsConsolidationOn.exists_mem {n m : ℕ} {E : Chain X m} {F : Chain X n} {S : Set (Fin n)}
    (h : E.IsConsolidationOn F S) {e : Fin m} {z : X} (hz : z ∈ E.link e) :
    ∃ t ∈ S, z ∈ F.link t ∧ F.link t ⊆ E.link e := by
  obtain ⟨T, hTS, hT⟩ := h.2 e
  rw [hT] at hz
  simp only [mem_iUnion, exists_prop] at hz
  obtain ⟨t, htT, hzt⟩ := hz
  exact ⟨t, hTS htT, hzt, by rw [hT]; exact subset_biUnion_of_mem (u := fun t => F.link t) htT⟩

/-- **The three-piece follower, glued.** `C` is the coarse chain (from `P` to `Q`, `R` in its link
`ρ ≥ 1` and not in its first link), `x` a pattern on `N'` links with `x 0 = 0`, `x ρ' = ρ`; `D`
a deep level with junctions `1 ≤ r`, `r + 2 ≤ α < n - 1`, `R ∈ d_r`, `W` in `D(0..r)`; `F` a
finer level refining `D`. `E_1`, `E_2`, `E_3` are the outputs of Theorem 5 on the stretches
`D(0..r)`, `D(r..α)`, `D(α..n-1)`, following `x|[0, ρ']`, its reverse, and `x`. Then the glued
chain is a chain from `P` to `Q`, a consolidation of `F`, follows `x` in `C`, and its initial
subchain up to `ρ'` is from `P` to `R` and covers `W`. -/
theorem threePiece {N N' n nF : ℕ} {P Q R : X} {W : Set X}
    (C : Chain X N) (hC : C.IsFrom P Q) (ρ : Fin N) (hρ : 0 < ρ.val)
    (hRC0 : R ∉ C.link ⟨0, hC.1⟩)
    (x : Fin N' → Fin N) (ρ' : Fin N') (hx0 : ∀ h : 0 < N', x ⟨0, h⟩ = ⟨0, hC.1⟩)
    (hxρ : x ρ' = ρ)
    (D : Chain X n) (hD : D.IsFrom P Q) (r α : Fin n) (hr : 0 < r.val)
    (hrα : r.val + 2 ≤ α.val) (hαn : α.val + 1 < n) (hRD : R ∈ D.link r)
    (hWD : ∀ w ∈ W, ∃ s : Fin n, s ≤ r ∧ w ∈ D.link s)
    (F : Chain X nF) (hF : F.IsFrom P Q) (hFD : F.Refines D) (hRF : R ∈ F.union)
    (hWF : W ⊆ F.union)
    (E₁ E₂ : Chain X (ρ'.val + 1)) (E₃ : Chain X N')
    (f₁ : ∀ e : Fin (ρ'.val + 1), E₁.link e ⊆ C.link (x ⟨e.val, by omega⟩))
    (f₂ : ∀ e : Fin (ρ'.val + 1), E₂.link e ⊆ C.link (x ⟨ρ'.val - e.val, by omega⟩))
    (f₃ : E₃.FollowsPattern x C)
    (c₁ : E₁.IsConsolidationOn F
      {t | ∃ s : Fin n, ⟨0, hD.1⟩ ≤ s ∧ s ≤ r ∧ F.link t ⊆ D.link s})
    (c₂ : E₂.IsConsolidationOn F {t | ∃ s : Fin n, r ≤ s ∧ s ≤ α ∧ F.link t ⊆ D.link s})
    (c₃ : E₃.IsConsolidationOn F
      {t | ∃ s : Fin n, α ≤ s ∧ s ≤ ⟨n - 1, by omega⟩ ∧ F.link t ⊆ D.link s})
    (d₁ : ∀ e : Fin (ρ'.val + 1), 0 < e.val → e.val < ρ'.val + 1 - 1 →
      Disjoint (E₁.link e) (D.link ⟨0, hD.1⟩ ∪ D.link r))
    (d₂ : ∀ e : Fin (ρ'.val + 1), 0 < e.val → e.val < ρ'.val + 1 - 1 →
      Disjoint (E₂.link e) (D.link r ∪ D.link α))
    (d₃ : ∀ e : Fin N', 0 < e.val → e.val < N' - 1 →
      Disjoint (E₃.link e) (D.link α ∪ D.link ⟨n - 1, by omega⟩))
    (e₁u : ∀ t, (∃ s : Fin n, ⟨0, hD.1⟩ ≤ s ∧ s ≤ r ∧ F.link t ⊆ D.link s) →
      (F.link t ∩ D.link ⟨0, hD.1⟩).Nonempty → F.link t ⊆ E₁.link ⟨0, by omega⟩)
    (e₁v : ∀ t, (∃ s : Fin n, ⟨0, hD.1⟩ ≤ s ∧ s ≤ r ∧ F.link t ⊆ D.link s) →
      (F.link t ∩ D.link r).Nonempty → F.link t ⊆ E₁.link ⟨ρ'.val + 1 - 1, by omega⟩)
    (e₂u : ∀ t, (∃ s : Fin n, r ≤ s ∧ s ≤ α ∧ F.link t ⊆ D.link s) →
      (F.link t ∩ D.link r).Nonempty → F.link t ⊆ E₂.link ⟨0, by omega⟩)
    (e₂v : ∀ t, (∃ s : Fin n, r ≤ s ∧ s ≤ α ∧ F.link t ⊆ D.link s) →
      (F.link t ∩ D.link α).Nonempty → F.link t ⊆ E₂.link ⟨ρ'.val + 1 - 1, by omega⟩)
    (e₃u : ∀ t, (∃ s : Fin n, α ≤ s ∧ s ≤ ⟨n - 1, by omega⟩ ∧ F.link t ⊆ D.link s) →
      (F.link t ∩ D.link α).Nonempty → F.link t ⊆ E₃.link ⟨0, ρ'.pos⟩)
    (e₃v : ∀ t, (∃ s : Fin n, α ≤ s ∧ s ≤ ⟨n - 1, by omega⟩ ∧ F.link t ⊆ D.link s) →
      (F.link t ∩ D.link ⟨n - 1, by omega⟩).Nonempty →
        F.link t ⊆ E₃.link ⟨N' - 1, by have := ρ'.pos; omega⟩) :
    ∃ E : Chain X N', E.IsFrom P Q ∧ E.IsConsolidationOf F ∧ E.FollowsPattern x C ∧
      ∃ h0 : (⟨0, ρ'.pos⟩ : Fin N') ≤ ρ', (E.sub ⟨0, ρ'.pos⟩ ρ' h0).IsFrom P R ∧
        W ⊆ E.span ⟨0, ρ'.pos⟩ ρ' := by
  classical
  have hN' : 0 < N' := ρ'.pos
  have hn : 0 < n := hD.1
  have hPD0 : P ∈ D.link ⟨0, hD.1⟩ := hD.2.1
  have hQDl : Q ∈ D.link ⟨n - 1, by omega⟩ := hD.2.2.1
  have hPDu := hD.2.2.2.1
  have hQDu := hD.2.2.2.2
  have hPCu := hC.2.2.2.1
  have hQCu := hC.2.2.2.2
  have hρN := ρ.isLt
  -- the D-adjacency
  have Dadj : ∀ {z : X} {s s' : Fin n}, z ∈ D.link s → z ∈ D.link s' →
      s.val ≤ s'.val + 1 ∧ s'.val ≤ s.val + 1 :=
    fun h1 h2 => (D.adjacent_iff _ _).mp ⟨_, h1, h2⟩
  -- where the points of the pieces lie in `D`
  have Loc1 : ∀ {e z}, z ∈ E₁.link e → ∃ s : Fin n, s ≤ r ∧ z ∈ D.link s := by
    intro e z hz
    obtain ⟨t, ⟨s, -, hs, hts⟩, hzt, -⟩ := c₁.exists_mem hz
    exact ⟨s, hs, hts hzt⟩
  have Loc2 : ∀ {e z}, z ∈ E₂.link e → ∃ s : Fin n, r ≤ s ∧ s ≤ α ∧ z ∈ D.link s := by
    intro e z hz
    obtain ⟨t, ⟨s, hs1, hs2, hts⟩, hzt, -⟩ := c₂.exists_mem hz
    exact ⟨s, hs1, hs2, hts hzt⟩
  have Loc3 : ∀ {e z}, z ∈ E₃.link e → ∃ s : Fin n, α ≤ s ∧ z ∈ D.link s := by
    intro e z hz
    obtain ⟨t, ⟨s, hs1, -, hts⟩, hzt, -⟩ := c₃.exists_mem hz
    exact ⟨s, hs1, hts hzt⟩
  -- the junction clauses
  have J1 : ∀ {e z}, z ∈ E₁.link e → z ∈ D.link r →
      z ∈ E₁.link ⟨ρ'.val + 1 - 1, by omega⟩ := by
    intro e z hz hzr
    obtain ⟨t, ht, hzt, -⟩ := c₁.exists_mem hz
    exact e₁v t ht ⟨z, hzt, hzr⟩ hzt
  have J2 : ∀ {e z}, z ∈ E₂.link e → z ∈ D.link r → z ∈ E₂.link ⟨0, by omega⟩ := by
    intro e z hz hzr
    obtain ⟨t, ht, hzt, -⟩ := c₂.exists_mem hz
    exact e₂u t ht ⟨z, hzt, hzr⟩ hzt
  have J3 : ∀ {e z}, z ∈ E₂.link e → z ∈ D.link α →
      z ∈ E₂.link ⟨ρ'.val + 1 - 1, by omega⟩ := by
    intro e z hz hzr
    obtain ⟨t, ht, hzt, -⟩ := c₂.exists_mem hz
    exact e₂v t ht ⟨z, hzt, hzr⟩ hzt
  have J4 : ∀ {e z}, z ∈ E₃.link e → z ∈ D.link α → z ∈ E₃.link ⟨0, hN'⟩ := by
    intro e z hz hzr
    obtain ⟨t, ht, hzt, -⟩ := c₃.exists_mem hz
    exact e₃u t ht ⟨z, hzt, hzr⟩ hzt
  -- cross intersections
  have X12 : ∀ {e e' z}, z ∈ E₁.link e → z ∈ E₂.link e' → z ∈ D.link r := by
    intro e e' z h1 h2
    obtain ⟨s, hs, hzs⟩ := Loc1 h1
    obtain ⟨s', hs1, -, hzs'⟩ := Loc2 h2
    have := Dadj hzs hzs'
    have hs' : s.val ≤ r.val := hs
    have hs1' : r.val ≤ s'.val := hs1
    rcases Nat.lt_or_ge s.val r.val with hlt | hge
    · rwa [show r = s' from Fin.ext (by omega)]
    · rwa [show r = s from Fin.ext (by omega)]
  have X23 : ∀ {e e' z}, z ∈ E₂.link e → z ∈ E₃.link e' → z ∈ D.link α := by
    intro e e' z h1 h2
    obtain ⟨s, -, hs, hzs⟩ := Loc2 h1
    obtain ⟨s', hs1, hzs'⟩ := Loc3 h2
    have := Dadj hzs hzs'
    have hs' : s.val ≤ α.val := hs
    have hs1' : α.val ≤ s'.val := hs1
    rcases Nat.lt_or_ge s.val α.val with hlt | hge
    · rwa [show α = s' from Fin.ext (by omega)]
    · rwa [show α = s from Fin.ext (by omega)]
  have X13 : ∀ {e e' z}, z ∈ E₁.link e → z ∈ E₃.link e' → False := by
    intro e e' z h1 h2
    obtain ⟨s, hs, hzs⟩ := Loc1 h1
    obtain ⟨s', hs1, hzs'⟩ := Loc3 h2
    have := Dadj hzs hzs'
    have hs' : s.val ≤ r.val := hs
    have hs1' : α.val ≤ s'.val := hs1
    omega
  -- adjacency in the pieces, on values
  have A1 : ∀ {e e' : Fin (ρ'.val + 1)} {z}, z ∈ E₁.link e → z ∈ E₁.link e' →
      e.val ≤ e'.val + 1 ∧ e'.val ≤ e.val + 1 :=
    fun h1 h2 => (E₁.adjacent_iff _ _).mp ⟨_, h1, h2⟩
  have A2 : ∀ {e e' : Fin (ρ'.val + 1)} {z}, z ∈ E₂.link e → z ∈ E₂.link e' →
      e.val ≤ e'.val + 1 ∧ e'.val ≤ e.val + 1 :=
    fun h1 h2 => (E₂.adjacent_iff _ _).mp ⟨_, h1, h2⟩
  have A3 : ∀ {e e' : Fin N'} {z}, z ∈ E₃.link e → z ∈ E₃.link e' →
      e.val ≤ e'.val + 1 ∧ e'.val ≤ e.val + 1 :=
    fun h1 h2 => (E₃.adjacent_iff _ _).mp ⟨_, h1, h2⟩
  -- the glued links
  let L : Fin N' → Set X := fun m => E₃.link m ∪
    (if m.val ≤ ρ'.val then E₁.link ⟨min m.val ρ'.val, by omega⟩ ∪
      E₂.link ⟨ρ'.val - m.val, by omega⟩ else ∅)
  have hmem : ∀ m z, z ∈ L m ↔ z ∈ E₃.link m ∨ (m.val ≤ ρ'.val ∧
      (z ∈ E₁.link ⟨min m.val ρ'.val, by omega⟩ ∨ z ∈ E₂.link ⟨ρ'.val - m.val, by omega⟩)) := by
    intro m z
    show z ∈ E₃.link m ∪ _ ↔ _
    by_cases h : m.val ≤ ρ'.val
    · rw [if_pos h]
      simp only [mem_union, h, true_and]
    · rw [if_neg h]
      simp only [mem_union, mem_empty_iff_false, h, false_and, or_false]
  have hL1 : ∀ (e : Fin (ρ'.val + 1)) z, z ∈ E₁.link e → z ∈ L ⟨e.val, by omega⟩ := by
    intro e z hz
    refine (hmem _ z).mpr (Or.inr ⟨by have := e.isLt; simp only; omega, Or.inl ?_⟩)
    have : (⟨min e.val ρ'.val, by omega⟩ : Fin (ρ'.val + 1)) = e :=
      Fin.ext (by have := e.isLt; simp only; omega)
    rwa [this]
  have hL2 : ∀ (e : Fin (ρ'.val + 1)) z, z ∈ E₂.link e →
      z ∈ L ⟨ρ'.val - e.val, by omega⟩ := by
    intro e z hz
    refine (hmem _ z).mpr (Or.inr ⟨by simp only; omega, Or.inr ?_⟩)
    have : (⟨ρ'.val - (ρ'.val - e.val), by omega⟩ : Fin (ρ'.val + 1)) = e :=
      Fin.ext (by have := e.isLt; simp only; omega)
    simp only at this ⊢
    rwa [this]
  have hL3 : ∀ (e : Fin N') z, z ∈ E₃.link e → z ∈ L e :=
    fun e z hz => (hmem _ z).mpr (Or.inl hz)
  let E : Chain X N' :=
    { link := L
      isOpen := fun m => by
        refine (E₃.isOpen m).union ?_
        split_ifs
        · exact (E₁.isOpen _).union (E₂.isOpen _)
        · exact isOpen_empty
      adjacent := by
        intro m m'
        constructor
        · rintro ⟨z, hz, hz'⟩
          have hm := m.isLt
          have hm' := m'.isLt
          rcases (hmem m z).mp hz with h3 | ⟨hle, h1 | h2⟩ <;>
            rcases (hmem m' z).mp hz' with h3' | ⟨hle', h1' | h2'⟩
          · have := A3 h3 h3'; omega
          · exact (X13 h1' h3).elim
          · have := A3 h3 (J4 h3 (X23 h2' h3)); have := A2 h2' (J3 h2' (X23 h2' h3))
            simp only at *; omega
          · exact (X13 h1 h3').elim
          · have := A1 h1 h1'; simp only at *; omega
          · have := A1 h1 (J1 h1 (X12 h1 h2')); have := A2 h2' (J2 h2' (X12 h1 h2'))
            simp only at *; omega
          · have := A3 h3' (J4 h3' (X23 h2 h3')); have := A2 h2 (J3 h2 (X23 h2 h3'))
            simp only at *; omega
          · have := A1 h1' (J1 h1' (X12 h1' h2)); have := A2 h2 (J2 h2 (X12 h1' h2))
            simp only at *; omega
          · have := A2 h2 h2'; simp only at *; omega
        · intro h
          obtain ⟨z, hz, hz'⟩ := (E₃.adjacent m m').mpr h
          exact ⟨z, hL3 _ _ hz, hL3 _ _ hz'⟩ }
  have hEmem : ∀ m z, z ∈ E.link m ↔ z ∈ L m := fun _ _ => Iff.rfl
  have hLeq : ∀ m m' : Fin N', m.val = m'.val → ∀ z, z ∈ L m → z ∈ L m' := by
    intro m m' h z hz
    rwa [show m = m' from Fin.ext h] at hz
  have hf1 : ∀ (e : Fin (ρ'.val + 1)) (m : Fin N'), e.val = m.val →
      E₁.link e ⊆ C.link (x m) := by
    intro e m h
    obtain ⟨mv, hmv⟩ := m
    simp only at h
    subst h
    exact f₁ e
  have hf2 : ∀ (e : Fin (ρ'.val + 1)) (m : Fin N'), ρ'.val - e.val = m.val →
      E₂.link e ⊆ C.link (x m) := by
    intro e m h
    obtain ⟨mv, hmv⟩ := m
    simp only at h
    subst h
    exact f₂ e
  have hxm0 : ∀ m : Fin N', m.val = 0 → x m = ⟨0, hC.1⟩ := by
    intro m h
    rw [show m = ⟨0, hN'⟩ from Fin.ext h, hx0 hN']
  -- `P` and `Q`
  have hPF : P ∈ L ⟨0, hN'⟩ := by
    obtain ⟨s, hs⟩ := hFD ⟨0, hF.1⟩
    have hs0 : s = ⟨0, hD.1⟩ := hPDu s (hs hF.2.1)
    have hmem1 := e₁u ⟨0, hF.1⟩ ⟨⟨0, hD.1⟩, le_rfl, Fin.le_def.mpr (Nat.zero_le _),
      by rw [← hs0]; exact hs⟩ ⟨P, hF.2.1, hPD0⟩ hF.2.1
    exact hL1 ⟨0, by omega⟩ P hmem1
  have hQF : Q ∈ L ⟨N' - 1, by omega⟩ := by
    obtain ⟨s, hs⟩ := hFD ⟨nF - 1, by have := hF.1; omega⟩
    have hsl : s = ⟨n - 1, by omega⟩ := hQDu s (hs hF.2.2.1)
    have := e₃v ⟨nF - 1, by have := hF.1; omega⟩ ⟨⟨n - 1, by omega⟩,
      Fin.le_def.mpr (by simp only; omega), le_rfl, by rw [← hsl]; exact hs⟩ ⟨Q, hF.2.2.1, hQDl⟩
      hF.2.2.1
    exact hL3 _ _ this
  have hPonly : ∀ m : Fin N', P ∈ L m → m.val = 0 := by
    intro m hm
    rcases (hmem m P).mp hm with h3 | ⟨hle, h1 | h2⟩
    · obtain ⟨s, hs, hPs⟩ := Loc3 h3
      have := congrArg Fin.val (hPDu s hPs)
      have : α.val ≤ s.val := hs
      simp only at *
      omega
    · by_contra hne
      rcases Nat.lt_or_ge m.val ρ'.val with hlt | hge
      · exact Set.disjoint_left.mp (d₁ _ (by simp only; omega) (by simp only; omega)) h1
          (Or.inl hPD0)
      · have hmρ : m = ρ' := Fin.ext (by omega)
        have := hf1 _ m (by simp only; omega) h1
        rw [hmρ, hxρ] at this
        have := congrArg Fin.val (hPCu ρ this)
        simp only at this
        omega
    · obtain ⟨s, hs, -, hPs⟩ := Loc2 h2
      have := congrArg Fin.val (hPDu s hPs)
      have : r.val ≤ s.val := hs
      simp only at *
      omega
  have hQonly : ∀ m : Fin N', Q ∈ L m → m.val = N' - 1 := by
    intro m hm
    rcases (hmem m Q).mp hm with h3 | ⟨hle, h1 | h2⟩
    · by_contra hne
      rcases Nat.eq_zero_or_pos m.val with h0 | hpos
      · have := f₃ m h3
        rw [hxm0 m h0] at this
        have := congrArg Fin.val (hQCu _ this)
        simp only at this
        omega
      · exact Set.disjoint_left.mp (d₃ m hpos (by omega)) h3 (Or.inr hQDl)
    · obtain ⟨s, hs, hQs⟩ := Loc1 h1
      have := congrArg Fin.val (hQDu s hQs)
      have : s.val ≤ r.val := hs
      simp only at *
      omega
    · obtain ⟨s, -, hs, hQs⟩ := Loc2 h2
      have := congrArg Fin.val (hQDu s hQs)
      have : s.val ≤ α.val := hs
      simp only at *
      omega
  -- `R`
  have hRρ : R ∈ L ρ' := by
    obtain ⟨t, ht⟩ := mem_iUnion.mp hRF
    obtain ⟨s, hs⟩ := hFD t
    have hadj := Dadj (hs ht) hRD
    by_cases h1 : s ≤ r
    · have := e₁v t ⟨s, Fin.le_def.mpr (Nat.zero_le _), h1, hs⟩ ⟨R, ht, hRD⟩ ht
      exact hLeq _ ρ' (by simp only; omega) R (hL1 _ R this)
    · have h2 : s ≤ α := Fin.le_def.mpr (by
        have := Fin.not_le.mp h1; rw [Fin.lt_def] at this; omega)
      have := e₂u t ⟨s, le_of_lt (not_le.mp h1), h2, hs⟩ ⟨R, ht, hRD⟩ ht
      exact hLeq _ ρ' (by simp only; omega) R (hL2 _ R this)
  have hRonly : ∀ m : Fin N', m.val ≤ ρ'.val → R ∈ L m → m.val = ρ'.val := by
    intro m hmle hm
    have hRC0' : ∀ m' : Fin N', m'.val = 0 → R ∉ C.link (x m') := by
      intro m' h0 hR
      rw [hxm0 m' h0] at hR
      exact hRC0 hR
    rcases (hmem m R).mp hm with h3 | ⟨hle, h1 | h2⟩
    · obtain ⟨s, hs, hRs⟩ := Loc3 h3
      have := Dadj hRs hRD
      have : α.val ≤ s.val := hs
      omega
    · by_contra hne
      rcases Nat.eq_zero_or_pos m.val with h0 | hpos
      · exact hRC0' m h0 (hf1 _ m (by simp only; omega) h1)
      · exact Set.disjoint_left.mp (d₁ _ (by simp only; omega) (by simp only; omega)) h1
          (Or.inr hRD)
    · by_contra hne
      rcases Nat.eq_zero_or_pos m.val with h0 | hpos
      · exact hRC0' m h0 (hf2 _ m (by simp only; omega) h2)
      · exact Set.disjoint_left.mp (d₂ _ (by simp only; omega) (by simp only; omega)) h2
          (Or.inl hRD)
  refine ⟨E, ⟨hN', hPF, hQF, fun m hm => Fin.ext (hPonly m hm),
    fun m hm => Fin.ext (hQonly m hm)⟩, ⟨fun t => ?_, fun m => ⟨{t | F.link t ⊆ L m}, ?_⟩⟩,
    fun m z hz => ?_, Fin.le_def.mpr (Nat.zero_le _), ⟨by omega, ?_, ?_, ?_, ?_⟩, fun w hw => ?_⟩
  · -- `F` refines `E`
    obtain ⟨s, hs⟩ := hFD t
    by_cases h1 : s ≤ r
    · obtain ⟨e, he⟩ := c₁.1 t ⟨s, Fin.le_def.mpr (Nat.zero_le _), h1, hs⟩
      exact ⟨⟨e.val, by omega⟩, fun z hz => hL1 e z (he hz)⟩
    · by_cases h2 : s ≤ α
      · obtain ⟨e, he⟩ := c₂.1 t ⟨s, le_of_lt (not_le.mp h1), h2, hs⟩
        exact ⟨_, fun z hz => hL2 e z (he hz)⟩
      · obtain ⟨e, he⟩ := c₃.1 t ⟨s, le_of_lt (not_le.mp h2),
          Fin.le_def.mpr (by have := s.isLt; simp only; omega), hs⟩
        exact ⟨e, fun z hz => hL3 e z (he hz)⟩
  · -- each link of `E` is a union of links of `F`
    ext z
    simp only [mem_iUnion, mem_setOf_eq, exists_prop]
    constructor
    · intro hz
      rcases (hmem m z).mp hz with h3 | ⟨hle, h1 | h2⟩
      · obtain ⟨t, -, hzt, hte⟩ := c₃.exists_mem h3
        exact ⟨t, fun y hy => hL3 _ _ (hte hy), hzt⟩
      · obtain ⟨t, -, hzt, hte⟩ := c₁.exists_mem h1
        exact ⟨t, fun y hy => (hmem m y).mpr (Or.inr ⟨hle, Or.inl (hte hy)⟩), hzt⟩
      · obtain ⟨t, -, hzt, hte⟩ := c₂.exists_mem h2
        exact ⟨t, fun y hy => (hmem m y).mpr (Or.inr ⟨hle, Or.inr (hte hy)⟩), hzt⟩
    · rintro ⟨t, hts, hzt⟩
      exact hts hzt
  · -- the pattern
    rcases (hmem m z).mp hz with h3 | ⟨hle, h1 | h2⟩
    · exact f₃ m h3
    · exact hf1 _ m (by simp only; omega) h1
    · exact hf2 _ m (by simp only; omega) h2
  · show P ∈ L ⟨0 + 0, _⟩
    exact hLeq _ _ (by simp) P hPF
  · show R ∈ L ⟨0 + (ρ'.val - 0 + 1 - 1), _⟩
    exact hLeq ρ' _ (by simp only; omega) R hRρ
  · intro i hi
    have hi' : P ∈ L ⟨0 + i.val, by omega⟩ := hi
    have := hPonly _ hi'
    exact Fin.ext (by simp only at this ⊢; omega)
  · intro i hi
    have hi' : R ∈ L ⟨0 + i.val, by omega⟩ := hi
    have := hRonly _ (by simp only; omega) hi'
    exact Fin.ext (by simp only at this ⊢; omega)
  · -- `W` in the span up to `ρ'`
    obtain ⟨s₀, hs₀, hws₀⟩ := hWD w hw
    obtain ⟨t, ht⟩ := mem_iUnion.mp (hWF hw)
    obtain ⟨s, hs⟩ := hFD t
    have hadj := Dadj (hs ht) hws₀
    have : s₀.val ≤ r.val := hs₀
    refine Chain.mem_span.mpr ?_
    by_cases h1 : s ≤ r
    · obtain ⟨e, he⟩ := c₁.1 t ⟨s, Fin.le_def.mpr (Nat.zero_le _), h1, hs⟩
      exact ⟨⟨e.val, by omega⟩, Fin.le_def.mpr (Nat.zero_le _),
        Fin.le_def.mpr (by have := e.isLt; simp only; omega), hL1 e w (he ht)⟩
    · have h2 : s ≤ α := Fin.le_def.mpr (by
        have := Fin.not_le.mp h1; rw [Fin.lt_def] at this; omega)
      obtain ⟨e, he⟩ := c₂.1 t ⟨s, le_of_lt (not_le.mp h1), h2, hs⟩
      exact ⟨⟨ρ'.val - e.val, by omega⟩, Fin.le_def.mpr (Nat.zero_le _),
        Fin.le_def.mpr (by simp only; omega), hL2 e w (he ht)⟩

end Chain

end HPC
