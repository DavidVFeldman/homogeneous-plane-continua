import Mathlib.Tactic

/-!
# Batch 122: Bing's induction for Theorem 3 in the faithful model with a meeting table

COMMISSION-batch122.md, Q2/Q3. The model: fine links `t < n` (Bing's `D`), coarse levels `j < K`
(Bing's `E`), `ρ t ≤ σ t` the least and greatest coarse link containing the fine link `t`, and a
meeting table `T t j` ("the fine link `t` meets the coarse link `j`"). `BHyp` collects what every
chain crooked (1948 sense) in a chain satisfies (`HPC.Fold.Recon122.bHyp_of_crooked`): the faithful
inequalities, forced meetings, the possible meetings, and crookedness read with `T`.

`BConcl` is Bing's conclusion in the block reading: a time function `β` with `β i = 0`, moving by at
most one between adjacent links, every fibre inside two adjacent coarse links, and Bing's end
clause read with `T` ("or" reading).

The main theorem `bing_main` (`Recon122General.lean`) proves `BHyp → BConcl` by Bing's induction
on `K`, with the repairs found in batch 122: the level groups of the special case are read as
`Cbot`, at `K = 5` the special case is done by an explicit grouping, and the branch "`d_i` between
`d_h` and `d_k`" applies the induction hypothesis to `D(h, k)` inside `E(2, r − 1)`.
-/

namespace HPC.Fold.Recon122

/-- **The hypotheses of the model**: `n` fine links, `K` coarse links, the coarse interval
`[ρ t, σ t]` of each fine link (faithful model), and a meeting table `T` containing the forced
meetings, contained in the possible ones, for which the fine chain is crooked (1948). -/
structure BHyp (n K : ℕ) (ρ σ : ℕ → ℕ) (T : ℕ → ℕ → Prop) : Prop where
  le : ∀ t, t < n → ρ t ≤ σ t
  wid : ∀ t, t < n → σ t ≤ ρ t + 1
  lt : ∀ t, t < n → σ t < K
  adj : ∀ t, t + 1 < n → σ t ≤ ρ (t + 1) + 1 ∧ σ (t + 1) ≤ ρ t + 1
  cont : ∀ t, t < n → ∀ j, ρ t ≤ j → j ≤ σ t → T t j
  fwd : ∀ t, t + 1 < n → ∀ j, ρ (t + 1) ≤ j → j ≤ σ (t + 1) → T t j
  bwd : ∀ t, t + 1 < n → ∀ j, ρ t ≤ j → j ≤ σ t → T (t + 1) j
  poss : ∀ t, t < n → ∀ j, T t j → σ t ≤ j + 1 ∧ j ≤ ρ t + 1
  crk : ∀ s t, s < t → t < n → ∀ a b, T s a → T t b → a + 3 ≤ b →
    ∃ r r', s < r ∧ r < r' ∧ r' < t ∧ ρ r ≤ b - 1 ∧ b - 1 ≤ σ r ∧ ρ r' ≤ a + 1 ∧ a + 1 ≤ σ r'
  crk' : ∀ s t, s < t → t < n → ∀ a b, T s a → T t b → b + 3 ≤ a →
    ∃ r r', s < r ∧ r < r' ∧ r' < t ∧ ρ r ≤ b + 1 ∧ b + 1 ≤ σ r ∧ ρ r' ≤ a - 1 ∧ a - 1 ≤ σ r'

/-- A partial consolidation on the fine links `p … q`: moves by at most one, and each fibre lies in
two adjacent coarse links. -/
def PCons (p q : ℕ) (ρ σ : ℕ → ℕ) (β : ℕ → ℕ) : Prop :=
  (∀ t, p ≤ t → t + 1 ≤ q → β (t + 1) ≤ β t + 1 ∧ β t ≤ β (t + 1) + 1) ∧
  (∀ v, ∃ j, ∀ t, p ≤ t → t ≤ q → β t = v → j ≤ σ t ∧ ρ t ≤ j + 1)

/-- Bing's end clause ("or" reading) for the end links `0` and `n − 1`. -/
def EndC (n K : ℕ) (ρ σ : ℕ → ℕ) (T : ℕ → ℕ → Prop) (β : ℕ → ℕ) : Prop :=
  ∀ e, e < n → (e = 0 ∨ e = n - 1) → (T e 0 ∨ T e (K - 1)) →
    (∀ t, t < n → β t = β e → ρ t ≤ 1) ∨ (∀ t, t < n → β t = β e → K - 2 ≤ σ t)

/-- **Bing's conclusion** (Theorem 3, block reading, two adjacent links, "or" end clause). -/
def BConcl (n K : ℕ) (ρ σ : ℕ → ℕ) (T : ℕ → ℕ → Prop) (i : ℕ) : Prop :=
  ∃ β : ℕ → ℕ, β i = 0 ∧ PCons 0 (n - 1) ρ σ β ∧ EndC n K ρ σ T β

/-! ## Transformations: mirror, reversal, sub-model -/

/-- Mirror the coarse chain. -/
def flipT (K : ℕ) (T : ℕ → ℕ → Prop) : ℕ → ℕ → Prop := fun t j => j ≤ K - 1 ∧ T t (K - 1 - j)

theorem BHyp.flip {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) :
    BHyp n K (fun t => K - 1 - σ t) (fun t => K - 1 - ρ t) (flipT K T) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht j h1 h2 => ?_,
    fun t ht j h1 h2 => ?_, fun t ht j h1 h2 => ?_, fun t ht j hj => ?_,
    fun s t hst ht a b ha hb hab => ?_, fun s t hst ht a b ha hb hab => ?_⟩
  · have := h.le t ht; have := h.lt t ht; omega
  · have := h.le t ht; have := h.wid t ht; have := h.lt t ht; omega
  · have := h.le t ht; have := h.lt t ht; omega
  · have := h.adj t ht; have := h.lt t (by omega); have := h.lt (t + 1) ht
    have := h.le t (by omega); have := h.le (t + 1) ht; omega
  · have := h.lt t ht; have := h.le t ht
    exact ⟨by omega, h.cont t ht _ (by omega) (by omega)⟩
  · have := h.lt (t + 1) ht; have := h.le (t + 1) ht
    exact ⟨by omega, h.fwd t ht _ (by omega) (by omega)⟩
  · have := h.lt t (by omega); have := h.le t (by omega)
    exact ⟨by omega, h.bwd t ht _ (by omega) (by omega)⟩
  · obtain ⟨hj1, hj2⟩ := hj
    have := h.poss t ht _ hj2; have := h.lt t ht; have := h.le t ht; omega
  · obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
    obtain ⟨r, r', h1, h2, h3, h4, h5, h6, h7⟩ :=
      h.crk' s t hst ht (K - 1 - a) (K - 1 - b) ha2 hb2 (by omega)
    have := h.lt r (by omega); have := h.lt r' (by omega)
    exact ⟨r, r', h1, h2, h3, by omega, by omega, by omega, by omega⟩
  · obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
    obtain ⟨r, r', h1, h2, h3, h4, h5, h6, h7⟩ :=
      h.crk s t hst ht (K - 1 - a) (K - 1 - b) ha2 hb2 (by omega)
    have := h.lt r (by omega); have := h.lt r' (by omega)
    have := h.le r (by omega); have := h.le r' (by omega)
    exact ⟨r, r', h1, h2, h3, by omega, by omega, by omega, by omega⟩

theorem BConcl.of_flip {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) {i : ℕ}
    (hi : i < n) (hc : BConcl n K (fun t => K - 1 - σ t) (fun t => K - 1 - ρ t) (flipT K T) i) :
    BConcl n K ρ σ T i := by
  obtain ⟨β, h0, ⟨hlip, hwid⟩, hend⟩ := hc
  refine ⟨β, h0, ⟨hlip, fun v => ?_⟩, fun e he hee hT => ?_⟩
  · obtain ⟨j, hj⟩ := hwid v
    refine ⟨K - 2 - j, fun t h1 h2 h3 => ?_⟩
    have := hj t h1 h2 h3; simp only at this
    have := h.lt t (by omega); have := h.le t (by omega); omega
  · have hK : 1 ≤ K := by have := h.lt e he; omega
    have hT' : flipT K T e 0 ∨ flipT K T e (K - 1) := by
      rcases hT with hT | hT
      · exact Or.inr ⟨le_rfl, by rwa [show K - 1 - (K - 1) = 0 by omega]⟩
      · exact Or.inl ⟨by omega, by rwa [show K - 1 - 0 = K - 1 by omega]⟩
    rcases hend e he hee hT' with hb | hb
    · right; intro t ht hte; have := hb t ht hte; simp only at this; have := h.lt t ht; omega
    · left; intro t ht hte; have := hb t ht hte; simp only at this
      have := h.lt t ht; have := h.le t ht; omega

/-- Reverse the fine chain. -/
theorem BHyp.rev {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) :
    BHyp n K (fun t => ρ (n - 1 - t)) (fun t => σ (n - 1 - t)) (fun t j => T (n - 1 - t) j) := by
  refine ⟨fun t ht => h.le _ (by omega), fun t ht => h.wid _ (by omega),
    fun t ht => h.lt _ (by omega), fun t ht => ?_, fun t ht j h1 h2 => h.cont _ (by omega) j h1 h2,
    fun t ht j h1 h2 => ?_, fun t ht j h1 h2 => ?_, fun t ht j hj => h.poss _ (by omega) j hj,
    fun s t hst ht a b ha hb hab => ?_, fun s t hst ht a b ha hb hab => ?_⟩
  · have := h.adj (n - 1 - (t + 1)) (by omega)
    rw [show n - 1 - (t + 1) + 1 = n - 1 - t by omega] at this
    exact ⟨this.2, this.1⟩
  · have := h.bwd (n - 1 - (t + 1)) (by omega) j h1 h2
    rwa [show n - 1 - (t + 1) + 1 = n - 1 - t by omega] at this
  · have := h.fwd (n - 1 - (t + 1)) (by omega) j
      (by rwa [show n - 1 - (t + 1) + 1 = n - 1 - t by omega])
      (by rwa [show n - 1 - (t + 1) + 1 = n - 1 - t by omega])
    exact this
  · obtain ⟨r, r', h1, h2, h3, h4, h5, h6, h7⟩ :=
      h.crk' (n - 1 - t) (n - 1 - s) (by omega) (by omega) b a hb ha (by omega)
    refine ⟨n - 1 - r', n - 1 - r, by omega, by omega, by omega, ?_⟩
    rw [show n - 1 - (n - 1 - r') = r' by omega, show n - 1 - (n - 1 - r) = r by omega]
    exact ⟨by omega, by omega, by omega, by omega⟩
  · obtain ⟨r, r', h1, h2, h3, h4, h5, h6, h7⟩ :=
      h.crk (n - 1 - t) (n - 1 - s) (by omega) (by omega) b a hb ha (by omega)
    refine ⟨n - 1 - r', n - 1 - r, by omega, by omega, by omega, ?_⟩
    rw [show n - 1 - (n - 1 - r') = r' by omega, show n - 1 - (n - 1 - r) = r by omega]
    exact ⟨by omega, by omega, by omega, by omega⟩

theorem BConcl.of_rev {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {i : ℕ} (hi : i < n)
    (hc : BConcl n K (fun t => ρ (n - 1 - t)) (fun t => σ (n - 1 - t))
      (fun t j => T (n - 1 - t) j) (n - 1 - i)) :
    BConcl n K ρ σ T i := by
  obtain ⟨β, h0, ⟨hlip, hwid⟩, hend⟩ := hc
  refine ⟨fun t => β (n - 1 - t), by simpa using h0, ⟨fun t h1 h2 => ?_, fun v => ?_⟩,
    fun e he hee hT => ?_⟩
  · have := hlip (n - 1 - (t + 1)) (by omega) (by omega)
    rw [show n - 1 - (t + 1) + 1 = n - 1 - t by omega] at this
    exact ⟨this.2, this.1⟩
  · obtain ⟨j, hj⟩ := hwid v
    refine ⟨j, fun t h1 h2 h3 => ?_⟩
    have := hj (n - 1 - t) (by omega) (by omega) h3
    simpa [show n - 1 - (n - 1 - t) = t by omega] using this
  · have hT' : T (n - 1 - (n - 1 - e)) 0 ∨ T (n - 1 - (n - 1 - e)) (K - 1) := by
      rwa [show n - 1 - (n - 1 - e) = e by omega]
    rcases hend (n - 1 - e) (by omega) (by omega) hT' with hb | hb
    · left; intro t ht hte
      have := hb (n - 1 - t) (by omega) (by simpa using hte)
      simpa [show n - 1 - (n - 1 - t) = t by omega] using this
    · right; intro t ht hte
      have := hb (n - 1 - t) (by omega) (by simpa using hte)
      simpa [show n - 1 - (n - 1 - t) = t by omega] using this

/-- The sub-model on the fine links `p … q` and the coarse links `lo … hi`. -/
theorem BHyp.sub {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T)
    {p q lo hi : ℕ} (hpq : p ≤ q) (hq : q < n)
    (hin : ∀ t, p ≤ t → t ≤ q → lo ≤ ρ t ∧ σ t ≤ hi) :
    BHyp (q - p + 1) (hi - lo + 1) (fun t => ρ (t + p) - lo) (fun t => σ (t + p) - lo)
      (fun t j => j + lo ≤ hi ∧ T (t + p) (j + lo)) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht j h1 h2 => ?_,
    fun t ht j h1 h2 => ?_, fun t ht j h1 h2 => ?_, fun t ht j hj => ?_,
    fun s t hst ht a b ha hb hab => ?_, fun s t hst ht a b ha hb hab => ?_⟩
  · have := h.le (t + p) (by omega); omega
  · have := h.wid (t + p) (by omega); have := hin (t + p) (by omega) (by omega); omega
  · have := hin (t + p) (by omega) (by omega); omega
  · have := h.adj (t + p) (by omega); have := hin (t + p) (by omega) (by omega)
    have := hin (t + 1 + p) (by omega) (by omega)
    rw [show t + 1 + p = t + p + 1 by omega] at *; omega
  · have := hin (t + p) (by omega) (by omega); have := h.le (t + p) (by omega)
    exact ⟨by omega, h.cont (t + p) (by omega) _ (by omega) (by omega)⟩
  · have := hin (t + 1 + p) (by omega) (by omega); have := h.le (t + 1 + p) (by omega)
    rw [show t + 1 + p = t + p + 1 by omega] at *
    exact ⟨by omega, h.fwd (t + p) (by omega) _ (by omega) (by omega)⟩
  · have := hin (t + p) (by omega) (by omega); have := h.le (t + p) (by omega)
    rw [show t + 1 + p = t + p + 1 by omega]
    exact ⟨by omega, h.bwd (t + p) (by omega) _ (by omega) (by omega)⟩
  · have := h.poss (t + p) (by omega) _ hj.2; have := hin (t + p) (by omega) (by omega); omega
  · obtain ⟨r, r', h1, h2, h3, h4, h5, h6, h7⟩ :=
      h.crk (s + p) (t + p) (by omega) (by omega) _ _ ha.2 hb.2 (by omega)
    refine ⟨r - p, r' - p, by omega, by omega, by omega, ?_⟩
    rw [show r - p + p = r by omega, show r' - p + p = r' by omega]
    have := hin r (by omega) (by omega); have := hin r' (by omega) (by omega)
    exact ⟨by omega, by omega, by omega, by omega⟩
  · obtain ⟨r, r', h1, h2, h3, h4, h5, h6, h7⟩ :=
      h.crk' (s + p) (t + p) (by omega) (by omega) _ _ ha.2 hb.2 (by omega)
    refine ⟨r - p, r' - p, by omega, by omega, by omega, ?_⟩
    rw [show r - p + p = r by omega, show r' - p + p = r' by omega]
    have := hin r (by omega) (by omega); have := hin r' (by omega) (by omega)
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- What the conclusion for a sub-model says about the original links (absolute indices). -/
theorem BConcl.sub_abs {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {p q lo hi i : ℕ} (hpq : p ≤ q)
    (hin : ∀ t, p ≤ t → t ≤ q → lo ≤ ρ t ∧ σ t ≤ hi) (hle : ∀ t, p ≤ t → t ≤ q → ρ t ≤ σ t)
    (hc : BConcl (q - p + 1) (hi - lo + 1) (fun t => ρ (t + p) - lo) (fun t => σ (t + p) - lo)
      (fun t j => j + lo ≤ hi ∧ T (t + p) (j + lo)) (i - p)) :
    ∃ H : ℕ → ℕ, H i = 0 ∧ PCons p q ρ σ H ∧
      ∀ e, (e = p ∨ e = q) → (T e lo ∨ T e hi) →
        (∀ t, p ≤ t → t ≤ q → H t = H e → ρ t ≤ lo + 1) ∨
        (∀ t, p ≤ t → t ≤ q → H t = H e → hi ≤ σ t + 1) := by
  obtain ⟨β, h0, ⟨hlip, hwid⟩, hend⟩ := hc
  refine ⟨fun t => β (t - p), h0, ⟨fun t h1 h2 => ?_, fun v => ?_⟩, fun e he hT => ?_⟩
  · have := hlip (t - p) (by omega) (by omega)
    simpa [show t + 1 - p = t - p + 1 by omega] using this
  · obtain ⟨j, hj⟩ := hwid v
    refine ⟨j + lo, fun t h1 h2 h3 => ?_⟩
    have := hj (t - p) (by omega) (by omega) h3
    simp only [show t - p + p = t by omega] at this
    have := hin t h1 h2; have := hle t h1 h2; omega
  · have hlohi : lo ≤ hi := by have := hin p le_rfl hpq; have := hle p le_rfl hpq; omega
    have hT' : ((e - p) = 0 ∨ e - p = q - p + 1 - 1) := by omega
    have hT'' : ((0 + lo ≤ hi ∧ T (e - p + p) (0 + lo)) ∨
        (hi - lo + 1 - 1 + lo ≤ hi ∧ T (e - p + p) (hi - lo + 1 - 1 + lo))) := by
      rw [show e - p + p = e by omega, show 0 + lo = lo by omega,
        show hi - lo + 1 - 1 + lo = hi by omega]
      rcases hT with hT | hT
      · exact Or.inl ⟨hlohi, hT⟩
      · exact Or.inr ⟨le_rfl, hT⟩
    rcases hend (e - p) (by omega) hT' hT'' with hb | hb
    · left; intro t h1 h2 h3
      have := hb (t - p) (by omega) h3
      simp only [show t - p + p = t by omega] at this; omega
    · right; intro t h1 h2 h3
      have := hb (t - p) (by omega) h3
      simp only [show t - p + p = t by omega] at this; have := hle t h1 h2
      have := hin t h1 h2; omega

/-! ## The level groupings: base case `m ≤ 4` and the case `d_i ⊆ e₁ + e₂` -/

/-- **Base case** `K ≤ 4`: the links in `e₁ + e₂`, and the others. -/
theorem bconcl_base {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) {i : ℕ}
    (hi : i < n) (hK : K ≤ 4) : BConcl n K ρ σ T i := by
  classical
  refine ⟨fun t => if (ρ t ≤ 1 ↔ ρ i ≤ 1) then 0 else 1, by simp, ⟨fun t _ _ => ?_, fun v => ?_⟩,
    fun e he _ _ => ?_⟩
  · constructor <;> simp only <;> split_ifs <;> omega
  · refine ⟨if (v = 0 ↔ ρ i ≤ 1) then 0 else 2, fun t _ ht hv => ?_⟩
    have := h.le t (by omega); have := h.lt t (by omega)
    subst hv
    by_cases h1 : ρ t ≤ 1 <;> by_cases h2 : ρ i ≤ 1 <;> simp [h1, h2] <;> omega
  · by_cases he1 : ρ e ≤ 1
    · left; intro t ht hte
      by_contra hc
      by_cases h2 : ρ i ≤ 1 <;> simp [he1, hc, h2] at hte
    · right; intro t ht hte
      have := h.le t ht
      by_cases h1 : ρ t ≤ 1
      · by_cases h2 : ρ i ≤ 1 <;> simp [he1, h1, h2] at hte
      · omega

/-- **The case `d_i ⊆ e₁ + e₂`**: the groups "in `e₁ + e₂`", "in `e₃` not `e₂`", …, "in
`e_{m−1} + e_m`", i.e. by the least level `ρ`. -/
theorem bconcl_low {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) {i : ℕ}
    (hi : i < n) (hK : 4 ≤ K) (hρi : ρ i ≤ 1) : BConcl n K ρ σ T i := by
  refine ⟨fun t => min (ρ t - 1) (K - 3), by simp; omega, ⟨fun t _ ht => ?_, fun v => ?_⟩,
    fun e he _ hT => ?_⟩
  · have := h.adj t (by omega); have := h.le t (by omega); have := h.le (t + 1) (by omega)
    simp only; omega
  · refine ⟨if v = 0 then 0 else if v < K - 3 then v + 1 else K - 2, fun t _ ht hv => ?_⟩
    have := h.le t (by omega); have := h.lt t (by omega)
    simp only at hv; subst hv
    split_ifs <;> omega
  · rcases hT with hT | hT
    · have := h.poss e he 0 hT; have := h.le e he
      left; intro t ht hte; simp only at hte; omega
    · have := h.poss e he _ hT; have := h.le e he
      right; intro t ht hte; simp only at hte; have := h.le t ht; omega

/-- **The case `d_i ⊆ e_{m−1} + e_m`**, by the mirror image. -/
theorem bconcl_high {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) {i : ℕ}
    (hi : i < n) (hK : 4 ≤ K) (hσi : K ≤ σ i + 2) : BConcl n K ρ σ T i :=
  BConcl.of_flip h hi (bconcl_low h.flip hi hK (by show K - 1 - σ i ≤ 1; omega))

end HPC.Fold.Recon122
