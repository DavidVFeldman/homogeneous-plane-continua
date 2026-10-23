import HPC.BJ59.Thm3Assembly

/-!
# Batch 198, library: Bing–Jones's Theorem 3

`theorem3_arc`: a snake-like arc of continua `X` (with `f : X → [0, 1]`) can be covered, for every
`ε > 0`, by an `ε`-chain whose first link meets `g₀ = f⁻¹(0)` and whose last link meets
`g₁ = f⁻¹(1)`.

*Proof* (Bing–Jones's, p. 175, with the chain repaired, `chain_assembly`). Take a coarse
`δ`-chain `E`; `E(i, j)` and `E(r, s)` are the links meeting `g₀` and `g₁`, with unions `V₀`, `V₁`.
Choose `a > 0`, `b < 1` with `G(0, a) ⊆ V₀`, `G(b, 1) ⊆ V₁`, and a fine `γ`-chain `F` (finer than a
Lebesgue number of `E` and than the distances from `g₀` to `G(a, 1)` and from `g₁` to `G(0, b)`),
oriented so that its links meeting `g₀` precede those meeting `g₁`. The links of `F` before the
first link meeting `g₀` lie in `G(0, a)` (`G(a, 1)` is connected and runs from those links to `g₁`),
so they lie in `V₀`. Let `f_{v+1}` be the first link after the links meeting `g₀` that is not in
`V₀`, and `f_{w−1}` the last link before those meeting `g₁` that is not in `V₁`. Then `f_v` lies in an
end link of `E(i, j)` and `f_w` in an end link of `E(r, s)`, and `w ≥ v + 4` when `γ` is small.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane

variable {X : Type*} [MetricSpace X]

/-- Points of links `p` and `p + d` of a `γ`-chain are less than `(d + 1) γ` apart. -/
theorem dist_lt_of_mem_links {N : ℕ} {F : Chain X N} {γ : ℝ} (hF : IsEpsChain F γ) :
    ∀ (d : ℕ) (p q : Fin N), (q : ℕ) = p + d → ∀ x ∈ F.link p, ∀ y ∈ F.link q,
      dist x y < (d + 1) * γ := by
  intro d
  induction d with
  | zero =>
    intro p q hpq x hx y hy
    have : q = p := Fin.ext (by simpa using hpq)
    subst this
    simpa using lt_of_le_of_lt (dist_le_diam_of_mem (hF q).1 hx hy) (hF q).2
  | succ d ih =>
    intro p q hpq x hx y hy
    set q' : Fin N := ⟨p + d, by omega⟩
    obtain ⟨z, hz, hz'⟩ := (F.adjacent q' q).2 (by simp [q']; omega)
    have h1 := ih p q' rfl x hx z hz
    have h2 := lt_of_le_of_lt (dist_le_diam_of_mem (hF q).1 hz' hy) (hF q).2
    have := dist_triangle x z y
    push_cast; linarith

/-- The union of the links of `E` between `i` and `j`. -/
def segUnion {n : ℕ} (E : Chain X n) (i j : Fin n) : Set X :=
  ⋃ (t : Fin n) (_ : i ≤ t ∧ t ≤ j), E.link t

theorem union_sub_eq {n : ℕ} (E : Chain X n) (i j : Fin n) (hij : i ≤ j) :
    (E.sub i j hij).union = segUnion E i j := by
  ext x
  simp only [Chain.union, segUnion, mem_iUnion]
  constructor
  · rintro ⟨t, ht⟩
    have := t.isLt
    exact ⟨_, ⟨by rw [Fin.le_def]; simp, by rw [Fin.le_def]; simp; omega⟩, ht⟩
  · rintro ⟨t, ⟨h1, h2⟩, ht⟩
    rw [Fin.le_def] at h1 h2
    refine ⟨⟨t - i, by omega⟩, ?_⟩
    show x ∈ E.link ⟨i + (t - i), _⟩
    have : (⟨i + (t - i), by omega⟩ : Fin n) = t := Fin.ext (by simp; omega)
    rw [this]; exact ht

theorem union_reverse {n : ℕ} (D : Chain X n) : D.reverse.union = D.union := by
  ext x
  simp only [Chain.union, mem_iUnion, Chain.reverse_link]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨_, ht⟩
  · rintro ⟨t, ht⟩; exact ⟨Fin.rev t, by rwa [Fin.rev_rev]⟩

/-- **The oriented case of Theorem 3**, given the coarse chain and the fine chain. -/
theorem theorem3_of_chains [CompactSpace X] {f : X → unitInterval} {n N : ℕ} (E : Chain X n)
    (F : Chain X N) {δ γ ε ρ lam : ℝ} {a b : unitInterval} {i j r s : Fin n}
    (hfc : Continuous f) (hfs : Function.Surjective f) (hfib : ∀ t, IsPreconnected (f ⁻¹' {t}))
    (hE : IsEpsChain E δ) (hF : IsEpsChain F γ) (hFcov : univ ⊆ F.union)
    (hij : i ≤ j) (hrs : r ≤ s)
    (h0E : ∀ t, (f ⁻¹' {0} ∩ E.link t).Nonempty ↔ (i ≤ t ∧ t ≤ j))
    (h1E : ∀ t, (f ⁻¹' {1} ∩ E.link t).Nonempty ↔ (r ≤ t ∧ t ≤ s))
    (hρ : ∀ x ∈ f ⁻¹' {0}, ∀ y ∈ f ⁻¹' {1}, ρ ≤ dist x y)
    (hδρ : δ ≤ ρ / 4) (hγρ : γ ≤ ρ / 8) (hδε : δ ≤ ε / 2) (hγε : γ ≤ ε / 2)
    (hlam : ∀ x, ∃ t, ball x lam ⊆ E.link t) (hγlam : 2 * γ ≤ lam)
    (ha : f ⁻¹' Icc 0 a ⊆ segUnion E i j) (hb : f ⁻¹' Icc b 1 ⊆ segUnion E r s)
    (hσ₀ : ∀ x ∈ f ⁻¹' {0}, ∀ y ∈ f ⁻¹' Icc a 1, γ ≤ dist x y)
    (hσ₁ : ∀ x ∈ f ⁻¹' {1}, ∀ y ∈ f ⁻¹' Icc 0 b, γ ≤ dist x y)
    (horient : ∀ k k' : Fin N, (F.link k ∩ f ⁻¹' {0}).Nonempty →
      (F.link k' ∩ f ⁻¹' {1}).Nonempty → k < k') :
    ∃ (m : ℕ) (D : Chain X (m + 1)), IsEpsChain D ε ∧ univ ⊆ D.union ∧
      (D.link 0 ∩ f ⁻¹' {0}).Nonempty ∧ (D.link (Fin.last m) ∩ f ⁻¹' {1}).Nonempty := by
  set g₀ := f ⁻¹' {0} with hg₀def
  set g₁ := f ⁻¹' {1} with hg₁def
  set V₀ := segUnion E i j
  set V₁ := segUnion E r s
  have hg₀ : IsPreconnected g₀ := hfib 0
  have hg₁ : IsPreconnected g₁ := hfib 1
  have hg₀ne : g₀.Nonempty := (hfs 0).imp fun x hx => hx
  have hg₁ne : g₁.Nonempty := (hfs 1).imp fun x hx => hx
  have hγ : 0 < γ := by
    obtain ⟨x, -⟩ := hg₀ne
    obtain ⟨k, hk⟩ := exists_link_of_mem_union (hFcov (mem_univ x))
    exact lt_of_le_of_lt diam_nonneg (hF k).2
  have hρpos : 0 < ρ := by linarith
  have hsubU : ∀ S : Set X, S ⊆ F.union := fun S => (subset_univ S).trans hFcov
  -- points of `V₀` are near `g₀`, points of `V₁` near `g₁`
  have hV₀near : ∀ x ∈ V₀, ∃ z ∈ g₀, dist x z < δ := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.1 hx
    obtain ⟨z, hz, hzt⟩ := (h0E t).2 ht
    exact ⟨z, hz, lt_of_le_of_lt (dist_le_diam_of_mem (hE t).1 hxt hzt) (hE t).2⟩
  have hV₁near : ∀ x ∈ V₁, ∃ z ∈ g₁, dist x z < δ := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.1 hx
    obtain ⟨z, hz, hzt⟩ := (h1E t).2 ht
    exact ⟨z, hz, lt_of_le_of_lt (dist_le_diam_of_mem (hE t).1 hxt hzt) (hE t).2⟩
  have hfar : ∀ x ∈ V₀, ∀ y ∈ V₁, ρ / 2 ≤ dist x y := by
    intro x hx y hy
    obtain ⟨z, hz, hxz⟩ := hV₀near x hx
    obtain ⟨z', hz', hyz'⟩ := hV₁near y hy
    have := hρ z hz z' hz'
    have := dist_triangle4 z x y z'
    rw [dist_comm z x] at this
    linarith
  have hV₀V₁ : Disjoint V₀ V₁ := Set.disjoint_left.2 fun x hx hx' => by
    have := hfar x hx x hx'; simp at this; linarith
  have hg₁V₀ : Disjoint g₁ V₀ := Set.disjoint_left.2 fun y hy hy' => by
    obtain ⟨z, hz, hyz⟩ := hV₀near y hy'
    have := hρ z hz y hy; rw [dist_comm] at this; linarith
  have hg₀V₁ : Disjoint g₀ V₁ := Set.disjoint_left.2 fun y hy hy' => by
    obtain ⟨z, hz, hyz⟩ := hV₁near y hy'
    have := hρ y hy z hz; linarith
  -- a `γ`-link lies in a link of `E`
  have hlink : ∀ k : Fin N, ∃ t, F.link k ⊆ E.link t := by
    intro k
    obtain ⟨y, hy⟩ := F.link_nonempty k
    obtain ⟨t, ht⟩ := hlam y
    refine ⟨t, fun z hz => ht ?_⟩
    rw [mem_ball, dist_comm]
    have := lt_of_le_of_lt (dist_le_diam_of_mem (hF k).1 hy hz) (hF k).2
    linarith
  have hlink2 : ∀ k k' : Fin N, (k' : ℕ) = k + 1 → ∃ t, F.link k ∪ F.link k' ⊆ E.link t := by
    intro k k' hkk'
    obtain ⟨y, hy, hy'⟩ := (F.adjacent k k').2 (by omega)
    obtain ⟨t, ht⟩ := hlam y
    refine ⟨t, fun z hz => ht ?_⟩
    rw [mem_ball, dist_comm]
    rcases hz with hz | hz
    · have := lt_of_le_of_lt (dist_le_diam_of_mem (hF k).1 hy hz) (hF k).2; linarith
    · have := lt_of_le_of_lt (dist_le_diam_of_mem (hF k').1 hy' hz) (hF k').2; linarith
  -- the links of `F` meeting `g₀` and `g₁`
  obtain ⟨t₀, t₁, ht01, ht⟩ := exists_trim F hg₀ hg₀ne (hsubU g₀)
  obtain ⟨u₀, u₁, hu01, hu⟩ := exists_trim F hg₁ hg₁ne (hsubU g₁)
  have hswap : ∀ {S : Set X} {k : Fin N}, (S ∩ F.link k).Nonempty → (F.link k ∩ S).Nonempty :=
    fun h => by rwa [inter_comm]
  have ht1 : (g₀ ∩ F.link t₁).Nonempty := (ht t₁).2 ⟨Fin.le_def.1 ht01, le_rfl⟩
  have ht0 : (g₀ ∩ F.link t₀).Nonempty := (ht t₀).2 ⟨le_rfl, Fin.le_def.1 ht01⟩
  have hu0 : (g₁ ∩ F.link u₀).Nonempty := (hu u₀).2 ⟨le_rfl, Fin.le_def.1 hu01⟩
  have hu1 : (g₁ ∩ F.link u₁).Nonempty := (hu u₁).2 ⟨Fin.le_def.1 hu01, le_rfl⟩
  have htu : t₁ < u₀ := horient t₁ u₀ (hswap ht1) (hswap hu0)
  -- links meeting `g₀` lie in `V₀`; links meeting `g₁` lie in `V₁`
  have hC₀ : ∀ k : Fin N, (g₀ ∩ F.link k).Nonempty → F.link k ⊆ V₀ := by
    intro k hk
    obtain ⟨t, hkt⟩ := hlink k
    obtain ⟨x, hxg, hxk⟩ := hk
    have htm := (h0E t).1 ⟨x, hxg, hkt hxk⟩
    exact fun y hy => mem_iUnion₂.2 ⟨t, htm, hkt hy⟩
  have hC₁ : ∀ k : Fin N, (g₁ ∩ F.link k).Nonempty → F.link k ⊆ V₁ := by
    intro k hk
    obtain ⟨t, hkt⟩ := hlink k
    obtain ⟨x, hxg, hxk⟩ := hk
    have htm := (h1E t).1 ⟨x, hxg, hkt hxk⟩
    exact fun y hy => mem_iUnion₂.2 ⟨t, htm, hkt hy⟩
  -- links before `t₀` lie in `G(0, a)`, links after `u₁` in `G(b, 1)`
  have hA₀ : ∀ k : Fin N, k < t₀ → F.link k ⊆ V₀ := by
    intro k hk x hx
    apply ha
    refine ⟨unitInterval.nonneg', ?_⟩
    by_contra hxa
    push_neg at hxa
    have hGc := isPreconnected_preimage_Icc hfc hfs hfib a 1
    have hmeet1 : (f ⁻¹' Icc a 1 ∩ F.link k).Nonempty := ⟨x, ⟨hxa.le, unitInterval.le_one'⟩, hx⟩
    have hmeet2 : (f ⁻¹' Icc a 1 ∩ F.link u₀).Nonempty := by
      obtain ⟨y, hy, hyu⟩ := hu0
      refine ⟨y, ⟨?_, unitInterval.le_one'⟩, hyu⟩
      rw [show f y = 1 from hy]; exact unitInterval.le_one'
    have := meets_between F hGc (hsubU _) hmeet1 hmeet2 t₀ (by
      rw [Fin.lt_def] at hk; omega) (by
      rw [Fin.lt_def] at htu; rw [Fin.le_def] at ht01; omega)
    obtain ⟨y, hy, hyt⟩ := this
    obtain ⟨z, hz, hzt⟩ := ht0
    have h1 := hσ₀ z hz y hy
    have h2 := lt_of_le_of_lt (dist_le_diam_of_mem (hF t₀).1 hzt hyt) (hF t₀).2
    linarith
  have hB₁ : ∀ k : Fin N, u₁ < k → F.link k ⊆ V₁ := by
    intro k hk x hx
    apply hb
    refine ⟨?_, unitInterval.le_one'⟩
    by_contra hxb
    push_neg at hxb
    have hGc := isPreconnected_preimage_Icc hfc hfs hfib 0 b
    have hmeet1 : (f ⁻¹' Icc 0 b ∩ F.link k).Nonempty :=
      ⟨x, ⟨unitInterval.nonneg', hxb.le⟩, hx⟩
    have hmeet2 : (f ⁻¹' Icc 0 b ∩ F.link t₁).Nonempty := by
      obtain ⟨y, hy, hyu⟩ := ht1
      refine ⟨y, ⟨unitInterval.nonneg', ?_⟩, hyu⟩
      rw [show f y = 0 from hy]; exact unitInterval.nonneg'
    have := meets_between F hGc (hsubU _) hmeet1 hmeet2 u₁ (by
      rw [Fin.lt_def] at htu; rw [Fin.le_def] at hu01; omega) (by
      rw [Fin.lt_def] at hk; omega)
    obtain ⟨y, hy, hyt⟩ := this
    obtain ⟨z, hz, hzt⟩ := hu1
    have h1 := hσ₁ z hz y hy
    have h2 := lt_of_le_of_lt (dist_le_diam_of_mem (hF u₁).1 hzt hyt) (hF u₁).2
    linarith
  -- the index `v`
  classical
  have hu0V : ¬ F.link u₀ ⊆ V₀ := fun h => by
    obtain ⟨y, hy, hyu⟩ := hu0
    exact Set.disjoint_left.1 hg₁V₀ hy (h hyu)
  have hSv : (Finset.univ.filter fun k : Fin N => t₁ < k ∧ ¬ F.link k ⊆ V₀).Nonempty :=
    ⟨u₀, by simp [htu, hu0V]⟩
  set k₁ := Finset.min' _ hSv with hk₁
  have hk₁mem := Finset.min'_mem _ hSv
  rw [← hk₁] at hk₁mem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk₁mem
  have hk₁min : ∀ k : Fin N, t₁ < k → ¬ F.link k ⊆ V₀ → k₁ ≤ k := fun k h1 h2 =>
    Finset.min'_le _ k (by simp [h1, h2])
  set v : ℕ := (k₁ : ℕ) - 1 with hvdef
  have hvt : (t₁ : ℕ) ≤ v := by have := Fin.lt_def.1 hk₁mem.1; omega
  have hlow : ∀ k : Fin N, (k : ℕ) ≤ v → F.link k ⊆ V₀ := by
    intro k hk
    by_cases h1 : k < t₀
    · exact hA₀ k h1
    by_cases h2 : k ≤ t₁
    · exact hC₀ k ((ht k).2 ⟨by rw [not_lt, Fin.le_def] at h1; exact h1, Fin.le_def.1 h2⟩)
    · by_contra hcon
      have := hk₁min k (not_le.1 h2) hcon
      rw [Fin.le_def] at this
      have := Fin.lt_def.1 hk₁mem.1
      omega
  have hlowU : lowUnion F v ⊆ V₀ := fun x hx => by
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx; exact hlow k hk hxk
  -- `f_v` lies in an end link of `E(i, j)`
  set fv : Fin N := ⟨v, by omega⟩
  have hk₁v : (k₁ : ℕ) = v + 1 := by have := Fin.lt_def.1 hk₁mem.1; omega
  have hend₀ : F.link fv ⊆ E.link j ∨ F.link fv ⊆ E.link i := by
    obtain ⟨μ, hμ⟩ := hlink2 fv k₁ hk₁v
    have hμ' : ¬ (i ≤ μ ∧ μ ≤ j) := fun h => hk₁mem.2 fun y hy =>
      mem_iUnion₂.2 ⟨μ, h, hμ (Or.inr hy)⟩
    have hfvV := hlow fv le_rfl
    have key : ∀ y ∈ F.link fv, ∀ τ : Fin n, i ≤ τ ∧ τ ≤ j → y ∈ E.link τ →
        ((τ : ℤ) - μ).natAbs ≤ 1 := fun y hy τ _ hyτ =>
      (E.adjacent τ μ).1 ⟨y, hyτ, hμ (Or.inl hy)⟩
    obtain ⟨y₀, hy₀⟩ := F.link_nonempty fv
    obtain ⟨τ₀, hτ₀, hyτ₀⟩ := mem_iUnion₂.1 (hfvV hy₀)
    have h0 := key y₀ hy₀ τ₀ hτ₀ hyτ₀
    rw [not_and_or, not_le, not_le] at hμ'
    rw [Fin.le_def, Fin.le_def] at hτ₀
    rcases hμ' with h | h
    · right
      intro y hy
      obtain ⟨τ, hτ, hyτ⟩ := mem_iUnion₂.1 (hfvV hy)
      have := key y hy τ hτ hyτ
      rw [Fin.le_def, Fin.le_def] at hτ
      rw [Fin.lt_def] at h
      have : τ = i := Fin.ext (by omega)
      exact this ▸ hyτ
    · left
      intro y hy
      obtain ⟨τ, hτ, hyτ⟩ := mem_iUnion₂.1 (hfvV hy)
      have := key y hy τ hτ hyτ
      rw [Fin.le_def, Fin.le_def] at hτ
      rw [Fin.lt_def] at h
      have : τ = j := Fin.ext (by omega)
      exact this ▸ hyτ
  -- the index `w`
  have ht1V : ¬ F.link t₁ ⊆ V₁ := fun h => by
    obtain ⟨y, hy, hyu⟩ := ht1
    exact Set.disjoint_left.1 hg₀V₁ hy (h hyu)
  have hSw : (Finset.univ.filter fun k : Fin N => k < u₀ ∧ ¬ F.link k ⊆ V₁).Nonempty :=
    ⟨t₁, by simp [htu, ht1V]⟩
  set k₂ := Finset.max' _ hSw with hk₂
  have hk₂mem := Finset.max'_mem _ hSw
  rw [← hk₂] at hk₂mem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk₂mem
  have hk₂max : ∀ k : Fin N, k < u₀ → ¬ F.link k ⊆ V₁ → k ≤ k₂ := fun k h1 h2 =>
    Finset.le_max' _ k (by simp [h1, h2])
  set w : ℕ := (k₂ : ℕ) + 1 with hwdef
  have hwu : w ≤ (u₀ : ℕ) := by have := Fin.lt_def.1 hk₂mem.1; omega
  have hwN : w < N := lt_of_le_of_lt hwu u₀.isLt
  have hhigh : ∀ k : Fin N, w ≤ (k : ℕ) → F.link k ⊆ V₁ := by
    intro k hk
    by_cases h1 : u₁ < k
    · exact hB₁ k h1
    by_cases h2 : u₀ ≤ k
    · exact hC₁ k ((hu k).2 ⟨Fin.le_def.1 h2, by rw [not_lt, Fin.le_def] at h1; exact h1⟩)
    · by_contra hcon
      have := hk₂max k (not_le.1 h2) hcon
      rw [Fin.le_def] at this
      omega
  have hhighU : highUnion F w ⊆ V₁ := fun x hx => by
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx; exact hhigh k hk hxk
  set fw : Fin N := ⟨w, hwN⟩
  have hend₁ : F.link fw ⊆ E.link r ∨ F.link fw ⊆ E.link s := by
    obtain ⟨μ, hμ⟩ := hlink2 k₂ fw rfl
    have hμ' : ¬ (r ≤ μ ∧ μ ≤ s) := fun h => hk₂mem.2 fun y hy =>
      mem_iUnion₂.2 ⟨μ, h, hμ (Or.inl hy)⟩
    have hfwV := hhigh fw le_rfl
    have key : ∀ y ∈ F.link fw, ∀ τ : Fin n, r ≤ τ ∧ τ ≤ s → y ∈ E.link τ →
        ((τ : ℤ) - μ).natAbs ≤ 1 := fun y hy τ _ hyτ =>
      (E.adjacent τ μ).1 ⟨y, hyτ, hμ (Or.inr hy)⟩
    obtain ⟨y₀, hy₀⟩ := F.link_nonempty fw
    obtain ⟨τ₀, hτ₀, hyτ₀⟩ := mem_iUnion₂.1 (hfwV hy₀)
    have h0 := key y₀ hy₀ τ₀ hτ₀ hyτ₀
    rw [not_and_or, not_le, not_le] at hμ'
    rw [Fin.le_def, Fin.le_def] at hτ₀
    rcases hμ' with h | h
    · left
      intro y hy
      obtain ⟨τ, hτ, hyτ⟩ := mem_iUnion₂.1 (hfwV hy)
      have := key y hy τ hτ hyτ
      rw [Fin.le_def, Fin.le_def] at hτ
      rw [Fin.lt_def] at h
      have : τ = r := Fin.ext (by omega)
      exact this ▸ hyτ
    · right
      intro y hy
      obtain ⟨τ, hτ, hyτ⟩ := mem_iUnion₂.1 (hfwV hy)
      have := key y hy τ hτ hyτ
      rw [Fin.le_def, Fin.le_def] at hτ
      rw [Fin.lt_def] at h
      have : τ = s := Fin.ext (by omega)
      exact this ▸ hyτ
  -- `w ≥ v + 4`
  have hvw : v + 4 ≤ w := by
    obtain ⟨y, hy⟩ := F.link_nonempty fv
    obtain ⟨y', hy'⟩ := F.link_nonempty fw
    have hfar' := hfar y (hlow fv le_rfl hy) y' (hhigh fw le_rfl hy')
    by_contra hcon
    push_neg at hcon
    rcases le_or_gt w v with h | h
    · exact Set.disjoint_left.1 hV₀V₁ (hlow fw h hy') (hhigh fw le_rfl hy')
    · have := dist_lt_of_mem_links hF (w - v) fv fw (by simp [fv, fw]; omega) y hy y' hy'
      have h4 : ((w - v : ℕ) : ℝ) + 1 ≤ 4 := by
        have : w - v ≤ 3 := by omega
        have : ((w - v : ℕ) : ℝ) ≤ 3 := by exact_mod_cast this
        linarith
      nlinarith
  -- the oriented coarse chains
  have hg₀low : g₀ ⊆ lowUnion F v := fun x hx => by
    obtain ⟨k, hk⟩ := exists_link_of_mem_union (hFcov (mem_univ x))
    have := (ht k).1 ⟨x, hx, hk⟩
    exact link_subset_lowUnion F (by omega) hk
  have hg₁high : g₁ ⊆ highUnion F w := fun x hx => by
    obtain ⟨k, hk⟩ := exists_link_of_mem_union (hFcov (mem_univ x))
    have := (hu k).1 ⟨x, hx, hk⟩
    exact link_subset_highUnion F (by omega) hk
  have hsub0 : ∀ k : Fin ((j : ℕ) - i + 1), (g₀ ∩ (E.sub i j hij).link k).Nonempty := fun k =>
    (h0E _).2 ⟨by rw [Fin.le_def]; simp, by rw [Fin.le_def]; simp; have := k.isLt; omega⟩
  have hsub1 : ∀ k : Fin ((s : ℕ) - r + 1), (g₁ ∩ (E.sub r s hrs).link k).Nonempty := fun k =>
    (h1E _).2 ⟨by rw [Fin.le_def]; simp, by rw [Fin.le_def]; simp; have := k.isLt; omega⟩
  have hU0 : (E.sub i j hij).union = V₀ := union_sub_eq E i j hij
  have hU1 : (E.sub r s hrs).union = V₁ := union_sub_eq E r s hrs
  have hlast0 : (E.sub i j hij).link (Fin.last _) = E.link j := by
    show E.link ⟨i + ((j : ℕ) - i), _⟩ = _
    congr 1; ext; simp; rw [Fin.le_def] at hij; omega
  have hfirst0 : (E.sub i j hij).reverse.link (Fin.last _) = E.link i := by
    rw [Chain.reverse_link, Fin.rev_last]
    show E.link ⟨i + 0, _⟩ = _
    congr 1
  have hfirst1 : (E.sub r s hrs).link 0 = E.link r := by
    show E.link ⟨r + 0, _⟩ = _
    congr 1
  have hlast1 : (E.sub r s hrs).reverse.link 0 = E.link s := by
    rw [Chain.reverse_link, Fin.rev_zero]
    show E.link ⟨r + ((s : ℕ) - r), _⟩ = _
    congr 1; ext; simp; rw [Fin.le_def] at hrs; omega
  have hEs0 := isEpsChain_sub hE i j hij
  have hEs1 := isEpsChain_sub hE r s hrs
  have hδγ : δ + γ ≤ ε := by linarith
  have hγε' : γ ≤ ε := by linarith
  have hvF : ∀ (E₀ : Chain X ((j : ℕ) - i + 1)), F.link fv ⊆ E₀.link (Fin.last _) →
      ∀ k : Fin N, (k : ℕ) = v → F.link k ⊆ E₀.link (Fin.last _) := fun E₀ h k hk => by
    have : k = fv := Fin.ext hk
    exact this ▸ h
  have hwF : ∀ (E₁ : Chain X ((s : ℕ) - r + 1)), F.link fw ⊆ E₁.link 0 →
      ∀ k : Fin N, (k : ℕ) = w → F.link k ⊆ E₁.link 0 := fun E₁ h k hk => by
    have : k = fw := Fin.ext hk
    exact this ▸ h
  rcases hend₀ with hv0 | hv0 <;> rcases hend₁ with hw1 | hw1
  · exact chain_assembly F (E.sub i j hij) (E.sub r s hrs) hF hFcov hEs0 hEs1 hδγ hγε' hvw hwN
      (hU0 ▸ hlowU) (hU1 ▸ hhighU) (hvF _ (hlast0 ▸ hv0)) (hwF _ (hfirst1 ▸ hw1))
      hg₀ hg₀low hsub0 hg₁ hg₁high hsub1
  · exact chain_assembly F (E.sub i j hij) (E.sub r s hrs).reverse hF hFcov hEs0
      (isEpsChain_reverse hEs1) hδγ hγε' hvw hwN (hU0 ▸ hlowU)
      ((union_reverse _).trans hU1 ▸ hhighU) (hvF _ (hlast0 ▸ hv0)) (hwF _ (hlast1 ▸ hw1))
      hg₀ hg₀low hsub0 hg₁ hg₁high (fun k => hsub1 _)
  · exact chain_assembly F (E.sub i j hij).reverse (E.sub r s hrs) hF hFcov
      (isEpsChain_reverse hEs0) hEs1 hδγ hγε' hvw hwN ((union_reverse _).trans hU0 ▸ hlowU)
      (hU1 ▸ hhighU) (hvF _ (hfirst0 ▸ hv0)) (hwF _ (hfirst1 ▸ hw1))
      hg₀ hg₀low (fun k => hsub0 _) hg₁ hg₁high hsub1
  · exact chain_assembly F (E.sub i j hij).reverse (E.sub r s hrs).reverse hF hFcov
      (isEpsChain_reverse hEs0) (isEpsChain_reverse hEs1) hδγ hγε' hvw hwN
      ((union_reverse _).trans hU0 ▸ hlowU) ((union_reverse _).trans hU1 ▸ hhighU)
      (hvF _ (hfirst0 ▸ hv0)) (hwF _ (hlast1 ▸ hw1))
      hg₀ hg₀low (fun k => hsub0 _) hg₁ hg₁high (fun k => hsub1 _)

/-- **Bing–Jones, Theorem 3** (pp. 174–175), with explicit hypotheses. -/
theorem theorem3_arc [CompactSpace X] {f : X → unitInterval} (hfc : Continuous f)
    (hfs : Function.Surjective f) (hfib : ∀ t, IsPreconnected (f ⁻¹' {t}))
    (hS : IsSnakeLike (univ : Set X)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (D : Chain X (m + 1)), IsEpsChain D ε ∧ univ ⊆ D.union ∧
      (D.link 0 ∩ f ⁻¹' {0}).Nonempty ∧ (D.link (Fin.last m) ∩ f ⁻¹' {1}).Nonempty := by
  set g₀ := f ⁻¹' {0} with hg₀def
  set g₁ := f ⁻¹' {1} with hg₁def
  have hg₀ : IsPreconnected g₀ := hfib 0
  have hg₁ : IsPreconnected g₁ := hfib 1
  have hg₀ne : g₀.Nonempty := (hfs 0).imp fun x hx => hx
  have hg₁ne : g₁.Nonempty := (hfs 1).imp fun x hx => hx
  have hg₀c : IsCompact g₀ := (isClosed_singleton.preimage hfc).isCompact
  have hg₁c : IsCompact g₁ := (isClosed_singleton.preimage hfc).isCompact
  have h01 : (0 : unitInterval) ≠ 1 := fun h => by
    have := congrArg Subtype.val h; simp at this
  obtain ⟨ρ, hρ, hρsep⟩ := exists_sep_of_disjoint hg₀c hg₁c
    (Set.disjoint_left.2 fun x hx hx' => h01 ((show f x = 0 from hx).symm.trans hx'))
  set δ := min (ε / 2) (ρ / 4) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  obtain ⟨n, E, hE, hEcov⟩ := hS.2 δ hδ
  have hsubE : ∀ S : Set X, S ⊆ E.union := fun S => (subset_univ S).trans hEcov
  obtain ⟨i, j, hij, h0E⟩ := exists_trim E hg₀ hg₀ne (hsubE g₀)
  obtain ⟨r, s, hrs, h1E⟩ := exists_trim E hg₁ hg₁ne (hsubE g₁)
  have h0E' : ∀ t, (g₀ ∩ E.link t).Nonempty ↔ (i ≤ t ∧ t ≤ j) := fun t => by
    rw [Fin.le_def, Fin.le_def]; exact h0E t
  have h1E' : ∀ t, (g₁ ∩ E.link t).Nonempty ↔ (r ≤ t ∧ t ≤ s) := fun t => by
    rw [Fin.le_def, Fin.le_def]; exact h1E t
  -- `a` and `b`
  have hV₀o : IsOpen (segUnion E i j) := isOpen_iUnion fun t => isOpen_iUnion fun _ => E.isOpen t
  have hV₁o : IsOpen (segUnion E r s) := isOpen_iUnion fun t => isOpen_iUnion fun _ => E.isOpen t
  have hg₀V : g₀ ⊆ segUnion E i j := fun x hx => by
    obtain ⟨t, ht⟩ := exists_link_of_mem_union (hsubE g₀ hx)
    exact mem_iUnion₂.2 ⟨t, (h0E' t).1 ⟨x, hx, ht⟩, ht⟩
  have hg₁V : g₁ ⊆ segUnion E r s := fun x hx => by
    obtain ⟨t, ht⟩ := exists_link_of_mem_union (hsubE g₁ hx)
    exact mem_iUnion₂.2 ⟨t, (h1E' t).1 ⟨x, hx, ht⟩, ht⟩
  have hK₀ : (f '' (segUnion E i j)ᶜ)ᶜ ∈ 𝓝 (0 : unitInterval) := by
    refine (hfc.isClosedMap _ hV₀o.isClosed_compl).isOpen_compl.mem_nhds ?_
    rintro ⟨x, hx, hx0⟩; exact hx (hg₀V hx0)
  have hK₁ : (f '' (segUnion E r s)ᶜ)ᶜ ∈ 𝓝 (1 : unitInterval) := by
    refine (hfc.isClosedMap _ hV₁o.isClosed_compl).isOpen_compl.mem_nhds ?_
    rintro ⟨x, hx, hx1⟩; exact hx (hg₁V hx1)
  obtain ⟨u, hu, hu0⟩ := exists_Ico_subset_of_mem_nhds' hK₀ (show (0 : unitInterval) < 1 by
    rw [← Subtype.coe_lt_coe]; simp)
  obtain ⟨l, hl, hl1⟩ := exists_Ioc_subset_of_mem_nhds' hK₁ (show (0 : unitInterval) < 1 by
    rw [← Subtype.coe_lt_coe]; simp)
  have hu' : (0 : ℝ) < u := hu.1
  have hl' : (l : ℝ) < 1 := hl.2
  set a : unitInterval := ⟨(u : ℝ) / 2, by constructor <;> linarith [u.2.2]⟩
  set b : unitInterval := ⟨((l : ℝ) + 1) / 2, by constructor <;> linarith [l.2.1]⟩
  have ha0 : (0 : ℝ) < a := by show (0 : ℝ) < (u : ℝ) / 2; linarith
  have hb1 : (b : ℝ) < 1 := by show ((l : ℝ) + 1) / 2 < 1; linarith
  have ha : f ⁻¹' Icc 0 a ⊆ segUnion E i j := by
    intro x hx
    by_contra hxV
    have hxu : f x ∈ Ico 0 u := ⟨unitInterval.nonneg', by
      rw [← Subtype.coe_lt_coe]
      have : (f x : ℝ) ≤ (u : ℝ) / 2 := hx.2
      linarith⟩
    exact hu0 hxu ⟨x, hxV, rfl⟩
  have hb : f ⁻¹' Icc b 1 ⊆ segUnion E r s := by
    intro x hx
    by_contra hxV
    have hxl : f x ∈ Ioc l 1 := ⟨by
      rw [← Subtype.coe_lt_coe]
      have : ((l : ℝ) + 1) / 2 ≤ f x := hx.1
      linarith, unitInterval.le_one'⟩
    exact hl1 hxl ⟨x, hxV, rfl⟩
  -- `σ₀`, `σ₁`
  obtain ⟨σ₀, hσ₀, hσ₀sep⟩ := exists_sep_of_disjoint hg₀c (isCompact_preimage_Icc hfc a 1)
    (Set.disjoint_left.2 fun x hx hx' => by
      have h1 : (a : ℝ) ≤ f x := hx'.1
      rw [show f x = 0 from hx] at h1; simp at h1; linarith)
  obtain ⟨σ₁, hσ₁, hσ₁sep⟩ := exists_sep_of_disjoint hg₁c (isCompact_preimage_Icc hfc 0 b)
    (Set.disjoint_left.2 fun x hx hx' => by
      have h1 : (f x : ℝ) ≤ b := hx'.2
      rw [show f x = 1 from hx] at h1; simp at h1; linarith)
  -- the Lebesgue number of `E`
  obtain ⟨lam, hlam, hlamE⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun t => E.isOpen t) hEcov
  set γ := min (min (lam / 2) (min σ₀ σ₁)) (min (ε / 2) (ρ / 8)) with hγdef
  have hγ : 0 < γ := lt_min (lt_min (by linarith) (lt_min hσ₀ hσ₁))
    (lt_min (by linarith) (by linarith))
  have hγ1 : γ ≤ lam / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hγ2 : γ ≤ σ₀ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγ3 : γ ≤ σ₁ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hγ4 : γ ≤ ε / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hγ5 : γ ≤ ρ / 8 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N, F, hF, hFcov⟩ := hS.2 γ hγ
  have hsubF : ∀ S : Set X, S ⊆ F.union := fun S => (subset_univ S).trans hFcov
  -- orientation of `F`
  obtain ⟨t₀, t₁, ht01, hT⟩ := exists_trim F hg₀ hg₀ne (hsubF g₀)
  obtain ⟨u₀, u₁, hu01, hU⟩ := exists_trim F hg₁ hg₁ne (hsubF g₁)
  have hnot : ∀ k : Fin N, ¬ ((g₀ ∩ F.link k).Nonempty ∧ (g₁ ∩ F.link k).Nonempty) := by
    rintro k ⟨⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩⟩
    have := hρsep x hx y hy
    have := lt_of_le_of_lt (dist_le_diam_of_mem (hF k).1 hxk hyk) (hF k).2
    linarith
  have hsep' : ∀ x ∈ g₀, ∀ y ∈ f ⁻¹' Icc a 1, γ ≤ dist x y := fun x hx y hy =>
    hγ2.trans (hσ₀sep x hx y hy)
  have hsep'' : ∀ x ∈ g₁, ∀ y ∈ f ⁻¹' Icc 0 b, γ ≤ dist x y := fun x hx y hy =>
    hγ3.trans (hσ₁sep x hx y hy)
  have hcases : (t₁ : ℕ) < u₀ ∨ (u₁ : ℕ) < t₀ := by
    by_contra hcon
    push_neg at hcon
    have hm : max (t₀ : ℕ) u₀ < N := max_lt t₀.isLt u₀.isLt
    rw [Fin.le_def] at ht01 hu01
    refine hnot ⟨max (t₀ : ℕ) u₀, hm⟩ ⟨(hT _).2 ⟨le_max_left _ _, ?_⟩,
      (hU _).2 ⟨le_max_right _ _, ?_⟩⟩
    · exact max_le ht01 hcon.1
    · exact max_le hcon.2 hu01
  rcases hcases with h | h
  · refine theorem3_of_chains E F hfc hfs hfib hE hF hFcov hij hrs h0E' h1E' hρsep
      (min_le_right _ _) hγ5 (min_le_left _ _) hγ4 (fun x => hlamE x (mem_univ x)) (by linarith) ha hb hsep' hsep'' ?_
    intro k k' hk hk'
    have h1 := (hT k).1 (by rwa [inter_comm] at hk)
    have h2 := (hU k').1 (by rwa [inter_comm] at hk')
    rw [Fin.lt_def]; omega
  · refine theorem3_of_chains E F.reverse hfc hfs hfib hE (isEpsChain_reverse hF)
      ((union_reverse F).symm ▸ hFcov) hij hrs h0E' h1E' hρsep
      (min_le_right _ _) hγ5 (min_le_left _ _) hγ4 (fun x => hlamE x (mem_univ x)) (by linarith) ha hb hsep' hsep'' ?_
    intro k k' hk hk'
    rw [Chain.reverse_link] at hk hk'
    have h1 := (hT _).1 (by rwa [inter_comm] at hk)
    have h2 := (hU _).1 (by rwa [inter_comm] at hk')
    rw [Fin.val_rev] at h1 h2
    rw [Fin.lt_def]; omega

end HPC.BJ59
