import HPC.Hagopian.H76Cut

/-!
# Batch 176, items C and E: the T12 package, Property 4, and the closing contradiction

* `T12Data` — the output of T12 and T13 in one structure (commission 176 §1.C): the point `p ∈ K`,
  the `ε₃/2`-homeomorphisms `h`, `h₁` (so `f = h₁h⁻¹`), T12 (2) (the closure of the `p`-component of
  `M ∩ π⁻¹[D]` is essential to `h[R(E)]`), and Hagopian's `F` with its decomposition `d`,
  separating `p` from `f(p)` in `π⁻¹[D]` and irreducible with respect to that (T13);
* `Property4` — Property 4 (p. 348) for an interval `[x, y]`, as a `Prop` on a `T12Data`;
* `property4_top_of_sepByCrossing` — Property 4 for the block above a gap of `St J`, from
  `SepByCrossing`;
* `not_property4_E` — `[x₁, x₂]` does not have Property 4;
* `false_of_property4_chain` — the closing contradiction (p. 348: "The resulting contradiction will
  complete our proof"): Property 4 for the top block and the induction step contradict the base.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Prop4

variable {M : Set Pt}

/-- **The T12 package** (commission 176 §1.C: "package `(K, h, h₁, f, p, F, d, xᵢ)` into one
structure"). `K` is Hagopian's arc component over `⟨p₃, q₃⟩` (here any subset of `M`), `p ∈ K`,
`h`, `h₁` are `ε₃/2`-homeomorphisms, `f = h₁h⁻¹` (`T12Data.f`); T12 (2) is `ess`; `G`, `d` are
Hagopian's `F` and its decomposition, with `d⁻¹(0) = k⁻¹(0)`, separating `p` from `f(p)` in
`π⁻¹[D]` and irreducible with respect to that (T13). The blocks `xᵢ` are determined by `d` and `I`
and are not fields. -/
structure T12Data (E : Set M) (k : E → unitInterval) (π : Pt → Pt) (F : ℝ × ℝ → Pt)
    (D' : Set (ℝ × ℝ)) (ε₃ : ℝ) where
  K : Set M
  h : M ≃ₜ M
  h₁ : M ≃ₜ M
  p : M
  p_mem : p ∈ K
  h_small : ∀ v, dist (h v) v < ε₃ / 2
  h₁_small : ∀ v, dist (h₁ v) v < ε₃ / 2
  ess : IsEssential k (h ⁻¹' (Subtype.val ⁻¹'
    closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (p : Pt))))
  G : Set M
  d : G → unitInterval
  hG : IsMinimalAdmissible G d
  hEG : E ⊆ G
  hX0 : layer d 0 = layer k 0
  sep : SepIn (π ⁻¹' (F '' D')) (toPt G) p ((h.symm.trans h₁) p)
  irr : ∀ F', IsExtensionAway E (layer k 0) F' →
    SepIn (π ⁻¹' (F '' D')) (toPt F') p ((h.symm.trans h₁) p) → F' ⊆ G → F' = G

variable {E : Set M} {k : E → unitInterval} {π : Pt → Pt} {F : ℝ × ℝ → Pt} {D' : Set (ℝ × ℝ)}
  {ε₃ : ℝ}

/-- `f = h₁h⁻¹` (T12 (1)). -/
def T12Data.f (D : T12Data E k π F D' ε₃) : M ≃ₜ M := D.h.symm.trans D.h₁

/-- `f` is an `ε₃`-homeomorphism. -/
theorem T12Data.f_small (D : T12Data E k π F D' ε₃) (v : M) : dist (D.f v) v < ε₃ := by
  have h1 := D.h₁_small (D.h.symm v)
  have h2 := D.h_small (D.h.symm v)
  rw [D.h.apply_symm_apply] at h2
  calc dist (D.f v) v ≤ dist (D.h₁ (D.h.symm v)) (D.h.symm v) + dist (D.h.symm v) v :=
        dist_triangle _ _ _
    _ < ε₃ / 2 + ε₃ / 2 := add_lt_add h1 (by rw [dist_comm]; exact h2)
    _ = ε₃ := by ring

/-- **Property 4** (p. 348) for the interval `[x, y]`: "There exists a point `yₙ` of `K` such that
(1) the closure of the `yₙ`-component `Cₙ` of `M ∩ π⁻¹[D]` is essential to `h[R(E)]`, and (2)
`d⁻¹[[x, y]]` separates `yₙ` from `f(yₙ)` in `π⁻¹[D]`." "Essential to `h[R(E)]`" is rendered as in
Lemma 7 and Property 2: `h⁻¹` of the set is essential to `R(E)`. -/
def Property4 (D : T12Data E k π F D' ε₃) (x y : unitInterval) : Prop :=
  ∃ yₙ ∈ D.K, IsEssential k (D.h ⁻¹' (Subtype.val ⁻¹'
      closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (yₙ : Pt)))) ∧
    SepIn (π ⁻¹' (F '' D')) (toPt (layerSet D.d (Icc x y))) yₙ (D.f yₙ)

/-- **`[x₁, x₂]` does not have Property 4** (p. 348), from `hagopian76_property4_base`: the block
`d⁻¹[[0, e]] = E` separates no two points of `π⁻¹[D]`. -/
theorem not_property4_E {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) (hF : IsCollar γ F) {c₁ : ℝ} (hc₁ : c₁ ≤ 1)
    (hR : IsCrossRegion M π F c₁ D') (hD'c : IsPreconnected D') (D : T12Data E k π F D' ε₃)
    {e : unitInterval} (he : layerSet D.d (Icc 0 e) = E) : ¬ Property4 D 0 e := by
  rintro ⟨y, -, -, hsep⟩
  exact hagopian76_property4_base hπ hπS hγπ hF hc₁ hR hD'c he _ _ hsep

/-- **The closing contradiction** (p. 348: "we now show that if `I = [x₂ᵢ₋₁, x₂ᵢ]` has Property 4,
then so does `J = [x₂ᵢ₋₃, x₂ᵢ₋₂]`. The resulting contradiction will complete our proof").
Abstract form: if the top block `[x₂ₙ₋₁, x₂ₙ]` has Property 4, every step `i → i − 1`
(`2 ≤ i ≤ n`) preserves it, and `[x₁, x₂]` does not have it, then `False`. -/
theorem false_of_property4_chain (D : T12Data E k π F D' ε₃) (x : ℕ → unitInterval) (n : ℕ)
    (hn : 1 ≤ n) (htop : Property4 D (x (2 * n - 1)) (x (2 * n)))
    (hstep : ∀ i, 2 ≤ i → i ≤ n → Property4 D (x (2 * i - 1)) (x (2 * i)) →
      Property4 D (x (2 * i - 3)) (x (2 * i - 2)))
    (hbase : ¬ Property4 D (x 1) (x 2)) : False := by
  have key : ∀ j, j + 1 ≤ n → Property4 D (x (2 * (n - j) - 1)) (x (2 * (n - j))) := by
    intro j
    induction j with
    | zero => intro _; simpa using htop
    | succ j ih =>
      intro hj
      have h := hstep (n - j) (by omega) (by omega) (ih (by omega))
      have e1 : 2 * (n - j) - 3 = 2 * (n - (j + 1)) - 1 := by omega
      have e2 : 2 * (n - j) - 2 = 2 * (n - (j + 1)) := by omega
      rwa [e1, e2] at h
  have h := key (n - 1) (by omega)
  have e1 : 2 * (n - (n - 1)) - 1 = 1 := by omega
  have e2 : 2 * (n - (n - 1)) = 2 := by omega
  rw [e1, e2] at h
  exact hbase h

variable [CompactSpace M] [ConnectedSpace M]

/-- **C. Property 4 for the block above a gap, from `SepByCrossing`** (p. 348: "The interval
`[x₂ₙ₋₁, x₂ₙ]` has the following property"). With `yₙ = p` (commission 176 §1.C: "The base of the
induction takes `yₙ = p`"): clause (1) is T12 (2) (`T12Data.ess`); clause (2) is `sepIn_above_gap`.
For `s₁ = x₂ₙ₋₂`, `s₂ = x₂ₙ₋₁` and `x₂ₙ = 1` (`hagopian76_x2n_eq_one_of_sepByCrossing`) this is
Property 4 for `[x₂ₙ₋₁, x₂ₙ]`. -/
theorem property4_top_of_sepByCrossing (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : T12Data E k π F D' ε₃) {c₁ : ℝ} {Y : Set Pt} (hY : IsCompact Y) (hYc : IsConnected Y)
    (hYO : Disjoint Y (π ⁻¹' (F '' D'))) (hfr : frontier (π ⁻¹' (F '' D')) ⊆ Y)
    (hSBC : SepByCrossing D.G π F c₁ D' (π ⁻¹' (F '' D')) D.p (D.f D.p))
    {s₁ s₂ : unitInterval} (h0 : 0 < s₁) (h12 : s₁ < s₂) (hEs : E ⊆ layerSet D.d (Icc 0 s₁))
    (hgap : ∀ r ∈ crossingIntervals D.d π F c₁ D', r.2 ≤ s₁ ∨ s₂ ≤ r.1) :
    Property4 D s₂ 1 :=
  ⟨D.p, D.p_mem, D.ess, sepIn_above_gap hX hi D.hG D.hX0 hY hYc hYO hfr D.sep D.irr hSBC h0 h12
    hEs hgap⟩

end Prop4

end HPC.Hagopian
