import HPC.BJ59.BJ59D
import HPC.Plane.Descr
import HPC.PseudoArc.Theorem10

/-!
# Batch 202: Part G, V — a plane circle of pseudo-arcs

The skeleton of commission 202 (`doc/batches/COMMISSION-batch202.md`). Bing–Jones §7
(pp. 189–191) asserts a plane circle of pseudo-arcs without constructing it. This batch constructs
one by a route that is not Bing–Jones's (commission §1):

* §2 circular descriptions: nested circular chains whose links carry arcs of the base circle;
* §3 the recognition theorem: a circular description describes a circle of pseudo-arcs;
* §4 sweep patterns: explicit patterns satisfying the conditions of §2;
* §5 the circular planar step: tame circular chains in the plane realize those patterns;
* §6 the assembly, `BJPlaneExample`, and the classification with no named hypothesis.

Source: R. H. Bing and F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959),
§7, pp. 189–191 (`doc/sources/bing-jones1959.pdf`; PDF page `n` is journal page `169 + n`).
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.HO16

/-! ## §2. Circular descriptions -/

/-- **A circular description** in `X` (commission §2). Level `k` is a circular chain of `N k`
links `L k t`, indexed by integers read modulo `N k`. Level `k + 1` refines level `k` along the
lifted pattern `pat k` (degree one: `pat k (t + N (k+1)) = pat k t + N k`), with closures nested
and tightness. Link `t` of level `k` carries the closed arc of the base circle `ℝ / ℤ` of length
`lam k` centred at `o k + t / N k` (lifted to `ℝ`; the arcs are labels, not geometry). The arcs
of new links lie in the arcs of their images (`arcNest`); every point of a shrunk arc is in the
shrunk arc of a child (`surv`); and the lifted patterns are crooked on every window a run of
level `k + 1` can occupy (`crook`). -/
structure CircDescr (X : Type*) [MetricSpace X] where
  /-- the number of links of level `k` -/
  N : ℕ → ℕ
  four_le : ∀ k, 4 ≤ N k
  /-- link `t` of level `k` -/
  L : ℕ → ℤ → Set X
  isOpen_L : ∀ k t, IsOpen (L k t)
  periodic : ∀ k (t : ℤ), L k (t + N k) = L k t
  meet_iff : ∀ k s t, (L k s ∩ L k t).Nonempty ↔ ∃ n : ℤ, |s - t - n * (N k : ℤ)| ≤ 1
  preconn : ∀ k t, IsPreconnected (L k t)
  /-- a compact set containing every link -/
  K : Set X
  isCompact_K : IsCompact K
  L_subset : ∀ k t, L k t ⊆ K
  /-- a mesh bound tending to zero -/
  ε : ℕ → ℝ
  ε_tendsto : Tendsto ε atTop (𝓝 0)
  diam_le : ∀ k t, diam (L k t) ≤ ε k
  /-- the lifted pattern of level `k + 1` in level `k` -/
  pat : ℕ → ℤ → ℤ
  pat_period : ∀ k (t : ℤ), pat k (t + N (k + 1)) = pat k t + N k
  pat_step : ∀ k t, |pat k (t + 1) - pat k t| ≤ 1
  nest : ∀ k t, closure (L (k + 1) t) ⊆ L k (pat k t)
  tight : ∀ k t l, (L (k + 1) t ∩ L k l).Nonempty →
    ∃ t' n : ℤ, |t' - t| ≤ 1 ∧ pat k t' = l + n * (N k : ℤ)
  /-- the offset of the centres of level `k` -/
  o : ℕ → ℝ
  /-- the length of the arcs of level `k` -/
  lam : ℕ → ℝ
  lam_tendsto : Tendsto lam atTop (𝓝 0)
  five_le_lam : ∀ k, 5 ≤ lam k * N k
  lam_add_four_le : ∀ k, lam k * N k + 4 ≤ N k
  arcNest : ∀ k (t : ℤ),
    |(o (k + 1) + (t : ℝ) / N (k + 1)) - (o k + (pat k t : ℝ) / N k)| ≤
      (lam k - lam (k + 1)) / 2
  surv : ∀ k (l : ℤ) (y : ℝ), |y - (o k + (l : ℝ) / N k)| ≤ lam k / 2 - 1 / (2 * N k) →
    ∃ t : ℤ, pat k t = l ∧
      |y - (o (k + 1) + (t : ℝ) / N (k + 1))| ≤ lam (k + 1) / 2 - 1 / (2 * N (k + 1))
  crook : ∀ k (a : ℤ),
    HPC.Fold.PatCrookedOn (fun u : ℕ => pat k (a + u)) 0 (⌈lam (k + 1) * N (k + 1)⌉₊ + 3)

namespace CircDescr

variable {X : Type*} [MetricSpace X] (Δ : CircDescr X)

/-- The continuum described: the intersection of the unions of the levels. -/
def M : Set X := ⋂ k, ⋃ t, Δ.L k t

/-- The fibre over `y` (commission (3.4)): the intersection over the levels of the union of the
links whose arcs contain `y`. By periodicity of `L`, unshifted centres suffice. -/
def fib (y : ℝ) : Set X :=
  ⋂ k, ⋃ (t : ℤ) (_ : |y - (Δ.o k + (t : ℝ) / Δ.N k)| ≤ Δ.lam k / 2), Δ.L k t

/-! ## §3. The recognition theorem -/

/-- (3.1) -/
theorem isCompact_M : IsCompact Δ.M := by
  sorry

/-- (3.2) Consecutive links meet in `M`. -/
theorem inter_M_nonempty (k : ℕ) (t : ℤ) : (Δ.L k t ∩ Δ.L k (t + 1) ∩ Δ.M).Nonempty := by
  sorry

/-- (3.5) **Survival**: the fibre over a point of a shrunk arc meets the link. -/
theorem fib_meets (k : ℕ) (l : ℤ) (y : ℝ)
    (hy : |y - (Δ.o k + (l : ℝ) / Δ.N k)| ≤ Δ.lam k / 2 - 1 / (2 * Δ.N k)) :
    (Δ.fib y ∩ Δ.L k l).Nonempty := by
  sorry

/-- **The recognition theorem** (commission §3): a circular description describes a circle of
pseudo-arcs. -/
theorem isCircleOfPA : IsCircleOfPA Δ.M := by
  sorry

end CircDescr

/-! ## §4. Sweep patterns -/

/-- The number of new links per old link in the sweep pattern with window parameter `m` and
stutter multiplier `S` (commission §4.2): `Q = 6 S z(m−2) z(m−1)`. -/
def sweepQ (m S : ℕ) : ℕ := 6 * S * HPC.Fold.z (m - 2) * HPC.Fold.z (m - 1)

/-- **The sweep pattern** (commission §4.2–4.3). New link `t` sits at `1/4 + t / Q` in units of
old links. The clauses: period; unit steps; `S`-slow; nesting (window radius `m/2 − 1/4`);
survival; crookedness on every window of `Q/2 + 4` indices. The sweep lemma (§4.1), in a shape of
your choice, is the main tool. -/
theorem exists_sweepPattern (m S : ℕ) (hm : 5 ≤ m) (hS : 1 ≤ S) :
    ∃ x : ℤ → ℤ,
      (∀ t : ℤ, x (t + sweepQ m S) = x t + 1) ∧
      (∀ t, |x (t + 1) - x t| ≤ 1) ∧
      (∀ s t, x s + 2 ≤ x t → (S : ℤ) ≤ |s - t|) ∧
      (∀ t, |(x t : ℝ) - (1 / 4 + (t : ℝ) / sweepQ m S)| ≤ (m : ℝ) / 2 - 1 / 4) ∧
      (∀ (l : ℤ) (y : ℝ), |y - l| ≤ (m : ℝ) / 2 - 1 / 2 →
        ∃ t, x t = l ∧
          |y - (1 / 4 + (t : ℝ) / sweepQ m S)| ≤ 1 / 4 - 1 / (2 * (sweepQ m S : ℝ))) ∧
      (∀ a : ℤ, HPC.Fold.PatCrookedOn (fun u : ℕ => x (a + u)) 0 (sweepQ m S / 2 + 3)) := by
  sorry

/-! ## §5. The circular planar step -/

/-- The standard rectangle `(2t, 2t + 3) × (0, 1)`, for an integer `t`. -/
def stdRectZ (t : ℤ) : Set Pt := Ioo (2 * (t : ℝ)) (2 * t + 3) ×ˢ Ioo 0 1

/-- The overlap zone of `stdRectZ t` and `stdRectZ (t + 1)`, widened as batch 84's `zone`. -/
def zoneZ (t : ℤ) : Set Pt := Icc (2 * (t : ℝ) + 8 / 5) (2 * t + 17 / 5) ×ˢ Icc 0 1

/-- The covering map of the plane minus the origin, of period `2N` in the first coordinate:
`(u, v) ↦ e^v (cos (π u / N), sin (π u / N))`. -/
noncomputable def circExp (N : ℕ) (p : Pt) : Pt :=
  (Real.exp p.2 * Real.cos (Real.pi * p.1 / N), Real.exp p.2 * Real.sin (Real.pi * p.1 / N))

/-- Link `t` of the standard circular chain of `N` links: a polar rectangle. -/
noncomputable def stdCircLink (N : ℕ) (t : ℤ) : Set Pt := circExp N '' stdRectZ t

/-- Zone `t` of the standard circular chain of `N` links. -/
noncomputable def stdCircZone (N : ℕ) (t : ℤ) : Set Pt := circExp N '' zoneZ t

/-- The standard circular chain is a circular chain. -/
theorem stdCircLink_meet_iff {N : ℕ} (hN : 4 ≤ N) (s t : ℤ) :
    (stdCircLink N s ∩ stdCircLink N t).Nonempty ↔ ∃ n : ℤ, |s - t - n * (N : ℤ)| ≤ 1 := by
  sorry

/-- **The circular planar step** (commission §5), the analogue of `real_step`: a slow lifted
pattern of degree one with bounded drift is realized by a tame circular chain, with closures
nested, tightness, and small links or links inside old zones. -/
theorem circ_step (Φ : Pt ≃ₜ Pt) {N : ℕ} (hN : 4 ≤ N) {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∃ S : ℕ, 12 ≤ S ∧ ∀ (Q : ℕ) (x : ℤ → ℤ) (y₀ : ℝ), 2 ≤ Q →
      (∀ t : ℤ, x (t + Q) = x t + 1) → (∀ t, |x (t + 1) - x t| ≤ 1) →
      (∀ s t, x s + 2 ≤ x t → (S : ℤ) ≤ |s - t|) →
      (∀ t, |(x t : ℝ) - (y₀ + (t : ℝ) / Q)| ≤ B) →
      ∃ ψ : Pt ≃ₜ Pt,
        (∀ t : ℤ,
          closure ((ψ.trans Φ) '' stdCircLink (Q * N) t) ⊆ Φ '' stdCircLink N (x t)) ∧
        (∀ t l : ℤ, ((ψ.trans Φ) '' stdCircLink (Q * N) t ∩ Φ '' stdCircLink N l).Nonempty →
          ∃ t' n : ℤ, |t' - t| ≤ 1 ∧ x t' = l + n * (N : ℤ)) ∧
        (∀ t : ℤ, diam ((ψ.trans Φ) '' stdCircLink (Q * N) t) ≤ ε ∨
          ∃ k : ℤ, (ψ.trans Φ) '' stdCircLink (Q * N) t ⊆ Φ '' stdCircZone N k) ∧
        (∀ t : ℤ, diam ((ψ.trans Φ) '' stdCircZone (Q * N) t) ≤ ε) := by
  sorry

/-! ## §6. The assembly and the classification -/

/-- **A circular description in the plane** (commission §6.1–6.2): levels built alternately by
`exists_sweepPattern` and `circ_step`, from the standard circular chain of 16 links. -/
theorem exists_circDescr_plane : Nonempty (CircDescr Pt) := by
  sorry

/-- **A plane circle of pseudo-arcs** (Bing–Jones §7, by the construction of this batch). -/
theorem bjPlaneExample : BJPlaneExample := by
  obtain ⟨Δ⟩ := exists_circDescr_plane
  exact ⟨Δ.M, Δ.isCircleOfPA⟩

/-- **The classification of homogeneous plane continua with Bing–Jones's third class**, with no
named hypothesis. -/
theorem ho16_classification₄ (M : Set Pt) [CompactSpace M] [ConnectedSpace M]
    (hnt : (univ : Set M).Nontrivial) :
    IsHomogeneous M ↔ Nonempty (M ≃ₜ Circle) ∨ IsPseudoArc (univ : Set M) ∨ IsCircleOfPA M :=
  ho16_classification₃ bjPlaneExample M hnt

/-- **The plane form of the classification**, with no named hypothesis. -/
theorem ho16_classification_plane₄ :
    ∃ C₁ C₂ C₃ : Set Pt,
      (Nonempty (C₁ ≃ₜ Circle) ∧ IsPseudoArc C₂ ∧ IsCircleOfPA C₃) ∧
      (IsHomogeneous C₁ ∧ IsHomogeneous C₂ ∧ IsHomogeneous C₃) ∧
      (IsEmpty (C₁ ≃ₜ C₂) ∧ IsEmpty (C₁ ≃ₜ C₃) ∧ IsEmpty (C₂ ≃ₜ C₃)) ∧
      ∀ M : Set Pt, IsCompact M → IsConnected M → M.Nontrivial →
        (IsHomogeneous M ↔ Nonempty (M ≃ₜ C₁) ∨ Nonempty (M ≃ₜ C₂) ∨ Nonempty (M ≃ₜ C₃)) :=
  ho16_classification_plane₃ bjPlaneExample

/-- **Domokos–Prajs, Theorem 6.1, "if"**, with no named hypothesis. -/
theorem dp22_theorem61' {X Y : Type} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
    {f : X → Circle} (hf : IsAtomicCircPAMap f) (hY : IsCircleOfPA Y) : Nonempty (X ≃ₜ Y) :=
  dp22_theorem61 bjThm10 hf hY

/-- **Domokos–Prajs, Theorem 6.1, both directions**, with no named hypothesis. -/
theorem dp22_theorem61_iff' {X : Type} [MetricSpace X] [CompactSpace X] :
    IsCircleOfPA X ↔ ∃ f : X → Circle, IsAtomicCircPAMap f :=
  dp22_theorem61_iff bjThm10 bjPlaneExample

/-- **The circle-likeness step**, with no named hypothesis. -/
theorem hoCircleLike' : HOCircleLike := hoCircleLike bjThm10 bjPlaneExample

end HPC.BJ59
