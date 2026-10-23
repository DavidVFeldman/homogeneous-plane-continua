import HPC.Jones.CutPoints
import HPC.Effros.Effros

/-!
# Batch 135: Jones 1951, the Lemma

F. B. Jones, *Certain homogeneous unicoherent indecomposable continua*, Proc. AMS 2 (1951),
855–859: the sets `U_x` and the Lemma (`U_y` is never a proper subset of `U_x` in a homogeneous
continuum).

**The proof here is not Jones's.** Jones runs a transfinite sequence of points through all
countable ordinals, with `U_{xᵢ}` strictly decreasing, and contradicts it with second
countability. Here the transfinite recursion is replaced by one lower semicontinuous function:
with `B₀, B₁, …` a countable base,
`g w = ∑ₖ [closure Bₖ ⊆ U_w] · 2⁻ᵏ`.
Each term is the indicator of an open set (Theorem 1 of 1948 in the form
`isClosed_exists_not_aposAt_left`), so `g` is lower semicontinuous and attains its minimum on the
compact `X` at some `w₀`; and `U_a ⊊ U_b` forces `g a < g b`. If `U_y ⊊ U_x`, a homeomorphism `T`
with `T x = w₀` gives `U_{T y} = T(U_y) ⊊ T(U_x) = U_{w₀}`, so `g (T y) < g w₀`: a contradiction.

Jones 1951, Theorem 1 (homogeneous + hereditarily unicoherent ⇒ indecomposable) was left open in
batch 135; it is **proved** in batch 136 by a different route (an irreducible continuum, not
Jones's decomposition space): `HPC.Jones.jones51_theorem1` in `HPC/Jones/Jones51Thm1.lean`.
-/

namespace HPC.Jones

open Set Topology Filter Metric ENNReal

variable {X : Type*} [MetricSpace X]

/-- Jones 1951's `U_x`: the points `z ≠ x` at which `X` is aposyndetic with respect to `x`. It is
open (Jones: \"It is evident\"). Jones 1955's `U_x = M − L_x`. -/
def aposSet (x : X) : Set X := {z | z ≠ x ∧ AposAt z x}

/-- `U_x` is the set of points at which `X` is aposyndetic with respect to `x` (aposyndesis with
respect to `x` already forces `z ≠ x`). -/
theorem aposSet_eq (x : X) : aposSet x = {z | AposAt z x} := by
  ext z
  exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩

theorem isOpen_aposSet (x : X) : IsOpen (aposSet x) := by
  rw [aposSet_eq]
  exact isOpen_aposAt_left x

/-- `X` is **homogeneous**. -/
def IsHomogeneous (X : Type*) [TopologicalSpace X] : Prop := ∀ x y : X, ∃ h : X ≃ₜ X, h x = y

omit [MetricSpace X] in
/-- `IsHomogeneous X` is the hypothesis `hom` of `HPC.Effros.effros_homogeneous`, and is Mathlib's
transitivity of the evaluation action `HPC.Effros.homeoMulAction` of the homeomorphism group. -/
theorem isHomogeneous_iff_isPretransitive [TopologicalSpace X] :
    IsHomogeneous X ↔ MulAction.IsPretransitive (X ≃ₜ X) X :=
  ⟨fun h => ⟨fun x y => h x y⟩, fun h x y => h.exists_smul_eq x y⟩

/-- A homeomorphism carries `U_x` onto `U_{T x}`. -/
theorem aposSet_homeomorph (T : X ≃ₜ X) (x : X) : aposSet (T x) = T '' aposSet x := by
  ext z
  rw [aposSet_eq, aposSet_eq]
  constructor
  · intro h
    refine ⟨T.symm z, ?_, T.apply_symm_apply z⟩
    show AposAt (T.symm z) x
    rw [← aposAt_homeomorph_iff T, T.apply_symm_apply]
    exact h
  · rintro ⟨a, ha, rfl⟩
    exact (aposAt_homeomorph_iff T).mpr ha

variable [CompactSpace X]

/-- For a closed `K`, the points `w` with `K ⊆ U_w` form an open set. -/
theorem isOpen_setOf_subset_aposSet {K : Set X} (hK : IsClosed K) :
    IsOpen {w : X | K ⊆ aposSet w} := by
  have h : {w : X | K ⊆ aposSet w} = {y : X | ∃ x ∈ K, ¬ AposAt x y}ᶜ := by
    ext w
    simp only [aposSet_eq, mem_setOf_eq, mem_compl_iff, not_exists, not_and, not_not,
      subset_def]
  rw [h]
  exact (isClosed_exists_not_aposAt_left hK).isOpen_compl

/-- **The replacement for Jones's transfinite sequence.** A lower semicontinuous function, strictly
monotone along proper inclusion of the sets `U_w`. -/
theorem exists_lsc_strictMono_aposSet [Nonempty X] :
    ∃ g : X → ℝ≥0∞, LowerSemicontinuous g ∧ ∀ a b : X, aposSet a ⊂ aposSet b → g a < g b := by
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis X
  have hBne : B.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have := hB.sUnion_eq
    rw [hne, sUnion_empty] at this
    exact empty_ne_univ this
  obtain ⟨f, rfl⟩ := hBc.exists_eq_range hBne
  set term : ℕ → X → ℝ≥0∞ := fun k =>
    {w : X | closure (f k) ⊆ aposSet w}.indicator (fun _ => (2⁻¹ : ℝ≥0∞) ^ k) with hterm
  refine ⟨fun w => ∑' k, term k w, lowerSemicontinuous_tsum fun k =>
    (isOpen_setOf_subset_aposSet isClosed_closure).lowerSemicontinuous_indicator (zero_le _), ?_⟩
  intro a b hab
  have hmono : ∀ k, term k a ≤ term k b := by
    intro k
    by_cases hk : closure (f k) ⊆ aposSet a
    · have hk' : closure (f k) ⊆ aposSet b := hk.trans hab.1
      simp only [hterm, indicator_of_mem (show a ∈ {w : X | closure (f k) ⊆ aposSet w} from hk),
        indicator_of_mem (show b ∈ {w : X | closure (f k) ⊆ aposSet w} from hk'), le_refl]
    · simp only [hterm, indicator_of_notMem (show a ∉ {w : X | closure (f k) ⊆ aposSet w} from hk),
        zero_le]
  obtain ⟨v, hvb, hva⟩ := exists_of_ssubset hab
  obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.mp (isOpen_aposSet b) v hvb
  obtain ⟨t, ⟨k, rfl⟩, hvt, hts⟩ := hB.mem_nhds_iff.mp (ball_mem_nhds v (half_pos hr))
  have hcl : closure (f k) ⊆ aposSet b := by
    refine (isClosed_closedBall.closure_subset_iff.mpr (hts.trans ball_subset_closedBall)).trans ?_
    exact (closedBall_subset_ball (half_lt_self hr)).trans hrb
  have hncl : ¬ closure (f k) ⊆ aposSet a := fun h => hva (h (subset_closure hvt))
  have hfin : ∑' k, term k a ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k) ?_ (ENNReal.tsum_le_tsum ?_)
    · rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.ofNat_ne_top
    · intro j
      exact indicator_le_self' (fun _ _ => zero_le _) a
  refine ENNReal.tsum_lt_tsum (i := k) hfin hmono ?_
  simp only [hterm, indicator_of_notMem (show a ∉ {w : X | closure (f k) ⊆ aposSet w} from hncl),
    indicator_of_mem (show b ∈ {w : X | closure (f k) ⊆ aposSet w} from hcl)]
  exact ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) k

/-- **Jones 1951, Lemma.** If `X` is homogeneous, then `U_y` is not a proper subset of `U_x`.

*Shape change:* the skeleton's `hxy : x ≠ y` is dropped (for `x = y` the claim is trivial, and the
proof does not use it). *Proof change:* Jones's transfinite recursion through the countable
ordinals is replaced by the minimum of the lower semicontinuous function of
`exists_lsc_strictMono_aposSet` (see the module docstring). -/
theorem jones51_lemma (hX : IsHomogeneous X) {x y : X} : ¬ (aposSet y ⊂ aposSet x) := by
  intro hlt
  haveI : Nonempty X := ⟨x⟩
  obtain ⟨g, hg, hstrict⟩ := exists_lsc_strictMono_aposSet (X := X)
  obtain ⟨w₀, -, hmin⟩ :=
    (hg.lowerSemicontinuousOn univ).exists_isMinOn univ_nonempty isCompact_univ
  obtain ⟨T, hT⟩ := hX x w₀
  have hlt' : aposSet (T y) ⊂ aposSet w₀ := by
    rw [← hT, aposSet_homeomorph, aposSet_homeomorph]
    refine ssubset_iff_subset_ne.mpr ⟨image_mono hlt.1, fun he => hlt.ne ?_⟩
    exact T.injective.image_injective he
  exact (hstrict _ _ hlt').not_ge (isMinOn_iff.mp hmin _ (mem_univ _))

/-! ### Jones 1951, Theorem 1

Left open in batch 135 (Jones's last paragraph treats an upper semicontinuous decomposition as a
compact metric continuum and applies Whyburn 1939, Theorem 6.21). **Proved in batch 136** without
the decomposition space, by an irreducible continuum: `HPC.Jones.jones51_theorem1`
(`HPC/Jones/Jones51Thm1.lean`), which uses the Lemma above.
-/

end HPC.Jones
