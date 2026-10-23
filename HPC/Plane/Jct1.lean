import HPC.Plane.Tree7Comp
import HPC.Fold.Theorem4Ge4

/-!
# Batch 125: the Jordan curve theorem for simple closed polygons, part I — crossing parity;
# and Theorem 4 as printed with at least four coarse links

COMMISSION-batch125.md. The skeleton of the commission with every `sorry` replaced by a proof.
Nothing in this file is `sorry`. Changes of shape (recorded in REPORT-batch125):

* `vertex_rule_placeholder` is deleted. The vertex rule proved is `crossesEast_jump` (per edge:
  near `x`, the indicator is unchanged at points not below `x` and jumps by
  `vJump x a + vJump x b` at points below `x`) together with `sum_vJump_telescope` (the jumps
  cancel mod 2 around a closed polygon).
* The hypothesis `hv : IsSimpleVertices v` is dropped from `parity_locallyConstant`,
  `parity_eq_of_isPreconnected` and `parity_eq_zero_of_far`: they hold for every closed polygon.
  Simplicity is used only in `exists_parity_flip`, `exists_nonhorizontal_edge` and
  `polygon_separates`.
* The import `HPC.Fold.Theorem4Only` is replaced by `HPC.Fold.Theorem4Ge4` (which imports it); the
  proof of `theorem4_literal_ge4` is there (`theorem4_literal_ge4_model`).

## Part I of `jct`

The field `PlaneFacts.jct` asks, for a simple closed polygon `Γ`: `Γᶜ = U ∪ V` with `U`, `V` open,
disjoint, connected, `U` bounded, `V` unbounded, `frontier U = Γ = frontier V`. The route is the
**parity of the number of crossings of the eastward ray** from `x` with `Γ`, by the half-open
rule: an edge from `a` to `b` is counted iff the heights of `a` and `b` straddle `x.2` half-openly
(`a.2 ≤ x.2 < b.2` or `b.2 ≤ x.2 < a.2`) and the point of the edge at height `x.2` lies strictly
to the right of `x`. This rule is defined for every `x ∉ Γ` with no general-position hypothesis:
horizontal edges are never counted, and at the height of a vertex the half-open convention counts
exactly the right number of the two edges there (both or neither if the edges leave the vertex on
the same side of the horizontal, exactly one if on opposite sides), which is what makes the parity
locally constant. This batch proves:

1. the parity is locally constant on `Γᶜ`, hence constant on preconnected subsets of `Γᶜ`;
2. it is `0` far to the east (and hence on the whole unbounded component of a far point);
3. it flips across every non-horizontal edge, and a simple closed polygon has such an edge;
   hence `Γᶜ` is not connected, and the set of odd parity is nonempty and bounded.

Part II (batch 126): at most two components, `frontier U = frontier V = Γ`; assembly of `jct`.

Conventions: `Pt = ℝ × ℝ`; `polygonOf`, `polyEdge`, `IsSimpleVertices`, `isSimpleClosedPolygon_iff`
from `Tree67`/`Tree7`.
-/

namespace HPC.Plane

open Set Filter Topology

/-! ### Crossing parity -/

/-- **The half-open east-ray crossing rule** for the segment from `a` to `b` and the point `x`:
the heights straddle `x.2` half-openly, and the point of the segment at height `x.2` is strictly to
the right of `x`. -/
def CrossesEast (x a b : Pt) : Prop :=
  ((a.2 ≤ x.2 ∧ x.2 < b.2) ∨ (b.2 ≤ x.2 ∧ x.2 < a.2)) ∧
    x.1 < a.1 + (x.2 - a.2) * (b.1 - a.1) / (b.2 - a.2)

open scoped Classical in
/-- The number of edges of the closed polygon `v` crossed by the east ray from `x`. -/
noncomputable def crossCount {n : ℕ} (v : Fin n → Pt) (x : Pt) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    CrossesEast x (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)).card

/-- The crossing parity. -/
noncomputable def parity {n : ℕ} (v : Fin n → Pt) (x : Pt) : ZMod 2 := (crossCount v x : ZMod 2)

/-! #### Single-edge facts -/

/-- The half-open straddle condition is the exclusive or of `a.2 ≤ h` and `b.2 ≤ h`. -/
theorem straddle_iff_xor (h : ℝ) (a b : Pt) :
    ((a.2 ≤ h ∧ h < b.2) ∨ (b.2 ≤ h ∧ h < a.2)) ↔ Xor' (a.2 ≤ h) (b.2 ≤ h) := by
  rw [xor_iff_or_and_not_and]
  constructor
  · rintro (h | h) <;> constructor
    · left; exact h.1
    · rintro ⟨_, h'⟩; linarith [h.2]
    · right; exact h.1
    · rintro ⟨h', _⟩; linarith [h.2]
  · rintro ⟨h | h, h'⟩
    · left; exact ⟨h, lt_of_not_ge fun hb => h' ⟨h, hb⟩⟩
    · right; exact ⟨h, lt_of_not_ge fun ha => h' ⟨ha, h⟩⟩

/-- `CrossesEast` with the straddle condition as an exclusive or and the abscissa condition as the
positivity of a continuous function of the point. -/
theorem crossesEast_iff_xor (y a b : Pt) : CrossesEast y a b ↔
    Xor' (a.2 ≤ y.2) (b.2 ≤ y.2) ∧
      0 < a.1 + (y.2 - a.2) * ((b.1 - a.1) / (b.2 - a.2)) - y.1 := by
  unfold CrossesEast; rw [sub_pos, mul_div_assoc, straddle_iff_xor]

theorem crossFun_continuous (a b : Pt) :
    Continuous fun y : Pt => a.1 + (y.2 - a.2) * ((b.1 - a.1) / (b.2 - a.2)) - y.1 := by
  fun_prop

/-- The rule is symmetric in the ends of the segment (the two disjuncts swap; the crossing
abscissa is the same point of the line). -/
theorem crossesEast_comm (x a b : Pt) : CrossesEast x a b ↔ CrossesEast x b a := by
  unfold CrossesEast
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1.symm, ?_⟩ <;>
  · have hne : a.2 - b.2 ≠ 0 := by rcases h1 with h | h <;> intro h' <;> linarith [h.1, h.2]
    have hne' : b.2 - a.2 ≠ 0 := fun h => hne (by linarith)
    convert h2 using 1
    field_simp
    ring

/-- The point of height `h` on the line through `a` and `b` lies on the segment when the heights
of `a`, `b` straddle `h` (half-openly). -/
theorem mem_segment_of_straddle {a b : Pt} {h : ℝ}
    (hs : (a.2 ≤ h ∧ h < b.2) ∨ (b.2 ≤ h ∧ h < a.2)) :
    (a.1 + (h - a.2) * (b.1 - a.1) / (b.2 - a.2), h) ∈ segment ℝ a b := by
  have hne : b.2 - a.2 ≠ 0 := by rcases hs with h | h <;> intro h' <;> linarith [h.1, h.2]
  set t := (h - a.2) / (b.2 - a.2)
  have ht0 : 0 ≤ t := by
    rcases hs with hh | hh
    · exact div_nonneg (by linarith) (by linarith)
    · exact div_nonneg_of_nonpos (by linarith) (by linarith)
  have ht1 : t ≤ 1 := by
    rcases hs with hh | hh
    · rw [div_le_one (by linarith)]; linarith
    · rw [div_le_one_of_neg (by linarith)]; linarith
  refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, t]; field_simp; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, t]; field_simp; ring

/-- On a non-horizontal segment the abscissa of a point is determined by its height. -/
theorem fst_eq_of_mem_segment {a b z : Pt} (hz : z ∈ segment ℝ a b) (hab : a.2 ≠ b.2) :
    z.1 = a.1 + (z.2 - a.2) * (b.1 - a.1) / (b.2 - a.2) := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  have hne : b.2 - a.2 ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  obtain rfl : s = 1 - t := by linarith
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.snd_add, Prod.smul_snd]
  field_simp; ring

/-- A point between the ends of a horizontal segment lies on it. -/
theorem mem_segment_of_horizontal {a b z : Pt} (ha : a.2 = z.2) (hb : b.2 = z.2)
    (h : a.1 ≤ z.1 ∧ z.1 ≤ b.1 ∨ b.1 ≤ z.1 ∧ z.1 ≤ a.1) : z ∈ segment ℝ a b := by
  have key : ∀ a b : Pt, a.2 = z.2 → b.2 = z.2 → a.1 ≤ z.1 → z.1 ≤ b.1 →
      z ∈ segment ℝ a b := by
    intro a b ha hb h1 h2
    rcases eq_or_lt_of_le (h1.trans h2) with he | hlt
    · have : z = a := Prod.ext (by linarith) ha.symm
      rw [this]; exact left_mem_segment _ _ _
    · have hne : b.1 - a.1 ≠ 0 := (sub_pos.2 hlt).ne'
      refine ⟨(b.1 - z.1) / (b.1 - a.1), (z.1 - a.1) / (b.1 - a.1),
        div_nonneg (by linarith) (by linarith), div_nonneg (by linarith) (by linarith), ?_, ?_⟩
      · field_simp; ring
      · ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; field_simp; ring
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; rw [ha, hb]; field_simp; ring
  rcases h with h | h
  · exact key a b ha hb h.1 h.2
  · rw [segment_symm]; exact key b a hb ha h.1 h.2

/-- A point *on* the segment is never strictly to its own right:
`x ∈ segment ℝ a b → ¬ CrossesEast x a b`. -/
theorem not_crossesEast_of_mem {x a b : Pt} (hx : x ∈ segment ℝ a b) : ¬ CrossesEast x a b := by
  rintro ⟨h1, h2⟩
  have hab : a.2 ≠ b.2 := by rcases h1 with h | h <;> intro h' <;> linarith [h.1, h.2]
  rw [← fst_eq_of_mem_segment hx hab] at h2
  exact lt_irrefl _ h2

/-! #### The indicator and the vertex rule -/

open scoped Classical in
/-- The indicator of `CrossesEast x a b` in `ZMod 2`. -/
noncomputable def ceInd (x a b : Pt) : ZMod 2 := if CrossesEast x a b then 1 else 0

open scoped Classical in
/-- The **vertex jump** of `a` seen from `x`: `1` iff `a` has the height of `x` and lies strictly to
its right. -/
noncomputable def vJump (x a : Pt) : ZMod 2 := if a.2 = x.2 ∧ x.1 < a.1 then 1 else 0

theorem ceInd_congr {x a b y c d : Pt} (h : CrossesEast y c d ↔ CrossesEast x a b) :
    ceInd y c d = ceInd x a b := by
  unfold ceInd
  split_ifs with h1 h2 h2 <;>
    first | rfl | exact absurd (h.1 h1) h2 | exact absurd (h.2 h2) h1

theorem ceInd_comm (x a b : Pt) : ceInd x a b = ceInd x b a :=
  ceInd_congr (crossesEast_comm x a b)

theorem zmod2_add_self (z : ZMod 2) : z + z = 0 := by
  fin_cases z <;> decide

theorem zmod2_eq_of_add_eq_zero {z w : ZMod 2} (h : z + w = 0) : z = w := by
  fin_cases z <;> fin_cases w <;> first | rfl | exact absurd h (by decide)

theorem eventually_height (x : Pt) (c : ℝ) :
    ∀ᶠ y in 𝓝 x, (c < x.2 → c < y.2) ∧ (x.2 < c → y.2 < c) := by
  have hc : Continuous fun y : Pt => y.2 := continuous_snd
  refine (Filter.Eventually.and ?_ ?_)
  · by_cases h : c < x.2
    · exact (continuousAt_const.eventually_lt hc.continuousAt h).mono fun y hy _ => hy
    · exact Filter.Eventually.of_forall fun y h' => absurd h' h
  · by_cases h : x.2 < c
    · exact (hc.continuousAt.eventually_lt continuousAt_const h).mono fun y hy _ => hy
    · exact Filter.Eventually.of_forall fun y h' => absurd h' h

theorem eventually_sign {f : Pt → ℝ} (hf : Continuous f) (x : Pt) :
    ∀ᶠ y in 𝓝 x, (0 < f x → 0 < f y) ∧ (f x < 0 → f y < 0) := by
  refine (Filter.Eventually.and ?_ ?_)
  · by_cases h : 0 < f x
    · exact (continuousAt_const.eventually_lt hf.continuousAt h).mono fun y hy _ => hy
    · exact Filter.Eventually.of_forall fun y h' => absurd h' h
  · by_cases h : f x < 0
    · exact (hf.continuousAt.eventually_lt continuousAt_const h).mono fun y hy _ => hy
    · exact Filter.Eventually.of_forall fun y h' => absurd h' h

theorem iff_of_height {x y : Pt} {c : ℝ} (hc : c ≠ x.2) (h1 : c < x.2 → c < y.2)
    (h2 : x.2 < c → y.2 < c) : (c ≤ y.2 ↔ c ≤ x.2) := by
  rcases lt_or_gt_of_ne hc with h | h
  · exact ⟨fun _ => h.le, fun _ => (h1 h).le⟩
  · exact ⟨fun h' => absurd (h2 h) (not_lt.2 h'), fun h' => absurd h (not_lt.2 h')⟩

theorem sign_iff {u v : ℝ} (hu : u ≠ 0) (h1 : 0 < u → 0 < v) (h2 : u < 0 → v < 0) :
    (0 < v ↔ 0 < u) := by
  rcases lt_or_gt_of_ne hu with h | h
  · exact ⟨fun h' => absurd (h2 h) (not_lt.2 h'.le), fun h' => absurd h (not_lt.2 h'.le)⟩
  · exact ⟨fun _ => h, fun _ => h1 h⟩

/-- The vertex rule for an edge with exactly one end (`a`) at the height of `x`. -/
theorem crossesEast_jump_end {x a b : Pt} (hx : x ∉ segment ℝ a b) (ha : a.2 = x.2)
    (hb : b.2 ≠ x.2) :
    ∀ᶠ y in 𝓝 x, (x.2 ≤ y.2 → (CrossesEast y a b ↔ CrossesEast x a b)) ∧
      (y.2 < x.2 → ceInd y a b + ceInd x a b = vJump x a + vJump x b) := by
  have hax : a.1 ≠ x.1 := fun h => hx (by
    have : x = a := Prod.ext h.symm ha.symm
    rw [this]; exact left_mem_segment _ _ _)
  have hFx : a.1 + (x.2 - a.2) * ((b.1 - a.1) / (b.2 - a.2)) - x.1 = a.1 - x.1 := by
    rw [ha]; ring
  have hFx0 : a.1 + (x.2 - a.2) * ((b.1 - a.1) / (b.2 - a.2)) - x.1 ≠ 0 := by
    rw [hFx]; exact sub_ne_zero.2 hax
  have hRx : 0 < a.1 + (x.2 - a.2) * ((b.1 - a.1) / (b.2 - a.2)) - x.1 ↔ x.1 < a.1 := by
    rw [hFx, sub_pos]
  filter_upwards [eventually_height x b.2, eventually_sign (crossFun_continuous a b) x]
    with y ⟨hb1, hb2⟩ ⟨hF1, hF2⟩
  have hR := (sign_iff hFx0 hF1 hF2).trans hRx
  have hB := iff_of_height hb hb1 hb2
  have hvb : vJump x b = 0 := by simp [vJump, hb]
  have hva : vJump x a = if x.1 < a.1 then 1 else 0 := by simp [vJump, ha]
  simp only [ceInd, crossesEast_iff_xor, hR, hRx, hB, hvb, hva]
  simp only [ha, le_refl, add_zero, ← not_le]
  by_cases p : x.2 ≤ y.2 <;> by_cases q : b.2 ≤ x.2 <;> by_cases r : x.1 < a.1 <;>
    simp [p, q, r]

/-- **The vertex rule** (the statement proved for item 2 of the commission). For a single segment
from `a` to `b` and a point `x` off it, near `x`:
* at points `y` not below `x` (`x.2 ≤ y.2`) the indicator of `CrossesEast · a b` is that at `x`;
* at points `y` strictly below `x`, the indicator *jumps* by `vJump x a + vJump x b` (mod 2): by
  the sum of the indicators of "this end has the height of `x` and lies strictly to its right".

The jump is a sum of terms attached to the *vertices*; summed over the edges of a closed polygon
each vertex is counted twice (`sum_vJump_telescope`), so the total jump vanishes mod 2. Horizontal
edges at the height of `x` are covered: both ends lie on the same side of `x` (`x` is off the
edge), so their jump `vJump x a + vJump x b` is `0`, and they are never crossed. -/
theorem crossesEast_jump {x a b : Pt} (hx : x ∉ segment ℝ a b) :
    ∀ᶠ y in 𝓝 x, (x.2 ≤ y.2 → (CrossesEast y a b ↔ CrossesEast x a b)) ∧
      (y.2 < x.2 → ceInd y a b + ceInd x a b = vJump x a + vJump x b) := by
  by_cases ha : a.2 = x.2 <;> by_cases hb : b.2 = x.2
  · have hno : ∀ z : Pt, ¬ CrossesEast z a b := fun z h => by
      rw [crossesEast_iff_xor, ha, hb] at h
      exact (xor_self _ ▸ h.1 : False)
    have hab : vJump x a = vJump x b := by
      have : x.1 < a.1 ↔ x.1 < b.1 := by
        constructor <;> intro h <;> by_contra h' <;> push_neg at h' <;>
          exact hx (mem_segment_of_horizontal ha hb
            (by first | (left; constructor <;> linarith) | (right; constructor <;> linarith)))
      simp only [vJump, ha, hb, true_and, this]
    refine Filter.Eventually.of_forall fun y =>
      ⟨fun _ => iff_of_false (hno y) (hno x), fun _ => ?_⟩
    simp only [ceInd, hno, if_false, add_zero, hab, zmod2_add_self]
  · exact crossesEast_jump_end hx ha hb
  · have := crossesEast_jump_end (a := b) (b := a) (by rwa [segment_symm]) hb ha
    filter_upwards [this] with y hy
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [crossesEast_comm y, crossesEast_comm x]; exact hy.1 h
    · rw [ceInd_comm y, ceInd_comm x, add_comm (vJump x a)]; exact hy.2 h
  · have hva : vJump x a = 0 := by simp [vJump, ha]
    have hvb : vJump x b = 0 := by simp [vJump, hb]
    filter_upwards [eventually_height x a.2, eventually_height x b.2,
      eventually_sign (crossFun_continuous a b) x] with y ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hF1, hF2⟩
    have hA := iff_of_height ha ha1 ha2
    have hB := iff_of_height hb hb1 hb2
    have key : CrossesEast y a b ↔ CrossesEast x a b := by
      rw [crossesEast_iff_xor, crossesEast_iff_xor, hA, hB]
      by_cases hxor : Xor' (a.2 ≤ x.2) (b.2 ≤ x.2)
      · have hF0 : a.1 + (x.2 - a.2) * ((b.1 - a.1) / (b.2 - a.2)) - x.1 ≠ 0 := by
          intro h0
          apply hx
          have hm := mem_segment_of_straddle ((straddle_iff_xor x.2 a b).2 hxor)
          have : a.1 + (x.2 - a.2) * (b.1 - a.1) / (b.2 - a.2) = x.1 := by
            rw [mul_div_assoc]; linarith
          rw [this] at hm; exact hm
        rw [sign_iff hF0 hF1 hF2]
      · exact iff_of_false (fun h => hxor h.1) (fun h => hxor h.1)
    refine ⟨fun _ => key, fun _ => ?_⟩
    rw [ceInd_congr key, hva, hvb, add_zero, zmod2_add_self]

/-- Away from the heights of both ends the indicator is locally constant (in `ZMod 2` form). -/
theorem ceInd_eventually_eq {x a b : Pt} (hx : x ∉ segment ℝ a b) (ha : x.2 ≠ a.2)
    (hb : x.2 ≠ b.2) : ∀ᶠ y in 𝓝 x, ceInd y a b = ceInd x a b := by
  filter_upwards [crossesEast_jump hx] with y hy
  rcases le_or_gt x.2 y.2 with h | h
  · exact ceInd_congr (hy.1 h)
  · have hva : vJump x a = 0 := by simp [vJump, Ne.symm ha]
    have hvb : vJump x b = 0 := by simp [vJump, Ne.symm hb]
    exact zmod2_eq_of_add_eq_zero ((hy.2 h).trans (by rw [hva, hvb, add_zero]))

/-- **Local constancy of a single edge's indicator away from the edge and away from the heights of
its ends.** If `x ∉ segment ℝ a b` and `x.2 ≠ a.2`, `x.2 ≠ b.2`, the indicator of `CrossesEast · a b`
is constant near `x`. -/
theorem crossesEast_locallyConstant_of_ne {x a b : Pt} (hx : x ∉ segment ℝ a b) (ha : x.2 ≠ a.2)
    (hb : x.2 ≠ b.2) :
    ∃ ε > 0, ∀ y, dist y x < ε → (CrossesEast y a b ↔ CrossesEast x a b) := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 (crossesEast_jump hx)
  refine ⟨ε, hε, fun y hy => ?_⟩
  rcases le_or_gt x.2 y.2 with h' | h'
  · exact (h hy).1 h'
  · have hva : vJump x a = 0 := by simp [vJump, Ne.symm ha]
    have hvb : vJump x b = 0 := by simp [vJump, Ne.symm hb]
    have he := zmod2_eq_of_add_eq_zero ((h hy).2 h' |>.trans (by rw [hva, hvb, add_zero]))
    unfold ceInd at he
    constructor <;> intro hc
    · by_contra hn; rw [if_pos hc, if_neg hn] at he; exact absurd he (by decide)
    · by_contra hn; rw [if_pos hc, if_neg hn] at he; exact absurd he (by decide)

/-! #### The parity as a sum; the telescoping of the vertex jumps -/

theorem parity_eq_sum {n : ℕ} (v : Fin n → Pt) (x : Pt) :
    parity v x = ∑ i : Fin n, ceInd x (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) := by
  classical
  unfold parity crossCount ceInd
  rw [Finset.natCast_card_filter]

theorem next_eq_finRotate {n : ℕ} (i : Fin n) :
    (⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ : Fin n) = finRotate n i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  rw [finRotate_succ_apply]
  ext
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]

/-- Summed over the edges of a closed polygon, each vertex jump is counted twice. -/
theorem sum_vJump_telescope {n : ℕ} (v : Fin n → Pt) (x : Pt) :
    ∑ i : Fin n, (vJump x (v i) + vJump x (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)) =
      0 := by
  rw [Finset.sum_add_distrib]
  simp only [next_eq_finRotate]
  rw [Equiv.sum_comp (finRotate n) (fun i => vJump x (v i)), zmod2_add_self]

theorem not_mem_edge_of_not_mem {n : ℕ} {v : Fin n → Pt} {x : Pt} (hx : x ∉ polygonOf v)
    (i : Fin n) : x ∉ segment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) :=
  fun h => hx (Set.mem_iUnion.2 ⟨i, h⟩)

/-- **The parity is locally constant on `Γᶜ`** (eventually form). No simplicity is needed. -/
theorem parity_eventually_eq {n : ℕ} (v : Fin n → Pt) {x : Pt} (hx : x ∉ polygonOf v) :
    ∀ᶠ y in 𝓝 x, parity v y = parity v x := by
  have hall := Filter.eventually_all.2 fun i : Fin n =>
    crossesEast_jump (not_mem_edge_of_not_mem hx i)
  filter_upwards [hall] with y hy
  rw [parity_eq_sum, parity_eq_sum]
  rcases le_or_gt x.2 y.2 with h | h
  · exact Finset.sum_congr rfl fun i _ => ceInd_congr ((hy i).1 h)
  · apply zmod2_eq_of_add_eq_zero
    rw [← Finset.sum_add_distrib, ← sum_vJump_telescope v x]
    exact Finset.sum_congr rfl fun i _ => (hy i).2 h

/-- **The parity is locally constant on `Γᶜ`.** (Simplicity of the polygon is not needed and the
hypothesis of the skeleton is dropped.) -/
theorem parity_locallyConstant {n : ℕ} {v : Fin n → Pt} {x : Pt}
    (hx : x ∉ polygonOf v) : ∃ ε > 0, ∀ y, dist y x < ε → parity v y = parity v x := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 (parity_eventually_eq v hx)
  exact ⟨ε, hε, fun y hy => h hy⟩

/-- Parity is constant on preconnected subsets of `Γᶜ`. (Simplicity is not needed.) -/
theorem parity_eq_of_isPreconnected {n : ℕ} {v : Fin n → Pt} {S : Set Pt}
    (hS : IsPreconnected S) (hSΓ : S ⊆ (polygonOf v)ᶜ) {x y : Pt} (hx : x ∈ S) (hy : y ∈ S) :
    parity v x = parity v y := by
  have hc : ContinuousOn (fun z => (parity v z).val) S := fun z hz =>
    (continuousAt_const.congr (by
      filter_upwards [parity_eventually_eq v (hSΓ hz)] with w hw
      rw [hw])).continuousWithinAt
  have := hS.constant_of_mapsTo (T := (Set.univ : Set ℕ)) IsDiscrete.univ hc (Set.mapsTo_univ _ _) hx hy
  exact ZMod.val_injective _ this

/-! #### Far away -/

theorem fst_le_max_of_mem_segment {a b z : Pt} (hz : z ∈ segment ℝ a b) :
    z.1 ≤ max a.1 b.1 := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  calc s * a.1 + t * b.1 ≤ s * max a.1 b.1 + t * max a.1 b.1 :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hs)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) ht)
    _ = max a.1 b.1 := by rw [← add_mul, hst, one_mul]

/-- **Parity is `0` far to the east**: beyond the largest abscissa of a vertex no edge is crossed. -/
theorem parity_far {n : ℕ} (v : Fin n → Pt) : ∃ R : ℝ, ∀ x : Pt, R < x.1 → parity v x = 0 := by
  refine ⟨∑ i, |(v i).1|, fun x hx => ?_⟩
  have hle : ∀ i, (v i).1 ≤ ∑ i, |(v i).1| := fun i =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |(v i).1|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have hno : ∀ i : Fin n,
      ¬ CrossesEast x (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) := by
    rintro i ⟨hs, hlt⟩
    have hm := fst_le_max_of_mem_segment (mem_segment_of_straddle hs)
    have := max_le (hle i) (hle ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)
    simp only at hm
    linarith
  rw [parity_eq_sum]
  exact Finset.sum_eq_zero fun i _ => by simp [ceInd, hno i]

theorem polygonOf_subset_closedBall {n : ℕ} (v : Fin n → Pt) :
    polygonOf v ⊆ Metric.closedBall 0 (∑ i, ‖v i‖) := by
  have hle : ∀ i, ‖v i‖ ≤ ∑ i, ‖v i‖ := fun i =>
    Finset.single_le_sum (f := fun i => ‖v i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  intro z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
  exact (convex_closedBall (0 : Pt) _).segment_subset
    (mem_closedBall_zero_iff.2 (hle _)) (mem_closedBall_zero_iff.2 (hle _)) hi

theorem isClosed_polygonOf {n : ℕ} (v : Fin n → Pt) : IsClosed (polygonOf v) :=
  isClosed_iUnion_of_finite fun _ => (isCompact_segment' _ _).isClosed

/-- Parity is `0` outside a closed ball containing the polygon. -/
theorem parity_eq_zero_of_far' {n : ℕ} (v : Fin n → Pt) :
    ∃ R : ℝ, polygonOf v ⊆ Metric.closedBall 0 R ∧ ∀ x : Pt, R < dist x 0 → parity v x = 0 := by
  obtain ⟨R0, hR0⟩ := parity_far v
  set R1 := ∑ i, ‖v i‖
  refine ⟨max R0 R1, (polygonOf_subset_closedBall v).trans
    (Metric.closedBall_subset_closedBall (le_max_right _ _)), fun x hx => ?_⟩
  have hS := (isConnected_compl_closedBall_pt (0 : Pt) (max R0 R1)).1
  have hSΓ : (Metric.closedBall (0 : Pt) (max R0 R1))ᶜ ⊆ (polygonOf v)ᶜ :=
    Set.compl_subset_compl.2 ((polygonOf_subset_closedBall v).trans
      (Metric.closedBall_subset_closedBall (le_max_right _ _)))
  set y0 : Pt := (|R0| + |R1| + 1, 0)
  have hy0 : max R0 R1 < dist y0 0 := by
    rw [Prod.dist_eq]
    simp only [y0, Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero, dist_self]
    rw [abs_of_pos (by positivity)]
    refine lt_of_lt_of_le ?_ (le_max_left _ _)
    exact max_lt (by linarith [le_abs_self R0, abs_nonneg R1])
      (by linarith [le_abs_self R1, abs_nonneg R0])
  rw [parity_eq_of_isPreconnected hS.isPreconnected hSΓ (x := x) (y := y0)
    (by simpa [Metric.mem_closedBall] using hx) (by simpa [Metric.mem_closedBall] using hy0)]
  exact hR0 y0 (by simp only [y0]; linarith [le_abs_self R0, abs_nonneg R1])

/-- Hence parity is `0` on the complement of a large closed ball (which is connected: the
complement of a sup-metric ball is a union of four half-planes, `isConnected_compl_closedBall_pt`
of `Tree7Star`). (Simplicity is not needed.) -/
theorem parity_eq_zero_of_far {n : ℕ} (v : Fin n → Pt) :
    ∃ R : ℝ, ∀ x : Pt, R < dist x 0 → parity v x = 0 :=
  let ⟨R, _, h⟩ := parity_eq_zero_of_far' v; ⟨R, h⟩


/-! #### The flip across a non-horizontal edge -/

/-- For a simple polygon, a point of edge `i` that is not a vertex lies on no other edge. -/
theorem not_mem_polyEdge_of_ne {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) {i j : Fin n}
    (hij : j ≠ i) {p : Pt} (hp : p ∈ polyEdge v i) (hpv : ∀ k, p ≠ v k) : p ∉ polyEdge v j := by
  intro hpj
  obtain ⟨h1, h2⟩ := hv.2.2 i j (Ne.symm hij)
  by_cases hadj : (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val
  · rcases h1 hadj ⟨hp, hpj⟩ with h | h | h <;> exact hpv _ h
  · exact Set.disjoint_left.1 (h2 hadj) hp hpj

/-- **Parity flips across a non-horizontal edge.** For some `p` in the relative interior of a
non-horizontal edge `i`, the points `p ∓ t • (1, 0)` for small `t > 0` are off `Γ` and have
different parities. (`p` is chosen at a height which is not the height of any vertex.) -/
theorem exists_parity_flip {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n)
    (hne : (v i).2 ≠ (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩).2) :
    ∃ p ∈ polyEdge v i, ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
      (p.1 - t, p.2) ∉ polygonOf v ∧ (p.1 + t, p.2) ∉ polygonOf v ∧
      parity v (p.1 - t, p.2) ≠ parity v (p.1 + t, p.2) := by
  classical
  set a := v i
  set b := v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩
  have hlt : min a.2 b.2 < max a.2 b.2 := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  obtain ⟨c, hcI, hcH⟩ := (Set.Ioo_infinite hlt).exists_notMem_finset
    (Finset.univ.image fun j : Fin n => (v j).2)
  have hcv : ∀ k, (v k).2 ≠ c := fun k hk =>
    hcH (Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩)
  have hstr : (a.2 < c ∧ c < b.2) ∨ (b.2 < c ∧ c < a.2) := by
    obtain ⟨h1, h2⟩ := hcI
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le] at h1; rw [max_eq_right h.le] at h2; exact Or.inl ⟨h1, h2⟩
    · rw [min_eq_right h.le] at h1; rw [max_eq_left h.le] at h2; exact Or.inr ⟨h1, h2⟩
  have hstr' : (a.2 ≤ c ∧ c < b.2) ∨ (b.2 ≤ c ∧ c < a.2) := by
    rcases hstr with h | h
    · exact Or.inl ⟨h.1.le, h.2⟩
    · exact Or.inr ⟨h.1.le, h.2⟩
  set X := a.1 + (c - a.2) * (b.1 - a.1) / (b.2 - a.2)
  set p : Pt := (X, c)
  have hp : p ∈ polyEdge v i := mem_segment_of_straddle hstr'
  have hpv : ∀ k, p ≠ v k := fun k h => hcv k (by rw [← h])
  have hoff : ∀ j, j ≠ i → p ∉ polyEdge v j := fun j hj => not_mem_polyEdge_of_ne hv hj hp hpv
  -- the eventual facts at `p`
  have hE : ∀ᶠ y in 𝓝 p, ∀ j : Fin n, j ≠ i → y ∉ polyEdge v j ∧
      ceInd y (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) =
        ceInd p (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall fun _ h => absurd hj h
    · have h1 : ∀ᶠ y in 𝓝 p, y ∉ polyEdge v j :=
        (isCompact_segment' _ _).isClosed.isOpen_compl.mem_nhds (hoff j hj)
      have h2 := ceInd_eventually_eq (hoff j hj) (Ne.symm (hcv j)) (Ne.symm (hcv _))
      filter_upwards [h1, h2] with y hy1 hy2 _ using ⟨hy1, hy2⟩
  obtain ⟨ε, hε, hεE⟩ := Metric.eventually_nhds_iff.1 hE
  refine ⟨p, hp, ε, hε, fun t ht htε => ?_⟩
  have hdist : ∀ s : ℝ, |s| < ε → dist ((p.1 + s, p.2) : Pt) p < ε := fun s hs => by
    rw [Prod.dist_eq]; simp [hs]
  have hm := hεE (hdist (-t) (by rw [abs_neg, abs_of_pos ht]; exact htε))
  have hpl := hεE (hdist t (by rw [abs_of_pos ht]; exact htε))
  simp only [← sub_eq_add_neg] at hm
  -- off the polygon
  have hoffi : ∀ s : ℝ, s ≠ 0 → ((p.1 + s, p.2) : Pt) ∉ polyEdge v i := fun s hs h => by
    have := fst_eq_of_mem_segment h hne
    simp only [p, X] at this
    exact hs (by linarith)
  have hnot : ∀ s : ℝ, s ≠ 0 → (∀ j : Fin n, j ≠ i → ((p.1 + s, p.2) : Pt) ∉ polyEdge v j) →
      ((p.1 + s, p.2) : Pt) ∉ polygonOf v := fun s hs hj h => by
    obtain ⟨j, hj'⟩ := Set.mem_iUnion.1 h
    by_cases hji : j = i
    · subst hji; exact hoffi s hs hj'
    · exact hj j hji hj'
  have hcrossm : ceInd (p.1 - t, p.2) a b = 1 := by
    simp only [ceInd, CrossesEast]; rw [if_pos]
    exact ⟨hstr', by simp only [p, X]; linarith⟩
  have hcrossp : ceInd (p.1 + t, p.2) a b = 0 := by
    simp only [ceInd, CrossesEast]; rw [if_neg]
    rintro ⟨_, h⟩; simp only [p, X] at h; linarith
  refine ⟨?_, hnot t ht.ne' fun j hj => (hpl j hj).1, ?_⟩
  · have := hnot (-t) (neg_ne_zero.2 ht.ne') fun j hj => by
      have := (hm j hj).1; rwa [sub_eq_add_neg] at this
    rwa [← sub_eq_add_neg] at this
  · rw [parity_eq_sum, parity_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hrest : ∀ q : Pt, (∀ j : Fin n, j ≠ i → q ∉ polyEdge v j ∧
        ceInd q (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) =
          ceInd p (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩)) →
        ∑ j ∈ Finset.univ.erase i,
          ceInd q (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) =
        ∑ j ∈ Finset.univ.erase i,
          ceInd p (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) := fun q hq =>
      Finset.sum_congr rfl fun j hj => (hq j (Finset.ne_of_mem_erase hj)).2
    rw [hrest _ hm, hrest _ hpl]
    change ceInd (p.1 - t, p.2) a b + _ ≠ ceInd (p.1 + t, p.2) a b + _
    rw [hcrossm, hcrossp, zero_add]
    intro h
    have := congrArg (· - ∑ j ∈ Finset.univ.erase i,
      ceInd p (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩)) h
    simp only [add_sub_cancel_right, sub_self] at this
    exact one_ne_zero this

/-! #### A non-horizontal edge exists -/

theorem prev_val_eq {n m : ℕ} (hm : m < n) :
    (m + n - 1) % n = if m = 0 then n - 1 else m - 1 := by
  split_ifs with h
  · subst h; rw [zero_add]; exact Nat.mod_eq_of_lt (by omega)
  · rw [show m + n - 1 = (m - 1) + n by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

theorem next_val_eq {n m : ℕ} (hm : m < n) :
    (m + 1) % n = if m + 1 = n then 0 else m + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- A simple closed polygon has a non-horizontal edge: otherwise all vertices have one height; at
the leftmost vertex `v m` both neighbours lie to the right, and the midpoint of `v m` and the nearer
neighbour lies on both edges at `v m` without being a vertex. -/
theorem exists_nonhorizontal_edge {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) :
    ∃ i : Fin n, (v i).2 ≠ (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩).2 := by
  obtain ⟨hn, hinj, hsimp⟩ := hv
  by_contra hcon
  push_neg at hcon
  -- all heights are equal
  have hall : ∀ k : ℕ, ∀ hk : k < n, (v ⟨k, hk⟩).2 = (v ⟨0, by omega⟩).2 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [← ih (by omega)]
      have := hcon ⟨k, by omega⟩
      simp only [Nat.mod_eq_of_lt hk] at this
      exact this.symm
  have hall' : ∀ j k : Fin n, (v j).2 = (v k).2 := fun j k => by
    rw [hall j.val j.isLt, hall k.val k.isLt]
  -- the leftmost vertex
  obtain ⟨m, -, hm⟩ := Finset.exists_min_image Finset.univ (fun j : Fin n => (v j).1)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hlt : ∀ j, j ≠ m → (v m).1 < (v j).1 := fun j hj =>
    lt_of_le_of_ne (hm j (Finset.mem_univ _)) fun h =>
      hj (hinj (Prod.ext h.symm (hall' j m)))
  set pr : Fin n := ⟨(m.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩
  set nx : Fin n := ⟨(m.val + 1) % n, Nat.mod_lt _ (by omega)⟩
  have hpr : pr.val = if m.val = 0 then n - 1 else m.val - 1 := prev_val_eq m.isLt
  have hnx : nx.val = if m.val + 1 = n then 0 else m.val + 1 := next_val_eq m.isLt
  have hprv : (pr.val + 1) % n = m.val := by
    rw [next_val_eq pr.isLt]; split_ifs at hpr ⊢ <;> omega
  have hprm : pr ≠ m := fun h => by
    have := congrArg Fin.val h; split_ifs at hpr <;> omega
  have hnxm : nx ≠ m := fun h => by
    have := congrArg Fin.val h; split_ifs at hnx <;> omega
  have hprnx : pr ≠ nx := fun h => by
    have := congrArg Fin.val h; split_ifs at hpr hnx <;> omega
  have hprnext : (⟨(pr.val + 1) % n, Nat.mod_lt _ (Fin.pos pr)⟩ : Fin n) = m := Fin.ext hprv
  -- the nearer neighbour and the midpoint
  set w := if (v nx).1 ≤ (v pr).1 then v nx else v pr
  have hw1 : (v m).1 < w.1 := by
    simp only [w]; split_ifs
    · exact hlt _ hnxm
    · exact hlt _ hprm
  have hwnx : w.1 ≤ (v nx).1 := by simp only [w]; split_ifs with h <;> [exact le_rfl; linarith]
  have hwpr : w.1 ≤ (v pr).1 := by simp only [w]; split_ifs with h <;> [exact h; exact le_rfl]
  set z : Pt := (((v m).1 + w.1) / 2, (v m).2)
  have hz1 : (v m).1 < z.1 := by simp only [z]; linarith
  have hz2 : z.1 < w.1 := by simp only [z]; linarith
  have hzpr : z ∈ polyEdge v pr := by
    unfold polyEdge; rw [hprnext]
    exact mem_segment_of_horizontal (hall' _ _) rfl (Or.inr ⟨hz1.le, by linarith⟩)
  have hznx : z ∈ polyEdge v m := by
    exact mem_segment_of_horizontal rfl (hall' _ _) (Or.inl ⟨hz1.le, by linarith⟩)
  have := (hsimp pr m hprm).1 (Or.inl hprv) ⟨hzpr, hznx⟩
  rw [hprnext] at this
  rcases this with h | h | h
  · have := congrArg Prod.fst h; linarith
  · have := congrArg Prod.fst h; linarith
  · have := congrArg Prod.fst h; linarith

/-! #### Separation -/

theorem isOpen_parity_set {n : ℕ} (v : Fin n → Pt) (e : ZMod 2) :
    IsOpen {x | x ∉ polygonOf v ∧ parity v x = e} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hx, hxe⟩
  filter_upwards [(isClosed_polygonOf v).isOpen_compl.mem_nhds hx, parity_eventually_eq v hx]
    with y hy1 hy2 using ⟨hy1, hy2.trans hxe⟩

/-- **The complement of a simple closed polygon is not connected**, and the odd-parity set is a
nonempty bounded open set, the even-parity set a nonempty open set containing the complement of a
ball. -/
theorem polygon_separates {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) :
    ¬ IsConnected (polygonOf v)ᶜ ∧
      IsOpen {x | x ∉ polygonOf v ∧ parity v x = 1} ∧
      {x | x ∉ polygonOf v ∧ parity v x = 1}.Nonempty ∧
      Bornology.IsBounded {x | x ∉ polygonOf v ∧ parity v x = 1} ∧
      IsOpen {x | x ∉ polygonOf v ∧ parity v x = 0} ∧
      ∃ R : ℝ, ∀ x : Pt, R < dist x 0 → x ∈ {x | x ∉ polygonOf v ∧ parity v x = 0} := by
  obtain ⟨i, hi⟩ := exists_nonhorizontal_edge hv
  obtain ⟨p, -, ε, hε, hflip⟩ := exists_parity_flip hv i hi
  obtain ⟨h1, h2, h3⟩ := hflip (ε / 2) (by positivity) (by linarith)
  obtain ⟨R, hRΓ, hR⟩ := parity_eq_zero_of_far' v
  refine ⟨fun hc => h3 (parity_eq_of_isPreconnected hc.isPreconnected subset_rfl h1 h2),
    isOpen_parity_set v 1, ?_, ?_, isOpen_parity_set v 0, R, fun x hx =>
      ⟨fun hxΓ => ?_, hR x hx⟩⟩
  · have : parity v (p.1 - ε / 2, p.2) = 1 ∨ parity v (p.1 + ε / 2, p.2) = 1 := by
      revert h3
      generalize parity v (p.1 - ε / 2, p.2) = u
      generalize parity v (p.1 + ε / 2, p.2) = w
      fin_cases u <;> fin_cases w <;> simp
    rcases this with h | h
    · exact ⟨_, h1, h⟩
    · exact ⟨_, h2, h⟩
  · refine (Metric.isBounded_closedBall (x := (0 : Pt)) (r := R)).subset fun x hx => ?_
    rw [Metric.mem_closedBall]
    by_contra hlt
    push_neg at hlt
    have := hx.2; rw [hR x hlt] at this; exact absurd this (by decide)
  · have := hRΓ hxΓ
    rw [Metric.mem_closedBall] at this
    linarith

end HPC.Plane

/-! ## Theorem 4 as printed, at least four coarse links -/

namespace HPC.Fold

open HPC.Chain

/-- **Bing's Theorem 4 as printed, `k ≥ 4`** (`Theorem4LiteralGe4`): the two-link form with the
only-clauses at both ends. Proved in `HPC/Fold/Theorem4Ge4.lean`: `two_core` with the pair form of
Theorem 3 at both ends (`seg3Z`), the `G`-block of `d_k` sent to the top group (the new grouping
for `K = 4`), and, where the companion would leave the segment of Theorem 3 (`r = h`, `s = k`), the
meeting condition `OnlyE` instead of a companion. -/
theorem theorem4_literal_ge4 {X : Type*} [MetricSpace X] {n k : ℕ} (hk : 4 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (r s : Fin n) (hrs : r ≤ s)
    (hlow : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, by omega⟩).Nonempty)
    (hhigh : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β r).val = 0 ∧ (β s).val = q - 1 ∧ OnlyIn E β hβ r ∧ OnlyIn E β hβ s ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 2 :=
  theorem4_literal_ge4_model hk hcr r s hrs hlow hhigh

theorem theorem4LiteralGe4_holds : Theorem4LiteralGe4 :=
  fun _ _ _ _ hk _ _ hcr r s hrs hlow hhigh => theorem4_literal_ge4 hk hcr r s hrs hlow hhigh

end HPC.Fold
