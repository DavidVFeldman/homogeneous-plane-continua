import HPC.Span.OT82Parity
import HPC.Fold.Questions78

/-!
# Batch 192, §6: disjoint crossing continua are ordered (commission 192 §6)

`crossing_traces_separated` (commission 191 §7): two disjoint continua crossing the closed strip
`[a, b] × ℝ` meet the line `x = a` in sets one of which lies strictly below the other.

Route of the commission: if the traces interleave, there are `p, q ∈ K` and `w ∈ K'` on `x = a`
with `p.2 < w.2 < q.2` (`crossing_core`). A polygonal path `β` in `S ∖ K` joins `w` to a point
`e ∈ K'` on `x = b` (`polyReach_of_isPreconnected`: polygonal reachability is relatively clopen).
Closing `β` by a detour outside the strip gives a closed polygon `P` missing `K`; its crossing
parity is equal at `p` and `q` (`K` is connected), but counting the crossings of the two east rays
from `(a − 2, y)` and `(a − ½, y)` gives parity `1` at height `p.2` and `0` at height `q.2`. No
Jordan curve theorem is used: the parity does not need simplicity.
-/

namespace HPC.Span

open Set Topology Metric Filter HPC.Plane

/-! ### Single-edge facts -/

/-- A horizontal edge is never crossed. -/
theorem ceInd_eq_zero_of_horizontal (x u u' : Pt) (h : u.2 = u'.2) : ceInd x u u' = 0 := by
  unfold ceInd
  rw [if_neg]
  rintro ⟨hs, -⟩
  rcases hs with h1 | h1 <;> linarith [h1.1, h1.2]

/-- If every crossing of an edge at height `y` is to the right of both `x₁` and `x₂`, the two east
rays from `(x₁, y)` and `(x₂, y)` cross it alike. -/
theorem ceInd_eq_of_right {x₁ x₂ y : ℝ} (u u' : Pt)
    (h : ((u.2 ≤ y ∧ y < u'.2) ∨ (u'.2 ≤ y ∧ y < u.2)) →
      max x₁ x₂ < u.1 + (y - u.2) * (u'.1 - u.1) / (u'.2 - u.2)) :
    ceInd (x₁, y) u u' = ceInd (x₂, y) u u' := by
  apply ceInd_congr
  unfold CrossesEast
  simp only
  constructor
  · rintro ⟨hs, -⟩; exact ⟨hs, lt_of_le_of_lt (le_max_right _ _) (h hs)⟩
  · rintro ⟨hs, -⟩; exact ⟨hs, lt_of_le_of_lt (le_max_left _ _) (h hs)⟩

/-- An edge whose crossings at height `y` lie in a set of first coordinates `≥ c`. -/
theorem crossing_ge_of_subset {u u' : Pt} {y c : ℝ} (hsub : ∀ z ∈ segment ℝ u u', c ≤ z.1)
    (hs : (u.2 ≤ y ∧ y < u'.2) ∨ (u'.2 ≤ y ∧ y < u.2)) :
    c ≤ u.1 + (y - u.2) * (u'.1 - u.1) / (u'.2 - u.2) :=
  hsub _ (mem_segment_of_straddle hs)

/-- A vertical edge on `x = c` is crossed exactly when it straddles and `x < c`. -/
theorem crossesEast_vertical {x y c : ℝ} {u u' : Pt} (hu : u.1 = c) (hu' : u'.1 = c) :
    CrossesEast (x, y) u u' ↔ ((u.2 ≤ y ∧ y < u'.2) ∨ (u'.2 ≤ y ∧ y < u.2)) ∧ x < c := by
  unfold CrossesEast
  simp only [hu, hu', sub_self, mul_zero, zero_div, add_zero]

/-! ### Polygonal reachability -/

/-- `z` is reachable from `w` by a polygonal path in `A`. -/
def PolyReach (A : Set Pt) (w z : Pt) : Prop :=
  ∃ (m : ℕ) (β : ℕ → Pt), β 0 = w ∧ β m = z ∧ ∀ j < m, segment ℝ (β j) (β (j + 1)) ⊆ A

theorem PolyReach.refl (A : Set Pt) (w : Pt) : PolyReach A w w :=
  ⟨0, fun _ => w, rfl, rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩

theorem PolyReach.snoc {A : Set Pt} {w z z' : Pt} (h : PolyReach A w z)
    (hs : segment ℝ z z' ⊆ A) : PolyReach A w z' := by
  obtain ⟨m, β, h0, hm, hseg⟩ := h
  refine ⟨m + 1, fun j => if j ≤ m then β j else z', by simp [h0], by simp, fun j hj => ?_⟩
  rcases Nat.lt_or_ge j m with hjm | hjm
  · simp only [if_pos hjm.le, if_pos (Nat.succ_le_of_lt hjm)]
    exact hseg j hjm
  · have : j = m := by omega
    subst this
    simp only [le_refl, if_true, if_neg (Nat.not_succ_le_self j)]
    rw [hm]; exact hs

/-- A preconnected subset of a set `A` in which every point sees a ball (within `A`) by segments
is polygonally connected inside `A`. -/
theorem polyReach_of_isPreconnected {A C : Set Pt}
    (hloc : ∀ z ∈ A, ∃ r > 0, ∀ z' ∈ A, dist z' z < r → segment ℝ z z' ⊆ A)
    (hCA : C ⊆ A) (hC : IsPreconnected C) {w : Pt} (hw : w ∈ C) :
    ∀ z ∈ C, PolyReach A w z := by
  choose! r hr0 hr using hloc
  set u := ⋃ z ∈ A ∩ {z | PolyReach A w z}, ball z (r z)
  set v := ⋃ z ∈ A ∩ {z | ¬ PolyReach A w z}, ball z (r z)
  have hu : IsOpen u := isOpen_biUnion fun _ _ => isOpen_ball
  have hv : IsOpen v := isOpen_biUnion fun _ _ => isOpen_ball
  -- points of `A` in a ball around a reachable point are reachable, and conversely
  have hfw : ∀ z ∈ A, PolyReach A w z → ∀ c ∈ A, c ∈ ball z (r z) → PolyReach A w c :=
    fun z hz h c hc hcb => h.snoc (hr z hz c hc hcb)
  have hbw : ∀ z ∈ A, ¬ PolyReach A w z → ∀ c ∈ A, c ∈ ball z (r z) → ¬ PolyReach A w c :=
    fun z hz h c hc hcb hc' => h (hc'.snoc (by rw [segment_symm]; exact hr z hz c hc hcb))
  have hcover : C ⊆ u ∪ v := by
    intro c hc
    by_cases h : PolyReach A w c
    · exact Or.inl (mem_biUnion ⟨hCA hc, h⟩ (mem_ball_self (hr0 c (hCA hc))))
    · exact Or.inr (mem_biUnion ⟨hCA hc, h⟩ (mem_ball_self (hr0 c (hCA hc))))
  have hdisj : C ∩ (u ∩ v) = ∅ := by
    ext c
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hc hcu hcv
    obtain ⟨z₁, ⟨hz₁, h₁⟩, hc₁⟩ := mem_iUnion₂.1 hcu
    obtain ⟨z₂, ⟨hz₂, h₂⟩, hc₂⟩ := mem_iUnion₂.1 hcv
    exact hbw z₂ hz₂ h₂ c (hCA hc) hc₂ (hfw z₁ hz₁ h₁ c (hCA hc) hc₁)
  rcases isPreconnected_iff_subset_of_disjoint.1 hC u v hu hv hcover hdisj with hCu | hCv
  · intro z hz
    obtain ⟨z₁, ⟨hz₁, h₁⟩, hc₁⟩ := mem_iUnion₂.1 (hCu hz)
    exact hfw z₁ hz₁ h₁ z (hCA hz) hc₁
  · exfalso
    obtain ⟨z₂, ⟨hz₂, h₂⟩, hc₂⟩ := mem_iUnion₂.1 (hCv hw)
    exact hbw z₂ hz₂ h₂ w (hCA hw) hc₂ (PolyReach.refl A w)

/-- In `S ∖ K`, with `S` convex and `K` closed, every point sees a ball by segments. -/
theorem segment_local_of_convex_diff {S K : Set Pt} (hS : Convex ℝ S) (hK : IsClosed K) :
    ∀ z ∈ S \ K, ∃ r > 0, ∀ z' ∈ S \ K, dist z' z < r → segment ℝ z z' ⊆ S \ K := by
  intro z hz
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, fun z' hz' _ => by
      rw [diff_empty]; exact hS.segment_subset hz.1 hz'.1⟩
  have hr : 0 < infDist z K := (hK.notMem_iff_infDist_pos hKne).1 hz.2
  refine ⟨infDist z K, hr, fun z' hz' hd => ?_⟩
  intro y hy
  refine ⟨hS.segment_subset hz.1 hz'.1 hy, fun hyK => ?_⟩
  have hyb : y ∈ ball z (infDist z K) :=
    (convex_ball z _).segment_subset (mem_ball_self hr) (mem_ball.2 hd) hy
  have := infDist_le_dist_of_mem hyK (x := z)
  rw [mem_ball, dist_comm] at hyb
  linarith

/-! ### The detour polygon -/

/-- The vertices of the closed polygon of §6, step 3: the path `β 0, …, β m`, then
`(b + 1, (β m).2)`, `(b + 1, −M)`, `(a − 1, −M)`, `(a − 1, (β 0).2)`. -/
noncomputable def detourV (β : ℕ → Pt) (m : ℕ) (a b M : ℝ) : ℕ → Pt := fun j =>
  if j ≤ m then β j else if j = m + 1 then (b + 1, (β m).2) else if j = m + 2 then (b + 1, -M)
    else if j = m + 3 then (a - 1, -M) else (a - 1, (β 0).2)

/-- The edges of the detour polygon. -/
theorem detour_edge_cases (β : ℕ → Pt) (m : ℕ) (a b M : ℝ) (i : Fin (m + 5)) :
    (i.val < m ∧ detourV β m a b M i = β i ∧
        detourV β m a b M ((i.val + 1) % (m + 5)) = β (i.val + 1)) ∨
      (i.val = m ∧ detourV β m a b M i = β m ∧
        detourV β m a b M ((i.val + 1) % (m + 5)) = (b + 1, (β m).2)) ∨
      (i.val = m + 1 ∧ detourV β m a b M i = (b + 1, (β m).2) ∧
        detourV β m a b M ((i.val + 1) % (m + 5)) = (b + 1, -M)) ∨
      (i.val = m + 2 ∧ detourV β m a b M i = (b + 1, -M) ∧
        detourV β m a b M ((i.val + 1) % (m + 5)) = (a - 1, -M)) ∨
      (i.val = m + 3 ∧ detourV β m a b M i = (a - 1, -M) ∧
        detourV β m a b M ((i.val + 1) % (m + 5)) = (a - 1, (β 0).2)) ∨
      (i.val = m + 4 ∧ detourV β m a b M i = (a - 1, (β 0).2) ∧
        detourV β m a b M ((i.val + 1) % (m + 5)) = β 0) := by
  obtain ⟨k, hk⟩ := i
  simp only
  have hmod : k + 1 < m + 5 → (k + 1) % (m + 5) = k + 1 := Nat.mod_eq_of_lt
  rcases Nat.lt_or_ge k (m + 4) with h4 | h4
  · rw [hmod (by omega)]
    rcases Nat.lt_or_ge k m with h | h
    · left
      refine ⟨h, ?_, ?_⟩ <;> simp only [detourV] <;> split_ifs <;> first | rfl | omega
    · have : k = m ∨ k = m + 1 ∨ k = m + 2 ∨ k = m + 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · right; left
        refine ⟨rfl, ?_, ?_⟩ <;> simp only [detourV] <;> split_ifs <;> first | rfl | omega
      · right; right; left
        refine ⟨rfl, ?_, ?_⟩ <;> simp only [detourV] <;> split_ifs <;> first | rfl | omega
      · right; right; right; left
        refine ⟨rfl, ?_, ?_⟩ <;> simp only [detourV] <;> split_ifs <;> first | rfl | omega
      · right; right; right; right; left
        refine ⟨rfl, ?_, ?_⟩ <;> simp only [detourV] <;> split_ifs <;> first | rfl | omega
  · have hk4 : k = m + 4 := by omega
    subst hk4
    right; right; right; right; right
    rw [show m + 4 + 1 = m + 5 by ring, Nat.mod_self]
    refine ⟨rfl, ?_, ?_⟩ <;> simp only [detourV] <;> split_ifs <;> first | rfl | omega

/-! ### The core: interleaved traces are impossible -/

theorem crossing_core {a b : ℝ} (hab : a < b) {K K' : Set Pt} (hK : Fold.Q78.IsContinuum K)
    (hK' : IsPreconnected K') (hKS : K ⊆ Icc a b ×ˢ univ) (hK'S : K' ⊆ Icc a b ×ˢ univ)
    (hdisj : Disjoint K K') {p q w e : Pt} (hp : p ∈ K) (hq : q ∈ K) (hw : w ∈ K') (he : e ∈ K')
    (hpa : p.1 = a) (hqa : q.1 = a) (hwa : w.1 = a) (heb : e.1 = b) (hpw : p.2 < w.2)
    (hwq : w.2 < q.2) : False := by
  set S : Set Pt := Icc a b ×ˢ univ
  have hSc : Convex ℝ S := (convex_Icc a b).prod convex_univ
  set A := S \ K
  have hK'A : K' ⊆ A := fun z hz => ⟨hK'S hz, fun hzK => disjoint_left.1 hdisj hzK hz⟩
  obtain ⟨m, β, hβ0, hβm, hβ⟩ := polyReach_of_isPreconnected
    (segment_local_of_convex_diff hSc hK.1.isClosed) hK'A hK' hw e he
  -- a lower bound for the heights of `K`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ K, -M < z.2 := by
    obtain ⟨c, hc⟩ := (hK.1.image continuous_snd).bddBelow
    exact ⟨-c + 1, fun z hz => by have := hc (mem_image_of_mem _ hz); simp at this ⊢; linarith⟩
  set P : Fin (m + 5) → Pt := fun i => detourV β m a b M i
  have hedge := detour_edge_cases β m a b M
  have hβS : ∀ j ≤ m, β j ∈ S := by
    intro j hj
    rcases Nat.lt_or_ge j m with h | h
    · exact (hβ j h (left_mem_segment ℝ _ _)).1
    · rw [show j = m by omega, hβm]; exact hK'S he
  have hβA : ∀ j < m, ∀ z ∈ segment ℝ (β j) (β (j + 1)), z ∈ A := fun j hj z hz => hβ j hj hz
  -- points of edges, by cases
  have hedge_mem : ∀ z ∈ polygonOf P, (∃ j < m, z ∈ segment ℝ (β j) (β (j + 1))) ∨
      z ∈ segment ℝ e (b + 1, e.2) ∨ z ∈ segment ℝ ((b + 1, e.2) : Pt) (b + 1, -M) ∨
      z ∈ segment ℝ ((b + 1, -M) : Pt) (a - 1, -M) ∨
      z ∈ segment ℝ ((a - 1, -M) : Pt) (a - 1, w.2) ∨ z ∈ segment ℝ ((a - 1, w.2) : Pt) w := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.1 hz
    change z ∈ segment ℝ (detourV β m a b M i) (detourV β m a b M ((i.val + 1) % (m + 5))) at hi
    rcases hedge i with ⟨h, h1, h2⟩ | ⟨h, h1, h2⟩ | ⟨h, h1, h2⟩ | ⟨h, h1, h2⟩ | ⟨h, h1, h2⟩ |
        ⟨h, h1, h2⟩ <;> rw [h1, h2] at hi
    · exact Or.inl ⟨i, h, hi⟩
    · rw [hβm] at hi; exact Or.inr (Or.inl hi)
    · rw [hβm] at hi; exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hi)))
    · rw [hβ0] at hi; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hi))))
    · rw [hβ0] at hi; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hi))))
  have heK : e ∉ K := fun h => disjoint_left.1 hdisj h he
  have hwK : w ∉ K := fun h => disjoint_left.1 hdisj h hw
  -- `K` misses the polygon
  have hKP : K ⊆ (polygonOf P)ᶜ := by
    intro z hzK hzP
    have hzS := hKS hzK
    have hz1S := hzS.1
    have hzM := hM z hzK
    rcases hedge_mem z hzP with ⟨j, hj, hz⟩ | hz | hz | hz | hz | hz
    · exact (hβA j hj z hz).2 hzK
    all_goals
      obtain ⟨h1, h2⟩ := mem_segment_coords hz
      simp only [Set.mem_uIcc] at h1 h2
      try dsimp only at h1 h2
    · have : z = e := Prod.ext (by rcases h1 with h1 | h1 <;> linarith [h1.1, h1.2, hz1S.2])
        (by rcases h2 with h2 | h2 <;> linarith [h2.1, h2.2])
      exact heK (this ▸ hzK)
    · rcases h1 with h1 | h1 <;> linarith [h1.1, h1.2, hz1S.2]
    · rcases h2 with h2 | h2 <;> linarith [h2.1, h2.2]
    · rcases h1 with h1 | h1 <;> linarith [h1.1, h1.2, hz1S.1]
    · have : z = w := Prod.ext (by rcases h1 with h1 | h1 <;> linarith [h1.1, h1.2, hz1S.1])
        (by rcases h2 with h2 | h2 <;> linarith [h2.1, h2.2])
      exact hwK (this ▸ hzK)
  -- the horizontal segments `[(a − ½, y), y]` from `p` and `q` miss the polygon
  have hleft : ∀ y ∈ K, y.1 = a → y.2 ≠ w.2 →
      segment ℝ ((a - 1 / 2, y.2) : Pt) y ⊆ (polygonOf P)ᶜ := by
    intro y hyK hya hyw z hz hzP
    obtain ⟨hz1, hz2⟩ := mem_segment_coords hz
    simp only [Set.mem_uIcc] at hz1 hz2
    try dsimp only at hz1 hz2
    have hz1' : a - 1 / 2 ≤ z.1 ∧ z.1 ≤ a := by
      rcases hz1 with h | h <;> constructor <;> linarith [h.1, h.2]
    have hz2' : z.2 = y.2 := by rcases hz2 with h | h <;> linarith [h.1, h.2]
    have hyM := hM y hyK
    rcases hedge_mem z hzP with ⟨j, hj, hz'⟩ | hz' | hz' | hz' | hz' | hz'
    · have hzA := hβA j hj z hz'
      have : z = y := Prod.ext (by linarith [hzA.1.1.1, hz1'.2]) hz2'
      exact hzA.2 (this ▸ hyK)
    all_goals
      obtain ⟨h1, h2⟩ := mem_segment_coords hz'
      simp only [Set.mem_uIcc] at h1 h2
      try dsimp only at h1 h2
    · rcases h1 with h1 | h1 <;> linarith [h1.1, h1.2, hz1'.2, heb]
    · rcases h1 with h1 | h1 <;> linarith [h1.1, h1.2, hz1'.2]
    · rcases h2 with h2 | h2 <;> linarith [h2.1, h2.2]
    · rcases h1 with h1 | h1 <;> linarith [h1.1, h1.2, hz1'.1]
    · exact hyw (by rcases h2 with h2 | h2 <;> linarith [h2.1, h2.2])
  have hpar_left : ∀ y ∈ K, y.1 = a → y.2 ≠ w.2 → parity P y = parity P (a - 1 / 2, y.2) :=
    fun y hyK hya hyw => parity_eq_of_isPreconnected (convex_segment _ _).isPreconnected
      (hleft y hyK hya hyw) (right_mem_segment ℝ _ _) (left_mem_segment ℝ _ _)
  -- far left the parity is `0`
  have hfarleft : ∀ y : ℝ, parity P (a - 2, y) = 0 := by
    intro y
    have hhalf : Convex ℝ {z : Pt | a - 1 ≤ z.1} :=
      convex_halfSpace_ge (LinearMap.fst ℝ ℝ ℝ).isLinear (a - 1)
    have hvert : ∀ i, P i ∈ {z : Pt | a - 1 ≤ z.1} := by
      intro i
      show a - 1 ≤ (detourV β m a b M i).1
      rcases hedge i with ⟨h, h1, -⟩ | ⟨h, h1, -⟩ | ⟨h, h1, -⟩ | ⟨h, h1, -⟩ | ⟨h, h1, -⟩ |
          ⟨h, h1, -⟩ <;> rw [h1] <;> try simp only
      · linarith [(hβS i h.le).1.1]
      · linarith [(hβS m le_rfl).1.1]
      all_goals linarith
    refine parity_eq_zero_of_not_mem_convex P (convex_convexHull ℝ _)
      (finite_range P).isCompact_convexHull (fun i => subset_convexHull ℝ _ (mem_range_self i)) ?_
    intro hmem
    have := convexHull_min (fun z hz => by obtain ⟨i, rfl⟩ := hz; exact hvert i) hhalf hmem
    simp at this; linarith
  -- counting crossings between `(a − 2, y)` and `(a − ½, y)`
  have hcount : ∀ y : ℝ, y ≠ w.2 → -M < y →
      parity P (a - 1 / 2, y) + parity P (a - 2, y) =
        if y < w.2 then 1 else 0 := by
    intro y hyw hyM
    rw [parity_eq_sum, parity_eq_sum, ← Finset.sum_add_distrib]
    rw [Finset.sum_eq_single (⟨m + 3, by omega⟩ : Fin (m + 5))]
    · show ceInd _ (detourV β m a b M (m + 3)) (detourV β m a b M ((m + 3 + 1) % (m + 5))) +
        ceInd _ (detourV β m a b M (m + 3)) (detourV β m a b M ((m + 3 + 1) % (m + 5))) = _
      obtain ⟨-, h1, h2⟩ : (m + 3 = m + 3 ∧ detourV β m a b M (m + 3) = (a - 1, -M) ∧
          detourV β m a b M ((m + 3 + 1) % (m + 5)) = (a - 1, w.2)) := by
        rcases hedge ⟨m + 3, by omega⟩ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, h1, h2⟩ |
            ⟨h, -⟩ <;> simp only at h <;> try omega
        exact ⟨rfl, h1, by rw [h2, hβ0]⟩
      try simp only at h1 h2
      rw [h1, h2]
      have hv : ∀ x : ℝ, CrossesEast (x, y) ((a - 1, -M) : Pt) (a - 1, w.2) ↔
          ((((a - 1, -M) : Pt).2 ≤ y ∧ y < ((a - 1, w.2) : Pt).2) ∨
            (((a - 1, w.2) : Pt).2 ≤ y ∧ y < ((a - 1, -M) : Pt).2)) ∧ x < a - 1 :=
        fun x => crossesEast_vertical rfl rfl
      unfold ceInd
      rw [if_neg (by rw [hv]; rintro ⟨-, h⟩; linarith)]
      by_cases hyw' : y < w.2
      · rw [if_pos (by rw [hv]; exact ⟨Or.inl ⟨hyM.le, hyw'⟩, by linarith⟩),
          if_pos hyw', zero_add]
      · rw [if_neg (by
          rw [hv]
          rintro ⟨hs, -⟩
          rcases hs with h | h
          · exact hyw' h.2
          · simp only at h; linarith [h.2]), if_neg hyw', zero_add]
    · intro i _ hi
      show ceInd _ (detourV β m a b M i) (detourV β m a b M ((i.val + 1) % (m + 5))) +
        ceInd _ (detourV β m a b M i) (detourV β m a b M ((i.val + 1) % (m + 5))) = 0
      have hi' : i.val ≠ m + 3 := fun h => hi (Fin.ext h)
      rcases hedge i with ⟨h, h1, h2⟩ | ⟨h, h1, h2⟩ | ⟨h, h1, h2⟩ | ⟨h, h1, h2⟩ | ⟨h, h1, h2⟩ |
          ⟨h, h1, h2⟩
      · rw [h1, h2, ceInd_eq_of_right (x₁ := a - 1 / 2) (x₂ := a - 2) _ _ ?_, zmod2_add_self]
        intro hs
        have := crossing_ge_of_subset (fun z hz => (hβA i h z hz).1.1.1) hs
        rw [max_eq_left (by linarith)]; linarith
      · rw [h1, h2, ceInd_eq_zero_of_horizontal _ _ _ (by rw [hβm]),
          ceInd_eq_zero_of_horizontal _ _ _ (by rw [hβm]), add_zero]
      · rw [h1, h2, ceInd_eq_of_right (x₁ := a - 1 / 2) (x₂ := a - 2) _ _ ?_, zmod2_add_self]
        intro _
        simp only [sub_self, mul_zero, zero_div, add_zero]
        rw [max_eq_left (by linarith)]; linarith
      · rw [h1, h2, ceInd_eq_zero_of_horizontal _ (b + 1, -M) (a - 1, -M) rfl,
          ceInd_eq_zero_of_horizontal _ (b + 1, -M) (a - 1, -M) rfl, add_zero]
      · exact absurd h hi'
      · rw [h1, h2, ceInd_eq_zero_of_horizontal _ _ _ (by rw [hβ0]),
          ceInd_eq_zero_of_horizontal _ _ _ (by rw [hβ0]), add_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- the contradiction
  have hpq : parity P p = parity P q :=
    parity_eq_of_isPreconnected hK.2.isPreconnected hKP hp hq
  have h1 := hcount p.2 hpw.ne (hM p hp)
  have h2 := hcount q.2 hwq.ne' (hM q hq)
  rw [if_pos hpw, hfarleft, add_zero, ← hpar_left p hp hpa hpw.ne] at h1
  rw [if_neg (not_lt.2 hwq.le), hfarleft, add_zero, ← hpar_left q hq hqa hwq.ne'] at h2
  rw [hpq, h2] at h1
  exact absurd h1 (by decide)

/-- **§6** (commission 191 §7): two disjoint continua crossing the closed strip `[a, b] × ℝ` meet
the line `x = a` in sets one of which lies strictly below the other. -/
theorem crossing_traces_separated {a b : ℝ} (hab : a < b) {K K' : Set Pt}
    (hK : Fold.Q78.IsContinuum K) (hK' : Fold.Q78.IsContinuum K')
    (hKS : K ⊆ Icc a b ×ˢ univ) (hK'S : K' ⊆ Icc a b ×ˢ univ)
    (hKa : ∃ z ∈ K, z.1 = a) (hKb : ∃ z ∈ K, z.1 = b)
    (hK'a : ∃ z ∈ K', z.1 = a) (hK'b : ∃ z ∈ K', z.1 = b) (hdisj : Disjoint K K') :
    (∀ z ∈ K, ∀ z' ∈ K', z.1 = a → z'.1 = a → z.2 < z'.2) ∨
      (∀ z ∈ K, ∀ z' ∈ K', z.1 = a → z'.1 = a → z'.2 < z.2) := by
  have htr : ∀ {L : Set Pt}, Fold.Q78.IsContinuum L → (∃ z ∈ L, z.1 = a) →
      ∃ lo ∈ L, lo.1 = a ∧ ∃ hi ∈ L, hi.1 = a ∧
        ∀ z ∈ L, z.1 = a → lo.2 ≤ z.2 ∧ z.2 ≤ hi.2 := by
    intro L hL ⟨z₀, hz₀, hz₀a⟩
    have hc : IsCompact (L ∩ {z | z.1 = a}) :=
      hL.1.inter_right (isClosed_eq continuous_fst continuous_const)
    obtain ⟨lo, ⟨hlo, hloa⟩, hlomin⟩ := hc.exists_isMinOn ⟨z₀, hz₀, hz₀a⟩
      continuous_snd.continuousOn
    obtain ⟨hi, ⟨hhi, hhia⟩, hhimax⟩ := hc.exists_isMaxOn ⟨z₀, hz₀, hz₀a⟩
      continuous_snd.continuousOn
    exact ⟨lo, hlo, hloa, hi, hhi, hhia, fun z hz hza =>
      ⟨hlomin (show z ∈ L ∩ {z | z.1 = a} from ⟨hz, hza⟩),
        hhimax (show z ∈ L ∩ {z | z.1 = a} from ⟨hz, hza⟩)⟩⟩
  obtain ⟨plo, hplo, hploa, phi, hphi, hphia, hpb⟩ := htr hK hKa
  obtain ⟨wlo, hwlo, hwloa, whi, hwhi, hwhia, hwb⟩ := htr hK' hK'a
  have hne : ∀ z ∈ K, ∀ z' ∈ K', z.1 = a → z'.1 = a → z.2 ≠ z'.2 := by
    intro z hz z' hz' hza hz'a h
    have : z = z' := Prod.ext (hza.trans hz'a.symm) h
    subst this
    exact disjoint_left.1 hdisj hz hz'
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨z₁, hz₁, z₁', hz₁', hz₁a, hz₁'a, h₁⟩, ⟨z₂, hz₂, z₂', hz₂', hz₂a, hz₂'a, h₂⟩⟩ := hcon
  rcases lt_or_gt_of_ne (hne plo hplo wlo hwlo hploa hwloa) with h | h
  · -- `K` has points below and above the lowest point of `K'`
    have hlt : wlo.2 < phi.2 := lt_of_le_of_ne
      (((hwb z₁' hz₁' hz₁'a).1.trans h₁).trans (hpb z₁ hz₁ hz₁a).2)
      (fun h' => hne phi hphi wlo hwlo hphia hwloa h'.symm)
    obtain ⟨e, he, heb⟩ := hK'b
    exact crossing_core hab hK hK'.2.isPreconnected hKS hK'S hdisj hplo hphi hwlo he hploa hphia
      hwloa heb h hlt
  · have hlt : plo.2 < whi.2 := lt_of_le_of_ne
      (((hpb z₂ hz₂ hz₂a).1.trans h₂).trans (hwb z₂' hz₂' hz₂'a).2)
      (hne plo hplo whi hwhi hploa hwhia)
    obtain ⟨e, he, heb⟩ := hKb
    exact crossing_core hab hK' hK.2.isPreconnected hK'S hKS hdisj.symm hwlo hwhi hplo he hwloa
      hwhia hploa heb h hlt

end HPC.Span
