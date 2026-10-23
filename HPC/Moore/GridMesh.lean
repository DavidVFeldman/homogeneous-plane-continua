import HPC.Moore.GridSquare

/-!
# Boxes of a finite subgrid are the subdivisions (counting argument)

Pure topology, used for the Schoenflies form of Moore 1919, Theorem E (batch 143, item B).

Given finitely many lines of each family of a pre-grid (including the four extreme lines), the open
boxes cut out by consecutive lines are disjoint, nonempty, and cover the complement of the lines.
If the complement of the lines in a set `U` has exactly as many components as there are boxes,
then every box lies in a single component (`PreGrid.box_sub_component`).
-/

namespace HPC.Sq

open Set Topology

variable {X : Type*} [TopologicalSpace X]

namespace Family

variable {ι : Type*} {K : Set X} (F : Family ι K)

theorem L_sub_L {G : Finset ι} (hG : InjOn F.t G) {j l : ι} (hj : j ∈ G) (hl : l ∈ G)
    (h : F.t l ≤ F.t j) : F.L l ⊆ F.L j := by
  rcases h.lt_or_eq with h | h
  · exact (F.mono l j h).1
  · rw [hG hl hj h]

theorem R_sub_R {G : Finset ι} (hG : InjOn F.t G) {j l : ι} (hj : j ∈ G) (hl : l ∈ G)
    (h : F.t j ≤ F.t l) : F.R l ⊆ F.R j := by
  rcases h.lt_or_eq with h | h
  · exact (F.mono j l h).2.1
  · rw [hG hj hl h]

theorem consec_le {G : Finset ι} {j j' k : ι} (hc : F.Consec G j j') (hk : k ∈ G)
    (h : F.t j < F.t k) : F.t j' ≤ F.t k :=
  (hc.2.2.2 k hk).resolve_left (not_le.mpr h)

/-- A point strictly between two consecutive lines determines them. -/
theorem consec_eq {G : Finset ι} (hG : InjOn F.t G) {j j' k k' : ι} (hc : F.Consec G j j')
    (hc' : F.Consec G k k') {z : X} (hz : z ∈ K) (h₁ : z ∉ F.L j) (h₂ : z ∉ F.R j')
    (h₃ : z ∉ F.L k) (h₄ : z ∉ F.R k') : j = k ∧ j' = k' := by
  have hzj' : z ∈ F.L j' := (F.mem_L_or_R hz j').resolve_right h₂
  have hzk' : z ∈ F.L k' := (F.mem_L_or_R hz k').resolve_right h₄
  have e1 : F.t j = F.t k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact h₃ (F.L_sub_L hG hc'.1 hc.2.1 (F.consec_le hc hc'.1 h) hzj')
    · exact h₁ (F.L_sub_L hG hc.1 hc'.2.1 (F.consec_le hc' hc.1 h) hzk')
  have hjk := hG hc.1 hc'.1 e1
  subst hjk
  refine ⟨rfl, hG hc.2.1 hc'.2.1 ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := F.consec_le hc' hc.2.1 hc.2.2.1
    linarith
  · have := F.consec_le hc hc'.2.1 hc'.2.2.1
    linarith

/-- The set of consecutive pairs of a finite set of lines containing the line at `0`. -/
theorem ncard_consec {G : Finset ι} (hG : InjOn F.t G) {a : ι} (ha : a ∈ G) (ha0 : F.t a = 0) :
    G.card - 1 ≤ {p : ι × ι | F.Consec G p.1 p.2}.ncard := by
  classical
  have hfin : {p : ι × ι | F.Consec G p.1 p.2}.Finite :=
    ((G ×ˢ G : Finset (ι × ι)).finite_toSet).subset fun p hp =>
      Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hp.1, hp.2.1⟩)
  rw [← Finset.card_erase_of_mem ha, ← ncard_coe_finset]
  refine (ncard_le_ncard ?_ (hfin.image Prod.snd)).trans (ncard_image_le hfin)
  intro i hi
  rw [Finset.mem_coe, Finset.mem_erase] at hi
  have hlt : F.t a < F.t i := by
    rcases (F.t_mem i).1.lt_or_eq with h | h
    · rw [ha0]; exact h
    · exact absurd (hG hi.2 ha (by rw [ha0, h])) hi.1
  obtain ⟨j, hj⟩ := F.exists_pred G ha hi.2 hlt
  exact ⟨(j, i), hj, rfl⟩

end Family

namespace PreGrid

variable {ιX ιY : Type*} {K : Set X} (g : PreGrid ιX ιY K)

/-- The lines of a finite subgrid. -/
def lines (G : Finset ιX) (H : Finset ιY) : Set X :=
  (⋃ j ∈ G, g.FX.line j) ∪ ⋃ m ∈ H, g.FY.line m

theorem box_disjoint_lines {G : Finset ιX} {H : Finset ιY} (hG : InjOn g.FX.t G)
    (hH : InjOn g.FY.t H) {j j' : ιX} {m m' : ιY}
    (hc : g.FX.Consec G j j') (hc' : g.FY.Consec H m m') :
    Disjoint (box g.FX g.FY j j' m m') (g.lines G H) := by
  rw [disjoint_left]
  rintro z ⟨-, hz⟩ hzC
  simp only [mem_union, not_or] at hz
  obtain ⟨⟨⟨hzL, hzR⟩, hzL'⟩, hzR'⟩ := hz
  rcases hzC with hzC | hzC
  · obtain ⟨l, hl, hzl⟩ := mem_iUnion₂.mp hzC
    rcases hc.2.2.2 l hl with h | h
    · exact hzL (g.FX.L_sub_L hG hc.1 hl h hzl.1)
    · exact hzR (g.FX.R_sub_R hG hc.2.1 hl h hzl.2)
  · obtain ⟨l, hl, hzl⟩ := mem_iUnion₂.mp hzC
    rcases hc'.2.2.2 l hl with h | h
    · exact hzL' (g.FY.L_sub_L hH hc'.1 hl h hzl.1)
    · exact hzR' (g.FY.R_sub_R hH hc'.2.1 hl h hzl.2)

/-- The boxes cover the complement of the lines. -/
theorem exists_box {G : Finset ιX} {H : Finset ιY} (hG0 : g.FX.i0 ∈ G) (hG1 : g.FX.i1 ∈ G)
    (hH0 : g.FY.i0 ∈ H) (hH1 : g.FY.i1 ∈ H) {z : X} (hz : z ∈ K) (hzC : z ∉ g.lines G H) :
    ∃ j j' m m', g.FX.Consec G j j' ∧ g.FY.Consec H m m' ∧ z ∈ box g.FX g.FY j j' m m' := by
  obtain ⟨j, j', hc, h1, h2⟩ := g.FX.exists_consec_mem G hG0 hG1 g.FX.t_i0 g.FX.t_i1 hz
  obtain ⟨m, m', hc', h3, h4⟩ := g.FY.exists_consec_mem H hH0 hH1 g.FY.t_i0 g.FY.t_i1 hz
  refine ⟨j, j', m, m', hc, hc', hz, ?_⟩
  simp only [lines, mem_union, mem_iUnion₂, not_or, not_exists] at hzC
  simp only [mem_union, not_or]
  refine ⟨⟨⟨fun h => hzC.1 j hc.1 ⟨h, h1⟩, fun h => hzC.1 j' hc.2.1 ⟨h2, h⟩⟩,
    fun h => hzC.2 m hc'.1 ⟨h, h3⟩⟩, fun h => hzC.2 m' hc'.2.1 ⟨h4, h⟩⟩

/-- Boxes of distinct consecutive pairs are disjoint. -/
theorem box_eq {G : Finset ιX} {H : Finset ιY} (hG : InjOn g.FX.t G)
    (hH : InjOn g.FY.t H) {j j' k k' : ιX} {m m' n n' : ιY}
    (hc : g.FX.Consec G j j') (hc' : g.FY.Consec H m m') (hd : g.FX.Consec G k k')
    (hd' : g.FY.Consec H n n') {z : X} (hz : z ∈ box g.FX g.FY j j' m m')
    (hz' : z ∈ box g.FX g.FY k k' n n') : (j = k ∧ j' = k') ∧ (m = n ∧ m' = n') := by
  obtain ⟨hzK, hz⟩ := hz
  obtain ⟨-, hz'⟩ := hz'
  simp only [mem_union, not_or] at hz hz'
  exact ⟨g.FX.consec_eq hG hc hd hzK hz.1.1.1 hz.1.1.2 hz'.1.1.1 hz'.1.1.2,
    g.FY.consec_eq hH hc' hd' hzK hz.1.2 hz.2 hz'.1.2 hz'.2⟩

/-- The open set whose trace on `K` is a box. -/
def boxOpen (j j' : ιX) (m m' : ιY) : Set X :=
  (g.FX.L j ∪ g.FX.R j' ∪ g.FY.L m ∪ g.FY.R m')ᶜ

theorem isOpen_boxOpen (j j' : ιX) (m m' : ιY) : IsOpen (g.boxOpen j j' m m') :=
  ((((g.FX.closedL j).union (g.FX.closedR j')).union (g.FY.closedL m)).union
    (g.FY.closedR m')).isOpen_compl

theorem box_eq_inter (j j' : ιX) (m m' : ιY) :
    box g.FX g.FY j j' m m' = K ∩ g.boxOpen j j' m m' := rfl

/-- **Counting.** If the complement in `U` of the lines of a finite subgrid has as many components
as there are boxes, then every box lies in one component. -/
theorem box_sub_component {G : Finset ιX} {H : Finset ιY} (hG : InjOn g.FX.t G)
    (hH : InjOn g.FY.t H) (hG0 : g.FX.i0 ∈ G) (hG1 : g.FX.i1 ∈ G)
    (hH0 : g.FY.i0 ∈ H) (hH1 : g.FY.i1 ∈ H) {U : Set X} (hUK : U ⊆ K)
    (hKU : K \ U ⊆ g.lines G H)
    (hcard : {c | ∃ x ∈ U \ g.lines G H, c = connectedComponentIn (U \ g.lines G H) x}.ncard =
      (G.card - 1) * (H.card - 1))
    {j j' : ιX} {m m' : ιY} (hc : g.FX.Consec G j j') (hc' : g.FY.Consec H m m') :
    ∃ x ∈ U \ g.lines G H, box g.FX g.FY j j' m m' ⊆ connectedComponentIn (U \ g.lines G H) x := by
  classical
  set C := g.lines G H
  set W := U \ C
  -- the boxes
  let P : Set ((ιX × ιX) × (ιY × ιY)) :=
    {p | g.FX.Consec G p.1.1 p.1.2 ∧ g.FY.Consec H p.2.1 p.2.2}
  let bx : (ιX × ιX) × (ιY × ιY) → Set X := fun p => box g.FX g.FY p.1.1 p.1.2 p.2.1 p.2.2
  have hbxW : ∀ p ∈ P, bx p ⊆ W := fun p hp z hz =>
    ⟨by_contra fun hzU => disjoint_left.mp (g.box_disjoint_lines hG hH hp.1 hp.2) hz
        (hKU ⟨hz.1, hzU⟩),
      disjoint_left.mp (g.box_disjoint_lines hG hH hp.1 hp.2) hz⟩
  have hbx_eq : ∀ p ∈ P, ∀ p' ∈ P, ∀ z, z ∈ bx p → z ∈ bx p' → p = p' := by
    rintro ⟨⟨j, j'⟩, ⟨m, m'⟩⟩ hp ⟨⟨k, k'⟩, ⟨n, n'⟩⟩ hp' z hz hz'
    obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := g.box_eq hG hH hp.1 hp.2 hp'.1 hp'.2 hz hz'
    rfl
  have hcov : ∀ z ∈ W, ∃ p ∈ P, z ∈ bx p := by
    intro z hz
    obtain ⟨j, j', m, m', h1, h2, h3⟩ := g.exists_box hG0 hG1 hH0 hH1 (hUK hz.1) hz.2
    exact ⟨((j, j'), (m, m')), ⟨h1, h2⟩, h3⟩
  -- each component lies in the box of any of its points
  have hcomp : ∀ x ∈ W, ∀ p ∈ P, x ∈ bx p → connectedComponentIn W x ⊆ bx p := by
    intro x hx p hp hxp
    have hconn := (isPreconnected_connectedComponentIn (F := W) (x := x))
    have hsub : connectedComponentIn W x ⊆ W := connectedComponentIn_subset W x
    let v : Set X := ⋃ q ∈ P \ {p}, g.boxOpen q.1.1 q.1.2 q.2.1 q.2.2
    have hv : IsOpen v := isOpen_biUnion fun q _ => g.isOpen_boxOpen _ _ _ _
    have huv : connectedComponentIn W x ⊆ g.boxOpen p.1.1 p.1.2 p.2.1 p.2.2 ∪ v := by
      intro z hz
      obtain ⟨q, hq, hzq⟩ := hcov z (hsub hz)
      by_cases hqp : q = p
      · subst hqp; exact Or.inl hzq.2
      · exact Or.inr (mem_iUnion₂.mpr ⟨q, ⟨hq, hqp⟩, hzq.2⟩)
    have hdis : connectedComponentIn W x ∩ (g.boxOpen p.1.1 p.1.2 p.2.1 p.2.2 ∩ v) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro z ⟨hz, hzp, hzv⟩
      obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.mp hzv
      exact hq.2 (hbx_eq q hq.1 p hp z ⟨hUK (hsub hz).1, hzq⟩ ⟨hUK (hsub hz).1, hzp⟩)
    rcases isPreconnected_iff_subset_of_disjoint.mp hconn (g.boxOpen p.1.1 p.1.2 p.2.1 p.2.2) v
      (g.isOpen_boxOpen _ _ _ _) hv huv hdis with h | h
    · intro z hz
      exact ⟨hUK (hsub hz).1, h hz⟩
    · exfalso
      obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (h (mem_connectedComponentIn hx))
      exact hq.2 (hbx_eq q hq.1 p hp x ⟨hUK hx.1, hxq⟩ hxp)
  -- the map from components to boxes
  let 𝒞 : Set (Set X) := {c | ∃ x ∈ W, c = connectedComponentIn W x}
  haveI : Nonempty ((ιX × ιX) × (ιY × ιY)) := ⟨((j, j'), (m, m'))⟩
  let φ : Set X → (ιX × ιX) × (ιY × ιY) := fun c => Classical.epsilon fun p => p ∈ P ∧ c ⊆ bx p
  have hφ : ∀ x ∈ W, φ (connectedComponentIn W x) ∈ P ∧
      connectedComponentIn W x ⊆ bx (φ (connectedComponentIn W x)) := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := hcov x hx
    exact Classical.epsilon_spec (p := fun p => p ∈ P ∧ connectedComponentIn W x ⊆ bx p)
      ⟨p, hp, hcomp x hx p hp hxp⟩
  have hφ_eq : ∀ x ∈ W, ∀ p ∈ P, x ∈ bx p → φ (connectedComponentIn W x) = p := fun x hx p hp hxp =>
    hbx_eq _ (hφ x hx).1 p hp x ((hφ x hx).2 (mem_connectedComponentIn hx)) hxp
  have himage : φ '' 𝒞 = P := by
    apply subset_antisymm
    · rintro _ ⟨c, ⟨x, hx, rfl⟩, rfl⟩
      exact (hφ x hx).1
    · intro p hp
      obtain ⟨y, hy⟩ := g.box_nonempty hp.1.2.2.1 hp.2.2.2.1
      exact ⟨_, ⟨y, hbxW p hp hy, rfl⟩, hφ_eq y (hbxW p hp hy) p hp hy⟩
  -- counting
  have hPfin : P.Finite := by
    refine ((((G ×ˢ G) ×ˢ (H ×ˢ H) : Finset _)).finite_toSet).subset ?_
    rintro p ⟨h1, h2⟩
    simp only [Finset.coe_product, mem_prod, Finset.mem_coe]
    exact ⟨⟨h1.1, h1.2.1⟩, h2.1, h2.2.1⟩
  have hPcard : (G.card - 1) * (H.card - 1) ≤ P.ncard := by
    have : P = {p : ιX × ιX | g.FX.Consec G p.1 p.2} ×ˢ {p : ιY × ιY | g.FY.Consec H p.1 p.2} := rfl
    rw [this, ncard_prod]
    exact Nat.mul_le_mul (g.FX.ncard_consec hG hG0 g.FX.t_i0) (g.FY.ncard_consec hH hH0 g.FY.t_i0)
  have hpos : 0 < (G.card - 1) * (H.card - 1) := by
    have h01 : g.FX.i0 ≠ g.FX.i1 := fun h => by
      have := g.FX.t_i1; rw [← h, g.FX.t_i0] at this; exact zero_ne_one this
    have h01' : g.FY.i0 ≠ g.FY.i1 := fun h => by
      have := g.FY.t_i1; rw [← h, g.FY.t_i0] at this; exact zero_ne_one this
    have a := Finset.card_le_card (show ({g.FX.i0, g.FX.i1} : Finset ιX) ⊆ G by
      intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> assumption)
    have b := Finset.card_le_card (show ({g.FY.i0, g.FY.i1} : Finset ιY) ⊆ H by
      intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> assumption)
    rw [Finset.card_pair h01] at a
    rw [Finset.card_pair h01'] at b
    exact Nat.mul_pos (by omega) (by omega)
  have h𝒞fin : 𝒞.Finite := finite_of_ncard_pos (by rw [hcard]; exact hpos)
  have hinj : InjOn φ 𝒞 := by
    refine injOn_of_ncard_image_eq (le_antisymm (ncard_image_le h𝒞fin) ?_) h𝒞fin
    rw [himage]
    exact (show 𝒞.ncard = _ from hcard).trans_le hPcard
  -- conclusion
  obtain ⟨y, hy⟩ := g.box_nonempty hc.2.2.1 hc'.2.2.1
  have hp : ((j, j'), (m, m')) ∈ P := ⟨hc, hc'⟩
  refine ⟨y, hbxW _ hp hy, fun z hz => ?_⟩
  have hzW := hbxW _ hp hz
  have hyW := hbxW _ hp hy
  have e : connectedComponentIn W z = connectedComponentIn W y :=
    hinj ⟨z, hzW, rfl⟩ ⟨y, hyW, rfl⟩ ((hφ_eq z hzW _ hp hz).trans (hφ_eq y hyW _ hp hy).symm)
  rw [← e]
  exact mem_connectedComponentIn hzW

end PreGrid

end HPC.Sq
