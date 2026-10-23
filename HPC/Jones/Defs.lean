import HPC.Plane.SorgenfreyDefs
import HPC.Plane.Atriodic51Defs

/-!
# Batch 135: Jones 1948 / 1951 — definitions and basic facts

The definitions of the batch-135 skeleton (`doc/batches/skeletons/Jones48-batch135.lean`, §1 of
Jones 1948), unchanged, together with the general facts used throughout `HPC/Jones/`:

* `isOpen_setOf_aposAt` — the set of pairs `(x, y)` with `X` aposyndetic at `x` with respect to
  `y` is open in `X × X` (this is Theorem 1 of Jones 1948, in its natural form);
* `isClosed_fst_image`, `isClosed_snd_image` — projections of closed subsets of `X × X`;
* `exists_finite_apos_cover`, `exists_nhd_uniform_apos` — Heine–Borel for aposyndesis;
* `aposAt_of_frontier` — if the frontier of an open `V ∋ b` (with `y ∉ closure V`) consists of
  points at which `X` is aposyndetic with respect to `y`, then so is `b`;
* `exists_ball_subset_of_closed_cover` — Baire, in the form used by Jones;
* `exists_ne_ne` — a nondegenerate continuum has a third point;
* `subset_of_isPreconnected_of_closed_cover` — a connected set in `W ∪ Q` (closed, disjoint)
  meeting `Q` lies in `Q`.

Convention (COMMISSION-batch135.md §1): Jones's `M` is the whole space `X`.
-/

namespace HPC.Jones

open Set Topology Filter Metric

variable {X : Type*} [MetricSpace X]

/-! ### Definitions (Jones 1948, §1) -/

/-- **`X` is aposyndetic at `x` with respect to `y`** (Jones 1941, 1948 p. 404). There are a
continuum `H` and an open set `U` with `X − y ⊇ H ⊇ U ∋ x`. -/
def AposAt (x y : X) : Prop :=
  ∃ H U : Set X, Fold.Q78.IsContinuum H ∧ IsOpen U ∧ x ∈ U ∧ U ⊆ H ∧ y ∉ H

/-- `X` is **aposyndetic at `x`**: aposyndetic at `x` with respect to every other point. -/
def AposyndeticAt (x : X) : Prop := ∀ y, y ≠ x → AposAt x y

/-- `X` is **aposyndetic**: aposyndetic at each of its points. -/
def IsAposyndetic (X : Type*) [MetricSpace X] : Prop := ∀ x y : X, x ≠ y → AposAt x y

/-- `X` is **totally non-aposyndetic**: non-aposyndetic at each of its points. -/
def TotallyNonAposyndetic (X : Type*) [MetricSpace X] : Prop :=
  ∀ x : X, ¬ AposyndeticAt x

/-- `X` is **semi-locally-connected at `x`** (Whyburn 1939). For each open `U ∋ x` there is an
open `V` with `U ⊇ V ∋ x` such that `X − U` is contained in the union of finitely many components
of `X − V`. -/
def SemiLocConnAt (x : X) : Prop :=
  ∀ U : Set X, IsOpen U → x ∈ U → ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
    ∃ F : Finset X, (↑F : Set X) ⊆ Vᶜ ∧ Uᶜ ⊆ ⋃ c ∈ F, connectedComponentIn Vᶜ c

/-- **`p` cuts `x` from `y`** (Jones 1948, p. 403). `x`, `y` are distinct points other than `p`,
and every subcontinuum containing `x` and `y` contains `p`. -/
def CutsPts (p x y : X) : Prop :=
  x ≠ p ∧ y ≠ p ∧ x ≠ y ∧
    ∀ K : Set X, Fold.Q78.IsContinuum K → x ∈ K → y ∈ K → p ∈ K

/-- `p` is a **weak cut point**: it cuts some `x` from some `y`. -/
def IsWeakCutPoint (p : X) : Prop := ∃ x y, CutsPts p x y

/-- `p` is a **strong cut point** (separating point): `X − p` is not connected. -/
def IsStrongCutPoint (p : X) : Prop := ¬ IsConnected ({p}ᶜ : Set X)

/-- The **composant** of `x`: the union of the proper subcontinua containing `x`. -/
def composant (x : X) : Set X :=
  {y | ∃ K : Set X, Fold.Q78.IsContinuum K ∧ K ≠ univ ∧ x ∈ K ∧ y ∈ K}

/-- `X` is **decomposable**: the union of two proper subcontinua. -/
def IsDecomposableSpace (X : Type*) [MetricSpace X] : Prop :=
  ∃ H K : Set X, Fold.Q78.IsContinuum H ∧ Fold.Q78.IsContinuum K ∧ H ≠ univ ∧ K ≠ univ ∧
    H ∪ K = univ

/-! ### Elementary facts about aposyndesis -/

theorem not_aposAt_self (x : X) : ¬ AposAt x x := by
  rintro ⟨H, U, -, -, hxU, hUH, hxH⟩
  exact hxH (hUH hxU)

theorem AposAt.ne {x y : X} (h : AposAt x y) : x ≠ y := by
  rintro rfl
  exact not_aposAt_self x h

/-- If `X` is aposyndetic at `x` with respect to `y` by `(H, U)`, it is so at every point of `U`
with respect to every point outside `H`. -/
theorem aposAt_of_mem {x y : X} {H U : Set X} (hH : Fold.Q78.IsContinuum H) (hU : IsOpen U)
    (hxU : x ∈ U) (hUH : U ⊆ H) (hyH : y ∉ H) : AposAt x y :=
  ⟨H, U, hH, hU, hxU, hUH, hyH⟩

/-- **The pairs of aposyndesis form an open set** (the content of Jones 1948, Theorem 1). -/
theorem isOpen_setOf_aposAt : IsOpen {p : X × X | AposAt p.1 p.2} := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨x, y⟩ ⟨H, U, hH, hU, hxU, hUH, hyH⟩
  have hO : IsOpen (U ×ˢ Hᶜ) := hU.prod hH.1.isClosed.isOpen_compl
  filter_upwards [hO.mem_nhds ⟨hxU, hyH⟩] with p hp
  exact ⟨H, U, hH, hU, hp.1, hUH, hp.2⟩

theorem isClosed_setOf_not_aposAt : IsClosed {p : X × X | ¬ AposAt p.1 p.2} := by
  have := (isOpen_setOf_aposAt (X := X)).isClosed_compl
  simpa [compl_setOf] using this

theorem isOpen_aposAt_left (y : X) : IsOpen {x : X | AposAt x y} :=
  isOpen_setOf_aposAt.preimage (continuous_id.prodMk continuous_const)

theorem isOpen_aposAt_right (x : X) : IsOpen {y : X | AposAt x y} :=
  isOpen_setOf_aposAt.preimage (continuous_const.prodMk continuous_id)

theorem isClosed_not_aposAt_left (y : X) : IsClosed {x : X | ¬ AposAt x y} := by
  simpa [compl_setOf] using (isOpen_aposAt_left y).isClosed_compl

theorem isClosed_not_aposAt_right (x : X) : IsClosed {y : X | ¬ AposAt x y} := by
  simpa [compl_setOf] using (isOpen_aposAt_right x).isClosed_compl

/-- A continuum is the image of a continuum under a homeomorphism. -/
theorem isContinuum_image_homeomorph (T : X ≃ₜ X) {H : Set X} (hH : Fold.Q78.IsContinuum H) :
    Fold.Q78.IsContinuum (T '' H) :=
  ⟨hH.1.image T.continuous, hH.2.image _ T.continuous.continuousOn⟩

/-- Aposyndesis is invariant under homeomorphisms. -/
theorem AposAt.image (T : X ≃ₜ X) {x y : X} (h : AposAt x y) : AposAt (T x) (T y) := by
  obtain ⟨H, U, hH, hU, hxU, hUH, hyH⟩ := h
  refine ⟨T '' H, T '' U, isContinuum_image_homeomorph T hH, T.isOpenMap U hU,
    mem_image_of_mem _ hxU, image_mono hUH, ?_⟩
  rintro ⟨w, hw, hwy⟩
  exact hyH (T.injective hwy ▸ hw)

theorem aposAt_homeomorph_iff (T : X ≃ₜ X) {x y : X} : AposAt (T x) (T y) ↔ AposAt x y := by
  refine ⟨fun h => ?_, fun h => h.image T⟩
  have := h.image T.symm
  simpa using this

/-! ### Topology -/

/-- A connected set covered by two disjoint closed sets and meeting the second lies in it. -/
theorem subset_of_isPreconnected_of_closed_cover {K W Q : Set X} (hK : IsPreconnected K)
    (hW : IsClosed W) (hQ : IsClosed Q) (hWQ : Disjoint W Q) (hcov : K ⊆ W ∪ Q)
    (hmeet : (K ∩ Q).Nonempty) : K ⊆ Q := by
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hK) W Q hW hQ hcov
    (by rw [hWQ.inter_eq, inter_empty]) with h | h
  · obtain ⟨z, hzK, hzQ⟩ := hmeet
    exact absurd hzQ (Set.disjoint_left.mp hWQ (h hzK))
  · exact h

/-- The component of a closed set is closed. -/
theorem isClosed_connectedComponentIn' {F : Set X} (hF : IsClosed F) (x : X) :
    IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · refine closure_subset_iff_isClosed.mp ?_
    refine (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx)) ?_
    exact closure_minimal (connectedComponentIn_subset F x) hF
  · rw [connectedComponentIn_eq_empty hx]; exact isClosed_empty

/-- **Finitely many components.** If an open `O ∋ x` is covered by finitely many components of a
closed set `F`, then the component of `x` in `F` contains an open set containing `x`. -/
theorem exists_open_subset_component {F O : Set X} (hF : IsClosed F) (t : Finset X)
    (hO : IsOpen O) {x : X} (hxO : x ∈ O) (hcov : O ⊆ ⋃ c ∈ t, connectedComponentIn F c) :
    ∃ O' : Set X, IsOpen O' ∧ x ∈ O' ∧ O' ⊆ connectedComponentIn F x := by
  classical
  set C := connectedComponentIn F x with hC
  set G : Set X := ⋃ c ∈ t.filter (fun c => c ∉ C), connectedComponentIn F c with hG
  have hGcl : IsClosed G :=
    isClosed_biUnion_finset fun c _ => isClosed_connectedComponentIn' hF _
  refine ⟨O ∩ Gᶜ, hO.inter hGcl.isOpen_compl, ⟨hxO, ?_⟩, ?_⟩
  · intro hxG
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hxG
    rw [Finset.mem_filter] at hc
    apply hc.2
    have hcF : c ∈ F := by
      by_contra h
      rw [connectedComponentIn_eq_empty h] at hxc
      exact hxc
    rw [hC, ← connectedComponentIn_eq hxc]
    exact mem_connectedComponentIn hcF
  · rintro z ⟨hzO, hzG⟩
    obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp (hcov hzO)
    by_cases hcC : c ∈ C
    · rw [hC, connectedComponentIn_eq hcC]; exact hzc
    · exact absurd (mem_iUnion₂.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, hcC⟩, hzc⟩) hzG

section Compact

variable [CompactSpace X]

theorem isClosed_fst_image {S : Set (X × X)} (hS : IsClosed S) : IsClosed (Prod.fst '' S) :=
  isClosedMap_fst_of_compactSpace S hS

theorem isClosed_snd_image {S : Set (X × X)} (hS : IsClosed S) : IsClosed (Prod.snd '' S) :=
  isClosedMap_snd_of_compactSpace S hS

/-- For a closed `M`, the points at which `X` is not aposyndetic with respect to some point of `M`
form a closed set. -/
theorem isClosed_exists_not_aposAt_right {M : Set X} (hM : IsClosed M) :
    IsClosed {x : X | ∃ y ∈ M, ¬ AposAt x y} := by
  have h : {x : X | ∃ y ∈ M, ¬ AposAt x y} =
      Prod.fst '' ({p : X × X | ¬ AposAt p.1 p.2} ∩ Prod.snd ⁻¹' M) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩; exact ⟨(x, y), ⟨hxy, hy⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨hab, hb⟩, rfl⟩; exact ⟨b, hb, hab⟩
  rw [h]
  exact isClosed_fst_image (isClosed_setOf_not_aposAt.inter (hM.preimage continuous_snd))

/-- For a closed `M`, the points `y` such that `X` is not aposyndetic at some point of `M` with
respect to `y` form a closed set. -/
theorem isClosed_exists_not_aposAt_left {M : Set X} (hM : IsClosed M) :
    IsClosed {y : X | ∃ x ∈ M, ¬ AposAt x y} := by
  have h : {y : X | ∃ x ∈ M, ¬ AposAt x y} =
      Prod.snd '' ({p : X × X | ¬ AposAt p.1 p.2} ∩ Prod.fst ⁻¹' M) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩; exact ⟨(x, y), ⟨hxy, hx⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨hab, ha⟩, rfl⟩; exact ⟨a, ha, hab⟩
  rw [h]
  exact isClosed_snd_image (isClosed_setOf_not_aposAt.inter (hM.preimage continuous_fst))

end Compact

/-- **Heine–Borel, first form.** If `X` is aposyndetic at every point of the compact `K` with
respect to `y`, finitely many pairs `(H i, U i)` do it: the `U i` cover `K`, the `H i` miss `y`. -/
theorem exists_finite_apos_cover {K : Set X} (hK : IsCompact K) {y : X}
    (h : ∀ x ∈ K, AposAt x y) :
    ∃ (t : Finset X) (H U : X → Set X), (∀ i ∈ t, Fold.Q78.IsContinuum (H i) ∧ IsOpen (U i) ∧
      U i ⊆ H i ∧ y ∉ H i) ∧ K ⊆ ⋃ i ∈ t, U i := by
  classical
  choose! H U hH hU hxU hUH hyH using h
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover U (fun x hx => (hU x hx).mem_nhds (hxU x hx))
  exact ⟨t, H, U, fun i hi => ⟨hH i (htK i hi), hU i (htK i hi), hUH i (htK i hi),
    hyH i (htK i hi)⟩, hcov⟩

/-- **Heine–Borel, second form.** If `X` is aposyndetic at `x` with respect to every point of the
compact `K`, one open `U ∋ x` works for all of them: for each `y ∈ K` some continuum contains `U`
and misses `y`. -/
theorem exists_nhd_uniform_apos {K : Set X} (hK : IsCompact K) {x : X}
    (h : ∀ y ∈ K, AposAt x y) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ K, ∃ H : Set X, Fold.Q78.IsContinuum H ∧ U ⊆ H ∧
      y ∉ H := by
  classical
  choose! H U hH hU hxU hUH hyH using h
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun y => (H y)ᶜ)
    (fun y hy => (hH y hy).1.isClosed.isOpen_compl.mem_nhds (hyH y hy))
  refine ⟨⋂ i ∈ t, U i, isOpen_biInter_finset fun i hi => hU i (htK i hi),
    mem_iInter₂.mpr fun i hi => hxU i (htK i hi), fun y hy => ?_⟩
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hcov hy)
  exact ⟨H i, hH i (htK i hi), (biInter_subset_of_mem hi).trans (hUH i (htK i hi)), hyi⟩

/-- The same with a closed ball: for `s` small, the closed ball `closedBall x s` lies in a
continuum missing `y`, for every `y ∈ K`. -/
theorem exists_radius_uniform_apos {K : Set X} (hK : IsCompact K) {x : X}
    (h : ∀ y ∈ K, AposAt x y) :
    ∃ s > 0, ∀ y ∈ K, ∃ H : Set X, Fold.Q78.IsContinuum H ∧ closedBall x s ⊆ H ∧ y ∉ H := by
  obtain ⟨U, hU, hxU, hH⟩ := exists_nhd_uniform_apos hK h
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hxU
  refine ⟨r / 2, half_pos hr, fun y hy => ?_⟩
  obtain ⟨H, hH, hUH, hyH⟩ := hH y hy
  exact ⟨H, hH, (closedBall_subset_ball (half_lt_self hr)).trans (hrU.trans hUH), hyH⟩

section Compact

variable [CompactSpace X]

/-- **Aposyndesis from the frontier.** Let `V` be open, `b ∈ V` and `y ∉ closure V`. If `X` is
aposyndetic at each point of the frontier of `V` with respect to `y`, it is aposyndetic at `b`
with respect to `y`. (The component of `b` in `closure V ∪ ⋃ Hᵢ` is a neighbourhood of `b`: by
boundary bumping every component of that closed set contains one of the finitely many `Hᵢ`.) -/
theorem aposAt_of_frontier [ConnectedSpace X] {V : Set X} (hV : IsOpen V) {b y : X} (hb : b ∈ V)
    (hy : y ∉ closure V) (hfr : ∀ z ∈ frontier V, AposAt z y) : AposAt b y := by
  classical
  obtain ⟨t, H, U, htH, hcov⟩ := exists_finite_apos_cover isClosed_frontier.isCompact hfr
  have hHne : ∀ i ∈ t, (H i).Nonempty := fun i hi => (htH i hi).1.2.nonempty
  choose! c hc using hHne
  set F : Set X := closure V ∪ ⋃ i ∈ t, H i with hF
  have hFcl : IsClosed F :=
    isClosed_closure.union (isClosed_biUnion_finset fun i hi => (htH i hi).1.1.isClosed)
  have hyF : y ∉ F := by
    rintro (h | h)
    · exact hy h
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp h
      exact (htH i hi).2.2.2 hyi
  have hHF : ∀ i ∈ t, H i ⊆ F := fun i hi =>
    (subset_biUnion_of_mem (u := H) hi).trans subset_union_right
  -- every point of `F` lies in the component of some `c i`
  have hcomp : ∀ z ∈ F, ∃ i ∈ t, z ∈ connectedComponentIn F (c i) := by
    intro z hz
    rcases hz with hz | hz
    · have hne : closure V ≠ univ := fun h => hy (h ▸ mem_univ y)
      obtain ⟨K, hK, hKV, hzK, w, hwK, hwc⟩ :=
        Plane.exists_continuum_bump_closed (M := univ) ⟨isCompact_univ, isConnected_univ⟩
          isClosed_closure (subset_univ _) hne hz
      have hwfr : w ∈ frontier V := by
        refine ⟨hKV hwK, ?_⟩
        intro hwi
        have he : univ \ closure V = (closure V)ᶜ := by ext; simp
        rw [he, closure_compl] at hwc
        exact hwc (interior_mono subset_closure hwi)
      obtain ⟨i, hi, hwi⟩ := mem_iUnion₂.mp (hcov hwfr)
      refine ⟨i, hi, ?_⟩
      have hpre : IsPreconnected (K ∪ H i) :=
        hK.2.isPreconnected.union w hwK ((htH i hi).2.2.1 hwi) (htH i hi).1.2.isPreconnected
      exact hpre.subset_connectedComponentIn (Or.inr (hc i hi))
        (union_subset (hKV.trans subset_union_left) (hHF i hi)) (Or.inl hzK)
    · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
      exact ⟨i, hi, (htH i hi).1.2.isPreconnected.subset_connectedComponentIn (hc i hi)
        (hHF i hi) hzi⟩
  have hOF : V ∪ ⋃ i ∈ t, U i ⊆ F := by
    refine union_subset (subset_closure.trans subset_union_left) ?_
    exact iUnion₂_subset fun i hi => ((htH i hi).2.2.1).trans (hHF i hi)
  have hcov' : V ∪ ⋃ i ∈ t, U i ⊆ ⋃ c' ∈ t.image c, connectedComponentIn F c' := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := hcomp z (hOF hz)
    exact mem_iUnion₂.mpr ⟨c i, Finset.mem_image_of_mem c hi, hzi⟩
  obtain ⟨O, hO, hbO, hOC⟩ := exists_open_subset_component hFcl (t.image c)
    (hV.union (isOpen_biUnion fun i hi => (htH i hi).2.1)) (Or.inl hb) hcov'
  have hbF : b ∈ F := Or.inl (subset_closure hb)
  refine ⟨connectedComponentIn F b, O, ⟨(isClosed_connectedComponentIn' hFcl b).isCompact,
    isConnected_connectedComponentIn_iff.mpr hbF⟩, hO, hbO, hOC, ?_⟩
  exact fun hyC => hyF (connectedComponentIn_subset F b hyC)

end Compact

/-! ### Baire, and a third point -/

/-- **Baire, in Jones's form.** If a nonempty open `D` is covered by countably many closed sets,
one of them contains a ball lying in `D`. -/
theorem exists_ball_subset_of_closed_cover [CompactSpace X] {ι : Type*} [Countable ι]
    {D : Set X} (hD : IsOpen D) (hDne : D.Nonempty) {F : ι → Set X} (hF : ∀ i, IsClosed (F i))
    (hcov : D ⊆ ⋃ i, F i) : ∃ i, ∃ x : X, ∃ r > 0, ball x r ⊆ D ∩ F i := by
  haveI : Nonempty X := ⟨hDne.some⟩
  have hall : ⋃ j : Option ι, (Option.elim j Dᶜ F) = univ := by
    refine eq_univ_of_forall fun z => ?_
    by_cases hz : z ∈ D
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hz)
      exact mem_iUnion.mpr ⟨some i, hi⟩
    · exact mem_iUnion.mpr ⟨none, hz⟩
  have hdense := dense_iUnion_interior_of_closed (f := fun j : Option ι => Option.elim j Dᶜ F)
    (fun j => by cases j with
      | none => exact hD.isClosed_compl
      | some i => exact hF i) hall
  obtain ⟨z, hzD, hz⟩ := hdense.inter_open_nonempty D hD hDne
  obtain ⟨j, hj⟩ := mem_iUnion.mp hz
  cases j with
  | none =>
    exact absurd (interior_subset hj) (by simpa using hzD)
  | some i =>
    have hO : IsOpen (D ∩ interior (F i)) := hD.inter isOpen_interior
    obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO z ⟨hzD, hj⟩
    exact ⟨i, z, r, hr, fun w hw => ⟨(hrO hw).1, interior_subset (hrO hw).2⟩⟩

/-- In a connected metric space, two distinct points `a ≠ b` have a point at distance
`dist a b / 2` from `a`. -/
theorem exists_dist_eq_half [ConnectedSpace X] {a b : X} (hab : a ≠ b) :
    ∃ c : X, dist a c = dist a b / 2 := by
  have hpos : 0 < dist a b := dist_pos.mpr hab
  have h := isPreconnected_univ.intermediate_value (mem_univ a) (mem_univ b)
    (f := fun z => dist a z) (continuous_const.dist continuous_id).continuousOn
  obtain ⟨c, -, hc⟩ := h (show dist a b / 2 ∈ Icc (dist a a) (dist a b) by
    rw [dist_self]; constructor <;> linarith)
  exact ⟨c, hc⟩

/-- **A third point.** A nondegenerate connected metric space has, for any two points, a point
different from both. -/
theorem exists_ne_ne [ConnectedSpace X] [Nontrivial X] (a b : X) : ∃ c : X, c ≠ a ∧ c ≠ b := by
  by_cases hab : a = b
  · subst hab
    obtain ⟨c, hc⟩ := exists_ne a
    exact ⟨c, hc, hc⟩
  · obtain ⟨c, hc⟩ := exists_dist_eq_half hab
    have hpos : 0 < dist a b := dist_pos.mpr hab
    refine ⟨c, ?_, ?_⟩
    · rintro rfl; rw [dist_self] at hc; linarith
    · rintro rfl; linarith

end HPC.Jones
