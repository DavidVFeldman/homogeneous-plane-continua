import HPC.Jones.Jones49A

/-!
# Batch 150: chains of separating points (Whyburn Ch. III §§1–2, streamlined)

A *separation chain* (`SepChain`) is a set `T` of points of a preconnected set `Q`, closed in a set
`R`, each `p ∈ T` coming with a separation `R − p = A p ∪ B p` into disjoint open sets such that
any two `A`-sides (and any two `B`-sides) meet in `Q`. This is the situation of Whyburn's (1.3):
the points of `T` all separate "the same two points" (here: the same two open sets) in `R`.

* `SepChain.lt` is Whyburn's natural order (1.31): `p < q` iff `q ∈ B p`. It is a strict linear
  order (`lt_total`, `lt_asymm`, `lt_trans`), and the sides are nested (`B_sub`, `A_sub`;
  Whyburn's (1.2)).
* `SepChain.M x y` is the closed interval `Q ∩ (B x ∩ A y + x + y)`; it is preconnected
  (`M_isPreconnected`) and closed in `R` (`M_closed`).
* `SepChain.Good p`: `p` is a limit point both of its predecessors and of its successors in `T`.
  All but countably many points of `T` are good (`countable_not_good`; Whyburn's (2.1)).
* `SepChain.Res p`: the points of `Q − p` not separated from `p` by any two points of `T` on either
  side of `p`. All but countably many good points have `Res p = ∅` (`countable_res`; the step of
  Whyburn's (2.2) that removes the elements `H` with a point `p_h` not separated from `H`).
* For a good point with `Res p = ∅`, in a locally compact space, small intervals `M x y` exist
  around `p` (`exists_small_interval`), and then a cut-wire argument in a compact ball gives an
  open set `V ∋ p` of small diameter with `frontier V ⊆ {x, y}` (`exists_open_frontier_pair`):
  this replaces Whyburn's (8.3) and (2.21)–(2.22). Hence (`countable_of_not_orderLE_two`) a chain
  of points none of which is of order `≤ 2` is countable.
-/

namespace HPC.Jones

open Set Topology Metric

section Generic

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]

/-- **The counting argument of Whyburn's (2.1).** If `lt` compares any two distinct points of `T`
and `lt p q` puts `g p` into `P q`, then only countably many `p ∈ T` have `g p` outside the closure
of `P p`. (Each such `p` is assigned a basic open set about `g p` missing `P p`; two points of `T`
cannot receive the same one.) -/
theorem countable_not_mem_closure_of_lt {T : Set X} (lt : X → X → Prop) (g : X → X)
    (P : X → Set X) (htot : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → lt p q ∨ lt q p)
    (hP : ∀ p ∈ T, ∀ q ∈ T, lt p q → g p ∈ P q) :
    {p ∈ T | g p ∉ closure (P p)}.Countable := by
  classical
  set 𝓑 := TopologicalSpace.countableBasis X
  have hB := TopologicalSpace.isBasis_countableBasis X
  have hex : ∀ p ∈ {p ∈ T | g p ∉ closure (P p)}, ∃ N ∈ 𝓑, g p ∈ N ∧ Disjoint N (P p) := by
    rintro p ⟨-, hp⟩
    have : (closure (P p))ᶜ ∈ 𝓝 (g p) := isClosed_closure.isOpen_compl.mem_nhds hp
    obtain ⟨N, hN, hgN, hNsub⟩ := hB.mem_nhds_iff.1 this
    exact ⟨N, hN, hgN, disjoint_left.2 fun z hzN hzP => hNsub hzN (subset_closure hzP)⟩
  choose! f hf using hex
  refine MapsTo.countable_of_injOn (fun p hp => (hf p hp).1) ?_
    (TopologicalSpace.countable_countableBasis X)
  intro p hp q hq hpq
  by_contra hne
  rcases htot p hp.1 q hq.1 hne with h | h
  · have h1 := hP p hp.1 q hq.1 h
    have h2 := (hf p hp).2.1
    rw [hpq] at h2
    exact disjoint_left.1 (hf q hq).2.2 h2 h1
  · have h1 := hP q hq.1 p hp.1 h
    have h2 := (hf q hq).2.1
    rw [← hpq] at h2
    exact disjoint_left.1 (hf p hp).2.2 h2 h1

end Generic

section CutWire

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- **Cut wire in a compact set** (Šura-Bura): if the component of `p` in a compact set `F` misses
a closed set `H`, some relatively clopen part `F ∩ G` of `F` (with `G` open) contains `p` and
misses `H`. -/
theorem exists_clopen_of_connectedComponentIn_disjoint {F H : Set X} (hF : IsCompact F)
    (hH : IsClosed H) {p : X} (hp : p ∈ F) (hdisj : Disjoint (connectedComponentIn F p) H) :
    ∃ G, IsOpen G ∧ p ∈ G ∧ IsClosed (F ∩ G) ∧ Disjoint (F ∩ G) H := by
  classical
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hF
  set p' : F := ⟨p, hp⟩
  set H' : Set F := Subtype.val ⁻¹' H
  have hHc : IsCompact H' := (hH.preimage continuous_subtype_val).isCompact
  have hCH : H' ∩ ⋂ s : { s : Set F // IsClopen s ∧ p' ∈ s }, (s : Set F) = ∅ := by
    rw [← connectedComponent_eq_iInter_isClopen]
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hzH hzC
    have : (z : X) ∈ connectedComponentIn F p := by
      rw [connectedComponentIn_eq_image hp]; exact ⟨z, hzC, rfl⟩
    exact disjoint_left.1 hdisj this hzH
  obtain ⟨u, hu⟩ := hHc.elim_finite_subfamily_closed
    (fun s : { s : Set F // IsClopen s ∧ p' ∈ s } => (s : Set F)) (fun s => s.2.1.isClosed) hCH
  set W' : Set F := ⋂ i ∈ u, (i : Set F)
  have hW'clopen : IsClopen W' := isClopen_biInter_finset fun i _ => i.2.1
  have hpW' : p' ∈ W' := mem_iInter₂.mpr fun i _ => i.2.2
  obtain ⟨G, hG, hGW⟩ := isOpen_induced_iff.mp hW'clopen.isOpen
  have himg : F ∩ G = Subtype.val '' W' := by
    ext z
    constructor
    · rintro ⟨hzF, hzG⟩
      refine ⟨⟨z, hzF⟩, ?_, rfl⟩
      rw [← hGW]; exact hzG
    · rintro ⟨w, hw, rfl⟩
      rw [← hGW] at hw
      exact ⟨w.2, hw⟩
  refine ⟨G, hG, ?_, ?_, ?_⟩
  · have : p' ∈ Subtype.val ⁻¹' G := by rw [hGW]; exact hpW'
    exact this
  · rw [himg]
    exact (hW'clopen.isClosed.isCompact.image continuous_subtype_val).isClosed
  · rw [himg, disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ hwH
    have : w ∈ H' ∩ W' := ⟨hwH, hw⟩
    rw [hu] at this
    exact this

end CutWire

section Chain

variable {X : Type*} [MetricSpace X]

/-- A **separation chain**: see the module docstring. -/
structure SepChain (X : Type*) [MetricSpace X] where
  /-- The ambient set (an open set of `X` in the applications). -/
  R : Set X
  /-- The component of `R` containing the chain. -/
  Q : Set X
  /-- The points of the chain. -/
  T : Set X
  /-- The side of the chosen separation of `R − p` containing the first fixed set. -/
  A : X → Set X
  /-- The side of the chosen separation of `R − p` containing the second fixed set. -/
  B : X → Set X
  isOpen_A : ∀ p ∈ T, IsOpen (A p)
  isOpen_B : ∀ p ∈ T, IsOpen (B p)
  union_eq : ∀ p ∈ T, A p ∪ B p = R \ {p}
  disj : ∀ p ∈ T, Disjoint (A p) (B p)
  preconn : IsPreconnected Q
  Q_sub : Q ⊆ R
  T_sub : T ⊆ Q
  closed_in : closure Q ∩ R ⊆ Q
  Q_max : ∀ D, IsPreconnected D → D ⊆ R → (D ∩ Q).Nonempty → D ⊆ Q
  commonA : ∀ p ∈ T, ∀ q ∈ T, (Q ∩ A p ∩ A q).Nonempty
  commonB : ∀ p ∈ T, ∀ q ∈ T, (Q ∩ B p ∩ B q).Nonempty

namespace SepChain

variable (C : SepChain X)

/-- Whyburn's natural order: `p` precedes `q` iff `q` lies on the `B`-side of `p`. -/
def lt (p q : X) : Prop := q ∈ C.B p

/-- The predecessors of `p` in the chain. -/
def preds (p : X) : Set X := {q ∈ C.T | C.lt q p}

/-- The successors of `p` in the chain. -/
def succs (p : X) : Set X := {q ∈ C.T | C.lt p q}

/-- The closed interval from `x` to `y` in `Q`. -/
def M (x y : X) : Set X := C.Q ∩ ((C.B x ∩ C.A y) ∪ {x, y})

/-- `p` is a limit point of its predecessors and of its successors. -/
def Good (p : X) : Prop := p ∈ closure (C.preds p) ∧ p ∈ closure (C.succs p)

/-- The residue at `p`: points of `Q − p` separated from `p` by no two points of the chain on
either side of `p`. -/
def Res (p : X) : Set X :=
  {z ∈ C.Q | z ≠ p ∧ ∀ x ∈ C.T, ∀ y ∈ C.T, C.lt x p → C.lt p y → z ∈ C.B x ∩ C.A y}

variable {C}

theorem A_sub_R {p : X} (hp : p ∈ C.T) : C.A p ⊆ C.R \ {p} := by
  rw [← C.union_eq p hp]; exact subset_union_left

theorem B_sub_R {p : X} (hp : p ∈ C.T) : C.B p ⊆ C.R \ {p} := by
  rw [← C.union_eq p hp]; exact subset_union_right

theorem notMem_A {p : X} (hp : p ∈ C.T) : p ∉ C.A p := fun h => (A_sub_R hp h).2 rfl

theorem notMem_B {p : X} (hp : p ∈ C.T) : p ∉ C.B p := fun h => (B_sub_R hp h).2 rfl

theorem mem_A_or_B {p z : X} (hp : p ∈ C.T) (hz : z ∈ C.R) (hzp : z ≠ p) :
    z ∈ C.A p ∨ z ∈ C.B p := by
  have : z ∈ C.A p ∪ C.B p := by rw [C.union_eq p hp]; exact ⟨hz, hzp⟩
  exact this

theorem notMem_B_of_A {p z : X} (hp : p ∈ C.T) (hz : z ∈ C.A p) : z ∉ C.B p :=
  disjoint_left.1 (C.disj p hp) hz

theorem notMem_A_of_B {p z : X} (hp : p ∈ C.T) (hz : z ∈ C.B p) : z ∉ C.A p :=
  disjoint_right.1 (C.disj p hp) hz

/-- The `A`-side of `p` in `Q`, with `p`, is preconnected. -/
theorem side_A {p : X} (hp : p ∈ C.T) : IsPreconnected (C.Q \ C.B p) := by
  have h := isPreconnected_side (B := C.B p) C.preconn (C.T_sub hp) (C.isOpen_A p hp)
    (C.isOpen_B p hp) (fun z hz => mem_A_or_B hp (C.Q_sub hz.1) hz.2)
    (fun z _ hzA => notMem_B_of_A hp hzA)
  have he : C.Q \ (C.B p \ {p}) = C.Q \ C.B p := by
    rw [diff_singleton_eq_self (notMem_B hp)]
  rwa [he] at h

/-- The `B`-side of `p` in `Q`, with `p`, is preconnected. -/
theorem side_B {p : X} (hp : p ∈ C.T) : IsPreconnected (C.Q \ C.A p) := by
  have h := isPreconnected_side (B := C.A p) (A := C.B p) C.preconn (C.T_sub hp)
    (C.isOpen_B p hp) (C.isOpen_A p hp)
    (fun z hz => (mem_A_or_B hp (C.Q_sub hz.1) hz.2).symm)
    (fun z _ hzB => notMem_A_of_B hp hzB)
  have he : C.Q \ (C.A p \ {p}) = C.Q \ C.A p := by
    rw [diff_singleton_eq_self (notMem_A hp)]
  rwa [he] at h

/-- A preconnected subset of `R − q` meeting `B q` lies in `B q`. -/
theorem subset_B_of_preconn {q : X} (hq : q ∈ C.T) {D : Set X} (hD : IsPreconnected D)
    (hDR : D ⊆ C.R) (hqD : q ∉ D) {z : X} (hzD : z ∈ D) (hzB : z ∈ C.B q) : D ⊆ C.B q := by
  have hsub : D ⊆ C.B q ∪ C.A q := by
    intro w hw
    exact (mem_A_or_B hq (hDR hw) (fun h => hqD (h ▸ hw))).symm
  exact hD.subset_left_of_subset_union (C.isOpen_B q hq) (C.isOpen_A q hq) (C.disj q hq).symm
    hsub ⟨z, hzD, hzB⟩

/-- A preconnected subset of `R − q` meeting `A q` lies in `A q`. -/
theorem subset_A_of_preconn {q : X} (hq : q ∈ C.T) {D : Set X} (hD : IsPreconnected D)
    (hDR : D ⊆ C.R) (hqD : q ∉ D) {z : X} (hzD : z ∈ D) (hzA : z ∈ C.A q) : D ⊆ C.A q := by
  have hsub : D ⊆ C.A q ∪ C.B q := by
    intro w hw
    exact mem_A_or_B hq (hDR hw) (fun h => hqD (h ▸ hw))
  exact hD.subset_left_of_subset_union (C.isOpen_A q hq) (C.isOpen_B q hq) (C.disj q hq)
    hsub ⟨z, hzD, hzA⟩

/-- Whyburn's (1.2)/(1.31): `p < q` iff `p` lies on the `A`-side of `q`. -/
theorem lt_iff {p q : X} (hp : p ∈ C.T) (hq : q ∈ C.T) (hpq : p ≠ q) :
    C.lt p q ↔ p ∈ C.A q := by
  constructor
  · intro h
    rcases mem_A_or_B hq (C.Q_sub (C.T_sub hp)) hpq with h' | h'
    · exact h'
    exfalso
    -- `Q − B p` is preconnected, contains `p ∈ B q` and a point of `A q`, but not `q`
    obtain ⟨a, ⟨haQ, hap⟩, haq⟩ := C.commonA p hp q hq
    have hD := side_A hp
    have hqD : q ∉ C.Q \ C.B p := fun hh => hh.2 h
    have := subset_B_of_preconn hq hD (diff_subset.trans C.Q_sub) hqD
      ⟨C.T_sub hp, notMem_B hp⟩ h'
    exact notMem_B_of_A hq haq (this ⟨haQ, notMem_B_of_A hp hap⟩)
  · intro h
    rcases mem_A_or_B hp (C.Q_sub (C.T_sub hq)) hpq.symm with h' | h'
    · exfalso
      obtain ⟨b, ⟨hbQ, hbp⟩, hbq⟩ := C.commonB p hp q hq
      have hD := side_B hp
      have hqD : q ∉ C.Q \ C.A p := fun hh => hh.2 h'
      have := subset_A_of_preconn hq hD (diff_subset.trans C.Q_sub) hqD
        ⟨C.T_sub hp, notMem_A hp⟩ h
      exact notMem_A_of_B hq hbq (this ⟨hbQ, notMem_A_of_B hp hbp⟩)
    · exact h'

theorem lt_total {p q : X} (hp : p ∈ C.T) (hq : q ∈ C.T) (hpq : p ≠ q) :
    C.lt p q ∨ C.lt q p := by
  rcases mem_A_or_B hq (C.Q_sub (C.T_sub hp)) hpq with h | h
  · exact Or.inl ((lt_iff hp hq hpq).2 h)
  · exact Or.inr h

theorem lt_asymm {p q : X} (hp : p ∈ C.T) (hq : q ∈ C.T) (h : C.lt p q) : ¬ C.lt q p := by
  intro h'
  have hpq : p ≠ q := by rintro rfl; exact notMem_B hp h
  exact notMem_B_of_A hq ((lt_iff hp hq hpq).1 h) h'

theorem lt_irrefl {p : X} (hp : p ∈ C.T) : ¬ C.lt p p := notMem_B hp

theorem ne_of_lt {p q : X} (hp : p ∈ C.T) (h : C.lt p q) : p ≠ q := by
  rintro rfl; exact notMem_B hp h

/-- Nesting of the `B`-sides (Whyburn's (1.2)(b)). -/
theorem B_sub {p q : X} (hp : p ∈ C.T) (hq : q ∈ C.T) (h : C.lt p q) :
    C.Q ∩ C.B q ⊆ C.B p := by
  have hpA : p ∈ C.A q := (lt_iff hp hq (ne_of_lt hp h)).1 h
  have hD := side_B hq
  have hpD : p ∉ C.Q \ C.A q := fun hh => hh.2 hpA
  have := subset_B_of_preconn hp hD (diff_subset.trans C.Q_sub) hpD
    ⟨C.T_sub hq, notMem_A hq⟩ h
  rintro z ⟨hzQ, hzB⟩
  exact this ⟨hzQ, notMem_A_of_B hq hzB⟩

/-- Nesting of the `A`-sides (Whyburn's (1.2)(b)). -/
theorem A_sub {p q : X} (hp : p ∈ C.T) (hq : q ∈ C.T) (h : C.lt p q) :
    C.Q ∩ C.A p ⊆ C.A q := by
  have hpA : p ∈ C.A q := (lt_iff hp hq (ne_of_lt hp h)).1 h
  have hD := side_A hp
  have hqD : q ∉ C.Q \ C.B p := fun hh => hh.2 h
  have := subset_A_of_preconn hq hD (diff_subset.trans C.Q_sub) hqD
    ⟨C.T_sub hp, notMem_B hp⟩ hpA
  rintro z ⟨hzQ, hzA⟩
  exact this ⟨hzQ, notMem_B_of_A hp hzA⟩

theorem lt_trans {p q r : X} (hp : p ∈ C.T) (hq : q ∈ C.T) (hr : r ∈ C.T) (h1 : C.lt p q)
    (h2 : C.lt q r) : C.lt p r :=
  B_sub hp hq h1 ⟨C.T_sub hr, h2⟩

/-- Points of `R` in the closure of `B x ∩ A y` lie in `B x ∩ A y` or are `x` or `y`. -/
theorem closure_BA {x y : X} (hx : x ∈ C.T) (hy : y ∈ C.T) :
    closure (C.B x ∩ C.A y) ∩ C.R ⊆ (C.B x ∩ C.A y) ∪ {x, y} := by
  rintro z ⟨hzc, hzR⟩
  by_cases hzx : z = x
  · exact Or.inr (Or.inl hzx)
  by_cases hzy : z = y
  · exact Or.inr (Or.inr hzy)
  left
  constructor
  · rcases mem_A_or_B hx hzR hzx with h | h
    · exfalso
      obtain ⟨w, hwA, hwB, -⟩ := mem_closure_iff.1 hzc _ (C.isOpen_A x hx) h
      exact notMem_B_of_A hx hwA hwB
    · exact h
  · rcases mem_A_or_B hy hzR hzy with h | h
    · exact h
    · exfalso
      obtain ⟨w, hwB, -, hwA⟩ := mem_closure_iff.1 hzc _ (C.isOpen_B y hy) h
      exact notMem_B_of_A hy hwA hwB

/-- The interval `M x y` is closed in `R`. -/
theorem M_closed {x y : X} (hx : x ∈ C.T) (hy : y ∈ C.T) : closure (C.M x y) ∩ C.R ⊆ C.M x y := by
  rintro z ⟨hzc, hzR⟩
  have hzQ : z ∈ C.Q := C.closed_in ⟨closure_mono inter_subset_left hzc, hzR⟩
  refine ⟨hzQ, ?_⟩
  have h1 : C.M x y ⊆ (C.B x ∩ C.A y) ∪ {x, y} := inter_subset_right
  have h2 := closure_mono h1 hzc
  have hfin : IsClosed ({x, y} : Set X) := (Set.toFinite _).isClosed
  rw [closure_union, hfin.closure_eq] at h2
  rcases h2 with h | h
  · exact closure_BA hx hy ⟨h, hzR⟩
  · exact Or.inr h

/-- The interval `M x y` is preconnected. -/
theorem M_isPreconnected {x y : X} (hx : x ∈ C.T) (hy : y ∈ C.T) (hxy : C.lt x y) :
    IsPreconnected (C.M x y) := by
  -- `D = Q − A x` is preconnected and contains `y`; cut it at `y`
  set D := C.Q \ C.A x
  have hD : IsPreconnected D := side_B hx
  have hyD : y ∈ D := ⟨C.T_sub hy, notMem_A_of_B hx hxy⟩
  have h := isPreconnected_side (B := C.B y) (A := C.A y) hD hyD (C.isOpen_A y hy)
    (C.isOpen_B y hy) (fun z hz => mem_A_or_B hy (C.Q_sub hz.1.1) hz.2)
    (fun z _ hzA => notMem_B_of_A hy hzA)
  rw [diff_singleton_eq_self (notMem_B hy)] at h
  convert h using 1
  ext z
  simp only [M, D, mem_inter_iff, mem_union, mem_insert_iff, mem_singleton_iff, mem_diff]
  constructor
  · rintro ⟨hzQ, ⟨hzB, hzA⟩ | rfl | rfl⟩
    · exact ⟨⟨hzQ, notMem_A_of_B hx hzB⟩, notMem_B_of_A hy hzA⟩
    · exact ⟨⟨hzQ, notMem_A hx⟩, notMem_B_of_A hy ((lt_iff hx hy (ne_of_lt hx hxy)).1 hxy)⟩
    · exact ⟨⟨hzQ, notMem_A_of_B hx hxy⟩, notMem_B hy⟩
  · rintro ⟨⟨hzQ, hzA⟩, hzB⟩
    refine ⟨hzQ, ?_⟩
    by_cases hzx : z = x
    · exact Or.inr (Or.inl hzx)
    by_cases hzy : z = y
    · exact Or.inr (Or.inr hzy)
    left
    exact ⟨(mem_A_or_B hx (C.Q_sub hzQ) hzx).resolve_left hzA,
      (mem_A_or_B hy (C.Q_sub hzQ) hzy).resolve_right hzB⟩

/-- An interval inside a larger one lies in the open part `B x ∩ A y`. -/
theorem M_sub_BA {x y x' y' : X} (hx : x ∈ C.T) (hy : y ∈ C.T) (hx' : x' ∈ C.T) (hy' : y' ∈ C.T)
    (h1 : C.lt x x') (h2 : C.lt y' y) (h3 : C.lt x' y') : C.M x' y' ⊆ C.B x ∩ C.A y := by
  rintro z ⟨hzQ, hz⟩
  refine ⟨?_, ?_⟩
  · rcases hz with ⟨hzB, -⟩ | rfl | rfl
    · exact B_sub hx hx' h1 ⟨hzQ, hzB⟩
    · exact h1
    · exact lt_trans hx hx' hy' h1 h3
  · rcases hz with ⟨-, hzA⟩ | rfl | rfl
    · exact A_sub hy' hy h2 ⟨hzQ, hzA⟩
    · exact (lt_iff hx' hy (ne_of_lt hx' (lt_trans hx' hy' hy h3 h2))).1
        (lt_trans hx' hy' hy h3 h2)
    · exact (lt_iff hy' hy (ne_of_lt hy' h2)).1 h2

theorem M_mono_left {x x' y : X} (hx : x ∈ C.T) (hx' : x' ∈ C.T) (hy : y ∈ C.T)
    (h1 : C.lt x x') (h3 : C.lt x' y) : C.M x' y ⊆ C.M x y := by
  rintro z ⟨hzQ, hz⟩
  refine ⟨hzQ, ?_⟩
  rcases hz with ⟨hzB, hzA⟩ | rfl | rfl
  · exact Or.inl ⟨B_sub hx hx' h1 ⟨hzQ, hzB⟩, hzA⟩
  · exact Or.inl ⟨h1, (lt_iff hx' hy (ne_of_lt hx' h3)).1 h3⟩
  · exact Or.inr (Or.inr rfl)

theorem M_mono_right {x y y' : X} (hx : x ∈ C.T) (hy : y ∈ C.T) (hy' : y' ∈ C.T)
    (h2 : C.lt y' y) (h3 : C.lt x y') : C.M x y' ⊆ C.M x y := by
  rintro z ⟨hzQ, hz⟩
  refine ⟨hzQ, ?_⟩
  rcases hz with ⟨hzB, hzA⟩ | rfl | rfl
  · exact Or.inl ⟨hzB, A_sub hy' hy h2 ⟨hzQ, hzA⟩⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl ⟨h3, (lt_iff hy' hy (ne_of_lt hy' h2)).1 h2⟩

/-! ### Countability of the exceptional points -/

/-- Whyburn's (2.1) for the chain: all but countably many points are good. -/
theorem countable_not_good [SecondCountableTopology X] : {p ∈ C.T | ¬ C.Good p}.Countable := by
  have h1 := countable_not_mem_closure_of_lt (T := C.T) C.lt id C.preds
    (fun p hp q hq hpq => lt_total hp hq hpq) (fun p hp q _ h => ⟨hp, h⟩)
  have h2 := countable_not_mem_closure_of_lt (T := C.T) (fun p q => C.lt q p) id C.succs
    (fun p hp q hq hpq => (lt_total hp hq hpq).symm) (fun p hp q _ h => ⟨hp, h⟩)
  refine (h1.union h2).mono ?_
  rintro p ⟨hp, hg⟩
  simp only [Good, not_and_or] at hg
  rcases hg with h | h
  · exact Or.inl ⟨hp, h⟩
  · exact Or.inr ⟨hp, h⟩

/-- Between a point `p` and a good point `q > p` there are points of the chain arbitrarily near
`q`. -/
theorem exists_pred_between {p q : X} (hp : p ∈ C.T) (hg : C.Good q)
    (h : C.lt p q) {N : Set X} (hN : N ∈ 𝓝 q) : ∃ x ∈ C.T, C.lt p x ∧ C.lt x q ∧ x ∈ N := by
  have hBN : C.B p ∩ N ∈ 𝓝 q := Filter.inter_mem ((C.isOpen_B p hp).mem_nhds h) hN
  obtain ⟨x, ⟨hxB, hxN⟩, hxT, hxq⟩ := mem_closure_iff_nhds.1 hg.1 _ hBN
  exact ⟨x, hxT, hxB, hxq, hxN⟩

/-- Between a good point `q` and a point `p > q` there are points of the chain arbitrarily near
`q`. -/
theorem exists_succ_between {p q : X} (hp : p ∈ C.T) (hq : q ∈ C.T) (hg : C.Good q)
    (h : C.lt q p) {N : Set X} (hN : N ∈ 𝓝 q) : ∃ y ∈ C.T, C.lt q y ∧ C.lt y p ∧ y ∈ N := by
  have hqA : q ∈ C.A p := (lt_iff hq hp (ne_of_lt hq h)).1 h
  have hAN : C.A p ∩ N ∈ 𝓝 q := Filter.inter_mem ((C.isOpen_A p hp).mem_nhds hqA) hN
  obtain ⟨y, ⟨hyA, hyN⟩, hyT, hqy⟩ := mem_closure_iff_nhds.1 hg.2 _ hAN
  have hyp : y ≠ p := by rintro rfl; exact notMem_A hp hyA
  exact ⟨y, hyT, hqy, (lt_iff hyT hp hyp).2 hyA, hyN⟩

theorem Res_sub_Q {p : X} : C.Res p ⊆ C.Q := fun _ hz => hz.1

/-- Residues of good points are ordered like the points: if `p < q`, `Res q ⊆ B p`. -/
theorem Res_sub_B {p q : X} (hp : p ∈ C.T) (hg : C.Good q) (h : C.lt p q) :
    C.Res q ⊆ C.B p := by
  intro z hz
  obtain ⟨x, hxT, hpx, hxq, -⟩ := exists_pred_between hp hg h Filter.univ_mem
  obtain ⟨y, hyT, hyq⟩ : (C.succs q).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have := hg.2
    rw [hne, closure_empty] at this
    exact this
  have := (hz.2.2 x hxT y hyT hxq hyq).1
  exact B_sub hp hxT hpx ⟨hz.1, this⟩

/-- Residues of good points are ordered like the points: if `q < p`, `Res q ⊆ A p`. -/
theorem Res_sub_A {p q : X} (hp : p ∈ C.T) (hq : q ∈ C.T) (hg : C.Good q) (h : C.lt q p) :
    C.Res q ⊆ C.A p := by
  intro z hz
  obtain ⟨y, hyT, hqy, hyp, -⟩ := exists_succ_between hp hq hg h Filter.univ_mem
  obtain ⟨x, hxT, hxq⟩ : (C.preds q).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have := hg.1
    rw [hne, closure_empty] at this
    exact this
  have := (hz.2.2 x hxT y hyT hxq hqy).2
  exact A_sub hyT hp hyp ⟨hz.1, this⟩

/-- All but countably many good points have empty residue (the removal step of Whyburn's (2.2)). -/
theorem countable_res [SecondCountableTopology X] :
    {p ∈ C.T | C.Good p ∧ (C.Res p).Nonempty}.Countable := by
  classical
  set T' := {p ∈ C.T | C.Good p ∧ (C.Res p).Nonempty}
  let z : X → X := fun p => if h : (C.Res p).Nonempty then h.some else p
  have hz : ∀ p ∈ T', z p ∈ C.Res p := by
    rintro p ⟨-, -, h⟩
    simp only [z, dif_pos h]
    exact h.some_mem
  set Pm : X → Set X := fun p => z '' {q ∈ T' | C.lt q p}
  set Pp : X → Set X := fun p => z '' {q ∈ T' | C.lt p q}
  have h1 := countable_not_mem_closure_of_lt (T := T') C.lt z Pm
    (fun p hp q hq hpq => lt_total hp.1 hq.1 hpq) (fun p hp q _ h => ⟨p, ⟨hp, h⟩, rfl⟩)
  have h2 := countable_not_mem_closure_of_lt (T := T') (fun p q => C.lt q p) z Pp
    (fun p hp q hq hpq => (lt_total hp.1 hq.1 hpq).symm) (fun p hp q _ h => ⟨p, ⟨hp, h⟩, rfl⟩)
  refine (h1.union h2).mono ?_
  intro p hp
  have hzp := hz p hp
  rcases mem_A_or_B hp.1 (C.Q_sub hzp.1) hzp.2.1 with hA | hB
  · -- `z p ∈ A p`, while the residues of the successors lie in `B p`
    right
    refine ⟨hp, fun hcl => ?_⟩
    have hsub : Pp p ⊆ C.B p := by
      rintro _ ⟨q, hq, rfl⟩
      exact Res_sub_B hp.1 hq.1.2.1 hq.2 (hz q hq.1)
    obtain ⟨w, hwA, hwP⟩ := mem_closure_iff.1 hcl _ (C.isOpen_A p hp.1) hA
    exact notMem_B_of_A hp.1 hwA (hsub hwP)
  · left
    refine ⟨hp, fun hcl => ?_⟩
    have hsub : Pm p ⊆ C.A p := by
      rintro _ ⟨q, hq, rfl⟩
      exact Res_sub_A hp.1 hq.1.1 hq.1.2.1 hq.2 (hz q hq.1)
    obtain ⟨w, hwB, hwP⟩ := mem_closure_iff.1 hcl _ (C.isOpen_B p hp.1) hB
    exact notMem_A_of_B hp.1 hwB (hsub hwP)

/-! ### Small intervals and order 2 -/

/-- **Small intervals.** About a good point with empty residue, if a closed ball about `p` is
compact and lies in `R`, some interval `M x y` (`x < p < y`) lies in the open ball. -/
theorem exists_small_interval {p : X} (hp : p ∈ C.T) (hg : C.Good p) (hres : C.Res p = ∅)
    {ρ : ℝ} (hρ : 0 < ρ) (hK : IsCompact (closedBall p ρ)) (hKR : closedBall p ρ ⊆ C.R) :
    ∃ x ∈ C.T, ∃ y ∈ C.T, C.lt x p ∧ C.lt p y ∧ C.M x y ⊆ ball p ρ := by
  by_contra hcon
  push_neg at hcon
  have hpM : ∀ {x y}, x ∈ C.T → y ∈ C.T → C.lt x p → C.lt p y → p ∈ C.M x y :=
    fun hx hy hxp hpy => ⟨C.T_sub hp, Or.inl ⟨hxp, (lt_iff hp hy (ne_of_lt hp hpy)).1 hpy⟩⟩
  let ι := {xy : X × X // xy.1 ∈ C.T ∧ xy.2 ∈ C.T ∧ C.lt xy.1 p ∧ C.lt p xy.2}
  obtain ⟨x0, hx0T, hx0p⟩ : (C.preds p).Nonempty := by
    by_contra hne; rw [not_nonempty_iff_eq_empty] at hne
    have := hg.1; rw [hne, closure_empty] at this; exact this
  obtain ⟨y0, hy0T, hy0p⟩ : (C.succs p).Nonempty := by
    by_contra hne; rw [not_nonempty_iff_eq_empty] at hne
    have := hg.2; rw [hne, closure_empty] at this; exact this
  haveI : Nonempty ι := ⟨⟨(x0, y0), hx0T, hy0T, hx0p, hy0p⟩⟩
  let K : ι → Set X := fun i => sphere p ρ ∩ C.M i.1.1 i.1.2
  have hsph : sphere p ρ ⊆ C.R := sphere_subset_closedBall.trans hKR
  have hKcl : ∀ i, IsClosed (K i) := by
    intro i
    refine closure_subset_iff_isClosed.1 fun z hz => ?_
    have h1 : z ∈ sphere p ρ := closure_minimal inter_subset_left isClosed_sphere hz
    exact ⟨h1, M_closed i.2.1 i.2.2.1 ⟨closure_mono inter_subset_right hz, hsph h1⟩⟩
  have hKc : ∀ i, IsCompact (K i) := fun i =>
    hK.of_isClosed_subset (hKcl i) (inter_subset_left.trans sphere_subset_closedBall)
  have hKne : ∀ i, (K i).Nonempty := by
    rintro ⟨⟨x, y⟩, hx, hy, hxp, hpy⟩
    obtain ⟨w, hwM, hw⟩ := not_subset.1 (hcon x hx y hy hxp hpy)
    have hconn := M_isPreconnected hx hy (lt_trans hx hp hy hxp hpy)
    have hρw : ρ ∈ Icc (dist p p) (dist w p) := by
      rw [dist_self]; exact ⟨hρ.le, not_lt.1 (by simpa [mem_ball] using hw)⟩
    obtain ⟨u, huM, hu⟩ := hconn.intermediate_value (hpM hx hy hxp hpy) hwM
      (continuous_id.dist continuous_const).continuousOn hρw
    exact ⟨u, by simpa [mem_sphere] using hu, huM⟩
  have hdir : Directed (· ⊇ ·) K := by
    rintro ⟨⟨x1, y1⟩, hx1, hy1, hx1p, hpy1⟩ ⟨⟨x2, y2⟩, hx2, hy2, hx2p, hpy2⟩
    -- the larger of the two left ends and the smaller of the two right ends
    obtain ⟨x3, hx3, hx3p, hl1, hl2⟩ : ∃ x3 ∈ C.T, C.lt x3 p ∧
        (C.M x3 y1 ⊆ C.M x1 y1 ∧ C.M x3 y2 ⊆ C.M x1 y2) ∧
        (C.M x3 y1 ⊆ C.M x2 y1 ∧ C.M x3 y2 ⊆ C.M x2 y2) := by
      by_cases h12 : x1 = x2
      · subst h12; exact ⟨x1, hx1, hx1p, ⟨le_rfl, le_rfl⟩, ⟨le_rfl, le_rfl⟩⟩
      rcases lt_total hx1 hx2 h12 with h | h
      · exact ⟨x2, hx2, hx2p, ⟨M_mono_left hx1 hx2 hy1 h (lt_trans hx2 hp hy1 hx2p hpy1),
          M_mono_left hx1 hx2 hy2 h (lt_trans hx2 hp hy2 hx2p hpy2)⟩, ⟨le_rfl, le_rfl⟩⟩
      · exact ⟨x1, hx1, hx1p, ⟨le_rfl, le_rfl⟩, ⟨M_mono_left hx2 hx1 hy1 h
          (lt_trans hx1 hp hy1 hx1p hpy1), M_mono_left hx2 hx1 hy2 h
          (lt_trans hx1 hp hy2 hx1p hpy2)⟩⟩
    obtain ⟨y3, hy3, hpy3, hr1, hr2⟩ : ∃ y3 ∈ C.T, C.lt p y3 ∧
        C.M x3 y3 ⊆ C.M x3 y1 ∧ C.M x3 y3 ⊆ C.M x3 y2 := by
      by_cases h12 : y1 = y2
      · subst h12; exact ⟨y1, hy1, hpy1, le_rfl, le_rfl⟩
      rcases lt_total hy1 hy2 h12 with h | h
      · exact ⟨y1, hy1, hpy1, le_rfl, M_mono_right hx3 hy2 hy1 h
          (lt_trans hx3 hp hy1 hx3p hpy1)⟩
      · exact ⟨y2, hy2, hpy2, M_mono_right hx3 hy1 hy2 h (lt_trans hx3 hp hy2 hx3p hpy2),
          le_rfl⟩
    refine ⟨⟨(x3, y3), hx3, hy3, hx3p, hpy3⟩, ?_, ?_⟩
    · exact inter_subset_inter_right _ (hr1.trans hl1.1)
    · exact inter_subset_inter_right _ (hr2.trans hl2.2)
  obtain ⟨w, hw⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed K hdir hKne
    hKc hKcl
  rw [mem_iInter] at hw
  have hw0 := hw ⟨(x0, y0), hx0T, hy0T, hx0p, hy0p⟩
  have hwRes : w ∈ C.Res p := by
    refine ⟨hw0.2.1, ?_, ?_⟩
    · rintro rfl
      have := hw0.1
      rw [mem_sphere, dist_self] at this
      exact hρ.ne this
    · intro x hx y hy hxp hpy
      obtain ⟨x', hx', hxx', hx'p, -⟩ := exists_pred_between hx hg hxp Filter.univ_mem
      obtain ⟨y', hy', hpy', hy'y, -⟩ := exists_succ_between hy hp hg hpy Filter.univ_mem
      exact M_sub_BA hx hy hx' hy' hxx' hy'y (lt_trans hx' hp hy' hx'p hpy')
        (hw ⟨(x', y'), hx', hy', hx'p, hpy'⟩).2
  rw [hres] at hwRes
  exact hwRes

/-- **Cut wire in a compact ball.** If an interval `M x y` about `p` lies in the open ball
`B(p, ρ)` whose closure is compact and lies in `R`, there is an open set `V ∋ p` in the ball with
`frontier V ⊆ {x, y}`. -/
theorem exists_open_frontier_pair {p x y : X} (hp : p ∈ C.T) (hx : x ∈ C.T) (hy : y ∈ C.T)
    (hxp : C.lt x p) (hpy : C.lt p y) {ρ : ℝ} (hK : IsCompact (closedBall p ρ))
    (hKR : closedBall p ρ ⊆ C.R) (hM : C.M x y ⊆ ball p ρ) :
    ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ ball p ρ ∧ frontier V ⊆ {x, y} := by
  set O := C.B x ∩ C.A y
  have hpO : p ∈ O := ⟨hxp, (lt_iff hp hy (ne_of_lt hp hpy)).1 hpy⟩
  have hpM : p ∈ C.M x y := ⟨C.T_sub hp, Or.inl hpO⟩
  have hpball : p ∈ ball p ρ := hM hpM
  set F := closure O ∩ closedBall p ρ
  have hFc : IsCompact F := hK.of_isClosed_subset (isClosed_closure.inter isClosed_closedBall)
    inter_subset_right
  have hpF : p ∈ F := ⟨subset_closure hpO, ball_subset_closedBall hpball⟩
  -- the component of `p` in `F` lies in `M x y`, hence misses the sphere
  have hCM : connectedComponentIn F p ⊆ C.M x y := by
    have hCF : connectedComponentIn F p ⊆ F := connectedComponentIn_subset _ _
    have hFR : F ⊆ C.R := inter_subset_right.trans hKR
    have hCQ : connectedComponentIn F p ⊆ C.Q :=
      C.Q_max _ isPreconnected_connectedComponentIn (hCF.trans hFR)
        ⟨p, mem_connectedComponentIn hpF, C.T_sub hp⟩
    intro z hz
    exact ⟨hCQ hz, closure_BA hx hy ⟨(hCF hz).1, hFR (hCF hz)⟩⟩
  have hdisj : Disjoint (connectedComponentIn F p) (sphere p ρ) := by
    rw [disjoint_left]
    intro z hz hzs
    have := hM (hCM hz)
    rw [mem_ball] at this; rw [mem_sphere] at hzs
    exact this.ne hzs
  obtain ⟨G, hG, hpG, hWcl, hWs⟩ :=
    exists_clopen_of_connectedComponentIn_disjoint hFc isClosed_sphere hpF hdisj
  have hWball : F ∩ G ⊆ ball p ρ := by
    intro z hz
    have h1 : dist z p ≤ ρ := hz.1.2
    have h2 : z ∉ sphere p ρ := disjoint_left.1 hWs hz
    rw [mem_sphere] at h2
    exact lt_of_le_of_ne h1 h2
  set V := O ∩ G ∩ ball p ρ
  have hVo : IsOpen V :=
    (((C.isOpen_B x hx).inter (C.isOpen_A y hy)).inter hG).inter isOpen_ball
  have hVW : V ⊆ F ∩ G := fun z hz =>
    ⟨⟨subset_closure hz.1.1, ball_subset_closedBall hz.2⟩, hz.1.2⟩
  refine ⟨V, hVo, ⟨⟨hpO, hpG⟩, hpball⟩, inter_subset_right, ?_⟩
  intro z hz
  rw [hVo.frontier_eq] at hz
  have hzW : z ∈ F ∩ G := closure_minimal hVW hWcl hz.1
  have hzR : z ∈ C.R := hKR hzW.1.2
  rcases closure_BA hx hy ⟨closure_mono (inter_subset_left.trans inter_subset_left) hz.1, hzR⟩
    with h | h
  · exact absurd ⟨⟨h, hzW.2⟩, hWball hzW⟩ hz.2
  · exact h

/-- A good point with empty residue, interior to `R`, in a locally compact space, is of order
`≤ 2`. -/
theorem orderLE_two [LocallyCompactSpace X] {p : X} (hp : p ∈ C.T) (hR : C.R ∈ 𝓝 p)
    (hg : C.Good p) (hres : C.Res p = ∅) : OrderLE p 2 := by
  intro N hN
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds p
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (Filter.inter_mem hKn hR) hN)
  have hρ : 0 < ε / 2 := half_pos hε
  have hcb : closedBall p (ε / 2) ⊆ ball p ε := closedBall_subset_ball (half_lt_self hε)
  have hcbK : IsCompact (closedBall p (ε / 2)) :=
    hKc.of_isClosed_subset isClosed_closedBall fun z hz => (hεsub (hcb hz)).1.1
  have hcbR : closedBall p (ε / 2) ⊆ C.R := fun z hz => (hεsub (hcb hz)).1.2
  obtain ⟨x, hx, y, hy, hxp, hpy, hM⟩ := exists_small_interval hp hg hres hρ hcbK hcbR
  obtain ⟨V, hVo, hpV, hVb, hVf⟩ := exists_open_frontier_pair hp hx hy hxp hpy hcbK hcbR hM
  refine ⟨V, hVo, hpV, fun z hz => (hεsub (hcb (ball_subset_closedBall (hVb hz)))).2,
    (Set.toFinite {x, y}).subset hVf, ?_⟩
  calc (frontier V).ncard ≤ ({x, y} : Set X).ncard := ncard_le_ncard hVf (Set.toFinite _)
    _ ≤ 2 := by
      rw [show ({x, y} : Set X) = insert x {y} from rfl]
      exact (ncard_insert_le _ _).trans (by rw [ncard_singleton])

/-- **A chain of points none of which is of order `≤ 2` is countable** (locally compact separable
metric space, `R` open). -/
theorem countable_of_not_orderLE_two [LocallyCompactSpace X] [SecondCountableTopology X]
    (hR : IsOpen C.R) (hT : ∀ p ∈ C.T, ¬ OrderLE p 2) : C.T.Countable := by
  refine ((countable_not_good (C := C)).union (countable_res (C := C))).mono fun p hp => ?_
  by_cases hg : C.Good p
  · right
    refine ⟨hp, hg, ?_⟩
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    exact hT p hp (orderLE_two hp (hR.mem_nhds (C.Q_sub (C.T_sub hp))) hg hne)
  · exact Or.inl ⟨hp, hg⟩

end SepChain

end Chain

end HPC.Jones
