import Mathlib

/-!
# Batch 94, §1: Moore's non-cut-point theorem (Nadler, *Continuum Theory*, 6.3–6.7)

General topology for a compact connected `T₁` space; no metric. The two definitions and the five
statements are the §1 part of the batch-94 skeleton (`HPC/Plane/NonCut51.lean`), moved here
unchanged so that the general theorem depends on Mathlib only; `NonCut51.lean` imports this file.

Besides Nadler's steps, the file uses one reformulation throughout: a separation `Y = P | Q` is the
same as a decomposition `Y = P ∪ Q` into two nonempty *separated* sets
(`closure P ∩ Q = ∅ = P ∩ closure Q`), and a preconnected subset of `P ∪ Q` lies in `P` or in `Q`
(`subset_side_of_isPreconnected`).
-/

namespace HPC.Plane

open Set Topology

section NonCut

variable {X : Type*} [TopologicalSpace X]

/-- `Y = P | Q` in Nadler's notation: `P`, `Q` nonempty, disjoint, open in `Y`, with union `Y`.
Stated for subsets of `X` with openness relative to `Y`. -/
def IsSeparation (Y P Q : Set X) : Prop :=
  P.Nonempty ∧ Q.Nonempty ∧ Disjoint P Q ∧ P ∪ Q = Y ∧ IsOpen ((↑) ⁻¹' P : Set Y) ∧
    IsOpen ((↑) ⁻¹' Q : Set Y)

/-- A *cut point* of the space: its complement is disconnected. -/
def IsCutPoint (x : X) : Prop := ¬ IsConnected ({x}ᶜ : Set X)

/-! ## Separations and separated sets -/

theorem IsSeparation.symm {Y P Q : Set X} (h : IsSeparation Y P Q) : IsSeparation Y Q P :=
  ⟨h.2.1, h.1, h.2.2.1.symm, by rw [union_comm]; exact h.2.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

theorem IsSeparation.subset_left {Y P Q : Set X} (h : IsSeparation Y P Q) : P ⊆ Y :=
  h.2.2.2.1 ▸ subset_union_left

theorem IsSeparation.subset_right {Y P Q : Set X} (h : IsSeparation Y P Q) : Q ⊆ Y :=
  h.symm.subset_left

/-- A relatively open piece of a separation lies in some open set missing the other piece. -/
theorem IsSeparation.exists_open_right {Y P Q : Set X} (h : IsSeparation Y P Q) :
    ∃ t : Set X, IsOpen t ∧ Q ⊆ t ∧ Disjoint t P ∧ t ∩ Y = Q := by
  obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.mp h.2.2.2.2.2
  have key : ∀ y ∈ Y, y ∈ t ↔ y ∈ Q := fun y hy => by
    have := congrArg (fun s : Set Y => (⟨y, hy⟩ : Y) ∈ s) hteq
    simpa using this
  refine ⟨t, ht, fun q hq => (key q (h.subset_right hq)).mpr hq, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro y hyt hyP
    exact Set.disjoint_left.mp h.2.2.1 hyP ((key y (h.subset_left hyP)).mp hyt)
  · ext y
    exact ⟨fun ⟨hyt, hyY⟩ => (key y hyY).mp hyt,
      fun hyQ => ⟨(key y (h.subset_right hyQ)).mpr hyQ, h.subset_right hyQ⟩⟩

theorem IsSeparation.disjoint_closure_left {Y P Q : Set X} (h : IsSeparation Y P Q) :
    Disjoint (closure P) Q := by
  obtain ⟨t, ht, hQt, htP, -⟩ := h.exists_open_right
  exact (htP.symm.closure_left ht).mono_right hQt

theorem IsSeparation.disjoint_closure_right {Y P Q : Set X} (h : IsSeparation Y P Q) :
    Disjoint P (closure Q) :=
  h.symm.disjoint_closure_left.symm

/-- In an open `Y`, the pieces of a separation are open. -/
theorem IsSeparation.isOpen_right {Y P Q : Set X} (h : IsSeparation Y P Q) (hY : IsOpen Y) :
    IsOpen Q := by
  obtain ⟨t, ht, -, -, hteq⟩ := h.exists_open_right
  rw [← hteq]; exact ht.inter hY

/-- Two nonempty separated sets with union `Y` form a separation of `Y`. -/
theorem IsSeparation.of_separated {Y P Q : Set X} (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPQ : P ∪ Q = Y) (h1 : Disjoint (closure P) Q) (h2 : Disjoint P (closure Q)) :
    IsSeparation Y P Q := by
  have key : ∀ {P Q : Set X}, P ∪ Q = Y → Disjoint P (closure Q) →
      IsOpen ((↑) ⁻¹' P : Set Y) := by
    intro P Q hPQ h2
    refine isOpen_induced_iff.mpr ⟨(closure Q)ᶜ, isClosed_closure.isOpen_compl, ?_⟩
    ext ⟨y, hy⟩
    simp only [mem_preimage, mem_compl_iff]
    constructor
    · intro hyQ
      rw [← hPQ] at hy
      rcases hy with hy | hy
      · exact hy
      · exact absurd (subset_closure hy) hyQ
    · intro hyP hyQ
      exact Set.disjoint_left.mp h2 hyP hyQ
  exact ⟨hP, hQ, h2.mono_right subset_closure, hPQ, key hPQ h2,
    key (by rw [union_comm]; exact hPQ) h1.symm⟩

/-- **A preconnected set inside a union of two separated sets lies in one of them.** -/
theorem subset_side_of_isPreconnected {T P Q : Set X} (hT : IsPreconnected T) (hTPQ : T ⊆ P ∪ Q)
    (h1 : Disjoint (closure P) Q) (h2 : Disjoint P (closure Q)) : T ⊆ P ∨ T ⊆ Q := by
  have hcov : T ⊆ (closure Q)ᶜ ∪ (closure P)ᶜ := fun x hx => by
    rcases hTPQ hx with h' | h'
    · exact Or.inl fun hc => Set.disjoint_left.mp h2 h' hc
    · exact Or.inr fun hc => Set.disjoint_left.mp h1 hc h'
  have hemp : T ∩ ((closure Q)ᶜ ∩ (closure P)ᶜ) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    intro hx hQ hP
    rcases hTPQ hx with h' | h'
    · exact hP (subset_closure h')
    · exact hQ (subset_closure h')
  rcases isPreconnected_iff_subset_of_disjoint.mp hT (closure Q)ᶜ (closure P)ᶜ
      isClosed_closure.isOpen_compl isClosed_closure.isOpen_compl hcov hemp with h | h
  · left
    intro x hx
    rcases hTPQ hx with h' | h'
    · exact h'
    · exact absurd (subset_closure h') (h hx)
  · right
    intro x hx
    rcases hTPQ hx with h' | h'
    · exact absurd (subset_closure h') (h hx)
    · exact h'

/-- A separation of a preconnected set's ambient superset: the preconnected set lies on one side. -/
theorem IsSeparation.subset_or_subset {Y P Q T : Set X} (h : IsSeparation Y P Q)
    (hT : IsPreconnected T) (hTY : T ⊆ Y) : T ⊆ P ∨ T ⊆ Q :=
  subset_side_of_isPreconnected hT (h.2.2.2.1 ▸ hTY) h.disjoint_closure_left h.disjoint_closure_right

/-- A connected space is not the union of two nonempty separated sets. -/
theorem eq_empty_of_separated_cover [ConnectedSpace X] {P Q : Set X} (hPQ : P ∪ Q = univ)
    (h1 : Disjoint (closure P) Q) (h2 : Disjoint P (closure Q)) (hQ : Q.Nonempty) : P = ∅ := by
  rcases subset_side_of_isPreconnected isPreconnected_univ hPQ.ge h1 h2 with h | h
  · obtain ⟨q, hq⟩ := hQ
    exact absurd (subset_closure hq) (Set.disjoint_left.mp h2 (h (mem_univ q)))
  · ext x
    simp only [mem_empty_iff_false, iff_false]
    intro hx
    exact Set.disjoint_left.mp h2 hx (subset_closure (h (mem_univ x)))

/-- A nonempty disconnected set has a separation, with any given point on the right. -/
theorem exists_separation_of_not_isConnected {Y : Set X} {c : X} (hc : c ∈ Y)
    (h : ¬ IsConnected Y) : ∃ P Q, IsSeparation Y P Q ∧ c ∈ Q := by
  have hpc : ¬ IsPreconnected Y := fun hp => h ⟨⟨c, hc⟩, hp⟩
  rw [isPreconnected_iff_subset_of_disjoint] at hpc
  push_neg at hpc
  obtain ⟨u, v, hu, hv, hsub, hdisj, hnu, hnv⟩ := hpc
  obtain ⟨a, haY, hav⟩ := not_subset.mp hnv
  obtain ⟨b, hbY, hbu⟩ := not_subset.mp hnu
  have hau : a ∈ u := (hsub haY).resolve_right hav
  have hbv : b ∈ v := (hsub hbY).resolve_left hbu
  have hsep : IsSeparation Y (Y ∩ u) (Y ∩ v) := by
    refine ⟨⟨a, haY, hau⟩, ⟨b, hbY, hbv⟩, ?_, ?_, ?_, ?_⟩
    · rw [Set.disjoint_left]
      rintro x ⟨hxY, hxu⟩ ⟨-, hxv⟩
      have : x ∈ Y ∩ (u ∩ v) := ⟨hxY, hxu, hxv⟩
      rw [hdisj] at this; exact this
    · ext x
      exact ⟨fun h => h.elim (·.1) (·.1), fun hx => (hsub hx).elim (fun h => Or.inl ⟨hx, h⟩)
        (fun h => Or.inr ⟨hx, h⟩)⟩
    · have : ((↑) ⁻¹' (Y ∩ u) : Set Y) = (↑) ⁻¹' u := by ext ⟨y, hy⟩; simp
      rw [this]; exact hu.preimage continuous_subtype_val
    · have : ((↑) ⁻¹' (Y ∩ v) : Set Y) = (↑) ⁻¹' v := by ext ⟨y, hy⟩; simp
      rw [this]; exact hv.preimage continuous_subtype_val
  rcases (hsub hc) with hcu | hcv
  · exact ⟨_, _, hsep.symm, hc, hcu⟩
  · exact ⟨_, _, hsep, hc, hcv⟩

/-! ## Nadler 6.3, 6.4 -/

/-- The core of 6.3, with `C` on the `u` side. -/
theorem union_subset_of_separation_aux [ConnectedSpace X] {C A B u v : Set X}
    (hAB : IsSeparation Cᶜ A B) (hu : IsOpen u) (hv : IsOpen v) (hsub : A ∪ C ⊆ u ∪ v)
    (hdisj : (A ∪ C) ∩ (u ∩ v) = ∅) (hCu : C ⊆ u) : A ∪ C ⊆ u := by
  have hno : ∀ x, x ∈ A ∪ C → x ∈ u → x ∈ v → False := fun x hx hxu hxv => by
    have : x ∈ (A ∪ C) ∩ (u ∩ v) := ⟨hx, hxu, hxv⟩
    rw [hdisj] at this; exact this
  set P := A ∩ v with hP
  set W := (A ∩ u) ∪ C with hW
  have hWu : W ⊆ u := union_subset inter_subset_right hCu
  have hWAC : W ⊆ A ∪ C := union_subset_union_left _ inter_subset_left
  have hcov : P ∪ (W ∪ B) = univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true]
    by_cases hxC : x ∈ C
    · exact Or.inr (Or.inl (Or.inr hxC))
    · have : x ∈ A ∪ B := hAB.2.2.2.1 ▸ hxC
      rcases this with hxA | hxB
      · rcases hsub (Or.inl hxA) with h | h
        · exact Or.inr (Or.inl (Or.inl ⟨hxA, h⟩))
        · exact Or.inl ⟨hxA, h⟩
      · exact Or.inr (Or.inr hxB)
  have h1 : Disjoint (closure P) (W ∪ B) := by
    rw [Set.disjoint_left]
    intro x hxP hx
    rcases hx with hxW | hxB
    · obtain ⟨z, hzu, hzA, hzv⟩ := mem_closure_iff.mp hxP u hu (hWu hxW)
      exact hno z (Or.inl hzA) hzu hzv
    · exact Set.disjoint_left.mp hAB.disjoint_closure_left (closure_mono inter_subset_left hxP)
        hxB
  have h2 : Disjoint P (closure (W ∪ B)) := by
    rw [Set.disjoint_left, closure_union]
    rintro x ⟨hxA, hxv⟩ hx
    rcases hx with hxW | hxB
    · obtain ⟨z, hzv, hzW⟩ := mem_closure_iff.mp hxW v hv hxv
      exact hno z (hWAC hzW) (hWu hzW) hzv
    · exact Set.disjoint_left.mp hAB.disjoint_closure_right hxA hxB
  have hP0 : P = ∅ := eq_empty_of_separated_cover hcov h1 h2
    (hAB.2.1.mono subset_union_right)
  intro x hx
  rcases hx with hxA | hxC
  · rcases hsub (Or.inl hxA) with h | h
    · exact h
    · have : x ∈ P := ⟨hxA, h⟩
      rw [hP0] at this; exact this.elim
  · exact hCu hxC

/-- **Nadler 6.3.** If `S` is connected, `C ⊆ S` connected and `S ∖ C = A | B`, then `A ∪ C` is
connected. -/
theorem isConnected_union_of_separation [ConnectedSpace X] {C A B : Set X} (hC : IsConnected C)
    (hAB : IsSeparation Cᶜ A B) : IsConnected (A ∪ C) := by
  refine ⟨hC.nonempty.mono subset_union_right, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hsub hdisj
  rcases isPreconnected_iff_subset_of_disjoint.mp hC.isPreconnected u v hu hv
      (subset_union_right.trans hsub) (by
        rw [← subset_empty_iff, ← hdisj]
        exact inter_subset_inter_left _ subset_union_right) with h | h
  · exact Or.inl (union_subset_of_separation_aux hAB hu hv hsub hdisj h)
  · refine Or.inr (union_subset_of_separation_aux hAB hv hu (by rw [union_comm u v] at hsub; exact hsub)
      (by rw [inter_comm u v] at hdisj; exact hdisj) h)

/-- **Nadler 6.4.** If `S ∖ {x} = K | L`, `S ∖ {y} = M | N`, `x ∈ M`, `y ∈ K`, then
`N ∪ {y} ⊆ K`. -/
theorem nadler_6_4 [ConnectedSpace X] {x y : X} {K L M N : Set X}
    (hx : IsSeparation {x}ᶜ K L) (hy : IsSeparation {y}ᶜ M N) (hxM : x ∈ M) (hyK : y ∈ K) :
    N ∪ {y} ⊆ K := by
  have hxy : x ≠ y := fun e => hy.subset_left hxM (e ▸ rfl)
  have hconn := isConnected_union_of_separation isConnected_singleton hy.symm
  have hsub : N ∪ {y} ⊆ {x}ᶜ := by
    rintro z (hz | hz)
    · rintro rfl
      exact Set.disjoint_left.mp hy.2.2.1 hxM hz
    · rw [mem_singleton_iff.mp hz]
      exact fun h => hxy (mem_singleton_iff.mp h).symm
  rcases hx.subset_or_subset hconn.isPreconnected hsub with h | h
  · exact h
  · exact absurd (h (Or.inr rfl)) (Set.disjoint_left.mp hx.2.2.1 hyK)

/-! ## Nadler 6.6 -/

/-- One side of 6.6: the `U`-side of a separation `S ∖ {c} = U | V` contains a non-cut point. -/
theorem exists_nonCutPoint_left [CompactSpace X] [ConnectedSpace X] [T1Space X]
    {c : X} {U V : Set X} (h : IsSeparation {c}ᶜ U V) : ∃ u ∈ U, ¬ IsCutPoint u := by
  classical
  by_contra hall
  push_neg at hall
  have hUc : ∀ {x}, x ∈ U → x ≠ c := fun hx e => h.subset_left hx (e ▸ rfl)
  have hex : ∀ x : X, ∃ P Q : Set X, x ∈ U → IsSeparation {x}ᶜ P Q ∧ c ∈ Q := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨P, Q, hPQ, hc⟩ :=
        exists_separation_of_not_isConnected (Y := {x}ᶜ) (c := c)
          (fun e => hUc hx (mem_singleton_iff.mp e).symm)
          (hall x hx)
      exact ⟨P, Q, fun _ => ⟨hPQ, hc⟩⟩
    · exact ⟨∅, ∅, fun h => absurd h hx⟩
  choose Ux Vx hsep using hex
  set A : X → Set X := fun x => Ux x ∪ {x} with hA
  -- (i) `A x ⊆ U` (6.4)
  have hAU : ∀ {x}, x ∈ U → A x ⊆ U := fun hx =>
    nadler_6_4 h (hsep _ hx).1.symm (hsep _ hx).2 hx
  -- (ii) `A x` is closed: its complement `V_x` is open
  have hAcl : ∀ {x}, x ∈ U → IsClosed (A x) := by
    intro x hx
    have hVo : IsOpen (Vx x) := (hsep x hx).1.isOpen_right isOpen_compl_singleton
    have : (A x)ᶜ = Vx x := by
      ext z
      simp only [hA, mem_compl_iff, mem_union, mem_singleton_iff, not_or]
      constructor
      · rintro ⟨hzU, hzx⟩
        have : z ∈ Ux x ∪ Vx x := (hsep x hx).1.2.2.2.1 ▸ hzx
        exact this.resolve_left hzU
      · intro hzV
        exact ⟨fun hzU => Set.disjoint_left.mp (hsep x hx).1.2.2.1 hzU hzV,
          fun e => (hsep x hx).1.subset_right hzV e⟩
    rw [← isOpen_compl_iff, this]; exact hVo
  -- (iii) `y ∈ U_x` implies `A y ⊆ U_x`
  have hstep : ∀ {x y}, x ∈ U → y ∈ Ux x → A y ⊆ Ux x := by
    intro x y hx hy
    have hyU : y ∈ U := hAU hx (Or.inl hy)
    have hxy : x ∈ ({y}ᶜ : Set X) := fun e =>
      (hsep x hx).1.subset_left hy (mem_singleton_iff.mpr (mem_singleton_iff.mp e).symm)
    rw [← (hsep y hyU).1.2.2.2.1] at hxy
    rcases hxy with hxUy | hxVy
    · exfalso
      have := nadler_6_4 (hsep y hyU).1 (hsep x hx).1 hy hxUy
      exact Set.disjoint_left.mp (hsep y hyU).1.2.2.1 (this (Or.inl (hsep x hx).2))
        (hsep y hyU).2
    · exact nadler_6_4 (hsep x hx).1 (hsep y hyU).1.symm hxVy hy
  have hnot : ∀ {x y}, x ∈ U → y ∈ Ux x → x ∉ A y := fun hx hy hxA =>
    (hsep _ hx).1.subset_left (hstep hx hy hxA) rfl
  -- (iv) the maximal principle
  obtain ⟨m, hm⟩ := zorn_superset (A '' U) (by
    intro ch hch hchain
    rcases ch.eq_empty_or_nonempty with he | hne
    · obtain ⟨u, hu⟩ := h.1
      exact ⟨A u, ⟨u, hu, rfl⟩, by simp [he]⟩
    · haveI : Nonempty ch := hne.to_subtype
      obtain ⟨p, hp⟩ := IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (fun a ha b hb => (hchain.total ha hb).elim (fun h => ⟨a, ha, subset_rfl, h⟩)
          (fun h => ⟨b, hb, h, subset_rfl⟩))
        (fun s hs => by obtain ⟨x, -, rfl⟩ := hch hs; exact ⟨x, Or.inr rfl⟩)
        (fun s hs => by obtain ⟨x, hx, rfl⟩ := hch hs; exact (hAcl hx).isCompact)
        (fun s hs => by obtain ⟨x, hx, rfl⟩ := hch hs; exact hAcl hx)
      obtain ⟨s₀, hs₀⟩ := hne
      obtain ⟨x₀, hx₀, rfl⟩ := hch hs₀
      have hpU : p ∈ U := hAU hx₀ (mem_sInter.mp hp _ hs₀)
      refine ⟨A p, ⟨p, hpU, rfl⟩, fun s hs => ?_⟩
      obtain ⟨x, hx, rfl⟩ := hch hs
      rcases mem_sInter.mp hp _ hs with hpx | hpx
      · exact (hstep hx hpx).trans subset_union_left
      · rw [mem_singleton_iff.mp hpx])
  obtain ⟨⟨x, hx, rfl⟩, hmin⟩ := hm
  obtain ⟨q, hq⟩ := (hsep x hx).1.1
  have hqU : q ∈ U := hAU hx (Or.inl hq)
  have hle : A x ⊆ A q := hmin ⟨q, hqU, rfl⟩ ((hstep hx hq).trans subset_union_left)
  exact hnot hx hq (hle (Or.inr rfl))

/-- **Nadler 6.6 (Moore's non-cut-point existence theorem).** In a nondegenerate compact connected
`T₁` space with a cut point `c`, `S ∖ {c} = U | V`, there is a non-cut point in `U` and one in
`V`. (The hypothesis `[Nontrivial X]` of the skeleton is implied by the separation and is not
used.) -/
theorem exists_nonCutPoint_of_cut [CompactSpace X] [ConnectedSpace X] [T1Space X]
    {c : X} {U V : Set X} (h : IsSeparation {c}ᶜ U V) :
    (∃ u ∈ U, ¬ IsCutPoint u) ∧ (∃ v ∈ V, ¬ IsCutPoint v) :=
  ⟨exists_nonCutPoint_left h, exists_nonCutPoint_left h.symm⟩

/-- **Nadler 6.6, second clause**: a nondegenerate compact connected `T₁` space has two non-cut
points. -/
theorem exists_two_nonCutPoints [CompactSpace X] [ConnectedSpace X] [T1Space X] [Nontrivial X] :
    ∃ a b : X, a ≠ b ∧ ¬ IsCutPoint a ∧ ¬ IsCutPoint b := by
  by_cases hc : ∃ c : X, IsCutPoint c
  · obtain ⟨c, hc⟩ := hc
    obtain ⟨d, hdc⟩ := exists_ne c
    obtain ⟨U, V, hUV, -⟩ := exists_separation_of_not_isConnected (Y := {c}ᶜ) hdc hc
    obtain ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩ := exists_nonCutPoint_of_cut hUV
    exact ⟨u, v, fun e => Set.disjoint_left.mp hUV.2.2.1 hu (e ▸ hv), hu', hv'⟩
  · push_neg at hc
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    exact ⟨a, b, hab, hc a, hc b⟩

/-- **Nadler 6.7.** No proper connected subset contains all the non-cut points. (Only
preconnectedness of `Z` is used; `[Nontrivial X]` of the skeleton is not needed.) -/
theorem not_subset_of_nonCutPoints [CompactSpace X] [ConnectedSpace X] [T1Space X]
    {Z : Set X} (hZ : IsConnected Z) (hne : Z ≠ univ) : ¬ {x | ¬ IsCutPoint x} ⊆ Z := by
  intro hsub
  obtain ⟨c, hc⟩ := (ne_univ_iff_exists_notMem Z).mp hne
  have hcut : IsCutPoint c := by
    by_contra h; exact hc (hsub h)
  obtain ⟨z, hz⟩ := hZ.nonempty
  have hzc : z ∈ ({c}ᶜ : Set X) := fun e => hc (mem_singleton_iff.mp e ▸ hz)
  obtain ⟨U, V, hUV, -⟩ := exists_separation_of_not_isConnected hzc hcut
  have hZc : Z ⊆ {c}ᶜ := fun y hy e => hc (mem_singleton_iff.mp e ▸ hy)
  obtain ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩ := exists_nonCutPoint_of_cut hUV
  rcases hUV.subset_or_subset hZ.isPreconnected hZc with h | h
  · exact Set.disjoint_left.mp hUV.2.2.1 (h (hsub hv')) hv
  · exact Set.disjoint_left.mp hUV.2.2.1 hu (h (hsub hu'))

end NonCut

end HPC.Plane
