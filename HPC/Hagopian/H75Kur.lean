import HPC.Hagopian.H75Defs
import HPC.Plane.SorgenfreyDefs

/-!
# Batch 155: Kuratowski §48 III–VII, the family `D` of an irreducible continuum

Throughout, `Y` is a compact metric space which is irreducible between two points `a ≠ b`
(no proper subcontinuum contains both). Following Kuratowski, *Topology* II, §48 III, let `D` be
the family of closed domains (`D = cl int D`) which are connected and contain `a` (together with
`∅`). We prove:

* `irr_compl_continuum`: for a subcontinuum `K ∋ a` with `b ∉ K`, `cl (Y − K)` is a continuum;
* `irr_no_hole`: the basic "no hole" lemma behind Kuratowski III, Theorem 1;
* `IsDElt.chain`: `D` is a chain (Kuratowski III);
* `IsDElt.subset_interior`: `D₁ ⊊ D₂` implies `D₁ ⊆ int D₂`;
* `IsDElt.closure_diff`: `cl (D₂ − D₁)` is a continuum (Kuratowski VII, proof of Theorem 2);
* `IsDElt.exists_between`: if every subcontinuum with interior is decomposable, `D` has no jumps
  (Kuratowski VII, Theorems 1–2).

The passage to an admissible map with nowhere dense layers (Kuratowski VII, Theorems 3–5) is in
`H75KurMap.lean`.
-/

namespace HPC.Hagopian

open Set Topology HPC.Plane

section Kur

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y] {a b : Y}

/-- Irreducibility between `a` and `b`, in the space `Y` itself. -/
def IrrBetween (a b : Y) : Prop :=
  ∀ K : Set Y, Fold.Q78.IsContinuum K → a ∈ K → b ∈ K → K = univ

theorem isContinuum_univ_of [ConnectedSpace Y] (y : Y) : Fold.Q78.IsContinuum (univ : Set Y) :=
  ⟨isCompact_univ, ⟨y, mem_univ _⟩, isPreconnected_univ⟩

omit [CompactSpace Y] in
theorem isContinuum_union {K L : Set Y} (hK : Fold.Q78.IsContinuum K) (hL : Fold.Q78.IsContinuum L)
    (h : (K ∩ L).Nonempty) : Fold.Q78.IsContinuum (K ∪ L) :=
  ⟨hK.1.union hL.1, hK.2.nonempty.mono subset_union_left,
    hK.2.isPreconnected.union' h hL.2.isPreconnected⟩

/-- **Kuratowski II, Theorem 3** (in the form used): for a subcontinuum `K` containing `a` but not
`b`, the closure of `Y − K` is a continuum. -/
theorem irr_compl_continuum [ConnectedSpace Y] (hirr : IrrBetween a b) {K : Set Y}
    (hK : Fold.Q78.IsContinuum K) (haK : a ∈ K) (hbK : b ∉ K) :
    Fold.Q78.IsContinuum (closure Kᶜ) := by
  obtain ⟨K', hK', -, hK'cl, hbK', hne⟩ := exists_continuum_bump_open (isContinuum_univ_of a)
    hK.1.isClosed.isOpen_compl (mem_univ b) hbK (fun h => h (mem_univ a) haK)
  rw [univ_inter] at hK'cl
  obtain ⟨x, hxK', hxK⟩ := hne
  have hxK : x ∈ K := not_not.1 hxK
  have hU := hirr _ (isContinuum_union hK hK' ⟨x, hxK, hxK'⟩) (Or.inl haK) (Or.inr hbK')
  have hsub : Kᶜ ⊆ K' := fun y hy => by
    have : y ∈ K ∪ K' := hU ▸ mem_univ y
    exact this.resolve_left hy
  have : closure Kᶜ = K' :=
    Subset.antisymm (closure_minimal hsub hK'.1.isClosed) hK'cl
  rw [this]; exact hK'

omit [CompactSpace Y] in
/-- `b ∈ cl (Y − K)` -/
theorem mem_closure_compl_of_not_mem {K : Set Y} (hbK : b ∉ K) : b ∈ closure Kᶜ :=
  subset_closure hbK

/-- **No hole.** Let `K ∋ a` be a subcontinuum not containing `b`, and `U ⊆ K` a nonempty open set
not containing `a` that is closed in `int K` (`cl U ∩ int K ⊆ U`). This is impossible: the
component of `K − U` containing `a` reaches `cl U − U ⊆ cl (Y − K)`, and with `cl (Y − K)` it
gives a continuum containing `a` and `b` that misses `U`. -/
theorem irr_no_hole [ConnectedSpace Y] (hirr : IrrBetween a b) {K : Set Y}
    (hK : Fold.Q78.IsContinuum K) (haK : a ∈ K) (hbK : b ∉ K) {U : Set Y} (hU : IsOpen U)
    (hUne : U.Nonempty) (hUK : U ⊆ K) (haU : a ∉ U) (hcl : closure U ∩ interior K ⊆ U) : False := by
  have hFcl : IsClosed (K \ U) := hK.1.isClosed.sdiff hU
  obtain ⟨u, hu⟩ := hUne
  have hFne : K \ U ≠ K := fun h => (h.symm ▸ hUK hu : u ∈ K \ U).2 hu
  obtain ⟨K₁, hK₁, hK₁F, haK₁, x, hxK₁, hxcl⟩ :=
    exists_continuum_bump_closed hK hFcl diff_subset hFne ⟨haK, haU⟩
  have hKF : K \ (K \ U) = U := by
    rw [diff_diff_cancel_left hUK]
  rw [hKF] at hxcl
  have hxF := hK₁F hxK₁
  have hxint : x ∉ interior K := fun h => hxF.2 (hcl ⟨hxcl, h⟩)
  have hxR : x ∈ closure Kᶜ := by rw [closure_compl]; exact hxint
  have hR := irr_compl_continuum hirr hK haK hbK
  have hall := hirr _ (isContinuum_union hK₁ hR ⟨x, hxK₁, hxR⟩) (Or.inl haK₁)
    (Or.inr (subset_closure hbK))
  have : u ∈ K₁ ∪ closure Kᶜ := hall ▸ mem_univ u
  rcases this with h | h
  · exact (hK₁F h).2 hu
  · rw [closure_compl] at h
    exact h (interior_maximal hUK hU hu)

/-- The members of Kuratowski's family `D`: closed domains, connected, containing `a` if
nonempty. -/
def IsDElt (a : Y) (D : Set Y) : Prop :=
  closure (interior D) = D ∧ IsPreconnected D ∧ (D.Nonempty → a ∈ D)

omit [CompactSpace Y] in
theorem IsDElt.isClosed {D : Set Y} (hD : IsDElt a D) : IsClosed D :=
  hD.1 ▸ isClosed_closure

theorem IsDElt.isContinuum {D : Set Y} (hD : IsDElt a D) (hne : D.Nonempty) :
    Fold.Q78.IsContinuum D :=
  ⟨hD.isClosed.isCompact, hne, hD.2.1⟩

omit [CompactSpace Y] in
theorem isDElt_empty : IsDElt a (∅ : Set Y) := by
  refine ⟨by simp, isPreconnected_empty, fun h => absurd h (by simp)⟩

omit [CompactSpace Y] in
theorem isDElt_univ [ConnectedSpace Y] : IsDElt a (univ : Set Y) :=
  ⟨by simp, isPreconnected_univ, fun _ => mem_univ a⟩

/-- A member of `D` other than `Y` does not contain `b`. -/
theorem IsDElt.not_mem_b (hirr : IrrBetween a b) {D : Set Y} (hD : IsDElt a D) (hDu : D ≠ univ) :
    b ∉ D := fun hb => hDu (hirr D (hD.isContinuum ⟨b, hb⟩) (hD.2.2 ⟨b, hb⟩) hb)

omit [CompactSpace Y] in
/-- A closed domain not contained in a closed set `F` has interior points outside `F`. -/
theorem exists_interior_not_mem {D F : Set Y} (hD : closure (interior D) = D) (hF : IsClosed F)
    (h : ¬ D ⊆ F) : ∃ x ∈ interior D, x ∉ F := by
  by_contra hcon
  push_neg at hcon
  exact h (hD ▸ closure_minimal hcon hF)

/-- **Kuratowski III, Theorem 1 (the subcontinuum lemma).** If `K ∋ a` is a subcontinuum with
nonempty interior, `cl int K` belongs to `D`. -/
theorem isDElt_closure_interior [ConnectedSpace Y] (hirr : IrrBetween a b) {K : Set Y}
    (hK : Fold.Q78.IsContinuum K) (haK : a ∈ K) (hint : (interior K).Nonempty) :
    IsDElt a (closure (interior K)) := by
  by_cases hbK : b ∈ K
  · rw [hirr K hK haK hbK]; simpa using (isDElt_univ (a := a))
  refine ⟨closure_interior_idem, ?_, fun _ => ?_⟩
  · rw [isPreconnected_iff_subset_of_disjoint_closed]
    intro A B hA hB hsub hdis
    by_contra hcon
    push_neg at hcon
    obtain ⟨hA', hB'⟩ := hcon
    -- both parts meet `int K`
    have key : ∀ A B : Set Y, IsClosed A → IsClosed B → closure (interior K) ⊆ A ∪ B →
        closure (interior K) ∩ (A ∩ B) = ∅ → ¬ closure (interior K) ⊆ B → a ∉ interior K \ B →
        False := by
      intro A B hA hB hsub hdis hnB haU
      have hU : IsOpen (interior K \ B) := isOpen_interior.sdiff hB
      have hUne : (interior K \ B).Nonempty := by
        by_contra h0
        rw [not_nonempty_iff_eq_empty, diff_eq_empty] at h0
        exact hnB (closure_minimal h0 hB)
      refine irr_no_hole hirr hK haK hbK hU hUne (diff_subset.trans interior_subset) haU ?_
      rintro x ⟨hxcl, hxint⟩
      refine ⟨hxint, fun hxB => ?_⟩
      have hxA : x ∈ A := closure_minimal (fun y hy => (hsub (subset_closure hy.1)).resolve_right
        hy.2) hA hxcl
      have : x ∈ closure (interior K) ∩ (A ∩ B) := ⟨subset_closure hxint, hxA, hxB⟩
      rw [hdis] at this; exact this
    by_cases haB : a ∈ interior K \ B
    · exact key B A hB hA (by rw [union_comm]; exact hsub) (by rw [inter_comm B]; exact hdis) hA'
        (fun h => h.2 ((hsub (subset_closure haB.1)).resolve_right haB.2))
    · exact key A B hA hB hsub hdis hB' haB
  · by_contra haint
    obtain ⟨u, hu⟩ := hint
    refine irr_no_hole hirr hK haK hbK isOpen_interior ⟨u, hu⟩ interior_subset
      (fun h => haint (subset_closure h)) (fun x hx => hx.2)

/-- **Kuratowski III: `D` is a chain.** -/
theorem IsDElt.chain [ConnectedSpace Y] (hirr : IrrBetween a b) {D₁ D₂ : Set Y} (h₁ : IsDElt a D₁)
    (h₂ : IsDElt a D₂) : D₁ ⊆ D₂ ∨ D₂ ⊆ D₁ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h12, h21⟩ := hcon
  have hne₁ : D₁.Nonempty := by
    by_contra h; rw [not_nonempty_iff_eq_empty] at h; exact h12 (h ▸ empty_subset _)
  have hne₂ : D₂.Nonempty := by
    by_contra h; rw [not_nonempty_iff_eq_empty] at h; exact h21 (h ▸ empty_subset _)
  have ha₁ := h₁.2.2 hne₁
  have ha₂ := h₂.2.2 hne₂
  have hb₁ : b ∉ D₁ := h₁.not_mem_b hirr (fun h => h21 (h ▸ subset_univ _))
  have hb₂ : b ∉ D₂ := h₂.not_mem_b hirr (fun h => h12 (h ▸ subset_univ _))
  set K := D₁ ∪ D₂
  have hK : Fold.Q78.IsContinuum K := isContinuum_union (h₁.isContinuum hne₁)
    (h₂.isContinuum hne₂) ⟨a, ha₁, ha₂⟩
  have hR := irr_compl_continuum hirr hK (Or.inl ha₁) (fun h => h.elim hb₁ hb₂)
  have hbR : b ∈ closure Kᶜ := subset_closure (fun h => h.elim hb₁ hb₂)
  -- `cl (Y − K)` meets `K`
  obtain ⟨x, -, hxR, hxK⟩ := isPreconnected_closed_iff.1 isPreconnected_univ _ _ isClosed_closure
    hK.1.isClosed (fun y _ => by
      by_cases hy : y ∈ K
      · exact Or.inr hy
      · exact Or.inl (subset_closure hy)) ⟨b, mem_univ _, hbR⟩ ⟨a, mem_univ _, Or.inl ha₁⟩
  have side : ∀ D D' : Set Y, IsDElt a D → IsDElt a D' → a ∈ D → D ⊆ K → D' ⊆ K → ¬ D' ⊆ D →
      x ∈ D → False := by
    intro D D' hD hD' haD hDK hD'K hD'D hxD
    have hall := hirr _ (isContinuum_union (hD.isContinuum ⟨a, haD⟩) hR ⟨x, hxD, hxR⟩)
      (Or.inl haD) (Or.inr hbR)
    obtain ⟨y, hy, hyD⟩ := exists_interior_not_mem hD'.1 hD.isClosed hD'D
    have : y ∈ D ∪ closure Kᶜ := hall ▸ mem_univ y
    rcases this with h | h
    · exact hyD h
    · rw [closure_compl] at h; exact h (interior_mono hD'K hy)
  rcases hxK with h | h
  · exact side D₁ D₂ h₁ h₂ ha₁ subset_union_left subset_union_right h21 h
  · exact side D₂ D₁ h₂ h₁ ha₂ subset_union_right subset_union_left h12 h

/-- **Strictness.** If `D₁ ⊊ D₂` in `D`, then `D₁ ⊆ int D₂`. -/
theorem IsDElt.subset_interior [ConnectedSpace Y] (hirr : IrrBetween a b) {D₁ D₂ : Set Y}
    (h₁ : IsDElt a D₁) (h₂ : IsDElt a D₂) (h12 : D₁ ⊆ D₂) (hne : D₁ ≠ D₂) :
    D₁ ⊆ interior D₂ := by
  by_cases hu : D₂ = univ
  · rw [hu, interior_univ]; exact subset_univ _
  intro x hx
  by_contra hxi
  have hb₂ := h₂.not_mem_b hirr hu
  have ha₁ : a ∈ D₁ := h₁.2.2 ⟨x, hx⟩
  have hD₂ := h₂.isContinuum ⟨a, h12 ha₁⟩
  have hR := irr_compl_continuum hirr hD₂ (h12 ha₁) hb₂
  have hxR : x ∈ closure D₂ᶜ := by rw [closure_compl]; exact hxi
  have hall := hirr _ (isContinuum_union (h₁.isContinuum ⟨x, hx⟩) hR ⟨x, hx, hxR⟩)
    (Or.inl ha₁) (Or.inr (subset_closure hb₂))
  have h21 : ¬ D₂ ⊆ D₁ := fun h => hne (Subset.antisymm h12 h)
  obtain ⟨y, hy, hyD⟩ := exists_interior_not_mem h₂.1 h₁.isClosed h21
  have : y ∈ D₁ ∪ closure D₂ᶜ := hall ▸ mem_univ y
  rcases this with h | h
  · exact hyD h
  · rw [closure_compl] at h; exact h hy

omit [CompactSpace Y] in
/-- For a closed domain `D₂` and a closed `D₁`, `cl (D₂ − D₁) = cl (int D₂ − D₁)`. -/
theorem closure_diff_eq {D₁ D₂ : Set Y} (h₂ : closure (interior D₂) = D₂) (h₁ : IsClosed D₁) :
    closure (D₂ \ D₁) = closure (interior D₂ \ D₁) := by
  refine Subset.antisymm (closure_minimal ?_ isClosed_closure)
    (closure_mono (diff_subset_diff_left interior_subset))
  intro x ⟨hx2, hx1⟩
  have : x ∈ D₁ᶜ ∩ closure (interior D₂) := ⟨hx1, h₂.symm ▸ hx2⟩
  have := h₁.isOpen_compl.inter_closure this
  rwa [inter_comm, ← diff_eq] at this

omit [CompactSpace Y] in
/-- A point of `int D₂` outside `int D₁` lies in `cl (int D₂ − D₁)`. -/
theorem mem_closure_diff_of {D₁ D₂ : Set Y} {z : Y} (hz2 : z ∈ interior D₂)
    (hz1 : z ∉ interior D₁) : z ∈ closure (interior D₂ \ D₁) := by
  have hz : z ∈ interior D₂ ∩ closure D₁ᶜ := ⟨hz2, by rw [closure_compl]; exact hz1⟩
  have := isOpen_interior.inter_closure hz
  rwa [← diff_eq] at this

/-- **Kuratowski VII, proof of Theorem 2.** If `D₁ ⊊ D₂` in `D`, then `cl (D₂ − D₁)` is a
continuum. -/
theorem IsDElt.closure_diff [ConnectedSpace Y] (hirr : IrrBetween a b) {D₁ D₂ : Set Y}
    (h₁ : IsDElt a D₁) (h₂ : IsDElt a D₂) (h12 : D₁ ⊆ D₂) (hne : D₁ ≠ D₂) :
    Fold.Q78.IsContinuum (closure (D₂ \ D₁)) := by
  have h21 : ¬ D₂ ⊆ D₁ := fun h => hne (Subset.antisymm h12 h)
  obtain ⟨w, hw2, hw1⟩ := exists_interior_not_mem h₂.1 h₁.isClosed h21
  have hPne : (closure (D₂ \ D₁)).Nonempty := ⟨w, subset_closure ⟨interior_subset hw2, hw1⟩⟩
  refine ⟨isClosed_closure.isCompact, hPne, ?_⟩
  rcases eq_empty_or_nonempty D₁ with he | hD₁ne
  · rw [he, diff_empty, h₂.isClosed.closure_eq]; exact h₂.2.1
  have ha₁ := h₁.2.2 hD₁ne
  have hb₁ := h₁.not_mem_b hirr (fun h => h21 (h ▸ subset_univ _))
  by_cases hu : D₂ = univ
  · rw [hu, ← compl_eq_univ_diff]
    exact (irr_compl_continuum hirr (h₁.isContinuum hD₁ne) ha₁ hb₁).2.isPreconnected
  have hb₂ := h₂.not_mem_b hirr hu
  set P := closure (D₂ \ D₁) with hP
  set W := interior D₂ \ D₁ with hW
  have hPW : P = closure W := closure_diff_eq h₂.1 h₁.isClosed
  have hPD₂ : P ⊆ D₂ := closure_minimal diff_subset h₂.isClosed
  have hD₂P : D₂ ⊆ D₁ ∪ P := fun x hx => by
    by_cases h : x ∈ D₁
    · exact Or.inl h
    · exact Or.inr (subset_closure ⟨hx, h⟩)
  rw [isPreconnected_closed_iff]
  intro A' B' hA' hB' hPAB hPA hPB
  by_contra hcon
  rw [not_nonempty_iff_eq_empty] at hcon
  set A := P ∩ A'
  set B := P ∩ B'
  have hAc : IsClosed A := isClosed_closure.inter hA'
  have hBc : IsClosed B := isClosed_closure.inter hB'
  have hAB : ∀ z, z ∈ A → z ∈ B → False := fun z hzA hzB => by
    have : z ∈ P ∩ (A' ∩ B') := ⟨hzA.1, hzA.2, hzB.2⟩
    rw [hcon] at this; exact this
  -- `B` meets `D₁`
  have hBD₁ : (B ∩ D₁).Nonempty := by
    obtain ⟨z, -, hz1, hz2⟩ := isPreconnected_closed_iff.1 h₂.2.1 (D₁ ∪ A) B
      (h₁.isClosed.union hAc) hBc (fun x hx => by
        rcases hD₂P hx with h | h
        · exact Or.inl (Or.inl h)
        · rcases hPAB h with h' | h'
          · exact Or.inl (Or.inr ⟨h, h'⟩)
          · exact Or.inr ⟨h, h'⟩)
      (by obtain ⟨d, hd⟩ := hD₁ne; exact ⟨d, h12 hd, Or.inl hd⟩)
      (by obtain ⟨z, hz⟩ := hPB; exact ⟨z, hPD₂ hz.1, hz⟩)
    rcases hz1 with h | h
    · exact ⟨z, hz2, h⟩
    · exact (hAB z h hz2).elim
  -- the open set `U = W − B'`
  set U := W ∩ B'ᶜ
  have hUo : IsOpen U := (isOpen_interior.sdiff h₁.isClosed).inter hB'.isOpen_compl
  obtain ⟨p, hpP, hpA'⟩ := hPA
  have hpB' : p ∉ B' := fun h => hAB p ⟨hpP, hpA'⟩ ⟨hpP, h⟩
  obtain ⟨u, huB', huW⟩ : (B'ᶜ ∩ W).Nonempty :=
    mem_closure_iff.1 (hPW ▸ hpP) _ hB'.isOpen_compl hpB'
  have hR₂ := irr_compl_continuum hirr (h₂.isContinuum ⟨a, h12 ha₁⟩) (h12 ha₁) hb₂
  set R₁ := closure D₁ᶜ with hR₁def
  set R₂ := closure D₂ᶜ with hR₂def
  have hR₁ := irr_compl_continuum hirr (h₁.isContinuum hD₁ne) ha₁ hb₁
  have huR₂ : u ∉ R₂ := by
    rw [hR₂def, closure_compl]; exact not_not.2 huW.1
  have hFR₁ : B ∪ R₂ ⊆ R₁ := union_subset
    (inter_subset_left.trans (closure_mono (diff_subset_compl _ _)))
    (closure_mono (compl_subset_compl.2 h12))
  have huR₁ : u ∈ R₁ := subset_closure huW.2
  have hFne : B ∪ R₂ ≠ R₁ := fun h => by
    have : u ∈ B ∪ R₂ := h ▸ huR₁
    rcases this with h' | h'
    · exact huB' h'.2
    · exact huR₂ h'
  -- `R₁ − (B ∪ R₂) ⊆ A`
  have hdiffA : R₁ \ (B ∪ R₂) ⊆ A := by
    rintro z ⟨hzR₁, hzF⟩
    have hzR₂ : z ∉ R₂ := fun h => hzF (Or.inr h)
    have hz2 : z ∈ interior D₂ := by
      rw [hR₂def, closure_compl] at hzR₂; exact not_not.1 hzR₂
    have hz1 : z ∉ interior D₁ := by rw [hR₁def, closure_compl] at hzR₁; exact hzR₁
    have hzP : z ∈ P := hPW ▸ mem_closure_diff_of hz2 hz1
    rcases hPAB hzP with h | h
    · exact ⟨hzP, h⟩
    · exact (hzF (Or.inl ⟨hzP, h⟩)).elim
  have hbR₂ : b ∈ R₂ := subset_closure hb₂
  have hFpre : IsPreconnected (B ∪ R₂) := by
    refine isPreconnected_of_forall b fun y hy => ?_
    rcases hy with hyB | hyR
    · obtain ⟨K, hK, hKF, hyK, z, hzK, hzcl⟩ := exists_continuum_bump_closed hR₁
        (hBc.union isClosed_closure) hFR₁ hFne (Or.inl hyB)
      have hzA : z ∈ A := closure_minimal hdiffA hAc hzcl
      have hzR₂ : z ∈ R₂ := (hKF hzK).resolve_left (fun h => hAB z hzA h)
      exact ⟨K ∪ R₂, union_subset hKF subset_union_right, Or.inr hbR₂, Or.inl hyK,
        hK.2.isPreconnected.union' ⟨z, hzK, hzR₂⟩ hR₂.2.isPreconnected⟩
    · exact ⟨R₂, subset_union_right, hbR₂, hyR, hR₂.2.isPreconnected⟩
  have hL : Fold.Q78.IsContinuum (D₁ ∪ (B ∪ R₂)) := by
    refine isContinuum_union (h₁.isContinuum hD₁ne)
      ⟨(hBc.union isClosed_closure).isCompact, ⟨b, Or.inr hbR₂⟩, hFpre⟩ ?_
    obtain ⟨z, hzB, hzD⟩ := hBD₁
    exact ⟨z, hzD, Or.inl hzB⟩
  have hall := hirr _ hL (Or.inl ha₁) (Or.inr (Or.inr hbR₂))
  have : u ∈ D₁ ∪ (B ∪ R₂) := hall ▸ mem_univ u
  rcases this with h | h | h
  · exact huW.2 h
  · exact huB' h.2
  · exact huR₂ h

/-- **Kuratowski VII, Theorems 1–2: no jumps.** If every subcontinuum with nonempty interior is
decomposable, then between any two members `D₁ ⊊ D₂` of `D` lies a third. -/
theorem IsDElt.exists_between [ConnectedSpace Y] (hirr : IrrBetween a b)
    (hH : ∀ K : Set Y, Fold.Q78.IsContinuum K → (interior K).Nonempty →
      ¬ Fold.Q78.IsIndecomposable K)
    {D₁ D₂ : Set Y} (h₁ : IsDElt a D₁) (h₂ : IsDElt a D₂) (h12 : D₁ ⊆ D₂) (hne : D₁ ≠ D₂) :
    ∃ D, IsDElt a D ∧ D₁ ⊆ D ∧ D ≠ D₁ ∧ D ⊆ D₂ ∧ D ≠ D₂ := by
  have h21 : ¬ D₂ ⊆ D₁ := fun h => hne (Subset.antisymm h12 h)
  have hPc := h₁.closure_diff hirr h₂ h12 hne
  set P := closure (D₂ \ D₁) with hP
  set W := interior D₂ \ D₁ with hW
  have hPW : P = closure W := closure_diff_eq h₂.1 h₁.isClosed
  have hPD₂ : P ⊆ D₂ := closure_minimal diff_subset h₂.isClosed
  have hWP : W ⊆ P := hPW ▸ subset_closure
  have hWo : IsOpen W := isOpen_interior.sdiff h₁.isClosed
  obtain ⟨w, hw2, hw1⟩ := exists_interior_not_mem h₂.1 h₁.isClosed h21
  have hintP : (interior P).Nonempty := ⟨w, interior_maximal hWP hWo ⟨hw2, hw1⟩⟩
  have hdec := hH P hPc hintP
  simp only [Fold.Q78.IsIndecomposable, hPc, true_and, not_forall, not_or] at hdec
  obtain ⟨A, B, hA, hB, hAP, hBP, hABP, hAne, hBne⟩ := hdec
  -- the main step, for the part `A` with `D₁ ∪ A` a continuum containing `a`
  have main : ∀ A B : Set Y, Fold.Q78.IsContinuum (D₁ ∪ A) → a ∈ D₁ ∪ A →
      Fold.Q78.IsContinuum A → Fold.Q78.IsContinuum B → A ⊆ P → A ∪ B = P → A ≠ P → B ≠ P →
      ∃ D, IsDElt a D ∧ D₁ ⊆ D ∧ D ≠ D₁ ∧ D ⊆ D₂ ∧ D ≠ D₂ := by
    intro A B hK haK hA hB hAP hABP hAne hBne
    set K := D₁ ∪ A
    have hBP : B ⊆ P := hABP ▸ subset_union_right
    have hKD₂ : K ⊆ D₂ := union_subset h12 (hAP.trans hPD₂)
    have hnot : ¬ interior K ⊆ D₁ := by
      intro hsub
      have h1 : W \ B ⊆ interior K := interior_maximal
        (fun x hx => Or.inr (((hABP ▸ hWP hx.1 : x ∈ A ∪ B)).resolve_right hx.2))
        (hWo.sdiff hB.1.isClosed)
      have h2 : W ⊆ B := fun x hx => by
        by_contra hxB
        exact hx.2 (hsub (h1 ⟨hx, hxB⟩))
      exact hBne (Subset.antisymm hBP (hPW ▸ closure_minimal h2 hB.1.isClosed))
    have hint : (interior K).Nonempty := by
      obtain ⟨x, hx, -⟩ := not_subset.1 hnot; exact ⟨x, hx⟩
    refine ⟨closure (interior K), isDElt_closure_interior hirr hK haK hint, ?_, ?_, ?_, ?_⟩
    · exact h₁.1 ▸ closure_mono (interior_mono subset_union_left)
    · intro h
      exact hnot (fun x hx => h ▸ subset_closure hx)
    · exact (closure_minimal interior_subset hK.1.isClosed).trans hKD₂
    · intro h
      have hsub : D₂ ⊆ K := h ▸ closure_minimal interior_subset hK.1.isClosed
      have : P ⊆ A := closure_minimal (fun x hx => (hsub hx.1).resolve_left hx.2) hA.1.isClosed
      exact hAne (Subset.antisymm hAP this)
  rcases eq_empty_or_nonempty D₁ with he | hD₁ne
  · have hPeq : P = D₂ := by rw [hP, he, diff_empty, h₂.isClosed.closure_eq]
    have ha₂ : a ∈ D₂ := h₂.2.2 (by obtain ⟨z, hz⟩ := hintP; exact ⟨z, hPD₂ (interior_subset hz)⟩)
    have haAB : a ∈ A ∪ B := hABP ▸ hPeq ▸ ha₂
    rcases haAB with h | h
    · exact main A B (by rw [he, empty_union]; exact hA) (by rw [he, empty_union]; exact h) hA hB hAP
        hABP hAne hBne
    · exact main B A (by rw [he, empty_union]; exact hB) (by rw [he, empty_union]; exact h) hB hA hBP
        (by rw [union_comm]; exact hABP) hBne hAne
  · have ha₁ := h₁.2.2 hD₁ne
    have hD₂P : D₂ ⊆ D₁ ∪ P := fun x hx => by
      by_cases h : x ∈ D₁
      · exact Or.inl h
      · exact Or.inr (subset_closure ⟨hx, h⟩)
    obtain ⟨z, -, hz1, hzP⟩ := isPreconnected_closed_iff.1 h₂.2.1 D₁ P h₁.isClosed
      isClosed_closure hD₂P (by obtain ⟨d, hd⟩ := hD₁ne; exact ⟨d, h12 hd, hd⟩)
      (by obtain ⟨z, hz⟩ := hintP; exact ⟨z, hPD₂ (interior_subset hz), interior_subset hz⟩)
    have hzAB : z ∈ A ∪ B := hABP ▸ hzP
    rcases hzAB with h | h
    · exact main A B (isContinuum_union (h₁.isContinuum hD₁ne) hA ⟨z, hz1, h⟩) (Or.inl ha₁) hA hB hAP
        hABP hAne hBne
    · exact main B A (isContinuum_union (h₁.isContinuum hD₁ne) hB ⟨z, hz1, h⟩) (Or.inl ha₁) hB hA hBP
        (by rw [union_comm]; exact hABP) hBne hAne

end Kur

end HPC.Hagopian
