import HPC.Plane.NonCut51Gen
import HPC.Moore.ArcChar

/-!
# Batch 146: the cut-point characterizations of arcs and simple closed curves

General topology, Mathlib only (with batch 94's `exists_two_nonCutPoints` and batch 137's
`isIrreducibleConnected_iff_arc`). Moore's 1925 Theorems 5–8 and 10 are instances of the results
here (`M25B5.lean`, `M25B9.lean`).

* `IsCutArc A B H`: `H` is compact and connected, contains `A ≠ B`, and is disconnected by the
  omission of any of its points other than `A` and `B` (Moore 1920, Definition 2; 1925, p. 417).
* `IsCutArc.irreducible`: such an `H` is irreducible between `A` and `B` (by Nadler 6.6: a point of
  `H − A − B` missing a connected set through `A`, `B` cuts off a piece with a non-cut point).
* `IsCutArc.exists_embedding`: in a metrizable space it is an embedded `[0, 1]`
  (`isIrreducibleConnected_iff_arc`); `isCutArc_range`: conversely.
* `exists_nonCut_diff`: a connected proper subset of a continuum misses a non-cut point
  (Nadler 6.7).
* `circle_char`: a nondegenerate continuum disconnected by the omission of any two of its points
  is, for any `p ≠ q` in it, the union of two cut-point arcs from `p` to `q` meeting only in `p`
  and `q` (Moore 1920, Theorem 4). Proof: first, no point is a cut point (else non-cut points on
  both sides, by Nadler 6.6, would give a pair whose omission leaves a connected set); then for a
  separation `J − p − q = U | V`, `U + p + q` is connected (a separation of it would make `p` or
  `q` a cut point) and each point of `U` disconnects it.
-/

namespace HPC.Moore

open Set Topology HPC.Plane

section General

variable {X : Type*} [TopologicalSpace X]

/-- **Cut-point arc** from `A` to `B`. -/
def IsCutArc (A B : X) (H : Set X) : Prop :=
  A ≠ B ∧ IsCompact H ∧ IsConnected H ∧ A ∈ H ∧ B ∈ H ∧
    ∀ x ∈ H, x ≠ A → x ≠ B → ¬ IsConnected (H \ {x})

/-- Connectedness is detected by an inducing map. -/
theorem isConnected_image_iff_of_isInducing {Y : Type*} [TopologicalSpace Y] {f : X → Y}
    (hf : IsInducing f) {s : Set X} : IsConnected (f '' s) ↔ IsConnected s := by
  rw [IsConnected, IsConnected, hf.isPreconnected_image, image_nonempty]

/-- Connectedness of a punctured subtype. -/
theorem isConnected_compl_singleton_subtype_iff {H : Set X} (x : H) :
    IsConnected ({x}ᶜ : Set H) ↔ IsConnected (H \ {(x : X)}) := by
  have himg : ((↑) : H → X) '' ({x}ᶜ : Set H) = H \ {(x : X)} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, fun h => hz (Subtype.ext h)⟩
    · rintro ⟨hy, hyx⟩
      exact ⟨⟨y, hy⟩, fun h => hyx (by rw [mem_singleton_iff] at h ⊢; rw [← h]), rfl⟩
  rw [← himg, isConnected_image_iff_of_isInducing IsInducing.subtypeVal]

theorem isCutPoint_subtype_iff {H : Set X} (x : H) :
    IsCutPoint x ↔ ¬ IsConnected (H \ {(x : X)}) := by
  rw [IsCutPoint, isConnected_compl_singleton_subtype_iff]

/-- Connectedness of a set of a subtype and of its image. -/
theorem isConnected_subtype_iff {H : Set X} (S : Set H) :
    IsConnected S ↔ IsConnected (((↑) : H → X) '' S) :=
  (isConnected_image_iff_of_isInducing IsInducing.subtypeVal).symm

/-- **Two non-cut points, in set form** (Nadler 6.6): a nondegenerate continuum has, for any `y`,
a non-cut point other than `y`. -/
theorem exists_nonCut_ne [T1Space X] {C : Set X} (hC : IsCompact C) (hCc : IsConnected C)
    (hCn : C.Nontrivial) (y : X) : ∃ u ∈ C, u ≠ y ∧ IsConnected (C \ {u}) := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  haveI : ConnectedSpace C := Subtype.connectedSpace hCc
  obtain ⟨a, ha, b, hb, hab⟩ := hCn
  haveI : Nontrivial C := ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩⟩
  obtain ⟨u, v, huv, hu, hv⟩ := exists_two_nonCutPoints (X := C)
  rw [isCutPoint_subtype_iff, not_not] at hu hv
  by_cases huy : (u : X) = y
  · refine ⟨v, v.2, fun h => huv (Subtype.ext (huy.trans h.symm)), hv⟩
  · exact ⟨u, u.2, huy, hu⟩

/-- **Nadler 6.6, set form**: if `x` cuts the continuum `C` and `L ⊆ C − x` is preconnected, there
is a non-cut point of `C` outside `L ∪ {x}`. -/
theorem exists_nonCut_off [T1Space X] {C : Set X} (hC : IsCompact C) (hCc : IsConnected C)
    {x : X} (hx : x ∈ C) (hne : (C \ {x}).Nonempty) (hcut : ¬ IsConnected (C \ {x}))
    {L : Set X} (hLC : L ⊆ C \ {x}) (hL : IsPreconnected L) :
    ∃ v ∈ C, v ∉ L ∧ v ≠ x ∧ IsConnected (C \ {v}) := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  haveI : ConnectedSpace C := Subtype.connectedSpace hCc
  set x' : C := ⟨x, hx⟩
  have hcut' : IsCutPoint x' := (isCutPoint_subtype_iff x').2 hcut
  obtain ⟨c, hcC, hcx⟩ := hne
  have hc' : (⟨c, hcC⟩ : C) ∈ ({x'}ᶜ : Set C) := fun e => hcx (congrArg Subtype.val e)
  obtain ⟨P, Q, hPQ, -⟩ := exists_separation_of_not_isConnected hc' hcut'
  set L' : Set C := (↑) ⁻¹' L
  have hLimg : ((↑) : C → X) '' L' = L := by
    rw [Subtype.image_preimage_coe]; exact inter_eq_right.2 (hLC.trans diff_subset)
  have hL' : IsPreconnected L' := by
    rw [← IsInducing.subtypeVal.isPreconnected_image, hLimg]; exact hL
  have hL'x : L' ⊆ {x'}ᶜ := fun z hz e => (hLC hz).2 (by rw [e]; rfl)
  have key : ∀ v : C, v ∈ ({x'}ᶜ : Set C) → v ∉ L' → ¬ IsCutPoint v →
      ∃ v ∈ C, v ∉ L ∧ v ≠ x ∧ IsConnected (C \ {v}) := by
    intro v hvx hvL hv
    rw [isCutPoint_subtype_iff, not_not] at hv
    exact ⟨v, v.2, hvL, fun e => hvx (Subtype.ext e), hv⟩
  obtain ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩ := exists_nonCutPoint_of_cut hPQ
  rcases hPQ.subset_or_subset hL' hL'x with h | h
  · exact key v (hPQ.subset_right hv) (fun hvL => disjoint_left.1 hPQ.2.2.1 (h hvL) hv) hv'
  · exact key u (hPQ.subset_left hu) (fun huL => disjoint_left.1 hPQ.2.2.1 hu (h huL)) hu'

/-- **A cut-point arc is irreducible** between its extremities. -/
theorem IsCutArc.irreducible [T1Space X] {A B : X} {H : Set X} (h : IsCutArc A B H) :
    ∀ L ⊆ H, L ≠ H → A ∈ L → B ∈ L → ¬ IsConnected L := by
  intro L hLH hne hA hB hL
  obtain ⟨x, hxH, hxL⟩ : ∃ x ∈ H, x ∉ L := by
    by_contra hc; push_neg at hc; exact hne (subset_antisymm hLH hc)
  have hxA : x ≠ A := fun e => hxL (e ▸ hA)
  have hxB : x ≠ B := fun e => hxL (e ▸ hB)
  have hcut := h.2.2.2.2.2 x hxH hxA hxB
  obtain ⟨v, hvH, hvL, -, hv⟩ := exists_nonCut_off h.2.1 h.2.2.1 hxH
    ⟨A, h.2.2.2.1, fun e => hxA (mem_singleton_iff.1 e).symm⟩ hcut
    (fun z hz => ⟨hLH hz, fun e => hxL ((mem_singleton_iff.1 e) ▸ hz)⟩) hL.isPreconnected
  exact h.2.2.2.2.2 v hvH (fun e => hvL (e ▸ hA)) (fun e => hvL (e ▸ hB)) hv

/-- **A cut-point arc is an embedded `[0, 1]`** (metrizable ambient space). -/
theorem IsCutArc.exists_embedding [TopologicalSpace.MetrizableSpace X] {A B : X} {H : Set X}
    (h : IsCutArc A B H) :
    ∃ f : unitInterval → X, IsEmbedding f ∧ range f = H ∧ f 0 = A ∧ f 1 = B :=
  (isIrreducibleConnected_iff_arc h.1).1 ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun L hL hne hA hB => h.irreducible L hL hne hA hB⟩

/-- **The image of a nondegenerate interval under an embedding of `[0, 1]` is a cut-point arc.** -/
theorem isCutArc_image_Icc {f : unitInterval → X} (hf : IsEmbedding f) {s t : unitInterval}
    (hst : s < t) : IsCutArc (f s) (f t) (f '' Icc s t) := by
  refine ⟨fun e => hst.ne (hf.injective e), isCompact_Icc.image hf.continuous,
    (isConnected_Icc hst.le).image _ hf.continuous.continuousOn, ⟨s, ⟨le_rfl, hst.le⟩, rfl⟩,
    ⟨t, ⟨hst.le, le_rfl⟩, rfl⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ hus hut hc
  have himg : f '' Icc s t \ {f u} = f '' (Icc s t \ {u}) := by
    rw [image_diff hf.injective, image_singleton]
  rw [himg, isConnected_image_iff_of_isInducing hf.isInducing] at hc
  have hs : s ∈ Icc s t \ {u} := ⟨⟨le_rfl, hst.le⟩, fun e => hus (by rw [mem_singleton_iff.1 e])⟩
  have ht : t ∈ Icc s t \ {u} := ⟨⟨hst.le, le_rfl⟩, fun e => hut (by rw [mem_singleton_iff.1 e])⟩
  exact (hc.isPreconnected.Icc_subset hs ht hu).2 rfl

/-- **The range of an embedding of `[0, 1]` is a cut-point arc.** -/
theorem isCutArc_range {f : unitInterval → X} (hf : IsEmbedding f) :
    IsCutArc (f 0) (f 1) (range f) := by
  have h := isCutArc_image_Icc hf (s := 0) (t := 1) (by simp)
  have hI : Icc (0 : unitInterval) 1 = univ := by
    ext u; simp [unitInterval.le_one']
  rwa [hI, image_univ] at h

/-- **Subcontinua of an embedded arc are intervals.** -/
theorem eq_image_Icc_of_subset_range {f : unitInterval → X} (hf : IsEmbedding f) {L : Set X}
    (hLK : L ⊆ range f) (hL : IsClosed L) (hLc : IsPreconnected L) (hLn : L.Nontrivial) :
    ∃ s t, s < t ∧ L = f '' Icc s t := by
  set P := f ⁻¹' L
  have hPimg : f '' P = L := image_preimage_eq_of_subset hLK
  have hPc : IsCompact P := (hL.preimage hf.continuous).isCompact
  have hPp : IsPreconnected P := by rw [← hf.isInducing.isPreconnected_image, hPimg]; exact hLc
  have hPne : P.Nonempty := by
    obtain ⟨x, hx⟩ := hLn.nonempty; obtain ⟨u, rfl⟩ := hLK hx; exact ⟨u, hx⟩
  obtain ⟨s, hs⟩ := hPc.exists_isLeast hPne
  obtain ⟨t, ht⟩ := hPc.exists_isGreatest hPne
  have hPeq : P = Icc s t := subset_antisymm (fun u hu => ⟨hs.2 hu, ht.2 hu⟩)
    (hPp.Icc_subset hs.1 ht.1)
  refine ⟨s, t, lt_of_le_of_ne (hs.2 ht.1) fun e => ?_, by rw [← hPimg, hPeq]⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hLn
  obtain ⟨u, rfl⟩ := hLK hx
  obtain ⟨w, rfl⟩ := hLK hy
  have hu : u ∈ Icc s t := hPeq ▸ hx
  have hw : w ∈ Icc s t := hPeq ▸ hy
  rw [← e] at hu hw
  exact hxy (by rw [le_antisymm hu.2 hu.1, le_antisymm hw.2 hw.1])

/-- **Extremities of a sub-arc.** If `L = f '' [s, t]` is a cut-point arc from `a` to `b`, then
`{a, b} = {f s, f t}`. -/
theorem ends_of_image_Icc {f : unitInterval → X} (hf : IsEmbedding f) {s t : unitInterval}
    (hst : s < t) {a b : X} (h : IsCutArc a b (f '' Icc s t)) :
    (a = f s ∧ b = f t) ∨ (a = f t ∧ b = f s) := by
  have hend : ∀ u ∈ ({s, t} : Set unitInterval), IsConnected (f '' Icc s t \ {f u}) := by
    intro u hu
    rw [← image_singleton, ← image_diff hf.injective]
    refine (isConnected_image_iff_of_isInducing hf.isInducing).2 ?_
    rcases hu with rfl | hu
    · have : Icc u t \ {u} = Ioc u t := by
        ext v; simp only [mem_diff, mem_Icc, mem_singleton_iff, mem_Ioc]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm h3), h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1.le, h2⟩, h1.ne'⟩
      rw [this]; exact isConnected_Ioc hst
    · rw [mem_singleton_iff] at hu; subst hu
      have : Icc s u \ {u} = Ico s u := by
        ext v; simp only [mem_diff, mem_Icc, mem_singleton_iff, mem_Ico]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, lt_of_le_of_ne h2 h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, h2.ne⟩
      rw [this]; exact isConnected_Ico hst
  have hs : f s = a ∨ f s = b := by
    by_contra hc; push_neg at hc
    exact h.2.2.2.2.2 (f s) ⟨s, ⟨le_rfl, hst.le⟩, rfl⟩ hc.1 hc.2 (hend s (Or.inl rfl))
  have ht : f t = a ∨ f t = b := by
    by_contra hc; push_neg at hc
    exact h.2.2.2.2.2 (f t) ⟨t, ⟨hst.le, le_rfl⟩, rfl⟩ hc.1 hc.2 (hend t (Or.inr rfl))
  have hne : f s ≠ f t := fun e => hst.ne (hf.injective e)
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact absurd (hs.trans ht.symm) hne
  · exact Or.inl ⟨hs.symm, ht.symm⟩
  · exact Or.inr ⟨ht.symm, hs.symm⟩
  · exact absurd (hs.trans ht.symm) hne

/-- An embedded arc minus an extremity is connected. -/
theorem isConnected_range_diff_ends {f : unitInterval → X} (hf : IsEmbedding f) :
    IsConnected (range f \ {f 0}) ∧ IsConnected (range f \ {f 1}) := by
  have h01 : (0 : unitInterval) < 1 := by simp
  have hI : range f = f '' Icc 0 1 := by
    rw [← image_univ]; congr 1; ext u; simp [unitInterval.le_one']
  have e0 : f '' Icc 0 1 \ {f 0} = f '' (Icc 0 1 \ {0}) := by
    rw [image_diff hf.injective, image_singleton]
  have e1 : f '' Icc 0 1 \ {f 1} = f '' (Icc 0 1 \ {1}) := by
    rw [image_diff hf.injective, image_singleton]
  rw [hI, e0, e1, isConnected_image_iff_of_isInducing hf.isInducing,
    isConnected_image_iff_of_isInducing hf.isInducing]
  constructor
  · have : Icc (0 : unitInterval) 1 \ {0} = Ioc 0 1 := by
      ext v; simp only [mem_diff, mem_Icc, mem_singleton_iff, mem_Ioc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm h3), h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1.le, h2⟩, h1.ne'⟩
    rw [this]; exact isConnected_Ioc h01
  · have : Icc (0 : unitInterval) 1 \ {1} = Ico 0 1 := by
      ext v; simp only [mem_diff, mem_Icc, mem_singleton_iff, mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, lt_of_le_of_ne h2 h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, h2.ne⟩
    rw [this]; exact isConnected_Ico h01

/-- **Moore 1925, Theorem 5, general form**: a cut-point arc is not disconnected by the omission
of an extremity. -/
theorem IsCutArc.isConnected_diff_ends [TopologicalSpace.MetrizableSpace X] {A B : X}
    {H : Set X} (h : IsCutArc A B H) : IsConnected (H \ {A}) ∧ IsConnected (H \ {B}) := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h.exists_embedding
  exact isConnected_range_diff_ends hf

/-- **Nadler 6.7, set form** (Moore 1925, Theorem 8): a connected proper subset of a continuum
misses a non-cut point. -/
theorem exists_nonCut_diff [T1Space X] {K H : Set X} (hK : IsCompact K) (hKc : IsConnected K)
    (hHK : H ⊆ K) (hH : IsConnected H) (hne : H ≠ K) : ∃ x ∈ K \ H, IsConnected (K \ {x}) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : ConnectedSpace K := Subtype.connectedSpace hKc
  set Z : Set K := (↑) ⁻¹' H
  have hZimg : ((↑) : K → X) '' Z = H := by
    rw [Subtype.image_preimage_coe]; exact inter_eq_right.2 hHK
  have hZ : IsConnected Z := by rw [isConnected_subtype_iff, hZimg]; exact hH
  have hZne : Z ≠ univ := fun e => hne (by
    apply subset_antisymm hHK
    intro x hx
    have : (⟨x, hx⟩ : K) ∈ Z := e ▸ mem_univ _
    exact this)
  have := not_subset_of_nonCutPoints hZ hZne
  obtain ⟨x, hx, hxZ⟩ := not_subset.1 this
  rw [mem_setOf_eq, isCutPoint_subtype_iff, not_not] at hx
  exact ⟨x, ⟨x.2, hxZ⟩, hx⟩

/-- Cut-point arcs are carried by embeddings. -/
theorem IsCutArc.image {Y : Type*} [TopologicalSpace Y] {e : X → Y} (he : IsEmbedding e)
    {a b : X} {s : Set X} (h : IsCutArc a b s) : IsCutArc (e a) (e b) (e '' s) := by
  refine ⟨fun h' => h.1 (he.injective h'), h.2.1.image he.continuous,
    h.2.2.1.image _ he.continuous.continuousOn, mem_image_of_mem _ h.2.2.2.1,
    mem_image_of_mem _ h.2.2.2.2.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ hxa hxb hc
  rw [← image_singleton, ← image_diff he.injective,
    isConnected_image_iff_of_isInducing he.isInducing] at hc
  exact h.2.2.2.2.2 x hx (fun e' => hxa (by rw [e'])) (fun e' => hxb (by rw [e'])) hc

end General

/-! ## The circle characterization (Moore 1920, Theorem 4) -/

section Circle

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [ConnectedSpace Y] [T2Space Y]

/-- Step 1: **no cut points**. -/
theorem circle_noCut (h2 : ∀ x y : Y, x ≠ y → ¬ IsConnected ({x, y}ᶜ : Set Y)) (x : Y)
    (hne : ({x}ᶜ : Set Y).Nonempty) : IsConnected ({x}ᶜ : Set Y) := by
  by_contra hx
  obtain ⟨c, hc⟩ := hne
  obtain ⟨U, V, hUV, -⟩ := exists_separation_of_not_isConnected hc hx
  have hUo : IsOpen U := hUV.symm.isOpen_right isOpen_compl_singleton
  have hVo : IsOpen V := hUV.isOpen_right isOpen_compl_singleton
  have hdisj : Disjoint U V := hUV.2.2.1
  have hcov : U ∪ V = {x}ᶜ := hUV.2.2.2.1
  have hxU : x ∉ U := fun h => (hUV.subset_left h) rfl
  have hxV : x ∉ V := fun h => (hUV.subset_right h) rfl
  -- the two halves `insert x U`, `insert x V` are continua
  have half : ∀ {U V : Set Y}, IsOpen U → IsOpen V → Disjoint U V → U ∪ V = {x}ᶜ →
      U.Nonempty → x ∉ V → ∃ u ∈ U, IsConnected (insert x U \ {u}) := by
    intro U V hUo hVo hdisj hcov hUn hxV
    have hxU : x ∉ U := fun h => (hcov.symm ▸ (subset_union_left h : x ∈ U ∪ V)) rfl
    have hCeq : insert x U = Vᶜ := by
      ext z
      simp only [mem_insert_iff, mem_compl_iff]
      constructor
      · rintro (rfl | hz) hzV
        · exact hxV hzV
        · exact disjoint_left.1 hdisj hz hzV
      · intro hzV
        by_cases hzx : z = x
        · exact Or.inl hzx
        · have : z ∈ U ∪ V := hcov ▸ hzx
          exact Or.inr (this.resolve_right hzV)
    have hCc : IsCompact (insert x U) := by rw [hCeq]; exact hVo.isClosed_compl.isCompact
    have hCconn : IsConnected (insert x U) :=
      ⟨insert_nonempty _ _, ac_insert_isPreconnected hUo hVo hdisj hcov⟩
    obtain ⟨u0, hu0⟩ := hUn
    have hCn : (insert x U).Nontrivial :=
      ⟨x, mem_insert _ _, u0, mem_insert_of_mem _ hu0, fun e => hxU (e ▸ hu0)⟩
    obtain ⟨u, huC, hux, hu⟩ := exists_nonCut_ne hCc hCconn hCn x
    exact ⟨u, (mem_insert_iff.1 huC).resolve_left hux, hu⟩
  obtain ⟨u, huU, hu⟩ := half hUo hVo hdisj hcov hUV.1 hxV
  obtain ⟨v, hvV, hv⟩ := half hVo hUo hdisj.symm (by rw [union_comm]; exact hcov) hUV.2.1 hxU
  have hux : u ≠ x := fun e => hxU (e ▸ huU)
  have hvx : v ≠ x := fun e => hxV (e ▸ hvV)
  have huv : u ≠ v := fun e => disjoint_left.1 hdisj huU (e ▸ hvV)
  apply h2 u v huv
  have heq : ({u, v}ᶜ : Set Y) = (insert x U \ {u}) ∪ (insert x V \ {v}) := by
    ext z
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or, mem_union, mem_diff]
    constructor
    · rintro ⟨hzu, hzv⟩
      by_cases hzx : z = x
      · exact Or.inl ⟨Or.inl hzx, hzu⟩
      · have : z ∈ U ∪ V := hcov ▸ hzx
        rcases this with h | h
        · exact Or.inl ⟨Or.inr h, hzu⟩
        · exact Or.inr ⟨Or.inr h, hzv⟩
    · rintro (⟨h | h, hzu⟩ | ⟨h | h, hzv⟩)
      · exact ⟨hzu, by rintro rfl; exact hvx h⟩
      · exact ⟨hzu, by rintro rfl; exact disjoint_left.1 hdisj h hvV⟩
      · exact ⟨by rintro rfl; exact hux h, hzv⟩
      · exact ⟨by rintro rfl; exact disjoint_left.1 hdisj huU h, hzv⟩
  rw [heq]
  exact hu.union ⟨x, ⟨mem_insert _ _, fun e => hux (mem_singleton_iff.1 e).symm⟩,
    ⟨mem_insert _ _, fun e => hvx (mem_singleton_iff.1 e).symm⟩⟩ hv

/-- Steps 2–5: **one half is a cut-point arc**. If `{p, q}ᶜ = U ∪ V` (open, disjoint, nonempty)
then `Vᶜ = U + p + q` is a cut-point arc from `p` to `q`. -/
theorem circle_half (h2 : ∀ x y : Y, x ≠ y → ¬ IsConnected ({x, y}ᶜ : Set Y))
    (hnc : ∀ x : Y, IsConnected ({x}ᶜ : Set Y)) {p q : Y} (hpq : p ≠ q) {U V : Set Y}
    (hUo : IsOpen U) (hVo : IsOpen V) (hdisj : Disjoint U V) (hcov : U ∪ V = {p, q}ᶜ)
    (hUn : U.Nonempty) (hVn : V.Nonempty) : IsCutArc p q Vᶜ := by
  have hpU : p ∉ U := fun h => (hcov ▸ (subset_union_left h : p ∈ U ∪ V)) (Or.inl rfl)
  have hqU : q ∉ U := fun h => (hcov ▸ (subset_union_left h : q ∈ U ∪ V)) (Or.inr rfl)
  have hpV : p ∉ V := fun h => (hcov ▸ (subset_union_right h : p ∈ U ∪ V)) (Or.inl rfl)
  have hqV : q ∉ V := fun h => (hcov ▸ (subset_union_right h : q ∈ U ∪ V)) (Or.inr rfl)
  have hmem : ∀ z, z ∉ V → z = p ∨ z = q ∨ z ∈ U := by
    intro z hzV
    by_cases hz : z = p ∨ z = q
    · rcases hz with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have : z ∈ U ∪ V := by rw [hcov]; simpa using hz
      exact Or.inr (Or.inr (this.resolve_right hzV))
  set a := Vᶜ with ha
  set b := Uᶜ with hb
  have hacl : IsClosed a := hVo.isClosed_compl
  have hbcl : IsClosed b := hUo.isClosed_compl
  have hUa : U ⊆ a := fun z hz hzV => disjoint_left.1 hdisj hz hzV
  have hab : ∀ z, z ∈ a → z ∈ b → z = p ∨ z = q := by
    intro z hza hzb
    rcases hmem z hza with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hzb
  have hpa : p ∈ a := hpV
  have hqa : q ∈ a := hqV
  -- `a` is preconnected
  have hapre : IsPreconnected a := by
    rw [isPreconnected_closed_iff]
    intro t t' ht ht' hsub hne1 hne2
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    set N := a ∩ t
    set K := a ∩ t'
    have hNK : ∀ z, z ∈ N → z ∈ K → False := fun z hzN hzK =>
      (eq_empty_iff_forall_notMem.1 hemp) z ⟨hzN.1, hzN.2, hzK.2⟩
    have hNcl : IsClosed N := hacl.inter ht
    have hKcl : IsClosed K := hacl.inter ht'
    have hcovNK : ∀ z ∈ a, z ∈ N ∨ z ∈ K := fun z hz =>
      (hsub hz).elim (fun h => Or.inl ⟨hz, h⟩) (fun h => Or.inr ⟨hz, h⟩)
    -- a piece missing both `p` and `q` is clopen
    have clopen_piece : ∀ {N K : Set Y}, IsClosed N → IsClosed K → (∀ z ∈ a, z ∈ N ∨ z ∈ K) →
        (∀ z, z ∈ N → z ∈ K → False) → N ⊆ a → K ⊆ a → K.Nonempty → p ∈ N → q ∈ N →
        False := by
      intro N K hN hK hcv hNK hNa hKa hKn hpN hqN
      have hKU : K = U ∩ Nᶜ := by
        ext z
        constructor
        · intro hz
          refine ⟨?_, fun hzN => hNK z hzN hz⟩
          rcases hmem z (hKa hz) with rfl | rfl | h
          · exact absurd hz (fun h' => hNK _ hpN h')
          · exact absurd hz (fun h' => hNK _ hqN h')
          · exact h
        · rintro ⟨hzU, hzN⟩
          exact (hcv z (hUa hzU)).resolve_left hzN
      have hKo : IsOpen K := by rw [hKU]; exact hUo.inter hN.isOpen_compl
      have := isClopen_iff.1 ⟨hK, hKo⟩
      rcases this with h | h
      · obtain ⟨z, hz⟩ := hKn; rw [h] at hz; exact hz
      · exact hNK p hpN (h ▸ mem_univ p)
    -- a piece through `p` only, with more than `p`, makes `p` a cut point
    have cut_piece : ∀ {N K : Set Y} {p q : Y}, IsClosed N → IsClosed K →
        (∀ z ∈ a, z ∈ N ∨ z ∈ K) → (∀ z, z ∈ N → z ∈ K → False) → K ⊆ a →
        (∀ z, z ∈ a → z ∈ b → z = p ∨ z = q) → p ∈ K → q ∈ N → (∃ k ∈ K, k ≠ p) →
        False := by
      intro N K p q hN hK hcv hNK hKa habpq hpK hqN ⟨k, hkK, hkp⟩
      have hc := (hnc p).isPreconnected
      rw [isPreconnected_closed_iff] at hc
      obtain ⟨z, hzp, hzK, hzNb⟩ := hc K (N ∪ b) hK (hN.union hbcl)
        (fun z _ => by
          by_cases hza : z ∈ a
          · rcases hcv z hza with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
          · exact Or.inr (Or.inr (fun hzU => hza (hUa hzU))))
        ⟨k, hkp, hkK⟩ ⟨q, fun e => hNK q hqN (by rw [mem_singleton_iff.1 e]; exact hpK),
          Or.inl hqN⟩
      rcases hzNb with h | h
      · exact hNK z h hzK
      · rcases habpq z (hKa hzK) h with rfl | rfl
        · exact hzp rfl
        · exact hNK z hqN hzK
    have hNa : N ⊆ a := inter_subset_left
    have hKa : K ⊆ a := inter_subset_left
    have hNn : N.Nonempty := hne1
    have hKn : K.Nonempty := hne2
    have hcovKN : ∀ z ∈ a, z ∈ K ∨ z ∈ N := fun z hz => (hcovNK z hz).symm
    have hKN : ∀ z, z ∈ K → z ∈ N → False := fun z h1 h2 => hNK z h2 h1
    have hab' : ∀ z, z ∈ a → z ∈ b → z = q ∨ z = p := fun z h1 h2 => (hab z h1 h2).symm
    rcases hcovNK p hpa with hpN | hpK <;> rcases hcovNK q hqa with hqN | hqK
    · exact clopen_piece hNcl hKcl hcovNK hNK hNa hKa hKn hpN hqN
    · -- `q ∈ K`, `p ∈ N`
      by_cases hk : ∃ k ∈ K, k ≠ q
      · exact cut_piece hNcl hKcl hcovNK hNK hKa hab' hqK hpN hk
      by_cases hn : ∃ n ∈ N, n ≠ p
      · exact cut_piece hKcl hNcl hcovKN hKN hNa hab hpN hqK hn
      push_neg at hk hn
      obtain ⟨u, hu⟩ := hUn
      rcases hcovNK u (hUa hu) with h | h
      · exact hpU (hn u h ▸ hu)
      · exact hqU (hk u h ▸ hu)
    · by_cases hk : ∃ k ∈ K, k ≠ p
      · exact cut_piece hNcl hKcl hcovNK hNK hKa hab hpK hqN hk
      by_cases hn : ∃ n ∈ N, n ≠ q
      · exact cut_piece hKcl hNcl hcovKN hKN hNa hab' hqN hpK hn
      push_neg at hk hn
      obtain ⟨u, hu⟩ := hUn
      rcases hcovNK u (hUa hu) with h | h
      · exact hqU (hn u h ▸ hu)
      · exact hpU (hk u h ▸ hu)
    · exact clopen_piece hKcl hNcl hcovKN hKN hKa hNa hNn hpK hqK
  refine ⟨hpq, hacl.isCompact, ⟨⟨p, hpa⟩, hapre⟩, hpa, hqa, ?_⟩
  -- Step 5: every point of `U` cuts `a`
  intro x hxa hxp hxq hc
  have hxU : x ∈ U := by
    rcases hmem x hxa with h | h | h
    · exact absurd h hxp
    · exact absurd h hxq
    · exact h
  obtain ⟨y, hyV⟩ := hVn
  have hxy : x ≠ y := fun e => disjoint_left.1 hdisj hxU (e ▸ hyV)
  apply h2 x y hxy
  set S : Set Y := {x, y}ᶜ with hS
  have hpS : p ∈ S := by
    simp only [hS, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨Ne.symm hxp, fun e => hpV (e ▸ hyV)⟩
  refine ⟨⟨p, hpS⟩, ?_⟩
  have haxS : a \ {x} ⊆ S := by
    rintro z ⟨hza, hzx⟩
    simp only [hS, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hzx, fun e => hza (e ▸ hyV)⟩
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hSuv hSuv'
  have side : ∀ {u v : Set Y}, IsOpen u → IsOpen v → S ⊆ u ∪ v → S ∩ (u ∩ v) = ∅ →
      a \ {x} ⊆ u → S ⊆ u := by
    intro u v hu hv hSuv hSuv' hau
    set Q := S ∩ v
    have hQV : Q ⊆ V := by
      rintro z ⟨hzS, hzv⟩
      by_contra hzV
      have hzu : z ∈ u := hau ⟨hzV, fun e => hzS (by rw [mem_singleton_iff.1 e]; simp)⟩
      exact (eq_empty_iff_forall_notMem.1 hSuv') z ⟨hzS, hzu, hzv⟩
    have hQu : Q ⊆ uᶜ := fun z hz hzu =>
      (eq_empty_iff_forall_notMem.1 hSuv') z ⟨hz.1, hzu, hz.2⟩
    have hQo : IsOpen Q := (isOpen_compl_iff.2 (Set.toFinite _).isClosed).inter hv
    have hcl : ∀ z, z ≠ y → z ∈ closure Q → z ∈ Q := by
      intro z hzy hz
      have hzu : z ∉ u := closure_minimal hQu hu.isClosed_compl hz
      have hzb : z ∈ b := closure_minimal (hQV.trans fun w hw hwU =>
        disjoint_left.1 hdisj hwU hw) hbcl hz
      have hzS : z ∈ S := by
        simp only [hS, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨fun e => hzb (e ▸ hxU), hzy⟩
      exact ⟨hzS, (hSuv hzS).resolve_left hzu⟩
    have hyc := (hnc y).isPreconnected
    rw [isPreconnected_iff_subset_of_disjoint] at hyc
    rcases hyc Q (closure Q)ᶜ hQo isClosed_closure.isOpen_compl
      (fun z hz => by
        by_cases h : z ∈ closure Q
        · exact Or.inl (hcl z hz h)
        · exact Or.inr h)
      (eq_empty_iff_forall_notMem.2 fun z hz => hz.2.2 (subset_closure hz.2.1)) with h | h
    · exact absurd (hQV (h (fun e => hpV (by rw [mem_singleton_iff.1 e]; exact hyV)))) hpV
    · intro z hzS
      refine (hSuv hzS).resolve_right fun hzv => ?_
      have hzy : z ≠ y := fun e => hzS (by rw [e]; simp)
      exact h hzy (subset_closure ⟨hzS, hzv⟩)
  rcases isPreconnected_iff_subset_of_disjoint.1 hc.isPreconnected u v hu hv
      (haxS.trans hSuv) (by
        refine eq_empty_of_subset_empty fun z hz => ?_
        rw [← hSuv']; exact ⟨haxS hz.1, hz.2⟩) with h | h
  · exact Or.inl (side hu hv hSuv hSuv' h)
  · refine Or.inr (side hv hu (by rw [union_comm]; exact hSuv) (by rw [inter_comm v]; exact hSuv') h)

/-- **The circle characterization in a space.** -/
theorem circle_char_space (h2 : ∀ x y : Y, x ≠ y → ¬ IsConnected ({x, y}ᶜ : Set Y)) {p q : Y}
    (hpq : p ≠ q) : ∃ a b : Set Y, IsCutArc p q a ∧ IsCutArc p q b ∧ a ∪ b = univ ∧
      a ∩ b = {p, q} := by
  have hnc : ∀ x : Y, IsConnected ({x}ᶜ : Set Y) := by
    intro x
    refine circle_noCut h2 x ?_
    by_cases hxp : x = p
    · exact ⟨q, fun e => hpq (hxp ▸ (mem_singleton_iff.1 e).symm)⟩
    · exact ⟨p, fun e => hxp (mem_singleton_iff.1 e).symm⟩
  obtain ⟨c, hc⟩ : ({p, q}ᶜ : Set Y).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hemp
    have hq : ({q} : Set Y) = {p}ᶜ := by
      ext z
      have hz : z ∈ ({p, q} : Set Y) := hemp ▸ mem_univ z
      simp only [mem_insert_iff, mem_singleton_iff] at hz
      simp only [mem_singleton_iff, mem_compl_iff]
      constructor
      · rintro rfl; exact Ne.symm hpq
      · intro hzp; exact hz.resolve_left hzp
    have hclo : IsClopen ({q} : Set Y) := ⟨isClosed_singleton, hq ▸ isOpen_compl_singleton⟩
    rcases isClopen_iff.1 hclo with h | h
    · exact (singleton_ne_empty q) h
    · exact hpq (mem_singleton_iff.1 (h ▸ mem_univ p))
  have hWo : IsOpen ({p, q}ᶜ : Set Y) := (Set.toFinite _).isClosed.isOpen_compl
  obtain ⟨U, V, hUV, -⟩ := exists_separation_of_not_isConnected hc (h2 p q hpq)
  have hUo : IsOpen U := hUV.symm.isOpen_right hWo
  have hVo : IsOpen V := hUV.isOpen_right hWo
  have hdisj : Disjoint U V := hUV.2.2.1
  have hcov : U ∪ V = {p, q}ᶜ := hUV.2.2.2.1
  refine ⟨Vᶜ, Uᶜ, circle_half h2 hnc hpq hUo hVo hdisj hcov hUV.1 hUV.2.1,
    circle_half h2 hnc hpq hVo hUo hdisj.symm (by rw [union_comm]; exact hcov) hUV.2.1 hUV.1,
    ?_, ?_⟩
  · rw [← compl_inter, inter_comm, disjoint_iff_inter_eq_empty.1 hdisj, compl_empty]
  · rw [← compl_union, union_comm, hcov, compl_compl]

end Circle

/-- **Moore 1920, Theorem 4** (for compact sets in a Hausdorff space): a nondegenerate continuum
`J` disconnected by the omission of any two of its points is, for any `p ≠ q` in `J`, the union of
two cut-point arcs from `p` to `q` with only `p` and `q` in common. -/
theorem circle_char {X : Type*} [TopologicalSpace X] [T2Space X] {J : Set X} (hJ : IsCompact J)
    (hJc : IsConnected J)
    (h2 : ∀ x ∈ J, ∀ y ∈ J, x ≠ y → ¬ IsConnected (J \ {x, y})) {p q : X} (hp : p ∈ J)
    (hq : q ∈ J) (hpq : p ≠ q) :
    ∃ a b : Set X, IsCutArc p q a ∧ IsCutArc p q b ∧ a ∪ b = J ∧ a ∩ b = {p, q} := by
  haveI : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  haveI : ConnectedSpace J := Subtype.connectedSpace hJc
  have h2' : ∀ x y : J, x ≠ y → ¬ IsConnected ({x, y}ᶜ : Set J) := by
    intro x y hxy hc
    have himg : ((↑) : J → X) '' ({x, y}ᶜ : Set J) = J \ {(x : X), (y : X)} := by
      ext z
      simp only [mem_image, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or, mem_diff]
      constructor
      · rintro ⟨w, ⟨hwx, hwy⟩, rfl⟩
        exact ⟨w.2, fun e => hwx (Subtype.ext e), fun e => hwy (Subtype.ext e)⟩
      · rintro ⟨hz, hzx, hzy⟩
        exact ⟨⟨z, hz⟩, ⟨fun e => hzx (by rw [← e]), fun e => hzy (by rw [← e])⟩, rfl⟩
    rw [isConnected_subtype_iff, himg] at hc
    exact h2 x x.2 y y.2 (fun e => hxy (Subtype.ext e)) hc
  obtain ⟨a, b, ha, hb, hab, hab'⟩ :=
    circle_char_space h2' (p := ⟨p, hp⟩) (q := ⟨q, hq⟩) (fun e => hpq (congrArg Subtype.val e))
  refine ⟨_, _, ha.image IsEmbedding.subtypeVal, hb.image IsEmbedding.subtypeVal, ?_, ?_⟩
  · rw [← image_union, hab, image_univ, Subtype.range_coe]
  · rw [← image_inter Subtype.val_injective, hab', image_pair]

end HPC.Moore
