import HPC.Hagopian.Hagopian76T

/-!
# Batch 176, item B: the cutting step through crossing components; Janiszewski in a domain

* `SepIn.mono` — separation passes to larger sets missing the two points;
* `sepIn_union_cases` — **Janiszewski's theorem inside a domain** (commission 176 §1.B, route 3):
  if `O` is surrounded by a compact connected `Y` (frontier of `O` in `Y`, `Y ∩ O = ∅`) and two
  compact sets `A`, `B` that do not meet inside `O` together separate `p` from `q` in `O`, one of
  them does. From `janiszewski_compact` applied to `(A ∩ Cl O) ∪ Y` and `(B ∩ Cl O) ∪ Y`;
* `closure_crossing_subset_interval` — the closure of a crossing component lies in the layers of its
  irreducible interval, a member of `I`;
* the named `Prop` `SepByCrossing` (the commission's `sep_by_crossing`, for `X = G`) and from it
  `TailCutKeepsSep` (`tailCutKeepsSep_of_sepByCrossing`) and the separation by the part of `G` above
  a gap of `St J` (`sepIn_above_gap`), which gives Property 4 (2) for the top block.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **Janiszewski's theorem inside a domain** (commission 176 §1.B, route 3: "State what is
needed"). Let `Y` be compact and connected, disjoint from `O`, and contain the frontier of `O`. If
compact sets `A`, `B` with `A ∩ B ∩ O = ∅` together separate `p` from `q` in `O`, then `A` or `B`
separates `p` from `q` in `O`. -/
theorem sepIn_union_cases {O Y A B : Set Pt} (hY : IsCompact Y) (hYc : IsConnected Y)
    (hYO : Disjoint Y O) (hfr : frontier O ⊆ Y) (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint (A ∩ B) O) {p q : Pt} (hsep : SepIn O (A ∪ B) p q) :
    SepIn O A p q ∨ SepIn O B p q := by
  obtain ⟨⟨hpO, hpAB⟩, ⟨hqO, hqAB⟩, hS⟩ := hsep
  have hpA : p ∉ A := fun h => hpAB (Or.inl h)
  have hpB : p ∉ B := fun h => hpAB (Or.inr h)
  have hqA : q ∉ A := fun h => hqAB (Or.inl h)
  have hqB : q ∉ B := fun h => hqAB (Or.inr h)
  have hpY : p ∉ Y := fun h => disjoint_left.1 hYO h hpO
  have hqY : q ∉ Y := fun h => disjoint_left.1 hYO h hqO
  by_contra hno
  push_neg at hno
  obtain ⟨hnA, hnB⟩ := hno
  set XA := (A ∩ closure O) ∪ Y with hXA
  set XB := (B ∩ closure O) ∪ Y with hXB
  -- a connected set in `O − A` is in the component of `p` in the complement of `XA`
  have key : ∀ {C : Set Pt}, ¬ SepIn O C p q → p ∉ C → q ∉ C →
      ¬ SeparatesPts ((C ∩ closure O) ∪ Y) p q := by
    intro C hn hpC hqC hsepC
    apply hn
    refine ⟨⟨hpO, hpC⟩, ⟨hqO, hqC⟩, fun S hSc hSO hpS hqS => hsepC.2.2 ?_⟩
    have hsub : S ⊆ ((C ∩ closure O) ∪ Y)ᶜ := by
      intro z hz hzX
      rcases hzX with ⟨hzC, -⟩ | hzY
      · exact (hSO hz).2 hzC
      · exact disjoint_left.1 hYO hzY (hSO hz).1
    exact hSc.subset_connectedComponentIn hpS hsub hqS
  have hjA := key hnA hpA hqA
  have hjB := key hnB hpB hqB
  have hXAc : IsCompact XA := (hA.inter_right isClosed_closure).union hY
  have hXBc : IsCompact XB := (hB.inter_right isClosed_closure).union hY
  have hint : XA ∩ XB = Y := by
    apply Subset.antisymm
    · rintro z ⟨hzA, hzB⟩
      by_contra hzY
      rcases hzA with ⟨hzA, hzcl⟩ | h
      · rcases hzB with ⟨hzB, -⟩ | h
        · have hzO : z ∉ O := fun hzO => disjoint_left.1 hAB ⟨hzA, hzB⟩ hzO
          exact hzY (hfr ⟨hzcl, fun hzi => hzO (interior_subset hzi)⟩)
        · exact hzY h
      · exact hzY h
    · intro z hz; exact ⟨Or.inr hz, Or.inr hz⟩
  have hj := HPC.Moore.janiszewski_compact hXAc hXBc (Or.inl (hint ▸ hYc)) hjA hjB
  apply hj
  have hpX : p ∉ XA ∪ XB := by
    rintro ((⟨h, -⟩ | h) | (⟨h, -⟩ | h))
    exacts [hpA h, hpY h, hpB h, hpY h]
  have hqX : q ∉ XA ∪ XB := by
    rintro ((⟨h, -⟩ | h) | (⟨h, -⟩ | h))
    exacts [hqA h, hqY h, hqB h, hqY h]
  refine ⟨hpX, hqX, fun hqC => ?_⟩
  set Cm := connectedComponentIn (XA ∪ XB)ᶜ p with hCm
  have hCmc : IsPreconnected Cm := isPreconnected_connectedComponentIn
  have hpCm : p ∈ Cm := mem_connectedComponentIn hpX
  have hCmX : Cm ⊆ (XA ∪ XB)ᶜ := connectedComponentIn_subset _ _
  have hpint : p ∈ interior O := by
    by_contra h
    exact hpY (hfr ⟨subset_closure hpO, h⟩)
  have hCmO : Cm ⊆ O := by
    refine Subset.trans ?_ interior_subset
    refine hCmc.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_right (compl_subset_compl.2 interior_subset_closure)) ?_
      ⟨p, hpCm, hpint⟩
    intro z hz
    by_cases hzc : z ∈ closure O
    · by_cases hzi : z ∈ interior O
      · exact Or.inl hzi
      · exact absurd (Or.inl (Or.inr (hfr ⟨hzc, hzi⟩))) (hCmX hz)
    · exact Or.inr hzc
  refine hS Cm hCmc (fun z hz => ⟨hCmO hz, ?_⟩) hpCm hqC
  rintro (hzA | hzB)
  · exact hCmX hz (Or.inl (Or.inl ⟨hzA, subset_closure (hCmO hz)⟩))
  · exact hCmX hz (Or.inr (Or.inl ⟨hzB, subset_closure (hCmO hz)⟩))

section Cut

variable {M : Set Pt}

theorem layerSet_subset {G : Set M} (d : G → unitInterval) (S : Set unitInterval) :
    layerSet d S ⊆ G := by
  rintro _ ⟨y, -, rfl⟩; exact y.2

theorem layerSet_mono {G : Set M} (d : G → unitInterval) {S T : Set unitInterval} (h : S ⊆ T) :
    layerSet d S ⊆ layerSet d T := by
  rintro _ ⟨y, hy, rfl⟩; exact ⟨y, h hy, rfl⟩

/-- **The closure of a crossing component lies in the layers of its irreducible interval**, which
is a member of Hagopian's `I`. -/
theorem closure_crossing_subset_interval {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) {π : Pt → Pt} {F : ℝ × ℝ → Pt} {c₁ : ℝ} {D' : Set (ℝ × ℝ)}
    {C : Set M} (hC : IsCrossingComponent G π F c₁ D' C) :
    ∃ r ∈ crossingIntervals d π F c₁ D', closure C ⊆ layerSet d (Icc r.1 r.2) := by
  obtain ⟨⟨z, hz, hCz⟩, -, -⟩ := id hC
  subst hCz
  have hCG : connectedComponentIn (crossSet G π F D') z ⊆ G :=
    (connectedComponentIn_subset _ _).trans fun m hm => hm.1
  obtain ⟨x, y, hirr, -, -⟩ := exists_irreducibleInterval hG hCG ⟨z, mem_connectedComponentIn hz⟩
  exact ⟨(x, y), ⟨_, hC, hirr⟩, closure_minimal hirr.1 (isClosed_layerSet_Icc hG x y)⟩

/-- **Named `Prop`: separation by `G` is witnessed by the closures of the crossing components**
(commission 176 §1.B, `sep_by_crossing`, for `X = G`): if `G` separates `p` from `q` in `O`, so does
the union of the closures of the crossing components of `G ∩ π⁻¹[D]`. Open.

*Shape:* stated for the given `p`, `q` (for Hagopian, `p ∈ K` and `f(p)`, both over the middle by
`eps3_positions_middle`), for `X = G` itself, and with closures (a weaker requirement than the
commission's union of components). It cannot hold for every pair of points of `π⁻¹[D]`: a pocket
component cuts off the points beneath it. -/
def SepByCrossing (G : Set M) (π : Pt → Pt) (F : ℝ × ℝ → Pt) (c₁ : ℝ) (D' : Set (ℝ × ℝ))
    (O : Set Pt) (p q : Pt) : Prop :=
  SepIn O (toPt G) p q →
    SepIn O (⋃ C ∈ {C : Set M | IsCrossingComponent G π F c₁ D' C}, toPt (closure C)) p q

/-- The closures of the crossing components lie in the union of the layers over the members of
`I`. -/
theorem iUnion_crossing_subset {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d)
    {π : Pt → Pt} {F : ℝ × ℝ → Pt} {c₁ : ℝ} {D' : Set (ℝ × ℝ)} {S : Set unitInterval}
    (hS : ∀ r ∈ crossingIntervals d π F c₁ D', Icc r.1 r.2 ⊆ S) :
    (⋃ C ∈ {C : Set M | IsCrossingComponent G π F c₁ D' C}, toPt (closure C)) ⊆
      toPt (layerSet d S) := by
  simp only [mem_setOf_eq, iUnion_subset_iff]
  intro C hC
  obtain ⟨r, hr, hsub⟩ := closure_crossing_subset_interval hG hC
  exact image_mono (hsub.trans (layerSet_mono d (hS r hr)))

/-- **B. The cutting step from `SepByCrossing`** (commission 176 §1.B: "With `sep_by_crossing`,
`TailCutKeepsSep` follows: the tail beyond the last block holds no crossing component"). -/
theorem tailCutKeepsSep_of_sepByCrossing {E G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) {π : Pt → Pt} {F : ℝ × ℝ → Pt} {c₁ : ℝ} {D' : Set (ℝ × ℝ)}
    {O : Set Pt} {p q : Pt} (hSBC : SepByCrossing G π F c₁ D' O p q) :
    TailCutKeepsSep E d π F c₁ D' O p q := by
  intro hsep t _ _ hIt
  have hsub : toPt (layerSet d (Icc 0 t)) ⊆ toPt G := image_mono (layerSet_subset d _)
  refine (hSBC hsep).mono (iUnion_crossing_subset hG fun r hr => ?_)
    (fun h => hsep.1.2 (hsub h)) (fun h => hsep.2.1.2 (hsub h))
  exact Icc_subset_Icc unitInterval.nonneg' (hIt r hr).le

theorem isCompact_toPt_layerSet [CompactSpace M] {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (x y : unitInterval) :
    IsCompact (toPt (layerSet d (Icc x y))) :=
  ((isClosed_layerSet_Icc hG x y).isCompact).image continuous_subtype_val

variable [CompactSpace M] [ConnectedSpace M]

/-- **C (2). Above a gap of `St J`, only the upper part separates** (commission 176 §1.B: "only the
top block separates, if `p` and `f(p)` are separated by crossing components that all lie in the top
block"). Let `G` be irreducible with respect to separating `p` from `q` in `O` among extensions of
`E` away from `k⁻¹(0)` (T13), let `O` be surrounded by a compact connected `Y`, and let
`s₁ < s₂` be a gap: every member of `I` lies in `[0, s₁]` or in `[s₂, 1]`, and
`E ⊆ d⁻¹[[0, s₁]]`. If `SepByCrossing` holds, `d⁻¹[[s₂, 1]]` separates `p` from `q` in `O`.

*Proof:* the closures of the crossing components lie in `d⁻¹[[0, s₁]] ∪ d⁻¹[[s₂, 1]]`, so these two
disjoint compact sets separate (`SepIn.mono`); by Janiszewski in `O` (`sepIn_union_cases`) one of
them does; `d⁻¹[[0, s₁]]` is a proper extension of `E` away from `k⁻¹(0)` (Lemma 5), excluded by
irreducibility. -/
theorem sepIn_above_gap (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d)
    (hX0 : layer d 0 = layer k 0) {π : Pt → Pt} {F : ℝ × ℝ → Pt} {c₁ : ℝ}
    {D' : Set (ℝ × ℝ)} {O Y : Set Pt} (hY : IsCompact Y) (hYc : IsConnected Y)
    (hYO : Disjoint Y O) (hfr : frontier O ⊆ Y) {p q : Pt} (hsep : SepIn O (toPt G) p q)
    (hirr : ∀ F', IsExtensionAway E (layer k 0) F' → SepIn O (toPt F') p q → F' ⊆ G → F' = G)
    (hSBC : SepByCrossing G π F c₁ D' O p q) {s₁ s₂ : unitInterval} (h0 : 0 < s₁)
    (h12 : s₁ < s₂) (hEs : E ⊆ layerSet d (Icc 0 s₁))
    (hgap : ∀ r ∈ crossingIntervals d π F c₁ D', r.2 ≤ s₁ ∨ s₂ ≤ r.1) :
    SepIn O (toPt (layerSet d (Icc s₂ 1))) p q := by
  have hsubG : ∀ S, toPt (layerSet d S) ⊆ toPt G := fun S => image_mono (layerSet_subset d S)
  have hAB : toPt (layerSet d (Icc 0 s₁)) ∪ toPt (layerSet d (Icc s₂ 1)) =
      toPt (layerSet d (Icc 0 s₁ ∪ Icc s₂ 1)) := by
    simp only [toPt, layerSet, preimage_union, image_union]
  have hsep2 : SepIn O (toPt (layerSet d (Icc 0 s₁)) ∪ toPt (layerSet d (Icc s₂ 1))) p q := by
    rw [hAB]
    refine (hSBC hsep).mono (iUnion_crossing_subset hG fun r hr => ?_)
      (fun h => hsep.1.2 (hsubG _ h)) (fun h => hsep.2.1.2 (hsubG _ h))
    rcases hgap r hr with h | h
    · exact fun u hu => Or.inl ⟨unitInterval.nonneg', hu.2.trans h⟩
    · exact fun u hu => Or.inr ⟨h.trans hu.1, unitInterval.le_one'⟩
  have hdisj : Disjoint (toPt (layerSet d (Icc 0 s₁)) ∩ toPt (layerSet d (Icc s₂ 1))) O := by
    rw [disjoint_left]
    rintro z ⟨⟨_, ⟨a, ha, rfl⟩, rfl⟩, ⟨_, ⟨b, hb, rfl⟩, hab⟩⟩ -
    have hba : b = a := Subtype.ext (Subtype.ext hab)
    subst hba
    exact absurd (hb.1.trans ha.2) (not_le.2 h12)
  rcases sepIn_union_cases hY hYc hYO hfr (isCompact_toPt_layerSet hG 0 s₁)
    (isCompact_toPt_layerSet hG s₂ 1) hdisj hsep2 with hA | hB
  · exfalso
    haveI : CompactSpace G := isCompact_iff_compactSpace.mp hG.isCompact
    obtain ⟨p', hp', hp'0, -⟩ := piece_map hG (lsc_of_minimalAdmissible hX hi hG) h0
      (P := layerSet d (Icc 0 s₁)) rfl
    have heq := hirr _ ⟨hEs, p', hp', hp'0.trans hX0⟩ hA (layerSet_subset d _)
    obtain ⟨g, hg⟩ := hG.2.1.2.1 1
    have hgm : (g : M) ∈ layerSet d (Icc 0 s₁) := by rw [heq]; exact g.2
    obtain ⟨g', hg', hgg'⟩ := hgm
    have : g' = g := Subtype.ext hgg'
    subst this
    have h1 : (1 : unitInterval) ≤ s₁ := hg ▸ hg'.2
    exact absurd (lt_of_lt_of_le (h12.trans_le unitInterval.le_one') h1) (lt_irrefl _)
  · exact hB

end Cut

end HPC.Hagopian
