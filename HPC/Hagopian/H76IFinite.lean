import HPC.Hagopian.H76EndElement

/-!
# Batch 174, items B and C: Hagopian's collection `I` is finite; `e` and `x₂ = e`

Commission 174 §1, §2.B–C; Hagopian 1976, p. 347: "Let `I` be the collection of all intervals
`[x, y]` such that `d⁻¹[[x, y]]` is irreducible with respect to containing a component of
`F ∩ π⁻¹[D]` whose closure meets `π⁻¹[(p₁, r)]` and `π⁻¹[(p₅, s)]`. It follows from Property 3 that
`I` is finite."

* `crossSet G π F D'`: the set `G ∩ π⁻¹[D]`, `D = F[D′]`.
* `IsCrossingComponent`: a component of `G ∩ π⁻¹[D]` whose closure meets both closed side segments.
* `IsIrreducibleInterval d C x y`: `[x, y]` is the least interval with `C ⊆ d⁻¹[[x, y]]`.
* `crossingIntervals`: Hagopian's `I`.

The route is commission 174 §1, steps 1–5: the closure of a crossing component contains the whole
layers over the interior of its interval (`layerSet_Ioo_subset`); two crossing components whose
intervals have overlapping interiors coincide (a component of `G ∩ π⁻¹[D]` is closed in it);
distinct members of `I` have disjoint interiors; each has length `≥ λ` (`crossing_length_pos_all`,
which covers the end element, §1.6); so `I` is finite.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section IFinite

variable {M : Set Pt}

/-- The part `G ∩ π⁻¹[D]` of `G` over Hagopian's domain `D = F[D′]`. -/
def crossSet (G : Set M) (π : Pt → Pt) (F : ℝ × ℝ → Pt) (D' : Set (ℝ × ℝ)) : Set M :=
  {m | m ∈ G ∧ π (m : Pt) ∈ F '' D'}

/-- **A crossing component** (p. 347): a component of `G ∩ π⁻¹[D]` whose closure meets the closed
side segments over `3/22` and `19/22` (heights in `[0, c₁]`), Hagopian's `π⁻¹[(p₁, r)]` and
`π⁻¹[(p₅, s)]`. -/
def IsCrossingComponent (G : Set M) (π : Pt → Pt) (F : ℝ × ℝ → Pt) (c₁ : ℝ) (D' : Set (ℝ × ℝ))
    (C : Set M) : Prop :=
  (∃ z ∈ crossSet G π F D', C = connectedComponentIn (crossSet G π F D') z) ∧
    (∃ x ∈ closure C, π (x : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) ∧
    (∃ x ∈ closure C, π (x : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 c₁))

/-- `d⁻¹[[x, y]]` is **irreducible with respect to containing `C`**: it contains `C`, and every
`d⁻¹[[x′, y′]]` containing `C` has `[x, y] ⊆ [x′, y′]`. -/
def IsIrreducibleInterval {G : Set M} (d : G → unitInterval) (C : Set M) (x y : unitInterval) :
    Prop :=
  C ⊆ layerSet d (Icc x y) ∧ ∀ x' y', C ⊆ layerSet d (Icc x' y') → x' ≤ x ∧ y ≤ y'

/-- **Hagopian's collection `I`** (p. 347): the intervals `[x, y]`, as pairs `(x, y)`, such that
`d⁻¹[[x, y]]` is irreducible with respect to containing a crossing component. -/
def crossingIntervals {G : Set M} (d : G → unitInterval) (π : Pt → Pt) (F : ℝ × ℝ → Pt) (c₁ : ℝ)
    (D' : Set (ℝ × ℝ)) : Set (unitInterval × unitInterval) :=
  {p | ∃ C, IsCrossingComponent G π F c₁ D' C ∧ IsIrreducibleInterval d C p.1 p.2}

theorem IsIrreducibleInterval.unique {G : Set M} {d : G → unitInterval} {C : Set M}
    {x y x' y' : unitInterval} (h : IsIrreducibleInterval d C x y)
    (h' : IsIrreducibleInterval d C x' y') : x = x' ∧ y = y' := by
  obtain ⟨h1, h2⟩ := h.2 x' y' h'.1
  obtain ⟨h3, h4⟩ := h'.2 x y h.1
  exact ⟨le_antisymm h3 h1, le_antisymm h2 h4⟩

theorem isClosed_layerSet_Icc {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d)
    (x y : unitInterval) : IsClosed (layerSet d (Icc x y)) :=
  (isCompact_img hG.isCompact hG.2.1.1 isClosed_Icc).isClosed

/-- **Every nonempty `C ⊆ G` has an irreducible interval**, and the closure of `C` meets its two end
layers (commission 174 §1.1: `d[Cl C] = [x, y]`). -/
theorem exists_irreducibleInterval {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) {C : Set M} (hCG : C ⊆ G) (hC : C.Nonempty) :
    ∃ x y, IsIrreducibleInterval d C x y ∧ (closure C ∩ layer d x).Nonempty ∧
      (closure C ∩ layer d y).Nonempty := by
  have hGc : IsCompact G := hG.isCompact
  have hclG : closure C ⊆ G := closure_minimal hCG hGc.isClosed
  set K : Set G := Subtype.val ⁻¹' closure C with hK
  have hKc : IsCompact (d '' K) := by
    haveI : CompactSpace G := isCompact_iff_compactSpace.mp hGc
    exact ((isClosed_closure.preimage continuous_subtype_val).isCompact).image hG.2.1.1
  obtain ⟨c, hcC⟩ := hC
  have hne : (d '' K).Nonempty := ⟨_, ⟨⟨c, hCG hcC⟩, subset_closure hcC, rfl⟩⟩
  obtain ⟨x, ⟨wx, hwxK, rfl⟩, hxl⟩ := hKc.exists_isLeast hne
  obtain ⟨y, ⟨wy, hwyK, rfl⟩, hyg⟩ := hKc.exists_isGreatest hne
  have hsub : C ⊆ layerSet d (Icc (d wx) (d wy)) := fun m hm => by
    have hmK : (⟨m, hCG hm⟩ : G) ∈ K := subset_closure hm
    exact ⟨⟨m, hCG hm⟩, ⟨hxl ⟨_, hmK, rfl⟩, hyg ⟨_, hmK, rfl⟩⟩, rfl⟩
  refine ⟨d wx, d wy, ⟨hsub, fun x' y' h => ?_⟩, ⟨wx, hwxK, wx, rfl, rfl⟩,
    ⟨wy, hwyK, wy, rfl, rfl⟩⟩
  have hcl := closure_minimal h (isClosed_layerSet_Icc hG x' y')
  have mem : ∀ w ∈ K, d w ∈ Icc x' y' := fun w hw => by
    obtain ⟨w', hw', hww⟩ := hcl hw
    rw [← Subtype.ext hww]; exact hw'
  exact ⟨(mem wx hwxK).1, (mem wy hwyK).2⟩

/-- The closure of `C` meets the end layers of its irreducible interval. -/
theorem IsIrreducibleInterval.closure_meets {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) {C : Set M} (hCG : C ⊆ G) (hC : C.Nonempty) {x y : unitInterval}
    (h : IsIrreducibleInterval d C x y) :
    (closure C ∩ layer d x).Nonempty ∧ (closure C ∩ layer d y).Nonempty := by
  obtain ⟨x', y', h', hx, hy⟩ := exists_irreducibleInterval hG hCG hC
  obtain ⟨rfl, rfl⟩ := h.unique h'
  exact ⟨hx, hy⟩

variable [CompactSpace M]

/-- **The closure of a connected `C` contains the whole layers over the interior of its
irreducible interval** (commission 174 §1.2, `layerSet_Ioo_subset`). -/
theorem IsIrreducibleInterval.layerSet_Ioo_subset_closure {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) {C : Set M} (hCG : C ⊆ G) (hC : IsConnected C)
    {x y : unitInterval} (h : IsIrreducibleInterval d C x y) :
    layerSet d (Ioo x y) ⊆ closure C := by
  obtain ⟨hx, hy⟩ := h.closure_meets hG hCG hC.nonempty
  exact layerSet_Ioo_subset hG (closure_minimal hCG hG.isCompact.isClosed)
    ⟨isClosed_closure.isCompact, hC.closure⟩ hx hy

omit [CompactSpace M] in
/-- A component of a set contains each point of the set in its closure (a component is closed in
the set). -/
theorem mem_component_of_mem_closure_in {S : Set M} {z w : M} (hz : z ∈ S)
    (hw : w ∈ S) (hwc : w ∈ closure (connectedComponentIn S z)) :
    w ∈ connectedComponentIn S z := by
  have hpre : IsPreconnected (insert w (connectedComponentIn S z)) :=
    (isPreconnected_connectedComponentIn).subset_closure (subset_insert _ _)
      (insert_subset hwc subset_closure)
  exact hpre.subset_connectedComponentIn (mem_insert_of_mem _ (mem_connectedComponentIn hz))
    (insert_subset hw (connectedComponentIn_subset _ _)) (mem_insert _ _)

omit [CompactSpace M] in
theorem IsCrossingComponent.isConnected {G : Set M} {π : Pt → Pt} {F : ℝ × ℝ → Pt} {c₁ : ℝ}
    {D' : Set (ℝ × ℝ)} {C : Set M} (h : IsCrossingComponent G π F c₁ D' C) : IsConnected C := by
  obtain ⟨⟨z, hz, rfl⟩, -, -⟩ := h
  exact ⟨⟨z, mem_connectedComponentIn hz⟩, isPreconnected_connectedComponentIn⟩

omit [CompactSpace M] in
theorem IsCrossingComponent.subset {G : Set M} {π : Pt → Pt} {F : ℝ × ℝ → Pt} {c₁ : ℝ}
    {D' : Set (ℝ × ℝ)} {C : Set M} (h : IsCrossingComponent G π F c₁ D' C) :
    C ⊆ crossSet G π F D' := by
  obtain ⟨⟨z, hz, rfl⟩, -, -⟩ := h
  exact connectedComponentIn_subset _ _

omit [CompactSpace M] in
/-- **Crossing components are equal as soon as one meets the closure of the other** (commission 174
§1.4: a component of `F ∩ π⁻¹[D]` is closed in it). -/
theorem IsCrossingComponent.eq_of_mem_closure {G : Set M} {π : Pt → Pt} {F : ℝ × ℝ → Pt}
    {c₁ : ℝ} {D' : Set (ℝ × ℝ)} {C₁ C₂ : Set M} (h₁ : IsCrossingComponent G π F c₁ D' C₁)
    (h₂ : IsCrossingComponent G π F c₁ D' C₂) {w : M} (hw₁ : w ∈ C₁) (hw₂ : w ∈ closure C₂) :
    C₁ = C₂ := by
  have hwS := h₁.subset hw₁
  obtain ⟨⟨z₁, hz₁, rfl⟩, -, -⟩ := h₁
  obtain ⟨⟨z₂, hz₂, rfl⟩, -, -⟩ := h₂
  have hw₂' := mem_component_of_mem_closure_in hz₂ hwS hw₂
  rw [connectedComponentIn_eq hw₁, connectedComponentIn_eq hw₂']

/-- **Distinct members of `I` have disjoint interiors** (commission 174 §1.3–1.4). This uses only
that `d` is a minimal admissible map of `G`; Property 3 is not needed. -/
theorem crossingIntervals_disjoint {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) {π : Pt → Pt} {F : ℝ × ℝ → Pt} {c₁ : ℝ} {D' : Set (ℝ × ℝ)}
    {p q : unitInterval × unitInterval} (hp : p ∈ crossingIntervals d π F c₁ D')
    (hq : q ∈ crossingIntervals d π F c₁ D') (hpq : p ≠ q) :
    Disjoint (Ioo (p.1 : ℝ) p.2) (Ioo (q.1 : ℝ) q.2) := by
  obtain ⟨C₁, hC₁, hI₁⟩ := hp
  obtain ⟨C₂, hC₂, hI₂⟩ := hq
  rw [Set.disjoint_left]
  intro t ht₁ ht₂
  apply hpq
  have hC₁G : C₁ ⊆ G := fun m hm => (hC₁.subset hm).1
  have hC₂G : C₂ ⊆ G := fun m hm => (hC₂.subset hm).1
  have ht0 : 0 ≤ t := (p.1.2.1).trans ht₁.1.le
  have ht1 : t ≤ 1 := ht₁.2.le.trans p.2.2.2
  set J : Set unitInterval := Ioo p.1 p.2 ∩ Ioo q.1 q.2 with hJ
  have hJo : IsOpen (d ⁻¹' J) := (isOpen_Ioo.inter isOpen_Ioo).preimage hG.2.1.1
  obtain ⟨V, hVo, hVJ⟩ := isOpen_induced_iff.1 hJo
  obtain ⟨w, hw⟩ := hG.2.1.2.1 ⟨t, ht0, ht1⟩
  have hwJ : d w ∈ J := by
    rw [hw]; exact ⟨⟨ht₁.1, ht₁.2⟩, ⟨ht₂.1, ht₂.2⟩⟩
  have hsub₁ := hI₁.layerSet_Ioo_subset_closure hG hC₁G hC₁.isConnected
  have hsub₂ := hI₂.layerSet_Ioo_subset_closure hG hC₂G hC₂.isConnected
  have hw₁ : (w : M) ∈ closure C₁ := hsub₁ ⟨w, hwJ.1, rfl⟩
  have hwV : (w : M) ∈ V := by
    have : w ∈ Subtype.val ⁻¹' V := by rw [hVJ]; exact hwJ
    exact this
  obtain ⟨z, hzV, hzC⟩ := mem_closure_iff.1 hw₁ V hVo hwV
  have hzJ : (⟨z, hC₁G hzC⟩ : G) ∈ d ⁻¹' J := by rw [← hVJ]; exact hzV
  have hz₂ : z ∈ closure C₂ := hsub₂ ⟨⟨z, hC₁G hzC⟩, hzJ.2, rfl⟩
  have hCC := hC₁.eq_of_mem_closure hC₂ hzC hz₂
  subst hCC
  obtain ⟨h1, h2⟩ := hI₁.unique hI₂
  exact Prod.ext h1 h2

/-- **Finiteness of a family of intervals with a length bound and disjoint interiors.** Left
endpoints are `λ`-separated, so `⌊x/λ⌋` is injective on the family and bounded by `1/λ`. -/
theorem finite_of_disjoint_Ioo {P : Set (unitInterval × unitInterval)} {lam : ℝ} (hlam : 0 < lam)
    (hlen : ∀ p ∈ P, lam ≤ (p.2 : ℝ) - p.1)
    (hdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (Ioo (p.1 : ℝ) p.2) (Ioo (q.1 : ℝ) q.2)) :
    P.Finite := by
  set f : unitInterval × unitInterval → ℕ := fun p => ⌊(p.1 : ℝ) / lam⌋₊ with hf
  have hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (p.1 : ℝ) ≤ q.1 → (p.1 : ℝ) + lam ≤ q.1 := by
    intro p hp q hq hpq hle
    have hlp := hlen p hp
    have hlq := hlen q hq
    by_contra hlt
    push_neg at hlt
    have hq1 : (q.1 : ℝ) < p.2 := by linarith
    set t := ((q.1 : ℝ) + min (p.2 : ℝ) q.2) / 2 with ht
    have hm1 : (q.1 : ℝ) < min (p.2 : ℝ) q.2 := lt_min hq1 (by linarith)
    have hmin1 := min_le_left (p.2 : ℝ) q.2
    have hmin2 := min_le_right (p.2 : ℝ) q.2
    exact Set.disjoint_left.1 (hdisj p hp q hq hpq)
      (show t ∈ Ioo (p.1 : ℝ) p.2 from ⟨by linarith, by linarith⟩) ⟨by linarith, by linarith⟩
  have hinj : Set.InjOn f P := by
    intro p hp q hq hfpq
    by_contra hpq
    have key : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (p.1 : ℝ) ≤ q.1 → f p ≠ f q := by
      intro p hp q hq hpq hle
      have h := hsep p hp q hq hpq hle
      have h0 : 0 ≤ (p.1 : ℝ) / lam := div_nonneg p.1.2.1 hlam.le
      have h1 : (p.1 : ℝ) / lam + 1 ≤ (q.1 : ℝ) / lam := by
        rw [div_add_one hlam.ne', div_le_div_iff_of_pos_right hlam]; exact h
      have h2 : ⌊(p.1 : ℝ) / lam + 1⌋₊ ≤ ⌊(q.1 : ℝ) / lam⌋₊ := Nat.floor_le_floor h1
      rw [Nat.floor_add_one h0] at h2
      simp only [hf]
      omega
    rcases le_total (p.1 : ℝ) q.1 with hle | hle
    · exact key p hp q hq hpq hle hfpq
    · exact key q hq p hp (Ne.symm hpq) hle hfpq.symm
  refine Set.Finite.of_finite_image ((Set.finite_Iic ⌊1 / lam⌋₊).subset ?_) hinj
  rintro _ ⟨p, -, rfl⟩
  exact Nat.floor_le_floor (div_le_div_of_nonneg_right p.1.2.2 hlam.le)

variable [ConnectedSpace M]

/-- **B. "It follows from Property 3 that `I` is finite"** (p. 347). Set-up of
`property3_layer_all`. There is `c > 0` such that for every domain `D = F[D′]` of height `c₁ ≤ c`
(`IsCrossRegion`), Hagopian's collection `I` (`crossingIntervals`) is finite.

*Proof:* commission 174 §1. Distinct members have disjoint interiors
(`crossingIntervals_disjoint`); each has length `≥ λ` (`crossing_length_pos_all`, applied to the
closure of its crossing component; this covers intervals accumulating at `1` through the end
element, §1.6); so `finite_of_disjoint_Ioo`. -/
theorem I_finite_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      (crossingIntervals d π F c₁ D').Finite := by
  obtain ⟨c, hc, hc1, hlen⟩ := crossing_length_pos_all hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG
    hP1 hG hEG hX0
  refine ⟨c, hc, hc1, fun c₁ D' hc₁ hR => ?_⟩
  obtain ⟨lam, hlam, hl⟩ := hlen c₁ D' hc₁ hR
  refine finite_of_disjoint_Ioo hlam (fun p hp => ?_)
    (fun p hp q hq hpq => crossingIntervals_disjoint hG hp hq hpq)
  obtain ⟨C, hC, hI⟩ := hp
  have hWc : IsClosed {m : M | π (m : Pt) ∈ closure (F '' D')} :=
    isClosed_closure.preimage (hπ.continuous.comp continuous_subtype_val)
  refine hl p.1 p.2 (closure C) hC.isConnected.isPreconnected.closure
    (closure_minimal hI.1 (isClosed_layerSet_Icc hG _ _)) (fun z hz => ?_) hC.2.1 hC.2.2
  exact (closure_minimal (s := C) (t := {m : M | π (m : Pt) ∈ closure (F '' D')})
    (fun m hm => subset_closure (hC.subset hm).2) hWc) hz

/-- **Property 3 as printed, for every element of the decomposition** (p. 347: "No component of
`F ∩ π⁻¹[D]` whose closure meets both `π⁻¹[(p₁, r)]` and `π⁻¹[(p₅, s)]` is contained in an element
of the decomposition of `F`"). The closure of such a component is a layer crossing, excluded in
every layer by `property3_layer_all` (the end element through a proper extension). -/
theorem property3_components_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ C : Set M, IsCrossingComponent G π F c₁ D' C → ∀ v : unitInterval, ¬ C ⊆ layer d v := by
  obtain ⟨c, hc, hc1, hP⟩ := property3_layer_all hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
    hG hEG hX0
  refine ⟨c, hc, hc1, fun c₁ D' hc₁ hR C hC v hCv => hP c₁ D' hc₁ hR v
    ⟨closure C, hC.isConnected.isPreconnected.closure,
      closure_minimal hCv (isClosed_layer hG.isCompact hG.2.1.1 v), fun z hz => ?_, hC.2.1,
      hC.2.2⟩⟩
  exact (closure_minimal (s := C) (t := {m : M | π (m : Pt) ∈ closure (F '' D')})
    (fun m hm => subset_closure (hC.subset hm).2)
    (isClosed_closure.preimage (hπ.continuous.comp continuous_subtype_val))) hz

end IFinite

end HPC.Hagopian
