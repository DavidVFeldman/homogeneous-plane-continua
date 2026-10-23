import HPC.Moore.M19EGrid
import HPC.Moore.M19ESeq

/-!
# Moore 1919, Theorem E: boxes of the pre-grid are subdivisions (batch 143)

For a double ruling `R` whose arcs belong to the two families of the pre-grid, the boxes cut out of
`J + I` by `DA`, `BC`, `AB`, `CD` and the arcs of `R` each lie in one subdivision of `R`
(`preGrid_box_sub_cell`). The proof is by counting: there are `(n + 1)(m + 1)` subdivisions
(`doubleRuling_cells_ncard`) and as many nonempty, disjoint boxes covering `I − ⋃ arcs`
(`HPC.Sq.PreGrid.box_sub_component`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

section Mesh

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
  (q : σ.Quad J I A B C D sAB sBC sCD sDA) {fA fB : unitInterval → S}
  (hfA : @IsEmbedding _ _ _ σ.topology fA) (hfAr : range fA = sAB) (hfA0 : fA 0 = A)
  (hfA1 : fA 1 = B)
  (hfB : @IsEmbedding _ _ _ σ.topology fB) (hfBr : range fB = sBC) (hfB0 : fB 0 = B)
  (hfB1 : fB 1 = C)
  (𝒜X : Set (Set S)) (h𝒜X : ∀ x ∈ 𝒜X, σ.XArc I sAB sCD A B C D x) (hdX : 𝒜X.Pairwise Disjoint)
  (𝒜Y : Set (Set S)) (h𝒜Y : ∀ y ∈ 𝒜Y, σ.XArc I sBC sDA B C D A y) (hdY : 𝒜Y.Pairwise Disjoint)
  (hcross : ∀ x ∈ 𝒜X, ∀ y ∈ 𝒜Y, ∃! P, P ∈ x ∩ y)

/-- **Boxes are subdivisions.** For a double ruling whose arcs belong to the two families, the
finite subfamilies consisting of the sides and the arcs of the ruling cut `J + I` into boxes each
of which lies in a subdivision of the ruling. -/
theorem preGrid_box_sub_cell {n m : ℕ} (R : σ.DoubleRuling q n m) (hRX : ∀ i, R.arcX i ∈ 𝒜X)
    (hRY : ∀ j, R.arcY j ∈ 𝒜Y) :
    letI := σ.topology
    ∃ (G : Finset (Option (Option 𝒜X))) (H : Finset (Option (Option 𝒜Y))),
      none ∈ G ∧ some none ∈ G ∧ (∀ i, some (some ⟨R.arcX i, hRX i⟩) ∈ G) ∧
      none ∈ H ∧ some none ∈ H ∧ (∀ j, some (some ⟨R.arcY j, hRY j⟩) ∈ H) ∧
      ∀ j j', (preGrid h1 h2 h3 h4 h5 h7 h8 q hfA hfAr hfA0 hfA1 hfB hfBr hfB0 hfB1 𝒜X h𝒜X hdX
          𝒜Y h𝒜Y hdY hcross).FX.Consec G j j' →
        ∀ k k', (preGrid h1 h2 h3 h4 h5 h7 h8 q hfA hfAr hfA0 hfA1 hfB hfBr hfB0 hfB1 𝒜X h𝒜X hdX
          𝒜Y h𝒜Y hdY hcross).FY.Consec H k k' →
          ∃ U ∈ R.cells, HPC.Sq.box
            (preGrid h1 h2 h3 h4 h5 h7 h8 q hfA hfAr hfA0 hfA1 hfB hfBr hfB0 hfB1 𝒜X h𝒜X hdX
              𝒜Y h𝒜Y hdY hcross).FX
            (preGrid h1 h2 h3 h4 h5 h7 h8 q hfA hfAr hfA0 hfA1 hfB hfBr hfB0 hfB1 𝒜X h𝒜X hdX
              𝒜Y h𝒜Y hdY hcross).FY j j' k k' ⊆ U := by
  letI := σ.topology
  classical
  set g := preGrid h1 h2 h3 h4 h5 h7 h8 q hfA hfAr hfA0 hfA1 hfB hfBr hfB0 hfB1 𝒜X h𝒜X hdX
    𝒜Y h𝒜Y hdY hcross with hg
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7
  have lX : ∀ i, g.FX.line i = lfLine sDA sBC 𝒜X i :=
    lineFam_line h1 h2 h3 h4 h5 h7 h8 q hfA hfAr hfA0 hfA1 𝒜X h𝒜X hdX
  have lY : ∀ k, g.FY.line k = lfLine sAB sCD 𝒜Y k :=
    lineFam_line h1 h2 h3 h4 h5 h7 h8 q.rot hfB hfBr hfB0 hfB1 𝒜Y h𝒜Y hdY
  let eX : Fin n → Option (Option 𝒜X) := fun i => some (some ⟨R.arcX i, hRX i⟩)
  let eY : Fin m → Option (Option 𝒜Y) := fun j => some (some ⟨R.arcY j, hRY j⟩)
  let G : Finset (Option (Option 𝒜X)) := insert none (insert (some none) (Finset.univ.image eX))
  let H : Finset (Option (Option 𝒜Y)) := insert none (insert (some none) (Finset.univ.image eY))
  have heX : Function.Injective eX := fun i i' h => by
    simp only [eX, Option.some.injEq, Subtype.mk.injEq] at h
    exact R.arcX_injective h1 h3 h4 h5 h
  have heY : Function.Injective eY := fun j j' h => by
    simp only [eY, Option.some.injEq, Subtype.mk.injEq] at h
    exact R.arcY_injective h1 h3 h4 h5 h
  have hGc : G.card = n + 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_image_of_injective _ heX, Finset.card_univ, Fintype.card_fin]
    · simp [eX]
    · simp [eX]
  have hHc : H.card = m + 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_image_of_injective _ heY, Finset.card_univ, Fintype.card_fin]
    · simp [eY]
    · simp [eY]
  have hJ : ∀ z ∈ J, z ∉ I := fun z hz hzI => disjoint_left.mp hIJ hzI hz
  have hlines : ∀ z ∈ I, z ∈ g.lines G H ↔ z ∈ R.carrier := by
    intro z hzI
    constructor
    · rintro (hz | hz)
      · obtain ⟨j, hjG, hzj⟩ := mem_iUnion₂.mp hz
        rw [lX] at hzj
        simp only [G, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hjG
        rcases hjG with rfl | rfl | ⟨i, rfl⟩
        · exact absurd hzI (hJ z (q.sDA_sub hzj))
        · exact absurd hzI (hJ z (q.sBC_sub hzj))
        · exact Or.inl (mem_iUnion.mpr ⟨i, hzj⟩)
      · obtain ⟨k, hkH, hzk⟩ := mem_iUnion₂.mp hz
        rw [lY] at hzk
        simp only [H, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hkH
        rcases hkH with rfl | rfl | ⟨j, rfl⟩
        · exact absurd hzI (hJ z (q.sAB_sub hzk))
        · exact absurd hzI (hJ z (q.sCD_sub hzk))
        · exact Or.inr (mem_iUnion.mpr ⟨j, hzk⟩)
    · rintro (hz | hz)
      · obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
        refine Or.inl (mem_iUnion₂.mpr ⟨eX i, ?_, ?_⟩)
        · simp [G]
        · rw [lX]; exact hzi
      · obtain ⟨j, hzj⟩ := mem_iUnion.mp hz
        refine Or.inr (mem_iUnion₂.mpr ⟨eY j, ?_, ?_⟩)
        · simp [H]
        · rw [lY]; exact hzj
  have hset : I \ g.lines G H = I \ R.carrier := by
    ext z
    simp only [mem_diff]
    exact ⟨fun h => ⟨h.1, fun h' => h.2 ((hlines z h.1).mpr h')⟩,
      fun h => ⟨h.1, fun h' => h.2 ((hlines z h.1).mp h')⟩⟩
  have hKU : (J ∪ I) \ I ⊆ g.lines G H := by
    rintro z ⟨hz, hzI⟩
    have hzJ : z ∈ J := hz.resolve_right hzI
    rw [← q.union] at hzJ
    rcases hzJ with ((h | h) | h) | h
    · exact Or.inr (mem_iUnion₂.mpr ⟨none, by simp [H], by rw [lY]; exact h⟩)
    · exact Or.inl (mem_iUnion₂.mpr ⟨some none, by simp [G], by rw [lX]; exact h⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨some none, by simp [H], by rw [lY]; exact h⟩)
    · exact Or.inl (mem_iUnion₂.mpr ⟨none, by simp [G], by rw [lX]; exact h⟩)
  have hcard : {c | ∃ x ∈ I \ g.lines G H, c = connectedComponentIn (I \ g.lines G H) x}.ncard =
      (G.card - 1) * (H.card - 1) := by
    rw [hset, hGc, hHc]
    exact doubleRuling_cells_ncard h1 h2 h3 h4 h5 h7 h8 R
  have tX : InjOn g.FX.t G :=
    (lfT_injective h1 h2 h3 h4 h5 h7 h8 q hfA hfAr hfA0 hfA1 𝒜X h𝒜X hdX).injOn
  have tY : InjOn g.FY.t H :=
    (lfT_injective h1 h2 h3 h4 h5 h7 h8 q.rot hfB hfBr hfB0 hfB1 𝒜Y h𝒜Y hdY).injOn
  refine ⟨G, H, by simp [G], by simp [G], fun i => by simp [G, eX], by simp [H], by simp [H],
    fun j => by simp [H, eY], fun j j' hc k k' hc' => ?_⟩
  obtain ⟨x, hx, hbox⟩ := g.box_sub_component tX tY (show none ∈ G by simp [G])
    (show some none ∈ G by simp [G]) (show none ∈ H by simp [H]) (show some none ∈ H by simp [H])
    subset_union_right hKU hcard hc hc'
  rw [hset] at hx hbox
  exact ⟨_, ⟨x, hx, rfl⟩, hbox⟩

end Mesh

end HPC.Moore
