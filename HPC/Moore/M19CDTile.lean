import HPC.Moore.M19CDDefs

/-!
# Moore 1919: tilings by interiors of closed curves (batch 141, item B, first part)

The tool behind the subdivision lemma. A *tiling* of an open set `U` relative to a closed set `G`
is a finite family of mutually exclusive interiors of closed curves lying on `G` whose union is
`U − G`. Adding to `G` an arc whose ends are on `G` and whose open arc lies in `U − G` splits one
tile into two (Theorems 24 and 25, `split_interior`); adding an arc that meets `G` in `k` points
(its ends among them) adds `k − 1` tiles (`Tiling.add_arc_finite`). The components of `U − G` are
then exactly the tiles (`Tiling.components`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

section Tile

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h7 h8

/-- **Splitting the interior of a closed curve by a cross-cut** (Theorems 24 and 25). If `γ` is an
arc from `a` to `b`, two points of the closed curve `K`, and the open arc `γ` lies in `V`, the
interior of `K`, then `V − γ` is the union of two mutually exclusive interiors of closed curves lying
on `K + γ`. -/
theorem split_interior {K V : Set S} (hV : σ.IsInteriorOf K V) {a b : S} (ha : a ∈ K)
    (hb : b ∈ K) {γ : Set S} (hγ : @TArc S σ.topology a b γ) (hγV : γ \ {a, b} ⊆ V) :
    ∃ K₁ R₁ K₂ R₂, σ.IsInteriorOf K₁ R₁ ∧ σ.IsInteriorOf K₂ R₂ ∧ K₁ ⊆ K ∪ γ ∧ K₂ ⊆ K ∪ γ ∧
      V \ γ = R₁ ∪ R₂ ∧ Disjoint R₁ R₂ ∧ γ ⊆ K₁ ∧ γ ⊆ K₂ := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, -, -, -, -, -, -, -, -, hdisVK, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hV
  obtain ⟨C₁, C₂, hC₁, hC₂, hCi, hCu⟩ := exists_two_arcs_of_isSCC h1 h3 h4 h51 hV.1 ha hb hγ.ne
  have hC₁t := (isArc_iff_tarc h1 h3 h4 h51).mp hC₁
  have hC₂t := (isArc_iff_tarc h1 h3 h4 h51).mp hC₂
  have hγC : ∀ {C : Set S}, C ⊆ K → TArc a b C → γ ∩ C = {a, b} := by
    intro C hCK hC
    apply subset_antisymm
    · rintro x ⟨hxγ, hxC⟩
      by_contra hx
      exact disjoint_left.mp hdisVK (hγV ⟨hxγ, hx⟩) (hCK hxC)
    · rintro x (rfl | rfl)
      · exact ⟨hγ.left_mem, hC.left_mem⟩
      · exact ⟨hγ.right_mem, hC.right_mem⟩
  have hC₁K : C₁ ⊆ K := hCu ▸ subset_union_left
  have hC₂K : C₂ ⊆ K := hCu ▸ subset_union_right
  have hscc : ∀ {C : Set S}, C ⊆ K → TArc a b C → σ.IsSCC (γ ∪ C) := fun hCK hC =>
    (isSCC_iff_tscc h1 h3 h4 h51).mpr ⟨a, b, γ, _, hγ, hC, hγC hCK hC, rfl⟩
  obtain ⟨R₁, hR₁r, hR₁b⟩ := h8 _ (hscc hC₁K hC₁t)
  obtain ⟨R₂, hR₂r, hR₂b⟩ := h8 _ (hscc hC₂K hC₂t)
  have hR₁ : σ.IsInteriorOf (γ ∪ C₁) R₁ := ⟨hscc hC₁K hC₁t, hR₁r, hR₁b⟩
  have hR₂ : σ.IsInteriorOf (γ ∪ C₂) R₂ := ⟨hscc hC₂K hC₂t, hR₂r, hR₂b⟩
  obtain ⟨c, hc⟩ := hC₁t.nonempty_diff
  obtain ⟨d, hd⟩ := hC₂t.nonempty_diff
  have hsep : σ.SeparatesOn K a b c d C₁ C₂ := ⟨hC₁, hC₂, hCi, hCu, hc, hd⟩
  have hγa := (isArc_iff_tarc h1 h3 h4 h51).mpr hγ
  obtain ⟨-, -, hdis⟩ := fa_theorem24 h1 h2 h3 h4 h5 h7 hV hsep hγV hR₁ hR₂
  have h25 := fa_theorem25 h1 h2 h3 h4 h5 h7 h8 hV hsep hγa hγV hR₁ hR₂
  obtain ⟨-, -, -, -, -, -, -, -, -, hdis₁, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hR₁
  obtain ⟨-, -, -, -, -, -, -, -, -, hdis₂, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hR₂
  refine ⟨_, R₁, _, R₂, hR₁, hR₂, union_subset subset_union_right (hC₁K.trans subset_union_left),
    union_subset subset_union_right (hC₂K.trans subset_union_left), ?_, hdis, subset_union_left,
    subset_union_left⟩
  rw [h25]
  ext x
  simp only [mem_diff, mem_union]
  constructor
  · rintro ⟨(⟨h, -⟩ | h) | h, hxγ⟩
    · exact absurd h hxγ
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨Or.inl (Or.inr h), fun hγx => disjoint_left.mp hdis₁ h (Or.inl hγx)⟩
    · exact ⟨Or.inr h, fun hγx => disjoint_left.mp hdis₂ h (Or.inl hγx)⟩

end Tile

/-- A *tiling* of `U` relative to `G`: a finite family of mutually exclusive interiors of closed
curves lying on `G`, with union `U − G`. -/
structure Space.Tiling (σ : Space S) (U G : Set S) (F : Finset (Set S)) : Prop where
  disj : (F : Set (Set S)).PairwiseDisjoint id
  int : ∀ V ∈ F, ∃ K, σ.IsInteriorOf K V ∧ K ⊆ G
  cover : ⋃ V ∈ F, V = U \ G

section TileOps

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h7 h8

/-- **Adding a cross-cut to a tiling** adds one tile. -/
theorem Space.Tiling.add_arc {U G : Set S} {F : Finset (Set S)} (hT : σ.Tiling U G F) {a b : S}
    (ha : a ∈ G) (hb : b ∈ G) {γ : Set S} (hγ : @TArc S σ.topology a b γ)
    (hγU : γ \ {a, b} ⊆ U \ G) :
    ∃ F' : Finset (Set S), σ.Tiling U (G ∪ γ) F' ∧ F'.card = F.card + 1 := by
  classical
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have hopen : ∀ V ∈ F, IsOpen V := fun V hV => by
    obtain ⟨K, hK, -⟩ := hT.int V hV
    exact (jordan h1 h2 h3 h4 h51 h7 hK).1
  -- the open arc lies in one tile
  obtain ⟨x, hx⟩ := hγ.nonempty_diff
  have hxU := hγU hx
  rw [← hT.cover] at hxU
  obtain ⟨V, hVF, hxV⟩ := mem_iUnion₂.mp hxU
  have hγV : γ \ {a, b} ⊆ V := by
    have hsub : γ \ {a, b} ⊆ V ∪ ⋃ W ∈ F.erase V, W := by
      intro y hy
      have := hγU hy
      rw [← hT.cover] at this
      obtain ⟨W, hWF, hyW⟩ := mem_iUnion₂.mp this
      by_cases hWV : W = V
      · exact Or.inl (hWV ▸ hyW)
      · exact Or.inr (mem_iUnion₂.mpr ⟨W, Finset.mem_erase.mpr ⟨hWV, hWF⟩, hyW⟩)
    refine hγ.isPreconnected_diff.subset_left_of_subset_union (hopen V hVF)
      (isOpen_biUnion fun W hW => hopen W (Finset.mem_of_mem_erase hW)) ?_ hsub ⟨x, hx, hxV⟩
    rw [disjoint_iUnion₂_right]
    intro W hW
    exact hT.disj hVF (Finset.mem_of_mem_erase hW) (Finset.ne_of_mem_erase hW).symm
  obtain ⟨K, hK, hKG⟩ := hT.int V hVF
  obtain ⟨hVo, -, hVne, hfrV, -, -, -, -, hclV, hdisVK, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hK
  have hVG : Disjoint V G := by
    rw [disjoint_left]
    intro y hyV hyG
    have : y ∈ ⋃ W ∈ F, W := mem_iUnion₂.mpr ⟨V, hVF, hyV⟩
    rw [hT.cover] at this
    exact this.2 hyG
  have hend : ∀ {e : S}, e ∈ γ → e ∈ G → e ∈ K := by
    intro e he heG
    have : e ∈ closure V := closure_mono hγV (hγ.subset_closure_diff he)
    rw [hclV] at this
    rcases this with h | h
    · exact absurd heG (disjoint_left.mp hVG h)
    · exact h
  obtain ⟨K₁, R₁, K₂, R₂, hR₁, hR₂, hK₁, hK₂, hsplit, hdis, -, -⟩ :=
    split_interior h1 h2 h3 h4 h5 h7 h8 hK (hend hγ.left_mem ha) (hend hγ.right_mem hb) hγ hγV
  obtain ⟨-, -, hR₁ne, -⟩ := jordan h1 h2 h3 h4 h51 h7 hR₁
  obtain ⟨-, -, hR₂ne, -⟩ := jordan h1 h2 h3 h4 h51 h7 hR₂
  have hR₁V : R₁ ⊆ V := fun y hy => (hsplit.symm ▸ Or.inl hy : y ∈ V \ γ).1
  have hR₂V : R₂ ⊆ V := fun y hy => (hsplit.symm ▸ Or.inr hy : y ∈ V \ γ).1
  have hnotin : ∀ {R : Set S}, R ⊆ V → R.Nonempty → R ∉ F.erase V := by
    intro R hRV hRne hR
    obtain ⟨y, hy⟩ := hRne
    exact disjoint_left.mp (hT.disj (Finset.mem_of_mem_erase hR) hVF (Finset.ne_of_mem_erase hR))
      hy (hRV hy)
  have hR₁₂ : R₁ ≠ R₂ := by
    intro e
    obtain ⟨y, hy⟩ := hR₁ne
    exact disjoint_left.mp hdis hy (e ▸ hy)
  refine ⟨insert R₁ (insert R₂ (F.erase V)), ⟨?_, ?_, ?_⟩, ?_⟩
  · -- disjointness
    intro P hP Q hQ hPQ
    simp only [Finset.coe_insert, mem_insert_iff, Finset.coe_erase, mem_diff,
      Finset.mem_coe, mem_singleton_iff] at hP hQ
    have key : ∀ {R W : Set S}, R ⊆ V → W ∈ F → W ≠ V → Disjoint R W := fun hRV hW hWV =>
      (hT.disj hVF hW (Ne.symm hWV)).mono_left hRV
    rcases hP with rfl | rfl | ⟨hP, hPV⟩ <;> rcases hQ with rfl | rfl | ⟨hQ, hQV⟩
    · exact absurd rfl hPQ
    · exact hdis
    · exact key hR₁V hQ hQV
    · exact hdis.symm
    · exact absurd rfl hPQ
    · exact key hR₂V hQ hQV
    · exact (key hR₁V hP hPV).symm
    · exact (key hR₂V hP hPV).symm
    · exact hT.disj hP hQ hPQ
  · intro W hW
    simp only [Finset.mem_insert, Finset.mem_erase] at hW
    rcases hW with rfl | rfl | ⟨-, hW⟩
    · exact ⟨K₁, hR₁, hK₁.trans (union_subset_union_left _ hKG)⟩
    · exact ⟨K₂, hR₂, hK₂.trans (union_subset_union_left _ hKG)⟩
    · obtain ⟨K', hK', hK'G⟩ := hT.int W hW
      exact ⟨K', hK', hK'G.trans subset_union_left⟩
  · ext y
    simp only [Finset.mem_insert, Finset.mem_erase, mem_iUnion, exists_prop, mem_diff, mem_union,
      not_or]
    constructor
    · rintro ⟨W, hW, hyW⟩
      rcases hW with rfl | rfl | ⟨hWV, hW⟩
      · have : y ∈ V \ γ := hsplit.symm ▸ Or.inl hyW
        have hyU : y ∈ U \ G := by rw [← hT.cover]; exact mem_iUnion₂.mpr ⟨V, hVF, this.1⟩
        exact ⟨hyU.1, hyU.2, this.2⟩
      · have : y ∈ V \ γ := hsplit.symm ▸ Or.inr hyW
        have hyU : y ∈ U \ G := by rw [← hT.cover]; exact mem_iUnion₂.mpr ⟨V, hVF, this.1⟩
        exact ⟨hyU.1, hyU.2, this.2⟩
      · have hyU : y ∈ U \ G := by rw [← hT.cover]; exact mem_iUnion₂.mpr ⟨W, hW, hyW⟩
        refine ⟨hyU.1, hyU.2, fun hyγ => ?_⟩
        have hyV : y ∈ V := by
          by_cases hyab : y ∈ ({a, b} : Set S)
          · rcases hyab with rfl | rfl
            · exact absurd ha hyU.2
            · exact absurd hb hyU.2
          · exact hγV ⟨hyγ, hyab⟩
        exact disjoint_left.mp (hT.disj hW hVF hWV) hyW hyV
    · rintro ⟨hyU, hyG, hyγ⟩
      have : y ∈ ⋃ W ∈ F, W := by rw [hT.cover]; exact ⟨hyU, hyG⟩
      obtain ⟨W, hW, hyW⟩ := mem_iUnion₂.mp this
      by_cases hWV : W = V
      · subst hWV
        have : y ∈ R₁ ∪ R₂ := hsplit ▸ ⟨hyW, hyγ⟩
        rcases this with h | h
        · exact ⟨R₁, Or.inl rfl, h⟩
        · exact ⟨R₂, Or.inr (Or.inl rfl), h⟩
      · exact ⟨W, Or.inr (Or.inr ⟨hWV, hW⟩), hyW⟩
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem (hnotin hR₂V hR₂ne),
      Finset.card_erase_of_mem hVF]
    · have : 0 < F.card := Finset.card_pos.mpr ⟨V, hVF⟩
      omega
    · simp only [Finset.mem_insert, not_or]
      exact ⟨hR₁₂, hnotin hR₁V hR₁ne⟩

/-- **Adding an arc meeting `G` in finitely many points.** If the arc `γ` has its ends on `G`, its
open arc in `U`, and meets `G` in `k` points, adding it to `G` adds `k − 1` tiles. -/
theorem Space.Tiling.add_arc_finite {U : Set S} :
    ∀ (k : ℕ) {G : Set S} {F : Finset (Set S)} {a b : S} {γ : Set S}, σ.Tiling U G F → a ∈ G →
      b ∈ G → @TArc S σ.topology a b γ → γ \ {a, b} ⊆ U → (γ ∩ G).Finite → (γ ∩ G).ncard = k →
      ∃ F' : Finset (Set S), σ.Tiling U (G ∪ γ) F' ∧ F'.card + 1 = F.card + k := by
  letI := σ.topology
  haveI := t2Space h1
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro G F a b γ hT ha hb hγ hγU hfin hk
  have hab : a ≠ b := hγ.ne
  by_cases hsub : γ ∩ G ⊆ {a, b}
  · have heq : γ ∩ G = {a, b} := subset_antisymm hsub (by
      rintro x (rfl | rfl)
      exacts [⟨hγ.left_mem, ha⟩, ⟨hγ.right_mem, hb⟩])
    have hk2 : k = 2 := by rw [← hk, heq, ncard_pair hab]
    obtain ⟨F', hT', hcard⟩ := hT.add_arc h1 h2 h3 h4 h5 h7 h8 ha hb hγ (fun x hx =>
      ⟨hγU hx, fun hxG => hx.2 (hsub ⟨hx.1, hxG⟩)⟩)
    exact ⟨F', hT', by omega⟩
  obtain ⟨p, ⟨hpγ, hpG⟩, hpab⟩ := not_subset.mp hsub
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hpab
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hu, hi⟩ := hγ.split hpγ hpab.1 hpab.2
  have hγ₁γ : γ₁ ⊆ γ := hu ▸ subset_union_left
  have hγ₂γ : γ₂ ⊆ γ := hu ▸ subset_union_right
  have hbγ₁ : b ∉ γ₁ := fun h => hpab.2 (by
    have : b ∈ γ₁ ∩ γ₂ := ⟨h, hγ₂.right_mem⟩
    rw [hi] at this; exact this.symm)
  have haγ₂ : a ∉ γ₂ := fun h => hpab.1 (by
    have : a ∈ γ₁ ∩ γ₂ := ⟨hγ₁.left_mem, h⟩
    rw [hi] at this; exact this.symm)
  have hs₁ : γ₁ ∩ G ⊆ (γ ∩ G) \ {b} := fun x hx =>
    ⟨⟨hγ₁γ hx.1, hx.2⟩, fun e => hbγ₁ (e ▸ hx.1)⟩
  have hs₂ : γ₂ ∩ G ⊆ (γ ∩ G) \ {a} := fun x hx =>
    ⟨⟨hγ₂γ hx.1, hx.2⟩, fun e => haγ₂ (e ▸ hx.1)⟩
  have hfin₁ : (γ₁ ∩ G).Finite := hfin.subset (hs₁.trans diff_subset)
  have hfin₂ : (γ₂ ∩ G).Finite := hfin.subset (hs₂.trans diff_subset)
  have hlt₁ : (γ₁ ∩ G).ncard < k := by
    rw [← hk]
    exact (ncard_le_ncard hs₁ (hfin.diff)).trans_lt
      (ncard_diff_singleton_lt_of_mem ⟨hγ.right_mem, hb⟩ hfin)
  have hlt₂ : (γ₂ ∩ G).ncard < k := by
    rw [← hk]
    exact (ncard_le_ncard hs₂ (hfin.diff)).trans_lt
      (ncard_diff_singleton_lt_of_mem ⟨hγ.left_mem, ha⟩ hfin)
  have hU₁ : γ₁ \ {a, p} ⊆ U := fun x hx => hγU ⟨hγ₁γ hx.1, by
    rintro (rfl | rfl)
    · exact hx.2 (Or.inl rfl)
    · exact hbγ₁ hx.1⟩
  have hU₂ : γ₂ \ {p, b} ⊆ U := fun x hx => hγU ⟨hγ₂γ hx.1, by
    rintro (rfl | rfl)
    · exact haγ₂ hx.1
    · exact hx.2 (Or.inr rfl)⟩
  obtain ⟨F₁, hT₁, hc₁⟩ := ih _ hlt₁ hT ha hpG hγ₁ hU₁ hfin₁ rfl
  have heq₂ : γ₂ ∩ (G ∪ γ₁) = γ₂ ∩ G := by
    ext x
    simp only [mem_inter_iff, mem_union]
    constructor
    · rintro ⟨hx₂, hx | hx⟩
      · exact ⟨hx₂, hx⟩
      · have : x ∈ γ₁ ∩ γ₂ := ⟨hx, hx₂⟩
        rw [hi] at this
        exact ⟨hx₂, (this : x = p) ▸ hpG⟩
    · rintro ⟨hx₂, hx⟩
      exact ⟨hx₂, Or.inl hx⟩
  obtain ⟨F₂, hT₂, hc₂⟩ := ih _ hlt₂ hT₁ (Or.inl hpG) (Or.inl hb) hγ₂ hU₂
    (by rw [heq₂]; exact hfin₂) (by rw [heq₂])
  refine ⟨F₂, by rwa [union_assoc, hu] at hT₂, ?_⟩
  have hun : (γ₁ ∩ G) ∪ (γ₂ ∩ G) = γ ∩ G := by rw [← union_inter_distrib_right, hu]
  have hin : (γ₁ ∩ G) ∩ (γ₂ ∩ G) = {p} := by
    have hp12 : p ∈ γ₁ ∩ γ₂ := by rw [hi]; rfl
    ext x
    constructor
    · rintro ⟨⟨hx₁, -⟩, hx₂, -⟩
      have : x ∈ γ₁ ∩ γ₂ := ⟨hx₁, hx₂⟩
      rw [hi] at this; exact this
    · rintro rfl; exact ⟨⟨hp12.1, hpG⟩, hp12.2, hpG⟩
  have := ncard_union_add_ncard_inter (γ₁ ∩ G) (γ₂ ∩ G) hfin₁ hfin₂
  rw [hun, hin, ncard_singleton, hk] at this
  omega

omit h8 in
/-- **The tiles are the components.** For a tiling of `U` relative to `G`, the components of
`U − G` are exactly the tiles. -/
theorem Space.Tiling.components {U G : Set S} {F : Finset (Set S)} (hT : σ.Tiling U G F) :
    {V | ∃ x ∈ U \ G, V = @connectedComponentIn S σ.topology (U \ G) x} = ↑F := by
  classical
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  have hfacts : ∀ V ∈ F, IsOpen V ∧ IsPreconnected V ∧ V.Nonempty := fun V hV => by
    obtain ⟨K, hK, -⟩ := hT.int V hV
    obtain ⟨h₁, h₂, h₃, -⟩ := jordan h1 h2 h3 h4 h51 h7 hK
    exact ⟨h₁, h₂, h₃⟩
  have hVsub : ∀ V ∈ F, V ⊆ U \ G := fun V hV x hx => by
    rw [← hT.cover]; exact mem_iUnion₂.mpr ⟨V, hV, hx⟩
  have key : ∀ V ∈ F, ∀ x ∈ V, connectedComponentIn (U \ G) x = V := by
    intro V hV x hxV
    apply subset_antisymm
    · have hsub : connectedComponentIn (U \ G) x ⊆ V ∪ ⋃ W ∈ F.erase V, W := by
        intro y hy
        have : y ∈ ⋃ W ∈ F, W := by rw [hT.cover]; exact connectedComponentIn_subset _ _ hy
        obtain ⟨W, hW, hyW⟩ := mem_iUnion₂.mp this
        by_cases hWV : W = V
        · exact Or.inl (hWV ▸ hyW)
        · exact Or.inr (mem_iUnion₂.mpr ⟨W, Finset.mem_erase.mpr ⟨hWV, hW⟩, hyW⟩)
      refine (isPreconnected_connectedComponentIn).subset_left_of_subset_union (hfacts V hV).1
        (isOpen_biUnion fun W hW => (hfacts W (Finset.mem_of_mem_erase hW)).1) ?_ hsub
        ⟨x, mem_connectedComponentIn (hVsub V hV hxV), hxV⟩
      rw [disjoint_iUnion₂_right]
      intro W hW
      exact hT.disj hV (Finset.mem_of_mem_erase hW) (Finset.ne_of_mem_erase hW).symm
    · exact (hfacts V hV).2.1.subset_connectedComponentIn hxV (hVsub V hV)
  ext V
  simp only [mem_setOf_eq, Finset.mem_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← hT.cover] at hx
    obtain ⟨W, hW, hxW⟩ := mem_iUnion₂.mp hx
    rw [key W hW x hxW]; exact hW
  · intro hV
    obtain ⟨x, hx⟩ := (hfacts V hV).2.2
    exact ⟨x, hVsub V hV hx, (key V hV x hx).symm⟩

end TileOps

end HPC.Moore
