import HPC.Moore.Sec6Th29

/-!
# Moore, F.A. (1916), §6: Theorem 31 (batch 138, item B)

**Theorem 31.** If `CD` is an arc, `B` a point of `CD`, `BX` an arc which has no point except `B`
in common with `CD`, and `R` a region containing `B`, then there is in `R` an arc `EFG` such
that (1) `E`, `G` are on `CD` in the order `CEBGD`; (2) the segment `EBG` of `CD` lies in `R`;
(3) `EFG` (open) has no point in common with `CD`; (4) there is on `BX` a point `H` such that the
segment `BH` of `BX`, except `B`, is within the closed curve `EFGBE`.

Moore's proof (pp. 146–147), followed step by step:

1. A region about `B` whose closure misses `C` and `D`, an arc `CYD` without it (Axiom 3,
   Theorem 15), its last point `C₁` on `CB` and the first point `D₁` after `C₁` on `BD`; the
   arc `C₁X₁D₁` of `CYD` meets `CD` only in `C₁`, `D₁`, and with the interval `C₁D₁` of `CD`
   forms a closed curve `J₀` (this is the construction of the proof of Theorem 23).
2. Theorem 28 for `J₀` at `B`, in a region `R₁ ⊆ R` missing `C₁X₁D₁ + CC₁ + D₁D`: an arc
   `E₁F₁G₁` within `J₀`, with `E₁BG₁` (a segment of `CD`, as it lies on `J₀` in `R₁`) in `R₁`.
3. Theorem 28 for `J₁ = E₁F₁G₁BE₁` at `B`, in a region `R₂ ⊆ R₁` missing `E₁F₁G₁ + CE₁ + G₁D`:
   an arc `E₂F₂G₂` without `J₁`, with `E₂BG₂` in `R₂`.
4. Theorem 27 for `J₁` and `E₂F₂G₂`: since the interior of `E₂F₂G₂BE₂` lies in `R₂` (Theorem 21)
   and so misses `E₁`, the interior `R₃` of `E₁E₂F₂G₂G₁F₁E₁` is `E₂BG₂ (open) + R₁' + R₂'`, the
   interiors of `J₁` and of `E₂F₂G₂BE₂` (Moore: \"By Theorem 25, `R₃ = R₁ + R₂ + E₂BG₂`\"; the
   statement that `E₂BG₂` is within `R₃`, which Theorem 25 needs, is what Theorem 27 supplies).
   `R₁'` and `R₂'` are disjoint (Theorem 24 (3)).
5. A segment `BH` of `BX` in `R₃`; `BH − B` is connected and misses `E₂BG₂`, so it lies in `R₁'`
   or in `R₂'`. In the first case `EFG = E₁F₁G₁`, in the second `EFG = E₂F₂G₂`.

The order `C E B G D` is expressed with the parametrization of `CD` (`InOrder`); the points `E`,
`G` on the two sides of `B` come from `Gen.order_of_arc_sub`: an arc of `CD` through `B` has its
endpoints on opposite sides of `B`.
-/

namespace HPC.Moore

open Set Topology
open unitInterval (nonneg' le_one')

namespace Gen

variable {X : Type*} [TopologicalSpace X]

/-- The preimage of a preconnected subset of an arc under its parametrization is preconnected. -/
theorem isPreconnected_preimage_of_embedding {g : unitInterval → X} (hg : IsEmbedding g)
    {S : Set X} (hS : IsPreconnected S) (hSr : S ⊆ range g) : IsPreconnected (g ⁻¹' S) := by
  rw [← hg.isInducing.isPreconnected_image, image_preimage_eq_of_subset hSr]
  exact hS

/-- A preconnected subset of an arc containing its two endpoints is the whole arc. -/
theorem TArc.mem_of_isPreconnected {E G Q : X} {P S : Set X} (hP : TArc E G P) (hQ : Q ∈ P)
    (hS : IsPreconnected S) (hSP : S ⊆ P) (hE : E ∈ S) (hG : G ∈ S) : Q ∈ S := by
  obtain ⟨-, p, hp, rfl, rfl, rfl⟩ := hP
  obtain ⟨β, rfl⟩ := hQ
  exact (isPreconnected_preimage_of_embedding hp hS hSP).Icc_subset hE hG ⟨nonneg', le_one'⟩

/-- An arc `P` lying on the arc `g` contains the interval of `g` between its endpoints. -/
theorem image_Icc_subset_of_arc {g : unitInterval → X} (hg : IsEmbedding g) {e s : unitInterval}
    {P : Set X} (hP : TArc (g e) (g s) P) (hPg : P ⊆ range g) :
    g '' Icc e s ⊆ P := by
  have hpre := isPreconnected_preimage_of_embedding hg hP.isPreconnected hPg
  rintro _ ⟨t, ht, rfl⟩
  exact hpre.Icc_subset hP.left_mem hP.right_mem ht

variable [T2Space X] in
/-- **Order on an arc.** If an arc `P` lying on the arc `g` passes through `g b`, other than its
endpoints `g e`, `g s`, then `b` lies strictly between `e` and `s`. -/
theorem order_of_arc_sub {g : unitInterval → X} (hg : IsEmbedding g) {e s b : unitInterval}
    {P : Set X} (hP : TArc (g e) (g s) P) (hPg : P ⊆ range g) (hb : g b ∈ P) (hbe : b ≠ e)
    (hbs : b ≠ s) : (e < b ∧ b < s) ∨ (s < b ∧ b < e) := by
  rcases le_total e s with h | h
  · have hsub := image_Icc_subset_of_arc hg hP hPg
    obtain ⟨t, ht, htb⟩ := hP.mem_of_isPreconnected hb
      (isPreconnected_Icc.image _ hg.continuous.continuousOn) hsub
      (mem_image_of_mem _ ⟨le_rfl, h⟩) (mem_image_of_mem _ ⟨h, le_rfl⟩)
    have := hg.injective htb; subst this
    exact Or.inl ⟨lt_of_le_of_ne ht.1 hbe.symm, lt_of_le_of_ne ht.2 hbs⟩
  · have hsub := image_Icc_subset_of_arc hg hP.symm hPg
    obtain ⟨t, ht, htb⟩ := hP.symm.mem_of_isPreconnected hb
      (isPreconnected_Icc.image _ hg.continuous.continuousOn) hsub
      (mem_image_of_mem _ ⟨le_rfl, h⟩) (mem_image_of_mem _ ⟨h, le_rfl⟩)
    have := hg.injective htb; subst this
    exact Or.inr ⟨lt_of_le_of_ne ht.1 hbs.symm, lt_of_le_of_ne ht.2 hbe⟩

end Gen

open Gen

variable {S : Type*} {σ : Space S}

/-- **The pocket construction** (steps 1–4 of Moore's proof of Theorem 31). At a point `f b`
(`0 < b < 1`) of the arc `f` and in a region `R` about it: closed curves `J₁ = F₁ ∪ P` and
`J₂ = F₂ ∪ Pb`, with `P = E₁BG₁`, `Pb = E₂BG₂` segments of the arc (`E₁ E₂ B G₂ G₁` in this order),
`F₁`, `F₂` meeting the arc only in their endpoints, whose interiors `I₁`, `I₂` are disjoint, miss
the arc, and together with the open segment `E₂BG₂` form a region `R₃` about `f b`.
*Axioms used: 1–8.* -/
theorem th31_pocket (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {f : unitInterval → S}
    (hf : @IsEmbedding _ _ _ σ.topology f) {b : unitInterval} (hb0 : 0 < b) (hb1 : b < 1)
    {R : Set S} (hR : R ∈ σ.region) (hBR : f b ∈ R) :
    letI := σ.topology
    ∃ e₁ s₁ e₂ s₂ : unitInterval, ∃ F₁ P F₂ Pb I₁ I₂ R₃ : Set S,
      0 < e₁ ∧ e₁ < e₂ ∧ e₂ < b ∧ b < s₂ ∧ s₂ < s₁ ∧ s₁ < 1 ∧
      TArc (f e₁) (f s₁) F₁ ∧ F₁ ⊆ R ∧ Disjoint (F₁ \ {f e₁, f s₁}) (range f) ∧
      TArc (f e₁) (f s₁) P ∧ P ⊆ range f ∧ f b ∈ P ∧ P ⊆ R ∧ TInt σ.region (F₁ ∪ P) I₁ ∧
      TArc (f e₂) (f s₂) F₂ ∧ F₂ ⊆ R ∧ Disjoint (F₂ \ {f e₂, f s₂}) (range f) ∧
      TArc (f e₂) (f s₂) Pb ∧ Pb ⊆ range f ∧ f b ∈ Pb ∧ Pb ⊆ R ∧ TInt σ.region (F₂ ∪ Pb) I₂ ∧
      IsOpen R₃ ∧ f b ∈ R₃ ∧ R₃ = Pb \ {f e₂, f s₂} ∪ I₁ ∪ I₂ ∧ Disjoint I₁ I₂ ∧
      Disjoint I₁ (range f) ∧ Disjoint I₂ (range f) ∧ R₃ ⊆ R := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  have h21 := th21Prop h1 h3 h4 h5 h7
  have hA8 := ax8Prop h1 h3 h4 h51 h8
  have hinj := hf.injective
  have hbAB : f b ≠ f 0 ∧ f b ≠ f 1 := ⟨fun e => hb0.ne' (hinj e), fun e => hb1.ne (hinj e)⟩
  have hcIm : ∀ s t : unitInterval, IsClosed (f '' Icc s t) := fun s t =>
    (isCompact_Icc.image hf.continuous).isClosed
  /- Step 1: the closed curve `J₀` (construction of the proof of Theorem 23) -/
  have hABc : IsClosed ({f 0, f 1} : Set S) := (toFinite _).isClosed
  obtain ⟨K₀, hK₀, hbK₀, hK₀cl⟩ := exists_region_closure_subset h1 hABc.isOpen_compl
    (by simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]; exact hbAB)
  have hA : f 0 ∈ (closure K₀)ᶜ := fun h => hK₀cl h (by simp)
  have hB' : f 1 ∈ (closure K₀)ᶜ := fun h => hK₀cl h (by simp)
  obtain ⟨Z, hZE, hZ⟩ := arcConn h1 h3 h4 h51 h2 _ isClosed_closure.isOpen_compl
    (hext_region h1 h3 K₀ hK₀) _ hA _ hB' (fun e => zero_ne_one' unitInterval (hinj e))
  have hbZ : f b ∉ Z := fun h => hZE h (subset_closure hbK₀)
  obtain ⟨P₁, hP₁, Z₁, hZ₁Z, hZ₁, hZ₁c⟩ := hZ.symm.first_point (hcIm 0 b)
    ⟨f 0, hZ.left_mem, mem_image_of_mem _ ⟨le_rfl, nonneg'⟩⟩
    (fun ⟨u, hu, hu1⟩ => by
      have := hinj hu1; subst this; exact absurd hu.2 (not_le.mpr hb1))
  obtain ⟨c, ⟨-, hcb⟩, rfl⟩ := hP₁
  have hcb' : c < b := lt_of_le_of_ne hcb fun e => hbZ (e ▸ hZ₁Z hZ₁.right_mem)
  obtain ⟨Q₁, hQ₁, Z₂, hZ₂Z₁, hZ₂, hZ₂c⟩ := hZ₁.symm.first_point (hcIm b 1)
    ⟨f 1, hZ₁.left_mem, mem_image_of_mem _ ⟨le_one', le_rfl⟩⟩
    (fun ⟨u, hu, hua⟩ => by
      have := hinj hua; subst this; exact absurd hu.1 (not_le.mpr hcb'))
  obtain ⟨d, ⟨hbd, -⟩, rfl⟩ := hQ₁
  have hbd' : b < d := lt_of_le_of_ne hbd fun e => hbZ (e ▸ hZ₁Z (hZ₂Z₁ hZ₂.right_mem))
  have hcd : c < d := hcb'.trans hbd'
  have hZ₂f : Z₂ ∩ range f ⊆ {f c, f d} := by
    rintro _ ⟨hx, u, rfl⟩
    rcases le_total u b with hu | hu
    · left
      have : f u ∈ Z₁ ∩ f '' Icc 0 b := ⟨hZ₂Z₁ hx, mem_image_of_mem _ ⟨nonneg', hu⟩⟩
      rwa [hZ₁c] at this
    · right
      have : f u ∈ Z₂ ∩ f '' Icc b 1 := ⟨hx, mem_image_of_mem _ ⟨hu, le_one'⟩⟩
      rwa [hZ₂c] at this
  have hJ₀ : TSCC (f '' Icc c d ∪ Z₂) := by
    refine ⟨f c, f d, _, _, TArc.image_Icc hf hcd, hZ₂, ?_, rfl⟩
    apply subset_antisymm
    · rintro x ⟨hx1, hx2⟩
      exact hZ₂f ⟨hx2, image_subset_range _ _ hx1⟩
    · rintro x hx
      rcases hx with rfl | rfl
      · exact ⟨mem_image_of_mem _ ⟨le_rfl, hcd.le⟩, hZ₂.left_mem⟩
      · exact ⟨mem_image_of_mem _ ⟨hcd.le, le_rfl⟩, hZ₂.right_mem⟩
  obtain ⟨R₀, hR₀, hR₀J⟩ := hA8 _ hJ₀
  have hR₀o := isOpen_region hR₀
  /- Step 2: Theorem 28 for `J₀` at `B` -/
  have hU₁c : IsClosed (Z₂ ∪ (f '' Icc 0 c ∪ f '' Icc d 1)) :=
    hZ₂.isClosed.union ((hcIm 0 c).union (hcIm d 1))
  have hbU₁ : f b ∈ R ∩ (Z₂ ∪ (f '' Icc 0 c ∪ f '' Icc d 1))ᶜ := by
    refine ⟨hBR, ?_⟩
    rintro (h | ⟨u, hu, hu'⟩ | ⟨u, hu, hu'⟩)
    · exact hbZ (hZ₁Z (hZ₂Z₁ h))
    · have := hinj hu'; subst this; exact absurd hu.2 (not_le.mpr hcb')
    · have := hinj hu'; subst this; exact absurd hu.1 (not_le.mpr hbd')
  obtain ⟨R₁, hR₁, hbR₁, hR₁U⟩ := (mem_nhds_iff_region h1).mp
    (((isOpen_region hR).inter hU₁c.isOpen_compl).mem_nhds hbU₁)
  have hbJ₀ : f b ∈ f '' Icc c d ∪ Z₂ := Or.inl (mem_image_of_mem _ ⟨hcb'.le, hbd'.le⟩)
  have hpar₁ : ∀ x ∈ f '' Icc c d ∪ Z₂, x ∈ R₁ → ∃ u, c < u ∧ u < d ∧ f u = x := by
    intro x hxJ hxR₁
    have hx := (hR₁U hxR₁).2
    simp only [mem_compl_iff, mem_union, not_or] at hx
    rcases hxJ with ⟨u, hu, rfl⟩ | h
    · refine ⟨u, lt_of_le_of_ne hu.1 fun e => hx.1 (e ▸ hZ₂.left_mem),
        lt_of_le_of_ne hu.2 fun e => hx.1 (e ▸ hZ₂.right_mem), rfl⟩
    · exact absurd h hx.1
  obtain ⟨e₁, s₁, F₁, P, hce₁, he₁b, hbs₁, hs₁d, hF₁, hF₁M, hP, hPJ₀, hPR₁, hbP⟩ :
      ∃ e₁ s₁ : unitInterval, ∃ F₁ P : Set S, c < e₁ ∧ e₁ < b ∧ b < s₁ ∧ s₁ < d ∧
        TArc (f e₁) (f s₁) F₁ ∧ F₁ \ {f e₁, f s₁} ⊆ R₀ ∩ R₁ ∧ TArc (f e₁) (f s₁) P ∧
        P ⊆ f '' Icc c d ∪ Z₂ ∧ P ⊆ R₁ ∧ f b ∈ P := by
    obtain ⟨E₁, G₁, F₁, P, P', hF₁, hF₁M, hP, -, -, hPJ, hbP, hPR₁⟩ :=
      fa_theorem28 h1 h2 h3 h4 h51 h6 h7
        ((isInteriorOf_iff h1 h3 h4 h51).mpr ⟨hJ₀, hR₀, hR₀J⟩) hbJ₀ hR₁ hbR₁ (Or.inl rfl)
    rw [isArc_iff_tarc h1 h3 h4 h51] at hF₁ hP
    have hPJ₀ : P ⊆ f '' Icc c d ∪ Z₂ := hPJ ▸ subset_union_left
    obtain ⟨u, hcu, hud, rfl⟩ := hpar₁ E₁ (hPJ₀ hP.left_mem) (hPR₁ hP.left_mem)
    obtain ⟨v, hcv, hvd, rfl⟩ := hpar₁ G₁ (hPJ₀ hP.right_mem) (hPR₁ hP.right_mem)
    have hPr : P ⊆ range f := fun x hx => by
      obtain ⟨w, -, -, rfl⟩ := hpar₁ x (hPJ₀ hx) (hPR₁ hx); exact mem_range_self w
    simp only [openArc, mem_diff, mem_insert_iff, mem_singleton_iff, not_or] at hbP
    rcases order_of_arc_sub hf hP hPr hbP.1 (fun e => hbP.2.1 (e ▸ rfl))
      (fun e => hbP.2.2 (e ▸ rfl)) with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact ⟨u, v, F₁, P, hcu, h1', h2', hvd, hF₁, hF₁M, hP, hPJ₀, hPR₁, hbP.1⟩
    · refine ⟨v, u, F₁, P, hcv, h1', h2', hud, hF₁.symm, ?_, hP.symm, hPJ₀, hPR₁, hbP.1⟩
      rw [pair_comm]; exact hF₁M
  have hPr : P ⊆ range f := fun x hx => by
    obtain ⟨w, -, -, rfl⟩ := hpar₁ x (hPJ₀ hx) (hPR₁ hx); exact mem_range_self w
  have hR₁R : R₁ ⊆ R := fun x hx => (hR₁U hx).1
  have hF₁K : ∀ x ∈ F₁ \ {f e₁, f s₁}, x ∉ range f := by
    rintro x hx ⟨u, rfl⟩
    have hxR₀ := (hF₁M hx).1
    have hxU := (hR₁U (hF₁M hx).2).2
    simp only [mem_compl_iff, mem_union, mem_image, not_or, not_exists, not_and] at hxU
    have hu : u ∈ Icc c d := ⟨not_lt.mp fun h => hxU.2.1 u ⟨nonneg', h.le⟩ rfl,
      not_lt.mp fun h => hxU.2.2 u ⟨h.le, le_one'⟩ rfl⟩
    exact notMem_of_mem_frontier hR₀o (hR₀J ▸ Or.inl (mem_image_of_mem _ hu)) hxR₀
  have hbF₁ : f b ∉ F₁ := by
    intro h
    by_cases hb' : f b ∈ ({f e₁, f s₁} : Set S)
    · rcases hb' with e | e
      · exact he₁b.ne' (hinj e)
      · exact hbs₁.ne (hinj e)
    · exact hF₁K (f b) ⟨h, hb'⟩ (mem_range_self b)
  have hF₁R : F₁ ⊆ R := by
    intro x hx
    by_cases hx' : x ∈ ({f e₁, f s₁} : Set S)
    · rcases hx' with rfl | rfl
      · exact hR₁R (hPR₁ hP.left_mem)
      · exact hR₁R (hPR₁ hP.right_mem)
    · exact hR₁R (hF₁M ⟨hx, hx'⟩).2
  /- Step 3: the closed curve `J₁ = E₁F₁G₁BE₁` and Theorem 28 for it at `B` -/
  have hJ₁ : TSCC (F₁ ∪ P) := by
    refine ⟨f e₁, f s₁, F₁, P, hF₁, hP, ?_, rfl⟩
    apply subset_antisymm
    · rintro x ⟨hx1, hx2⟩
      by_contra hx
      exact notMem_of_mem_frontier hR₀o (hR₀J ▸ hPJ₀ hx2) (hF₁M ⟨hx1, hx⟩).1
    · rintro x hx
      rcases hx with rfl | rfl
      · exact ⟨hF₁.left_mem, hP.left_mem⟩
      · exact ⟨hF₁.right_mem, hP.right_mem⟩
  obtain ⟨I₁, hI₁, hI₁J⟩ := hA8 _ hJ₁
  have hI₁o := isOpen_region hI₁
  have hJ₁cl : F₁ ∪ P ⊆ closure I₁ := hI₁J ▸ frontier_subset_closure
  have hU₂c : IsClosed (F₁ ∪ (f '' Icc 0 e₁ ∪ f '' Icc s₁ 1)) :=
    hF₁.isClosed.union ((hcIm 0 e₁).union (hcIm s₁ 1))
  have hbU₂ : f b ∈ R₁ ∩ (F₁ ∪ (f '' Icc 0 e₁ ∪ f '' Icc s₁ 1))ᶜ := by
    refine ⟨hbR₁, ?_⟩
    rintro (h | ⟨u, hu, hu'⟩ | ⟨u, hu, hu'⟩)
    · exact hbF₁ h
    · have := hinj hu'; subst this; exact absurd hu.2 (not_le.mpr he₁b)
    · have := hinj hu'; subst this; exact absurd hu.1 (not_le.mpr hbs₁)
  obtain ⟨R₂, hR₂, hbR₂, hR₂U⟩ := (mem_nhds_iff_region h1).mp
    (((isOpen_region hR₁).inter hU₂c.isOpen_compl).mem_nhds hbU₂)
  have hR₂R₁ : R₂ ⊆ R₁ := fun x hx => (hR₂U hx).1
  have hR₂F₁ : ∀ x ∈ R₂, x ∉ F₁ := fun x hx h => (hR₂U hx).2 (Or.inl h)
  have hpar₂ : ∀ x ∈ F₁ ∪ P, x ∈ R₂ → ∃ u, e₁ < u ∧ u < s₁ ∧ f u = x := by
    intro x hxJ hxR₂
    have hx := (hR₂U hxR₂).2
    simp only [mem_compl_iff, mem_union, mem_image, not_or, not_exists, not_and] at hx
    rcases hxJ with h | h
    · exact absurd h hx.1
    · obtain ⟨u, rfl⟩ := hPr h
      exact ⟨u, not_le.mp fun h' => hx.2.1 u ⟨nonneg', h'⟩ rfl,
        not_le.mp fun h' => hx.2.2 u ⟨h', le_one'⟩ rfl, rfl⟩
  obtain ⟨e₂, s₂, F₂, Pb, Po, he₁e₂, he₂b, hbs₂, hs₂s₁, hF₂, hF₂M, hPb, hPo, hPbPo, hPbJ₁, hbPb,
      hPbR₂⟩ :
      ∃ e₂ s₂ : unitInterval, ∃ F₂ Pb Po : Set S, e₁ < e₂ ∧ e₂ < b ∧ b < s₂ ∧ s₂ < s₁ ∧
        TArc (f e₂) (f s₂) F₂ ∧ F₂ \ {f e₂, f s₂} ⊆ (closure I₁)ᶜ ∩ R₂ ∧
        TArc (f e₂) (f s₂) Pb ∧ TArc (f e₂) (f s₂) Po ∧ Pb ∩ Po = {f e₂, f s₂} ∧
        Pb ∪ Po = F₁ ∪ P ∧ f b ∈ Pb \ {f e₂, f s₂} ∧ Pb ⊆ R₂ := by
    obtain ⟨E₂, G₂, F₂, Pb, Po, hF₂, hF₂M, hPb, hPo, hPbPo, hPbJ, hbPb, hPbR₂⟩ :=
      fa_theorem28 h1 h2 h3 h4 h51 h6 h7
        ((isInteriorOf_iff h1 h3 h4 h51).mpr ⟨hJ₁, hI₁, hI₁J⟩) (Or.inr hbP) hR₂ hbR₂
        (Or.inr rfl)
    rw [isArc_iff_tarc h1 h3 h4 h51] at hF₂ hPb hPo
    rw [ext_eq_compl_closure h1] at hF₂M
    have hPbJ₁ : Pb ⊆ F₁ ∪ P := hPbJ ▸ subset_union_left
    obtain ⟨u, hcu, hud, rfl⟩ := hpar₂ E₂ (hPbJ₁ hPb.left_mem) (hPbR₂ hPb.left_mem)
    obtain ⟨v, hcv, hvd, rfl⟩ := hpar₂ G₂ (hPbJ₁ hPb.right_mem) (hPbR₂ hPb.right_mem)
    have hPbr : Pb ⊆ range f := fun x hx => by
      obtain ⟨w, -, -, rfl⟩ := hpar₂ x (hPbJ₁ hx) (hPbR₂ hx); exact mem_range_self w
    have hbPb' := hbPb
    simp only [openArc, mem_diff, mem_insert_iff, mem_singleton_iff, not_or] at hbPb'
    rcases order_of_arc_sub hf hPb hPbr hbPb'.1 (fun e => hbPb'.2.1 (e ▸ rfl))
      (fun e => hbPb'.2.2 (e ▸ rfl)) with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact ⟨u, v, F₂, Pb, Po, hcu, h1', h2', hvd, hF₂, hF₂M, hPb, hPo, hPbPo, hPbJ, hbPb,
        hPbR₂⟩
    · refine ⟨v, u, F₂, Pb, Po, hcv, h1', h2', hud, hF₂.symm, ?_, hPb.symm, hPo.symm, ?_, hPbJ,
        ?_, hPbR₂⟩
      · rw [pair_comm]; exact hF₂M
      · rw [pair_comm]; exact hPbPo
      · rw [pair_comm]; exact hbPb
  have hPbJ₁' : Pb ⊆ F₁ ∪ P := hPbJ₁ ▸ subset_union_left
  have hPoJ₁ : Po ⊆ F₁ ∪ P := hPbJ₁ ▸ subset_union_right
  have hPbr : Pb ⊆ range f := fun x hx => by
    obtain ⟨w, -, -, rfl⟩ := hpar₂ x (hPbJ₁' hx) (hPbR₂ hx); exact mem_range_self w
  have hF₂J₁ : ∀ x ∈ F₂ \ {f e₂, f s₂}, x ∉ F₁ ∪ P := fun x hx h => (hF₂M hx).1 (hJ₁cl h)
  have hF₂R₂ : F₂ ⊆ R₂ := by
    intro x hx
    by_cases hx' : x ∈ ({f e₂, f s₂} : Set S)
    · rcases hx' with rfl | rfl
      · exact hPbR₂ hPb.left_mem
      · exact hPbR₂ hPb.right_mem
    · exact (hF₂M ⟨hx, hx'⟩).2
  /- Step 4: Theorem 27 for `J₁` and `E₂F₂G₂` -/
  have hJ₂ := tscc_of_open_disjoint hPb hF₂ hPbJ₁' hF₂J₁
  have hJ₃ := tscc_of_open_disjoint hPo hF₂ hPoJ₁ hF₂J₁
  obtain ⟨I₂, hI₂, hI₂J⟩ := hA8 _ hJ₂
  obtain ⟨R₃, hR₃, hR₃J⟩ := hA8 _ hJ₃
  have hTI₁ : TInt σ.region (F₁ ∪ P) I₁ := ⟨hJ₁, hI₁, hI₁J⟩
  have hTI₂ : TInt σ.region (F₂ ∪ Pb) I₂ := ⟨hJ₂, hI₂, hI₂J⟩
  have hTR₃ : TInt σ.region (F₂ ∪ Po) R₃ := ⟨hJ₃, hR₃, hR₃J⟩
  have he₁Po : f e₁ ∈ Po \ {f e₂, f s₂} := by
    refine ⟨?_, ?_⟩
    · rcases (hPbJ₁ ▸ (Or.inl hF₁.left_mem : f e₁ ∈ F₁ ∪ P) : f e₁ ∈ Pb ∪ Po) with h | h
      · exact absurd hF₁.left_mem (hR₂F₁ _ (hPbR₂ h))
      · exact h
    · rintro (e | e)
      · exact he₁e₂.ne (hinj e)
      · exact (he₁b.trans hbs₂).ne (hinj e)
  have hcpt : ∀ R ∈ σ.region, IsCompact (closure R) := fun R hR => isCompact_closure_region h1 h4 hR
  have hnc := not_isCompact_univ h1 h5
  have harc := arcConn h1 h3 h4 h51 h2
  have h27 := th27 hopen_region (hpc_region h1 h2) h21 harc hA8 (hext_region h1 h3) hcpt hnc
    hTI₁ hPo hPb (by rw [inter_comm]; exact hPbPo) (by rw [union_comm]; exact hPbJ₁) he₁Po hbPb
    hF₂ (fun x hx => (hF₂M hx).1) hTR₃ hTI₂
  have h27' := th27 hopen_region (hpc_region h1 h2) h21 harc hA8 (hext_region h1 h3) hcpt hnc
    hTI₁ hPb hPo hPbPo hPbJ₁ hbPb he₁Po hF₂ (fun x hx => (hF₂M hx).1) hTI₂ hTR₃
  have hI₂R₂ : I₂ ⊆ R₂ := h21 R₂ hR₂ I₂ hI₂ (by
    rw [hI₂J]
    exact (union_subset hF₂R₂ hPbR₂).trans subset_closure)
  have he₁I₂ : f e₁ ∈ (closure I₂)ᶜ := by
    rcases h27.1 with h | h
    · exact absurd hF₁.left_mem (hR₂F₁ _ (hI₂R₂ (h27.2 h).1))
    · exact h
  obtain ⟨hbR₃, hR₃eq⟩ := h27'.2 he₁I₂
  have hdis : Disjoint I₁ I₂ := th24_disj hopen_region (hpc_region h1 h2) hTR₃
    (subset_union_right : Po ⊆ F₂ ∪ Po) (hPbJ₁.symm ▸ hTI₁ : TInt σ.region (Pb ∪ Po) I₁)
    (by rw [union_comm]; exact hTI₂) (by rw [hR₃eq]; exact subset_union_right)
    (fun x hx => (hF₂M hx).1) hF₂.nonempty_diff
  /- The interiors miss the arc -/
  have hF₁R₁ : F₁ ⊆ R₁ := by
    intro x hx
    by_cases hx' : x ∈ ({f e₁, f s₁} : Set S)
    · rcases hx' with rfl | rfl
      · exact hPR₁ hP.left_mem
      · exact hPR₁ hP.right_mem
    · exact (hF₁M ⟨hx, hx'⟩).2
  have hI₁R₀ : I₁ ⊆ R₀ := th24_sub h21 ⟨hJ₀, hR₀, hR₀J⟩ (hPJ₀ hP.left_mem) (hPJ₀ hP.right_mem)
    hPJ₀ (fun x hx => (hF₁M hx).1) hTI₁
  have hI₁R₁ : I₁ ⊆ R₁ := h21 R₁ hR₁ I₁ hI₁ (by
    rw [hI₁J]; exact (union_subset hF₁R₁ hPR₁).trans subset_closure)
  have hI₁K : Disjoint I₁ (range f) := by
    rw [disjoint_left]
    rintro _ hx ⟨u, rfl⟩
    by_cases hu : u ∈ Icc c d
    · exact notMem_of_mem_frontier hR₀o (hR₀J ▸ Or.inl (mem_image_of_mem _ hu)) (hI₁R₀ hx)
    · apply (hR₁U (hI₁R₁ hx)).2
      simp only [mem_Icc, not_and_or, not_le] at hu
      rcases hu with hu | hu
      · exact Or.inr (Or.inl (mem_image_of_mem _ ⟨nonneg', hu.le⟩))
      · exact Or.inr (Or.inr (mem_image_of_mem _ ⟨hu.le, le_one'⟩))
  have hR₃o := isOpen_region hR₃
  have hI₂K : Disjoint I₂ (range f) := by
    rw [disjoint_left]
    rintro _ hx ⟨u, rfl⟩
    by_cases hu : u ∈ Icc e₁ s₁
    · have hP' : f u ∈ Pb ∪ Po :=
        hPbJ₁ ▸ Or.inr (image_Icc_subset_of_arc hf hP hPr (mem_image_of_mem _ hu))
      rcases hP' with h | h
      · exact notMem_of_mem_frontier (isOpen_region hI₂) (by rw [hI₂J]; exact Or.inr h) hx
      · exact notMem_of_mem_frontier hR₃o (by rw [hR₃J]; exact Or.inr h)
          (by rw [hR₃eq]; exact Or.inr hx)
    · apply (hR₂U (hI₂R₂ hx)).2
      simp only [mem_Icc, not_and_or, not_le] at hu
      rcases hu with hu | hu
      · exact Or.inr (Or.inl (mem_image_of_mem _ ⟨nonneg', hu.le⟩))
      · exact Or.inr (Or.inr (mem_image_of_mem _ ⟨hu.le, le_one'⟩))
  have hF₂K : Disjoint (F₂ \ {f e₂, f s₂}) (range f) := by
    rw [disjoint_left]
    rintro x hx ⟨u, rfl⟩
    have hx' := (hR₂U (hF₂M hx).2).2
    simp only [mem_compl_iff, mem_union, mem_image, not_or, not_exists, not_and] at hx'
    have hu : u ∈ Icc e₁ s₁ := ⟨not_lt.mp fun h' => hx'.2.1 u ⟨nonneg', h'.le⟩ rfl,
      not_lt.mp fun h' => hx'.2.2 u ⟨h'.le, le_one'⟩ rfl⟩
    exact (hF₂M hx).1 (hJ₁cl (Or.inr (image_Icc_subset_of_arc hf hP hPr
      (mem_image_of_mem f hu))))
  refine ⟨e₁, s₁, e₂, s₂, F₁, P, F₂, Pb, I₁, I₂, R₃, lt_of_le_of_lt nonneg' hce₁, he₁e₂, he₂b,
    hbs₂, hs₂s₁, hs₁d.trans_le le_one', hF₁, hF₁R, disjoint_left.mpr hF₁K, hP, hPr, hbP,
    hPR₁.trans hR₁R, hTI₁, hF₂, hF₂R₂.trans (hR₂R₁.trans hR₁R), hF₂K, hPb, hPbr, hbPb.1,
    hPbR₂.trans (hR₂R₁.trans hR₁R), hTI₂, hR₃o, hbR₃, hR₃eq, hdis, hI₁K, hI₂K, ?_⟩
  rw [hR₃eq]
  rintro x ((h | h) | h)
  · exact hR₁R (hR₂R₁ (hPbR₂ h.1))
  · exact hR₁R (hI₁R₁ h)
  · exact hR₁R (hR₂R₁ (hI₂R₂ h))

/-- **Theorem 31.** *Axioms used: 1, 2, 3, 4, 5, 6, 7, 8.* Moore's proof (Theorems 15, 21, 23's
construction, 24, 27, 28), see the module docstring.
**Shape change:** the axioms are made explicit. **Tacit hypothesis (check 3):** `B` is a point of
the open arc `CD` (`B ≠ C, D`), which the order `C E B G D` requires; the skeleton already
carries it (`hB : B ∈ openArc C D K`). -/
theorem fa_theorem31 (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
    {C D B Xp : S} {K L : Set S} (hK : σ.IsArc C D K) (hB : B ∈ openArc C D K)
    (hL : σ.IsArc B Xp L) (hKL : K ∩ L = {B}) {R : Set S} (hR : R ∈ σ.region) (hBR : B ∈ R) :
    ∃ E G : S, ∃ F seg : Set S, σ.IsArc E G F ∧ F ⊆ R ∧ σ.InOrder K C D [C, E, B, G, D] ∧
      σ.IsArc E G seg ∧ seg ⊆ K ∧ B ∈ seg ∧ seg ⊆ R ∧ Disjoint (openArc E G F) K ∧
      ∃ H : S, ∃ BH : Set S, σ.IsArc B H BH ∧ BH ⊆ L ∧
        ∃ I, σ.IsInteriorOf (F ∪ seg) I ∧ BH \ {B} ⊆ I := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  rw [isArc_iff_tarc h1 h3 h4 h51] at hK hL
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := hK
  have hinj := hf.injective
  obtain ⟨b, rfl⟩ := hB.1
  have hbAB := hB.2
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hbAB
  have hb0 : 0 < b := lt_of_le_of_ne nonneg' fun e => hbAB.1 (by rw [← e])
  have hb1 : b < 1 := lt_of_le_of_ne le_one' fun e => hbAB.2 (by rw [e])
  obtain ⟨e₁, s₁, e₂, s₂, F₁, P, F₂, Pb, I₁, I₂, R₃, he₁, he₁e₂, he₂b, hbs₂, hs₂s₁, hs₁, hF₁,
    hF₁R, hF₁K, hP, hPr, hbP, hPR, hTI₁, hF₂, hF₂R, hF₂K, hPb, hPbr, hbPb, hPbR, hTI₂, hR₃o,
    hbR₃, hR₃eq, hdis, -, -, -⟩ := th31_pocket h1 h2 h3 h4 h5 h6 h7 h8 hf hb0 hb1 hR hBR
  have hI₁o := isOpen_region hTI₁.2.1
  /- Step 5: the segment `BH` of `BX` -/
  obtain ⟨-, l, hl, rfl, hl0, rfl⟩ := hL
  obtain ⟨u', hu', hu'sub⟩ := exists_Ico_subset_of_mem_nhds
    ((hR₃o.preimage hl.continuous).mem_nhds (show l 0 ∈ R₃ by rw [hl0]; exact hbR₃))
    ⟨1, zero_lt_one' unitInterval⟩
  obtain ⟨τ, hτ0, hτu⟩ := exists_between hu'
  have hBH : TArc (f b) (l τ) (l '' Icc 0 τ) := hl0 ▸ TArc.image_Icc hl hτ0
  have hBHsub : l '' Icc 0 τ \ {f b} ⊆ I₁ ∪ I₂ := by
    rintro _ ⟨⟨t, ht, rfl⟩, htb⟩
    have hR₃t : l t ∈ R₃ := hu'sub ⟨ht.1, ht.2.trans_lt hτu⟩
    rw [hR₃eq] at hR₃t
    rcases hR₃t with (h | h) | h
    · have : l t ∈ range f ∩ range l := ⟨hPbr h.1, mem_range_self t⟩
      rw [hKL] at this
      exact absurd this htb
    · exact Or.inl h
    · exact Or.inr h
  have hInOrder : ∀ e s : unitInterval, 0 < e → e < b → b < s → s < 1 →
      σ.InOrder (range f) (f 0) (f 1) [f 0, f e, f b, f s, f 1] := by
    intro e s he hes hsb hs1
    refine ⟨f, hf, rfl, rfl, rfl, [0, e, b, s, 1], ?_, rfl⟩
    rw [← List.isChain_iff_pairwise]
    simp [he, hes, hsb, hs1]
  rcases hBH.symm.isPreconnected_diff_right.subset_or_subset hI₁o (isOpen_region hTI₂.2.1) hdis
    hBHsub with h | h
  · exact ⟨f e₁, f s₁, F₁, P, (isArc_iff_tarc h1 h3 h4 h51).mpr hF₁, hF₁R,
      hInOrder e₁ s₁ he₁ (he₁e₂.trans he₂b) (hbs₂.trans hs₂s₁) hs₁,
      (isArc_iff_tarc h1 h3 h4 h51).mpr hP, hPr, hbP, hPR, hF₁K, l τ, _,
      (isArc_iff_tarc h1 h3 h4 h51).mpr hBH, image_subset_range _ _, I₁,
      (isInteriorOf_iff h1 h3 h4 h51).mpr hTI₁, h⟩
  · exact ⟨f e₂, f s₂, F₂, Pb, (isArc_iff_tarc h1 h3 h4 h51).mpr hF₂, hF₂R,
      hInOrder e₂ s₂ (he₁.trans he₁e₂) he₂b hbs₂ (hs₂s₁.trans hs₁),
      (isArc_iff_tarc h1 h3 h4 h51).mpr hPb, hPbr, hbPb, hPbR, hF₂K, l τ, _,
      (isArc_iff_tarc h1 h3 h4 h51).mpr hBH, image_subset_range _ _, I₂,
      (isInteriorOf_iff h1 h3 h4 h51).mpr hTI₂, h⟩

end HPC.Moore
