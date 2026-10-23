import HPC.HO16.OrdFold

/-!
# Batch 196, §3: library for Proposition 19

The hypotheses of Proposition 19 in the full fold (`P19`), and the basic facts H–O use on
pp. 203–208: (19.1)–(19.3) for the sheets, preimages of the frontier sets, finiteness of
preimages, and consistent complements pulled back along `φ`.
-/

namespace HPC.HO16

open Set Topology Metric Filter

section Lib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## General facts on sheets and preimages -/

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- On a sheet on which `π` is injective, the preimage of the image of a part is the part. -/
theorem inter_preimage_image_of_injOn {Fi X : Set (E × ℝ)} (hinj : InjOn Prod.fst Fi)
    (hX : X ⊆ Fi) : Fi ∩ Prod.fst ⁻¹' (Prod.fst '' X) = X := by
  apply Subset.antisymm
  · rintro p ⟨hp, q, hq, hqp⟩
    rw [hinj (hX hq) hp hqp] at hq
    exact hq
  · intro p hp; exact ⟨hX hp, p, hp, rfl⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem foldPre_mono {F F' S S' : Set (E × ℝ)} (hF : F ⊆ F') (hS : S ⊆ S') :
    foldPre F S ⊆ foldPre F' S' :=
  fun _ hq => ⟨⟨hF hq.1.1, hq.1.2⟩, hS hq.2⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem foldPre_union (F S S' : Set (E × ℝ)) :
    foldPre F (S ∪ S') = foldPre F S ∪ foldPre F S' := by
  ext q; simp only [foldPre, mem_inter_iff, mem_preimage, mem_union]; tauto

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem foldPre_empty (F : Set (E × ℝ)) : foldPre F ∅ = ∅ := by
  ext q; simp [foldPre]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem disjoint_foldPre {F S S' : Set (E × ℝ)} (h : Disjoint S S') :
    Disjoint (foldPre F S) (foldPre F S') :=
  Set.disjoint_left.2 fun _ hq hq' => Set.disjoint_left.1 h hq.2 hq'.2

omit [NormedSpace ℝ E] in
theorem isClosed_foldPre {F S : Set (E × ℝ)} (hF : IsClosed F) (hS : IsClosed S) :
    IsClosed (foldPre F S) :=
  (hF.prod isClosed_Icc).inter (hS.preimage continuous_phiStar)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `π(φ⋆⁻¹(X) ∩ T⋆)` lies over `π(X)`. -/
theorem fst_mem_of_mem_foldPre {F S : Set (E × ℝ)} {q : (E × ℝ) × ℝ} (hq : q ∈ foldPre F S) :
    q.1 ∈ F ∧ q.1.1 ∈ Prod.fst '' S :=
  ⟨hq.1.1, phiStar q, hq.2, rfl⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Over a point of a straight set `X`, `φ⋆` takes the values of `X`: if `phiStar q ∈ X'`,
`X' ⊆ X` lies over `π(Y)` with `Y ⊆ X`, and `π` is injective on `X`, then `phiStar q ∈ Y`. -/
theorem phiStar_mem_of_injOn {X Y : Set (E × ℝ)} (hinj : InjOn Prod.fst X) (hYX : Y ⊆ X)
    {q : (E × ℝ) × ℝ} (hq : phiStar q ∈ X) (hqY : q.1.1 ∈ Prod.fst '' Y) : phiStar q ∈ Y := by
  obtain ⟨y, hy, hyq⟩ := hqY
  rw [hinj (hYX hy) hq hyq] at hy
  exact hy

omit [NormedSpace ℝ E] in
/-- Preimages of finite sets under `φ⋆` are finite, for a union of three sheets on which `π` is
injective. -/
theorem foldPre_finite {F₁ F₂ F₃ X : Set (E × ℝ)} (h₁ : InjOn Prod.fst F₁)
    (h₂ : InjOn Prod.fst F₂) (h₃ : InjOn Prod.fst F₃) (hX : X.Finite) :
    (foldPre (F₁ ∪ F₂ ∪ F₃) X).Finite := by
  classical
  have key : ∀ {Fi : Set (E × ℝ)}, InjOn Prod.fst Fi →
      (foldPre Fi X).Finite := by
    intro Fi hi
    refine (hX.image fun x => ((Function.invFunOn Prod.fst Fi x.1), x.2)).subset ?_
    rintro q ⟨⟨hqF, -⟩, hqX⟩
    refine ⟨phiStar q, hqX, ?_⟩
    have hex : ∃ a ∈ Fi, a.1 = q.1.1 := ⟨q.1, hqF, rfl⟩
    have h1 : Function.invFunOn Prod.fst Fi q.1.1 = q.1 :=
      hi (Function.invFunOn_mem hex) hqF (Function.invFunOn_eq hex)
    simp only [phiStar]
    rw [h1]
  refine ((key h₁).union ((key h₂).union (key h₃))).subset ?_
  rintro q ⟨⟨(h | h) | h, hI⟩, hqX⟩
  · exact Or.inl ⟨⟨h, hI⟩, hqX⟩
  · exact Or.inr (Or.inl ⟨⟨h, hI⟩, hqX⟩)
  · exact Or.inr (Or.inr ⟨⟨h, hI⟩, hqX⟩)

/-- **Consistent complements pulled back along `φ = π`** (pp. 207–208). `X ⊆ F` is closed, the
components of `F \ X` lie over `G \ A`, the frontier points of `F \ X` lie over `A`, and
`cl(F \ X) ⊆ R`. If `A` has consistent complement relative to `B` in `G`, then `X` has
consistent complement relative to `R ∩ φ⁻¹(B)` in `F`. -/
theorem hasConsCompl_pullback {G A B : Set E} {F X R : Set (E × ℝ)} (hG : IsClosed G)
    (hF : IsPLGraph F) (hFG : Prod.fst '' F ⊆ G) (hX : IsClosed X)
    (hXA : F ∩ Prod.fst ⁻¹' A ⊆ X) (hfr : X ∩ closure (F \ X) ⊆ Prod.fst ⁻¹' A)
    (hR : closure (F \ X) ⊆ R) (hc : HasConsCompl G A B) :
    HasConsCompl F X (R ∩ Prod.fst ⁻¹' B) := by
  intro x hx
  set C := connectedComponentIn (F \ X) x with hCdef
  have hCsub : C ⊆ F \ X := connectedComponentIn_subset _ _
  have hxA : x.1 ∈ G \ A := ⟨hFG ⟨x, hx.1, rfl⟩, fun h => hx.2 (hXA ⟨hx.1, h⟩)⟩
  set C' := connectedComponentIn (G \ A) x.1 with hC'def
  have hCC' : Prod.fst '' C ⊆ C' := by
    refine (isPreconnected_connectedComponentIn.image _ continuous_fst.continuousOn).subset_connectedComponentIn
      ⟨x, mem_connectedComponentIn hx, rfl⟩ ?_
    rintro _ ⟨p, hp, rfl⟩
    have hp' := hCsub hp
    exact ⟨hFG ⟨p, hp'.1, rfl⟩, fun h => hp'.2 (hXA ⟨hp'.1, h⟩)⟩
  have hC'sub : C' ⊆ G \ A := connectedComponentIn_subset _ _
  -- the frontier of `C` lies over the frontier of `C'`
  have hfrC : relFrontier F C ⊆ R ∩ Prod.fst ⁻¹' relFrontier G C' := by
    intro z hz
    have hzX : z ∈ X := hF.relFrontier_comp_subset hX x hz
    have hzcl : z ∈ closure (F \ X) := closure_mono hCsub hz.1
    have hzA : z.1 ∈ A := hfr ⟨hzX, hzcl⟩
    refine ⟨hR hzcl, ?_⟩
    have h1 : z.1 ∈ closure C' :=
      closure_mono hCC' (map_mem_closure continuous_fst hz.1 fun p hp => ⟨p, hp, rfl⟩)
    rcases closure_subset_union_relFrontier hG (hC'sub.trans diff_subset) h1 with h | h
    · exact absurd hzA (hC'sub h).2
    · exact h
  rcases hc x.1 hxA with h | h
  · exact Or.inl fun z hz => ⟨(hfrC hz).1, h (hfrC hz).2⟩
  · exact Or.inr (Set.disjoint_left.2 fun z hz hz' =>
      Set.disjoint_left.1 h (hfrC hz).2 hz'.2)

end Lib

end HPC.HO16
