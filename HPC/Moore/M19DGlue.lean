import HPC.Moore.M19CDMain

/-!
# Moore 1919, Theorem D: gluing rulings along a cut

If `ABCDA` is cut along an arc `x` from `AB` to `CD` into `AXX′DA` and `XBCX′X`, and each half has
a ruling all of whose subdivisions have a property `Good` inherited by subsets, then so has `ABCDA`
(`Space.Quad.Cut.rulable`). This is the inductive step of `Space.ArcRuling.refine`
(`refine_stepX`), with the rulings of the halves given. Rulability is invariant under rotation and
reflection of the quadrilateral (`Space.Rulable.of_rot`, `Space.Rulable.of_refl`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

section Sym

variable {I sAB sBC sCD sDA : Set S} {A B C D : S} {Good : Set S → Prop}

theorem Space.Rulable.of_rot (h1 : σ.Axiom1) (H : σ.Rulable Good I sBC sCD sDA sAB B C D A) :
    σ.Rulable Good I sAB sBC sCD sDA A B C D := by
  obtain ⟨𝒳, 𝒴, R, hG⟩ := H
  refine ⟨𝒴, 𝒳, ((R.rot h1).rot h1).rot h1, ?_⟩
  rw [union_comm]; exact hG

theorem Space.Rulable.of_refl (h1 : σ.Axiom1) (H : σ.Rulable Good I sAB sDA sCD sBC B A D C) :
    σ.Rulable Good I sAB sBC sCD sDA A B C D := by
  obtain ⟨𝒳, 𝒴, R, hG⟩ := H
  exact ⟨𝒳, 𝒴, R.rule_refl h1, hG⟩

theorem Space.Rulable.to_rot (h1 : σ.Axiom1) (H : σ.Rulable Good I sAB sBC sCD sDA A B C D) :
    σ.Rulable Good I sBC sCD sDA sAB B C D A := by
  obtain ⟨𝒳, 𝒴, R, hG⟩ := H
  refine ⟨𝒴, 𝒳, R.rot h1, ?_⟩
  rw [union_comm]; exact hG

end Sym

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S} {Good : Set S → Prop}

/-- **Gluing rulings along a cut.** If both halves of the cut of `ABCDA` along `x` have rulings
all of whose subdivisions are `Good`, so has `ABCDA`. -/
theorem Space.Quad.Cut.rulable (hGood : ∀ U V, U ⊆ V → Good V → Good U)
    {q : σ.Quad J I A B C D sAB sBC sCD sDA} {x : Set S} (c : q.Cut x)
    (hxq : σ.XArc I sAB sCD A B C D x)
    (HA : σ.Rulable Good c.IA c.s₁ x c.t₁ sDA A c.X c.X' D)
    (HB : σ.Rulable Good c.IB c.s₂ sBC c.t₂ x c.X B C c.X') :
    σ.Rulable Good I sAB sBC sCD sDA A B C D := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨𝒳A', 𝒴A', RA', hPA⟩ := HA
  obtain ⟨𝒳B', 𝒴B', RB', hPB⟩ := HB
  have finE : ∀ {𝒵 : Set (Set S)}, 𝒵.Finite → (∀ y ∈ 𝒵, (y ∩ x).Finite) →
      (x ∩ ⋃₀ 𝒵).Finite := fun hf h =>
    ((hf.image (· ∩ x)).sUnion (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)).subset
      (by rintro z ⟨hzx, y, hy, hzy⟩; exact ⟨_, ⟨y, hy, rfl⟩, hzy, hzx⟩)
  have hEB : x ∩ ⋃₀ 𝒴B' ⊆ x \ {c.X, c.X'} := by
    rintro z ⟨hzx, yb, hyb, hzyb⟩
    obtain ⟨P, e, -, he, -, -, hybx, -⟩ := c.yB_spec (RB'.arcY yb hyb)
    rw [Space.Quad.Cut.single hzyb hzx hybx, pair_comm]; exact he
  have hEBf : (x ∩ ⋃₀ 𝒴B').Finite := finE RB'.finY fun y hy => by
    obtain ⟨P, e, -, -, -, -, hybx, -⟩ := c.yB_spec (RB'.arcY y hy)
    rw [hybx]; exact finite_singleton e
  obtain ⟨𝒴A'', hYA', RA'', hcovA, -⟩ :=
    RA'.extendY_finite h1 h2 h3 h4 h5 h6 h7 h8 c.qA hEBf hEB
  have hEA : x ∩ ⋃₀ 𝒴A'' ⊆ x \ {c.X, c.X'} := by
    rintro z ⟨hzx, ya, hya, hzya⟩
    obtain ⟨e, Q, he, -, -, -, hyax, -⟩ := c.yA_spec (RA''.arcY ya hya)
    rw [Space.Quad.Cut.single hzya hzx hyax]; exact he
  have hEAf : (x ∩ ⋃₀ 𝒴A'').Finite := finE RA''.finY fun y hy => by
    obtain ⟨e, Q, -, -, -, -, hyax, -⟩ := c.yA_spec (RA''.arcY y hy)
    rw [hyax]; exact finite_singleton e
  obtain ⟨𝒴B'', hYB', RB''r, hcovB, hnewB⟩ :=
    (RB'.rule_refl h1).extendY_finite h1 h2 h3 h4 h5 h6 h7 h8 c.qB.refl hEAf hEA
  have RB'' := RB''r.rule_refl h1
  have mA : ∀ ya ∈ 𝒴A'', ∃ yb ∈ 𝒴B'', (ya ∩ yb).Nonempty := by
    intro ya hya
    obtain ⟨e, Q, he, -, -, -, hyax, -⟩ := c.yA_spec (RA''.arcY ya hya)
    have heya : e ∈ ya := (hyax.symm ▸ mem_singleton e : e ∈ ya ∩ x).1
    obtain ⟨yb, hyb, heyb⟩ := hcovB ⟨he.1, ya, hya, heya⟩
    exact ⟨yb, hyb, e, heya, heyb⟩
  have mB : ∀ yb ∈ 𝒴B'', ∃ ya ∈ 𝒴A'', (ya ∩ yb).Nonempty := by
    intro yb hyb
    rcases hnewB yb hyb with hold | ⟨z, hzyb, -, ya, hya, hzya⟩
    · obtain ⟨P, e, -, he, -, -, hybx, -⟩ := c.yB_spec (RB'.arcY yb hold)
      have heyb : e ∈ yb := (hybx.symm ▸ mem_singleton e : e ∈ yb ∩ x).1
      obtain ⟨ya, hya, heya⟩ := hcovA ⟨he.1, yb, hold, heyb⟩
      exact ⟨ya, hya, e, heya, heyb⟩
    · exact ⟨ya, hya, z, hzya, hzyb⟩
  refine ⟨insert x (𝒳A' ∪ 𝒳B'), glueY 𝒴A'' 𝒴B'', c.glue h1 h2 h3 h4 h51 h7 hxq RA'' RB'', ?_⟩
  rw [c.cells_split h1 h2 h3 h4 h51 h7 (G := ⋃₀ insert x (𝒳A' ∪ 𝒳B') ∪ ⋃₀ glueY 𝒴A'' 𝒴B'')
    (GA := ⋃₀ 𝒳A' ∪ ⋃₀ 𝒴A'') (GB := ⋃₀ 𝒳B' ∪ ⋃₀ 𝒴B'') (fun z hz => Or.inl ⟨x, mem_insert _ _, hz⟩)
    (fun z hz => c.glue_carrier_iffA h1 h2 h3 h4 h51 h7 RA'' RB'' mA hz)
    (fun z hz => c.glue_carrier_iffB h1 h2 h3 h4 h51 h7 RA'' RB'' mB hz)
    (RA''.isClosed_carrier h1) (RB''.isClosed_carrier h1)]
  rintro U (hU | hU)
  · exact Space.cellsOf_forall_mono hGood (union_subset_union_right _ (sUnion_mono hYA')) hPA U hU
  · exact Space.cellsOf_forall_mono hGood (union_subset_union_right _ (sUnion_mono hYB')) hPB U hU

end Ax

end HPC.Moore
