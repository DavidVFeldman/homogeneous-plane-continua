import HPC.Moore.M19CDExt

/-!
# Moore 1919: refinement of a double ruling (batch 141, item E)

Moore uses twice, without proof, that rulings of the subdivisions of a double ruling `τ₁` can be
extended to a double ruling `τ₂` of the whole quadrilateral "such that each arc of `τ₁` is also an
arc of `τ₂`" (p. 175, in the proof of Theorem D; p. 176, in the proof of Theorem E).

`Space.ArcRuling.refine` proves it in the following form. Let `Good` be a property of sets inherited
by subsets (in Moore's two uses: *lies within some curve (region) of a given set*, or *lies wholly
without `g₁, …, gₖ` or within some curve of `G`*). If every subdivision of the ruling `(𝒳, 𝒴)`,
taken as the interior of a quadrilateral in any way, has a ruling all of whose subdivisions have
property `Good`, then there is a ruling `(𝒳′, 𝒴′)` of `ABCDA` with `𝒳 ⊆ 𝒳′`, `𝒴 ⊆ 𝒴′` (each arc of the
given ruling is an arc of the new one), all of whose subdivisions have property `Good` and lie in
subdivisions of the given ruling.

Proof: induction on the number of arcs. Cut along an arc `x` of `𝒳` (or, if `𝒳` is empty, of `𝒴`,
after rotating); refine the two halves; make the arcs `Y` of the two halves end at the same points of
`x` by the extension lemma (`Space.ArcRuling.extendY_finite`); glue (`Space.Quad.Cut.glue`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-- The quadrilateral `ABCDA` (interior `I`) has a ruling all of whose subdivisions have property
`Good`. -/
def Space.Rulable (σ : Space S) (Good : Set S → Prop) (I sAB sBC sCD sDA : Set S) (A B C D : S) :
    Prop :=
  ∃ 𝒳 𝒴 : Set (Set S), σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴 ∧
    ∀ U ∈ σ.cellsOf I (⋃₀ 𝒳 ∪ ⋃₀ 𝒴), Good U

/-- Every subdivision of `I` by `G`, taken as the interior of a quadrilateral in any way, has a
ruling all of whose subdivisions have property `Good`. -/
def Space.CellsRulable (σ : Space S) (Good : Set S → Prop) (I G : Set S) : Prop :=
  ∀ {J' I' : Set S} {A' B' C' D' : S} {s₁ s₂ s₃ s₄ : Set S},
    σ.Quad J' I' A' B' C' D' s₁ s₂ s₃ s₄ → I' ∈ σ.cellsOf I G → σ.Rulable Good I' s₁ s₂ s₃ s₄ A' B' C' D'

theorem Space.ArcRuling.isClosed_carrier (h1 : σ.Axiom1) {I sAB sBC sCD sDA : Set S} {A B C D : S}
    {𝒳 𝒴 : Set (Set S)} (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) :
    @IsClosed S σ.topology (⋃₀ 𝒳 ∪ ⋃₀ 𝒴) := by
  letI := σ.topology
  haveI := t2Space h1
  have hc : ∀ {I' a b : Set S} {A' B' C' D' : S} {w : Set S},
      σ.XArc I' a b A' B' C' D' w → IsClosed w := fun ⟨_, _, _, _, hw, _⟩ => hw.isClosed
  rw [sUnion_eq_biUnion, sUnion_eq_biUnion]
  exact (R.finX.isClosed_biUnion fun w hw => hc (R.arcX w hw)).union
    (R.finY.isClosed_biUnion fun w hw => hc (R.arcY w hw))

theorem Space.cellsOf_forall_mono {Good : Set S → Prop} (hGood : ∀ U V, U ⊆ V → Good V → Good U)
    {U G G' : Set S} (hG : G ⊆ G') (h : ∀ V ∈ σ.cellsOf U G, Good V) :
    ∀ V ∈ σ.cellsOf U G', Good V := fun V hV => by
  obtain ⟨W, hW, hVW⟩ := Space.cellsOf_mono hG hV
  exact hGood _ _ hVW (h W hW)

namespace Space.Quad.Cut

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}
  {q : σ.Quad J I A B C D sAB sBC sCD sDA} {x : Set S} (c : q.Cut x)

/-- The subdivisions of `I` by a closed set `G ⊇ x` are those of the two halves. -/
theorem cells_split (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S)) (h7 : σ.Axiom7) {G GA GB : Set S} (hxG : x ⊆ G)
    (hA : ∀ z ∈ c.IA, z ∈ G ↔ z ∈ GA) (hB : ∀ z ∈ c.IB, z ∈ G ↔ z ∈ GB)
    (hGA : @IsClosed S σ.topology GA) (hGB : @IsClosed S σ.topology GB) :
    σ.cellsOf I G = σ.cellsOf c.IA GA ∪ σ.cellsOf c.IB GB :=
  letI := σ.topology
  Space.cellsOf_union (c.diff_eq hxG hA hB) ((c.IA_open h1 h2 h3 h4 h51 h7).sdiff hGA)
    ((c.IB_open h1 h2 h3 h4 h51 h7).sdiff hGB) (c.dis.mono diff_subset diff_subset)

end Space.Quad.Cut

/-- The refinement statement for all rulings with fewer than `n` arcs. -/
def RefinesBelow (σ : Space S) (Good : Set S → Prop) (n : ℕ) : Prop :=
  ∀ {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S} {𝒳 𝒴 : Set (Set S)},
    σ.Quad J I A B C D sAB sBC sCD sDA → σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴 →
    𝒳.ncard + 𝒴.ncard < n → σ.CellsRulable Good I (⋃₀ 𝒳 ∪ ⋃₀ 𝒴) →
    ∃ 𝒳' 𝒴', 𝒳 ⊆ 𝒳' ∧ 𝒴 ⊆ 𝒴' ∧ σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳' 𝒴' ∧
      ∀ U ∈ σ.cellsOf I (⋃₀ 𝒳' ∪ ⋃₀ 𝒴'), Good U

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S} {𝒳 𝒴 : Set (Set S)}
  {Good : Set S → Prop}

/-- The inductive step when `𝒳` has an arc `x`: cut along `x`. -/
theorem refine_stepX (hGood : ∀ U V, U ⊆ V → Good V → Good U) {n : ℕ} (ih : RefinesBelow σ Good n)
    (q : σ.Quad J I A B C D sAB sBC sCD sDA) (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴)
    (hn : 𝒳.ncard + 𝒴.ncard = n) {x : Set S} (hx : x ∈ 𝒳)
    (H : σ.CellsRulable Good I (⋃₀ 𝒳 ∪ ⋃₀ 𝒴)) :
    ∃ 𝒳' 𝒴', 𝒳 ⊆ 𝒳' ∧ 𝒴 ⊆ 𝒴' ∧ σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳' 𝒴' ∧
      ∀ U ∈ σ.cellsOf I (⋃₀ 𝒳' ∪ ⋃₀ 𝒴'), Good U := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  have hxq := R.arcX x hx
  obtain ⟨c⟩ := q.exists_cut h1 h2 h3 h4 h5 h7 h8 hxq
  have RA := c.restrictA h1 h2 h3 h4 h51 h7 R hx
  have RB := c.restrictB h1 h2 h3 h4 h51 h7 R hx
  have hY : ∀ K : Set S, ((· ∩ K) '' 𝒴).ncard ≤ 𝒴.ncard := fun K => ncard_image_le R.finY
  have hX : ∀ K : Set S, {w ∈ 𝒳 | w ≠ x ∧ w ⊆ K}.ncard < 𝒳.ncard := fun K =>
    ncard_lt_ncard ⟨fun w hw => hw.1, fun h => (h hx).2.1 rfl⟩ R.finX
  have hsplit := c.cells_split h1 h2 h3 h4 h51 h7 (fun z hz => Or.inl ⟨x, hx, hz⟩)
    (fun z hz => c.carrier_iffA h1 h2 h3 h4 h51 h7 R hx hz)
    (fun z hz => c.carrier_iffB h1 h2 h3 h4 h51 h7 R hx hz)
    (RA.isClosed_carrier h1) (RB.isClosed_carrier h1)
  obtain ⟨𝒳A', 𝒴A', hXA, hYA, RA', hPA⟩ := ih c.qA RA
    (by have := hX c.clA; have := hY c.clA; omega) fun q' hI' => H q' (hsplit ▸ Or.inl hI')
  obtain ⟨𝒳B', 𝒴B', hXB, hYB, RB', hPB⟩ := ih c.qB RB
    (by have := hX c.clB; have := hY c.clB; omega) fun q' hI' => H q' (hsplit ▸ Or.inr hI')
  have finE : ∀ {𝒵 : Set (Set S)}, 𝒵.Finite → (∀ y ∈ 𝒵, (y ∩ x).Finite) →
      (x ∩ ⋃₀ 𝒵).Finite := fun hf h =>
    ((hf.image (· ∩ x)).sUnion (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)).subset
      (by rintro z ⟨hzx, y, hy, hzy⟩; exact ⟨_, ⟨y, hy, rfl⟩, hzy, hzx⟩)
  -- make the arcs of the half `A` end at the ends on `x` of those of the half `B`
  have hEB : x ∩ ⋃₀ 𝒴B' ⊆ x \ {c.X, c.X'} := by
    rintro z ⟨hzx, yb, hyb, hzyb⟩
    obtain ⟨P, e, -, he, -, -, hybx, -⟩ := c.yB_spec (RB'.arcY yb hyb)
    rw [Space.Quad.Cut.single hzyb hzx hybx, pair_comm]; exact he
  have hEBf : (x ∩ ⋃₀ 𝒴B').Finite := finE RB'.finY fun y hy => by
    obtain ⟨P, e, -, -, -, -, hybx, -⟩ := c.yB_spec (RB'.arcY y hy)
    rw [hybx]; exact finite_singleton e
  obtain ⟨𝒴A'', hYA', RA'', hcovA, -⟩ :=
    RA'.extendY_finite h1 h2 h3 h4 h5 h6 h7 h8 c.qA hEBf hEB
  -- and those of the half `B` at the ends on `x` of those of the half `A`
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
  have cross_cl : ∀ y ∈ 𝒴, ((y ∩ c.clA) ∩ (y ∩ c.clB)).Nonempty := fun y hy => by
    obtain ⟨z, ⟨hzx, hzy⟩, -⟩ := R.cross x hx y hy
    exact ⟨z, ⟨hzy, c.x_sub_clA hzx⟩, ⟨hzy, c.x_sub_clB hzx⟩⟩
  refine ⟨insert x (𝒳A' ∪ 𝒳B'), glueY 𝒴A'' 𝒴B'', ?_, ?_,
    c.glue h1 h2 h3 h4 h51 h7 hxq RA'' RB'', ?_⟩
  · intro w hw
    rcases (c.X_eq h1 h2 h3 h4 h51 h7 R hx).le hw with rfl | h | h
    · exact mem_insert _ _
    · exact Or.inr (Or.inl (hXA h))
    · exact Or.inr (Or.inr (hXB h))
  · intro y hy
    exact ⟨y ∩ c.clA, hYA' (hYA ⟨y, hy, rfl⟩), y ∩ c.clB, hYB' (hYB ⟨y, hy, rfl⟩), cross_cl y hy,
      c.y_eq (R.arcY y hy)⟩
  · rw [c.cells_split h1 h2 h3 h4 h51 h7 (G := ⋃₀ insert x (𝒳A' ∪ 𝒳B') ∪ ⋃₀ glueY 𝒴A'' 𝒴B'')
      (GA := ⋃₀ 𝒳A' ∪ ⋃₀ 𝒴A'') (GB := ⋃₀ 𝒳B' ∪ ⋃₀ 𝒴B'') (fun z hz => Or.inl ⟨x, mem_insert _ _, hz⟩)
      (fun z hz => c.glue_carrier_iffA h1 h2 h3 h4 h51 h7 RA'' RB'' mA hz)
      (fun z hz => c.glue_carrier_iffB h1 h2 h3 h4 h51 h7 RA'' RB'' mB hz)
      (RA''.isClosed_carrier h1) (RB''.isClosed_carrier h1)]
    rintro U (hU | hU)
    · exact Space.cellsOf_forall_mono hGood (union_subset_union_right _ (sUnion_mono hYA')) hPA U hU
    · exact Space.cellsOf_forall_mono hGood (union_subset_union_right _ (sUnion_mono hYB')) hPB U hU

theorem refinesBelow (hGood : ∀ U V, U ⊆ V → Good V → Good U) (n : ℕ) : RefinesBelow σ Good n := by
  letI := σ.topology
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; omega
  | succ n ih =>
    intro J I A B C D sAB sBC sCD sDA 𝒳 𝒴 q R hn H
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | hn
    · exact ih q R hn H
    rcases 𝒳.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · rcases 𝒴.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
      · have h51 := axiom5₁_of_axiom5 h5
        obtain ⟨-, hIc, ⟨z, hz⟩, -⟩ := jordan h1 h2 h3 h4 h51 h7 q.interior
        have hcell : I ∈ σ.cellsOf I (⋃₀ ∅ ∪ ⋃₀ ∅) := by
          refine ⟨z, by simpa using hz, ?_⟩
          simp only [sUnion_empty, union_empty, diff_empty]
          exact (hIc.connectedComponentIn hz).symm
        obtain ⟨𝒳', 𝒴', R', hP⟩ := H q hcell
        exact ⟨𝒳', 𝒴', empty_subset _, empty_subset _, R', hP⟩
      · have H' : σ.CellsRulable Good I (⋃₀ 𝒴 ∪ ⋃₀ ∅) := by rw [union_comm]; exact H
        obtain ⟨𝒳', 𝒴', hX', -, R', hP⟩ := refine_stepX h1 h2 h3 h4 h5 h6 h7 h8 hGood ih q.rot
          (R.rot h1) (by rw [ncard_empty] at hn ⊢; omega) hy₀ H'
        refine ⟨𝒴', 𝒳', empty_subset _, hX', ((R'.rot h1).rot h1).rot h1, ?_⟩
        rw [union_comm]; exact hP
    · exact refine_stepX h1 h2 h3 h4 h5 h6 h7 h8 hGood ih q R hn hx H

/-- **Refinement of a double ruling** (item E; used without proof on pp. 175 and 176). Let `Good` be a
property inherited by subsets. If every subdivision of the ruling `(𝒳, 𝒴)` of `ABCDA`, taken as the
interior of a quadrilateral in any way, has a ruling all of whose subdivisions have property `Good`,
then `ABCDA` has a ruling `(𝒳′, 𝒴′)` containing every arc of `(𝒳, 𝒴)`, each subdivision of which has
property `Good` and lies in a subdivision of `(𝒳, 𝒴)`. -/
theorem Space.ArcRuling.refine (hGood : ∀ U V, U ⊆ V → Good V → Good U)
    (q : σ.Quad J I A B C D sAB sBC sCD sDA) (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴)
    (H : σ.CellsRulable Good I (⋃₀ 𝒳 ∪ ⋃₀ 𝒴)) :
    ∃ 𝒳' 𝒴', 𝒳 ⊆ 𝒳' ∧ 𝒴 ⊆ 𝒴' ∧ σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳' 𝒴' ∧
      ∀ U ∈ σ.cellsOf I (⋃₀ 𝒳' ∪ ⋃₀ 𝒴'),
        Good U ∧ ∃ V ∈ σ.cellsOf I (⋃₀ 𝒳 ∪ ⋃₀ 𝒴), U ⊆ V := by
  obtain ⟨𝒳', 𝒴', hX, hY, R', hP⟩ :=
    refinesBelow h1 h2 h3 h4 h5 h6 h7 h8 hGood _ q R (Nat.lt_succ_self _) H
  exact ⟨𝒳', 𝒴', hX, hY, R', fun U hU =>
    ⟨hP U hU, Space.cellsOf_mono (union_subset_union (sUnion_mono hX) (sUnion_mono hY)) hU⟩⟩

end Ax

end HPC.Moore
