import HPC.Moore.M19CDGlue

/-!
# Moore 1919: adding an arc to a ruling (batch 141, item E)

Through every point `P` of the open side `BC` of `ABCDA` that is on no arc `Y` of a ruling
`(𝒳, 𝒴)`, there is an arc `y` from `BC` to `DA` such that `(𝒳, 𝒴 + y)` is again a ruling
(`Space.ArcRuling.extendY`); hence any finite set of points of the open side `BC` can be made ends of
arcs `Y` (`Space.ArcRuling.extendY_finset`). The proof is by induction on the number of arcs: cut
along an arc `x` of `𝒳` and extend in the two halves, gluing on `x`; if `𝒳` is empty, cut along an
arc of `𝒴` instead; if there are no arcs, Theorem 35 (accessibility, `exists_arc_through`) gives
the arc.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

namespace Space.ArcRuling

variable {I sAB sBC sCD sDA : Set S} {A B C D : S} {𝒳 𝒴 : Set (Set S)}

/-- A ruling remains a ruling when arcs are removed. -/
theorem mono (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) {𝒳' 𝒴' : Set (Set S)}
    (hX : 𝒳' ⊆ 𝒳) (hY : 𝒴' ⊆ 𝒴) : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳' 𝒴' where
  finX := R.finX.subset hX
  finY := R.finY.subset hY
  arcX x hx := R.arcX x (hX hx)
  arcY y hy := R.arcY y (hY hy)
  disjX := R.disjX.mono hX
  disjY := R.disjY.mono hY
  cross x hx y hy := R.cross x (hX hx) y (hY hy)

/-- The empty ruling. -/
theorem empty : σ.ArcRuling I sAB sBC sCD sDA A B C D ∅ ∅ where
  finX := finite_empty
  finY := finite_empty
  arcX _ h := absurd h (notMem_empty _)
  arcY _ h := absurd h (notMem_empty _)
  disjX := pairwise_empty _
  disjY := pairwise_empty _
  cross _ h := absurd h (notMem_empty _)

/-- With no arcs `X`, an arc `Y` missing the arcs of `𝒴` may be added. -/
theorem insert_of_disj (R : σ.ArcRuling I sAB sBC sCD sDA A B C D ∅ 𝒴) {y : Set S}
    (hy : σ.XArc I sBC sDA B C D A y) (hd : ∀ w ∈ 𝒴, w ≠ y → Disjoint y w) :
    σ.ArcRuling I sAB sBC sCD sDA A B C D ∅ (insert y 𝒴) where
  finX := finite_empty
  finY := R.finY.insert y
  arcX _ h := absurd h (notMem_empty _)
  arcY w hw := by
    rcases hw with rfl | hw
    · exact hy
    · exact R.arcY w hw
  disjX := pairwise_empty _
  disjY := pairwise_insert.mpr ⟨R.disjY, fun w hw hne => ⟨hd w hw hne.symm, (hd w hw hne.symm).symm⟩⟩
  cross _ h := absurd h (notMem_empty _)

end Space.ArcRuling

namespace Space.Quad.Cut

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}
  {q : σ.Quad J I A B C D sAB sBC sCD sDA} {x : Set S} (c : q.Cut x)

theorem x_sub_clA : x ⊆ c.clA := fun _ h => Or.inr (Or.inl (Or.inl (Or.inr h)))
theorem x_sub_clB : x ⊆ c.clB := fun _ h => Or.inr (Or.inr h)

/-- `ABCDA` and its interior lie on the closures of the two halves. -/
theorem sub_cl_union : I ∪ J ⊆ c.clA ∪ c.clB := by
  rintro z (hz | hz)
  · by_cases hzx : z ∈ x
    · exact Or.inl (c.x_sub_clA hzx)
    · have : z ∈ I \ x := ⟨hz, hzx⟩
      rw [c.split] at this
      rcases this with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
  · rw [← q.union] at hz
    rcases hz with ((h | h) | h) | h
    · rw [← c.hs] at h
      rcases h with h | h
      · exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr h))))
    · rw [← c.ht] at h
      rcases h with h | h
      · exact Or.inl (Or.inr (Or.inl (Or.inr h)))
      · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inr (Or.inr h))

/-- An arc `Y` of `ABCDA` is the union of its parts on the closures of the two halves. -/
theorem y_eq {y : Set S} (hy : σ.XArc I sBC sDA B C D A y) :
    y = (y ∩ c.clA) ∪ (y ∩ c.clB) := by
  have hsub := hy.sub_cl q.sBC_sub q.sDA_sub
  ext z
  constructor
  · intro hz
    rcases c.sub_cl_union (hsub hz) with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  · rintro (h | h)
    · exact h.1
    · exact h.1

end Space.Quad.Cut

/-- The statement of the extension lemma for all rulings with fewer than `n` arcs. -/
def ExtendsBelow (σ : Space S) (n : ℕ) : Prop :=
  ∀ {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S} {𝒳 𝒴 : Set (Set S)},
    σ.Quad J I A B C D sAB sBC sCD sDA → σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴 →
    𝒳.ncard + 𝒴.ncard < n → ∀ P ∈ sBC \ {B, C}, P ∉ ⋃₀ 𝒴 →
    ∃ y, P ∈ y ∧ σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 (insert y 𝒴)

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S} {𝒳 𝒴 : Set (Set S)}

include h1 h2 h3 h4 h5 h6 h7 h8 in
/-- With no arcs, the arc is given by accessibility (Theorem 35). -/
theorem extend_base (q : σ.Quad J I A B C D sAB sBC sCD sDA) {P : S} (hP : P ∈ sBC \ {B, C}) :
    ∃ y, P ∈ y ∧ σ.ArcRuling I sAB sBC sCD sDA A B C D ∅ {y} := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨Q, hQ⟩ := ((isArc_iff_tarc h1 h3 h4 h51).mp q.da).nonempty_diff
  have hPQ : P ≠ Q := fun e => disjoint_left.mp q.bc_da hP.1 (e ▸ hQ.1)
  obtain ⟨y, hy, hyI⟩ := exists_arc_through h1 h2 h3 h4 h5 h6 h7 h8 q.interior (Or.inl rfl)
    (q.sBC_sub hP.1) (q.sDA_sub hQ.1) hPQ
  refine ⟨y, hy.left_mem, ?_⟩
  have := Space.ArcRuling.empty.insert_of_disj (σ := σ) (I := I) (sAB := sAB) (sBC := sBC)
    (sCD := sCD) (sDA := sDA) (A := A) (B := B) (C := C) (D := D) (𝒴 := ∅)
    ⟨P, Q, hP, hQ, hy, hyI⟩ (fun w hw => absurd hw (notMem_empty _))
  simpa using this

include h1 h2 h3 h4 h5 h7 h8 in
/-- The inductive step when `𝒳` has an arc `x`: cut along `x`. -/
theorem extend_stepX {n : ℕ} (ih : ExtendsBelow σ n) (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) (hn : 𝒳.ncard + 𝒴.ncard = n) {x : Set S}
    (hx : x ∈ 𝒳) {P : S} (hP : P ∈ sBC \ {B, C}) (hPY : P ∉ ⋃₀ 𝒴) :
    ∃ y, P ∈ y ∧ σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 (insert y 𝒴) := by
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨c⟩ := q.exists_cut h1 h2 h3 h4 h5 h7 h8 (R.arcX x hx)
  have RA := c.restrictA h1 h2 h3 h4 h51 h7 R hx
  have RB := c.restrictB h1 h2 h3 h4 h51 h7 R hx
  have hY : ∀ K : Set S, ((· ∩ K) '' 𝒴).ncard ≤ 𝒴.ncard := fun K => ncard_image_le R.finY
  have hX : ∀ K : Set S, {w ∈ 𝒳 | w ≠ x ∧ w ⊆ K}.ncard < 𝒳.ncard := fun K =>
    ncard_lt_ncard ⟨fun w hw => hw.1, fun h => (h hx).2.1 rfl⟩ R.finX
  have hPB : P ∉ ⋃₀ ((· ∩ c.clB) '' 𝒴) := by
    rintro ⟨_, ⟨y, hy, rfl⟩, hPy, -⟩; exact hPY ⟨y, hy, hPy⟩
  obtain ⟨yb, hPyb, RB'⟩ := ih c.qB RB (by have := hX c.clB; have := hY c.clB; omega) P hP hPB
  obtain ⟨P₁, e, -, he, -, -, hybx, -⟩ := c.yB_spec (RB'.arcY yb (mem_insert _ _))
  have heyb : e ∈ yb := (hybx.symm ▸ mem_singleton e : e ∈ yb ∩ x).1
  have heA : e ∉ ⋃₀ ((· ∩ c.clA) '' 𝒴) := by
    rintro ⟨_, ⟨y, hy, rfl⟩, hey, -⟩
    have hyB : y ∩ c.clB ∈ insert yb ((· ∩ c.clB) '' 𝒴) := Or.inr ⟨y, hy, rfl⟩
    by_cases heq : yb = y ∩ c.clB
    · exact hPY ⟨y, hy, (heq ▸ hPyb : P ∈ y ∩ c.clB).1⟩
    · exact disjoint_left.mp (RB'.disjY (mem_insert _ _) hyB heq) heyb ⟨hey, c.x_sub_clB he.1⟩
  have he' : e ∈ x \ {c.X, c.X'} := by rw [pair_comm]; exact he
  obtain ⟨ya, heya, RA'⟩ := ih c.qA RA (by have := hX c.clA; have := hY c.clA; omega) e he' heA
  have cross_cl : ∀ y ∈ 𝒴, ((y ∩ c.clA) ∩ (y ∩ c.clB)).Nonempty := fun y hy => by
    obtain ⟨z, ⟨hzx, hzy⟩, -⟩ := R.cross x hx y hy
    exact ⟨z, ⟨hzy, c.x_sub_clA hzx⟩, ⟨hzy, c.x_sub_clB hzx⟩⟩
  have G := c.glue h1 h2 h3 h4 h51 h7 (R.arcX x hx) RA' RB'
  refine ⟨ya ∪ yb, Or.inr hPyb, G.mono ((c.X_eq h1 h2 h3 h4 h51 h7 R hx).le) ?_⟩
  rintro _ (rfl | hy)
  · exact ⟨ya, mem_insert _ _, yb, mem_insert _ _, ⟨e, heya, heyb⟩, rfl⟩
  · rename_i y
    exact ⟨y ∩ c.clA, Or.inr ⟨y, hy, rfl⟩, y ∩ c.clB, Or.inr ⟨y, hy, rfl⟩, cross_cl y hy,
      c.y_eq (R.arcY y hy)⟩

include h1 h2 h3 h4 h5 h7 h8 in
/-- The inductive step when `𝒳` is empty and `𝒴` has an arc `y₀`: cut along `y₀`. -/
theorem extend_stepY {n : ℕ} (ih : ExtendsBelow σ n) (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    (R : σ.ArcRuling I sAB sBC sCD sDA A B C D ∅ 𝒴) (hn : 𝒴.ncard = n) {y₀ : Set S}
    (hy₀ : y₀ ∈ 𝒴) {P : S} (hP : P ∈ sBC \ {B, C}) (hPY : P ∉ ⋃₀ 𝒴) :
    ∃ y, P ∈ y ∧ σ.ArcRuling I sAB sBC sCD sDA A B C D ∅ (insert y 𝒴) := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨c⟩ := q.rot.exists_cut h1 h2 h3 h4 h5 h7 h8 ((R.rot h1).arcX y₀ hy₀)
  have RA := c.restrictA h1 h2 h3 h4 h51 h7 (R.rot h1) hy₀
  have RB := c.restrictB h1 h2 h3 h4 h51 h7 (R.rot h1) hy₀
  rw [image_empty] at RA RB
  have hX : ∀ K : Set S, {w ∈ 𝒴 | w ≠ y₀ ∧ w ⊆ K}.ncard < 𝒴.ncard := fun K =>
    ncard_lt_ncard ⟨fun w hw => hw.1, fun h => (h hy₀).2.1 rfl⟩ R.finY
  have hPy₀ : P ∉ y₀ := fun h => hPY ⟨y₀, hy₀, h⟩
  have hPs : P ∈ c.s₁ ∪ c.s₂ := by rw [c.hs]; exact hP.1
  have hXeq := c.X_eq h1 h2 h3 h4 h51 h7 (R.rot h1) hy₀
  have icl := c.inter_cl h1 h2 h3 h4 h51 h7
  have hPn : ∀ K : Set S, P ∉ ⋃₀ {w ∈ 𝒴 | w ≠ y₀ ∧ w ⊆ K} := fun K ⟨w, hw, hPw⟩ =>
    hPY ⟨w, hw.1, hPw⟩
  rcases hPs with hPs | hPs
  · have hP' : P ∈ c.s₁ \ {B, c.X} := ⟨hPs, by
      rintro (h | h)
      · exact hP.2 (Or.inl h)
      · exact hPy₀ (h ▸ c.qA.bc.left_mem)⟩
    obtain ⟨y, hPy, R'⟩ := ih c.qA.rot.rot.rot (((RA.rot h1).rot h1).rot h1)
      (by rw [ncard_empty, zero_add, ← hn]; exact hX _) P hP' (hPn _)
    obtain ⟨hyd, hycl, hyI⟩ := c.wA_spec (R'.arcY y (mem_insert _ _))
    refine ⟨y, hPy, R.insert_of_disj hyI fun w hw hne => ?_⟩
    have hw' : w ∈ insert y₀ ({w ∈ 𝒴 | w ≠ y₀ ∧ w ⊆ c.clA} ∪ {w ∈ 𝒴 | w ≠ y₀ ∧ w ⊆ c.clB}) :=
      hXeq ▸ hw
    rcases hw' with rfl | hwA | hwB
    · exact hyd
    · exact R'.disjY (mem_insert _ _) (Or.inr hwA) hne.symm
    · exact disjoint_left.mpr fun z hzy hzw =>
        disjoint_left.mp hyd hzy (icl ⟨hycl hzy, hwB.2.2 hzw⟩)
  · have hP' : P ∈ c.s₂ \ {c.X, C} := ⟨hPs, by
      rintro (h | h)
      · exact hPy₀ (h ▸ c.qA.bc.left_mem)
      · exact hP.2 (Or.inr h)⟩
    obtain ⟨y, hPy, R'⟩ := ih c.qB.rot.rot.rot (((RB.rot h1).rot h1).rot h1)
      (by rw [ncard_empty, zero_add, ← hn]; exact hX _) P hP' (hPn _)
    obtain ⟨hyd, hycl, hyI⟩ := c.wB_spec (R'.arcY y (mem_insert _ _))
    refine ⟨y, hPy, R.insert_of_disj hyI fun w hw hne => ?_⟩
    have hw' : w ∈ insert y₀ ({w ∈ 𝒴 | w ≠ y₀ ∧ w ⊆ c.clA} ∪ {w ∈ 𝒴 | w ≠ y₀ ∧ w ⊆ c.clB}) :=
      hXeq ▸ hw
    rcases hw' with rfl | hwA | hwB
    · exact hyd
    · exact disjoint_left.mpr fun z hzy hzw =>
        disjoint_left.mp hyd hzy (icl ⟨hwA.2.2 hzw, hycl hzy⟩)
    · exact R'.disjY (mem_insert _ _) (Or.inr hwB) hne.symm

include h1 h2 h3 h4 h5 h6 h7 h8 in
theorem extendsBelow (n : ℕ) : ExtendsBelow σ n := by
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; omega
  | succ n ih =>
    intro J I A B C D sAB sBC sCD sDA 𝒳 𝒴 q R hn P hP hPY
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | hn
    · exact ih q R hn P hP hPY
    rcases 𝒳.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · rcases 𝒴.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
      · obtain ⟨y, hPy, hR⟩ := extend_base h1 h2 h3 h4 h5 h6 h7 h8 q hP
        exact ⟨y, hPy, by simpa using hR⟩
      · exact extend_stepY h1 h2 h3 h4 h5 h7 h8 ih q R (by simpa using hn) hy₀ hP hPY
    · exact extend_stepX h1 h2 h3 h4 h5 h7 h8 ih q R hn hx hP hPY

include h1 h2 h3 h4 h5 h6 h7 h8 in
/-- **Adding an arc to a ruling.** Through a point `P` of the open side `BC` on no arc of `𝒴`
there is an arc `y` such that `(𝒳, 𝒴 + y)` is a ruling. -/
theorem Space.ArcRuling.extendY (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) {P : S} (hP : P ∈ sBC \ {B, C})
    (hPY : P ∉ ⋃₀ 𝒴) : ∃ y, P ∈ y ∧ σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 (insert y 𝒴) :=
  extendsBelow h1 h2 h3 h4 h5 h6 h7 h8 _ q R (Nat.lt_succ_self _) P hP hPY

include h1 h2 h3 h4 h5 h6 h7 h8 in
/-- **Adding arcs through finitely many points.** Every finite set `E` of points of the open side
`BC` is covered by the arcs of a ruling `(𝒳, 𝒴′)` with `𝒴 ⊆ 𝒴′`, each new arc passing through a
point of `E`. -/
theorem Space.ArcRuling.extendY_finite (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) {E : Set S} (hE : E.Finite)
    (hEs : E ⊆ sBC \ {B, C}) :
    ∃ 𝒴', 𝒴 ⊆ 𝒴' ∧ σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴' ∧ E ⊆ ⋃₀ 𝒴' ∧
      ∀ y ∈ 𝒴', y ∈ 𝒴 ∨ (y ∩ E).Nonempty := by
  induction E, hE using Set.Finite.induction_on with
  | empty => exact ⟨𝒴, subset_rfl, R, empty_subset _, fun y hy => Or.inl hy⟩
  | @insert P E hPE hE ihE =>
    obtain ⟨𝒴', hsub, R', hcov, hnew⟩ := ihE ((subset_insert _ _).trans hEs)
    have hnew' : ∀ y ∈ 𝒴', y ∈ 𝒴 ∨ (y ∩ insert P E).Nonempty := fun y hy =>
      (hnew y hy).imp_right fun ⟨z, hz⟩ => ⟨z, hz.1, Or.inr hz.2⟩
    by_cases hP : P ∈ ⋃₀ 𝒴'
    · exact ⟨𝒴', hsub, R', insert_subset hP hcov, hnew'⟩
    · obtain ⟨y, hPy, R''⟩ := R'.extendY h1 h2 h3 h4 h5 h6 h7 h8 q (hEs (mem_insert _ _)) hP
      refine ⟨insert y 𝒴', hsub.trans (subset_insert _ _), R'',
        insert_subset ⟨y, mem_insert _ _, hPy⟩ (hcov.trans (sUnion_mono (subset_insert _ _))), ?_⟩
      rintro w (rfl | hw)
      · exact Or.inr ⟨P, hPy, mem_insert _ _⟩
      · exact hnew' w hw

end Ax

end HPC.Moore
