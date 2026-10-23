import HPC.Moore.M19CDRuling

/-!
# Moore 1919: the two halves of a cut ruling (batch 141, item E)

For a cut `c` of `ABCDA` along an arc `x` of a ruling `(𝒳, 𝒴)`: the closures of the two halves
meet only on `x` (`Cut.inter_cl`); the ruling restricts to rulings of both halves
(`Cut.restrictA`, `Cut.restrictB`), from which it is recovered (`Cut.X_eq`), and off `x` the arcs of
the restricted rulings are those of the given one (`Cut.carrier_iffA`, `Cut.carrier_iffB`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

namespace Space.Quad.Cut

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}
  {q : σ.Quad J I A B C D sAB sBC sCD sDA} {x : Set S} (c : q.Cut x)

/-- The closure of the half `AXX′DA`. -/
def clA : Set S := c.IA ∪ (c.s₁ ∪ x ∪ c.t₁ ∪ sDA)

/-- The closure of the half `XBCX′X`. -/
def clB : Set S := c.IB ∪ (c.s₂ ∪ sBC ∪ c.t₂ ∪ x)

theorem s₁_sub : c.s₁ ⊆ sAB := fun _ h => by
  have h' : _ ∈ c.s₁ ∪ c.s₂ := Or.inl h
  rwa [c.hs] at h'
theorem s₂_sub : c.s₂ ⊆ sAB := fun _ h => by
  have h' : _ ∈ c.s₁ ∪ c.s₂ := Or.inr h
  rwa [c.hs] at h'
theorem t₁_sub : c.t₁ ⊆ sCD := fun _ h => by
  have h' : _ ∈ c.t₁ ∪ c.t₂ := Or.inl h
  rwa [c.ht] at h'
theorem t₂_sub : c.t₂ ⊆ sCD := fun _ h => by
  have h' : _ ∈ c.t₁ ∪ c.t₂ := Or.inr h
  rwa [c.ht] at h'

theorem single {y p : S} {U V : Set S} (hU : y ∈ U) (hV : y ∈ V) (h : U ∩ V = {p}) : y = p := by
  have h' : y ∈ U ∩ V := ⟨hU, hV⟩
  rw [h] at h'; exact h'

theorem B_notMem_s₁ : B ∉ c.s₁ := fun h => c.qB.ab.1 (single h c.qB.ab.right_mem c.hsi).symm
theorem A_notMem_s₂ : A ∉ c.s₂ := fun h => c.qA.ab.1 (single c.qA.ab.left_mem h c.hsi)
theorem C_notMem_t₁ : C ∉ c.t₁ := fun h => c.qB.cd.1 (single h c.qB.cd.left_mem c.hti)
theorem D_notMem_t₂ : D ∉ c.t₂ := fun h => c.qA.cd.1 (single c.qA.cd.right_mem h c.hti).symm

theorem IA_sub : c.IA ⊆ I \ x := c.split ▸ subset_union_left
theorem IB_sub : c.IB ⊆ I \ x := c.split ▸ subset_union_right

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
  (h51 : Space.Axiom5₁ (S := S)) (h7 : σ.Axiom7)
include h1 h2 h3 h4 h51 h7

theorem IA_open : @IsOpen S σ.topology c.IA := (jordan h1 h2 h3 h4 h51 h7 c.qA.interior).1
theorem IB_open : @IsOpen S σ.topology c.IB := (jordan h1 h2 h3 h4 h51 h7 c.qB.interior).1

theorem closure_IA : @closure S σ.topology c.IA = c.clA :=
  (jordan h1 h2 h3 h4 h51 h7 c.qA.interior).2.2.2.2.2.2.2.2.1

theorem closure_IB : @closure S σ.topology c.IB = c.clB :=
  (jordan h1 h2 h3 h4 h51 h7 c.qB.interior).2.2.2.2.2.2.2.2.1

/-- The closures of the two halves meet only on `x`. -/
theorem inter_cl : c.clA ∩ c.clB ⊆ x := by
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 h51 h7
  have notI : ∀ {z : S}, z ∈ J → z ∉ I := fun hz hzI => disjoint_left.mp hIJ hzI hz
  rintro z ⟨hA, hB⟩
  rcases hA with hA | hA
  · exfalso
    obtain ⟨hzI, hzx⟩ := c.IA_sub hA
    rcases hB with hB | (((hB | hB) | hB) | hB)
    · exact disjoint_left.mp c.dis hA hB
    · exact notI (q.sAB_sub (c.s₂_sub hB)) hzI
    · exact notI (q.sBC_sub hB) hzI
    · exact notI (q.sCD_sub (c.t₂_sub hB)) hzI
    · exact hzx hB
  rcases hB with hB | hB
  · exfalso
    obtain ⟨hzI, hzx⟩ := c.IB_sub hB
    rcases hA with ((hA | hA) | hA) | hA
    · exact notI (q.sAB_sub (c.s₁_sub hA)) hzI
    · exact hzx hA
    · exact notI (q.sCD_sub (c.t₁_sub hA)) hzI
    · exact notI (q.sDA_sub hA) hzI
  rcases hB with ((hB | hB) | hB) | hB
  · rcases hA with ((hA | hA) | hA) | hA
    · exact single hA hB c.hsi ▸ c.qA.bc.left_mem
    · exact hA
    · exact absurd (c.t₁_sub hA) (disjoint_left.mp q.ab_cd (c.s₂_sub hB))
    · exact absurd (single hA (c.s₂_sub hB) q.da_ab ▸ hB) c.A_notMem_s₂
  · rcases hA with ((hA | hA) | hA) | hA
    · exact absurd (single (c.s₁_sub hA) hB q.ab_bc ▸ hA) c.B_notMem_s₁
    · exact hA
    · exact absurd (single hB (c.t₁_sub hA) q.bc_cd ▸ hA) c.C_notMem_t₁
    · exact absurd hA (disjoint_left.mp q.bc_da hB)
  · rcases hA with ((hA | hA) | hA) | hA
    · exact absurd (c.t₂_sub hB) (disjoint_left.mp q.ab_cd (c.s₁_sub hA))
    · exact hA
    · exact single hA hB c.hti ▸ c.qA.bc.right_mem
    · exact absurd (single (c.t₂_sub hB) hA q.cd_da ▸ hB) c.D_notMem_t₂
  · exact hB

theorem closure_IB_disjoint_DA : Disjoint (@closure S σ.topology c.IB) sDA := by
  rw [c.closure_IB h1 h2 h3 h4 h51 h7, disjoint_left]
  intro z hzB hzDA
  have := c.inter_cl h1 h2 h3 h4 h51 h7 ⟨Or.inr (Or.inr hzDA), hzB⟩
  exact disjoint_left.mp c.qA.bc_da this hzDA

theorem closure_IA_disjoint_BC : Disjoint (@closure S σ.topology c.IA) sBC := by
  rw [c.closure_IA h1 h2 h3 h4 h51 h7, disjoint_left]
  intro z hzA hzBC
  have := c.inter_cl h1 h2 h3 h4 h51 h7 ⟨hzA, Or.inr (Or.inl (Or.inl (Or.inr hzBC)))⟩
  exact disjoint_left.mp c.qB.bc_da hzBC this

variable {𝒳 𝒴 : Set (Set S)}

/-- The ruling restricted to the half `AXX′DA`. -/
theorem restrictA (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) (hx : x ∈ 𝒳) :
    σ.ArcRuling c.IA c.s₁ x c.t₁ sDA A c.X c.X' D {w ∈ 𝒳 | w ≠ x ∧ w ⊆ c.clA}
      ((· ∩ c.clA) '' 𝒴) :=
  R.restrict_half h1 h2 h3 h4 h51 h7 q hx c.qA c.s₁_sub c.t₁_sub c.split
    (c.IB_open h1 h2 h3 h4 h51 h7) c.dis (c.closure_IB_disjoint_DA h1 h2 h3 h4 h51 h7)

/-- The ruling restricted to the half `XBCX′X`. -/
theorem restrictB (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) (hx : x ∈ 𝒳) :
    σ.ArcRuling c.IB c.s₂ sBC c.t₂ x c.X B C c.X' {w ∈ 𝒳 | w ≠ x ∧ w ⊆ c.clB}
      ((· ∩ c.clB) '' 𝒴) :=
  ((R.rule_refl h1).restrict_half h1 h2 h3 h4 h51 h7 q.refl hx c.qB.refl c.s₂_sub c.t₂_sub
    (by rw [c.split, union_comm]) (c.IA_open h1 h2 h3 h4 h51 h7) c.dis.symm
    (c.closure_IA_disjoint_BC h1 h2 h3 h4 h51 h7)).rule_refl h1

theorem sideA (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) (hx : x ∈ 𝒳) {w : Set S}
    (hw : w ∈ 𝒳) (hwx : w ≠ x) : w ⊆ c.clA ∨ w ∩ c.IA = ∅ :=
  R.side_of_cut h1 h2 h3 h4 h51 h7 q hx c.qA c.split (c.IB_open h1 h2 h3 h4 h51 h7) c.dis hw hwx

theorem sideB (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) (hx : x ∈ 𝒳) {w : Set S}
    (hw : w ∈ 𝒳) (hwx : w ≠ x) : w ⊆ c.clB ∨ w ∩ c.IB = ∅ :=
  (R.rule_refl h1).side_of_cut h1 h2 h3 h4 h51 h7 q.refl hx c.qB.refl
    (by rw [c.split, union_comm]) (c.IA_open h1 h2 h3 h4 h51 h7) c.dis.symm hw hwx

/-- The arcs `X` of the ruling are `x` and those of the two halves. -/
theorem X_eq (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) (hx : x ∈ 𝒳) :
    𝒳 = insert x ({w ∈ 𝒳 | w ≠ x ∧ w ⊆ c.clA} ∪ {w ∈ 𝒳 | w ≠ x ∧ w ⊆ c.clB}) := by
  letI := σ.topology
  apply subset_antisymm
  · intro w hw
    by_cases hwx : w = x
    · exact Or.inl hwx
    right
    rcases c.sideA h1 h2 h3 h4 h51 h7 R hx hw hwx with hA | hA
    · exact Or.inl ⟨hw, hwx, hA⟩
    rcases c.sideB h1 h2 h3 h4 h51 h7 R hx hw hwx with hB | hB
    · exact Or.inr ⟨hw, hwx, hB⟩
    exfalso
    obtain ⟨P, P', -, -, hwa, hwI⟩ := R.arcX w hw
    obtain ⟨z, hz⟩ := hwa.nonempty_diff
    have hzx : z ∉ x := fun h => disjoint_left.mp (R.disjX hw hx hwx) hz.1 h
    have : z ∈ I \ x := ⟨hwI hz, hzx⟩
    rw [c.split] at this
    rcases this with h | h
    · exact (eq_empty_iff_forall_notMem.mp hA) z ⟨hz.1, h⟩
    · exact (eq_empty_iff_forall_notMem.mp hB) z ⟨hz.1, h⟩
  · rintro w (rfl | (⟨hw, -⟩ | ⟨hw, -⟩))
    · exact hx
    · exact hw
    · exact hw

/-- Within `IA`, a point is on an arc of the ruling if and only if it is on an arc of the
restricted ruling. -/
theorem carrier_iffA (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) (hx : x ∈ 𝒳) {z : S}
    (hz : z ∈ c.IA) :
    z ∈ ⋃₀ 𝒳 ∪ ⋃₀ 𝒴 ↔ z ∈ ⋃₀ {w ∈ 𝒳 | w ≠ x ∧ w ⊆ c.clA} ∪ ⋃₀ ((· ∩ c.clA) '' 𝒴) := by
  have hzx := (c.IA_sub hz).2
  constructor
  · rintro (⟨w, hw, hzw⟩ | ⟨y, hy, hzy⟩)
    · have hwx : w ≠ x := fun e => hzx (e ▸ hzw)
      rcases c.sideA h1 h2 h3 h4 h51 h7 R hx hw hwx with hA | hA
      · exact Or.inl ⟨w, ⟨hw, hwx, hA⟩, hzw⟩
      · exact absurd ⟨hzw, hz⟩ (eq_empty_iff_forall_notMem.mp hA z)
    · exact Or.inr ⟨_, ⟨y, hy, rfl⟩, hzy, Or.inl hz⟩
  · rintro (⟨w, ⟨hw, -⟩, hzw⟩ | ⟨_, ⟨y, hy, rfl⟩, hzy, -⟩)
    · exact Or.inl ⟨w, hw, hzw⟩
    · exact Or.inr ⟨y, hy, hzy⟩

theorem carrier_iffB (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) (hx : x ∈ 𝒳) {z : S}
    (hz : z ∈ c.IB) :
    z ∈ ⋃₀ 𝒳 ∪ ⋃₀ 𝒴 ↔ z ∈ ⋃₀ {w ∈ 𝒳 | w ≠ x ∧ w ⊆ c.clB} ∪ ⋃₀ ((· ∩ c.clB) '' 𝒴) := by
  have hzx := (c.IB_sub hz).2
  constructor
  · rintro (⟨w, hw, hzw⟩ | ⟨y, hy, hzy⟩)
    · have hwx : w ≠ x := fun e => hzx (e ▸ hzw)
      rcases c.sideB h1 h2 h3 h4 h51 h7 R hx hw hwx with hB | hB
      · exact Or.inl ⟨w, ⟨hw, hwx, hB⟩, hzw⟩
      · exact absurd ⟨hzw, hz⟩ (eq_empty_iff_forall_notMem.mp hB z)
    · exact Or.inr ⟨_, ⟨y, hy, rfl⟩, hzy, Or.inl hz⟩
  · rintro (⟨w, ⟨hw, -⟩, hzw⟩ | ⟨_, ⟨y, hy, rfl⟩, hzy, -⟩)
    · exact Or.inl ⟨w, hw, hzw⟩
    · exact Or.inr ⟨y, hy, hzy⟩

end Ax

/-- `I − G` from the two halves, when `G ⊇ x` agrees with `GA` on `IA` and with `GB` on `IB`. -/
theorem diff_eq {G GA GB : Set S} (hxG : x ⊆ G) (hA : ∀ z ∈ c.IA, z ∈ G ↔ z ∈ GA)
    (hB : ∀ z ∈ c.IB, z ∈ G ↔ z ∈ GB) : I \ G = (c.IA \ GA) ∪ (c.IB \ GB) := by
  ext z
  constructor
  · rintro ⟨hzI, hzG⟩
    have : z ∈ I \ x := ⟨hzI, fun h => hzG (hxG h)⟩
    rw [c.split] at this
    rcases this with h | h
    · exact Or.inl ⟨h, fun h' => hzG ((hA z h).mpr h')⟩
    · exact Or.inr ⟨h, fun h' => hzG ((hB z h).mpr h')⟩
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · exact ⟨(c.IA_sub h).1, fun hG => h' ((hA z h).mp hG)⟩
    · exact ⟨(c.IB_sub h).1, fun hG => h' ((hB z h).mp hG)⟩

end Space.Quad.Cut

end HPC.Moore
