import HPC.Jones.Jones49FTheta
import HPC.Jones.Whyburn

/-!
# Batch 158, item E: Moore 1962, Theorem 28

"If `D` is a simple domain and each of the two mutually exclusive continua `H` and `K` is a subset of
`D` [read: of `D ∪ J`] and each of them intersects `J`, the boundary of `D`, then no pair of points of
`H` separates two points of `K` from each other on `J`."

The excerpt of Moore 1962 in the repository breaks off inside the proof (p. 171 is followed by
p. 172 of a different section), so Moore's route could not be followed. The route used:

1. `J = P ∪ Q`, arcs from `a` to `b` (`tscc_split`); if `c`, `f` lie in different components of
   `J − {a, b}`, one lies in `P − {a, b}` and the other in `Q − {a, b}`.
2. `D` is the bounded side `I` of `J` (Jordan curve theorem); `E = (Cl D)ᶜ` is the other side.
3. An arc `L` from `a` to `b` lying, except for its ends, in `E` (`exists_exterior_arc`): `J` is
   aposyndetic and cyclic, so every point of `J` is accessible from `E` (`accessible_of_cyclic`,
   batch 152); two accessing arcs from a point of `E` are joined (`TArc.join`).
4. `P ∪ L` is a simple closed curve; its side `S` containing `Q − {a, b}` contains `D`, and the other
   side `T` misses `Cl D`.
5. Points `x ∈ T` near `c` and `y ∈ E` near `f` are joined in the complement of `H ∪ L` (through `K`)
   and in the complement of `Cl D` (in `E`); `(H ∪ L) ∩ Cl D = H` is connected. By Janiszewski's
   theorem (`janiszewski_compact`, batch 146) `L ∪ Cl D` does not separate `x` from `y`; but the
   component of `x` in its complement lies in `T`, and `y ∈ S`.

Neither the Schoenflies theorem nor the batch-151 crossing results are used.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Moore.Gen HPC.Jones

section Moore28

/-- A simple closed curve splits at any two of its points into two arcs. -/
theorem tscc_split_at {J : Set Pt} (hJ : TSCC J) {a b : Pt} (ha : a ∈ J) (hb : b ∈ J)
    (hab : a ≠ b) : ∃ P Q : Set Pt, TArc a b P ∧ TArc a b Q ∧ P ∩ Q = {a, b} ∧ P ∪ Q = J := by
  obtain ⟨s, t, C₁, C₂, h₁, h₂, h12, rfl⟩ := hJ
  exact tscc_split h₁ h₂ h12 ha hb hab

theorem TSCC.isCompact' {J : Set Pt} (hJ : TSCC J) : IsCompact J := by
  obtain ⟨s, t, C₁, C₂, h₁, h₂, -, rfl⟩ := hJ
  exact h₁.isCompact.union h₂.isCompact

theorem TSCC.isConnected' {J : Set Pt} (hJ : TSCC J) : IsConnected J := by
  obtain ⟨s, t, C₁, C₂, h₁, h₂, -, rfl⟩ := hJ
  exact ⟨⟨s, Or.inl h₁.left_mem⟩,
    IsPreconnected.union s h₁.left_mem h₂.left_mem h₁.isPreconnected h₂.isPreconnected⟩

/-- A simple closed curve is aposyndetic. -/
theorem tscc_aposyndetic {J : Set Pt} (hJ : TSCC J) : IsAposyndetic J := by
  intro x y hxy
  have hxy' : (x : Pt) ≠ y := fun h => hxy (Subtype.ext h)
  obtain ⟨L₁, L₂, h₁, h₂, -, hU⟩ := tscc_split_at hJ x.2 y.2 hxy'
  obtain ⟨u, hu, hu'⟩ := h₁.nonempty_diff
  obtain ⟨v, hv, hv'⟩ := h₂.nonempty_diff
  have hux : u ≠ x := fun h => hu' (Or.inl h)
  have huy : u ≠ y := fun h => hu' (Or.inr h)
  have hvx : v ≠ x := fun h => hv' (Or.inl h)
  have hvy : v ≠ y := fun h => hv' (Or.inr h)
  obtain ⟨Γ₁, Γ₂, hΓ₁, hΓ₂, hΓU, hΓI⟩ := h₁.split hu hux huy
  obtain ⟨Δ₁, Δ₂, hΔ₁, hΔ₂, hΔU, hΔI⟩ := h₂.split hv hvx hvy
  have hsubJ : Γ₁ ∪ Δ₁ ⊆ J := by
    rw [← hU, ← hΓU, ← hΔU]
    exact union_subset_union subset_union_left subset_union_left
  have himg : Subtype.val '' (Subtype.val ⁻¹' (Γ₁ ∪ Δ₁) : Set J) = Γ₁ ∪ Δ₁ := by
    rw [Subtype.image_preimage_coe]; exact inter_eq_right.2 hsubJ
  have hmem2 : ∀ {z w : Pt} {Γ Γ' : Set Pt}, Γ ∩ Γ' = {w} → z ∈ Γ → z ∈ Γ' → z = w :=
    fun {z w Γ Γ'} h hz hz' => by
      have h3 : z ∈ Γ ∩ Γ' := ⟨hz, hz'⟩
      rw [h] at h3; exact h3
  refine ⟨Subtype.val ⁻¹' (Γ₁ ∪ Δ₁), Subtype.val ⁻¹' (Γ₂ ∪ Δ₂)ᶜ, ⟨?_, ?_⟩,
    (hΓ₂.isClosed.union hΔ₂.isClosed).isOpen_compl.preimage continuous_subtype_val, ?_, ?_, ?_⟩
  · rw [Subtype.isCompact_iff, himg]; exact hΓ₁.isCompact.union hΔ₁.isCompact
  · refine ⟨⟨x, Or.inl hΓ₁.left_mem⟩, Topology.IsInducing.subtypeVal.isPreconnected_image.1 ?_⟩
    rw [himg]
    exact IsPreconnected.union (x : Pt) hΓ₁.left_mem hΔ₁.left_mem
      hΓ₁.isPreconnected hΔ₁.isPreconnected
  · rintro (h | h)
    · exact hux (hmem2 hΓI hΓ₁.left_mem h).symm
    · exact hvx (hmem2 hΔI hΔ₁.left_mem h).symm
  · intro z hz
    have hzJ : (z : Pt) ∈ L₁ ∪ L₂ := hU ▸ z.2
    rw [← hΓU, ← hΔU] at hzJ
    simp only [mem_preimage, mem_compl_iff, mem_union, not_or] at hz
    simp only [mem_preimage, mem_union]
    rcases hzJ with (h | h) | (h | h)
    · exact Or.inl h
    · exact absurd h hz.1
    · exact Or.inr h
    · exact absurd h hz.2
  · rintro (h | h)
    · exact huy (hmem2 hΓI h hΓ₂.right_mem).symm
    · exact hvy (hmem2 hΔI h hΔ₂.right_mem).symm

/-- A simple closed curve has no cut point. -/
theorem tscc_cyclic {J : Set Pt} (hJ : TSCC J) (z : J) : IsConnected ({z}ᶜ : Set J) := by
  obtain ⟨w, hwJ, hwz⟩ : ∃ w ∈ J, w ≠ (z : Pt) := by
    obtain ⟨s, t, C₁, C₂, h₁, h₂, -, hJeq⟩ := hJ
    by_cases hs : s = z
    · exact ⟨t, hJeq ▸ Or.inl h₁.right_mem, fun h => h₁.ne (hs.trans h.symm)⟩
    · exact ⟨s, hJeq ▸ Or.inl h₁.left_mem, hs⟩
  obtain ⟨L₁, L₂, hL₁, hL₂, -, hU⟩ := tscc_split_at hJ z.2 hwJ hwz.symm
  have himg : Subtype.val '' ({z}ᶜ : Set J) = J \ {(z : Pt)} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨q.2, fun h => hq (Subtype.ext h)⟩
    · rintro ⟨hp, hpz⟩; exact ⟨⟨p, hp⟩, fun h => hpz (congrArg Subtype.val h), rfl⟩
  refine ⟨⟨⟨w, hwJ⟩, fun h => hwz (congrArg Subtype.val h)⟩,
    Topology.IsInducing.subtypeVal.isPreconnected_image.1 ?_⟩
  have hJz : (L₁ ∪ L₂) \ {(z : Pt)} = J \ {(z : Pt)} := congrArg (fun S => S \ {(z : Pt)}) hU
  rw [himg, ← hJz, union_diff_distrib]
  exact IsPreconnected.union w ⟨hL₁.right_mem, hwz⟩
    ⟨hL₂.right_mem, hwz⟩ hL₁.symm.isPreconnected_diff_right hL₂.symm.isPreconnected_diff_right

/-- **Every point of a simple closed curve is accessible from each side**; in particular two points
`a ≠ b` of `J` are the ends of an arc lying, except for its ends, in a given side `E`. -/
theorem exists_side_arc {J : Set Pt} (hJ : TSCC J) {E : Set Pt} (hEc : IsConnected E)
    (hEJ : Disjoint E J) (hfE : frontier E = J) {a b : Pt} (ha : a ∈ J) (hb : b ∈ J)
    (hab : a ≠ b) : ∃ L : Set Pt, TArc a b L ∧ L \ {a, b} ⊆ E := by
  have hJc := TSCC.isCompact' hJ
  have hJconn := TSCC.isConnected' hJ
  haveI : CompactSpace J := isCompact_iff_compactSpace.1 hJc
  haveI : ConnectedSpace J := isConnected_iff_connectedSpace.1 hJconn
  have hS : ∀ z : J, SemiLocConnAt z := semiLocConn_of_isAposyndetic (tscc_aposyndetic hJ)
  obtain ⟨w, hw⟩ := hEc.nonempty
  have hwJ : w ∉ J := disjoint_left.1 hEJ hw
  have hcc : connectedComponentIn Jᶜ w = E := side_eq_cc hEc.isPreconnected hfE hEJ hw
  obtain ⟨Ca, hCa, hCaE⟩ := accessible_of_cyclic hJc hJconn hS (tscc_cyclic hJ) hwJ
    (p := a) (by rw [hcc, hfE]; exact ha) (y := w) (by rw [hcc]; exact hw)
    (fun h => hwJ (h ▸ ha))
  obtain ⟨Cb, hCb, hCbE⟩ := accessible_of_cyclic hJc hJconn hS (tscc_cyclic hJ) hwJ
    (p := b) (by rw [hcc, hfE]; exact hb) (y := w) (by rw [hcc]; exact hw)
    (fun h => hwJ (h ▸ hb))
  obtain ⟨L, hLsub, hL⟩ := hCa.symm.join hCb.symm ⟨w, hCa.left_mem, hCb.left_mem⟩ hab
  refine ⟨L, hL, fun z hz => ?_⟩
  rcases hLsub hz.1 with h | h
  · rw [← hcc]; exact hCaE ⟨h, fun h' => hz.2 (Or.inl h')⟩
  · rw [← hcc]; exact hCbE ⟨h, fun h' => hz.2 (Or.inr h')⟩

/-- **The core of Theorem 28**: with `J = P ∪ Q` and an exterior arc `L` from `a` to `b`, disjoint
continua `H ∋ a, b` and `K ∋ c, f` in `Cl D` with `c ∈ P − {a, b}`, `f ∈ Q − {a, b}` are
impossible. -/
theorem moore28_core {J D H K P Q L E : Set Pt} {a b c f : Pt} (hP : TArc a b P)
    (hQ : TArc a b Q) (hPQ : P ∩ Q = {a, b}) (hJ : P ∪ Q = J) (hDc : IsPreconnected D)
    (hDJ : Disjoint D J) (hcl : closure D = D ∪ J) (hDcpt : IsCompact (closure D))
    (hE : (closure D)ᶜ = E) (hEc : IsPreconnected E) (hJE : J ⊆ closure E) (hL : TArc a b L)
    (hLE : L \ {a, b} ⊆ E) (hH : Fold.Q78.IsContinuum H) (hK : IsPreconnected K)
    (hHK : Disjoint H K) (hHD : H ⊆ closure D) (hKD : K ⊆ closure D) (ha : a ∈ H) (hb : b ∈ H)
    (hcK : c ∈ K) (hcP : c ∈ P \ {a, b}) (hfK : f ∈ K) (hfQ : f ∈ Q \ {a, b}) : False := by
  have hJD : J ⊆ closure D := hcl ▸ subset_union_right
  have hPD : P ⊆ closure D := fun z hz => hJD (hJ ▸ Or.inl hz)
  have hQD : Q ⊆ closure D := fun z hz => hJD (hJ ▸ Or.inr hz)
  have hEcl : ∀ z ∈ E, z ∉ closure D := fun z hz h => (hE ▸ hz) h
  -- `L` meets `Cl D` only in `a`, `b`
  have hLD : ∀ z ∈ L, z ∈ closure D → z = a ∨ z = b := fun z hzL hzD => by
    by_contra h
    push_neg at h
    exact hEcl z (hLE ⟨hzL, fun h' => h'.elim h.1 h.2⟩) hzD
  have hPL : P ∩ L = {a, b} := by
    apply subset_antisymm
    · rintro z ⟨hzP, hzL⟩; exact hLD z hzL (hPD hzP)
    · rintro z (rfl | rfl)
      · exact ⟨hP.left_mem, hL.left_mem⟩
      · exact ⟨hP.right_mem, hL.right_mem⟩
  have hJP : TSCC (P ∪ L) := ⟨a, b, P, L, hP, hL, hPL, rfl⟩
  -- `Q − {a, b}` misses `P ∪ L`
  have hQo : Disjoint (Q \ {a, b}) (P ∪ L) := by
    refine disjoint_left.2 fun z hz h => ?_
    rcases h with h | h
    · have : z ∈ P ∩ Q := ⟨h, hz.1⟩
      rw [hPQ] at this; exact hz.2 this
    · rcases hLD z h (hQD hz.1) with rfl | rfl
      · exact hz.2 (Or.inl rfl)
      · exact hz.2 (Or.inr rfl)
  obtain ⟨S, T, hSo, -, hTo, hTc, hST, hU, -, hfT, hQS⟩ :=
    jordan_side hJP hQ.isPreconnected_diff hQo
  have hTPL : Disjoint T (P ∪ L) := by
    refine disjoint_left.2 fun z hz h => ?_
    have : z ∈ S ∪ T := Or.inr hz
    rw [hU] at this; exact this h
  -- `D ⊆ S`
  have hDPL : Disjoint D (P ∪ L) := by
    refine disjoint_left.2 fun z hz h => ?_
    rcases h with h | h
    · exact disjoint_left.1 hDJ hz (hJ ▸ Or.inl h)
    · rcases hLD z h (subset_closure hz) with rfl | rfl
      · exact disjoint_left.1 hDJ hz (hJ ▸ Or.inl hP.left_mem)
      · exact disjoint_left.1 hDJ hz (hJ ▸ Or.inl hP.right_mem)
  have hDS : D ⊆ S := sub_side_of_closure hSo hTo hST hU hfT hQS hDc hDPL hQ.nonempty_diff
    (fun z hz => hQD hz.1)
  -- `T` misses `Cl D`
  have hTD : ∀ z ∈ T, z ∉ closure D := fun z hzT hzD => by
    rw [hcl] at hzD
    rcases hzD with h | h
    · exact disjoint_left.1 hST (hDS h) hzT
    · rw [← hJ] at h
      rcases h with h | h
      · exact disjoint_left.1 hTPL hzT (Or.inl h)
      · by_cases hab : z ∈ ({a, b} : Set Pt)
        · rcases hab with rfl | rfl
          · exact disjoint_left.1 hTPL hzT (Or.inl hP.left_mem)
          · exact disjoint_left.1 hTPL hzT (Or.inl hP.right_mem)
        · exact disjoint_left.1 hST (hQS ⟨h, hab⟩) hzT
  -- the closed set `A = H ∪ L`
  set A := H ∪ L with hA
  have hAc : IsCompact A := hH.1.union hL.isCompact
  have hcA : c ∉ A := by
    rintro (h | h)
    · exact disjoint_left.1 hHK h hcK
    · rcases hLD c h (hPD hcP.1) with rfl | rfl
      · exact hcP.2 (Or.inl rfl)
      · exact hcP.2 (Or.inr rfl)
  have hfA : f ∉ A := by
    rintro (h | h)
    · exact disjoint_left.1 hHK h hfK
    · rcases hLD f h (hQD hfQ.1) with rfl | rfl
      · exact hfQ.2 (Or.inl rfl)
      · exact hfQ.2 (Or.inr rfl)
  have hKA : K ⊆ Aᶜ := by
    rintro z hz (h | h)
    · exact disjoint_left.1 hHK h hz
    · rcases hLD z h (hKD hz) with rfl | rfl
      · exact disjoint_left.1 hHK ha hz
      · exact disjoint_left.1 hHK hb hz
  -- `x ∈ T` near `c`
  obtain ⟨r, hr, hrA⟩ := Metric.isOpen_iff.1 hAc.isClosed.isOpen_compl c hcA
  have hcT : c ∈ closure T := frontier_subset_closure (hfT ▸ Or.inl hcP.1)
  obtain ⟨x, hxT, hxc⟩ := Metric.mem_closure_iff.1 hcT r hr
  have hxball : x ∈ ball c r := by rw [mem_ball, dist_comm]; exact hxc
  -- `y ∈ E` near `f`, on the side `S`
  obtain ⟨r', hr', hr'A⟩ := Metric.isOpen_iff.1 (hSo.inter hAc.isClosed.isOpen_compl) f
    ⟨hQS hfQ, hfA⟩
  obtain ⟨y, hyE, hyf⟩ := Metric.mem_closure_iff.1 (hJE (show f ∈ J from hJ ▸ Or.inr hfQ.1)) r' hr'
  have hyball : y ∈ ball f r' := by rw [mem_ball, dist_comm]; exact hyf
  have hyS : y ∈ S := (hr'A hyball).1
  have hyA : y ∉ A := (hr'A hyball).2
  have hxA : x ∉ A := hrA hxball
  have hxE : x ∈ E := hE ▸ hTD x hxT
  -- Janiszewski
  have hAB : A ∩ closure D = H := by
    ext z
    constructor
    · rintro ⟨h | h, hzD⟩
      · exact h
      · rcases hLD z h hzD with rfl | rfl
        · exact ha
        · exact hb
    · intro h; exact ⟨Or.inl h, hHD h⟩
  have hnA : ¬ SeparatesPts A x y := by
    rintro ⟨-, -, hsep⟩
    apply hsep
    have hZ : IsPreconnected (ball c r ∪ K ∪ ball f r') :=
      (isPreconnected_ball.union c (mem_ball_self hr) hcK hK).union f (Or.inr hfK)
        (mem_ball_self hr') isPreconnected_ball
    refine hZ.subset_connectedComponentIn (Or.inl (Or.inl hxball)) ?_ (Or.inr hyball)
    rintro z ((h | h) | h)
    · exact hrA h
    · exact hKA h
    · exact (hr'A h).2
  have hnB : ¬ SeparatesPts (closure D) x y := by
    rintro ⟨-, -, hsep⟩
    apply hsep
    refine hEc.subset_connectedComponentIn hxE (fun z hz => ?_) hyE
    exact hEcl z hz
  have hJan := HPC.Moore.janiszewski_compact hAc hDcpt (Or.inl (hAB ▸ hH.2)) hnA hnB
  apply hJan
  refine ⟨fun h => h.elim hxA (hEcl x hxE), fun h => h.elim hyA (hEcl y hyE), fun hy => ?_⟩
  have hsub : (A ∪ closure D)ᶜ ⊆ (P ∪ L)ᶜ := by
    intro z hz h
    rcases h with h | h
    · exact hz (Or.inr (hPD h))
    · exact hz (Or.inl (Or.inr h))
  have hcc : connectedComponentIn (P ∪ L)ᶜ x = T := side_eq_cc hTc hfT hTPL hxT
  have := connectedComponentIn_mono x hsub hy
  rw [hcc] at this
  exact disjoint_left.1 hST hyS this

/-- **Moore 1962, Theorem 28** (p. 156). -/
theorem moore62_theorem28_aux {J D H K : Set Pt} (hJ : TSCC J) (hD : IsOpen D)
    (hDc : IsConnected D) (hDb : Bornology.IsBounded D) (hDJ : frontier D = J)
    (hH : Fold.Q78.IsContinuum H) (hK : Fold.Q78.IsContinuum K) (hHK : Disjoint H K)
    (hHD : H ⊆ D ∪ J) (hKD : K ⊆ D ∪ J) {a b c f : Pt} (ha : a ∈ H ∩ J) (hb : b ∈ H ∩ J)
    (hc : c ∈ K ∩ J) (hf : f ∈ K ∩ J) (hab : a ≠ b) :
    connectedComponentIn (J \ {a, b}) c = connectedComponentIn (J \ {a, b}) f := by
  obtain ⟨P, Q, hP, hQ, hPQ, hPQJ⟩ := tscc_split_at hJ ha.2 hb.2 hab
  obtain ⟨I, E, hIo, hIc, hEo, hEc, hIE, hIEU, -, hEb, hfI, hfE⟩ :=
    jordan_curve_theorem (tscc_homeomorph_circle hJ)
  have hcl : closure D = D ∪ J := by rw [closure_eq_self_union_frontier, hDJ]
  have hDJd : Disjoint D J := by
    rw [← hDJ, disjoint_iff_inter_eq_empty]; exact hD.inter_frontier_eq
  have hDne : D.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, frontier_empty] at hDJ
    exact (hDJ ▸ ha.2 : a ∈ (∅ : Set Pt))
  -- `D` is a side of `J`
  have hside : ∀ W : Set Pt, IsOpen W → IsPreconnected W → W ⊆ Jᶜ → D ⊆ W → W = D := by
    intro W hWo hWc hWJ hDW
    refine subset_antisymm ?_ hDW
    refine hWc.subset_left_of_subset_union hD isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)) (fun z hz => ?_)
      (by obtain ⟨z, hz⟩ := hDne; exact ⟨z, hDW hz, hz⟩)
    by_cases hzD : z ∈ closure D
    · rw [hcl] at hzD
      rcases hzD with h | h
      · exact Or.inl h
      · exact absurd h (hWJ hz)
    · exact Or.inr hzD
  have hDIE : D ⊆ I ∪ E := hIEU ▸ fun z hz hzJ => disjoint_left.1 hDJd hz hzJ
  have hIJ : I ⊆ Jᶜ := hIEU ▸ subset_union_left
  have hEJ : E ⊆ Jᶜ := hIEU ▸ subset_union_right
  have hDI : D = I := by
    rcases hDc.isPreconnected.subset_or_subset hIo hEo hIE hDIE with h | h
    · exact (hside I hIo hIc.isPreconnected hIJ h).symm
    · exact absurd (hside E hEo hEc.isPreconnected hEJ h ▸ hDb) hEb
  have hEeq : (closure D)ᶜ = E := by
    rw [hcl, hDI]
    ext z
    constructor
    · intro hz
      have : z ∈ I ∪ E := hIEU ▸ fun h => hz (Or.inr h)
      exact this.resolve_left fun h => hz (Or.inl h)
    · rintro hz (h | h)
      · exact disjoint_left.1 hIE h hz
      · exact hEJ hz h
  have hDcpt : IsCompact (closure D) := hDb.isCompact_closure
  have hEJd : Disjoint E J := disjoint_left.2 fun z hz h => hEJ hz h
  obtain ⟨L, hL, hLE⟩ := exists_side_arc hJ hEc hEJd hfE ha.2 hb.2 hab
  have hJE : J ⊆ closure E := hfE ▸ frontier_subset_closure
  have hHD' : H ⊆ closure D := hcl ▸ hHD
  have hKD' : K ⊆ closure D := hcl ▸ hKD
  have hcab : c ∉ ({a, b} : Set Pt) := by
    rintro (rfl | rfl)
    · exact disjoint_left.1 hHK ha.1 hc.1
    · exact disjoint_left.1 hHK hb.1 hc.1
  have hfab : f ∉ ({a, b} : Set Pt) := by
    rintro (rfl | rfl)
    · exact disjoint_left.1 hHK ha.1 hf.1
    · exact disjoint_left.1 hHK hb.1 hf.1
  have hcJ : c ∈ P ∪ Q := hPQJ ▸ hc.2
  have hfJ : f ∈ P ∪ Q := hPQJ ▸ hf.2
  have same : ∀ R : Set Pt, TArc a b R → R ⊆ J → c ∈ R → f ∈ R →
      connectedComponentIn (J \ {a, b}) c = connectedComponentIn (J \ {a, b}) f := by
    intro R hR hRJ hcR hfR
    apply connectedComponentIn_eq
    exact hR.isPreconnected_diff.subset_connectedComponentIn ⟨hcR, hcab⟩
      (diff_subset_diff_left hRJ) ⟨hfR, hfab⟩
  have hPJ : P ⊆ J := hPQJ ▸ subset_union_left
  have hQJ : Q ⊆ J := hPQJ ▸ subset_union_right
  rcases hcJ with hcP | hcQ <;> rcases hfJ with hfP | hfQ
  · exact same P hP hPJ hcP hfP
  · exact (moore28_core hP hQ hPQ hPQJ hDc.isPreconnected hDJd hcl hDcpt hEeq hEc.isPreconnected
      hJE hL hLE hH hK.2.isPreconnected hHK hHD' hKD' ha.1 hb.1 hc.1 ⟨hcP, hcab⟩ hf.1
      ⟨hfQ, hfab⟩).elim
  · exact (moore28_core hQ hP (by rw [inter_comm, hPQ]) (by rw [union_comm, hPQJ])
      hDc.isPreconnected hDJd hcl hDcpt hEeq hEc.isPreconnected hJE hL hLE hH hK.2.isPreconnected
      hHK hHD' hKD' ha.1 hb.1 hc.1 ⟨hcQ, hcab⟩ hf.1 ⟨hfP, hfab⟩).elim
  · exact same Q hQ hQJ hcQ hfQ

end Moore28

end HPC.Hagopian
