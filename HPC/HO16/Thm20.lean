import HPC.HO16.P19Defs

/-!
# Batch 196, §5: Theorem 20 from Theorem 15 (and Proposition 19)

H–O pp. 209–210. The induction of Theorem 20 (`ho16_lift_aux`, with Proposition 19 as the
hypothesis `HOProp19`), the reduction to connected graphs, and the assembly
`ho16_theorem20_of_thm15_prop19`. `HOProp19` is proved (`hoProp19_holds`, `Prop19Conn.lean`); the
skeleton's statements, without it, are in `HO16D.lean`.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

/-- A subspace of a hereditarily indecomposable space is hereditarily indecomposable. -/
theorem isHereditarilyIndecomposable_univ_subtype {X : Type*} [MetricSpace X]
    (hHI : IsHereditarilyIndecomposable (univ : Set X)) (s : Set X) :
    IsHereditarilyIndecomposable (univ : Set s) := by
  intro K _ hK
  have hcont : ∀ A : Set s, Fold.Q78.IsContinuum A →
      Fold.Q78.IsContinuum ((Subtype.val : s → X) '' A) := fun A hA =>
    ⟨hA.1.image continuous_subtype_val, hA.2.image _ continuous_subtype_val.continuousOn⟩
  obtain ⟨-, hind⟩ := hHI _ (subset_univ _) (hcont K hK)
  refine ⟨hK, fun A B hA hB hAK hBK hAB => ?_⟩
  have hinj : Function.Injective (Subtype.val : s → X) := Subtype.val_injective
  rcases hind _ _ (hcont A hA) (hcont B hB) (image_mono hAK) (image_mono hBK)
    (by rw [← image_union, hAB]) with h | h
  · exact Or.inl (hinj.image_injective h)
  · exact Or.inr (hinj.image_injective h)

/-- The measure of the induction of Theorem 20: `(k + 1)²` for a stairwell structure of height
`k`, `(k + 1)² + k + 1 − i₀` for a broken structure of height `k` with a pit at level `i₀`. -/
theorem ho16_lift_aux (h19 : HOProp19) (n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Set E), IsPLGraph G →
      IsConnected G → ∀ (S : Set (E × ℝ)) (k : ℕ), Odd k →
      ((HasStairwell G S k ∧ (k + 1) * (k + 1) ≤ n) ∨
        (∃ i₀, HasBrokenStairwell G S k i₀ ∧ (k + 1) * (k + 1) + (k + 1 - i₀) ≤ n)) →
      ∀ (X : Type) [MetricSpace X] [CompactSpace X], IsHereditarilyIndecomposable (univ : Set X) →
      ∀ f : X → E, Continuous f → (∀ x, f x ∈ G) → ∀ ε : ℝ, 0 < ε →
      ∃ h : X → E × ℝ, Continuous h ∧ (∀ x, h x ∈ S) ∧ ∀ x, dist (f x) (h x).1 < ε := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro E _ _ G hG hconn S k hk hcase X _ _ hHI f hf hfG ε hε
  rcases hcase with ⟨⟨T, α, hS⟩, hn⟩ | ⟨i₀, ⟨T, α, γ, P₁, P₂, hB⟩, hn⟩
  · -- a stairwell structure of height `k`
    by_cases hk1 : k = 1
    · subst hk1
      obtain ⟨-, -, hθc, hθ⟩ := ho16_height_one hG hconn hS
      refine ⟨fun x => Function.invFunOn Prod.fst S (f x), hθc.comp_continuous hf hfG,
        fun x => (hθ _ (hfG x)).1, fun x => ?_⟩
      rw [(hθ _ (hfG x)).2, dist_self]
      exact hε
    · have hk3 : 3 ≤ k := by
        obtain ⟨m, hm⟩ := hk
        have := hS.1
        omega
      have hB := ho16_prop17 hS hk3
      have hodd : Odd (k - 2) := by
        obtain ⟨m, hm⟩ := hk
        exact ⟨m - 1, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have hj : j + 2 - 2 = j := by omega
      rw [hj] at hB hodd
      refine IH ((j + 1) * (j + 1) + (j + 1 - 1)) ?_ E G hG hconn S j hodd
        (Or.inr ⟨1, ⟨_, _, _, _, _, hB⟩, le_rfl⟩) X hHI f hf hfG ε hε
      have : j + 1 - 1 = j := by omega
      rw [this]
      nlinarith
  · -- a broken stairwell structure of height `k` with a pit at level `i₀`
    have hi₁ : 1 ≤ i₀ := hB.1
    have hik : i₀ ≤ k := hB.2.1
    have hSdef : S = (⋃ i ∈ Icc 1 k, T i) ∪ P₁ ∪ P₂ := hB.2.2.2.2.2.2.2.1
    by_cases hγ : γ = ∅
    · -- p. 201, first remark
      have hS' := ho16_rem17_gamma hB hγ
      obtain ⟨h, hc, hmem, hd⟩ := IH ((k + 1) * (k + 1)) (by omega) E G hG hconn _ k hk
        (Or.inl ⟨⟨T, α, hS'⟩, le_rfl⟩) X hHI f hf hfG ε hε
      refine ⟨h, hc, fun x => ?_, hd⟩
      rw [hSdef]
      exact Or.inl (Or.inl (hmem x))
    by_cases hE : endSet G P₁ = ∅
    · -- p. 201, second remark
      obtain ⟨-, hS'⟩ := ho16_rem17_P1 hconn hB hE
      have hk1 : 1 ≤ k + 1 - i₀ := by omega
      have hk2 : 2 ≤ k + 1 := by omega
      obtain ⟨h, hc, hmem, hd⟩ := IH ((1 + 1) * (1 + 1)) (by nlinarith) E G hG hconn _ 1 odd_one
        (Or.inl ⟨⟨_, _, hS'⟩, le_rfl⟩) X hHI f hf hfG ε hε
      refine ⟨h, hc, fun x => ?_, hd⟩
      rw [hSdef]
      exact Or.inl (Or.inr (hmem x))
    -- Proposition 19, Theorem 8, and the induction hypothesis in `E × ℝ`
    obtain ⟨G₁, G₂, G₃, F₁, F₂, F₃, hF, hFconn, S', hS'S, hlt, heq⟩ :=
      h19 E G S k i₀ T α γ P₁ P₂ hG hconn hB (nonempty_iff_ne_empty.2 hγ)
        (nonempty_iff_ne_empty.2 hE)
    obtain ⟨g, hgc, hgF, hgd⟩ := ho16_theorem8 hHI hF hf hfG (half_pos hε)
    have hcase' : (HasStairwell (F₁ ∪ F₂ ∪ F₃) S' k ∧ (k + 1) * (k + 1) < n) ∨
        (∃ i₀', HasBrokenStairwell (F₁ ∪ F₂ ∪ F₃) S' k i₀' ∧
          (k + 1) * (k + 1) + (k + 1 - i₀') < n) := by
      rcases lt_or_eq_of_le hik with hlt' | heq'
      · exact Or.inr ⟨i₀ + 1, hlt hlt', by omega⟩
      · exact Or.inl ⟨heq heq', by omega⟩
    obtain ⟨h', hc', hmem', hd'⟩ : ∃ h' : X → (E × ℝ) × ℝ, Continuous h' ∧
        (∀ x, h' x ∈ S') ∧ ∀ x, dist (g x) (h' x).1 < ε / 2 := by
      rcases hcase' with ⟨hS', hm⟩ | ⟨i₀', hS', hm⟩
      · exact IH _ hm (E × ℝ) _ hF.isPLGraph_union hFconn S' k hk (Or.inl ⟨hS', le_rfl⟩) X hHI
          g hgc hgF (ε / 2) (half_pos hε)
      · exact IH _ hm (E × ℝ) _ hF.isPLGraph_union hFconn S' k hk
          (Or.inr ⟨i₀', hS', le_rfl⟩) X hHI g hgc hgF (ε / 2) (half_pos hε)
    refine ⟨fun x => phiStar (h' x), continuous_phiStar.comp hc', fun x => (hS'S (hmem' x)).2,
      fun x => ?_⟩
    have h1 : dist (g x).1 (h' x).1.1 ≤ dist (g x) (h' x).1 := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    calc dist (f x) (phiStar (h' x)).1 = dist (f x) (h' x).1.1 := rfl
      _ ≤ dist (f x) (g x).1 + dist (g x).1 (h' x).1.1 := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le (hgd x) (h1.trans (hd' x).le)
      _ = ε := add_halves ε

/-- **The induction of Theorem 20** (pp. 209–210): a map of a hereditarily indecomposable
compactum to a connected PL graph `G` is approximated by the first coordinate of a map into any
set with a stairwell structure of odd height.

With Proposition 19 as the hypothesis `h19 : HOProp19`; the skeleton's `ho16_lift_stairwell`
(`HO16D.lean`) discharges it with `hoProp19_holds`. -/
theorem ho16_lift_stairwell_of_prop19 (h19 : HOProp19) (k : ℕ) (hk : Odd k) (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Set E) (hG : IsPLGraph G)
    (hconn : IsConnected G) (S : Set (E × ℝ))
    (hS : HasStairwell G S k) (X : Type) [MetricSpace X] [CompactSpace X]
    (hHI : IsHereditarilyIndecomposable (univ : Set X)) (f : X → E) (hf : Continuous f)
    (hfG : ∀ x, f x ∈ G) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : X → E × ℝ, Continuous h ∧ (∀ x, h x ∈ S) ∧ ∀ x, dist (f x) (h x).1 < ε :=
  ho16_lift_aux h19 _ E G hG hconn S k hk (Or.inl ⟨hS, le_rfl⟩) X hHI f hf hfG ε hε

/-- **H–O Theorem 20, forward direction**, from Theorem 15 and Proposition 19.

With Proposition 19 as the hypothesis `h19 : HOProp19`; the skeleton's `ho16_theorem20_of_thm15`
(`HO16D.lean`) discharges it with `hoProp19_holds`. -/
theorem ho16_theorem20_of_thm15_prop19 (h19 : HOProp19) (h15 : HOThm15) : HOThm20 := by
  intro X _ _ hHI E _ _ G hG f hf hfG M hMG hsep U hU hMU ε hε
  classical
  -- one component at a time
  have key : ∀ C : Set E, ∃ H : X → E × ℝ, ∀ y ∈ G, C = connectedComponentIn G y →
      ContinuousOn H (f ⁻¹' C) ∧ ∀ x, f x ∈ C →
        H x ∈ U ∩ (G ×ˢ Icc (0 : ℝ) 1) ∧ dist (f x) (H x).1 < ε := by
    intro C
    by_cases hCex : ∃ y ∈ G, C = connectedComponentIn G y
    swap
    · exact ⟨fun _ => 0, fun y hy hC => absurd ⟨y, hy, hC⟩ hCex⟩
    obtain ⟨y, hyG, rfl⟩ := hCex
    set C := connectedComponentIn G y with hCdef
    have hCpl : IsPLGraph C := hG.connectedComponentIn y
    have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.2 hyG
    have hCG : C ⊆ G := connectedComponentIn_subset G y
    set M' := M ∩ C ×ˢ (univ : Set ℝ) with hM'def
    have hM' : M' ⊆ C ×ˢ Ioo (0 : ℝ) 1 := by
      rintro p ⟨hpM, hpC, -⟩
      exact ⟨hpC, (hMG hpM).2⟩
    have hsep' : SeparatesIn (C ×ˢ Icc (0 : ℝ) 1) M' (C ×ˢ ({0} : Set ℝ))
        (C ×ˢ ({1} : Set ℝ)) := by
      obtain ⟨V₀, V₁, hV₀, hV₁, hcov, hdis, h0, h1⟩ := hsep
      refine ⟨V₀, V₁, hV₀, hV₁, ?_, ?_, ?_, ?_⟩
      · rintro p ⟨⟨hpC, hpI⟩, hpM⟩
        exact hcov ⟨⟨hCG hpC, hpI⟩, fun h => hpM ⟨h, hpC, trivial⟩⟩
      · apply subset_empty_iff.1
        rintro p ⟨hpV, ⟨hpC, hpI⟩, hpM⟩
        have : p ∈ V₀ ∩ V₁ ∩ (G ×ˢ Icc (0 : ℝ) 1 \ M) :=
          ⟨hpV, ⟨hCG hpC, hpI⟩, fun h => hpM ⟨h, hpC, trivial⟩⟩
        rw [hdis] at this
        exact this
      · rintro p ⟨hpC, hp⟩
        exact h0 ⟨hCG hpC, hp⟩
      · rintro p ⟨hpC, hp⟩
        exact h1 ⟨hCG hpC, hp⟩
    obtain ⟨S, k, hSU, hk, hSt⟩ :=
      h15 E C hCpl hCconn M' hM' hsep' U hU (inter_subset_left.trans hMU)
    have hXc : IsClosed (f ⁻¹' C) := (hG.isClosed_comp y).preimage hf
    haveI : CompactSpace (f ⁻¹' C) := isCompact_iff_compactSpace.1 hXc.isCompact
    obtain ⟨hc, hcc, hcS, hcd⟩ := ho16_lift_stairwell_of_prop19 h19 k hk E C hCpl hCconn S hSt
      (f ⁻¹' C) (isHereditarilyIndecomposable_univ_subtype hHI _) (fun x => f x.1)
      (hf.comp continuous_subtype_val) (fun x => x.2) ε hε
    refine ⟨fun x => if hx : f x ∈ C then hc ⟨x, hx⟩ else 0, fun y' _ hC' => ⟨?_, ?_⟩⟩
    · rw [continuousOn_iff_continuous_restrict]
      convert hcc using 1
      ext1 ⟨x, hx⟩
      simp only [restrict_apply]
      rw [dif_pos (show f x ∈ C from hx)]
    · intro x hx
      simp only [dif_pos hx]
      refine ⟨⟨(hSU (hcS ⟨x, hx⟩)).1, ?_⟩, hcd ⟨x, hx⟩⟩
      obtain ⟨-, h1, h2⟩ := hSU (hcS ⟨x, hx⟩)
      exact ⟨hCG h1, Ioo_subset_Icc_self h2⟩
  choose H hH using key
  have hcomp : ∀ x, f x ∈ connectedComponentIn G (f x) := fun x =>
    mem_connectedComponentIn (hfG x)
  refine ⟨fun x => H (connectedComponentIn G (f x)) x, ?_,
    fun x => ((hH _ (f x) (hfG x) rfl).2 x (hcomp x)).1,
    fun x => ((hH _ (f x) (hfG x) rfl).2 x (hcomp x)).2⟩
  rw [continuous_iff_continuousAt]
  intro x
  set C := connectedComponentIn G (f x)
  obtain ⟨O, hO, hCO⟩ := exists_open_eq_inter (connectedComponentIn_subset G (f x))
    (hG.comp_relOpen (f x))
  have hopen : IsOpen (f ⁻¹' C) := by
    have : f ⁻¹' C = f ⁻¹' O := by
      ext x'
      simp only [mem_preimage]
      rw [show C = G ∩ O from hCO]
      exact ⟨fun h => h.2, fun h => ⟨hfG x', h⟩⟩
    rw [this]
    exact hO.preimage hf
  have hmem : f ⁻¹' C ∈ 𝓝 x := hopen.mem_nhds (hcomp x)
  have heq : (fun x' => H (connectedComponentIn G (f x')) x') =ᶠ[𝓝 x] H C := by
    filter_upwards [hmem] with x' hx'
    rw [← connectedComponentIn_eq hx']
  exact (((hH C (f x) (hfG x) rfl).1).continuousAt hmem).congr heq.symm

/-- The classification step of batch 193 from `HOThm15` and `HOProp19`; the skeleton's
`homeomorph_pseudoArc_of_indec_homogeneous_of_thm15` (`HO16D.lean`) discharges `HOProp19` with
`hoProp19_holds`. -/
theorem homeomorph_pseudoArc_of_indec_homogeneous_of_thm15_prop19 (h19 : HOProp19)
    (h15 : HOThm15) (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (hhom : IsHomogeneous M)
    (hind : ¬ IsDecomposableSpace M) (hnt : (univ : Set M).Nontrivial) :
    ∃ M₀ : Set Pt, IsPseudoArc M₀ ∧ Nonempty (M ≃ₜ M₀) :=
  homeomorph_pseudoArc_of_indec_homogeneous (ho16_theorem20_of_thm15_prop19 h19 h15) M hhom
    hind hnt

end HPC.HO16
