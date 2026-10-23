import HPC.Jones.Moore22
import HPC.Moore.M25Plane
import HPC.Plane.Tree7Star
import HPC.Jones.Jones49Why

/-!
# Batch 150, item B: Moore 1922, Theorem 4 — the general (non-planar-separation) steps

Steps of Theorem 4 that do not use plane separation by continua:

* `isPreconnected_compl_of_mooreSimplyConnected`: the complement of a bounded open set which is
  simply connected in Moore's sense is connected (a bounded clopen piece `E₂` of the complement
  would give the bounded set `H = thickening (δ/2) E₂`, whose frontier lies in `R` but which is not
  contained in `R`);
* `isConnected_frontier_of_mooreSimplyConnected`: hence (unicoherence of the plane) the boundary of
  a bounded, connected, open, Moore-simply-connected set is connected;
* `locallyConnectedSpace_of_cikAt`: a set connected im kleinen at each of its points is locally
  connected (as a space);
* `exists_crossing_continua`: the reconstruction of the cited PNAS argument — from a point `P` of a
  continuum `M` at which `M` is not connected im kleinen, two concentric squares about `P` and
  infinitely many mutually disjoint subcontinua of `M` each meeting both squares and lying between
  them.
-/

namespace HPC.Jones

open Set Topology Metric HPC.Plane

/-- **The complement of a bounded, Moore-simply-connected open set is connected.** -/
theorem isPreconnected_compl_of_mooreSimplyConnected {R : Set Pt} (hRo : IsOpen R)
    (hRb : Bornology.IsBounded R) (hsc : MooreSimplyConnected R) : IsPreconnected Rᶜ := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hcov hdisj
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnu, hnv⟩ := hcon
  have hRc : IsClosed Rᶜ := hRo.isClosed_compl
  set E1 := Rᶜ ∩ u
  set E2 := Rᶜ ∩ v
  have hE1c : IsClosed E1 := hRc.inter hu
  have hE2c : IsClosed E2 := hRc.inter hv
  have hE12 : Disjoint E1 E2 := by
    rw [disjoint_iff_inter_eq_empty]
    rw [← hdisj]; ext z; simp only [E1, E2, mem_inter_iff]; tauto
  have hE1ne : E1.Nonempty := by
    obtain ⟨z, hz, hzv⟩ := not_subset.1 hnv
    exact ⟨z, hz, (hcov hz).resolve_right hzv⟩
  have hE2ne : E2.Nonempty := by
    obtain ⟨z, hz, hzu⟩ := not_subset.1 hnu
    exact ⟨z, hz, (hcov hz).resolve_left hzu⟩
  -- the outside of a large ball is connected and lies in one of the two pieces
  obtain ⟨ρ, hρ⟩ := hRb.subset_closedBall (0 : Pt)
  have hO : IsPreconnected (closedBall (0 : Pt) ρ)ᶜ :=
    (isConnected_compl_closedBall_pt 0 ρ).1.isPreconnected
  have hORc : (closedBall (0 : Pt) ρ)ᶜ ⊆ Rᶜ := compl_subset_compl.2 hρ
  have key : ∀ {F1 F2 : Set Pt}, IsClosed F1 → IsClosed F2 → Disjoint F1 F2 → F2.Nonempty →
      F1 ∪ F2 = Rᶜ → (closedBall (0 : Pt) ρ)ᶜ ⊆ F1 → False := by
    intro F1 F2 hF1 hF2 hF12 hF2ne hun hOF1
    have hF2b : F2 ⊆ closedBall (0 : Pt) ρ := fun z hz => by
      by_contra hz'
      exact disjoint_left.1 hF12 (hOF1 hz') hz
    have hF2k : IsCompact F2 := (isCompact_closedBall _ _).of_isClosed_subset hF2 hF2b
    obtain ⟨δ, hδ, hδsub⟩ := hF2k.exists_cthickening_subset_open hF1.isOpen_compl
      (fun z hz hz1 => disjoint_left.1 hF12 hz1 hz)
    set H := thickening (δ / 2) F2
    have hHb : Bornology.IsBounded H := hF2k.isBounded.thickening
    have hfr : frontier H ⊆ R := by
      intro z hz
      have h1 := frontier_thickening_subset F2 hz
      simp only [mem_setOf_eq] at h1
      have hz2 : z ∉ F2 := fun h => by
        rw [infEDist_zero_of_mem h] at h1
        exact (ENNReal.ofReal_pos.2 (half_pos hδ)).ne h1
      have hzc : z ∈ cthickening δ F2 := by
        rw [cthickening, mem_setOf_eq, h1]
        exact ENNReal.ofReal_le_ofReal (half_le_self hδ.le)
      have hz1 : z ∉ F1 := hδsub hzc
      by_contra hzR
      have : z ∈ F1 ∪ F2 := by rw [hun]; exact hzR
      rcases this with h | h
      · exact hz1 h
      · exact hz2 h
    obtain ⟨w, hw⟩ := hF2ne
    have hwH : w ∈ H := self_subset_thickening (half_pos hδ) F2 hw
    have hwR : w ∈ R := hsc H hHb hfr hwH
    have : w ∈ F1 ∪ F2 := Or.inr hw
    rw [hun] at this
    exact this hwR
  have hun12 : E1 ∪ E2 = Rᶜ := by
    ext z; simp only [E1, E2, mem_union, mem_inter_iff]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h; rcases hcov h with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have hOsub : (closedBall (0 : Pt) ρ)ᶜ ⊆ E1 ∪ E2 := hun12 ▸ hORc
  rcases (isPreconnected_iff_subset_of_disjoint_closed.1 hO) E1 E2 hE1c hE2c hOsub (by
      rw [disjoint_iff_inter_eq_empty.1 hE12, inter_empty]) with h | h
  · exact key hE1c hE2c hE12 hE2ne hun12 h
  · exact key hE2c hE1c hE12.symm hE1ne (by rw [union_comm]; exact hun12) h

/-- **The boundary of a bounded, connected, open, Moore-simply-connected set is connected.** -/
theorem isConnected_frontier_of_mooreSimplyConnected {R : Set Pt} (hRo : IsOpen R)
    (hRc : IsConnected R) (hRb : Bornology.IsBounded R) (hsc : MooreSimplyConnected R) :
    IsConnected (frontier R) := by
  have hfr : frontier R = closure R ∩ Rᶜ := by
    rw [frontier, hRo.interior_eq, diff_eq]
  refine ⟨?_, ?_⟩
  · refine nonempty_frontier_iff.2 ⟨hRc.nonempty, fun h => ?_⟩
    rw [h] at hRb
    obtain ⟨ρ, hρ⟩ := hRb.subset_closedBall (0 : Pt)
    exact (isConnected_compl_closedBall_pt 0 ρ).2
      (isBounded_closedBall.subset fun z _ => hρ (mem_univ z))
  · rw [hfr]
    refine HPC.Moore.plane_unicoherent isClosed_closure hRo.isClosed_compl
      hRc.isPreconnected.closure (isPreconnected_compl_of_mooreSimplyConnected hRo hRb hsc) ?_
    exact eq_univ_of_forall fun z => by
      by_cases hz : z ∈ R
      · exact Or.inl (subset_closure hz)
      · exact Or.inr hz

/-- **Connected im kleinen at every point implies locally connected.** For a set `M` of the
plane, viewed as a space. -/
theorem locallyConnectedSpace_of_cikAt {M : Set Pt} (h : ∀ P ∈ M, CikAt M P) :
    LocallyConnectedSpace M := by
  rw [locallyConnectedSpace_iff_connectedComponentIn_open]
  intro F hF x hxF
  rw [Metric.isOpen_iff]
  intro y hy
  have hyF : y ∈ F := connectedComponentIn_subset _ _ hy
  obtain ⟨ε, hε, hεF⟩ := Metric.isOpen_iff.1 hF y hyF
  obtain ⟨δ, hδ, hδC⟩ := h y y.2 ε hε
  refine ⟨δ, hδ, fun z hz => ?_⟩
  obtain ⟨C, hCM, hCc, hzC, hyC, hCb, hCd⟩ := hδC z z.2 (mem_ball.1 hz)
  set C' : Set M := Subtype.val ⁻¹' C
  have hCimg : Subtype.val '' C' = C := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe]; exact inter_eq_left.2 hCM
  have hC'c : IsPreconnected C' := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, hCimg]; exact hCc
  have hC'F : C' ⊆ F := by
    intro w hw
    apply hεF
    rw [mem_ball, Subtype.dist_eq]
    exact (dist_le_diam_of_mem hCb hw hyC).trans_lt hCd
  have hC'sub := hC'c.subset_connectedComponentIn (x := y) hyC hC'F
  rw [connectedComponentIn_eq hy]
  exact hC'sub hzC

/-- **The PNAS step of Theorem 4 (reconstructed).** Moore's sufficiency proof cites "the argument
beginning with the second line from the bottom of page 365 … of [PNAS 4 (1918)]" for this: if a
compact connected plane set `M` is not connected im kleinen at `P ∈ M`, there are two concentric
squares about `P` (circles of the sup metric) and infinitely many mutually exclusive continua
`t n ⊆ M`, each lying between the squares and meeting both.

Proof: with `ε` witnessing the failure, `r₂ = ε/3`, `r₁ = ε/6`, let `Γ` be the component of `P` in
`M ∩ B̄(P, r₂)`. Points `X ∈ M` arbitrarily near `P` lie outside `Γ`; their components in
`M ∩ B̄(P, r₂)` are infinitely many (a finite union of them is closed and misses `P`), pairwise
disjoint, and each meets the outer square (boundary bumping). Inside each, a second boundary bumping
from a point of the outer square, in the part outside `B(P, r₁)`, gives `t n`. -/
theorem exists_crossing_continua {M : Set Pt} (hMc : IsCompact M) (hMconn : IsConnected M)
    {P : Pt} (hP : P ∈ M) (hnot : ¬ CikAt M P) :
    ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ ∃ t : ℕ → Set Pt, Pairwise (fun m n => Disjoint (t m) (t n)) ∧
      ∀ n, IsConnected (t n) ∧ IsCompact (t n) ∧ t n ⊆ M ∧
        (∀ z ∈ t n, r₁ ≤ dist z P ∧ dist z P ≤ r₂) ∧ (∃ z ∈ t n, dist z P = r₁) ∧
        (∃ z ∈ t n, dist z P = r₂) := by
  classical
  simp only [CikAt, not_forall, not_exists, not_and, exists_prop] at hnot
  obtain ⟨ε, hε, hbad⟩ := hnot
  set r₂ := ε / 3
  set r₁ := ε / 6
  have hr₁ : 0 < r₁ := by positivity
  have hr₁₂ : r₁ < r₂ := by simp only [r₁, r₂]; linarith
  set K := M ∩ closedBall P r₂
  have hKc : IsCompact K := hMc.inter_right isClosed_closedBall
  have hKcl : IsClosed K := hKc.isClosed
  have hPK : P ∈ K := ⟨hP, mem_closedBall_self (by positivity)⟩
  set Γ := connectedComponentIn K P
  -- a point `X` given by the failure is not in `Γ`
  have hXΓ : ∀ {X}, (∀ C ⊆ M, IsPreconnected C → X ∈ C → P ∈ C → Bornology.IsBounded C →
      ¬ diam C < ε) → X ∉ Γ := by
    intro X hX hXG
    have hΓK : Γ ⊆ K := connectedComponentIn_subset _ _
    have hΓb : Γ ⊆ closedBall P r₂ := hΓK.trans inter_subset_right
    refine hX Γ (hΓK.trans inter_subset_left) isPreconnected_connectedComponentIn hXG
      (mem_connectedComponentIn hPK) (isBounded_closedBall.subset hΓb) ?_
    calc diam Γ ≤ 2 * r₂ := diam_le_of_subset_closedBall' (by positivity) hΓb
      _ < ε := by simp only [r₂]; linarith
  set 𝒞 : Set (Set Pt) := {S | ∃ X ∈ M, dist X P < r₁ ∧ X ∉ Γ ∧ S = connectedComponentIn K X}
  have hcomp_eq : ∀ {X z}, z ∈ connectedComponentIn K X →
      connectedComponentIn K X = connectedComponentIn K z := fun hz => connectedComponentIn_eq hz
  have hPnot : ∀ S ∈ 𝒞, P ∉ S := by
    rintro S ⟨X, -, -, hXG, rfl⟩ hPS
    have := hcomp_eq hPS
    have hXK : X ∈ connectedComponentIn K X := by
      by_contra hn
      rw [connectedComponentIn_eq_empty (fun h => hn (mem_connectedComponentIn h))] at hPS
      exact hPS
    rw [this] at hXK
    exact hXG hXK
  have hinf : 𝒞.Infinite := by
    intro hfin
    have hUcl : IsClosed (⋃₀ 𝒞) := sUnion_eq_biUnion ▸ Set.Finite.isClosed_biUnion (s := 𝒞)
      (f := id) hfin fun S hS => by
      obtain ⟨X, -, -, -, rfl⟩ := hS
      exact isClosed_connectedComponentIn_of_isClosed hKcl X
    have hPU : P ∉ ⋃₀ 𝒞 := fun ⟨S, hS, hPS⟩ => hPnot S hS hPS
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hUcl.isOpen_compl P hPU
    obtain ⟨X, hXM, hXd, hX⟩ := hbad (min δ r₁) (lt_min hδ hr₁)
    have hXd1 : dist X P < r₁ := hXd.trans_le (min_le_right _ _)
    have hXK : X ∈ K := ⟨hXM, le_of_lt (hXd1.trans hr₁₂)⟩
    have hmem : connectedComponentIn K X ∈ 𝒞 := ⟨X, hXM, hXd1, hXΓ hX, rfl⟩
    exact hδU (mem_ball.2 (hXd.trans_le (min_le_left _ _)))
      ⟨_, hmem, mem_connectedComponentIn hXK⟩
  set f := hinf.natEmbedding
  have hKM : K ≠ M := by
    intro hKM
    obtain ⟨X, hXM, -, hX⟩ := hbad r₁ hr₁
    apply hXΓ hX
    have : Γ = connectedComponentIn M P := by simp only [Γ, hKM]
    rw [this]
    exact hMconn.isPreconnected.subset_connectedComponentIn hP subset_rfl hXM
  have hstep : ∀ n, ∃ T : Set Pt, IsConnected T ∧ IsCompact T ∧ T ⊆ (f n : Set Pt) ∧
      (∀ z ∈ T, r₁ ≤ dist z P ∧ dist z P ≤ r₂) ∧ (∃ z ∈ T, dist z P = r₁) ∧
      (∃ z ∈ T, dist z P = r₂) := by
    intro n
    obtain ⟨X, hXM, hXd, -, hSX⟩ := (f n).2
    set S := (f n : Set Pt)
    have hXK : X ∈ K := ⟨hXM, le_of_lt (hXd.trans hr₁₂)⟩
    have hSK : S ⊆ K := by rw [hSX]; exact connectedComponentIn_subset _ _
    have hXS : X ∈ S := by rw [hSX]; exact mem_connectedComponentIn hXK
    have hSconn : IsPreconnected S := by rw [hSX]; exact isPreconnected_connectedComponentIn
    have hScl : IsClosed S := by rw [hSX]; exact isClosed_connectedComponentIn_of_isClosed hKcl X
    have hSc : IsCompact S := hKc.of_isClosed_subset hScl hSK
    -- first bumping: `S` meets the outer square
    obtain ⟨K0, -, hK0c, hK0K, hXK0, w, hwK0, hwcl⟩ :=
      exists_continuum_bump_compact hMconn.isPreconnected hKc inter_subset_left hKM hXK
    have hK0S : K0 ⊆ S := by
      rw [hSX]; exact hK0c.isPreconnected.subset_connectedComponentIn hXK0 hK0K
    have hwS : w ∈ S := hK0S hwK0
    have hwd : dist w P = r₂ := by
      have h1 : dist w P ≤ r₂ := (hSK hwS).2
      have h2 : r₂ ≤ dist w P := by
        have hsub : M \ K ⊆ {z | r₂ ≤ dist z P} := fun z hz => by
          by_contra h
          exact hz.2 ⟨hz.1, mem_closedBall.2 (le_of_lt (not_le.1 h))⟩
        exact closure_minimal hsub (isClosed_le continuous_const
          (continuous_id.dist continuous_const)) hwcl
      linarith
    -- second bumping, inside `S`, outside the inner square
    set F := S ∩ {z | r₁ ≤ dist z P}
    have hFcl : IsClosed F := hScl.inter (isClosed_le continuous_const
      (continuous_id.dist continuous_const))
    have hFc : IsCompact F := hSc.of_isClosed_subset hFcl inter_subset_left
    have hFS : F ≠ S := fun h => by
      have : X ∈ F := by rw [h]; exact hXS
      exact absurd this.2 (not_le.2 hXd)
    have hwF : w ∈ F := ⟨hwS, show r₁ ≤ dist w P by rw [hwd]; exact hr₁₂.le⟩
    obtain ⟨T, hTc, hTconn, hTF, hwT, u, huT, hucl⟩ :=
      exists_continuum_bump_compact hSconn hFc inter_subset_left hFS hwF
    refine ⟨T, hTconn, hTc, hTF.trans inter_subset_left,
      fun z hz => ⟨(hTF hz).2, (hSK (hTF hz).1).2⟩, ⟨u, huT, ?_⟩, ⟨w, hwT, hwd⟩⟩
    have h1 : r₁ ≤ dist u P := (hTF huT).2
    have h2 : dist u P ≤ r₁ := by
      have hsub : S \ F ⊆ {z | dist z P ≤ r₁} := fun z hz => by
        by_contra h
        exact hz.2 ⟨hz.1, show r₁ ≤ dist z P from le_of_lt (not_le.1 h)⟩
      exact closure_minimal hsub (isClosed_le (continuous_id.dist continuous_const)
        continuous_const) hucl
    linarith
  choose t ht using hstep
  refine ⟨r₁, r₂, hr₁, hr₁₂, t, ?_, fun n => ?_⟩
  · intro m n hmn
    refine disjoint_left.2 fun z hzm hzn => hmn ?_
    have h1 := (ht m).2.2.1 hzm
    have h2 := (ht n).2.2.1 hzn
    obtain ⟨X, -, -, -, hSX⟩ := (f m).2
    obtain ⟨Y, -, -, -, hSY⟩ := (f n).2
    have : (f m : Set Pt) = f n := by
      rw [hSX] at h1 ⊢; rw [hSY] at h2 ⊢
      rw [hcomp_eq h1, hcomp_eq h2]
    exact f.injective (Subtype.ext this)
  · obtain ⟨hc, hk, hsub, hd, h1, h2⟩ := ht n
    obtain ⟨X, -, -, -, hSX⟩ := (f n).2
    refine ⟨hc, hk, ?_, hd, h1, h2⟩
    intro z hz
    have := hsub hz
    rw [hSX] at this
    exact (connectedComponentIn_subset _ _ this).1

end HPC.Jones
