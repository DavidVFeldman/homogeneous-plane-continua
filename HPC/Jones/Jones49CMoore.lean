import HPC.Jones.Jones49CAnn
import HPC.Jones.Moore22T4

/-!
# Batch 151, items B and C: Moore's sufficiency in local form; Moore 1922 Theorem 4

With the cyclic order of crossing continua (`sector_cyclic`, `HPC/Jones/Jones49CAnn.lean`):

* `exists_crossing_continua_closed`: the PNAS step of batch 150 (`exists_crossing_continua`) for a
  *closed* connected set (the boundary of an unbounded domain need not be compact);
* `exists_cross_sub`: a continuum crossing an annulus inside a closed connected set joining the inner
  disc to the outside, lying in a connected piece through the given inner point (boundary bumping
  twice);
* `cikAt_of_locallyConnectedSpace`: a locally connected set is connected im kleinen at each point;
* `sphere_walk`: walking along the middle square from a point off a closed set `K` to the first
  point of `K`;
* `sufficiency_local`: **Moore's p. 236 argument with Whyburn's local condition** — the boundary of
  an open plane set is locally connected if it is connected and no boundary point is the limit of
  points of `R` no two of which lie in a small connected subset of `R`;
* `propertyS_of_locallyConnected`: **necessity** — a bounded connected open plane set with locally
  connected boundary has property S (no simple connectivity needed);
* `hloc_of_propertyS`: property S gives the local condition (pigeonhole).
-/

namespace HPC.Jones.Sector

open Set Topology Metric Filter HPC.Plane

/-- **The PNAS step for closed sets.** `exists_crossing_continua` (batch 150) with `IsClosed M` in
place of `IsCompact M`; the proof is the same, with `M ∩ B̄(P, r₂)` compact as a closed subset of a
closed ball. -/
theorem exists_crossing_continua_closed {M : Set Pt} (hMcl : IsClosed M) (hMconn : IsConnected M)
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
  have hKc : IsCompact K := (isCompact_closedBall P r₂).inter_left hMcl
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
/-- A crossing continuum meets every intermediate square (intermediate value theorem). -/
theorem IsCrossA.exists_dist_eq {P : ℝ × ℝ} {r₁ r₂ ρ : ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsCrossA P r₁ r₂ K) (h1 : r₁ ≤ ρ) (h2 : ρ ≤ r₂) : ∃ z ∈ K, dist z P = ρ := by
  obtain ⟨a, ha, hda⟩ := hK.inner
  obtain ⟨b, hb, hdb⟩ := hK.outer
  obtain ⟨z, hz, hzd⟩ := hK.conn.isPreconnected.intermediate_value ha hb
    (continuous_id.dist continuous_const).continuousOn
    ⟨show dist a P ≤ ρ by linarith, show ρ ≤ dist b P by linarith⟩
  exact ⟨z, hz, hzd⟩

/-- **A crossing continuum inside a closed connected set.** If a closed connected `S` has a point `X`
inside the inner square and a point `Y` outside the outer one, a subcontinuum `T` of `S` crosses the
annulus, and lies in a connected `K0 ⊆ S ∩ B̄(P, r₂)` containing `X` (boundary bumping twice). -/
theorem exists_cross_sub {S : Set (ℝ × ℝ)} (hS : IsClosed S) (hSc : IsPreconnected S)
    {P X Y : ℝ × ℝ} {r₁ r₂ : ℝ} (h12 : r₁ < r₂) (hX : X ∈ S) (hXd : dist X P < r₁) (hY : Y ∈ S)
    (hYd : r₂ < dist Y P) :
    ∃ T K0 : Set (ℝ × ℝ), IsCrossA P r₁ r₂ T ∧ T ⊆ K0 ∧ K0 ⊆ S ∩ closedBall P r₂ ∧
      IsPreconnected K0 ∧ X ∈ K0 := by
  set K := S ∩ closedBall P r₂
  have hKc : IsCompact K := (isCompact_closedBall P r₂).inter_left hS
  have hKS : K ≠ S := fun h => by
    have : Y ∈ K := h ▸ hY
    exact absurd (mem_closedBall.1 this.2) (not_le.2 hYd)
  have hXK : X ∈ K := ⟨hX, mem_closedBall.2 (hXd.trans h12).le⟩
  obtain ⟨K0, hK0c, hK0conn, hK0K, hXK0, w, hwK0, hwcl⟩ :=
    exists_continuum_bump_compact hSc hKc inter_subset_left hKS hXK
  have hwd : dist w P = r₂ := by
    have h1 : dist w P ≤ r₂ := mem_closedBall.1 (hK0K hwK0).2
    have h2 : r₂ ≤ dist w P := by
      have hsub : S \ K ⊆ {z | r₂ ≤ dist z P} := fun z hz => by
        by_contra h
        exact hz.2 ⟨hz.1, mem_closedBall.2 (le_of_lt (not_le.1 h))⟩
      exact closure_minimal hsub (isClosed_le continuous_const
        (continuous_id.dist continuous_const)) hwcl
    linarith
  set F := K0 ∩ {z | r₁ ≤ dist z P}
  have hFcl : IsClosed F := hK0c.isClosed.inter (isClosed_le continuous_const
    (continuous_id.dist continuous_const))
  have hFc : IsCompact F := hK0c.of_isClosed_subset hFcl inter_subset_left
  have hFK0 : F ≠ K0 := fun h => by
    have : X ∈ F := by rw [h]; exact hXK0
    exact absurd this.2 (not_le.2 hXd)
  have hwF : w ∈ F := ⟨hwK0, show r₁ ≤ dist w P by rw [hwd]; exact h12.le⟩
  obtain ⟨T, hTc, hTconn, hTF, hwT, u, huT, hucl⟩ :=
    exists_continuum_bump_compact hK0conn.isPreconnected hFc inter_subset_left hFK0 hwF
  have hud : dist u P = r₁ := by
    have h1 : r₁ ≤ dist u P := (hTF huT).2
    have h2 : dist u P ≤ r₁ := by
      have hsub : K0 \ F ⊆ {z | dist z P ≤ r₁} := fun z hz => by
        by_contra h
        exact hz.2 ⟨hz.1, show r₁ ≤ dist z P from le_of_lt (not_le.1 h)⟩
      exact closure_minimal hsub (isClosed_le (continuous_id.dist continuous_const)
        continuous_const) hucl
    linarith
  refine ⟨T, K0, ⟨hTc, hTconn, fun z hz => ⟨(hTF hz).2, mem_closedBall.1 (hK0K (hTF hz).1).2⟩,
    ⟨u, huT, hud⟩, ⟨w, hwT, hwd⟩⟩, hTF.trans inter_subset_left, hK0K, hK0conn.isPreconnected,
    hXK0⟩

/-- **Locally connected implies connected im kleinen** at each point (the converse of
`locallyConnectedSpace_of_cikAt`). -/
theorem cikAt_of_locallyConnectedSpace {M : Set Pt} [LocallyConnectedSpace M] {P : Pt}
    (hP : P ∈ M) : CikAt M P := by
  intro ε hε
  set F : Set M := {y | dist (y : Pt) P < ε / 3}
  have hFo : IsOpen F := isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const
  have hPF : (⟨P, hP⟩ : M) ∈ F := by
    show dist P P < ε / 3
    rw [dist_self]; positivity
  have hCo := (locallyConnectedSpace_iff_connectedComponentIn_open.1 inferInstance) F hFo _ hPF
  obtain ⟨δ, hδ, hδC⟩ := Metric.isOpen_iff.1 hCo _ (mem_connectedComponentIn hPF)
  refine ⟨δ, hδ, fun X hX hXd => ?_⟩
  set C' := connectedComponentIn F ⟨P, hP⟩
  have hsub : Subtype.val '' C' ⊆ closedBall P (ε / 3) := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_closedBall.2 (connectedComponentIn_subset _ _ hy : y ∈ F).le
  refine ⟨Subtype.val '' C', by rintro _ ⟨y, -, rfl⟩; exact y.2,
    isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn,
    ⟨⟨X, hX⟩, hδC (by rw [mem_ball, Subtype.dist_eq]; exact hXd), rfl⟩,
    ⟨⟨P, hP⟩, mem_connectedComponentIn hPF, rfl⟩, isBounded_closedBall.subset hsub,
    (diam_le_of_subset_closedBall' (by positivity) hsub).trans_lt (by linarith)⟩

/-- The parametrization `s ↦ Ecov P (s, ρ)` of the square of radius `ρ` about `P`. -/
theorem continuous_Ecov_rad (P : ℝ × ℝ) (ρ : ℝ) : Continuous fun s : ℝ => Ecov P (s, ρ) :=
  (continuous_Ecov P).comp (continuous_id.prodMk continuous_const)

/-- **Walking along a square.** From a point `w` of the square of radius `ρ` off a closed set `K` to a
point of `K` on the same square: there are parameters `a < b` with `Ecov P (a, ρ) = w`,
`Ecov P (b, ρ) ∈ K`, and no parameter of `[a, b)` mapped into `K`. -/
theorem sphere_walk {P w y : ℝ × ℝ} {ρ : ℝ} (hρ : 0 < ρ) {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (hw : dist w P = ρ) (hwK : w ∉ K) (hy : dist y P = ρ) (hyK : y ∈ K) :
    ∃ a b : ℝ, a < b ∧ Ecov P (a, ρ) = w ∧ Ecov P (b, ρ) ∈ K ∧
      ∀ t ∈ Ico a b, Ecov P (t, ρ) ∉ K := by
  obtain ⟨⟨a, ρ'⟩, ha, hfa⟩ := Ecov_surj (r₂ := ρ) hρ (show w ∈ Ann P ρ ρ from ⟨hw.ge, hw.le⟩)
  have hρ' : ρ' = ρ := le_antisymm ha.2 ha.1
  subst hρ'
  obtain ⟨⟨c, ρ''⟩, hc, hfc⟩ := Ecov_surj (r₂ := ρ') hρ (show y ∈ Ann P ρ' ρ' from ⟨hy.ge, hy.le⟩)
  have hρ'' : ρ'' = ρ' := le_antisymm hc.2 hc.1
  subst hρ''
  obtain ⟨j, hj⟩ := exists_int_gt ((a - c) / (2 * Real.pi))
  have hpi : 0 < 2 * Real.pi := by positivity
  set c' := c + 2 * Real.pi * j
  have hac : a < c' := by
    have := (div_lt_iff₀ hpi).1 hj
    simp only [c']; linarith
  have hfc' : Ecov P (c', ρ'') = y := by rw [← hfc]; exact Ecov_sh P (c, ρ'') j
  set f := fun s : ℝ => Ecov P (s, ρ'')
  set Z := Icc a c' ∩ f ⁻¹' K
  have hZc : IsCompact Z := isCompact_Icc.inter_right (hK.preimage (continuous_Ecov_rad P ρ''))
  have hZne : Z.Nonempty := ⟨c', ⟨hac.le, le_rfl⟩, show f c' ∈ K by simp only [f]; rw [hfc']; exact hyK⟩
  have hbZ := hZc.sInf_mem hZne
  have hbdd : BddBelow Z := ⟨a, fun t ht => ht.1.1⟩
  refine ⟨a, sInf Z, lt_of_le_of_ne hbZ.1.1 fun h => hwK ?_, hfa, hbZ.2, fun t ht htK => ?_⟩
  · have := hbZ.2; rw [← h] at this; simp only [f, mem_preimage] at this; rwa [hfa] at this
  · have : t ∈ Z := ⟨⟨ht.1, ht.2.le.trans hbZ.1.2⟩, htK⟩
    exact absurd (csInf_le hbdd this) (not_le.2 ht.2)

/-- **Moore's sufficiency, local form** (Moore 1922 p. 236, with Whyburn's §14 condition in place of
property S). If the boundary `M` of an open plane set `R` is connected and is not locally connected,
then (`exists_crossing_continua_closed`, `sector_cyclic`) there are crossing continua `kₙ ⊆ M` of an
annulus about a point `P ∈ M`, each `kₙ` (`n ≥ 1`) in a piece `Vₙ` cut off by `kₙ₋₁` and `kₙ₊₁`;
points `bₙ ∈ kₙ` on the middle square, a limit point `p` of the odd-indexed ones, and points
`cₙ ∈ R` close to `bₙ` (hence in `Vₙ`) converge to `p`; a connected subset of `R` of diameter
`< (r₂ - r₁)/4` containing two of the odd-indexed `cₙ` would lie in the annulus, miss every `kₙ`, and
so lie in two disjoint pieces. -/
theorem sufficiency_local {R : Set Pt} (hR : IsOpen R) (hB : IsConnected (frontier R))
    (hloc : ∀ p ∈ frontier R, ∀ ε > 0, ¬ ∃ u : ℕ → Pt, (∀ n, u n ∈ R) ∧ Tendsto u atTop (𝓝 p) ∧
      ∀ i j, i ≠ j → ¬ ∃ C ⊆ R, IsPreconnected C ∧ u i ∈ C ∧ u j ∈ C ∧ Bornology.IsBounded C ∧
        diam C < ε) :
    LocallyConnectedSpace (frontier R) := by
  set M := frontier R
  have hMcl : IsClosed M := isClosed_frontier
  have hRM : ∀ z ∈ R, z ∉ M := fun z hz hzM => hzM.2 (by rw [hR.interior_eq]; exact hz)
  by_contra hnot
  have hex : ∃ P ∈ M, ¬ CikAt M P := by
    by_contra h
    push_neg at h
    exact hnot (locallyConnectedSpace_of_cikAt h)
  obtain ⟨P, hPM, hP⟩ := hex
  obtain ⟨r₁, r₂, h0, h12, t, htd, ht⟩ := exists_crossing_continua_closed hMcl hB hPM hP
  have htc : ∀ n, IsCrossA P r₁ r₂ (t n) := fun n =>
    ⟨(ht n).2.1, (ht n).1, (ht n).2.2.2.1, (ht n).2.2.2.2.1, (ht n).2.2.2.2.2⟩
  have htM : ∀ n, t n ⊆ M := fun n => (ht n).2.2.1
  obtain ⟨g, hg, V, hV⟩ := sector_cyclic h0 h12 htc htd
  set ρ := (r₁ + r₂) / 2
  set η := (r₂ - r₁) / 4
  have hη : 0 < η := by simp only [η]; linarith
  have hb : ∀ n, ∃ b ∈ t (g n), dist b P = ρ := fun n =>
    (htc (g n)).exists_dist_eq (by simp only [ρ]; linarith) (by simp only [ρ]; linarith)
  choose b hbk hbd using hb
  have hδ : ∀ n : ℕ, ∃ δ > 0, δ ≤ η ∧ δ ≤ 1 / ((n : ℝ) + 1) ∧
      (1 ≤ n → ∀ z ∈ ball (b n) δ, z ∉ t (g (n - 1)) ∪ t (g (n + 1))) := by
    intro n
    have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    by_cases hn : 1 ≤ n
    · have hKc : IsClosed (t (g (n - 1)) ∪ t (g (n + 1))) :=
        ((htc _).compact.union (htc _).compact).isClosed
      have hbK : b n ∉ t (g (n - 1)) ∪ t (g (n + 1)) := by
        rintro (h | h)
        · exact disjoint_left.1 (htd (hg.injective.ne (by omega : n ≠ n - 1))) (hbk n) h
        · exact disjoint_left.1 (htd (hg.injective.ne (by omega : n ≠ n + 1))) (hbk n) h
      obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl _ hbK
      refine ⟨min (min η (1 / ((n : ℝ) + 1))) r, lt_min (lt_min hη h1) hr,
        (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
        fun _ z hz => hrK (ball_subset_ball (min_le_right _ _) hz)⟩
    · exact ⟨min η (1 / ((n : ℝ) + 1)), lt_min hη h1, min_le_left _ _, min_le_right _ _,
        fun h => absurd h hn⟩
  choose δ hδ0 hδη hδn hδK using hδ
  have hc : ∀ n, ∃ c ∈ R, dist (b n) c < δ n := fun n =>
    Metric.mem_closure_iff.1 (frontier_subset_closure (htM _ (hbk n))) _ (hδ0 n)
  choose c hcR hcd using hc
  have hcV : ∀ n, 1 ≤ n → c n ∈ V n := by
    intro n hn
    have hsub : ball (b n) (δ n) ⊆ V n := by
      refine (hV n hn).2.2.2.2 _ (convex_ball _ _).isPreconnected (fun z hz => ⟨⟨?_, ?_⟩,
        hδK n hn z hz⟩) ⟨b n, mem_ball_self (hδ0 n), (hV n hn).1 (hbk n)⟩
      · have h1 := dist_triangle (b n) z P
        have h2 : dist (b n) z < δ n := by rw [dist_comm]; exact hz
        have := hδη n
        simp only [ρ, η] at *
        linarith [hbd n]
      · have h1 := dist_triangle z (b n) P
        have h2 : dist z (b n) < δ n := hz
        have := hδη n
        simp only [ρ, η] at *
        linarith [hbd n]
    exact hsub (by rw [mem_ball, dist_comm]; exact hcd n)
  -- a convergent subsequence of the odd-indexed points `b`
  obtain ⟨p, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (x := fun i => b (2 * i + 1))
    (isBounded_closedBall (x := P) (r := ρ)) fun i => mem_closedBall.2 (hbd _).le
  have hpM : p ∈ M := hMcl.mem_of_tendsto hlim (Eventually.of_forall fun i => htM _ (hbk _))
  set u : ℕ → Pt := fun i => c (2 * φ i + 1)
  have hut : Tendsto u atTop (𝓝 p) := by
    rw [Metric.tendsto_atTop] at hlim ⊢
    intro e he
    obtain ⟨N₁, hN₁⟩ := hlim (e / 2) (half_pos he)
    obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt (half_pos he)
    refine ⟨max N₁ N₂, fun i hi => ?_⟩
    have h1 := hN₁ i (le_of_max_le_left hi)
    have hi2 : (N₂ : ℝ) + 1 ≤ ((2 * φ i + 1 : ℕ) : ℝ) + 1 := by
      have : N₂ ≤ φ i := (le_of_max_le_right hi).trans (hφ.id_le i)
      exact_mod_cast (by omega : N₂ + 1 ≤ 2 * φ i + 1 + 1)
    have h2 : δ (2 * φ i + 1) < e / 2 :=
      (hδn _).trans_lt ((one_div_le_one_div_of_le (by positivity) hi2).trans_lt hN₂)
    have h3 := hcd (2 * φ i + 1)
    have h4 := dist_triangle (u i) (b (2 * φ i + 1)) p
    simp only [Function.comp] at h1
    rw [dist_comm] at h3
    simp only [u] at h4 ⊢
    linarith
  apply hloc p hpM η hη
  refine ⟨u, fun i => hcR _, hut, fun i j hij => ?_⟩
  rintro ⟨C, hCR, hCc, hiC, hjC, hCb, hCd⟩
  have htrap : ∀ m, 1 ≤ m → c m ∈ C → C ⊆ V m := by
    intro m hm hmC
    refine (hV m hm).2.2.2.2 C hCc (fun z hz => ⟨⟨?_, ?_⟩, ?_⟩) ⟨c m, hmC, hcV m hm⟩
    · have h1 := dist_le_diam_of_mem hCb hz hmC
      have h2 := hcd m
      have h3 := dist_triangle (b m) (c m) P
      have h4 := dist_triangle (c m) z P
      have := hδη m
      rw [dist_comm z] at h1
      simp only [ρ, η] at *
      linarith [hbd m]
    · have h1 := dist_le_diam_of_mem hCb hz hmC
      have h2 := hcd m
      have h3 := dist_triangle (c m) (b m) P
      have h4 := dist_triangle z (c m) P
      have := hδη m
      rw [dist_comm (b m)] at h2
      simp only [ρ, η] at *
      linarith [hbd m]
    · rintro (h | h) <;> exact hRM z (hCR hz) (htM _ h)
  have hm := htrap _ (by omega) hiC
  have hn := htrap _ (by omega) hjC
  have hφne : φ i ≠ φ j := hφ.injective.ne hij
  have hsep : 2 * φ j + 1 + 2 ≤ 2 * φ i + 1 ∨ 2 * φ i + 1 + 2 ≤ 2 * φ j + 1 := by omega
  exact disjoint_left.1 ((hV (2 * φ j + 1) (by omega)).2.2.2.1 (2 * φ i + 1) hsep)
    (hn hiC) (hm hiC)

/-- **Moore 1922 Theorem 4, necessity** (with the repair of the last step). A bounded connected open
plane set `R` with locally connected boundary `M` has property S.

If property S fails at `ε`, some square of a finite cover of `R̄` by squares of radius `ε/8` meets
infinitely many components `Cₙ` of `R ∩ B(x, ε/4)`; paths in `R` give continua `γₙ ⊆ Cₙ` crossing
the annulus `ε/8 ≤ d(·, x) ≤ 3ε/16`; by `sector_cyclic` each `γₙ` (`n ≥ 1`, after extraction) lies in a
piece `Vₙ` cut off by its neighbours. Walking along the middle square from `γₙ` to the first point of
a neighbour, the walk must meet `M` before reaching it (otherwise it would lie in `R` and join `Cₙ`
to a neighbouring component), at a point `zₙ ∈ M ∩ Vₙ`. *Repair:* the points `zₙ` are taken in `M`
(Moore's `Yₘ, Yₙ` lie in `R`). At a limit point `q` of the odd-indexed `zₙ`, `M` is connected im
kleinen, so two of them lie in a small connected subset of `M`, which misses every `γₙ` and so lies
in two disjoint pieces. Simple connectivity is not used. -/
theorem propertyS_of_locallyConnected {R : Set Pt} (hR : IsOpen R) (hRc : IsConnected R)
    (hRb : Bornology.IsBounded R) (hlc : LocallyConnectedSpace (frontier R)) : PropertyS R := by
  classical
  set M := frontier R
  have hMcl : IsClosed M := isClosed_frontier
  have hRM : ∀ z ∈ R, z ∉ M := fun z hz hzM => hzM.2 (by rw [hR.interior_eq]; exact hz)
  intro ε hε
  by_contra hno
  set a := ε / 8
  set b := 3 * ε / 16
  have ha : 0 < a := by positivity
  have hab : a < b := by simp only [a, b]; linarith
  have hbε : b < ε / 4 := by simp only [b]; linarith
  set 𝒞 : Pt → Set (Set Pt) := fun x =>
    {C | ∃ z ∈ R, dist z x < a ∧ C = connectedComponentIn (R ∩ ball x (ε / 4)) z}
  have hpiece : ∀ x, ∀ C ∈ 𝒞 x, IsPreconnected C ∧ Bornology.IsBounded C ∧ diam C < ε := by
    rintro x C ⟨z, -, -, rfl⟩
    have hsub : connectedComponentIn (R ∩ ball x (ε / 4)) z ⊆ closedBall x (ε / 4) :=
      (connectedComponentIn_subset _ _).trans (inter_subset_right.trans ball_subset_closedBall)
    exact ⟨isPreconnected_connectedComponentIn, isBounded_closedBall.subset hsub,
      (diam_le_of_subset_closedBall' (by positivity) hsub).trans_lt (by linarith)⟩
  obtain ⟨F, -, hFcov⟩ := hRb.isCompact_closure.elim_nhds_subcover (fun x => ball x a)
    (fun x _ => ball_mem_nhds x ha)
  have hinf : ∃ x, (𝒞 x).Infinite := by
    by_contra hfin
    simp only [not_exists, Set.not_infinite] at hfin
    apply hno
    refine ⟨F.biUnion fun x => (hfin x).toFinset, ?_, ?_⟩
    · intro A hA
      simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset] at hA
      obtain ⟨x, -, hA⟩ := hA
      exact hpiece x A hA
    · ext z
      constructor
      · intro hz
        have : z ∈ ⋃ x ∈ F, ball x a := hFcov (subset_closure hz)
        simp only [mem_iUnion] at this
        obtain ⟨x, hxF, hzx⟩ := this
        simp only [mem_iUnion]
        refine ⟨connectedComponentIn (R ∩ ball x (ε / 4)) z, ?_,
          mem_connectedComponentIn ⟨hz, ball_subset_ball (by linarith) hzx⟩⟩
        simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset]
        exact ⟨x, hxF, z, hz, hzx, rfl⟩
      · intro hz
        simp only [mem_iUnion] at hz
        obtain ⟨A, hA, hzA⟩ := hz
        simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset] at hA
        obtain ⟨x, -, w, -, -, rfl⟩ := hA
        exact (connectedComponentIn_subset _ _ hzA).1
  obtain ⟨x, hx⟩ := hinf
  set e := hx.natEmbedding
  have hRout : ∃ y ∈ R, b < dist y x := by
    by_contra h
    push_neg at h
    apply hno
    have hsub : R ⊆ closedBall x b := fun y hy => mem_closedBall.2 (h y hy)
    refine ⟨{R}, fun A hA => ?_, by simp⟩
    rw [Finset.mem_singleton] at hA
    subst hA
    exact ⟨hRc.isPreconnected, isBounded_closedBall.subset hsub,
      (diam_le_of_subset_closedBall' (by positivity) hsub).trans_lt (by simp only [b]; linarith)⟩
  obtain ⟨y, hyR, hyd⟩ := hRout
  have hpc : IsPathConnected R := hR.isConnected_iff_isPathConnected.1 hRc
  have hstep : ∀ n, ∃ T, IsCrossA x a b T ∧ T ⊆ (e n : Set Pt) := by
    intro n
    obtain ⟨z, hzR, hzd, hzC⟩ := (e n).2
    set γ := (hpc.joinedIn z hzR y hyR).somePath
    obtain ⟨T, K0, hT, hTK0, hK0, hK0c, hzK0⟩ := exists_cross_sub
      (isCompact_range γ.continuous).isClosed (isConnected_range γ.continuous).isPreconnected hab
      ⟨0, γ.source⟩ hzd ⟨1, γ.target⟩ hyd
    refine ⟨T, hT, hTK0.trans ?_⟩
    rw [hzC]
    refine hK0c.subset_connectedComponentIn hzK0 fun w hw => ⟨?_, ?_⟩
    · obtain ⟨s, hs⟩ := (hK0 hw).1
      rw [← hs]
      exact (hpc.joinedIn z hzR y hyR).somePath_mem s
    · exact mem_ball.2 ((mem_closedBall.1 (hK0 hw).2).trans_lt hbε)
  choose T hT hTC using hstep
  have hCR : ∀ n, (e n : Set Pt) ⊆ R ∩ ball x (ε / 4) := by
    intro n
    obtain ⟨z, -, -, hz⟩ := (e n).2
    rw [hz]
    exact connectedComponentIn_subset _ _
  have hRk : ∀ n, T n ⊆ R := fun n => (hTC n).trans ((hCR n).trans inter_subset_left)
  have hCdisj : ∀ m n, m ≠ n → Disjoint (e m : Set Pt) (e n) := by
    intro m n hmn
    refine disjoint_left.2 fun w hwm hwn => hmn (e.injective (Subtype.ext ?_))
    obtain ⟨z, -, -, hz⟩ := (e m).2
    obtain ⟨z', -, -, hz'⟩ := (e n).2
    rw [hz] at hwm ⊢
    rw [hz'] at hwn ⊢
    rw [connectedComponentIn_eq hwm, connectedComponentIn_eq hwn]
  have htd : Pairwise fun m n => Disjoint (T m) (T n) := fun m n hmn =>
    ((hCdisj m n hmn).mono_left (hTC m)).mono_right (hTC n)
  obtain ⟨g, hg, V, hV⟩ := sector_cyclic ha hab hT htd
  set ρ := (a + b) / 2
  have hρ : 0 < ρ := by simp only [ρ]; linarith
  set f : ℝ → Pt := fun s => Ecov x (s, ρ)
  have hfc : Continuous f := continuous_Ecov_rad x ρ
  have hfd : ∀ s, dist (f s) x = ρ := fun s => by
    simp only [f]; rw [dist_Ecov, abs_of_pos hρ]
  have hfA : ∀ s, f s ∈ Ann x a b := fun s => by
    refine ⟨?_, ?_⟩ <;> rw [hfd] <;> simp only [ρ] <;> linarith
  -- a point of the boundary in each `V n`, on the middle square
  have hz : ∀ n, 1 ≤ n → ∃ z ∈ M, z ∈ V n ∧ dist z x = ρ := by
    intro n hn
    obtain ⟨hkV, -, hVk, -, htrap⟩ := hV n hn
    obtain ⟨w, hwk, hwd⟩ := (hT (g n)).exists_dist_eq (ρ := ρ) (by simp only [ρ]; linarith)
      (by simp only [ρ]; linarith)
    obtain ⟨y', hyk, hyd'⟩ := (hT (g (n + 1))).exists_dist_eq (ρ := ρ)
      (by simp only [ρ]; linarith) (by simp only [ρ]; linarith)
    have hKc : IsClosed (T (g (n - 1)) ∪ T (g (n + 1))) :=
      ((hT _).compact.union (hT _).compact).isClosed
    have hwK : w ∉ T (g (n - 1)) ∪ T (g (n + 1)) := by
      rintro (h | h)
      · exact disjoint_left.1 (hVk (n - 1) (by omega)) (hkV hwk) h
      · exact disjoint_left.1 (hVk (n + 1) (by omega)) (hkV hwk) h
    obtain ⟨s₀, s₁, hs, hfs₀, hfs₁, hIco⟩ := sphere_walk hρ hKc hwd hwK hyd' (Or.inr hyk)
    have hwQ : w ∈ f '' Icc s₀ s₁ := ⟨s₀, left_mem_Icc.2 hs.le, hfs₀⟩
    have hQ : ∃ s ∈ Icc s₀ s₁, f s ∈ M := by
      by_contra hno'
      push_neg at hno'
      have hQc : IsPreconnected (f '' Icc s₀ s₁) := isPreconnected_Icc.image f hfc.continuousOn
      have hQsub : f '' Icc s₀ s₁ ⊆ R ∪ (closure R)ᶜ := by
        rintro _ ⟨s, hs, rfl⟩
        by_cases h : f s ∈ R
        · exact Or.inl h
        · exact Or.inr fun hcl => hno' s hs ⟨hcl, by rw [hR.interior_eq]; exact h⟩
      have hdisjR : Disjoint R (closure R)ᶜ := disjoint_compl_right.mono_left subset_closure
      rcases IsPreconnected.subset_or_subset hR isClosed_closure.isOpen_compl hdisjR hQsub hQc
        with h | h
      · have hsubB : f '' Icc s₀ s₁ ⊆ R ∩ ball x (ε / 4) := fun z hz => ⟨h hz, by
          obtain ⟨s, -, rfl⟩ := hz
          rw [mem_ball, hfd]; simp only [ρ, a, b] at *; linarith⟩
        obtain ⟨z0, -, -, hz0⟩ := (e (g n)).2
        have hw' : w ∈ connectedComponentIn (R ∩ ball x (ε / 4)) z0 := by
          rw [← hz0]; exact hTC _ hwk
        have h1 := hQc.subset_connectedComponentIn hwQ hsubB
        have hf1 : f s₁ ∈ (e (g n) : Set Pt) := by
          rw [hz0, connectedComponentIn_eq hw']
          exact h1 ⟨s₁, right_mem_Icc.2 hs.le, rfl⟩
        rcases hfs₁ with h' | h'
        · exact disjoint_left.1 (hCdisj (g n) (g (n - 1)) (hg.injective.ne (by omega))) hf1
            (hTC _ h')
        · exact disjoint_left.1 (hCdisj (g n) (g (n + 1)) (hg.injective.ne (by omega))) hf1
            (hTC _ h')
      · exact h hwQ (subset_closure (hRk _ hwk))
    obtain ⟨s, hsI, hsM⟩ := hQ
    have hss : s < s₁ := by
      refine lt_of_le_of_ne hsI.2 fun h => ?_
      rw [h] at hsM
      rcases hfs₁ with h' | h' <;> exact hRM _ (hRk _ h') hsM
    have hQ' : f '' Ico s₀ s₁ ⊆ V n := htrap _ (isPreconnected_Ico.image f hfc.continuousOn)
      (by rintro _ ⟨t, ht, rfl⟩; exact ⟨hfA t, hIco t ht⟩)
      ⟨w, ⟨s₀, left_mem_Ico.2 hs, hfs₀⟩, hkV hwk⟩
    exact ⟨f s, hsM, hQ' ⟨s, ⟨hsI.1, hss⟩, rfl⟩, hfd s⟩
  choose! z hzM hzV hzd using hz
  obtain ⟨q, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (x := fun i => z (2 * i + 1))
    (isBounded_closedBall (x := x) (r := ρ)) fun i => mem_closedBall.2 (hzd _ (by omega)).le
  have hqM : q ∈ M := hMcl.mem_of_tendsto hlim (Eventually.of_forall fun i => hzM _ (by omega))
  have hqd : dist q x = ρ :=
    (isClosed_eq (continuous_id.dist continuous_const) continuous_const).mem_of_tendsto hlim
      (Eventually.of_forall fun i => hzd _ (by omega))
  set η := (b - a) / 4
  have hη : 0 < η := by simp only [η]; linarith
  obtain ⟨δ, hδ, hδC⟩ := cikAt_of_locallyConnectedSpace hqM η hη
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) δ hδ
  obtain ⟨C₁, hC₁M, hC₁c, h1, hq1, hC₁b, hC₁d⟩ :=
    hδC (z (2 * φ N + 1)) (hzM _ (by omega)) (hN N le_rfl)
  obtain ⟨C₂, hC₂M, hC₂c, h2, hq2, hC₂b, hC₂d⟩ :=
    hδC (z (2 * φ (N + 1) + 1)) (hzM _ (by omega)) (hN (N + 1) (by omega))
  set D := C₁ ∪ C₂
  have hDc : IsPreconnected D := hC₁c.union q hq1 hq2 hC₂c
  have hDq : ∀ w ∈ D, dist w q < η := by
    rintro w (hw | hw)
    · exact (dist_le_diam_of_mem hC₁b hw hq1).trans_lt hC₁d
    · exact (dist_le_diam_of_mem hC₂b hw hq2).trans_lt hC₂d
  have hDM : D ⊆ M := union_subset hC₁M hC₂M
  have htrap' : ∀ j, 1 ≤ j → (D ∩ V j).Nonempty → D ⊆ V j := by
    intro j hj hne
    refine (hV j hj).2.2.2.2 D hDc (fun w hw => ⟨⟨?_, ?_⟩, ?_⟩) hne
    · have := hDq w hw
      have := dist_triangle q w x
      rw [dist_comm q w] at *
      simp only [ρ, η] at *
      linarith
    · have := hDq w hw
      have := dist_triangle w q x
      simp only [ρ, η] at *
      linarith
    · rintro (h | h) <;> exact hRM _ (hRk _ h) (hDM hw)
  have hm := htrap' (2 * φ N + 1) (by omega) ⟨_, Or.inl h1, hzV _ (by omega)⟩
  have hn := htrap' (2 * φ (N + 1) + 1) (by omega) ⟨_, Or.inr h2, hzV _ (by omega)⟩
  have hmn : 2 * φ N + 1 + 2 ≤ 2 * φ (N + 1) + 1 := by
    have : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
    omega
  exact disjoint_left.1 ((hV (2 * φ N + 1) (by omega)).2.2.2.1 _ (Or.inl hmn)) (hm (Or.inr hq2))
    (hn (Or.inr hq2))

/-- **Property S gives Whyburn's local condition** (the pigeonhole step, Moore 1922 p. 236: "Then
`R` is not the sum of a finite collection of connected point-sets all of diameter less than `ε`").
Of infinitely many points of `R`, two lie in the same piece of a finite cover by connected sets of
diameter `< ε`. -/
theorem hloc_of_propertyS {R : Set Pt} (hS : PropertyS R) :
    ∀ p ∈ frontier R, ∀ ε > 0, ¬ ∃ u : ℕ → Pt, (∀ n, u n ∈ R) ∧ Tendsto u atTop (𝓝 p) ∧
      ∀ i j, i ≠ j → ¬ ∃ C ⊆ R, IsPreconnected C ∧ u i ∈ C ∧ u j ∈ C ∧ Bornology.IsBounded C ∧
        diam C < ε := by
  rintro p - ε hε ⟨u, hu, -, hno⟩
  obtain ⟨s, hs, hR⟩ := hS ε hε
  have hmem : ∀ n, ∃ A : s, u n ∈ (A : Set Pt) := fun n => by
    have := hu n
    rw [hR] at this
    simp only [mem_iUnion] at this
    obtain ⟨A, hA, h⟩ := this
    exact ⟨⟨A, hA⟩, h⟩
  choose A hA using hmem
  obtain ⟨i, j, hij, hAij⟩ := Finite.exists_ne_map_eq_of_infinite A
  have hAs := hs _ (A i).2
  refine hno i j hij ⟨A i, fun z hz => ?_, hAs.1, hA i, by rw [hAij]; exact hA j, hAs.2.1, hAs.2.2⟩
  rw [hR]
  exact mem_biUnion (A i).2 hz

end HPC.Jones.Sector
