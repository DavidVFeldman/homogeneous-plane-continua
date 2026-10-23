import HPC.Jones.Jones75L

/-!
# Batch 189: Jones 1975 I — arcs and lines; no small reversal; recurrence

Source: F. B. Jones, *Use of a new technique in homogeneous continua*, Houston J. Math. 1 (1975),
57–61 (notes `doc/notes/jones75.md`). Route: commission 189.

The skeleton of batch 189, split over four files under `HPC/Jones/`:

| skeleton item | here |
|---|---|
| §1 `JonesSetting`, `jonesSetting_of_plane` | `Jones75Arcs.lean` |
| §2.1 `JonesSetting.union_arc`, `JonesSetting.nested` | `Jones75Arcs.lean` |
| §2.2 `JonesSetting.exists_arc_through` | `Jones75Arcs.lean` |
| §2.3 `arcComp`, `IsLine`, `JonesSetting.exists_line` | `Jones75Line.lean` |
| §2.4 `JonesSetting.line_arc`, `JonesSetting.homeo_on_line` | `Jones75Rev.lean` |
| §3 `JonesSetting.no_reversal_arc`, `exists_no_reversal`, `orientation` | `Jones75Rev.lean` |
| §4 `omegaLim`, `IsArcSaturated`, `omegaLim_saturated`, `line_recurrent`, `jones75_d` | here |
| §5 (L): `JonesSetting.no_backtrack`, `no_backtrack_in_collar` | `Jones75L.lean` |

§2–§4 are stated for a compact metric space `Y` under the hypotheses that Jones's (a)–(c) and the
Effros corollary provide (`JonesSetting`), not for a plane continuum. Planarity is used only from §5
on. The dyadic solenoid satisfies `JonesSetting` (not formalized), so §2–§4 are not vacuous.

Shape changes (recorded in the report): `JonesSetting.line_arc` takes `IsLine ℓ` and no longer
the unused `JonesSetting Y`; `JonesSetting.no_reversal_arc` no longer takes the unused hypothesis
`A ∩ C = {p}`; §5 (L), whose shape was left open, is stated in two forms (`Jones75L.lean`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section General

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]

/-! ## §4. Recurrence (replaces the second half of Jones (d)) -/

/-- The forward limit set of a line. -/
def omegaLim (ℓ : ℝ → Y) : Set Y := ⋂ t : ℝ, closure (ℓ '' Ici t)

/-- A set is *arc-saturated* if it contains the arc component of each of its points. -/
def IsArcSaturated (Z : Set Y) : Prop := ∀ x ∈ Z, arcComp x ⊆ Z

omit [CompactSpace Y] in
theorem mem_omegaLim_iff {ℓ : ℝ → Y} {z : Y} :
    z ∈ omegaLim ℓ ↔ ∀ T, ∀ ε > 0, ∃ u ≥ T, dist (ℓ u) z < ε := by
  simp only [omegaLim, mem_iInter, Metric.mem_closure_iff]
  constructor
  · intro h T ε hε
    obtain ⟨_, ⟨u, hu, rfl⟩, hd⟩ := h T ε hε
    exact ⟨u, hu, by rw [dist_comm]; exact hd⟩
  · intro h T ε hε
    obtain ⟨u, hu, hd⟩ := h T ε hε
    exact ⟨_, ⟨u, hu, rfl⟩, by rw [dist_comm]; exact hd⟩

/-- **§4.1**: limit sets are arc-saturated (Effros). -/
theorem JonesSetting.omegaLim_saturated (S : JonesSetting Y) {ℓ : ℝ → Y} (hℓ : IsLine ℓ) :
    IsArcSaturated (omegaLim ℓ) := by
  intro z hz y hy
  obtain ⟨lam, hlam, hlam0⟩ := S.exists_line z
  have hyr : y ∈ range lam := by rw [hlam.2.2, hlam0]; exact hy
  obtain ⟨s, rfl⟩ := hyr
  rw [mem_omegaLim_iff] at hz ⊢
  intro T ε hε
  set K := lam '' uIcc 0 s with hK
  have hKc : IsCompact K := isCompact_uIcc.image hlam.1
  -- the line `ℓ` is not eventually inside the compact arc `K`
  have hv : ∃ v ≥ T, ℓ v ∉ K := by
    by_contra hno
    push_neg at hno
    obtain ⟨r, -, hr⟩ := hno T le_rfl
    obtain ⟨χ, hχc, -, -, hχ⟩ := S.homeo_on_line_gen hlam hℓ (Homeomorph.refl Y) (s₀ := r)
      (by rw [Homeomorph.refl_apply, hr]; exact mem_range_self T)
    obtain ⟨B, hB⟩ := (isCompact_uIcc.image hχc).bddAbove
    obtain ⟨r', hr', hr'e⟩ := hno (max T (B + 1)) (le_max_left _ _)
    have h1 : χ r' = max T (B + 1) := hℓ.2.1 ((hχ r').symm.trans hr'e)
    have h2 := hB (mem_image_of_mem χ hr')
    linarith [le_max_right T (B + 1)]
  obtain ⟨v, hvT, hvK⟩ := hv
  have hη : 0 < infDist (ℓ v) K :=
    (infDist_pos_iff_notMem_closure ⟨lam 0, mem_image_of_mem _ left_mem_uIcc⟩).1
      (hKc.isClosed.closure_eq.symm ▸ hvK)
  obtain ⟨δ, hδ, hEff⟩ := HPC.Effros.effros_homogeneous S.hom (lt_min hε hη)
  obtain ⟨u, hu, hud⟩ := hz v δ hδ
  obtain ⟨h, hhz, hhsmall⟩ := hEff z (ℓ u) (by rw [dist_comm]; exact hud)
  obtain ⟨ψ, hψc, -, -, hψ⟩ :=
    S.homeo_on_line hlam hℓ h (by rw [hlam0, hhz]; exact mem_range_self u)
  have hψ0 : ψ 0 = u := hℓ.2.1 (by rw [← hψ, hlam0, hhz])
  refine ⟨ψ s, ?_, ?_⟩
  · by_contra hlt
    push_neg at hlt
    have hvmem : v ∈ uIcc (ψ 0) (ψ s) := by
      rw [hψ0, mem_uIcc]; right; exact ⟨by linarith, hu⟩
    obtain ⟨r, hr, hrv⟩ := intermediate_value_uIcc hψc.continuousOn hvmem
    have h1 := hhsmall (lam r)
    rw [hψ, hrv] at h1
    have h2 := infDist_le_dist_of_mem (x := ℓ v) (mem_image_of_mem lam hr)
    have h3 := min_le_right ε (infDist (ℓ v) K)
    linarith
  · have := hhsmall (lam s)
    rw [hψ] at this
    exact this.trans_le (min_le_left _ _)

/-- **§4.2**, at the base point: `ℓ 0` lies in the forward limit set (Effros with
`ε = ½ d(ℓ(0), ω(ℓ))`). -/
theorem JonesSetting.zero_mem_omegaLim (S : JonesSetting Y) {ℓ : ℝ → Y} (hℓ : IsLine ℓ) :
    ℓ 0 ∈ omegaLim ℓ := by
  set K := omegaLim ℓ with hKdef
  have hKc : IsClosed K := isClosed_iInter fun _ => isClosed_closure
  have hKne : K.Nonempty := by
    apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    · exact fun a b => ⟨max a b, closure_mono (image_mono (Ici_subset_Ici.2 (le_max_left _ _))),
        closure_mono (image_mono (Ici_subset_Ici.2 (le_max_right _ _)))⟩
    · exact fun t => ⟨ℓ t, subset_closure (mem_image_of_mem _ self_mem_Ici)⟩
    · exact fun t => isClosed_closure.isCompact
    · exact fun _ => isClosed_closure
  by_contra h0
  have hη : 0 < infDist (ℓ 0) K :=
    (infDist_pos_iff_notMem_closure hKne).1 (hKc.closure_eq.symm ▸ h0)
  obtain ⟨δ, hδ, hEff⟩ := HPC.Effros.effros_homogeneous S.hom (half_pos hη)
  obtain ⟨p, hp⟩ := hKne
  have hp' := hp
  rw [hKdef, mem_omegaLim_iff] at hp'
  obtain ⟨t, -, ht⟩ := hp' 0 δ hδ
  obtain ⟨g, hg, hgsmall⟩ := hEff (ℓ t) p ht
  have hg0 : g (ℓ 0) ∈ K := by
    apply S.omegaLim_saturated hℓ p hp
    rw [← hg, ← image_arcComp]
    refine mem_image_of_mem g ?_
    rw [← hℓ.range_eq t]; exact mem_range_self 0
  have h1 := infDist_le_dist_of_mem (x := ℓ 0) hg0
  have h2 := hgsmall (ℓ 0)
  rw [dist_comm] at h2
  linarith

omit [CompactSpace Y] in
theorem omegaLim_shift (ℓ : ℝ → Y) (c : ℝ) : omegaLim (fun s => ℓ (s + c)) = omegaLim ℓ := by
  ext z
  simp only [mem_omegaLim_iff]
  constructor
  · intro h T ε hε
    obtain ⟨u, hu, hd⟩ := h (T - c) ε hε
    exact ⟨u + c, by linarith, hd⟩
  · intro h T ε hε
    obtain ⟨u, hu, hd⟩ := h (T + c) ε hε
    exact ⟨u - c, by linarith, by simpa using hd⟩

/-- **§4.2**: every line lies in its own forward limit set (commission 189 §4.2: Effros with
`ε = ½ d(ℓ(0), ω(ℓ))`). -/
theorem JonesSetting.line_recurrent (S : JonesSetting Y) {ℓ : ℝ → Y} (hℓ : IsLine ℓ) :
    range ℓ ⊆ omegaLim ℓ := by
  rintro _ ⟨c, rfl⟩
  have := S.zero_mem_omegaLim (hℓ.shift c)
  simpa [omegaLim_shift] using this

/-- **§4.3, Jones (d), second sentence** (\"every point of `ab` is a limit point of `T − ab`\"), for
every line and both directions. -/
theorem JonesSetting.jones75_d (S : JonesSetting Y) {ℓ : ℝ → Y} (hℓ : IsLine ℓ) (s : ℝ) :
    ℓ '' Iic s ⊆ closure (ℓ '' Ioi s) ∧ ℓ '' Ici s ⊆ closure (ℓ '' Iio s) := by
  constructor
  · rintro _ ⟨v, -, rfl⟩
    have := mem_iInter.1 (S.line_recurrent hℓ (mem_range_self v)) (s + 1)
    refine closure_mono (image_mono fun w hw => ?_) this
    simp only [mem_Ici] at hw
    simp only [mem_Ioi]
    linarith
  · rintro _ ⟨v, -, rfl⟩
    have h2 := mem_iInter.1 (S.line_recurrent hℓ.neg (mem_range_self (-v))) (-s + 1)
    simp only [neg_neg] at h2
    refine closure_mono ?_ h2
    rintro _ ⟨w, hw, rfl⟩
    simp only [mem_Ici] at hw
    exact ⟨-w, by simp only [mem_Iio]; linarith, rfl⟩

end General

/-! ## §5. In the plane: (L), no backtracking near an arc of a line

Proved in `Jones75L.lean`: `JonesSetting.no_backtrack` (abstract coordinate, metric strip) and
`no_backtrack_in_collar` (the collar form of commission 189 §5). -/

/-! ## §6. The planar contradiction: reconnaissance only (commission 189 §6)

Target, for a later batch: `jones75_noArc : NoArcIndecHomPlane`. The hand proof and the skeleton
proposal are in `doc/batches/REPORT-batch189.md` §6. -/

end HPC.Hagopian
