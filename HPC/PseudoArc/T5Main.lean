import HPC.PseudoArc.T5Chain
import HPC.PseudoArc.PatGeom

/-!
# Theorem 5 for descriptions

Batch 80. The choice of the deep level `m` (Bing's (P1)): at every deep enough level the links of
`D_m` within `W` positions of each other lie in one link of `D_2` (a thick reading, by
compactness), the links of `D_m` near a link meeting `d(2)_u` lie in `d(1)_h` (compactness of the
closure of `d(2)_u`, which lies in `d(1)_h`), likewise for `v`, `k`, and links meeting `d(2)_u` are
far (in index) from links meeting `d(2)_v` (their closures are disjoint). Then `T5.assemble`
applied to `D_0, D_1, D_m, D_{m+1}` gives Theorem 5 with `j = m + 1`.
-/

namespace HPC.Description

open Set Filter

variable {X : Type*} [MetricSpace X] {P Q : X}

/-- Thick readings in level `i`. -/
theorem eventually_thick_at [CompactSpace X] (Δ : Description X P Q) (i w : ℕ) :
    ∀ᶠ m in atTop, ∀ p : Fin (Δ.n m), ∃ s : Fin (Δ.n i), ∀ p' : Fin (Δ.n m),
      ((p : ℤ) - p').natAbs ≤ w → (Δ.D m).link p' ⊆ (Δ.D i).link s := by
  have hK : IsCompact (closure (Δ.D (i + 1)).union) := isClosed_closure.isCompact
  have hcov : closure (Δ.D (i + 1)).union ⊆ ⋃ s, (Δ.D i).link s :=
    Δ.closure_union_subset (by omega)
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hK (fun s => (Δ.D i).isOpen s) hcov
  have hev : ∀ᶠ m in atTop, Δ.ε m < δ / (w + 2) :=
    Δ.ε_tendsto.eventually_lt_const (by positivity)
  filter_upwards [hev, eventually_ge_atTop (i + 1)] with m hm hm1
  intro p
  obtain ⟨y, hy⟩ := (Δ.D m).link_nonempty p
  have hyK : y ∈ closure (Δ.D (i + 1)).union := by
    obtain ⟨u, hu⟩ := Δ.refines_of_le hm1 p
    exact subset_closure (mem_iUnion.mpr ⟨u, hu hy⟩)
  obtain ⟨s, hs⟩ := hleb y hyK
  refine ⟨s, fun p' hp' z hz => hs ?_⟩
  rw [Metric.mem_ball]
  have h1 := (Δ.D m).dist_le_of_mem_links' (Δ.bdd m) (Δ.diam_le m) w p' p
    (by rw [← Int.natAbs_neg]; simpa using hp') hz hy
  have h2 := Δ.ε_pos m
  have h3 : Δ.ε m * (w + 2) < δ := (lt_div_iff₀ (by positivity)).mp hm
  nlinarith

/-- **End zones.** If the closure of `A` lies in the open set `O`, then at every deep enough
level, the links within `d` positions of a link meeting `A` lie in `O`. -/
theorem eventually_zone [CompactSpace X] (Δ : Description X P Q) {A O : Set X} (hO : IsOpen O)
    (hAO : closure A ⊆ O) (d : ℕ) :
    ∀ᶠ m in atTop, ∀ q p' : Fin (Δ.n m), ((Δ.D m).link q ∩ A).Nonempty →
      ((q : ℤ) - p').natAbs ≤ d → (Δ.D m).link p' ⊆ O := by
  obtain ⟨δ, hδ, hth⟩ := isClosed_closure.isCompact.exists_thickening_subset_open hO hAO
  have hev : ∀ᶠ m in atTop, Δ.ε m < δ / (d + 2) :=
    Δ.ε_tendsto.eventually_lt_const (by positivity)
  filter_upwards [hev] with m hm
  intro q p' ⟨y, hyq, hyA⟩ hqp z hz
  apply hth
  rw [Metric.mem_thickening_iff]
  refine ⟨y, subset_closure hyA, ?_⟩
  have h1 := (Δ.D m).dist_le_of_mem_links' (Δ.bdd m) (Δ.diam_le m) d p' q
    (by rw [← Int.natAbs_neg]; simpa using hqp) hz hyq
  have h2 := Δ.ε_pos m
  have h3 : Δ.ε m * (d + 2) < δ := (lt_div_iff₀ (by positivity)).mp hm
  nlinarith

/-- **Bing 1948, Theorem 5**, for every description of a compact space. -/
theorem theorem5_of [CompactSpace X] (Δ : Description X P Q) : Theorem5Statement Δ := by
  classical
  intro N x h k u v hx huv hsub hcu hcv hdisj w
  obtain ⟨hN, hx0, hxN, hxr, hxs⟩ := hx
  have hpat : T5.Pat x h k := ⟨hN, hx0, hxN, fun t => (hxr t), hxs⟩
  have huv' : u < v := by
    rcases eq_or_lt_of_le huv with he | hlt
    · subst he
      obtain ⟨z, hz⟩ := (Δ.D 1).link_nonempty u
      exact absurd (hdisj.le_bot ⟨subset_closure hz, subset_closure hz⟩) (by simp)
    · exact hlt
  set W := 4 * (N + 2) + 10 with hWdef
  have hVc : IsOpen (closure ((Δ.D 1).link v))ᶜ := isClosed_closure.isOpen_compl
  have hUV : closure ((Δ.D 1).link u) ⊆ (closure ((Δ.D 1).link v))ᶜ :=
    fun z hz hz' => hdisj.le_bot ⟨hz, hz'⟩
  obtain ⟨m, ⟨⟨⟨⟨hthick, hzU⟩, hzV⟩, hsep⟩, hmw⟩⟩ := ((((Δ.eventually_thick_at 1 W).and
    (Δ.eventually_zone ((Δ.D 0).isOpen h) hcu (4 * W))).and
    (Δ.eventually_zone ((Δ.D 0).isOpen k) hcv (4 * W))).and
    (Δ.eventually_zone hVc hUV (10 * W))).and (eventually_ge_atTop w) |>.exists
  refine ⟨m + 1, by omega, ?_⟩
  obtain ⟨hnF, hPF, hQF, _, _⟩ := Δ.isFrom (m + 1)
  choose τ1 hτ1 using hthick
  choose σ0 hσ0 using fun t => Δ.closure_subset m t
  have hσ0' : ∀ t, (Δ.D (m + 1)).link t ⊆ (Δ.D m).link (σ0 t) :=
    fun t => subset_closure.trans (hσ0 t)
  choose ρ0 hρ0 using hsub
  let ρ : Fin (Δ.n 1) → Fin (Δ.n 0) := fun t => if ht : u < t ∧ t < v then
    ρ0 t ht.1.le ht.2.le else h
  have hhk : h ≤ k := (hxr ⟨0, hN⟩).1.trans (hxr ⟨0, hN⟩).2
  have H : T5.Setup (Δ.D 0) (Δ.D 1) (Δ.D m) (Δ.D (m + 1)) h k u v W σ0 τ1 ρ :=
    { hk := hhk
      σ0_sub := hσ0'
      thick := hτ1
      ρ_sub := fun t h1 h2 => by
        simp only [ρ, dif_pos (And.intro h1 h2)]
        exact (hρ0 t h1.le h2.le).2.2
      ρ_range := fun t => by
        simp only [ρ]
        split_ifs with ht
        · exact ⟨(hρ0 t ht.1.le ht.2.le).1, (hρ0 t ht.1.le ht.2.le).2.1⟩
        · exact ⟨le_rfl, hhk⟩
      zoneU := hzU
      zoneV := hzV
      sep := fun q q' hq hq' => by
        by_contra hcon
        push_neg at hcon
        obtain ⟨z, hz1, hz2⟩ := hq'
        exact hsep q q' hq hcon hz1 (subset_closure hz2) }
  have hS : PatCore.Setting (T5.sigN σ0 hnF) (Δ.n (m + 1) - 1) :=
    Chain.setting_of_crooked (Δ.crooked m) σ0 hσ0' hnF
  obtain ⟨σ1, hσ1⟩ : ∃ σ1 : Fin (Δ.n (m + 1)) → Fin (Δ.n 1),
      ∀ t, (Δ.D (m + 1)).link t ⊆ (Δ.D 1).link (σ1 t) :=
    ⟨fun t => (Δ.refines_of_le (show 1 ≤ m + 1 by omega) t).choose,
      fun t => (Δ.refines_of_le (show 1 ≤ m + 1 by omega) t).choose_spec⟩
  obtain ⟨E, hE1, hE2, hE3, -, -⟩ := T5.assemble H hnF hS hpat le_rfl (Δ.isFrom (m + 1))
    (Δ.isFrom 1) σ1 hσ1 huv'
  exact ⟨E, hE1, hE2, hE3⟩

end HPC.Description
