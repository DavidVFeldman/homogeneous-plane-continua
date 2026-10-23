import HPC.PseudoArc.T5Main

/-!
# Batch 115: Theorem 5 with an arbitrary coarse chain and the end clauses

Auxiliary file for `HPC/PseudoArc/Thm14.lean` (COMMISSION-batch115.md, item 3). The proof of
`Description.theorem5_of` never uses that Bing's `D_1` (the coarse chain, `Δ.D 0`) is a level of
the description, nor that it is a chain from `P` to `Q`: only that it is a chain of open sets into
whose links the stretch `D_2(u, v)` fits and whose links `d(1)_h`, `d(1)_k` contain the closures of
`d(2)_u`, `d(2)_v`. So the coarse chain may be any chain `C` and Bing's `D_2` any level `Δ.D i`.
This replaces the *thinned description* of the commission (levels `C, D_a, D_{a+1}, …`), and it
allows `C` to be *reversed*, which the stretch `R → A` of the three-piece follower needs (there the
pattern runs from `ρ` down to `0`, and `IsPatternFromTo` asks for `h ≤ k`).

Two further conclusions are recorded, read off the construction of `T5.assemble` (extended for
this in `T5Chain.lean`): every link of `D_j` in the stretch meeting `d(2)_u` lies in the *first*
link of `E`, every one meeting `d(2)_v` in the *last*. And the level `j` may be any deep enough
level (`∀ᶠ j in atTop`), so that three applications can share one level.
-/

namespace HPC.Description

open Set Filter

variable {X : Type*} [MetricSpace X] {P Q : X}

/-- **Theorem 5, general form.** `C` is any chain (Bing's `D_1`), `Δ.D i` any level (Bing's
`D_2`). For every deep enough level `j` there is a chain `E` following `x` in `C`, a consolidation
of the links of `D_j` lying in links of `D_i(u, v)`, with no interior link meeting
`d_i(u) ∪ d_i(v)`, whose first link contains every such link of `D_j` meeting `d_i(u)` and whose
last link contains every such link meeting `d_i(v)`. -/
theorem theorem5_gen [CompactSpace X] (Δ : Description X P Q) {n0 : ℕ} (C : Chain X n0)
    (i : ℕ) {N : ℕ} (x : Fin N → Fin n0) (h k : Fin n0) (u v : Fin (Δ.n i))
    (hx : IsPatternFromTo x h k) (huv : u ≤ v)
    (hsub : ∀ t : Fin (Δ.n i), u ≤ t → t ≤ v → ∃ s : Fin n0, h ≤ s ∧ s ≤ k ∧
      (Δ.D i).link t ⊆ C.link s)
    (hcu : closure ((Δ.D i).link u) ⊆ C.link h) (hcv : closure ((Δ.D i).link v) ⊆ C.link k)
    (hdisj : Disjoint (closure ((Δ.D i).link u)) (closure ((Δ.D i).link v))) :
    ∀ᶠ j in atTop, ∃ E : Chain X N, E.FollowsPattern x C ∧
      E.IsConsolidationOn (Δ.D j)
        {t | ∃ s : Fin (Δ.n i), u ≤ s ∧ s ≤ v ∧ (Δ.D j).link t ⊆ (Δ.D i).link s} ∧
      (∀ e : Fin N, 0 < e.val → e.val < N - 1 →
        Disjoint (E.link e) ((Δ.D i).link u ∪ (Δ.D i).link v)) ∧
      (∀ t, (∃ s : Fin (Δ.n i), u ≤ s ∧ s ≤ v ∧ (Δ.D j).link t ⊆ (Δ.D i).link s) →
        ((Δ.D j).link t ∩ (Δ.D i).link u).Nonempty → (Δ.D j).link t ⊆ E.link ⟨0, hx.1⟩) ∧
      (∀ t, (∃ s : Fin (Δ.n i), u ≤ s ∧ s ≤ v ∧ (Δ.D j).link t ⊆ (Δ.D i).link s) →
        ((Δ.D j).link t ∩ (Δ.D i).link v).Nonempty →
          (Δ.D j).link t ⊆ E.link ⟨N - 1, by have := hx.1; omega⟩) := by
  classical
  obtain ⟨hN, hx0, hxN, hxr, hxs⟩ := hx
  have hpat : T5.Pat x h k := ⟨hN, hx0, hxN, fun t => (hxr t), hxs⟩
  have huv' : u < v := by
    rcases eq_or_lt_of_le huv with he | hlt
    · subst he
      obtain ⟨z, hz⟩ := (Δ.D i).link_nonempty u
      exact absurd (hdisj.le_bot ⟨subset_closure hz, subset_closure hz⟩) (by simp)
    · exact hlt
  set W := 4 * (N + 2) + 10 with hWdef
  have hVc : IsOpen (closure ((Δ.D i).link v))ᶜ := isClosed_closure.isOpen_compl
  have hUV : closure ((Δ.D i).link u) ⊆ (closure ((Δ.D i).link v))ᶜ :=
    fun z hz hz' => hdisj.le_bot ⟨hz, hz'⟩
  have hev := ((((Δ.eventually_thick_at i W).and
    (Δ.eventually_zone (C.isOpen h) hcu (4 * W))).and
    (Δ.eventually_zone (C.isOpen k) hcv (4 * W))).and
    (Δ.eventually_zone hVc hUV (10 * W))).and (eventually_ge_atTop i)
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp hev
  refine eventually_atTop.mpr ⟨M0 + 1, fun j hj => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  obtain ⟨⟨⟨⟨hthick, hzU⟩, hzV⟩, hsep⟩, hmi⟩ := hM0 m (by omega)
  obtain ⟨hnF, hPF, hQF, _, _⟩ := Δ.isFrom (m + 1)
  choose τ1 hτ1 using hthick
  choose σ0 hσ0 using fun t => Δ.closure_subset m t
  have hσ0' : ∀ t, (Δ.D (m + 1)).link t ⊆ (Δ.D m).link (σ0 t) :=
    fun t => subset_closure.trans (hσ0 t)
  choose ρ0 hρ0 using hsub
  let ρ : Fin (Δ.n i) → Fin n0 := fun t => if ht : u < t ∧ t < v then
    ρ0 t ht.1.le ht.2.le else h
  have hhk : h ≤ k := (hxr ⟨0, hN⟩).1.trans (hxr ⟨0, hN⟩).2
  have H : T5.Setup C (Δ.D i) (Δ.D m) (Δ.D (m + 1)) h k u v W σ0 τ1 ρ :=
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
  obtain ⟨σ1, hσ1⟩ : ∃ σ1 : Fin (Δ.n (m + 1)) → Fin (Δ.n i),
      ∀ t, (Δ.D (m + 1)).link t ⊆ (Δ.D i).link (σ1 t) :=
    ⟨fun t => (Δ.refines_of_le (show i ≤ m + 1 by omega) t).choose,
      fun t => (Δ.refines_of_le (show i ≤ m + 1 by omega) t).choose_spec⟩
  obtain ⟨E, hE1, hE2, hE3, hE4, hE5⟩ := T5.assemble H hnF hS hpat le_rfl (Δ.isFrom (m + 1))
    (Δ.isFrom i) σ1 hσ1 huv'
  exact ⟨E, hE1, hE2, hE3, hE4, hE5⟩

end HPC.Description
