import HPC.PseudoArc.PatMain
import HPC.PseudoArc.Statements79
import HPC.Chains.Consolidation

/-!
# Pattern following: from the combinatorial core to chains

Batch 80. The geometric half of the proof of Bing's Theorem 6: the core theorem
`HPC.PatCore.realize` is applied to

* the reading `σ` of a fine level `F = D (m + 1)` in the level `R = D m` above it (crooked,
  because `F` is crooked in `R`), and
* a *thick* reading `τ` of `R` in the first level `D 0`: every link of `R` within `w` positions
  of position `p` lies in the link `τ p` of `D 0`. Thick readings exist for all large `m`, by
  compactness (a Lebesgue number for the cover of `closure (D 1).union` by the links of `D 0`)
  and because the mesh tends to zero.

The lift produced by `realize` is a block map, and the block consolidation of `F` it defines is
the chain asked for by Theorem 6.
-/

namespace HPC

open Set Filter

variable {X : Type*} [MetricSpace X]

namespace Chain

/-- Points of links at index distance `k` are at distance at most `(k + 1) ε` when every link has
diameter at most `ε`. -/
theorem dist_le_of_mem_links {n : ℕ} (D : Chain X n) {ε : ℝ}
    (hb : ∀ t, Bornology.IsBounded (D.link t)) (hd : ∀ t, Metric.diam (D.link t) ≤ ε) :
    ∀ (k : ℕ) (i j : Fin n), j.val = i.val + k → ∀ y ∈ D.link i, ∀ z ∈ D.link j,
      dist y z ≤ (k + 1) * ε := by
  intro k
  induction k with
  | zero =>
    intro i j hij y hy z hz
    have : j = i := Fin.ext (by omega)
    subst this
    simpa using (Metric.dist_le_diam_of_mem (hb j) hy hz).trans (hd j)
  | succ k ih =>
    intro i j hij y hy z hz
    let j' : Fin n := ⟨i.val + k, by omega⟩
    obtain ⟨u, hu1, hu2⟩ := (D.adjacent_iff j' j).mpr (by simp only [j']; omega)
    have h1 := ih i j' rfl y hy u hu1
    have h2 := (Metric.dist_le_diam_of_mem (hb j) hu2 hz).trans (hd j)
    calc dist y z ≤ dist y u + dist u z := dist_triangle _ _ _
      _ ≤ (k + 1) * ε + ε := by linarith
      _ = ((k + 1 : ℕ) + 1) * ε := by push_cast; ring

/-- Symmetric form of `dist_le_of_mem_links`. -/
theorem dist_le_of_mem_links' {n : ℕ} (D : Chain X n) {ε : ℝ}
    (hb : ∀ t, Bornology.IsBounded (D.link t)) (hd : ∀ t, Metric.diam (D.link t) ≤ ε)
    (k : ℕ) (i j : Fin n) (hij : ((i : ℤ) - j).natAbs ≤ k) {y z : X} (hy : y ∈ D.link i)
    (hz : z ∈ D.link j) : dist y z ≤ (k + 1) * ε := by
  have hε : 0 ≤ ε := Metric.diam_nonneg.trans (hd i)
  rcases le_total i.val j.val with h | h
  · have := D.dist_le_of_mem_links hb hd (j.val - i.val) i j (by omega) y hy z hz
    calc dist y z ≤ ((j.val - i.val : ℕ) + 1) * ε := this
      _ ≤ (k + 1) * ε := by
        gcongr
        exact_mod_cast (show j.val - i.val ≤ k by omega)
  · have := D.dist_le_of_mem_links hb hd (i.val - j.val) j i (by omega) z hz y hy
    rw [dist_comm]
    calc dist z y ≤ ((i.val - j.val : ℕ) + 1) * ε := this
      _ ≤ (k + 1) * ε := by
        gcongr
        exact_mod_cast (show i.val - j.val ≤ k by omega)

/-- The reading of a crooked chain `F` in `R` (clamped to `ℕ`) satisfies the hypotheses
`HPC.PatCore.Setting` of the combinatorial core. -/
theorem setting_of_crooked {nF nR : ℕ} {F : Chain X nF} {R : Chain X nR}
    (hc : F.IsCrookedIn' R) (σ0 : Fin nF → Fin nR) (hσ : ∀ t, F.link t ⊆ R.link (σ0 t))
    (hnF : 0 < nF) :
    PatCore.Setting (fun f => ((σ0 ⟨min f (nF - 1), by omega⟩ : Fin nR) : ℤ)) (nF - 1) := by
  have hv : ∀ g (hg : g < nF), (⟨min g (nF - 1), by omega⟩ : Fin nF) = ⟨g, hg⟩ :=
    fun g hg => Fin.ext (by simp only; omega)
  have hnear : ∀ (t : Fin nF) (s : Fin nR), F.link t ⊆ R.link s →
      ((σ0 t : ℤ) - (s : ℤ)).natAbs ≤ 1 := by
    intro t s hts
    obtain ⟨z, hz⟩ := F.link_nonempty t
    exact (R.adjacent _ _).mp ⟨z, hσ t hz, hts hz⟩
  constructor
  · intro f
    have := pattern_lipschitz hσ ⟨min (f + 1) (nF - 1), by omega⟩ ⟨min f (nF - 1), by omega⟩
      ((F.adjacent_iff _ _).mpr (by simp only; omega))
    rw [abs_le]; omega
  · intro f f' hff' hf' h3
    rw [hv f (by omega), hv f' (by omega)] at h3 ⊢
    set a : Fin nF := ⟨f, by omega⟩
    set b : Fin nF := ⟨f', by omega⟩
    have hab : a < b := by simp only [a, b, Fin.mk_lt_mk]; exact hff'
    have hne : ∀ t : Fin nF, (F.link t ∩ R.link (σ0 t)).Nonempty := by
      intro t
      obtain ⟨z, hz⟩ := F.link_nonempty t
      exact ⟨z, hz, hσ t hz⟩
    have hsv : ∀ t : Fin nF,
        ((σ0 ⟨min t.val (nF - 1), by omega⟩ : Fin nR) : ℤ) = (σ0 t : ℤ) := by
      intro t; rw [hv t.val t.isLt]
    rcases (show (σ0 a : ℕ) + 2 < σ0 b ∨ (σ0 b : ℕ) + 2 < σ0 a by
        rw [le_abs'] at h3; omega) with hlt | hlt
    · obtain ⟨r, s, hbtw, hr, hs⟩ := hc.2 (σ0 a) (σ0 b) hlt a b (hne a) (hne b)
      rcases hbtw with ⟨h1, h2, h3'⟩ | ⟨h1, h2, h3'⟩
      · refine ⟨r.val, s.val, h1, h2, h3', ?_, ?_⟩
        · rw [hsv r]; have := hnear r _ hr; simp only at this; rw [abs_le]; omega
        · rw [hsv s]; have := hnear s _ hs; simp only at this; rw [abs_le]; omega
      · exact absurd (h3'.trans (h2.trans h1)) (not_lt.mpr hab.le)
    · obtain ⟨r, s, hbtw, hr, hs⟩ := hc.2 (σ0 b) (σ0 a) hlt b a (hne b) (hne a)
      rcases hbtw with ⟨h1, h2, h3'⟩ | ⟨h1, h2, h3'⟩
      · exact absurd (h1.trans (h2.trans h3')) (not_lt.mpr hab.le)
      · refine ⟨s.val, r.val, h3', h2, h1, ?_, ?_⟩
        · rw [hsv s]; have := hnear s _ hs; simp only at this; rw [abs_le]; omega
        · rw [hsv r]; have := hnear r _ hr; simp only at this; rw [abs_le]; omega

/-- A lift `φ` of the links of a chain `F` from `P` to `Q` into a pattern `x` in `D0`, moving by
at most one, from the first to the last index, defines a block consolidation of `F` which is a
chain from `P` to `Q` following `x` in `D0`. -/
theorem exists_consolidation_of_lift {nF N n0 : ℕ} {P Q : X} (F : Chain X nF) (D0 : Chain X n0)
    (hF : F.IsFrom P Q) (x : Fin N → Fin n0) (φ : ℕ → ℕ) (h0 : φ 0 = 0)
    (hT : φ (nF - 1) = N - 1)
    (hstep : ∀ f, f < nF - 1 → (φ (f + 1) : ℤ) - φ f ≤ 1 ∧ (φ f : ℤ) - φ (f + 1) ≤ 1)
    (hle : ∀ f, f < nF → φ f < N)
    (hsub : ∀ f (hf : f < nF), F.link ⟨f, hf⟩ ⊆ D0.link (x ⟨φ f, hle f hf⟩)) :
    ∃ E : Chain X N, E.IsFrom P Q ∧ E.IsConsolidationOf F ∧ E.FollowsPattern x D0 := by
  obtain ⟨hnF, hP0, hQ1, hPu, hQu⟩ := hF
  have hN : 0 < N := by have := hle 0 hnF; omega
  let β : Fin nF → Fin N := fun f => ⟨φ f, hle f f.2⟩
  have hβ : IsBlockMap β := by
    constructor
    · intro e
      have hg : ∀ k, |(φ (min (k + 1) (nF - 1)) : ℤ) - φ (min k (nF - 1))| ≤ 1 := by
        intro k
        by_cases hk : k < nF - 1
        · rw [min_eq_left (by omega), min_eq_left (by omega)]
          have := hstep k hk; rw [abs_le]; omega
        · rw [min_eq_right (by omega), min_eq_right (by omega)]; simp
      obtain ⟨j, -, hj⟩ := PatCore.ivt_nat (fun k => (φ (min k (nF - 1)) : ℤ)) hg (nF - 1) e
        (Or.inl ⟨by simp [h0], by simp only [min_self, hT]; have := e.isLt; omega⟩)
      refine ⟨⟨min j (nF - 1), by omega⟩, Fin.ext ?_⟩
      simp only [β]; exact_mod_cast hj
    · intro t t' htt'
      have := hstep t (by have := t'.isLt; omega)
      simp only [β, htt']; omega
  refine ⟨F.ofBlocks β hβ, ?_, ofBlocks_isConsolidationOf _ _ _, ?_⟩
  · have hb0 : β ⟨0, hnF⟩ = ⟨0, hN⟩ := Fin.ext (by simp [β, h0])
    have hbT : β ⟨nF - 1, by omega⟩ = ⟨N - 1, by omega⟩ := Fin.ext (by simp [β, hT])
    refine ⟨hN, ?_, ?_, ?_, ?_⟩
    · rw [ofBlocks_link]; exact mem_biUnion (show _ ∈ {t | β t = _} from hb0) hP0
    · rw [ofBlocks_link]; exact mem_biUnion (show _ ∈ {t | β t = _} from hbT) hQ1
    · intro e he
      rw [ofBlocks_link, mem_iUnion₂] at he
      obtain ⟨t, ht, hPt⟩ := he
      have := hPu t hPt
      subst this
      rw [← hb0]; exact ht.symm
    · intro e he
      rw [ofBlocks_link, mem_iUnion₂] at he
      obtain ⟨t, ht, hQt⟩ := he
      have := hQu t hQt
      subst this
      rw [← hbT]; exact ht.symm
  · intro e z hz
    rw [ofBlocks_link, mem_iUnion₂] at hz
    obtain ⟨t, ht, hzt⟩ := hz
    have ht' : β t = e := ht
    subst ht'
    exact hsub t.val t.isLt hzt

end Chain

namespace Description

variable {P Q : X}

/-- **Thick readings.** For every `w`, at every deep enough level `m`, each position `p` has a
link of `D 0` containing all links of `D m` within `w` positions of `p`. -/
theorem eventually_thick [CompactSpace X] (Δ : Description X P Q) (w : ℕ) :
    ∀ᶠ m in atTop, ∀ p : Fin (Δ.n m), ∃ s : Fin (Δ.n 0), ∀ p' : Fin (Δ.n m),
      ((p : ℤ) - p').natAbs ≤ w → (Δ.D m).link p' ⊆ (Δ.D 0).link s := by
  have hK : IsCompact (closure (Δ.D 1).union) := isClosed_closure.isCompact
  have hcov : closure (Δ.D 1).union ⊆ ⋃ s, (Δ.D 0).link s :=
    Δ.closure_union_subset (by norm_num)
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hK (fun s => (Δ.D 0).isOpen s) hcov
  have hev : ∀ᶠ m in atTop, Δ.ε m < δ / (w + 2) :=
    Δ.ε_tendsto.eventually_lt_const (by positivity)
  filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
  intro p
  obtain ⟨y, hy⟩ := (Δ.D m).link_nonempty p
  have hyK : y ∈ closure (Δ.D 1).union := by
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

/-- **Theorem 6 with `j > 0`**, for every description with `P ≠ Q` of a compact space. -/
theorem theorem6Pos_of_ne [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q) :
    Theorem6PosStatement Δ := by
  intro N x hx
  obtain ⟨hN, hm0, hx0, hxT, hxs⟩ := hx
  obtain ⟨m, hmthick, hmN⟩ := ((Δ.eventually_thick (4 * N + 10)).and
    (((Δ.n_tendsto_atTop hPQ).comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop N)).exists
  simp only [Function.comp] at hmN
  refine ⟨m + 1, by omega, ?_⟩
  obtain ⟨hnR, hPR, hQR, hPRu, hQRu⟩ := Δ.isFrom m
  obtain ⟨hnF, hPF, hQF, -, -⟩ := Δ.isFrom (m + 1)
  obtain ⟨hn0, hP0, hQ0, hP0u, hQ0u⟩ := Δ.isFrom 0
  choose τ0 hτ0 using hmthick
  choose σ0 hσ0 using fun t => Δ.closure_subset m t
  have hσ0' : ∀ t, (Δ.D (m + 1)).link t ⊆ (Δ.D m).link (σ0 t) :=
    fun t => subset_closure.trans (hσ0 t)
  let cl : ℤ → Fin (Δ.n m) := fun p => ⟨min p.toNat (Δ.n m - 1), by omega⟩
  let τ : ℤ → ℤ := fun p => (τ0 (cl p) : ℤ)
  let σ : ℕ → ℤ := fun f => (σ0 ⟨min f (Δ.n (m + 1) - 1), by omega⟩ : ℤ)
  let x' : ℕ → ℤ := fun i => (x ⟨min i (N - 1), by omega⟩ : ℤ)
  have hcl : ∀ q : Fin (Δ.n m), cl q = q := fun q => Fin.ext (by simp only [cl]; omega)
  have hcld : ∀ p p' : ℤ, |p - p'| ≤ (4 * N + 10 : ℕ) →
      (((cl p : Fin (Δ.n m)) : ℤ) - (cl p' : Fin (Δ.n m))).natAbs ≤ 4 * N + 10 := by
    intro p p' h; rw [abs_le] at h; simp only [cl]; omega
  have hslow : PatCore.Slow (4 * N + 10) τ := by
    intro p p' hpp'
    have h1 := hτ0 (cl p) (cl p') (hcld p p' hpp')
    have h2 := hτ0 (cl p') (cl p') (by simp)
    obtain ⟨z, hz⟩ := (Δ.D m).link_nonempty (cl p')
    have := ((Δ.D 0).adjacent _ _).mp ⟨z, h1 hz, h2 hz⟩
    simp only [τ]; rw [abs_le]; omega
  have hσ0_0 : σ0 ⟨min 0 (Δ.n (m + 1) - 1), by omega⟩ = ⟨0, hnR⟩ := by
    refine hPRu _ (hσ0' _ ?_)
    have : (⟨min 0 (Δ.n (m + 1) - 1), by omega⟩ : Fin (Δ.n (m + 1))) = ⟨0, hnF⟩ := Fin.ext (by simp)
    rw [this]; exact hPF
  have hσ0_T : σ0 ⟨min (Δ.n (m + 1) - 1) (Δ.n (m + 1) - 1), by omega⟩ = ⟨Δ.n m - 1, by omega⟩ := by
    refine hQRu _ (hσ0' _ ?_)
    have : (⟨min (Δ.n (m + 1) - 1) (Δ.n (m + 1) - 1), by omega⟩ : Fin (Δ.n (m + 1))) = ⟨Δ.n (m + 1) - 1, by omega⟩ :=
      Fin.ext (by simp)
    rw [this]; exact hQF
  have hτ0_0 : ((τ0 ⟨0, hnR⟩ : Fin (Δ.n 0)) : ℕ) = 0 := by
    have := hP0u _ (hτ0 ⟨0, hnR⟩ ⟨0, hnR⟩ (by simp) hPR)
    rw [this]
  have hτ0_T : ((τ0 ⟨Δ.n m - 1, by omega⟩ : Fin (Δ.n 0)) : ℕ) = Δ.n 0 - 1 := by
    have := hQ0u _ (hτ0 ⟨Δ.n m - 1, by omega⟩ ⟨Δ.n m - 1, by omega⟩ (by simp) hQR)
    rw [this]
  have hx'0 : x' 0 = 0 := by
    simp only [x']
    have : (⟨min 0 (N - 1), by omega⟩ : Fin N) = ⟨0, hN⟩ := Fin.ext (by simp)
    rw [this, hx0]; rfl
  have hx'T : x' (N - 1) = (Δ.n 0 : ℤ) - 1 := by
    simp only [x']
    have : (⟨min (N - 1) (N - 1), by omega⟩ : Fin N) = ⟨N - 1, by omega⟩ := Fin.ext (by simp)
    rw [this, hxT]; push_cast; omega
  have hx'v : ∀ i (hi : i < N), x' i = (x ⟨i, hi⟩ : ℤ) := by
    intro i hi; simp only [x']
    rw [show (⟨min i (N - 1), by omega⟩ : Fin N) = ⟨i, hi⟩ from Fin.ext (by simp; omega)]
  have hS := Chain.setting_of_crooked (Δ.crooked m) σ0 hσ0' hnF
  have hreal := PatCore.realize (σ := σ) hS le_rfl hslow (x := x') (by omega)
    (by
      intro i hi
      rw [hx'v i (by omega), hx'v (i + 1) (by omega)]
      have := hxs ⟨i, by omega⟩ ⟨i + 1, by omega⟩ rfl
      rw [abs_le]; omega)
    (by intro i hi; rw [hx'0]; simp [x'])
    (by intro i hi; rw [hx'T]; simp only [x']; omega)
    (by intro f hf; rw [hx'0]; simp [τ])
    (by intro f hf; rw [hx'T]; simp only [τ]; omega)
    (by
      rw [hx'0]; simp only [τ, σ]; rw [hσ0_0, hcl]; exact_mod_cast hτ0_0)
    (by
      rw [hx'T]; simp only [τ, σ]; rw [hσ0_T, hcl, hτ0_T]; omega)
    (by omega)
  obtain ⟨φ, hφ0, hφT, hφstep, hφ⟩ := hreal
  have hle : ∀ f, f < Δ.n (m + 1) → φ f < N := fun f hf => by
    have := (hφ f (Nat.zero_le _) (by omega)).2.1; omega
  refine Chain.exists_consolidation_of_lift (Δ.D (m + 1)) (Δ.D 0) (Δ.isFrom (m + 1)) x φ hφ0
    hφT (fun f hf => hφstep f (Nat.zero_le _) hf) hle ?_
  intro f hf
  obtain ⟨-, hφle, p, hp, hpv⟩ := hφ f (Nat.zero_le _) (by omega)
  have hfv : (⟨min f (Δ.n (m + 1) - 1), by omega⟩ : Fin (Δ.n (m + 1))) = ⟨f, hf⟩ := Fin.ext (by simp; omega)
  have hsub1 := hσ0' ⟨f, hf⟩
  have hdist : (((cl p : Fin (Δ.n m)) : ℤ) - (σ0 ⟨f, hf⟩ : Fin (Δ.n m))).natAbs ≤ 4 * N + 10 := by
    have := hcld p (σ f) hp
    simp only [σ] at this
    rw [hfv, hcl] at this
    exact this
  have hsub2 := hτ0 (cl p) (σ0 ⟨f, hf⟩) hdist
  have hval : τ0 (cl p) = x ⟨φ f, hle f hf⟩ := by
    apply Fin.ext
    have : (τ0 (cl p) : ℤ) = x' (φ f) := hpv
    rw [hx'v _ (hle f hf)] at this
    exact_mod_cast this
  rw [← hval]
  exact hsub1.trans hsub2

end Description

end HPC
