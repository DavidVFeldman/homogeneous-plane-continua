import HPC.Jones.Jones49DSep

/-!
# Batch 152, items B and D: accumulating continua; bad points of a non-locally-connected boundary

* `BadAt R p ε`: Whyburn's failure at `p` — points of `R` converging to `p`, no two of which lie in a
  connected subset of `R` of diameter `< ε` (p. 747).
* `not_orderLE_of_accumulating`: a point at which infinitely many pairwise disjoint connected sets
  accumulate, each reaching a fixed distance from it, has no finite order (the pigeonhole of p. 748,
  turned around).
* `exists_bad_point_of_crossing`: Moore's p. 236 argument (`HPC.Jones.Sector.sufficiency_local`) at an
  arbitrary middle radius `ρ`: from infinitely many disjoint continua of `frontier R` crossing an
  annulus, a point `h ∈ frontier R` with `d(h, P) = ρ` at which Whyburn's condition fails, together
  with crossing continua accumulating at `h`.
-/

namespace HPC.Jones.Sec14

open Set Topology Metric Filter HPC.Plane HPC.Jones.Sector

/-- **Whyburn's failure at `p`** (p. 747): a sequence of points of `R` converging to `p`, no two of
which lie in a connected subset of `R` of diameter `< ε`. This is the negation of the local
hypothesis of `moore22_sufficiency_local` at `p` and `ε`. -/
def BadAt (R : Set Pt) (p : Pt) (ε : ℝ) : Prop :=
  ∃ u : ℕ → Pt, (∀ n, u n ∈ R) ∧ Tendsto u atTop (𝓝 p) ∧
    ∀ i j, i ≠ j → ¬ ∃ C ⊆ R, IsPreconnected C ∧ u i ∈ C ∧ u j ∈ C ∧ Bornology.IsBounded C ∧
      diam C < ε

/-- A preconnected set meeting `V` and its complement meets the frontier of `V`. -/
theorem IsPreconnected.inter_frontier_nonempty' {X : Type*} [TopologicalSpace X] {s V : Set X}
    (hs : IsPreconnected s) (h1 : (s ∩ V).Nonempty) (h2 : (s \ V).Nonempty) :
    (s ∩ frontier V).Nonempty := by
  rw [frontier_eq_closure_inter_closure]
  obtain ⟨a, haS, haV⟩ := h1
  obtain ⟨b, hbS, hbV⟩ := h2
  refine isPreconnected_closed_iff.1 hs _ _ isClosed_closure isClosed_closure (fun z _ => ?_)
    ⟨a, haS, subset_closure haV⟩ ⟨b, hbS, subset_closure hbV⟩
  by_cases hz : z ∈ V
  · exact Or.inl (subset_closure hz)
  · exact Or.inr (subset_closure hz)

/-- **Accumulating continua exclude finite order** (item B; it replaces Whyburn's curve `K` and his
pigeonhole). If infinitely many pairwise disjoint preconnected sets `T i` accumulate at `p`
(points `b i ∈ T i` converge to `p`) and each reaches distance `≥ d > 0` from `p`, then `p` has no
order `≤ n` for any `n`: an open `V ∋ p` inside `B(p, d)` contains `b i` for large `i`, so the
frontier of `V` meets the disjoint sets `T i` for all large `i`. -/
theorem not_orderLE_of_accumulating {X : Type*} [MetricSpace X] {p : X} {T : ℕ → Set X}
    (hT : ∀ i, IsPreconnected (T i)) (hd : Pairwise fun i j => Disjoint (T i) (T j))
    {b : ℕ → X} (hb : ∀ i, b i ∈ T i) (hlim : Tendsto b atTop (𝓝 p)) {d : ℝ} (hd0 : 0 < d)
    (hfar : ∀ i, ∃ a ∈ T i, d ≤ dist a p) (n : ℕ) : ¬ OrderLE p n := by
  intro h
  obtain ⟨V, hVo, hpV, hVU, hfin, -⟩ := h (ball p d) (ball_mem_nhds p hd0)
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 (hlim (hVo.mem_nhds hpV))
  have hmeet : ∀ k, (T (k + i₀) ∩ frontier V).Nonempty := by
    intro k
    obtain ⟨a, haT, hda⟩ := hfar (k + i₀)
    refine IsPreconnected.inter_frontier_nonempty' (hT _) ⟨b (k + i₀), hb _, hi₀ _ (by omega)⟩
      ⟨a, haT, fun haV => ?_⟩
    have := mem_ball.1 (hVU haV)
    linarith
  choose f hfT hfV using hmeet
  have hinj : Function.Injective f := by
    intro k l hkl
    by_contra hne
    have hkl' : k + i₀ ≠ l + i₀ := by omega
    exact disjoint_left.1 (hd hkl') (hfT k) (hkl ▸ hfT l)
  exact (Set.infinite_of_injective_forall_mem hinj hfV) hfin

/-- **Bad points at every middle radius** (Moore's p. 236 argument, `Sector.sufficiency_local`, at the
radius `ρ` instead of the middle one). Let `t n ⊆ frontier R` be pairwise disjoint continua crossing
the annulus `r₁ ≤ d(·, P) ≤ r₂`, and `ρ` in the middle third. After the cyclic extraction
(`sector_cyclic`), points `b n ∈ t (g n)` on the square of radius `ρ` have a limit point `h` along the
odd indices; points `c n ∈ R` near `b n` converge to `h`, and no two of them lie in a connected subset
of `R` of diameter `< (r₂ - r₁)/6`. The continua `t (s i)` with `b i ∈ t (s i)`, `b i → h`, are
returned for `not_orderLE_of_accumulating`. -/
theorem exists_bad_point_of_crossing {R : Set Pt} (hR : IsOpen R) {P : Pt} {r₁ r₂ : ℝ}
    (h0 : 0 < r₁) (h12 : r₁ < r₂) {t : ℕ → Set Pt} (htc : ∀ n, IsCrossA P r₁ r₂ (t n))
    (htd : Pairwise fun m n => Disjoint (t m) (t n)) (htM : ∀ n, t n ⊆ frontier R) {ρ : ℝ}
    (hρ1 : r₁ + (r₂ - r₁) / 3 ≤ ρ) (hρ2 : ρ ≤ r₂ - (r₂ - r₁) / 3) :
    ∃ h ∈ frontier R, dist h P = ρ ∧ BadAt R h ((r₂ - r₁) / 6) ∧
      ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ b : ℕ → Pt, (∀ i, b i ∈ t (s i)) ∧
        Tendsto b atTop (𝓝 h) := by
  set M := frontier R
  have hMcl : IsClosed M := isClosed_frontier
  have hRM : ∀ z ∈ R, z ∉ M := fun z hz hzM => hzM.2 (by rw [hR.interior_eq]; exact hz)
  obtain ⟨g, hg, V, hV⟩ := sector_cyclic h0 h12 htc htd
  set η := (r₂ - r₁) / 6 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hb : ∀ n, ∃ b ∈ t (g n), dist b P = ρ := fun n =>
    (htc (g n)).exists_dist_eq (by linarith) (by linarith)
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
        linarith [hbd n]
      · have h1 := dist_triangle z (b n) P
        have h2 : dist z (b n) < δ n := hz
        have := hδη n
        linarith [hbd n]
    exact hsub (by rw [mem_ball, dist_comm]; exact hcd n)
  obtain ⟨p, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (x := fun i => b (2 * i + 1))
    (isBounded_closedBall (x := P) (r := ρ)) fun i => mem_closedBall.2 (hbd _).le
  have hpM : p ∈ M := hMcl.mem_of_tendsto hlim (Eventually.of_forall fun i => htM _ (hbk _))
  have hpd : dist p P = ρ := by
    have h1 := hlim.dist (tendsto_const_nhds (x := P))
    have h2 : ((fun x => dist x P) ∘ ((fun i => b (2 * i + 1)) ∘ φ)) = fun _ => ρ := by
      funext i; exact hbd _
    have h3 : Tendsto (fun i => dist (((fun i => b (2 * i + 1)) ∘ φ) i) P) atTop
        (𝓝 (dist p P)) := h1
    have h4 : (fun i => dist (((fun i => b (2 * i + 1)) ∘ φ) i) P) = fun _ => ρ := h2
    rw [h4] at h3
    exact (tendsto_nhds_unique tendsto_const_nhds h3).symm
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
  refine ⟨p, hpM, hpd, ⟨u, fun i => hcR _, hut, fun i j hij => ?_⟩,
    fun i => g (2 * φ i + 1), fun i j hij => hg (by have := hφ hij; omega),
    fun i => b (2 * φ i + 1), fun i => hbk _, hlim⟩
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
      linarith [hbd m]
    · have h1 := dist_le_diam_of_mem hCb hz hmC
      have h2 := hcd m
      have h3 := dist_triangle (c m) (b m) P
      have h4 := dist_triangle z (c m) P
      have := hδη m
      rw [dist_comm (b m)] at h2
      linarith [hbd m]
    · rintro (h | h) <;> exact hRM z (hCR hz) (htM _ h)
  have hm := htrap _ (by omega) hiC
  have hn := htrap _ (by omega) hjC
  have hφne : φ i ≠ φ j := hφ.injective.ne hij
  have hsep : 2 * φ j + 1 + 2 ≤ 2 * φ i + 1 ∨ 2 * φ i + 1 + 2 ≤ 2 * φ j + 1 := by omega
  exact disjoint_left.1 ((hV (2 * φ j + 1) (by omega)).2.2.2.1 (2 * φ i + 1) hsep)
    (hn hiC) (hm hiC)

end HPC.Jones.Sec14
