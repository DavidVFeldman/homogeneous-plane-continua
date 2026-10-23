import HPC.Jones.Jones49B
import HPC.Jones.Jones49CMoore

/-!
# Batch 151 skeleton: crossing continua; Moore 1922 Theorem 4 (local form and both directions);
complementary domains of plane continua; Whyburn 1939 (6.22) in the §14 form

Save as `HPC/Jones/Jones49C.lean` (splitting under `HPC/Jones/` is expected); add
`import HPC.Jones.Jones49C` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be
adjusted, each change recorded at the statement and in the report.

Sources (page images, 150–200 dpi): Moore 1922 pp. 235–237 (`doc/sources/moore1922.pdf`); Whyburn,
*Semi-locally-connected sets*, Amer. J. Math. 61 (1939), §14, pp. 747–749
(`doc/sources/whyburn1939.pdf`). Whyburn's §14 proof begins: "Let `R` be a complementary domain of
`M`. Clearly we may suppose `R` bounded, since an inversion of the plane can be used to throw `R`
into a bounded region complementary to the image of `M`. We shall show that `R` has property `S`
… If this is not so, there exists a sequence of points `p₁, p₂, …` of `R` converging to a point
`p ∈ M` and an `ε > 0` such that for no `i, j` can `pᵢ` and `pⱼ` be joined by a connected subset of
`R` of diameter `< 4ε`."
-/

namespace HPC.Jones

open Set Topology Metric Filter HPC.Plane

/-! ## Continua crossing an annulus -/

/-- **The sector theorem** (REPORT-batch150 §2; the step behind Moore 1922 p. 236 "must clearly
contain a point either of `kₙ₋₁` or of `kₙ₊₁`" and p. 237 "It can easily be seen that no two of the
sets `R̄₂, R̄₄, …` …"). Two disjoint continua crossing a closed annulus (each in the annulus, each
meeting both boundary circles) cut it into two pieces; a connected subset of the open annulus
joining points of different pieces meets one of the two continua. Together with it, the cyclic
order on the middle circle of infinitely many mutually exclusive crossing continua. *The shape is
left to you*; the annulus may be taken with squares (sup metric) as in `exists_crossing_continua`.

*Shape chosen (batch 151):* the annulus is the closed square annulus `Ann P r₁ r₂`
(`r₁ ≤ d(z, P) ≤ r₂`, sup metric, `0 < r₁ < r₂`) and a crossing continuum is `IsCrossA P r₁ r₂ K`
(compact, connected, in the annulus, meeting both squares). The two pieces `V₁`, `V₂` are nonempty,
disjoint, relatively open in the annulus, and cover the annulus minus `K ∪ K'`; a preconnected subset
of the (closed) annulus meeting both pieces meets `K ∪ K'`. The cyclic order is the companion
theorem `sector_cyclic_order`. Tools used: the component criterion for a continuous logarithm
(`HPC.Moore.exists_log_of_mem_component`) and the connectedness of the outside of a square; neither
Janiszewski's theorem, unicoherence, the Jordan curve theorem nor the θ-curve theorems are used. -/
theorem sector_theorem {P : Pt} {r₁ r₂ : ℝ} (h0 : 0 < r₁) (h12 : r₁ < r₂) {K K' : Set Pt}
    (hK : Sector.IsCrossA P r₁ r₂ K) (hK' : Sector.IsCrossA P r₁ r₂ K') (hd : Disjoint K K') :
    ∃ V₁ V₂ : Set Pt, V₁.Nonempty ∧ V₂.Nonempty ∧ Disjoint V₁ V₂ ∧
      V₁ ∪ V₂ = Sector.Ann P r₁ r₂ \ (K ∪ K') ∧ Sector.RelOpenAnn P r₁ r₂ V₁ ∧
      Sector.RelOpenAnn P r₁ r₂ V₂ ∧
      ∀ C : Set Pt, IsPreconnected C → C ⊆ Sector.Ann P r₁ r₂ → (C ∩ V₁).Nonempty →
        (C ∩ V₂).Nonempty → (C ∩ (K ∪ K')).Nonempty := by
  obtain ⟨V₁, V₂, h1, h2, hV, hU, o1, o2⟩ := Sector.sector_two h0 h12 hK hK' hd
  refine ⟨V₁, V₂, h1, h2, hV, hU, o1, o2, fun C hC hCA hC1 hC2 => ?_⟩
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hV1 : V₁ ⊆ Sector.Ann P r₁ r₂ := fun z hz => by
    have : z ∈ V₁ ∪ V₂ := Or.inl hz
    rw [hU] at this
    exact this.1
  have hV2 : V₂ ⊆ Sector.Ann P r₁ r₂ := fun z hz => by
    have : z ∈ V₁ ∪ V₂ := Or.inr hz
    rw [hU] at this
    exact this.1
  have hCs : C ⊆ V₁ ∪ V₂ := fun z hz => by
    rw [hU]
    exact ⟨hCA hz, fun h => (eq_empty_iff_forall_notMem.1 hne) z ⟨hz, h⟩⟩
  have := Sector.preconnected_sub_piece o1 o2 hV1 hV2 hV hC hCs hC1
  obtain ⟨z, hzC, hz2⟩ := hC2
  exact disjoint_left.1 hV (this hzC) hz2

/-- **The cyclic order** of infinitely many pairwise disjoint continua crossing the annulus
(companion of `sector_theorem`; `HPC.Jones.Sector.sector_cyclic`). After extraction (`g`), each
`k (g n)` with `n ≥ 1` lies in a piece `V n` of the annulus cut off by its neighbours `k (g (n - 1))`
and `k (g (n + 1))`: `V n` misses every other `k (g m)` and every `V m` with `|n - m| ≥ 2`, and a
preconnected subset of the annulus off the two neighbours that meets `V n` lies in `V n`. The order is
that of the continua (via lifts to the strip), not only of their points on a middle square. -/
theorem sector_cyclic_order {P : Pt} {r₁ r₂ : ℝ} (h0 : 0 < r₁) (h12 : r₁ < r₂)
    {k : ℕ → Set Pt} (hk : ∀ n, Sector.IsCrossA P r₁ r₂ (k n))
    (hdisj : Pairwise fun m n => Disjoint (k m) (k n)) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ V : ℕ → Set Pt, ∀ n, 1 ≤ n →
      k (g n) ⊆ V n ∧ V n ⊆ Sector.Ann P r₁ r₂ ∧ (∀ m, m ≠ n → Disjoint (V n) (k (g m))) ∧
      (∀ m, (n + 2 ≤ m ∨ m + 2 ≤ n) → Disjoint (V n) (V m)) ∧
      (∀ C, IsPreconnected C → C ⊆ Sector.Ann P r₁ r₂ \ (k (g (n - 1)) ∪ k (g (n + 1))) →
        (C ∩ V n).Nonempty → C ⊆ V n) :=
  Sector.sector_cyclic h0 h12 hk hdisj

/-! ## Moore 1922 Theorem 4 -/

/-- **Moore's sufficiency, local form** (REPORT-batch150 §5 (a)). A connected open plane set `R`,
bounded or not, with connected boundary, such that no boundary point `p` is the limit of a sequence
of points of `R` no two of which can be joined in `R` by a connected set of diameter `< ε` (Whyburn's
§14 condition), has a locally connected boundary. Moore's p. 236 argument, which uses neither
boundedness nor simple connectivity.

The hypothesis `hRc` (connectedness of `R`) is kept as in the skeleton; the proof
(`HPC.Jones.Sector.sufficiency_local`) does not use it. -/
theorem moore22_sufficiency_local {R : Set Pt} (hR : IsOpen R) (hRc : IsConnected R)
    (hB : IsConnected (frontier R))
    (hloc : ∀ p ∈ frontier R, ∀ ε > 0, ¬ ∃ u : ℕ → Pt, (∀ n, u n ∈ R) ∧ Tendsto u atTop (𝓝 p) ∧
      ∀ i j, i ≠ j → ¬ ∃ C ⊆ R, IsPreconnected C ∧ u i ∈ C ∧ u j ∈ C ∧ Bornology.IsBounded C ∧
        diam C < ε) :
    LocallyConnectedSpace (frontier R) :=
  Sector.sufficiency_local hR hB hloc

/-- **Moore 1922, Theorem 4** — left open in batch 150, restated verbatim. A simply connected bounded
domain has a continuous curve as its boundary iff it has property S.

Sufficiency: property S gives Whyburn's local condition (`Sector.hloc_of_propertyS`, pigeonhole),
hence local connectedness by `moore22_sufficiency_local`; connectedness of the boundary is batch
150's `isConnected_frontier_of_mooreSimplyConnected`. Necessity: `Sector.propertyS_of_locallyConnected`
(Moore's pp. 236–237 argument with the repaired last step), which does not use simple
connectivity. -/
theorem moore22_theorem4 {R : Set Pt} (hR : IsOpen R) (hRc : IsConnected R)
    (hRb : Bornology.IsBounded R) (hsc : MooreSimplyConnected R) :
    PropertyS R ↔ (IsConnected (frontier R) ∧ LocallyConnectedSpace (frontier R)) := by
  constructor
  · intro hS
    have hB := isConnected_frontier_of_mooreSimplyConnected hR hRc hRb hsc
    exact ⟨hB, moore22_sufficiency_local hR hRc hB (Sector.hloc_of_propertyS hS)⟩
  · rintro ⟨-, hlc⟩
    exact Sector.propertyS_of_locallyConnected hR hRc hRb hlc

/-! ## Complementary domains of plane continua -/

/-- The complement of a complementary domain of a closed connected plane set is connected: it is `M`
together with the closures of the other complementary domains, each of which meets `M` (the argument
inside `HPC.Moore.brouwer_boundary`). -/
theorem isPreconnected_compl_connectedComponentIn_compl {M : Set Pt} (hM : IsClosed M)
    (hMc : IsConnected M) (x : Pt) : IsPreconnected (connectedComponentIn Mᶜ x)ᶜ := by
  set D := connectedComponentIn Mᶜ x with hDdef
  have hDo : IsOpen D := hM.isOpen_compl.connectedComponentIn
  have hDM : D ⊆ Mᶜ := connectedComponentIn_subset _ _
  obtain ⟨m, hm⟩ := hMc.nonempty
  have hMD : M ⊆ Dᶜ := fun z hz h => hDM h hz
  refine isPreconnected_of_forall m fun y hy => ?_
  by_cases hyM : y ∈ M
  · exact ⟨M, hMD, hm, hyM, hMc.isPreconnected⟩
  set C := connectedComponentIn Mᶜ y
  have hCo : IsOpen C := hM.isOpen_compl.connectedComponentIn
  have hCc : IsPreconnected (closure C) := isPreconnected_connectedComponentIn.closure
  have hCD : closure C ⊆ Dᶜ := by
    intro z hz hzD
    obtain ⟨w, hwD, hwC⟩ := mem_closure_iff.1 hz D hDo hzD
    have h1 := connectedComponentIn_eq hwD
    have h2 := connectedComponentIn_eq hwC
    exact hy (by rw [hDdef, h1, ← h2]; exact mem_connectedComponentIn hyM)
  have hmeet : (M ∩ closure C).Nonempty := by
    by_contra hno
    rw [not_nonempty_iff_eq_empty] at hno
    have hsub : closure C ⊆ C := by
      intro z hz
      have hzM : z ∈ Mᶜ := fun h => (eq_empty_iff_forall_notMem.1 hno) z ⟨h, hz⟩
      by_contra hzC
      exact HPC.Moore.frontier_connectedComponentIn_subset hM.isOpen_compl y
        ⟨hz, by rw [hCo.interior_eq]; exact hzC⟩ hzM
    have hclopen : IsClopen C := ⟨closure_subset_iff_isClosed.1 hsub, hCo⟩
    rcases isClopen_iff.1 hclopen with h | h
    · exact (h ▸ mem_connectedComponentIn hyM : y ∈ (∅ : Set Pt))
    · exact (connectedComponentIn_subset _ _ (h ▸ mem_univ m : m ∈ C)) hm
  obtain ⟨z, hzM, hzC⟩ := hmeet
  exact ⟨M ∪ closure C, union_subset hMD hCD, Or.inl hm,
    Or.inr (subset_closure (mem_connectedComponentIn hyM)),
    hMc.isPreconnected.union z hzM hzC hCc⟩

/-- The boundary of every complementary domain of a plane continuum is a continuum (bounded or
unbounded domain). Immediate from Brouwer's boundary theorem `HPC.Moore.brouwer_boundary` (for closed
connected `M`, by unicoherence of the plane). -/
theorem isConnected_frontier_complDomain {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    {x : Pt} (hx : x ∉ M) : IsConnected (frontier (connectedComponentIn Mᶜ x)) :=
  HPC.Moore.brouwer_boundary hM.isClosed hMc ⟨x, hx, rfl⟩

/-- A bounded complementary domain of a plane continuum is simply connected in Moore's sense
(REPORT-batch150 §5 (b)). The complement `Uᶜ` of the domain is connected
(`isPreconnected_compl_connectedComponentIn_compl`) and unbounded; if `H` is bounded with
`frontier H ⊆ U`, then `Uᶜ ⊆ interior H ∪ (closure H)ᶜ`, so `Uᶜ` lies in the exterior of `H`, and
`H ⊆ U`. Only the closedness of `M` is used, and the hypothesis `hx` (kept as in the skeleton) is
not needed: for `x ∈ M` the domain is empty. -/
theorem mooreSimplyConnected_complDomain {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    {x : Pt} (hx : x ∉ M) (hb : Bornology.IsBounded (connectedComponentIn Mᶜ x)) :
    MooreSimplyConnected (connectedComponentIn Mᶜ x) := by
  set U := connectedComponentIn Mᶜ x
  intro H hH hfr
  have hUc := isPreconnected_compl_connectedComponentIn_compl hM.isClosed hMc x
  have hcov : Uᶜ ⊆ interior H ∪ (closure H)ᶜ := by
    intro z hz
    by_contra h
    simp only [mem_union, mem_compl_iff, not_or, not_not] at h
    exact hz (hfr ⟨h.2, h.1⟩)
  have hdisj : Disjoint (interior H) (closure H)ᶜ :=
    disjoint_compl_right.mono_left (interior_subset.trans subset_closure)
  rcases IsPreconnected.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl hdisj
    hcov hUc with h | h
  · exfalso
    obtain ⟨ρ, hρ⟩ := (hb.union (hH.subset interior_subset)).subset_closedBall (0 : Pt)
    apply (isConnected_compl_closedBall_pt 0 ρ).2
    refine (isBounded_closedBall (x := (0 : Pt)) (r := ρ)).subset fun z hz => ?_
    by_cases hzU : z ∈ U
    · exact hρ (Or.inl hzU)
    · exact hρ (Or.inr (h hzU))
  · intro z hz
    by_contra hzU
    exact h hzU (subset_closure hz)

/-! ## Whyburn 1939 (6.22), in the form §14 uses -/

/-- **(6.22), §14 form** (p. 747: "Then by (6.22) there exists a `δ > 0` and a component `N` of
`M − M·V_δ(p)` which contains `M − M·V_ε(p)`"). For a compact semi-locally-connected continuum `M`
and a non-cut point `p`, stated in the subtype `M`. -/
theorem whyburn39_6_22_sec14 {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    (hS : ∀ z : X, SemiLocConnAt z) {p : X} (hp : IsConnected ({p}ᶜ : Set X)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, δ < ε ∧ ∃ c ∈ (ball p δ)ᶜ,
      (ball p ε)ᶜ ⊆ connectedComponentIn (ball p δ)ᶜ c := by
  classical
  obtain ⟨q, hq⟩ := hp.nonempty
  have hqp : q ≠ p := hq
  have hap := isAposyndetic_of_semiLocConn hS
  -- for every `a ≠ p`: a continuum `L a ∋ q` missing `p`, and an open `U a ∋ a` inside it
  have hex : ∀ a : X, a ≠ p → ∃ L U : Set X, IsCompact L ∧ IsPreconnected L ∧ q ∈ L ∧ p ∉ L ∧
      IsOpen U ∧ a ∈ U ∧ U ⊆ L := by
    intro a ha
    have hcomp : connectedComponentIn ({p}ᶜ : Set X) q = {p}ᶜ :=
      hp.isPreconnected.connectedComponentIn hq
    obtain ⟨N, hN, hqN, haN, hpN⟩ := whyburn_6_2 hS hqp (b := a) (by rw [hcomp]; exact ha)
    obtain ⟨H, U, hH, hU, haU, hUH, hpH⟩ := hap a p ha
    exact ⟨N ∪ H, U, hN.1.union hH.1, hN.2.isPreconnected.union a haN (hUH haU)
      hH.2.isPreconnected, Or.inl hqN, fun h => h.elim hpN hpH, hU, haU, hUH.trans
      subset_union_right⟩
  choose! L U hLc hLp hqL hpL hUo haU hUL using hex
  have hSc : IsCompact (ball p ε)ᶜ := isOpen_ball.isClosed_compl.isCompact
  have hne : ∀ a ∈ (ball p ε)ᶜ, a ≠ p := fun a ha h => ha (h ▸ mem_ball_self hε)
  obtain ⟨F, hFcov⟩ := hSc.elim_nhds_subcover' (fun a ha => U a)
    (fun a ha => (hUo a (hne a ha)).mem_nhds (haU a (hne a ha)))
  set W := ⋃ a ∈ F, L a
  have hWc : IsClosed W := F.finite_toSet.isClosed_biUnion fun a _ =>
    (hLc a (hne a a.2)).isClosed
  have hpW : p ∉ W := by
    simp only [W, mem_iUnion, not_exists]
    exact fun a _ => hpL a (hne a a.2)
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hWc.isOpen_compl p hpW
  have hqp' : 0 < dist q p := dist_pos.2 hqp
  set δ := min (min (ε / 2) r) (dist q p / 2)
  have hδ0 : 0 < δ := lt_min (lt_min (half_pos hε) hr) (half_pos hqp')
  have hδr : δ ≤ r := (min_le_left _ _).trans (min_le_right _ _)
  have hδε : δ < ε := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hε)
  have hqδ : q ∈ (ball p δ)ᶜ := by
    simp only [mem_compl_iff, mem_ball, not_lt]
    exact (min_le_right _ _).trans (half_le_self hqp'.le)
  refine ⟨δ, hδ0, hδε, q, hqδ, fun z hz => ?_⟩
  have hz' := hFcov hz
  simp only [mem_iUnion] at hz'
  obtain ⟨a, ha, hza⟩ := hz'
  have hLW : L a ⊆ (ball p δ)ᶜ := fun w hw hwb => by
    have : w ∈ W := mem_biUnion ha hw
    exact hrW (ball_subset_ball hδr hwb) this
  exact (hLp a (hne a a.2)).subset_connectedComponentIn (hqL a (hne a a.2)) hLW
    (hUL a (hne a a.2) hza)

end HPC.Jones
