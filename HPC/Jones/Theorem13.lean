import HPC.Jones.Theorem13Aux

/-!
# Batch 135: Jones 1948, Theorem 13

Jones's proof, with his notation: `A` and `ε` such that for each `p ∈ U(A, ε)` there is a point
`q ∉ U(A, ε)` with `X` not aposyndetic at `q` with respect to `p` (Baire); rings
`R₀ = U(A, ε/4)` and `Rₙ = {r_{n-1} < d(·, A) < rₙ}` with `rₙ = ε/2 − ε/(4(n+1))`; points
`xₙ ∈ Rₙ` (Theorem 6, under the assumption that the theorem is false), small balls `Vₙ ∋ xₙ`, and
separations `X − Vₙ = Wₙ ∪ Qₙ` (`exists_split_of_not_aposAt`) with `xₙ₋₁ ∈ Qₙ`,
`V̄ₙ ⊆ Wₙ₋₁`, and a continuum `Hₙ₋₁ ⊇ V̄ₙ₋₁` missing `V̄ₙ`. Then `Qₙ` increases and `Wₙ` decreases
(`separation_nested`), `z ∈ ⋂ Wₙ` on the sphere `d(·, A) = ε`, `y` a cluster point of the `xₙ`, and
`y` cuts `x₀` from `z`.

Shape of the recursion: one configuration `Cfg` per stage (the point `xₙ`, the radius of `Vₙ`,
and `Wₙ`, `Qₙ`), the stage invariant `Good`, the link `Rel` between consecutive stages. Jones's
finite families `H_{n1}, …, H_{n m_n}` are replaced by the uniform radius of
`exists_radius_uniform_apos`. Jones's `V₂ ⊆ R₂ · ∏ U_{2i} · (M − H₁)` is supplemented by
`V̄₂ ⊆ W₁`, which his argument (\"consequently `Q₂` contains `Q₁` and `W₁` contains `W₂`\") uses.
-/

namespace HPC.Jones

open Set Topology Filter Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

namespace T13J

/-- Jones's radii `rₙ = ε/2 − ε/(4(n+1))` (`r₀ = ε/4`). -/
noncomputable def rad (ε : ℝ) (n : ℕ) : ℝ := ε / 2 - ε / (4 * ((n : ℝ) + 1))

/-- The inner radius of the `n`-th ring (`-1` for `n = 0`). -/
noncomputable def lo (ε : ℝ) : ℕ → ℝ
  | 0 => -1
  | n + 1 => rad ε n

/-- The ring `Rₙ`. -/
def ring (A : X) (ε : ℝ) (n : ℕ) : Set X := {p | lo ε n < dist p A ∧ dist p A < rad ε n}

/-- The closed annulus `R̄_∞ − U(A, rₙ)`. -/
def outer (A : X) (ε : ℝ) (n : ℕ) : Set X := {p | rad ε n ≤ dist p A ∧ dist p A ≤ ε / 2}

/-- A stage of the construction: `xₙ`, the radius of `Vₙ = U(xₙ, sₙ)`, `Wₙ` and `Qₙ`. -/
structure Cfg (X : Type*) where
  x : X
  s : ℝ
  W : Set X
  Q : Set X

/-- The stage invariant. -/
def Good (A : X) (ε : ℝ) (n : ℕ) (c : Cfg X) : Prop :=
  0 < c.s ∧ c.s < 1 / ((n : ℝ) + 1) ∧ closedBall c.x c.s ⊆ ring A ε n ∧
  (∀ y ∈ outer A ε n, ∃ H : Set X, Fold.Q78.IsContinuum H ∧ closedBall c.x c.s ⊆ H ∧ y ∉ H) ∧
  IsClosed c.W ∧ IsClosed c.Q ∧ Disjoint c.W c.Q ∧ c.W ∪ c.Q = (ball c.x c.s)ᶜ ∧
  ∃ w ∈ c.W, ε ≤ dist w A

/-- The link between consecutive stages. -/
def Rel (c c' : Cfg X) : Prop :=
  closedBall c'.x c'.s ⊆ c.W ∧ c.x ∈ c'.Q ∧
  ∃ H : Set X, Fold.Q78.IsContinuum H ∧ closedBall c.x c.s ⊆ H ∧ Disjoint H (closedBall c'.x c'.s)

section Radii

variable {ε : ℝ}

theorem rad_lt (hε : 0 < ε) (n : ℕ) : rad ε n < ε / 2 := by
  unfold rad
  have : 0 < ε / (4 * ((n : ℝ) + 1)) := by positivity
  linarith

theorem rad_mono (hε : 0 < ε) {j k : ℕ} (h : j ≤ k) : rad ε j ≤ rad ε k := by
  unfold rad
  have hjk : (j : ℝ) ≤ k := by exact_mod_cast h
  have : ε / (4 * ((k : ℝ) + 1)) ≤ ε / (4 * ((j : ℝ) + 1)) := by gcongr
  linarith

theorem rad_strictMono (hε : 0 < ε) {j k : ℕ} (h : j < k) : rad ε j < rad ε k := by
  unfold rad
  have hjk : (j : ℝ) < k := by exact_mod_cast h
  have : ε / (4 * ((k : ℝ) + 1)) < ε / (4 * ((j : ℝ) + 1)) := by gcongr
  linarith

theorem rad_pos (hε : 0 < ε) (n : ℕ) : 0 < rad ε n := by
  have h0 : rad ε 0 = ε / 4 := by unfold rad; norm_num; ring
  have := rad_mono hε (Nat.zero_le n)
  rw [h0] at this
  linarith

theorem rad_lt_eps (hε : 0 < ε) (n : ℕ) : rad ε n < ε := by
  have := rad_lt hε n; linarith

theorem lo_ge (hε : 0 < ε) {k n : ℕ} (h : k < n) : rad ε k ≤ lo ε n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact rad_mono hε (by omega)

end Radii

variable {A : X} {ε : ℝ}

omit [CompactSpace X] [ConnectedSpace X] in
theorem isOpen_ring (n : ℕ) : IsOpen (ring A ε n) :=
  (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const)

omit [CompactSpace X] [ConnectedSpace X] in
theorem isClosed_outer (n : ℕ) : IsClosed (outer A ε n) :=
  (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
    (isClosed_le (continuous_id.dist continuous_const) continuous_const)

omit [CompactSpace X] [ConnectedSpace X] in
/-- Away from `Vₙ`, `Wₙ` is the complement of `Qₙ`; so `Wₙ` is open there. -/
theorem Good.W_inter_open {n : ℕ} {c : Cfg X} (hc : Good A ε n c) :
    IsOpen (c.W ∩ {p | rad ε n < dist p A}) := by
  obtain ⟨-, -, hball, -, -, hQ, hWQ, hcov, -⟩ := hc
  have heq : c.W ∩ {p | rad ε n < dist p A} = c.Qᶜ ∩ {p | rad ε n < dist p A} := by
    ext p
    simp only [mem_inter_iff, mem_compl_iff, mem_setOf_eq]
    constructor
    · rintro ⟨hpW, hp⟩; exact ⟨fun h => Set.disjoint_left.mp hWQ hpW h, hp⟩
    · rintro ⟨hpQ, hp⟩
      refine ⟨?_, hp⟩
      have hpV : p ∈ (ball c.x c.s)ᶜ := fun h =>
        absurd (hball (ball_subset_closedBall h)).2 (not_lt.mpr hp.le)
      have : p ∈ c.W ∪ c.Q := hcov.symm ▸ hpV
      exact this.resolve_right hpQ
  rw [heq]
  exact hQ.isOpen_compl.inter (isOpen_lt continuous_const (continuous_id.dist continuous_const))

omit [ConnectedSpace X] in
/-- **Building a stage** around a point `x` of the `n`-th ring at which `X` is aposyndetic with
respect to every point of `R̄_∞ − U(A, rₙ)`: a small ball inside a given open `G`, and a
separation of its complement with a prescribed point `p₀ ∉ G` in `Q`. -/
theorem build (hε : 0 < ε) (hfar : ∀ p ∈ ball A ε, ∃ q, ε < dist q A ∧ ¬ AposAt q p) {n : ℕ}
    {x : X} {G : Set X} (hG : IsOpen G) (hxG : x ∈ G) (hGr : G ⊆ ring A ε n)
    (hapos : ∀ y ∈ outer A ε n, AposAt x y) {p₀ : X} (hp₀ : p₀ ∉ G) :
    ∃ c : Cfg X, c.x = x ∧ Good A ε n c ∧ closedBall c.x c.s ⊆ G ∧ p₀ ∈ c.Q := by
  obtain ⟨s₀, hs₀, hgood₀⟩ := exists_radius_uniform_apos (isClosed_outer n).isCompact hapos
  obtain ⟨ρ, hρ, hρG⟩ := Metric.isOpen_iff.mp hG x hxG
  set s := min s₀ (min (ρ / 2) (1 / (2 * ((n : ℝ) + 1)))) with hsdef
  have hs : 0 < s := lt_min hs₀ (lt_min (half_pos hρ) (by positivity))
  have hsρ : s < ρ := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hρ))
  have hsn : s < 1 / ((n : ℝ) + 1) := by
    refine (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt ?_)
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hballG : closedBall x s ⊆ G := (closedBall_subset_ball hsρ).trans hρG
  have hgood : ∀ y ∈ outer A ε n, ∃ H : Set X, Fold.Q78.IsContinuum H ∧ closedBall x s ⊆ H ∧
      y ∉ H := fun y hy => by
    obtain ⟨H, hH, hbH, hyH⟩ := hgood₀ y hy
    exact ⟨H, hH, (closedBall_subset_closedBall (min_le_left _ _)).trans hbH, hyH⟩
  have hxA : x ∈ ball A ε := by
    rw [mem_ball]; exact (hGr hxG).2.trans (rad_lt_eps hε n)
  obtain ⟨q, hq, hqna⟩ := hfar x hxA
  have hOop : IsOpen {p : X | ε < dist p A} :=
    isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have hPV : Disjoint {p : X | ε ≤ dist p A} (ball x s) := by
    rw [Set.disjoint_left]
    intro p hp hpb
    have := (hGr (hballG (ball_subset_closedBall hpb))).2.trans (rad_lt_eps hε n)
    exact absurd hp (not_le.mpr this)
  obtain ⟨W, Q, hW, hQ, hWQ, hcov, ⟨w₁, hw₁W, hw₁P⟩, ⟨w₂, hw₂Q, hw₂P⟩⟩ :=
    exists_split_of_not_aposAt isOpen_ball (mem_ball_self hs) hPV hOop hq
      (fun p (hp : ε < dist p A) => show ε ≤ dist p A from le_of_lt hp) hqna
  have hp₀V : p₀ ∈ (ball x s)ᶜ := fun h => hp₀ (hballG (ball_subset_closedBall h))
  have hp₀WQ : p₀ ∈ W ∪ Q := hcov.symm ▸ hp₀V
  by_cases hp₀Q : p₀ ∈ Q
  · exact ⟨⟨x, s, W, Q⟩, rfl, ⟨hs, hsn, hballG.trans hGr, hgood, hW, hQ, hWQ, hcov, w₁, hw₁W,
      hw₁P⟩, hballG, hp₀Q⟩
  · exact ⟨⟨x, s, Q, W⟩, rfl, ⟨hs, hsn, hballG.trans hGr, hgood, hQ, hW, hWQ.symm,
      by rw [union_comm]; exact hcov, w₂, hw₂Q, hw₂P⟩, hballG, hp₀WQ.resolve_right hp₀Q⟩

variable {D : Set X}

omit [ConnectedSpace X] in
/-- **Theorem 6, used as in Jones's proof of Theorem 13.** If no three points of `D` are such that
one cuts the other two, then in each nonempty open `D' ⊆ D` there is a point at which `X` is
aposyndetic with respect to each point of a closed `M₀ ⊆ D − D'`. -/
theorem exists_apos_point (hnc : ¬ ∃ x ∈ D, ∃ y ∈ D, ∃ z ∈ D, CutsPts y x z) {D' M₀ : Set X}
    (hD' : IsOpen D') (hD'ne : D'.Nonempty) (hD'D : D' ⊆ D) (hM₀ : IsClosed M₀)
    (hM₀D : M₀ ⊆ D) (hdisj : Disjoint D' M₀) : ∃ x ∈ D', ∀ y ∈ M₀, AposAt x y := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨z, hz⟩ := hD'ne
  obtain ⟨x₀, hx₀, y₀, hy₀, hcut⟩ := theorem6 hD' ⟨z, hz⟩ hM₀ hdisj hcon
    (fun h => Set.disjoint_left.mp hdisj hz h)
  exact hnc ⟨x₀, hD'D hx₀, y₀, hM₀D hy₀, z, hD'D hz, hcut⟩

omit [CompactSpace X] [ConnectedSpace X] in
theorem outer_subset (hε : 0 < ε) (hD : closedBall A ε ⊆ D) (n : ℕ) : outer A ε n ⊆ D :=
  fun p hp => hD (mem_closedBall.mpr (hp.2.trans (by linarith)))

omit [CompactSpace X] [ConnectedSpace X] in
theorem ring_subset (hε : 0 < ε) (hD : closedBall A ε ⊆ D) (n : ℕ) : ring A ε n ⊆ D :=
  fun _ hp => hD (mem_closedBall.mpr (hp.2.trans (rad_lt_eps hε n)).le)

omit [CompactSpace X] [ConnectedSpace X] in
theorem disjoint_ring_outer (n : ℕ) : Disjoint (ring A ε n) (outer A ε n) := by
  rw [Set.disjoint_left]
  intro p hp hp'
  exact absurd hp.2 (not_lt.mpr hp'.1)

omit [ConnectedSpace X] in
/-- **The first stage.** -/
theorem init (hε : 0 < ε) (hfar : ∀ p ∈ ball A ε, ∃ q, ε < dist q A ∧ ¬ AposAt q p)
    (hD : closedBall A ε ⊆ D) (hnc : ¬ ∃ x ∈ D, ∃ y ∈ D, ∃ z ∈ D, CutsPts y x z) :
    ∃ c : Cfg X, Good A ε 0 c := by
  have hA : A ∈ ring A ε 0 := by
    refine ⟨?_, ?_⟩
    · show (-1 : ℝ) < dist A A; rw [dist_self]; norm_num
    · rw [dist_self]; exact rad_pos hε 0
  obtain ⟨x₀, hx₀, hapos⟩ := exists_apos_point hnc (isOpen_ring 0) ⟨A, hA⟩ (ring_subset hε hD 0)
    (isClosed_outer 0) (outer_subset hε hD 0) (disjoint_ring_outer 0)
  obtain ⟨q, hq, -⟩ := hfar A (mem_ball_self hε)
  have hqr : q ∉ ring A ε 0 := fun h => by
    have := h.2.trans (rad_lt_eps hε 0); linarith
  obtain ⟨c, -, hc, -⟩ := build hε hfar (isOpen_ring 0) hx₀ Subset.rfl hapos hqr
  exact ⟨c, hc⟩

/-- **One step**: from stage `n` to stage `n + 1`. -/
theorem step (hε : 0 < ε) (hfar : ∀ p ∈ ball A ε, ∃ q, ε < dist q A ∧ ¬ AposAt q p)
    (hD : closedBall A ε ⊆ D) (hnc : ¬ ∃ x ∈ D, ∃ y ∈ D, ∃ z ∈ D, CutsPts y x z) {n : ℕ}
    {c : Cfg X} (hc : Good A ε n c) : ∃ c' : Cfg X, Good A ε (n + 1) c' ∧ Rel c c' := by
  have hWo := hc.W_inter_open
  obtain ⟨hs, -, hball, hgood, hW, hQ, hWQ, hcov, w₀, hw₀W, hw₀⟩ := hc
  set D' := ring A ε (n + 1) ∩ c.Qᶜ with hD'def
  have hD'open : IsOpen D' := (isOpen_ring _).inter hQ.isOpen_compl
  have hD'W : D' ⊆ c.W := by
    rintro p ⟨hpr, hpQ⟩
    have hpV : p ∈ (ball c.x c.s)ᶜ := fun h => by
      have h1 := (hball (ball_subset_closedBall h)).2
      have h2 : rad ε n < dist p A := hpr.1
      linarith
    have : p ∈ c.W ∪ c.Q := hcov.symm ▸ hpV
    exact this.resolve_right hpQ
  have hrr := rad_strictMono hε (Nat.lt_succ_self n)
  have hD'ne : D'.Nonempty := by
    obtain ⟨w, hwW, hw⟩ := exists_mem_dist_eq hW hWo (rad_pos hε n).le
      (a := (rad ε n + rad ε (n + 1)) / 2) (by linarith) hw₀W
      (by have := rad_lt_eps hε (n + 1); linarith)
    refine ⟨w, ⟨?_, ?_⟩, fun h => Set.disjoint_left.mp hWQ hwW h⟩
    · show rad ε n < dist w A; rw [hw]; linarith
    · rw [hw]; linarith
  obtain ⟨x', hx'D', hx'apos⟩ := exists_apos_point hnc hD'open hD'ne
    (inter_subset_left.trans (ring_subset hε hD _)) (isClosed_outer _) (outer_subset hε hD _)
    ((disjoint_ring_outer (n + 1)).mono_left inter_subset_left)
  have hx'outer : x' ∈ outer A ε n := by
    refine ⟨hx'D'.1.1.le, ?_⟩
    have := hx'D'.1.2.trans (rad_lt hε (n + 1)); exact this.le
  obtain ⟨H, hH, hballH, hx'H⟩ := hgood x' hx'outer
  set G := D' ∩ Hᶜ with hGdef
  have hGopen : IsOpen G := hD'open.inter hH.1.isClosed.isOpen_compl
  have hcxG : c.x ∉ G := fun h => h.2 (hballH (mem_closedBall_self hs.le))
  obtain ⟨c', hc'x, hc'good, hc'G, hcxQ⟩ := build hε hfar hGopen ⟨hx'D', hx'H⟩
    (inter_subset_left.trans inter_subset_left) hx'apos hcxG
  refine ⟨c', hc'good, hc'G.trans (inter_subset_left.trans hD'W), hcxQ, H, hH, hballH, ?_⟩
  rw [Set.disjoint_right]
  intro p hp
  exact (hc'G hp).2

/-- **Jones's construction, conclusion.** Under the hypotheses on `A` and `ε`, three points of
`D` are such that one cuts the other two. -/
theorem core (hε : 0 < ε) (hfar : ∀ p ∈ ball A ε, ∃ q, ε < dist q A ∧ ¬ AposAt q p)
    (hD : closedBall A ε ⊆ D) : ∃ x ∈ D, ∃ y ∈ D, ∃ z ∈ D, CutsPts y x z := by
  by_contra hnc
  haveI : Nonempty (Cfg X) := ⟨⟨A, 0, ∅, ∅⟩⟩
  have hstep := fun n (c : Cfg X) (hc : Good A ε n c) => step hε hfar hD hnc hc
  choose! nxt hnxt using hstep
  obtain ⟨c₀, hc₀⟩ := init hε hfar hD hnc
  let cfg : ℕ → Cfg X := fun n => Nat.rec c₀ (fun k c => nxt k c) n
  have hcfgS : ∀ n, cfg (n + 1) = nxt n (cfg n) := fun n => rfl
  have hgood : ∀ n, Good A ε n (cfg n) := by
    intro n
    induction n with
    | zero => exact hc₀
    | succ n ih => rw [hcfgS]; exact (hnxt n _ ih).1
  have hrel : ∀ n, Rel (cfg n) (cfg (n + 1)) := fun n => (hnxt n _ (hgood n)).2
  -- the separations are nested
  have hnest : ∀ n, (cfg (n + 1)).W ⊆ (cfg n).W ∧ (cfg n).Q ⊆ (cfg (n + 1)).Q := by
    intro n
    obtain ⟨hs, -, -, -, hW, hQ, hWQ, hcov, -⟩ := hgood n
    obtain ⟨-, -, -, -, hW', hQ', hWQ', hcov', -⟩ := hgood (n + 1)
    obtain ⟨hb', hxQ', H, hH, hballH, hHdisj⟩ := hrel n
    have hHQ : H ⊆ (cfg (n + 1)).Q := by
      refine subset_of_isPreconnected_of_closed_cover hH.2.isPreconnected hW' hQ' hWQ' ?_
        ⟨(cfg n).x, hballH (mem_closedBall_self hs.le), hxQ'⟩
      rw [hcov']
      exact fun p hp hpb => Set.disjoint_left.mp hHdisj hp (ball_subset_closedBall hpb)
    exact separation_nested ⟨_, mem_ball_self hs⟩ hW hQ' hWQ hcov hWQ' hcov'
      (closure_ball_subset_closedBall.trans (hballH.trans hHQ))
      (closure_ball_subset_closedBall.trans hb') hW' hQ
  have hQmono : ∀ n, (cfg 1).Q ⊆ (cfg (n + 1)).Q := by
    intro n
    induction n with
    | zero => exact Subset.rfl
    | succ n ih => exact ih.trans (hnest (n + 1)).2
  -- the point `z`
  have hsph : IsClosed {p : X | dist p A = ε} :=
    isClosed_eq (continuous_id.dist continuous_const) continuous_const
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => (cfg (n + 1)).W ∩ {p : X | dist p A = ε})
    (fun n => inter_subset_inter_left _ (hnest (n + 1)).1)
    (fun n => by
      obtain ⟨-, -, -, -, hW, -, -, -, w, hwW, hw⟩ := hgood (n + 1)
      obtain ⟨w', hw'W, hw'⟩ := exists_mem_dist_eq hW (hgood (n + 1)).W_inter_open
        (rad_pos hε _).le (rad_lt_eps hε _) hwW hw
      exact ⟨w', hw'W, hw'⟩)
    (((hgood 1).2.2.2.2.1.inter hsph).isCompact)
    (fun n => (hgood (n + 1)).2.2.2.2.1.inter hsph)
  have hzW : ∀ n, z ∈ (cfg (n + 1)).W := fun n => (mem_iInter.mp hz n).1
  have hzA : dist z A = ε := (mem_iInter.mp hz 0).2
  -- the point `y`
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := fun n => (cfg n).x)
    (fun n => mem_univ _)
  have hxr : ∀ n, (cfg n).x ∈ ring A ε n := fun n =>
    (hgood n).2.2.1 (mem_closedBall_self (hgood n).1.le)
  have hlimd : Tendsto (fun m => dist (cfg (φ m)).x A) atTop (𝓝 (dist y A)) :=
    hlim.dist tendsto_const_nhds
  have hyA_le : dist y A ≤ ε / 2 :=
    le_of_tendsto hlimd (Eventually.of_forall fun m => ((hxr (φ m)).2.trans (rad_lt hε _)).le)
  have hyA_ge : ∀ k, rad ε k ≤ dist y A := fun k =>
    ge_of_tendsto hlimd (eventually_atTop.mpr ⟨k + 1, fun m hm =>
      (lo_ge hε (by have : m ≤ φ m := hφ.id_le m; omega)).trans (hxr (φ m)).1.le⟩)
  -- the three points lie in `D`
  have hx0A : dist (cfg 0).x A < rad ε 0 := (hxr 0).2
  have hx0D : (cfg 0).x ∈ D := hD (mem_closedBall.mpr (hx0A.trans (rad_lt_eps hε 0)).le)
  have hyD : y ∈ D := hD (mem_closedBall.mpr (hyA_le.trans (by linarith)))
  have hzD : z ∈ D := hD (mem_closedBall.mpr hzA.le)
  apply hnc
  refine ⟨(cfg 0).x, hx0D, y, hyD, z, hzD, ?_, ?_, ?_, fun K hK hx0K hzK => ?_⟩
  · intro h; have := hyA_ge 0; rw [h] at hx0A; linarith
  · intro h; rw [h] at hzA; linarith
  · intro h; rw [h] at hx0A; have := rad_lt_eps hε 0; linarith
  · by_contra hyK
    have hη : 0 < infDist y K := (hK.1.isClosed.notMem_iff_infDist_pos ⟨z, hzK⟩).mp hyK
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hη)
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hlim (infDist y K / 2) (half_pos hη)
    set m := max N₁ (N + 1) with hm
    have hi1 : N + 1 ≤ φ m := (le_max_right _ _).trans (hφ.id_le m)
    have hdist : dist (cfg (φ m)).x y < infDist y K / 2 := hN₁ m (le_max_left _ _)
    have hsi : (cfg (φ m)).s < infDist y K / 2 := by
      refine (hgood (φ m)).2.1.trans_le (le_trans ?_ hN.le)
      refine one_div_le_one_div_of_le (by positivity) ?_
      have : (N : ℝ) + 1 ≤ (φ m : ℝ) := by exact_mod_cast hi1
      linarith
    have hKV : K ⊆ (ball (cfg (φ m)).x (cfg (φ m)).s)ᶜ := by
      intro k hk hkb
      have h1 : infDist y K ≤ dist y k := infDist_le_dist_of_mem hk
      have h2 : dist y k ≤ dist k (cfg (φ m)).x + dist (cfg (φ m)).x y := by
        rw [dist_comm y k]; exact dist_triangle _ _ _
      have h3 : dist k (cfg (φ m)).x < (cfg (φ m)).s := hkb
      linarith
    obtain ⟨j, hj⟩ : ∃ j, φ m = j + 1 := ⟨φ m - 1, by omega⟩
    obtain ⟨-, -, -, -, hWi, hQi, hWQi, hcovi, -⟩ := hgood (φ m)
    have hzWi : z ∈ (cfg (φ m)).W := hj ▸ hzW j
    have hx0Q : (cfg 0).x ∈ (cfg (φ m)).Q := hj ▸ hQmono j (hrel 0).2.1
    have hKW : K ⊆ (cfg (φ m)).W := by
      refine subset_of_isPreconnected_of_closed_cover hK.2.isPreconnected hQi hWi hWQi.symm ?_
        ⟨z, hzK, hzWi⟩
      rw [union_comm, hcovi]; exact hKV
    exact Set.disjoint_left.mp hWQi (hKW hx0K) hx0Q

end T13J

/-- **Theorem 13.** Let `D` be open (nonempty), and suppose that for each `p ∈ D` there is a point
`o ≠ p` such that `X` is not aposyndetic at `o` with respect to `p`. Then `D` contains distinct
`x`, `y`, `z` with `y` cutting `x` from `z`. (The longest proof of the paper.) -/
theorem theorem13 {D : Set X} (hD : IsOpen D) (hDne : D.Nonempty)
    (h : ∀ p ∈ D, ∃ o, o ≠ p ∧ ¬ AposAt o p) :
    ∃ x ∈ D, ∃ y ∈ D, ∃ z ∈ D, CutsPts y x z := by
  set F : ℕ → Set X := fun n => Prod.snd '' ({p : X × X | ¬ AposAt p.1 p.2} ∩
    {p : X × X | 1 / ((n : ℝ) + 1) ≤ dist p.1 p.2}) with hF
  have hFcl : ∀ n, IsClosed (F n) := fun n => isClosed_snd_image
    (isClosed_setOf_not_aposAt.inter (isClosed_le continuous_const continuous_dist))
  have hcov : D ⊆ ⋃ n, F n := by
    intro p hp
    obtain ⟨o, hop, hna⟩ := h p hp
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.mpr hop)
    exact mem_iUnion.mpr ⟨n, (o, p), ⟨hna, hn.le⟩, rfl⟩
  obtain ⟨n, A, r, hr, hball⟩ := exists_ball_subset_of_closed_cover hD hDne hFcl hcov
  set ε := min (r / 2) (1 / (3 * ((n : ℝ) + 1))) with hεdef
  have hε : 0 < ε := lt_min (half_pos hr) (by positivity)
  have hεr : ε < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hε3 : 3 * ε ≤ 1 / ((n : ℝ) + 1) := by
    have h1 : ε ≤ 1 / (3 * ((n : ℝ) + 1)) := min_le_right _ _
    have h2 : 1 / (3 * ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) / 3 := by
      field_simp
    rw [h2] at h1
    linarith
  have hεD : closedBall A ε ⊆ D := fun p hp => (hball (closedBall_subset_ball hεr hp)).1
  refine T13J.core hε (fun p hp => ?_) hεD
  obtain ⟨⟨q, p'⟩, ⟨hna, hd⟩, hp'⟩ := (hball (ball_subset_ball hεr.le hp)).2
  simp only at hp' hna hd
  subst hp'
  refine ⟨q, ?_, hna⟩
  have h1 : dist q p' ≤ dist q A + dist A p' := dist_triangle _ _ _
  have h2 : dist A p' < ε := by rw [dist_comm]; exact hp
  have hd' : 1 / ((n : ℝ) + 1) ≤ dist q p' := hd
  linarith

end HPC.Jones
