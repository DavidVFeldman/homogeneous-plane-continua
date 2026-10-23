import HPC.Plane.Thm12B

/-!
# Batch 107: Bing 1951 (Duke) Theorem 5 — uncountably many disjoint plane copies of a snake-like
# continuum

COMMISSION-batch107.md. Bing (p. 655): *If `M` is a snake-like continuum, there is an uncountable
collection `W` of mutually exclusive continua in the plane such that each element of `W` is
homeomorphic with `M`.* His proof cites Theorem 1 of Moore [10]. Here instead: the construction of
Theorem 4 (`T4.lean`: a sequence of `TStage`s, `tN = ⋂ D_i^*`, `exists_homeomorph_tN`) is run along
a binary tree. At each level the tame chain `Φ(stdRect j)` is first squeezed into two disjoint
sub-strips of itself — lower, `y ↦ (y + 1/2)/3`, and upper, `y ↦ (y + 7/4)/3`, both affine
homeomorphisms of the plane carrying `stdRect j` into `stdRect j` — and the step of Theorem 4
(`t4_step`) is then taken inside each. A branch `b : ℕ → Bool` selects a strip at each level; its
intersection `tNb b` is homeomorphic to `M` by the argument of `exists_homeomorph_tN` (factored
here as `exists_homeomorph_gN`, over any sequence of stages with the `t4_step` properties), and two
branches that differ first at level `i` have level-`(i+1)` chains with disjoint unions, so their
continua are disjoint.

Shape changes against the skeleton (recorded in the report):
* `squeeze_stdRect_subset` is **false as stated** (the squeezes fix `x`, so the closure of the
  image reaches the vertical sides `x = 2j`, `x = 2j + 3`, which are not in the open rectangle);
  it is commented out, its negation is proved (`not_squeeze_stdRect_subset`), and it is replaced by
  `squeeze_image_stdRect_subset` (no closure), which is all the construction uses.
* `t4_step_branch` keeps the zone clause of `t4_step` (in the form `⊆ S.Φ '' zone k`), which the
  mesh estimate of the plane chains needs.
-/

namespace HPC.Plane

open Set Topology Metric

variable {X : Type*} [MetricSpace X]

/-! ### 1. Squeezes -/

/-- The vertical shift of the squeeze: `1/2` (lower) or `7/4` (upper). -/
noncomputable def squeezeShift (b : Bool) : ℝ := cond b (7 / 4) (1 / 2)

/-- The lower squeeze `(x, y) ↦ (x, (y + 1/2)/3)` and the upper squeeze
`(x, y) ↦ (x, (y + 7/4)/3)`, as homeomorphisms of the plane. -/
noncomputable def squeeze (b : Bool) : Pt ≃ₜ Pt where
  toFun p := (p.1, (p.2 + squeezeShift b) / 3)
  invFun p := (p.1, 3 * p.2 - squeezeShift b)
  left_inv p := by ext <;> simp; ring
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem squeeze_apply (b : Bool) (p : Pt) :
    squeeze b p = (p.1, (p.2 + squeezeShift b) / 3) := rfl

/-- The squeezes carry `[0, 1]` into `[1/6, 11/12] ⊆ (0, 1)`. -/
theorem squeeze_snd_bounds (b : Bool) {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    1 / 6 ≤ (y + squeezeShift b) / 3 ∧ (y + squeezeShift b) / 3 ≤ 11 / 12 := by
  cases b <;> simp only [squeezeShift, cond_false, cond_true] <;> constructor <;> linarith

/- **False as stated** (`not_squeeze_stdRect_subset` below): the squeezes fix the first
coordinate, so the closure of `squeeze b '' stdRect j` contains the point `(2j, (1/2 + c)/3)` on the
left side of the rectangle, which is not in the open rectangle `stdRect j`. Replaced by
`squeeze_image_stdRect_subset`.

theorem squeeze_stdRect_subset (b : Bool) (j : ℕ) :
    closure (squeeze b '' stdRect j) ⊆ stdRect j := by
  sorry
-/

/-- The skeleton's `squeeze_stdRect_subset` is false: for every `b` and `j`. -/
theorem not_squeeze_stdRect_subset (b : Bool) (j : ℕ) :
    ¬ closure (squeeze b '' stdRect j) ⊆ stdRect j := by
  intro h
  have hcl : closure (stdRect j) = Icc (2 * (j : ℝ)) (2 * j + 3) ×ˢ Icc 0 1 := by
    rw [stdRect, closure_prod_eq, closure_Ioo (by linarith), closure_Ioo (by norm_num)]
  have hp : ((2 * (j : ℝ)), (1 / 2 + squeezeShift b) / 3) ∈ closure (squeeze b '' stdRect j) := by
    rw [← (squeeze b).image_closure, hcl]
    exact ⟨(2 * (j : ℝ), 1 / 2), ⟨⟨le_refl _, by linarith⟩, by norm_num, by norm_num⟩, rfl⟩
  have := (h hp).1.1
  exact lt_irrefl _ this

/-- Corrected form: the squeezes carry each standard rectangle into itself. -/
theorem squeeze_image_stdRect_subset (b : Bool) (j : ℕ) : squeeze b '' stdRect j ⊆ stdRect j := by
  rintro _ ⟨⟨x, y⟩, ⟨hx, hy0, hy1⟩, rfl⟩
  obtain ⟨h1, h2⟩ := squeeze_snd_bounds b hy0.le hy1.le
  exact ⟨hx, by simp only [squeeze_apply]; linarith, by simp only [squeeze_apply]; linarith⟩

/-- The squeezes carry each zone into itself. -/
theorem squeeze_image_zone_subset (b : Bool) (k : ℕ) : squeeze b '' zone k ⊆ zone k := by
  rintro _ ⟨⟨x, y⟩, ⟨hx, hy0, hy1⟩, rfl⟩
  obtain ⟨h1, h2⟩ := squeeze_snd_bounds b hy0 hy1
  exact ⟨hx, by simp only [squeeze_apply]; linarith, by simp only [squeeze_apply]; linarith⟩

theorem squeeze_disjoint (j j' : ℕ) :
    Disjoint (squeeze false '' stdRect j) (squeeze true '' stdRect j') := by
  rw [Set.disjoint_left]
  rintro _ ⟨⟨x, y⟩, ⟨-, hy0, hy1⟩, rfl⟩ ⟨⟨x', y'⟩, ⟨-, hy0', hy1'⟩, he⟩
  simp only [squeeze_apply, squeezeShift, cond_false, cond_true, Prod.mk.injEq] at he
  linarith [he.2]

/-! ### Factoring `exists_homeomorph_tN` over any sequence of stages -/

/-- The properties of `t4_step` between two consecutive stages, with mesh bound `ε`. -/
def TStep {M : Set X} (S S' : TStage M) (ε : ℝ) : Prop :=
  ∃ x : Fin S'.m → Fin S.m,
    (∀ t, S'.C.link t ⊆ S.C.link (x t)) ∧
    (∀ t, closure ((tameChain S'.Φ S'.m).link t) ⊆ (tameChain S.Φ S.m).link (x t)) ∧
    Function.Surjective x ∧
    (∀ t, Bornology.IsBounded (S'.C.link t) ∧ diam (S'.C.link t) < ε) ∧
    (∀ t, diam ((tameChain S'.Φ S'.m).link t) ≤ ε ∨
      ∃ k : ℕ, k < S.m ∧ (tameChain S'.Φ S'.m).link t ⊆ S.Φ '' zone k) ∧
    (∀ k : ℕ, k < S'.m → Bornology.IsBounded (S'.Φ '' zone k) ∧ diam (S'.Φ '' zone k) ≤ ε)

section Generic

variable {M : Set X} (T : ℕ → TStage M)
  (h0 : (T 0).Φ = Homeomorph.refl Pt ∧
    ∀ t, Bornology.IsBounded ((T 0).C.link t) ∧ diam ((T 0).C.link t) < 1)
  (hs : ∀ i, TStep (T i) (T (i + 1)) (1 / 2 ^ i))

/-- The plane set `⋂ D_i^*` of a sequence of stages. -/
def gN : Set Pt := ⋂ i, (tameChain (T i).Φ (T i).m).union

include h0 hs in
theorem gzone_diam (i : ℕ) (k : ℕ) (hk : k < (T i).m) :
    Bornology.IsBounded ((T i).Φ '' zone k) ∧ diam ((T i).Φ '' zone k) ≤ 2 / 2 ^ i := by
  cases i with
  | zero =>
      have e : (T 0).Φ '' zone k = zone k := by
        rw [h0.1]; ext p; simp
      rw [e]
      refine ⟨(isCompact_zone k).isBounded, ?_⟩
      refine diam_le_of_forall_dist_le (by norm_num) ?_
      rintro ⟨a, b⟩ ⟨⟨h1, h2⟩, h3, h4⟩ ⟨c, d⟩ ⟨⟨h5, h6⟩, h7, h8⟩
      apply dist_le_of_abs_le
      · rw [abs_le]; simp only at *; constructor <;> linarith
      · rw [abs_le]; simp only at *; constructor <;> linarith
  | succ i =>
      obtain ⟨-, -, -, -, -, -, h⟩ := hs i
      obtain ⟨b, d⟩ := h k hk
      refine ⟨b, d.trans (le_of_eq ?_)⟩
      rw [pow_succ]; field_simp

include h0 hs in
theorem glink_diam (i : ℕ) (t : Fin (T i).m) :
    diam ((tameChain (T i).Φ (T i).m).link t) ≤ 4 / 2 ^ i := by
  cases i with
  | zero =>
      have e : (tameChain (T 0).Φ (T 0).m).link t = stdRect t := by
        simp only [tameChain_link, h0.1]; ext p; simp
      rw [e]; simp only [pow_zero, div_one]
      refine (diam_le_of_forall_dist_le (by norm_num) ?_).trans (by norm_num : (3 : ℝ) ≤ 4)
      rintro ⟨a, b⟩ ⟨⟨h1, h2⟩, h3, h4⟩ ⟨c, d⟩ ⟨⟨h5, h6⟩, h7, h8⟩
      apply dist_le_of_abs_le
      · rw [abs_le]; simp only at *; constructor <;> linarith
      · rw [abs_le]; simp only at *; constructor <;> linarith
  | succ i =>
      obtain ⟨-, -, -, -, -, h, -⟩ := hs i
      rcases h t with h | ⟨k, hk, hsub⟩
      · refine h.trans ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
        nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) i]
      · obtain ⟨b, d⟩ := gzone_diam T h0 hs i k hk
        refine (diam_mono hsub b).trans (d.trans (le_of_eq ?_))
        rw [pow_succ]; field_simp; norm_num

include h0 hs in
theorem gC_diam (i : ℕ) (t : Fin (T i).m) :
    Bornology.IsBounded ((T i).C.link t) ∧ diam ((T i).C.link t) < 8 / 2 ^ i := by
  cases i with
  | zero =>
      obtain ⟨b, d⟩ := h0.2 t
      exact ⟨b, by simp only [pow_zero, div_one]; linarith⟩
  | succ i =>
      obtain ⟨-, -, -, -, h, -, -⟩ := hs i
      obtain ⟨b, d⟩ := h t
      refine ⟨b, d.trans ?_⟩
      rw [div_lt_div_iff₀ (by positivity) (by positivity), pow_succ]
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) i]

theorem gchain_closure_compact (i : ℕ) (t : Fin (T i).m) :
    IsCompact (closure ((tameChain (T i).Φ (T i).m).link t)) := by
  rw [closure_tameChain_link]
  exact (isCompact_closure_stdRect t).image (T i).Φ.continuous

include hs in
theorem isCompact_gN : IsCompact (gN T) := by
  refine isCompact_iInter_union (fun i => tameChain (T i).Φ (T i).m) (fun i t => ?_)
    (gchain_closure_compact T)
  obtain ⟨x, -, h, -⟩ := hs i
  exact ⟨x t, h t⟩

include hs in
theorem gchain_meets (i : ℕ) (s : Fin (T i).m) :
    ((tameChain (T i).Φ (T i).m).link s ∩ gN T).Nonempty := by
  refine link_inter_iInter_union_nonempty (fun i => tameChain (T i).Φ (T i).m) (fun i s => ?_)
    (fun i t => ?_) (gchain_closure_compact T) i s
  · obtain ⟨x, -, h, hsj, -⟩ := hs i
    obtain ⟨t, rfl⟩ := hsj s
    exact ⟨t, h t⟩
  · obtain ⟨x, -, h, -⟩ := hs i
    exact ⟨x t, h t⟩

include h0 hs in
/-- **`exists_homeomorph_tN`, factored**: any sequence of stages starting from the standard
rectangles and linked by the `t4_step` properties with `ε = 1/2^i` gives a plane set
homeomorphic to `M`. -/
theorem exists_homeomorph_gN (hMc : IsCompact M) (hMconn : IsConnected M) :
    Nonempty (M ≃ₜ gN T) := by
  have hεpos : ∀ i : ℕ, (0 : ℝ) < 8 / 2 ^ i := fun i => by positivity
  have hsum : Summable (fun i : ℕ => (8 : ℝ) / 2 ^ i) := by
    have := (summable_geometric_two).mul_left 8
    refine this.congr fun i => ?_
    rw [one_div, inv_pow]; ring
  have htl : ∀ i t, diam ((tameChain (T i).Φ (T i).m).link t) < 8 / 2 ^ i := fun i t => by
    have := glink_diam T h0 hs i t
    have : (4 : ℝ) / 2 ^ i < 8 / 2 ^ i := by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num
    linarith
  obtain ⟨H, -⟩ := MatchingCovers.exists_homeomorph
    (M₁ := M) (M₂ := gN T) (ε := fun i => 8 / 2 ^ i)
    { N := fun i => (T i).m
      x₁ := fun i => (T i).C.link
      x₂ := fun i => (tameChain (T i).Φ (T i).m).link
      open₁ := fun i => (T i).C.isOpen
      open₂ := fun i => (tameChain (T i).Φ (T i).m).isOpen
      cover₁ := fun i => (T i).hC.1
      cover₂ := fun i => iInter_subset _ i
      meet₁ := fun i k => (T i).hC.meets hMconn k
      meet₂ := fun i k => gchain_meets T hs i k
      bdd₁ := fun i k => (gC_diam T h0 hs i k).1
      bdd₂ := fun i k => tameChain_link_bounded _ _ k
      diam₁ := fun i k => (gC_diam T h0 hs i k).2.le
      diam₂ := fun i k => (htl i k).le
      match₁ := by
        intro i j k hjk
        obtain ⟨x, h1, h2, -⟩ := hs i
        exact Chain.pattern_matching (Y₂ := tameChain (T (i + 1)).Φ (T (i + 1)).m)
          (Z₂ := tameChain (T i).Φ (T i).m) x h1
          (fun t => subset_closure.trans (h2 t)) (htl i)
          (fun s => tameChain_link_bounded _ _ s) j k hjk
      match₂ := by
        intro i j k hjk
        obtain ⟨x, h1, h2, -⟩ := hs i
        exact Chain.pattern_matching (Y₁ := tameChain (T (i + 1)).Φ (T (i + 1)).m)
          (Z₁ := tameChain (T i).Φ (T i).m) x
          (fun t => subset_closure.trans (h2 t)) h1 (fun s => (gC_diam T h0 hs i s).2)
          (fun s => (gC_diam T h0 hs i s).1) j k hjk }
    hMc (isCompact_gN T hs) hεpos hsum
  exact ⟨H⟩

end Generic

/-! ### 2. The branching step -/

/-- **One branching step.** From a stage `S` and a bit `b`, a stage `S'` with the properties of
`t4_step` (refinement of `S.C` and of the tame chain, surjective block map, mesh `< ε`, the
slowness/zone clause) and in addition: every link of the new tame chain has closure in
`S.Φ '' (squeeze b '' stdRect (x t))`. The two choices of `b` give tame chains with disjoint
unions. -/
theorem t4_step_branch {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (S : TStage M) (b : Bool) {ε : ℝ} (hε : 0 < ε) :
    ∃ S' : TStage M, ∃ x : Fin S'.m → Fin S.m,
      (∀ t, S'.C.link t ⊆ S.C.link (x t)) ∧
      (∀ t, closure ((tameChain S'.Φ S'.m).link t) ⊆ S.Φ '' (squeeze b '' stdRect (x t))) ∧
      Function.Surjective x ∧
      (∀ t, Bornology.IsBounded (S'.C.link t) ∧ diam (S'.C.link t) < ε) ∧
      (∀ t, diam ((tameChain S'.Φ S'.m).link t) ≤ ε ∨
        ∃ k : ℕ, k < S.m ∧ (tameChain S'.Φ S'.m).link t ⊆ S.Φ '' zone k) ∧
      (∀ k : ℕ, k < S'.m → Bornology.IsBounded (S'.Φ '' zone k) ∧ diam (S'.Φ '' zone k) ≤ ε) := by
  let Sb : TStage M := ⟨S.m, S.C, (squeeze b).trans S.Φ, S.hm, S.hC⟩
  obtain ⟨S', x, h1, h2, h3, h4, h5, h6⟩ := t4_step hMc hMconn hsnake Sb hε
  refine ⟨S', x, h1, fun t => ?_, h3, h4, fun t => ?_, h6⟩
  · refine (h2 t).trans (le_of_eq ?_)
    show ((squeeze b).trans S.Φ) '' stdRect (x t) = _
    rw [← image_comp]; rfl
  · rcases h5 t with h | ⟨k, hk, hsub⟩
    · exact Or.inl h
    · refine Or.inr ⟨k, hk, hsub.trans ?_⟩
      show ((squeeze b).trans S.Φ) '' zone k ⊆ S.Φ '' zone k
      rw [show ((squeeze b).trans S.Φ) '' zone k = S.Φ '' (squeeze b '' zone k) by
        rw [← image_comp]; rfl]
      exact image_mono (squeeze_image_zone_subset b k)

/-! ### 3. The tree -/

/-- The stage chosen by `t4_step_branch` from `S` with bit `c` at level `i` (`ε = 1/2^i`). -/
noncomputable def branchNext {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (S : TStage M) (c : Bool) (i : ℕ) : TStage M :=
  Classical.choose (t4_step_branch hMc hMconn hsnake S c (ε := 1 / 2 ^ i) (by positivity))

/-- **The tree of stages**: `tstageTree b i` is the stage reached after following the first `i`
bits of `b`; it depends only on those bits. -/
noncomputable def tstageTree {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (b : ℕ → Bool) : ℕ → TStage M
  | 0 => Classical.choose (exists_t4_base hMconn hsnake)
  | i + 1 => branchNext hMc hMconn hsnake (tstageTree hMc hMconn hsnake b i) (b i) i

theorem tstageTree_prefix {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (b b' : ℕ → Bool) (i : ℕ) (h : ∀ k < i, b k = b' k) :
    tstageTree hMc hMconn hsnake b i = tstageTree hMc hMconn hsnake b' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have e1 := ih (fun k hk => h k (by omega))
      have e2 : b i = b' i := h i (by omega)
      simp only [tstageTree]
      rw [e1, e2]

section TreeSpec

variable {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)

theorem tstageTree_zero (b : ℕ → Bool) :
    (tstageTree hMc hMconn hsnake b 0).Φ = Homeomorph.refl Pt ∧
    ∀ t, Bornology.IsBounded ((tstageTree hMc hMconn hsnake b 0).C.link t) ∧
      diam ((tstageTree hMc hMconn hsnake b 0).C.link t) < 1 :=
  Classical.choose_spec (exists_t4_base hMconn hsnake)

theorem tstageTree_tstep (b : ℕ → Bool) (i : ℕ) :
    TStep (tstageTree hMc hMconn hsnake b i) (tstageTree hMc hMconn hsnake b (i + 1))
      (1 / 2 ^ i) := by
  obtain ⟨x, h1, h2, h3, h4, h5, h6⟩ := Classical.choose_spec
    (t4_step_branch hMc hMconn hsnake (tstageTree hMc hMconn hsnake b i) (b i)
      (ε := 1 / 2 ^ i) (by positivity))
  exact ⟨x, h1, fun t => (h2 t).trans (image_mono (squeeze_image_stdRect_subset _ _)), h3, h4,
    h5, h6⟩

theorem tstageTree_squeeze (b : ℕ → Bool) (i : ℕ)
    (t : Fin (tstageTree hMc hMconn hsnake b (i + 1)).m) :
    ∃ s : ℕ, (tameChain (tstageTree hMc hMconn hsnake b (i + 1)).Φ
        (tstageTree hMc hMconn hsnake b (i + 1)).m).link t ⊆
      (tstageTree hMc hMconn hsnake b i).Φ '' (squeeze (b i) '' stdRect s) := by
  obtain ⟨x, -, h2, -⟩ := Classical.choose_spec
    (t4_step_branch hMc hMconn hsnake (tstageTree hMc hMconn hsnake b i) (b i)
      (ε := 1 / 2 ^ i) (by positivity))
  exact ⟨x t, subset_closure.trans (h2 t)⟩

end TreeSpec

/-- The plane continuum of the branch `b`. -/
def tNb {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (b : ℕ → Bool) : Set Pt :=
  ⋂ i, (tameChain (tstageTree hMc hMconn hsnake b i).Φ (tstageTree hMc hMconn hsnake b i).m).union

/-- Each branch is homeomorphic to `M` (the argument of `exists_homeomorph_tN`, factored as
`exists_homeomorph_gN`). -/
theorem exists_homeomorph_tNb {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (b : ℕ → Bool) : Nonempty (M ≃ₜ tNb hMc hMconn hsnake b) :=
  exists_homeomorph_gN (tstageTree hMc hMconn hsnake b) (tstageTree_zero hMc hMconn hsnake b)
    (tstageTree_tstep hMc hMconn hsnake b) hMc hMconn

theorem isContinuum_tNb {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (b : ℕ → Bool) : Fold.Q78.IsContinuum (tNb hMc hMconn hsnake b) := by
  refine ⟨isCompact_gN (tstageTree hMc hMconn hsnake b) (tstageTree_tstep hMc hMconn hsnake b), ?_⟩
  obtain ⟨T⟩ := exists_homeomorph_tNb hMc hMconn hsnake b
  haveI : ConnectedSpace M := isConnected_iff_connectedSpace.mp hMconn
  have h := isConnected_univ.image (fun p : M => (T p : Pt))
    ((continuous_subtype_val.comp T.continuous).continuousOn)
  convert h using 1
  ext q
  constructor
  · intro hq
    refine ⟨T.symm ⟨q, hq⟩, mem_univ _, ?_⟩
    simp
  · rintro ⟨p, -, rfl⟩
    exact (T p).2

/-! ### 4. Disjointness -/

/-- Branches differing at some bit give disjoint continua. -/
theorem tNb_disjoint {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    {b b' : ℕ → Bool} (h : b ≠ b') : Disjoint (tNb hMc hMconn hsnake b) (tNb hMc hMconn hsnake b') := by
  classical
  have hex : ∃ i, b i ≠ b' i := by
    by_contra hc
    push_neg at hc
    exact h (funext hc)
  set i := Nat.find hex with hi_def
  have hi : b i ≠ b' i := Nat.find_spec hex
  have hpre : ∀ k < i, b k = b' k := fun k hk => by
    by_contra hne
    exact Nat.find_min hex hk hne
  have e := tstageTree_prefix hMc hMconn hsnake b b' i hpre
  rw [Set.disjoint_left]
  intro p hp hp'
  obtain ⟨t, ht⟩ := mem_iUnion.mp (mem_iInter.mp hp (i + 1))
  obtain ⟨t', ht'⟩ := mem_iUnion.mp (mem_iInter.mp hp' (i + 1))
  obtain ⟨s, hs⟩ := tstageTree_squeeze hMc hMconn hsnake b i t
  obtain ⟨s', hs'⟩ := tstageTree_squeeze hMc hMconn hsnake b' i t'
  have h1 := hs ht
  have h2 := hs' ht'
  rw [e] at h1
  obtain ⟨q, hq, rfl⟩ := h1
  obtain ⟨q', hq', hqq⟩ := h2
  obtain rfl := (tstageTree hMc hMconn hsnake b' i).Φ.injective hqq
  revert hq hq' hi
  cases b i <;> cases b' i <;> intro hi hq' hq
  · exact hi rfl
  · exact Set.disjoint_left.mp (squeeze_disjoint s s') hq hq'
  · exact Set.disjoint_left.mp (squeeze_disjoint s' s) hq' hq
  · exact hi rfl

/-! ### 5. Theorem 5 -/

/-- **Bing 1951, Theorem 5.** A family of pairwise disjoint plane continua indexed by `ℕ → Bool`
(hence of the cardinality of the continuum), each homeomorphic to `M`. -/
theorem theorem5_1951 {M : Set X} (hM : IsSnakeLike M) :
    ∃ W : (ℕ → Bool) → Set Pt, (∀ b, Fold.Q78.IsContinuum (W b) ∧ Nonempty (M ≃ₜ W b)) ∧
      ∀ b b', b ≠ b' → Disjoint (W b) (W b') := by
  obtain ⟨⟨hMc, hMconn⟩, hsnake⟩ := hM
  exact ⟨tNb hMc hMconn hsnake, fun b => ⟨isContinuum_tNb hMc hMconn hsnake b,
    exists_homeomorph_tNb hMc hMconn hsnake b⟩, fun b b' h => tNb_disjoint hMc hMconn hsnake h⟩

/-- `ℕ → Bool` is not countable (Cantor: `Cardinal.cantor`). -/
theorem not_countable_nat_bool : ¬ Countable (ℕ → Bool) := by
  intro h
  have := Cardinal.mk_le_aleph0_iff.mpr h
  rw [Cardinal.mk_pi, Cardinal.mk_fintype] at this
  simp at this
  exact absurd this (not_le.mpr (Cardinal.cantor _))

/-- The collection is uncountable. -/
theorem theorem5_1951_uncountable {M : Set X} (hM : IsSnakeLike M) :
    ∃ 𝒲 : Set (Set Pt), ¬ 𝒲.Countable ∧ (∀ N ∈ 𝒲, Fold.Q78.IsContinuum N ∧ Nonempty (M ≃ₜ N)) ∧
      𝒲.PairwiseDisjoint id := by
  obtain ⟨W, hW, hdisj⟩ := theorem5_1951 hM
  have hinj : Function.Injective W := by
    intro b b' hbb
    by_contra hne
    obtain ⟨p, hp⟩ := (hW b).1.2.nonempty
    exact Set.disjoint_left.mp (hdisj b b' hne) hp (hbb ▸ hp)
  refine ⟨range W, fun hc => ?_, ?_, ?_⟩
  · have hu := hc.preimage hinj
    rw [preimage_range] at hu
    exact not_countable_nat_bool (Set.countable_univ_iff.mp hu)
  · rintro _ ⟨b, rfl⟩
    exact hW b
  · rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩ hne
    exact hdisj b b' fun h => hne (h ▸ rfl)

end HPC.Plane
