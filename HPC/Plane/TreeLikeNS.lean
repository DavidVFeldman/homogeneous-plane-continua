import HPC.Plane.Enc2
import HPC.Plane.Ingram68Star
import HPC.Plane.TreeLikeNSGraph
import HPC.Plane.TreeLikeNSLog

/-!
# Batch 133: tree-like plane continua contain no separating continuum; Bing 1951 (Duke)
# Theorem 7 as printed

Batch 133 delivery of the skeleton (original: `doc/batches/skeletons/TreeLikeNS.lean`,
commission `doc/batches/COMMISSION-batch133.md`). Every work item is proved; nothing in this file
or its two helper files is `sorry`. Report: `doc/batches/REPORT-batch133.md`.

**Changes of shape** (each also noted at the declaration):
* `toCpx` and `continuous_toCpx` are moved to the helper file `TreeLikeNSLog.lean` (same names,
  same namespace), so that the helper lemmas on logarithms can use them.
* `exists_log_on_ball`: statement as in the skeleton; the constant `4` suffices (the Euclidean
  norm of `toCpx` is at most twice the sup norm and at least the sup norm).
* `exists_log_on_treeChain` is proved from `exists_leaf` by induction on the number of links,
  carrying the ball invariant (`exists_log_inv`). The triple-intersection clause of tree chains is
  not used: a leaf meets exactly one other link.
* `exists_leaf` is proved without trees in the abstract: grow a chain-connected subcollection one
  link at a time (coherence) up to all links but one; the last link `C` meets exactly one link of
  the rest, since meeting two would produce, from a shortest chain between them, a circular
  subcollection (`TreeLikeNSGraph.lean`).
* `no_log_on_polygon`: the per-edge jump is `edge_jump` (`TreeLikeNSLog.lean`), with `θ = arg (p − z)`
  as in the header. Vertices on the east ray need no separate case: `arg` takes values in
  `(−π, π]` with `0 ≤ arg w ↔ 0 ≤ im w`, which is exactly the half-open convention of
  `CrossesEast` (`crossesEast_iff_cross`).
* `exists_polygon_around` uses the cut-wire theorem `exists_split_of_no_continuum` in the compact
  subspace `Wᶜ ∩ closedBall 0 R`, splitting off the sphere `dist · 0 = R`.
* The imports `HPC.Plane.Enc1Cyc`, `HPC.Plane.Cyc2Circle`, `HPC.Plane.Ingram68` are replaced by
  what is used: `HPC.Plane.Ingram68Star` (the cut wire) and the two helper files.

## Why

Bing states Theorem 7 for a *tree-like* plane continuum ("In the proof of Theorem 6 we establish
the following result"). The proof of Theorem 6 uses the hypothesis "M contains no continuum which
separates the plane". So Bing's Theorem 7 rests on an unstated step: a tree-like plane continuum
contains no continuum that separates the plane. That step is `treeLike_nonseparating`. It is
classical (tree-like continua are acyclic, and Borsuk's separation theorem applies), but neither
Bing nor the repository proves it. With it, Theorem 7 holds as printed (`theorem7_1951_treeLike`),
and Theorem 6 becomes an equivalence (`isTreeLike_iff_nonseparating`).

## The argument (no Borsuk, no Brouwer: logarithms and the crossing parity of batch 125)

Identify `Pt` with `ℂ` (`toCpx`).

1. **A logarithm on a fine tree cover.** Let `G` be a tree chain, all of whose links have
   diameter `< ε` and lie at distance `> 8ε` from `p`. Then `z ↦ z − p` has a continuous logarithm
   on `⋃ G` (`exists_log_on_treeChain`).
   * Each link `A` lies in a ball `D_A = ball c_A (3ε)` (sup metric) that misses `p`. A convex set
     missing `p` carries a continuous branch of `log (z − p)`.
   * Induct by removing a leaf. A leaf link `A` meets exactly one other link `B`. The ball
     branches on `D_A` and `D_B` differ by a constant on the convex set `D_A ∩ D_B ⊇ A ∩ B`.
     Shift the branch on `A` by that constant.
   * Invariant: on each link `A`, the logarithm is the restriction of a branch defined on all of
     `D_A`. This handles disconnected links and disconnected `A ∩ B`.
   * Graph theory needed: the nerve of a tree chain is a tree (no circular subcollection, so no
     chordless cycle, so no cycle; coherent, so connected). A tree with at least two vertices has a
     leaf whose removal leaves a tree chain.
2. **No logarithm on a polygon around `p`** (`no_log_on_polygon`). Suppose `J = polygonOf v` is
   simple, `p ∈ polyInterior J`, and `L` is continuous on `J` with `exp (L z) = z − p`.
   * Along each edge `[vᵢ, vᵢ₊₁]` (which misses `p`), `Im (L vᵢ₊₁ − L vᵢ) = αᵢ`, the signed angle
     subtended at `p`, with `αᵢ ∈ (−π, π)`.
   * Telescoping around the closed polygon gives `Σ αᵢ = 0`.
   * With `θ(z) = arg (p − z)`, whose cut is the *east* ray from `p`, `αᵢ = θ(vᵢ₊₁) − θ(vᵢ) + 2π jᵢ`
     with `jᵢ ∈ {−1, 0, 1}`. Also `jᵢ` is odd exactly when the edge crosses the east ray in the
     half-open sense of `CrossesEast`.
   * So `0 = Σ jᵢ ≡ crossCount ≡ parity v p = 1 (mod 2)` (`polyInterior_eq_oddSet`). Contradiction.
3. **A polygon in `W` around `p`** (`exists_polygon_around`). Let `W` be open, `p ∉ W`, with the
   component of `p` in `Wᶜ` bounded.
   * Cut-wire theorem (`exists_split_of_no_continuum`, batch 132, in a compact subspace) on
     `F = Wᶜ ∩ closedBall 0 R`: `F = F₁ ⊔ F₂` with `p ∈ F₁` and `F₁ ⊆ ball 0 R`.
   * Grid at mesh `δ` well below the distance from `F₁` to `F₂ ∪ (ball 0 R)ᶜ`: the frontier of the
     grid union of `F₁` lies in `W`.
   * The batch-130 odd-set argument for a *point* `x ∈ M` of a bounded `M` gives a simple closed
     polygon `J` on the boundary graph with `x ∈ polyInterior J`
     (`exists_enclosing_polygon_pt`). This is the proof of `exists_enclosing_polygon` with
     `x₀ := x`, needing only that `M` is bounded.
4. **Assembly** (`treeLike_nonseparating`).
   * Suppose `K ⊆ M` separates the plane. Take `p` in a bounded component of `Kᶜ`, and put
     `d = infDist p K`.
   * Take a tree chain for `M` of mesh `ε < d / 16`. The links meeting `K` form a tree chain `G'`;
     it is coherent because `K` is connected.
   * `W = ⋃ G'` contains `K`, lies within `ε` of `K`, and misses `p`.
   * The component of `p` in `Wᶜ` lies in that of `p` in `Kᶜ`, so it is bounded.
   * Step 3 gives a polygon `J ⊆ W` around `p`. Step 1 gives a logarithm on `W`. Restricting it
     to `J` contradicts step 2.
-/

namespace HPC.Plane

open Set Metric

open scoped Classical

/-! ### 0. The definition of tree-like (edit to `Tree67.lean`, COMMISSION-batch133.md §1)

`IsTreeLike` as defined up to batch 132 asks `diam A < ε` of the links but not boundedness.
Mathlib's `diam` of an unbounded set is `0`, so `{univ}` is a tree chain of every mesh, and every
continuum, a circle included, is "tree-like". The old definition is kept here under a new name,
and its triviality is proved. `Tree67.lean`'s `IsTreeLike` gets `Bornology.IsBounded A`, as
`IsEpsChain` (snake-like) has. -/

/-- The definition of `IsTreeLike` up to batch 132 (links not required to be bounded). -/
def IsTreeLikeOld (M : Set Pt) : Prop :=
  Fold.Q78.IsContinuum M ∧ ∀ ε : ℝ, 0 < ε → ∃ G : Finset (Set Pt), IsTreeChain G ∧
    (∀ A ∈ G, diam A < ε) ∧ M ⊆ ⋃ A ∈ G, A

/-- `{univ}` is a tree chain. -/
theorem isTreeChain_univ : IsTreeChain {(univ : Set Pt)} := by
  refine ⟨fun A hA => by rw [Finset.mem_singleton.1 hA]; exact isOpen_univ, ?_, ?_, ?_⟩
  · intro G' hG' hne
    obtain ⟨A, hA⟩ := hne
    have : G' = {univ} := Finset.eq_singleton_iff_unique_mem.2
      ⟨by rw [← Finset.mem_singleton.1 (hG'.1 hA)]; exact hA,
        fun B hB => Finset.mem_singleton.1 (hG'.1 hB)⟩
    exact absurd this hG'.ne
  · intro A hA B hB C hC hAB
    rw [Finset.mem_singleton.1 hA, Finset.mem_singleton.1 hB] at hAB
    exact absurd rfl hAB
  · rintro G' hG' ⟨m, hm, d, hd, rfl, -⟩
    have h1 := Finset.card_le_card hG'
    rw [Finset.card_image_of_injective _ hd, Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton] at h1
    omega

/-- **The old definition is trivial**: every continuum satisfies it (`G = {univ}`; `univ` is
unbounded, so `diam univ = 0`). Hence `treeLike_nonseparating` was false for it (a circle). -/
theorem isTreeLikeOld_of_isContinuum {M : Set Pt} (hM : Fold.Q78.IsContinuum M) :
    IsTreeLikeOld M := by
  refine ⟨hM, fun ε hε => ⟨{univ}, isTreeChain_univ, fun A hA => ?_, fun x _ => ?_⟩⟩
  · rw [Finset.mem_singleton.1 hA, diam_eq_zero_of_unbounded]
    · exact hε
    · intro hb
      obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : Pt)
      have := hR (mem_univ ((|R| + 1, 0) : Pt))
      rw [mem_closedBall, dist_zero_right, Prod.norm_def] at this
      simp only [Real.norm_eq_abs, norm_zero] at this
      have h2 : |R| + 1 ≤ max |(|R| + 1)| 0 := by
        rw [abs_of_pos (by positivity : (0:ℝ) < |R| + 1)]; exact le_max_left _ _
      linarith [le_abs_self R]
  · exact mem_iUnion₂.2 ⟨univ, Finset.mem_singleton_self _, mem_univ x⟩

/-! ### 1. A logarithm on a fine tree cover

(`toCpx` and `continuous_toCpx` are in `TreeLikeNSLog.lean`.) -/

theorem norm_toCpx_sub_le (z c : Pt) : ‖toCpx z - toCpx c‖ ≤ 2 * dist z c := by
  have h := Complex.norm_le_abs_re_add_abs_im (toCpx z - toCpx c)
  rw [show (toCpx z - toCpx c).re = z.1 - c.1 by simp [toCpx],
    show (toCpx z - toCpx c).im = z.2 - c.2 by simp [toCpx]] at h
  have h1 : |z.1 - c.1| ≤ dist z c := by
    rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_left _ _
  have h2 : |z.2 - c.2| ≤ dist z c := by
    rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_right _ _
  linarith

theorem dist_le_norm_toCpx_sub (z c : Pt) : dist z c ≤ ‖toCpx z - toCpx c‖ := by
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
  constructor
  · have := Complex.abs_re_le_norm (toCpx z - toCpx c)
    simpa [toCpx] using this
  · have := Complex.abs_im_le_norm (toCpx z - toCpx c)
    simpa [toCpx] using this

/-- On a convex set missing `p` there is a continuous branch of `log (z − p)`. Here:
`Complex.log ((z − p) / (c − p)) + Complex.log (c − p)` on `ball c r`, where `(z − p) / (c − p)`
stays in the right half-plane. -/
theorem exists_log_on_ball {p c : Pt} {r : ℝ} (hr : 0 < r) (hp : 4 * r < dist c p) :
    ∃ L : Pt → ℂ, ContinuousOn L (ball c r) ∧
      ∀ z ∈ ball c r, Complex.exp (L z) = toCpx z - toCpx p := by
  set D := toCpx c - toCpx p with hD
  have hDn : 4 * r < ‖D‖ := lt_of_lt_of_le hp (dist_le_norm_toCpx_sub c p)
  have hD0 : D ≠ 0 := by
    intro h; rw [h, norm_zero] at hDn; linarith
  have hre : ∀ z ∈ ball c r, 0 < ((toCpx z - toCpx p) / D).re := by
    intro z hz
    have hzc : ‖toCpx z - toCpx c‖ < 2 * r := by
      have := norm_toCpx_sub_le z c
      rw [mem_ball] at hz; linarith
    have heq : (toCpx z - toCpx p) / D = 1 + (toCpx z - toCpx c) / D := by
      rw [one_add_div hD0, hD]; congr 1; ring
    rw [heq, Complex.add_re, Complex.one_re]
    have h1 : ‖(toCpx z - toCpx c) / D‖ < 1 := by
      rw [norm_div, div_lt_one (norm_pos_iff.2 hD0)]; linarith
    have h2 := Complex.abs_re_le_norm ((toCpx z - toCpx c) / D)
    linarith [neg_abs_le ((toCpx z - toCpx c) / D).re]
  refine ⟨fun z => Complex.log ((toCpx z - toCpx p) / D) + Complex.log D, ?_, fun z hz => ?_⟩
  · refine ContinuousOn.add (ContinuousOn.clog ?_ fun z hz => Or.inl (hre z hz)) continuousOn_const
    exact ((continuous_toCpx.sub continuous_const).div_const _).continuousOn
  · have hne : (toCpx z - toCpx p) / D ≠ 0 := fun h => by
      have := hre z hz; rw [h, Complex.zero_re] at this; exact lt_irrefl _ this
    simp only
    rw [Complex.exp_add, Complex.exp_log hne, Complex.exp_log hD0]
    field_simp

/-- The nerve of a tree chain is a tree. The form needed: a tree chain with at least two links has
a link `A` meeting exactly one other link `B`, such that `G.erase A` is again a tree chain.
(Proof: `exists_chainConn_card` gives a chain-connected `H ⊆ G` with one link fewer; the missing
link meets one link of `H` by coherence and at most one by `no_two_nbrs`.) -/
theorem exists_leaf {G : Finset (Set Pt)} (hG : IsTreeChain G) (h2 : 2 ≤ G.card) :
    ∃ A ∈ G, ∃ B ∈ G, A ≠ B ∧ (A ∩ B).Nonempty ∧
      (∀ C ∈ G, C ≠ A → C ≠ B → Disjoint A C) ∧ IsTreeChain (G.erase A) := by
  obtain ⟨hopen, hcoh, htri, hcirc⟩ := hG
  obtain ⟨H, hHG, hcard, hconn⟩ := exists_chainConn_card hcoh (G.card - 2) (by omega)
  have hsd : (G \ H).card = 1 := by rw [Finset.card_sdiff_of_subset hHG]; omega
  obtain ⟨C, hC⟩ := Finset.card_eq_one.1 hsd
  have hCmem : C ∈ G \ H := by rw [hC]; exact Finset.mem_singleton_self _
  obtain ⟨hCG, hCH⟩ := Finset.mem_sdiff.1 hCmem
  have hHeq : H = G.erase C := by
    refine Finset.eq_of_subset_of_card_le (fun X hX => Finset.mem_erase.2
      ⟨fun e => hCH (e ▸ hX), hHG hX⟩) ?_
    rw [Finset.card_erase_of_mem hCG]; omega
  have hss : H ⊂ G := Finset.ssubset_iff_subset_ne.2 ⟨hHG, fun e => hCH (e ▸ hCG)⟩
  obtain ⟨X, hX, Y, hY, hXY⟩ := hcoh H hss (Finset.card_pos.1 (by omega))
  have hYC : Y = C := by
    have := hY; rw [hC] at this; exact Finset.mem_singleton.1 this
  subst hYC
  refine ⟨Y, hCG, X, hHG hX, fun e => hCH (e ▸ hX), by rw [inter_comm]; exact hXY, ?_, ?_⟩
  · intro D hD hDY hDX
    have hDH : D ∈ H := by
      by_contra hn
      have : D ∈ G \ H := Finset.mem_sdiff.2 ⟨hD, hn⟩
      rw [hC] at this; exact hDY (Finset.mem_singleton.1 this)
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra hne
    exact no_two_nbrs hcirc hHG hconn hCG hCH hX hDH (Ne.symm hDX)
      (by rw [inter_comm]; exact hXY) (Set.nonempty_iff_ne_empty.2 hne)
  · rw [← hHeq]
    exact ⟨fun A hA => hopen A (hHG hA), isCoherent_of_chainConn hconn,
      fun A hA B hB D hD => htri A (hHG hA) B (hHG hB) D (hHG hD),
      fun G' hG' => hcirc G' (hG'.trans hHG)⟩

/-- The ball branch of a single link: a link `A` of diameter `< ε`, nonempty and `8ε`-far from
`p`, lies in a ball `ball c ε` carrying a branch of `log (z − p)`. -/
theorem exists_ball_branch {A : Set Pt} {ε : ℝ} (hε : 0 < ε)
    (hA : Bornology.IsBounded A ∧ diam A < ε) (hne : A.Nonempty) {p : Pt}
    (hfar : ∀ z ∈ A, 8 * ε < dist z p) :
    ∃ (c : Pt) (ℓ : Pt → ℂ), A ⊆ ball c ε ∧ ContinuousOn ℓ (ball c ε) ∧
      ∀ z ∈ ball c ε, Complex.exp (ℓ z) = toCpx z - toCpx p := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨ℓ, hℓ, hℓe⟩ := exists_log_on_ball hε (c := a) (p := p) (by linarith [hfar a ha])
  exact ⟨a, ℓ, fun z hz => mem_ball.2 (lt_of_le_of_lt (dist_le_diam_of_mem hA.1 hz ha) hA.2),
    hℓ, hℓe⟩

/-- **The induction with the ball invariant**: on each link `A`, the logarithm is the restriction
of a branch defined on a whole ball around `A`. -/
theorem exists_log_inv {ε : ℝ} (hε : 0 < ε) {p : Pt} :
    ∀ N, ∀ G : Finset (Set Pt), G.card = N → IsTreeChain G →
      (∀ A ∈ G, Bornology.IsBounded A ∧ diam A < ε) → (∀ A ∈ G, ∀ z ∈ A, 8 * ε < dist z p) →
      ∃ L : Pt → ℂ, ∀ A ∈ G, A.Nonempty → ∃ (c : Pt) (ℓ : Pt → ℂ), A ⊆ ball c ε ∧
        ContinuousOn ℓ (ball c ε) ∧ (∀ z ∈ ball c ε, Complex.exp (ℓ z) = toCpx z - toCpx p) ∧
        ∀ z ∈ A, L z = ℓ z := by
  intro N
  induction N with
  | zero =>
    intro G hG _ _ _
    refine ⟨0, fun A hA => ?_⟩
    rw [Finset.card_eq_zero.1 hG] at hA
    exact absurd hA (Finset.notMem_empty _)
  | succ N ih =>
    intro G hcard hG hdiam hfar
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      obtain ⟨A, rfl⟩ := Finset.card_eq_one.1 hcard
      by_cases hne : A.Nonempty
      · obtain ⟨c, ℓ, hAc, hℓ, hℓe⟩ := exists_ball_branch hε (hdiam A (Finset.mem_singleton_self _))
          hne (hfar A (Finset.mem_singleton_self _))
        refine ⟨ℓ, fun A' hA' _ => ?_⟩
        rw [Finset.mem_singleton.1 hA']
        exact ⟨c, ℓ, hAc, hℓ, hℓe, fun z _ => rfl⟩
      · refine ⟨0, fun A' hA' hne' => ?_⟩
        rw [Finset.mem_singleton.1 hA'] at hne'
        exact absurd hne' hne
    · obtain ⟨A, hA, B, hB, hAB, hABne, hdisj, hGe⟩ := exists_leaf hG (by omega)
      obtain ⟨L₀, hL₀⟩ := ih (G.erase A) (by rw [Finset.card_erase_of_mem hA, hcard]; rfl) hGe
        (fun D hD => hdiam D (Finset.mem_of_mem_erase hD))
        (fun D hD => hfar D (Finset.mem_of_mem_erase hD))
      have hBe : B ∈ G.erase A := Finset.mem_erase.2 ⟨Ne.symm hAB, hB⟩
      obtain ⟨z₀, hz₀A, hz₀B⟩ := hABne
      obtain ⟨cB, ℓB, hBc, hℓB, hℓBe, hL₀B⟩ := hL₀ B hBe ⟨z₀, hz₀B⟩
      obtain ⟨cA, ℓA, hAc, hℓA, hℓAe⟩ := exists_ball_branch hε (hdiam A hA) ⟨z₀, hz₀A⟩ (hfar A hA)
      set S := ball cA ε ∩ ball cB ε
      have hS : IsPreconnected S := ((convex_ball cA ε).inter (convex_ball cB ε)).isPreconnected
      have hz₀S : z₀ ∈ S := ⟨hAc hz₀A, hBc hz₀B⟩
      set κ := ℓB z₀ - ℓA z₀
      have hconst : ∀ z ∈ S, ℓB z - ℓA z = κ := fun z hz =>
        sub_const_of_exp_eq hS (hℓB.mono inter_subset_right) (hℓA.mono inter_subset_left)
          (fun w hw => by rw [hℓBe w hw.2, hℓAe w hw.1]) hz hz₀S
      have hz₀p : toCpx z₀ - toCpx p ≠ 0 := by
        refine toCpx_sub_ne_zero fun e => ?_
        have := hfar A hA z₀ hz₀A
        rw [e, dist_self] at this; linarith
      have hexpκ : Complex.exp κ = 1 := by
        simp only [κ]
        rw [Complex.exp_sub, hℓBe z₀ hz₀S.2, hℓAe z₀ hz₀S.1, div_self hz₀p]
      refine ⟨fun z => if z ∈ A then ℓA z + κ else L₀ z, fun D hD hDne => ?_⟩
      by_cases hDA : D = A
      · subst hDA
        refine ⟨cA, fun z => ℓA z + κ, hAc, hℓA.add continuousOn_const, fun z hz => ?_,
          fun z hz => by simp only [hz, if_true]⟩
        simp only
        rw [Complex.exp_add, hexpκ, mul_one, hℓAe z hz]
      · have hDe : D ∈ G.erase A := Finset.mem_erase.2 ⟨hDA, hD⟩
        by_cases hDB : D = B
        · subst hDB
          refine ⟨cB, ℓB, hBc, hℓB, hℓBe, fun z hz => ?_⟩
          by_cases hzA : z ∈ A
          · simp only [hzA, if_true]
            have := hconst z ⟨hAc hzA, hBc hz⟩
            linear_combination -this
          · simp only [hzA, if_false]; exact hL₀B z hz
        · obtain ⟨c, ℓ, hDc, hℓ, hℓe, hL₀D⟩ := hL₀ D hDe hDne
          refine ⟨c, ℓ, hDc, hℓ, hℓe, fun z hz => ?_⟩
          have hzA : z ∉ A := fun hzA => Set.disjoint_left.1 (hdisj D hD hDA hDB) hzA hz
          simp only [hzA, if_false]; exact hL₀D z hz

/-- **A logarithm on a fine tree cover.** Suppose `G` is a tree chain, each link of `G` has
diameter `< ε`, and every point of every link is at distance `> 8 ε` from `p`. Then `z − p` has a
continuous logarithm on `⋃ G`. (Induction on `G.card` with the ball invariant of the header:
`exists_log_inv`.) -/
theorem exists_log_on_treeChain {G : Finset (Set Pt)} (hG : IsTreeChain G) {ε : ℝ} (hε : 0 < ε)
    (hdiam : ∀ A ∈ G, Bornology.IsBounded A ∧ diam A < ε) {p : Pt}
    (hfar : ∀ A ∈ G, ∀ z ∈ A, 8 * ε < dist z p) :
    ∃ L : Pt → ℂ, ContinuousOn L (⋃ A ∈ G, A) ∧
      ∀ z ∈ ⋃ A ∈ G, A, Complex.exp (L z) = toCpx z - toCpx p := by
  obtain ⟨L, hL⟩ := exists_log_inv hε G.card G rfl hG hdiam hfar
  refine ⟨L, fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨A, hA, hzA⟩ := mem_iUnion₂.1 hz
    obtain ⟨c, ℓ, hAc, hℓ, -, hLℓ⟩ := hL A hA ⟨z, hzA⟩
    have hca : ContinuousAt ℓ z := hℓ.continuousAt (isOpen_ball.mem_nhds (hAc hzA))
    have heq : ℓ =ᶠ[nhds z] L := Filter.mem_of_superset ((hG.1 A hA).mem_nhds hzA)
      fun w hw => (hLℓ w hw).symm
    exact (hca.congr heq).continuousWithinAt
  · obtain ⟨A, hA, hzA⟩ := mem_iUnion₂.1 hz
    obtain ⟨c, ℓ, hAc, -, hℓe, hLℓ⟩ := hL A hA ⟨z, hzA⟩
    rw [hLℓ z hzA, hℓe z (hAc hzA)]

/-! ### 2. No logarithm on a polygon around `p` -/

/-- **No logarithm on a simple closed polygon around `p`.** The angle sum is `0` by telescoping
and odd by the crossing parity (header, step 2; `parity`, `CrossesEast`, `polyInterior_eq_oddSet`).
Per edge, `log_diff_edge` gives the change of `L` as the principal `log ((p − b) / (p − a))`, and
`edge_jump` its argument as `arg (p − b) − arg (p − a) + 2π j` with `j` odd iff `CrossesEast`. -/
theorem no_log_on_polygon {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) {p : Pt}
    (hp : p ∈ polyInterior (polygonOf v)) :
    ¬ ∃ L : Pt → ℂ, ContinuousOn L (polygonOf v) ∧
      ∀ z ∈ polygonOf v, Complex.exp (L z) = toCpx z - toCpx p := by
  rintro ⟨L, hLc, hLe⟩
  rw [polyInterior_eq_oddSet hv] at hp
  obtain ⟨hpP, hpar⟩ := hp
  have hseg : ∀ i : Fin n, segment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) ⊆
      polygonOf v := fun i =>
    subset_iUnion (fun i : Fin n => segment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)) i
  have hpi : ∀ i : Fin n, p ∉ segment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) :=
    fun i h => hpP (hseg i h)
  have hedge := fun i => log_diff_edge (hpi i) (hLc.mono (hseg i)) (fun z hz => hLe z (hseg i hz))
  choose j hj hjc using fun i => edge_jump (hpi i)
  have hsumL : ∑ i : Fin n, (L (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) - L (v i)) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [next_eq_finRotate]
    rw [Equiv.sum_comp (finRotate n) (fun i => L (v i)), sub_self]
  have hsumA : ∑ i : Fin n, ((toCpx p - toCpx (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)).arg -
      (toCpx p - toCpx (v i)).arg) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [next_eq_finRotate]
    rw [Equiv.sum_comp (finRotate n) (fun i => (toCpx p - toCpx (v i)).arg), sub_self]
  have hsumArg : ∑ i : Fin n, ((toCpx p - toCpx (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)) /
      (toCpx p - toCpx (v i))).arg = 0 := by
    have := congrArg Complex.im hsumL
    rw [Complex.im_sum, Complex.zero_im] at this
    simp only [hedge, Complex.log_im] at this
    exact this
  have hsumj : ∑ i : Fin n, j i = 0 := by
    simp only [hj, Finset.sum_add_distrib, hsumA, zero_add, ← Finset.mul_sum] at hsumArg
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    have : ((∑ i : Fin n, j i : ℤ) : ℝ) = 0 := by
      push_cast
      exact (mul_eq_zero.1 hsumArg).resolve_left h2
    exact_mod_cast this
  have : parity v p = 0 := by
    rw [parity_eq_sum]
    simp only [← hjc]
    rw [← Int.cast_sum, hsumj, Int.cast_zero]
  rw [this] at hpar
  exact absurd hpar (by decide)

/-! ### 3. A polygon in an open set around a point -/

/-- **Batch 130 for a point.** For bounded `M`, `x ∈ M` and `δ > 0`, some simple closed polygon on
the boundary graph of the grid union has `x` in its interior. (The proof of
`exists_enclosing_polygon`, with `x₀ := x`.) -/
theorem exists_enclosing_polygon_pt {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ}
    (hδ : 0 < δ) {x : Pt} (hx : x ∈ M) :
    ∃ J : Set Pt, IsSimpleClosedPolygon J ∧ J ⊆ graphSet (bdryGraph M δ) ∧ x ∈ polyInterior J := by
  set G := bdryGraph M δ
  obtain ⟨L, hLs, hLZ, hLd, hZL⟩ :=
    exists_simpleCycle_decomposition (isCycle_oddSet (isProper_bdryGraph M hδ) (farPt M δ))
  have hsum : (L.map fun C => cycParity C x).sum = 1 := by
    rw [← cycParity_foldr hLd, ← hZL]
    exact cycParity_oddSet_eq_one_on hM hδ hx
  obtain ⟨C, hCL, hC1⟩ : ∃ C ∈ L, cycParity C x = 1 := by
    by_contra hcon
    push_neg at hcon
    have : (L.map fun C => cycParity C x).sum = 0 := by
      refine List.sum_eq_zero fun a ha => ?_
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 ha
      rcases zmod2_cases (cycParity C x) 0 with h | h
      · exact h
      · exact absurd (by simpa using h) (hcon C hC)
    rw [this] at hsum
    exact zero_ne_one hsum
  obtain ⟨n, v, hv, hgC, hpar⟩ := hLs C hCL
  have hJG : polygonOf v ⊆ graphSet G :=
    hgC ▸ graphSet_mono ((hLZ C hCL).trans (oddSet_subset _ _))
  have hxJ : x ∉ polygonOf v := fun h => by
    have := disjoint_frontier_gridUnion hM hδ
    rw [frontier_gridUnion M hδ] at this
    exact Set.disjoint_left.1 this hx (hJG h)
  refine ⟨polygonOf v, isSimpleClosedPolygon_iff.2 ⟨n, v, hv, rfl⟩, hJG, ?_⟩
  rw [polyInterior_eq_oddSet hv]
  exact ⟨hxJ, by rw [← hpar, hC1]⟩

/-- **A polygon in `W` around `p`.** Suppose `W` is open, `p ∉ W`, and the component of `p` in
`Wᶜ` is bounded. Then some simple closed polygon `J ⊆ W` has `p` in its interior. (Cut-wire, then
`exists_enclosing_polygon_pt` and `frontier_gridUnion`.) -/
theorem exists_polygon_around {W : Set Pt} (hW : IsOpen W) {p : Pt} (hp : p ∉ W)
    (hb : Bornology.IsBounded (connectedComponentIn Wᶜ p)) :
    ∃ J : Set Pt, IsSimpleClosedPolygon J ∧ J ⊆ W ∧ p ∈ polyInterior J := by
  obtain ⟨R, hR⟩ := hb.subset_ball (0 : Pt)
  set X : Set Pt := Wᶜ ∩ closedBall 0 R with hXdef
  have hXc : IsCompact X := (isCompact_closedBall 0 R).inter_left hW.isClosed_compl
  haveI : CompactSpace X := isCompact_iff_compactSpace.1 hXc
  have hpc : p ∈ connectedComponentIn Wᶜ p := mem_connectedComponentIn hp
  have hpX : p ∈ X := ⟨hp, ball_subset_closedBall (hR hpc)⟩
  set E₁ : Set X := {⟨p, hpX⟩}
  set E₂ : Set X := {x | dist (x : Pt) 0 = R}
  have hE₂ : IsClosed E₂ := isClosed_eq (continuous_subtype_val.dist continuous_const)
    continuous_const
  obtain ⟨F₁, F₂, hF₁, hF₂, hF₁₂, hF, hE₁F, hE₂F⟩ := exists_split_of_no_continuum (S := X)
    (F := univ) isClosed_univ (subset_univ _) (subset_univ _) isClosed_singleton hE₂
    (by
      intro C hC _ hC1 hC2
      obtain ⟨y, hyC, hyE⟩ := hC2
      obtain ⟨y', hy'C, hy'E⟩ := hC1
      have hy' : y' = ⟨p, hpX⟩ := hy'E
      have himg : IsPreconnected ((↑) '' C : Set Pt) :=
        hC.2.isPreconnected.image _ continuous_subtype_val.continuousOn
      have hsub : ((↑) '' C : Set Pt) ⊆ connectedComponentIn Wᶜ p :=
        himg.subset_connectedComponentIn ⟨y', hy'C, by rw [hy']⟩
          (by rintro _ ⟨w, -, rfl⟩; exact w.2.1)
      have := hR (hsub ⟨y, hyC, rfl⟩)
      rw [mem_ball] at this
      have hyE' : dist (y : Pt) 0 = R := hyE
      linarith)
  set M : Set Pt := (↑) '' F₁
  have hMc : IsCompact M := hF₁.isCompact.image continuous_subtype_val
  have hpM : p ∈ M := ⟨⟨p, hpX⟩, hE₁F rfl, rfl⟩
  have hMball : ∀ x ∈ M, dist x 0 < R := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : dist (x : Pt) 0 ≤ R := x.2.2
    refine lt_of_le_of_ne h1 fun he => ?_
    exact Set.disjoint_left.1 hF₁₂ hx (hE₂F he)
  set Z : Set Pt := (↑) '' F₂ ∪ {x | R ≤ dist x 0}
  have hZc : IsClosed Z := (hF₂.isCompact.image continuous_subtype_val).isClosed.union
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hMZ : M ⊆ Zᶜ := by
    rintro _ ⟨x, hx, rfl⟩ (⟨y, hy, hyx⟩ | hR')
    · rw [Subtype.val_injective hyx] at hy
      exact Set.disjoint_left.1 hF₁₂ hx hy
    · have := hMball x ⟨x, hx, rfl⟩
      exact absurd hR' (not_le.2 this)
  have hWZ : ∀ x, x ∉ W → x ∉ M → x ∈ Z := by
    intro x hxW hxM
    by_cases hxR : R ≤ dist x 0
    · exact Or.inr hxR
    · have hxX : x ∈ X := ⟨hxW, mem_closedBall.2 (le_of_lt (not_le.1 hxR))⟩
      have : (⟨x, hxX⟩ : X) ∈ F₁ ∪ F₂ := hF ▸ mem_univ _
      rcases this with h | h
      · exact absurd ⟨_, h, rfl⟩ hxM
      · exact Or.inl ⟨_, h, rfl⟩
  obtain ⟨δ, hδ, hδZ⟩ := hMc.exists_cthickening_subset_open hZc.isOpen_compl hMZ
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨J, hJ, hJG, hpJ⟩ := exists_enclosing_polygon_pt hMc.isBounded hδ2 hpM
  refine ⟨J, hJ, fun z hz => ?_, hpJ⟩
  have hzF : z ∈ frontier (gridUnion M (δ / 2)) := by
    rw [frontier_gridUnion M hδ2]; exact hJG hz
  have hzM : z ∉ M := fun h => Set.disjoint_left.1 (disjoint_frontier_gridUnion hMc.isBounded hδ2)
    h hzF
  have hzQ : z ∈ gridUnion M (δ / 2) := graphSet_bdryGraph_subset M hδ2 (hJG hz)
  have hzZ : z ∈ Zᶜ := by
    apply hδZ
    have := gridUnion_subset_cthickening hMc.isBounded hδ2 hzQ
    rwa [show 2 * (δ / 2) = δ by ring] at this
  by_contra hzW
  exact hzZ (hWZ z hzW hzM)

/-! ### 4. Assembly -/

/-- The complement of a closed (sup-norm) ball is preconnected: four open half-planes. -/
theorem isPreconnected_compl_closedBall (R : ℝ) :
    IsPreconnected (closedBall (0 : Pt) R)ᶜ := by
  set T := |R| + 1
  have hT : R < T := by have := le_abs_self R; simp only [T]; linarith
  have hT' : -T < -R := by linarith
  have hU : (closedBall (0 : Pt) R)ᶜ =
      ((Ioi R ×ˢ univ ∪ univ ×ˢ Ioi R) ∪ Iio (-R) ×ˢ univ) ∪ univ ×ˢ Iio (-R) := by
    ext x
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      max_le_iff, not_and_or, not_le, mem_union, mem_prod, mem_Ioi, mem_Iio, mem_univ, and_true,
      true_and, lt_abs]
    have e1 : R < -x.1 ↔ x.1 < -R := by constructor <;> intro <;> linarith
    have e2 : R < -x.2 ↔ x.2 < -R := by constructor <;> intro <;> linarith
    rw [e1, e2]
    tauto
  rw [hU]
  refine IsPreconnected.union ((-T, -T) : Pt) (by simp [hT']) (by simp [hT']) ?_
    (isPreconnected_univ.prod isPreconnected_Iio)
  refine IsPreconnected.union ((-T, T) : Pt) (by simp [hT]) (by simp [hT']) ?_
    (isPreconnected_Iio.prod isPreconnected_univ)
  exact IsPreconnected.union ((T, T) : Pt) (by simp [hT]) (by simp [hT])
    (isPreconnected_Ioi.prod isPreconnected_univ) (isPreconnected_univ.prod isPreconnected_Ioi)

/-- If a compact `K` separates the plane, some point off `K` has a bounded component in `Kᶜ`.
(The complement of a large closed ball is connected and lies in one component of `Kᶜ`.) -/
theorem exists_bounded_component_of_separates {K : Set Pt} (hK : IsCompact K)
    (hs : SeparatesPlane K) :
    ∃ p, p ∉ K ∧ Bornology.IsBounded (connectedComponentIn Kᶜ p) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Pt)
  set U := (closedBall (0 : Pt) R)ᶜ
  have hUK : U ⊆ Kᶜ := compl_subset_compl.2 hR
  set u : Pt := (|R| + 1, 0)
  have huU : u ∈ U := by
    simp only [U, u, mem_compl_iff, mem_closedBall, dist_zero_right, Prod.norm_def,
      Real.norm_eq_abs, norm_zero, not_le]
    rw [abs_of_pos (by positivity : (0:ℝ) < |R| + 1)]
    exact lt_of_lt_of_le (by linarith [le_abs_self R]) (le_max_left _ _)
  have hall : Kᶜ ⊆ connectedComponentIn Kᶜ u := by
    intro x hx
    have hunb := hcon x hx
    have : ¬ connectedComponentIn Kᶜ x ⊆ closedBall 0 R := fun h =>
      hunb (isBounded_closedBall.subset h)
    obtain ⟨y, hy, hyU⟩ := Set.not_subset.1 this
    have hUy : U ⊆ connectedComponentIn Kᶜ y :=
      (isPreconnected_compl_closedBall R).subset_connectedComponentIn hyU hUK
    rw [← connectedComponentIn_eq hy] at hUy
    have hux := hUy huU
    rw [← connectedComponentIn_eq hux]
    exact mem_connectedComponentIn hx
  have hconn : IsConnected Kᶜ := by
    have heq : connectedComponentIn Kᶜ u = Kᶜ :=
      Subset.antisymm (connectedComponentIn_subset _ _) hall
    rw [← heq]
    exact isConnected_connectedComponentIn_iff.2 (hUK huU)
  exact hs hconn

/-- The links of a tree chain that meet a continuum `K` form a tree chain (coherence: `K` is
connected, and two subcollections with no meeting links would split `K`). -/
theorem isTreeChain_filter_meet {G : Finset (Set Pt)} (hG : IsTreeChain G) {K : Set Pt}
    (hK : IsConnected K) (hKG : K ⊆ ⋃ A ∈ G, A) :
    IsTreeChain (G.filter fun A => (A ∩ K).Nonempty) := by
  obtain ⟨hopen, -, htri, hcirc⟩ := hG
  set G' := G.filter fun A => (A ∩ K).Nonempty
  have hG'G : G' ⊆ G := Finset.filter_subset _ _
  refine ⟨fun A hA => hopen A (hG'G hA), ?_, fun A hA B hB C hC => htri A (hG'G hA) B (hG'G hB) C
    (hG'G hC), fun H hH => hcirc H (hH.trans hG'G)⟩
  intro H hHsub hHne
  by_contra hno
  push_neg at hno
  obtain ⟨Y, hYG', hYH⟩ := Finset.exists_of_ssubset hHsub
  obtain ⟨X, hX⟩ := hHne
  set U := ⋃ A ∈ H, A
  set V := ⋃ B ∈ G' \ H, B
  have hU : IsOpen U := isOpen_biUnion fun A hA => hopen A (hG'G (hHsub.1 hA))
  have hV : IsOpen V := isOpen_biUnion fun B hB => hopen B (hG'G (Finset.mem_sdiff.1 hB).1)
  have hKUV : K ⊆ U ∪ V := by
    intro k hk
    obtain ⟨A, hA, hkA⟩ := mem_iUnion₂.1 (hKG hk)
    have hAG' : A ∈ G' := Finset.mem_filter.2 ⟨hA, k, hkA, hk⟩
    by_cases hAH : A ∈ H
    · exact Or.inl (mem_iUnion₂.2 ⟨A, hAH, hkA⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨A, Finset.mem_sdiff.2 ⟨hAG', hAH⟩, hkA⟩)
  have hKU : (K ∩ U).Nonempty := by
    obtain ⟨k, hkX, hkK⟩ := (Finset.mem_filter.1 (hHsub.1 hX)).2
    exact ⟨k, hkK, mem_iUnion₂.2 ⟨X, hX, hkX⟩⟩
  have hKV : (K ∩ V).Nonempty := by
    obtain ⟨k, hkY, hkK⟩ := (Finset.mem_filter.1 hYG').2
    exact ⟨k, hkK, mem_iUnion₂.2 ⟨Y, Finset.mem_sdiff.2 ⟨hYG', hYH⟩, hkY⟩⟩
  obtain ⟨z, hzK, hzU, hzV⟩ := hK.isPreconnected U V hU hV hKUV hKU hKV
  obtain ⟨A, hA, hzA⟩ := mem_iUnion₂.1 hzU
  obtain ⟨B, hB, hzB⟩ := mem_iUnion₂.1 hzV
  exact Set.not_nonempty_iff_eq_empty.2 (hno A hA B hB) ⟨z, hzA, hzB⟩

/-- **A tree-like plane continuum contains no continuum that separates the plane.** The unstated
step of Bing 1951 (Duke), Theorem 7 (header). -/
theorem treeLike_nonseparating {M : Set Pt} (hM : IsTreeLike M) :
    ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K := by
  intro K hKM hK hs
  obtain ⟨p, hpK, hpb⟩ := exists_bounded_component_of_separates hK.1 hs
  have hKne := hK.2.nonempty
  set d := infDist p K
  have hd : 0 < d := (hK.1.isClosed.notMem_iff_infDist_pos hKne).1 hpK
  set ε := d / 10
  have hε : 0 < ε := by positivity
  obtain ⟨G, hG, hGd, hGM⟩ := hM.2 ε hε
  set G' := G.filter fun A => (A ∩ K).Nonempty
  have hG' : IsTreeChain G' := isTreeChain_filter_meet hG hK.2 (hKM.trans hGM)
  have hfar : ∀ A ∈ G', ∀ z ∈ A, 8 * ε < dist z p := by
    intro A hA z hz
    obtain ⟨hAG, k, hkA, hkK⟩ := Finset.mem_filter.1 hA
    have h1 : dist z k < ε := lt_of_le_of_lt (dist_le_diam_of_mem (hGd A hAG).1 hz hkA) (hGd A hAG).2
    have h2 : d ≤ dist p k := infDist_le_dist_of_mem hkK
    have h3 := dist_triangle p z k
    rw [dist_comm p z] at h3
    have : ε = d / 10 := rfl
    linarith
  obtain ⟨L, hLc, hLe⟩ := exists_log_on_treeChain hG' hε
    (fun A hA => hGd A (Finset.mem_filter.1 hA).1) hfar
  set W := ⋃ A ∈ G', A
  have hWo : IsOpen W := isOpen_biUnion fun A hA => hG'.1 A hA
  have hpW : p ∉ W := by
    intro h
    obtain ⟨A, hA, hpA⟩ := mem_iUnion₂.1 h
    have := hfar A hA p hpA
    rw [dist_self] at this; linarith
  have hKW : K ⊆ W := by
    intro k hk
    obtain ⟨A, hA, hkA⟩ := mem_iUnion₂.1 (hGM (hKM hk))
    exact mem_iUnion₂.2 ⟨A, Finset.mem_filter.2 ⟨hA, k, hkA, hk⟩, hkA⟩
  have hb : Bornology.IsBounded (connectedComponentIn Wᶜ p) :=
    hpb.subset (connectedComponentIn_mono _ (compl_subset_compl.2 hKW))
  obtain ⟨J, hJ, hJW, hpJ⟩ := exists_polygon_around hWo hpW hb
  obtain ⟨n, v, hv, rfl⟩ := isSimpleClosedPolygon_iff.1 hJ
  exact no_log_on_polygon hv hpJ ⟨L, hLc.mono hJW, fun z hz => hLe z (hJW hz)⟩

/-- **Bing 1951 (Duke), Theorem 7, as printed.** If `M` is a tree-like plane continuum and
`ε > 0`, there is a tree chain covering `M` whose links are the interiors of simple closed curves
(here: polygons) of diameters less than `ε`. -/
theorem theorem7_1951_treeLike {M : Set Pt} (hM : IsTreeLike M) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Finset (Set Pt), IsTreeChain G ∧
      (∀ h ∈ G, ∃ Γ : Set Pt, IsSimpleClosedPolygon Γ ∧ h = polyInterior Γ) ∧
      (∀ h ∈ G, diam h < ε) ∧ M ⊆ ⋃ h ∈ G, h :=
  theorem7_1951 hM.1 (treeLike_nonseparating hM) hε

/-- **Theorem 6 and its converse.** A bounded plane continuum is tree-like iff it contains no
continuum that separates the plane. -/
theorem isTreeLike_iff_nonseparating {M : Set Pt} (hM : Fold.Q78.IsContinuum M) :
    IsTreeLike M ↔ ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K :=
  ⟨fun h => treeLike_nonseparating h, fun h => theorem6_1951 hM h⟩

end HPC.Plane
