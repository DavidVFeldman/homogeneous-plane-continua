import HPC.Jones.Jones49DCross

/-!
# Batch 152 skeleton: Whyburn 1939, §14 Theorem (boundaries of complementary domains of a compact
semi-locally-connected plane continuum are locally connected)

Save as `HPC/Jones/Jones49D.lean` (splitting under `HPC/Jones/` is expected); add
`import HPC.Jones.Jones49D` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be
adjusted, each change recorded at the statement and in the report.

Source: Whyburn, *Semi-locally-connected sets*, Amer. J. Math. 61 (1939), pp. 747–749
(`doc/sources/whyburn1939.pdf`, PDF pp. 16–18), read from page images at 150 dpi. The proof:
1. (p. 747) reduction to bounded `R` by inversion (gap: `A.21` of the ledger; not used);
2. if `R` lacks property S, points `pᵢ → p ∈ M` of `R`, no two joinable in `R` by a connected set of
   diameter `< 4ε` — this is the negation of the hypothesis of `moore22_sufficiency_local`;
3. **`p` not a cut point of `M`** (pp. 747–748): (6.22) gives `δ` and the component `N`; a subarc
   `xy` of an arc `p₁p₂` in `R`, ends on `C_δ`, interior outside `C_δ`, `x`, `y` not joinable by a
   continuum of `R` in `V_{2ε}(p)`; `u`, `v` separating `x`, `y` on `C_δ`; `J = xy + xuy`; `I` the
   complementary region of `J` not containing `N`; `0 ∈ I·V_ε(p)` joined to `u`; "by a theorem of
   R. L. Moore, there exists a simple closed curve `C ⊂ J + C_ε` such that if `E` is the
   complementary region of `C` containing `0`, then `E ⊂ I·V_ε(p)`"; the arc `x₁wy₁` of `C` gives a
   continuum of `R` in `V_{2ε}(p)` joining `x` and `y`, a contradiction;
4. **general `p`** (p. 748): arcs `pᵢq` in `R` to a point `q` outside `V_ε(p)`, first points `qᵢ` on
   `C_ε`, a limit continuum `H ⊂ M`, every point of `H` within `V_ε(p)` a cut point of `M` (by 3);
   "then there exists a point `p′` of `H·V_ε(p)` which is of order 2 in `M`" (footnote 6; now
   `whyburn_3_2`); "Hence there exists a simple closed curve `K` in `V_ε(p)` such that `K·M = c + d`,
   `c, d ∈ M`, and the complementary region `D` of `K` containing `p′` lies in `V_ε(p)`"; pigeonhole
   on the two components of `K − (c + d)`.

## Route taken (batch 152)

No arcs, no Jordan curves, no inversion.
* **Step 3** (item C) is proved by Janiszewski's theorem for plane compacta
  (`HPC.Moore.janiszewski_compact`), in the form `whyburn39_moore_curve` (item A, the shape chosen):
  near a non-cut point `p`, two points of `R` close to `p` lie in a connected subset of `R` close
  to `p` (`HPC.Jones.Sec14.local_join_of_noncut`). Moore's curve `C`, the θ-curve step and the arc
  `p₁p₂` are not used.
* **Step 4** (item D) is reorganized. If the boundary is not locally connected, Moore's p. 236
  construction (`exists_crossing_continua_closed`, `sector_cyclic`) gives, for every radius `ρ` in an
  interval, a boundary point `h_ρ` at which Whyburn's condition fails and at which infinitely many
  disjoint subcontinua of the boundary accumulate (`HPC.Jones.Sec14.exists_bad_point_of_crossing`).
  Such a point has no finite order in `M` (`whyburn39_curve_from_order_two`, item B, the shape
  chosen), so by `whyburn_3_2` all but countably many `h_ρ` are non-cut points of `M`, and step 3
  excludes each of them. The curve `K` is not needed.
-/

namespace HPC.Jones

open Set Topology Metric Filter HPC.Plane

/-- **\"A theorem of R. L. Moore\"** (p. 748, footnote 14; in substance F.A. Theorem 43, corrected),
in `ℝ²`, in the form the proof uses. *The shape is left to you* (REPORT-batch151 §8: build it
directly, as the component of `I·V_ε(p)` containing `0`).

*Shape chosen (batch 152).* What Whyburn takes from `C` is a connection, inside `V_{2ε}(p)` and inside
`R`, between two points of `R` near `p`. The form proved supplies exactly that, with no curve: `N` a
closed connected subset of `M` containing `M − V_ε(p)`, and `W` the component of `V_ε(p) − N`
containing `p` (the analogue of Whyburn's `E`: a domain inside `V_ε(p)` whose frontier lies in
`N ∪ C_ε`). Any two points of a complementary domain `R` of `M` lying in `W` lie in one component of
`W − M` (which is contained in `R`). Proof: Janiszewski's theorem (`HPC.Moore.janiszewski_compact`)
for `K = (M ∩ W̄) ∪ N` and `L = Wᶜ ∩ B̄(p, ρ)`, with `K ∩ L = N`. Neither the Jordan curve theorem
nor arcs are used. Whether the frontier of Whyburn's component `E` is a simple closed curve is not
decided here; it is not needed. -/
theorem whyburn39_moore_curve {M N : Set Pt} (hM : IsCompact M) (hN : IsClosed N)
    (hNc : IsConnected N) (hNM : N ⊆ M) {p : Pt} {ε : ℝ} (hout : M \ ball p ε ⊆ N) {x a b : Pt}
    (ha : a ∈ connectedComponentIn Mᶜ x) (hb : b ∈ connectedComponentIn Mᶜ x)
    (haW : a ∈ connectedComponentIn (N ∪ (ball p ε)ᶜ)ᶜ p)
    (hbW : b ∈ connectedComponentIn (N ∪ (ball p ε)ᶜ)ᶜ p) :
    b ∈ connectedComponentIn (connectedComponentIn (N ∪ (ball p ε)ᶜ)ᶜ p ∩ Mᶜ) a :=
  Sec14.join_in_domain hM hN hNc hNM hout ha hb haW hbW

/-- **The curve `K` from order 2** (p. 748, unargued). *The shape is left to you.* Whyburn's
pigeonhole needs only: an open `D ∋ p′` inside `V_ε(p)` whose frontier meets `M` in finitely many
points and minus `M` has finitely many components. State and prove whatever form the proof needs,
and record whether Whyburn's Jordan-curve form holds as stated (it requires `c`, `d` accessible from
`Mᶜ` on both sides).

*Shape chosen (batch 152): the pigeonhole turned around.* The proof does not construct `K` or `D`.
It shows instead that the points where the argument has to work have no finite order: if
infinitely many pairwise disjoint connected sets `T i` accumulate at `p` (points `b i ∈ T i` with
`b i → p`) and each reaches distance `≥ d > 0` from `p`, then `p` is not of order `≤ n` for any `n`
(the frontier of a small neighbourhood of `p` meets all but finitely many `T i`). Applied in the
subspace `M`, this places such points among those excluded by `whyburn_3_2` unless they are non-cut
points. Neither Whyburn's Jordan-curve form nor the weaker form with `D` is proved or refuted here;
neither is needed. -/
theorem whyburn39_curve_from_order_two {X : Type*} [MetricSpace X] {p : X} {T : ℕ → Set X}
    (hT : ∀ i, IsPreconnected (T i)) (hd : Pairwise fun i j => Disjoint (T i) (T j))
    {b : ℕ → X} (hb : ∀ i, b i ∈ T i) (hlim : Tendsto b atTop (𝓝 p)) {d : ℝ} (hd0 : 0 < d)
    (hfar : ∀ i, ∃ a ∈ T i, d ≤ dist a p) (n : ℕ) : ¬ OrderLE p n :=
  Sec14.not_orderLE_of_accumulating hT hd hb hlim hd0 hfar n

/-- **Step 3** (`p` not a cut point, pp. 747–748): Whyburn's local condition holds at a boundary
point `p` of a complementary domain `R` that is not a cut point of `M` — no sequence of points of `R`
converging to `p` is pairwise non-joinable in `R` by connected sets of diameter `< ε`.

*Proof (batch 152).* `HPC.Jones.Sec14.local_join_of_noncut` (with (6.22) and
`whyburn39_moore_curve`) at `ε/3`: two terms of the sequence within `δ` of `p` lie in a connected
subset of `R` inside `V_{ε/3}(p)`, of diameter `≤ 2ε/3 < ε`. The hypotheses `hx` and `hp` are kept
as in the skeleton; the proof does not use them (for `x ∈ M` the domain is empty, and the joining
statement holds at every non-cut point of `M`). -/
theorem whyburn39_local_noncut {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    (hS : ∀ z : M, SemiLocConnAt z) {x : Pt} (hx : x ∉ M) {p : M}
    (hp : (p : Pt) ∈ frontier (connectedComponentIn Mᶜ x))
    (hpc : IsConnected ({p}ᶜ : Set M)) {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ u : ℕ → Pt, (∀ n, u n ∈ connectedComponentIn Mᶜ x) ∧ Tendsto u atTop (𝓝 (p : Pt)) ∧
      ∀ i j, i ≠ j → ¬ ∃ C ⊆ connectedComponentIn Mᶜ x, IsPreconnected C ∧ u i ∈ C ∧ u j ∈ C ∧
        Bornology.IsBounded C ∧ diam C < ε := by
  obtain ⟨δ, hδ, hj⟩ := Sec14.local_join_of_noncut hM hMc hS hpc (ε := ε / 3) (by positivity) x
  rintro ⟨u, huR, hu, hbad⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hu (ball_mem_nhds (p : Pt) hδ))
  obtain ⟨C, hCR, hCc, h1, h2, hCb⟩ :=
    hj _ (huR n₀) _ (huR (n₀ + 1)) (hn₀ n₀ le_rfl) (hn₀ _ (by omega))
  refine hbad n₀ (n₀ + 1) (by omega) ⟨C, hCR, hCc, h1, h2, isBounded_ball.subset hCb, ?_⟩
  calc diam C ≤ 2 * (ε / 3) :=
        diam_le_of_subset_closedBall' (by positivity) (hCb.trans ball_subset_closedBall)
    _ < ε := by linarith

/-- **Theorem 14** (p. 747). If `M` is a compact semi-locally-connected plane continuum, the boundary
of each complementary domain of `M`, bounded or not, is locally connected.

*Proof (batch 152), no inversion.* The boundary `B` is a continuum
(`isConnected_frontier_complDomain`). If it is not locally connected, it is not connected im kleinen
at some point (`locallyConnectedSpace_of_cikAt`), and `exists_crossing_continua_closed` gives pairwise
disjoint subcontinua `tₙ` of `B` crossing an annulus `r₁ ≤ d(·, P) ≤ r₂`. For every `ρ` in the middle
third, `exists_bad_point_of_crossing` gives `h_ρ ∈ B` with `d(h_ρ, P) = ρ` at which Whyburn's
condition fails (with `ε = (r₂ - r₁)/6`) and at which subcontinua `tₙ` accumulate; so `h_ρ` has no
finite order in `M` (`whyburn39_curve_from_order_two`), and is a cut point of `M` by step 3
(`whyburn39_local_noncut`). The `h_ρ` are distinct, so uncountably many cut points of `M` are not of
order 2, against `whyburn_3_2`. (Moore's sufficiency argument enters through
`exists_bad_point_of_crossing`, a version of `moore22_sufficiency_local` at an arbitrary radius.) -/
theorem whyburn39_theorem14 {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    (hS : ∀ z : M, SemiLocConnAt z) {x : Pt} (hx : x ∉ M) :
    LocallyConnectedSpace (frontier (connectedComponentIn Mᶜ x)) := by
  classical
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hM
  haveI : ConnectedSpace M := isConnected_iff_connectedSpace.1 hMc
  set R := connectedComponentIn Mᶜ x with hRdef
  have hRo : IsOpen R := hM.isClosed.isOpen_compl.connectedComponentIn
  have hBM : frontier R ⊆ M := by
    have := HPC.Moore.frontier_connectedComponentIn_subset hM.isClosed.isOpen_compl x
    rwa [compl_compl] at this
  have hB := isConnected_frontier_complDomain hM hMc hx
  by_contra hnot
  obtain ⟨P, hPB, hP⟩ : ∃ P ∈ frontier R, ¬ CikAt (frontier R) P := by
    by_contra h
    push_neg at h
    exact hnot (locallyConnectedSpace_of_cikAt h)
  obtain ⟨r₁, r₂, h0, h12, t, htd, ht⟩ :=
    Sector.exists_crossing_continua_closed isClosed_frontier hB hPB hP
  have htc : ∀ n, Sector.IsCrossA P r₁ r₂ (t n) := fun n =>
    ⟨(ht n).2.1, (ht n).1, (ht n).2.2.2.1, (ht n).2.2.2.2.1, (ht n).2.2.2.2.2⟩
  have htM : ∀ n, t n ⊆ frontier R := fun n => (ht n).2.2.1
  set S : Set M := {p : M | ¬ IsConnected ({p}ᶜ : Set M) ∧ ¬ HasOrder p 2}
  have hScount : S.Countable := whyburn_3_2
  have key : ∀ ρ ∈ Icc (r₁ + (r₂ - r₁) / 3) (r₂ - (r₂ - r₁) / 3),
      ∃ h : M, dist (h : Pt) P = ρ ∧ h ∈ S := by
    rintro ρ ⟨hρ1, hρ2⟩
    obtain ⟨h, hhB, hhd, hbad, s, hs, b, hbt, hblim⟩ :=
      Sec14.exists_bad_point_of_crossing hRo h0 h12 htc htd htM hρ1 hρ2
    have hhM : h ∈ M := hBM hhB
    refine ⟨⟨h, hhM⟩, hhd, fun hpc => ?_, fun h2 => ?_⟩
    · exact whyburn39_local_noncut hM hMc hS hx (p := ⟨h, hhM⟩) hhB hpc
        (ε := (r₂ - r₁) / 6) (by linarith) hbad
    · have htsM : ∀ i, t (s i) ⊆ M := fun i => (htM _).trans hBM
      refine whyburn39_curve_from_order_two (p := (⟨h, hhM⟩ : M))
        (T := fun i => Subtype.val ⁻¹' t (s i)) (fun i => ?_) (fun i j hij => ?_)
        (b := fun i => ⟨b i, htsM i (hbt i)⟩) (fun i => hbt i)
        (tendsto_subtype_rng.2 hblim) (d := (r₂ - r₁) / 3) (by linarith) (fun i => ?_) 2 h2.1
      · rw [← IsInducing.subtypeVal.isPreconnected_image,
          image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact htsM i)]
        exact (htc _).conn.isPreconnected
      · exact (htd (hs.injective.ne hij)).preimage _
      · obtain ⟨a, haT, had⟩ := (htc (s i)).inner
        refine ⟨⟨a, htsM i haT⟩, haT, ?_⟩
        rw [Subtype.dist_eq]
        have := dist_triangle h a P
        rw [dist_comm h a] at this
        simp only
        linarith
  choose! f hfd hfS using key
  have hcount : (Icc (r₁ + (r₂ - r₁) / 3) (r₂ - (r₂ - r₁) / 3)).Countable := by
    refine MapsTo.countable_of_injOn (fun ρ hρ => hfS ρ hρ) (fun ρ hρ ρ' hρ' he => ?_) hScount
    rw [← hfd ρ hρ, ← hfd ρ' hρ', he]
  have hlt : r₁ + (r₂ - r₁) / 3 < r₂ - (r₂ - r₁) / 3 := by linarith
  have h1 := Cardinal.mk_Icc_real hlt
  have h2 := hcount.le_aleph0
  rw [h1] at h2
  exact absurd h2 (not_le.2 Cardinal.aleph0_lt_continuum)

end HPC.Jones
