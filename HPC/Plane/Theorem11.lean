import HPC.Plane.Theorem9B
import HPC.Plane.Theorem11Gen

/-!
# Batch 96: Bing 1951 Theorem 11 — the easy half, and reconnaissance on the hard half

Skeleton of `COMMISSION-batch96.md`, saved as `HPC/Plane/Theorem11.lean` and imported at the end of
the root `HPC.lean`.

Theorem 11 (p. 660): *necessary and sufficient conditions that a compact hereditarily decomposable
continuum be snake-like are that it be atriodic and hereditarily unicoherent.*

§1 is the necessity ("it is easy to see"). §2 sets up Bing's minimal counterexample and the
structure his proof of sufficiency needs; §3 is sufficiency, conditional on `theorem10_1951`.

**Status (batch 96).**
* §1: all four statements proved (chain combinatorics in `HPC/Plane/Theorem11Nec.lean`).
* `not_separation_of_accumulates` (item 1) is **false as stated** (an open `N` may avoid a point of
  `g` without avoiding a neighbourhood of it): refuted by `not_separation_of_accumulates_false`
  (the commented-out statement was removed in batch 103; see `LEDGER.md`); the corrected statement, with `¬ g ⊆ closure N`, is
  `not_separation_of_accumulates'`, proved.
* Items 2, 4, 5, 7, 8 proved (`separation_of_degenerate`, `exists_two_sides`, `sides_continua`,
  `condA_side`, `epsCoverable_amalgam`, `exists_minimal_notCoverable`).
* Item 3 (`exists_degenerate_interior_elt`) is **false** (batch 97: refuted by
  `exists_degenerate_interior_elt_refuted`, `HPC/Plane/Layers51.lean`, in the Cantor organ); the
  sorried statement was removed in batch 103 (see `LEDGER.md`).
* `theorem11_1951_of_T10` and `theorem11_1951_iff_of_T10` are proved with the statement of
  `exists_degenerate_interior_elt` as a further hypothesis `hdeg` (shape change).

**Shape changes.**
* §1: `IsUnicoherent`, `IsHereditarilyUnicoherent`, `IsAtriodic` and `IsTriod` are defined only
  over a compact metric space (`Atriodic51Defs.lean`), so the last three statements of §1 are
  stated over `S` (compact) instead of `X`. `isSnakeLike_of_subcontinuum` stays over `X`.
* `EpsCoverable` is defined in `HPC/Plane/Theorem11Gen.lean` (same definition), so that the
  general lemmas there can use it.
* `exists_minimal_notCoverable` is stated over the compact space `S` (the Brouwer reduction used,
  `exists_minimal_of_seq`, needs second countability); the general form is unchanged otherwise.
* `theorem11_1951_of_T10`, `theorem11_1951_iff_of_T10`: extra hypothesis `hdeg`.
-/

namespace HPC.Plane

open Set Topology Metric

universe u

variable {X : Type*} [MetricSpace X]

/-! ## §1. Necessity: snake-like ⇒ atriodic and hereditarily unicoherent (Nadler 12.2–12.5) -/

/-- A subcontinuum of a snake-like continuum is snake-like (Nadler 12.5; Bing uses it without
comment). The links meeting `K` have consecutive indices (`meets_between`, from
`Chain.inter_link_nonempty_between`), so they form a subchain covering `K`. -/
theorem isSnakeLike_of_subcontinuum {M K : Set X} (hM : IsSnakeLike M) (hK : Fold.Q78.IsContinuum K)
    (hKM : K ⊆ M) : IsSnakeLike K :=
  isSnakeLike_of_subcontinuum_aux hM hK hKM

section CompactNecessity

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- A snake-like continuum is unicoherent (Nadler 12.2). (Shape change: over a compact space.) -/
theorem isUnicoherent_of_isSnakeLike {M : Set S} (hM : IsSnakeLike M) : IsUnicoherent M :=
  isUnicoherent_of_isSnakeLike_aux hM

/-- A snake-like continuum is hereditarily unicoherent. (Shape change: over a compact space.) -/
theorem isHereditarilyUnicoherent_of_isSnakeLike {M : Set S} (hM : IsSnakeLike M) :
    IsHereditarilyUnicoherent M := fun _ hKM hK _ =>
  isUnicoherent_of_isSnakeLike (isSnakeLike_of_subcontinuum hM hK hKM)

/-- A snake-like continuum is atriodic (Nadler 12.4: a triod is not chainable). (Shape change:
over a compact space.) -/
theorem isAtriodic_of_isSnakeLike {M : Set S} (hM : IsSnakeLike M) : IsAtriodic M := fun _ hTM hT =>
  not_isTriod_of_isSnakeLike (isSnakeLike_of_subcontinuum hM hT.1 hTM) hT

end CompactNecessity

/-! ## §2. The hard half: structure -/

section Structure

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! `EpsCoverable` (`M` is covered by some `ε`-chain) is defined in `Theorem11Gen.lean`. -/

/-- If `ε`-chains refine to `E`, `E` is an `ε`-chain. -/
theorem isEpsChain_of_refines {m n : ℕ} {E : Chain X m} {D : Chain X n} (hED : E.Refines D)
    {ε : ℝ} (hD : IsEpsChain D ε) : IsEpsChain E ε := fun i => by
  obtain ⟨j, hj⟩ := hED i
  exact ⟨(hD j).1.subset hj, lt_of_le_of_lt (Metric.diam_mono hj (hD j).1) (hD j).2⟩

theorem epsCoverable_singleton (x : X) {ε : ℝ} (hε : 0 < ε) : EpsCoverable {x} ε := by
  refine ⟨1, chainSingle (ball x (ε / 3)) isOpen_ball ⟨x, mem_ball_self (by linarith)⟩,
    fun _ => ⟨isBounded_ball, lt_of_le_of_lt (diam_ball (by linarith)) (by linarith)⟩, ?_⟩
  rw [singleton_subset_iff]
  simp only [Chain.union, mem_iUnion]
  exact ⟨⟨0, one_pos⟩, mem_ball_self (by linarith)⟩

theorem exists_subset_of_iInter_subset {Y : Type*} [TopologicalSpace Y] {K : ℕ → Set Y}
    (hanti : Antitone K) (hc : IsCompact (K 0)) (hcl : ∀ n, IsClosed (K n)) {U : Set Y}
    (hU : IsOpen U) (h : ⋂ n, K n ⊆ U) : ∃ n, K n ⊆ U := by
  by_contra hno
  push_neg at hno
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => K n \ U) (fun i => diff_subset_diff_left (hanti (Nat.le_succ i)))
    (fun n => by obtain ⟨x, hx, hxU⟩ := not_subset.mp (hno n); exact ⟨x, hx, hxU⟩)
    (hc.diff hU) (fun n => (hcl n).sdiff hU)
  rw [mem_iInter] at hx
  exact (hx 0).2 (h (mem_iInter.mpr fun n => (hx n).1))

/-- The intersection of a decreasing sequence of continua is a continuum. -/
theorem isContinuum_iInter_antitone {K : ℕ → Set X} (hK : ∀ n, Fold.Q78.IsContinuum (K n))
    (hanti : Antitone K) : Fold.Q78.IsContinuum (⋂ n, K n) := by
  have hcl : ∀ n, IsClosed (K n) := fun n => (hK n).1.isClosed
  refine ⟨(hK 0).1.of_isClosed_subset (isClosed_iInter hcl) (iInter_subset _ 0), ?_, ?_⟩
  · exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K
      (fun i => hanti (Nat.le_succ i)) (fun n => (hK n).2.nonempty) (hK 0).1 hcl
  · rw [isPreconnected_closed_iff]
    intro t t' ht ht' hcov ⟨a, haK, hat⟩ ⟨b, hbK, hbt'⟩
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hA : IsClosed ((⋂ n, K n) ∩ t) := (isClosed_iInter hcl).inter ht
    have hB : IsClosed ((⋂ n, K n) ∩ t') := (isClosed_iInter hcl).inter ht'
    have hAB : Disjoint ((⋂ n, K n) ∩ t) ((⋂ n, K n) ∩ t') := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have : x ∈ (⋂ n, K n) ∩ (t ∩ t') := ⟨hx1.1, hx1.2, hx2.2⟩
      rw [hemp] at this; exact this
    obtain ⟨O₁, O₂, hO₁, hO₂, hAO, hBO, hO⟩ := normal_separation hA hB hAB
    obtain ⟨n, hn⟩ := exists_subset_of_iInter_subset hanti (hK 0).1 hcl (hO₁.union hO₂)
      (fun x hx => by
        rcases hcov hx with h | h
        · exact Or.inl (hAO ⟨hx, h⟩)
        · exact Or.inr (hBO ⟨hx, h⟩))
    obtain ⟨z, -, hz1, hz2⟩ := (hK n).2.2 O₁ O₂ hO₁ hO₂ hn
      ⟨a, mem_iInter.mp haK n, hAO ⟨haK, hat⟩⟩ ⟨b, mem_iInter.mp hbK n, hBO ⟨hbK, hbt'⟩⟩
    exact Set.disjoint_left.mp hO hz1 hz2

/-- **Bing's minimal counterexample.** If a continuum is not `ε`-coverable, it contains a
subcontinuum which is not `ε`-coverable but all of whose proper subcontinua are (Brouwer
reduction, `exists_minimal_of_seq`: the property passes to intersections of decreasing sequences,
since a chain covering the intersection covers some member — `exists_subset_of_iInter_subset`).
(Shape change: over the compact space `S`. The skeleton's hypothesis `hε : 0 < ε` turned out
not to be needed; it is kept since it is part of the commissioned statement.) -/
theorem exists_minimal_notCoverable {M : Set S} (hM : Fold.Q78.IsContinuum M) {ε : ℝ}
    (hε : 0 < ε) (hnot : ¬ EpsCoverable M ε) :
    ∃ S' ⊆ M, Fold.Q78.IsContinuum S' ∧ ¬ EpsCoverable S' ε ∧
      ∀ K ⊆ S', Fold.Q78.IsContinuum K → K ≠ S' → EpsCoverable K ε := by
  set P : Set S → Prop := fun s => Fold.Q78.IsContinuum s ∧ s ⊆ M ∧ ¬ EpsCoverable s ε with hP
  have hseq : ∀ h : ℕ → Set S, (∀ n, P (h n)) → Antitone h → P (⋂ n, h n) := by
    intro h hh hanti
    refine ⟨isContinuum_iInter_antitone (fun n => (hh n).1) hanti,
      (iInter_subset h 0).trans (hh 0).2.1, ?_⟩
    rintro ⟨n, D, hD, hsub⟩
    obtain ⟨k, hk⟩ := exists_subset_of_iInter_subset hanti (hh 0).1.1
      (fun n => (hh n).1.1.isClosed) (isOpen_iUnion D.isOpen) hsub
    exact (hh k).2.2 ⟨n, D, hD, hk⟩
  obtain ⟨m, hmM, hPm, hmin⟩ := exists_minimal_of_seq P (fun s hs => hs.1.1.isClosed) hseq
    (s₀ := M) ⟨hM, subset_rfl, hnot⟩
  refine ⟨m, hmM, hPm.1, hPm.2.2, fun K hKm hK hne => ?_⟩
  by_contra hKc
  exact hne (hmin K ⟨hK, hKm.trans hmM, hKc⟩ hKm)

/-- A side of a separation of the complement of a subcontinuum is preconnected (property 2: no
three pieces). -/
theorem side_isPreconnected (hS : BingS S) {H U V : Set S} (hH : Fold.Q78.IsContinuum H)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hcov : U ∪ V = Hᶜ)
    (hVne : V.Nonempty) : IsPreconnected U := by
  intro u v hu hv hsub hUu hUv
  by_contra hemp
  rw [not_nonempty_iff_eq_empty] at hemp
  refine hS.no_three_open hH (hU.inter hu) (hU.inter hv) hV hUu hUv hVne ?_
    (hUV.mono inter_subset_left le_rfl) (hUV.mono inter_subset_left le_rfl) ?_
  · rw [Set.disjoint_iff_inter_eq_empty, ← hemp]
    ext x; simp only [mem_inter_iff]; tauto
  · ext x
    simp only [mem_diff, mem_univ, true_and, mem_union, mem_inter_iff]
    constructor
    · intro hx
      have : x ∈ U ∪ V := hcov ▸ hx
      rcases this with h | h
      · rcases hsub h with h' | h'
        · exact Or.inl (Or.inl ⟨h, h'⟩)
        · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr h
    · rintro ((⟨h, -⟩ | ⟨h, -⟩) | h)
      · exact (hcov ▸ (Or.inl h : x ∈ U ∪ V) : x ∈ Hᶜ)
      · exact (hcov ▸ (Or.inl h : x ∈ U ∪ V) : x ∈ Hᶜ)
      · exact (hcov ▸ (Or.inr h : x ∈ U ∪ V) : x ∈ Hᶜ)

/-- **The two sides of an element** (property 2 gives at most two components of `S ∖ g`; (a)
gives at least two for an interior element). For an element `g = bingElt r` that is not an end
element, `S ∖ g` has exactly two components, and every other element lies in one of them. Stated as
the existence of the two open sides. -/
theorem exists_two_sides (hS : BingS S) {r : S} (hr : ¬ IsEndElt r) :
    ∃ U V : Set S, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (bingElt r)ᶜ ∧
      IsConnected U ∧ IsConnected V := by
  have hcut : IsCutElt r := fun h => hr ((isEndElt_iff_not_isCutElt hS r).mpr fun hc => hc h)
  have hg := bingElt_isContinuum hS r
  have hne : ((bingElt r)ᶜ).Nonempty := by
    obtain ⟨x, hx⟩ := (ne_univ_iff_exists_notMem _).mp (bingElt_ne_univ hS r)
    exact ⟨x, hx⟩
  have hnp : ¬ IsPreconnected (bingElt r)ᶜ := fun h => hcut ⟨hne, h⟩
  simp only [IsPreconnected, not_forall, exists_prop] at hnp
  obtain ⟨u, v, hu, hv, hcov, hun, hvn, huv⟩ := hnp
  rw [not_nonempty_iff_eq_empty] at huv
  have hO := hg.1.isClosed.isOpen_compl
  have hdisj : Disjoint ((bingElt r)ᶜ ∩ u) ((bingElt r)ᶜ ∩ v) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← huv]
    ext x; simp only [mem_inter_iff]; tauto
  have hcov' : (bingElt r)ᶜ ∩ u ∪ (bingElt r)ᶜ ∩ v = (bingElt r)ᶜ := by
    ext x
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro hx
      rcases hcov hx with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  refine ⟨_, _, hO.inter hu, hO.inter hv, hdisj, hcov',
    ⟨hun, side_isPreconnected hS hg (hO.inter hu) (hO.inter hv) hdisj hcov' hvn⟩,
    ⟨hvn, side_isPreconnected hS hg (hO.inter hv) (hO.inter hu) hdisj.symm
      (by rw [union_comm]; exact hcov') hun⟩⟩

/-- **Bing's `H` and `K`**: `g'` together with all elements on one side. With `U`, `V` the two
sides of `g' = bingElt r`: `H = U ∪ g'`, `K = V ∪ g'` are continua, `H ∪ K = S`, `H ∩ K = g'`,
and both are proper. (Nadler 6.3 in the closed form `isContinuum_side`. The skeleton's hypothesis
`hr : ¬ IsEndElt r` turned out not to be needed — it is implicit in the two nonempty sides — and is
kept since it is part of the commissioned statement.) -/
theorem sides_continua (hS : BingS S) {r : S} (hr : ¬ IsEndElt r) {U V : Set S}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hcov : U ∪ V = (bingElt r)ᶜ)
    (hUc : IsConnected U) (hVc : IsConnected V) :
    Fold.Q78.IsContinuum (U ∪ bingElt r) ∧ Fold.Q78.IsContinuum (V ∪ bingElt r) ∧
      U ∪ bingElt r ≠ univ ∧ V ∪ bingElt r ≠ univ := by
  haveI := hS.connected
  have hg := bingElt_isContinuum hS r
  have hUsub : U ⊆ (bingElt r)ᶜ := hcov ▸ subset_union_left
  have hVsub : V ⊆ (bingElt r)ᶜ := hcov ▸ subset_union_right
  have hc : (bingElt r)ᶜ ⊆ U ∪ V := hcov.ge
  have h1 := isContinuum_side hg.1.isClosed hg.2 hU hV hUV hc
    (by rw [inter_eq_right.mpr hUsub]; exact hUc.nonempty)
    (by rw [inter_eq_right.mpr hVsub]; exact hVc.nonempty)
  have h2 := isContinuum_side hg.1.isClosed hg.2 hV hU hUV.symm (by rw [union_comm]; exact hc)
    (by rw [inter_eq_right.mpr hVsub]; exact hVc.nonempty)
    (by rw [inter_eq_right.mpr hUsub]; exact hUc.nonempty)
  rw [inter_eq_right.mpr hUsub] at h1
  rw [inter_eq_right.mpr hVsub] at h2
  refine ⟨h1, h2, fun e => ?_, fun e => ?_⟩
  · obtain ⟨v, hv⟩ := hVc.nonempty
    have : v ∈ U ∪ bingElt r := e ▸ mem_univ v
    rcases this with h | h
    · exact Set.disjoint_left.mp hUV h hv
    · exact hVsub hv h
  · obtain ⟨w, hw⟩ := hUc.nonempty
    have : w ∈ V ∪ bingElt r := e ▸ mem_univ w
    rcases this with h | h
    · exact Set.disjoint_left.mp hUV hw h
    · exact hUsub hw h

-- (Item 3, `exists_degenerate_interior_elt`, is false and was removed in batch 103: see `LEDGER.md`.)

/-- **Q-A. Condition A on the sides.** If `g' = {p'}` is a degenerate interior element with sides
`U`, `V`, then `p'` satisfies condition A for `H = U ∪ {p'}` (and symmetrically for `K`). Bing:
"`p'` satisfies condition A for `M` equal to either `H` or `K`" — unargued; here for the
degenerate case. Proof (as suggested in the commission): `H` is a `BingS` continuum, `{p'}` is an
element of `H` (`bingElt_subtype_subset`) whose complement `U` is connected, hence an end element
of `H`; for a nondegenerate subcontinuum `L ∋ p'` of `H`, `endElt_inter_contains_endElt` (in the
space `H`) makes `{p'}` an end element of `L`, and Theorem 8 (c) for `L` makes `L` irreducible
from `p'` to any point of the other end element of `L`. -/
theorem condA_side (hS : BingS S) {p : S} (hp : bingElt p = {p}) (hpe : ¬ IsEndElt p)
    {U V : Set S} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcov : U ∪ V = (bingElt p)ᶜ) (hUc : IsConnected U) (hVc : IsConnected V) :
    CondA (U ∪ {p}) p := by
  have hHc : Fold.Q78.IsContinuum (U ∪ {p}) := by
    have := (sides_continua hS hpe hU hV hUV hcov hUc hVc).1
    rwa [hp] at this
  have hpU : p ∉ U := fun h =>
    (hcov ▸ (Or.inl h : p ∈ U ∪ V) : p ∈ (bingElt p)ᶜ) (mem_bingElt p)
  have hHnt : (U ∪ {p}).Nontrivial := by
    obtain ⟨w, hw⟩ := hUc.nonempty
    exact ⟨w, Or.inl hw, p, Or.inr rfl, fun h => hpU (h ▸ hw)⟩
  haveI : CompactSpace (U ∪ {p} : Set S) := isCompact_iff_compactSpace.mp hHc.1
  have hSH : BingS (U ∪ {p} : Set S) := bingS_subcontinuum hS hHc hHnt
  set p' : (U ∪ {p} : Set S) := ⟨p, Or.inr rfl⟩ with hp'
  have hgp' : bingElt p' = {p'} := by
    apply Subset.antisymm
    · intro y hy
      have h1 := bingElt_subtype_subset hS hHc p' ⟨y, hy, rfl⟩
      have h2 : (p' : S) = p := rfl
      rw [h2, hp, mem_singleton_iff] at h1
      exact Subtype.ext h1
    · intro y hy
      rw [mem_singleton_iff] at hy
      rw [hy]; exact mem_bingElt p'
  have hend : IsEndElt p' := by
    rw [isEndElt_iff_not_isCutElt hSH]
    intro hcut
    apply hcut
    rw [hgp']
    have hpre : ({p'}ᶜ : Set (U ∪ {p} : Set S)) = (↑) ⁻¹' U := by
      ext ⟨y, hy⟩
      simp only [mem_compl_iff, mem_singleton_iff, mem_preimage]
      constructor
      · intro hne
        rcases hy with h | h
        · exact h
        · exact absurd (Subtype.ext (mem_singleton_iff.mp h)) hne
      · intro hyU heq
        apply hpU
        have : y = p := congrArg Subtype.val heq
        rw [← this]; exact hyU
    rw [hpre]
    have himg : ((↑) : (U ∪ {p} : Set S) → S) '' ((↑) ⁻¹' U) = U := by
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr subset_union_left]
    refine ⟨?_, IsInducing.subtypeVal.isPreconnected_image.mp (by rw [himg]; exact hUc.2)⟩
    obtain ⟨w, hw⟩ := hUc.nonempty
    exact ⟨⟨w, Or.inl hw⟩, hw⟩
  refine ⟨Or.inr rfl, fun W hWH hW hWnt hpW => ?_⟩
  have hW' : Fold.Q78.IsContinuum ((↑) ⁻¹' W : Set (U ∪ {p} : Set S)) :=
    isContinuum_preimage_val (by rwa [inter_eq_left.mpr hWH])
  haveI : CompactSpace ((↑) ⁻¹' W : Set (U ∪ {p} : Set S)) := isCompact_iff_compactSpace.mp hW'.1
  have hp'W : p' ∈ ((↑) ⁻¹' W : Set (U ∪ {p} : Set S)) := hpW
  obtain ⟨e, he, heg⟩ := endElt_inter_contains_endElt hSH hend hW' hp'W (mem_bingElt p')
  have hW'nt : ((↑) ⁻¹' W : Set (U ∪ {p} : Set S)).Nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hWnt
    exact ⟨⟨x, hWH hx⟩, hx, ⟨y, hWH hy⟩, hy, fun h => hxy (congrArg Subtype.val h)⟩
  have hSW := bingS_subcontinuum hSH hW' hW'nt
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_endElts hSW
  obtain ⟨e', he', hee'⟩ : ∃ e' : ((↑) ⁻¹' W : Set (U ∪ {p} : Set S)),
      IsEndElt e' ∧ bingElt e ≠ bingElt e' := by
    by_cases h : bingElt e = bingElt a
    · exact ⟨b, hb, h ▸ hab⟩
    · exact ⟨a, ha, h⟩
  have hirr := bingElt_irreducible hSW e e' he he' hee'
  have heval : ((e : (U ∪ {p} : Set S)) : S) = p := by
    have : (e : (U ∪ {p} : Set S)) ∈ ({p'} : Set (U ∪ {p} : Set S)) :=
      hgp' ▸ heg ⟨e, mem_bingElt e, rfl⟩
    rw [mem_singleton_iff] at this
    rw [this]
  refine ⟨((e' : (U ∪ {p} : Set S)) : S), ?_, hW, hpW, e'.2, fun K hK hKW hpK hqK => ?_⟩
  · intro hq
    apply hee'
    have : e' = e := Subtype.ext (Subtype.ext (hq.trans heval.symm))
    rw [this]
  · have hKH : Fold.Q78.IsContinuum ((↑) ⁻¹' K : Set (U ∪ {p} : Set S)) :=
      isContinuum_preimage_val (by rwa [inter_eq_left.mpr (hKW.trans hWH)])
    have hKW' : Fold.Q78.IsContinuum
        ((↑) ⁻¹' ((↑) ⁻¹' K : Set (U ∪ {p} : Set S)) : Set ((↑) ⁻¹' W : Set (U ∪ {p} : Set S))) :=
      isContinuum_preimage_val (by rw [inter_eq_left.mpr (preimage_mono hKW)]; exact hKH)
    have huniv := hirr _ hKW' (show ((e : (U ∪ {p} : Set S)) : S) ∈ K by rw [heval]; exact hpK) hqK
    refine Subset.antisymm hKW fun x hx => ?_
    have : (⟨⟨x, hWH hx⟩, hx⟩ : ((↑) ⁻¹' W : Set (U ∪ {p} : Set S))) ∈
        ((↑) ⁻¹' ((↑) ⁻¹' K : Set (U ∪ {p} : Set S)) :
          Set ((↑) ⁻¹' W : Set (U ∪ {p} : Set S))) := huniv ▸ trivial
    exact this

omit [CompactSpace S] in
/-- **Q-sep. The separation sentence, degenerate case.** With `g' = {p'}` and `N` an open
neighbourhood of `p'`, `S ∖ N` is the union of the two disjoint closed sets `H ∖ N` and `K ∖ N`.
(Immediate; recorded because the nondegenerate case fails, see `not_separation_of_accumulates'`.) -/
theorem separation_of_degenerate {p : S} {U V : Set S} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hcov : U ∪ V = {p}ᶜ) {N : Set S} (hN : IsOpen N) (hpN : p ∈ N) :
    IsClosed ((U ∪ {p}) \ N) ∧ IsClosed ((V ∪ {p}) \ N) ∧
      Disjoint ((U ∪ {p}) \ N) ((V ∪ {p}) \ N) ∧
      ((U ∪ {p}) \ N) ∪ ((V ∪ {p}) \ N) = Nᶜ := by
  have hpU : p ∉ U := fun h => (hcov ▸ (Or.inl h : p ∈ U ∪ V) : p ∈ ({p}ᶜ : Set S)) rfl
  have hpV : p ∉ V := fun h => (hcov ▸ (Or.inr h : p ∈ U ∪ V) : p ∈ ({p}ᶜ : Set S)) rfl
  have hUc : U ∪ {p} = Vᶜ := by
    ext x
    constructor
    · rintro (h | h) hxV
      · exact Set.disjoint_left.mp hUV h hxV
      · rw [mem_singleton_iff] at h; exact hpV (h ▸ hxV)
    · intro hxV
      by_cases hxp : x = p
      · exact Or.inr hxp
      · have : x ∈ U ∪ V := hcov ▸ hxp
        exact Or.inl (this.resolve_right hxV)
  have hVc : V ∪ {p} = Uᶜ := by
    ext x
    constructor
    · rintro (h | h) hxU
      · exact Set.disjoint_left.mp hUV hxU h
      · rw [mem_singleton_iff] at h; exact hpU (h ▸ hxU)
    · intro hxU
      by_cases hxp : x = p
      · exact Or.inr hxp
      · have : x ∈ U ∪ V := hcov ▸ hxp
        exact Or.inl (this.resolve_left hxU)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hUc]; exact hV.isClosed_compl.sdiff hN
  · rw [hVc]; exact hU.isClosed_compl.sdiff hN
  · rw [Set.disjoint_left]
    rintro x ⟨hx1, hxN⟩ ⟨hx2, -⟩
    rcases hx1 with h | h
    · rcases hx2 with h' | h'
      · exact Set.disjoint_left.mp hUV h h'
      · rw [mem_singleton_iff] at h'; exact hxN (h' ▸ hpN)
    · rw [mem_singleton_iff] at h; exact hxN (h ▸ hpN)
  · ext x
    simp only [mem_union, mem_diff, mem_compl_iff]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
    · intro hxN
      by_cases hxp : x = p
      · exact Or.inl ⟨Or.inr hxp, hxN⟩
      · have : x ∈ U ∪ V := hcov ▸ hxp
        rcases this with h | h
        · exact Or.inl ⟨Or.inl h, hxN⟩
        · exact Or.inr ⟨Or.inl h, hxN⟩

-- Commented-out statement `not_separation_of_accumulates` removed in batch 103; see `LEDGER.md`.

/-- **Refutation of the skeleton's `not_separation_of_accumulates`** (counterexample on the unit
interval: `g = H = {0}`, `K = [0, 1]`, `N = (0, 1/2)`, `H' = {0}`, `K' = [1/2, 1]`). -/
theorem not_separation_of_accumulates_false :
    ¬ (∀ (T : Type) [MetricSpace T] [CompactSpace T] (g H K N : Set T), H ∩ K = g →
      (∀ x ∈ g, x ∈ closure (K \ g)) → IsOpen N → ¬ g ⊆ N →
      ¬ ∃ H' K' : Set T, H' ∪ K' = Nᶜ ∧ Disjoint (closure H') K' ∧ Disjoint H' (closure K') ∧
        H \ N ⊆ H' ∧ K \ (g ∪ N) ⊆ K') := by
  intro h
  set N : Set unitInterval := Subtype.val ⁻¹' Ioo (0 : ℝ) (1 / 2) with hN
  set K' : Set unitInterval := Subtype.val ⁻¹' Ici (1 / 2 : ℝ) with hK'
  have hK'c : IsClosed K' := isClosed_Ici.preimage continuous_subtype_val
  have h0K' : (0 : unitInterval) ∉ K' := by
    simp only [hK', mem_preimage, mem_Ici, Set.Icc.coe_zero]; norm_num
  refine h unitInterval {0} {0} univ N (inter_univ _) ?_ (isOpen_Ioo.preimage continuous_subtype_val)
    ?_ ⟨{0}, K', ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [mem_singleton_iff] at hx
    subst hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨⟨min (ε / 2) 1, ⟨le_min (by linarith) zero_le_one, min_le_right _ _⟩⟩,
      ⟨mem_univ _, ?_⟩, ?_⟩
    · rw [mem_singleton_iff]
      intro e
      have := congrArg Subtype.val e
      simp only [Set.Icc.coe_zero] at this
      have : 0 < min (ε / 2) 1 := lt_min (by linarith) one_pos
      linarith
    · rw [Subtype.dist_eq, Set.Icc.coe_zero, Real.dist_eq, zero_sub, abs_neg,
        abs_of_nonneg (le_min (by linarith) zero_le_one)]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  · intro hsub
    have := hsub (mem_singleton 0)
    simp only [hN, mem_preimage, mem_Ioo, Set.Icc.coe_zero] at this
    exact lt_irrefl _ this.1
  · ext x
    simp only [mem_union, mem_singleton_iff, hK', hN, mem_preimage, mem_Ici, mem_compl_iff,
      mem_Ioo, not_and, not_lt]
    have hx0 : (0 : ℝ) ≤ x := x.2.1
    constructor
    · rintro (h | h)
      · intro h0; rw [h, Set.Icc.coe_zero] at h0; exact absurd h0 (lt_irrefl _)
      · intro _; exact h
    · intro hx
      by_cases hx' : (x : ℝ) = 0
      · left; exact Subtype.ext hx'
      · right; exact hx (lt_of_le_of_ne hx0 (Ne.symm hx'))
  · rw [isClosed_singleton.closure_eq, disjoint_singleton_left]; exact h0K'
  · rw [hK'c.closure_eq, disjoint_singleton_left]; exact h0K'
  · exact diff_subset
  · rintro x ⟨-, hx⟩
    simp only [mem_union, mem_singleton_iff, hN, mem_preimage, mem_Ioo, not_or, not_and,
      not_lt] at hx
    simp only [hK', mem_preimage, mem_Ici]
    have hx0 : (0 : ℝ) ≤ x := x.2.1
    exact hx.2 (lt_of_le_of_ne hx0 (fun e => hx.1 (Subtype.ext e.symm)))

omit [CompactSpace S] in
/-- **The nondegenerate branch of Bing's proof cannot work as written** (corrected form of the
skeleton's `not_separation_of_accumulates`: `¬ g ⊆ N` replaced by `¬ g ⊆ closure N`). If `K ∖ g`
accumulates at every point of `g` (as it does when `g` is a two-sided limit of elements), then for
an open `N` whose closure misses a point of `g` there is no pair of separated sets `H'`, `K'` with
`H' ∪ K' = S ∖ N`, `H ∖ N ⊆ H'`, `K ∖ (g ∪ N) ⊆ K'`. Pure point-set statement, no `BingS`. -/
theorem not_separation_of_accumulates' {g H K N : Set S} (hHK : H ∩ K = g)
    (hacc : ∀ x ∈ g, x ∈ closure (K \ g)) (hgN : ¬ g ⊆ closure N) :
    ¬ ∃ H' K' : Set S, H' ∪ K' = Nᶜ ∧ Disjoint (closure H') K' ∧ Disjoint H' (closure K') ∧
      H \ N ⊆ H' ∧ K \ (g ∪ N) ⊆ K' := by
  rintro ⟨H', K', -, -, h2, hH, hK⟩
  obtain ⟨x, hxg, hxN⟩ := not_subset.mp hgN
  have hxH : x ∈ H := (hHK.symm ▸ hxg : x ∈ H ∩ K).1
  have hxH' : x ∈ H' := hH ⟨hxH, fun h => hxN (subset_closure h)⟩
  have hx1 : x ∈ (closure N)ᶜ ∩ closure (K \ g) := ⟨hxN, hacc x hxg⟩
  have hx2 := isClosed_closure.isOpen_compl.inter_closure hx1
  have hsub : (closure N)ᶜ ∩ (K \ g) ⊆ K' := by
    rintro y ⟨hyN, hyK, hyg⟩
    exact hK ⟨hyK, fun h => h.elim hyg fun h' => hyN (subset_closure h')⟩
  have hx3 : x ∈ closure K' := closure_mono hsub hx2
  exact Set.disjoint_left.mp h2 hxH' hx3

end Structure

/-! ## §3. Sufficiency, conditional on Theorem 10 -/

section Sufficiency

variable {S : Type u} [MetricSpace S] [CompactSpace S]

omit [CompactSpace S] in
/-- **Amalgamation of two chains at a common end point** (Bing's displayed chain
`H'·h₁, …, H'·h_{m−1}, (H'·h_m) ∪ N ∪ (K'·k₁), K'·k₂, …, K'·k_n`). If `H ∩ K = {p}`,
`H ∪ K = S`, `h` is an `ε`-chain covering `H` with `p ∈ h_m ∖ cl h_{m−1}` and in no other link's
closure, `k` an `ε`-chain covering `K` with `p ∈ k₁ ∖ cl k₂` and in no other link's closure, then
`S` is covered by an `ε`-chain. (Links of the displayed chain must be open; `H ∖ N` and `K ∖ N`
are the separated pieces; the middle link has diameter `< ε` once `N` is small.) Proof: the general
form `epsCoverable_amalgam_gen` (`Theorem11Gen.lean`); there the middle link is the small ball `N`
alone, the links `h_m`, `k₁` being kept (cut down to open neighbourhoods of `H ∖ N'`, `K ∖ N'`) as
separate links, which avoids Bing's middle link of diameter up to `2ε`. -/
theorem epsCoverable_amalgam {H K : Set S} (hH : Fold.Q78.IsContinuum H)
    (hK : Fold.Q78.IsContinuum K) {p : S} (hHK : H ∩ K = {p}) (hcov : H ∪ K = univ) {ε : ℝ}
    (hε : 0 < ε)
    (hh : ∃ (m : ℕ) (h : Chain S m) (hm : 0 < m), IsEpsChain h ε ∧ H ⊆ h.union ∧
      p ∈ h.link ⟨m - 1, by omega⟩ ∧ ∀ j : Fin m, j.val ≠ m - 1 → p ∉ closure (h.link j))
    (hk : ∃ (n : ℕ) (k : Chain S n) (hn : 0 < n), IsEpsChain k ε ∧ K ⊆ k.union ∧
      p ∈ k.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (k.link j)) :
    EpsCoverable (univ : Set S) ε :=
  epsCoverable_amalgam_gen hH hK hHK hcov.ge hε hh hk

omit [CompactSpace S] in
/-- Condition A transfers from a subcontinuum (as a subtype) to the ambient space. -/
theorem condA_image_val {S' : Set S} {A : Set S'} {p : S'} (h : CondA A p) :
    CondA (((↑) : S' → S) '' A) p := by
  refine ⟨⟨p, h.1, rfl⟩, fun W hWA hW hWnt hpW => ?_⟩
  have hWS' : W ⊆ S' := hWA.trans (Subtype.coe_image_subset _ _)
  have hW' : Fold.Q78.IsContinuum ((↑) ⁻¹' W : Set S') :=
    isContinuum_preimage_val (by rwa [inter_eq_left.mpr hWS'])
  have hWA' : ((↑) ⁻¹' W : Set S') ⊆ A := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := hWA hx
    rwa [← Subtype.ext hyx]
  have hW'nt : ((↑) ⁻¹' W : Set S').Nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hWnt
    exact ⟨⟨x, hWS' hx⟩, hx, ⟨y, hWS' hy⟩, hy, fun e => hxy (congrArg Subtype.val e)⟩
  obtain ⟨q, hqp, hirr⟩ := h.2 _ hWA' hW' hW'nt hpW
  refine ⟨q, fun e => hqp (Subtype.ext e), hW, hpW, hirr.2.2.1, fun K hK hKW hpK hqK => ?_⟩
  have hK' : Fold.Q78.IsContinuum ((↑) ⁻¹' K : Set S') :=
    isContinuum_preimage_val (by rwa [inter_eq_left.mpr (hKW.trans hWS')])
  have := hirr.2.2.2 _ hK' (preimage_mono hKW) hpK hqK
  refine Subset.antisymm hKW fun x hx => ?_
  have : (⟨x, hWS' hx⟩ : S') ∈ ((↑) ⁻¹' K : Set S') := this ▸ hx
  exact this

/-- **Theorem 11, sufficiency, from Theorem 10 as a hypothesis.** A compact hereditarily
decomposable, atriodic, hereditarily unicoherent continuum is snake-like. The hypothesis `hT10` is
the statement of `theorem10_1951` (`EndPoints51.lean`), which is still open; when it closes, this
becomes unconditional.

(Shape change, batch 96: the further hypothesis `hdeg` is the statement of
`exists_degenerate_interior_elt` for compact metric spaces in the universe of `S`; it is refuted in
universe `0` by `theorem11_hdeg_refuted` (`HPC/Plane/Layers51.lean`);
it is applied to Bing's minimal counterexample `S'`, a `BingS` space by `bingS_subcontinuum`.)
Proof: Bing's — minimal non-`ε`-coverable `S'` (`exists_minimal_notCoverable`), a degenerate
interior element `{p}` of `S'` (`hdeg`), its two sides (`exists_two_sides`, `sides_continua`),
condition A on each side (`condA_side`, transferred by `condA_image_val`), Theorem 10 chains with
`p` in an end link only (`hT10`), amalgamation (`epsCoverable_amalgam_gen`).

Superseded by `theorem11_1951` / `theorem11_1951_iff` (`Theorem11B.lean`), which need neither
hypothesis. -/
theorem theorem11_1951_of_T10
    (hT10 : ∀ {M : Set S}, Fold.Q78.IsContinuum M → ∀ {m : ℕ} (D : Chain S m), M ⊆ D.union →
      ∀ {p : S}, CondA M p →
      ∃ (n : ℕ) (E : Chain S n) (hn : 0 < n), M ⊆ E.union ∧ E.Refines D ∧
        p ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (E.link j))
    (hdeg : ∀ (T : Type u) [MetricSpace T] [CompactSpace T], BingS T →
      ∃ p : T, bingElt p = {p} ∧ ¬ IsEndElt p)
    (hS : BingS S) : IsSnakeLike (univ : Set S) := by
  haveI := hS.connected
  refine ⟨⟨isCompact_univ, isConnected_univ⟩, fun ε hε => ?_⟩
  by_contra hnot
  obtain ⟨S', -, hS', hnc, hmin⟩ :=
    exists_minimal_notCoverable ⟨isCompact_univ, isConnected_univ⟩ hε hnot
  have hnt : S'.Nontrivial := by
    by_contra h
    obtain ⟨x, hx⟩ := hS'.2.nonempty
    rw [(Set.not_nontrivial_iff.mp h).eq_singleton_of_mem hx] at hnc
    exact hnc (epsCoverable_singleton x hε)
  haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
  have hBS := bingS_subcontinuum hS hS' hnt
  obtain ⟨p, hp, hpe⟩ := hdeg S' hBS
  obtain ⟨U, V, hU, hV, hUV, hcov, hUc, hVc⟩ := exists_two_sides hBS hpe
  have hAU := condA_side hBS hp hpe hU hV hUV hcov hUc hVc
  have hAV := condA_side hBS hp hpe hV hU hUV.symm (by rw [union_comm]; exact hcov) hVc hUc
  obtain ⟨hHc, hKc, hHne, hKne⟩ := sides_continua hBS hpe hU hV hUV hcov hUc hVc
  rw [hp] at hHc hKc hHne hKne hcov
  have hpU : p ∉ U := fun h => (hcov ▸ (Or.inl h : p ∈ U ∪ V) : p ∈ ({p}ᶜ : Set S')) rfl
  have hpV : p ∉ V := fun h => (hcov ▸ (Or.inr h : p ∈ U ∪ V) : p ∈ ({p}ᶜ : Set S')) rfl
  -- the two sides in `S`
  have side : ∀ {A : Set S'}, Fold.Q78.IsContinuum A → A ≠ univ → CondA A p →
      ∃ (n : ℕ) (E : Chain S n) (hn : 0 < n), IsEpsChain E ε ∧ ((↑) : S' → S) '' A ⊆ E.union ∧
        (p : S) ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → (p : S) ∉ closure (E.link j) := by
    intro A hA hAne hAp
    have hAS : Fold.Q78.IsContinuum (((↑) : S' → S) '' A) := isContinuum_image_val hA
    have hAsub : ((↑) : S' → S) '' A ⊆ S' := Subtype.coe_image_subset _ _
    have hAne' : ((↑) : S' → S) '' A ≠ S' := by
      intro e
      apply hAne
      refine eq_univ_of_forall fun x => ?_
      have : (x : S) ∈ ((↑) : S' → S) '' A := by rw [e]; exact x.2
      obtain ⟨y, hy, hyx⟩ := this
      rwa [← Subtype.ext hyx]
    obtain ⟨m, D, hD, hAD⟩ := hmin _ hAsub hAS hAne'
    obtain ⟨n, E, hn, hAE, hED, hp0, hpcl⟩ := hT10 hAS D hAD (condA_image_val hAp)
    exact ⟨n, E, hn, isEpsChain_of_refines hED hD, hAE, hp0, hpcl⟩
  obtain ⟨n₁, E₁, hn₁, hE₁, hHE₁, hp₁, hpcl₁⟩ := side hHc hHne hAU
  obtain ⟨n₂, E₂, hn₂, hE₂, hKE₂, hp₂, hpcl₂⟩ := side hKc hKne hAV
  have hrev : Fin.rev (⟨n₁ - 1, by omega⟩ : Fin n₁) = ⟨0, hn₁⟩ :=
    Fin.ext (by simp [Fin.val_rev]; omega)
  have hHK : ((↑) : S' → S) '' (U ∪ {p}) ∩ ((↑) : S' → S) '' (V ∪ {p}) = {(p : S)} := by
    rw [← image_inter Subtype.val_injective, ← image_singleton]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact absurd h2 (Set.disjoint_left.mp hUV h1)
      · exact h2
      · exact h1
      · exact h1
    · intro h; exact ⟨Or.inr h, Or.inr h⟩
  have hcovS : S' ⊆ ((↑) : S' → S) '' (U ∪ {p}) ∪ ((↑) : S' → S) '' (V ∪ {p}) := by
    intro x hx
    by_cases hxp : (⟨x, hx⟩ : S') = p
    · exact Or.inl ⟨p, Or.inr rfl, by rw [← hxp]⟩
    · have : (⟨x, hx⟩ : S') ∈ U ∪ V := hcov ▸ hxp
      rcases this with h | h
      · exact Or.inl ⟨_, Or.inl h, rfl⟩
      · exact Or.inr ⟨_, Or.inl h, rfl⟩
  refine hnc (epsCoverable_amalgam_gen (isContinuum_image_val hHc) (isContinuum_image_val hKc)
    hHK hcovS hε ⟨n₁, E₁.reverse, hn₁, fun i => hE₁ _, fun x hx => ?_, ?_, ?_⟩
    ⟨n₂, E₂, hn₂, hE₂, hKE₂, hp₂, hpcl₂⟩)
  · obtain ⟨i, hi⟩ := exists_link_of_mem_union (hHE₁ hx)
    simp only [Chain.union, mem_iUnion, Chain.reverse_link]
    exact ⟨Fin.rev i, by rw [Fin.rev_rev]; exact hi⟩
  · rw [Chain.reverse_link, hrev]; exact hp₁
  · intro j hj
    rw [Chain.reverse_link]
    exact hpcl₁ _ (by rw [Fin.val_rev]; omega)

/-- **Theorem 11 as an equivalence**, for a compact nondegenerate hereditarily decomposable
continuum, conditional as above (shape change: also on `hdeg`).

Superseded by `theorem11_1951` / `theorem11_1951_iff` (`Theorem11B.lean`), which need neither
hypothesis. -/
theorem theorem11_1951_iff_of_T10
    (hT10 : ∀ {M : Set S}, Fold.Q78.IsContinuum M → ∀ {m : ℕ} (D : Chain S m), M ⊆ D.union →
      ∀ {p : S}, CondA M p →
      ∃ (n : ℕ) (E : Chain S n) (hn : 0 < n), M ⊆ E.union ∧ E.Refines D ∧
        p ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (E.link j))
    (hdeg : ∀ (T : Type u) [MetricSpace T] [CompactSpace T], BingS T →
      ∃ p : T, bingElt p = {p} ∧ ¬ IsEndElt p)
    [ConnectedSpace S] [Nontrivial S] (hd : IsHereditarilyDecomposable (univ : Set S)) :
    IsSnakeLike (univ : Set S) ↔
      IsAtriodic (univ : Set S) ∧ IsHereditarilyUnicoherent (univ : Set S) := by
  constructor
  · intro h
    exact ⟨isAtriodic_of_isSnakeLike h, isHereditarilyUnicoherent_of_isSnakeLike h⟩
  · rintro ⟨ha, hu⟩
    exact theorem11_1951_of_T10 hT10 hdeg ⟨inferInstance, inferInstance, ha, hu, hd⟩

end Sufficiency

end HPC.Plane
