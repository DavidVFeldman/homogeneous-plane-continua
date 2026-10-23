import HPC.Hagopian.H84Fold
import HPC.Hagopian.H84Lemma1415
import HPC.Hagopian.H84Lemma12

/-!
# Batch 186 skeleton: Hagopian 1984 III — the quotient package; Lemmas 12–16

Save as `HPC/Hagopian/Hagopian84B.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian84B` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; record each shape in the report. Unproved items are
commented out with an `OPEN` note, as before. Every theorem with a named `Prop` or structure among
its hypotheses gets a non-vacuity note.

Source: Hagopian 1984 (`doc/sources/hagopian1984.pdf`), pp. 339–344. Route: commission 186.
Indexing: the links `L 0, …, L 4` are the paper's `L₁, …, L₅`, and `midUnion L = L 1 ∪ L 2 ∪ L 3`
is `⋃𝔏′`. Lemmas 12–16 keep the shapes of the commented-out blocks of `Hagopian84A.lean`; delete
those blocks when the statements are proved here, leaving one-line pointers.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## §2. The quotient package -/

section Package

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- The inverse of a `δ`-homeomorphism is a `δ`-homeomorphism. -/
theorem dist_symm_lt_of_small {δ : ℝ} (g : M ≃ₜ M) (hg : ∀ v, dist v (g v) < δ) :
    ∀ v, dist v (g.symm v) < δ := by
  intro v
  have := hg (g.symm v)
  rw [g.apply_symm_apply, dist_comm] at this
  exact this

/-- **§2.1, a Jones decomposition** (what Theorem 1 of 1984 produces with `N = M`): upper
semicontinuous; connected classes, none equal to `M`; respected by every `δ`-homeomorphism for some
`δ > 0`; and an arc of classes (a compact `C` with a continuous surjection `c` onto `[0, 1]` whose
fibres are the traces of the classes). -/
structure IsJonesDecomp84 (r : Setoid M) : Prop where
  usc : IsUSCDecomp r
  conn : ∀ x, IsConnected (cls r x)
  proper : ∀ x, cls r x ≠ univ
  invariant : ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) → ∀ x y, r x y → r (h x) (h y)
  arc : ∃ (C : Set M) (c : C → unitInterval), IsCompact C ∧ Continuous c ∧
    Function.Surjective c ∧ ∀ x y : C, c x = c y ↔ r x y

/-- **§2.2, homogeneity**: finite compositions of `δ`-homeomorphisms act transitively on `M`
(the orbits are open by `hagopian84_lemma1`, and `M` is connected). This replaces the chain of
points `vᵢ` of p. 344. -/
theorem exists_comp_small_homeo (hX : IsHomogeneous M) {δ : ℝ} (hδ : 0 < δ)
    (Q : (M ≃ₜ M) → Prop) (hQ : ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) → Q h)
    (hQt : ∀ f g, Q f → Q g → Q (f.trans g)) (x y : M) : ∃ h, Q h ∧ h x = y := by
  have hid : Q (Homeomorph.refl M) := hQ _ fun v => by simpa using hδ
  set O : Set M := {z | ∃ h, Q h ∧ h x = z} with hO
  have hxO : x ∈ O := ⟨Homeomorph.refl M, hid, rfl⟩
  have hself : ∀ z : M, z ∈ Wset84 z δ := fun z => ⟨Homeomorph.refl M, fun v => by simpa using hδ, rfl⟩
  have hopen : IsOpen O := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨h, hh, rfl⟩
    refine ⟨Wset84 (h x) δ, ?_, hagopian84_lemma1 hX _ δ, hself _⟩
    rintro w ⟨g, hg, rfl⟩
    exact ⟨h.trans g, hQt h g hh (hQ g hg), rfl⟩
  have hclosed : IsClosed O := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    refine ⟨Wset84 z δ, ?_, hagopian84_lemma1 hX _ δ, hself z⟩
    rintro w ⟨g, hg, rfl⟩ ⟨h, hh, hhw⟩
    exact hz ⟨h.trans g.symm, hQt h _ hh (hQ _ (dist_symm_lt_of_small g hg)), by simp [hhw]⟩
  rcases isClopen_iff.1 ⟨hclosed, hopen⟩ with h | h
  · rw [h] at hxO; exact absurd hxO (notMem_empty x)
  · have hy : y ∈ O := h ▸ mem_univ y
    exact hy

/-- **§2.1, the reduction**: `Hagopian84Decomp` from Jones decompositions (route: commission 186
§2.2). Non-vacuity note required. -/
theorem hagopian84Decomp_of_package
    (hP : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M], IsHomogeneous M →
      ¬ IsDecomposableSpace M → ¬ IsHereditarilyIndecomposable (univ : Set M) →
        ∃ r : Setoid M, IsJonesDecomp84 r) :
    Hagopian84Decomp := by
  intro M _ _ hX hi hH
  obtain ⟨r, hr⟩ := hP M hX hi hH
  haveI := t2Space_quotient hr.usc
  haveI := metrizableSpace_quotient hr.usc
  letI : MetricSpace (Quotient r) := TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨δ, hδ, hinv⟩ := hr.invariant
  have hfib : ∀ x : M, Quotient.mk r ⁻¹' {Quotient.mk r x} = cls r x := fun x => by
    ext z
    simp only [mem_preimage, mem_singleton_iff]
    exact mk_eq_mk_iff_mem_cls
  refine ⟨Quotient r, inferInstance, inferInstance, Quotient.mk r, continuous_quotient_mk',
    Quotient.mk_surjective, fun y => ?_, fun y => ?_, fun y₁ y₂ => ?_, ?_⟩
  · induction y using Quotient.inductionOn with | h x => rw [hfib]; exact hr.conn x
  · induction y using Quotient.inductionOn with | h x => rw [hfib]; exact hr.proper x
  · -- homogeneity: compositions of `δ`-homeomorphisms respect `r` and act transitively
    induction y₁ using Quotient.inductionOn with | h x₁ => ?_
    induction y₂ using Quotient.inductionOn with | h x₂ => ?_
    obtain ⟨T, hT, hTx⟩ := exists_comp_small_homeo hX hδ (fun T => ∀ a b, r a b ↔ r (T a) (T b))
      (fun T hT a b => ⟨hinv T hT a b, fun hab => by
        have := hinv T.symm (dist_symm_lt_of_small T hT) (T a) (T b) hab
        simpa using this⟩)
      (fun f g hf hg a b => (hf a b).trans (hg (f a) (f b))) x₁ x₂
    obtain ⟨S, hS⟩ := exists_homeomorph_quotient T hT
    exact ⟨S, by rw [hS, hTx]⟩
  · -- the arc: the composite `C → M → M/r` factors through `c`
    obtain ⟨C, c, hCc, hcc, hcs, hcr⟩ := hr.arc
    haveI : CompactSpace C := isCompact_iff_compactSpace.1 hCc
    let c' : C(C, unitInterval) := ⟨c, hcc⟩
    have hq : IsQuotientMap c' := hcc.isClosedMap.isQuotientMap hcc hcs
    let g : C(C, Quotient r) := ⟨fun z => Quotient.mk r z.1,
      continuous_quotient_mk'.comp continuous_subtype_val⟩
    have hfac : Function.FactorsThrough g c' := fun a b hab => Quotient.sound ((hcr a b).1 hab)
    let φ := hq.lift g hfac
    have hφ : ∀ z, φ (c z) = Quotient.mk r z.1 := fun z =>
      DFunLike.congr_fun (hq.lift_comp g hfac) z
    have hinj : Function.Injective φ := by
      intro t₁ t₂ ht
      obtain ⟨z₁, rfl⟩ := hcs t₁
      obtain ⟨z₂, rfl⟩ := hcs t₂
      rw [hφ, hφ] at ht
      exact (hcr z₁ z₂).2 (Quotient.exact ht)
    exact ⟨range φ, ⟨(φ.continuous.isClosedEmbedding hinj).isEmbedding.toHomeomorph.symm⟩⟩

end Package

/-! ## §3. Lemmas 12 and 13: the chain -/

section Chain

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- `W(S, δ)` (p. 339): the points `h(x)` with `x ∈ S` and `h` a `δ`-homeomorphism. Open by
`hagopian84_lemma1`. -/
def WsetOf (S : Set M) (δ : ℝ) : Set M := ⋃ x ∈ S, Wset84 x δ

/-- The links of the proof of Lemma 13 (p. 339): `L i = W(k⁻¹[[x₃ᵢ, x₃ᵢ₊₃]], δ)`, the paper's
`Lᵢ₊₁ = W(k⁻¹[[x₃ᵢ, x₃ᵢ₊₃]], δ)`. -/
def chainLinks84 {E : Set M} (k : E → unitInterval) (x : Fin 16 → unitInterval) (δ : ℝ) :
    Fin 5 → Set M :=
  fun i => WsetOf (layerSet k (Icc (x ⟨3 * i.val, by have := i.isLt; omega⟩)
    (x ⟨3 * i.val + 3, by have := i.isLt; omega⟩))) δ

/-- **§3.1 step 4(a), folds** (combinatorics; the reduction "By (1), (2), and (3), there exist
numbers `r`, `s`, and `t` …" of p. 340, with its mirror case). Five open subsets of `[0, 1]`,
non-adjacent ones disjoint, covering, with `0 ∈ V 0 \ V 1` and `1 ∈ V 4 \ V 3`. If one of them is
not an interval, there is a fold.

*Proof* (`exists_fold_aux`, `H84Fold.lean`): not the π-argument of the commission but a sweep
from left to right. Without a fold, if `a ∈ V p`, no point left of `a` lies in a later set and no
point `≥ a` in an earlier one, then `V p` is an interval and the first point after `a` outside `V p`
lies in `V (p + 1)`, with the same two properties. A gap in `V p` would give a point of `V p` with
points outside `V p` on both sides; the last such point before it and the first after it lie in
neighbours of `V p`, and the two properties force both into the same neighbour, which is a fold.
Start at `a = 0`, `p = 0`. -/
theorem exists_fold {V : Fin 5 → Set unitInterval} (hV : ∀ i, IsOpen (V i))
    (hcov : ∀ u, ∃ i, u ∈ V i) (hdisj : ∀ i j : Fin 5, (i : ℕ) + 1 < j → Disjoint (V i) (V j))
    (h0 : (0 : unitInterval) ∈ V 0 \ V 1) (h1 : (1 : unitInterval) ∈ V 4 \ V 3)
    (hnc : ∃ i, ¬ (V i).OrdConnected) :
    ∃ r s t : unitInterval, r < s ∧ s < t ∧ ∃ p q : Fin 5, ((p : ℕ) + 1 = q ∨ (q : ℕ) + 1 = p) ∧
      s ∈ V p ∧ r ∈ V q \ V p ∧ t ∈ V q \ V p :=
  exists_fold_aux hV hcov hdisj h0 h1 hnc

-- `chainLinks84_runsStraight`: proved in batch 187, `Hagopian84C.lean` (`H84Runs13.lean`).

-- `chainLinks84_regular`: proved in batch 187, `Hagopian84C.lean` (`H84Regular13.lean`).

/-- **§3.2, Lemma 12** (p. 339). Shape of the commented-out block of `Hagopian84A.lean`, with the
allowed addition: every component of `midUnion P` is a component of `midUnion L`.

*Proof* (`hagopian84_lemma12_aux`, `H84Lemma12.lean`): Hagopian's construction, `A = L 0 ∖ Cl L 1`,
`B = L 4 ∖ Cl L 3`, Moore's Theorem 44 in the compact form `exists_closed_split_of_no_connected`
inside `M ∖ (A ∪ B)`, and `P = (L 0, L 1 ∖ L', L 2 ∖ L', L 3 ∖ L', L 4)`. The hypothesis of
Theorem 44 comes from atriodicity directly (the closure of a connected set meeting both sets is a
continuum meeting `E` and missing both end layers, so `subset_of_meets_avoids` puts it in `E`); the
"essential subcontinuum" sentence is not needed. -/
theorem hagopian84_lemma12 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {L : Fin 5 → Set M} (hL : IsChain5 L)
    (hn : IsNormal5 L) (hr : IsRegular5 L) (hs : RunsStraight k L)
    (h0 : layer k 0 ⊆ L 0 \ closure (L 1)) (h1 : layer k 1 ⊆ L 4 \ closure (L 3)) :
    ∃ P, IsOrderedRefinement5 P L ∧ IsFree5 P ∧ IsNormal5 P ∧ IsRegular5 P ∧ RunsStraight k P ∧
      ∀ x ∈ midUnion P, connectedComponentIn (midUnion P) x =
        connectedComponentIn (midUnion L) x :=
  hagopian84_lemma12_aux hX hi hE hL hn hr hs h0 h1

-- `hagopian84_lemma13`: proved in batch 187, `Hagopian84C.lean` (`H84Lemma13.lean`).

end Chain

/-! ## §4. Lemmas 14 and 15; the arc -/

section Delta

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- **§4.1** (p. 341: "Note that since `𝒫` is regular, `Δ(𝒫)` is a decomposition of
`(⋃𝒫)∖Cl(P₁ ∪ P₅)`").

*Shape change:* `hX`, `hi` and `hn` are dropped (not used). *Proof* (`delta5_partition_aux`): a
layer through a point outside `Cl Pᵢ` misses `Cl Pᵢ` (running straight, condition (4)); a member of
`Δ(𝒫)` lies in the component it comes from (`K ∪ Z` lies between `K` and `Cl K`), so two members
that meet come from the same component, where the decomposition is unique. -/
theorem delta5_partition {P : Fin 5 → Set M} (hP : IsChain5 P) (hr : IsRegular5 P) :
    ⋃₀ Delta5 P = (⋃ i, P i) \ closure (P 0 ∪ P 4) ∧
      ∀ Z ∈ Delta5 P, ∀ Z' ∈ Delta5 P, (Z ∩ Z').Nonempty → Z = Z' :=
  delta5_partition_aux hP.isOpen hr

omit [ConnectedSpace M] in
/-- **§4.1, positivity** (unargued: the `ε = ½ρ(⋃Δ(𝒫), M∖⋃𝒫′)` of Lemmas 14 and 15 is
positive).

*Shape change:* `hX`, `hi` and `hn` are dropped (not used). *Proof* (`delta5_dist_pos_aux`, the
route of commission 186 §4.1): `Cl ⋃Δ(𝒫) ⊆ ⋃𝒫′` by freeness, then compactness. -/
theorem delta5_dist_pos {P : Fin 5 → Set M} (hP : IsChain5 P) (hf : IsFree5 P)
    (hr : IsRegular5 P) :
    ∃ η > 0, ∀ z ∈ ⋃₀ Delta5 P, ∀ y : M, y ∉ midUnion P → η ≤ dist z y :=
  delta5_dist_pos_aux hP.isOpen hf hr

/-- **§4.2, Lemma 14** (p. 341). Shape of the commented-out block (Hausdorff form).

*Shape change:* the normality added by the skeleton is dropped (not used). *Proof*
(`hagopian84_lemma14_aux`): for `ε' = min ε η` (`η` of `delta5_dist_pos`), `W(z, ε')` is open; an
`ε'`-homeomorphism `h` with `h z = z'` satisfies `h[Z] = Z'` by Lemma 3 (`delta_translate_eq`: the
end layers of both closures lie outside `⋃𝒫′`, at distance `≥ η` from `Z`, `Z'`, which checks the
three hypotheses of `hagopian76_lemma3`). -/
theorem hagopian84_lemma14 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hf : IsFree5 P) (hr : IsRegular5 P) :
    ∀ Z ∈ Delta5 P, ∀ z ∈ Z, ∀ ε > 0, ∃ δ > 0, ∀ Z' ∈ Delta5 P, ∀ z' ∈ Z', dist z z' < δ →
      Z ⊆ thickening ε Z' ∧ Z' ⊆ thickening ε Z :=
  hagopian84_lemma14_aux hX hi hP hf hr

/-- **§4.3, Lemma 15** (p. 341). Shape of the commented-out block, with normality added; `ε` is
smaller than Hagopian's (commission 186 §4.3).

*Proof* (`hagopian84_lemma15_aux`): `ε` is less than `η` and than the distances from `Cl P 0` to
`Cl P 2 ∪ Cl P 3 ∪ Cl P 4` and from `Cl P 4` to `Cl P 0 ∪ Cl P 1 ∪ Cl P 2`. Then `h[Z]` lies in one
component `K′` of `⋃𝒫′`; `h[Cl K] ∩ Cl K′` meets two layers of `h[Cl K]` (else
`no_arm_at_interior_layer`); `layers_agree` makes `h[Z]` a layer of `Cl K′`, the degenerate case
being impossible because `h` keeps the end layers of `Cl K` near `P 0` and `P 4`. -/
theorem hagopian84_lemma15 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P)
    (hr : IsRegular5 P) :
    ∃ ε > 0, ∀ Z ∈ Delta5 P, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < ε) → h '' Z ∈ Omega5 P :=
  hagopian84_lemma15_aux hX hi hP hn hf hr

omit [CompactSpace M] [ConnectedSpace M] in
/-- **§4.4, the arc** (p. 344: "Since `M/𝔇` is an atriodic homogeneous continuum that contains an
arc", unargued): the closure of a component of `midUnion P` has a closed interval of layers in
`Δ(𝒫)`.

*Shape change:* `hX`, `hi` and `hr` are dropped (not used). *Proof* (`exists_interval_in_P2`): the
closure meets `P 2` (otherwise `P 0 ∪ P 1` and `P 3 ∪ P 4` separate it); the layer through such a
point lies in `P 2`, so misses `Cl(P 0 ∪ P 4)` by normality; the parameters of layers inside `P 2`
form an open set. -/
theorem exists_interval_in_delta {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) {x : M}
    (hx : x ∈ midUnion P) {c : closure (connectedComponentIn (midUnion P) x) → unitInterval}
    (hc : IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) x)) c)
    (hcs : RunsStraight c P) :
    ∃ a b : unitInterval, a < b ∧ ∀ t ∈ Icc a b, layer c t ∈ Delta5 P :=
  exists_interval_in_delta_aux hP hn hx hc hcs

end Delta

/-! ## §5. Lemma 16 -/

-- `hagopian84_lemma16`: proved in batch 187, `Hagopian84C.lean` (`H84Strand.lean`).

end HPC.Hagopian
