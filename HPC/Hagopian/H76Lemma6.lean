import HPC.Hagopian.Hagopian76D
import HPC.Hagopian.H76Absorb

/-!
# Batch 160, item A: Lemma 6, first part — `Cl R(X, E)` is indecomposable

Hagopian 1976, pp. 342–343. Write `X = k⁻¹(0)`, `R = R(X, E)`, `𝓕` for the extensions of `E` away
from `X`, and suppose `Cl R = B ∪ C` with `B`, `C` proper subcontinua.

* Step 1 (`lemma6_step1`): one of `B`, `C` contains `X`; call it `B`. (Via `E`: `E ∩ B`, `E ∩ C` are
  continua; one meeting `X` and another layer contains `X`, `layer_zero_subset_of_meets`.)
* Step 2 (`lemma6_step2`): `X ∩ C = ∅`. (An element `H` of `𝓕` meeting `B − C` and `C − B`; the
  continuum among `H ∩ B`, `H ∩ C` that meets the far end layer of `H` is `H`.)
* Step 3 (`lemma6_step3`): if `K ∈ 𝓕` meets `C − B`, then `Cl R − C ⊆ K` (so `B − C ⊆ K`).
* Absorption (`subset_extUnion_of_meets`, `H76Absorb.lean`): `C` misses `X` and meets `K`, so
  `C ⊆ R`.
* Steps 4–5 (`lemma6_main`): the sequence `{Fᵢ}`, the far-end points `zᵢ ∈ C`, a cluster point
  `c ∈ C ⊆ R`; `L ∈ 𝓕` containing `K ∪ {c}`, `w ∈ R − L`, `δ`, and (Lemma 2) a `δ`-homeomorphism `f`
  with `f(c) = zᵢ`, `w ∈ Fᵢ`. Then `L ∩ f[L] = ∅`, `f[L] ⊆ R` (absorption again), and
  `f[X] ⊆ (B ∪ C) − C ⊆ K ⊆ L`: a contradiction.

Hagopian proves in step 5 that `c ∉ R` and then, in steps 6–7, derives a contradiction from
`c ∉ R` (homeomorphisms `h₁`, `h₂`, the triod `C ∪ N ∪ h₁⁻¹[N] ∪ h₂⁻¹[P]`). Here absorption gives
`C ⊆ R` outright, so `c ∈ R`, and step 5 alone gives the contradiction; steps 6–7 are not needed.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Lemma6

variable {M : Set Pt}

/-! ### Generalities -/

/-- Two disjoint sets, one compact and one closed, are a positive distance apart. -/
theorem exists_pos_le_dist {α : Type*} [MetricSpace α] {A B : Set α} (hA : IsCompact A)
    (hB : IsClosed B) (h : Disjoint A B) : ∃ ε > 0, ∀ a ∈ A, ∀ b ∈ B, ε ≤ dist a b := by
  obtain ⟨δ, hδ, hdis⟩ := h.exists_thickenings hA hB
  refine ⟨δ, hδ, fun a ha b hb => le_of_not_gt fun hlt => ?_⟩
  exact disjoint_left.1 hdis (mem_thickening_iff.2 ⟨a, ha, by rwa [dist_comm]⟩)
    (self_subset_thickening hδ _ hb)

/-- The end layer `d⁻¹(0)` lies in the closure of `d⁻¹(0, s)`, for `0 < s`. -/
theorem layer_zero_subset_closure {F : Set M} {d : F → unitInterval} (hd : Continuous d)
    (hd0 : ∀ t, interior (d ⁻¹' {t}) = ∅) {s : unitInterval} (hs : 0 < s) :
    layer d 0 ⊆ closure (layerSet d (Ioo 0 s)) := by
  rintro _ ⟨w, hw, rfl⟩
  have hw1 : d w = 0 := hw
  have hcl : w ∈ closure (d ⁻¹' Ioo 0 s) := by
    rw [_root_.mem_closure_iff]
    intro o ho hwo
    have ho' : IsOpen (o ∩ d ⁻¹' Iio s) := ho.inter (isOpen_Iio.preimage hd)
    have hwo' : w ∈ o ∩ d ⁻¹' Iio s := ⟨hwo, by rw [mem_preimage, hw1]; exact hs⟩
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hsub : o ∩ d ⁻¹' Iio s ⊆ d ⁻¹' {0} := by
      intro v ⟨hvo, hvs⟩
      by_contra hv1
      have hlt : 0 < d v := lt_of_le_of_ne unitInterval.nonneg' (Ne.symm hv1)
      have : v ∈ o ∩ d ⁻¹' Ioo 0 s := ⟨hvo, hlt, hvs⟩
      rw [hne] at this; exact this
    have := interior_maximal hsub ho' hwo'
    rw [hd0 0] at this; exact this
  exact image_closure_subset_closure_image continuous_subtype_val ⟨w, hcl, rfl⟩

/-- **The interval lemma at `0`.** A subcontinuum of `F` meeting `d⁻¹(0)` and a point `y` with
`d(y) > 0` contains `d⁻¹(0)`. -/
theorem layer_zero_subset_of_meets {F : Set M} {d : F → unitInterval}
    (hF : IsMinimalAdmissible F d) {K : Set M} (hKF : K ⊆ F) (hK : Fold.Q78.IsContinuum K)
    (h0 : (K ∩ layer d 0).Nonempty) (y : F) (hyK : (y : M) ∈ K) (hy : 0 < d y) :
    layer d 0 ⊆ K := by
  have hIoo := layerSet_Ioo_subset hF hKF hK h0 ⟨y, hyK, y, rfl, rfl⟩
  exact (layer_zero_subset_closure hF.2.1.1 hF.2.2 hy).trans (closure_minimal hIoo hK.1.isClosed)

/-- A continuum meeting both end layers of `H` contains `H` (hereditary unicoherence and the end
set property). -/
theorem subset_of_meets_ends (hHU : IsHereditarilyUnicoherent (univ : Set M)) {H : Set M}
    {d : H → unitInterval} (hd : IsMinimalAdmissible H d) {B : Set M}
    (hB : Fold.Q78.IsContinuum B) (h0 : (B ∩ layer d 0).Nonempty)
    (h1 : (B ∩ layer d 1).Nonempty) : H ⊆ B := by
  obtain ⟨x, hxB, hx⟩ := h0
  obtain ⟨y, hyB, hy⟩ := h1
  have hHc : Fold.Q78.IsContinuum H := by
    obtain ⟨⟨a, b, hab⟩, -, -⟩ := hd; exact hab.1
  have hHB := isContinuum_inter_of_HU hHU hHc hB ⟨x, img_subset _ hx, hxB⟩
  have := end_sets_aux hd inter_subset_left hHB ⟨x, ⟨img_subset _ hx, hxB⟩, hx⟩
    ⟨y, ⟨img_subset _ hy, hyB⟩, hy⟩
  rw [← this]; exact inter_subset_right

theorem IsExtensionAway.isContinuum {E X₀ F : Set M} (h : IsExtensionAway E X₀ F) :
    Fold.Q78.IsContinuum F := by
  obtain ⟨-, d, ⟨⟨a, b, hab⟩, -, -⟩, -⟩ := h; exact hab.1

theorem IsExtensionAway.subset_extUnion {E X₀ F : Set M} (h : IsExtensionAway E X₀ F) :
    F ⊆ extUnion E X₀ := fun _ hx => ⟨F, h, hx⟩

theorem IsExtensionAway.end_subset {E X₀ F : Set M} (h : IsExtensionAway E X₀ F) : X₀ ⊆ F := by
  obtain ⟨-, d, -, hdX⟩ := h; rw [← hdX]; exact img_subset _

/-- A point of `Cl R` outside a closed set `B` gives a point of some extension outside `B`. -/
theorem exists_mem_ext_not_mem {E X₀ B : Set M} (hB : IsClosed B) {p : M}
    (hp : p ∈ closure (extUnion E X₀)) (hpB : p ∉ B) :
    ∃ F, IsExtensionAway E X₀ F ∧ ∃ r ∈ F, r ∉ B := by
  obtain ⟨r, hrB, F, hF, hrF⟩ := _root_.mem_closure_iff.1 hp Bᶜ hB.isOpen_compl hpB
  exact ⟨F, hF, r, hrF, hrB⟩

/-- `Cl R(X, E)` is a continuum. -/
theorem isContinuum_closure_extUnion [CompactSpace M] {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) : Fold.Q78.IsContinuum (closure (extUnion E (layer k 0))) := by
  obtain ⟨e, he⟩ := layer_nonempty hE.2.1.2.1 0
  have heE : e ∈ E := img_subset _ he
  have hc : IsConnected (extUnion E (layer k 0)) := by
    refine ⟨⟨e, E, ⟨subset_rfl, k, hE, rfl⟩, heE⟩, isPreconnected_sUnion (e : M) _ ?_ ?_⟩
    · intro F hF; exact hF.1 heE
    · intro F hF; exact (IsExtensionAway.isContinuum hF).2.2
  exact ⟨isClosed_closure.isCompact, hc.closure⟩

section Ext

variable [CompactSpace M] [ConnectedSpace M]

/-- Two extensions away from `X` have a common upper bound in `𝓕` (Lemma 4, linear order). -/
theorem ext_upper (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {F₁ F₂ : Set M}
    (h₁ : IsExtensionAway E (layer k 0) F₁) (h₂ : IsExtensionAway E (layer k 0) F₂) :
    ∃ H, IsExtensionAway E (layer k 0) H ∧ F₁ ⊆ H ∧ F₂ ⊆ H := by
  by_cases h : F₁ = F₂
  · subst h; exact ⟨F₁, h₁, subset_rfl, subset_rfl⟩
  rcases hagopian76_lemma4_chain hX hi hE h₁ h₂ h with h | h
  · exact ⟨F₂, h₂, h, subset_rfl⟩
  · exact ⟨F₁, h₁, subset_rfl, h⟩

/-! ### Steps 1–3 -/

omit [CompactSpace M] [ConnectedSpace M] in
/-- **Step 1.** "Since `E` is irreducible and `M` is hereditarily unicoherent, and since `X` does
not have interior relative to `E`, it follows that `B` contains `X`" (after renaming). -/
theorem lemma6_step1 (hHU : IsHereditarilyUnicoherent (univ : Set M)) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {B C : Set M}
    (hB : Fold.Q78.IsContinuum B) (hC : Fold.Q78.IsContinuum C) (hEBC : E ⊆ B ∪ C) :
    layer k 0 ⊆ B ∨ layer k 0 ⊆ C := by
  have hEc : Fold.Q78.IsContinuum E := by
    obtain ⟨⟨a, b, hab⟩, -, -⟩ := hE; exact hab.1
  by_contra hcon
  rw [not_or, not_subset, not_subset] at hcon
  obtain ⟨⟨x, hxX, hxB⟩, ⟨x', hx'X, hx'C⟩⟩ := hcon
  have key : ∀ P : Set M, Fold.Q78.IsContinuum P → ∀ u ∈ layer k 0, u ∈ P →
      ∀ v ∈ layer k 0, v ∉ P → ∀ e : E, (e : M) ∈ P → k e = 0 := by
    intro P hP u hu huP v hv hvP e heP
    by_contra hne
    have hEP := isContinuum_inter_of_HU hHU hEc hP ⟨u, img_subset _ hu, huP⟩
    have := layer_zero_subset_of_meets hE inter_subset_left hEP ⟨u, ⟨img_subset _ hu, huP⟩, hu⟩ e
      ⟨e.2, heP⟩ (lt_of_le_of_ne unitInterval.nonneg' (Ne.symm hne))
    exact hvP (this hv).2
  have hx'B : x' ∈ B := (hEBC (img_subset _ hx'X)).resolve_right hx'C
  have hxC : x ∈ C := (hEBC (img_subset _ hxX)).resolve_left hxB
  obtain ⟨t, ht⟩ := hE.2.1.2.1 1
  rcases hEBC t.2 with htB | htC
  · exact zero_ne_one ((key B hB x' hx'X hx'B x hxX hxB t htB).symm.trans ht)
  · exact zero_ne_one ((key C hC x hxX hxC x' hx'X hx'C t htC).symm.trans ht)

/-- **Step 2.** "The sets `X` and `C` are disjoint." -/
theorem lemma6_step2 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {B C : Set M}
    (hB : Fold.Q78.IsContinuum B) (hC : Fold.Q78.IsContinuum C)
    (hBC : B ∪ C = closure (extUnion E (layer k 0))) (hBne : B ≠ closure (extUnion E (layer k 0)))
    (hCne : C ≠ closure (extUnion E (layer k 0))) (hXB : layer k 0 ⊆ B) :
    Disjoint C (layer k 0) := by
  have hHU := hagopian75_lemma1_hu hX hi
  set R := extUnion E (layer k 0)
  rw [disjoint_left]
  intro xc hxcC hxcX
  obtain ⟨p, hpR, hpB⟩ : ∃ p ∈ closure R, p ∉ B := by
    by_contra h; push_neg at h
    exact hBne (Subset.antisymm (by rw [← hBC]; exact subset_union_left) h)
  obtain ⟨q, hqR, hqC⟩ : ∃ q ∈ closure R, q ∉ C := by
    by_contra h; push_neg at h
    exact hCne (Subset.antisymm (by rw [← hBC]; exact subset_union_right) h)
  obtain ⟨F₁, hF₁, r₁, hr₁, hr₁B⟩ := exists_mem_ext_not_mem hB.1.isClosed hpR hpB
  obtain ⟨F₂, hF₂, r₂, hr₂, hr₂C⟩ := exists_mem_ext_not_mem hC.1.isClosed hqR hqC
  obtain ⟨H, hH, h1, h2⟩ := ext_upper hX hi hE hF₁ hF₂
  have hHR := IsExtensionAway.subset_extUnion hH
  obtain ⟨-, d, hd, hdX⟩ := hH
  obtain ⟨t, ht⟩ := hd.2.1.2.1 1
  have htBC : (t : M) ∈ B ∪ C := by rw [hBC]; exact subset_closure (hHR t.2)
  rcases htBC with htB | htC
  · exact hr₁B (subset_of_meets_ends hHU hd hB ⟨xc, hXB hxcX, by rw [hdX]; exact hxcX⟩
      ⟨t, htB, t, ht, rfl⟩ (h1 hr₁))
  · exact hr₂C (subset_of_meets_ends hHU hd hC ⟨xc, hxcC, by rw [hdX]; exact hxcX⟩
      ⟨t, htC, t, ht, rfl⟩ (h2 hr₂))

/-- **Step 3.** "Let `K` be an element of `𝓕` that meets `C − B`. Note that `B − C` is contained in
`K`." Proved in the form `Cl R − C ⊆ K`. -/
theorem lemma6_step3 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {B C : Set M}
    (hB : Fold.Q78.IsContinuum B) (hC : Fold.Q78.IsContinuum C)
    (hBC : B ∪ C = closure (extUnion E (layer k 0))) (hXB : layer k 0 ⊆ B) {K : Set M}
    (hK : IsExtensionAway E (layer k 0) K) {p : M} (hpK : p ∈ K) (hpC : p ∈ C) (hpB : p ∉ B) :
    closure (extUnion E (layer k 0)) \ C ⊆ K := by
  have hHU := hagopian75_lemma1_hu hX hi
  set R := extUnion E (layer k 0)
  have hKc := IsExtensionAway.isContinuum hK
  have hRC : R \ C ⊆ K := by
    rintro w ⟨⟨Fw, hFw, hwF⟩, hwC⟩
    obtain ⟨H, hH, hKH, hFwH⟩ := ext_upper hX hi hE hK hFw
    have hwH := hFwH hwF
    have hHR := IsExtensionAway.subset_extUnion hH
    obtain ⟨-, dK, hdK, hdKX⟩ := hK
    obtain ⟨-, d, hd, hdX⟩ := hH
    obtain ⟨s, -, hseg, -⟩ :=
      hagopian76_initial_segment hX hi hdK hd hKH (hdX.trans hdKX.symm)
    have hfar : ∀ t : H, d t = 1 → (t : M) ∈ C := by
      intro t ht
      have htBC : (t : M) ∈ B ∪ C := by rw [hBC]; exact subset_closure (hHR t.2)
      refine htBC.resolve_left fun htB => hpB ?_
      obtain ⟨x, hx⟩ := hd.2.1.2.1 0
      have hxB : (x : M) ∈ B := hXB (by rw [← hdX]; exact ⟨x, hx, rfl⟩)
      exact subset_of_meets_ends hHU hd hB ⟨x, hxB, x, hx, rfl⟩ ⟨t, htB, t, ht, rfl⟩ (hKH hpK)
    by_contra hwK
    set w' : H := ⟨w, hwH⟩
    set p' : H := ⟨p, hKH hpK⟩
    have hp's : d p' ≤ s := by
      have : p ∈ layerSet d (Icc 0 s) := by rw [hseg]; exact hpK
      obtain ⟨v, hv, hvp⟩ := this
      have : v = p' := Subtype.ext hvp
      subst this; exact hv.2
    have hw's : s < d w' := lt_of_not_ge fun h =>
      hwK (by rw [← hseg]; exact ⟨w', ⟨unitInterval.nonneg', h⟩, rfl⟩)
    have hp'1 : d p' < 1 := lt_of_le_of_lt hp's (lt_of_lt_of_le hw's unitInterval.le_one')
    obtain ⟨t, ht⟩ := hd.2.1.2.1 1
    have := tail_subset hHU hd hC (hfar t ht) ⟨t, ht, rfl⟩ p' hpC hp'1
    exact hwC (this ⟨w', ⟨lt_of_le_of_lt hp's hw's, unitInterval.le_one'⟩, rfl⟩)
  rintro w ⟨hwR, hwC⟩
  have hw : w ∈ closure (R \ C) := by
    have := hC.1.isClosed.isOpen_compl.inter_closure (show w ∈ Cᶜ ∩ closure R from ⟨hwC, hwR⟩)
    exact closure_mono (fun x (hx : x ∈ Cᶜ ∩ R) => (⟨hx.2, hx.1⟩ : x ∈ R \ C)) this
  exact closure_minimal hRC hKc.1.isClosed hw

/-! ### Steps 4–5 -/

/-- **Steps 4 and 5.** Under the hypothesis `Cl R(X, E) = B ∪ C` with `B`, `C` proper subcontinua
and `X ⊆ B`: a contradiction. -/
theorem lemma6_main (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {B C : Set M}
    (hB : Fold.Q78.IsContinuum B) (hC : Fold.Q78.IsContinuum C)
    (hBC : B ∪ C = closure (extUnion E (layer k 0))) (hBne : B ≠ closure (extUnion E (layer k 0)))
    (hCne : C ≠ closure (extUnion E (layer k 0))) (hXB : layer k 0 ⊆ B) : False := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  have hCX := lemma6_step2 hX hi hE hB hC hBC hBne hCne hXB
  -- step 3: `K`
  obtain ⟨p, hpR, hpB⟩ : ∃ p ∈ closure (extUnion E (layer k 0)), p ∉ B := by
    by_contra h; push_neg at h
    exact hBne (Subset.antisymm (by rw [← hBC]; exact subset_union_left) h)
  obtain ⟨K, hK, p', hp'K, hp'B⟩ := exists_mem_ext_not_mem hB.1.isClosed hpR hpB
  have hp'C : p' ∈ C := by
    have : p' ∈ B ∪ C := by rw [hBC]; exact subset_closure (IsExtensionAway.subset_extUnion hK hp'K)
    exact this.resolve_left hp'B
  have hstep3 := lemma6_step3 hX hi hE hB hC hBC hXB hK hp'K hp'C hp'B
  -- absorption: `C ⊆ R`
  have hCR : C ⊆ extUnion E (layer k 0) := subset_extUnion_of_meets hX hHU hAT hK hC hCX ⟨p', hp'C, hp'K⟩
  -- step 4: the sequence, the far ends, the cluster point `c`
  obtain ⟨Fs, hmono, hFs, hRU⟩ := hagopian76_lemma4_seq hX hi hE
  have hnomax := (hagopian76_lemma4 hX hi hE).2
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, K ⊆ Fs i₀ := by
    by_contra h; push_neg at h
    have hRK : extUnion E (layer k 0) ⊆ K := by
      rw [hRU]; refine iUnion_subset fun i => ?_
      by_cases heq : Fs i = K
      · exact heq.le
      rcases hagopian76_lemma4_chain hX hi hE (hFs i) hK heq with h' | h'
      · exact h'
      · exact absurd h' (h i)
    obtain ⟨H, hH, hKH⟩ := hnomax K hK
    exact hKH.2 ((IsExtensionAway.subset_extUnion hH).trans hRK)
  have hKi : ∀ i, i₀ ≤ i → K ⊆ Fs i := fun i hi => hi₀.trans (hmono.monotone hi)
  choose d hd hdX using fun i => (hFs i).2
  choose z hz using fun i => (hd i).2.1.2.1 1
  have hzC : ∀ i, i₀ ≤ i → ((z i : M)) ∈ C := by
    intro i hi
    have hzBC : (z i : M) ∈ B ∪ C := by
      rw [hBC]; exact subset_closure (IsExtensionAway.subset_extUnion (hFs i) (z i).2)
    refine hzBC.resolve_left fun hzB => hp'B ?_
    obtain ⟨x, hx⟩ := (hd i).2.1.2.1 0
    have hxB : (x : M) ∈ B := hXB (by rw [← hdX i]; exact ⟨x, hx, rfl⟩)
    exact subset_of_meets_ends hHU (hd i) hB ⟨x, hxB, x, hx, rfl⟩ ⟨z i, hzB, z i, hz i, rfl⟩
      (hKi i hi hp'K)
  obtain ⟨c, hcC, φ, hφ, hlim⟩ :=
    hC.1.tendsto_subseq (x := fun n => ((z (n + i₀) : M))) (fun n => hzC _ (by omega))
  have hcR : c ∈ extUnion E (layer k 0) := hCR hcC
  -- step 5
  rw [hRU] at hcR
  obtain ⟨j, hcj⟩ := mem_iUnion.1 hcR
  set ℓ := max j i₀
  set L := Fs ℓ with hLdef
  have hcL : c ∈ L := hmono.monotone (le_max_left _ _) hcj
  have hKL : K ⊆ L := hKi ℓ (le_max_right _ _)
  have hLc := IsExtensionAway.isContinuum (hFs ℓ)
  have hXL : layer k 0 ⊆ L := IsExtensionAway.end_subset (hFs ℓ)
  obtain ⟨H, hH, hLH⟩ := hnomax L (hFs ℓ)
  obtain ⟨w, hwH, hwL⟩ := not_subset.1 hLH.2
  have hwR : w ∈ ⋃ i, Fs i := hRU ▸ IsExtensionAway.subset_extUnion hH hwH
  obtain ⟨j', hwj'⟩ := mem_iUnion.1 hwR
  have hEc : Fold.Q78.IsContinuum E := by
    obtain ⟨⟨a, b, hab⟩, -, -⟩ := hE; exact hab.1
  have hXc : IsCompact (layer k 0) := (isContinuum_layer hEc.1 hE.2.1 0).1
  obtain ⟨ε, hε, hεsep⟩ := exists_pos_le_dist hXc hC.1.isClosed hCX.symm
  obtain ⟨δ₀, hδ₀, hδ₀sep⟩ := exists_pos_le_dist (isCompact_singleton (x := w)) hLc.1.isClosed
    (disjoint_singleton_left.2 hwL)
  have hδ : 0 < min ε δ₀ := lt_min hε hδ₀
  obtain ⟨hO, hcO⟩ := hagopian76_lemma2 hX hδ c
  have hev := hlim (hO.mem_nhds hcO)
  rw [Filter.mem_map, Filter.mem_atTop_sets] at hev
  obtain ⟨N, hN⟩ := hev
  set n := max N (max ℓ j')
  have hni : n ≤ φ n := hφ.id_le n
  obtain ⟨f, hfc, hfδ⟩ := hN n (le_max_left _ _)
  set i := φ n + i₀
  have hLi : L ⊆ Fs i := hmono.monotone (by omega)
  have hwi : w ∈ Fs i := hmono.monotone (by omega) hwj'
  obtain ⟨-, dL, hdL, hdLX⟩ := hFs ℓ
  obtain ⟨s, -, hseg, -⟩ :=
    hagopian76_initial_segment hX hi hdL (hd i) hLi ((hdX i).trans hdLX.symm)
  rw [← hLdef] at hseg
  have hfLc := isContinuum_homeo_image f hLc
  have hzfL : (z i : M) ∈ f '' L := ⟨c, hcL, hfc⟩
  -- `L ∩ f[L] = ∅`
  have hdisj : Disjoint L (f '' L) := by
    rw [disjoint_left]
    intro y hyL hyf
    set y' : Fs i := ⟨y, hLi hyL⟩
    have hy's : d i y' ≤ s := by
      have : y ∈ layerSet (d i) (Icc 0 s) := by rw [hseg]; exact hyL
      obtain ⟨v, hv, hvy⟩ := this
      have : v = y' := Subtype.ext hvy
      subst this; exact hv.2
    have hw's : s < d i ⟨w, hwi⟩ := lt_of_not_ge fun h =>
      hwL (by rw [← hseg]; exact ⟨⟨w, hwi⟩, ⟨unitInterval.nonneg', h⟩, rfl⟩)
    have hsub := tail_subset hHU (hd i) hfLc hzfL ⟨z i, hz i, rfl⟩ y' hyf
      (lt_of_le_of_lt hy's (lt_of_lt_of_le hw's unitInterval.le_one'))
    obtain ⟨l, hlL, hlw⟩ := hsub ⟨⟨w, hwi⟩, ⟨lt_of_le_of_lt hy's hw's, unitInterval.le_one'⟩, rfl⟩
    have h1 := hfδ l
    have h2 := hδ₀sep w rfl l hlL
    rw [hlw, dist_comm] at h1
    linarith [min_le_right ε δ₀]
  -- `f[L] ⊆ R(X, E)`
  have hfLR : f '' L ⊆ extUnion E (layer k 0) := subset_extUnion_of_meets hX hHU hAT (hFs i) hfLc
    (hdisj.mono_left hXL).symm ⟨z i, hzfL, (z i).2⟩
  -- the contradiction
  obtain ⟨x, hx⟩ := layer_nonempty hE.2.1.2.1 0
  have hfx : f x ∈ f '' L := ⟨x, hXL hx, rfl⟩
  have hfxC : f x ∉ C := fun h => by
    have h1 := hεsep x hx (f x) h
    have h2 := hfδ x
    linarith [min_le_left ε δ₀]
  have hfxK : f x ∈ K := hstep3 ⟨subset_closure (hfLR hfx), hfxC⟩
  exact disjoint_left.1 hdisj (hKL hfxK) hfx

/-- **Lemma 6, first part.** `Cl R(X, E)` is indecomposable. -/
theorem lemma6_X_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    Fold.Q78.IsIndecomposable (closure (extUnion E (layer k 0))) := by
  have hHU := hagopian75_lemma1_hu hX hi
  refine ⟨isContinuum_closure_extUnion hE, fun A B hA hB hAR hBR hAB => ?_⟩
  by_contra hne
  push_neg at hne
  have hER : E ⊆ A ∪ B := by
    rw [hAB]; exact (IsExtensionAway.subset_extUnion ⟨subset_rfl, k, hE, rfl⟩).trans subset_closure
  rcases lemma6_step1 hHU hE hA hB hER with h | h
  · exact lemma6_main hX hi hE hA hB hAB hne.1 hne.2 h
  · exact lemma6_main hX hi hE hB hA (by rw [union_comm]; exact hAB) hne.2 hne.1 h

end Ext

end Lemma6

end HPC.Hagopian
