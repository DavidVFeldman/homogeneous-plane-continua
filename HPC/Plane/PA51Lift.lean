import HPC.Plane.PA51Pre

/-!
# Batch 88: passing between a compact continuum `M ⊆ X` and the compact space `M`

* `subChain`: a chain of `X` covering a preconnected set `M`, every link meeting `M`, restricts to
  a chain of the subspace `M` (consecutive links still meet inside `M`, by connectedness).
* hereditary indecomposability, chainability and composants pass from `M ⊆ X` to the space `M`.
* `ext M r U`: an open set of `X` extending a relatively open `U ⊆ M`, inside the `r`-neighbourhood
  of `M`: the points nearer to `U` than to `M \ U`. It meets `M` in `U`, preserves inclusion and
  disjointness, and (for small `r`) closure-inclusion.
* `lift_description`: a description of the space `M` from `p` to `q` with continuum all of `M`
  lifts to a description in `X` from `p` to `q` with continuum `M`.
-/

namespace HPC.Plane

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

namespace PA51

/-! ### Restricting chains to a subspace -/

/-- Consecutive links of a chain covering a preconnected set `M`, all links meeting `M`, meet
inside `M`. -/
theorem inter_inter_nonempty {n : ℕ} (C : Chain X n) {M : Set X} (hconn : IsPreconnected M)
    (hcov : M ⊆ C.union) (hmeet : ∀ i, (C.link i ∩ M).Nonempty) (i j : Fin n)
    (hij : j.val = i.val + 1) : (C.link i ∩ C.link j ∩ M).Nonempty := by
  have hsub : M ⊆ lowU C (i.val + 1) ∪ highU C i.val := by
    intro x hx
    obtain ⟨l, hl⟩ := mem_iUnion.mp (hcov hx)
    rcases Nat.lt_or_ge l.val (i.val + 1) with h | h
    · exact Or.inl (mem_iUnion₂.mpr ⟨l, h, hl⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨l, by omega, hl⟩)
  obtain ⟨a, haC, haM⟩ := hmeet i
  obtain ⟨b, hbC, hbM⟩ := hmeet j
  obtain ⟨z, hzM, hzu, hzv⟩ := hconn _ _ (isOpen_lowU C _) (isOpen_highU C _) hsub
    ⟨a, haM, mem_iUnion₂.mpr ⟨i, by omega, haC⟩⟩ ⟨b, hbM, mem_iUnion₂.mpr ⟨j, by omega, hbC⟩⟩
  obtain ⟨l, hl, hzl⟩ := mem_iUnion₂.mp hzu
  obtain ⟨l', hl', hzl'⟩ := mem_iUnion₂.mp hzv
  have := (C.adjacent_iff l l').mp ⟨z, hzl, hzl'⟩
  have e1 : l = i := Fin.ext (by omega)
  have e2 : l' = j := Fin.ext (by omega)
  subst e1 e2
  exact ⟨z, ⟨hzl, hzl'⟩, hzM⟩

/-- The restriction of a chain covering a preconnected set `M`, every link meeting `M`, to the
subspace `M`. -/
def subChain {n : ℕ} (C : Chain X n) (M : Set X) (hconn : IsPreconnected M)
    (hcov : M ⊆ C.union) (hmeet : ∀ i, (C.link i ∩ M).Nonempty) : Chain M n where
  link i := Subtype.val ⁻¹' C.link i
  isOpen i := (C.isOpen i).preimage continuous_subtype_val
  adjacent i j := by
    constructor
    · rintro ⟨z, h1, h2⟩
      exact (C.adjacent i j).mp ⟨z.1, h1, h2⟩
    · intro h
      have h' : i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1 := by omega
      rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
      · obtain ⟨z, ⟨h1, h2⟩, hz⟩ := inter_inter_nonempty C hconn hcov hmeet i j (by omega)
        exact ⟨⟨z, hz⟩, h1, h2⟩
      · have : i = j := Fin.ext heq
        subst this
        obtain ⟨z, h1, hz⟩ := hmeet i
        exact ⟨⟨z, hz⟩, h1, h1⟩
      · obtain ⟨z, ⟨h1, h2⟩, hz⟩ := inter_inter_nonempty C hconn hcov hmeet j i (by omega)
        exact ⟨⟨z, hz⟩, h2, h1⟩

theorem isBounded_preimage_val {M S : Set X} (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (Subtype.val ⁻¹' S : Set M) := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hS
  exact Metric.isBounded_iff.mpr ⟨C, fun a ha b hb => hC ha hb⟩

theorem diam_preimage_val_le {M S : Set X} (hS : Bornology.IsBounded S) :
    diam (Subtype.val ⁻¹' S : Set M) ≤ diam S := by
  rw [← isometry_subtype_coe.diam_image]
  exact diam_mono (image_preimage_subset _ _) hS

theorem isBounded_image_val {M : Set X} {S : Set M} (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (Subtype.val '' S) := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hS
  refine Metric.isBounded_iff.mpr ⟨C, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact hC ha hb

theorem isContinuum_image_val {M : Set X} {K : Set M} (hK : Fold.Q78.IsContinuum K) :
    Fold.Q78.IsContinuum (Subtype.val '' K) :=
  ⟨hK.1.image continuous_subtype_val, hK.2.image _ continuous_subtype_val.continuousOn⟩

/-- Hereditary indecomposability passes to the subspace. -/
theorem hI_sub {M : Set X} (hM : IsHereditarilyIndecomposable M) :
    ∀ K : Set M, Fold.Q78.IsContinuum K → Fold.Q78.IsIndecomposable K := by
  intro K hK
  refine ⟨hK, fun A B hA hB hAK hBK hAB => ?_⟩
  have hinj : Function.Injective (fun S : Set M => Subtype.val '' S) :=
    Set.image_injective.mpr Subtype.val_injective
  have hKM : Subtype.val '' K ⊆ M := by rintro _ ⟨z, -, rfl⟩; exact z.2
  have := (hM _ hKM (isContinuum_image_val hK)).2 _ _
    (isContinuum_image_val hA) (isContinuum_image_val hB) (image_mono hAK) (image_mono hBK)
    (by rw [← image_union, hAB])
  rcases this with h | h
  · exact Or.inl (hinj h)
  · exact Or.inr (hinj h)

/-- Chainability passes to the subspace. -/
theorem snake_sub {M : Set X} (hM : IsSnakeLike M) (hne : M.Nonempty) :
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain M n), IsEpsChain D ε ∧ univ ⊆ D.union := by
  intro ε hε
  obtain ⟨n, C, hCε, hcov, hmeet⟩ := exists_cover_meeting hM.1.2.isPreconnected hne hM.2 hε
  refine ⟨n, subChain C M hM.1.2.isPreconnected hcov hmeet, fun i => ?_, fun z _ => ?_⟩
  · exact ⟨isBounded_preimage_val (hCε i).1,
      (diam_preimage_val_le (hCε i).1).trans_lt (hCε i).2⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov z.2)
    exact mem_iUnion.mpr ⟨i, hi⟩

/-- Composants: a point outside the composant of `p` in `M` is outside the composant of `p` in
the space `M`. -/
theorem not_mem_composant_sub {M : Set X} {p q : X} (hp : p ∈ M) (hq : q ∈ M)
    (hpq : q ∉ composant M p) :
    (⟨q, hq⟩ : M) ∉ composant (univ : Set M) ⟨p, hp⟩ := by
  intro h
  obtain ⟨K, ⟨hK, -, hKne, hpK⟩, hqK⟩ := mem_sUnion.mp h
  apply hpq
  have hKM : Subtype.val '' K ⊆ M := by rintro _ ⟨z, -, rfl⟩; exact z.2
  refine mem_sUnion.mpr ⟨Subtype.val '' K, ⟨isContinuum_image_val hK,
    hKM, ?_, ⟨_, hpK, rfl⟩⟩, ⟨_, hqK, rfl⟩⟩
  intro heq
  apply hKne
  refine eq_univ_of_forall fun z => ?_
  have : (z : X) ∈ Subtype.val '' K := by rw [heq]; exact z.2
  obtain ⟨w, hw, hwz⟩ := this
  exact Subtype.val_injective hwz ▸ hw

/-- Points in different composants of a nontrivial set are distinct. -/
theorem ne_of_not_mem_composant {M : Set X} (hnd : M.Nontrivial) {p q : X} (hp : p ∈ M)
    (hpq : q ∉ composant M p) : p ≠ q := by
  rintro rfl
  apply hpq
  refine mem_sUnion.mpr ⟨{p}, ⟨⟨isCompact_singleton, isConnected_singleton⟩,
    singleton_subset_iff.mpr hp, ?_, rfl⟩, rfl⟩
  intro h
  obtain ⟨a, ha, b, hb, hab⟩ := hnd
  rw [← h] at ha hb
  exact hab ((mem_singleton_iff.mp ha).trans (mem_singleton_iff.mp hb).symm)

/-- **The description of the subspace** (Bing 1951, Theorem 1, body of the proof). -/
theorem exists_description_sub {M : Set X} (hMs : IsSnakeLike M)
    (hMh : IsHereditarilyIndecomposable M) (hnd : M.Nontrivial) {p q : X} (hp : p ∈ M)
    (hq : q ∈ M) (hpq : q ∉ composant M p) :
    ∃ Δ : Description M ⟨p, hp⟩ ⟨q, hq⟩, Δ.M = univ := by
  haveI : CompactSpace M := isCompact_iff_compactSpace.mp hMs.1.1
  refine exists_description_univ (hI_sub hMh) (snake_sub hMs ⟨p, hp⟩) ?_
    (not_mem_composant_sub hp hq hpq)
  intro h
  exact ne_of_not_mem_composant hnd hp hpq (congrArg Subtype.val h)

/-! ### Extending relatively open sets -/

/-- The extension of a relatively open subset `U` of `M` to an open subset of `X` inside the
`r`-neighbourhood of `M`. -/
def ext (M : Set X) (r : ℝ) (U : Set M) : Set X :=
  {x | infEDist x (Subtype.val '' U) < infEDist x (M \ Subtype.val '' U)} ∩ thickening r M

theorem isOpen_ext (M : Set X) (r : ℝ) (U : Set M) : IsOpen (ext M r U) :=
  (isOpen_lt continuous_infEDist continuous_infEDist).inter isOpen_thickening

theorem isClosed_diff_image {M : Set X} (hM : IsClosed M) {U : Set M} (hU : IsOpen U) :
    IsClosed (M \ Subtype.val '' U) := by
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hU
  have : M \ Subtype.val '' (Subtype.val ⁻¹' O : Set M) = M ∩ Oᶜ := by
    ext x
    simp only [mem_diff, mem_image, mem_preimage, mem_inter_iff, mem_compl_iff]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, fun hxO => h ⟨⟨x, hx⟩, hxO, rfl⟩⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, fun ⟨z, hz, hzx⟩ => h (hzx ▸ hz)⟩
  rw [this]
  exact hM.inter hO.isClosed_compl

/-- `ext M r U` meets `M` in `U`. -/
theorem mem_ext_iff {M : Set X} (hM : IsClosed M) {U : Set M} (hU : IsOpen U) {r : ℝ}
    (hr : 0 < r) (z : M) : (z : X) ∈ ext M r U ↔ z ∈ U := by
  constructor
  · rintro ⟨h, -⟩
    by_contra hz
    have : (z : X) ∈ M \ Subtype.val '' U := by
      refine ⟨z.2, ?_⟩
      rintro ⟨w, hw, hwz⟩
      exact hz (Subtype.val_injective hwz ▸ hw)
    rw [mem_setOf_eq, infEDist_zero_of_mem this] at h
    exact (ENNReal.not_lt_zero h)
  · intro hz
    refine ⟨?_, self_subset_thickening hr M z.2⟩
    have hzU : (z : X) ∈ Subtype.val '' U := ⟨z, hz, rfl⟩
    rw [mem_setOf_eq, infEDist_zero_of_mem hzU]
    have hcl := isClosed_diff_image hM hU
    have hnot : (z : X) ∉ M \ Subtype.val '' U := fun h => h.2 ⟨z, hz, rfl⟩
    rw [mem_iff_infEDist_zero_of_closed hcl] at hnot
    exact pos_iff_ne_zero.mpr hnot

/-- Disjoint relatively open sets have disjoint extensions. -/
theorem ext_disjoint (M : Set X) {U V : Set M} (hUV : Disjoint U V) (r r' : ℝ) :
    Disjoint (ext M r U) (ext M r' V) := by
  rw [Set.disjoint_left]
  rintro x ⟨h1, -⟩ ⟨h2, -⟩
  simp only [mem_setOf_eq] at h1 h2
  have e1 : Subtype.val '' V ⊆ M \ Subtype.val '' U := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    rintro ⟨w, hw, hwz⟩
    exact Set.disjoint_left.mp hUV (Subtype.val_injective hwz ▸ hw) hz
  have e2 : Subtype.val '' U ⊆ M \ Subtype.val '' V := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    rintro ⟨w, hw, hwz⟩
    exact Set.disjoint_left.mp hUV hz (Subtype.val_injective hwz ▸ hw)
  have a1 := infEDist_anti (x := x) e1
  have a2 := infEDist_anti (x := x) e2
  exact lt_irrefl _ (((h1.trans_le a1).trans h2).trans_le a2)

/-- Extensions are monotone. -/
theorem ext_mono (M : Set X) {U V : Set M} (hUV : U ⊆ V) {r r' : ℝ} (hrr : r ≤ r') :
    ext M r U ⊆ ext M r' V := by
  rintro x ⟨h, ht⟩
  refine ⟨?_, thickening_mono hrr M ht⟩
  simp only [mem_setOf_eq] at h ⊢
  calc infEDist x (Subtype.val '' V) ≤ infEDist x (Subtype.val '' U) :=
        infEDist_anti (image_mono hUV)
    _ < infEDist x (M \ Subtype.val '' U) := h
    _ ≤ infEDist x (M \ Subtype.val '' V) := infEDist_anti (diff_subset_diff_right (image_mono hUV))

/-- An extension lies in the `r`-neighbourhood of the set extended. -/
theorem ext_subset_thickening (M : Set X) (r : ℝ) (U : Set M) :
    ext M r U ⊆ thickening r (Subtype.val '' U) := by
  rintro x ⟨h, ht⟩
  rw [mem_thickening_iff_infEDist_lt] at ht ⊢
  have hM : M = Subtype.val '' U ∪ (M \ Subtype.val '' U) := by
    refine (union_diff_cancel ?_).symm
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  rw [hM, infEDist_union, min_eq_left h.le] at ht
  exact ht

theorem isBounded_ext (M : Set X) (r : ℝ) {U : Set M} (hU : Bornology.IsBounded U) :
    Bornology.IsBounded (ext M r U) :=
  (isBounded_image_val hU).thickening.subset (ext_subset_thickening M r U)

theorem diam_ext_le (M : Set X) {r : ℝ} (hr : 0 ≤ r) {U : Set M} (hU : Bornology.IsBounded U) :
    diam (ext M r U) ≤ diam U + 2 * r := by
  refine (diam_mono (ext_subset_thickening M r U) (isBounded_image_val hU).thickening).trans ?_
  refine (diam_thickening_le _ hr).trans ?_
  rw [isometry_subtype_coe.diam_image]

/-- **Closures.** If the closure of `U` lies in `V`, then for small `r` the closure of the
extension of `U` lies in the extension of `V` (with any larger radius). -/
theorem exists_closure_ext_subset {M : Set X} (hM : IsCompact M) {U V : Set M}
    (hV : IsOpen V) (hUV : closure U ⊆ V) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r, 0 < r ∧ r < ρ ∧ closure (ext M r U) ⊆ ext M ρ V := by
  set U' : Set X := Subtype.val '' U
  set V' : Set X := Subtype.val '' V
  set K : Set X := Subtype.val '' closure U
  have hKc : IsCompact K := by
    haveI : CompactSpace M := isCompact_iff_compactSpace.mp hM
    exact isClosed_closure.isCompact.image continuous_subtype_val
  have hUK : U' ⊆ K := image_mono subset_closure
  have hKV : K ⊆ V' := image_mono hUV
  have hdisj : Disjoint K (M \ V') := by
    rw [Set.disjoint_left]
    intro x hxK hx
    exact hx.2 (hKV hxK)
  obtain ⟨δ, hδ, hδd⟩ := hdisj.exists_thickenings hKc (isClosed_diff_image hM.isClosed hV)
  refine ⟨min δ ρ / 2, by positivity, by linarith [min_le_right δ ρ], ?_⟩
  intro x hx
  have hx1 : x ∈ cthickening (min δ ρ / 2) U' :=
    closure_thickening_subset_cthickening _ _ (closure_mono (ext_subset_thickening M _ U) hx)
  rw [mem_cthickening_iff] at hx1
  have hmin : 0 < min δ ρ := lt_min hδ hρ
  have hlt : ∀ t : ℝ, min δ ρ / 2 < t → infEDist x U' < ENNReal.ofReal t := by
    intro t ht
    have h0 : 0 < t := lt_of_le_of_lt (by positivity) ht
    exact hx1.trans_lt ((ENNReal.ofReal_lt_ofReal_iff h0).mpr ht)
  have hxδ : infEDist x U' < ENNReal.ofReal δ :=
    hlt δ (by linarith [min_le_left δ ρ, show 0 < min δ ρ from lt_min hδ hρ])
  have hfar : ENNReal.ofReal δ ≤ infEDist x (M \ V') := by
    by_contra hcon
    push_neg at hcon
    have h1 : x ∈ thickening δ (M \ V') := mem_thickening_iff_infEDist_lt.mpr hcon
    have h2 : x ∈ thickening δ K :=
      mem_thickening_iff_infEDist_lt.mpr ((infEDist_anti hUK).trans_lt hxδ)
    exact Set.disjoint_left.mp hδd h2 h1
  refine ⟨?_, ?_⟩
  · show infEDist x V' < infEDist x (M \ V')
    exact ((infEDist_anti (hUK.trans hKV)).trans_lt hxδ).trans_le hfar
  · rw [mem_thickening_iff_infEDist_lt]
    have hUM : U' ⊆ M := by rintro _ ⟨z, -, rfl⟩; exact z.2
    exact (infEDist_anti hUM).trans_lt
      (hlt ρ (by linarith [min_le_right δ ρ, show 0 < min δ ρ from lt_min hδ hρ]))

/-- The lift of a chain of the subspace `M`. -/
def liftChain {M : Set X} (hM : IsClosed M) {n : ℕ} (C : Chain M n) (r : ℝ) (hr : 0 < r) :
    Chain X n where
  link t := ext M r (C.link t)
  isOpen t := isOpen_ext M r _
  adjacent i j := by
    rw [← C.adjacent i j]
    constructor
    · intro h
      by_contra hne
      have hd : Disjoint (C.link i) (C.link j) :=
        Set.disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne)
      obtain ⟨x, hx1, hx2⟩ := h
      exact Set.disjoint_left.mp (ext_disjoint M hd r r) hx1 hx2
    · rintro ⟨z, h1, h2⟩
      exact ⟨z, (mem_ext_iff hM (C.isOpen i) hr z).mpr h1, (mem_ext_iff hM (C.isOpen j) hr z).mpr h2⟩

theorem exists_pos_le_all {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ r, 0 < r ∧ ∀ i, r ≤ f i := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact ⟨1, one_pos, fun i => i.elim0⟩
  · obtain ⟨i₀, -, hi₀⟩ := (Finset.univ : Finset (Fin n)).exists_min_image f
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    exact ⟨f i₀, hf i₀, fun i => hi₀ i (Finset.mem_univ _)⟩

/-- **Lifting a description of the subspace.** -/
theorem lift_description {M : Set X} (hM : IsCompact M) {p q : X} (hp : p ∈ M) (hq : q ∈ M)
    (Δ' : Description M ⟨p, hp⟩ ⟨q, hq⟩) (hΔ' : Δ'.M = univ) :
    ∃ Δ : Description X p q, Δ.M = M := by
  classical
  have hMc := hM.isClosed
  -- the radii
  have hstep : ∀ (i : ℕ) (ρ : {ρ : ℝ // 0 < ρ}), ∃ r : {r : ℝ // 0 < r}, r.1 < ρ.1 ∧
      r.1 ≤ 1 / ((i : ℝ) + 2) ∧ ∀ t : Fin (Δ'.n (i + 1)), ∃ s,
        closure (ext M r.1 ((Δ'.D (i + 1)).link t)) ⊆ ext M ρ.1 ((Δ'.D i).link s) := by
    intro i ρ
    choose s hs using Δ'.closure_subset i
    choose r hr0 hrρ hrcl using fun t => exists_closure_ext_subset hM ((Δ'.D i).isOpen (s t))
      (hs t) ρ.2
    obtain ⟨r₀, hr₀, hr₀le⟩ := exists_pos_le_all r hr0
    set r₁ := min r₀ (1 / ((i : ℝ) + 2))
    have hr₁ : 0 < r₁ := lt_min hr₀ (by positivity)
    refine ⟨⟨r₁, hr₁⟩, ?_, min_le_right _ _, fun t => ⟨s t, ?_⟩⟩
    · show r₁ < ρ.1
      have t₀ : Fin (Δ'.n (i + 1)) := ⟨0, (Δ'.isFrom (i + 1)).1⟩
      exact (min_le_left _ _).trans_lt ((hr₀le t₀).trans_lt (hrρ t₀))
    · exact (closure_mono (ext_mono M subset_rfl ((min_le_left _ _).trans (hr₀le t)))).trans
        (hrcl t)
  choose R hRlt hRle hRcl using hstep
  let rr : ℕ → {ρ : ℝ // 0 < ρ} := fun i => Nat.rec ⟨1, one_pos⟩ (fun i ρ => R i ρ) i
  have hrrs : ∀ i, rr (i + 1) = R i (rr i) := fun i => rfl
  have hrr0 : (rr 0).1 = 1 := rfl
  have hrr_le : ∀ i, (rr i).1 ≤ 1 / ((i : ℝ) + 1) := by
    intro i
    cases i with
    | zero => simp [hrr0]
    | succ i =>
      rw [hrrs]
      refine (hRle i (rr i)).trans (le_of_eq ?_)
      push_cast; ring
  have hrr_anti : ∀ i, (rr (i + 1)).1 ≤ (rr i).1 := fun i => by rw [hrrs]; exact (hRlt i _).le
  set r : ℕ → ℝ := fun i => (rr i).1 with hr
  have hrpos : ∀ i, 0 < r i := fun i => (rr i).2
  have hrt : Tendsto r atTop (𝓝 0) :=
    squeeze_zero (fun i => (hrpos i).le) hrr_le tendsto_one_div_add_atTop_nhds_zero_nat
  have hmem : ∀ i (t : Fin (Δ'.n i)) (z : M), (z : X) ∈ ext M (r i) ((Δ'.D i).link t) ↔
      z ∈ (Δ'.D i).link t := fun i t z => mem_ext_iff hMc ((Δ'.D i).isOpen t) (hrpos i) z
  refine ⟨{
    n := Δ'.n
    D := fun i => liftChain hMc (Δ'.D i) (r i) (hrpos i)
    isFrom := fun i => ?_
    crooked := fun i => ?_
    closure_subset := fun i t => ?_
    ε := fun i => Δ'.ε i + 2 * r i
    ε_pos := fun i => by have := Δ'.ε_pos i; have := hrpos i; positivity
    ε_tendsto := by simpa using Δ'.ε_tendsto.add (hrt.const_mul 2)
    bdd := fun i t => isBounded_ext M _ (Δ'.bdd i t)
    diam_le := fun i t => by
      refine (diam_ext_le M (hrpos i).le (Δ'.bdd i t)).trans ?_
      linarith [Δ'.diam_le i t] }, ?_⟩
  · obtain ⟨hn, hP, hQ, hPu, hQu⟩ := Δ'.isFrom i
    exact ⟨hn, (hmem i _ ⟨p, hp⟩).mpr hP, (hmem i _ ⟨q, hq⟩).mpr hQ,
      fun j hj => hPu j ((hmem i j ⟨p, hp⟩).mp hj), fun j hj => hQu j ((hmem i j ⟨q, hq⟩).mp hj)⟩
  · obtain ⟨href, hcr⟩ := Δ'.crooked i
    have hmeet : ∀ (a : Fin (Δ'.n (i + 1))) (h : Fin (Δ'.n i)),
        (ext M (r (i + 1)) ((Δ'.D (i + 1)).link a) ∩ ext M (r i) ((Δ'.D i).link h)).Nonempty →
        ((Δ'.D (i + 1)).link a ∩ (Δ'.D i).link h).Nonempty := by
      intro a h hne
      by_contra hcon
      exact Set.disjoint_iff_inter_eq_empty.mp (ext_disjoint M
        (Set.disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hcon)) _ _)
        |> fun he => (nonempty_iff_ne_empty.mp hne) he
    refine ⟨fun t => ?_, fun h k hk a b ha hb => ?_⟩
    · obtain ⟨s, hs⟩ := href t
      exact ⟨s, ext_mono M hs (hrr_anti i)⟩
    · obtain ⟨u, v, hb', hu, hv⟩ := hcr h k hk a b (hmeet a h ha) (hmeet b k hb)
      exact ⟨u, v, hb', ext_mono M hu (hrr_anti i), ext_mono M hv (hrr_anti i)⟩
  · show ∃ s, closure (ext M (r (i + 1)) ((Δ'.D (i + 1)).link t)) ⊆ ext M (r i) ((Δ'.D i).link s)
    have : r (i + 1) = (R i (rr i)).1 := by simp only [hr, hrrs]
    rw [this]
    exact hRcl i (rr i) t
  · show (⋂ i, (liftChain hMc (Δ'.D i) (r i) (hrpos i)).union) = M
    refine Subset.antisymm ?_ ?_
    · intro x hx
      rw [mem_iInter] at hx
      rw [← hMc.closure_eq, mem_closure_iff_infEDist_zero]
      refine le_antisymm ?_ (zero_le _)
      refine ENNReal.le_of_forall_pos_le_add fun e he _ => ?_
      obtain ⟨i, hi⟩ := (hrt.eventually (gt_mem_nhds (show (0 : ℝ) < e by exact_mod_cast he))).exists
      obtain ⟨t, ht⟩ := mem_iUnion.mp (hx i)
      have := mem_thickening_iff_infEDist_lt.mp ht.2
      rw [zero_add]
      refine this.le.trans ?_
      rw [ENNReal.ofReal_le_iff_le_toReal (by simp)]
      simpa using hi.le
    · intro x hxM
      refine mem_iInter.mpr fun i => ?_
      have hz : (⟨x, hxM⟩ : M) ∈ Δ'.M := hΔ' ▸ mem_univ _
      obtain ⟨t, ht⟩ := mem_iUnion.mp (Δ'.M_subset_union i hz)
      exact mem_iUnion.mpr ⟨t, (hmem i t ⟨x, hxM⟩).mpr ht⟩

end PA51

end HPC.Plane
