import HPC.Hagopian.H76Lemma3

/-!
# Batch 156, item D: Lemma 4 of Hagopian 1976, first paragraph

`E ⊆ F`, both with minimal admissible maps `k`, `d`, and `d⁻¹(0) = k⁻¹(0)`.

* `s` is the largest value of `d` on `E`; `s > 0` since `E ⊄ k⁻¹(0)`. Every layer `d⁻¹(r)`, `r < s`,
  lies in `E` (`r = 0`: it is `k⁻¹(0)`; `0 < r < s`: interval lemma in `F`), and `E ⊆ d⁻¹[[0, s]]`.
* **Each layer of `E` lies in a layer of `F`.** `k⁻¹(t)` is a subcontinuum of `F`; if `d` took two
  values `α < β` on it, it would contain `d⁻¹(α, β)` (interval lemma), an open subset of `F` inside
  `E`, so `k⁻¹(t)` would have interior in `E`.
* **A layer of `E` inside a layer `d⁻¹(u)`, `u < s`, is that layer.** `d⁻¹(u) ⊆ E` is a subcontinuum
  of `E`; if `k` took two values `α < β` on it, it would contain `k⁻¹(α, β)`, open in `E`; since
  `d⁻¹[0, s)` is open in `F` and lies in `E`, `k⁻¹(α, β)` would be open in `F`, so `d⁻¹(u)` would have
  interior in `F`.

The printed claims `layerSet d (Icc 0 s) = E` and "each element of the decomposition of `E` (except
possibly `k⁻¹(1)`) is an element of the decomposition of `F`" are not consequences of the reason
given ("Since the decompositions of `E` and `F` are minimal"); see the statement in
`Hagopian76A.lean`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Lemma4Layers

variable {M : Set Pt}

/-- **Lemma 4, first paragraph** (the part that follows from minimality). -/
theorem lemma4_layers_aux {E F : Set M} {k : E → unitInterval} {d : F → unitInterval}
    (hE : IsMinimalAdmissible E k) (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F)
    (hX0 : layer d 0 = layer k 0) :
    ∃ s : unitInterval, 0 < s ∧ layerSet d (Ico 0 s) ⊆ E ∧ E ⊆ layerSet d (Icc 0 s) ∧
      (∀ t, ∃ u, layer k t ⊆ layer d u) ∧
      ∀ t u, u < s → layer k t ⊆ layer d u → layer k t = layer d u := by
  obtain ⟨⟨a, b, hab⟩, hk, hk0⟩ := hE
  obtain ⟨⟨a', b', hab'⟩, hd, hd0⟩ := hF
  have hEc := hab.1
  have hFc := hab'.1
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hFc.1
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hEc.1
  -- `s`
  set SE : Set F := Subtype.val ⁻¹' E
  have hSEc : IsCompact SE := (hEc.1.isClosed.preimage continuous_subtype_val).isCompact
  obtain ⟨x₀, hx₀⟩ := hk.2.1 0
  have hx₀d : (x₀ : M) ∈ layer d 0 := hX0 ▸ ⟨x₀, hx₀, rfl⟩
  have hx₀S : (⟨x₀, hEF x₀.2⟩ : F) ∈ SE := x₀.2
  obtain ⟨w, hwS, hwmax⟩ := hSEc.exists_isMaxOn ⟨_, hx₀S⟩ hd.1.continuousOn
  set s := d w
  -- `s > 0`
  obtain ⟨z, hz⟩ := hk.2.1 1
  have hzX : (z : M) ∉ layer d 0 := by
    rw [hX0]
    rintro ⟨z', hz', hzz⟩
    have : z' = z := Subtype.ext hzz
    have h0 : k z' = 0 := hz'
    rw [this, hz] at h0
    exact one_ne_zero h0
  have hs0 : 0 < s := by
    refine lt_of_lt_of_le ?_ (hwmax (show (⟨z, hEF z.2⟩ : F) ∈ SE from z.2))
    refine lt_of_le_of_ne unitInterval.nonneg' fun h0 => hzX ⟨⟨z, hEF z.2⟩, h0.symm, rfl⟩
  -- `d⁻¹[0, s) ⊆ E`
  have hlow : layerSet d (Ico 0 s) ⊆ E := by
    rintro _ ⟨y, hy, rfl⟩
    rcases (hy : d y ∈ Ico 0 s).1.lt_or_eq with h | h
    · exact layer_subset_of_meets' hab' hd hEF hEc ⟨x₀, x₀.2, hx₀d⟩ ⟨w, hwS, w, rfl, rfl⟩ h
        hy.2 ⟨y, rfl, rfl⟩
    · have : (y : M) ∈ layer d 0 := ⟨y, h.symm, rfl⟩
      rw [hX0] at this
      exact img_subset _ this
  have hup : E ⊆ layerSet d (Icc 0 s) := fun x hx =>
    ⟨⟨x, hEF hx⟩, ⟨unitInterval.nonneg', hwmax (show (⟨x, hEF hx⟩ : F) ∈ SE from hx)⟩, rfl⟩
  -- each layer of `E` lies in a layer of `F`
  have hin : ∀ t, ∃ u, layer k t ⊆ layer d u := by
    intro t
    set Y := layer k t
    have hY : Fold.Q78.IsContinuum Y := isContinuum_layer hEc.1 hk t
    have hYF : Y ⊆ F := (img_subset _).trans hEF
    set SY : Set F := Subtype.val ⁻¹' Y
    have hSYc : IsCompact SY := (hY.1.isClosed.preimage continuous_subtype_val).isCompact
    obtain ⟨y₀, hy₀⟩ := hk.2.1 t
    have hy₀S : (⟨y₀, hEF y₀.2⟩ : F) ∈ SY := ⟨y₀, hy₀, rfl⟩
    obtain ⟨y₁, hy₁, hmin⟩ := hSYc.exists_isMinOn ⟨_, hy₀S⟩ hd.1.continuousOn
    obtain ⟨y₂, hy₂, hmax⟩ := hSYc.exists_isMaxOn ⟨_, hy₀S⟩ hd.1.continuousOn
    rcases (show d y₁ ≤ d y₂ from hmin hy₂).lt_or_eq with hlt | heq
    · exfalso
      obtain ⟨v, hv1, hv2⟩ := exists_between hlt
      obtain ⟨p, hp⟩ := hd.2.1 v
      have hΩ : IsOpen (d ⁻¹' Ioo (d y₁) (d y₂)) := isOpen_Ioo.preimage hd.1
      obtain ⟨O, hO, hOΩ⟩ := isOpen_induced_iff.1 hΩ
      have hmid : ∀ q : F, d q ∈ Ioo (d y₁) (d y₂) → (q : M) ∈ Y := fun q hq =>
        layer_subset_of_meets' hab' hd hYF hY ⟨y₁, hy₁, y₁, rfl, rfl⟩ ⟨y₂, hy₂, y₂, rfl, rfl⟩
          hq.1 hq.2 ⟨q, rfl, rfl⟩
      have hpY := hmid p (hp ▸ ⟨hv1, hv2⟩)
      set Q : Set E := Subtype.val ⁻¹' O
      have hQo : IsOpen Q := hO.preimage continuous_subtype_val
      have hpE : (p : M) ∈ E := img_subset _ hpY
      have hQne : Q.Nonempty := by
        refine ⟨⟨p, hpE⟩, ?_⟩
        have : p ∈ Subtype.val ⁻¹' O := hOΩ ▸ (show d p ∈ Ioo (d y₁) (d y₂) from hp ▸ ⟨hv1, hv2⟩)
        exact this
      have hQs : Q ⊆ k ⁻¹' {t} := by
        intro x hx
        have hxF : (x : M) ∈ F := hEF x.2
        have : (⟨x, hxF⟩ : F) ∈ d ⁻¹' Ioo (d y₁) (d y₂) := by rw [← hOΩ]; exact hx
        obtain ⟨x', hx', hxx⟩ := hmid _ this
        have : x' = x := Subtype.ext hxx
        rw [← this]; exact hx'
      have hint : (interior (k ⁻¹' {t})).Nonempty := hQne.mono (interior_maximal hQs hQo)
      rw [hk0 t] at hint
      exact not_nonempty_empty hint
    · refine ⟨d y₁, fun x hx => ?_⟩
      have hxF : x ∈ F := hYF hx
      have hxS : (⟨x, hxF⟩ : F) ∈ SY := hx
      exact ⟨⟨x, hxF⟩, le_antisymm (heq ▸ hmax hxS) (hmin hxS), rfl⟩
  refine ⟨s, hs0, hlow, hup, hin, fun t u hus htu => subset_antisymm htu ?_⟩
  -- a layer of `E` inside `d⁻¹(u)`, `u < s`
  set U := layer d u
  have hU : Fold.Q78.IsContinuum U := isContinuum_layer hFc.1 hd u
  have hUE : U ⊆ E := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hx
    exact hlow ⟨y, ⟨unitInterval.nonneg', (mem_singleton_iff.1 hy) ▸ hus⟩, rfl⟩
  set SU : Set E := Subtype.val ⁻¹' U
  have hSUc : IsCompact SU := (hU.1.isClosed.preimage continuous_subtype_val).isCompact
  obtain ⟨y₀, hy₀⟩ := hk.2.1 t
  have hy₀U : (y₀ : M) ∈ U := htu ⟨y₀, hy₀, rfl⟩
  obtain ⟨y₁, hy₁, hmin⟩ := hSUc.exists_isMinOn ⟨y₀, hy₀U⟩ hk.1.continuousOn
  obtain ⟨y₂, hy₂, hmax⟩ := hSUc.exists_isMaxOn ⟨y₀, hy₀U⟩ hk.1.continuousOn
  rcases (show k y₁ ≤ k y₂ from hmin hy₂).lt_or_eq with hlt | heq
  · exfalso
    obtain ⟨v, hv1, hv2⟩ := exists_between hlt
    obtain ⟨p, hp⟩ := hk.2.1 v
    have hΩ : IsOpen (k ⁻¹' Ioo (k y₁) (k y₂)) := isOpen_Ioo.preimage hk.1
    obtain ⟨O, hO, hOΩ⟩ := isOpen_induced_iff.1 hΩ
    have hmid : ∀ q : E, k q ∈ Ioo (k y₁) (k y₂) → (q : M) ∈ U := fun q hq =>
      layer_subset_of_meets' hab hk hUE hU ⟨y₁, hy₁, y₁, rfl, rfl⟩ ⟨y₂, hy₂, y₂, rfl, rfl⟩
        hq.1 hq.2 ⟨q, rfl, rfl⟩
    set Q : Set F := Subtype.val ⁻¹' O ∩ d ⁻¹' Iio s
    have hQo : IsOpen Q := (hO.preimage continuous_subtype_val).inter (isOpen_Iio.preimage hd.1)
    have hpU := hmid p (hp ▸ ⟨hv1, hv2⟩)
    obtain ⟨p', hp', hpp⟩ := hpU
    have hQne : Q.Nonempty := by
      refine ⟨p', ?_, ?_⟩
      · show (p' : M) ∈ O
        rw [hpp]
        have : p ∈ Subtype.val ⁻¹' O := hOΩ ▸ (show k p ∈ Ioo (k y₁) (k y₂) from hp ▸ ⟨hv1, hv2⟩)
        exact this
      · show d p' < s
        rw [mem_singleton_iff.1 hp']; exact hus
    have hQs : Q ⊆ d ⁻¹' {u} := by
      rintro x ⟨hxO, hxs⟩
      have hxE : (x : M) ∈ E := hlow ⟨x, ⟨unitInterval.nonneg', hxs⟩, rfl⟩
      have : (⟨x, hxE⟩ : E) ∈ k ⁻¹' Ioo (k y₁) (k y₂) := by rw [← hOΩ]; exact hxO
      obtain ⟨x', hx', hxx⟩ := hmid _ this
      have : x' = x := Subtype.ext hxx
      rw [← this]; exact hx'
    have hint : (interior (d ⁻¹' {u})).Nonempty := hQne.mono (interior_maximal hQs hQo)
    rw [hd0 u] at hint
    exact not_nonempty_empty hint
  · intro x hx
    have hxE := hUE hx
    have hxS : (⟨x, hxE⟩ : E) ∈ SU := hx
    have hkx : k ⟨x, hxE⟩ = t := by
      have h1 : k ⟨x, hxE⟩ = k y₁ :=
        le_antisymm ((show k ⟨x, hxE⟩ ≤ k y₂ from hmax hxS).trans heq.symm.le)
          (show k y₁ ≤ k ⟨x, hxE⟩ from hmin hxS)
      have hy0 : y₀ ∈ SU := hy₀U
      have h3 : k y₀ = k y₁ :=
        le_antisymm ((show k y₀ ≤ k y₂ from hmax hy0).trans heq.symm.le)
          (show k y₁ ≤ k y₀ from hmin hy0)
      rw [h1, ← h3, hy₀]
    exact ⟨⟨x, hxE⟩, hkx, rfl⟩

end Lemma4Layers

end HPC.Hagopian
