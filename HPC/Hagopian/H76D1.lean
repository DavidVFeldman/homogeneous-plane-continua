import HPC.Hagopian.Hagopian76A

/-!
# Batch 157, item A: D1 reduced to the swallowed-layer configuration

The first paragraph of Lemma 4 (Hagopian 1976, p. 341), re-rendered in `Hagopian76B.lean`, and the
statement `hagopian76_no_swallowed_layer` ("no layer `k⁻¹(t)`, `t < 1`, lies in a layer of `F` that
meets `k⁻¹(1)`") are equivalent, given `hagopian76_lemma4_layers'`. Both directions are proved here,
without homogeneity:

* `lemma4_layers_of_no_swallowed`: from `lemma4_layers_aux`, `k⁻¹(1)` lies in `d⁻¹(s)` (otherwise
  `k⁻¹(1) = d⁻¹(u)` with `u < s`, and `d⁻¹[[0, u]]` would be a proper subcontinuum of `E` meeting both
  end sets); so a layer `k⁻¹(t)`, `t < 1`, that is not a layer of `F` lies in `d⁻¹(s)`, which meets
  `k⁻¹(1)`: the swallowed configuration.
* `no_swallowed_of_lemma4_layers`: if `k⁻¹(t) = d⁻¹(u')` and `k⁻¹(t) ⊆ d⁻¹(u)`, then `u' = u`, and
  `k⁻¹(1)` would meet `k⁻¹(t)`.

So D1 is exactly the exclusion of the swallowed configuration; it remains open (`OPEN.md`).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section D1

theorem IsMinimalAdmissible.isCompact {X : Type*} [MetricSpace X] {E : Set X} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) : IsCompact E := by
  obtain ⟨⟨a, b, hab⟩, -, -⟩ := hE
  exact hab.1.1

/-- Two layers sharing a point have the same parameter. -/
theorem layer_param_eq {X : Type*} {F : Set X} {d : F → unitInterval} {x : X} {u u' : unitInterval}
    (hx : x ∈ layer d u) (hx' : x ∈ layer d u') : u = u' := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨y', hy', hyy⟩ := hx'
  have : y' = y := Subtype.ext hyy
  rw [this] at hy'
  exact (mem_singleton_iff.1 hy).symm.trans (mem_singleton_iff.1 hy')

theorem layer_nonempty {X : Type*} {E : Set X} {k : E → unitInterval} (hk : Function.Surjective k)
    (t : unitInterval) : (layer k t).Nonempty := by
  obtain ⟨e, he⟩ := hk t
  exact ⟨e, e, he, rfl⟩

variable {M : Set Pt}

/-- **The swallowed configuration excluded ⇒ the first paragraph of Lemma 4, as printed.** -/
theorem lemma4_layers_of_no_swallowed {E F : Set M} {k : E → unitInterval}
    {d : F → unitInterval} (hE : IsMinimalAdmissible E k) (hF : IsMinimalAdmissible F d)
    (hEF : E ⊆ F) (hX0 : layer d 0 = layer k 0)
    (hns : ∀ t u : unitInterval, t < 1 → layer k t ⊆ layer d u →
      (layer k 1 ∩ layer d u).Nonempty → False) :
    ∃ s : unitInterval, 0 < s ∧ (∀ r, r < s → layer d r ⊆ E) ∧ E ⊆ layerSet d (Icc 0 s) ∧
      (layer d s ∩ E).Nonempty ∧
      ∀ t : unitInterval, t ≠ 1 → ∃ u : unitInterval, layer k t = layer d u := by
  obtain ⟨s, hs0, hlow, hup, hin, heq⟩ := lemma4_layers_aux hE hF hEF hX0
  have hks := hE.2.1.2.1
  have hds := hF.2.1.2.1
  -- a layer of `E` lies in a layer `d⁻¹(u)` with `u ≤ s`
  have hle : ∀ t u, layer k t ⊆ layer d u → u ≤ s := fun t u htu => by
    obtain ⟨x, hx⟩ := layer_nonempty hks t
    obtain ⟨y, hy, hyx⟩ := hup (img_subset _ hx)
    have h1 : (x : M) ∈ layer d (d y) := ⟨y, rfl, hyx⟩
    rw [layer_param_eq (htu hx) h1]
    exact hy.2
  have hlayer : ∀ r, r < s → layer d r ⊆ E := fun r hr => by
    rintro _ ⟨y, hy, rfl⟩
    exact hlow ⟨y, ⟨unitInterval.nonneg', (mem_singleton_iff.1 hy) ▸ hr⟩, rfl⟩
  -- `k⁻¹(1) ⊆ d⁻¹(s)`
  have hZ : layer k 1 ⊆ layer d s := by
    obtain ⟨u, hu⟩ := hin 1
    rcases (hle 1 u hu).lt_or_eq with hus | rfl
    · exfalso
      have hZu := heq 1 u hus hu
      set C := layerSet d (Icc 0 u)
      have hC : Fold.Q78.IsContinuum C :=
        isContinuum_img hF.isCompact hF.2.1 isClosed_Icc isPreconnected_Icc
          ⟨0, unitInterval.nonneg', unitInterval.nonneg'⟩
      have hCE : C ⊆ E := by
        rintro _ ⟨y, hy, rfl⟩
        exact hlow ⟨y, ⟨hy.1, lt_of_le_of_lt hy.2 hus⟩, rfl⟩
      have h0 : (C ∩ layer k 0).Nonempty := by
        obtain ⟨x, hx⟩ := layer_nonempty hks 0
        refine ⟨x, ?_, hx⟩
        rw [← hX0] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨y, ⟨unitInterval.nonneg', (mem_singleton_iff.1 hy) ▸ unitInterval.nonneg'⟩, rfl⟩
      have h1 : (C ∩ layer k 1).Nonempty := by
        obtain ⟨x, hx⟩ := layer_nonempty hks 1
        refine ⟨x, ?_, hx⟩
        rw [hZu] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨y, ⟨unitInterval.nonneg', (mem_singleton_iff.1 hy).le⟩, rfl⟩
      have hCeq := end_sets_aux hE hCE hC h0 h1
      obtain ⟨v, huv, hvs⟩ := exists_between hus
      obtain ⟨y, hy⟩ := hds v
      have hyE : (y : M) ∈ E := hlow ⟨y, ⟨unitInterval.nonneg', hy ▸ hvs⟩, rfl⟩
      rw [← hCeq] at hyE
      obtain ⟨y', hy', hyy⟩ := hyE
      have : y' = y := Subtype.ext hyy
      rw [this] at hy'
      have h2 : d y ≤ u := hy'.2
      rw [hy] at h2
      exact absurd h2 (not_le.2 huv)
    · exact hu
  refine ⟨s, hs0, hlayer, hup, ?_, fun t ht => ?_⟩
  · obtain ⟨x, hx⟩ := layer_nonempty hks 1
    exact ⟨x, hZ hx, img_subset _ hx⟩
  · obtain ⟨u, hu⟩ := hin t
    rcases (hle t u hu).lt_or_eq with hus | rfl
    · exact ⟨u, heq t u hus hu⟩
    · exfalso
      obtain ⟨x, hx⟩ := layer_nonempty hks 1
      exact hns t u (lt_of_le_of_ne unitInterval.le_one' ht) hu ⟨x, hx, hZ hx⟩

/-- **The first paragraph of Lemma 4, as printed ⇒ the swallowed configuration is excluded.** -/
theorem no_swallowed_of_lemma4_layers {E F : Set M} {k : E → unitInterval}
    {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hlay : ∀ t : unitInterval, t ≠ 1 → ∃ u : unitInterval, layer k t = layer d u)
    {t u : unitInterval} (ht : t < 1) (hsub : layer k t ⊆ layer d u)
    (hZ : (layer k 1 ∩ layer d u).Nonempty) : False := by
  obtain ⟨u', hu'⟩ := hlay t (ne_of_lt ht)
  obtain ⟨x, hx⟩ := layer_nonempty hE.2.1.2.1 t
  have huu : u' = u := layer_param_eq (hu' ▸ hx) (hsub hx)
  obtain ⟨z, hz1, hzu⟩ := hZ
  rw [← huu, ← hu'] at hzu
  have := layer_param_eq hz1 hzu
  rw [this] at ht
  exact lt_irrefl _ ht

end D1

end HPC.Hagopian
