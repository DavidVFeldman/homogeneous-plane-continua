import HPC.Hagopian.Hagopian76H

/-!
# Batch 164, item A: the reparametrization of a minimal admissible map

Hagopian p. 345: "Since `M` is homogeneous, we can assume … that `π[k⁻¹(i/22)] = (i, 0)` for each
integer `i`." A homeomorphism `θ` of `[0, 1]` turns `k` into `θ ∘ k`, still minimal admissible, with
the same layers (relabelled) and the same relation `S`; `γ` becomes `γ ∘ θ⁻¹`. For the piecewise
linear `θ` sending `y` to `z` (`plr y z`), the collar `F` becomes `F ∘ (θ⁻¹ × id)`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## Relabelling by a homeomorphism of `[0, 1]` -/

section Relabel

variable {M : Set Pt}

/-- A homeomorphism of `[0, 1]` applied to a minimal admissible map gives a minimal admissible
map. -/
theorem IsMinimalAdmissible.homeo {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) (θ : unitInterval ≃ₜ unitInterval) :
    IsMinimalAdmissible E (fun e => θ (k e)) := by
  have hpre : ∀ t, (fun e => θ (k e)) ⁻¹' {t} = k ⁻¹' {θ.symm t} := by
    intro t
    ext e
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h; rw [← h, Homeomorph.symm_apply_apply]
    · intro h; rw [h, Homeomorph.apply_symm_apply]
  refine ⟨hE.1, ⟨θ.continuous.comp hE.2.1.1, fun t => ?_, fun t => ?_⟩, fun t => ?_⟩
  · obtain ⟨e, he⟩ := hE.2.1.2.1 (θ.symm t)
    exact ⟨e, by simp only [he, Homeomorph.apply_symm_apply]⟩
  · rw [hpre]; exact hE.2.1.2.2 _
  · rw [hpre]; exact hE.2.2 _

/-- The layers of `θ ∘ k` are those of `k`, relabelled. -/
theorem layer_homeo {E : Set M} (k : E → unitInterval) (θ : unitInterval ≃ₜ unitInterval)
    (t : unitInterval) : layer (fun e => θ (k e)) t = layer k (θ.symm t) := by
  ext m
  simp only [layer, mem_image, mem_preimage, mem_singleton_iff]
  constructor
  · rintro ⟨e, he, rfl⟩; exact ⟨e, by rw [← he, Homeomorph.symm_apply_apply], rfl⟩
  · rintro ⟨e, he, rfl⟩; exact ⟨e, by rw [he, Homeomorph.apply_symm_apply], rfl⟩

/-- The layer of `θ ∘ k` over `θ t` is the layer of `k` over `t`. -/
theorem layer_homeo_apply {E : Set M} (k : E → unitInterval) (θ : unitInterval ≃ₜ unitInterval)
    (t : unitInterval) : layer (fun e => θ (k e)) (θ t) = layer k t := by
  rw [layer_homeo, Homeomorph.symm_apply_apply]

/-- The relation `S` does not see the relabelling. -/
theorem layerSetoid_homeo {E : Set M} (k : E → unitInterval) (θ : unitInterval ≃ₜ unitInterval)
    (p q : Pt) : layerSetoid (fun e => θ (k e)) p q ↔ layerSetoid k p q := by
  have hkey : ∀ r, layerKey (fun e => θ (k e)) r = Sum.map θ id (layerKey k r) := by
    intro r
    simp only [layerKey]
    split_ifs <;> rfl
  change layerKey _ p = layerKey _ q ↔ layerKey k p = layerKey k q
  rw [hkey, hkey]
  constructor
  · intro h
    have hinj : Function.Injective (Sum.map θ (id : Pt → Pt)) :=
      Sum.map_injective.2 ⟨θ.injective, Function.injective_id⟩
    exact hinj h
  · intro h; rw [h]

/-- The full transport of the set-up of T0–T2 (`π`, `γ`, accessibility) along a homeomorphism `θ`
of `[0, 1]`. -/
theorem setup_homeo {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} {γ : unitInterval → Pt} (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγ : IsEmbedding γ) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    (θ : unitInterval ≃ₜ unitInterval) :
    IsMinimalAdmissible E (fun e => θ (k e)) ∧
      (∀ p q, π p = π q ↔ layerSetoid (fun e => θ (k e)) p q) ∧
      IsEmbedding (fun t => γ (θ.symm t)) ∧
      (∀ t, ∀ x ∈ toPt (layer (fun e => θ (k e)) t), π x = γ (θ.symm t)) ∧
      range (fun t => γ (θ.symm t)) = range γ := by
  refine ⟨hE.homeo θ, fun p q => (hπS p q).trans (layerSetoid_homeo k θ p q).symm,
    hγ.comp θ.symm.isEmbedding, fun t x hx => hγπ _ x (by rwa [layer_homeo] at hx), ?_⟩
  exact (θ.symm.surjective.range_comp γ)

end Relabel

/-! ## The piecewise linear homeomorphism sending `y` to `z` -/

section PL

/-- The piecewise linear map of `ℝ` fixing `0` and `1` and sending `y` to `z`. -/
noncomputable def plr (y z : ℝ) (x : ℝ) : ℝ :=
  if x ≤ y then x * z / y else z + (x - y) * (1 - z) / (1 - y)

variable {y z : ℝ}

theorem plr_of_le {x : ℝ} (h : x ≤ y) : plr y z x = x * z / y := if_pos h

theorem plr_of_lt {x : ℝ} (h : y < x) : plr y z x = z + (x - y) * (1 - z) / (1 - y) :=
  if_neg (not_le.2 h)

theorem plr_zero (hy0 : 0 ≤ y) : plr y z 0 = 0 := by
  rw [plr_of_le hy0]; simp

theorem plr_one (hy1 : y < 1) : plr y z 1 = 1 := by
  rw [plr_of_lt hy1]; field_simp [(sub_pos.2 hy1).ne']; ring

theorem plr_self (hy0 : 0 < y) : plr y z y = z := by
  rw [plr_of_le le_rfl]; field_simp

theorem continuous_plr (hy0 : 0 < y) (hy1 : y < 1) : Continuous (plr y z) := by
  refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const ?_
  intro x hx
  rw [hx]
  field_simp [hy0.ne', (sub_pos.2 hy1).ne']
  ring

theorem plr_le_iff (hy0 : 0 < y) (hy1 : y < 1) (hz0 : 0 < z) (hz1 : z < 1) {x : ℝ} :
    plr y z x ≤ z ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hxy
    push_neg at hxy
    rw [plr_of_lt hxy] at h
    have : 0 < (x - y) * (1 - z) / (1 - y) :=
      div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    linarith
  · intro h
    rw [plr_of_le h, div_le_iff₀ hy0]
    nlinarith

theorem plr_plr (hy0 : 0 < y) (hy1 : y < 1) (hz0 : 0 < z) (hz1 : z < 1) (x : ℝ) :
    plr z y (plr y z x) = x := by
  by_cases h : x ≤ y
  · have h' : plr y z x ≤ z := (plr_le_iff hy0 hy1 hz0 hz1).2 h
    rw [plr_of_le h', plr_of_le h]
    field_simp
  · push_neg at h
    have h' : z < plr y z x := lt_of_not_ge fun h'' => (not_le.2 h) ((plr_le_iff hy0 hy1 hz0 hz1).1 h'')
    rw [plr_of_lt h', plr_of_lt h]
    field_simp [(sub_pos.2 hy1).ne', (sub_pos.2 hz1).ne']
    ring

/-- `plr y z` as a homeomorphism of `ℝ`, with inverse `plr z y`. -/
noncomputable def plrHomeo (hy0 : 0 < y) (hy1 : y < 1) (hz0 : 0 < z) (hz1 : z < 1) : ℝ ≃ₜ ℝ where
  toFun := plr y z
  invFun := plr z y
  left_inv := plr_plr hy0 hy1 hz0 hz1
  right_inv := plr_plr hz0 hz1 hy0 hy1
  continuous_toFun := continuous_plr hy0 hy1
  continuous_invFun := continuous_plr hz0 hz1

theorem plr_strictMono (hy0 : 0 < y) (hy1 : y < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    StrictMono (plr y z) := by
  intro a b hab
  by_cases hb : b ≤ y
  · rw [plr_of_le (hab.le.trans hb), plr_of_le hb]
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hab hz0) hy0
  · push_neg at hb
    by_cases ha : a ≤ y
    · have h1 : plr y z a ≤ z := (plr_le_iff hy0 hy1 hz0 hz1).2 ha
      have h2 : z < plr y z b :=
        lt_of_not_ge fun h => (not_le.2 hb) ((plr_le_iff hy0 hy1 hz0 hz1).1 h)
      linarith
    · push_neg at ha
      rw [plr_of_lt ha, plr_of_lt hb]
      have : (a - y) * (1 - z) / (1 - y) < (b - y) * (1 - z) / (1 - y) :=
        div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (by linarith) (by linarith))
          (by linarith)
      linarith

theorem plr_mem_Icc (hy0 : 0 < y) (hy1 : y < 1) (hz0 : 0 < z) (hz1 : z < 1) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : plr y z x ∈ Icc (0 : ℝ) 1 := by
  have hm := (plr_strictMono hy0 hy1 hz0 hz1).monotone
  exact ⟨plr_zero (z := z) hy0.le ▸ hm hx.1, plr_one (z := z) hy1 ▸ hm hx.2⟩

theorem plr_mem_Ioo (hy0 : 0 < y) (hy1 : y < 1) (hz0 : 0 < z) (hz1 : z < 1) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : plr y z x ∈ Ioo (0 : ℝ) 1 := by
  have hm := plr_strictMono hy0 hy1 hz0 hz1
  exact ⟨plr_zero (z := z) hy0.le ▸ hm hx.1, plr_one (z := z) hy1 ▸ hm hx.2⟩

/-- `plr y z` as a homeomorphism of `[0, 1]`. -/
noncomputable def plrI (hy0 : 0 < y) (hy1 : y < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    unitInterval ≃ₜ unitInterval where
  toFun t := ⟨plr y z t, plr_mem_Icc hy0 hy1 hz0 hz1 t.2⟩
  invFun t := ⟨plr z y t, plr_mem_Icc hz0 hz1 hy0 hy1 t.2⟩
  left_inv t := Subtype.ext (plr_plr hy0 hy1 hz0 hz1 t)
  right_inv t := Subtype.ext (plr_plr hz0 hz1 hy0 hy1 t)
  continuous_toFun := ((continuous_plr hy0 hy1).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_plr hz0 hz1).comp continuous_subtype_val).subtype_mk _

theorem plrI_coe (hy0 : 0 < y) (hy1 : y < 1) (hz0 : 0 < z) (hz1 : z < 1) (t : unitInterval) :
    ((plrI hy0 hy1 hz0 hz1 t : unitInterval) : ℝ) = plr y z t := rfl

theorem plrI_symm_coe (hy0 : 0 < y) (hy1 : y < 1) (hz0 : 0 < z) (hz1 : z < 1)
    (t : unitInterval) : (((plrI hy0 hy1 hz0 hz1).symm t : unitInterval) : ℝ) = plr z y t := rfl

end PL

/-! ## Transport of a collar -/

/-- `plr z y × id` maps the open rectangle onto itself. -/
theorem image_plr_rect {F : ℝ × ℝ → Pt} {y z : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hz0 : 0 < z)
    (hz1 : z < 1) :
    (fun q : ℝ × ℝ => F (plr z y q.1, q.2)) '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) =
      F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) := by
  ext p
  constructor
  · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
    exact ⟨(plr z y q.1, q.2), ⟨plr_mem_Ioo hz0 hz1 hy0 hy1 hq1, hq2⟩, rfl⟩
  · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
    refine ⟨(plr y z q.1, q.2), ⟨plr_mem_Ioo hy0 hy1 hz0 hz1 hq1, hq2⟩, ?_⟩
    simp only [plr_plr hy0 hy1 hz0 hz1]

/-- **A collar, read through `θ⁻¹ × id`, is a collar of `γ ∘ θ⁻¹`**, for `θ = plr y z`. -/
theorem IsCollar.plrTransport {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {y z : ℝ}
    (hy0 : 0 < y) (hy1 : y < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    IsCollar (fun t => γ ((plrI hy0 hy1 hz0 hz1).symm t)) (fun q => F (plr z y q.1, q.2)) := by
  obtain ⟨hemb, h0, hopen⟩ := hF
  set K := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hK
  have hmaps : MapsTo (fun q : ℝ × ℝ => (plr z y q.1, q.2)) K K := fun q hq =>
    ⟨plr_mem_Icc hz0 hz1 hy0 hy1 hq.1, hq.2⟩
  have hmaps' : MapsTo (fun q : ℝ × ℝ => (plr y z q.1, q.2)) K K := fun q hq =>
    ⟨plr_mem_Icc hy0 hy1 hz0 hz1 hq.1, hq.2⟩
  have hc : Continuous (fun q : ℝ × ℝ => (plr z y q.1, q.2)) :=
    ((continuous_plr hz0 hz1).comp continuous_fst).prodMk continuous_snd
  have hc' : Continuous (fun q : ℝ × ℝ => (plr y z q.1, q.2)) :=
    ((continuous_plr hy0 hy1).comp continuous_fst).prodMk continuous_snd
  -- the homeomorphism of the rectangle
  set φ : K ≃ₜ K :=
    { toFun := hmaps.restrict _ _ _
      invFun := hmaps'.restrict _ _ _
      left_inv := fun q => Subtype.ext (Prod.ext (plr_plr hz0 hz1 hy0 hy1 _) rfl)
      right_inv := fun q => Subtype.ext (Prod.ext (plr_plr hy0 hy1 hz0 hz1 _) rfl)
      continuous_toFun := hc.restrict hmaps
      continuous_invFun := hc'.restrict hmaps' } with hφ
  refine ⟨?_, fun t => ?_, ?_⟩
  · have : K.restrict (fun q => F (plr z y q.1, q.2)) = K.restrict F ∘ φ := by
      funext q; rfl
    rw [this]
    exact hemb.comp φ.isEmbedding
  · exact h0 ((plrI hy0 hy1 hz0 hz1).symm t)
  · rw [image_plr_rect hy0 hy1 hz0 hz1]; exact hopen

end HPC.Hagopian
