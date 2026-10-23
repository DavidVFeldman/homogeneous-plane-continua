import HPC.Hagopian.H84TwoSided

/-!
# Batch 185, §2–§3.1: Lemma 7 of 1984 and rigidity

Commission 185 §2 (Hagopian 1984, p. 336, Lemma 7) and §3.1.

* `no_arm_at_interior_layer`: a continuum `A` meeting a type λ continuum `G` only inside an interior
  layer `Y = g⁻¹(u)`, and not inside `Y`, makes `G ∪ A` a triod with core `Y` (against
  atriodicity).
* `layer_common_of_essential`: if `G₁ ∩ G₂` is a continuum meeting two layers of each, a layer of
  `G₁` through a point of `G₁ ∩ G₂` is a layer of `G₂` (Lemma 6 twice).
* `hagopian84_lemma7_aux`: Lemma 7, by the case split on `K = H ∩ F` (`H` the two-sided extension
  of `E`, `I` that of `F`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Lemma7

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **The triod at an interior layer.** `(G, g)` minimal admissible, `0 < u < 1`, `A` a continuum
with `A ∩ G ≠ ∅`, `A ∩ G ⊆ g⁻¹(u)` and `A ⊄ g⁻¹(u)`: then `G ∪ A` is a triod with core `g⁻¹(u)`
(arms `g⁻¹([0, u))`, `g⁻¹((u, 1])`, `A ∖ g⁻¹(u)`), against atriodicity. -/
theorem no_arm_at_interior_layer (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {G : Set M}
    {g : G → unitInterval} (hG : IsMinimalAdmissible G g) {u : unitInterval} (hu0 : 0 < u)
    (hu1 : u < 1) {A : Set M} (hA : Fold.Q78.IsContinuum A) (hAG : A ∩ G ⊆ layer g u)
    (hAne : (A ∩ G).Nonempty) (hAY : ¬ A ⊆ layer g u) : False := by
  have hAT := (hagopian75_lemma1 hX hi).1
  have hGc : Fold.Q78.IsContinuum G := by obtain ⟨_, _, h⟩ := hG.1; exact h.1
  set Y := layer g u with hY
  set P₁ := layerSet g (Iio u) with hP₁
  set P₂ := layerSet g (Ioi u) with hP₂
  set P₃ := A \ Y with hP₃
  have hYc : Fold.Q78.IsContinuum Y :=
    isContinuum_img hG.isCompact hG.2.1 isClosed_singleton isPreconnected_singleton
      (singleton_nonempty u)
  have hcl₁ : closure P₁ ⊆ layerSet g (Iic u) :=
    closure_minimal (fun _ ⟨x, hx, hxe⟩ => ⟨x, show g x ≤ u from le_of_lt hx, hxe⟩)
      (isCompact_img hG.isCompact hG.2.1.1 isClosed_Iic).isClosed
  have hcl₂ : closure P₂ ⊆ layerSet g (Ici u) :=
    closure_minimal (fun _ ⟨x, hx, hxe⟩ => ⟨x, show u ≤ g x from le_of_lt hx, hxe⟩)
      (isCompact_img hG.isCompact hG.2.1.1 isClosed_Ici).isClosed
  have hcl₃ : closure P₃ ⊆ A := closure_minimal diff_subset hA.1.isClosed
  have hP₁G : P₁ ⊆ G := layerSet_subset' g _
  have hP₂G : P₂ ⊆ G := layerSet_subset' g _
  have hP₁Y : Disjoint P₁ Y := by
    rw [disjoint_left]; rintro _ ⟨x, hx, rfl⟩ hy
    exact (ne_of_lt hx) (layer_param_eq ⟨x, rfl, rfl⟩ hy)
  have hP₂Y : Disjoint P₂ Y := by
    rw [disjoint_left]; rintro _ ⟨x, hx, rfl⟩ hy
    exact (ne_of_gt hx) (layer_param_eq ⟨x, rfl, rfl⟩ hy)
  have h12 : Disjoint (layerSet g (Iic u)) P₂ := by
    rw [disjoint_left]; rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    subst this
    exact absurd (show g y ≤ u from hx) (not_le.2 hy)
  have h21 : Disjoint P₁ (layerSet g (Ici u)) := by
    rw [disjoint_left]; rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    subst this
    exact absurd (show u ≤ g y from hy) (not_le.2 hx)
  have hT : Fold.Q78.IsContinuum (G ∪ A) := by
    obtain ⟨p, hpA, hpG⟩ := hAne
    exact ⟨hG.isCompact.union hA.1, IsConnected.union ⟨p, hpG, hpA⟩ hGc.2 hA.2⟩
  refine hAT (G ∪ A) (subset_univ _) ⟨hT, Y, hYc, (layer_subset' g u).trans subset_union_left,
    P₁, P₂, P₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hG.2.1.2.1 0
    exact ⟨x, x, by rw [mem_preimage, hx]; exact hu0, rfl⟩
  · obtain ⟨x, hx⟩ := hG.2.1.2.1 1
    exact ⟨x, x, by rw [mem_preimage, hx]; exact hu1, rfl⟩
  · exact diff_nonempty.2 hAY
  · ext p
    constructor
    · rintro ⟨hp | hp, hpY⟩
      · rcases lt_trichotomy (g ⟨p, hp⟩) u with h | h | h
        · exact Or.inl (Or.inl ((mem_layerSet_iff' hp).2 h))
        · exact absurd ((mem_layer_iff' hp).2 h) hpY
        · exact Or.inl (Or.inr ((mem_layerSet_iff' hp).2 h))
      · exact Or.inr ⟨hp, hpY⟩
    · rintro ((hp | hp) | hp)
      · exact ⟨Or.inl (hP₁G hp), disjoint_left.1 hP₁Y hp⟩
      · exact ⟨Or.inl (hP₂G hp), disjoint_left.1 hP₂Y hp⟩
      · exact ⟨Or.inr hp.1, hp.2⟩
  · exact h12.mono_left hcl₁
  · exact h21.mono_right hcl₂
  · rw [disjoint_left]; intro p hp hp3
    exact hp3.2 (hAG ⟨hp3.1, layerSet_subset' g _ (hcl₁ hp)⟩)
  · rw [disjoint_left]; intro p hp hp3
    exact disjoint_left.1 hP₁Y hp (hAG ⟨hcl₃ hp3, hP₁G hp⟩)
  · rw [disjoint_left]; intro p hp hp3
    exact hp3.2 (hAG ⟨hp3.1, layerSet_subset' g _ (hcl₂ hp)⟩)
  · rw [disjoint_left]; intro p hp hp3
    exact disjoint_left.1 hP₂Y hp (hAG ⟨hcl₃ hp3, hP₂G hp⟩)

omit [CompactSpace M] [ConnectedSpace M] in
/-- A subset `K` of `G` through a point of `g⁻¹(u)` meets two layers of `G` or lies in `g⁻¹(u)`. -/
theorem two_layers_or_subset {G : Set M} {g : G → unitInterval} {K : Set M} (hKG : K ⊆ G)
    {u : unitInterval} {p : M} (hpK : p ∈ K) (hpu : p ∈ layer g u) :
    (∃ t₁ t₂, t₁ ≠ t₂ ∧ (K ∩ layer g t₁).Nonempty ∧ (K ∩ layer g t₂).Nonempty) ∨
      K ⊆ layer g u := by
  by_cases h : K ⊆ layer g u
  · exact Or.inr h
  · obtain ⟨q, hqK, hqu⟩ := not_subset.1 h
    have hqG := hKG hqK
    refine Or.inl ⟨u, g ⟨q, hqG⟩, fun he => hqu ((mem_layer_iff' hqG).2 he.symm), ⟨p, hpK, hpu⟩,
      ⟨q, hqK, (mem_layer_iff' hqG).2 rfl⟩⟩

/-- **Common layers** (Lemma 6 twice): if `K = G₁ ∩ G₂` is a continuum meeting two layers of `G₁`
and two layers of `G₂`, the layer of `G₁` through a point of `K` is a layer of `G₂`. -/
theorem layer_common_of_essential (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {G₁ G₂ : Set M} {g₁ : G₁ → unitInterval} {g₂ : G₂ → unitInterval}
    (h₁ : IsMinimalAdmissible G₁ g₁) (h₂ : IsMinimalAdmissible G₂ g₂)
    (hK : Fold.Q78.IsContinuum (G₁ ∩ G₂))
    (hK₁ : ∃ t₁ t₂, t₁ ≠ t₂ ∧ ((G₁ ∩ G₂) ∩ layer g₁ t₁).Nonempty ∧
      ((G₁ ∩ G₂) ∩ layer g₁ t₂).Nonempty)
    (hK₂ : ∃ t₁ t₂, t₁ ≠ t₂ ∧ ((G₁ ∩ G₂) ∩ layer g₂ t₁).Nonempty ∧
      ((G₁ ∩ G₂) ∩ layer g₂ t₂).Nonempty)
    {u : unitInterval} {p : M} (hp : p ∈ G₁ ∩ G₂) (hpu : p ∈ layer g₁ u) :
    ∃ v, layer g₁ u = layer g₂ v := by
  obtain ⟨t₁, t₂, ht, ha, hb⟩ := hK₁
  obtain ⟨-, ⟨hirr, e, he, he0⟩, hlay₁⟩ :=
    hagopian84_lemma6 hX hi h₁ ⟨inter_subset_left, hK, t₁, t₂, ht, ha, hb⟩
  obtain ⟨t₁', t₂', ht', ha', hb'⟩ := hK₂
  have hK' : Fold.Q78.IsContinuum (G₂ ∩ G₁) := by rw [inter_comm]; exact hK
  -- Lemma 6 for `G₂`, on the same set written `G₁ ∩ G₂`
  have hess₂ : IsEssential84 g₂ (G₁ ∩ G₂) := ⟨inter_subset_right, hK, t₁', t₂', ht', ha', hb'⟩
  obtain ⟨-, -, hlay₂⟩ := hagopian84_lemma6 hX hi h₂ hess₂
  have hme : IsMinimalAdmissible (G₁ ∩ G₂) e := ⟨hirr, he, he0⟩
  obtain ⟨s, hs⟩ := hlay₁ e hme (e ⟨p, hp⟩)
  obtain ⟨v, hv⟩ := hlay₂ e hme (e ⟨p, hp⟩)
  have hpe : p ∈ layer e (e ⟨p, hp⟩) := ⟨⟨p, hp⟩, rfl, rfl⟩
  have hsu : s = u := layer_param_eq (hs ▸ hpe) hpu
  subst hsu
  exact ⟨v, hs.symm.trans hv⟩

/-- **Lemma 7** (Hagopian 1984, p. 336), from the two-sided extension. Let `H ⊇ E` and `I ⊇ F` be
two-sided extensions (`hagopian84_two_sided_aux`): `k⁻¹(r) = H`-layer `u` with `0 < u < 1`
(Lemma 6). `K = H ∩ F` is a continuum through a point `p` of `F ∩ k⁻¹(r)`.
* `K` inside the `H`-layer `u`: then `F ⊄ H` (else `F ⊆ k⁻¹(r) ⊆ E`), and `F` is an arm at
  `k⁻¹(r)` (`no_arm_at_interior_layer`).
* `K` meets two `H`-layers and two `F`-layers: `layer_common_of_essential`.
* `K` meets two `H`-layers and lies in the `F`-layer `Y`: `Y` is an interior `I`-layer; if `H ∩ I`
  meets two `I`-layers, two distinct `H`-layers inside `K ⊆ Y` would both be the `I`-layer `Y`;
  otherwise `H ∩ I ⊆ Y` and `H` is an arm at `Y` (a point of `E∖F` lies off `Y`). -/
theorem hagopian84_lemma7_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E F : Set M}
    {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hEF : (E \ F).Nonempty) (hFE : (F \ E).Nonempty)
    {r : unitInterval} (hr : (F ∩ layer k r).Nonempty) : ∃ u, layer k r = layer d u := by
  have hHU := hagopian75_lemma1_hu hX hi
  obtain ⟨H, dH, hH, hEss, hE0, hE1⟩ := hagopian84_two_sided_aux hX hi hE
  obtain ⟨I, dI, hI, hFss, hF0, hF1⟩ := hagopian84_two_sided_aux hX hi hF
  have hEH : E ⊆ H := hEss.1
  have hFI : F ⊆ I := hFss.1
  have hHc : Fold.Q78.IsContinuum H := by obtain ⟨_, _, h⟩ := hH.1; exact h.1
  have hFc : Fold.Q78.IsContinuum F := by obtain ⟨_, _, h⟩ := hF.1; exact h.1
  have hIc : Fold.Q78.IsContinuum I := by obtain ⟨_, _, h⟩ := hI.1; exact h.1
  -- `k⁻¹(r)` is an interior layer of `H`
  obtain ⟨-, -, hlayE⟩ := hagopian84_lemma6 hX hi hH hEss
  obtain ⟨u, hu⟩ := hlayE k hE r
  have hkrE : layer k r ⊆ E := layer_subset' k r
  obtain ⟨p, hpF, hpr⟩ := hr
  have hu0 : 0 < u := by
    refine lt_of_le_of_ne unitInterval.nonneg' fun h => ?_
    rw [← h] at hu
    exact disjoint_left.1 hE0 (hkrE hpr) (hu ▸ hpr)
  have hu1 : u < 1 := by
    refine lt_of_le_of_ne unitInterval.le_one' fun h => ?_
    rw [h] at hu
    exact disjoint_left.1 hE1 (hkrE hpr) (hu ▸ hpr)
  have hpH : p ∈ H := hEH (hkrE hpr)
  have hpu : p ∈ layer dH u := hu ▸ hpr
  have hK : Fold.Q78.IsContinuum (H ∩ F) := isContinuum_inter_of_hu hHU hHc hFc ⟨p, hpH, hpF⟩
  rcases two_layers_or_subset (inter_subset_left : H ∩ F ⊆ H) ⟨hpH, hpF⟩ hpu with hK₁ | hKu
  swap
  · -- `K` inside the `H`-layer `u`
    exfalso
    by_cases hFH : F ⊆ H
    · obtain ⟨q, hqF, hqE⟩ := hFE
      exact hqE (hkrE (hu ▸ hKu ⟨hFH hqF, hqF⟩))
    · refine no_arm_at_interior_layer hX hi hH hu0 hu1 hFc (fun q hq => hKu ⟨hq.2, hq.1⟩)
        ⟨p, hpF, hpH⟩ fun hsub => hFH (hsub.trans (layer_subset' dH u))
  -- `K` meets two `H`-layers
  rcases two_layers_or_subset (inter_subset_right : H ∩ F ⊆ F) ⟨hpH, hpF⟩
      ((mem_layer_iff' hpF).2 rfl) with hK₂ | hKY
  · obtain ⟨v, hv⟩ := layer_common_of_essential hX hi hH hF hK hK₁ hK₂ ⟨hpH, hpF⟩ hpu
    exact ⟨v, hu.trans hv⟩
  -- `K` inside the `F`-layer `Y`
  exfalso
  set u' := d ⟨p, hpF⟩ with hu'
  obtain ⟨-, -, hlayF⟩ := hagopian84_lemma6 hX hi hI hFss
  obtain ⟨w, hw⟩ := hlayF d hF u'
  have hYF : layer d u' ⊆ F := layer_subset' d u'
  have hpY : p ∈ layer d u' := (mem_layer_iff' hpF).2 rfl
  have hw0 : 0 < w := by
    refine lt_of_le_of_ne unitInterval.nonneg' fun h => ?_
    rw [← h] at hw
    exact disjoint_left.1 hF0 (hYF hpY) (hw ▸ hpY)
  have hw1 : w < 1 := by
    refine lt_of_le_of_ne unitInterval.le_one' fun h => ?_
    rw [h] at hw
    exact disjoint_left.1 hF1 (hYF hpY) (hw ▸ hpY)
  have hpI : p ∈ I := hFI hpF
  have hK₂c : Fold.Q78.IsContinuum (H ∩ I) := isContinuum_inter_of_hu hHU hHc hIc ⟨p, hpH, hpI⟩
  rcases two_layers_or_subset (inter_subset_right : H ∩ I ⊆ I) ⟨hpH, hpI⟩ (hw ▸ hpY) with
    hKI | hKIw
  · -- two distinct `H`-layers inside `K ⊆ Y` would both be the `I`-layer `w`
    obtain ⟨t₁, t₂, ht, ⟨q₁, hq₁K, hq₁⟩, ⟨q₂, hq₂K, hq₂⟩⟩ := hK₁
    have hKKI : H ∩ F ⊆ H ∩ I := fun q hq => ⟨hq.1, hFI hq.2⟩
    have hK₁' : ∃ t₁ t₂, t₁ ≠ t₂ ∧ ((H ∩ I) ∩ layer dH t₁).Nonempty ∧
        ((H ∩ I) ∩ layer dH t₂).Nonempty :=
      ⟨t₁, t₂, ht, ⟨q₁, hKKI hq₁K, hq₁⟩, ⟨q₂, hKKI hq₂K, hq₂⟩⟩
    obtain ⟨v₁, hv₁⟩ := layer_common_of_essential hX hi hH hI hK₂c hK₁' hKI (hKKI hq₁K) hq₁
    obtain ⟨v₂, hv₂⟩ := layer_common_of_essential hX hi hH hI hK₂c hK₁' hKI (hKKI hq₂K) hq₂
    have hq₁w : q₁ ∈ layer dI w := hw ▸ hKY hq₁K
    have hq₂w : q₂ ∈ layer dI w := hw ▸ hKY hq₂K
    have e₁ : v₁ = w := layer_param_eq (hv₁ ▸ hq₁) hq₁w
    have e₂ : v₂ = w := layer_param_eq (hv₂ ▸ hq₂) hq₂w
    have h12 : layer dH t₁ = layer dH t₂ := by rw [hv₁, hv₂, e₁, e₂]
    exact ht (layer_param_eq hq₁ (h12 ▸ hq₁))
  · -- `H ∩ I ⊆ Y`: `H` is an arm at `Y`
    obtain ⟨e, heE, heF⟩ := hEF
    refine no_arm_at_interior_layer hX hi hI hw0 hw1 hHc hKIw ⟨p, hpH, hpI⟩ fun hsub => ?_
    exact heF (hYF (hw ▸ hsub (hEH heE)))

end Lemma7

end HPC.Hagopian
