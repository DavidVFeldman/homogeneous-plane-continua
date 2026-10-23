import HPC.Hagopian.H76Step8

/-!
# Batch 160, item A: "Since `M` is atriodic, `R(E)` is a composant of `Cl R(E)`" (p. 343)

* `not_indec_of_minimalAdmissible`: a continuum with a minimal admissible map is decomposable.
* `closure_extUnion_one`: step 8 for the other end, `Cl R(Z, E) = Cl R(E)` (step 8 applied to the
  reversed map).
* `exists_ext_of_subset`: every continuum `G ⊆ R(X, E)` lies in one extension away from `X`.
  Otherwise `G` contains every point of `R(X, E)` outside the extension `F_{i₀}` through a point of
  `G` (the interval lemma in a large `F_m`), so `R(X, E) = G ∪ F_{i₀}` is closed; then
  `R(X, E) = Cl R(X, E)` is indecomposable (Lemma 6) and is the union of the increasing proper
  subcontinua `Fᵢ` through a point of `X`, which is impossible (a point outside every proper
  subcontinuum through that point, `T13.exists_not_mem_proper_subcontinua`).
* `ext_inter_subset`: an extension `K` away from `X` and an extension `Q` away from `Z` meet only in
  `E`. If `q ∈ K ∩ Q − E`, then by absorption every tail of `Q` beyond `X` through `q` lies in
  `R(X, E)`, so `Q ⊆ R(X, E)`, so `Q` lies in one extension `F` away from `X`; then a subcontinuum
  of `Q` cut off from `X` by a level of `F` meets both end sets of `Q`, which is impossible.
* `Rset_composant_aux`: the claim. For the inclusion `⊇`: a proper subcontinuum `P` of `Cl R(E)`
  through `x ∈ F` (an extension) gives the proper subcontinuum `A = P ∪ F ⊇ E`; extensions `K`, `Q`
  away from `X`, `Z` not inside `A` exist (step 8); of the three continua `A`, `K`, `Q` through a
  point of `X` one lies in the union of the other two (atriodicity), and since `K ∩ Q ⊆ E ⊆ A` it is
  `A`, so `A ⊆ K ∪ Q ⊆ R(E)`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Comp

variable {M : Set Pt}

/-- A continuum with a minimal admissible map is decomposable. -/
theorem not_indec_of_minimalAdmissible (hHU : IsHereditarilyUnicoherent (univ : Set M))
    {F : Set M} {d : F → unitInterval} (hF : IsMinimalAdmissible F d) :
    ¬ Fold.Q78.IsIndecomposable F := by
  intro hI
  obtain ⟨y₀, hy₀⟩ := hF.2.1.2.1 0
  obtain ⟨y₁, hy₁⟩ := hF.2.1.2.1 1
  exact false_of_indec_subset_layers hHU hI subset_rfl y₀ y₁ y₀.2 y₁.2
    (by rw [hy₀, hy₁]; exact zero_lt_one) hF

variable [CompactSpace M] [ConnectedSpace M]

/-- **Step 8 at the other end:** `Cl R(Z, E) = Cl R(E)`. -/
theorem closure_extUnion_one (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    closure (extUnion E (layer k 1)) = closure (Rset k) := by
  have h := closure_extUnion_aux hX hi hE.symm_comp
  rw [layer_symm_comp, unitInterval.symm_zero] at h
  have hR : Rset (unitInterval.symm ∘ k) = Rset k := by
    unfold Rset
    rw [layer_symm_comp, layer_symm_comp, unitInterval.symm_zero,
      unitInterval.symm_one, union_comm]
  rw [h, hR]

/-- **`R(X, E)` is not closed.** Otherwise `R(X, E) = Cl R(X, E)` is indecomposable (Lemma 6) and
is the union of the increasing proper subcontinua `Fᵢ` through a point `p` of `X`; a point lying in
no proper subcontinuum through `p` (`T13.exists_not_mem_proper_subcontinua`) is impossible. -/
theorem not_isClosed_extUnion (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ¬ IsClosed (extUnion E (layer k 0)) := by
  intro hRc
  obtain ⟨Fs, hmono, hFs, hRU⟩ := hagopian76_lemma4_seq hX hi hE
  have hI := lemma6_X_aux hX hi hE
  rw [hRc.closure_eq] at hI
  obtain ⟨p, hp⟩ := layer_nonempty hE.2.1.2.1 0
  have hpR : p ∈ extUnion E (layer k 0) :=
    IsExtensionAway.subset_extUnion (hFs 0) (IsExtensionAway.end_subset (hFs 0) hp)
  obtain ⟨b, hbR, hb⟩ := T13.exists_not_mem_proper_subcontinua hI hpR
  have hbR' := hbR
  rw [hRU] at hbR'
  obtain ⟨i, hbi⟩ := mem_iUnion.1 hbR'
  refine hb (Fs i) (IsExtensionAway.isContinuum (hFs i)) (IsExtensionAway.subset_extUnion (hFs i))
    ?_ (IsExtensionAway.end_subset (hFs i) hp) hbi
  intro heq
  have : Fs (i + 1) ⊆ Fs i := by
    rw [heq]; exact IsExtensionAway.subset_extUnion (hFs (i + 1))
  exact (hmono (Nat.lt_succ_self i)).not_ge this

/-- **Escape.** If a continuum `G` through a point of `F_{i₀}` is, inside `R(X, E)`, contained in no
`Fⱼ`, then `G ∪ F_{i₀}` contains `R(X, E)` (the interval lemma in a large `F_m`). -/
theorem subset_union_of_escape (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} {Fs : ℕ → Set M} (hmono : StrictMono Fs)
    (hFs : ∀ i, IsExtensionAway E (layer k 0) (Fs i)) (hRU : extUnion E (layer k 0) = ⋃ i, Fs i)
    {G : Set M} (hG : Fold.Q78.IsContinuum G) {g₀ : M} {i₀ : ℕ} (hg₀ : g₀ ∈ G)
    (hg₀i : g₀ ∈ Fs i₀) (hnot : ∀ j, ¬ (G ∩ extUnion E (layer k 0) ⊆ Fs j)) :
    extUnion E (layer k 0) ⊆ G ∪ Fs i₀ := by
  have hHU := hagopian75_lemma1_hu hX hi
  choose d hd hdX using fun i => (hFs i).2
  intro x hx
  by_cases hxi : x ∈ Fs i₀
  · exact Or.inr hxi
  left
  rw [hRU] at hx
  obtain ⟨j, hxj⟩ := mem_iUnion.1 hx
  obtain ⟨g₁, ⟨hg₁G, hg₁R⟩, hg₁j⟩ := not_subset.1 (hnot j)
  rw [hRU] at hg₁R
  obtain ⟨m₀, hg₁m⟩ := mem_iUnion.1 hg₁R
  set m := max (max i₀ j) m₀
  have hi₀m : Fs i₀ ⊆ Fs m := hmono.monotone (by omega)
  have hjm : Fs j ⊆ Fs m := hmono.monotone (by omega)
  have hm₀m : Fs m₀ ⊆ Fs m := hmono.monotone (by omega)
  obtain ⟨a, -, hsega, -⟩ :=
    hagopian76_initial_segment hX hi (hd i₀) (hd m) hi₀m ((hdX m).trans (hdX i₀).symm)
  obtain ⟨b, -, hsegb, -⟩ :=
    hagopian76_initial_segment hX hi (hd j) (hd m) hjm ((hdX m).trans (hdX j).symm)
  set x' : Fs m := ⟨x, hjm hxj⟩
  set g₀' : Fs m := ⟨g₀, hi₀m hg₀i⟩
  set g₁' : Fs m := ⟨g₁, hm₀m hg₁m⟩
  have hg₀a : d m g₀' ≤ a := by
    have : (g₀' : M) ∈ layerSet (d m) (Icc 0 a) := by rw [hsega]; exact hg₀i
    exact (mem_layerSet_val.1 this).2
  have hxa : a < d m x' := lt_of_not_ge fun h =>
    hxi (by rw [← hsega]; exact (mem_layerSet_val (y := x')).2 ⟨unitInterval.nonneg', h⟩)
  have hxb : d m x' ≤ b := by
    have : (x' : M) ∈ layerSet (d m) (Icc 0 b) := by rw [hsegb]; exact hxj
    exact (mem_layerSet_val.1 this).2
  have hg₁b : b < d m g₁' := lt_of_not_ge fun h =>
    hg₁j (by rw [← hsegb]; exact (mem_layerSet_val (y := g₁')).2 ⟨unitInterval.nonneg', h⟩)
  have hGm := isContinuum_inter_of_HU hHU hG (IsExtensionAway.isContinuum (hFs m))
    ⟨g₀, hg₀, g₀'.2⟩
  have hIoo := layerSet_Ioo_subset (hd m) inter_subset_right hGm
    ⟨g₀, ⟨hg₀, g₀'.2⟩, g₀', rfl, rfl⟩ ⟨g₁, ⟨hg₁G, g₁'.2⟩, g₁', rfl, rfl⟩
  exact (hIoo (mem_layerSet_val.2 ⟨lt_of_le_of_lt hg₀a hxa, lt_of_le_of_lt hxb hg₁b⟩)).1

/-- **A continuum in `R(X, E)` lies in one extension away from `X`.** -/
theorem exists_ext_of_subset (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {G : Set M}
    (hG : Fold.Q78.IsContinuum G) (hGR : G ⊆ extUnion E (layer k 0)) :
    ∃ F, IsExtensionAway E (layer k 0) F ∧ G ⊆ F := by
  obtain ⟨Fs, hmono, hFs, hRU⟩ := hagopian76_lemma4_seq hX hi hE
  by_contra hcon
  push_neg at hcon
  have hnot : ∀ j, ¬ (G ∩ extUnion E (layer k 0) ⊆ Fs j) := fun j h =>
    hcon _ (hFs j) (fun x hx => h ⟨hx, hGR hx⟩)
  obtain ⟨g₀, hg₀⟩ := hG.2.1
  have hg₀R := hGR hg₀
  rw [hRU] at hg₀R
  obtain ⟨i₀, hg₀i⟩ := mem_iUnion.1 hg₀R
  have hsub := subset_union_of_escape hX hi hmono hFs hRU hG hg₀ hg₀i hnot
  apply not_isClosed_extUnion hX hi hE
  have : extUnion E (layer k 0) = G ∪ Fs i₀ :=
    Subset.antisymm hsub (union_subset hGR (IsExtensionAway.subset_extUnion (hFs i₀)))
  rw [this]
  exact hG.1.isClosed.union (IsExtensionAway.isContinuum (hFs i₀)).1.isClosed

/-- **The two sides meet only in `E`.** An extension away from `X` and an extension away from `Z`
have intersection `E`. -/
theorem ext_inter_subset (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {K Q : Set M}
    (hK : IsExtensionAway E (layer k 0) K) (hQ : IsExtensionAway E (layer k 1) Q) :
    K ∩ Q ⊆ E := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  rintro q ⟨hqK, hqQ⟩
  by_contra hqE
  have hQc := IsExtensionAway.isContinuum hQ
  obtain ⟨hEQ, e, he, heZ⟩ := hQ
  have heZ' : layer e 0 = layer (unitInterval.symm ∘ k) 0 := by
    rw [layer_symm_comp, unitInterval.symm_zero]; exact heZ
  obtain ⟨σ, -, hseg, hlay⟩ := hagopian76_initial_segment hX hi hE.symm_comp he hEQ heZ'
  obtain ⟨u, hu⟩ := hlay 1
  have hXu : layer k 0 = layer e u := by
    rw [← hu, layer_symm_comp, unitInterval.symm_one]
  have hout : ∀ g : Q, (g : M) ∉ E → σ < e g := fun g hg => lt_of_not_ge fun h =>
    hg (by rw [← hseg]; exact mem_layerSet_val.2 ⟨unitInterval.nonneg', h⟩)
  have huσ : u ≤ σ := by
    obtain ⟨x, hx⟩ := layer_nonempty hE.2.1.2.1 0
    have hx' : x ∈ layer e u := by rw [← hXu]; exact hx
    obtain ⟨v, hv, hvx⟩ := hx'
    have hxE : x ∈ E := img_subset _ hx
    have : (v : M) ∈ layerSet e (Icc 0 σ) := by rw [hseg, hvx]; exact hxE
    have h' := (mem_layerSet_val.1 this).2
    rwa [show e v = u from hv] at h'
  have hQR : Q ⊆ extUnion E (layer k 0) := by
    intro g hgQ
    by_cases hgE : g ∈ E
    · exact IsExtensionAway.subset_extUnion ⟨subset_rfl, k, hE, rfl⟩ hgE
    set g' : Q := ⟨g, hgQ⟩
    set q' : Q := ⟨q, hqQ⟩
    set t := min (e g') (e q')
    have hσt : σ < t := lt_min (hout g' hgE) (hout q' hqE)
    have hG : Fold.Q78.IsContinuum (layerSet e (Icc t 1)) :=
      isContinuum_img hQc.1 he.2.1 isClosed_Icc isPreconnected_Icc ⟨1, unitInterval.le_one', le_rfl⟩
    have hGX : Disjoint (layerSet e (Icc t 1)) (layer k 0) := by
      rw [disjoint_left]
      rintro v ⟨v', hv', rfl⟩ hvX
      rw [hXu] at hvX
      obtain ⟨v'', hv'', hvv⟩ := hvX
      have : v'' = v' := Subtype.ext hvv
      subst this
      have h1 : e v'' = u := hv''
      have h2 := hv'.1
      rw [h1] at h2
      exact absurd (lt_of_le_of_lt huσ (lt_of_lt_of_le hσt h2)) (lt_irrefl _)
    have hqG : q ∈ layerSet e (Icc t 1) :=
      mem_layerSet_val.2 (show e q' ∈ Icc t 1 from ⟨min_le_right _ _, unitInterval.le_one'⟩)
    have hgG : g ∈ layerSet e (Icc t 1) :=
      mem_layerSet_val.2 (show e g' ∈ Icc t 1 from ⟨min_le_left _ _, unitInterval.le_one'⟩)
    exact subset_extUnion_of_meets hX hHU hAT hK hG hGX ⟨q, hqG, hqK⟩ hgG
  obtain ⟨F, hF, hQF⟩ := exists_ext_of_subset hX hi hE hQc hQR
  have hFc := IsExtensionAway.isContinuum hF
  obtain ⟨-, d, hd, hdX⟩ := hF
  obtain ⟨z, hz⟩ := hE.2.1.2.1 1
  obtain ⟨b, hb⟩ := he.2.1.2.1 1
  have hbE : (b : M) ∉ E := by
    intro hbE
    have : (b : M) ∈ layerSet e (Icc 0 σ) := by rw [hseg]; exact hbE
    have hσ1 : σ = 1 := by
      have h := (mem_layerSet_val.1 this).2
      rw [hb] at h
      exact le_antisymm unitInterval.le_one' h
    apply hqE
    rw [← hseg, hσ1]
    exact mem_layerSet_val.2 (show e ⟨q, hqQ⟩ ∈ Icc 0 1 from
      ⟨unitInterval.nonneg', unitInterval.le_one'⟩)
  have hzQ : (z : M) ∈ Q := hEQ z.2
  have hXd : ∀ v : F, (v : M) ∉ E → 0 < d v := by
    intro v hv
    refine lt_of_le_of_ne unitInterval.nonneg' fun h0 => hv ?_
    have : (v : M) ∈ layer k 0 := by rw [← hdX]; exact ⟨v, h0.symm, rfl⟩
    exact img_subset _ this
  have hzd : 0 < d ⟨z, hQF hzQ⟩ := by
    refine lt_of_le_of_ne unitInterval.nonneg' fun h0 => ?_
    have : (z : M) ∈ layer k 0 := by rw [← hdX]; exact ⟨⟨z, hQF hzQ⟩, h0.symm, rfl⟩
    obtain ⟨v, hv, hvz⟩ := this
    have : v = z := Subtype.ext hvz
    subst this
    exact zero_ne_one ((show k v = 0 from hv).symm.trans hz)
  have hbd : 0 < d ⟨b, hQF b.2⟩ := hXd _ hbE
  set τ := min (d ⟨z, hQF hzQ⟩) (d ⟨b, hQF b.2⟩)
  have hτ : 0 < τ := lt_min hzd hbd
  have hL : Fold.Q78.IsContinuum (layerSet d (Icc τ 1)) :=
    isContinuum_img hFc.1 hd.2.1 isClosed_Icc isPreconnected_Icc ⟨1, unitInterval.le_one', le_rfl⟩
  have hzL : (z : M) ∈ layerSet d (Icc τ 1) :=
    mem_layerSet_val.2 (show d ⟨z, hQF hzQ⟩ ∈ Icc τ 1 from ⟨min_le_left _ _, unitInterval.le_one'⟩)
  have hbL : (b : M) ∈ layerSet d (Icc τ 1) :=
    mem_layerSet_val.2 (show d ⟨b, hQF b.2⟩ ∈ Icc τ 1 from ⟨min_le_right _ _, unitInterval.le_one'⟩)
  have hY := isContinuum_inter_of_HU hHU hQc hL ⟨z, hzQ, hzL⟩
  have hYQ := end_sets_aux he inter_subset_left hY
    ⟨z, ⟨hzQ, hzL⟩, by rw [heZ]; exact ⟨z, hz, rfl⟩⟩ ⟨b, ⟨b.2, hbL⟩, b, hb, rfl⟩
  obtain ⟨x, hx⟩ := layer_nonempty hE.2.1.2.1 0
  have hxE : x ∈ E := img_subset _ hx
  have hxY : x ∈ Q ∩ layerSet d (Icc τ 1) := by rw [hYQ]; exact hEQ hxE
  set x' : F := ⟨x, hQF (hEQ hxE)⟩
  have hxd : d x' = 0 := mem_layer_val.1 (show (x' : M) ∈ layer d 0 by rw [hdX]; exact hx)
  have := (mem_layerSet_val.1 (show (x' : M) ∈ layerSet d (Icc τ 1) from hxY.2)).1
  rw [hxd] at this
  exact absurd (lt_of_lt_of_le hτ this) (lt_irrefl _)

/-- **"Since `M` is atriodic, `R(E)` is a composant of `Cl R(E)`."** -/
theorem Rset_composant_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {x : M} (hx : x ∈ Rset k) :
    Rset k = HPC.composant (closure (Rset k)) x := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  set I := closure (Rset k)
  have hI := lemma6_aux hX hi hE
  have hext : ∀ y ∈ Rset k, ∃ F, (IsExtensionAway E (layer k 0) F ∨
      IsExtensionAway E (layer k 1) F) ∧ y ∈ F := by
    rintro y (⟨F, hF, hyF⟩ | ⟨F, hF, hyF⟩)
    · exact ⟨F, Or.inl hF, hyF⟩
    · exact ⟨F, Or.inr hF, hyF⟩
  have hEF : ∀ F, (IsExtensionAway E (layer k 0) F ∨ IsExtensionAway E (layer k 1) F) →
      E ⊆ F ∧ F ⊆ Rset k ∧ Fold.Q78.IsContinuum F ∧ ¬ Fold.Q78.IsIndecomposable F := by
    rintro F (hF | hF)
    · refine ⟨hF.1, (IsExtensionAway.subset_extUnion hF).trans subset_union_left,
        IsExtensionAway.isContinuum hF, ?_⟩
      obtain ⟨-, d, hd, -⟩ := hF
      exact not_indec_of_minimalAdmissible hHU hd
    · refine ⟨hF.1, (IsExtensionAway.subset_extUnion hF).trans subset_union_right,
        IsExtensionAway.isContinuum hF, ?_⟩
      obtain ⟨-, d, hd, -⟩ := hF
      exact not_indec_of_minimalAdmissible hHU hd
  have hRI : Rset k ⊆ I := subset_closure
  obtain ⟨e₀, -⟩ := hE.2.1.2.1 0
  apply Subset.antisymm
  · intro y hy
    obtain ⟨F₁, hF₁, hxF₁⟩ := hext x hx
    obtain ⟨F₂, hF₂, hyF₂⟩ := hext y hy
    obtain ⟨hE₁, hR₁, hc₁, hn₁⟩ := hEF F₁ hF₁
    obtain ⟨hE₂, hR₂, hc₂, hn₂⟩ := hEF F₂ hF₂
    refine ⟨F₁ ∪ F₂, ⟨isContinuum_union hc₁ hc₂ ⟨e₀, hE₁ e₀.2, hE₂ e₀.2⟩,
      union_subset (hR₁.trans hRI) (hR₂.trans hRI), ?_, Or.inl hxF₁⟩, Or.inr hyF₂⟩
    intro heq
    rcases hI.2 F₁ F₂ hc₁ hc₂ (hR₁.trans hRI) (hR₂.trans hRI) heq with h | h
    · exact hn₁ (by rw [h]; exact hI)
    · exact hn₂ (by rw [h]; exact hI)
  · rintro y ⟨P, ⟨hP, hPI, hPne, hxP⟩, hyP⟩
    obtain ⟨F, hF, hxF⟩ := hext x hx
    obtain ⟨hEF', hFR, hFc, hFn⟩ := hEF F hF
    have hAc : Fold.Q78.IsContinuum (P ∪ F) := isContinuum_union hP hFc ⟨x, hxP, hxF⟩
    have hAI : P ∪ F ⊆ I := union_subset hPI (hFR.trans hRI)
    have hAne : P ∪ F ≠ I := by
      intro heq
      rcases hI.2 P F hP hFc hPI (hFR.trans hRI) heq with h | h
      · exact hPne h
      · exact hFn (by rw [h]; exact hI)
    have hEA : E ⊆ P ∪ F := hEF'.trans subset_union_right
    obtain ⟨K, hK, hKA⟩ : ∃ K, IsExtensionAway E (layer k 0) K ∧ ¬ K ⊆ P ∪ F := by
      by_contra h
      push_neg at h
      apply hAne
      apply Subset.antisymm hAI
      show closure (Rset k) ⊆ P ∪ F
      rw [← closure_extUnion_aux hX hi hE]
      exact closure_minimal (sUnion_subset fun K hK => h K hK) hAc.1.isClosed
    obtain ⟨Q, hQ, hQA⟩ : ∃ Q, IsExtensionAway E (layer k 1) Q ∧ ¬ Q ⊆ P ∪ F := by
      by_contra h
      push_neg at h
      apply hAne
      apply Subset.antisymm hAI
      show closure (Rset k) ⊆ P ∪ F
      rw [← closure_extUnion_one hX hi hE]
      exact closure_minimal (sUnion_subset fun Q hQ => h Q hQ) hAc.1.isClosed
    obtain ⟨p, -⟩ := hE.2.1.2.1 0
    rcases three_continua hHU hAT hAc (IsExtensionAway.isContinuum hK)
        (IsExtensionAway.isContinuum hQ) (hEA p.2) (hK.1 p.2) (hQ.1 p.2) with h | h | h
    · rcases h (Or.inl hyP) with h' | h'
      · exact Or.inl (IsExtensionAway.subset_extUnion hK h')
      · exact Or.inr (IsExtensionAway.subset_extUnion hQ h')
    · exfalso
      obtain ⟨w, hwK, hwA⟩ := not_subset.1 hKA
      rcases h hwK with h' | h'
      · exact hwA h'
      · exact hwA (hEA (ext_inter_subset hX hi hE hK hQ ⟨hwK, h'⟩))
    · exfalso
      obtain ⟨w, hwQ, hwA⟩ := not_subset.1 hQA
      rcases h hwQ with h' | h'
      · exact hwA h'
      · exact hwA (hEA (ext_inter_subset hX hi hE hK hQ ⟨h', hwQ⟩))

end Comp

end HPC.Hagopian
