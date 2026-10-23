import HPC.Hagopian.Hagopian76F

/-!
# Batch 162, item A: half-ray density

Hagopian 1976, p. 343 (Lemma 7). For a continuum `G` essential to `R(E)` with its minimal map `d`
and an interior layer `d⁻¹(u)`, the two "half-rays" of the composant from `d⁻¹(u)` are each dense in
`Cl R(E)` (`halfray_dense_aux`), and they meet only in `d⁻¹(u)` (`halfray_inter_subset`).

* `piece_end_layers`: on a piece `P = d⁻¹[[a, b]]` of a type A′ continuum with continuous
  decomposition, **every** minimal admissible map has end layers `d⁻¹(a)`, `d⁻¹(b)` (in some order);
  `piece_map`: such a map exists; `Rset_eq_of_maps`: `R(·)` does not depend on the map.
* `extUnion_eq_of_subset`: if `Q ⊇ P` has the same layer over `0`, then `R(X, P) = R(X, Q)` (the
  extensions away from `X` form a chain, `ext_chain`).
* `closure_Rset_piece`: `Cl R(P) = Cl R(G)` for a piece `P` of `G`;
  `closure_Rset_of_common`: two type A′ continua sharing a continuum that meets two layers of each
  have the same `Cl R(·)`;
* `closure_Rset_essential`: `Cl R(G) = Cl R(E)` for `G` essential to `R(E)` (the cases
  `G ⊆ R(X, E)`, `G ⊆ R(Z, E)`, and the two-sided case of `essential_typeA'_two_sided`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Piece

variable {X : Type*} [MetricSpace X]

/-- **End layers on a piece.** Every minimal admissible map `p` of the piece `P = d⁻¹[[a, b]]` has
end layers `d⁻¹(a)`, `d⁻¹(b)`, in one order or the other. -/
theorem piece_end_layers {G : Set X} [CompactSpace G] {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hL : ∀ x, LSCAt (Setoid.ker d) x) {a b : unitInterval}
    (hab : a < b) {P : Set X} (hP : P = layerSet d (Icc a b)) {p : P → unitInterval}
    (hp : IsMinimalAdmissible P p) :
    (layer p 0 = layer d a ∧ layer p 1 = layer d b) ∨
      (layer p 0 = layer d b ∧ layer p 1 = layer d a) := by
  subst hP
  have hPG : layerSet d (Icc a b) ⊆ G := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hd := hG.2.1
  have hGc := hG.isCompact
  have hdpiece : ∀ c c' : unitInterval, a ≤ c → c ≤ c' → c' ≤ b →
      Fold.Q78.IsContinuum (layerSet d (Icc c c')) ∧ layerSet d (Icc c c') ⊆ layerSet d (Icc a b) :=
    fun c c' h1 h2 h3 =>
    ⟨isContinuum_img hGc hd isClosed_Icc isPreconnected_Icc ⟨c, le_rfl, h2⟩,
     by rintro _ ⟨y, hy, rfl⟩; exact ⟨y, ⟨h1.trans hy.1, hy.2.trans h3⟩, rfl⟩⟩
  have hA : ∀ K ⊆ layerSet d (Icc a b), Fold.Q78.IsContinuum K → (K ∩ layer d a).Nonempty →
      (K ∩ layer d b).Nonempty → K = layerSet d (Icc a b) := fun K hK hKc ha hb =>
    eq_layerSet_of_subcontinuum hG hL (hK.trans hPG) hKc hab ha hb hK
  -- the two points
  obtain ⟨x₀, hx₀⟩ := hd.2.1 a
  obtain ⟨z₀, hz₀⟩ := hd.2.1 b
  have hxP : (x₀ : X) ∈ layerSet d (Icc a b) := ⟨x₀, by rw [mem_preimage, hx₀]; exact ⟨le_rfl, hab.le⟩, rfl⟩
  have hzP : (z₀ : X) ∈ layerSet d (Icc a b) := ⟨z₀, by rw [mem_preimage, hz₀]; exact ⟨hab.le, le_rfl⟩, rfl⟩
  set x : layerSet d (Icc a b) := ⟨x₀, hxP⟩
  set z : layerSet d (Icc a b) := ⟨z₀, hzP⟩
  have hxa : (x : X) ∈ layer d a := ⟨x₀, hx₀, rfl⟩
  have hzb : (z : X) ∈ layer d b := ⟨z₀, hz₀, rfl⟩
  -- the parameter in `G` of a point of the piece
  have hparam : ∀ w : layerSet d (Icc a b), ∃ g : G, (g : X) = w ∧ d g ∈ Icc a b := by
    rintro ⟨_, g, hg, rfl⟩; exact ⟨g, rfl, hg⟩
  -- the main step, for a map with `q x = 0`, `q z = 1`
  have main : ∀ q : layerSet d (Icc a b) → unitInterval, IsMinimalAdmissible _ q → q x = 0 →
      q z = 1 → layer q 0 = layer d a ∧ layer q 1 = layer d b := by
    intro q hq hqx hqz
    have hqc := hq.isCompact
    have hqpiece : ∀ c c' : unitInterval, c ≤ c' → Fold.Q78.IsContinuum (layerSet q (Icc c c')) ∧
        layerSet q (Icc c c') ⊆ layerSet d (Icc a b) := fun c c' h =>
      ⟨isContinuum_img hqc hq.2.1 isClosed_Icc isPreconnected_Icc ⟨c, le_rfl, h⟩,
       by rintro _ ⟨y, -, rfl⟩; exact y.2⟩
    have hB : ∀ K ⊆ layerSet d (Icc a b), Fold.Q78.IsContinuum K → (K ∩ layer q 0).Nonempty →
        (K ∩ layer q 1).Nonempty → K = layerSet d (Icc a b) := fun K hK hKc h0 h1 =>
      end_sets_aux hq hK hKc h0 h1
    have hmemq : ∀ (w : layerSet d (Icc a b)) (S : Set unitInterval), (w : X) ∈ layerSet q S →
        q w ∈ S := by
      rintro w S ⟨w', hw', hww'⟩
      rw [← Subtype.ext hww']; exact hw'
    have hmemd : ∀ (g : G) (S : Set unitInterval), (g : X) ∈ layerSet d S → d g ∈ S := by
      rintro g S ⟨g', hg', hgg'⟩
      rw [← Subtype.ext hgg']; exact hg'
    refine ⟨Subset.antisymm ?_ ?_, Subset.antisymm ?_ ?_⟩
    · -- `q⁻¹(0) ⊆ d⁻¹(a)`
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨g, hgw, hg⟩ := hparam w
      by_contra hne
      have hlt : a < d g := lt_of_le_of_ne hg.1 fun h => hne (by rw [← hgw]; exact ⟨g, h.symm, rfl⟩)
      obtain ⟨hKc, hKP⟩ := hdpiece (d g) b hlt.le hg.2 le_rfl
      have hK := hB _ hKP hKc ⟨w, by rw [← hgw]; exact ⟨g, ⟨le_rfl, hg.2⟩, rfl⟩, w, hw, rfl⟩
        ⟨z, ⟨z₀, by rw [mem_preimage, hz₀]; exact ⟨hg.2, le_rfl⟩, rfl⟩, z, hqz, rfl⟩
      have : (x₀ : X) ∈ layerSet d (Icc (d g) b) := by rw [hK]; exact hxP
      have := (hmemd x₀ _ this).1
      rw [hx₀] at this
      exact absurd hlt (not_lt.2 this)
    · -- `d⁻¹(a) ⊆ q⁻¹(0)`
      rintro _ ⟨g, hg, rfl⟩
      have hgP : (g : X) ∈ layerSet d (Icc a b) := ⟨g, by rw [mem_preimage, hg]; exact ⟨le_rfl, hab.le⟩, rfl⟩
      set w : layerSet d (Icc a b) := ⟨g, hgP⟩
      by_contra hne
      have hlt : 0 < q w := lt_of_le_of_ne unitInterval.nonneg' fun h => hne ⟨w, h.symm, rfl⟩
      obtain ⟨hKc, hKP⟩ := hqpiece (q w) 1 unitInterval.le_one'
      have hK := hA _ hKP hKc ⟨w, ⟨w, ⟨le_rfl, unitInterval.le_one'⟩, rfl⟩, g, hg, rfl⟩
        ⟨z, ⟨z, by rw [mem_preimage, hqz]; exact ⟨unitInterval.le_one', le_rfl⟩, rfl⟩, hzb⟩
      have : (x : X) ∈ layerSet q (Icc (q w) 1) := by rw [hK]; exact hxP
      have := (hmemq x _ this).1
      rw [hqx] at this
      exact absurd hlt (not_lt.2 this)
    · -- `q⁻¹(1) ⊆ d⁻¹(b)`
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨g, hgw, hg⟩ := hparam w
      by_contra hne
      have hlt : d g < b := lt_of_le_of_ne hg.2 fun h => hne (by rw [← hgw]; exact ⟨g, h, rfl⟩)
      obtain ⟨hKc, hKP⟩ := hdpiece a (d g) le_rfl hg.1 hlt.le
      have hK := hB _ hKP hKc ⟨x, ⟨x₀, by rw [mem_preimage, hx₀]; exact ⟨le_rfl, hg.1⟩, rfl⟩, x, hqx, rfl⟩
        ⟨w, by rw [← hgw]; exact ⟨g, ⟨hg.1, le_rfl⟩, rfl⟩, w, hw, rfl⟩
      have : (z₀ : X) ∈ layerSet d (Icc a (d g)) := by rw [hK]; exact hzP
      have := (hmemd z₀ _ this).2
      rw [hz₀] at this
      exact absurd hlt (not_lt.2 this)
    · -- `d⁻¹(b) ⊆ q⁻¹(1)`
      rintro _ ⟨g, hg, rfl⟩
      have hgP : (g : X) ∈ layerSet d (Icc a b) := ⟨g, by rw [mem_preimage, hg]; exact ⟨hab.le, le_rfl⟩, rfl⟩
      set w : layerSet d (Icc a b) := ⟨g, hgP⟩
      by_contra hne
      have hlt : q w < 1 := lt_of_le_of_ne unitInterval.le_one' fun h => hne ⟨w, h, rfl⟩
      obtain ⟨hKc, hKP⟩ := hqpiece 0 (q w) unitInterval.nonneg'
      have hK := hA _ hKP hKc ⟨x, ⟨x, by rw [mem_preimage, hqx]; exact ⟨le_rfl, unitInterval.nonneg'⟩, rfl⟩, hxa⟩
        ⟨w, ⟨w, ⟨unitInterval.nonneg', le_rfl⟩, rfl⟩, g, hg, rfl⟩
      have : (z : X) ∈ layerSet q (Icc 0 (q w)) := by rw [hK]; exact hzP
      have := (hmemq z _ this).2
      rw [hqz] at this
      exact absurd hlt (not_lt.2 this)
  -- `{p x, p z} = {0, 1}`
  have hpc := hp.isCompact
  set α := p x
  set β := p z
  obtain ⟨hKc, -⟩ : Fold.Q78.IsContinuum (layerSet p (Icc (min α β) (max α β))) ∧ True :=
    ⟨isContinuum_img hpc hp.2.1 isClosed_Icc isPreconnected_Icc ⟨min α β, le_rfl,
      min_le_max⟩, trivial⟩
  have hKP : layerSet p (Icc (min α β) (max α β)) ⊆ layerSet d (Icc a b) := by
    rintro _ ⟨y, -, rfl⟩; exact y.2
  have hK := hA _ hKP hKc ⟨x, ⟨x, ⟨min_le_left _ _, le_max_left _ _⟩, rfl⟩, hxa⟩
    ⟨z, ⟨z, ⟨min_le_right _ _, le_max_right _ _⟩, rfl⟩, hzb⟩
  have hall : ∀ w, p w ∈ Icc (min α β) (max α β) := by
    intro w
    have : (w : X) ∈ layerSet p (Icc (min α β) (max α β)) := by rw [hK]; exact w.2
    obtain ⟨w', hw', hww'⟩ := this
    rw [← Subtype.ext hww']; exact hw'
  obtain ⟨w0, hw0⟩ := hp.2.1.2.1 0
  obtain ⟨w1, hw1⟩ := hp.2.1.2.1 1
  have hmin : min α β = 0 := le_antisymm (hw0 ▸ (hall w0).1) unitInterval.nonneg'
  have hmax : max α β = 1 := le_antisymm unitInterval.le_one' (hw1 ▸ (hall w1).2)
  have hab' : (α = 0 ∧ β = 1) ∨ (α = 1 ∧ β = 0) := by
    rcases le_total α β with h | h
    · left; rw [min_eq_left h] at hmin; rw [max_eq_right h] at hmax; exact ⟨hmin, hmax⟩
    · right; rw [min_eq_right h] at hmin; rw [max_eq_left h] at hmax; exact ⟨hmax, hmin⟩
  rcases hab' with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · exact Or.inl (main p hp h0 h1)
  · have := main (unitInterval.symm ∘ p) hp.symm_comp
      (by simp only [Function.comp_apply]; rw [show p x = 1 from h1, unitInterval.symm_one])
      (by simp only [Function.comp_apply]; rw [show p z = 0 from h0, unitInterval.symm_zero])
    rw [layer_symm_comp, layer_symm_comp, unitInterval.symm_zero, unitInterval.symm_one] at this
    exact Or.inr ⟨this.2, this.1⟩

/-- **A piece carries a minimal admissible map with the expected end layers.** -/
theorem piece_map {G : Set X} [CompactSpace G] {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hL : ∀ x, LSCAt (Setoid.ker d) x) {a b : unitInterval}
    (hab : a < b) {P : Set X} (hP : P = layerSet d (Icc a b)) :
    ∃ p : P → unitInterval, IsMinimalAdmissible P p ∧ layer p 0 = layer d a ∧
      layer p 1 = layer d b := by
  subst hP
  have hd := hG.2.1
  have hHc : Fold.Q78.IsContinuum (layerSet d (Icc a b)) :=
    isContinuum_img hG.isCompact hd isClosed_Icc isPreconnected_Icc ⟨a, le_rfl, hab.le⟩
  have hHG : layerSet d (Icc a b) ⊆ G := by rintro _ ⟨y, -, rfl⟩; exact y.2
  obtain ⟨x₀, hx₀⟩ := hd.2.1 a
  obtain ⟨z₀, hz₀⟩ := hd.2.1 b
  obtain ⟨-, -, -, -, ⟨hirr, k₀, hk₀, hk₀0⟩⟩ := isTypeA'_of_subcontinuum hG hL hHG hHc hab.ne
    ⟨x₀, ⟨x₀, by rw [mem_preimage, hx₀]; exact ⟨le_rfl, hab.le⟩, rfl⟩, x₀, hx₀, rfl⟩
    ⟨z₀, ⟨z₀, by rw [mem_preimage, hz₀]; exact ⟨hab.le, le_rfl⟩, rfl⟩, z₀, hz₀, rfl⟩
  have hk : IsMinimalAdmissible (layerSet d (Icc a b)) k₀ := ⟨hirr, hk₀, hk₀0⟩
  rcases piece_end_layers hG hL hab rfl hk with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact ⟨k₀, hk, h0, h1⟩
  · refine ⟨unitInterval.symm ∘ k₀, hk.symm_comp, ?_, ?_⟩
    · rw [layer_symm_comp, unitInterval.symm_zero, h1]
    · rw [layer_symm_comp, unitInterval.symm_one, h0]

end Piece

section Ray

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **`R(·)` does not depend on the minimal admissible map.** -/
theorem Rset_eq_of_maps (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {P : Set M}
    {p q : P → unitInterval} (hp : IsMinimalAdmissible P p) (hq : IsMinimalAdmissible P q) :
    Rset p = Rset q := by
  haveI : CompactSpace P := isCompact_iff_compactSpace.mp hp.isCompact
  have hL := lsc_of_minimalAdmissible hX hi hp
  have hP : P = layerSet p (Icc 0 1) := by
    ext x
    constructor
    · intro hx; exact ⟨⟨x, hx⟩, ⟨unitInterval.nonneg', unitInterval.le_one'⟩, rfl⟩
    · rintro ⟨y, -, rfl⟩; exact y.2
  rcases piece_end_layers hp hL zero_lt_one hP hq with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · unfold Rset; rw [h0, h1]
  · unfold Rset; rw [h0, h1, union_comm]

omit [CompactSpace M] [ConnectedSpace M] in
/-- **Same end, larger continuum, same extensions.** -/
theorem extUnion_eq_of_subset (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {P Q : Set M} {p : P → unitInterval} {q : Q → unitInterval}
    (hp : IsMinimalAdmissible P p) (hq : IsMinimalAdmissible Q q) (hPQ : P ⊆ Q)
    (h0 : layer q 0 = layer p 0) : extUnion P (layer p 0) = extUnion Q (layer q 0) := by
  ext x
  constructor
  · rintro ⟨K, hK, hxK⟩
    have hQext : IsExtensionAway P (layer p 0) Q := ⟨hPQ, q, hq, h0⟩
    rcases ext_chain hHU hAT hp hK hQext with h | h
    · exact ⟨Q, ⟨subset_rfl, q, hq, rfl⟩, h hxK⟩
    · obtain ⟨-, e, he, heX⟩ := hK
      exact ⟨K, ⟨h, e, he, heX.trans h0.symm⟩, hxK⟩
  · rintro ⟨K, ⟨hQK, e, he, heX⟩, hxK⟩
    exact ⟨K, ⟨hPQ.trans hQK, e, he, heX.trans h0⟩, hxK⟩

/-- `Cl R(P) = Cl R(Q)` for `P ⊆ Q` with the same layer over `0`. -/
theorem closure_Rset_eq_of_subset (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P Q : Set M} {p : P → unitInterval} {q : Q → unitInterval}
    (hp : IsMinimalAdmissible P p) (hq : IsMinimalAdmissible Q q) (hPQ : P ⊆ Q)
    (h0 : layer q 0 = layer p 0) : closure (Rset p) = closure (Rset q) := by
  rw [← closure_extUnion_aux hX hi hp, ← closure_extUnion_aux hX hi hq,
    extUnion_eq_of_subset (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hp hq hPQ h0]

/-- **`Cl R(P) = Cl R(G)` for a piece `P = d⁻¹[[a, b]]` of `G`.** -/
theorem closure_Rset_piece (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {G : Set M}
    {d : G → unitInterval} (hd : IsMinimalAdmissible G d) {a b : unitInterval} (hab : a < b)
    {P : Set M} (hP : P = layerSet d (Icc a b)) {p : P → unitInterval}
    (hp : IsMinimalAdmissible P p) (hp1 : layer p 1 = layer d b) :
    closure (Rset p) = closure (Rset d) := by
  haveI : CompactSpace G := isCompact_iff_compactSpace.mp hd.isCompact
  have hL := lsc_of_minimalAdmissible hX hi hd
  have hb0 : 0 < b := lt_of_le_of_lt unitInterval.nonneg' hab
  obtain ⟨q, hq, hq0, hq1⟩ := piece_map hd hL hb0 (P := layerSet d (Icc 0 b)) rfl
  have hPQ : P ⊆ layerSet d (Icc 0 b) := by
    rw [hP]; rintro _ ⟨y, hy, rfl⟩; exact ⟨y, ⟨unitInterval.nonneg', hy.2⟩, rfl⟩
  have hQG : layerSet d (Icc 0 b) ⊆ G := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have h1 : closure (Rset (unitInterval.symm ∘ p)) = closure (Rset (unitInterval.symm ∘ q)) := by
    refine closure_Rset_eq_of_subset hX hi hp.symm_comp hq.symm_comp hPQ ?_
    rw [layer_symm_comp, layer_symm_comp, unitInterval.symm_zero, hq1, hp1]
  have h2 : closure (Rset q) = closure (Rset d) :=
    closure_Rset_eq_of_subset hX hi hq hd hQG hq0.symm
  rw [Rset_symm_comp, Rset_symm_comp] at h1
  rw [h1, h2]

/-- **A common piece.** If a continuum `J` lies in `G` and in `K` and meets two layers of each,
then `Cl R(G) = Cl R(K)`. -/
theorem closure_Rset_of_common (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {G K J : Set M} {d : G → unitInterval} {e : K → unitInterval} (hd : IsMinimalAdmissible G d)
    (he : IsMinimalAdmissible K e) (hJG : J ⊆ G) (hJK : J ⊆ K) (hJ : Fold.Q78.IsContinuum J)
    {t₁ t₂ : unitInterval} (ht : t₁ ≠ t₂) (h₁ : (J ∩ layer d t₁).Nonempty)
    (h₂ : (J ∩ layer d t₂).Nonempty) {s₁ s₂ : unitInterval} (hs : s₁ ≠ s₂)
    (h₁' : (J ∩ layer e s₁).Nonempty) (h₂' : (J ∩ layer e s₂).Nonempty) :
    closure (Rset d) = closure (Rset e) := by
  haveI : CompactSpace G := isCompact_iff_compactSpace.mp hd.isCompact
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp he.isCompact
  have hLd := lsc_of_minimalAdmissible hX hi hd
  have hLe := lsc_of_minimalAdmissible hX hi he
  obtain ⟨a, b, hab, hJd, -⟩ := isTypeA'_of_subcontinuum hd hLd hJG hJ ht h₁ h₂
  obtain ⟨a', b', hab', hJe, -⟩ := isTypeA'_of_subcontinuum he hLe hJK hJ hs h₁' h₂'
  obtain ⟨p, hp, -, hp1⟩ := piece_map hd hLd hab hJd
  obtain ⟨q, hq, -, hq1⟩ := piece_map he hLe hab' hJe
  rw [← closure_Rset_piece hX hi hd hab hJd hp hp1, ← closure_Rset_piece hX hi he hab' hJe hq hq1,
    Rset_eq_of_maps hX hi hp hq]

/-- **`Cl R(G) = Cl R(E)` for a continuum `G` essential to `R(E)`.** -/
theorem closure_Rset_essential (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {G : Set M} (hG : IsEssential k G)
    {d : G → unitInterval} (hd : IsMinimalAdmissible G d) :
    closure (Rset d) = closure (Rset k) := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  have hlayer_ne : ∀ {Y : Set M} {g : Y → unitInterval}, IsMinimalAdmissible Y g →
      ∀ {a b : unitInterval}, layer g a = layer g b → a = b := by
    intro Y g hg a b hab
    obtain ⟨y, hy⟩ := layer_nonempty hg.2.1.2.1 a
    exact layer_param_eq hy (hab ▸ hy)
  have hG01 : (G ∩ layer d 0).Nonempty ∧ (G ∩ layer d 1).Nonempty := by
    obtain ⟨x, hx⟩ := layer_nonempty hd.2.1.2.1 0
    obtain ⟨y, hy⟩ := layer_nonempty hd.2.1.2.1 1
    exact ⟨⟨x, img_subset _ hx, hx⟩, ⟨y, img_subset _ hy, hy⟩⟩
  have h01 : (0 : unitInterval) ≠ 1 := fun h => by
    have := congrArg Subtype.val h; norm_num at this
  -- the one-sided case, for `k` or its reverse
  have one : ∀ {k' : E → unitInterval}, IsMinimalAdmissible E k' → IsEssential k' G →
      G ⊆ extUnion E (layer k' 0) → closure (Rset d) = closure (Rset k') := by
    intro k' hE' hG' hsub
    obtain ⟨-, hGc, F, dF, hEF, hdF, hdFX, t₁, t₂, ht, h₁, h₂⟩ := hG'
    obtain ⟨G₀, hG₀, hGG₀⟩ := exists_ext_of_subset hX hi hE' hGc hsub
    obtain ⟨G', hGG', hEG', dG, hdG, hdGX, u₁, u₂, hu, hu₁, hu₂⟩ : ∃ G' : Set M, G ⊆ G' ∧
        E ⊆ G' ∧ ∃ dG : G' → unitInterval, IsMinimalAdmissible G' dG ∧ layer dG 0 = layer k' 0 ∧
        ∃ u₁ u₂ : unitInterval, u₁ ≠ u₂ ∧ (G ∩ layer dG u₁).Nonempty ∧
          (G ∩ layer dG u₂).Nonempty := by
      rcases hdFX with hdFX | hdFX
      · obtain ⟨G', hG', hFG', hGG'⟩ := ext_upper hX hi hE' ⟨hEF, dF, hdF, hdFX⟩ hG₀
        obtain ⟨hEG', dG, hdG, hdGX⟩ := hG'
        obtain ⟨-, -, -, hlay⟩ := hagopian76_initial_segment hX hi hdF hdG hFG'
          (hdGX.trans hdFX.symm)
        obtain ⟨u₁, hu₁⟩ := hlay t₁
        obtain ⟨u₂, hu₂⟩ := hlay t₂
        refine ⟨G', hGG₀.trans hGG', hEG', dG, hdG, hdGX, u₁, u₂, fun h => ht ?_, hu₁ ▸ h₁,
          hu₂ ▸ h₂⟩
        exact hlayer_ne hdF (hu₁.trans (h ▸ hu₂.symm))
      · obtain ⟨p₁, hp₁H, hp₁⟩ := h₁
        obtain ⟨p₂, hp₂H, hp₂⟩ := h₂
        have hp₁E : p₁ ∈ E := ext_inter_subset hX hi hE' hG₀ ⟨hEF, dF, hdF, hdFX⟩
          ⟨hGG₀ hp₁H, img_subset _ hp₁⟩
        have hp₂E : p₂ ∈ E := ext_inter_subset hX hi hE' hG₀ ⟨hEF, dF, hdF, hdFX⟩
          ⟨hGG₀ hp₂H, img_subset _ hp₂⟩
        have hdX' : layer dF 0 = layer (unitInterval.symm ∘ k') 0 := by
          rw [layer_symm_comp, unitInterval.symm_zero]; exact hdFX
        obtain ⟨-, -, -, hlayF⟩ := hagopian76_initial_segment hX hi hE'.symm_comp hdF hEF hdX'
        have hk12 : k' ⟨p₁, hp₁E⟩ ≠ k' ⟨p₂, hp₂E⟩ := by
          intro hkeq
          obtain ⟨v, hv⟩ := hlayF (unitInterval.symm (k' ⟨p₁, hp₁E⟩))
          rw [layer_symm_comp, unitInterval.symm_symm] at hv
          have hq₁ : p₁ ∈ layer dF v := by rw [← hv]; exact ⟨⟨p₁, hp₁E⟩, rfl, rfl⟩
          have hq₂ : p₂ ∈ layer dF v := by rw [← hv, hkeq]; exact ⟨⟨p₂, hp₂E⟩, rfl, rfl⟩
          exact ht ((layer_param_eq hp₁ hq₁).trans (layer_param_eq hq₂ hp₂))
        obtain ⟨hEG, dG, hdG, hdGX⟩ := hG₀
        obtain ⟨-, -, -, hlay⟩ := hagopian76_initial_segment hX hi hE' hdG hEG hdGX
        obtain ⟨u₁, hu₁⟩ := hlay (k' ⟨p₁, hp₁E⟩)
        obtain ⟨u₂, hu₂⟩ := hlay (k' ⟨p₂, hp₂E⟩)
        refine ⟨G₀, hGG₀, hEG, dG, hdG, hdGX, u₁, u₂, fun h => hk12 ?_, ⟨p₁, hp₁H, ?_⟩,
          ⟨p₂, hp₂H, ?_⟩⟩
        · exact hlayer_ne hE' (hu₁.trans (h ▸ hu₂.symm))
        · rw [← hu₁]; exact ⟨⟨p₁, hp₁E⟩, rfl, rfl⟩
        · rw [← hu₂]; exact ⟨⟨p₂, hp₂E⟩, rfl, rfl⟩
    rw [closure_Rset_of_common hX hi hd hdG subset_rfl hGG' hGc h01 hG01.1 hG01.2 hu hu₁ hu₂,
      closure_Rset_eq_of_subset hX hi hE' hdG hEG' hdGX]
  by_cases hX0 : G ⊆ extUnion E (layer k 0)
  · exact one hE hG hX0
  by_cases hX1 : G ⊆ extUnion E (layer k 1)
  · have h := hX1
    rw [← unitInterval.symm_zero, ← layer_symm_comp] at h
    rw [one hE.symm_comp hG.symm_comp h, Rset_symm_comp]
  -- the two-sided case
  obtain ⟨hHR, hHc, -⟩ := hG
  have hEc : Fold.Q78.IsContinuum E := by
    obtain ⟨⟨a, b, hab⟩, -, -⟩ := hE; exact hab.1
  set k' := unitInterval.symm ∘ k with hk'
  have hE' : IsMinimalAdmissible E k' := hE.symm_comp
  have hk'0 : layer k' 0 = layer k 1 := by rw [layer_symm_comp, unitInterval.symm_zero]
  have hHX : (G ∩ layer k 0).Nonempty := by
    by_contra hdis
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hdis
    obtain ⟨h, hhH, hhX⟩ : ∃ h ∈ G, h ∈ extUnion E (layer k 0) := by
      by_contra hn; push_neg at hn
      exact hX1 fun y hy => (hHR hy).resolve_left (hn y hy)
    obtain ⟨K, hK, hhK⟩ := hhX
    exact hX0 (subset_extUnion_of_meets hX hHU hAT hK hHc hdis ⟨h, hhH, hhK⟩)
  have hHZ : (G ∩ layer k 1).Nonempty := by
    by_contra hdis
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hdis
    obtain ⟨x₀, hx₀H, hx₀X⟩ := hHX
    have hEZ : IsExtensionAway E (layer k' 0) E := ⟨subset_rfl, k', hE', rfl⟩
    have := subset_extUnion_of_meets hX hHU hAT hEZ hHc (by rw [hk'0]; exact hdis)
      ⟨x₀, hx₀H, img_subset _ hx₀X⟩
    rw [hk'0] at this
    exact hX1 this
  have hEH : E ⊆ G := by
    obtain ⟨x₀, hx₀H, hx₀X⟩ := hHX
    obtain ⟨z₀, hz₀H, hz₀Z⟩ := hHZ
    have hHE := isContinuum_inter_of_HU hHU hHc hEc ⟨x₀, hx₀H, img_subset _ hx₀X⟩
    have := end_sets_aux hE inter_subset_right hHE ⟨x₀, ⟨hx₀H, img_subset _ hx₀X⟩, hx₀X⟩
      ⟨z₀, ⟨hz₀H, img_subset _ hz₀Z⟩, hz₀Z⟩
    rw [← this]; exact inter_subset_left
  obtain ⟨K, hK, hHK⟩ := exists_ext_cover hX hi hE hHc hHR hHX
  obtain ⟨Q, hQ', hHQ'⟩ := exists_ext_cover hX hi hE' hHc (by rw [Rset_symm_comp]; exact hHR)
    (by rw [hk'0]; exact hHZ)
  have hHKQ : G ⊆ K ∪ Q := by
    intro y hy
    rcases hHR hy with h | h
    · exact Or.inl (hHK ⟨hy, h⟩)
    · exact Or.inr (hHQ' ⟨hy, by rw [hk'0]; exact h⟩)
  have hKc := IsExtensionAway.isContinuum hK
  have hQc := IsExtensionAway.isContinuum hQ'
  have hQR := IsExtensionAway.subset_extUnion hQ'
  have hKR := IsExtensionAway.subset_extUnion hK
  rw [hk'0] at hQR
  obtain ⟨hEK, dK, hdK, hdKX⟩ := hK
  obtain ⟨hEQ, e, he, heZ⟩ := hQ'
  obtain ⟨b₀, hb₀H, hb₀E⟩ : ∃ b₀ ∈ G ∩ K, b₀ ∉ E := by
    by_contra hn; push_neg at hn
    apply hX1
    intro y hy
    rcases hHKQ hy with h | h
    · exact hQR (hEQ (hn y ⟨hy, h⟩))
    · exact hQR h
  obtain ⟨a₀, ha₀H, ha₀E⟩ : ∃ a₀ ∈ G ∩ Q, a₀ ∉ E := by
    by_contra hn; push_neg at hn
    apply hX0
    intro y hy
    rcases hHKQ hy with h | h
    · exact hKR h
    · exact hKR (hEK (hn y ⟨hy, h⟩))
  obtain ⟨x, hx⟩ := layer_nonempty hE.2.1.2.1 0
  obtain ⟨z, hz⟩ := layer_nonempty hE.2.1.2.1 1
  have hxE : x ∈ E := img_subset _ hx
  have hzE : z ∈ E := img_subset _ hz
  -- `G ∩ K` meets two layers of `K`
  have hJc := isContinuum_inter_of_HU hHU hHc hKc ⟨b₀, hb₀H⟩
  have hJ0 : (G ∩ K ∩ layer dK 0).Nonempty := ⟨x, ⟨hEH hxE, hEK hxE⟩, by rw [hdKX]; exact hx⟩
  have hJb : (G ∩ K ∩ layer dK (dK ⟨b₀, hb₀H.2⟩)).Nonempty := ⟨b₀, hb₀H, ⟨b₀, hb₀H.2⟩, rfl, rfl⟩
  have hb0 : (0 : unitInterval) ≠ dK ⟨b₀, hb₀H.2⟩ := fun h => hb₀E (by
    have : b₀ ∈ layer dK 0 := ⟨⟨b₀, hb₀H.2⟩, h.symm, rfl⟩
    rw [hdKX] at this; exact img_subset _ this)
  -- `G ∩ Q` meets two layers of `Q`
  have hJ'c := isContinuum_inter_of_HU hHU hHc hQc ⟨a₀, ha₀H⟩
  have hJ'0 : (G ∩ Q ∩ layer e 0).Nonempty := ⟨z, ⟨hEH hzE, hEQ hzE⟩, by rw [heZ, hk'0]; exact hz⟩
  have hJ'a : (G ∩ Q ∩ layer e (e ⟨a₀, ha₀H.2⟩)).Nonempty := ⟨a₀, ha₀H, ⟨a₀, ha₀H.2⟩, rfl, rfl⟩
  have ha0 : (0 : unitInterval) ≠ e ⟨a₀, ha₀H.2⟩ := fun h => ha₀E (by
    have : a₀ ∈ layer e 0 := ⟨⟨a₀, ha₀H.2⟩, h.symm, rfl⟩
    rw [heZ] at this; exact img_subset _ this)
  have hRK : closure (Rset k) = closure (Rset dK) := closure_Rset_eq_of_subset hX hi hE hdK hEK hdKX
  have hRQ : closure (Rset k') = closure (Rset e) := closure_Rset_eq_of_subset hX hi hE' he hEQ heZ
  rw [Rset_symm_comp] at hRQ
  by_cases hJ2 : ∃ t₁ t₂ : unitInterval, t₁ ≠ t₂ ∧ (G ∩ K ∩ layer d t₁).Nonempty ∧
      (G ∩ K ∩ layer d t₂).Nonempty
  · obtain ⟨t₁, t₂, ht, h₁, h₂⟩ := hJ2
    rw [closure_Rset_of_common hX hi hd hdK inter_subset_left inter_subset_right hJc ht h₁ h₂ hb0
      hJ0 hJb, hRK]
  · -- then `G ∩ Q` meets two layers of `G`
    set s₀ := d ⟨x, hEH hxE⟩
    obtain ⟨t, hts⟩ : ∃ t : unitInterval, t ≠ s₀ := by
      by_cases h : s₀ = 0
      · exact ⟨1, by rw [h]; exact h01.symm⟩
      · exact ⟨0, Ne.symm h⟩
    obtain ⟨g, hg⟩ := layer_nonempty hd.2.1.2.1 t
    have hgG : g ∈ G := img_subset _ hg
    have hxs : x ∈ layer d s₀ := ⟨⟨x, hEH hxE⟩, rfl, rfl⟩
    have hgQ : g ∈ Q := by
      rcases hHKQ hgG with h | h
      · exact absurd ⟨s₀, t, hts.symm, ⟨x, ⟨hEH hxE, hEK hxE⟩, hxs⟩, ⟨g, ⟨hgG, h⟩, hg⟩⟩ hJ2
      · exact h
    rw [closure_Rset_of_common hX hi hd he inter_subset_left inter_subset_right hJ'c hts.symm
      ⟨x, ⟨hEH hxE, hEQ hxE⟩, hxs⟩ ⟨g, ⟨hgG, hgQ⟩, hg⟩ ha0 hJ'0 hJ'a, hRQ]

/-- **The two half-rays meet only in the layer.** -/
theorem halfray_inter_subset (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {G : Set M}
    {d : G → unitInterval} (hd : IsMinimalAdmissible G d) {u : unitInterval} (hu0 : 0 < u)
    (hu1 : u < 1) {Kup Kdn : Set M}
    (hKup : IsExtensionAway (layerSet d (Icc u 1)) (layer d u) Kup)
    (hKdn : IsExtensionAway (layerSet d (Icc 0 u)) (layer d u) Kdn) :
    Kup ∩ Kdn ⊆ layer d u := by
  have hHU := hagopian75_lemma1_hu hX hi
  haveI : CompactSpace G := isCompact_iff_compactSpace.mp hd.isCompact
  have hL := lsc_of_minimalAdmissible hX hi hd
  obtain ⟨p, hp, hp0, hp1⟩ := piece_map hd hL hu1 (P := layerSet d (Icc u 1)) rfl
  obtain ⟨q, hq, hq0, hq1⟩ := piece_map hd hL hu0 (P := layerSet d (Icc 0 u)) rfl
  have hGp : layerSet d (Icc u 1) ⊆ G := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hGq : layerSet d (Icc 0 u) ⊆ G := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hdn : G ∩ Kdn ⊆ layerSet d (Icc 0 u) :=
    ext_inter_subset hX hi hq ⟨hGq, d, hd, hq0.symm⟩ (by rw [hq1]; exact hKdn)
  have hKupc := IsExtensionAway.isContinuum hKup
  have hKdnc := IsExtensionAway.isContinuum hKdn
  rintro y ⟨hyup, hydn⟩
  by_contra hyu
  obtain ⟨hGK, dK, hdK, hdKu⟩ := hKup
  obtain ⟨w, hw⟩ := layer_nonempty hd.2.1.2.1 u
  have hwG : w ∈ G := img_subset _ hw
  have hwu : ∀ S : Set unitInterval, u ∈ S → w ∈ layerSet d S := fun S hS => by
    obtain ⟨w', hw', rfl⟩ := hw; exact ⟨w', by rw [mem_preimage, show d w' = u from hw']; exact hS, rfl⟩
  have hwKup : w ∈ Kup := hGK (hwu _ ⟨le_rfl, unitInterval.le_one'⟩)
  have hwKdn : w ∈ Kdn := hKdn.1 (hwu _ ⟨unitInterval.nonneg', le_rfl⟩)
  have hY := isContinuum_inter_of_HU hHU hKupc hKdnc ⟨w, hwKup, hwKdn⟩
  obtain ⟨s, hs0, hseg, -⟩ := hagopian76_initial_segment hX hi hp hdK hGK (hdKu.trans hp0.symm)
  set c := dK ⟨y, hyup⟩
  have hc0 : 0 < c := lt_of_le_of_ne unitInterval.nonneg' fun h => hyu (by
    rw [← hdKu]; exact ⟨⟨y, hyup⟩, h.symm, rfl⟩)
  have hIoo := layerSet_Ioo_subset hdK inter_subset_left hY
    ⟨w, ⟨hwKup, hwKdn⟩, by rw [hdKu]; exact hw⟩ ⟨y, ⟨hyup, hydn⟩, ⟨y, hyup⟩, rfl, rfl⟩
  obtain ⟨v, hv0, hv⟩ := exists_between (lt_min hc0 hs0)
  obtain ⟨z, hz⟩ := hdK.2.1.2.1 v
  have hzY : (z : M) ∈ Kup ∩ Kdn := hIoo ⟨z, by rw [mem_preimage, hz]; exact ⟨hv0, hv.trans_le (min_le_left _ _)⟩,
    rfl⟩
  have hzp : (z : M) ∈ layerSet d (Icc u 1) := by
    rw [← hseg]; exact ⟨z, by rw [mem_preimage, hz]; exact ⟨unitInterval.nonneg', (hv.trans_le
      (min_le_right _ _)).le⟩, rfl⟩
  have hzq : (z : M) ∈ layerSet d (Icc 0 u) := hdn ⟨hGp hzp, hzY.2⟩
  obtain ⟨g₁, hg₁, hg₁z⟩ := hzp
  obtain ⟨g₂, hg₂, hg₂z⟩ := hzq
  have : g₁ = g₂ := Subtype.ext (hg₁z.trans hg₂z.symm)
  subst this
  have hdg : d g₁ = u := le_antisymm hg₂.2 hg₁.1
  have hzu : (z : M) ∈ layer dK 0 := by rw [hdKu, ← hg₁z]; exact ⟨g₁, hdg, rfl⟩
  have := layer_param_eq hzu ⟨z, hz, rfl⟩
  rw [← this] at hv0
  exact lt_irrefl _ hv0

/-- **Half-ray density** (the skeleton's `halfray_dense`). -/
theorem halfray_dense_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hGE : IsEssential k G) {u : unitInterval} (hu0 : 0 < u)
    (hu1 : u < 1) :
    closure (extUnion (layerSet d (Icc u 1)) (layer d u)) = closure (Rset k) ∧
      closure (extUnion (layerSet d (Icc 0 u)) (layer d u)) = closure (Rset k) := by
  haveI : CompactSpace G := isCompact_iff_compactSpace.mp hG.isCompact
  have hL := lsc_of_minimalAdmissible hX hi hG
  have hR := closure_Rset_essential hX hi hE hGE hG
  obtain ⟨p, hp, hp0, hp1⟩ := piece_map hG hL hu1 (P := layerSet d (Icc u 1)) rfl
  obtain ⟨q, hq, hq0, hq1⟩ := piece_map hG hL hu0 (P := layerSet d (Icc 0 u)) rfl
  constructor
  · rw [← hp0, closure_extUnion_aux hX hi hp, closure_Rset_piece hX hi hG hu1 rfl hp hp1, hR]
  · have hq' : IsMinimalAdmissible (layerSet d (Icc 0 u)) (unitInterval.symm ∘ q) := hq.symm_comp
    have hq'0 : layer (unitInterval.symm ∘ q) 0 = layer d u := by
      rw [layer_symm_comp, unitInterval.symm_zero, hq1]
    rw [← hq'0, closure_extUnion_aux hX hi hq', Rset_symm_comp,
      closure_Rset_piece hX hi hG hu0 rfl hq hq1, hR]

end Ray

end HPC.Hagopian
