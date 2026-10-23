import HPC.BJ59.Thm10Glue
import HPC.BJ59.Thm10Pattern
import HPC.BJ59.Thm10Sub
import HPC.BJ59.Thm10Runs

/-!
# Batch 201, §4 (a)–(e): the pieces of the step

The maps of the sub-arcs (`exists_subarc_piece`, from `bj_theorem8_cor_sub`), the maps at the
ends (`exists_end_piece`, from `exists_pattern`), and the choice of `τ` (`exists_tau_run`,
`exists_tau_incl`).
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Tau

variable {Z : Type*} [MetricSpace Z] [CompactSpace Z]

/-- **Choice of `τ`, runs**: a run all of whose links meet the fibre over `c` and covering it
does the same for the fibres near `c`. -/
theorem exists_tau_run {φ : Z → unitInterval} (hφ : Continuous φ) (hφo : IsOpenMap φ) {N : ℕ}
    (F : Chain Z N) {t u : ℕ} {c : unitInterval}
    (hmeet : ∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ φ ⁻¹' {c}).Nonempty)
    (hcov : φ ⁻¹' {c} ⊆ ⋃ (k : Fin N) (_ : t ≤ k.val ∧ k.val ≤ u), F.link k) :
    ∃ τ > 0, ∀ x : unitInterval, |(x : ℝ) - c| ≤ τ →
      (∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ φ ⁻¹' {x}).Nonempty) ∧
      φ ⁻¹' {x} ⊆ ⋃ (k : Fin N) (_ : t ≤ k.val ∧ k.val ≤ u), F.link k := by
  classical
  have hm : ∀ k : Fin N, ∃ τ > 0, t ≤ k.val → k.val ≤ u → ∀ x : unitInterval,
      |(x : ℝ) - c| ≤ τ → (F.link k ∩ φ ⁻¹' {x}).Nonempty := by
    intro k
    by_cases hk : t ≤ k.val ∧ k.val ≤ u
    · obtain ⟨τ, hτ, h⟩ := exists_meets_near hφo (F.isOpen k) (hmeet k hk.1 hk.2)
      exact ⟨τ, hτ, fun _ _ => h⟩
    · exact ⟨1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose τk hτk hτkm using hm
  obtain ⟨τ₁, hτ₁, hτ₁le⟩ := exists_pos_forall_le τk hτk
  obtain ⟨τ₂, hτ₂, hτ₂c⟩ := exists_tube hφ isCompact_univ
    (isOpen_biUnion fun k _ => F.isOpen k) (fun z hz => hcov hz.2)
  refine ⟨min τ₁ τ₂, lt_min hτ₁ hτ₂, fun x hx => ⟨fun k hk1 hk2 => hτkm k hk1 hk2 x
    (hx.trans ((min_le_left _ _).trans (hτ₁le k))), fun z hz => hτ₂c z (mem_univ z) ?_⟩⟩
  simp only [mem_preimage, mem_singleton_iff] at hz
  rw [hz]; exact hx.trans (min_le_right _ _)

/-- **Choice of `τ`, inclusions**: if the closure of every link meets the fibre over `c` inside
a given open set, so do the links near the fibre. -/
theorem exists_tau_incl {φ : Z → unitInterval} (hφ : Continuous φ) {N : ℕ} (F : Chain Z N)
    {c : unitInterval} (V : Fin N → Set Z) (hV : ∀ k, IsOpen (V k))
    (h : ∀ k, closure (F.link k) ∩ φ ⁻¹' {c} ⊆ V k) :
    ∃ τ > 0, ∀ k, ∀ y ∈ F.link k, |(φ y : ℝ) - c| ≤ τ → y ∈ V k := by
  choose τk hτk hτkc using fun k => exists_tube hφ isClosed_closure.isCompact (hV k) (h k)
  obtain ⟨τ, hτ, hτle⟩ := exists_pos_forall_le τk hτk
  exact ⟨τ, hτ, fun k y hy hyc => hτkc k y (subset_closure hy) (hyc.trans (hτle k))⟩

end Tau

section Pieces

variable {X Y : Type} [MetricSpace X] [MetricSpace Y] [CompactSpace Y]

/-- **The map of a sub-arc** (commission 201 §4 (a), (b), (d)): the run `[r, s]` of `D` over
`[a, b]`, and for every fine chain `F` a chain map into it with (R1) and (R2). -/
theorem exists_subarc_piece {f : X → unitInterval} {g : Y → unitInterval} (hf : IsContArcPA f)
    (hg : IsContArcPA g) (hSY : IsSnakeLike (univ : Set Y)) {n m : ℕ} (D : Chain X n)
    (E : Chain Y m) (H : Fin n → Fin m) (hDc : univ ⊆ D.union) (hEf : IsFibreFine g E)
    (hA : IsFibreChainMap f g D E H) {a b : unitInterval} (hab : a < b)
    (h1b : ∀ u v : ℕ, u ≤ v →
      f ⁻¹' Icc a b ⊆ ⋃ (k : Fin n) (_ : u ≤ k.val ∧ k.val ≤ v), D.link k →
      ¬ f ⁻¹' Icc a b ⊆ ⋃ (k : Fin n) (_ : u + 1 ≤ k.val ∧ k.val ≤ v), D.link k →
      ¬ f ⁻¹' Icc a b ⊆ ⋃ (k : Fin n) (_ : u ≤ k.val ∧ k.val + 1 ≤ v), D.link k →
      ∀ x ∈ Icc a b, ∀ k : Fin n, u ≤ k.val → k.val ≤ v → (D.link k ∩ f ⁻¹' {x}).Nonempty) :
    ∃ r s : ℕ, r ≤ s ∧ s < n ∧
      (∀ x ∈ Icc a b, ∀ j : Fin n, r ≤ j.val → j.val ≤ s → (D.link j ∩ f ⁻¹' {x}).Nonempty) ∧
      (∀ x ∈ Icc a b, f ⁻¹' {x} ⊆ ⋃ (j : Fin n) (_ : r ≤ j.val ∧ j.val ≤ s), D.link j) ∧
      ∃ ε > 0, ∀ (N : ℕ) (F : Chain Y N), IsEpsChain F ε → univ ⊆ F.union →
        ∃ R : Fin N → Fin n, IsChainMap R ∧ (∀ k, r ≤ (R k).val ∧ (R k).val ≤ s) ∧
          (∀ k, ∀ y ∈ F.link k, g y ∈ Icc a b → y ∈ E.link (H (R k))) ∧
          ∀ x ∈ Icc a b, ∀ v w : ℕ, w < N → v ≤ w →
            g ⁻¹' {x} ⊆ ⋃ (k : Fin N) (_ : v ≤ k.val ∧ k.val ≤ w), F.link k →
            IsPatternOn R r s v w := by
  classical
  obtain ⟨hHc, hHs, hA3, hA4⟩ := hA
  -- the minimal run
  have hPne : (f ⁻¹' Icc a b).Nonempty := by
    obtain ⟨x, hx⟩ := hf.2.2.1 a
    exact ⟨x, by simp only [mem_preimage, hx]; exact ⟨le_rfl, hab.le⟩⟩
  obtain ⟨r, s, hrs, hsn, hcov, hl, hr⟩ := exists_minimal_run D hPne (fun z _ => hDc (mem_univ z))
  have hmeet := h1b r s hrs hcov hl hr
  have hcovx : ∀ x ∈ Icc a b, f ⁻¹' {x} ⊆ ⋃ (j : Fin n) (_ : r ≤ j.val ∧ j.val ≤ s), D.link j :=
    fun x hx z hz => hcov (by
      simp only [mem_preimage, mem_singleton_iff] at hz
      simp only [mem_preimage, hz]; exact hx)
  refine ⟨r, s, hrs, hsn, hmeet, hcovx, ?_⟩
  -- the image run `[a', b']` of `E`
  set S : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => r ≤ j.val ∧ j.val ≤ s) with hS
  have hSne : S.Nonempty := ⟨⟨r, by omega⟩, by simp [hS, hrs]⟩
  obtain ⟨jmin, hjminS, hjmin⟩ := S.exists_min_image (fun j => (H j).val) hSne
  obtain ⟨jmax, hjmaxS, hjmax⟩ := S.exists_max_image (fun j => (H j).val) hSne
  simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hjminS hjmaxS hjmin hjmax
  set a' := (H jmin).val with ha'
  set b' := (H jmax).val with hb'
  have ha'b' : a' ≤ b' := hjmin jmax hjmaxS
  have hivt : ∀ v, a' ≤ v → v ≤ b' → ∃ j : Fin n, r ≤ j.val ∧ j.val ≤ s ∧ (H j).val = v := by
    intro v h1 h2
    rcases le_total jmin jmax with h | h
    · obtain ⟨j, hj1, hj2, hj⟩ := chainMap_ivt hHc h (v := v) (by omega) (by omega)
      exact ⟨j, by have : jmin.val ≤ j.val := hj1; omega,
        by have : j.val ≤ jmax.val := hj2; omega, hj⟩
    · obtain ⟨j, hj1, hj2, hj⟩ := chainMap_ivt hHc h (v := v) (by omega) (by omega)
      exact ⟨j, by have : jmax.val ≤ j.val := hj1; omega,
        by have : j.val ≤ jmin.val := hj2; omega, hj⟩
  have hHrange : ∀ j : Fin n, r ≤ j.val → j.val ≤ s → a' ≤ (H j).val ∧ (H j).val ≤ b' :=
    fun j h1 h2 => ⟨hjmin j ⟨h1, h2⟩, hjmax j ⟨h1, h2⟩⟩
  have hb'm : b' < m := (H jmax).isLt
  set Esub : Chain Y (b' - a' + 1) := E.sub ⟨a', by omega⟩ ⟨b', hb'm⟩ ha'b' with hEsub
  have hEsub_link : ∀ t : Fin (b' - a' + 1), Esub.link t = E.link ⟨a' + t.val, by omega⟩ :=
    fun t => rfl
  set ℓ := s - r + 1 with hℓ
  set H₁ : Fin ℓ → Fin (b' - a' + 1) := fun k =>
    ⟨(H ⟨r + k.val, by omega⟩).val - a', by
      have := hHrange ⟨r + k.val, by omega⟩ (by simp only; omega) (by simp only; omega); omega⟩
    with hH₁
  have hH₁c : IsChainMap H₁ := by
    intro i j hij
    have h := hHc ⟨r + i.val, by omega⟩ ⟨r + j.val, by omega⟩ (by simp only; omega)
    have h1 := hHrange ⟨r + i.val, by omega⟩ (by simp only; omega) (by simp only; omega)
    have h2 := hHrange ⟨r + j.val, by omega⟩ (by simp only; omega) (by simp only; omega)
    simp only [hH₁]
    omega
  have hH₁s : Function.Surjective H₁ := by
    intro t
    obtain ⟨j, hj1, hj2, hj⟩ := hivt (a' + t.val) (by omega) (by omega)
    refine ⟨⟨j.val - r, by omega⟩, Fin.ext ?_⟩
    simp only [hH₁]
    rw [show (⟨r + (j.val - r), _⟩ : Fin n) = j from Fin.ext (by simp only; omega), hj]
    omega
  -- the hypotheses of the corollary
  have hfib : ∀ x ∈ Icc a b, g ⁻¹' {x} ⊆ ⋃ (j : Fin n) (_ : r ≤ j.val ∧ j.val ≤ s),
      E.link (H j) := fun x hx => hA4 x r s (fun j h1 h2 => hmeet x hx j h1 h2) (hcovx x hx)
  have hE : g ⁻¹' Icc a b ⊆ Esub.union := by
    intro y hy
    obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.1 (hfib (g y) hy rfl)
    have := hHrange j hj.1 hj.2
    refine mem_iUnion.2 ⟨⟨(H j).val - a', by omega⟩, ?_⟩
    rw [hEsub_link]
    convert hyj using 2
    ext; simp only; omega
  have hEf' : ∀ t ∈ Icc a b, ∀ k, (Esub.link k ∩ g ⁻¹' {t}).Nonempty := by
    intro t ht k
    obtain ⟨j, hj1, hj2, hj⟩ := hivt (a' + k.val) (by omega) (by omega)
    rw [hEsub_link]
    have := hA3 t j (hmeet t ht j hj1 hj2)
    convert this using 3
    exact Fin.ext hj.symm
  have hn' : b' - a' + 1 = 1 ∨ 3 ≤ b' - a' + 1 := by
    rcases hEf with h | h
    · left; have := (H jmax).isLt; omega
    · right
      have := h a a' b' (fun y hy => by
        obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.1 (hfib a ⟨le_rfl, hab.le⟩ hy)
        exact mem_iUnion₂.2 ⟨H j, hHrange j hj.1 hj.2, hyj⟩)
      omega
  obtain ⟨ε, hε, hcor⟩ := bj_theorem8_cor_sub hg hSY hab hn' Esub hE hEf' H₁ hH₁c hH₁s
  refine ⟨ε, hε, fun N F hF hFc => ?_⟩
  obtain ⟨R', hR'c, hR'1, hR'2⟩ := hcor N F hF (fun y _ => hFc (mem_univ y))
  refine ⟨fun k => ⟨r + (R' k).val, by have := (R' k).isLt; omega⟩, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have := hR'c i j hij
    simp only
    omega
  · intro k
    have := (R' k).isLt
    simp only
    omega
  · intro k y hy hyab
    have := hR'1 k ⟨hy, hyab⟩
    rw [hEsub_link] at this
    convert this using 2
    have h := hHrange ⟨r + (R' k).val, by have := (R' k).isLt; omega⟩
      (by simp only; omega) (by simp only; have := (R' k).isLt; omega)
    ext; simp only [hH₁]; omega
  · intro x hx v w hw hvw hcovF j hj1 hj2
    obtain ⟨k, hk, hvk, hkc⟩ := hR'2 x hx v w hw hvw hcovF ⟨j.val - r, by omega⟩
    refine ⟨k, hk, hvk, fun c hc => ⟨by omega, Fin.ext ?_⟩⟩
    have := congrArg Fin.val (hkc c hc)
    simp only at this ⊢
    omega

/-- **The map at an end** (commission 201 §4 (c), (d)): the minimal run `W` of `D` covering the
end fibre over `c`, and for every fine chain `F` a chain map into it following `h⁻¹` on closures,
with each link of `W` the image of three consecutive links meeting the fibre of `g`. -/
theorem exists_end_piece {f : X → unitInterval} {g : Y → unitInterval} (hf : IsContArcPA f)
    (hg : IsContArcPA g) {c : unitInterval} (h : f ⁻¹' {c} ≃ₜ g ⁻¹' {c}) {n : ℕ}
    (D : Chain X n) (hDc : univ ⊆ D.union) :
    ∃ w₁ w₂ : ℕ, w₁ ≤ w₂ ∧ w₂ < n ∧
      (∀ j : Fin n, w₁ ≤ j.val → j.val ≤ w₂ → (D.link j ∩ f ⁻¹' {c}).Nonempty) ∧
      f ⁻¹' {c} ⊆ ⋃ (j : Fin n) (_ : w₁ ≤ j.val ∧ j.val ≤ w₂), D.link j ∧
      ∃ ε > 0, ∀ (N : ℕ) (F : Chain Y N), IsEpsChain F ε → univ ⊆ F.union →
        ∃ R : Fin N → Fin n, IsChainMap R ∧ (∀ k, w₁ ≤ (R k).val ∧ (R k).val ≤ w₂) ∧
          (∀ k (z : g ⁻¹' {c}), (z : Y) ∈ closure (F.link k) → (h.symm z : X) ∈ D.link (R k)) ∧
          ∀ j : Fin n, w₁ ≤ j.val → j.val ≤ w₂ → ∃ a : ℕ, ∃ ha : a + 2 < N,
            ∀ (c' : ℕ) (hc : c' ≤ 2), (F.link ⟨a + c', by omega⟩ ∩ g ⁻¹' {c}).Nonempty ∧
              R ⟨a + c', by omega⟩ = j := by
  have hPne : (f ⁻¹' {c}).Nonempty := (hf.2.2.2 c).2.2.nonempty
  obtain ⟨w₁, w₂, hw, hwn, hcov, hl, hr⟩ := exists_minimal_run D hPne
    (fun z _ => hDc (mem_univ z))
  have hpc : IsPreconnected (f ⁻¹' {c}) := (hf.2.2.2 c).1.1.2.isPreconnected
  have hpriv := exists_point_only_of_minimal D hpc hw hwn hcov hl hr
  refine ⟨w₁, w₂, hw, hwn, fun j h1 h2 => ?_, hcov, ?_⟩
  · obtain ⟨z, hz, -⟩ := hpriv j h1 h2
    exact ⟨z, hz.2, hz.1⟩
  have hQ : IsCompact (g ⁻¹' {c}) := (isClosed_singleton.preimage hg.1).isCompact
  have hQc : IsPreconnected (g ⁻¹' {c}) := (hg.2.2.2 c).1.1.2.isPreconnected
  have hQn : (g ⁻¹' {c}).Nontrivial := (hg.2.2.2 c).2.2
  obtain ⟨ε, hε, hpat⟩ := exists_pattern hQ hQc hQn (fun z => (h.symm z : X))
    (continuous_subtype_val.comp h.symm.continuous) D hw hwn
    (fun z => hcov (h.symm z).2)
    (fun j h1 h2 => by
      obtain ⟨z, hz, hzo⟩ := hpriv j h1 h2
      refine ⟨h ⟨z, hz.1⟩, ?_, fun j' h1' h2' hne => ?_⟩
      · simp only [Homeomorph.symm_apply_apply]; exact hz.2
      · simp only [Homeomorph.symm_apply_apply]; exact hzo j' h1' h2' hne)
  exact ⟨ε, hε, fun N F hF hFc => hpat N F hF (fun y _ => hFc (mem_univ y))⟩

end Pieces

end HPC.BJ59
