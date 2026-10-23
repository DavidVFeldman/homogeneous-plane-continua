import HPC.Effros.Fat

/-!
# Batch 134, §B: the open mapping principle (van Mill 2004, §3)

A Polish group acting continuously and transitively on a nonempty metric Baire space acts
micro-transitively: `U • x` is a neighbourhood of `x` for every neighbourhood `U` of `1`
(`effros_open_mapping`), and every orbit map is open (`isOpenMap_smul_left`).

Lemma 3.4 (`vanMill_3_4_dense`, `vanMill_3_4`) and Proposition 3.5 (`vanMill_3_5`) are proved
as printed by van Mill, i.e. with closures: `x ∈ interior (closure (U n • x))` and
`interior (closure (U (n+1) • x)) ⊆ U n • x`. (The transcription in COMMISSION-batch134.md §3.2
dropped the closure bars; the commission's repaired forms 3.4′ and 3.5′ coincide with the
original.)
-/

namespace HPC.Effros

open Set Topology Filter Metric MeasureTheory
open scoped Pointwise

section OpenMapping

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A neighbourhood base `U n` of `1` with van Mill's properties:
(i) each `U n` is open and symmetric, and `U 0 = univ`;
(ii) `U (n+1) * U (n+1) ⊆ U n`;
and the `U n` form a basis of `𝓝 1`. (In a first countable group; Polish groups are.) -/
theorem exists_vanMill_basis [PolishSpace G] :
    ∃ U : ℕ → Set G, U 0 = univ ∧ (∀ n, IsOpen (U n) ∧ (1 : G) ∈ U n ∧ (U n)⁻¹ = U n) ∧
      (∀ n, U (n + 1) * U (n + 1) ⊆ U n) ∧ (𝓝 (1 : G)).HasBasis (fun _ => True) U := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable G
  obtain ⟨B, hB⟩ := (𝓝 (1 : G)).exists_antitone_basis
  obtain ⟨U, hU0, hU⟩ := exists_seq_of_step (σ := Set G)
    (G := fun s => IsOpen s ∧ (1 : G) ∈ s ∧ s⁻¹ = s)
    (R := fun n s t => t * t ⊆ s ∧ t ⊆ B n) (s₀ := univ)
    ⟨isOpen_univ, mem_univ _, inv_univ⟩ (by
      rintro n s ⟨hso, hs1, -⟩
      have hW : s ∩ B n ∈ 𝓝 (1 : G) := inter_mem (hso.mem_nhds hs1) (hB.1.mem_of_mem trivial)
      obtain ⟨S, hSo, hS1, hSS⟩ := exists_open_nhds_one_mul_subset hW
      refine ⟨S ∩ S⁻¹, ⟨hSo.inter hSo.inv, ⟨hS1, by simpa using hS1⟩, ?_⟩, ?_, ?_⟩
      · rw [inter_inv, inv_inv, inter_comm]
      · exact (mul_subset_mul inter_subset_left inter_subset_left).trans
          (hSS.trans inter_subset_left)
      · intro g hg
        have : g * 1 ∈ S * S := mul_mem_mul hg.1 hS1
        rw [mul_one] at this
        exact (hSS this).2)
  refine ⟨U, hU0, fun n => (hU n).1, fun n => (hU n).2.1, ⟨fun t => ⟨fun ht => ?_, ?_⟩⟩⟩
  · obtain ⟨i, -, hi⟩ := hB.1.mem_iff.1 ht
    exact ⟨i + 1, trivial, (hU i).2.2.trans hi⟩
  · rintro ⟨i, -, hi⟩
    exact mem_of_superset ((hU i).1.1.mem_nhds (hU i).1.2.1) hi

variable [MetricSpace X] [MulAction G X] [ContinuousSMul G X]

/-- `U • x := {g • x | g ∈ U}`. -/
def orbitPart (U : Set G) (x : X) : Set X := (fun g : G => g • x) '' U

omit [TopologicalSpace G] [IsTopologicalGroup G] [MetricSpace X] [ContinuousSMul G X] in
theorem mem_orbitPart {U : Set G} {x y : X} : y ∈ orbitPart U x ↔ ∃ g ∈ U, g • x = y :=
  Iff.rfl

/-- **van Mill, Lemma 3.1.** Suppose `V` is open and `z ∈ V ∩ U n • x`. Then
`U m • z ⊆ V ∩ U n • x` for some `m`. (The hypothesis `U 0 = univ` of the skeleton is not
used and was dropped.) -/
theorem vanMill_3_1 {U : ℕ → Set G}
    (hU : ∀ n, IsOpen (U n) ∧ (1 : G) ∈ U n ∧ (U n)⁻¹ = U n)
    (hb : (𝓝 (1 : G)).HasBasis (fun _ => True) U) (x : X) (n : ℕ) {V : Set X} (hV : IsOpen V)
    {z : X} (hz : z ∈ V ∩ orbitPart (U n) x) :
    ∃ m, orbitPart (U m) z ⊆ V ∩ orbitPart (U n) x := by
  obtain ⟨hzV, h, hhU, rfl⟩ := hz
  have hcont : Continuous fun g : G => (g * h) • x :=
    (continuous_id.mul continuous_const).smul continuous_const
  set N := (fun g : G => (g * h) • x) ⁻¹' V ∩ (fun g : G => g * h) ⁻¹' U n with hN
  have hNo : IsOpen N := (hV.preimage hcont).inter
    ((hU n).1.preimage (continuous_id.mul continuous_const))
  have hN1 : N ∈ 𝓝 (1 : G) := hNo.mem_nhds ⟨by simpa using hzV, by simpa using hhU⟩
  obtain ⟨m, -, hm⟩ := hb.mem_iff.1 hN1
  refine ⟨m, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  have hgN := hm hg
  refine ⟨?_, g * h, hgN.2, ?_⟩
  · have := hgN.1
    simpa [mul_smul] using this
  · simp [mul_smul]

omit [IsTopologicalGroup G] in
/-- The image of a meager set under the homeomorphism `p ↦ g • p` is meager. -/
theorem isMeagre_smul_image (g : G) {A : Set X} (hA : IsMeagre A) :
    IsMeagre ((fun p => g • p) '' A) :=
  (Homeomorph.smul g).isInducing.isMeagre_image hA

/-- **van Mill, Lemma 3.2.** If the action is transitive and `X` is a nonempty Baire space, then
`U • x` is not meager for any neighbourhood `U` of `1`. (Lindelöf: countably many translates of
`U` cover `G`.) -/
theorem vanMill_3_2 [PolishSpace G] [MulAction.IsPretransitive G X] [BaireSpace X] [Nonempty X]
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) (x : X) : ¬ IsMeagre (orbitPart U x) := by
  intro hm
  set U' := interior U with hU'
  have hU'1 : (1 : G) ∈ U' := mem_interior_iff_mem_nhds.2 hU
  -- countably many translates `φ • U'` cover `G`
  obtain ⟨F, hFc, hFcov⟩ : ∃ F : Set G, F.Countable ∧ ⋃ φ ∈ F, φ • U' = univ := by
    have hcov : (univ : Set G) ⊆ ⋃ φ : G, φ • U' := fun g _ =>
      mem_iUnion.2 ⟨g, ⟨1, hU'1, mul_one g⟩⟩
    obtain ⟨F, hFc, hF⟩ := TopologicalSpace.isOpen_iUnion_countable (fun φ : G => φ • U')
      (fun φ => isOpen_interior.smul φ)
    refine ⟨F, hFc, eq_univ_of_univ_subset ?_⟩
    rw [hF]
    exact hcov
  have hall : (univ : Set X) ⊆ ⋃ φ ∈ F, (fun p => φ • p) '' orbitPart U x := by
    intro y _
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
    have hg : g ∈ ⋃ φ ∈ F, φ • U' := hFcov.symm ▸ mem_univ g
    obtain ⟨φ, hφF, u, hu, rfl⟩ := mem_iUnion₂.1 hg
    exact mem_iUnion₂.2 ⟨φ, hφF, u • x, ⟨u, interior_subset hu, rfl⟩, by simp [mul_smul]⟩
  have : IsMeagre (univ : Set X) :=
    (isMeagre_biUnion hFc fun φ _ => isMeagre_smul_image φ hm).mono hall
  exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty this

/-- **van Mill, Corollary 3.3.** `U n • x` is nowhere meager. (The hypothesis `U 0 = univ` of the
skeleton is not used and was dropped.) -/
theorem vanMill_3_3 [PolishSpace G] [MulAction.IsPretransitive G X] [BaireSpace X] [Nonempty X]
    {U : ℕ → Set G} (hU : ∀ n, IsOpen (U n) ∧ (1 : G) ∈ U n ∧ (U n)⁻¹ = U n)
    (hb : (𝓝 (1 : G)).HasBasis (fun _ => True) U) (x : X) (n : ℕ) :
    NowhereMeagre (orbitPart (U n) x) := by
  rintro V hV ⟨z, hz⟩ hm
  obtain ⟨m, hm'⟩ := vanMill_3_1 hU hb x n hV hz
  exact vanMill_3_2 ((hU m).1.mem_nhds (hU m).2.1) z (hm.mono hm')

/-- **van Mill, Lemma 3.4, second sentence.** `x` lies in the interior of `closure (U n • x)`.
This is the lemma as printed: the original has closure bars over `U n x` in Lemma 3.4 and in
Proposition 3.5, which the transcription of COMMISSION-batch134.md §3.2 lost; the suspected gap
there is an artifact of the transcription (REPORT-batch134.md). Proof: `V := interior (closure
(U (n+1) • x))` is nonempty (3.2) and meets `U (n+1) • x`, say at `h • x`. Then `x ∈ h⁻¹ • V`,
which is open and contained in `closure (U n • x)` by (i) and (ii). (The hypotheses
`U 0 = univ` and "basis" of the skeleton are not used and were dropped.) -/
theorem vanMill_3_4 [PolishSpace G] [MulAction.IsPretransitive G X] [BaireSpace X] [Nonempty X]
    {U : ℕ → Set G} (hU : ∀ n, IsOpen (U n) ∧ (1 : G) ∈ U n ∧ (U n)⁻¹ = U n)
    (hUU : ∀ n, U (n + 1) * U (n + 1) ⊆ U n) (x : X) (n : ℕ) :
    x ∈ interior (closure (orbitPart (U n) x)) := by
  set V := interior (closure (orbitPart (U (n + 1)) x)) with hV
  have hVne : V.Nonempty := nonempty_interior_closure_of_not_meagre
    (vanMill_3_2 ((hU (n + 1)).1.mem_nhds (hU (n + 1)).2.1) x)
  obtain ⟨_, hhV, h, hhU, rfl⟩ : (V ∩ orbitPart (U (n + 1)) x).Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    have := interior_subset hv
    rw [_root_.mem_closure_iff] at this
    exact this V isOpen_interior hv
  have hhinv : h⁻¹ ∈ U (n + 1) := by
    rw [← (hU (n + 1)).2.2] at hhU
    simpa using hhU
  have hsub : h⁻¹ • V ⊆ closure (orbitPart (U n) x) := by
    calc h⁻¹ • V ⊆ h⁻¹ • closure (orbitPart (U (n + 1)) x) := smul_set_mono interior_subset
      _ = closure (h⁻¹ • orbitPart (U (n + 1)) x) :=
          (closure_smul (h⁻¹ : G) (orbitPart (U (n + 1)) x)).symm
      _ ⊆ closure (orbitPart (U n) x) := by
        apply closure_mono
        rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
        exact ⟨h⁻¹ * g, hUU n (mul_mem_mul hhinv hg), by simp [mul_smul]⟩
  exact interior_maximal hsub (isOpen_interior.smul _) ⟨h • x, hhV, by simp⟩

/-- **van Mill, Lemma 3.4, first sentence** (as printed, with the closure bars of the original):
the interior of `closure (U n • x)` is dense in `closure (U n • x)`. Van Mill's proof: an open
`V` meeting `closure (U n • x)` meets `U n • x`; by 3.3 `V ∩ U n • x` is not meager, so its
closure has nonempty interior, which lies in `closure V ∩ interior (closure (U n • x))` and hence
meets `V`. -/
theorem vanMill_3_4_dense [PolishSpace G] [MulAction.IsPretransitive G X] [BaireSpace X]
    [Nonempty X] {U : ℕ → Set G} (hU : ∀ n, IsOpen (U n) ∧ (1 : G) ∈ U n ∧ (U n)⁻¹ = U n)
    (hb : (𝓝 (1 : G)).HasBasis (fun _ => True) U) (x : X) (n : ℕ) :
    closure (orbitPart (U n) x) ⊆ closure (interior (closure (orbitPart (U n) x))) := by
  intro y hy
  rw [_root_.mem_closure_iff] at hy ⊢
  intro V hV hyV
  have hne := hy V hV hyV
  obtain ⟨o, ho⟩ := nonempty_interior_closure_of_not_meagre (vanMill_3_3 hU hb x n V hV hne)
  have hoV : o ∈ closure V := closure_mono inter_subset_left (interior_subset ho)
  rw [_root_.mem_closure_iff] at hoV
  obtain ⟨w, hwO, hwV⟩ := hoV _ isOpen_interior ho
  exact ⟨w, hwV, interior_mono (closure_mono inter_subset_right) hwO⟩

/-- **van Mill, Proposition 3.5** (as printed, with the closure bar). `interior (closure (U (n+1) • x)) ⊆ U n • x`.
For `z` in the left side, put `E := interior (closure (U (n+1) • x)) ∩ interior (closure
(U (n+1) • z))`, an open neighbourhood of `z` by 3.4. The sets `U (n+1) • x ∩ E` and
`U (n+1) • z ∩ E` are nowhere meager (3.3), analytic (continuous images of the open, hence Polish,
`U (n+1)`), and each lies in the closure of the other (`E` lies in both closures). By
Proposition 2.2 (relative form, `inter_nonempty_of_nowhereMeagre`) they meet at
`g • x = h • z`, so `z = (h⁻¹ * g) • x` with `h⁻¹ * g ∈ U n`. (The hypothesis `U 0 = univ` of
the skeleton is not used and was dropped.) -/
theorem vanMill_3_5 [PolishSpace G] [MulAction.IsPretransitive G X] [BaireSpace X] [Nonempty X]
    {U : ℕ → Set G} (hU : ∀ n, IsOpen (U n) ∧ (1 : G) ∈ U n ∧ (U n)⁻¹ = U n)
    (hUU : ∀ n, U (n + 1) * U (n + 1) ⊆ U n) (hb : (𝓝 (1 : G)).HasBasis (fun _ => True) U)
    (x : X) (n : ℕ) :
    interior (closure (orbitPart (U (n + 1)) x)) ⊆ orbitPart (U n) x := by
  intro z hz
  set E := interior (closure (orbitPart (U (n + 1)) x)) ∩
    interior (closure (orbitPart (U (n + 1)) z)) with hE
  have hEo : IsOpen E := isOpen_interior.inter isOpen_interior
  have hzE : z ∈ E := ⟨hz, vanMill_3_4 hU hUU z (n + 1)⟩
  have hana : ∀ w : X, AnalyticSet (orbitPart (U (n + 1)) w ∩ E) := by
    intro w
    have hc : Continuous fun g : G => g • w := continuous_id.smul continuous_const
    have : orbitPart (U (n + 1)) w ∩ E =
        (fun g : G => g • w) '' (U (n + 1) ∩ (fun g : G => g • w) ⁻¹' E) := by
      rw [image_inter_preimage]; rfl
    rw [this]
    exact ((hU (n + 1)).1.inter (hEo.preimage hc)).analyticSet_image hc
  have hnm : ∀ w : X, NowhereMeagre (orbitPart (U (n + 1)) w ∩ E) := by
    intro w V hV hne hm
    have h1 : V ∩ (orbitPart (U (n + 1)) w ∩ E) = (V ∩ E) ∩ orbitPart (U (n + 1)) w := by
      ext; simp only [mem_inter_iff]; tauto
    rw [h1] at hne hm
    exact vanMill_3_3 hU hb w (n + 1) (V ∩ E) (hV.inter hEo) hne hm
  -- `E` lies in the closure of each of the two sets
  have hcl : ∀ w : X, E ⊆ closure (orbitPart (U (n + 1)) w) →
      E ⊆ closure (orbitPart (U (n + 1)) w ∩ E) := by
    intro w hw y hy
    have := hEo.inter_closure ⟨hy, hw hy⟩
    rw [inter_comm] at this
    exact this
  have hSne : (orbitPart (U (n + 1)) x ∩ E).Nonempty := by
    have := hcl x (fun y hy => interior_subset hy.1) hzE
    rw [_root_.mem_closure_iff] at this
    obtain ⟨y, -, hy⟩ := this univ isOpen_univ trivial
    exact ⟨y, hy⟩
  obtain ⟨y, ⟨⟨g, hg, rfl⟩, -⟩, ⟨h, hh, hhz⟩, -⟩ := inter_nonempty_of_nowhereMeagre (hana x)
    (hana z) (hnm x) (hnm z) hSne
    (fun y hy => hcl z (fun y hy => interior_subset hy.2) hy.2)
  have hhinv : h⁻¹ ∈ U (n + 1) := by
    rw [← (hU (n + 1)).2.2] at hh
    simpa using hh
  refine ⟨h⁻¹ * g, hUU n (mul_mem_mul hhinv hg), ?_⟩
  simp only at hhz
  show (h⁻¹ * g) • x = z
  rw [mul_smul, ← hhz]
  simp

/-- **The open mapping principle** (Effros 1965; van Mill 2004, Theorem 1.2 for a Polish group).
Suppose a Polish group acts continuously and transitively on a nonempty metric Baire space. Then
for every `x` and every neighbourhood `U` of `1`, the set `U • x` is a neighbourhood of `x`. That
is, the action is micro-transitive, and `g ↦ g • x` is open. -/
theorem effros_open_mapping [PolishSpace G] [MulAction.IsPretransitive G X] [BaireSpace X]
    [Nonempty X] (x : X) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) : orbitPart U x ∈ 𝓝 x := by
  obtain ⟨B, -, hB, hBUU, hb⟩ := exists_vanMill_basis (G := G)
  obtain ⟨n, -, hn⟩ := hb.mem_iff.1 hU
  have h1 := vanMill_3_4 hB hBUU x (n + 1)
  have h2 := vanMill_3_5 hB hBUU hb x n
  refine mem_of_superset (isOpen_interior.mem_nhds h1) (h2.trans ?_)
  exact image_mono hn

/-- The orbit map `g ↦ g • x` is open. -/
theorem isOpenMap_smul_left [PolishSpace G] [MulAction.IsPretransitive G X] [BaireSpace X]
    [Nonempty X] (x : X) : IsOpenMap (fun g : G => g • x) := by
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨g, hg, rfl⟩
  have hO' : (fun k => g * k) ⁻¹' O ∈ 𝓝 (1 : G) :=
    (hO.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using hg)
  have h1 := effros_open_mapping x hO'
  have h2 : (fun p => g • p) '' orbitPart ((fun k => g * k) ⁻¹' O) x ∈ 𝓝 (g • x) := by
    have := (Homeomorph.smul g).isOpenMap.image_mem_nhds h1
    simpa using this
  refine mem_of_superset h2 ?_
  rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  exact ⟨g * k, hk, by simp [mul_smul]⟩

/-- **van Mill, remark after Corollary 3.6.** `U • x` is open for every open `U ⊆ G`. -/
theorem isOpen_orbitPart [PolishSpace G] [MulAction.IsPretransitive G X] [BaireSpace X]
    [Nonempty X] {U : Set G} (hU : IsOpen U) (x : X) : IsOpen (orbitPart U x) :=
  isOpenMap_smul_left x U hU

end OpenMapping

end HPC.Effros
