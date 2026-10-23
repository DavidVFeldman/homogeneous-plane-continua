import HPC.PseudoArc.Theorem13
import HPC.Fold.Theorem7
import HPC.PseudoArc.T14Irred

/-!
# Bing 1948, Theorems 14 and 15: preliminaries; irreducible subcontinua

**Theorems 14 and 15 are proved**, in `HPC/PseudoArc/Thm14.lean` (`HPC.Description.theorem14`,
`HPC.Description.theorem15`, batch 115); the covering descriptions come from Lehner's Lemma 3
(`HPC/PseudoArc/Lehner.lean`, batch 114). Neither is open. This file keeps the preliminaries
(irreducible subcontinua, `theorem15_of_theorem14`, the reduction of the covering description to
one level).

Skeleton for batch 83 (save as `HPC/PseudoArc/Theorem14.lean`; add `import HPC.PseudoArc.Theorem14`
to the root `HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be
adjusted with the change recorded, except that `theorem14` and `theorem15` keep their conclusions.

Conventions as in `Theorem13.lean`: `Δ : Description X P Q` with `P ≠ Q` in a compact `X`;
`composant Δ.M p` is the union of the proper subcontinua of `Δ.M` containing `p`
(`Statements79.lean`); `Fold.Q78.IsContinuum K` is `IsCompact K ∧ IsConnected K`.

The hypotheses Bing leaves implicit and the skeleton states are listed in COMMISSION-batch83.md
§3.2 and §3.5: `W_i ≠ M` in Theorem 15; `P_i ≠ R_i` in Theorem 14; `Q_i ∈ M`.

*Batch 83 status.* `exists_irreducible`, `irreducible_unique` and `theorem15_of_theorem14` are
proved, statements unchanged. `exists_description_covering` is reduced
(`exists_description_covering_of_step`, proved) to the one-level claim `covering_step`;
`theorem14` was not proved in batch 83, so `theorem15` was then conditional on it (both are now
proved, see above). See REPORT-batch83.md.

*Batch 114.* `covering_step` and `exists_description_covering` are proved in
`HPC/PseudoArc/Lehner.lean` (Lehner's Lemma 3, `n = 2`) and have been moved there.

*Batch 115.* `theorem14` is proved in `HPC/PseudoArc/Thm14.lean` (the tracked alternating
construction) and has been moved there with `theorem15`, both with their statements unchanged.
-/

namespace HPC

open Set

variable {X : Type*} [MetricSpace X]

/-- `W` is a continuum containing `A` and `B`, and no proper subcontinuum of `W` contains both:
Bing's "subcontinuum irreducible from `A` to `B`". -/
def IsIrreducibleBetween (W : Set X) (A B : X) : Prop :=
  Fold.Q78.IsContinuum W ∧ A ∈ W ∧ B ∈ W ∧
    ∀ K : Set X, Fold.Q78.IsContinuum K → K ⊆ W → A ∈ K → B ∈ K → K = W

/-- **Irreducible subcontinua exist.** A continuum containing `A` and `B` contains a subcontinuum
irreducible between them. (Zorn on the subcontinua containing `A` and `B`, ordered by reverse
inclusion; a nested intersection of continua is a continuum.) -/
theorem exists_irreducible [CompactSpace X] {K : Set X} (hK : Fold.Q78.IsContinuum K) {A B : X}
    (hA : A ∈ K) (hB : B ∈ K) : ∃ W, W ⊆ K ∧ IsIrreducibleBetween W A B := by
  set S : Set (Set X) := {W | W ⊆ K ∧ Fold.Q78.IsContinuum W ∧ A ∈ W ∧ B ∈ W}
  obtain ⟨m, hmK, hm⟩ := zorn_superset_nonempty S (fun c hcS hch hne => by
    refine ⟨⋂₀ c, ⟨?_, ⟨?_, ⟨A, ?_⟩, ?_⟩, ?_, ?_⟩, fun W hW => sInter_subset_of_mem hW⟩
    · obtain ⟨W, hW⟩ := hne
      exact (sInter_subset_of_mem hW).trans (hcS hW).1
    · exact (isClosed_sInter fun W hW => (hcS hW).2.1.1.isClosed).isCompact
    · exact mem_sInter.mpr fun W hW => (hcS hW).2.2.1
    · exact T14.isPreconnected_sInter_chain hne hch (fun W hW => (hcS hW).2.1.1)
        (fun W hW => (hcS hW).2.1.2.isPreconnected)
    · exact mem_sInter.mpr fun W hW => (hcS hW).2.2.1
    · exact mem_sInter.mpr fun W hW => (hcS hW).2.2.2) K ⟨subset_rfl, hK, hA, hB⟩
  obtain ⟨⟨-, hmc, hAm, hBm⟩, hmin⟩ := hm
  refine ⟨m, hmK, hmc, hAm, hBm, fun K' hK' hK'm hAK hBK => ?_⟩
  exact Subset.antisymm hK'm (hmin ⟨hK'm.trans hmK, hK', hAK, hBK⟩ hK'm)

/-- Irreducibility is carried along by a self-homeomorphism of `M`. -/
theorem IsIrreducibleBetween.homImage {M : Set X} (T : M ≃ₜ M) {W : Set X} (hWM : W ⊆ M)
    {A B : M} (h : IsIrreducibleBetween W A B) :
    IsIrreducibleBetween (T14.homImage T W) (T A) (T B) := by
  refine ⟨T14.isContinuum_homImage T hWM h.1, (T14.mem_homImage T W A).mpr h.2.1,
    (T14.mem_homImage T W B).mpr h.2.2.1, fun K hK hKW hAK hBK => ?_⟩
  have hKM : K ⊆ M := hKW.trans (T14.homImage_subset T W)
  have hK' := T14.isContinuum_homImage T.symm hKM hK
  have hK'W : T14.homImage T.symm K ⊆ W := by
    have := T14.homImage_mono T.symm hKW
    rwa [T14.homImage_symm T hWM] at this
  have hmem : ∀ w : M, (T w : X) ∈ K → (w : X) ∈ T14.homImage T.symm K := fun w hw => by
    have := (T14.mem_homImage T.symm K (T w)).mpr hw
    simpa using this
  have hEq := h.2.2.2 _ hK' hK'W (hmem A hAK) (hmem B hBK)
  have hback := T14.homImage_symm T.symm hKM
  rw [Homeomorph.symm_symm, hEq] at hback
  exact hback.symm

/-- **The auxiliary point of Theorem 15.** A nondegenerate proper subcontinuum `W` of the
described continuum, through `P`, is irreducible between `P` and some `R ≠ P` of `W` lying in the
composant of `P` in `M`. -/
theorem exists_irreducible_partner [CompactSpace X] {P Q : X} (Δ : Description X P Q) {W : Set X}
    (hW : Fold.Q78.IsContinuum W) (hWM : W ⊆ Δ.M) (hWne : W ≠ Δ.M) (hnd : W.Nontrivial)
    {P₁ : X} (hP₁ : P₁ ∈ W) :
    ∃ R, R ∈ W ∧ P₁ ≠ R ∧ IsIrreducibleBetween W P₁ R ∧ R ∈ composant Δ.M P₁ := by
  have hind := Description.theorem10 Δ W hWM hW
  have hne := composant_ne_of_indecomposable hind hnd hP₁
  have hsub : composant W P₁ ⊆ W := sUnion_subset fun K hK => hK.2.1
  obtain ⟨R, hRW, hRc⟩ : ∃ R ∈ W, R ∉ composant W P₁ := by
    by_contra hcon
    push_neg at hcon
    exact hne (Subset.antisymm hsub hcon)
  have hPc : P₁ ∈ composant W P₁ := by
    refine mem_sUnion.mpr ⟨{P₁}, ⟨⟨isCompact_singleton, isConnected_singleton⟩,
      singleton_subset_iff.mpr hP₁, ?_, rfl⟩, rfl⟩
    intro h
    exact hnd.ne_singleton h.symm
  refine ⟨R, hRW, fun h => hRc (h ▸ hPc), ⟨hW, hP₁, hRW, fun K hK hKW hPK hRK => ?_⟩, ?_⟩
  · by_contra hKne
    exact hRc (mem_sUnion.mpr ⟨K, ⟨hK, hKW, hKne, hPK⟩, hRK⟩)
  · exact mem_sUnion.mpr ⟨W, ⟨hW, hWM, hWne, hP₁⟩, hRW⟩

namespace Description

variable {P Q : X}

/-- **The irreducible subcontinuum is unique** (Bing p. 742, last paragraph): in the described
continuum, two subcontinua both irreducible between the distinct points `A`, `B` coincide. Bing's
witness is the limit superior of the spans of the subchains `D_k(A, B)`; proof in
COMMISSION-batch83.md §3.1 (`exists_least_connected`).

(Batch 83: the hypothesis `hPQ` of the skeleton is not used by the proof; it is kept because the
skeleton has it.) -/
theorem irreducible_unique [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q) {A B : X}
    (hA : A ∈ Δ.M) (hB : B ∈ Δ.M) (hAB : A ≠ B) {W₁ W₂ : Set X} (h₁ : W₁ ⊆ Δ.M) (h₂ : W₂ ⊆ Δ.M)
    (hi₁ : IsIrreducibleBetween W₁ A B) (hi₂ : IsIrreducibleBetween W₂ A B) : W₁ = W₂ := by
  obtain ⟨L, hLc, hLp, hAL, hBL, -, hLmin⟩ := Δ.exists_least_connected hA hB hAB
  have hLcont : Fold.Q78.IsContinuum L := ⟨hLc.isCompact, ⟨A, hAL⟩, hLp⟩
  have key : ∀ W, W ⊆ Δ.M → IsIrreducibleBetween W A B → L = W := fun W hW hi =>
    hi.2.2.2 L hLcont (hLmin W hi.1.1.isClosed hi.1.2.isPreconnected hW hi.2.1 hi.2.2.1) hAL hBL
  exact (key W₁ h₁ hi₁).symm.trans (key W₂ h₂ hi₂)

/-- **Bing 1948, Theorem 14** (statement), with the implicit hypotheses `P_i ≠ R_i` and `Q_i ∈ M`
made explicit. -/
def Theorem14Statement (Δ : Description X P Q) : Prop :=
  ∀ (P₁ Q₁ R₁ P₂ Q₂ R₂ : X) (hP₁ : P₁ ∈ Δ.M) (hQ₁ : Q₁ ∈ Δ.M) (hR₁ : R₁ ∈ Δ.M)
    (hP₂ : P₂ ∈ Δ.M) (hQ₂ : Q₂ ∈ Δ.M) (hR₂ : R₂ ∈ Δ.M),
    R₁ ∈ composant Δ.M P₁ → R₂ ∈ composant Δ.M P₂ →
    Q₁ ∉ composant Δ.M P₁ → Q₂ ∉ composant Δ.M P₂ →
    P₁ ≠ R₁ → P₂ ≠ R₂ →
    ∃ T : Δ.M ≃ₜ Δ.M, T ⟨P₁, hP₁⟩ = ⟨P₂, hP₂⟩ ∧ T ⟨Q₁, hQ₁⟩ = ⟨Q₂, hQ₂⟩ ∧ T ⟨R₁, hR₁⟩ = ⟨R₂, hR₂⟩

/-- **Theorem 15 from Theorem 14** (Bing p. 741–742), with the implicit hypothesis `W_i ≠ M`.
`Q_i` "in a composant not containing `W_i`" is stated as `Q_i ∉ composant Δ.M P_i`
(COMMISSION-batch83.md §3.2). The image of `W₁` under `T`, read in `X`, is `W₂`. -/
theorem theorem15_of_theorem14 [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q)
    (h14 : Theorem14Statement Δ)
    {W₁ W₂ : Set X} (hW₁ : Fold.Q78.IsContinuum W₁) (hW₂ : Fold.Q78.IsContinuum W₂)
    (hW₁M : W₁ ⊆ Δ.M) (hW₂M : W₂ ⊆ Δ.M) (hW₁ne : W₁ ≠ Δ.M) (hW₂ne : W₂ ≠ Δ.M)
    (hnd₁ : W₁.Nontrivial) (hnd₂ : W₂.Nontrivial)
    {P₁ P₂ Q₁ Q₂ : X} (hP₁ : P₁ ∈ W₁) (hP₂ : P₂ ∈ W₂) (hQ₁ : Q₁ ∈ Δ.M) (hQ₂ : Q₂ ∈ Δ.M)
    (hQ₁c : Q₁ ∉ composant Δ.M P₁) (hQ₂c : Q₂ ∉ composant Δ.M P₂) :
    ∃ T : Δ.M ≃ₜ Δ.M, T ⟨P₁, hW₁M hP₁⟩ = ⟨P₂, hW₂M hP₂⟩ ∧ T ⟨Q₁, hQ₁⟩ = ⟨Q₂, hQ₂⟩ ∧
      (fun w : Δ.M => (T w : X)) '' {w | (w : X) ∈ W₁} = W₂ := by
  obtain ⟨R₁, hR₁W, hPR₁, hirr₁, hR₁c⟩ := exists_irreducible_partner Δ hW₁ hW₁M hW₁ne hnd₁ hP₁
  obtain ⟨R₂, hR₂W, hPR₂, hirr₂, hR₂c⟩ := exists_irreducible_partner Δ hW₂ hW₂M hW₂ne hnd₂ hP₂
  obtain ⟨T, hTP, hTQ, hTR⟩ := h14 P₁ Q₁ R₁ P₂ Q₂ R₂ (hW₁M hP₁) hQ₁ (hW₁M hR₁W) (hW₂M hP₂) hQ₂
    (hW₂M hR₂W) hR₁c hR₂c hQ₁c hQ₂c hPR₁ hPR₂
  refine ⟨T, hTP, hTQ, ?_⟩
  have h := IsIrreducibleBetween.homImage T hW₁M (A := ⟨P₁, hW₁M hP₁⟩) (B := ⟨R₁, hW₁M hR₁W⟩)
    hirr₁
  rw [hTP, hTR] at h
  exact Δ.irreducible_unique hPQ (hW₂M hP₂) (hW₂M hR₂W) hPR₂ (T14.homImage_subset T W₁) hW₂M h
    hirr₂

/-- **Bing's minimality** (p. 742): in the described continuum, a subcontinuum irreducible
between distinct points lies in every closed connected subset of `M` through them. -/
theorem IsIrreducibleBetween.subset_of_isPreconnected [CompactSpace X] (Δ : Description X P Q)
    {A B : X} (hA : A ∈ Δ.M) (hB : B ∈ Δ.M) (hAB : A ≠ B) {W : Set X} (hWM : W ⊆ Δ.M)
    (hW : IsIrreducibleBetween W A B) {K : Set X} (hKc : IsClosed K) (hK : IsPreconnected K)
    (hKM : K ⊆ Δ.M) (hAK : A ∈ K) (hBK : B ∈ K) : W ⊆ K := by
  obtain ⟨L, hLc, hLp, hAL, hBL, -, hLmin⟩ := Δ.exists_least_connected hA hB hAB
  have hLW : L = W := hW.2.2.2 L ⟨hLc.isCompact, ⟨A, hAL⟩, hLp⟩
    (hLmin W hW.1.1.isClosed hW.1.2.isPreconnected hWM hW.2.1 hW.2.2.1) hAL hBL
  rw [← hLW]
  exact hLmin K hKc hK hKM hAK hBK

/-- Under the hypotheses of `exists_description_covering`, `W` is a proper subcontinuum of `M`
and does not contain `Q'`. -/
theorem IsIrreducibleBetween.ne_M_and_not_mem [CompactSpace X] (Δ : Description X P Q)
    {P' Q' R : X} (hP' : P' ∈ Δ.M) (hR : R ∈ Δ.M) (hRc : R ∈ composant Δ.M P')
    (hQc : Q' ∉ composant Δ.M P') (hPR : P' ≠ R) {W : Set X} (hW : W ⊆ Δ.M)
    (hWirr : IsIrreducibleBetween W P' R) : W ≠ Δ.M ∧ Q' ∉ W := by
  obtain ⟨K, ⟨hK, hKM, hKne, hPK⟩, hRK⟩ := mem_sUnion.mp hRc
  have hWK := IsIrreducibleBetween.subset_of_isPreconnected Δ hP' hR hPR hW hWirr
    hK.1.isClosed hK.2.isPreconnected hKM hPK hRK
  refine ⟨fun h => hKne (Subset.antisymm hKM (h ▸ hWK)), fun hQ => hQc ?_⟩
  exact mem_sUnion.mpr ⟨K, ⟨hK, hKM, hKne, hPK⟩, hWK hQ⟩

/-- A chain `F` *covers `W` up to `R`*: for some link `b`, the subchain of `F` from its first link
to `b` is a chain from `P'` to `R`, and its links cover `W`. -/
def CoversUpTo {N : ℕ} (F : Chain X N) (P' R : X) (W : Set X) : Prop :=
  ∃ hN : 0 < N, ∃ b : Fin N, ∃ h0b : (⟨0, hN⟩ : Fin N) ≤ b,
    (F.sub ⟨0, hN⟩ b h0b).IsFrom P' R ∧ W ⊆ F.span ⟨0, hN⟩ b

/-- **The one-level covering claim** to which `exists_description_covering` reduces
(`exists_description_covering_of_step`): for every level `L` of `Δ` there is a consolidation of a
deeper level that is a chain from `P'` to `Q'`, has small links nested in the links of `D_L`,
and covers `W` up to `R`. No crookedness is asked of it: Theorems 1 and 2 supply that in the
assembly. -/
def CoveringStep (Δ : Description X P Q) (P' Q' R : X) (W : Set X) : Prop :=
  ∀ L, ∃ k, L < k ∧ ∃ N, ∃ F : Chain X N, F.IsFrom P' Q' ∧ F.IsConsolidationOf (Δ.D k) ∧
    (∀ u, ∃ t, closure (F.link u) ⊆ (Δ.D L).link t) ∧
    (∀ u, Metric.diam (F.link u) ≤ 1 / ((L : ℝ) + 1)) ∧ CoversUpTo F P' R W

/-- **Reduction of the covering description to one level.** -/
theorem exists_description_covering_of_step [CompactSpace X] (Δ : Description X P Q)
    {P' Q' R : X} {W : Set X} (hstep : CoveringStep Δ P' Q' R W) :
    ∃ Δ' : Description X P' Q', Δ'.M = Δ.M ∧
      ∀ i, ∃ b : Fin (Δ'.n i), ∃ h0b : (⟨0, (Δ'.isFrom i).1⟩ : Fin (Δ'.n i)) ≤ b,
        ((Δ'.D i).sub ⟨0, (Δ'.isFrom i).1⟩ b h0b).IsFrom P' R ∧
        W ⊆ (Δ'.D i).span ⟨0, (Δ'.isFrom i).1⟩ b := by
  obtain ⟨Δ', hM, hG⟩ := Δ.exists_description_of_steps (fun N F => CoversUpTo F P' R W) hstep
  refine ⟨Δ', hM, fun i => ?_⟩
  obtain ⟨hN, b, h0b, h1, h2⟩ := hG i
  exact ⟨b, h0b, h1, h2⟩

-- `covering_step` and `exists_description_covering` moved to `HPC/PseudoArc/Lehner.lean` in batch
-- 114 (proved there by Lehner's Lemma 3, `n = 2`), with their statements unchanged.

-- `theorem14` (formerly open, item 3 of OPEN.md before batch 116) and `theorem15` moved to `HPC/PseudoArc/Thm14.lean`
-- in batch 115, where they are proved (Theorem 14 by the tracked alternating construction, Theorem
-- 15 by `theorem15_of_theorem14` as before), with their statements unchanged.

end Description

end HPC
