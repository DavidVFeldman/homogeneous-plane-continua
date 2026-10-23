import HPC.PseudoArc.Theorem14
import HPC.Fold.T9Blocks

/-!
# Batch 86: reconnaissance on `covering_step`

Three proved propositions about the one-level claim `Description.covering_step`
(then in `HPC/PseudoArc/Theorem14.lean` and open):

*Batch 116 note:* the covering step was closed in batch 114 by Lehner's route
(`lehner_lemma3_two`, `HPC/PseudoArc/Lehner.lean`); this file's results stand as results about the
fold reformulations.

* `Chain.meet_ordConnected`: the links of a chain meeting a preconnected subset of its union form
  an index interval (the interval `[a, c]` of the commission, §1.3 Q2).
* `Description.coveringStep_of_folds`: `CoveringStep` follows from a *time-ordering fold* at every
  level (`IsCoveringFold`): a block map of a deep level `D_k`, every block inside one link of a
  level `D_m` with `m > L` and `ε_m ≤ 1/(L+1)`, sending the links through `P'` to block `0`, the
  links through `Q'` to the last block, the links through `R` to one block `b`, and every link
  meeting `W` to a block `≤ b`. This is the exact combinatorial form of Q2.
* `Description.window_of_irreducible`: the finite-level content of the Hausdorff convergence of
  batch 83 (Q3 (a)): for deep `k`, every link of `D_k` meeting `W` lies in a common link of `D_L`
  with some link of the subchain `D_k(P', R)`.

The model question (Q2 in the faithful model) is answered in `HPC/PseudoArc/Recon86Model.lean`.
-/

namespace HPC

open Set Metric

variable {X : Type*} [MetricSpace X]

namespace Chain

/-- **The links meeting a preconnected set form an interval.** If `K` is preconnected and lies in
the union of the chain `D`, and the links `i ≤ k` meet `K`, then so does every link `j` between
them. -/
theorem meet_ordConnected {n : ℕ} (D : Chain X n) {K : Set X} (hK : IsPreconnected K)
    (hKD : K ⊆ D.union) {i j k : Fin n} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : (D.link i ∩ K).Nonempty) (hk : (D.link k ∩ K).Nonempty) :
    (D.link j ∩ K).Nonempty := by
  by_contra hj
  rw [not_nonempty_iff_eq_empty] at hj
  set U : Set X := ⋃ (t : Fin n) (_ : t < j), D.link t with hU
  set V : Set X := ⋃ (t : Fin n) (_ : j < t), D.link t with hV
  have hUo : IsOpen U := isOpen_biUnion fun t _ => D.isOpen t
  have hVo : IsOpen V := isOpen_biUnion fun t _ => D.isOpen t
  have hcov : K ⊆ U ∪ V := by
    intro x hx
    obtain ⟨t, ht⟩ := mem_iUnion.mp (hKD hx)
    rcases lt_trichotomy t j with h | rfl | h
    · exact Or.inl (mem_biUnion h ht)
    · exact absurd (show x ∈ D.link t ∩ K from ⟨ht, hx⟩) (by rw [hj]; exact id)
    · exact Or.inr (mem_biUnion h ht)
  have hij' : i < j := by
    rcases eq_or_lt_of_le hij with h | h
    · subst h; rw [hj] at hi; exact absurd hi (by simp)
    · exact h
  have hjk' : j < k := by
    rcases eq_or_lt_of_le hjk with h | h
    · subst h; rw [hj] at hk; exact absurd hk (by simp)
    · exact h
  obtain ⟨x, hxi, hxK⟩ := hi
  obtain ⟨y, hyk, hyK⟩ := hk
  obtain ⟨z, hzK, hzU, hzV⟩ := hK U V hUo hVo hcov ⟨x, hxK, mem_biUnion hij' hxi⟩
    ⟨y, hyK, mem_biUnion hjk' hyk⟩
  obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hzU
  obtain ⟨t', ht', hzt'⟩ := mem_iUnion₂.mp hzV
  have hadj := (D.adjacent_iff t t').mp ⟨z, hzt, hzt'⟩
  have h1 : t.val < j.val := ht
  have h2 : j.val < t'.val := ht'
  omega

end Chain

namespace Description

variable {P Q : X}

/-- **A time-ordering fold at level `L`** (the combinatorial content of `CoveringStep`, commission
§1.2–1.3 Q2): a block map `β` of the level `D_k` onto `q` blocks such that every block lies in a
single link of `D_m`; every link of `D_k` containing `P'` is in block `0`, every link containing
`Q'` in the last block, every link containing `R` in the block `b`, and every link meeting `W` in a
block `≤ b`. -/
structure IsCoveringFold (Δ : Description X P Q) (P' Q' R : X) (W : Set X) (k m q : ℕ)
    (β : Fin (Δ.n k) → Fin q) (b : Fin q) : Prop where
  block : Chain.IsBlockMap β
  small : ∀ u : Fin q, ∃ s : Fin (Δ.n m), ∀ t, β t = u → (Δ.D k).link t ⊆ (Δ.D m).link s
  first : ∀ t, P' ∈ (Δ.D k).link t → (β t).val = 0
  last : ∀ t, Q' ∈ (Δ.D k).link t → (β t).val = q - 1
  atR : ∀ t, R ∈ (Δ.D k).link t → β t = b
  le_b : ∀ t, ((Δ.D k).link t ∩ W).Nonempty → β t ≤ b

/-- **`CoveringStep` from time-ordering folds.** If for every `L` some deep level `D_k` has a
time-ordering fold whose blocks lie in the links of a level `D_m` with `L < m` and
`ε_m ≤ 1/(L+1)`, then `CoveringStep Δ P' Q' R W` holds. So `covering_step` is implied by a
purely combinatorial statement about the patterns of the levels of `Δ` (commission §1.3 Q2). -/
theorem coveringStep_of_folds (Δ : Description X P Q) {P' Q' R : X} (hP' : P' ∈ Δ.M)
    (hQ' : Q' ∈ Δ.M) (hR : R ∈ Δ.M) {W : Set X} (hW : W ⊆ Δ.M)
    (hfold : ∀ L, ∃ k, L < k ∧ ∃ m, L < m ∧ Δ.ε m ≤ 1 / ((L : ℝ) + 1) ∧
      ∃ q, ∃ β : Fin (Δ.n k) → Fin q, ∃ b, Δ.IsCoveringFold P' Q' R W k m q β b) :
    CoveringStep Δ P' Q' R W := by
  intro L
  obtain ⟨k, hLk, m, hLm, hεm, q, β, b, hF⟩ := hfold L
  have hβ := hF.block
  set F := (Δ.D k).ofBlocks β hβ with hFdef
  have hmem : ∀ x ∈ Δ.M, ∃ t, x ∈ (Δ.D k).link t := fun x hx =>
    mem_iUnion.mp (Δ.M_subset_union k hx)
  have hlinkF : ∀ (u : Fin q) (x : X), x ∈ F.link u ↔ ∃ t, β t = u ∧ x ∈ (Δ.D k).link t := by
    intro u x
    rw [hFdef, Chain.ofBlocks_link]
    simp only [mem_iUnion, mem_setOf_eq, exists_prop]
  have hq : 0 < q := by
    obtain ⟨t, -⟩ := hmem P' hP'
    exact lt_of_le_of_lt (Nat.zero_le _) (β t).isLt
  -- a block lies in one link of `D_m`
  have hsmall : ∀ u : Fin q, ∃ s : Fin (Δ.n m), F.link u ⊆ (Δ.D m).link s := by
    intro u
    obtain ⟨s, hs⟩ := hF.small u
    refine ⟨s, fun x hx => ?_⟩
    obtain ⟨t, ht, hxt⟩ := (hlinkF u x).mp hx
    exact hs t ht hxt
  -- the chain from `P'` to `Q'`
  have hfrom : F.IsFrom P' Q' := by
    refine ⟨hq, ?_, ?_, ?_, ?_⟩
    · obtain ⟨t, ht⟩ := hmem P' hP'
      exact (hlinkF _ _).mpr ⟨t, Fin.ext (hF.first t ht), ht⟩
    · obtain ⟨t, ht⟩ := hmem Q' hQ'
      exact (hlinkF _ _).mpr ⟨t, Fin.ext (hF.last t ht), ht⟩
    · intro u hu
      obtain ⟨t, rfl, ht⟩ := (hlinkF u P').mp hu
      exact Fin.ext (hF.first t ht)
    · intro u hu
      obtain ⟨t, rfl, ht⟩ := (hlinkF u Q').mp hu
      exact Fin.ext (hF.last t ht)
  refine ⟨k, hLk, q, F, hfrom, Chain.ofBlocks_isConsolidationOf _ β hβ, ?_, ?_, ?_⟩
  · -- closures of blocks in links of `D_L`
    intro u
    obtain ⟨s, hs⟩ := hsmall u
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨s', hs'⟩ := Δ.closure_subset m' s
    obtain ⟨s'', hs''⟩ := Δ.refines_of_le (show L ≤ m' by omega) s'
    exact ⟨s'', (closure_mono hs).trans (hs'.trans hs'')⟩
  · -- small diameters
    intro u
    obtain ⟨s, hs⟩ := hsmall u
    exact (diam_mono hs (Δ.bdd m s)).trans ((Δ.diam_le m s).trans hεm)
  · -- covering `W` up to `R`
    have h0b : (⟨0, hq⟩ : Fin q) ≤ b := Fin.le_def.mpr (Nat.zero_le _)
    refine ⟨hq, b, h0b, ?_, ?_⟩
    · refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · obtain ⟨t, ht⟩ := hmem P' hP'
        exact (hlinkF _ _).mpr ⟨t, Fin.ext (by simp [hF.first t ht]), ht⟩
      · obtain ⟨t, ht⟩ := hmem R hR
        refine (hlinkF _ _).mpr ⟨t, ?_, ht⟩
        rw [hF.atR t ht]
        ext; simp only; omega
      · intro v hv
        obtain ⟨t, htv, ht⟩ := (hlinkF _ P').mp hv
        have h1 := hF.first t ht
        have h2 := congrArg Fin.val htv
        simp only at h2
        ext; simp only; omega
      · intro v hv
        obtain ⟨t, htv, ht⟩ := (hlinkF _ R).mp hv
        have h1 := hF.atR t ht
        have h2 := v.isLt
        ext; simp only at htv ⊢
        rw [h1] at htv
        have := congrArg Fin.val htv
        simp only at this
        omega
    · intro w hw
      obtain ⟨t, ht⟩ := hmem w (hW hw)
      have hle := hF.le_b t ⟨w, ht, hw⟩
      exact Chain.mem_span.mpr ⟨β t, Fin.le_def.mpr (Nat.zero_le _), hle,
        (hlinkF _ _).mpr ⟨t, rfl, ht⟩⟩

/-- **The window property** (commission §1.3 Q3 (a), the coarse reading of batch 83's Hausdorff
convergence). Let `W ⊆ M` be irreducible between the distinct points `P'` and `R` of `M`. For every
level `L`, from some level `N` on, every link of `D_k` that meets `W` lies, together with some link
of *every* subchain `D_k(a, b)` from `P'` to `R`, inside one link of `D_L`.

So the links of `W` beyond `R`'s link are, in the coarse reading, inside the window swept by the
subchain from `P'` to `R`. (`HPC/PseudoArc/Recon86Model.lean` shows that this, together with
crookedness, does not by itself produce a time-ordering fold.) -/
theorem window_of_irreducible [CompactSpace X] (Δ : Description X P Q) {P' R : X}
    (hP' : P' ∈ Δ.M) (hR : R ∈ Δ.M) (hPR : P' ≠ R) {W : Set X} (hW : W ⊆ Δ.M)
    (hWirr : IsIrreducibleBetween W P' R) (L : ℕ) :
    ∃ N, ∀ k, N ≤ k → ∀ a b : Fin (Δ.n k), (Δ.D k).IsSubchainFrom a b P' R →
      ∀ u : Fin (Δ.n k), ((Δ.D k).link u ∩ W).Nonempty →
        ∃ v : Fin (Δ.n k), a ≤ v ∧ v ≤ b ∧
          ∃ s : Fin (Δ.n L), (Δ.D k).link u ⊆ (Δ.D L).link s ∧ (Δ.D k).link v ⊆ (Δ.D L).link s := by
  -- a Lebesgue number of the cover of `M` by the links of `D_L`
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric Δ.isCompact_M
    (fun s => (Δ.D L).isOpen s) (Δ.M_subset_union L)
  have hWmin : ∀ K : Set X, IsClosed K → IsPreconnected K → K ⊆ Δ.M → P' ∈ K → R ∈ K →
      W ⊆ K := fun K hKc hKp hKM hPK hRK =>
    IsIrreducibleBetween.subset_of_isPreconnected Δ hP' hR hPR hW hWirr hKc hKp hKM hPK hRK
  obtain ⟨N₁, hN₁⟩ := Δ.subset_thickening_span hWmin (η := δ / 3) (by linarith)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp Δ.ε_tendsto) (δ / 3) (by linarith)
  refine ⟨max N₁ N₂, fun k hk a b hab u ⟨w, hwu, hwW⟩ => ?_⟩
  have hεk : Δ.ε k < δ / 3 := by
    have := hN₂ k (le_of_max_le_right hk)
    rw [Real.dist_eq, sub_zero, abs_of_pos (Δ.ε_pos k)] at this
    exact this
  obtain ⟨s, hs⟩ := hleb w (hW hwW)
  have hwth := hN₁ k (le_of_max_le_left hk) a b hab hwW
  obtain ⟨z, hz, hwz⟩ := mem_thickening_iff.mp hwth
  obtain ⟨v, hav, hvb, hzv⟩ := Chain.mem_span.mp hz
  refine ⟨v, hav, hvb, s, fun y hy => hs ?_, fun y hy => hs ?_⟩
  · rw [mem_ball]
    have := (dist_le_diam_of_mem (Δ.bdd k u) hy hwu).trans (Δ.diam_le k u)
    linarith
  · rw [mem_ball]
    have h1 := (dist_le_diam_of_mem (Δ.bdd k v) hy hzv).trans (Δ.diam_le k v)
    have h2 := dist_triangle y z w
    rw [dist_comm z w] at h2
    linarith

end Description

end HPC
