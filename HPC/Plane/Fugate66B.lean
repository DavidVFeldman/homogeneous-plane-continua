import HPC.Plane.Fugate66BThm1
import HPC.Plane.Fugate66BMiller

/-!
# Batch 101: Fugate 1966, Lemma 2 (corrected), Miller's theorem, Lemma 4, Theorem 1 (sufficiency),
# Corollary 1

The batch-101 skeleton, with proofs. Source: Fugate 1966, pp. 463–467, transcribed in
COMMISSION-batch101.md §1. Chains are 0-indexed: Fugate's `E(1,m)` is `E.link 0 … E.link (m−1)`.
Status of each item and the shape changes are recorded in `REPORT-batch101.md`.

The proofs live in five files imported here:
* `Fugate66BLemma2.lean` — Definition 5 in full (`ContainedExactly'`, moved there so that the later
  files can use it), Lemma 2 corrected, and its taut form;
* `Fugate66BHU.lean` — hereditary unicoherence of `A ∪ B` (the consequence of Miller's theorem);
* `Fugate66BLemma4.lean` — Lemma 4 in ℕ-indexed form (`fugate_lemma4_weak`, data `Fit`);
* `Fugate66BThm1.lean` — Theorem 1, sufficiency (Cases i and ii, Claims 2–3, the chain `𝒢`);
* `Fugate66BMiller.lean` — the refutation of the transcribed Miller theorem (two half-disks).

Batch 103 (pruning): batch 100's sorried `fugate_theorem1_sufficiency`, `fugate_theorem1` and
`fugate_cor2` (formerly in `Fugate66.lean`) were deleted; the proved versions below now carry those
canonical names, and the primed names `fugate_theorem1_sufficiency'`, `fugate_theorem1'`,
`fugate_cor2'` are kept as aliases. Batch 100's `fugate_cor1` (Fugate's hypothesis: the union
unicoherent) stays open in `Fugate66.lean`; `fugate_cor1'` and `fugate_cor1_iff` below assume the
union hereditarily unicoherent.
-/

namespace HPC.Plane

open Set Topology Metric

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ## Definition 5, corrected

`ContainedExactly'` is defined in `Fugate66BLemma2.lean`. Shape change: clause (2) is stated as
Fugate states it — `A` lies in no proper subchain of `F(j..k)`, i.e. `A` has a point of `F_j` in no
other link of `F(j..k)` and a point of `F_k` in no other link of `F(j..k)` — rather than the
skeleton's "`A` meets `F_j` and `F_k`", which is weaker (it allows `A ⊆ F*(j..k−1)`) and does not
give the point `c ∈ E_m − E*(j,m−1)` that Theorem 1 (Case ii, Claim 3) needs. The skeleton's
`by omega` index proofs did not elaborate inside a conjunction; the bounds are now existential
binders. -/

omit [CompactSpace S] in
/-- **Lemma 2, corrected**: `A ⊆ᵉ F*(s..n−1)` (Definition 5 in full). Fugate: from Lemma 1 (`A`
meets `F_n − Cl F_{n−1}`), take the least `s` with `A ⊆ F*(s..n−1)`, and cut the earlier links away
from a closed neighbourhood of `A`. The taut form is `fugate_lemma2'_taut`. -/
theorem fugate_lemma2' {M A : Set S} (hM : Fold.Q78.IsContinuum M) (hA : IsTerminalSub M A)
    {m : ℕ} (E : Chain S m) (hE : M ⊆ E.union) :
    ∃ (n : ℕ) (F : Chain S n) (s : ℕ), M ⊆ F.union ∧ F.Refines E ∧
      ContainedExactly' F A s (n - 1) :=
  fugate_lemma2'_aux hM hA E hE

/-! ## Miller's theorem (Fugate's "[6, Theorem 1.5, p. 180]") -/

-- Commented-out statement `miller_1_5` removed in batch 103; see `LEDGER.md`.

omit [CompactSpace S] in
/-- A one-point (or empty) continuum is unicoherent. -/
theorem isUnicoherent_of_not_nontrivial {D : Set S} (hD : ¬ D.Nontrivial) : IsUnicoherent D := by
  intro H K hH hK hHK
  rw [Set.not_nontrivial_iff] at hD
  obtain ⟨x, hx⟩ := hH.2.nonempty
  obtain ⟨y, hy⟩ := hK.2.nonempty
  have hxy : x = y := hD (hHK ▸ Or.inl hx) (hHK ▸ Or.inr hy)
  subst hxy
  exact ⟨⟨x, hx, hy⟩, (hD.anti (inter_subset_left.trans (hHK ▸ subset_union_left))).isPreconnected⟩

/-- **Miller's Theorem 1.5 with the hypothesis that makes it true**: `A`, `B` hereditarily
unicoherent continua with `A ∪ B` unicoherent. Then every subcontinuum of `A ∪ B` is unicoherent
(`isHereditarilyUnicoherent_union`), so a non-unicoherent `D` does not exist and the conclusion
holds vacuously. -/
theorem miller_1_5_of_hu {A B D : Set S} (hA : Fold.Q78.IsContinuum A)
    (hB : Fold.Q78.IsContinuum B) (hAhu : IsHereditarilyUnicoherent A)
    (hBhu : IsHereditarilyUnicoherent B) (hu : IsUnicoherent (A ∪ B))
    (hD : Fold.Q78.IsContinuum D) (hDAB : D ⊆ A ∪ B) (hDnu : ¬ IsUnicoherent D) :
    D ⊆ A ∨ D ⊆ B := by
  exfalso
  by_cases hnt : D.Nontrivial
  · exact hDnu (isHereditarilyUnicoherent_union hA hB hAhu hBhu (hu A B hA hB rfl) D hDAB hD hnt)
  · exact hDnu (isUnicoherent_of_not_nontrivial hnt)

/-- **What Theorem 1 needs from Miller**: `A`, `B` snake-like (hence hereditarily unicoherent),
`A ∪ B` unicoherent ⇒ `A ∪ B` hereditarily unicoherent. Proved directly
(`isHereditarilyUnicoherent_union`), not through `miller_1_5`.

Shape change: the hypothesis `(A ∩ B).Nonempty` is not used (unicoherence of `A ∪ B` makes `A ∩ B`
a continuum) and has been removed. -/
theorem hu_union_of_snakeLike {A B : Set S} (hA : IsSnakeLike A) (hB : IsSnakeLike B)
    (hu : IsUnicoherent (A ∪ B)) : IsHereditarilyUnicoherent (A ∪ B) :=
  isHereditarilyUnicoherent_union hA.1 hB.1 (isHereditarilyUnicoherent_of_isSnakeLike hA)
    (isHereditarilyUnicoherent_of_isSnakeLike hB) (hu A B hA.1 hB.1 rfl)

/-! ## Lemma 4 -/

/-- **Fugate, Lemma 4 (the fitting).** `A`, `B` snake-like, `A ∩ B` terminal in both. For every
`ε > 0` there are `ε`-chains `E = E(0..m−1)` covering `A` and `F = F(0..n−1)` covering `B` and
indices `j ≤ m−1`, `k ≤ n−1`, `t` such that
1. both are taut `ε`-chains covering `A`, `B`;
2. `A ∩ B ⊆ᵉ E*(j..m−1)` and `A ∩ B ⊆ᵉ F*(k..n−1)` (Definition 5 in full);
3. `F(k..n−1)` is a closed refinement of `E(j..m−1)`;
4. `Cl E*(0..j−1) ∩ F* = ∅`;
5. `Cl F*(0..k−2) ∩ E* = ∅`;
6. if `k ≥ 1`: `j ≤ t ≤ m−1`, `Cl F_{k−1} ∩ A = ∅`, `Cl F_{k−1} ∩ E* ⊆ E_t`, and `Cl F_{k−1}` meets
   no other link of `E`.

Shape changes: the unused hypothesis `(A ∩ B).Nonempty` is removed (terminality includes it); the
index bounds in clause (6), which the skeleton's `by omega` could not see, are binders (`k < n` is
also part of clause (2)). If `k = 0` clause (6) is vacuous; when `B ⊄ A` and `ε` is small, `k ≥ 1`
automatically, and Theorem 1 handles `k = 0` separately (then `B ⊆ E*`).

Proof: the ℕ-indexed `fugate_lemma4_weak` (Fugate's construction), whose cut families are trimmed
to chains (`exists_chain_of_weak`): the cuts can destroy the overlap of consecutive links, but the
links meeting `A` (resp. `B`) form a run that keeps `E_j, …, E_{m−1}` (resp. `F_k, …, F_{n−1}`),
so only an initial segment is dropped and all clauses survive the shift of indices. -/
theorem fugate_lemma4 {A B : Set S} (hA : IsSnakeLike A) (hB : IsSnakeLike B)
    (hTA : IsTerminalSub A (A ∩ B)) (hTB : IsTerminalSub B (A ∩ B)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n : ℕ) (E : Chain S m) (F : Chain S n) (j k t : ℕ),
      IsEpsChain E ε ∧ IsEpsChain F ε ∧ IsTaut E ∧ IsTaut F ∧ A ⊆ E.union ∧ B ⊆ F.union ∧
      ContainedExactly' E (A ∩ B) j (m - 1) ∧ ContainedExactly' F (A ∩ B) k (n - 1) ∧
      (∀ i : Fin n, k ≤ i.val → ∃ i' : Fin m, j ≤ i'.val ∧ closure (F.link i) ⊆ E.link i') ∧
      Disjoint (closure (⋃ (i : Fin m) (_ : i.val < j), E.link i)) F.union ∧
      Disjoint (closure (⋃ (i : Fin n) (_ : i.val + 2 ≤ k), F.link i)) E.union ∧
      (∀ (hk : 1 ≤ k) (hkn : k < n), ∃ htm : t < m, j ≤ t ∧
        Disjoint (closure (F.link ⟨k - 1, by omega⟩)) A ∧
        closure (F.link ⟨k - 1, by omega⟩) ∩ E.union ⊆ E.link ⟨t, htm⟩ ∧
        ∀ i : Fin m, i.val ≠ t → Disjoint (closure (F.link ⟨k - 1, by omega⟩)) (E.link i)) := by
  classical
  obtain ⟨m, n, j, k, t, E, F, hf⟩ := fugate_lemma4_weak hA hB hTA hTB hε
  obtain ⟨cj, hcjC, hcj, hcjo⟩ := hf.exE_first
  obtain ⟨cm, hcmC, hcm, hcmo⟩ := hf.exE_last
  obtain ⟨ck, hckC, hck, hcko⟩ := hf.exF_first
  obtain ⟨cn, hcnC, hcn, hcno⟩ := hf.exF_last
  have hAcov : A ⊆ ⋃ i, ⋃ (_ : i < m), E i := fun x hx => by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hf.covA hx); exact mem_iUnion₂.mpr ⟨i, hf.lt_m hi, hi⟩
  have hBcov : B ⊆ ⋃ i, ⋃ (_ : i < n), F i := fun x hx => by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hf.covB hx); exact mem_iUnion₂.mpr ⟨i, hf.lt_n hi, hi⟩
  obtain ⟨a, m', E', haj, -, ham, hEL, hAE', -, hrange⟩ := exists_chain_of_weak E hf.openE
    (fun i l h _ => hf.weakE i l h) hA.1.2.isPreconnected hAcov hf.jm ⟨cj, hcj, hcjC.1⟩
  have ham' : a + m' = m := by
    have := hrange (m - 1) (by have := hf.jm; omega) ⟨cm, hcm, hcmC.1⟩; omega
  obtain ⟨a', n', F', hak, -, han, hFL, hBF', -, hrange'⟩ := exists_chain_of_weak F hf.openF
    (fun i l h _ => hf.weakF i l h) hB.1.2.isPreconnected hBcov hf.kn ⟨ck, hck, hckC.2⟩
  have han' : a' + n' = n := by
    have := hrange' (n - 1) (by have := hf.kn; omega) ⟨cn, hcn, hcnC.2⟩; omega
  have hjm := hf.jm
  have hkn := hf.kn
  have hjt := hf.jt
  have htm := hf.tm
  refine ⟨m', n', E', F', j - a, k - a', t - a, fun i => by rw [hEL i]; exact hf.smallE _,
    fun i => by rw [hFL i]; exact hf.smallF _, fun i l hil => ?_, fun i l hil => ?_, hAE', hBF',
    ⟨by omega, by omega, ?_, ⟨cj, hcjC, ?_, ?_⟩, ⟨cm, hcmC, ?_, ?_⟩, ?_, ?_⟩,
    ⟨by omega, by omega, ?_, ⟨ck, hckC, ?_, ?_⟩, ⟨cn, hcnC, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- `E'` taut
    refine infDist'_pos (E'.link_nonempty i) (E'.link_nonempty l) ?_
    rw [hEL, hEL]
    rcases hil with h | h
    · exact (hf.tautE _ _ (by omega)).symm
    · exact hf.tautE _ _ (by omega)
  · -- `F'` taut
    refine infDist'_pos (F'.link_nonempty i) (F'.link_nonempty l) ?_
    rw [hFL, hFL]
    rcases hil with h | h
    · exact (hf.tautF _ _ (by omega)).symm
    · exact hf.tautF _ _ (by omega)
  · -- (2) for `E'`: covering
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hAE' hx.1)
    rw [hEL] at hi
    refine mem_iUnion₂.mpr ⟨i, ⟨?_, by omega⟩, by rw [hEL]; exact hi⟩
    by_contra h
    exact (eq_empty_iff_forall_notMem.mp hf.exE_cl) x
      ⟨hx, subset_closure (mem_iUnion₂.mpr ⟨a + i.val, by omega, hi⟩)⟩
  · rw [hEL]; convert hcj using 2; simp only []; omega
  · intro h
    obtain ⟨i, hi, hci⟩ := mem_iUnion₂.mp h
    rw [hEL] at hci
    exact hcjo _ (by omega) hci
  · rw [hEL]; convert hcm using 2; simp only []; omega
  · intro h
    obtain ⟨i, hi, hci⟩ := mem_iUnion₂.mp h
    rw [hEL] at hci
    exact hcmo _ (by omega) hci
  · refine eq_empty_of_subset_empty (hf.exE_cl ▸ inter_subset_inter_right _ (closure_mono ?_))
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    rw [hEL] at hxi
    exact mem_iUnion₂.mpr ⟨a + i.val, by omega, hxi⟩
  · have : (⋃ (i : Fin m') (_ : m' - 1 < i.val), E'.link i) = ∅ := by
      ext z
      simp only [mem_iUnion, mem_empty_iff_false, iff_false, not_exists]
      intro i hi; omega
    rw [this, closure_empty, inter_empty]
  · -- (2) for `F'`: covering
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hBF' hx.2)
    rw [hFL] at hi
    refine mem_iUnion₂.mpr ⟨i, ⟨?_, by omega⟩, by rw [hFL]; exact hi⟩
    by_contra h
    exact (eq_empty_iff_forall_notMem.mp hf.exF_cl) x
      ⟨hx, subset_closure (mem_iUnion₂.mpr ⟨a' + i.val, by omega, hi⟩)⟩
  · rw [hFL]; convert hck using 2; simp only []; omega
  · intro h
    obtain ⟨i, hi, hci⟩ := mem_iUnion₂.mp h
    rw [hFL] at hci
    exact hcko _ (by omega) hci
  · rw [hFL]; convert hcn using 2; simp only []; omega
  · intro h
    obtain ⟨i, hi, hci⟩ := mem_iUnion₂.mp h
    rw [hFL] at hci
    exact hcno _ (by omega) hci
  · refine eq_empty_of_subset_empty (hf.exF_cl ▸ inter_subset_inter_right _ (closure_mono ?_))
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    rw [hFL] at hxi
    exact mem_iUnion₂.mpr ⟨a' + i.val, by omega, hxi⟩
  · have : (⋃ (i : Fin n') (_ : n' - 1 < i.val), F'.link i) = ∅ := by
      ext z
      simp only [mem_iUnion, mem_empty_iff_false, iff_false, not_exists]
      intro i hi; omega
    rw [this, closure_empty, inter_empty]
  · -- (3)
    intro i hi
    obtain ⟨i'', hji'', hi''m, hsub⟩ := hf.refine (a' + i.val) (by omega) (by omega)
    refine ⟨⟨i'' - a, by omega⟩, by simp only []; omega, ?_⟩
    rw [hFL, hEL, show a + (i'' - a) = i'' by omega]
    exact hsub
  · -- (4)
    refine Set.disjoint_left.mpr fun x hx hxF => ?_
    have hx' : x ∈ closure (⋃ l, ⋃ (_ : l < j), E l) := closure_mono (fun y hy => by
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
      rw [hEL] at hyi
      exact mem_iUnion₂.mpr ⟨a + i.val, by omega, hyi⟩) hx
    obtain ⟨l, hl, hxl⟩ := mem_closure_biUnion_lt hx'
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxF
    rw [hFL] at hxi
    exact Set.disjoint_left.mp (hf.four l _ hl) hxl hxi
  · -- (5)
    refine Set.disjoint_left.mpr fun x hx hxE => ?_
    have hx' : x ∈ closure (⋃ l, ⋃ (_ : l + 2 ≤ k), F l) := closure_mono (fun y hy => by
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
      rw [hFL] at hyi
      exact mem_iUnion₂.mpr ⟨a' + i.val, by omega, hyi⟩) hx
    obtain ⟨l, hl, hxl⟩ := mem_closure_biUnion_add_two_le hx'
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxE
    rw [hEL] at hxi
    exact Set.disjoint_left.mp (hf.five l _ hl) hxl hxi
  · -- (6)
    intro hk1 hkn'
    have hF1 : F'.link ⟨k - a' - 1, by omega⟩ = F (k - 1) := by
      rw [hFL]; congr 1; simp only []; omega
    have hk' : 1 ≤ k := by omega
    refine ⟨by omega, by omega, ?_, ?_, fun i hi => ?_⟩
    · rw [hF1]; exact hf.sixA hk'
    · rintro x ⟨hxF, hxE⟩
      rw [hF1] at hxF
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxE
      rw [hEL] at hxi
      have hit : a + i.val = t := by
        by_contra h
        exact Set.disjoint_left.mp (hf.sixt hk' _ h) hxF hxi
      rw [hEL, show a + (t - a) = t by omega]
      rwa [hit] at hxi
    · rw [hF1, hEL]
      exact hf.sixt hk' _ (by omega)

/-! ## Theorem 1, sufficiency -/

/-- **Fugate, Theorem 1 (sufficiency)**, from Lemma 4 by the two-case construction of
pp. 466–467 (`fugate_theorem1_sufficiency_hu`), with hereditary unicoherence of `A ∪ B` supplied by
`hu_union_of_snakeLike`. -/
theorem fugate_theorem1_sufficiency {A B : Set S} (hA : IsSnakeLike A) (hB : IsSnakeLike B)
    (hAB : (A ∩ B).Nonempty) (hat : IsAtriodic (A ∪ B)) (hu : IsUnicoherent (A ∪ B)) :
    IsSnakeLike (A ∪ B) :=
  fugate_theorem1_sufficiency_of_unicoherent hA hB hAB hat hu

alias fugate_theorem1_sufficiency' := fugate_theorem1_sufficiency

/-- **Fugate, Theorem 1.** `A`, `B` snake-like with `A ∩ B ≠ ∅`: `A ∪ B` is snake-like iff it is
atriodic and unicoherent. -/
theorem fugate_theorem1 {A B : Set S} (hA : IsSnakeLike A) (hB : IsSnakeLike B)
    (hAB : (A ∩ B).Nonempty) :
    IsSnakeLike (A ∪ B) ↔ IsAtriodic (A ∪ B) ∧ IsUnicoherent (A ∪ B) :=
  ⟨fugate_theorem1_necessity, fun h => fugate_theorem1_sufficiency' hA hB hAB h.1 h.2⟩

alias fugate_theorem1' := fugate_theorem1

/-! ## Corollary 1 -/

omit [CompactSpace S] in
/-- Atriodicity passes to subsets. -/
theorem IsAtriodic.mono {T U : Set S} (h : IsAtriodic T) (hUT : U ⊆ T) : IsAtriodic U :=
  fun X hX => h X (hX.trans hUT)

/-- **Corollary 1, with the hypothesis Fugate's induction needs**: the whole union hereditarily
unicoherent (hence so is every partial union, and every partial union is atriodic). Induction on
the number of pieces through `fugate_theorem1_sufficiency_hu`.

Fugate's own hypothesis (the union unicoherent) is not reached: the two-piece reduction
`hu_union_of_snakeLike` needs the partial union `A_0 ∪ … ∪ A_i` to meet `A_{i+1}` in a connected
set, which unicoherence of the whole union does not obviously give (REPORT-batch101.md,
item 5). -/
theorem fugate_cor1' {k : ℕ} (A : Fin (k + 1) → Set S) (hA : ∀ i, IsSnakeLike (A i))
    (hmeet : ∀ i : Fin k, (A i.castSucc ∩ A i.succ).Nonempty)
    (hat : IsAtriodic (⋃ i, A i)) (hhu : IsHereditarilyUnicoherent (⋃ i, A i)) :
    IsSnakeLike (⋃ i, A i) := by
  set U : ℕ → Set S := fun p => ⋃ (l : Fin (k + 1)) (_ : l.val ≤ p), A l with hU
  have hUsub : ∀ p, U p ⊆ ⋃ i, A i := fun p => iUnion₂_subset fun l _ => subset_iUnion A l
  have key : ∀ p, p ≤ k → IsSnakeLike (U p) := by
    intro p
    induction p with
    | zero =>
      intro _
      have : U 0 = A 0 := by
        ext x
        simp only [hU, mem_iUnion, exists_prop, nonpos_iff_eq_zero]
        constructor
        · rintro ⟨l, hl, hx⟩
          rwa [show l = 0 from Fin.ext hl] at hx
        · intro hx; exact ⟨0, rfl, hx⟩
      rw [this]; exact hA 0
    | succ p ih =>
      intro hp
      have hsplit : U (p + 1) = U p ∪ A ⟨p + 1, by omega⟩ := by
        ext x
        simp only [hU, mem_iUnion, mem_union, exists_prop]
        constructor
        · rintro ⟨l, hl, hx⟩
          rcases Nat.lt_or_ge l.val (p + 1) with h | h
          · exact Or.inl ⟨l, by omega, hx⟩
          · right; rwa [show l = ⟨p + 1, by omega⟩ from Fin.ext (by simp only []; omega)] at hx
        · rintro (⟨l, hl, hx⟩ | hx)
          · exact ⟨l, by omega, hx⟩
          · exact ⟨⟨p + 1, by omega⟩, le_rfl, hx⟩
      rw [hsplit]
      refine fugate_theorem1_sufficiency_hu (ih (by omega)) (hA _) ?_
        (hat.mono (hsplit ▸ hUsub (p + 1))) (hhu.mono (hsplit ▸ hUsub (p + 1)))
      obtain ⟨x, hx1, hx2⟩ := hmeet ⟨p, by omega⟩
      exact ⟨x, mem_iUnion₂.mpr ⟨⟨p, by omega⟩, le_rfl, hx1⟩, hx2⟩
  have : (⋃ i, A i) = U k := by
    ext x
    simp only [hU, mem_iUnion, exists_prop]
    exact ⟨fun ⟨l, hx⟩ => ⟨l, by omega, hx⟩, fun ⟨l, _, hx⟩ => ⟨l, hx⟩⟩
  rw [this]; exact key k le_rfl

/-- **Corollary 1** (both directions), under hereditary unicoherence of the union: the union of a
finite chain of snake-like continua is snake-like iff it is atriodic. (A snake-like continuum is
unicoherent, so with hereditary unicoherence assumed, unicoherence is automatic.) -/
theorem fugate_cor1_iff {k : ℕ} (A : Fin (k + 1) → Set S) (hA : ∀ i, IsSnakeLike (A i))
    (hmeet : ∀ i : Fin k, (A i.castSucc ∩ A i.succ).Nonempty)
    (hhu : IsHereditarilyUnicoherent (⋃ i, A i)) :
    IsSnakeLike (⋃ i, A i) ↔ IsAtriodic (⋃ i, A i) :=
  ⟨fun h => (fugate_cor1_necessity A h).1, fun h => fugate_cor1' A hA hmeet h hhu⟩

/-! ## Corollary 2 -/

/-- **Fugate, Corollary 2.** A decomposable unicoherent continuum all of whose proper subcontinua
are snake-like is snake-like (batch 100's `fugate_cor2_of_theorem1`, with Theorem 1 now
proved). -/
theorem fugate_cor2 {M : Set S} (hM : Fold.Q78.IsContinuum M) (hu : IsUnicoherent M)
    (hdec : ∃ A B : Set S, Fold.Q78.IsContinuum A ∧ Fold.Q78.IsContinuum B ∧ A ≠ M ∧ B ≠ M ∧
      A ∪ B = M)
    (hsub : ∀ K ⊆ M, Fold.Q78.IsContinuum K → K ≠ M → IsSnakeLike K) : IsSnakeLike M :=
  fugate_cor2_of_theorem1 (fun _ _ hA hB hAB hat hu => fugate_theorem1_sufficiency' hA hB hAB hat hu)
    hM hu hdec hsub

alias fugate_cor2' := fugate_cor2

end HPC.Plane
