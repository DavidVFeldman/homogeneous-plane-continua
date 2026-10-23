import HPC.Moore.Defs

/-!
# Moore, F.A. (1916), §3: Theorems 1–9 and "`M'` is closed" (batch 137, item B)

The section heading of F.A. §3 is "Consequences of Axioms 1–3, 5₁". Each theorem below carries
only the axioms its proof uses (a shape change from the skeleton, which included all four for
every statement); the axioms used are listed in each docstring:

| statement | axioms used |
|---|---|
| Theorem 1, "`M'` is closed" | none |
| Theorems 2, 3, 6, 7, 8, 9 | Axiom 1 |
| Theorems 4, 5 | Axioms 1, 3, 5₁ |

Theorem 4 (and everything resting on it) needs the region to be nonempty: Moore's proof opens
with "There exists in `R` at least one point `O`". The printed statement is false when `∅` is a
region, and the axioms do not exclude `∅` (`HPC/Moore/Refute.lean`).

Theorem 10 is in `HPC/Moore/Chains.lean`.
-/

namespace HPC.Moore

open Set

variable {S : Type*} {σ : Space S}

namespace Space

/-! ### Generic facts (no axioms) -/

theorem subset_cl (M : Set S) : M ⊆ σ.cl M := subset_union_left

/-- A point outside `M` lying in a region that misses `M` is not in `M'`. -/
theorem notMem_cl_of_region {M : Set S} {X : S} (hXM : X ∉ M) {V : Set S} (hV : V ∈ σ.region)
    (hXV : X ∈ V) (hVM : Disjoint V M) : X ∉ σ.cl M := by
  rintro (h | h)
  · exact hXM h
  · obtain ⟨⟨y, hyV, hyM⟩, -⟩ := h V hV hXV
    exact disjoint_left.mp hVM hyV hyM

/-- A point outside `M'` lies in a region that misses `M`. -/
theorem exists_region_disjoint_of_notMem_cl {M : Set S} {X : S} (hX : X ∉ σ.cl M) :
    ∃ V ∈ σ.region, X ∈ V ∧ Disjoint V M := by
  have hXM : X ∉ M := fun h => hX (Or.inl h)
  have hXb : X ∉ σ.bdry M := fun h => hX (Or.inr h)
  simp only [bdry, mem_setOf_eq, not_forall] at hXb
  obtain ⟨V, hV, hXV, hn⟩ := hXb
  refine ⟨V, hV, hXV, ?_⟩
  rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
  exact fun h => hn ⟨h, ⟨X, hXV, hXM⟩⟩

/-- A boundary point of `M` not in `M` is a limit point of `M`. -/
theorem isLimitPt_of_mem_bdry {M : Set S} {X : S} (hX : X ∈ σ.bdry M) (hXM : X ∉ M) :
    σ.IsLimitPt X M := by
  intro R hR hXR
  obtain ⟨⟨y, hyR, hyM⟩, -⟩ := hX R hR hXR
  exact ⟨y, hyM, hyR, fun h => hXM (h ▸ hyM)⟩

/-- A limit point of `M` not in `M` is a boundary point of `M`. -/
theorem mem_bdry_of_isLimitPt {M : Set S} {X : S} (hX : σ.IsLimitPt X M) (hXM : X ∉ M) :
    X ∈ σ.bdry M := by
  intro R hR hXR
  obtain ⟨y, hyM, hyR, -⟩ := hX R hR hXR
  exact ⟨⟨y, hyR, hyM⟩, ⟨X, hXR, hXM⟩⟩

theorem mem_cl_of_isLimitPt {M : Set S} {X : S} (hX : σ.IsLimitPt X M) : X ∈ σ.cl M := by
  by_cases hXM : X ∈ M
  · exact Or.inl hXM
  · exact Or.inr (mem_bdry_of_isLimitPt hX hXM)

theorem IsLimitPt.mono {M N : Set S} {X : S} (h : σ.IsLimitPt X M) (hMN : M ⊆ N) :
    σ.IsLimitPt X N := fun R hR hXR => by
  obtain ⟨y, hyM, hyR, hyX⟩ := h R hR hXR
  exact ⟨y, hMN hyM, hyR, hyX⟩

/-! ### The fundamental sequence -/

/-- `K` is a *fundamental sequence* (F.A. p. 133, footnote §): it satisfies the two conditions
of Axiom 1, so that `σ.Axiom1 ↔ ∃ K, σ.IsFund K`. -/
def IsFund (K : ℕ → Set S) : Prop :=
  (∀ n, K n ∈ σ.region) ∧ (∀ (m : ℕ) (P : S), ∃ n > m, P ∈ K n) ∧
    ∀ R ∈ σ.region, ∀ P ∈ R, ∀ P' ∈ R, P ≠ P' →
      ∃ δ : ℕ, ∀ n > δ, P ∈ K n → σ.cl (K n) ⊆ R \ {P'}

theorem axiom1_iff : σ.Axiom1 ↔ ∃ K, σ.IsFund K := Iff.rfl

/-- Axiom 1, condition (2), in the form used throughout: arbitrarily late fundamental regions
about `P` lie, with their boundaries, in `R − P'`. -/
theorem IsFund.exists_late {K : ℕ → Set S} (hK : σ.IsFund K) {R : Set S} (hR : R ∈ σ.region)
    {P P' : S} (hP : P ∈ R) (hP' : P' ∈ R) (hne : P ≠ P') (m : ℕ) :
    ∃ n > m, P ∈ K n ∧ σ.cl (K n) ⊆ R \ {P'} := by
  obtain ⟨δ, hδ⟩ := hK.2.2 R hR P hP P' hP' hne
  obtain ⟨n, hn, hPn⟩ := hK.2.1 (max m δ) P
  exact ⟨n, lt_of_le_of_lt (le_max_left _ _) hn, hPn,
    hδ n (lt_of_le_of_lt (le_max_right _ _) hn) hPn⟩

variable (h1 : σ.Axiom1)
include h1

/-- Every point lies in a region (Axiom 1 (1)). -/
theorem exists_region_mem (P : S) : ∃ R ∈ σ.region, P ∈ R := by
  obtain ⟨K, hK, hK1, -⟩ := h1
  obtain ⟨n, -, hn⟩ := hK1 0 P
  exact ⟨K n, hK n, hn⟩

/-- Axiom 1 (2) for an arbitrary region. -/
theorem exists_region_cl_subset_diff {R : Set S} (hR : R ∈ σ.region) {P P' : S} (hP : P ∈ R)
    (hP' : P' ∈ R) (hne : P ≠ P') : ∃ K ∈ σ.region, P ∈ K ∧ σ.cl K ⊆ R \ {P'} := by
  have hK' : ∃ K, σ.IsFund K := h1
  obtain ⟨K, hK⟩ := hK'
  obtain ⟨n, -, hPn, hcl⟩ := hK.exists_late hR hP hP' hne 0
  exact ⟨K n, hK.1 n, hPn, hcl⟩

end Space

open Space

/-- **Theorem 1.** No point of a region is a boundary point of that region. (No proof printed.)
*Axioms used: none* — `R` itself is a region containing `P` with `R − R = ∅`. -/
theorem fa_theorem1 {R : Set S} (hR : R ∈ σ.region) {P : S} (hP : P ∈ R) :
    P ∉ σ.bdry R := by
  intro h
  obtain ⟨-, x, hx1, hx2⟩ := h R hR hP
  exact hx2 hx1

/-- **Theorem 3.** If `M` is finite and `P ∉ M`, some region contains `P` and no point of `M`.
(No proof printed.) *Axioms used: 1.* Induction on `M`: a region `R ∋ P` missing `M` either misses
a new point `a`, or Axiom 1 (2) gives a region about `P` inside `R − a`. -/
theorem fa_theorem3 (h1 : σ.Axiom1) {P : S} {M : Set S} (hM : M.Finite) (hPM : P ∉ M) :
    ∃ R ∈ σ.region, P ∈ R ∧ Disjoint R M := by
  induction M, hM using Set.Finite.induction_on with
  | empty =>
    obtain ⟨R, hR, hPR⟩ := exists_region_mem h1 P
    exact ⟨R, hR, hPR, disjoint_empty R⟩
  | @insert a M _ _ ih =>
    have haP : P ≠ a := fun h => hPM (h ▸ mem_insert a M)
    obtain ⟨R, hR, hPR, hRM⟩ := ih (fun h => hPM (mem_insert_of_mem a h))
    by_cases haR : a ∈ R
    · obtain ⟨K, hK, hPK, hcl⟩ := exists_region_cl_subset_diff h1 hR hPR haR haP
      refine ⟨K, hK, hPK, disjoint_insert_right.mpr ⟨fun h => ?_, ?_⟩⟩
      · exact (hcl (subset_cl K h)).2 rfl
      · exact hRM.mono_left fun x hx => (hcl (subset_cl K hx)).1
    · exact ⟨R, hR, hPR, disjoint_insert_right.mpr ⟨haR, hRM⟩⟩

/-- **Theorem 6.** Two regions with a common point `P` contain a common region about `P`.
*Axioms used: 1.* (Moore derives it from Theorem 5; Axiom 1 (2) gives it directly, the case of a
region with only the point `P` being trivial.) -/
theorem fa_theorem6 (h1 : σ.Axiom1) {K L : Set S} (hK : K ∈ σ.region) (hL : L ∈ σ.region)
    {P : S} (hPK : P ∈ K) (hPL : P ∈ L) : ∃ R ∈ σ.region, P ∈ R ∧ R ⊆ K ∩ L := by
  by_cases hK' : ∃ P' ∈ K, P' ≠ P
  · by_cases hL' : ∃ Q' ∈ L, Q' ≠ P
    · obtain ⟨P', hP'K, hP'P⟩ := hK'
      obtain ⟨Q', hQ'L, hQ'P⟩ := hL'
      obtain ⟨F, hF⟩ := h1
      obtain ⟨δ₁, hδ₁⟩ := hF.2.2 K hK P hPK P' hP'K hP'P.symm
      obtain ⟨δ₂, hδ₂⟩ := hF.2.2 L hL P hPL Q' hQ'L hQ'P.symm
      obtain ⟨n, hn, hPn⟩ := hF.2.1 (max δ₁ δ₂) P
      refine ⟨F n, hF.1 n, hPn, fun x hx => ⟨?_, ?_⟩⟩
      · exact (hδ₁ n (lt_of_le_of_lt (le_max_left _ _) hn) hPn (subset_cl _ hx)).1
      · exact (hδ₂ n (lt_of_le_of_lt (le_max_right _ _) hn) hPn (subset_cl _ hx)).1
    · push_neg at hL'
      exact ⟨L, hL, hPL, fun x hx => ⟨hL' x hx ▸ hPK, hx⟩⟩
  · push_neg at hK'
    exact ⟨K, hK, hPK, fun x hx => ⟨hx, hK' x hx ▸ hPL⟩⟩

/-- **Theorem 2.** If `P` is a limit point of `M`, every region containing `P` contains infinitely
many points of `M`. *Axioms used: 1* (through Theorems 3 and 6). -/
theorem fa_theorem2 (h1 : σ.Axiom1) {P : S} {M : Set S} (hP : σ.IsLimitPt P M) {R : Set S}
    (hR : R ∈ σ.region) (hPR : P ∈ R) : (R ∩ M).Infinite := by
  intro hfin
  obtain ⟨R₁, hR₁, hPR₁, hdis⟩ :=
    fa_theorem3 h1 (hfin.diff (t := {P})) (fun h => h.2 rfl)
  obtain ⟨R₂, hR₂, hPR₂, hsub⟩ := fa_theorem6 h1 hR hR₁ hPR hPR₁
  obtain ⟨x, hxM, hxR₂, hxP⟩ := hP R₂ hR₂ hPR₂
  exact disjoint_left.mp hdis (hsub hxR₂).2 ⟨⟨(hsub hxR₂).1, hxM⟩, hxP⟩

/-- No point is a limit point of a one-point set (Theorem 3). *Axioms used: 1.* -/
theorem not_isLimitPt_singleton (h1 : σ.Axiom1) (X O : S) : ¬ σ.IsLimitPt X {O} := by
  intro h
  by_cases hXO : X = O
  · subst hXO
    obtain ⟨R, hR, hXR⟩ := exists_region_mem h1 X
    obtain ⟨y, hy, -, hyX⟩ := h R hR hXR
    exact hyX hy
  · obtain ⟨R, hR, hXR, hdis⟩ :=
      fa_theorem3 h1 (finite_singleton O) (fun h => hXO h)
    obtain ⟨y, hy, hyR, -⟩ := h R hR hXR
    exact disjoint_left.mp hdis hyR hy

/-- **Regularity** (Axiom 1): every region about `P` contains, with its boundary, a region about
`P`. If the region has a second point this is Axiom 1 (2); if it is `{P}`, it is its own `M'`. -/
theorem exists_region_cl_subset (h1 : σ.Axiom1) {R : Set S} (hR : R ∈ σ.region) {P : S}
    (hP : P ∈ R) : ∃ K ∈ σ.region, P ∈ K ∧ σ.cl K ⊆ R := by
  by_cases h : ∃ P' ∈ R, P' ≠ P
  · obtain ⟨P', hP', hne⟩ := h
    obtain ⟨K, hK, hPK, hcl⟩ := exists_region_cl_subset_diff h1 hR hP hP' hne.symm
    exact ⟨K, hK, hPK, hcl.trans diff_subset⟩
  · push_neg at h
    refine ⟨R, hR, hP, fun X hX => ?_⟩
    by_contra hXR
    have hXP : X ≠ P := fun h' => hXR (h' ▸ hP)
    obtain ⟨V, hV, hXV, hdis⟩ := fa_theorem3 h1 (finite_singleton P) (fun h' => hXP h')
    refine notMem_cl_of_region hXR hV hXV ?_ hX
    exact disjoint_left.mpr fun y hyV hyR => disjoint_left.mp hdis hyV (h y hyR)

/-- **Theorem 4.** Every (nonempty) region contains infinitely many points.
*Axioms used: 1, 3, 5₁.* **Shape change:** the hypothesis `R.Nonempty` is added. Moore's proof
begins "There exists in `R` at least one point `O`"; for `R = ∅` the printed statement fails, and
`∅` may be a region (`HPC/Moore/Refute.lean`, `not_fa_theorem4_printed`). -/
theorem fa_theorem4 (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h51 : Space.Axiom5₁ (S := S)) {R : Set S}
    (hR : R ∈ σ.region) (hne : R.Nonempty) : R.Infinite := by
  obtain ⟨O, hO⟩ := hne
  obtain ⟨P₁, P₂, hP₁O, hP₂O, hP₁₂⟩ : ∃ P₁ P₂ : S, P₁ ≠ O ∧ P₂ ≠ O ∧ P₁ ≠ P₂ := by
    obtain ⟨a, b, c, hab, hbc, hac⟩ := h51
    by_cases haO : a = O
    · subst haO; exact ⟨b, c, hab.symm, hac.symm, hbc⟩
    · by_cases hbO : b = O
      · subst hbO; exact ⟨a, c, haO, fun h => hbc h.symm, hac⟩
      · exact ⟨a, b, haO, hbO, hab⟩
  obtain ⟨R₁, hR₁, hP₁R₁, hdis⟩ := fa_theorem3 h1 (P := P₁) (M := {O, P₂}) (toFinite _)
    (by simp [hP₁O, hP₁₂])
  have hOR₁ : O ∉ R₁ := fun h => disjoint_left.mp hdis h (by simp)
  have hP₂R₁ : P₂ ∉ R₁ := fun h => disjoint_left.mp hdis h (by simp)
  obtain ⟨K, hK, hP₁K, hclK⟩ := exists_region_cl_subset h1 hR₁ hP₁R₁
  have hOK : O ∈ σ.ext K := fun h => hOR₁ (hclK h)
  have hP₂K : P₂ ∈ σ.ext K := fun h => hP₂R₁ (hclK h)
  have hsplit : {O} ∪ (σ.ext K \ {O}) = σ.ext K := union_diff_cancel (singleton_subset_iff.mpr hOK)
  rcases h3 K hK {O} (σ.ext K \ {O}) hsplit disjoint_sdiff_right (singleton_nonempty O)
      ⟨P₂, hP₂K, hP₂O⟩ with ⟨x, hx, hlim⟩ | ⟨x, -, hlim⟩
  · rw [mem_singleton_iff] at hx
    subst hx
    exact (fa_theorem2 h1 hlim hR hO).mono inter_subset_left
  · exact absurd hlim (not_isLimitPt_singleton h1 x O)

/-- A nonempty region has a point other than any given point. -/
theorem exists_ne_of_region (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h51 : Space.Axiom5₁ (S := S)) {R : Set S}
    (hR : R ∈ σ.region) {P : S} (hP : P ∈ R) : ∃ P' ∈ R, P' ≠ P :=
  let ⟨P', hP', hne⟩ := ((fa_theorem4 h1 h3 h51 hR ⟨P, hP⟩).diff (finite_singleton P)).nonempty
  ⟨P', hP', hne⟩

/-- **Theorem 5.** For each point `P`, a strictly decreasing sequence of regions with
intersection `{P}` that closes down on `P`: every region about `P` contains some `Rₙ'`.
*Axioms used: 1, 3, 5₁* (Theorem 4 makes each step possible). As in Moore's proof, `Rₙ₊₁` is a
fundamental region later than `Rₙ`, containing `P`, properly inside `Rₙ`. Condition (1) of the
printed theorem is a consequence of (3) and Theorem 3. -/
theorem fa_theorem5 (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h51 : Space.Axiom5₁ (S := S)) (P : S) :
    ∃ R : ℕ → Set S, (∀ n, R n ∈ σ.region) ∧ (⋂ n, R n) = {P} ∧ (∀ n, R (n + 1) ⊂ R n) ∧
      ∀ U ∈ σ.region, P ∈ U → ∃ n, σ.cl (R n) ⊆ U := by
  have hK' : ∃ K, σ.IsFund K := h1
  obtain ⟨K, hK⟩ := hK'
  have step : ∀ m : ℕ, P ∈ K m → ∃ n > m, P ∈ K n ∧ K n ⊂ K m := by
    intro m hm
    obtain ⟨P', hP', hne⟩ := exists_ne_of_region h1 h3 h51 (hK.1 m) hm
    obtain ⟨n, hn, hPn, hcl⟩ := hK.exists_late (hK.1 m) hm hP' hne.symm m
    refine ⟨n, hn, hPn, ⟨fun x hx => (hcl (subset_cl _ hx)).1, fun h => ?_⟩⟩
    exact (hcl (subset_cl _ (h hP'))).2 rfl
  choose g hg hPg hsub using step
  obtain ⟨k₀, -, hk₀⟩ := hK.2.1 0 P
  let f : ℕ → {m // P ∈ K m} := fun n =>
    Nat.rec ⟨k₀, hk₀⟩ (fun _ x => ⟨g x.1 x.2, hPg x.1 x.2⟩) n
  have hf : ∀ n, (f (n + 1)).1 = g (f n).1 (f n).2 := fun n => rfl
  have hmono : StrictMono fun n => (f n).1 :=
    strictMono_nat_of_lt_succ fun n => by rw [hf]; exact hg _ _
  have hclose : ∀ U ∈ σ.region, P ∈ U → ∃ n, σ.cl (K (f n).1) ⊆ U := by
    intro U hU hPU
    obtain ⟨P', hP', hne⟩ := exists_ne_of_region h1 h3 h51 hU hPU
    obtain ⟨δ, hδ⟩ := hK.2.2 U hU P hPU P' hP' hne.symm
    refine ⟨δ + 1, (hδ _ ?_ (f (δ + 1)).2).trans diff_subset⟩
    have := hmono.id_le (δ + 1)
    simp only [id] at this
    omega
  refine ⟨fun n => K (f n).1, fun n => hK.1 _, ?_, fun n => by
    simp only [hf]; exact hsub _ _, hclose⟩
  ext X
  simp only [mem_iInter, mem_singleton_iff]
  refine ⟨fun h => ?_, fun h n => h ▸ (f n).2⟩
  by_contra hXP
  obtain ⟨U, hU, hPU, hdis⟩ := fa_theorem3 h1 (finite_singleton X) (fun h' => hXP h'.symm)
  obtain ⟨n, hn⟩ := hclose U hU hPU
  exact disjoint_left.mp hdis (hn (subset_cl _ (h n))) rfl

/-- **Theorem 7.** A limit point of `M + N` is a limit point of `M` or of `N`. (No proof
printed.) *Axioms used: 1* (Theorem 6). -/
theorem fa_theorem7 (h1 : σ.Axiom1) {P : S} {M N : Set S} (h : σ.IsLimitPt P (M ∪ N)) :
    σ.IsLimitPt P M ∨ σ.IsLimitPt P N := by
  by_contra hc
  push_neg at hc
  obtain ⟨hM, hN⟩ := hc
  simp only [IsLimitPt, not_forall, not_exists, not_and, not_not] at hM hN
  obtain ⟨R₁, hR₁, hP₁, h₁⟩ := hM
  obtain ⟨R₂, hR₂, hP₂, h₂⟩ := hN
  obtain ⟨R₃, hR₃, hP₃, hsub⟩ := fa_theorem6 h1 hR₁ hR₂ hP₁ hP₂
  obtain ⟨x, hx, hxR, hxP⟩ := h R₃ hR₃ hP₃
  rcases hx with hx | hx
  · exact hxP (h₁ x hx (hsub hxR).1)
  · exact hxP (h₂ x hx (hsub hxR).2)

/-- **Theorem 8.** If `P` is the sequential limit point of `P₁, P₂, …`, no other point is a limit
point of `{P₁, P₂, …}`. *Axioms used: 1.* Moore uses Theorem 5 for a region `K ∋ P` with `K'`
inside a region missing `X`; the regularity lemma `exists_region_cl_subset` (Axiom 1 only) does
the same. -/
theorem fa_theorem8 (h1 : σ.Axiom1) {P : S} {u : ℕ → S} (hu : σ.IsSeqLimit P u) {X : S}
    (hX : X ≠ P) : ¬ σ.IsLimitPt X (range u) := by
  intro hlim
  obtain ⟨R, hR, hPR, hdis⟩ := fa_theorem3 h1 (finite_singleton X) (fun h => hX h.symm)
  obtain ⟨K, hK, hPK, hcl⟩ := exists_region_cl_subset h1 hR hPR
  have hXK : X ∉ σ.cl K := fun h => disjoint_left.mp hdis (hcl h) rfl
  obtain ⟨V, hV, hXV, hVK⟩ := exists_region_disjoint_of_notMem_cl hXK
  obtain ⟨δ, hδ⟩ := hu K hK hPK
  obtain ⟨W, hW, hXW, hWF⟩ := fa_theorem3 h1 (((finite_Iic δ).image u).diff (t := {X}))
    (fun h => h.2 rfl)
  obtain ⟨V', hV', hXV', hsub⟩ := fa_theorem6 h1 hV hW hXV hXW
  obtain ⟨y, ⟨n, rfl⟩, hyV', hyX⟩ := hlim V' hV' hXV'
  by_cases hn : n ≤ δ
  · exact disjoint_left.mp hWF (hsub hyV').2 ⟨⟨n, hn, rfl⟩, hyX⟩
  · exact disjoint_left.mp hVK (hsub hyV').1 (hδ n (by omega))

/-- **Theorem 9.** A limit point of `M` is the sequential limit point of a sequence of points of
`M` distinct from it. *Axioms used: 1.* The `n`-th term is taken in a fundamental region `K_m`
about `P` with `m > n` (Moore takes it in the `n`-th region of Theorem 5; "Zermelo's postulate" is
the `choose` below). Every region about a limit point has a second point, so Axiom 1 (2) applies to
it. -/
theorem fa_theorem9 (h1 : σ.Axiom1) {P : S} {M : Set S} (hP : σ.IsLimitPt P M) :
    ∃ u : ℕ → S, (∀ n, u n ∈ M ∧ u n ≠ P) ∧ σ.IsSeqLimit P u := by
  obtain ⟨K, hK0, hK1, hK2⟩ := h1
  choose m hm hPm using fun n => hK1 n P
  choose u huM huK huP using fun n => hP (K (m n)) (hK0 _) (hPm n)
  refine ⟨u, fun n => ⟨huM n, huP n⟩, fun U hU hPU => ?_⟩
  obtain ⟨x, -, hxU, hxP⟩ := hP U hU hPU
  obtain ⟨δ, hδ⟩ := hK2 U hU P hPU x hxU hxP.symm
  refine ⟨δ, fun n hn => ((hδ (m n) ?_ (hPm n)) (subset_cl _ (huK n))).1⟩
  have := hm n
  omega

/-- Unnumbered (p. 135): "It is clear that if `M` is a set of points then `M'` is closed."
*Axioms used: none.* A limit point `P ∉ M` of `M'` has, in each region `R` about it, a point
`x ∈ M'` with `x ≠ P`; if `x` is a boundary point of `M`, the region `R` (which contains `x`)
meets `M`. -/
theorem fa_cl_isClosed (M : Set S) : σ.IsClosedM (σ.cl M) := by
  intro P hP
  by_cases hPM : P ∈ M
  · exact Or.inl hPM
  refine Or.inr fun R hR hPR => ⟨?_, ⟨P, hPR, hPM⟩⟩
  obtain ⟨x, hx, hxR, -⟩ := hP R hR hPR
  rcases hx with hx | hx
  · exact ⟨x, hxR, hx⟩
  · exact (hx R hR hxR).1

end HPC.Moore
