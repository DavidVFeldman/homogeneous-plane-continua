import HPC.Plane.Sorgenfrey

/-!
# Batch 104: Bing's Theorem 11 (Duke 1951) by Fugate 1969, Case II

Saved from the uploaded skeleton as `HPC/Plane/Theorem11B.lean`; `import HPC.Plane.Theorem11B` is
added at the end of `HPC.lean`. No existing file was edited. Every item is proved, with no `sorry`;
`theorem11_1951` is the sorry-free form of Theorem 11 (the superseded `theorem11_1951_of_T10'` was
deleted from `Layers51.lean` in batch 105).

Shape changes (each also recorded at the declaration):
* `isTerminalSub_of_union_terminal`, `isTerminalSub_iInter`, `exists_terminal_point_of_isTerminalSub`:
  the unused hypothesis that `M` is a continuum is removed.
* `epsCoverable_of_halves`: `ε`-chains instead of `ε/2`-chains (stronger), and the unused
  hypotheses "`μ` in the closure of no other link" are removed.

Source: J. B. Fugate, *A characterization of chainable continua*, Canad. J. Math. 21 (1969),
383–393: Lemma 3, Lemma 4, Theorem 2 Case II (COMMISSION-batch104.md §1 transcribes them).
Fugate's arc structure `f : M → [0,1]` is replaced by the two sides of an element (batch 96) and
Theorem 8 (a). `IsTerminalSub` is batch 100's (Fugate's Definition 1 = Definition 4 of 1966).
-/

namespace HPC.Plane

open Set Topology Metric

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ## Fugate 1969, Lemmas 3 and 4 (hereditarily decomposable case) -/

omit [CompactSpace S] in
/-- The core contradiction in Fugate's Lemma 3. -/
theorem fugate69_lemma3_core {M K R T : Set S} {y p q x : S} (hhu : IsHereditarilyUnicoherent M)
    (hK : Fold.Q78.IsContinuum K) (hR : Fold.Q78.IsContinuum R)
    (hKM : K ⊆ M) (hRM : R ⊆ M) (hTM : T ⊆ M) (hyR : y ∈ R) (hyK : y ∈ K) (hpR : p ∈ R)
    (hred : ¬ IsIrreducibleBetween R y p) (hqK : q ∈ K) (hirrR : IsIrreducibleBetween (K ∪ R) q p)
    (hxR : x ∈ R) (hxK : x ∉ K) (hirrT : IsIrreducibleBetween (K ∪ T) y x) : False := by
  obtain ⟨L, hL, hLR, hyL, hpL, hLne⟩ : ∃ L, Fold.Q78.IsContinuum L ∧ L ⊆ R ∧ y ∈ L ∧ p ∈ L ∧
      L ≠ R := by
    by_contra h
    push_neg at h
    exact hred ⟨hR, hyR, hpR, fun L hL hLR hy hp => h L hL hLR hy hp⟩
  have hqL : q ∉ L := fun hq => hLne (Subset.antisymm hLR
    ((hirrR.2.2.2 L hL (hLR.trans subset_union_right) hq hpL).symm ▸ subset_union_right))
  have hLK : L ∪ K = K ∪ R := hirrR.2.2.2 _ (isContinuum_union hL hK ⟨y, hyL, hyK⟩)
    (union_subset (hLR.trans subset_union_right) subset_union_left) (Or.inr hqK) (Or.inl hpL)
  have hxL : x ∈ L := by
    have : x ∈ L ∪ K := hLK ▸ Or.inr hxR
    exact this.resolve_right hxK
  have hKT : Fold.Q78.IsContinuum (K ∪ T) := hirrT.1
  have hI : Fold.Q78.IsContinuum (L ∩ (K ∪ T)) :=
    isContinuum_inter_of_hu hhu hL hKT (hLR.trans hRM) (union_subset hKM hTM) ⟨y, hyL, Or.inl hyK⟩
  have := hirrT.2.2.2 _ hI inter_subset_right ⟨hyL, Or.inl hyK⟩ ⟨hxL, hirrT.2.2.1⟩
  have hq : q ∈ L ∩ (K ∪ T) := by rw [this]; exact Or.inl hqK
  exact hqL hq.1

/-- One half of Fugate's Lemma 3: from the non-terminality of `X` (where `K = X ∪ Y` is terminal
and `Y ≠ K`), a continuum `R ⊇ X` irreducible from no point of `X`, with `K ∪ R` irreducible from a
point `q ∈ Y ∖ X` to a point `p ∈ R ∖ K`. -/
theorem fugate69_lemma3_half {M K X Y : Set S} (hat : IsAtriodic M)
    (hhu : IsHereditarilyUnicoherent M) (hK : IsTerminalSub M K)
    (hX : Fold.Q78.IsContinuum X) (hY : Fold.Q78.IsContinuum Y) (hYK : Y ≠ K)
    (hXY : X ∪ Y = K) (hXT : ¬ IsTerminalSub M X) :
    ∃ R : Set S, Fold.Q78.IsContinuum R ∧ R ⊆ M ∧ X ⊆ R ∧
      (∀ a ∈ X, ∀ z, ¬ IsIrreducibleBetween R a z) ∧
      ∃ q p : S, q ∈ K ∧ q ∈ Y ∧ q ∉ X ∧ p ∈ R ∧ p ∉ K ∧ IsIrreducibleBetween (K ∪ R) q p := by
  have hKM : K ⊆ M := hK.2.1
  have hXK : X ⊆ K := hXY ▸ subset_union_left
  have hYK' : Y ⊆ K := hXY ▸ subset_union_right
  have hXM : X ⊆ M := hXK.trans hKM
  rw [isTerminalSub_iff_irreducible hat hhu hX hXM] at hXT
  push_neg at hXT
  obtain ⟨R₀, hR₀, hR₀M, hR₀X, hno⟩ := hXT
  set R := X ∪ R₀ with hR
  have hRc : Fold.Q78.IsContinuum R := isContinuum_union hX hR₀ (by
    obtain ⟨z, h1, h2⟩ := hR₀X; exact ⟨z, h2, h1⟩)
  have hRM : R ⊆ M := union_subset hXM hR₀M
  have hXR : X ⊆ R := subset_union_left
  have hdag : ∀ a ∈ X, ∀ z, ¬ IsIrreducibleBetween R a z := fun a ha z => hno a z ha
  have hRnt : R.Nontrivial := by
    by_contra h
    obtain ⟨a, ha⟩ := hX.2.nonempty
    have hRa : R = {a} := (Set.not_nontrivial_iff.mp h).eq_singleton_of_mem (hXR ha)
    refine hdag a ha a ⟨hRc, hXR ha, hXR ha, fun L hL hLR haL _ => ?_⟩
    rw [hRa] at hLR ⊢
    exact Subset.antisymm hLR (singleton_subset_iff.mpr haL)
  obtain ⟨r₁, r₂, -, hirr⟩ := exists_irreducibleBetween_of_atriodic hRc hRnt
    (fun T hT => hat T (hT.trans hRM)) (hhu.mono hRM)
  have hr₁ : r₁ ∉ X := fun h => hdag r₁ h r₂ hirr
  have hr₂ : r₂ ∉ X := fun h => hdag r₂ h r₁ hirr.symm
  have hRK : ¬ R ⊆ K := by
    intro hRK
    have h1 : r₁ ∈ Y := ((hXY.symm ▸ hRK hirr.2.1 : r₁ ∈ X ∪ Y)).resolve_left hr₁
    have h2 : r₂ ∈ Y := ((hXY.symm ▸ hRK hirr.2.2.1 : r₂ ∈ X ∪ Y)).resolve_left hr₂
    have hI := isContinuum_inter_of_hu hhu hRc hY hRM (hYK'.trans hKM) ⟨r₁, hirr.2.1, h1⟩
    have hRY : R ∩ Y = R := hirr.2.2.2 _ hI inter_subset_left ⟨hirr.2.1, h1⟩ ⟨hirr.2.2.1, h2⟩
    have : X ⊆ Y := fun z hz => (hRY.symm ▸ hXR hz : z ∈ R ∩ Y).2
    exact hYK (by rw [← hXY, union_eq_right.mpr this])
  obtain ⟨q, p, hqK, hirrK⟩ := (isTerminalSub_iff_irreducible hat hhu hK.1 hKM).mp hK R hRc hRM
    (by obtain ⟨a, ha⟩ := hX.2.nonempty; exact ⟨a, hXR ha, hXK ha⟩)
  have hpK : p ∉ K := by
    intro hpK
    have := hirrK.2.2.2 K hK.1 subset_union_left hqK hpK
    exact hRK (fun z hz => this.symm ▸ (Or.inr hz : z ∈ K ∪ R))
  have hpR : p ∈ R := (hirrK.2.2.1).resolve_left hpK
  have hqX : q ∉ X := by
    intro hqX
    have := hirrK.2.2.2 R hRc subset_union_right (hXR hqX) hpR
    exact hdag q hqX p (this ▸ hirrK)
  exact ⟨R, hRc, hRM, hXR, hdag, q, p, hqK, (hXY.symm ▸ hqK : q ∈ X ∪ Y).resolve_left hqX, hqX,
    hpR, hpK, hirrK⟩

/-- **Lemma 3.** `M` atriodic, hereditarily unicoherent; `K` terminal in `M`; `K = A ∪ B` with
`A`, `B` proper subcontinua of `K`. Then `A` or `B` is terminal in `M`. (Proof via Lemma 2 =
`isTerminalSub_iff_irreducible'`: `fugate69_lemma3_half` twice, then `fugate69_lemma3_core` in
either case of the terminality of `K`.) Shape change: the skeleton's hypothesis that `M` is a
continuum is not used and has been removed. Glosses: Fugate's "clearly `A ⊆ R`" is obtained by
replacing `R` with `R ∪ A`; his "`p ∈ R`" needs `R ⊄ K`, proved from Sorgenfrey's theorem (an
irreducible pair of `R` avoids `A`, so lies in `B`, forcing `A ⊆ R ⊆ B`); the case `R ⊆ S ∪ K` is
the mirror image, handled by the same core lemma. -/
theorem isTerminalSub_of_union_terminal {M K A B : Set S}
    (hat : IsAtriodic M) (hhu : IsHereditarilyUnicoherent M) (hK : IsTerminalSub M K)
    (hA : Fold.Q78.IsContinuum A) (hB : Fold.Q78.IsContinuum B) (hAK : A ≠ K) (hBK : B ≠ K)
    (hAB : A ∪ B = K) : IsTerminalSub M A ∨ IsTerminalSub M B := by
  by_contra hno
  rw [not_or] at hno
  obtain ⟨hAn, hBn⟩ := hno
  have hKM := hK.2.1
  obtain ⟨R, hR, hRM, hAR, hdagA, q, p, hqK, hqB, -, hpR, hpK, hirrR⟩ :=
    fugate69_lemma3_half hat hhu hK hA hB hBK hAB hAn
  obtain ⟨T, hT, hTM, hBT, hdagB, y, x, hyK, hyA, -, hxT, hxK, hirrT⟩ :=
    fugate69_lemma3_half hat hhu hK hB hA hAK (by rw [union_comm]; exact hAB) hBn
  obtain ⟨a, ha⟩ := hA.2.nonempty
  obtain ⟨b, hb⟩ := hB.2.nonempty
  have hAK' : A ⊆ K := hAB ▸ subset_union_left
  have hBK' : B ⊆ K := hAB ▸ subset_union_right
  rcases hK.2.2 R T hR hT hRM hTM ⟨a, hAR ha, hAK' ha⟩ ⟨b, hBT hb, hBK' hb⟩ with h | h
  · have hpT : p ∈ T := (h hpR).resolve_left hpK
    exact fugate69_lemma3_core (R := T) (T := R) hhu hK.1 hT hKM hTM hRM (hBT hqB) hqK hxT
      (hdagB q hqB x) hyK hirrT hpT hpK hirrR
  · have hxR : x ∈ R := (h hxT).resolve_right hxK
    exact fugate69_lemma3_core (R := R) (T := T) hhu hK.1 hR hKM hRM hTM (hAR hyA) hyK hpR
      (hdagA y hyA p) hqK hirrR hxR hxK hirrT

omit [CompactSpace S] in
/-- Terminality is inductive: the intersection of a decreasing sequence of terminal subcontinua
is terminal (Lemma 4's "Property P is inductive"). Shape change: the skeleton's hypothesis that `M`
is a continuum is not used and has been removed. Proof: one of the two alternatives of Definition 4
holds for infinitely many `n`, hence (the sequence decreasing) for all `n`. -/
theorem isTerminalSub_iInter {M : Set S} {N : ℕ → Set S}
    (hN : ∀ n, IsTerminalSub M (N n)) (hanti : Antitone N) : IsTerminalSub M (⋂ n, N n) := by
  refine ⟨isContinuum_iInter_antitone (fun n => (hN n).1) hanti,
    (iInter_subset _ 0).trans (hN 0).2.1, fun K L hK hL hKM hLM hKN hLN => ?_⟩
  have hmeet : ∀ {Z : Set S}, (Z ∩ ⋂ n, N n).Nonempty → ∀ n, (Z ∩ N n).Nonempty :=
    fun h n => h.mono (inter_subset_inter_right _ (iInter_subset _ n))
  have hor : ∀ n, K ⊆ N n ∪ L ∨ L ⊆ K ∪ N n := fun n =>
    (hN n).2.2 K L hK hL hKM hLM (hmeet hKN n) (hmeet hLN n)
  by_cases h1 : ∀ n, K ⊆ N n ∪ L
  · left
    intro z hz
    by_cases hzL : z ∈ L
    · exact Or.inr hzL
    · exact Or.inl (mem_iInter.mpr fun n => ((h1 n) hz).resolve_right hzL)
  · push_neg at h1
    obtain ⟨n₀, hn₀⟩ := h1
    right
    intro z hz
    by_cases hzK : z ∈ K
    · exact Or.inl hzK
    · refine Or.inr (mem_iInter.mpr fun n => ?_)
      have hm : L ⊆ K ∪ N (max n n₀) := (hor _).resolve_left fun h =>
        hn₀ (h.trans (union_subset_union_left _ (hanti (le_max_right _ _))))
      exact hanti (le_max_left n n₀) ((hm hz).resolve_left hzK)

/-- **Lemma 4, hereditarily decomposable case.** A terminal subcontinuum `K` of an atriodic,
hereditarily unicoherent, hereditarily decomposable `M` contains a terminal point of `M`
(condition B). Brouwer reduction (`exists_minimal_of_seq`) on "terminal in `M`, inside `K`"; a
minimal such continuum is a point by Lemma 3. Shape change: the skeleton's hypothesis that `M` is a
continuum is not used and has been removed. -/
theorem exists_terminal_point_of_isTerminalSub {M K : Set S}
    (hat : IsAtriodic M) (hhu : IsHereditarilyUnicoherent M) (hhd : IsHereditarilyDecomposable M)
    (hK : IsTerminalSub M K) : ∃ μ ∈ K, CondB M μ := by
  obtain ⟨L, hLK, hL, hmin⟩ := exists_minimal_of_seq (fun L => IsTerminalSub M L)
    (fun s hs => hs.1.1.isClosed) (fun h hh ha => isTerminalSub_iInter hh ha) hK
  by_cases hnt : L.Nontrivial
  · exfalso
    obtain ⟨A, B, hA, hB, hAL, hBL, hAB⟩ := hhd L hL.2.1 hL.1 hnt
    rcases isTerminalSub_of_union_terminal hat hhu hL hA hB hAL hBL hAB with h | h
    · exact hAL (hmin A h (hAB ▸ subset_union_left))
    · exact hBL (hmin B h (hAB ▸ subset_union_right))
  · obtain ⟨μ, hμ⟩ := hL.1.2.nonempty
    have hLμ : L = {μ} := (Set.not_nontrivial_iff.mp hnt).eq_singleton_of_mem hμ
    exact ⟨μ, hLK hμ, (isTerminalSub_singleton_iff M μ).mp (hLμ ▸ hL)⟩

/-! ## The two halves of a `BingS` space at an interior element -/

/-- With `g' = bingElt r` interior and sides `U`, `V` (batch 96): `A = U ∪ g'`, `B = V ∪ g'`,
and `C = closure V` (Fugate's `Cl(B − A)`); `A ∪ C = univ`, `A ∩ C ⊆ g'`, and `A ∩ C` is
terminal in `A` and in `C` (Remark 1 for `M = A ∪ C`). -/
theorem halves_terminal (hS : BingS S) {r : S} (hr : ¬ IsEndElt r) {U V : Set S}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hcov : U ∪ V = (bingElt r)ᶜ)
    (hUc : IsConnected U) (hVc : IsConnected V) :
    Fold.Q78.IsContinuum (closure V) ∧ (U ∪ bingElt r) ∪ closure V = univ ∧
      (U ∪ bingElt r) ∩ closure V ⊆ bingElt r ∧
      IsTerminalSub (U ∪ bingElt r) ((U ∪ bingElt r) ∩ closure V) ∧
      IsTerminalSub (closure V) ((U ∪ bingElt r) ∩ closure V) := by
  haveI := hS.connected
  haveI := hS.nontrivial
  obtain ⟨hA, -, -, -⟩ := sides_continua hS hr hU hV hUV hcov hUc hVc
  have hC : Fold.Q78.IsContinuum (closure V) := ⟨isClosed_closure.isCompact, hVc.closure⟩
  have hunion : (U ∪ bingElt r) ∪ closure V = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ bingElt r
    · exact Or.inl (Or.inr hx)
    · rcases (hcov.symm ▸ hx : x ∈ U ∪ V) with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (subset_closure h)
  have hUcl : Disjoint U (closure V) := hUV.closure_right hU
  have hinter : (U ∪ bingElt r) ∩ closure V ⊆ bingElt r := by
    rintro x ⟨hx | hx, hxc⟩
    · exact absurd hxc (Set.disjoint_left.mp hUcl hx)
    · exact hx
  have huni : IsUnicoherent (univ : Set S) :=
    hS.hu univ Subset.rfl ⟨isCompact_univ, isConnected_univ⟩ nontrivial_univ
  have hne : ((U ∪ bingElt r) ∩ closure V).Nonempty := (huni _ _ hA hC hunion).nonempty
  have hat : IsAtriodic ((U ∪ bingElt r) ∪ closure V) := hunion ▸ hS.atriodic
  have hu : IsUnicoherent ((U ∪ bingElt r) ∪ closure V) := hunion ▸ huni
  obtain ⟨v, hv⟩ := hVc.nonempty
  obtain ⟨u, hu'⟩ := hUc.nonempty
  have hvr : v ∉ bingElt r := fun h => (hcov.symm ▸ (Or.inr hv : v ∈ U ∪ V) : v ∈ (bingElt r)ᶜ) h
  have hCA : ¬ closure V ⊆ U ∪ bingElt r := fun h =>
    (h (subset_closure hv)).elim (fun h' => Set.disjoint_left.mp hUV h' hv) hvr
  have hAC : ¬ U ∪ bingElt r ⊆ closure V := fun h =>
    Set.disjoint_left.mp hUcl hu' (h (Or.inl hu'))
  refine ⟨hC, hunion, hinter,
    inter_isTerminalSub_of_union hA (hS.hu.mono (subset_univ _)) hC hne hat hu hCA, ?_⟩
  have := inter_isTerminalSub_of_union hC (hS.hu.mono (subset_univ _)) hA
    (by rw [inter_comm]; exact hne) (by rw [union_comm]; exact hat)
    (by rw [union_comm]; exact hu) hAC
  rwa [inter_comm] at this

omit [CompactSpace S] in
/-- A separation `P`, `R` of `gᶜ` against a pair of sides `Us`, `Vs` of `g`: a nonempty
preconnected `X ⊆ P` and a nonempty `Y ⊆ R` (both off `g`) lie on opposite sides of `g`. -/
theorem sides_of_separation {g Us Vs P R X Y : Set S} (hUs : IsOpen Us) (hVs : IsOpen Vs)
    (hUV : Disjoint Us Vs) (hcov : Us ∪ Vs = gᶜ) (hUc : IsPreconnected Us)
    (hVc : IsPreconnected Vs) (hP : IsOpen P) (hR : IsOpen R) (hPR : Disjoint P R)
    (hgPR : gᶜ ⊆ P ∪ R) (hX : IsPreconnected X) (hXne : X.Nonempty) (hXg : X ⊆ gᶜ)
    (hXP : X ⊆ P) (hYg : Y ⊆ gᶜ) (hYR : Y ⊆ R) :
    (X ⊆ Us ∧ Y ⊆ Vs) ∨ (X ⊆ Vs ∧ Y ⊆ Us) := by
  have key : ∀ {Us Vs : Set S}, Us ∪ Vs = gᶜ → IsPreconnected Us → X ⊆ Us → Y ⊆ Vs := by
    intro Us Vs hcov hUc hXU y hy
    rcases (hcov.ge (hYg hy) : y ∈ Us ∪ Vs) with h | h
    · exfalso
      obtain ⟨x, hx⟩ := hXne
      rcases hUc.subset_or_subset hP hR hPR ((subset_union_left.trans hcov.subset).trans hgPR)
        with h' | h'
      · exact Set.disjoint_left.mp hPR (h' h) (hYR hy)
      · exact Set.disjoint_left.mp hPR (hXP hx) (h' (hXU hx))
    · exact h
  rcases hX.subset_or_subset hUs hVs hUV (hXg.trans hcov.ge) with h | h
  · exact Or.inl ⟨h, key hcov hUc h⟩
  · exact Or.inr ⟨h, key (by rw [union_comm]; exact hcov) hVc h⟩

/-- For `t ∉ g' = bingElt r` and `p ∈ g'`: a neighbourhood `O` of `p` such that `bingElt t`
separates `g'` from the element of no point of `O`. (If `bingElt t` is an end element it
separates nothing; otherwise `O` is the complement of the closed side of `bingElt t` away from
`g'`.) -/
theorem exists_nbhd_not_separated (hS : BingS S) {r t p : S} (ht : t ∉ bingElt r)
    (hp : p ∈ bingElt r) : ∃ O : Set S, IsOpen O ∧ p ∈ O ∧ ∀ s ∈ O,
      ¬ Separates (bingElt t) (bingElt r) (bingElt s) := by
  have hne : ∀ {s : S}, Separates (bingElt t) (bingElt r) (bingElt s) →
      bingElt r ≠ bingElt t ∧ bingElt s ≠ bingElt t ∧ bingElt r ≠ bingElt s := by
    rintro s ⟨d1, d2, P, R, -, -, hPR, -, hrP, hsR⟩
    refine ⟨fun e => Set.disjoint_left.mp d1 (e ▸ mem_bingElt r) (mem_bingElt r),
      fun e => Set.disjoint_left.mp d2 (e ▸ mem_bingElt s) (mem_bingElt s),
      fun e => Set.disjoint_left.mp hPR (hrP (mem_bingElt r)) (hsR (e ▸ mem_bingElt r))⟩
  by_cases hte : IsEndElt t
  · refine ⟨univ, isOpen_univ, mem_univ _, fun s _ hsep => ?_⟩
    obtain ⟨n1, n2, n3⟩ := hne hsep
    exact hte r s n1 n2 n3 hsep
  · obtain ⟨Ut, Vt, hUt, hVt, hUVt, hcovt, hUtc, hVtc⟩ := exists_two_sides hS hte
    obtain ⟨hUtc', hVtc', -, -⟩ := sides_continua hS hte hUt hVt hUVt hcovt hUtc hVtc
    have hrt : bingElt r ⊆ (bingElt t)ᶜ := fun x hx hx' =>
      Set.disjoint_left.mp (disjoint_bingElt_of_notMem hS ht) hx' hx
    have key : ∀ {Ut Vt : Set S}, IsOpen Ut → IsOpen Vt → Disjoint Ut Vt →
        Ut ∪ Vt = (bingElt t)ᶜ → IsConnected Ut → IsConnected Vt →
        Fold.Q78.IsContinuum (Vt ∪ bingElt t) → bingElt r ⊆ Ut →
        ∃ O : Set S, IsOpen O ∧ p ∈ O ∧ ∀ s ∈ O,
          ¬ Separates (bingElt t) (bingElt r) (bingElt s) := by
      intro Ut Vt hUt hVt hUVt hcovt hUtc hVtc hVtc' hrU
      refine ⟨(Vt ∪ bingElt t)ᶜ, hVtc'.1.isClosed.isOpen_compl, ?_, fun s hs hsep => ?_⟩
      · rintro (h | h)
        · exact Set.disjoint_left.mp hUVt (hrU hp) h
        · exact hrt hp h
      · have hsep' := hsep
        obtain ⟨-, d2, P, R, hP, hR, hPR, hcovPR, hrP, hsR⟩ := hsep
        rcases sides_of_separation hUt hVt hUVt hcovt hUtc.isPreconnected hVtc.isPreconnected
          hP hR hPR (fun x hx => hcovPR ⟨mem_univ x, hx⟩)
          (bingElt_isContinuum hS r).2.isPreconnected ⟨r, mem_bingElt r⟩ hrt hrP
          (fun x hx hx' => Set.disjoint_left.mp d2 hx' hx) hsR with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact hs (Or.inl (h2 (mem_bingElt s)))
        · exact Set.disjoint_left.mp hUVt (hrU hp) (h1 hp)
    rcases (bingElt_isContinuum hS r).2.isPreconnected.subset_or_subset hUt hVt hUVt
      (hrt.trans hcovt.ge) with h | h
    · exact key hUt hVt hUVt hcovt hUtc hVtc hVtc' h
    · exact key hVt hUt hUVt.symm (by rw [union_comm]; exact hcovt) hVtc hUtc hUtc' h

/-- The last step of Claim 1: with `bingElt s` separating `g'` (in its side `Us`) from a point
`t ∈ Q ∩ V` (in its side `Vs`), the continuum `W = (Us ∪ bingElt s) ∩ closure V` ("the elements
between `g'` and `bingElt s`") meets `A ∩ C` at `p`, contains `s ∉ Q` and misses `t ∈ Q`, so `A ∩ C`
is not terminal in `C`. -/
theorem claim1_core (hS : BingS S) {r : S} (hr : ¬ IsEndElt r) {U V : Set S}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hcov : U ∪ V = (bingElt r)ᶜ)
    (hUc : IsConnected U) (hVc : IsConnected V) {Q : Set S} (hQ : Fold.Q78.IsContinuum Q)
    (hQC : Q ⊆ closure V) (hmeet : (Q ∩ ((U ∪ bingElt r) ∩ closure V)).Nonempty)
    {s t p : S} (hse : ¬ IsEndElt s) {Us Vs : Set S} (hUs : IsOpen Us) (hVs : IsOpen Vs)
    (hUVs : Disjoint Us Vs) (hcovs : Us ∪ Vs = (bingElt s)ᶜ) (hUsc : IsConnected Us)
    (hVsc : IsConnected Vs) (hgU : bingElt r ⊆ Us) (htVs : t ∈ Vs) (htQ : t ∈ Q) (htV : t ∈ V)
    (hsV : s ∈ V) (hsQ : s ∉ Q) (hp : p ∈ (U ∪ bingElt r) ∩ closure V) : False := by
  obtain ⟨hC, -, hinter, -, hterm⟩ := halves_terminal hS hr hU hV hUV hcov hUc hVc
  obtain ⟨hWs, -, -, -⟩ := sides_continua hS hse hUs hVs hUVs hcovs hUsc hVsc
  haveI := hS.connected
  haveI := hS.nontrivial
  have huni : IsUnicoherent (univ : Set S) :=
    hS.hu univ Subset.rfl ⟨isCompact_univ, isConnected_univ⟩ nontrivial_univ
  have hVr : V ⊆ (bingElt r)ᶜ := subset_union_right.trans hcov.subset
  have hVsg : Vs ⊆ (bingElt r)ᶜ := fun x hx hxr => Set.disjoint_left.mp hUVs (hgU hxr) hx
  have hVsV : Vs ⊆ V := hVsc.isPreconnected.subset_left_of_subset_union hV hU hUV.symm
    ((hVsg.trans hcov.ge).trans (union_comm U V).le) ⟨t, htVs, htV⟩
  have hunion : (Us ∪ bingElt s) ∪ closure V = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ Us ∪ bingElt s
    · exact Or.inl hx
    · rcases (hcovs.ge (fun h => hx (Or.inr h)) : x ∈ Us ∪ Vs) with h | h
      · exact absurd (Or.inl h) hx
      · exact Or.inr (subset_closure (hVsV h))
  have hW : Fold.Q78.IsContinuum ((Us ∪ bingElt s) ∩ closure V) :=
    ⟨hWs.1.inter_right isClosed_closure, huni _ _ hWs hC hunion⟩
  rcases hterm.2.2 _ Q hW hQ inter_subset_right hQC
    ⟨p, ⟨Or.inl (hgU (hinter hp)), hp.2⟩, hp⟩ hmeet with h | h
  · rcases h ⟨Or.inr (mem_bingElt s), subset_closure hsV⟩ with h' | h'
    · exact hVr hsV (hinter h')
    · exact hsQ h'
  · rcases h htQ with ⟨h' | h', -⟩ | h'
    · exact Set.disjoint_left.mp hUVs h' htVs
    · exact (hcovs.subset (Or.inr htVs) : t ∈ (bingElt s)ᶜ) h'
    · exact hVr htV (hinter h')

/-- **Claim 1 (Fugate, p. 391).** A subcontinuum `Q` of `C = closure V` meeting `A ∩ C` and not
contained in it contains `A ∩ C`. (Fugate: via `f⁻¹[½, f(s)]`; here via the elements between `g'`
and the element of a point of `Q` in `V`, Theorem 8 (a) and the sides.) -/
theorem claim1_contains_inter (hS : BingS S) {r : S} (hr : ¬ IsEndElt r) {U V : Set S}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hcov : U ∪ V = (bingElt r)ᶜ)
    (hUc : IsConnected U) (hVc : IsConnected V) {Q : Set S} (hQ : Fold.Q78.IsContinuum Q)
    (hQC : Q ⊆ closure V) (hmeet : (Q ∩ (U ∪ bingElt r) ∩ closure V).Nonempty)
    (hnot : ¬ Q ⊆ (U ∪ bingElt r) ∩ closure V) :
    (U ∪ bingElt r) ∩ closure V ⊆ Q := by
  obtain ⟨hC, -, hinter, -, -⟩ := halves_terminal hS hr hU hV hUV hcov hUc hVc
  obtain ⟨-, hBc, -, -⟩ := sides_continua hS hr hU hV hUV hcov hUc hVc
  have hmeet' : (Q ∩ ((U ∪ bingElt r) ∩ closure V)).Nonempty := by rwa [← inter_assoc]
  have hVr : V ⊆ (bingElt r)ᶜ := subset_union_right.trans hcov.subset
  have hclV : closure V ⊆ V ∪ bingElt r := closure_minimal subset_union_left hBc.1.isClosed
  intro p hp
  by_contra hpQ
  obtain ⟨t, htQ, htA⟩ := not_subset.mp hnot
  have htV : t ∈ V := by
    rcases hclV (hQC htQ) with h | h
    · exact h
    · exact absurd ⟨Or.inr h, hQC htQ⟩ htA
  have htr : t ∉ bingElt r := hVr htV
  obtain ⟨O, hO, hpO, hOsep⟩ := exists_nbhd_not_separated hS htr (hinter hp)
  have hO' : IsOpen (O ∩ Qᶜ ∩ (bingElt t)ᶜ) := (hO.inter hQ.1.isClosed.isOpen_compl).inter
    (bingElt_isContinuum hS t).1.isClosed.isOpen_compl
  have hpt : p ∉ bingElt t := fun h =>
    Set.disjoint_left.mp (disjoint_bingElt_of_notMem hS htr) h (hinter hp)
  obtain ⟨s, ⟨⟨hsO, hsQ⟩, hst⟩, hsV⟩ := mem_closure_iff.mp hp.2 _ hO' ⟨⟨hpO, hpQ⟩, hpt⟩
  have hsr : s ∉ bingElt r := hVr hsV
  have ne_rt : bingElt r ≠ bingElt t := fun e => htr (e ▸ mem_bingElt t)
  have ne_ts : bingElt t ≠ bingElt s := fun e => hst (e ▸ mem_bingElt s)
  have ne_rs : bingElt r ≠ bingElt s := fun e => hsr (e ▸ mem_bingElt s)
  rcases bingElt_separates_triple hS r t s ne_rt ne_ts ne_rs with h | h | h
  · obtain ⟨-, -, P, R, hP, hR, hPR, hcovPR, htP, hsR⟩ := h
    have hVPR : V ⊆ P ∪ R := fun x hx => hcovPR ⟨mem_univ x, hVr hx⟩
    rcases hVc.isPreconnected.subset_or_subset hP hR hPR hVPR with h' | h'
    · exact Set.disjoint_left.mp hPR (h' hsV) (hsR (mem_bingElt s))
    · exact Set.disjoint_left.mp hPR (htP (mem_bingElt t)) (h' htV)
  · exact hOsep s hsO h
  · have hse : ¬ IsEndElt s := fun hse => hse r t ne_rs ne_ts ne_rt h
    obtain ⟨Us, Vs, hUs, hVs, hUVs, hcovs, hUsc, hVsc⟩ := exists_two_sides hS hse
    obtain ⟨d1, d2, P, R, hP, hR, hPR, hcovPR, hrP, htR⟩ := h
    rcases sides_of_separation hUs hVs hUVs hcovs hUsc.isPreconnected hVsc.isPreconnected hP hR
      hPR (fun x hx => hcovPR ⟨mem_univ x, hx⟩) (bingElt_isContinuum hS r).2.isPreconnected
      ⟨r, mem_bingElt r⟩ (fun x hx hx' => Set.disjoint_left.mp d1 hx' hx) hrP
      (fun x hx hx' => Set.disjoint_left.mp d2 hx' hx) htR with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact claim1_core hS hr hU hV hUV hcov hUc hVc hQ hQC hmeet' hse hUs hVs hUVs hcovs hUsc
        hVsc h1 (h2 (mem_bingElt t)) htQ htV hsV hsQ hp
    · exact claim1_core hS hr hU hV hUV hcov hUc hVc hQ hQC hmeet' hse hVs hUs hUVs.symm
        (by rw [union_comm]; exact hcovs) hVsc hUsc h1 (h2 (mem_bingElt t)) htQ htV hsV hsQ hp

/-- **The terminal point of both halves** (Fugate: Lemma 4 applied to `A ∩ C` in `A`, then "`K` is
a terminal subcontinuum of `Cl(B − A)`" via Claim 1 and a triod): there is `μ ∈ A ∩ C` with
`CondB A μ` and `CondB C μ`. -/
theorem exists_mu (hS : BingS S) {r : S} (hr : ¬ IsEndElt r) {U V : Set S}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hcov : U ∪ V = (bingElt r)ᶜ)
    (hUc : IsConnected U) (hVc : IsConnected V) :
    ∃ μ ∈ (U ∪ bingElt r) ∩ closure V, CondB (U ∪ bingElt r) μ ∧ CondB (closure V) μ := by
  obtain ⟨hC, -, -, hAterm, -⟩ := halves_terminal hS hr hU hV hUV hcov hUc hVc
  obtain ⟨hA, -, -, -⟩ := sides_continua hS hr hU hV hUV hcov hUc hVc
  obtain ⟨μ, hμ, hBA⟩ := exists_terminal_point_of_isTerminalSub (M := U ∪ bingElt r)
    (fun T _ => hS.atriodic T (subset_univ T)) (hS.hu.mono (subset_univ _))
    (fun K _ => hS.hd K (subset_univ K)) hAterm
  refine ⟨μ, hμ, hBA, hμ.2, fun H K hHC hKC hH hK hμH hμK => ?_⟩
  have hUcl : Disjoint U (closure V) := hUV.closure_right hU
  have key : ∀ {H K : Set S}, H ⊆ closure V → K ⊆ closure V → Fold.Q78.IsContinuum H →
      Fold.Q78.IsContinuum K → μ ∈ H → μ ∈ K → ¬ H ⊆ U ∪ bingElt r → ¬ H ⊆ K → ¬ K ⊆ H →
      False := by
    intro H K hHC hKC hH hK hμH hμK hHA hHK hKH
    have h1 : (U ∪ bingElt r) ∩ closure V ⊆ H := claim1_contains_inter hS hr hU hV hUV hcov hUc
      hVc hH hHC ⟨μ, ⟨hμH, hμ.1⟩, hμ.2⟩ fun h => hHA (h.trans inter_subset_left)
    have h2 : (U ∪ bingElt r) ∩ closure V ⊆ K := claim1_contains_inter hS hr hU hV hUV hcov hUc
      hVc hK hKC ⟨μ, ⟨hμK, hμ.1⟩, hμ.2⟩ fun h => hKH (h.trans h1)
    obtain ⟨x, hxH, hxK⟩ := not_subset.mp hHK
    obtain ⟨y, hyK, hyH⟩ := not_subset.mp hKH
    obtain ⟨u, hu⟩ := hUc.nonempty
    refine hS.atriodic _ (subset_univ _) (isTriod_union_of_three hH hK hA ⟨μ, hμH, hμK⟩
      ⟨μ, hμK, hμ.1⟩ ⟨μ, hμH, hμ.1⟩ ?_ ?_ ?_ (hS.hu.mono (subset_univ _)))
    · intro h
      rcases h hxH with h' | h'
      · exact hxK h'
      · exact hxK (h2 ⟨h', hHC hxH⟩)
    · intro h
      rcases h hyK with h' | h'
      · exact hyH h'
      · exact hyH (h1 ⟨h', hKC hyK⟩)
    · intro h
      rcases h (Or.inl hu) with h' | h'
      · exact Set.disjoint_left.mp hUcl hu (hHC h')
      · exact Set.disjoint_left.mp hUcl hu (hKC h')
  by_contra hno
  rw [not_or] at hno
  by_cases hHA : H ⊆ U ∪ bingElt r
  · by_cases hKA : K ⊆ U ∪ bingElt r
    · exact (not_or.mpr hno) (hBA.2 H K hHA hKA hH hK hμH hμK)
    · exact key hKC hHC hK hH hμK hμH hKA hno.2 hno.1
  · exact key hHC hKC hH hK hμH hμK hHA hno.1 hno.2

/-! ## Claim 2 and the amalgamation -/

/-- The links of a chain, extended by `∅` to a sequence (for weak chains). -/
def chainSeq {X : Type*} [MetricSpace X] {n : ℕ} (E : Chain X n) (i : ℕ) : Set X :=
  if h : i < n then E.link ⟨i, h⟩ else ∅

section ChainSeq

variable {X : Type*} [MetricSpace X] {n : ℕ}

theorem chainSeq_isOpen (E : Chain X n) (i : ℕ) : IsOpen (chainSeq E i) := by
  unfold chainSeq
  split_ifs
  exacts [E.isOpen _, isOpen_empty]

theorem chainSeq_disjoint (E : Chain X n) {i l : ℕ} (h : i + 2 ≤ l) :
    Disjoint (chainSeq E i) (chainSeq E l) := by
  unfold chainSeq
  split_ifs with hi hl
  · rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty, E.adjacent_iff]
    simp only
    omega
  all_goals simp

theorem chainSeq_small {E : Chain X n} {ε : ℝ} (hE : IsEpsChain E ε) (hε : 0 < ε) (i : ℕ) :
    Bornology.IsBounded (chainSeq E i) ∧ diam (chainSeq E i) < ε := by
  unfold chainSeq
  split_ifs
  exacts [hE _, ⟨Bornology.isBounded_empty, by simpa using hε⟩]

theorem mem_chainSeq {E : Chain X n} {z : X} (hz : z ∈ E.union) : ∃ i < n, z ∈ chainSeq E i := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  exact ⟨i, i.2, by simp [chainSeq, i.2, hi]⟩

theorem chainSeq_last {E : Chain X n} (hn : 0 < n) :
    chainSeq E (n - 1) = E.link ⟨n - 1, by omega⟩ := by
  simp [chainSeq, show n - 1 < n by omega]

theorem small_of_subset {A B : Set X} {ε : ℝ} (h : A ⊆ B)
    (hB : Bornology.IsBounded B ∧ diam B < ε) : Bornology.IsBounded A ∧ diam A < ε :=
  ⟨hB.1.subset h, (diam_mono h hB.1).trans_lt hB.2⟩

end ChainSeq

/-- **Claim 2 (Fugate, p. 392).** No continuum in `M ∖ O` meets both `A ∖ O` and `M ∖ E*`, when
`μ ∈ O`, `A ⊆ E*`, `A ∪ C = M` and Claim 1 holds (stated for preconnected sets, via closures). -/
theorem claim2 {M A C O Estar : Set S} (hhu : IsHereditarilyUnicoherent M)
    (hA : Fold.Q78.IsContinuum A) (hC : Fold.Q78.IsContinuum C) (hAC : A ∪ C = M) {μ : S}
    (hμO : μ ∈ O) (hO : IsOpen O) (hAE : A ⊆ Estar)
    (hclaim1 : ∀ Q : Set S, Fold.Q78.IsContinuum Q → Q ⊆ C → (Q ∩ (A ∩ C)).Nonempty →
      ¬ Q ⊆ A ∩ C → A ∩ C ⊆ Q) (hμ : μ ∈ A ∩ C) :
    ∀ Z ⊆ M \ O, IsPreconnected Z → (Z ∩ (A \ O)).Nonempty → (Z ∩ (M \ Estar)).Nonempty →
      False := by
  intro Z hZ hZc ⟨a, haZ, haA⟩ ⟨z, hzZ, hzM, hzE⟩
  have hMO : IsClosed (M \ O) := (hAC ▸ (hA.1.union hC.1)).isClosed.sdiff hO
  set N := closure Z with hN
  have hNsub : N ⊆ M \ O := closure_minimal hZ hMO
  have hNc : Fold.Q78.IsContinuum N :=
    ⟨isClosed_closure.isCompact, ⟨⟨a, subset_closure haZ⟩, hZc.closure⟩⟩
  have hzA : z ∉ A := fun h => hzE (hAE h)
  have hzC : z ∈ C := ((hAC.symm ▸ hzM : z ∈ A ∪ C)).resolve_left hzA
  have hNM : N ⊆ M := hNsub.trans diff_subset
  have hmeet : (N ∩ (A ∩ C)).Nonempty :=
    isPreconnected_closed_iff.mp hNc.2.isPreconnected A C hA.1.isClosed hC.1.isClosed
      (hAC.symm ▸ hNM) ⟨a, subset_closure haZ, haA.1⟩ ⟨z, subset_closure hzZ, hzC⟩
  obtain ⟨w, hwN, hwA, hwC⟩ := hmeet
  have hQ := isContinuum_inter_of_hu hhu hNc hC hNM (hAC ▸ subset_union_right)
    ⟨z, subset_closure hzZ, hzC⟩
  have := hclaim1 _ hQ inter_subset_right ⟨w, ⟨hwN, hwC⟩, hwA, hwC⟩
    (fun h => hzA (h ⟨subset_closure hzZ, hzC⟩).1) hμ
  exact (hNsub this.1).2 hμO

/-- **Claim 2 + the chain (Fugate, p. 392), abstracted.** `A`, `C` continua with `A ∪ C = M`;
`μ ∈ A ∩ C`; Claim 1 holds for `C` relative to `A`; `E` an `ε`-chain covering `A` with `μ` in its last
link, `F` likewise for `C`; `M` hereditarily unicoherent. Then `M` is covered by an `ε`-chain.

Shape change: the skeleton's `ε/2`-chains are replaced by `ε`-chains (a stronger statement), and the
hypotheses "`μ` in the closure of no other link" are dropped (unused). No mesh is lost: Fugate's
link `(F_y ∩ T) ∪ U` lies in `F_y` because `cl U ⊆ E_x ∩ F_y`. The chain is
`(E_1 ∩ S) − cl U, …, (E_{x−1} ∩ S) − cl U, E_x ∩ S, (F_y ∩ T) ∪ U, F_{y−1} ∩ T, …, F_1 ∩ T`
(removing `cl U` from the first `x − 2` links changes nothing, as they miss `E_x ⊇ cl U`); it is a
weak chain (non-consecutive links disjoint), trimmed to a chain by `exists_chain_of_weak`. -/
theorem epsCoverable_of_halves {M A C : Set S} (hM : Fold.Q78.IsContinuum M)
    (hhu : IsHereditarilyUnicoherent M) (hA : Fold.Q78.IsContinuum A)
    (hC : Fold.Q78.IsContinuum C) (hAC : A ∪ C = M) {μ : S} (hμ : μ ∈ A ∩ C)
    (hclaim1 : ∀ Q : Set S, Fold.Q78.IsContinuum Q → Q ⊆ C → (Q ∩ (A ∩ C)).Nonempty →
      ¬ Q ⊆ A ∩ C → A ∩ C ⊆ Q)
    {ε : ℝ} (hε : 0 < ε)
    (hE : ∃ (x : ℕ) (E : Chain S x) (hx : 0 < x), IsEpsChain E ε ∧ A ⊆ E.union ∧
      μ ∈ E.link ⟨x - 1, by omega⟩)
    (hF : ∃ (y : ℕ) (F : Chain S y) (hy : 0 < y), IsEpsChain F ε ∧ C ⊆ F.union ∧
      μ ∈ F.link ⟨y - 1, by omega⟩) :
    EpsCoverable M ε := by
  obtain ⟨x, E, hx, hEε, hAE, hμE⟩ := hE
  obtain ⟨y, F, hy, hFε, hCF, hμF⟩ := hF
  rw [← chainSeq_last hx] at hμE
  rw [← chainSeq_last hy] at hμF
  -- the small open set `O` about `μ`, with closure inside both last links
  obtain ⟨O, hO, hμO, hclO⟩ : ∃ O : Set S, IsOpen O ∧ μ ∈ O ∧
      closure O ⊆ chainSeq E (x - 1) ∩ chainSeq F (y - 1) := by
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp
      ((chainSeq_isOpen E _).inter (chainSeq_isOpen F _)) μ ⟨hμE, hμF⟩
    exact ⟨ball μ (δ / 2), isOpen_ball, mem_ball_self (by linarith),
      (closure_ball_subset_closedBall).trans ((closedBall_subset_ball (by linarith)).trans hsub)⟩
  have hOE : O ⊆ chainSeq E (x - 1) := subset_closure.trans (hclO.trans inter_subset_left)
  have hOF : O ⊆ chainSeq F (y - 1) := subset_closure.trans (hclO.trans inter_subset_right)
  set Estar := ⋃ i, ⋃ (_ : i < x), chainSeq E i with hEstar
  have hAEs : A ⊆ Estar := fun a ha => by
    obtain ⟨i, hi, hai⟩ := mem_chainSeq (hAE ha)
    exact mem_iUnion₂.mpr ⟨i, hi, hai⟩
  have hEso : IsOpen Estar := isOpen_iUnion fun i => isOpen_iUnion fun _ => chainSeq_isOpen E i
  have hOEs : O ⊆ Estar := fun z hz => mem_iUnion₂.mpr ⟨x - 1, by omega, hOE hz⟩
  have hMcl : IsClosed M := hM.1.isClosed
  have hAM : A ⊆ M := hAC ▸ subset_union_left
  obtain ⟨H, L, hH, hL, hHL, hdisj, hPH, hQL⟩ := exists_closed_split_of_no_connected
    (hM.1.diff hO) (hA.1.isClosed.sdiff hO) (hMcl.sdiff hEso) (diff_subset_diff_left hAM)
    (diff_subset_diff_right hOEs)
    (claim2 hhu hA hC hAC hμO hO hAEs hclaim1 hμ)
  obtain ⟨S₀, T₀, hS₀, hT₀, hHS₀, hLT₀, hST⟩ := normal_separation hH hL hdisj
  -- the weak chain
  let Lk : ℕ → Set S := fun i =>
    if i < x - 1 then (chainSeq E i ∩ S₀) \ closure O
    else if i = x - 1 then chainSeq E i ∩ S₀
    else if i = x then (chainSeq F (y - 1) ∩ T₀) ∪ O
    else chainSeq F (x + y - 1 - i) ∩ T₀
  have hLe : ∀ i, i < x → Lk i ⊆ chainSeq E i ∩ S₀ := by
    intro i hi z hz
    simp only [Lk] at hz
    split_ifs at hz with h1 h2
    · exact hz.1
    · exact hz
    all_goals omega
  have hLf : ∀ i, x ≤ i → Lk i ⊆ chainSeq F (x + y - 1 - i) := by
    intro i hi z hz
    simp only [Lk] at hz
    split_ifs at hz with h1 h2 h3
    · omega
    · omega
    · subst h3
      rw [show i + y - 1 - i = y - 1 by omega]
      exact hz.elim (fun h => h.1) (fun h => hOF h)
    · exact hz.1
  have hLT : ∀ i, x < i → Lk i ⊆ T₀ := by
    intro i hi z hz
    simp only [Lk] at hz
    split_ifs at hz with h1 h2 h3
    · omega
    · omega
    · omega
    · exact hz.2
  have hLO : ∀ i, i < x - 1 → Disjoint (Lk i) (closure O) := by
    intro i hi
    simp only [Lk, if_pos hi]
    exact disjoint_sdiff_left
  have hLx : Lk x = (chainSeq F (y - 1) ∩ T₀) ∪ O := by
    simp only [Lk, show ¬ x < x - 1 by omega, show x ≠ x - 1 by omega, if_false, if_true]
  have hLo : ∀ i, IsOpen (Lk i) := by
    intro i
    simp only [Lk]
    split_ifs
    · exact ((chainSeq_isOpen E i).inter hS₀).sdiff isClosed_closure
    · exact (chainSeq_isOpen E i).inter hS₀
    · exact ((chainSeq_isOpen F _).inter hT₀).union hO
    · exact (chainSeq_isOpen F _).inter hT₀
  have hLs : ∀ i, Bornology.IsBounded (Lk i) ∧ diam (Lk i) < ε := by
    intro i
    rcases lt_or_ge i x with h | h
    · exact small_of_subset ((hLe i h).trans inter_subset_left) (chainSeq_small hEε hε i)
    · exact small_of_subset (hLf i h) (chainSeq_small hFε hε _)
  have hLw : ∀ i l, i + 2 ≤ l → l < x + y → Disjoint (Lk i) (Lk l) := by
    intro i l hil hl
    rcases lt_or_ge l x with h | h
    · exact ((chainSeq_disjoint E hil).mono ((hLe i (by omega)).trans inter_subset_left)
        ((hLe l h).trans inter_subset_left))
    rcases le_or_gt x i with h' | h'
    · exact ((chainSeq_disjoint F (i := x + y - 1 - l) (l := x + y - 1 - i) (by omega)).symm.mono
        (hLf i h') (hLf l h))
    rcases eq_or_lt_of_le h with h'' | h''
    · subst h''
      rw [hLx]
      refine Disjoint.union_right ?_ ?_
      · exact (hST.mono ((hLe i h').trans inter_subset_right) inter_subset_right)
      · exact (hLO i (by omega)).mono_right subset_closure
    · exact hST.mono ((hLe i h').trans inter_subset_right) (hLT l h'')
  have hcov : M ⊆ ⋃ i, ⋃ (_ : i < x + y), Lk i := by
    intro z hzM
    by_cases hzO : z ∈ O
    · exact mem_iUnion₂.mpr ⟨x, by omega, by rw [hLx]; exact Or.inr hzO⟩
    have hz : z ∈ H ∪ L := hHL ▸ ⟨hzM, hzO⟩
    rcases hz with hzH | hzL
    · have hzS : z ∈ S₀ := hHS₀ hzH
      have hzE : z ∈ Estar := by
        by_contra h
        exact Set.disjoint_left.mp hdisj hzH (hQL ⟨hzM, h⟩)
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzE
      by_cases hix : i < x - 1
      · by_cases hzc : z ∈ closure O
        · refine mem_iUnion₂.mpr ⟨x - 1, by omega, ?_⟩
          simp only [Lk, show ¬ x - 1 < x - 1 by omega, if_false, if_true]
          exact ⟨(hclO hzc).1, hzS⟩
        · refine mem_iUnion₂.mpr ⟨i, by omega, ?_⟩
          simp only [Lk, if_pos hix]
          exact ⟨⟨hzi, hzS⟩, hzc⟩
      · have hi' : i = x - 1 := by omega
        subst hi'
        refine mem_iUnion₂.mpr ⟨x - 1, by omega, ?_⟩
        simp only [Lk, show ¬ x - 1 < x - 1 by omega, if_false, if_true]
        exact ⟨hzi, hzS⟩
    · have hzT : z ∈ T₀ := hLT₀ hzL
      have hzA : z ∉ A := fun h => Set.disjoint_left.mp hdisj (hPH ⟨h, hzO⟩) hzL
      have hzC : z ∈ C := ((hAC.symm ▸ hzM : z ∈ A ∪ C)).resolve_left hzA
      obtain ⟨k, hk, hzk⟩ := mem_chainSeq (hCF hzC)
      by_cases hky : k = y - 1
      · subst hky
        exact mem_iUnion₂.mpr ⟨x, by omega, by rw [hLx]; exact Or.inl ⟨hzk, hzT⟩⟩
      · refine mem_iUnion₂.mpr ⟨x + y - 1 - k, by omega, ?_⟩
        simp only [Lk, show ¬ x + y - 1 - k < x - 1 by omega, show x + y - 1 - k ≠ x - 1 by omega,
          show x + y - 1 - k ≠ x by omega, if_false]
        rw [show x + y - 1 - (x + y - 1 - k) = k by omega]
        exact ⟨hzk, hzT⟩
  obtain ⟨a, k, D, -, -, -, hDL, hMD, -, -⟩ := exists_chain_of_weak Lk hLo hLw
    hM.2.isPreconnected hcov (i₀ := x) (by omega)
    ⟨μ, by rw [hLx]; exact Or.inr hμO, hAM hμ.1⟩
  exact ⟨k, D, fun t => by rw [hDL t]; exact hLs _, hMD⟩

/-! ## Theorem 11 -/

/-- **An interior element exists** (Theorem 11: "any third element is interior"): two distinct end
elements exist; their union is closed with empty interior, so a third element exists, and of three
distinct elements one separates the other two (Theorem 8 (a)), so it is not an end element. -/
theorem exists_not_endElt (hS : BingS S) : ∃ r : S, ¬ IsEndElt r := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_endElts hS
  have hint : interior (bingElt a ∪ bingElt b) = ∅ := by
    rw [interior_union_isClosed_of_interior_empty (bingElt_isContinuum hS a).1.isClosed
      (bingElt_interior_eq_empty hS b)]
    exact bingElt_interior_eq_empty hS a
  obtain ⟨c, hc⟩ : ∃ c, c ∉ bingElt a ∪ bingElt b := by
    by_contra h
    push_neg at h
    haveI := hS.nontrivial
    rw [eq_univ_of_forall h, interior_univ] at hint
    exact univ_nonempty.ne_empty hint
  have hca : bingElt a ≠ bingElt c := fun e => hc (Or.inl (e ▸ mem_bingElt c))
  have hcb : bingElt b ≠ bingElt c := fun e => hc (Or.inr (e ▸ mem_bingElt c))
  refine ⟨c, fun hce => ?_⟩
  rcases bingElt_separates_triple hS a b c hab hcb hca with h | h | h
  · exact ha b c hab.symm hca.symm hcb h
  · exact hb a c hab hcb.symm hca h
  · exact hce a b hca hcb hab h

section SubtypeTransfer

variable {S' : Set S}

omit [CompactSpace S] in
theorem isContinuum_preimage_val_of_subset {Q : Set S} (hQ : Fold.Q78.IsContinuum Q)
    (hQS : Q ⊆ S') : Fold.Q78.IsContinuum (((↑) : S' → S) ⁻¹' Q) :=
  isContinuum_preimage_val (by rwa [inter_eq_left.mpr hQS])

omit [MetricSpace S] [CompactSpace S] in
theorem subset_of_preimage_val_subset {Q L : Set S} (hQS : Q ⊆ S')
    (h : ((↑) : S' → S) ⁻¹' Q ⊆ ((↑) : S' → S) ⁻¹' L) : Q ⊆ L := fun q hq =>
  h (show (⟨q, hQS hq⟩ : S') ∈ ((↑) : S' → S) ⁻¹' Q from hq)

omit [MetricSpace S] [CompactSpace S] in
theorem preimage_val_subset_of_subset_image {Q : Set S} {K : Set S'}
    (h : Q ⊆ ((↑) : S' → S) '' K) : ((↑) : S' → S) ⁻¹' Q ⊆ K := fun x hx => by
  obtain ⟨y, hy, e⟩ := h hx
  rwa [← Subtype.ext e]

omit [CompactSpace S] in
/-- Condition B passes from a subcontinuum (as a subtype) to the ambient space. -/
theorem condB_image_val {K : Set S'} {μ : S'} (h : CondB K μ) :
    CondB (((↑) : S' → S) '' K) μ := by
  refine ⟨⟨μ, h.1, rfl⟩, fun H L hHK hLK hH hL hμH hμL => ?_⟩
  have hHS : H ⊆ S' := hHK.trans (Subtype.coe_image_subset _ _)
  have hLS : L ⊆ S' := hLK.trans (Subtype.coe_image_subset _ _)
  rcases h.2 _ _ (preimage_val_subset_of_subset_image hHK) (preimage_val_subset_of_subset_image hLK)
    (isContinuum_preimage_val_of_subset hH hHS) (isContinuum_preimage_val_of_subset hL hLS)
    hμH hμL with h' | h'
  · exact Or.inl (subset_of_preimage_val_subset hHS h')
  · exact Or.inr (subset_of_preimage_val_subset hLS h')

omit [CompactSpace S] in
/-- Claim 1's conclusion passes from a subcontinuum (as a subtype) to the ambient space. -/
theorem claim1_image_val {A C : Set S'}
    (h : ∀ Q : Set S', Fold.Q78.IsContinuum Q → Q ⊆ C → (Q ∩ (A ∩ C)).Nonempty →
      ¬ Q ⊆ A ∩ C → A ∩ C ⊆ Q) :
    ∀ Q : Set S, Fold.Q78.IsContinuum Q → Q ⊆ ((↑) : S' → S) '' C →
      (Q ∩ (((↑) : S' → S) '' A ∩ ((↑) : S' → S) '' C)).Nonempty →
      ¬ Q ⊆ ((↑) : S' → S) '' A ∩ ((↑) : S' → S) '' C →
      ((↑) : S' → S) '' A ∩ ((↑) : S' → S) '' C ⊆ Q := by
  intro Q hQ hQC hmeet hnot
  rw [← image_inter Subtype.val_injective] at hmeet hnot ⊢
  have hQS : Q ⊆ S' := hQC.trans (Subtype.coe_image_subset _ _)
  obtain ⟨w, hwQ, y, hy, rfl⟩ := hmeet
  have := h _ (isContinuum_preimage_val_of_subset hQ hQS) (preimage_val_subset_of_subset_image hQC)
    ⟨y, hwQ, hy⟩ (fun h' => hnot fun q hq => ⟨⟨q, hQS hq⟩, h' hq, rfl⟩)
  rintro _ ⟨z, hz, rfl⟩
  exact this hz

end SubtypeTransfer

/-- **Bing 1951, Theorem 11 (sufficiency), by Fugate 1969 Case II.** A compact, nondegenerate,
atriodic, hereditarily unicoherent, hereditarily decomposable metric continuum is snake-like.
Proof: a minimal non-`ε`-coverable subcontinuum `S'` (`exists_minimal_notCoverable`), a `BingS`
space (`bingS_subcontinuum`); an interior element `g'` of `S'` (`exists_not_endElt`) and its sides
`U`, `V`; the halves `A = U ∪ g'`, `C = closure V`; the common terminal point `μ` (`exists_mu`);
chains for the proper subcontinua `A`, `C` with `μ` in the last link (`fugate_lemma1`); Claim 2 and
the amalgamated chain (`epsCoverable_of_halves`) cover `S'`, a contradiction. -/
theorem theorem11_1951 (hS : BingS S) : IsSnakeLike (univ : Set S) := by
  haveI := hS.connected
  refine ⟨⟨isCompact_univ, isConnected_univ⟩, fun ε hε => ?_⟩
  by_contra hnot
  obtain ⟨S', -, hS', hnc, hmin⟩ :=
    exists_minimal_notCoverable ⟨isCompact_univ, isConnected_univ⟩ hε hnot
  have hnt : S'.Nontrivial := by
    by_contra h
    obtain ⟨x, hx⟩ := hS'.2.nonempty
    rw [(Set.not_nontrivial_iff.mp h).eq_singleton_of_mem hx] at hnc
    exact hnc (epsCoverable_singleton x hε)
  haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
  have hBS := bingS_subcontinuum hS hS' hnt
  obtain ⟨r, hr⟩ := exists_not_endElt hBS
  obtain ⟨U, V, hU, hV, hUV, hcov, hUc, hVc⟩ := exists_two_sides hBS hr
  obtain ⟨μ, hμ, hBA, hBC⟩ := exists_mu hBS hr hU hV hUV hcov hUc hVc
  obtain ⟨hC, hunion, -, -, -⟩ := halves_terminal hBS hr hU hV hUV hcov hUc hVc
  obtain ⟨hA, -, hAne, -⟩ := sides_continua hBS hr hU hV hUV hcov hUc hVc
  have hCne : closure V ≠ univ := by
    obtain ⟨u, hu⟩ := hUc.nonempty
    intro e
    exact Set.disjoint_left.mp (hUV.closure_right hU) hu (e ▸ mem_univ u)
  have himg_ne : ∀ {K : Set S'}, K ≠ univ → ((↑) : S' → S) '' K ≠ S' := by
    intro K hK e
    apply hK
    refine eq_univ_of_forall fun x => ?_
    have : (x : S) ∈ ((↑) : S' → S) '' K := by rw [e]; exact x.2
    obtain ⟨y, hy, hyx⟩ := this
    rwa [← Subtype.ext hyx]
  have chain : ∀ {K : Set S'}, Fold.Q78.IsContinuum K → K ≠ univ → CondB K μ →
      ∃ (x : ℕ) (E : Chain S x) (hx : 0 < x), IsEpsChain E ε ∧
        ((↑) : S' → S) '' K ⊆ E.union ∧ (μ : S) ∈ E.link ⟨x - 1, by omega⟩ := by
    intro K hK hKne hB
    obtain ⟨m, D, hD, hKD⟩ := hmin _ (Subtype.coe_image_subset _ _) (isContinuum_image_val hK)
      (himg_ne hKne)
    obtain ⟨n, F, hn, hKF, hFD, z, hz, hzF, -⟩ := fugate_lemma1 (isContinuum_image_val hK)
      ((isTerminalSub_singleton_iff _ _).mpr (condB_image_val hB)) D hKD
    rw [mem_singleton_iff] at hz
    subst hz
    exact ⟨n, F, hn, isEpsChain_of_refines hFD hD, hKF, hzF⟩
  have hACS : ((↑) : S' → S) '' (U ∪ bingElt r) ∪ ((↑) : S' → S) '' closure V = S' := by
    rw [← image_union, hunion, image_univ, Subtype.range_coe]
  exact hnc (epsCoverable_of_halves hS' (hS.hu.mono (subset_univ _)) (isContinuum_image_val hA)
    (isContinuum_image_val hC) hACS ⟨⟨μ, hμ.1, rfl⟩, ⟨μ, hμ.2, rfl⟩⟩
    (claim1_image_val fun Q hQ hQC hm hn =>
      claim1_contains_inter hBS hr hU hV hUV hcov hUc hVc hQ hQC (by rwa [inter_assoc]) hn)
    hε (chain hA hAne hBA) (chain hC hCne hBC))

/-- **Theorem 11 as stated by Bing**: for a compact nondegenerate hereditarily decomposable
continuum, snake-like ⇔ atriodic and hereditarily unicoherent. -/
theorem theorem11_1951_iff [ConnectedSpace S] [Nontrivial S]
    (hd : IsHereditarilyDecomposable (univ : Set S)) :
    IsSnakeLike (univ : Set S) ↔
      IsAtriodic (univ : Set S) ∧ IsHereditarilyUnicoherent (univ : Set S) := by
  constructor
  · intro h
    exact ⟨isAtriodic_of_isSnakeLike h, isHereditarilyUnicoherent_of_isSnakeLike h⟩
  · rintro ⟨ha, hu⟩
    exact theorem11_1951 ⟨inferInstance, inferInstance, ha, hu, hd⟩

end HPC.Plane
