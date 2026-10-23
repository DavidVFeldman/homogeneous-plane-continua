import HPC.Plane.Atriodic51BNine
import HPC.Plane.Atriodic51BCounter

/-!
# Bing 1951 (*Snake-like continua*), §4, part two: Theorem 8 with Bing's own elements, and Theorem 9

Skeleton for batch 93 (save as `HPC/Plane/Atriodic51B.lean`; add `import HPC.Plane.Atriodic51B` to
the root `HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted
with the change recorded; `theorem8_1951'` keeps its conclusion.

**Correction to batch 92.** Bing's definition (p. 658) is: "for each point `p` let `g_p` denote the
intersection of all continua which contain *interiorly a continuum that* contains `p` interiorly."
The batch-92 skeleton (and §5 of its commission) dropped the inner layer and defined `gElt p` as the
intersection of all continua containing `p` interiorly. `Counter92` refutes the one-layer variant;
it does not touch Bing's. `bingElt` below is Bing's definition. Nothing in the batch-92 files is to
be changed except the ledger note of item 4 of the commission.

**Status (batch 93).** `theorem8_1951'`, `gElt_subset_bingElt`, `Counter92.bingElt_bar`,
`Counter92.bingElt_curve`, step 2 (`bingH_iInter`) and `condA_of_bingH_singleton` are proved.
Steps 1 and 3 (`endElt_mem_bingH`, `bingH_irreducible_singleton`) are open, so `theorem9_1951`
depends on them; `theorem9_1951_of_steps` is Theorem 9 with the two open steps as hypotheses,
proved. `bingH_step3_iff` shows step 3 is equivalent to "every member of `H` contains a point
satisfying condition A". See `REPORT-batch93.md`. Supporting files: `Atriodic51BElt.lean`
(Theorem 8), `Atriodic51BNine.lean` (Brouwer reduction), `Atriodic51BCounter.lean` (`S₀`).
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! `ContainsNested`, `bingElt` and the bridge `gElt_subset_bingElt` (statements unchanged) are in
`HPC/Plane/Atriodic51BElt.lean`, imported here, so that the supporting files can use them. -/

/-- **Theorem 8** (Bing 1951, p. 658) with Bing's elements; conclusion as in batch 92's
`theorem8_1951`, now for `bingElt`. -/
theorem theorem8_1951' (hS : BingS S) :
    (∀ p : S, Fold.Q78.IsContinuum (bingElt p)) ∧
    (∀ p : S, p ∈ bingElt p) ∧ (∀ p q : S, q ∈ bingElt p → bingElt p = bingElt q) ∧
    (∀ (p : S) (U : Set S), IsOpen U → bingElt p ⊆ U →
      IsOpen (⋃ q ∈ {q | bingElt q ⊆ U}, bingElt q)) ∧
    (∀ p q r : S, bingElt p ≠ bingElt q → bingElt q ≠ bingElt r → bingElt p ≠ bingElt r →
      Separates (bingElt p) (bingElt q) (bingElt r) ∨
        Separates (bingElt q) (bingElt p) (bingElt r) ∨
        Separates (bingElt r) (bingElt p) (bingElt q)) ∧
    (∀ p : S, interior (bingElt p) = ∅) ∧
    (∀ r s : S, (∀ q q' : S, bingElt q ≠ bingElt r → bingElt q' ≠ bingElt r →
          bingElt q ≠ bingElt q' → ¬ Separates (bingElt r) (bingElt q) (bingElt q')) →
      (∀ q q' : S, bingElt q ≠ bingElt s → bingElt q' ≠ bingElt s → bingElt q ≠ bingElt q' →
          ¬ Separates (bingElt s) (bingElt q) (bingElt q')) →
      bingElt r ≠ bingElt s →
      ∀ M : Set S, Fold.Q78.IsContinuum M → r ∈ M → s ∈ M → M = univ) :=
  ⟨bingElt_isContinuum hS, mem_bingElt, bingElt_partition hS, fun _ U hU _ => bingElt_usc hS U hU,
    bingElt_separates_triple hS, bingElt_interior_eq_empty hS, bingElt_irreducible hS⟩

namespace Counter92

/-- **The corrected elements on the counterexample**: every bar point's element is the whole bar
`[0, 2] × {0}` (so `G` = {curve points} ∪ {bar}, and the one-layer failure disappears). -/
theorem bingElt_bar {b : S₀} (hb0 : b.1.2 = 0) : bingElt b = {z : S₀ | z.1.2 = 0} := by
  refine Subset.antisymm (fun z hz => ?_)
    (fun u hu => mem_sInter.mpr fun H ⟨hH, H', hH', hH'H, hbH'⟩ => ?_)
  · -- `z` lies in every window `{|y| ≤ ε}`
    have key : ∀ ε, 0 < ε → |z.1.2| ≤ ε := fun ε hε =>
      abs_le.mpr (bingElt_subset (isContinuum_window (c := b) ⟨by linarith, by linarith⟩)
        (containsNested_window (by linarith) (by linarith)) hz)
    show z.1.2 = 0
    by_contra hne
    have hpos := abs_pos.mpr hne
    linarith [key (|z.1.2| / 2) (by positivity)]
  · -- the inner continuum contains a half-bar, hence `(1, 0)`, interiorly in `H`
    have hq0 : q₀.1.2 = 0 := by simp [q₀, bar]
    have hq1 : q₀.1.1 = 1 := by simp [q₀, bar]
    have hu' : (u : S₀).1.2 = 0 := hu
    rcases le_total b.1.1 1 with h1 | h1
    · have hL := barL_subset_of_interior hH' hb0 h1 hbH'
      have hR := barR_subset_of_interior hH hq0 hq1.ge (hH'H (hL ⟨hq0, hq1.le⟩))
      rcases le_total u.1.1 1 with hu1 | hu1
      · exact interior_subset (hH'H (hL ⟨hu', hu1⟩))
      · exact hR ⟨hu', hu1⟩
    · have hR := barR_subset_of_interior hH' hb0 h1 hbH'
      have hL := barL_subset_of_interior hH hq0 hq1.le (hH'H (hR ⟨hq0, hq1.ge⟩))
      rcases le_total u.1.1 1 with hu1 | hu1
      · exact hL ⟨hu', hu1⟩
      · exact interior_subset (hH'H (hR ⟨hu', hu1⟩))

/-- A curve point's element is itself. -/
theorem bingElt_curve {c : S₀} (hc : c.1.2 ≠ 0) : bingElt c = {c} := by
  refine Subset.antisymm (fun z hz => ?_) (singleton_subset_iff.mpr (mem_bingElt c))
  by_contra hzc
  have hne : z.1.2 ≠ c.1.2 := fun h => hzc (eq_of_hgt h (h ▸ hc))
  have hpos := abs_pos.mpr (sub_ne_zero.mpr hne)
  set δ := |z.1.2 - c.1.2| / 2 with hδ
  have h := bingElt_subset (isContinuum_window (c := c) ⟨by linarith, by linarith⟩)
    (containsNested_window (a := c.1.2 - δ) (b := c.1.2 + δ) (by linarith) (by linarith)) hz
  have h2 : |z.1.2 - c.1.2| ≤ δ := abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  linarith

end Counter92

/-- An *end element* of `G`: one that separates no two others. (Shape change, batch 93: the
skeleton's unused argument `hS : BingS S` is dropped.) -/
def IsEndElt (r : S) : Prop :=
  ∀ q q' : S, bingElt q ≠ bingElt r → bingElt q' ≠ bingElt r → bingElt q ≠ bingElt q' →
    ¬ Separates (bingElt r) (bingElt q) (bingElt q')

/-- **Bing's collection `H`** (proof of Theorem 9, p. 659): proper subcontinua `h` of `S` such
that whenever `h` is a proper subcontinuum of a subcontinuum `S'`, `S'` is irreducible from `h` to
some point (`IsIrreducibleBetween` is batch 83's `Theorem14.lean` notion, from a point to a point;
irreducibility from a *set* `h` to a point `p` means: `S'` contains `h ∪ {p}` and no proper
subcontinuum of `S'` does). -/
def IrredFromSet (S' h : Set S) (p : S) : Prop :=
  Fold.Q78.IsContinuum S' ∧ h ⊆ S' ∧ p ∈ S' ∧
    ∀ K : Set S, Fold.Q78.IsContinuum K → K ⊆ S' → h ⊆ K → p ∈ K → K = S'

def BingH (h : Set S) : Prop :=
  Fold.Q78.IsContinuum h ∧ h ≠ univ ∧
    ∀ S' : Set S, Fold.Q78.IsContinuum S' → h ⊆ S' → h ≠ S' → ∃ p : S, IrredFromSet S' h p

/-- **Step 2**: `H` is inductive — the intersection of a decreasing sequence of members is a
member. -/
theorem bingH_iInter (hS : BingS S) {h : ℕ → Set S} (hh : ∀ n, BingH (h n))
    (hanti : Antitone h) : BingH (⋂ n, h n) := by
  have hne : (⋂ n, h n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed h
      (fun n => hanti (Nat.le_succ n)) (fun n => (hh n).1.2.1) (hh 0).1.1
      (fun n => (hh n).1.1.isClosed)
  have hcont : Fold.Q78.IsContinuum (⋂ n, h n) := by
    have := prop1_inter_continuum hS (𝒦 := range h) (range_nonempty h)
      (by rintro _ ⟨n, rfl⟩; exact (hh n).1) (by rwa [sInter_range])
    rwa [sInter_range] at this
  refine ⟨hcont, fun e => (hh 0).2.1 (eq_univ_of_univ_subset (e ▸ iInter_subset h 0)), ?_⟩
  intro S' hS' hsub hne'
  obtain ⟨N, hN⟩ : ∃ N, ¬ S' ⊆ h N := by
    by_contra hall
    push_neg at hall
    exact hne' (Subset.antisymm hsub (subset_iInter hall))
  have hNm : ∀ m, N ≤ m → ¬ S' ⊆ h m := fun m hm hsm => hN (hsm.trans (hanti hm))
  have hmeet : ∀ m, (S' ∩ h m).Nonempty := fun m =>
    hne.mono (subset_inter hsub (iInter_subset h m))
  have hK : ∀ m, Fold.Q78.IsContinuum (S' ∪ h m) := fun m =>
    isContinuum_union hS' (hh m).1 (hmeet m)
  -- `S' ∪ h m` is irreducible from `h m` to some `p m`
  have hp : ∀ m, N ≤ m → ∃ p, IrredFromSet (S' ∪ h m) (h m) p := fun m hm =>
    (hh m).2.2 _ (hK m) subset_union_right (fun e => hNm m hm (e ▸ subset_union_left))
  haveI : Nonempty S := ⟨hne.some⟩
  choose! p hpm using hp
  have hpnot : ∀ m, N ≤ m → p m ∉ h m := fun m hm hpm' =>
    hNm m hm ((hpm m hm).2.2.2 (h m) (hh m).1 subset_union_right subset_rfl hpm' ▸
      subset_union_left)
  set x := p N with hx
  have hxS' : x ∈ S' := ((hpm N le_rfl).2.2.1).resolve_right (hpnot N le_rfl)
  have hKsub : ∀ m, N ≤ m → S' ∪ h m ⊆ S' ∪ h N := fun m hm =>
    union_subset_union_right _ (hanti hm)
  -- the far point `x = p N` serves for every `m ≥ N`
  have claim : ∀ m, N ≤ m → IrredFromSet (S' ∪ h m) (h m) x := by
    intro m hm
    obtain ⟨z, hz⟩ := (hh m).1.2.1
    refine ⟨hK m, subset_union_right, Or.inl hxS', ?_⟩
    intro J hJ hJK hmJ hxJ
    have hJN : J ∪ h N = S' ∪ h N :=
      (hpm N le_rfl).2.2.2 _ (isContinuum_union hJ (hh N).1 ⟨z, hmJ hz, hanti hm hz⟩)
        (union_subset (hJK.trans (hKsub m hm)) subset_union_right) subset_union_right
        (Or.inl hxJ)
    by_cases hpJ : p m ∈ J
    · exact (hpm m hm).2.2.2 J hJ hJK hmJ hpJ
    · exfalso
      have hpN : p m ∈ h N := by
        have : p m ∈ J ∪ h N := hJN ▸ hKsub m hm (hpm m hm).2.2.1
        exact this.resolve_left hpJ
      have hI := hS.inter_two (hh N).1 (hK m) ⟨z, hanti hm hz, Or.inr hz⟩
      have heq := (hpm m hm).2.2.2 _ hI inter_subset_right
        (subset_inter (hanti hm) subset_union_right) ⟨hpN, (hpm m hm).2.2.1⟩
      have hxN : x ∈ h N ∩ (S' ∪ h m) := by rw [heq]; exact Or.inl hxS'
      exact hpnot N le_rfl hxN.1
  refine ⟨x, hS', hsub, hxS', ?_⟩
  intro K hK' hKS hhK hxK
  refine Subset.antisymm hKS fun y hy => ?_
  by_contra hyK
  apply hyK
  apply hhK
  rw [mem_iInter]
  intro m
  have hmN := le_max_right m N
  obtain ⟨z, hz⟩ := hne
  have hU : K ∪ h (max m N) = S' ∪ h (max m N) :=
    (claim _ hmN).2.2.2 _ (isContinuum_union hK' (hh _).1 ⟨z, hhK hz, iInter_subset h _ hz⟩)
      (union_subset_union_left _ hKS) subset_union_right (Or.inl hxK)
  have : y ∈ K ∪ h (max m N) := hU ▸ Or.inl hy
  exact hanti (le_max_left m N) (this.resolve_left hyK)

omit [CompactSpace S] in
/-- A point `{p}` in `H` satisfies condition A for `S`. (Shape change, batch 93: the unused
argument `hS : BingS S` is dropped.) -/
theorem condA_of_bingH_singleton {p : S} (hp : BingH {p}) : CondA (univ : Set S) p := by
  refine ⟨mem_univ p, fun W _ hW hWnt hpW => ?_⟩
  have hne : ({p} : Set S) ≠ W := fun e => hWnt.not_subsingleton (e ▸ subsingleton_singleton)
  have hps : ({p} : Set S) ⊆ W := singleton_subset_iff.mpr hpW
  obtain ⟨q, -, -, hqW, hirr⟩ := hp.2.2 W hW hps hne
  refine ⟨q, fun hqp => hne (hirr {p} ⟨isCompact_singleton, isConnected_singleton⟩ hps subset_rfl
    (hqp ▸ rfl)), hW, hpW, hqW, fun K hK hKW hpK hqK =>
      hirr K hK hKW (singleton_subset_iff.mpr hpK) hqK⟩

/-- Conversely, a point satisfying condition A for `S` gives a member `{p}` of `H`. -/
theorem bingH_singleton_of_condA (hS : BingS S) {p : S} (hp : CondA (univ : Set S) p) :
    BingH {p} := by
  haveI := hS.nontrivial
  refine ⟨⟨isCompact_singleton, isConnected_singleton⟩, fun e => ?_, fun W hW hpW hne => ?_⟩
  · obtain ⟨y, hy⟩ := exists_ne p
    have : y ∈ ({p} : Set S) := e ▸ mem_univ y
    exact hy this
  · have hpW' : p ∈ W := hpW rfl
    have hWnt : W.Nontrivial := by
      obtain ⟨y, hyW, hy⟩ : ∃ y ∈ W, y ≠ p := by
        by_contra hno
        push_neg at hno
        exact hne (Subset.antisymm hpW fun y hy => hno y hy)
      exact ⟨p, hpW', y, hyW, hy.symm⟩
    obtain ⟨q, -, hW', -, hqW, hirr⟩ := hp.2 W (subset_univ _) hW hWnt hpW'
    exact ⟨q, hW', hpW, hqW, fun K hK hKW hpK hqK => hirr K hK hKW (hpK rfl) hqK⟩

/-- **Step 3 is Theorem 9 for the members of `H`**: given the proved inductiveness of `H`, step 3
holds if and only if every member of `H` contains a point satisfying condition A for `S`. -/
theorem bingH_step3_iff (hS : BingS S) :
    (∀ h : Set S, BingH h → (∀ h' : Set S, BingH h' → h' ⊆ h → h' = h) → ∃ p : S, h = {p}) ↔
      ∀ h : Set S, BingH h → ∃ p ∈ h, CondA (univ : Set S) p := by
  constructor
  · intro hQ3 h hh
    obtain ⟨m, hmh, hm, hmin⟩ := exists_minimal_of_seq BingH (fun s hs => hs.1.1.isClosed)
      (fun h hh ha => bingH_iInter hS hh ha) hh
    obtain ⟨p, rfl⟩ := hQ3 m hm hmin
    exact ⟨p, hmh rfl, condA_of_bingH_singleton hm⟩
  · intro hA h hh hmin
    obtain ⟨p, hph, hp⟩ := hA h hh
    exact ⟨p, (hmin {p} (bingH_singleton_of_condA hS hp) (singleton_subset_iff.mpr hph)).symm⟩

/-- **Theorem 9, conditional form** (batch 93): Bing's assembly — Brouwer reduction on `H` inside
the end element (using the proved inductiveness `bingH_iInter`), then step 3, then
`condA_of_bingH_singleton` — with the two unproved steps (step 1, `endElt_mem_bingH`, and step 3,
`bingH_irreducible_singleton`) as hypotheses. -/
theorem theorem9_1951_of_steps (hS : BingS S)
    (hQ1 : ∀ r : S, IsEndElt r → BingH (bingElt r))
    (hQ3 : ∀ h : Set S, BingH h → (∀ h' : Set S, BingH h' → h' ⊆ h → h' = h) → ∃ p : S, h = {p})
    {r : S} (hr : IsEndElt r) :
    ∃ p ∈ bingElt r, CondA (univ : Set S) p := by
  obtain ⟨m, hmr, hm, hmin⟩ := exists_minimal_of_seq BingH (fun s hs => hs.1.1.isClosed)
    (fun h hh ha => bingH_iInter hS hh ha) (hQ1 r hr)
  obtain ⟨p, rfl⟩ := hQ3 m hm hmin
  exact ⟨p, hmr rfl, condA_of_bingH_singleton hm⟩

end HPC.Plane
