import HPC.Fold.Decide
import HPC.Fold.LandList

/-!
# The extension law, as a decidable statement

Batch 75 found one uniform regularity in the census of least walks (§2.1 there): at every sampled
basepoint of least leg count `k ≥ 3`, at spans eight to fourteen, a least walk is a walk serving
the basepoint in a sub-band — a band `[L', H']` of smaller span, the arms truncated at their first
exit from it — with exactly one leg appended at the end, run to `L + 1` or to `H − 1`. This file
states that regularity exactly, as a predicate of a finite pair and a basepoint, proves that the
predicate is decidable, and records the conjecture it supports. Nothing here is a step towards
`s3_general`, and no statement here is claimed beyond what is proved.

* `bandPrefixLen`, `truncArm` — an arm truncated at its first exit from a band.
* `ExtendsSubBand ρ i L H k` — the extension law at one basepoint, with `k` the number of legs of
  the extended walk.
* `extendsSubBandB`, `extendsSubBandB_iff`, the `Decidable` instance — the predicate is decided by
  a finite search, and the search is proved equal to the definition.
* `walkList_mem_Icc` — the walk of a start and a target list inside `[L', H']` has all its levels
  in `[L', H']`, so the clause "a walk `w'` with levels in `[L', H']`" is what the definition says.
* `foldsOnto_arms_of_split` — two-arm gluing, as the repository's lemmas give it: each arm is
  glued at its own split index with its own arrival time; the two arms share only the walk.

The kernel checks at the stored witnesses of batches 72, 71, 74 and 75 are in
`HPC/Fold/Audit76.lean`.

## The conjecture (not proved; a census statement)

```
-- Conjecture (batch 76). For every span S ≥ 8, every basepoint of a faithful pair of span S
-- whose least leg count is at least three satisfies the extension law at its least leg count:
--
--   ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L H : ℤ) (k : ℕ),
--     IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) →
--     (∃ t, ρ t = L) → (∃ t, ρ t = H) → L + 8 ≤ H →
--     LeastLegs ρ i L H k → 3 ≤ k →
--     ExtendsSubBand ρ i L H k
--
-- where `LeastLegs ρ i L H k` says that some walk with k turning targets in [L+1, H−1] (directions
-- alternating, start within one of ρ i) folds both whole arms and none with fewer does.
--
-- Evidence: census-batch75.c (batch 75 §2.1, 17 425 sampled basepoints, spans 8–14, found by a
-- sub-walk search) and census-batch76.c, which decides ExtendsSubBand exactly at every sampled
-- basepoint of spans 8–14 (logs census-batch76-span8.log … -span14.log; the counts are in
-- REPORT-batch76.md §2.3), and the kernel checks of HPC/Fold/Audit76.lean.
```

`LeastLegs` is not defined in Lean here: the conjecture is recorded as a comment, as commissioned,
and its hypothesis on the least leg count is the census's.
-/

namespace HPC.Fold

/-! ## Truncating an arm at its first exit from a band -/

/-- The number of leading indices `j < m` at which `g j` lies in `[lo, hi]`: the index of the
first exit from the band, or `m` if there is none. -/
def bandPrefixLen (g : ℕ → ℤ) (m : ℕ) (lo hi : ℤ) : ℕ :=
  (List.range m).findIdx fun j => !(decide (lo ≤ g j ∧ g j ≤ hi))

/-- **An arm truncated at its first exit from `[lo, hi]`.** -/
def truncArm {m : ℕ} (f : Fin m → ℤ) (lo hi : ℤ) : Fin (bandPrefixLen (armSeq f) m lo hi) → ℤ :=
  fun j => armSeq f j.val

theorem bandPrefixLen_le (g : ℕ → ℤ) (m : ℕ) (lo hi : ℤ) : bandPrefixLen g m lo hi ≤ m := by
  unfold bandPrefixLen
  simpa using List.findIdx_le_length (p := fun j => !(decide (lo ≤ g j ∧ g j ≤ hi)))
    (xs := List.range m)

/-- Every index before the truncation is in the band. -/
theorem mem_band_of_lt_bandPrefixLen {g : ℕ → ℤ} {m : ℕ} {lo hi : ℤ} {j : ℕ}
    (hj : j < bandPrefixLen g m lo hi) : lo ≤ g j ∧ g j ≤ hi := by
  have hjm : j < m := lt_of_lt_of_le hj (bandPrefixLen_le g m lo hi)
  unfold bandPrefixLen at hj
  have h := List.not_of_lt_findIdx hj
  simpa [List.getElem_range] using h

/-- The truncation index, when it is below `m`, is out of the band. -/
theorem not_mem_band_bandPrefixLen {g : ℕ → ℤ} {m : ℕ} {lo hi : ℤ}
    (hlt : bandPrefixLen g m lo hi < m) :
    ¬ (lo ≤ g (bandPrefixLen g m lo hi) ∧ g (bandPrefixLen g m lo hi) ≤ hi) := by
  unfold bandPrefixLen at hlt ⊢
  have hw : List.findIdx (fun j => !(decide (lo ≤ g j ∧ g j ≤ hi))) (List.range m) <
      (List.range m).length := by simpa using hlt
  have h := List.findIdx_getElem (w := hw)
  simp only [List.getElem_range, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at h
  exact h

/-- The truncated arm is the arm, read up to the truncation. -/
theorem truncArm_apply {m : ℕ} (f : Fin m → ℤ) (lo hi : ℤ)
    (j : Fin (bandPrefixLen (armSeq f) m lo hi)) :
    truncArm f lo hi j = f ⟨j.val, lt_of_lt_of_le j.isLt (bandPrefixLen_le _ _ _ _)⟩ := by
  simp [truncArm, armSeq, lt_of_lt_of_le j.isLt (bandPrefixLen_le _ _ _ _)]

/-! ## The walk of a target list stays in the band of its targets -/

/-- **The levels of `walkList s ts` lie in `[lo, hi]`** when the start and every target do. -/
theorem walkList_mem_Icc {lo hi : ℤ} :
    ∀ (s : ℤ) (ts : List ℤ), lo ≤ s → s ≤ hi → (∀ t ∈ ts, lo ≤ t ∧ t ≤ hi) →
      ∀ p, lo ≤ walkList s ts p ∧ walkList s ts p ≤ hi := by
  intro s ts
  induction ts generalizing s with
  | nil => intro h1 h2 _ p; exact ⟨h1, h2⟩
  | cons t ts ih =>
    intro h1 h2 hts p
    have ht := hts t List.mem_cons_self
    rw [walkList]
    split_ifs with hp hst
    · omega
    · omega
    · exact ih t ht.1 ht.2 (fun u hu => hts u (List.mem_cons_of_mem _ hu)) _

/-! ## The extension law -/

/-- **`ExtendsSubBand ρ i L H k`** — the extension law at the basepoint `i`, with `k` the number of
legs of the extended walk. There are `L ≤ L' ≤ ρ i ≤ H' ≤ H` with `H' − L' ≤ H − L − 3`, a walk
`w'` — a start `s` and `k − 1` targets, all in `[L', H']`, so that every level of `w'` is in
`[L', H']` (`walkList_mem_Icc`) — folding both arms truncated at their first exit from `[L', H']`,
and a level `e ∈ {L + 1, H − 1}` different from the last level of `w'`, such that the walk `w`
equal to `w'` with one leg appended to `e` folds both whole arms. -/
def ExtendsSubBand {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L H : ℤ) (k : ℕ) : Prop :=
  ∃ (L' H' s e : ℤ) (ts : List ℤ),
    L ≤ L' ∧ L' ≤ ρ i ∧ ρ i ≤ H' ∧ H' ≤ H ∧ H' - L' ≤ H - L - 3 ∧
    L' ≤ s ∧ s ≤ H' ∧ ts.length = k - 1 ∧ (∀ t ∈ ts, L' ≤ t ∧ t ≤ H') ∧
    (e = L + 1 ∨ e = H - 1) ∧ e ≠ (s :: ts).getLast (List.cons_ne_nil s ts) ∧
    FoldsOnto (truncArm (armG ρ i) L' H') (walkLen s ts) (walkList s ts) ∧
    FoldsOnto (truncArm (armT ρ i) L' H') (walkLen s ts) (walkList s ts) ∧
    FoldsOnto (armG ρ i) (walkLen s (ts ++ [e])) (walkList s (ts ++ [e])) ∧
    FoldsOnto (armT ρ i) (walkLen s (ts ++ [e])) (walkList s (ts ++ [e]))

/-! ## The finite search -/

/-- The integers of `[lo, hi]`, as a list. -/
def intRange (lo hi : ℤ) : List ℤ :=
  (List.range (hi - lo + 1).toNat).map fun j : ℕ => lo + (j : ℤ)

theorem mem_intRange {lo hi x : ℤ} : x ∈ intRange lo hi ↔ lo ≤ x ∧ x ≤ hi := by
  simp only [intRange, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · intro h; exact ⟨(x - lo).toNat, by omega, by omega⟩

/-- The lists of length `n` with entries in `A`. -/
def listsOver : ℕ → List ℤ → List (List ℤ)
  | 0, _ => [[]]
  | n + 1, A => A.flatMap fun a => (listsOver n A).map (a :: ·)

theorem mem_listsOver {A : List ℤ} :
    ∀ {n : ℕ} {ts : List ℤ}, ts ∈ listsOver n A ↔ ts.length = n ∧ ∀ t ∈ ts, t ∈ A := by
  intro n
  induction n with
  | zero => intro ts; cases ts <;> simp [listsOver]
  | succ n ih =>
    intro ts
    cases ts with
    | nil => simp [listsOver]
    | cons t ts =>
      simp only [listsOver, List.mem_flatMap, List.mem_map, List.cons.injEq, List.length_cons,
        List.mem_cons, forall_eq_or_imp, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨a, ha, l, hl, rfl, rfl⟩
        exact ⟨(ih.1 hl).1, ha, (ih.1 hl).2⟩
      · rintro ⟨hlen, ht, hts⟩
        exact ⟨t, ht, ts, ih.2 ⟨hlen, hts⟩, rfl, rfl⟩

/-- The verdict of the finite search. -/
def extendsSubBandB {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L H : ℤ) (k : ℕ) : Bool :=
  (intRange L H).any fun L' => (intRange L H).any fun H' =>
    decide (L' ≤ ρ i ∧ ρ i ≤ H' ∧ H' - L' ≤ H - L - 3) &&
    (intRange L' H').any fun s => (listsOver (k - 1) (intRange L' H')).any fun ts =>
      [L + 1, H - 1].any fun e =>
        decide (e ≠ (s :: ts).getLast (List.cons_ne_nil s ts)) &&
        foldsB (truncArm (armG ρ i) L' H') (walkLen s ts) (walkList s ts) &&
        foldsB (truncArm (armT ρ i) L' H') (walkLen s ts) (walkList s ts) &&
        foldsB (armG ρ i) (walkLen s (ts ++ [e])) (walkList s (ts ++ [e])) &&
        foldsB (armT ρ i) (walkLen s (ts ++ [e])) (walkList s (ts ++ [e]))

/-- **The search is the definition.** -/
theorem extendsSubBandB_iff {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L H : ℤ) (k : ℕ) :
    extendsSubBandB ρ i L H k = true ↔ ExtendsSubBand ρ i L H k := by
  unfold extendsSubBandB ExtendsSubBand
  simp only [List.any_eq_true, mem_intRange, mem_listsOver, Bool.and_eq_true, decide_eq_true_eq,
    foldsB_iff, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨L', ⟨hL1, -⟩, H', ⟨-, hH2⟩, ⟨h1, h2, h3⟩, s, ⟨hs1, hs2⟩, ts, ⟨hlen, hts⟩, e, he,
      ⟨⟨⟨hne, hG'⟩, hT'⟩, hG⟩, hT⟩
    exact ⟨L', H', s, e, ts, hL1, h1, h2, hH2, h3, hs1, hs2, hlen, hts, he, hne, hG', hT', hG, hT⟩
  · rintro ⟨L', H', s, e, ts, hL1, h1, h2, hH2, h3, hs1, hs2, hlen, hts, he, hne, hG', hT', hG, hT⟩
    exact ⟨L', ⟨hL1, by omega⟩, H', ⟨by omega, hH2⟩, ⟨h1, h2, h3⟩, s, ⟨hs1, hs2⟩, ts, ⟨hlen, hts⟩,
      e, he, ⟨⟨⟨hne, hG'⟩, hT'⟩, hG⟩, hT⟩

/-- **`ExtendsSubBand` is decidable** on a concrete pair and basepoint. -/
instance decidableExtendsSubBand {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L H : ℤ) (k : ℕ) :
    Decidable (ExtendsSubBand ρ i L H k) :=
  decidable_of_iff _ (extendsSubBandB_iff ρ i L H k)

/-- **A witness, checked component by component.** The form in which the kernel checks of
`HPC/Fold/Audit76.lean` are made: every clause of `ExtendsSubBand` for one explicit choice of
`L', H', s, ts, e`, the four folds given as verdicts of `foldsB`. -/
theorem extendsSubBand_of_witness {n : ℕ} {ρ : Fin n → ℤ} {i : Fin n} {L H : ℤ} {k : ℕ}
    (L' H' s e : ℤ) (ts : List ℤ)
    (hband : decide (L ≤ L' ∧ L' ≤ ρ i ∧ ρ i ≤ H' ∧ H' ≤ H ∧ H' - L' ≤ H - L - 3 ∧
      L' ≤ s ∧ s ≤ H' ∧ ts.length = k - 1 ∧ (e = L + 1 ∨ e = H - 1)) = true)
    (hts : (ts.all fun t => decide (L' ≤ t ∧ t ≤ H')) = true)
    (he : decide (e ≠ (s :: ts).getLast (List.cons_ne_nil s ts)) = true)
    (hG' : foldsB (truncArm (armG ρ i) L' H') (walkLen s ts) (walkList s ts) = true)
    (hT' : foldsB (truncArm (armT ρ i) L' H') (walkLen s ts) (walkList s ts) = true)
    (hG : foldsB (armG ρ i) (walkLen s (ts ++ [e])) (walkList s (ts ++ [e])) = true)
    (hT : foldsB (armT ρ i) (walkLen s (ts ++ [e])) (walkList s (ts ++ [e])) = true) :
    ExtendsSubBand ρ i L H k := by
  simp only [decide_eq_true_eq] at hband he
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hband
  refine ⟨L', H', s, e, ts, h1, h2, h3, h4, h5, h6, h7, h8, fun t ht => ?_, h9, he,
    foldsOnto_of_foldsB hG', foldsOnto_of_foldsB hT', foldsOnto_of_foldsB hG,
    foldsOnto_of_foldsB hT⟩
  have := List.all_eq_true.1 hts t ht
  simpa using this

/-! ## Two-arm gluing, as the repository's lemmas give it -/

/-- **Two-arm gluing needs no common arrival time.** `FoldsOnto` gives each arm its own
itinerary; the two arms share only the walk `(len, c)`. So each arm is glued by `foldsFrom_split`
at its own split index (`sG` on the forward arm, `sT` on the backward arm) with its own arrival
time (`uG`, `uT`), and nothing relates `uG` to `uT` or `sG` to `sT`. This is the form in which
`s3_at_window` (`HPC/Fold/Cut.lean`) uses the lemma, and the form `Tracking` states. -/
theorem foldsOnto_arms_of_split {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (len : ℕ) (c : ℕ → ℤ)
    (sG uG : ℕ) (hsG : sG < n - i.val)
    (hpreG : ∃ β : Fin (sG + 1) → ℕ, (∀ j, β j < len) ∧
      (∀ j j' : Fin (sG + 1), j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1) ∧
      (∀ j : Fin (sG + 1), j.val = 0 → β j = 0) ∧
      (∀ j : Fin (sG + 1), j.val = sG → β j = uG) ∧
      ∀ j : Fin (sG + 1), |armG ρ i ⟨j.val, by omega⟩ - c (β j)| ≤ 1)
    (hsufG : FoldsFrom (fun j : Fin (n - i.val - sG) => armG ρ i ⟨sG + j.val, by omega⟩)
      len c uG)
    (sT uT : ℕ) (hsT : sT < i.val + 1)
    (hpreT : ∃ β : Fin (sT + 1) → ℕ, (∀ j, β j < len) ∧
      (∀ j j' : Fin (sT + 1), j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1) ∧
      (∀ j : Fin (sT + 1), j.val = 0 → β j = 0) ∧
      (∀ j : Fin (sT + 1), j.val = sT → β j = uT) ∧
      ∀ j : Fin (sT + 1), |armT ρ i ⟨j.val, by omega⟩ - c (β j)| ≤ 1)
    (hsufT : FoldsFrom (fun j : Fin (i.val + 1 - sT) => armT ρ i ⟨sT + j.val, by omega⟩)
      len c uT) :
    FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  ⟨foldsFrom_split (armG ρ i) len c 0 uG sG hsG hpreG hsufG,
    foldsFrom_split (armT ρ i) len c 0 uT sT hsT hpreT hsufT⟩

end HPC.Fold
