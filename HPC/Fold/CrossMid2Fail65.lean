import HPC.Fold.CrossPartner64
import HPC.Fold.Bing9

/-!
# `CrossMid2L5` is false, and where the branch `L + 5` really stands

Batch 64 named the residue of the branch `L + 5` `CrossMid2L5`: *at a basepoint of the branch the
arm that `w8` does not serve has the floor clause of `w71` at its descents to exactly `L + 2`*
(`Mid2Floor`). The census of that batch found the clause at all 461 crossings of the corpus, and
the batch-64 assembly `s3_span_nine_mid5_of_crossMid2_of_low1` takes it as its hypothesis.

**It is false**, and Bing's own chain refutes it. At the basepoint `145` of `bing 0 9`
(`HPC/Fold/Bing9.lean`, 986 links, faithful, span exactly nine with both ends attained) both arms
are `LowAt (L + 1) (L + 8)`, so the basepoint lies in the branch; the forward arm is served by
`w8`; and the backward arm reads

```
5 4 3 4 3 2 3 4 3 4 5 4 3 4 5 4 5 6 …
```

so it descends to exactly `L + 2` at its arm index **five**, having been nowhere near `L + 6`.
`Mid2Floor` asks, at that descent, for a time at `L + 6` or above at arm index three or more and
four steps earlier — that is, at an index in `[3, 1]`, which is empty. So the clause fails
(`not_mid2Floor_bing9_armT`), the arm is not served by `w8` (`not_w8_bing9_armT`), and
`not_crossMid2L5` follows. The hypothesis of `s3_span_nine_mid5_of_crossMid2_of_low1` is therefore
never met, and that assembly is vacuous.

## Why, and how early

Three arm facts explain it and bound it.

* `mid2Floor_of_leg4Land` — `Mid2Floor` is *weaker* than the floor clause of `w8`, of `w71` and
  of `w72` alike, so only an arm outside all three can fail it. That is what made the statement
  look safe.
* `not_leg4Land_of_early_low` — an arm of the branch standing at `L + 2` or below at an index of
  six or less satisfies **no** walk of the family with `P = L + 5` and peak `K ≥ L + 7`: not `w8`,
  not `w71`, not `w72`. Their common floor clause asks for a landmark at index `K - P + 1 ≥ 3`
  and at least `K - 1 - f d ≥ 4` steps before the descent, and `[3, d - 4]` is empty for
  `d ≤ 6`.
* `arm_low_index_ge_five` — and the timing law puts the first such descent no earlier than arm
  index five (`ivSep3`: three levels cost five steps). So the window in which the branch's own
  walks are defeated outright is exactly the two arm indices `5` and `6`, and Bing's chain
  occupies the first of them.

Past index six `Mid2Floor` can still fail — it fails at any descent to `L + 2` whose arm has
stayed at `L + 5` or below throughout `[3, d - 4]` — so the refutation is not a boundary effect of
the first few steps; the witness merely takes the cheapest instance of it.

## What is left standing

The basepoint `145` of `bing 0 9` is **not** a crossing of the trichotomy: `probe65.c` reads its
two arms and finds both served by `wb`, so the pair folds onto that walk (the arm half of this is
`leg4Land_wb_bing9_armT` below; the forward arm's sentence is measured and not proved, its arm
being 841 links long). What the counterexample refutes is the *statement* `CrossMid2L5`, whose
hypothesis is only that `w8` does not serve the arm, and not the crossing of the trichotomy that
the name intends. `CrossMid2L5'` below is the statement with the crossing written out as
`Leg4TriCrossL5` writes it — no walk of the three serves both arms — and
`s3_span_nine_mid5_of_crossMid2'_of_low1` is the batch-64 assembly rebuilt on it. The census of
`census-batch65.c` measures both. Over the corpus of that census — 1 393 322 basepoints of the
branch, 2 786 644 arms — `Mid2Floor` fails on 310 028 arms; none of them satisfies `w8`, `w71` or
`w72` (which is `mid2Floor_of_leg4Land`, checked); 76 178 of them stand at `L + 2` or below within
six arm indices, and the least index of a descent to exactly `L + 2` seen anywhere is `5`, which
is the bound `arm_low_index_ge_five` proves. `CrossMid2L5` fails at 308 258 of those basepoints —
the counterexample is not isolated — and at every one of them a walk of the four-leg family serves
both arms anyway. Of the corpus's 461 crossings of the trichotomy, **none** has an arm failing
`Mid2Floor`, so `CrossMid2L5'` is what the measurement actually supports.
-/

namespace HPC.Fold

/-! ## `Mid2Floor` is weaker than `w8` -/

/-- **`Mid2Floor` is a consequence of the landmark sentence of every walk of the family based at
`L + 5` whose peak is at `L + 7` or above.** Their common floor clause fires at the descents to
`L + 2` and returns exactly what `Mid2Floor` asks — a landmark at index `K - P + 1 ≥ 3`, at least
`K - 1 - f d ≥ 4` steps earlier, at `K - 1 ≥ L + 6` or above. So `Mid2Floor` is *necessary* for
`w8`, for `w71` and for `w72` alike, and only an arm outside all three can fail it, which is why
the statement `CrossMid2L5` looked safe. -/
theorem mid2Floor_of_leg4Land {m : ℕ} {f : Fin m → ℤ} {L H K M : ℤ} (hK : L + 7 ≤ K)
    (h : Leg4Land f H K M (L + 5)) : Mid2Floor f L := by
  intro d hd
  obtain ⟨j, h1, h2, h3⟩ := h.1 d (by omega)
  exact ⟨j, by omega, by omega, by omega⟩

/-- **In particular an arm served by `w8` has `Mid2Floor`.** -/
theorem mid2Floor_of_leg4Land_w8 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h8 : Leg4Land f (L + 9) (L + 8) (L + 1) (L + 5)) : Mid2Floor f L :=
  mid2Floor_of_leg4Land (by omega) h8

/-- **And so does an arm served by `w71`.** -/
theorem mid2Floor_of_leg4Land_w71 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h : Leg4Land f (L + 9) (L + 7) (L + 1) (L + 5)) : Mid2Floor f L :=
  mid2Floor_of_leg4Land (by omega) h

/-- **Or by `w72`.** -/
theorem mid2Floor_of_leg4Land_w72 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h : Leg4Land f (L + 9) (L + 7) (L + 2) (L + 5)) : Mid2Floor f L :=
  mid2Floor_of_leg4Land (by omega) h

/-! ## An early descent to `L + 2` defeats every walk based at `L + 5` -/

/-- **`Mid2Floor` fails at any descent to exactly `L + 2` at arm index six or less.** The clause
asks for a landmark at an index in `[3, d - 4]`, and that range is empty. -/
theorem not_mid2Floor_of_early {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (d : Fin m)
    (hd : f d = L + 2) (hlt : d.val ≤ 6) : ¬ Mid2Floor f L := by
  intro h
  obtain ⟨j, h1, h2, -⟩ := h d hd
  omega

/-- **And so does the floor clause of every walk of the family based at `L + 5` whose peak is at
`L + 7` or above.** This covers `w8 = (9, 8, 1, 5)`, `w71 = (9, 7, 1, 5)` and
`w72 = (9, 7, 2, 5)` at once: an arm at `L + 2` or below at an index of six or less satisfies
none of them. -/
theorem not_leg4Land_of_early_low {m : ℕ} {f : Fin m → ℤ} {L H K M : ℤ} (hK : L + 7 ≤ K)
    (d : Fin m) (hd : f d ≤ L + 2) (hlt : d.val ≤ 6) : ¬ Leg4Land f H K M (L + 5) := by
  intro h
  obtain ⟨j, h1, h2, -⟩ := h.1 d (by omega)
  omega

/-! ## The timing law: no descent to `L + 2` before arm index five -/

/-- **Three levels cost five steps.** A link of the band at `L + 2` or below is at least five
indices from the basepoint of the branch, on whichever side it lies. -/
theorem arm_low_index_ge_five {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (i t : Fin n) (L : ℤ) (hp : ρ i = L + 5) (ht : ρ t ≤ L + 2) :
    i.val + 5 ≤ t.val ∨ t.val + 5 ≤ i.val := by
  have hne : t.val ≠ i.val := by
    intro h
    rw [Fin.ext h, hp] at ht
    omega
  rcases ivSep3 hcr t i hne (ρ t) (L + 5) (by omega) le_rfl (hcr.le t) (by omega)
    (by have := hcr.le i; omega) with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- **On the forward arm**: a time at `L + 2` or below lies at arm index five or more. -/
theorem armG_low_index_ge_five {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (d : Fin (n - i.val)) (hd : armG ρ i d ≤ L + 2) :
    5 ≤ d.val := by
  have hi := i.isLt
  have hdlt := d.isLt
  have := arm_low_index_ge_five hcr i ⟨i.val + d.val, by omega⟩ L hp hd
  simp only at this
  omega

/-- **On the backward arm**: the same. -/
theorem armT_low_index_ge_five {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (d : Fin (i.val + 1)) (hd : armT ρ i d ≤ L + 2) :
    5 ≤ d.val := by
  have hi := i.isLt
  have hdlt := d.isLt
  have := arm_low_index_ge_five hcr i ⟨i.val - d.val, by omega⟩ L hp hd
  simp only at this
  omega

/-! ## The witness: the basepoint `145` of `bing 0 9` -/

/-- The basepoint of the refutation: the link `145` of Bing's 986-link chain. -/
abbrev bing9Pt : Fin 986 := ⟨145, by norm_num⟩

theorem bing9Pt_level : bing9 bing9Pt = 0 + 5 := by decide +kernel

/-- The backward arm stands at `L + 2` at its arm index five: its levels begin
`5 4 3 4 3 2 3 4 3 4 5 4 …`. -/
theorem bing9_armT_five : armT bing9 bing9Pt ⟨5, by decide⟩ = 0 + 2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem bing9_lowAt_armG : LowAt (armG bing9 bing9Pt) (0 + 1) (0 + 8) := by
  unfold LowAt
  decide +kernel

set_option maxRecDepth 100000 in
theorem bing9_lowAt_armT : LowAt (armT bing9 bing9Pt) (0 + 1) (0 + 8) := by
  unfold LowAt
  decide +kernel

/-- **The backward arm fails `Mid2Floor`.** -/
theorem not_mid2Floor_bing9_armT : ¬ Mid2Floor (armT bing9 bing9Pt) 0 :=
  not_mid2Floor_of_early ⟨5, by decide⟩ bing9_armT_five (by norm_num)

/-- **And it is not served by `w8`** — nor by `w71` or `w72`, by the same lemma. -/
theorem not_w8_bing9_armT :
    ¬ Leg4Land (armT bing9 bing9Pt) (0 + 9) (0 + 8) (0 + 1) (0 + 5) :=
  not_leg4Land_of_early_low (by norm_num) ⟨5, by decide⟩
    (le_of_eq bing9_armT_five) (by norm_num)

theorem not_w71_bing9_armT :
    ¬ Leg4Land (armT bing9 bing9Pt) (0 + 9) (0 + 7) (0 + 1) (0 + 5) :=
  not_leg4Land_of_early_low (by norm_num) ⟨5, by decide⟩
    (le_of_eq bing9_armT_five) (by norm_num)

theorem not_w72_bing9_armT :
    ¬ Leg4Land (armT bing9 bing9Pt) (0 + 9) (0 + 7) (0 + 2) (0 + 5) :=
  not_leg4Land_of_early_low (by norm_num) ⟨5, by decide⟩
    (le_of_eq bing9_armT_five) (by norm_num)

/-- **`CrossMid2L5` is false.** -/
theorem not_crossMid2L5 : ¬ CrossMid2L5 := by
  intro h
  exact not_mid2Floor_bing9_armT
    ((h 986 bing9 bing9 bing9Pt 0 bing9_isLip bing9_faithful
        (fun t => by have := bing9_lb t; omega) (fun t => by have := bing9_ub t; omega)
        bing9Pt_level bing9_lowAt_armG bing9_lowAt_armT).1 not_w8_bing9_armT)

/-! ## The failing arm is a `wb` partner -/

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **The arm that fails `Mid2Floor` is served by `wb`**, the reflected walk
`L+6 → L+3 → L+7 → L+1 → L+8` — it is a partner of exactly the kind `leg4Land_w71_of_wb_of_mid2`
is about. So `Mid2Floor` is not a consequence of `wb`, of the band, or of the branch hypothesis:
`wb` fires at the ascents to `L + 8` and at the descents to `L + 1`, and says nothing at a descent
that stops at `L + 2`. -/
theorem leg4Land_wb_bing9_armT :
    Leg4Land (armRefl (0 + (0 + 9)) (armT bing9 bing9Pt)) (0 + 9) (0 + 6) (0 + 2) (0 + 4) := by
  unfold Leg4Land armRefl
  decide +kernel

/-! ## The statement with the crossing written out -/

/-- **A crossing of the trichotomy at the branch `L + 5`**: no walk of the three of `leg4Land_tri`
serves both arms. This is the hypothesis `Leg4TriCrossL5` carries and the one `CrossMid2L5`
dropped. -/
def TriCrossL5 {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ¬ (Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5) ∧
      Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5)) ∧
  ¬ (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∧
      Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4)) ∧
  ¬ (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) ∧
      Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4))

/-- **The residue, restated.** `CrossMid2L5` with the crossing of the trichotomy as a hypothesis.
The counterexample above does not touch it: the basepoint `145` of `bing 0 9` is not a crossing.
`census-batch65.c` measures the statement over the corpus. -/
def CrossMid2L5' : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ), IsLip ρ → IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) → ρ i = L + 5 →
    LowAt (armG ρ i) (L + 1) (L + 8) → LowAt (armT ρ i) (L + 1) (L + 8) →
    TriCrossL5 ρ i L →
    (¬ Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5) → Mid2Floor (armT ρ i) L) ∧
    (¬ Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5) → Mid2Floor (armG ρ i) L)

/-- **The batch-64 assembly, rebuilt on the corrected residue.** At a crossing of the trichotomy
whose forward arm is served by `w8`, whose backward arm is served by `wb`, and whose crossing
witness descends to `L + 1`, the pair folds. -/
theorem s3_span_nine_mid5_of_crossMid2'_of_low1 (hres : CrossMid2L5') {n : ℕ} {ρ σ : Fin n → ℤ}
    (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L ≤ ρ t)
    (hG : LowAt (armG ρ i) (L + 1) (L + 8)) (hT : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross3 : TriCrossL5 ρ i L)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hb : Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4))
    (hpair : ∀ dG : Fin (n - i.val), L + 9 ≤ armG ρ i dG →
      ∃ dT : Fin (i.val + 1), armT ρ i dT ≤ L + 1 ∧
        ¬ ∃ j : Fin (i.val + 1), 4 ≤ (j.val : ℤ) ∧
            (j.val : ℤ) + (L + 7 - armT ρ i dT) ≤ (dT.val : ℤ) ∧ L + 7 ≤ armT ρ i j) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hnot8 : ¬ Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5) := fun hT8 =>
    hcross3.1 ⟨h8, hT8⟩
  exact s3_span_nine_mid5_of_cross_low1_wb_armT hcr hlip i L hp hHb hLb h8 hb
    ((hres n ρ σ i L hlip hcr hLb hHb hp hG hT hcross3).1 hnot8) hpair

end HPC.Fold
