import HPC.Fold.Step

/-!
# The cut route

The outside-in route is closed in the form that could carry an induction. Batch 34 proved that
a trim of span one less can never be appended to (`no_outer_member_of_span_one_trim`), so the
trim must strip both extreme levels; and with the trim corrected the "every inner-serving walk
extends" form is **false**.

What had never been attempted is the route through the cut: `crookedIvF_cut_first` (batch 26)
produces, between an index at the bottom and a later one at the top, two banded stretches whose
bands are narrower than the ambient. This file runs that route, and reports what it finds.

**The commissioned `CutData` is empty.** Its two clauses `atR` and `bandA` clash at `r`, and its
two clauses `atR'` and `bandB` clash at `r'`: no sequence whatever satisfies it
(`not_cutData`), so the commissioned `exists_cutData` is false wherever its hypotheses can be
met (`not_exists_cutData_cutSeq`), `cutData_spans` is vacuously true, and — the reason the route
as commissioned cannot be run — `cutWalk` is provable outright by vacuity (`cutWalk`), while
`s3ZigFreeInterior_of_cutWalk` is *equivalent* to the goal it was meant to reduce
(`s3ZigFreeInterior_iff_cutWalk_imp`). The clash is not a typo in one clause: the cut of batch 26
reaches `H − 2` at `r`, not `H − 1`, and *falls to* `L + 1` at `r'`, which is exactly why the
stretch `[r, r']` cannot also be banded from below at `r'` itself.

**The corrected cut is `CutData'`**, which is what `crookedIvF_cut_first` actually proves
(`exists_cutData'`, `cutData'_spans`): the first stretch `[a, r]` is banded above by `H − 2`, the
second `[r, r')` below by `L + 2`.

**But each stretch is narrower on one side only, and that is not enough.** The commission's
premise — that the cut's bands are "two narrower than the ambient, which is exactly what
`isZigFree_append_outer'` requires" — is wrong: `isZigFree_append_outer'` requires the band to be
strictly inside `[L, H]` at *both* ends, and the first stretch contains `a`, where the level is
`L` exactly. So batch 34's obstruction applies to it verbatim: no member of the family of the
first stretch's band extends, by the two outer legs, to a member of the family of `[L, H]`
(`cut_stretchA_no_extension`, from `no_outer_member_of_boundary_trim`). The cut route therefore
inherits the defect that closed the trim route, at the bottom end of its first stretch and at
the top end of its second whenever that stretch reaches `H`.

What is delivered besides the refutations: the reversal symmetry of the whole setting
(`isCrookedIvF_revSeq`, `s3ZigFreeInterior_arms_rev`), which the cut needs because it demands a
bottom index *before* a top one; the corrected statement `CutWalk'` with the reduction
`s3ZigFreeInterior_of_cutWalk'` — and, honestly, the equivalence `cutWalk'_iff_s3ZigFreeInterior`:
since the cut always exists, the corrected route adds data to work with, not strength to the
statement. `cutWalk'` itself is neither proved nor refuted and is kept, commented out, at the end.

**The census does not support a walk built from the cut.** Over `bing 0 n`, `n = 6 … 12`, with
the enclosing cut at each interior basepoint and the core of the cut stretch containing it — the
maximal subinterval avoiding both extreme levels, so that the append lemma applies, and it always
does: 0 of the serving members had an oriented extension outside the family of `[L, H]` — some
member of the core's family folds both core arms at *every* interior basepoint, but the extension
by the two outer legs folds both whole arms for *some* such member at only 24 of 25 basepoints at
span six and 12 239 of 13 635 at span twelve, and for *every* such member at 13 of 25 and 9 657
of 13 635. So the cut's own stretch is a worse trim than batch 34's, which passed the weak form
everywhere; no construction suggests itself from it.

The census is `census-batch35.c` with its output in `census-batch35.log`; the report is
REPORT-batch35.md.

English proofs: COMMISSION-batch35.md §2–§3, and REPORT-batch35.md.
-/

namespace HPC.Fold

/-! ## The commissioned cut data, and why it is empty -/

/-- The data the cut supplies, as commissioned: between an index at the bottom and a later one
at the top, the sequence comes within one of the top at `r` and then within one of the bottom at
`r'`, with both crossings taken as early as possible. **This structure is empty**
(`not_cutData`); `CutData'` is the corrected form. -/
structure CutData {n : ℕ} (ρ : Fin n → ℤ) (L H : ℤ) (a r r' b : ℕ) : Prop where
  order : a < r ∧ r < r' ∧ r' < b ∧ b < n
  bot : ∀ j : Fin n, j.val = a → ρ j = L
  top : ∀ j : Fin n, j.val = b → ρ j = H
  atR : ∀ j : Fin n, j.val = r → H - 1 ≤ ρ j
  atR' : ∀ j : Fin n, j.val = r' → ρ j ≤ L + 1
  bandA : ∀ j : Fin n, a ≤ j.val → j.val ≤ r → ρ j ≤ H - 2
  bandB : ∀ j : Fin n, r ≤ j.val → j.val ≤ r' → L + 2 ≤ ρ j

/-- **The clash at `r`.** `atR` puts the level at `r` at least `H − 1`; `bandA`, which covers its
own right endpoint, puts it at most `H − 2`. -/
theorem cutData_top_clash {n : ℕ} {ρ : Fin n → ℤ} {L H : ℤ} {a r r' b : ℕ}
    (h : CutData ρ L H a r r' b) : False := by
  obtain ⟨har, hrr', hr'b, hbn⟩ := h.order
  have hrn : r < n := by omega
  have h1 := h.atR ⟨r, hrn⟩ rfl
  have h2 := h.bandA ⟨r, hrn⟩ (by simp; omega) (by simp)
  omega

/-- **The clash at `r'`.** `atR'` puts the level at `r'` at most `L + 1`; `bandB`, which covers
its own right endpoint, puts it at least `L + 2`. -/
theorem cutData_bot_clash {n : ℕ} {ρ : Fin n → ℤ} {L H : ℤ} {a r r' b : ℕ}
    (h : CutData ρ L H a r r' b) : False := by
  obtain ⟨har, hrr', hr'b, hbn⟩ := h.order
  have hr'n : r' < n := by omega
  have h1 := h.atR' ⟨r', hr'n⟩ rfl
  have h2 := h.bandB ⟨r', hr'n⟩ (by simp; omega) (by simp)
  omega

/-- **The commissioned cut data is empty**, for every sequence, every band and every choice of
the four indices. -/
theorem not_cutData {n : ℕ} {ρ : Fin n → ℤ} {L H : ℤ} {a r r' b : ℕ} :
    ¬ CutData ρ L H a r r' b :=
  fun h => cutData_top_clash h

-- Commented-out statement `exists_cutData` removed in batch 103; see `LEDGER.md`.

/-- `cutSeq` meets every hypothesis of the commissioned `exists_cutData` at `L = 3`, `H = 7`,
`a = 0`, `b = 12`. -/
theorem cutSeq_cutData_hypotheses :
    IsCrookedIvF cutSeq cutSeq ∧ (∀ t, (3 : ℤ) ≤ cutSeq t) ∧ (∀ t, cutSeq t ≤ 7) ∧
      (3 : ℤ) + 3 ≤ 7 ∧ (0 : ℕ) < 12 ∧ (12 : ℕ) < 37 ∧
      (∀ j : Fin 37, j.val = 0 → cutSeq j = 3) ∧ (∀ j : Fin 37, j.val = 12 → cutSeq j = 7) :=
  ⟨cutSeq_faithful, cutSeq_bounds.1, cutSeq_bounds.2, by norm_num, by norm_num, by norm_num,
    by decide, by decide⟩

/-- **The refutation of `exists_cutData`.** Under hypotheses that are met, the conclusion
fails. -/
theorem not_exists_cutData_cutSeq : ¬ ∃ r r', CutData cutSeq 3 7 0 r r' 12 := by
  rintro ⟨r, r', h⟩
  exact not_cutData h

/-- **`cutData_spans`, as commissioned.** True, but vacuously: its hypothesis is empty. -/
theorem cutData_spans {n : ℕ} {ρ : Fin n → ℤ} {L H : ℤ} {a r r' b : ℕ}
    (h : CutData ρ L H a r r' b) :
    (∀ j : Fin n, a ≤ j.val → j.val ≤ r → L ≤ ρ j ∧ ρ j ≤ H - 2) ∧
    (∀ j : Fin n, r ≤ j.val → j.val ≤ r' → L + 2 ≤ ρ j ∧ ρ j ≤ H) :=
  absurd h not_cutData

/-! ### `CutWalk` is provable, and proves nothing -/

/-- **`CutWalk`**, as commissioned: from the cut, a walk for the whole basepoint. Since the cut
data it quantifies over is empty, the statement is vacuously true. -/
def CutWalk : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) → L + 3 ≤ ρ i → ρ i ≤ H - 3 →
    ∀ (a r r' b : ℕ), CutData ρ L H a r r' b →
    ∃ ts : List ℤ, IsZigFree L H ts ∧
      FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2

/-- **`CutWalk` holds, by vacuity.** -/
theorem cutWalk : CutWalk := by
  intro n ρ σ i H L _ _ _ _ _ _ _ _ a r r' b hcd
  exact absurd hcd not_cutData

-- Commented-out statement `s3ZigFreeInterior_of_cutWalk` removed in batch 103; see `LEDGER.md`.
theorem s3ZigFreeInterior_iff_cutWalk_imp :
    (CutWalk → S3ZigFreeInterior) ↔ S3ZigFreeInterior :=
  ⟨fun h => h cutWalk, fun h _ => h⟩

/-! ## The corrected cut -/

/-- **The cut, as `crookedIvF_cut_first` actually gives it.** Between an index `a` at the bottom
and a later index `b` at the top, the sequence first reaches the top band at `r`, where its level
is exactly `H − 2`, and then first falls to the bottom band at `r'`, where its level is at most
`L + 1`; before `r` it stays at or below `H − 2`, and strictly between `r` and `r'` it stays at
or above `L + 2`. -/
structure CutData' {n : ℕ} (ρ : Fin n → ℤ) (L H : ℤ) (a r r' b : ℕ) : Prop where
  order : a < r ∧ r < r' ∧ r' < b ∧ b < n
  bot : ∀ j : Fin n, j.val = a → ρ j = L
  top : ∀ j : Fin n, j.val = b → ρ j = H
  atR : ∀ j : Fin n, j.val = r → ρ j = H - 2
  atR' : ∀ j : Fin n, j.val = r' → ρ j ≤ L + 1
  bandA : ∀ j : Fin n, a < j.val → j.val ≤ r → ρ j ≤ H - 2
  bandB : ∀ j : Fin n, r < j.val → j.val < r' → L + 2 ≤ ρ j

/-- **The cut exists**, in the corrected form: the repackaging of `crookedIvF_cut_first`. The
commission's `a` and `b` must be an index at the bottom and a *later* index at the top, which is
what that lemma needs; the ambient bounds `hLb`, `hHb` are not needed. -/
theorem exists_cutData' {n : ℕ} {ρ σ : Fin n → ℤ} {L H : ℤ} (hf : IsCrookedIvF ρ σ)
    {a b : Fin n} (hab : a < b) (ha : ρ a = L) (hb : ρ b = H) (hLH : L + 3 ≤ H) :
    ∃ r r' : ℕ, CutData' ρ L H a.val r r' b.val := by
  obtain ⟨R, R', haR, hRR', hR'b, hRval, hR'val, hbelow, habove⟩ :=
    crookedIvF_cut_first hf hf.isLip hab ha hb hLH
  refine ⟨R.val, R'.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨haR, hRR', hR'b, b.isLt⟩
  · intro j hj
    rw [show j = a from Fin.ext hj]; exact ha
  · intro j hj
    rw [show j = b from Fin.ext hj]; exact hb
  · intro j hj
    rw [show j = R from Fin.ext hj]; exact hRval
  · intro j hj
    rw [show j = R' from Fin.ext hj]; exact hR'val
  · intro j h1 h2
    rcases eq_or_lt_of_le h2 with he | hlt
    · rw [show j = R from Fin.ext he]; omega
    · exact le_trans (hbelow j h1 hlt) (by omega)
  · intro j h1 h2
    exact habove j h1 h2

/-- **The two stretches of the cut, with their bands.** The first runs in `[L, H − 2]`, the
second — up to but not including its right endpoint — in `[L + 1, H]`, and strictly inside its
two endpoints in `[L + 2, H]`. The third stretch is the one batch 27 showed cannot be banded in
general; it is not claimed. -/
theorem cutData'_spans {n : ℕ} {ρ : Fin n → ℤ} {L H : ℤ} {a r r' b : ℕ}
    (h : CutData' ρ L H a r r' b) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H) :
    (∀ j : Fin n, a ≤ j.val → j.val ≤ r → L ≤ ρ j ∧ ρ j ≤ H - 2) ∧
    (∀ j : Fin n, r ≤ j.val → j.val < r' → L + 1 ≤ ρ j ∧ ρ j ≤ H) := by
  refine ⟨?_, ?_⟩
  · intro j h1 h2
    refine ⟨hLb j, ?_⟩
    rcases eq_or_lt_of_le h1 with he | hlt
    · rw [h.bot j he.symm]; omega
    · exact h.bandA j hlt h2
  · intro j h1 h2
    refine ⟨?_, hHb j⟩
    rcases eq_or_lt_of_le h1 with he | hlt
    · rw [h.atR j he.symm]; omega
    · exact le_trans (by omega) (h.bandB j hlt h2)

/-! ## The obstruction the cut inherits

The commission's premise is that the cut's two bands are "two narrower than the ambient, which
is exactly what `isZigFree_append_outer'` requires". They are not: that lemma requires the inner
band to be strictly inside `[L, H]` at *both* ends, and each of the cut's stretches is narrower
at one end only. The first stretch contains `a`, whose level is `L` exactly. -/

/-- **A trim that touches either extreme level is useless.** Batch 34's
`zigFree_append_forces_inner`, in the form the cut needs: if the inner band reaches down to `L`
or up to `H`, no member of its family becomes a member of the family of `[L, H]` when the two
outer legs are appended. -/
theorem no_outer_member_of_boundary_trim {L H L' H' x y : ℤ} {ts : List ℤ}
    (h : IsZigFree L' H' ts) (h3 : L' + 3 ≤ H')
    (hxy : (x, y) = (L + 1, H - 1) ∨ (x, y) = (H - 1, L + 1))
    (hbd : L' ≤ L ∨ H ≤ H') :
    ¬ IsZigFree L H (ts ++ [x, y]) := by
  intro hA
  obtain ⟨h1, h2⟩ := zigFree_append_forces_inner h h3 hxy hA
  omega

/-- **The cut's first stretch cannot be appended to.** Its band attains `L` at `a`, so however
its family's members fold the stretch's arms, their extensions by the two outer legs are not
members of the family of `[L, H]` — the conclusion of `S3ZigFreeInterior` asks for a member of
that family, so the cut route, taken stretch-first, is closed at exactly the place the trim
route was. -/
theorem cut_stretchA_no_extension {L H H' x y : ℤ} {ts : List ℤ}
    (h : IsZigFree L H' ts) (h3 : L + 3 ≤ H')
    (hxy : (x, y) = (L + 1, H - 1) ∨ (x, y) = (H - 1, L + 1)) :
    ¬ IsZigFree L H (ts ++ [x, y]) :=
  no_outer_member_of_boundary_trim h h3 hxy (Or.inl le_rfl)

/-! ## Reversal symmetry

The cut needs a bottom index *before* a top one; a sequence may present them in either order, so
the reduction needs the setting's invariance under reversing the sequence and the basepoint
together. -/

/-- **Faithful crookedness is reversal-invariant.** -/
theorem isCrookedIvF_revSeq {n : ℕ} {ρ σ : Fin n → ℤ} (h : IsCrookedIvF ρ σ) :
    IsCrookedIvF (revSeq ρ) (revSeq σ) := by
  refine ⟨fun t => h.le _, fun t => h.width _, ?_, ?_⟩
  · intro t t' htt'
    have ht := t.isLt
    have ht' := t'.isLt
    have hA : (⟨n - 1 - t'.val, by omega⟩ : Fin n).val + 1 = (⟨n - 1 - t.val, by omega⟩ : Fin n).val
        := by simp only; omega
    have := h.adj ⟨n - 1 - t'.val, by omega⟩ ⟨n - 1 - t.val, by omega⟩ hA.symm
    show max (σ ⟨n - 1 - t.val, _⟩) (σ ⟨n - 1 - t'.val, _⟩) ≤
      min (ρ ⟨n - 1 - t.val, _⟩) (ρ ⟨n - 1 - t'.val, _⟩) + 1
    rw [max_comm, min_comm]
    exact this
  · rintro s t hst hh kk ⟨u, hu, hu1, hu2⟩ ⟨v, hv, hv1, hv2⟩ habs
    have hs := s.isLt
    have ht := t.isLt
    have hstv : s.val < t.val := hst
    have hu' := u.isLt
    have hv' := v.isLt
    have hST : (⟨n - 1 - t.val, by omega⟩ : Fin n) < ⟨n - 1 - s.val, by omega⟩ := by
      simp only [Fin.lt_def]; omega
    -- the two witnesses, transported
    have hU : ((((⟨n - 1 - u.val, by omega⟩ : Fin n) : ℤ)) -
        ((⟨n - 1 - s.val, by omega⟩ : Fin n) : ℤ)).natAbs ≤ 1 := by
      have h0 : ((u : ℤ) - s.val).natAbs ≤ 1 := hu
      show (((n - 1 - u.val : ℕ) : ℤ) - ((n - 1 - s.val : ℕ) : ℤ)).natAbs ≤ 1
      omega
    have hV : ((((⟨n - 1 - v.val, by omega⟩ : Fin n) : ℤ)) -
        ((⟨n - 1 - t.val, by omega⟩ : Fin n) : ℤ)).natAbs ≤ 1 := by
      have h0 : ((v : ℤ) - t.val).natAbs ≤ 1 := hv
      show (((n - 1 - v.val : ℕ) : ℤ) - ((n - 1 - t.val : ℕ) : ℤ)).natAbs ≤ 1
      omega
    obtain ⟨r, r', h1, h2, h3, hlt1, hlt2⟩ :=
      h.crooked ⟨n - 1 - t.val, by omega⟩ ⟨n - 1 - s.val, by omega⟩ hST kk hh
        ⟨⟨n - 1 - v.val, by omega⟩, hV, hv1, hv2⟩ ⟨⟨n - 1 - u.val, by omega⟩, hU, hu1, hu2⟩
        (by rw [abs_sub_comm]; exact habs)
    have h1v : n - 1 - t.val < r.val := h1
    have h2v : r.val < r'.val := h2
    have h3v : r'.val < n - 1 - s.val := h3
    have hr := r.isLt
    have hr' := r'.isLt
    refine ⟨⟨n - 1 - r'.val, by omega⟩, ⟨n - 1 - r.val, by omega⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Fin.lt_def]; omega
    · simp only [Fin.lt_def]; omega
    · simp only [Fin.lt_def]; omega
    · intro hlt
      obtain ⟨e1, e2⟩ := hlt2 hlt
      have eρ1 : revSeq ρ (⟨n - 1 - r'.val, by omega⟩ : Fin n) = ρ r' :=
        congrArg ρ (Fin.ext (by simp only; omega))
      have eσ1 : revSeq σ (⟨n - 1 - r'.val, by omega⟩ : Fin n) = σ r' :=
        congrArg σ (Fin.ext (by simp only; omega))
      have eρ2 : revSeq ρ (⟨n - 1 - r.val, by omega⟩ : Fin n) = ρ r :=
        congrArg ρ (Fin.ext (by simp only; omega))
      have eσ2 : revSeq σ (⟨n - 1 - r.val, by omega⟩ : Fin n) = σ r :=
        congrArg σ (Fin.ext (by simp only; omega))
      rw [eρ1, eσ1, eρ2, eσ2]
      exact ⟨e2, e1⟩
    · intro hlt
      obtain ⟨e1, e2⟩ := hlt1 hlt
      have eρ1 : revSeq ρ (⟨n - 1 - r'.val, by omega⟩ : Fin n) = ρ r' :=
        congrArg ρ (Fin.ext (by simp only; omega))
      have eσ1 : revSeq σ (⟨n - 1 - r'.val, by omega⟩ : Fin n) = σ r' :=
        congrArg σ (Fin.ext (by simp only; omega))
      have eρ2 : revSeq ρ (⟨n - 1 - r.val, by omega⟩ : Fin n) = ρ r :=
        congrArg ρ (Fin.ext (by simp only; omega))
      have eσ2 : revSeq σ (⟨n - 1 - r.val, by omega⟩ : Fin n) = σ r :=
        congrArg σ (Fin.ext (by simp only; omega))
      rw [eρ1, eσ1, eρ2, eσ2]
      exact ⟨e2, e1⟩

/-- **The conclusion of `S3ZigFreeInterior` is reversal-invariant.** A walk serving both arms at
the reversed basepoint of the reversed sequence serves both arms at the original one. -/
theorem s3ZigFreeInterior_arms_rev {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) {ts : List ℤ}
    (hG : FoldsOnto (armG (revSeq ρ) (revIdx i)) (zigWalk ts).1 (zigWalk ts).2)
    (hT : FoldsOnto (armT (revSeq ρ) (revIdx i)) (zigWalk ts).1 (zigWalk ts).2) :
    FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2 := by
  have hi := i.isLt
  have hlen : n - (revIdx i).val = i.val + 1 := by simp only [revIdx]; omega
  have hlen' : (revIdx i).val + 1 = n - i.val := by simp only [revIdx]; omega
  refine ⟨?_, ?_⟩
  · refine foldsOnto_congr (m := (revIdx i).val + 1) (m' := n - i.val) hlen'.symm ?_ hT
    intro j
    exact (armT_revSeq_apply ρ i j.val (by omega) j.isLt).symm
  · refine foldsOnto_congr (m := n - (revIdx i).val) (m' := i.val + 1) hlen.symm ?_ hG
    intro j
    exact (armG_revSeq_apply ρ i j.val (by omega) j.isLt).symm

/-! ## The corrected statement of the route -/

/-- **`CutWalk'`.** The commissioned `CutWalk` with the corrected cut data: at an interior
basepoint, and given a cut, a member of the free family of `[L, H]` that folds both whole arms.
Unlike `CutWalk` this is not vacuous — the cut exists (`exists_cutData'`) — and by
`s3ZigFreeInterior_of_cutWalk'` it implies the interior case. -/
def CutWalk' : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) → L + 3 ≤ ρ i → ρ i ≤ H - 3 →
    ∀ (a r r' b : ℕ), CutData' ρ L H a r r' b →
    ∃ ts : List ℤ, IsZigFree L H ts ∧
      FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2

/-- **What the route does buy.** With the cut in hand the interior case follows: the bottom and
top levels are attained somewhere, and if the top comes first the reversed sequence presents them
in the order the cut needs. -/
theorem s3ZigFreeInterior_of_cutWalk' (h : CutWalk') : S3ZigFreeInterior := by
  intro n ρ σ i H L hcr hLb hHb hLH heL heH hlo hhi
  obtain ⟨tL, htL⟩ := heL
  obtain ⟨tH, htH⟩ := heH
  rcases lt_trichotomy tL tH with hlt | heq | hgt
  · obtain ⟨r, r', hcd⟩ := exists_cutData' hcr hlt htL htH hLH
    exact h n ρ σ i H L hcr hLb hHb hLH ⟨tL, htL⟩ ⟨tH, htH⟩ hlo hhi _ r r' _ hcd
  · exact absurd (htL.symm.trans (heq ▸ htH)) (by omega)
  · -- the top comes first: reverse
    have hcr' : IsCrookedIvF (revSeq ρ) (revSeq σ) := isCrookedIvF_revSeq hcr
    have hLb' : ∀ t, L ≤ revSeq ρ t := fun t => hLb _
    have hHb' : ∀ t, revSeq ρ t ≤ H := fun t => hHb _
    have hvL : revSeq ρ (revIdx tL) = L := by rw [revSeq_revIdx]; exact htL
    have hvH : revSeq ρ (revIdx tH) = H := by rw [revSeq_revIdx]; exact htH
    have hvi : revSeq ρ (revIdx i) = ρ i := revSeq_revIdx ρ i
    have hab : revIdx tL < revIdx tH := by
      have h1 := tL.isLt
      have h2 := tH.isLt
      have : tH.val < tL.val := hgt
      simp only [revIdx, Fin.lt_def]
      omega
    obtain ⟨r, r', hcd⟩ := exists_cutData' hcr' hab hvL hvH hLH
    obtain ⟨ts, hzf, hG, hT⟩ :=
      h n (revSeq ρ) (revSeq σ) (revIdx i) H L hcr' hLb' hHb' hLH ⟨revIdx tL, hvL⟩
        ⟨revIdx tH, hvH⟩ (by rw [hvi]; exact hlo) (by rw [hvi]; exact hhi) _ r r' _ hcd
    obtain ⟨hG', hT'⟩ := s3ZigFreeInterior_arms_rev ρ i hG hT
    exact ⟨ts, hzf, hG', hT'⟩

/-- **And what it does not buy.** `CutWalk'` is *equivalent* to the interior case: its
conclusion is that of `S3ZigFreeInterior` and its extra hypothesis, the cut, always holds. So the
route adds data to work with, not strength to the statement — which is the honest reading of
what a route through the cut can be. -/
theorem cutWalk'_iff_s3ZigFreeInterior : CutWalk' ↔ S3ZigFreeInterior := by
  refine ⟨s3ZigFreeInterior_of_cutWalk', fun h n ρ σ i H L hcr hLb hHb hLH heL heH hlo hhi
    _ _ _ _ _ => h n ρ σ i H L hcr hLb hHb hLH heL heH hlo hhi⟩

-- Commented-out statement `cutWalk'` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
