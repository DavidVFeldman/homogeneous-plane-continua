import HPC.Fold.ZigFree

/-!
# Bing 1948, Theorem 7: minimality, and the timing bound it gives

Batch 29 closed every basepoint within two of an extreme and proved the range sharp: the
straight descent `6,5,4,3,2,1,0` based at its middle admits no walk of unit steps at all
(`no_zigWalk_fold_veeSeq`), so the interior cases cannot be settled without crookedness. What
that sequence lacks is length: it crosses six levels in six indices, while a token that starts
at time zero and moves one level per step cannot be near both extremes at times so close
together.

Crookedness forbids exactly that. Bing's Theorem 7 says a chain crooked in a chain of `n` links
has at least `z(n)` links, where `z 0 = 1`, `z 1 = 2`, `z 2 = 3` and
`z (n+3) = 2 · z (n+2) + z (n+1) − 2`. The repository has the construction and its length
(`bingPath`, `bingPath_length`, batch 24); the lower bound — the content of Theorem 7 — is
proved here, as `minimality`, and it supplies the token's timing budget.

The engine is `minGap`: if some link of a faithful crooked sequence meets coarse level `ℓ` and
another meets `ℓ + d`, then the sequence has at least `z d` links. Its proof is Bing's own
recursion read backwards. The crookedness clause at the pair of those two links produces two
intermediate links, one meeting `ℓ + d − 1` and, after it, one meeting `ℓ + 1`; the three
contiguous stretches they cut the sequence into meet pairs of levels `d − 1`, `d − 2`, `d − 1`
apart, each stretch is again faithful and crooked (`isCrookedIvF_restrict`), and the three
lengths overlap in exactly two links, so induction gives
`2 · z (d−1) + z (d−2) − 2 = z d` links. Measuring the gap with the *intervals* `[ρ, σ]`, not
with `ρ` alone, is what makes the three pieces come out one short of the whole rather than two.

Checked in `census-batch30.c`: the shortest faithful crooked sequence is exhaustively 2, 3, 6,
13 links at spans 1, 2, 3, 4, against `z 1 = 2`, `z 2 = 3`, `z 3 = 6`, `z 4 = 13`; on
`bingPath 0 n` for `n = 3 … 8` and random contiguous subchains, every pair of indices at level
distance `d ≥ 3` is at least `z d − 1` apart, and every contiguous stretch is faithful and
crooked.

English proofs: COMMISSION-batch30.md §2–§3. Delivered complete: no `sorry` remains.
-/

namespace HPC.Fold

/-! ## The recurrence -/

/-- Bing's recurrence is monotone: one step. -/
theorem z_le_succ : ∀ m : ℕ, z m ≤ z (m + 1)
  | 0 => by decide
  | 1 => by decide
  | m + 2 => by
      have h1 := z_pos (m + 1)
      have h2 := z_pos (m + 2)
      have he : z (m + 3) = 2 * z (m + 2) + z (m + 1) - 2 := rfl
      show z (m + 2) ≤ z (m + 3)
      omega

/-- `z` is monotone. -/
theorem z_ge_of_le {a b : ℕ} (h : a ≤ b) : z a ≤ z b := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact ih.trans (z_le_succ b)

private theorem z_gt_linear_aux : ∀ m : ℕ, 2 * (m + 3) ≤ z (m + 3) ∧ 2 * (m + 4) ≤ z (m + 4)
  | 0 => ⟨by decide, by decide⟩
  | m + 1 => by
      obtain ⟨h1, h2⟩ := z_gt_linear_aux m
      refine ⟨h2, ?_⟩
      have hp := z_pos (m + 3)
      have he : z (m + 5) = 2 * z (m + 4) + z (m + 3) - 2 := rfl
      show 2 * (m + 5) ≤ z (m + 5)
      omega

/-- `z` outgrows the linear bound the walk budget needs. -/
theorem z_gt_linear (d : ℕ) (h : 3 ≤ d) : 2 * d ≤ z d := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
  exact (z_gt_linear_aux m).1

/-! ## Restriction -/

/-- A contiguous stretch of a faithful crooked sequence is faithful and crooked. Needed to
apply `Minimality` to a sub-stretch, and not previously in the repository. -/
theorem isCrookedIvF_restrict {n : ℕ} {ρ σ : Fin n → ℤ} (h : IsCrookedIvF ρ σ)
    (a b : ℕ) (hab : a ≤ b) (hb : b < n) :
    IsCrookedIvF (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩)
                 (fun j : Fin (b - a + 1) => σ ⟨a + j.val, by omega⟩) := by
  refine ⟨fun t => h.le _, fun t => h.width _, ?_, ?_⟩
  · intro t t' htt'
    exact h.adj _ _ (by show a + t'.val = a + t.val + 1; omega)
  · rintro s t hst hh kk ⟨u, hu, hu1, hu2⟩ ⟨v, hv, hv1, hv2⟩ habs
    have hsb : s.val ≤ b - a := by omega
    have htb : t.val ≤ b - a := by omega
    have hstv : s.val < t.val := hst
    -- transport the data to the ambient sequence
    have hS : (⟨a + s.val, by omega⟩ : Fin n) < ⟨a + t.val, by omega⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    have hU : (((⟨a + u.val, by omega⟩ : Fin n) : ℤ) - ((⟨a + s.val, by omega⟩ : Fin n) : ℤ)).natAbs
        ≤ 1 := by
      simpa using (by simpa using hu : ((u : ℤ) - (s : ℤ)).natAbs ≤ 1)
    have hV : (((⟨a + v.val, by omega⟩ : Fin n) : ℤ) - ((⟨a + t.val, by omega⟩ : Fin n) : ℤ)).natAbs
        ≤ 1 := by
      simpa using (by simpa using hv : ((v : ℤ) - (t : ℤ)).natAbs ≤ 1)
    obtain ⟨R, R', h1, h2, h3, hup, hdn⟩ :=
      h.crooked ⟨a + s.val, by omega⟩ ⟨a + t.val, by omega⟩ hS hh kk
        ⟨⟨a + u.val, by omega⟩, hU, hu1, hu2⟩ ⟨⟨a + v.val, by omega⟩, hV, hv1, hv2⟩ habs
    have hR1 : a + s.val < R.val := h1
    have hR2 : R.val < R'.val := h2
    have hR3 : R'.val < a + t.val := h3
    refine ⟨⟨R.val - a, by omega⟩, ⟨R'.val - a, by omega⟩, by simp [Fin.lt_def]; omega,
      by simp [Fin.lt_def]; omega, by simp [Fin.lt_def]; omega, ?_, ?_⟩
    · have hRe : (⟨a + (R.val - a), by omega⟩ : Fin n) = R := Fin.ext (by simp; omega)
      have hRe' : (⟨a + (R'.val - a), by omega⟩ : Fin n) = R' := Fin.ext (by simp; omega)
      simpa [hRe, hRe'] using hup
    · have hRe : (⟨a + (R.val - a), by omega⟩ : Fin n) = R := Fin.ext (by simp; omega)
      have hRe' : (⟨a + (R'.val - a), by omega⟩ : Fin n) = R' := Fin.ext (by simp; omega)
      simpa [hRe, hRe'] using hdn

/-- The adjacency clause of the faithful model already forces `ρ` to be 1-Lipschitz. -/
theorem IsCrookedIvF.isLip {n : ℕ} {ρ σ : Fin n → ℤ} (h : IsCrookedIvF ρ σ) : IsLip ρ := by
  intro j j' hj
  have hadj := h.adj j j' hj
  rw [max_le_iff] at hadj
  have := h.le j
  have := h.le j'
  rw [abs_le]
  omega

/-! ## Theorem 7 -/

/-- **Bing 1948, Theorem 7**, the lower bound, in the faithful sequence model: a faithful
crooked sequence of span `d` has at least `z d` terms. -/
def Minimality : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (L H : ℤ), IsLip ρ → IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    z (H - L).toNat ≤ n

/-- **The engine of Theorem 7.** If one link of a faithful crooked sequence meets level `ℓ`
and another, distinct, link meets level `ℓ + d`, the sequence has at least `z d` links.

Levels are met by the *interval* `[ρ, σ]` of a link, not by `ρ` alone: that is what makes the
three pieces of the induction lose only two links between them. -/
theorem minGap : ∀ (d : ℕ) {n : ℕ} {ρ σ : Fin n → ℤ}, IsCrookedIvF ρ σ →
    ∀ (p q : Fin n) (l : ℤ), ρ p ≤ l → l ≤ σ p → ρ q ≤ l + d → l + d ≤ σ q → p ≠ q →
    z d ≤ n := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro n ρ σ hf p q l hp1 hp2 hq1 hq2 hpq
    have hne : p.val ≠ q.val := fun hc => hpq (Fin.ext hc)
    -- the three small spans
    match d, ih with
    | 0, _ =>
        have : z 0 = 1 := rfl
        omega
    | 1, _ =>
        have : z 1 = 2 := rfl
        have := p.isLt
        have := q.isLt
        omega
    | 2, _ =>
        have hz : z 2 = 3 := rfl
        have hfar : 2 ≤ ((q : ℤ) - (p : ℤ)).natAbs := by
          by_contra hc
          have hnear := hf.near (t := p) (u := q) (by omega)
          push_cast at hp1 hp2 hq1 hq2
          omega
        have := p.isLt
        have := q.isLt
        omega
    | (m + 3), ih =>
        have hzrec : z (m + 3) = 2 * z (m + 2) + z (m + 1) - 2 := rfl
        have hz1 := z_pos (m + 1)
        have hz2 := z_pos (m + 2)
        -- a stretch between two links meeting levels `e` apart has at least `z e` links,
        -- in whichever index order the low and the high link come
        have piece : ∀ (a b : Fin n) (e : ℕ) (x : ℤ), a < b → e < m + 3 →
            ((ρ a ≤ x ∧ x ≤ σ a ∧ ρ b ≤ x + e ∧ x + e ≤ σ b) ∨
              (ρ b ≤ x ∧ x ≤ σ b ∧ ρ a ≤ x + e ∧ x + e ≤ σ a)) →
            z e ≤ b.val - a.val + 1 := by
          intro a b e x hab he hcov
          have hle : a.val ≤ b.val := le_of_lt hab
          have hbn : b.val < n := b.isLt
          have hrestr := isCrookedIvF_restrict hf a.val b.val hle hbn
          have h0 : (⟨a.val + (0 : ℕ), by omega⟩ : Fin n) = a := Fin.ext (by simp)
          have h1 : (⟨a.val + (b.val - a.val), by omega⟩ : Fin n) = b := Fin.ext (by simp; omega)
          have hne0 : (⟨0, by omega⟩ : Fin (b.val - a.val + 1)) ≠ ⟨b.val - a.val, by omega⟩ := by
            intro hc
            have := congrArg Fin.val hc
            simp at this
            omega
          rcases hcov with ⟨ha1, ha2, hb1, hb2⟩ | ⟨hb1, hb2, ha1, ha2⟩
          · refine ih e he hrestr ⟨0, by omega⟩ ⟨b.val - a.val, by omega⟩ x ?_ ?_ ?_ ?_ hne0
            · simpa [h0] using ha1
            · simpa [h0] using ha2
            · simpa [h1] using hb1
            · simpa [h1] using hb2
          · refine ih e he hrestr ⟨b.val - a.val, by omega⟩ ⟨0, by omega⟩ x ?_ ?_ ?_ ?_
              (Ne.symm hne0)
            · simpa [h1] using hb1
            · simpa [h1] using hb2
            · simpa [h0] using ha1
            · simpa [h0] using ha2
        -- the cut, in whichever index order the two links come
        have main : ∀ (P Q : Fin n) (x : ℤ), P < Q →
            ((ρ P ≤ x ∧ x ≤ σ P ∧ ρ Q ≤ x + (m + 3) ∧ x + (m + 3) ≤ σ Q) ∨
              (ρ Q ≤ x ∧ x ≤ σ Q ∧ ρ P ≤ x + (m + 3) ∧ x + (m + 3) ≤ σ P)) →
            z (m + 3) ≤ n := by
          intro P Q x hPQ hcov
          have hQn : Q.val < n := Q.isLt
          rcases hcov with ⟨hP1, hP2, hQ1, hQ2⟩ | ⟨hQ1, hQ2, hP1, hP2⟩
          · -- `P` is the low link
            obtain ⟨r, r', hr1, hr2, hr3, hup, -⟩ :=
              hf.crooked P Q hPQ x (x + (m + 3)) ⟨P, by simp, hP1, hP2⟩ ⟨Q, by simp, hQ1, hQ2⟩
                (by rw [abs_sub_comm, abs_of_nonneg (by omega)]; omega)
            obtain ⟨⟨hra, hrb⟩, hr'a, hr'b⟩ := hup (by omega)
            have e1 : z (m + 2) ≤ r.val - P.val + 1 :=
              piece P r (m + 2) x hr1 (by omega)
                (Or.inl ⟨hP1, hP2, by push_cast; omega, by push_cast; omega⟩)
            have e2 : z (m + 1) ≤ r'.val - r.val + 1 :=
              piece r r' (m + 1) (x + 1) hr2 (by omega)
                (Or.inr ⟨by omega, by omega,
                  by push_cast; omega, by push_cast; omega⟩)
            have e3 : z (m + 2) ≤ Q.val - r'.val + 1 :=
              piece r' Q (m + 2) (x + 1) hr3 (by omega)
                (Or.inl ⟨by omega, by omega,
                  by push_cast at hQ1 ⊢; omega, by push_cast at hQ2 ⊢; omega⟩)
            have o1 : P.val < r.val := hr1
            have o2 : r.val < r'.val := hr2
            have o3 : r'.val < Q.val := hr3
            omega
          · -- `P` is the high link
            obtain ⟨r, r', hr1, hr2, hr3, -, hdn⟩ :=
              hf.crooked P Q hPQ (x + (m + 3)) x ⟨P, by simp, hP1, hP2⟩ ⟨Q, by simp, hQ1, hQ2⟩
                (by rw [abs_of_nonneg (by omega)]; omega)
            obtain ⟨⟨hra, hrb⟩, hr'a, hr'b⟩ := hdn (by omega)
            have e1 : z (m + 2) ≤ r.val - P.val + 1 :=
              piece P r (m + 2) (x + 1) hr1 (by omega)
                (Or.inr ⟨by omega, by omega,
                  by push_cast at hP1 ⊢; omega, by push_cast at hP2 ⊢; omega⟩)
            have e2 : z (m + 1) ≤ r'.val - r.val + 1 :=
              piece r r' (m + 1) (x + 1) hr2 (by omega)
                (Or.inl ⟨by omega, by omega,
                  by push_cast; omega, by push_cast; omega⟩)
            have e3 : z (m + 2) ≤ Q.val - r'.val + 1 :=
              piece r' Q (m + 2) x hr3 (by omega)
                (Or.inr ⟨hQ1, hQ2, by push_cast; omega, by push_cast; omega⟩)
            have o1 : P.val < r.val := hr1
            have o2 : r.val < r'.val := hr2
            have o3 : r'.val < Q.val := hr3
            omega
        rcases Nat.lt_or_ge p.val q.val with hlt | hge
        · exact main p q l hlt
            (Or.inl ⟨hp1, hp2, by push_cast at hq1 ⊢; omega, by push_cast at hq2 ⊢; omega⟩)
        · have hlt : q.val < p.val := by omega
          exact main q p l hlt
            (Or.inr ⟨hp1, hp2, by push_cast at hq1 ⊢; omega, by push_cast at hq2 ⊢; omega⟩)

/-- **Bing 1948, Theorem 7.** A faithful crooked sequence whose levels fill `[L, H]` has at
least `z (H − L)` terms. The Lipschitz hypothesis is part of the commissioned statement; the
proof does not use it, since the adjacency clause of the model already forces it. -/
theorem minimality : Minimality := by
  intro n ρ σ L H _ hf hLb hHb ⟨a, ha⟩ ⟨b, hb⟩
  have hLH : L ≤ H := le_trans (hLb a) (hHb a)
  rcases eq_or_lt_of_le hLH with he | hlt
  · have h0 : (H - L).toNat = 0 := by omega
    have hz : z 0 = 1 := rfl
    have := a.isLt
    rw [h0, hz]
    omega
  · have hab : a ≠ b := by
      intro hc
      rw [hc, hb] at ha
      omega
    have hd : (L : ℤ) + ((H - L).toNat : ℤ) = H := by
      have : ((H - L).toNat : ℤ) = H - L := Int.toNat_of_nonneg (by omega)
      omega
    exact minGap (H - L).toNat hf a b L (le_of_eq ha) (by rw [← ha]; exact hf.le a)
      (by rw [hd]; exact le_of_eq hb) (by rw [hd, ← hb]; exact hf.le b) hab

/-! ## What it buys -/

/-- **The timing bound.** Two indices at level distance `d` are at least `z d − 1` apart. -/
theorem index_gap_of_level_gap (_hmin : Minimality) {n : ℕ} {ρ σ : Fin n → ℤ}
    (_hlip : IsLip ρ) (hf : IsCrookedIvF ρ σ) (s t : Fin n) (hst : s < t) :
    z (|ρ t - ρ s|).toNat ≤ t.val - s.val + 1 := by
  have hle : s.val ≤ t.val := le_of_lt hst
  have htn : t.val < n := t.isLt
  have hrestr := isCrookedIvF_restrict hf s.val t.val hle htn
  have h0 : (⟨s.val + (0 : ℕ), by omega⟩ : Fin n) = s := Fin.ext (by simp)
  have h1 : (⟨s.val + (t.val - s.val), by omega⟩ : Fin n) = t := Fin.ext (by simp; omega)
  have hne : (⟨0, by omega⟩ : Fin (t.val - s.val + 1)) ≠ ⟨t.val - s.val, by omega⟩ := by
    intro hc
    have := congrArg Fin.val hc
    simp at this
    omega
  set d := (|ρ t - ρ s|).toNat with hd
  have hdz : ((d : ℤ)) = |ρ t - ρ s| := Int.toNat_of_nonneg (abs_nonneg _)
  rcases le_total (ρ s) (ρ t) with hcase | hcase
  · have hdv : (d : ℤ) = ρ t - ρ s := by rw [hdz, abs_of_nonneg (by omega)]
    exact minGap d hrestr ⟨0, by omega⟩ ⟨t.val - s.val, by omega⟩ (ρ s)
      (by simp) (by simpa [h0] using hf.le s)
      (by simp only [h1]; omega) (by simp only [h1]; have := hf.le t; omega) hne
  · have hdv : (d : ℤ) = ρ s - ρ t := by rw [hdz, abs_of_nonpos (by omega)]; ring
    exact minGap d hrestr ⟨t.val - s.val, by omega⟩ ⟨0, by omega⟩ (ρ t)
      (by simp [h1]) (by simpa [h1] using hf.le t)
      (by simp only [h0]; omega) (by simp only [h0]; have := hf.le s; omega) (Ne.symm hne)

/-- The obstruction of `no_zigWalk_fold_veeSeq` cannot occur in a faithful crooked sequence: an
arm that must be near `L` and near `H` gives the token `z (H − L) − 1` indices to cross, and the
walk of a ladder needs only `H − L − 2`. -/
theorem timing_slack (hmin : Minimality) {n : ℕ} {ρ σ : Fin n → ℤ} (L H : ℤ)
    (hlip : IsLip ρ) (hf : IsCrookedIvF ρ σ) (_hLb : ∀ t, L ≤ ρ t) (_hHb : ∀ t, ρ t ≤ H)
    (hLH : L + 3 ≤ H) (s t : Fin n) (hst : s < t) (hs : ρ s = L) (ht : ρ t = H) :
    (H - L - 2).toNat ≤ t.val - s.val := by
  have hgap := index_gap_of_level_gap hmin hlip hf s t hst
  have hdv : (|ρ t - ρ s|).toNat = (H - L).toNat := by rw [hs, ht, abs_of_nonneg (by omega)]
  rw [hdv] at hgap
  have hd3 : 3 ≤ (H - L).toNat := by omega
  have hlin := z_gt_linear (H - L).toNat hd3
  omega

/-- `index_gap_of_level_gap` with the hypotheses the proof does not need dropped: neither
`Minimality`, which is now a theorem, nor the Lipschitz clause, which the model forces. -/
theorem index_gap_of_level_gap' {n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ)
    (s t : Fin n) (hst : s < t) : z (|ρ t - ρ s|).toNat ≤ t.val - s.val + 1 :=
  index_gap_of_level_gap minimality hf.isLip hf s t hst

/-- `timing_slack` with the hypotheses the proof does not need dropped: the two levels need
only be attained, not extreme. -/
theorem timing_slack' {n : ℕ} {ρ σ : Fin n → ℤ} (L H : ℤ) (hf : IsCrookedIvF ρ σ)
    (hLH : L + 3 ≤ H) (s t : Fin n) (hst : s < t) (hs : ρ s = L) (ht : ρ t = H) :
    (H - L - 2).toNat ≤ t.val - s.val := by
  have hgap := index_gap_of_level_gap' hf s t hst
  have hdv : (|ρ t - ρ s|).toNat = (H - L).toNat := by rw [hs, ht, abs_of_nonneg (by omega)]
  rw [hdv] at hgap
  have hlin := z_gt_linear (H - L).toNat (by omega)
  omega

end HPC.Fold
