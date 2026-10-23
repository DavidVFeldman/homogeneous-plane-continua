import HPC.Fold.Leg4Wide

/-!
# The criterion of the wide four-leg engine, as a predicate

`foldsOnto_leg4W` (`HPC/Fold/Leg4Wide.lean`) is the engine of the four-leg walks: for parameters
`L H K M P` inside a window, a 1-Lipschitz arm of the band `[L, H]` based within one of `P` folds
onto `leg4Walk L H K M P` as soon as three *announcements* hold — one for the descents to `P - 3`,
one for the descents to `P - 4`, one for the ascents to `K + 2`.

Batch 58 asks a question about those announcements rather than about the fold, so they are
packaged here as a predicate:

* `Leg4Window L H K M P` — the engine's window on the parameters;
* `Leg4CritG p lo hi H K M P` — the base condition and the three announcements, with the
  *triggers* read on the point sequence `p`, every landmark of the form "at `l` or above" read on
  `hi` and every landmark of the form "at `l` or below" read on `lo`;
* `Leg4Crit f H K M P` — the point form, `lo = hi = p = f`, which is exactly the list of
  hypotheses of `foldsOnto_leg4W`;
* `foldsOnto_of_leg4Crit` — the engine, restated with the criterion as a single hypothesis.

The general form is what question 3 of COMMISSION.md asks about: a link of a faithful pair is the
interval `[ρ, σ]`, and the interval reading of the criterion is `Leg4CritG ρ ρ σ` for an arm read
upwards and `Leg4CritG (a - ρ) (a - σ) (a - ρ)` for an arm read through the reflection `armRefl a`.
-/

namespace HPC.Fold

/-- **The window of the wide four-leg engine**, as `foldsOnto_leg4W` states it. -/
def Leg4Window (L H K M P : ℤ) : Prop :=
  L + 2 ≤ P ∧ P ≤ L + 6 ∧ P ≤ K ∧ K ≤ H - 1 ∧ L + 1 ≤ M ∧ M ≤ P - 2 ∧ M + 3 ≤ K ∧ H ≤ K + 3

instance (L H K M P : ℤ) : Decidable (Leg4Window L H K M P) := by
  unfold Leg4Window; infer_instance

/-- **The criterion of the wide four-leg engine, read on an interval.** The triggers are read on
the point sequence `p`; a landmark "at `l` or above" is read on the upper end `hi` and a landmark
"at `l` or below" on the lower end `lo`. -/
def Leg4CritG {m : ℕ} (p lo hi : Fin m → ℤ) (H K M P : ℤ) : Prop :=
  (∀ d : Fin m, d.val = 0 → P - 1 ≤ p d ∧ p d ≤ P ∧ p d ≤ K - 1) ∧
  (∀ d : Fin m, p d ≤ P - 3 →
      (∃ k : Fin m, k.val < d.val ∧ K ≤ hi k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ lo k ≤ P - 2 ∧ K - 1 ≤ hi k')) ∧
  (∀ d : Fin m, p d ≤ P - 4 →
      (∃ k : Fin m, k.val < d.val ∧ K + 2 ≤ hi k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ lo k ≤ M - 1 ∧ H - 2 ≤ hi k') ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        K + 1 ≤ hi k ∧ lo k' ≤ M ∧ H - 2 ≤ hi k'')) ∧
  (∀ d : Fin m, K + 2 ≤ p d →
      (∃ k : Fin m, k.val < d.val ∧ lo k ≤ M - 1) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ K + 1 ≤ hi k ∧ lo k' ≤ M + 1) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        lo k ≤ P - 2 ∧ K ≤ hi k' ∧ lo k'' ≤ M + 1))

instance {m : ℕ} (p lo hi : Fin m → ℤ) (H K M P : ℤ) :
    Decidable (Leg4CritG p lo hi H K M P) := by
  unfold Leg4CritG
  exact @instDecidableAnd _ _ inferInstance
    (@instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance inferInstance))

/-- **The criterion in point form**: the hypotheses of `foldsOnto_leg4W`, verbatim. -/
def Leg4Crit {m : ℕ} (f : Fin m → ℤ) (H K M P : ℤ) : Prop := Leg4CritG f f f H K M P

instance {m : ℕ} (f : Fin m → ℤ) (H K M P : ℤ) : Decidable (Leg4Crit f H K M P) := by
  unfold Leg4Crit; infer_instance

/-- **The engine, with the criterion as one hypothesis.** -/
theorem foldsOnto_of_leg4Crit {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L H K M P : ℤ)
    (hw : Leg4Window L H K M P) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H)
    (hc : Leg4Crit f H K M P) :
    FoldsOnto f (leg4Len L H K M P) (leg4Walk L H K M P) := by
  obtain ⟨hLP, hPL, hPK, hKH, hLM, hMP, hMK, hHK⟩ := hw
  obtain ⟨hbase, hfloor, hdeep, hceil⟩ := hc
  obtain ⟨h0lo, h0hi, h0K⟩ := hbase ⟨0, hm⟩ rfl
  exact foldsOnto_leg4W hm f hf L H K M P hLP hPL hPK hKH hLM hMP hMK hHK h0lo h0hi h0K
    hL hH hfloor hdeep hceil

/-- The interval reading is weaker than the point reading: a link's interval contains its point,
so every landmark the point form announces the interval form announces too. -/
theorem leg4CritG_of_leg4Crit {m : ℕ} {ρ σ : Fin m → ℤ} (hle : ∀ t, ρ t ≤ σ t) (H K M P : ℤ)
    (h : Leg4Crit ρ H K M P) : Leg4CritG ρ ρ σ H K M P := by
  obtain ⟨hbase, hfloor, hdeep, hceil⟩ := h
  refine ⟨hbase, ?_, ?_, ?_⟩
  · intro d hd
    rcases hfloor d hd with ⟨k, hk, hkv⟩ | ⟨k, k', h1, h2, h3, h4⟩
    · exact Or.inl ⟨k, hk, le_trans hkv (hle k)⟩
    · exact Or.inr ⟨k, k', h1, h2, h3, le_trans h4 (hle k')⟩
  · intro d hd
    rcases hdeep d hd with ⟨k, hk, hkv⟩ | ⟨k, k', h1, h2, h3, h4⟩ |
      ⟨k, k', k'', h1, h2, h3, h4, h5, h6⟩
    · exact Or.inl ⟨k, hk, le_trans hkv (hle k)⟩
    · exact Or.inr (Or.inl ⟨k, k', h1, h2, h3, le_trans h4 (hle k')⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', h1, h2, h3, le_trans h4 (hle k), h5,
        le_trans h6 (hle k'')⟩)
  · intro d hd
    rcases hceil d hd with ⟨k, hk, hkv⟩ | ⟨k, k', h1, h2, h3, h4⟩ |
      ⟨k, k', k'', h1, h2, h3, h4, h5, h6⟩
    · exact Or.inl ⟨k, hk, hkv⟩
    · exact Or.inr (Or.inl ⟨k, k', h1, h2, le_trans h3 (hle k), h4⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', h1, h2, h3, h4, le_trans h5 (hle k'), h6⟩)

end HPC.Fold
