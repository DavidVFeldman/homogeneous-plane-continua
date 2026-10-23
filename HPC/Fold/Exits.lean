import HPC.Fold.Reduction

/-!
# What `SegLam` demands of a single arm

Four per-arm lemmas reducing `SegLam` to conditions on the arm's first exit from the window
`[p−1, p+1]`, and three named propositions recording what is conjectured but unproved.

The per-arm lemmas are proved. The propositions are not; each records computational evidence
in its docstring. Their combination into `F2Prime` is **not** claimed here: the obvious chain
fails when the height is set by an arm that never drops, and the correct combination has not
been established.

English proofs: COMMISSION-batch10.md §3. Delivered complete: no `sorry` remains.

One remark on the delivery, anticipated by the commission: clause (4) of `SegLam` asks for
`L ≤ A j`, which is an ambient hypothesis on the arm rather than a consequence of the window
bounds, so the hypothesis `∀ j, L ≤ A j` is added to `segLam_of_bounded` and to
`segLam_of_peak_before_drop` as directed — and, for the same reason, to `segLam_of_no_drop`,
which is proved by reduction to `segLam_of_bounded`.
-/

namespace HPC.Fold

variable {m : ℕ} {A : Fin m → ℤ} {p H L h : ℤ}

/-- An arm confined to `[p−1, h+1]` satisfies `SegLam`: take `t = m`, so the leg-3 clauses are
vacuous, and let `s` be the least peak index or `m`.

The hypothesis `hL` is the ambient lower bound demanded by clause (4); it was added to the
commissioned statement. The hypothesis `h0` turns out to be unnecessary and is kept as
commissioned (`hm` only appears in its statement). -/
theorem segLam_of_bounded (hm : 0 < m) (_h0 : A ⟨0, hm⟩ = p) (hL : ∀ j, L ≤ A j) (hb : ∀ j, p - 1 ≤ A j ∧ A j ≤ h + 1) :
    SegLam A p H L h := by
  classical
  by_cases hex : ∃ j : Fin m, h ≤ A j + phase A j
  · obtain ⟨s, hsP, hsmin⟩ := exists_least_index (fun j => h ≤ A j + phase A j) hex
    refine ⟨s.val, m, le_of_lt s.isLt, le_rfl, ?_, ?_, ?_, ?_, Or.inl rfl⟩
    · exact fun j _ => hb j
    · intro hs'
      rwa [show (⟨s.val, hs'⟩ : Fin m) = s from Fin.ext rfl]
    · exact fun j hj => lt_of_not_ge (hsmin j hj)
    · exact fun j _ _ => ⟨hL j, (hb j).2⟩
  · push_neg at hex
    refine ⟨m, m, le_rfl, le_rfl, ?_, ?_, ?_, ?_, Or.inl rfl⟩
    · exact fun j _ => hb j
    · intro hs'; exact absurd hs' (lt_irrefl m)
    · exact fun j _ => hex j
    · exact fun j _ hj => absurd hj (by omega)

/-- An arm that never drops to `p − 2` attains its maximum inside the defining set of
`hStarArm`, so `hStarArm` is that maximum. -/
theorem le_hStarArm_of_no_drop (hm : 0 < m) (_h0 : A ⟨0, hm⟩ = p)
    (hnd : ∀ j, p - 1 ≤ A j) (j : Fin m) : A j ≤ hStarArm A p := by
  classical
  set S : Set ℤ := {v : ℤ | ∃ j : Fin m, A j = v ∧ ∀ j' : Fin m, j' ≤ j → p - 1 ≤ A j'}
  have hsub : S ⊆ Set.range A := by
    rintro v ⟨j, rfl, -⟩
    exact ⟨j, rfl⟩
  have hbdd : BddAbove S := ((Set.finite_range A).subset hsub).bddAbove
  exact le_csSup hbdd ⟨j, rfl, fun j' _ => hnd j'⟩

/-- Hence an arm with no drop satisfies `SegLam` at any height at least its own demand.

As for `segLam_of_bounded`, the ambient lower bound `hL` is added to the commissioned
statement. -/
theorem segLam_of_no_drop (hm : 0 < m) (h0 : A ⟨0, hm⟩ = p) (hL : ∀ j, L ≤ A j)
    (hnd : ∀ j, p - 1 ≤ A j) (hh : hStarArm A p ≤ h) :
    SegLam A p H L h := by
  refine segLam_of_bounded hm h0 hL (fun j => ⟨hnd j, ?_⟩)
  have := le_hStarArm_of_no_drop hm h0 hnd j
  omega

/-- The general per-arm criterion. If the arm's phase-adjusted level reaches `h` no later than
its first drop to `p − 2`, and whenever it exceeds `h + 1` after that it has visited `L + 1` or
below in between, then `SegLam` holds.

As directed by the commission, the ambient lower bound `hL` is added to the commissioned
statement. The hypotheses `hA`, `h0` and `hph` turn out to be unnecessary and are kept as
commissioned (`hm` only appears in the statement of `h0`). -/
theorem segLam_of_peak_before_drop (hm : 0 < m) (_hA : IsLip A) (_h0 : A ⟨0, hm⟩ = p)
    (_hph : p ≤ h) (hL : ∀ j, L ≤ A j) (s : ℕ) (hs : s < m)
    (hpeak : ∀ hs' : s < m, h ≤ A ⟨s, hs'⟩ + phase A ⟨s, hs'⟩)
    (hmin : ∀ j : Fin m, j.val < s → A j + phase A j < h)
    (hnodrop : ∀ j : Fin m, j.val < s → p - 1 ≤ A j)
    (hvalley : ∀ u : Fin m, s ≤ u.val → h + 1 < A u →
      ∃ j : Fin m, s ≤ j.val ∧ j.val < u.val ∧ A j ≤ L + 1) :
    SegLam A p H L h := by
  classical
  -- the first three clauses, common to both cases
  have hleg1 : ∀ j : Fin m, j.val < s → p - 1 ≤ A j ∧ A j ≤ h + 1 := by
    intro j hj
    refine ⟨hnodrop j hj, ?_⟩
    have h1 := hmin j hj
    rcases phase_zero_or_one A j with e | e <;> omega
  by_cases hex : ∃ u : Fin m, s ≤ u.val ∧ h + 1 < A u
  · obtain ⟨u₀, ⟨hu₀s, hu₀A⟩, hu₀min⟩ :=
      exists_least_index (fun u : Fin m => s ≤ u.val ∧ h + 1 < A u) hex
    obtain ⟨j, hjs, hju₀, hjL⟩ := hvalley u₀ hu₀s hu₀A
    refine ⟨s, j.val + 1, by omega, by omega, hleg1, hpeak, hmin, ?_, Or.inr ⟨by omega, ?_⟩⟩
    · intro j' hj's hj't
      refine ⟨hL j', ?_⟩
      by_contra hcon
      exact hu₀min j' (by omega) ⟨hj's, by omega⟩
    · intro j' hj'
      rwa [show j' = j from Fin.ext (by omega)]
  · push_neg at hex
    refine ⟨s, m, by omega, le_rfl, hleg1, hpeak, hmin, ?_, Or.inl rfl⟩
    intro j hj _
    exact ⟨hL j, hex j hj⟩

/-! ## Conjectures

The three statements below are recorded, not proved. Each is quantified over crooked
1-Lipschitz sequences and every basepoint. -/

/-- **Exclusion.** Never do both arms drop to `p − 2` and both arms rise to `p + 2`.

Verified on 10 115 854 basepoints: every crooked 1-Lipschitz sequence of length at most 13 on
six levels, and random crooked sequences to length 90. Sixteen constructed adversaries — one
arm built to drop then climb, the other to climb then drop — are never crooked as whole
sequences. -/
def Exclusion : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n), IsLip ρ → IsCrookedSeq ρ →
    ¬ ((∃ j, ρ i - 2 ≥ armG ρ i j) ∧ (∃ j, ρ i - 2 ≥ armT ρ i j) ∧
       (∃ j, ρ i + 2 ≤ armG ρ i j) ∧ (∃ j, ρ i + 2 ≤ armT ρ i j))

/-- **Balance.** If both arms drop to `p − 2`, their demands differ by at most one.

Verified on 13 198 instances in the same corpus, no exception. -/
def Balance : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n), IsLip ρ → IsCrookedSeq ρ →
    (∃ j, ρ i - 2 ≥ armG ρ i j) → (∃ j, ρ i - 2 ≥ armT ρ i j) →
    |hStarArm (armG ρ i) (ρ i) - hStarArm (armT ρ i) (ρ i)| ≤ 1

/-- The per-arm valley condition: past the peak index `s`, the arm does not exceed `h + 1`
without having visited `L + 1` or below in between. This is the hypothesis `hvalley` of
`segLam_of_peak_before_drop`, named so it can be quantified over both arms. -/
def ValleyBefore {m : ℕ} (A : Fin m → ℤ) (L h : ℤ) (s : ℕ) : Prop :=
  ∀ u : Fin m, s ≤ u.val → h + 1 < A u →
    ∃ j : Fin m, s ≤ j.val ∧ j.val < u.val ∧ A j ≤ L + 1

/-- **HighExitValley.** At the height `hStar`, both arms satisfy `ValleyBefore` at their own
peak indices.

Verified on 1 037 456 arms in the same corpus, no exception. -/
def HighExitValley : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ), IsLip ρ → IsCrookedSeq ρ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∀ s : ℕ, (∀ j : Fin (n - i.val), j.val < s →
        armG ρ i j + phase (armG ρ i) j < hStar ρ i H L) →
      ValleyBefore (armG ρ i) L (hStar ρ i H L) s) ∧
    (∀ s : ℕ, (∀ j : Fin (i.val + 1), j.val < s →
        armT ρ i j + phase (armT ρ i) j < hStar ρ i H L) →
      ValleyBefore (armT ρ i) L (hStar ρ i H L) s)

end HPC.Fold
