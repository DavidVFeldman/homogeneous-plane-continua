import HPC.Fold.Bing9ShaveWitness
import HPC.Fold.Landmark

/-!
# The crossing at the ceiling is false, and so is the third walk

The branch `L + 4` of span nine was left by batch 48 resting on two statements *across the
basepoint*, `cross_valley_profile` and `cross_ceil_profile` (`HPC/Fold/Mixed.lean`), through which
`unserved_profile` and then `unserved_leg3deep` were to be reached. This file refutes the second
of the two, and with it both of the statements that depend on it, at a basepoint of the general
model that is already in the development: the basepoint `336` of `bing9sB` — `bing 0 9` with the
peak at index `309` shaved from `7` to `6` — which batch 46 used to refute `unserved_ceiling`.

Three facts about that basepoint, all of them decided on the chain itself:

* **the forward arm fails `Leg3Ceil`** (`not_leg3Ceil_sBG`). It stands at `L + 8` at its step
  `72`, and before that step it never drops below `L + 2` except at its step `2` — so the clause's
  low landmark `k`, which has to come five steps after a time at `L + 5` and so at its step `8` or
  later, does not exist;
* the Λ-walk does not fold the backward arm (`not_foldsOnto_lam_sBT`, batch 46), and the V-walk
  does not fold the forward arm (`not_foldsOnto_vee_sBG`), so the pair folds onto neither canonical
  walk;
* **the third walk does not fold the forward arm either** (`not_foldsOnto_leg3_sBG`). This is new,
  and it is `leg3Ceil_of_foldsOnto_leg3` (`HPC/Fold/Landmark.lean`) that gives it: `Leg3Ceil` is
  not only sufficient for the fold onto `L+3 → L+6 → L+1 → L+8`, it is necessary.

Hence the three refutations below. The pair is nevertheless served — by the walk
`L+3 → L+2 → L+8 → L+1`, checked outside Lean in `census-batch49c.c` — so span nine is not
refuted; what is refuted is the route to it through the third walk.

Why the censuses of batches 46–48 did not see this: they read the branch hypothesis
`HighAt (armG ρ i) (L + 1) (L + 8)` as asking a time at `L + 1` or below before every time at
`L + 8`, where the definition asks `L + 2` or below. The forward arm here never goes below `L + 2`
before its step `72`, so the basepoint was outside their corpus, although the Lean witnesses of
batch 46 used exactly it. `census-batch49b.c` reads the hypothesis as the definition does and
finds 225 refutations of `cross_ceil_profile` and 39 of `unserved_profile` over the same
generators.
-/

namespace HPC.Fold

/-! ## The forward arm at the basepoint `336` fails `Leg3Ceil` -/

/-- Before its step seventy-two the forward arm stands at `L + 2` or below only at its step two.
(With `sBG_before_seventytwo`: it stands at `L + 2` exactly there.) -/
theorem sBG_low_early : ∀ j : Fin (986 - sBBase.val), j.val < 72 → sBG j ≤ 2 → j.val < 3 := by
  decide +kernel

/-- **The forward arm fails the ceiling clause.** Its ascent to `L + 8` at step seventy-two has no
low landmark: the clause asks for a time at `L + 2` or below at a step at least `8`, and the arm
has none before its step `72`. -/
theorem not_leg3Ceil_sBG : ¬ Leg3Ceil sBG 0 := by
  intro h
  obtain ⟨j, k, hj3, hjk, hkd, -, hkv⟩ := h ⟨72, by decide⟩ (by rw [sBG_seventytwo]; norm_num)
  have hk6 : k.val + 6 ≤ 72 := hkd
  have hk72 : k.val < 72 := by omega
  have := sBG_low_early k hk72 (by omega)
  omega

/-- **The third walk does not fold the forward arm.** By `leg3Ceil_of_foldsOnto_leg3` a fold onto
`L+3 → L+6 → L+1 → L+8` forces the ceiling clause, which fails here. -/
theorem not_foldsOnto_leg3_sBG :
    ¬ FoldsOnto sBG (leg3Len 0 (0 + 9) (0 + 6) (0 + 4)) (leg3Walk 0 (0 + 9) (0 + 6) (0 + 4)) := by
  intro h
  exact not_leg3Ceil_sBG (leg3Ceil_of_foldsOnto_leg3 h)

/-! ## The three statements, and their refutations -/

/-- The statement of the work item `cross_ceil_profile` of `HPC/Fold/Mixed.lean`. -/
def CrossCeilProfile : Prop :=
  ∀ {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) →
    (∃ t, ρ t = L) → (∃ t, ρ t = L + 9) → ρ i = L + 4 →
    HighAt (armG ρ i) (L + 1) (L + 8) → HighAt (armT ρ i) (L + 1) (L + 8) →
    (¬ Leg3Ceil (armG ρ i) L ∨ ¬ Leg3Ceil (armT ρ i) L) →
    FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)

/-- The statement of `unserved_profile` of `HPC/Fold/Mixed.lean`. -/
def UnservedProfile : Prop :=
  ∀ {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) →
    (∃ t, ρ t = L) → (∃ t, ρ t = L + 9) → ρ i = L + 4 →
    HighAt (armG ρ i) (L + 1) (L + 8) → HighAt (armT ρ i) (L + 1) (L + 8) →
    ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
       FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)) →
    ¬ (FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
       FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L)) →
    (Leg3Valley (armG ρ i) L ∧ Leg3Ceil (armG ρ i) L) ∧
      (Leg3Valley (armT ρ i) L ∧ Leg3Ceil (armT ρ i) L)

/-- The statement of `unserved_leg3deep` of `HPC/Fold/Mixed.lean`: the third walk serves every
unserved pair of the branch. -/
def UnservedLeg3deep : Prop :=
  ∀ {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) →
    (∃ t, ρ t = L) → (∃ t, ρ t = L + 9) → ρ i = L + 4 →
    HighAt (armG ρ i) (L + 1) (L + 8) → HighAt (armT ρ i) (L + 1) (L + 8) →
    ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
       FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)) →
    ¬ (FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
       FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L)) →
    FoldsOnto (armG ρ i) (leg3Len L (L + 9) (L + 6) (L + 4))
        (leg3Walk L (L + 9) (L + 6) (L + 4)) ∧
      FoldsOnto (armT ρ i) (leg3Len L (L + 9) (L + 6) (L + 4))
        (leg3Walk L (L + 9) (L + 6) (L + 4))

/-- The pair at the basepoint `336` of `bing9sB` folds onto neither canonical walk. -/
theorem sB_not_lam :
    ¬ (FoldsOnto (armG bing9sB sBBase) (lamLen (0 + 3) (0 + 9) 0) (lamCenter (0 + 3) (0 + 9) 0) ∧
      FoldsOnto (armT bing9sB sBBase) (lamLen (0 + 3) (0 + 9) 0)
        (lamCenter (0 + 3) (0 + 9) 0)) := by
  rintro ⟨-, h2⟩
  exact not_foldsOnto_lam_sBT (by simpa [sBT] using h2)

theorem sB_not_vee :
    ¬ (FoldsOnto (armG bing9sB sBBase) (veeLen (0 + 5) (0 + 9) 0) (veeCenter (0 + 5) (0 + 9) 0) ∧
      FoldsOnto (armT bing9sB sBBase) (veeLen (0 + 5) (0 + 9) 0)
        (veeCenter (0 + 5) (0 + 9) 0)) := by
  rintro ⟨h1, -⟩
  exact not_foldsOnto_vee_sBG (by simpa [sBG] using h1)

/-- **The ceiling crossing is false in the general model.** At the basepoint `336` of `bing9sB`
the forward arm fails `Leg3Ceil`, so the item asks both arms to fold onto the Λ-walk; the backward
arm does not. -/
theorem not_crossCeilProfile : ¬ CrossCeilProfile := by
  intro h
  have := h bing9sB bing9 sBBase 0 bing9sB_isLip bing9sB_faithful bing9sB_lb
    (fun t => by simpa using bing9sB_ub t) bing9sB_attains_bot
    (by simpa using bing9sB_attains_top) (by simpa using sBBase_level)
    (by simpa [sBG] using sBG_highAt) (by simpa [sBT] using sBT_highAt)
    (Or.inl (by simpa [sBG] using not_leg3Ceil_sBG))
  exact sB_not_lam this

/-- **`unserved_profile` is false in the general model**, at the same basepoint: the pair is
unserved and its forward arm fails `Leg3Ceil`. -/
theorem not_unservedProfile : ¬ UnservedProfile := by
  intro h
  have := h bing9sB bing9 sBBase 0 bing9sB_isLip bing9sB_faithful bing9sB_lb
    (fun t => by simpa using bing9sB_ub t) bing9sB_attains_bot
    (by simpa using bing9sB_attains_top) (by simpa using sBBase_level)
    (by simpa [sBG] using sBG_highAt) (by simpa [sBT] using sBT_highAt) sB_not_lam sB_not_vee
  exact not_leg3Ceil_sBG (by simpa [sBG] using this.1.2)

/-- **The third walk does not serve every unserved pair.** The same basepoint: the pair is
unserved, and the forward arm does not fold onto `L+3 → L+6 → L+1 → L+8`. -/
theorem not_unservedLeg3deep : ¬ UnservedLeg3deep := by
  intro h
  have := h bing9sB bing9 sBBase 0 bing9sB_isLip bing9sB_faithful bing9sB_lb
    (fun t => by simpa using bing9sB_ub t) bing9sB_attains_bot
    (by simpa using bing9sB_attains_top) (by simpa using sBBase_level)
    (by simpa [sBG] using sBG_highAt) (by simpa [sBT] using sBT_highAt) sB_not_lam sB_not_vee
  exact not_foldsOnto_leg3_sBG (by simpa [sBG] using this.1)

end HPC.Fold
