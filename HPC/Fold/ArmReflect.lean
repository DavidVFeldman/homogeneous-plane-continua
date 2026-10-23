import HPC.Fold.ThreeWalks

/-!
# Reflecting an arm, and the branch `L + 5` at the level of arms

Batch 48 showed that the branch `L + 5` is **not** the reflection of the branch `L + 4` in the
general model: reflecting a faithful pair `(ρ, σ)` in a level gives the pair `(a - σ, a - ρ)`,
whose point sequence is `a - σ` and not `a - ρ`, and the folds it delivers are folds of `a - σ`
(`HPC/Fold/Reflect.lean`, `HPC/Fold/LinkFold.lean`).

Reflecting a single **arm** is a different operation and needs no symmetry of the model:
`armRefl a f = fun j => a - f j` is a relabelling of the levels of one 1-Lipschitz sequence. Every
statement of the development whose hypotheses are *only* `IsLip`, the band, the basepoint level
and the landmark clauses transports along it verbatim. That is what this file does, and the answer
it gives to the commission's third question is in two halves.

* **The criteria transport.** The three exact criteria of batch 51 are statements of exactly that
  kind, so each has a mirror at the basepoint `L + 5`, with the three walks replaced by their
  reflections and each landmark clause by the clause obtained by reading `L + k` as `L + 9 - k`:
  `foldsOnto_w3R_iff_landmark`, `foldsOnto_w4R_iff_landmark`, `foldsOnto_w5R_iff_landmark`.
  `three_walks5_iff_sentence` and `s3_span_nine_mid5_of_sentence` are then the branch `L + 5`'s
  form of `three_walks_iff_sentence` and `s3_span_nine_mid4_of_sentence`, with the same proofs read
  through the reflection. So the branch `L + 5` needs no new engine: its walks are the reflections
  of `w₃`, `w₄`, `w₅` and its criteria are the reflected sentences.

* **The dichotomies do not transport for free.** `valley4_or_vee` and `leg3Ceil_or_lam` consume the
  crookedness of the arm, and `CrookUp` and `CrookDown` are *not* reflections of each other: the
  reflection of `CrookDown` is the clause `CrookUpR` below, whose two windows sit one level above
  those of `CrookUp` (`crookUpR_iff_crookDown_armRefl`), and the model delivers `CrookUp`. The
  reflected dichotomies are therefore proved here from `CrookUpR`/`CrookDownR`
  (`ceil4R_or_lam`, `floor3R_or_vee`, `unserved_three_walks5_or_cross`), and whether an arm of the
  model satisfies those clauses is settled — negatively — in `HPC/Fold/ArmReflectGap.lean`.

The dictionary of clauses, at the reflection level `a = L + (L + 9)`:

| branch `L + 4` | branch `L + 5` |
|---|---|
| `Valley4` (descents to `L + 1` announced at `L + 5`) | `Ceil4R` (ascents to `L + 8` announced at `L + 4`) |
| `Leg3Ceil` | `Floor3R` |
| `MidW4`, `CeilW4`, `BottomW4` | `MidW4R`, `FloorW4R`, `TopW4R` |
| `Valley5`, `TopW5` | `Ceil5R`, `BottomW5R` |
-/

namespace HPC.Fold

/-! ## The reflection of an arm -/

/-- **The reflection of an arm in the level `a`**: `j ↦ a - f j`. -/
def armRefl (a : ℤ) {m : ℕ} (f : Fin m → ℤ) : Fin m → ℤ := fun j => a - f j

@[simp] theorem armRefl_apply (a : ℤ) {m : ℕ} (f : Fin m → ℤ) (j : Fin m) :
    armRefl a f j = a - f j := rfl

/-- Reflection is an involution. -/
theorem armRefl_armRefl (a : ℤ) {m : ℕ} (f : Fin m → ℤ) : armRefl a (armRefl a f) = f := by
  funext j; simp only [armRefl_apply]; ring

/-- The reflection of a 1-Lipschitz arm is 1-Lipschitz. -/
theorem armRefl_isLip {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) (a : ℤ) : IsLip (armRefl a f) := by
  intro j j' hjj'
  have := hf j j' hjj'
  simp only [armRefl_apply]
  rw [abs_le] at this ⊢
  omega

/-- **Folding transports.** An arm folds onto a walk exactly when its reflection folds onto the
reflected walk. -/
theorem foldsOnto_armRefl {m : ℕ} (a : ℤ) (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) :
    FoldsOnto (armRefl a f) len (fun u => a - c u) ↔ FoldsOnto f len c := by
  constructor <;> rintro ⟨β, h1, h2, h3, h4⟩ <;> refine ⟨β, h1, h2, h3, fun j => ?_⟩ <;>
    · have := h4 j
      simp only [armRefl_apply] at this ⊢
      rw [abs_le] at this ⊢
      omega

/-- The form in which the transport is used: a fold of the arm itself onto a reflected walk. -/
theorem foldsOnto_armRefl' {m : ℕ} (a : ℤ) (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) :
    FoldsOnto f len (fun u => a - c u) ↔ FoldsOnto (armRefl a f) len c := by
  have key := foldsOnto_armRefl a (armRefl a f) len c
  rw [armRefl_armRefl] at key
  exact key

/-! ## The reflected walks

The three walks of the branch `L + 4` and the two canonical walks all have reflections inside the
development's own families: `leg3Walk` and `leg3Walk'` are reflections of one another by
definition, and the Λ-itinerary and the V-itinerary are reflections of one another because
`lamCenter` is equivariant under a translation of all three of its levels. -/

/-- The peak level translates. -/
theorem κ_translate (p H c : ℤ) : κ (p + c) (H + c) = κ p H + c := by
  simp only [κ]; omega

/-- The length of the Λ-itinerary is translation-invariant. -/
theorem lamLen_translate (p H L c : ℤ) : lamLen (p + c) (H + c) (L + c) = lamLen p H L := by
  simp only [lamLen, κ_translate]
  congr 1
  omega

/-- The centers of the Λ-itinerary translate. -/
theorem lamCenter_translate (p H L c : ℤ) (u : ℕ) :
    lamCenter (p + c) (H + c) (L + c) u = lamCenter p H L u + c := by
  simp only [lamCenter, κ_translate]
  split_ifs <;> omega

/-- **The reflection of a Λ-walk is a V-walk.** -/
theorem veeCenter_armRefl (p H L : ℤ) (u : ℕ) :
    veeCenter (L + H - p) H L u = (L + H) - lamCenter p H L u := by
  have h := lamCenter_translate p H L (-(L + H)) u
  simp only [veeCenter]
  have e1 : -(L + H - p) = p + -(L + H) := by ring
  have e2 : -L = H + -(L + H) := by ring
  have e3 : -H = L + -(L + H) := by ring
  rw [e1, e2, e3, h]
  ring

/-- **The reflection of a V-walk is a Λ-walk.** -/
theorem lamCenter_armRefl (p H L : ℤ) (u : ℕ) :
    lamCenter (L + H - p) H L u = (L + H) - veeCenter p H L u := by
  have h := veeCenter_armRefl (L + H - p) H L u
  have e : L + H - (L + H - p) = p := by ring
  rw [e] at h
  omega

/-- The two itineraries have the same length under the reflection. -/
theorem veeLen_armRefl (p H L : ℤ) : veeLen (L + H - p) H L = lamLen p H L := by
  simp only [veeLen]
  have e1 : -(L + H - p) = p + -(L + H) := by ring
  have e2 : -L = H + -(L + H) := by ring
  have e3 : -H = L + -(L + H) := by ring
  rw [e1, e2, e3, lamLen_translate]

/-- The two itineraries have the same length under the reflection. -/
theorem lamLen_armRefl (p H L : ℤ) : lamLen (L + H - p) H L = veeLen p H L := by
  have h := veeLen_armRefl (L + H - p) H L
  have e : L + H - (L + H - p) = p := by ring
  rw [e] at h
  omega

/-- **`w₃` reflected.** The reflection of `w₃ = L+3 → L+6 → L+1 → L+8` is the walk
`L+6 → L+3 → L+8 → L+1`, based at `L + 5`. -/
theorem w3R_eq (L : ℤ) :
    leg3Walk' L (L + 9) (L + 6) (L + 5) =
      fun u => (L + (L + 9)) - leg3Walk L (L + 9) (L + 6) (L + 4) u := by
  funext u
  simp only [leg3Walk', show L + (L + 9) - (L + 5) = L + 4 from by ring]

/-- **`w₄` reflected.** The reflection of `w₄ = L+3 → L+2 → L+8 → L+1` is
`leg3Walk L (L+9) (L+7) (L+7)`, based at `L + 6`. -/
theorem w4R_eq (L : ℤ) :
    leg3Walk L (L + 9) (L + 7) (L + 7) =
      fun u => (L + (L + 9)) - leg3Walk' L (L + 9) (L + 7) (L + 2) u := by
  funext u
  simp only [leg3Walk', show L + (L + 9) - (L + 2) = L + 7 from by ring]
  ring

/-- **`w₅` reflected.** The reflection of `w₅ = L+3 → L+7 → L+1 → L+8` is the walk
`L+6 → L+2 → L+8 → L+1`, based at `L + 5`. -/
theorem w5R_eq (L : ℤ) :
    leg3Walk' L (L + 9) (L + 7) (L + 5) =
      fun u => (L + (L + 9)) - leg3Walk L (L + 9) (L + 7) (L + 4) u := by
  funext u
  simp only [leg3Walk', show L + (L + 9) - (L + 5) = L + 4 from by ring]

/-! ## The reflected clauses

Each clause of the branch `L + 4` is read through `L + k ↦ L + 9 - k`. -/

/-- **The ceiling clause of `w₃` reflected** (the reflection of `Valley4`). Before every ascent to
`L + 8` a time at `L + 4` or below, at a step at least `3` and at least four steps earlier. -/
def Ceil4R {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, L + 8 ≤ f d → ∃ j : Fin m, 3 ≤ j.val ∧ j.val + 4 ≤ d.val ∧ f j ≤ L + 4

/-- **The floor clause of `w₃` reflected** (the reflection of `Leg3Ceil`). -/
def Floor3R {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L + 1 →
    ∃ j k : Fin m, 3 ≤ j.val ∧ j.val + 5 ≤ k.val ∧ k.val + 6 ≤ d.val ∧
      f j ≤ L + 4 ∧ L + 7 ≤ f k

/-- **The landmark sentence of `w₃` reflected.** -/
def Leg3LandR {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop := Ceil4R f L ∧ Floor3R f L

/-- **The trough clause of `w₄` reflected** (the reflection of `MidW4`). -/
def MidW4R {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L + 4 → ∃ j : Fin m, 1 ≤ j.val ∧ j.val + 2 ≤ d.val ∧ L + 6 ≤ f j

/-- **The floor clause of `w₄` reflected** (the reflection of `CeilW4`). -/
def FloorW4R {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L + 1 → ∃ j : Fin m, 1 ≤ j.val ∧ j.val + 5 ≤ d.val ∧ L + 6 ≤ f j

/-- **The ceiling clause of `w₄` reflected** (the reflection of `BottomW4`). -/
def TopW4R {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, L + 9 ≤ f d → ∃ j k : Fin m, 1 ≤ j.val ∧ j.val + 6 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
    L + 6 ≤ f j ∧ f k ≤ L + 2

/-- **The ceiling clause of `w₅` reflected** (the reflection of `Valley5`). -/
def Ceil5R {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, L + 8 ≤ f d → ∃ j : Fin m, 4 ≤ j.val ∧ j.val + 5 ≤ d.val ∧ f j ≤ L + 3

/-- **The floor clause of `w₅` reflected** (the reflection of `TopW5`). -/
def BottomW5R {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L → ∃ j k : Fin m, 4 ≤ j.val ∧ j.val + 6 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
    f j ≤ L + 3 ∧ L + 7 ≤ f k

/-! ### Each reflected clause is the clause of the reflected arm -/

theorem valley4_armRefl {m : ℕ} (f : Fin m → ℤ) (L : ℤ) :
    Valley4 (armRefl (L + (L + 9)) f) L ↔ Ceil4R f L := by
  simp only [Valley4, Ceil4R, armRefl_apply]
  constructor
  · intro h d hd
    obtain ⟨j, h1, h2, h3⟩ := h d (by omega)
    exact ⟨j, h1, h2, by omega⟩
  · intro h d hd
    obtain ⟨j, h1, h2, h3⟩ := h d (by omega)
    exact ⟨j, h1, h2, by omega⟩

theorem leg3Ceil_armRefl {m : ℕ} (f : Fin m → ℤ) (L : ℤ) :
    Leg3Ceil (armRefl (L + (L + 9)) f) L ↔ Floor3R f L := by
  simp only [Leg3Ceil, Floor3R, armRefl_apply]
  constructor
  · intro h d hd
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := h d (by omega)
    exact ⟨j, k, h1, h2, h3, by omega, by omega⟩
  · intro h d hd
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := h d (by omega)
    exact ⟨j, k, h1, h2, h3, by omega, by omega⟩

theorem leg3Land_armRefl {m : ℕ} (f : Fin m → ℤ) (L : ℤ) :
    Leg3Land (armRefl (L + (L + 9)) f) L ↔ Leg3LandR f L := by
  rw [Leg3Land, Leg3LandR, ← leg3Ceil_armRefl f L, ← valley4_armRefl f L, Valley4]

theorem midW4_armRefl {m : ℕ} (f : Fin m → ℤ) (L : ℤ) :
    MidW4 (armRefl (L + (L + 9)) f) L ↔ MidW4R f L := by
  simp only [MidW4, MidW4R, armRefl_apply]
  constructor
  · intro h d hd
    obtain ⟨j, h1, h2, h3⟩ := h d (by omega)
    exact ⟨j, h1, h2, by omega⟩
  · intro h d hd
    obtain ⟨j, h1, h2, h3⟩ := h d (by omega)
    exact ⟨j, h1, h2, by omega⟩

theorem ceilW4_armRefl {m : ℕ} (f : Fin m → ℤ) (L : ℤ) :
    CeilW4 (armRefl (L + (L + 9)) f) L ↔ FloorW4R f L := by
  simp only [CeilW4, FloorW4R, armRefl_apply]
  constructor
  · intro h d hd
    obtain ⟨j, h1, h2, h3⟩ := h d (by omega)
    exact ⟨j, h1, h2, by omega⟩
  · intro h d hd
    obtain ⟨j, h1, h2, h3⟩ := h d (by omega)
    exact ⟨j, h1, h2, by omega⟩

theorem bottomW4_armRefl {m : ℕ} (f : Fin m → ℤ) (L : ℤ) :
    BottomW4 (armRefl (L + (L + 9)) f) L ↔ TopW4R f L := by
  simp only [BottomW4, TopW4R, armRefl_apply]
  constructor
  · intro h d hd
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := h d (by omega)
    exact ⟨j, k, h1, h2, h3, by omega, by omega⟩
  · intro h d hd
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := h d (by omega)
    exact ⟨j, k, h1, h2, h3, by omega, by omega⟩

theorem valley5_armRefl {m : ℕ} (f : Fin m → ℤ) (L : ℤ) :
    Valley5 (armRefl (L + (L + 9)) f) L ↔ Ceil5R f L := by
  simp only [Valley5, Ceil5R, armRefl_apply]
  constructor
  · intro h d hd
    obtain ⟨j, h1, h2, h3⟩ := h d (by omega)
    exact ⟨j, h1, h2, by omega⟩
  · intro h d hd
    obtain ⟨j, h1, h2, h3⟩ := h d (by omega)
    exact ⟨j, h1, h2, by omega⟩

theorem topW5_armRefl {m : ℕ} (f : Fin m → ℤ) (L : ℤ) :
    TopW5 (armRefl (L + (L + 9)) f) L ↔ BottomW5R f L := by
  simp only [TopW5, BottomW5R, armRefl_apply]
  constructor
  · intro h d hd
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := h d (by omega)
    exact ⟨j, k, h1, h2, h3, by omega, by omega⟩
  · intro h d hd
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := h d (by omega)
    exact ⟨j, k, h1, h2, h3, by omega, by omega⟩

/-! ## The three criteria at the basepoint `L + 5` -/

/-- The reflected arm is based at `L + 4`. -/
theorem armRefl_base {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 5) :
    armRefl (L + (L + 9)) f ⟨0, hm⟩ = L + 4 := by
  simp only [armRefl_apply, h0]; ring

/-- The reflected arm stays in the band. -/
theorem armRefl_lb {m : ℕ} (f : Fin m → ℤ) (L : ℤ) (hH : ∀ j, f j ≤ L + 9) :
    ∀ j, L ≤ armRefl (L + (L + 9)) f j := by
  intro j; have := hH j; simp only [armRefl_apply]; omega

/-- The reflected arm stays in the band. -/
theorem armRefl_ub {m : ℕ} (f : Fin m → ℤ) (L : ℤ) (hL : ∀ j, L ≤ f j) :
    ∀ j, armRefl (L + (L + 9)) f j ≤ L + 9 := by
  intro j; have := hL j; simp only [armRefl_apply]; omega

/-- **The criterion for the reflection of `w₃`.** For a 1-Lipschitz arm of the band based at
`L + 5`, folding onto `L+6 → L+3 → L+8 → L+1` is equivalent to the reflected landmark sentence. -/
theorem foldsOnto_w3R_iff_landmark {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) :
    FoldsOnto f (leg3Len L (L + 9) (L + 6) (L + 4)) (leg3Walk' L (L + 9) (L + 6) (L + 5)) ↔
      Leg3LandR f L := by
  rw [w3R_eq L, foldsOnto_armRefl' (L + (L + 9)) f,
    foldsOnto_leg3deep_iff_landmark hm (armRefl (L + (L + 9)) f) (armRefl_isLip hf _) L
      (armRefl_base hm f L h0) (armRefl_lb f L hH) (armRefl_ub f L hL),
    leg3Land_armRefl f L]

/-- **The criterion for the reflection of `w₄`.** -/
theorem foldsOnto_w4R_iff_landmark {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) :
    FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 7)) (leg3Walk L (L + 9) (L + 7) (L + 7)) ↔
      (MidW4R f L ∧ FloorW4R f L ∧ TopW4R f L) := by
  rw [w4R_eq L, foldsOnto_armRefl' (L + (L + 9)) f,
    foldsOnto_w4_iff_landmark hm (armRefl (L + (L + 9)) f) (armRefl_isLip hf _) L
      (armRefl_base hm f L h0) (armRefl_lb f L hH) (armRefl_ub f L hL),
    midW4_armRefl f L, ceilW4_armRefl f L, bottomW4_armRefl f L]

/-- **Two clauses suffice for the reflection of `w₄`**, as they do for `w₄` itself. -/
theorem foldsOnto_w4R_of_mid_top {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hmid : MidW4R f L) (htop : TopW4R f L) :
    FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 7)) (leg3Walk L (L + 9) (L + 7) (L + 7)) := by
  rw [w4R_eq L, foldsOnto_armRefl' (L + (L + 9)) f]
  exact foldsOnto_w4_profile_min hm (armRefl (L + (L + 9)) f) (armRefl_isLip hf _) L
    (armRefl_base hm f L h0) (armRefl_lb f L hH) (armRefl_ub f L hL)
    (midW4Min_of_midW4 ((midW4_armRefl f L).2 hmid))
    (bottomW4Min_of_bottomW4 ((bottomW4_armRefl f L).2 htop))

/-- **The criterion for the reflection of `w₅`.** -/
theorem foldsOnto_w5R_iff_landmark {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) :
    FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 4)) (leg3Walk' L (L + 9) (L + 7) (L + 5)) ↔
      (Ceil5R f L ∧ BottomW5R f L) := by
  rw [w5R_eq L, foldsOnto_armRefl' (L + (L + 9)) f,
    foldsOnto_w5_iff_landmark hm (armRefl (L + (L + 9)) f) (armRefl_isLip hf _) L
      (armRefl_base hm f L h0) (armRefl_lb f L hH) (armRefl_ub f L hL),
    valley5_armRefl f L, topW5_armRefl f L]

/-! ## The sentence of the three reflected walks -/

/-- **The sentence of the three walks at the basepoint `L + 5`**: the reflection of
`ThreeWalksSentence`. -/
def ThreeWalksSentence5 {mg mt : ℕ} (g : Fin mg → ℤ) (t : Fin mt → ℤ) (L : ℤ) : Prop :=
  (Leg3LandR g L ∧ Leg3LandR t L) ∨
  ((MidW4R g L ∧ TopW4R g L) ∧ (MidW4R t L ∧ TopW4R t L)) ∨
  ((Ceil5R g L ∧ BottomW5R g L) ∧ (Ceil5R t L ∧ BottomW5R t L))

/-- **The sentence of the branch `L + 5` is the reflection of the sentence of the branch
`L + 4`.** -/
theorem threeWalksSentence5_armRefl {mg mt : ℕ} (g : Fin mg → ℤ) (t : Fin mt → ℤ) (L : ℤ) :
    ThreeWalksSentence (armRefl (L + (L + 9)) g) (armRefl (L + (L + 9)) t) L ↔
      ThreeWalksSentence5 g t L := by
  rw [ThreeWalksSentence, ThreeWalksSentence5, leg3Land_armRefl g L, leg3Land_armRefl t L,
    midW4_armRefl g L, midW4_armRefl t L, bottomW4_armRefl g L, bottomW4_armRefl t L,
    valley5_armRefl g L, valley5_armRefl t L, topW5_armRefl g L, topW5_armRefl t L]

/-- **Three walks, at the basepoint `L + 5`.** For two 1-Lipschitz arms of the band based at
`L + 5`, the two arms fold onto one of the three reflected walks — both onto the same one —
exactly when one of the three reflected landmark sentences holds of both. -/
theorem three_walks5_iff_sentence {mg mt : ℕ} (hg : 0 < mg) (ht : 0 < mt)
    (g : Fin mg → ℤ) (t : Fin mt → ℤ) (hglip : IsLip g) (htlip : IsLip t) (L : ℤ)
    (hg0 : g ⟨0, hg⟩ = L + 5) (ht0 : t ⟨0, ht⟩ = L + 5)
    (hgL : ∀ j, L ≤ g j) (hgH : ∀ j, g j ≤ L + 9)
    (htL : ∀ j, L ≤ t j) (htH : ∀ j, t j ≤ L + 9) :
    ((FoldsOnto g (leg3Len L (L + 9) (L + 6) (L + 4)) (leg3Walk' L (L + 9) (L + 6) (L + 5)) ∧
        FoldsOnto t (leg3Len L (L + 9) (L + 6) (L + 4)) (leg3Walk' L (L + 9) (L + 6) (L + 5))) ∨
      (FoldsOnto g (leg3Len L (L + 9) (L + 7) (L + 7)) (leg3Walk L (L + 9) (L + 7) (L + 7)) ∧
        FoldsOnto t (leg3Len L (L + 9) (L + 7) (L + 7)) (leg3Walk L (L + 9) (L + 7) (L + 7))) ∨
      (FoldsOnto g (leg3Len L (L + 9) (L + 7) (L + 4)) (leg3Walk' L (L + 9) (L + 7) (L + 5)) ∧
        FoldsOnto t (leg3Len L (L + 9) (L + 7) (L + 4)) (leg3Walk' L (L + 9) (L + 7) (L + 5)))) ↔
      ThreeWalksSentence5 g t L := by
  have hw3g := foldsOnto_w3R_iff_landmark hg g hglip L hg0 hgL hgH
  have hw3t := foldsOnto_w3R_iff_landmark ht t htlip L ht0 htL htH
  have hw4g := foldsOnto_w4R_iff_landmark hg g hglip L hg0 hgL hgH
  have hw4t := foldsOnto_w4R_iff_landmark ht t htlip L ht0 htL htH
  have hw5g := foldsOnto_w5R_iff_landmark hg g hglip L hg0 hgL hgH
  have hw5t := foldsOnto_w5R_iff_landmark ht t htlip L ht0 htL htH
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨hw3g.1 h1, hw3t.1 h2⟩
    · obtain ⟨hm1, -, hb1⟩ := hw4g.1 h1
      obtain ⟨hm2, -, hb2⟩ := hw4t.1 h2
      exact Or.inr (Or.inl ⟨⟨hm1, hb1⟩, ⟨hm2, hb2⟩⟩)
    · exact Or.inr (Or.inr ⟨hw5g.1 h1, hw5t.1 h2⟩)
  · rintro (⟨h1, h2⟩ | ⟨⟨hm1, hb1⟩, ⟨hm2, hb2⟩⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨hw3g.2 h1, hw3t.2 h2⟩
    · exact Or.inr (Or.inl
        ⟨foldsOnto_w4R_of_mid_top hg g hglip L hg0 hgL hgH hm1 hb1,
          foldsOnto_w4R_of_mid_top ht t htlip L ht0 htL htH hm2 hb2⟩)
    · exact Or.inr (Or.inr ⟨hw5g.2 h1, hw5t.2 h2⟩)

/-- **The branch `L + 5` from the sentence.** If an unserved pair of the branch satisfies the
reflected sentence, the branch is complete: this is `s3_span_nine_mid4_of_sentence` read through
the reflection, with the two canonical walks replaced by *their* reflections — the Λ-walk based at
`L + 4` and the V-walk based at `L + 6`. -/
theorem s3_span_nine_mid5_of_sentence {m : ℕ} (ρ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 5)
    (hsent :
      ¬ (FoldsOnto (armG ρ i) (lamLen (L + 4) (L + 9) L) (lamCenter (L + 4) (L + 9) L) ∧
          FoldsOnto (armT ρ i) (lamLen (L + 4) (L + 9) L) (lamCenter (L + 4) (L + 9) L)) →
      ¬ (FoldsOnto (armG ρ i) (veeLen (L + 6) (L + 9) L) (veeCenter (L + 6) (L + 9) L) ∧
          FoldsOnto (armT ρ i) (veeLen (L + 6) (L + 9) L) (veeCenter (L + 6) (L + 9) L)) →
      ThreeWalksSentence5 (armG ρ i) (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ), FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hi := i.isLt
  have hmG : 0 < m - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 5 := by
    rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 5 := by
    rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  by_cases hlam : FoldsOnto (armG ρ i) (lamLen (L + 4) (L + 9) L) (lamCenter (L + 4) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 4) (L + 9) L) (lamCenter (L + 4) (L + 9) L)
  · exact ⟨_, _, hlam.1, hlam.2⟩
  · by_cases hvee : FoldsOnto (armG ρ i) (veeLen (L + 6) (L + 9) L)
        (veeCenter (L + 6) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (veeLen (L + 6) (L + 9) L) (veeCenter (L + 6) (L + 9) L)
    · exact ⟨_, _, hvee.1, hvee.2⟩
    · rcases (three_walks5_iff_sentence hmG hmT (armG ρ i) (armT ρ i) (armG_isLip hlip i)
        (armT_isLip hlip i) L hG0 hT0 (fun j => hLb _) (fun j => hHb _) (fun j => hLb _)
        (fun j => hHb _)).2 (hsent hlam hvee) with ⟨hfG, hfT⟩ | ⟨hfG, hfT⟩ | ⟨hfG, hfT⟩
      · exact ⟨_, _, hfG, hfT⟩
      · exact ⟨_, _, hfG, hfT⟩
      · exact ⟨_, _, hfG, hfT⟩

/-! ## The reflected crookedness clauses

`CrookUp` and `CrookDown` are *not* reflections of one another: the reflection of `CrookDown` is
`CrookUpR`, whose two windows sit one level above those of `CrookUp`, and the reflection of
`CrookUp` is `CrookDownR`. The dichotomies of the branch `L + 4` reflect only with these clauses
in place of the model's own. -/

/-- **The reflection of `CrookDown`.** Between a time and a later time three or more levels above
it, the arm has been *at* the upper level or one below, and after that at the lower level or one
above. `CrookUp` asks the same with both windows one level lower. -/
def CrookUpR {m : ℕ} (f : Fin m → ℤ) : Prop :=
  ∀ s t : Fin m, s.val < t.val → f s + 3 ≤ f t →
    ∃ u u' : Fin m, s.val < u.val ∧ u.val < u'.val ∧ u'.val < t.val ∧
      f t - 1 ≤ f u ∧ f u ≤ f t ∧ f s + 1 ≤ f u' ∧ f u' ≤ f s + 2

/-- **The reflection of `CrookUp`.** -/
def CrookDownR {m : ℕ} (f : Fin m → ℤ) : Prop :=
  ∀ s t : Fin m, s.val < t.val → f t + 3 ≤ f s →
    ∃ u u' : Fin m, s.val < u.val ∧ u.val < u'.val ∧ u'.val < t.val ∧
      f t + 1 ≤ f u ∧ f u ≤ f t + 2 ∧ f s - 1 ≤ f u' ∧ f u' ≤ f s

theorem crookUpR_iff_crookDown_armRefl {m : ℕ} (f : Fin m → ℤ) (a : ℤ) :
    CrookUpR f ↔ CrookDown (armRefl a f) := by
  simp only [CrookUpR, CrookDown, armRefl_apply]
  constructor
  · intro h s t hst hlev
    obtain ⟨u, u', h1, h2, h3, h4, h5, h6, h7⟩ := h s t hst (by omega)
    exact ⟨u, u', h1, h2, h3, by omega, by omega, by omega, by omega⟩
  · intro h s t hst hlev
    obtain ⟨u, u', h1, h2, h3, h4, h5, h6, h7⟩ := h s t hst (by omega)
    exact ⟨u, u', h1, h2, h3, by omega, by omega, by omega, by omega⟩

theorem crookDownR_iff_crookUp_armRefl {m : ℕ} (f : Fin m → ℤ) (a : ℤ) :
    CrookDownR f ↔ CrookUp (armRefl a f) := by
  simp only [CrookDownR, CrookUp, armRefl_apply]
  constructor
  · intro h s t hst hlev
    obtain ⟨u, u', h1, h2, h3, h4, h5, h6, h7⟩ := h s t hst (by omega)
    exact ⟨u, u', h1, h2, h3, by omega, by omega, by omega, by omega⟩
  · intro h s t hst hlev
    obtain ⟨u, u', h1, h2, h3, h4, h5, h6, h7⟩ := h s t hst (by omega)
    exact ⟨u, u', h1, h2, h3, by omega, by omega, by omega, by omega⟩

/-- **The reflection of `valley4_or_vee`.** An arm based at `L + 5` satisfying the reflected
down-clause either meets the reflected ceiling clause of `w₃` or folds onto the Λ-walk based at
`L + 4`. -/
theorem ceil4R_or_lam {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (hcr : CrookUpR f)
    (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) :
    Ceil4R f L ∨ FoldsOnto f (lamLen (L + 4) (L + 9) L) (lamCenter (L + 4) (L + 9) L) := by
  rcases valley4_or_vee hm (armRefl (L + (L + 9)) f) (armRefl_isLip hf _)
    ((crookUpR_iff_crookDown_armRefl f (L + (L + 9))).1 hcr) L (armRefl_base hm f L h0)
    (armRefl_lb f L hH) (armRefl_ub f L hL) with h | h
  · exact Or.inl ((valley4_armRefl f L).1 h)
  · refine Or.inr ?_
    have e : lamLen (L + 4) (L + 9) L = veeLen (L + 5) (L + 9) L := by
      have := lamLen_armRefl (L + 5) (L + 9) L
      rw [show L + (L + 9) - (L + 5) = L + 4 from by ring] at this
      exact this
    have ec : lamCenter (L + 4) (L + 9) L =
        fun u => (L + (L + 9)) - veeCenter (L + 5) (L + 9) L u := by
      funext u
      have := lamCenter_armRefl (L + 5) (L + 9) L u
      rw [show L + (L + 9) - (L + 5) = L + 4 from by ring] at this
      exact this
    rw [e, ec, foldsOnto_armRefl' (L + (L + 9)) f]
    exact h

/-- **The reflection of `leg3Ceil_or_lam`.** An arm based at `L + 5` satisfying both reflected
clauses either meets the reflected floor clause of `w₃` or folds onto the V-walk based at
`L + 6`. -/
theorem floor3R_or_vee {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (hcru : CrookDownR f)
    (hcrd : CrookUpR f) (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j)
    (hH : ∀ j, f j ≤ L + 9) :
    Floor3R f L ∨ FoldsOnto f (veeLen (L + 6) (L + 9) L) (veeCenter (L + 6) (L + 9) L) := by
  rcases leg3Ceil_or_lam hm (armRefl (L + (L + 9)) f) (armRefl_isLip hf _)
    ((crookDownR_iff_crookUp_armRefl f (L + (L + 9))).1 hcru)
    ((crookUpR_iff_crookDown_armRefl f (L + (L + 9))).1 hcrd) L (armRefl_base hm f L h0)
    (armRefl_lb f L hH) (armRefl_ub f L hL) with h | h
  · exact Or.inl ((leg3Ceil_armRefl f L).1 h)
  · refine Or.inr ?_
    have e : veeLen (L + 6) (L + 9) L = lamLen (L + 3) (L + 9) L := by
      have := veeLen_armRefl (L + 3) (L + 9) L
      rw [show L + (L + 9) - (L + 3) = L + 6 from by ring] at this
      exact this
    have ec : veeCenter (L + 6) (L + 9) L =
        fun u => (L + (L + 9)) - lamCenter (L + 3) (L + 9) L u := by
      funext u
      have := veeCenter_armRefl (L + 3) (L + 9) L u
      rw [show L + (L + 9) - (L + 3) = L + 6 from by ring] at this
      exact this
    rw [e, ec, foldsOnto_armRefl' (L + (L + 9)) f]
    exact h

/-- **What is left of the branch `L + 5` is a crossing**, exactly as at the branch `L + 4`: either
both arms meet the two clauses of the reflected `w₃` — and then both fold onto it — or some arm
fails one of them and is served by a canonical walk on its own. The hypotheses are the reflected
crookedness clauses, which is where the reflection of the branch `L + 4` stops being free. -/
theorem three_walks5_or_cross {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (hcru : CrookDownR f) (hcrd : CrookUpR f) (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 5)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) :
    Leg3LandR f L ∨
      FoldsOnto f (lamLen (L + 4) (L + 9) L) (lamCenter (L + 4) (L + 9) L) ∨
      FoldsOnto f (veeLen (L + 6) (L + 9) L) (veeCenter (L + 6) (L + 9) L) := by
  rcases ceil4R_or_lam hm f hf hcrd L h0 hL hH with hc | h
  · rcases floor3R_or_vee hm f hf hcru hcrd L h0 hL hH with hfl | h
    · exact Or.inl ⟨hc, hfl⟩
    · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

end HPC.Fold
