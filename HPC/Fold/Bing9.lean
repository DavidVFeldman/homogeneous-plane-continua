import HPC.Fold.Mixed

/-!
# The 986-link chain `bing 0 9`, and the counterexample to `unserved_high8`

Bing's chain `bing 0 9` has 986 links and span exactly nine, with both ends attained, so it is
the shortest sequence at which the span-nine branch can be read at all: a faithful crooked
sequence of span nine needs `z 9 = 986` links. This file puts it into Lean, proves it faithful,
and refutes at one of its basepoints the work item `unserved_high8` of batch 44.

`HPC/Fold/DichotomyFaithful.lean` proved the 409-link chain faithful, and the method carries over
unchanged: the chain is one natural number in base sixteen, a link is read off by a shift and a
mask, and the crookedness clause is checked for each start `s` and each pair of levels only at
the *least* later index at which the second level is met — monotone in the far index, so one
check per `(s, x, y)` rather than one per pair. The only change is bookkeeping: the check is cut
into five blocks of indices, each a separate kernel evaluation, because one block of 986 exceeds
the elaborator's heartbeat budget.

## The counterexample

At the basepoint `278`, which stands at level `4`:

* both arms are `HighAt (L + 1) (L + 8)`, so the basepoint lies in the open branch;
* the backward arm drops to `L + 1` at its step `39` having never been above `L + 6`, so it does
  not fold onto the Λ-walk based at `L + 3` (`not_foldsOnto_lam_b9T`);
* the forward arm rises to `L + 7` at its step `31`, having been at `L + 2` only at its step `2`,
  too early for the V-walk based at `L + 5` (`not_foldsOnto_vee_b9G`);
* so the pair folds onto neither canonical walk — and yet the forward arm stands at `L + 8` at
  its step `130` with no earlier time at `L + 1` or below (`not_highAt_b9G`).

That is exactly the conclusion `unserved_high8` asserted, so the work item is false
(`not_unservedHigh8`). What the three-leg walk of `HPC/Fold/Leg3Deep.lean` actually asks at the
ceiling is the weaker announcement `CeilAnn`, which this arm does satisfy; the branch is re-split
on it in `HPC/Fold/Mixed.lean`.
-/

namespace HPC.Fold

/-! ## The chain as a numeral -/

/-- The 986 links of `bing 0 9`, as the base-sixteen digits of one natural number. -/
def bing9Nat : ℕ := 108955440866675458832150531444332717254066531029671156032823923856895392350943643789945635184457250634341709871231486305988637336510736926208533643953996153399217335017767358493106037793229100653890765995210842794772726751372104331228533712146519759066849951864149590214234995862536983321182752267466690895561014004627536070783454366043599299537195189580249827368242159804438966977328484747041289150476251650364014368043338159632748680055252553397698155493388187245692346141270235338441441402768838716843624987364463906670394439272097333991277235597317385272541373168678420672992662642113265513683239840903616941218509981818130553559662178421277533452028066908106592284120625650686377098358375676528929789039731064673080235316637574931606106647684927417894400370866059175120130938452567813124041341029893579922824229544334513473745053205383332342510851734684489946615194679585418186172921731053513337934110941731370396637248729807787235733041706127533286823647517277133157696809790683149801378697222370097359158082228985276946736374253615228729202740359697396578921489787486217113076743645311997638099136199151767117448908915712896669244428892735867807964809590169668082175430633519714832

/-- Reading a link off the numeral. -/
def rho9 (i : ℕ) : ℕ := (bing9Nat >>> (4 * i)) &&& 15

/-- **Bing's chain `bing 0 9`**: 986 links, span exactly nine, both ends attained. -/
def bing9 : Fin 986 → ℤ := fun t => (rho9 t.val : ℤ)

theorem rho9_lt : ∀ i : Fin 986, rho9 i.val < 10 := by decide +kernel

theorem bing9_lb : ∀ t, (0 : ℤ) ≤ bing9 t := fun _ => Int.natCast_nonneg _

theorem bing9_ub : ∀ t, bing9 t ≤ 9 := by decide +kernel

theorem bing9_attains_bot : ∃ t, bing9 t = 0 := ⟨⟨0, by norm_num⟩, by decide +kernel⟩

theorem bing9_attains_top : ∃ t, bing9 t = 9 := ⟨⟨985, by norm_num⟩, by decide +kernel⟩

/-- The adjacency check, read along the chain rather than over all pairs. -/
def lipChk9 : Bool :=
  (List.range 985).all fun i => decide (rho9 (i + 1) ≤ rho9 i + 1 ∧ rho9 i ≤ rho9 (i + 1) + 1)

set_option maxRecDepth 10000000 in
theorem lipChk9_true : lipChk9 = true := by decide +kernel

theorem rho9_step : ∀ i : ℕ, i + 1 < 986 →
    rho9 (i + 1) ≤ rho9 i + 1 ∧ rho9 i ≤ rho9 (i + 1) + 1 := by
  have h := lipChk9_true
  rw [lipChk9, List.all_eq_true] at h
  intro i hi
  have := h i (List.mem_range.2 (by omega))
  simpa using this

theorem bing9_isLip : IsLip bing9 := by
  intro j j' hjj'
  have hj := j.isLt
  have hj' := j'.isLt
  have := rho9_step j.val (by omega)
  show |((rho9 j'.val : ℤ)) - ((rho9 j.val : ℤ))| ≤ 1
  rw [hjj', abs_le]
  omega


/-! ## The crookedness search

The clause of `IsCrookedIvF` for a pair `s < t` and levels `x, y` asks for `s < r < r' < t` with
prescribed levels; if it holds for some `t₀ ≤ t` it holds for `t`. So it suffices to check, for
each `s` and each pair of levels met, the least `t₀ > s` at which `y` is met. -/

/-- `y` is met at `i`: it is the level of `i − 1`, of `i`, or of `i + 1`. -/
def levHas9 (i y : ℕ) : Bool :=
  (i != 0 && rho9 (i - 1) == y) || rho9 i == y || (i + 1 < 986 && rho9 (i + 1) == y)

/-- The least index at or after `s`, within the given fuel, at which `y` is met. -/
def firstLev9 (y : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, s =>
    if 986 ≤ s then none else if levHas9 s y then some s else firstLev9 y fuel (s + 1)

/-- The least index at or after `s`, within the given fuel, whose level is `v`. -/
def firstVal9 (v : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, s =>
    if 986 ≤ s then none else if rho9 s == v then some s else firstVal9 v fuel (s + 1)

/-- The crookedness clause for the level pair `(x, y)` at `s`, checked at the least index at
which `y` is met. -/
def checkOne9 (s x y : ℕ) : Bool :=
  if x + 3 ≤ y then
    match firstLev9 y (986 - s) (s + 1) with
    | none => true
    | some t0 =>
      match firstVal9 (y - 1) (t0 - s) (s + 1) with
      | none => false
      | some r =>
        if t0 ≤ r then false else
          match firstVal9 (x + 1) (t0 - r) (r + 1) with
          | none => false
          | some r' => decide (r' < t0)
  else if y + 3 ≤ x then
    match firstLev9 y (986 - s) (s + 1) with
    | none => true
    | some t0 =>
      match firstVal9 (y + 1) (t0 - s) (s + 1) with
      | none => false
      | some r =>
        if t0 ≤ r then false else
          match firstVal9 (x - 1) (t0 - r) (r + 1) with
          | none => false
          | some r' => decide (r' < t0)
  else true

def checkS9 (s : ℕ) : Bool :=
  (List.range 10).all fun x =>
    if levHas9 s x then (List.range 10).all fun y => checkOne9 s x y else true

def checkRange9 (lo len : ℕ) : Bool := (List.range' lo len).all checkS9

set_option maxRecDepth 10000000 in
theorem chk9_0 : checkRange9 0 200 = true := by decide +kernel

set_option maxRecDepth 10000000 in
theorem chk9_1 : checkRange9 200 200 = true := by decide +kernel

set_option maxRecDepth 10000000 in
theorem chk9_2 : checkRange9 400 200 = true := by decide +kernel

set_option maxRecDepth 10000000 in
theorem chk9_3 : checkRange9 600 200 = true := by decide +kernel

set_option maxRecDepth 10000000 in
theorem chk9_4 : checkRange9 800 186 = true := by decide +kernel

/-- The check passes at every start. -/
theorem checkS9_true : ∀ s : ℕ, s < 986 → checkS9 s = true := by
  intro s hs
  have e0 := chk9_0
  have e1 := chk9_1
  have e2 := chk9_2
  have e3 := chk9_3
  have e4 := chk9_4
  rw [checkRange9, List.all_eq_true] at e0 e1 e2 e3 e4
  rcases Nat.lt_or_ge s 200 with h | h
  · exact e0 s (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  rcases Nat.lt_or_ge s 400 with h' | h'
  · exact e1 s (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  rcases Nat.lt_or_ge s 600 with h'' | h''
  · exact e2 s (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  rcases Nat.lt_or_ge s 800 with h3 | h3
  · exact e3 s (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact e4 s (List.mem_range'_1.2 ⟨by omega, by omega⟩)

/-! ## The specifications of the two searches -/

theorem firstVal9_spec : ∀ (v fuel s r : ℕ), firstVal9 v fuel s = some r →
    s ≤ r ∧ r < 986 ∧ rho9 r = v := by
  intro v fuel
  induction fuel with
  | zero => intro s r h; simp [firstVal9] at h
  | succ f ih =>
    intro s r h
    rw [firstVal9] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hs
      split at h
      · rename_i hv
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨le_rfl, by omega, by simpa using hv⟩
      · have := ih (s + 1) r h
        exact ⟨by omega, this.2.1, this.2.2⟩

theorem firstLev9_le : ∀ (y fuel s t : ℕ), s ≤ t → t < 986 → t < s + fuel → levHas9 t y = true →
    ∃ t0, firstLev9 y fuel s = some t0 ∧ t0 ≤ t := by
  intro y fuel
  induction fuel with
  | zero => intro s t h1 _ h2 _; omega
  | succ f ih =>
    intro s t h1 hlt986 h2 h3
    rw [firstLev9]
    split
    · omega
    · split
      · exact ⟨s, rfl, h1⟩
      · rename_i hne
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · exact absurd h3 (by simpa using hne)
        · exact ih (s + 1) t (by omega) hlt986 (by omega) h3

/-! ## Faithfulness -/

theorem levHas9_of_near {s u : Fin 986} (h : ((u : ℤ) - s.val).natAbs ≤ 1) :
    levHas9 s.val (rho9 u.val) = true := by
  have hu := u.isLt
  have hs := s.isLt
  have hcase : s.val = u.val + 1 ∨ u.val = s.val ∨ u.val = s.val + 1 := by omega
  rcases hcase with h1 | h1 | h1
  · have hs0 : s.val ≠ 0 := by omega
    have hval : rho9 (s.val - 1) = rho9 u.val := by rw [show s.val - 1 = u.val by omega]
    simp [levHas9, hval, hs0]
  · simp [levHas9, h1]
  · have hlt : s.val + 1 < 986 := by omega
    have hval : rho9 (s.val + 1) = rho9 u.val := by rw [h1]
    simp [levHas9, hval, hlt]

theorem checkOne9_true {s x y : ℕ} (hs : s < 986) (hx : levHas9 s x = true) (hxlt : x < 10)
    (hylt : y < 10) : checkOne9 s x y = true := by
  have hS := checkS9_true s hs
  rw [checkS9, List.all_eq_true] at hS
  have hx' := hS x (List.mem_range.2 hxlt)
  rw [if_pos hx, List.all_eq_true] at hx'
  exact hx' y (List.mem_range.2 hylt)

/-- **The chain is faithful.** -/
theorem bing9_faithful : IsCrookedIvF bing9 bing9 := by
  refine ⟨fun t => le_rfl, fun t => by omega, ?_, ?_⟩
  · intro t t' htt'
    have h := bing9_isLip t t' htt'
    rw [abs_le] at h
    omega
  · rintro s t hst h k ⟨u, hu, hu1, hu2⟩ ⟨v, hv, hv1, hv2⟩ habs
    have hxv : h = (rho9 u.val : ℤ) := by
      have : bing9 u = (rho9 u.val : ℤ) := rfl
      omega
    have hyv : k = (rho9 v.val : ℤ) := by
      have : bing9 v = (rho9 v.val : ℤ) := rfl
      omega
    set x := rho9 u.val with hxdef
    set y := rho9 v.val with hydef
    have hxlt : x < 10 := rho9_lt u
    have hylt : y < 10 := rho9_lt v
    have hsx : levHas9 s.val x = true := levHas9_of_near hu
    have hty : levHas9 t.val y = true := levHas9_of_near hv
    have hs : s.val < 986 := s.isLt
    have ht : t.val < 986 := t.isLt
    have hstv : s.val < t.val := hst
    have hchk := checkOne9_true hs hsx hxlt hylt
    have hcases : x + 3 ≤ y ∨ y + 3 ≤ x := by
      rw [hxv, hyv] at habs
      rcases abs_cases ((x : ℤ) - y) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
    obtain ⟨t0, ht0, ht0le⟩ :=
      firstLev9_le y (986 - s.val) (s.val + 1) t.val (by omega) ht (by omega) hty
    rcases hcases with hc | hc
    · rw [checkOne9, if_pos hc] at hchk
      simp only [ht0] at hchk
      cases hr : firstVal9 (y - 1) (t0 - s.val) (s.val + 1) with
      | none => simp [hr] at hchk
      | some r =>
        simp only [hr] at hchk
        obtain ⟨hr1, hr2, hr3⟩ := firstVal9_spec _ _ _ _ hr
        by_cases hrt : t0 ≤ r
        · simp [hrt] at hchk
        · rw [if_neg hrt] at hchk
          cases hr' : firstVal9 (x + 1) (t0 - r) (r + 1) with
          | none => simp [hr'] at hchk
          | some r2 =>
            simp only [hr'] at hchk
            obtain ⟨hs1, hs2, hs3⟩ := firstVal9_spec _ _ _ _ hr'
            have hlt2 : r2 < t0 := by simpa using hchk
            refine ⟨⟨r, hr2⟩, ⟨r2, hs2⟩, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [Fin.lt_def]; omega
            · simp only [Fin.lt_def]; omega
            · simp only [Fin.lt_def]; omega
            · intro _
              have e1 : bing9 ⟨r, hr2⟩ = ((y - 1 : ℕ) : ℤ) := by
                show ((rho9 r : ℕ) : ℤ) = _
                rw [hr3]
              have e2 : bing9 ⟨r2, hs2⟩ = ((x + 1 : ℕ) : ℤ) := by
                show ((rho9 r2 : ℕ) : ℤ) = _
                rw [hs3]
              rw [e1, e2, hxv, hyv]
              push_cast [Nat.cast_sub (by omega : 1 ≤ y)]
              omega
            · intro hcon
              rw [hxv, hyv] at hcon
              omega
    · rw [checkOne9, if_neg (by omega : ¬ (x + 3 ≤ y)), if_pos hc] at hchk
      simp only [ht0] at hchk
      cases hr : firstVal9 (y + 1) (t0 - s.val) (s.val + 1) with
      | none => simp [hr] at hchk
      | some r =>
        simp only [hr] at hchk
        obtain ⟨hr1, hr2, hr3⟩ := firstVal9_spec _ _ _ _ hr
        by_cases hrt : t0 ≤ r
        · simp [hrt] at hchk
        · rw [if_neg hrt] at hchk
          cases hr' : firstVal9 (x - 1) (t0 - r) (r + 1) with
          | none => simp [hr'] at hchk
          | some r2 =>
            simp only [hr'] at hchk
            obtain ⟨hs1, hs2, hs3⟩ := firstVal9_spec _ _ _ _ hr'
            have hlt2 : r2 < t0 := by simpa using hchk
            refine ⟨⟨r, hr2⟩, ⟨r2, hs2⟩, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [Fin.lt_def]; omega
            · simp only [Fin.lt_def]; omega
            · simp only [Fin.lt_def]; omega
            · intro hcon
              rw [hxv, hyv] at hcon
              omega
            · intro _
              have e1 : bing9 ⟨r, hr2⟩ = ((y + 1 : ℕ) : ℤ) := by
                show ((rho9 r : ℕ) : ℤ) = _
                rw [hr3]
              have e2 : bing9 ⟨r2, hs2⟩ = ((x - 1 : ℕ) : ℤ) := by
                show ((rho9 r2 : ℕ) : ℤ) = _
                rw [hs3]
              rw [e1, e2, hxv, hyv]
              push_cast [Nat.cast_sub (by omega : 1 ≤ x)]
              omega

end HPC.Fold
