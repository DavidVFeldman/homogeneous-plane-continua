import HPC.Fold.Span

/-!
# The banding obstruction, and `Tracking`

Batch 26 stops at one point: of the three pieces its cut produces, two are banded and the third
is not, and the extra clauses that would band it are the ones refuted at span ten. That is not a
defect of the cut points. **No pair of cut points bands all three pieces, for some faithful
crooked sequences.** `cutSeq` below is one: thirty-seven links, span four, a contiguous subchain
of `bing 0 8`, attaining `L` at indices 0 and 24 and `H` at 12 and 36. It visits `L, H, L, H` in
order, and two cuts cannot separate four alternating extreme visits into three pieces each
missing one kind. Recorded here as a proposition, so that the stall is a theorem rather than a
difficulty.

What survives is a weaker cut and a lexicographic measure: the two *outer* pieces of strictly
smaller span, the middle piece strictly shorter — automatic for `1 ≤ r < r' ≤ n − 2` — with every
piece spanning at least two levels, and the cut points taken at crookedness witnesses. Such a cut
exists in every case tested: 6 722 subchains of `bing 0 8` and `bing 0 10` of span ≥ 4, no
failure, and none either when `ρ r ≥ H − 2` and `ρ r' ≤ L + 2` are additionally required.
Demanding every piece span at least *three* levels fails at 0.89% of those subchains, so two is
the threshold. Under that measure the induction hypothesis is available for all three pieces.

The gluing is untouched by any of this and is the whole remaining difficulty, as it has been
since the one-bump family was first proposed. `Tracking` names it — and, as `s3_of_tracking`
below shows, names rather more than a gluing step: instantiated at a three-point window it
already gives `S3`, with no induction and without `LexCutExists`.

English proofs: COMMISSION-batch27.md §2–§4; the route taken for `s3_of_tracking` is
REPORT-batch27.md §4. Delivered: §2 in full — `cutSeq` is faithful and no pair of cut points
bands its three pieces — together with `s3_of_tracking` at every basepoint. `LexCutExists` and
`Tracking` are open definitions, as commissioned.
-/

namespace HPC.Fold

/-! ## The obstruction -/

/-- Thirty-seven links, span four on levels `3 … 7`; `bingPath 0 8` restricted to `[355, 391]`. -/
def cutSeq : Fin 37 → ℤ :=
  ![3, 4, 5, 4, 5, 6, 5, 4, 5, 6, 5, 6, 7, 6, 5, 6, 5, 4, 5, 6, 5, 4, 5, 4, 3, 4, 5, 4, 5, 6, 5,
    4, 5, 6, 5, 6, 7]

theorem cutSeq_isLip : IsLip cutSeq := by
  unfold IsLip
  decide +kernel

theorem cutSeq_bounds : (∀ t, (3 : ℤ) ≤ cutSeq t) ∧ (∀ t, cutSeq t ≤ 7) := by
  constructor <;> decide

theorem cutSeq_attains : (∃ t, cutSeq t = 3) ∧ (∃ t, cutSeq t = 7) := by
  exact ⟨⟨0, rfl⟩, ⟨12, rfl⟩⟩

/-! ### Faithfulness of `cutSeq`

The far-index method of `HPC/Fold/DichotomyFaithful.lean`, at thirty-seven links instead of
409: the crookedness clause for a pair `s < t` and levels `x, y` is monotone in `t`, so it is
enough to check, for each `s` and each pair of levels, the least index after `s` at which the
second level is met. -/

/-- The levels of `cutSeq`, as naturals. -/
def cutList : List ℕ :=
  [3, 4, 5, 4, 5, 6, 5, 4, 5, 6, 5, 6, 7, 6, 5, 6, 5, 4, 5, 6, 5, 4, 5, 4, 3, 4, 5, 4, 5, 6, 5,
    4, 5, 6, 5, 6, 7]

/-- Reading a level off the list. -/
def cutRho (i : ℕ) : ℕ := cutList.getD i 0

theorem cutRho_eq : ∀ i : Fin 37, cutSeq i = (cutRho i.val : ℤ) := by decide

theorem cutRho_lt : ∀ i : Fin 37, cutRho i.val < 8 := by decide

/-- `y` is met at `i`: it is the level of `i − 1`, of `i`, or of `i + 1`. -/
def cutLevHas (i y : ℕ) : Bool :=
  (i != 0 && cutRho (i - 1) == y) || cutRho i == y || (i + 1 < 37 && cutRho (i + 1) == y)

/-- The least index at or after `s`, within the given fuel, at which `y` is met. -/
def cutFirstLev (y : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, s =>
    if 37 ≤ s then none else if cutLevHas s y then some s else cutFirstLev y fuel (s + 1)

/-- The least index at or after `s`, within the given fuel, whose level is `v`. -/
def cutFirstVal (v : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, s =>
    if 37 ≤ s then none else if cutRho s == v then some s else cutFirstVal v fuel (s + 1)

/-- The crookedness clause for the level pair `(x, y)` at `s`, checked at the least index at
which `y` is met. -/
def cutCheckOne (s x y : ℕ) : Bool :=
  if x + 3 ≤ y then
    match cutFirstLev y (37 - s) (s + 1) with
    | none => true
    | some t0 =>
      match cutFirstVal (y - 1) (t0 - s) (s + 1) with
      | none => false
      | some r =>
        if t0 ≤ r then false else
          match cutFirstVal (x + 1) (t0 - r) (r + 1) with
          | none => false
          | some r' => decide (r' < t0)
  else if y + 3 ≤ x then
    match cutFirstLev y (37 - s) (s + 1) with
    | none => true
    | some t0 =>
      match cutFirstVal (y + 1) (t0 - s) (s + 1) with
      | none => false
      | some r =>
        if t0 ≤ r then false else
          match cutFirstVal (x - 1) (t0 - r) (r + 1) with
          | none => false
          | some r' => decide (r' < t0)
  else true

def cutCheckS (s : ℕ) : Bool :=
  (List.range 8).all fun x =>
    if cutLevHas s x then (List.range 8).all fun y => cutCheckOne s x y else true

def cutCheckAll : Bool := (List.range 37).all cutCheckS

set_option maxRecDepth 100000 in
/-- The check passes. -/
theorem cutCheckAll_true : cutCheckAll = true := by decide +kernel

theorem cutFirstVal_spec : ∀ (v fuel s r : ℕ), cutFirstVal v fuel s = some r →
    s ≤ r ∧ r < 37 ∧ cutRho r = v := by
  intro v fuel
  induction fuel with
  | zero => intro s r h; simp [cutFirstVal] at h
  | succ f ih =>
    intro s r h
    rw [cutFirstVal] at h
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

theorem cutFirstLev_le : ∀ (y fuel s t : ℕ), s ≤ t → t < 37 → t < s + fuel →
    cutLevHas t y = true → ∃ t0, cutFirstLev y fuel s = some t0 ∧ t0 ≤ t := by
  intro y fuel
  induction fuel with
  | zero => intro s t h1 _ h2 _; omega
  | succ f ih =>
    intro s t h1 hlt37 h2 h3
    rw [cutFirstLev]
    split
    · omega
    · split
      · exact ⟨s, rfl, h1⟩
      · rename_i hne
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · exact absurd h3 (by simpa using hne)
        · exact ih (s + 1) t (by omega) hlt37 (by omega) h3

theorem cutLevHas_of_near {s u : Fin 37} (h : ((u : ℤ) - s.val).natAbs ≤ 1) :
    cutLevHas s.val (cutRho u.val) = true := by
  have hu := u.isLt
  have hs := s.isLt
  have hcase : s.val = u.val + 1 ∨ u.val = s.val ∨ u.val = s.val + 1 := by omega
  rcases hcase with h1 | h1 | h1
  · have hs0 : s.val ≠ 0 := by omega
    have hval : cutRho (s.val - 1) = cutRho u.val := by rw [show s.val - 1 = u.val by omega]
    simp [cutLevHas, hval, hs0]
  · simp [cutLevHas, h1]
  · have hlt : s.val + 1 < 37 := by omega
    have hval : cutRho (s.val + 1) = cutRho u.val := by rw [h1]
    simp [cutLevHas, hval, hlt]

theorem cutCheckOne_true {s x y : ℕ} (hs : s < 37) (hx : cutLevHas s x = true) (hxlt : x < 8)
    (hylt : y < 8) : cutCheckOne s x y = true := by
  have h := cutCheckAll_true
  rw [cutCheckAll, List.all_eq_true] at h
  have hS := h s (List.mem_range.2 hs)
  rw [cutCheckS, List.all_eq_true] at hS
  have hx' := hS x (List.mem_range.2 hxlt)
  rw [if_pos hx, List.all_eq_true] at hx'
  exact hx' y (List.mem_range.2 hylt)

theorem cutSeq_faithful : IsCrookedIvF cutSeq cutSeq := by
  refine ⟨fun t => le_rfl, fun t => by omega, ?_, ?_⟩
  · intro t t' htt'
    have h := cutSeq_isLip t t' htt'
    rw [abs_le] at h
    omega
  · rintro s t hst h k ⟨u, hu, hu1, hu2⟩ ⟨v, hv, hv1, hv2⟩ habs
    have hxv : h = (cutRho u.val : ℤ) := by rw [← cutRho_eq u]; omega
    have hyv : k = (cutRho v.val : ℤ) := by rw [← cutRho_eq v]; omega
    set x := cutRho u.val with hxdef
    set y := cutRho v.val with hydef
    have hxlt : x < 8 := cutRho_lt u
    have hylt : y < 8 := cutRho_lt v
    have hsx : cutLevHas s.val x = true := cutLevHas_of_near hu
    have hty : cutLevHas t.val y = true := cutLevHas_of_near hv
    have hs : s.val < 37 := s.isLt
    have ht : t.val < 37 := t.isLt
    have hstv : s.val < t.val := hst
    have hchk := cutCheckOne_true hs hsx hxlt hylt
    have hcases : x + 3 ≤ y ∨ y + 3 ≤ x := by
      rw [hxv, hyv] at habs
      rcases abs_cases ((x : ℤ) - y) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
    obtain ⟨t0, ht0, ht0le⟩ :=
      cutFirstLev_le y (37 - s.val) (s.val + 1) t.val (by omega) ht (by omega) hty
    rcases hcases with hc | hc
    · rw [cutCheckOne, if_pos hc] at hchk
      simp only [ht0] at hchk
      cases hr : cutFirstVal (y - 1) (t0 - s.val) (s.val + 1) with
      | none => simp [hr] at hchk
      | some r =>
        simp only [hr] at hchk
        obtain ⟨hr1, hr2, hr3⟩ := cutFirstVal_spec _ _ _ _ hr
        by_cases hrt : t0 ≤ r
        · simp [hrt] at hchk
        · rw [if_neg hrt] at hchk
          cases hr' : cutFirstVal (x + 1) (t0 - r) (r + 1) with
          | none => simp [hr'] at hchk
          | some r2 =>
            simp only [hr'] at hchk
            obtain ⟨hs1, hs2, hs3⟩ := cutFirstVal_spec _ _ _ _ hr'
            have hlt2 : r2 < t0 := by simpa using hchk
            refine ⟨⟨r, hr2⟩, ⟨r2, hs2⟩, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [Fin.lt_def]; omega
            · simp only [Fin.lt_def]; omega
            · simp only [Fin.lt_def]; omega
            · intro _
              have e1 : cutSeq ⟨r, hr2⟩ = ((y - 1 : ℕ) : ℤ) := by rw [cutRho_eq ⟨r, hr2⟩, hr3]
              have e2 : cutSeq ⟨r2, hs2⟩ = ((x + 1 : ℕ) : ℤ) := by rw [cutRho_eq ⟨r2, hs2⟩, hs3]
              rw [e1, e2, hxv, hyv]
              push_cast [Nat.cast_sub (by omega : 1 ≤ y)]
              omega
            · intro hcon
              rw [hxv, hyv] at hcon
              omega
    · rw [cutCheckOne, if_neg (by omega : ¬ (x + 3 ≤ y)), if_pos hc] at hchk
      simp only [ht0] at hchk
      cases hr : cutFirstVal (y + 1) (t0 - s.val) (s.val + 1) with
      | none => simp [hr] at hchk
      | some r =>
        simp only [hr] at hchk
        obtain ⟨hr1, hr2, hr3⟩ := cutFirstVal_spec _ _ _ _ hr
        by_cases hrt : t0 ≤ r
        · simp [hrt] at hchk
        · rw [if_neg hrt] at hchk
          cases hr' : cutFirstVal (x - 1) (t0 - r) (r + 1) with
          | none => simp [hr'] at hchk
          | some r2 =>
            simp only [hr'] at hchk
            obtain ⟨hs1, hs2, hs3⟩ := cutFirstVal_spec _ _ _ _ hr'
            have hlt2 : r2 < t0 := by simpa using hchk
            refine ⟨⟨r, hr2⟩, ⟨r2, hs2⟩, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [Fin.lt_def]; omega
            · simp only [Fin.lt_def]; omega
            · simp only [Fin.lt_def]; omega
            · intro hcon
              rw [hxv, hyv] at hcon
              omega
            · intro _
              have e1 : cutSeq ⟨r, hr2⟩ = ((y + 1 : ℕ) : ℤ) := by rw [cutRho_eq ⟨r, hr2⟩, hr3]
              have e2 : cutSeq ⟨r2, hs2⟩ = ((x - 1 : ℕ) : ℤ) := by rw [cutRho_eq ⟨r2, hs2⟩, hs3]
              rw [e1, e2, hxv, hyv]
              push_cast [Nat.cast_sub (by omega : 1 ≤ x)]
              omega

/-! ### The span on an index interval

The commission's `spanOn` was a difference of a `Finset.sup'` and a `Finset.inf'`, each with a
nonemptiness side condition. Those side conditions are avoided here — as the commission allows —
by computing the span from the list of levels on the interval, with the value `0` on an interval
that meets no index. The two lemmas that follow are all the rest of the file uses: every level
on the interval lies between the two ends, so `spanOn ρ a b ≤ d` bounds every difference. -/

/-- The levels of `ρ` at the indices of `[a, b]`. -/
def levelsOn {n : ℕ} (ρ : Fin n → ℤ) (a b : ℕ) : List ℤ :=
  (List.finRange n).filterMap (fun t => if a ≤ t.val ∧ t.val ≤ b then some (ρ t) else none)

/-- The span of `ρ` on the index interval `[a, b]`: the largest level minus the smallest, and
`0` when the interval meets no index. -/
def spanOn {n : ℕ} (ρ : Fin n → ℤ) (a b : ℕ) : ℤ :=
  (levelsOn ρ a b).foldl max ((levelsOn ρ a b).headD 0) -
    (levelsOn ρ a b).foldl min ((levelsOn ρ a b).headD 0)

theorem mem_levelsOn {n : ℕ} (ρ : Fin n → ℤ) {a b : ℕ} (t : Fin n) (h1 : a ≤ t.val)
    (h2 : t.val ≤ b) : ρ t ∈ levelsOn ρ a b := by
  rw [levelsOn, List.mem_filterMap]
  exact ⟨t, List.mem_finRange t, by simp [h1, h2]⟩

theorem self_le_foldl_max : ∀ (l : List ℤ) (d : ℤ), d ≤ l.foldl max d := by
  intro l
  induction l with
  | nil => intro d; simp
  | cons z zs ih => intro d; exact le_trans (le_max_left d z) (ih (max d z))

theorem foldl_min_le_self : ∀ (l : List ℤ) (d : ℤ), l.foldl min d ≤ d := by
  intro l
  induction l with
  | nil => intro d; simp
  | cons z zs ih => intro d; exact le_trans (ih (min d z)) (min_le_left d z)

theorem le_foldl_max : ∀ (l : List ℤ) (d y : ℤ), y ∈ l → y ≤ l.foldl max d := by
  intro l
  induction l with
  | nil => intro d y h; simp at h
  | cons x xs ih =>
    intro d y h
    rcases List.mem_cons.1 h with he | hy
    · subst he
      have hstep : (y :: xs).foldl max d = xs.foldl max (max d y) := by simp [List.foldl]
      rw [hstep]
      exact le_trans (le_max_right d y) (self_le_foldl_max xs (max d y))
    · exact ih (max d x) y hy

theorem foldl_min_le : ∀ (l : List ℤ) (d y : ℤ), y ∈ l → l.foldl min d ≤ y := by
  intro l
  induction l with
  | nil => intro d y h; simp at h
  | cons x xs ih =>
    intro d y h
    rcases List.mem_cons.1 h with he | hy
    · subst he
      have hstep : (y :: xs).foldl min d = xs.foldl min (min d y) := by simp [List.foldl]
      rw [hstep]
      exact le_trans (foldl_min_le_self xs (min d y)) (min_le_right d y)
    · exact ih (min d x) y hy

/-- **The span bounds every difference.** -/
theorem sub_le_spanOn {n : ℕ} (ρ : Fin n → ℤ) {a b : ℕ} (t t' : Fin n)
    (h1 : a ≤ t.val) (h2 : t.val ≤ b) (h1' : a ≤ t'.val) (h2' : t'.val ≤ b) :
    ρ t - ρ t' ≤ spanOn ρ a b := by
  have hm := le_foldl_max (levelsOn ρ a b) ((levelsOn ρ a b).headD 0) _ (mem_levelsOn ρ t h1 h2)
  have hm' :=
    foldl_min_le (levelsOn ρ a b) ((levelsOn ρ a b).headD 0) _ (mem_levelsOn ρ t' h1' h2')
  rw [spanOn]
  omega

/-- **The obstruction.** No pair of cut points splits `cutSeq` into three pieces each of span
strictly below the whole. Exhaustive over all 595 pairs. -/
theorem cutSeq_no_three_cut :
    ¬ ∃ r r' : ℕ, 0 < r ∧ r < r' ∧ r' < 36 ∧
      spanOn cutSeq 0 r ≤ 3 ∧ spanOn cutSeq r r' ≤ 3 ∧ spanOn cutSeq r' 36 ≤ 3 := by
  have key : ∀ r < 36, ∀ r' < 36, ¬ (0 < r ∧ r < r' ∧
      spanOn cutSeq 0 r ≤ 3 ∧ spanOn cutSeq r r' ≤ 3 ∧ spanOn cutSeq r' 36 ≤ 3) := by
    decide +kernel
  rintro ⟨r, r', h1, h2, h3, h4, h5, h6⟩
  exact key r (by omega) r' h3 ⟨h1, h2, h4, h5, h6⟩

/-- Hence the three-banded-pieces step is not available in general. -/
theorem no_three_banded_cut_in_general :
    ∃ (n : ℕ) (ρ : Fin n → ℤ) (L H : ℤ), IsLip ρ ∧ IsCrookedIvF ρ ρ ∧
      (∀ t, L ≤ ρ t) ∧ (∀ t, ρ t ≤ H) ∧ L + 3 ≤ H ∧ (∃ t, ρ t = L) ∧ (∃ t, ρ t = H) ∧
      ¬ ∃ r r' : ℕ, 0 < r ∧ r < r' ∧ r' < n - 1 ∧
        spanOn ρ 0 r ≤ H - L - 1 ∧ spanOn ρ r r' ≤ H - L - 1 ∧
        spanOn ρ r' (n-1) ≤ H - L - 1 := by
  refine ⟨37, cutSeq, 3, 7, cutSeq_isLip, cutSeq_faithful, cutSeq_bounds.1, cutSeq_bounds.2,
    by norm_num, cutSeq_attains.1, cutSeq_attains.2, ?_⟩
  simpa using cutSeq_no_three_cut

/-! ## The measure that survives -/

/-- A cut whose two outer pieces have strictly smaller span, whose middle piece is therefore
strictly shorter, with every piece spanning at least two levels and the cut points at
crookedness witnesses. -/
def LexCut {n : ℕ} (ρ : Fin n → ℤ) (L H : ℤ) (r r' : ℕ) : Prop :=
  0 < r ∧ r < r' ∧ r' < n - 1 ∧
  spanOn ρ 0 r ≤ H - L - 1 ∧ spanOn ρ r' (n-1) ≤ H - L - 1 ∧
  2 ≤ spanOn ρ 0 r ∧ 2 ≤ spanOn ρ r r' ∧ 2 ≤ spanOn ρ r' (n-1)

/-- **Open.** A lexicographic cut exists. Evidence in the module docstring; no proof. -/
def LexCutExists : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (L H : ℤ), IsLip ρ → IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 4 ≤ H → (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    ∃ r r', LexCut ρ L H r r'

/-! ## The gluing -/

/-- **`Tracking`.** The two arms of a cut, extended over one common walk.

`ρ` is faithful and crooked, `i` a basepoint, and `r < r'` a cut whose middle piece contains
`i`. Both arms of the middle piece fold onto `c`, leaving off at times `uG` and `uT`. The
claim: the walk extends so that the two outer pieces fold on from those times — **one walk,
both extensions**.

The one-sided form of this — extend the walk for a single suffix — is vacuous: take the
extension to follow the suffix, clamped into `[L + 1, H - 1]`, which moves each level by at
most one. `FoldsFrom` constrains the walk nowhere else. The content is entirely that a single
extension must serve both sides, and that is why the earlier batches' families failed: a shape
chosen for one arm is a shape imposed on the other. -/
def Tracking : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L H : ℤ) (r r' : ℕ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (_hri : r < i.val) → (_hir : i.val < r') → (_hrn : r' < n - 1) →
    ∀ (len : ℕ) (c : ℕ → ℤ) (uG uT : ℕ),
      (∀ u, u < len → L + 1 ≤ c u ∧ c u ≤ H - 1) →
      -- the middle piece's forward arm folds, ending at time `uG`
      (∃ β : Fin (r' - i.val + 1) → ℕ, (∀ j, β j < len) ∧
        (∀ j j', j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1) ∧
        (∀ j, j.val = 0 → β j = 0) ∧ (∀ j, j.val = r' - i.val → β j = uG) ∧
        (∀ j, |ρ ⟨i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩ - c (β j)| ≤ 1)) →
      -- and its backward arm, ending at time `uT`
      (∃ β : Fin (i.val - r + 1) → ℕ, (∀ j, β j < len) ∧
        (∀ j j', j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1) ∧
        (∀ j, j.val = 0 → β j = 0) ∧ (∀ j, j.val = i.val - r → β j = uT) ∧
        (∀ j, |ρ ⟨i.val - j.val, by have := i.isLt; omega⟩ - c (β j)| ≤ 1)) →
      ∃ (len' : ℕ) (c' : ℕ → ℤ), len ≤ len' ∧ (∀ u, u < len → c' u = c u) ∧
        FoldsFrom (fun j : Fin (n - r') => ρ ⟨r' + j.val, by have := j.isLt; omega⟩) len' c' uG ∧
        FoldsFrom (fun j : Fin (r + 1) => ρ ⟨r - j.val, by have := i.isLt; omega⟩) len' c' uT

/-! ## `S3` from the gluing

The architecture the commission describes is an induction on `(H − L, n)` with `LexCutExists`
supplying the cut. It turns out not to be needed: `Tracking` may be instantiated at a
**three-point window**. Three consecutive levels of a 1-Lipschitz sequence span at most two, so
a single time carries all three, and the walk `Tracking` is asked to extend is one time long.
Its two conclusions are then precisely the two arms of the window's ends, and the two- or
three-link prefixes inside the window are folded at that one time. Every basepoint of `[0, n-2]`
lies in such a window, and the last basepoint follows by prefixing one fresh time to the walk.

So `Tracking`, as stated, is not a gluing step on top of an induction: it already implies `S3`
outright, and `LexCutExists` is not used. -/

/-- Transporting a fold along an equality of lengths and a pointwise equality. -/
theorem foldsFrom_congr {m m' : ℕ} {f : Fin m → ℤ} {g : Fin m' → ℤ} {len u : ℕ} {c : ℕ → ℤ}
    (hm : m' = m) (hfg : ∀ j : Fin m', g j = f ⟨j.val, hm ▸ j.isLt⟩) (h : FoldsFrom f len c u) :
    FoldsFrom g len c u := by
  subst hm
  have hgf : g = f := funext fun j => by simpa using hfg j
  rw [hgf]
  exact h

/-- The same, for folds that start at time zero. -/
theorem foldsOnto_congr {m m' : ℕ} {f : Fin m → ℤ} {g : Fin m' → ℤ} {len : ℕ} {c : ℕ → ℤ}
    (hm : m' = m) (hfg : ∀ j : Fin m', g j = f ⟨j.val, hm ▸ j.isLt⟩) (h : FoldsOnto f len c) :
    FoldsOnto g len c := by
  subst hm
  have hgf : g = f := funext fun j => by simpa using hfg j
  rw [hgf]
  exact h

/-- A window of three consecutive indices has a centre in `[L + 1, H - 1]` within one of all
three levels. -/
theorem window_center {n : ℕ} {ρ : Fin n → ℤ} {L H : ℤ} (hlip : IsLip ρ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H) {a : ℕ} (ha : a + 2 < n) :
    ∃ v : ℤ, L + 1 ≤ v ∧ v ≤ H - 1 ∧
      ∀ t : Fin n, a ≤ t.val → t.val ≤ a + 2 → |ρ t - v| ≤ 1 := by
  have h0 : a < n := by omega
  have h1 : a + 1 < n := by omega
  set x0 := ρ ⟨a, h0⟩ with hx0
  set x1 := ρ ⟨a + 1, h1⟩ with hx1
  set x2 := ρ ⟨a + 2, ha⟩ with hx2
  have s01 : |x1 - x0| ≤ 1 := hlip ⟨a, h0⟩ ⟨a + 1, h1⟩ rfl
  have s12 : |x2 - x1| ≤ 1 := hlip ⟨a + 1, h1⟩ ⟨a + 2, ha⟩ rfl
  rw [abs_le] at s01 s12
  have hL0 := hLb ⟨a, h0⟩
  have hL1 := hLb ⟨a + 1, h1⟩
  have hL2 := hLb ⟨a + 2, ha⟩
  have hH0 := hHb ⟨a, h0⟩
  have hH1 := hHb ⟨a + 1, h1⟩
  have hH2 := hHb ⟨a + 2, ha⟩
  set m : ℤ := min (min x0 x1) x2 with hmdef
  have hm0 : m ≤ x0 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hm1 : m ≤ x1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hm2 : m ≤ x2 := min_le_right _ _
  have hmeq : m = x0 ∨ m = x1 ∨ m = x2 := by
    rcases min_cases (min x0 x1) x2 with ⟨he, -⟩ | ⟨he, -⟩
    · rcases min_cases x0 x1 with ⟨he', -⟩ | ⟨he', -⟩
      · exact Or.inl (hmdef.trans (he.trans he'))
      · exact Or.inr (Or.inl (hmdef.trans (he.trans he')))
    · exact Or.inr (Or.inr (hmdef.trans he))
  set v : ℤ := min (H - 1) (m + 1) with hvdef
  have hvH : v ≤ H - 1 := min_le_left _ _
  have hvm : v ≤ m + 1 := min_le_right _ _
  have hveq : v = H - 1 ∨ v = m + 1 := by
    rcases min_cases (H - 1) (m + 1) with ⟨he, -⟩ | ⟨he, -⟩
    · exact Or.inl he
    · exact Or.inr he
  refine ⟨v, ?_, hvH, ?_⟩
  · rcases hveq with he | he <;> omega
  · intro t ht1 ht2
    have hcase : t = (⟨a, h0⟩ : Fin n) ∨ t = (⟨a + 1, h1⟩ : Fin n) ∨ t = (⟨a + 2, ha⟩ : Fin n) := by
      have := t.isLt
      rcases (by omega : t.val = a ∨ t.val = a + 1 ∨ t.val = a + 2) with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases hcase with rfl | rfl | rfl <;> rw [abs_le] <;>
      rcases hveq with he | he <;> rcases hmeq with he' | he' | he' <;> omega

/-- **The three-point window.** `Tracking` at the window `[a, a+2]`, whose three levels one time
carries: the suffix from `a + 2` and the reversed prefix up to `a` both fold from time `0` of a
walk whose first value is within one of all three window levels. -/
theorem tracking_window (h2 : Tracking) {n : ℕ} {ρ σ : Fin n → ℤ} {L H : ℤ}
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hLH : L + 3 ≤ H) {a : ℕ} (ha : a + 3 < n) :
    ∃ (len : ℕ) (c : ℕ → ℤ), 0 < len ∧
      (∀ t : Fin n, a ≤ t.val → t.val ≤ a + 2 → |ρ t - c 0| ≤ 1) ∧
      FoldsFrom (fun j : Fin (n - (a + 2)) => ρ ⟨a + 2 + j.val, by omega⟩) len c 0 ∧
      FoldsFrom (fun j : Fin (a + 1) => ρ ⟨a - j.val, by omega⟩) len c 0 := by
  obtain ⟨v, hv1, hv2, hvw⟩ := window_center hlip hLb hHb hLH (a := a) (by omega)
  have hi : a + 1 < n := by omega
  have hii : ((⟨a + 1, hi⟩ : Fin n) : ℕ) = a + 1 := rfl
  obtain ⟨len, c, hle, hagree, hG, hT⟩ :=
    h2 n ρ σ ⟨a + 1, hi⟩ L H a (a + 2) hlip hcr hLb hHb hLH (by simp) (by simp) (by omega)
      1 (fun _ => v) 0 0 (fun u _ => ⟨hv1, hv2⟩)
      ⟨fun _ => 0, fun _ => Nat.zero_lt_one, fun j j' _ => by simp, fun _ _ => rfl,
        fun _ _ => rfl, fun j => by
          have hj := j.isLt
          exact hvw _ (by simp; omega) (by simp; omega)⟩
      ⟨fun _ => 0, fun _ => Nat.zero_lt_one, fun j j' _ => by simp, fun _ _ => rfl,
        fun _ _ => rfl, fun j => by
          have hj := j.isLt
          exact hvw _ (by simp; omega) (by simp; omega)⟩
  have hc0 : c 0 = v := hagree 0 (by omega)
  exact ⟨len, c, by omega, fun t h1 h2' => by rw [hc0]; exact hvw t h1 h2', hG, hT⟩

/-- Every basepoint of a three-point window folds, once the window's two outer pieces do. -/
theorem s3_at_window {n : ℕ} {ρ : Fin n → ℤ} {a : ℕ} (ha : a + 3 < n) {len : ℕ} {c : ℕ → ℤ}
    (hlen : 0 < len)
    (hwin : ∀ t : Fin n, a ≤ t.val → t.val ≤ a + 2 → |ρ t - c 0| ≤ 1)
    (hG : FoldsFrom (fun j : Fin (n - (a + 2)) => ρ ⟨a + 2 + j.val, by omega⟩) len c 0)
    (hT : FoldsFrom (fun j : Fin (a + 1) => ρ ⟨a - j.val, by omega⟩) len c 0)
    (b : Fin n) (hb1 : a ≤ b.val) (hb2 : b.val ≤ a + 2) :
    FoldsOnto (armG ρ b) len c ∧ FoldsOnto (armT ρ b) len c := by
  have hbn := b.isLt
  constructor
  · -- the forward arm: at most three links inside the window, then the suffix from `a + 2`
    refine foldsFrom_split (armG ρ b) len c 0 0 (a + 2 - b.val) (by omega) ?_ ?_
    · refine ⟨fun _ => 0, fun _ => hlen, fun j j' _ => by simp, fun _ _ => rfl, fun _ _ => rfl,
        fun j => ?_⟩
      have := j.isLt
      exact hwin _ (by simp; omega) (by simp; omega)
    · refine foldsFrom_congr (by omega) (fun j => ?_) hG
      simp only [armG]
      congr 1
      exact Fin.ext (by simp; omega)
  · -- the backward arm: at most three links inside the window, then the prefix up to `a`
    refine foldsFrom_split (armT ρ b) len c 0 0 (b.val - a) (by omega) ?_ ?_
    · refine ⟨fun _ => 0, fun _ => hlen, fun j j' _ => by simp, fun _ _ => rfl, fun _ _ => rfl,
        fun j => ?_⟩
      have := j.isLt
      exact hwin _ (by simp; omega) (by simp; omega)
    · refine foldsFrom_congr (by omega) (fun j => ?_) hT
      simp only [armT]
      congr 1
      exact Fin.ext (by simp; omega)

/-- Prefixing one fresh time to a walk, to move a basepoint one step outwards. -/
theorem foldsOnto_cons {m len : ℕ} {g : Fin (m + 1) → ℤ} {c : ℕ → ℤ} {u : ℕ}
    (hnear : |g ⟨0, by omega⟩ - c u| ≤ 1)
    (htail : FoldsOnto (fun j : Fin m => g ⟨j.val + 1, by omega⟩) len c) :
    FoldsOnto g (len + 1) (fun t => if t = 0 then c u else c (t - 1)) := by
  obtain ⟨β, hlt, hlipβ, h0, hw⟩ := htail
  refine ⟨fun j => if _h : j.val = 0 then 0 else β ⟨j.val - 1, by have := j.isLt; omega⟩ + 1,
    ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j.val = 0
    · simp [hj]
    · simp only [dif_neg hj]
      have := hlt ⟨j.val - 1, by have := j.isLt; omega⟩
      omega
  · intro j j' hjj'
    have hj := j.isLt
    have hj' := j'.isLt
    by_cases h0j : j.val = 0
    · have h1j' : j'.val = 1 := by omega
      have hz : β ⟨j'.val - 1, by omega⟩ = 0 := h0 _ (by simp; omega)
      simp only [dif_pos h0j, dif_neg (show ¬ j'.val = 0 by omega), hz]
      norm_num
    · have h0j' : ¬ j'.val = 0 := by omega
      simp only [dif_neg h0j, dif_neg h0j']
      have hstep := hlipβ ⟨j.val - 1, by omega⟩ ⟨j'.val - 1, by omega⟩ (by simp; omega)
      rw [abs_le] at hstep ⊢
      push_cast at hstep ⊢
      omega
  · intro j hj
    simp [hj]
  · intro j
    have hj := j.isLt
    by_cases h0j : j.val = 0
    · simpa [dif_pos h0j, show j = (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) from Fin.ext h0j]
        using hnear
    · have hb : |g ⟨(j.val - 1) + 1, by omega⟩ - c (β ⟨j.val - 1, by omega⟩)| ≤ 1 :=
        hw ⟨j.val - 1, by omega⟩
      have he : g ⟨(j.val - 1) + 1, by omega⟩ = g j := by
        congr 1
        exact Fin.ext (by simp; omega)
      rw [he] at hb
      have hne : ¬ (β ⟨j.val - 1, by omega⟩ + 1 = 0) := by omega
      simp only [dif_neg h0j, if_neg hne]
      simpa using hb

/-- **The architecture.** `S3` from the gluing. The commissioned hypothesis `LexCutExists` is
not needed: the three-point window gives `Tracking` a one-time walk to extend, so no induction
on the span is performed. It is kept in the statement because the commission asked for it. -/
theorem s3_of_tracking (_h1 : LexCutExists) (h2 : Tracking) : S3 := by
  intro n ρ σ i H L hlip hcr hLb hHb hLH hL hH
  -- the span forces at least four links
  obtain ⟨tL, htL⟩ := hL
  obtain ⟨tH, htH⟩ := hH
  have hn4 : 4 ≤ n := by
    by_contra hc
    have hd : ∀ t t' : Fin n, |ρ t - ρ t'| ≤ 2 := by
      intro t t'
      have ht := t.isLt
      have ht' := t'.isLt
      rcases le_total t'.val t.val with h | h
      · have := abs_sub_le_of_isLip hlip (t.val - t'.val) t' t (by omega)
        have : |ρ t - ρ t'| ≤ ((t.val - t'.val : ℕ) : ℤ) := this
        have hb : ((t.val - t'.val : ℕ) : ℤ) ≤ 2 := by
          have : t.val - t'.val ≤ 2 := by omega
          exact_mod_cast this
        omega
      · have := abs_sub_le_of_isLip hlip (t'.val - t.val) t t' (by omega)
        have h2' : |ρ t' - ρ t| ≤ ((t'.val - t.val : ℕ) : ℤ) := this
        have hb : ((t'.val - t.val : ℕ) : ℤ) ≤ 2 := by
          have : t'.val - t.val ≤ 2 := by omega
          exact_mod_cast this
        rw [abs_sub_comm] at h2'
        omega
    have := hd tH tL
    rw [htL, htH, abs_le] at this
    omega
  -- every basepoint but the last lies in a three-point window
  have hmain : ∀ b : Fin n, b.val ≤ n - 2 →
      ∃ (len : ℕ) (c : ℕ → ℤ), FoldsOnto (armG ρ b) len c ∧ FoldsOnto (armT ρ b) len c := by
    intro b hb
    have hbn := b.isLt
    set a := min b.val (n - 4) with hadef
    have ha : a + 3 < n := by omega
    have hb1 : a ≤ b.val := min_le_left _ _
    have hb2 : b.val ≤ a + 2 := by omega
    obtain ⟨len, c, hlen, hwin, hG, hT⟩ := tracking_window h2 hlip hcr hLb hHb hLH ha
    obtain ⟨hGb, hTb⟩ := s3_at_window ha hlen hwin hG hT b hb1 hb2
    exact ⟨len, c, hGb, hTb⟩
  rcases le_or_gt i.val (n - 2) with hi | hi
  · exact hmain i hi
  · -- the last basepoint: prefix one time to the walk of the basepoint before it
    have hin : i.val = n - 1 := by have := i.isLt; omega
    obtain ⟨len, c, hG, hT⟩ := hmain ⟨n - 2, by omega⟩ (by simp)
    -- the forward arm at `n - 2` reaches `n - 1` at some time `u`
    obtain ⟨β, hlt, hlipβ, h0, hw⟩ := hG
    have h1lt : (1 : ℕ) < n - (n - 2) := by omega
    set u := β ⟨1, h1lt⟩ with hu
    have hnear : |ρ i - c u| ≤ 1 := by
      have := hw ⟨1, h1lt⟩
      simp only [armG] at this
      have he : (⟨(n - 2) + 1, by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
      rw [he] at this
      exact this
    refine ⟨len + 1, fun t => if t = 0 then c u else c (t - 1), ?_, ?_⟩
    · -- the forward arm at the last index is a single link
      refine ⟨fun _ => 0, fun _ => Nat.succ_pos len, fun j j' hjj' => ?_, fun _ _ => rfl,
        fun j => ?_⟩
      · simp
      · have harm : (armG ρ i) j = ρ i := by
          have hjl := j.isLt
          show ρ ⟨i.val + j.val, _⟩ = ρ i
          congr 1
          exact Fin.ext (by simp; omega)
        simpa [harm] using hnear
    · -- the backward arm at the last index is the backward arm at `n - 2`, one link longer
      have hcast : FoldsOnto (fun j : Fin (n - 2 + 1) =>
          armT ρ i ⟨j.val + 1, by have := j.isLt; omega⟩) len c := by
        refine foldsOnto_congr (m' := n - 2 + 1) rfl (fun j => ?_) hT
        show ρ ⟨i.val - (j.val + 1), _⟩ = ρ ⟨n - 2 - j.val, _⟩
        congr 1
        exact Fin.ext (by simp; omega)
      have hhead : |armT ρ i ⟨0, by omega⟩ - c u| ≤ 1 := by
        have hg0 : armT ρ i ⟨0, by omega⟩ = ρ i := rfl
        rw [hg0]
        exact hnear
      have hcons := foldsOnto_cons (m := n - 2 + 1)
        (g := fun j : Fin ((n - 2 + 1) + 1) => armT ρ i ⟨j.val, by have := j.isLt; omega⟩)
        hhead hcast
      exact foldsOnto_congr (m := (n - 2 + 1) + 1) (m' := i.val + 1)
        (f := fun j : Fin ((n - 2 + 1) + 1) => armT ρ i ⟨j.val, by have := j.isLt; omega⟩)
        (by omega) (fun j => rfl) hcons

end HPC.Fold
