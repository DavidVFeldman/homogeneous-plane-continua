import HPC.Fold.Cut

/-!
# The increasing-amplitude family, and its refutation

Batch 27 showed that `Tracking`, stated over an arbitrary walk, is at least as hard as `S3`:
instantiated at a three-point window it *is* `S3`. Constraining the cut does not repair it —
3 187 of 5 680 subchains of `bing 0 8` and `bing 0 10` admit a `LexCut` whose middle piece is
three links, and the same collapse follows. **No black-box extension hypothesis can be a step
in a proof of `S3`**: the extension must be constructed with the middle piece's itinerary, not
after it.

What the minimal itineraries look like, at the basepoint of each span where the reversal count
is largest:

| span | basepoint | minimal turning sequences |
|---|---|---|
| 6 | 5 | `c₀ → 1 → 5` |
| 8 | 57 | `c₀ → {5,6} → 1 → 7` |
| 10 | 343 | `c₀ → {2,3} → {7,8} → 1 → 9` |

Every one ends `→ L+1 → H−1`, and the amplitudes `|tⱼ₊₁ − tⱼ|` strictly increase. `IsZig` is
that family.

**The gate of COMMISSION.md §1 fails, and it fails at every span, for a structural reason.**
A zig walk cannot start in either extreme band: if `ts[0] = L + 1` then, its entries lying in
`[L+1, H−1]`, the first turn must go up, the second must reverse with a strictly larger
amplitude, and it therefore lands strictly below `L + 1`. So `L + 2 ≤ ts[0] ≤ H − 2`
(`zig_base_lower`, `zig_base_upper`). But `FoldsOnto` pins time `0` to the basepoint, so at a
basepoint with `ρ i = L` the walk must begin within one of `L`, i.e. at `L + 1`; no zig walk
does. Hence `¬ S3Zig` (`not_s3Zig`), witnessed by `cutSeq` — thirty-seven links of `bing 0 8`,
span four, faithful, whose first link is at level `L = 3` — at basepoint `0`. The base-centre
clause of `S3Zig` is not what causes this: it is implied by `FoldsOnto`
(`abs_sub_base_le_of_folds`), and the refutation below uses the folds rather than the clause,
so deleting the clause would change nothing.

The census (`census-batch28.c`) decides `S3Zig` exactly, by bitmask reachability over all zig
walks, at *every* basepoint of `bing 0 n` for `n = 4 … 12` — spans eleven and twelve included,
which is what §1 asked for — and at every basepoint of 4 000 random and 8 025 grid-sampled
subchains of `bing 0 12` of span ≥ 9. The outcome is uniform: the only basepoints not served
are those at an extreme level, exactly the ones the structural obstruction kills, and every
other basepoint is served. So the family is right in the interior and wrong at the ends. The
maximum over basepoints of the least number of turning targets is `⌊span/2⌋ − 1` again: 4 at
span 11, first attained at basepoint 343, level 5, whose twelve minimal itineraries are
`{4,5,6} → {2,3} → {7,8} → 1 → 10`; and 5 at span 12, first attained at basepoint 2027,
level 5, whose sixteen minimal itineraries are `{4,5} → {7,8} → {2,3} → {9,10} → 1 → 11`.

Relaxing the family by exempting the *first* amplitude from the increase condition — keeping
`|t₂ − t₁| < |t₃ − t₂| < ⋯`, the alternation, the band and the extreme finish — restores
exactly the missing base levels (`L + 1` and `H − 1` become reachable starts) and serves every
basepoint of every chain and subchain censused. That is `IsZigFree`/`S3ZigFree` below, stated
but neither proved nor refuted; it is the shape the next formulation should take.

English proofs: COMMISSION-batch28.md §2–§3. Delivered: `zigWalk` supplied, with its length
(`zigWalk_length`) and its values (`zigWalk_head`, `zigWalk_step`, `zigWalk_mem_band`);
`s3_of_s3Zig`, `zig_not_contains_offLam`, and `not_s3Zig`; `s3Zig` is refuted and kept,
commented out, at the end. `ts.get!` is written `ts[·]!` throughout, that being the
current spelling of indexing with a default.
-/

namespace HPC.Fold

/-! ## The family -/

/-- A turning sequence: alternating directions, strictly increasing amplitudes, ending at the
two extreme bands in either order. -/
structure IsZig (L H : ℤ) (ts : List ℤ) : Prop where
  bounds : ∀ t ∈ ts, L + 1 ≤ t ∧ t ≤ H - 1
  len : 3 ≤ ts.length
  alt : ∀ j, j + 2 < ts.length →
    (ts[j+1]! - ts[j]!) * (ts[j+2]! - ts[j+1]!) < 0
  amp : ∀ j, j + 2 < ts.length →
    |ts[j+1]! - ts[j]!| < |ts[j+2]! - ts[j+1]!|
  ends : (ts[ts.length - 2]!, ts[ts.length - 1]!) = (L + 1, H - 1) ∨
         (ts[ts.length - 2]!, ts[ts.length - 1]!) = (H - 1, L + 1)

/-- The same family with the first amplitude exempt from the increase condition: only
`|t₂ − t₁| < |t₃ − t₂| < ⋯` is required. Recorded because it is what the census supports:
it serves every basepoint of every chain tested, including those at the extreme levels, where
`IsZig` is impossible. -/
structure IsZigFree (L H : ℤ) (ts : List ℤ) : Prop where
  bounds : ∀ t ∈ ts, L + 1 ≤ t ∧ t ≤ H - 1
  len : 3 ≤ ts.length
  alt : ∀ j, j + 2 < ts.length →
    (ts[j+1]! - ts[j]!) * (ts[j+2]! - ts[j+1]!) < 0
  amp : ∀ j, 1 ≤ j → j + 2 < ts.length →
    |ts[j+1]! - ts[j]!| < |ts[j+2]! - ts[j+1]!|
  ends : (ts[ts.length - 2]!, ts[ts.length - 1]!) = (L + 1, H - 1) ∨
         (ts[ts.length - 2]!, ts[ts.length - 1]!) = (H - 1, L + 1)

theorem IsZig.isZigFree {L H : ℤ} {ts : List ℤ} (h : IsZig L H ts) : IsZigFree L H ts :=
  ⟨h.bounds, h.len, h.alt, fun j _ hj => h.amp j hj, h.ends⟩

/-! ## The walk through a turning sequence -/

/-- The unit-step run from `a` to `b`: the levels strictly after `a`, up to and including `b`. -/
def stepRun (a b : ℤ) : List ℤ :=
  if h : a = b then []
  else (if h : a < b then a + 1 else a - 1) :: stepRun (if h : a < b then a + 1 else a - 1) b
termination_by (b - a).natAbs
decreasing_by
  · split <;> omega

/-- The levels after the first, walking from `a` through the turning targets `ts`. -/
def zigTail : ℤ → List ℤ → List ℤ
  | _, [] => []
  | a, t :: rest => stepRun a t ++ zigTail t rest

/-- All the levels of the walk through `ts`, one level per step. -/
def zigLevels : List ℤ → List ℤ
  | [] => []
  | t :: rest => t :: zigTail t rest

/-- The total amplitude of a turning sequence starting at `a`. -/
def ampSum : ℤ → List ℤ → ℕ
  | _, [] => 0
  | a, t :: rest => (t - a).natAbs + ampSum t rest

/-- The walk through a turning sequence, one level per step. -/
def zigWalk (ts : List ℤ) : ℕ × (ℕ → ℤ) :=
  ((zigLevels ts).length, fun u => (zigLevels ts).getD u 0)

theorem stepRun_length (a b : ℤ) : (stepRun a b).length = (b - a).natAbs := by
  induction a using stepRun.induct b with
  | case1 => simp [stepRun]
  | case2 a h ih =>
      rw [stepRun, dif_neg h, List.length_cons, ih]
      split <;> omega

theorem zigTail_length (a : ℤ) (ts : List ℤ) : (zigTail a ts).length = ampSum a ts := by
  induction ts generalizing a with
  | nil => simp [zigTail, ampSum]
  | cons t rest ih => simp [zigTail, ampSum, stepRun_length, ih]

/-- **The length of a zig walk**: one step per unit of amplitude, plus the starting level. -/
theorem zigWalk_length (t : ℤ) (rest : List ℤ) :
    (zigWalk (t :: rest)).1 = ampSum t rest + 1 := by
  simp [zigWalk, zigLevels, zigTail_length]

/-- **The value of a zig walk at time `0`** is the base centre. -/
theorem zigWalk_head (t : ℤ) (rest : List ℤ) : (zigWalk (t :: rest)).2 0 = t := rfl

/-- `FoldsOnto` already pins the walk's first value to within one of the basepoint's level:
the base-centre clause of `S3Zig` is implied by the folds, not an extra demand. -/
theorem abs_sub_base_le_of_folds {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (ts : List ℤ)
    (hne : ts ≠ []) (h : FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2) :
    |ρ i - ts[0]!| ≤ 1 := by
  obtain ⟨β, -, -, hzero, hclose⟩ := h
  have hi := i.isLt
  set j : Fin (n - i.val) := ⟨0, by omega⟩ with hj
  have hβ : β j = 0 := hzero j rfl
  have h1 := hclose j
  rw [hβ] at h1
  have h2 : armG ρ i j = ρ i := by simp [armG, hj]
  obtain ⟨t, rest, rfl⟩ : ∃ t rest, ts = t :: rest := by
    cases ts with
    | nil => exact absurd rfl hne
    | cons t rest => exact ⟨t, rest, rfl⟩
  rw [h2, zigWalk_head] at h1
  simpa using h1

theorem stepRun_getLast? (a b : ℤ) : (a :: stepRun a b).getLast? = some b := by
  induction a using stepRun.induct b with
  | case1 => simp [stepRun]
  | case2 a h ih => rw [stepRun, dif_neg h, List.getLast?_cons_cons]; exact ih

theorem stepRun_isChain (a b : ℤ) :
    List.IsChain (fun x y : ℤ => |y - x| = 1) (a :: stepRun a b) := by
  induction a using stepRun.induct b with
  | case1 => simp [stepRun]
  | case2 a h ih =>
      rw [stepRun, dif_neg h, List.isChain_cons]
      refine ⟨?_, ih⟩
      intro y hy
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      split <;> simp

theorem zigTail_isChain (a : ℤ) (ts : List ℤ) :
    List.IsChain (fun x y : ℤ => |y - x| = 1) (a :: zigTail a ts) := by
  induction ts generalizing a with
  | nil => simp [zigTail]
  | cons t rest ih =>
      have hsplit : a :: zigTail a (t :: rest) = (a :: stepRun a t) ++ zigTail t rest := by
        simp [zigTail]
      rw [hsplit, List.isChain_append]
      refine ⟨stepRun_isChain a t, (List.isChain_cons.mp (ih t)).2, ?_⟩
      intro x hx y hy
      rw [stepRun_getLast? a t] at hx
      simp only [Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact (List.isChain_cons.mp (ih t)).1 y hy

theorem zigLevels_isChain (ts : List ℤ) :
    List.IsChain (fun x y : ℤ => |y - x| = 1) (zigLevels ts) := by
  cases ts with
  | nil => simp [zigLevels]
  | cons t rest => exact zigTail_isChain t rest

/-- **A zig walk moves one level per step**, which is what makes it a walk. -/
theorem zigWalk_step (ts : List ℤ) (u : ℕ) (hu : u + 1 < (zigWalk ts).1) :
    |(zigWalk ts).2 (u + 1) - (zigWalk ts).2 u| = 1 := by
  have hlen : u + 1 < (zigLevels ts).length := by simpa [zigWalk] using hu
  have h1 : (zigWalk ts).2 u = (zigLevels ts)[u]'(by omega) := by
    simp [zigWalk, List.getElem?_eq_getElem (show u < (zigLevels ts).length by omega)]
  have h2 : (zigWalk ts).2 (u + 1) = (zigLevels ts)[u + 1]'hlen := by
    simp [zigWalk, List.getElem?_eq_getElem hlen]
  rw [h1, h2]
  exact List.isChain_iff_getElem.mp (zigLevels_isChain ts) u hlen

theorem stepRun_mem_bounds {a b x : ℤ} (hx : x ∈ stepRun a b) :
    min a b ≤ x ∧ x ≤ max a b := by
  induction a using stepRun.induct b with
  | case1 => simp [stepRun] at hx
  | case2 a h ih =>
      rw [stepRun, dif_neg h, List.mem_cons] at hx
      rcases hx with rfl | hx
      · split <;> omega
      · have := ih hx
        split at this <;> omega

theorem zigTail_bounds {lo hi a : ℤ} {ts : List ℤ} (ha : lo ≤ a) (ha' : a ≤ hi)
    (h : ∀ t ∈ ts, lo ≤ t ∧ t ≤ hi) : ∀ x ∈ zigTail a ts, lo ≤ x ∧ x ≤ hi := by
  induction ts generalizing a with
  | nil => simp [zigTail]
  | cons t rest ih =>
      intro x hx
      rw [zigTail, List.mem_append] at hx
      obtain ⟨ht, ht'⟩ := h t (List.mem_cons_self ..)
      rcases hx with hx | hx
      · have := stepRun_mem_bounds hx
        constructor <;> omega
      · exact ih ht ht' (fun s hs => h s (List.mem_cons_of_mem _ hs)) x hx

theorem zigLevels_bounds {lo hi : ℤ} {ts : List ℤ} (h : ∀ t ∈ ts, lo ≤ t ∧ t ≤ hi) :
    ∀ x ∈ zigLevels ts, lo ≤ x ∧ x ≤ hi := by
  cases ts with
  | nil => simp [zigLevels]
  | cons t rest =>
      intro x hx
      rw [zigLevels, List.mem_cons] at hx
      obtain ⟨ht, ht'⟩ := h t (List.mem_cons_self ..)
      rcases hx with rfl | hx
      · exact ⟨ht, ht'⟩
      · exact zigTail_bounds ht ht' (fun s hs => h s (List.mem_cons_of_mem _ hs)) x hx

/-- **The values of a zig walk** all lie in the band `[L+1, H−1]`. -/
theorem zigWalk_mem_band {L H : ℤ} {ts : List ℤ} (h : IsZig L H ts) (u : ℕ)
    (hu : u < (zigWalk ts).1) : L + 1 ≤ (zigWalk ts).2 u ∧ (zigWalk ts).2 u ≤ H - 1 := by
  have hval : (zigWalk ts).2 u = (zigLevels ts)[u]'hu := by
    simp [zigWalk, List.getElem?_eq_getElem hu]
  rw [hval]
  exact zigLevels_bounds h.bounds _ (List.getElem_mem _)

/-! ## `S3Zig` -/

/-- **`S3Zig`.** `S3` with the itinerary drawn from the increasing-amplitude family, based at
one of the three centres. -/
def S3Zig : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    ∃ ts : List ℤ, IsZig L H ts ∧
      (ts[0]! = ρ i - 1 ∨ ts[0]! = ρ i ∨ ts[0]! = ρ i + 1) ∧
      FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2

/-- **`S3ZigFree`.** The same with the relaxed family, which the census supports at every
basepoint. Neither proved nor refuted here. -/
def S3ZigFree : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    ∃ ts : List ℤ, IsZigFree L H ts ∧
      FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2

theorem s3_of_s3Zig (h : S3Zig) : S3 := by
  intro n ρ σ i H L hlip hcr hL hH hLH heL heH
  obtain ⟨ts, -, -, hG, hT⟩ := h n ρ σ i H L hlip hcr hL hH hLH heL heH
  exact ⟨(zigWalk ts).1, (zigWalk ts).2, hG, hT⟩

theorem s3_of_s3ZigFree (h : S3ZigFree) : S3 := by
  intro n ρ σ i H L hlip hcr hL hH hLH heL heH
  obtain ⟨ts, -, hG, hT⟩ := h n ρ σ i H L hlip hcr hL hH hLH heL heH
  exact ⟨(zigWalk ts).1, (zigWalk ts).2, hG, hT⟩

theorem s3ZigFree_of_s3Zig (h : S3Zig) : S3ZigFree := by
  intro n ρ σ i H L hlip hcr hL hH hLH heL heH
  obtain ⟨ts, hz, -, hG, hT⟩ := h n ρ σ i H L hlip hcr hL hH hLH heL heH
  exact ⟨ts, hz.isZigFree, hG, hT⟩

/-! ## The obstruction: a zig walk starts strictly inside the band -/

theorem zig_mem {L H : ℤ} {ts : List ℤ} (h : IsZig L H ts) {k : ℕ} (hk : k < ts.length) :
    L + 1 ≤ ts[k]! ∧ ts[k]! ≤ H - 1 := by
  rw [getElem!_pos ts k hk]
  exact h.bounds _ (List.getElem_mem _)

/-- No zig sequence begins in the lower extreme band: from `L + 1` the first turn must ascend,
and the next, reversing with a strictly larger amplitude, would leave the band. -/
theorem zig_base_lower {L H : ℤ} {ts : List ℤ} (h : IsZig L H ts) : L + 2 ≤ ts[0]! := by
  have hlen := h.len
  have h0 := zig_mem h (k := 0) (by omega)
  have h1 := zig_mem h (k := 1) (by omega)
  have h2 := zig_mem h (k := 2) (by omega)
  have halt : (ts[1]! - ts[0]!) * (ts[2]! - ts[1]!) < 0 := h.alt 0 (by omega)
  have hamp : |ts[1]! - ts[0]!| < |ts[2]! - ts[1]!| := h.amp 0 (by omega)
  rcases mul_neg_iff.mp halt with ⟨hp, hn⟩ | ⟨hn, hp⟩
  · rw [abs_of_pos (by omega), abs_of_neg (by omega)] at hamp
    omega
  · omega

/-- No zig sequence begins in the upper extreme band. -/
theorem zig_base_upper {L H : ℤ} {ts : List ℤ} (h : IsZig L H ts) : ts[0]! ≤ H - 2 := by
  have hlen := h.len
  have h0 := zig_mem h (k := 0) (by omega)
  have h1 := zig_mem h (k := 1) (by omega)
  have h2 := zig_mem h (k := 2) (by omega)
  have halt : (ts[1]! - ts[0]!) * (ts[2]! - ts[1]!) < 0 := h.alt 0 (by omega)
  have hamp : |ts[1]! - ts[0]!| < |ts[2]! - ts[1]!| := h.amp 0 (by omega)
  rcases mul_neg_iff.mp halt with ⟨hp, hn⟩ | ⟨hn, hp⟩
  · omega
  · rw [abs_of_neg (by omega), abs_of_pos (by omega)] at hamp
    omega

/-- The one-bump family sits inside the new one only when its peak is extreme; recorded so the
relation between the two is on the record rather than assumed. The witness is of the class the
commission names, `c ≤ L + 1`; the reason it works is `zig_base_lower`. -/
theorem zig_not_contains_offLam :
    ∃ (c h L H : ℤ), L + 1 ≤ c ∧ c ≤ h ∧ h ≤ H - 1 ∧ L + 3 ≤ H ∧
      ¬ ∃ ts : List ℤ, IsZig L H ts ∧ ts[0]! = c ∧ (zigWalk ts).1 = (offLam c h L H).1 ∧
        ∀ u, u < (offLam c h L H).1 → (zigWalk ts).2 u = (offLam c h L H).2 u := by
  refine ⟨1, 3, 0, 4, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  rintro ⟨ts, hz, h0, -, -⟩
  have := zig_base_lower hz
  omega

/-! ## The refutation -/

/-- `S3Zig` has no chance at a basepoint sitting at the bottom level: `FoldsOnto` pins time `0`
to the basepoint, so the walk would have to start at `L + 1`, and no zig walk does. -/
theorem s3Zig_fails_at_low_basepoint (h : S3Zig) {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hL : ∀ t, L ≤ ρ t) (hH : ∀ t, ρ t ≤ H)
    (hLH : L + 3 ≤ H) (heL : ∃ t, ρ t = L) (heH : ∃ t, ρ t = H) (hi : ρ i = L) : False := by
  obtain ⟨ts, hz, -, hG, -⟩ := h n ρ σ i H L hlip hcr hL hH hLH heL heH
  have hne : ts ≠ [] := by
    have := hz.len
    rintro rfl
    simp at this
  have hclose := abs_sub_base_le_of_folds ρ i ts hne hG
  rw [abs_le] at hclose
  have := zig_base_lower hz
  omega

/-- The same at the top level. -/
theorem s3Zig_fails_at_high_basepoint (h : S3Zig) {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hL : ∀ t, L ≤ ρ t) (hH : ∀ t, ρ t ≤ H)
    (hLH : L + 3 ≤ H) (heL : ∃ t, ρ t = L) (heH : ∃ t, ρ t = H) (hi : ρ i = H) : False := by
  obtain ⟨ts, hz, -, hG, -⟩ := h n ρ σ i H L hlip hcr hL hH hLH heL heH
  have hne : ts ≠ [] := by
    have := hz.len
    rintro rfl
    simp at this
  have hclose := abs_sub_base_le_of_folds ρ i ts hne hG
  rw [abs_le] at hclose
  have := zig_base_upper hz
  omega

/-- **`S3Zig` is false.** `cutSeq` at basepoint `0`: thirty-seven links of `bing 0 8`, faithful,
on levels `3 … 7`, whose first link is at the bottom level. -/
theorem not_s3Zig : ¬ S3Zig := fun h =>
  s3Zig_fails_at_low_basepoint h cutSeq cutSeq 0 7 3 cutSeq_isLip cutSeq_faithful
    cutSeq_bounds.1 cutSeq_bounds.2 (by norm_num) cutSeq_attains.1 cutSeq_attains.2 rfl

-- Commented-out statement `s3Zig` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
