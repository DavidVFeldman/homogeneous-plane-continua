import HPC.Fold.Choice

/-!
# The arms cannot be separated

Batch 32 settled that the choice of walk is not a table: not constant on a band
(`notConstantOnBand`), and not boundable in size (`cover_card_ge_span` — any cover of the
basepoints of a Lipschitz chain reaching both extremes needs at least `⌊(H−L)/3⌋ + 1` walks).
What remains is a construction that reads the arms and iterates `foldsOnto_prefixLeg` with
`isZigFree_cons`.

The obvious induction hypothesis for that is a statement about a *pair*: two faithful crooked
sequences confined to `[L, H]`, both starting within one of a common centre, fold onto a common
member of the family. **That is false**, and it is refuted here.

Take `bing 0 6`, span six. Its forward stretch from index 57 and its backward stretch from index
13 both begin at level three:

```
A = 3 2 3 4 3 4 5 4 3 4 5 4 5 6
B = 3 4 3 2 3 2 1 2 3 2 1 2 1 0
```

Each is a contiguous stretch of a faithful crooked sequence, and each is faithful and crooked in
its own right (`pairA_faithful`, `pairB_faithful`, by the decidable criterion of batch 22 — the
route the commission's `isCrookedIvF_restrict` offered was not needed at this length). Each on
its own folds onto a member of the family (`pairA_served`, `pairB_served`), and **no member of
the family takes both**.

`not_pairAtLevel` is proved without enumerating the forty members of the band's family, and it
is the stronger statement that the enumeration would not give: `no_common_walk_pairA_pairB`
refutes a common walk of *any* shape, member of the family or not. The argument is the
opposite-arms obstruction `no_common_walk_of_opposite_arms`:

* `A` never falls below `b − 1 = 2` and is at `2` only at index one; `B` never rises above
  `b + 1 = 4` and is at `4` only at index one.
* A fold pins the token to time `0` at index `0` and moves it by at most one time per link, so
  the token's times form a contiguous stretch of `[0, ∞)`: whatever time it ends at, it has
  visited every earlier time.
* `A` reaches `b + 3 = 6`, so its token ends at a time whose centre is at least `b + 2`; `B`
  reaches `b − 3 = 0`, so its token ends at a time whose centre is at most `b − 2`. One of those
  two times comes first, and the other arm's token must cross it — which forces that crossing to
  happen at index one, hence at time one, hence the walk's first two centres lie on one side of
  the base. Then the other arm's value at index one, which lies on the other side, is out of
  reach.

So the two arms of a basepoint are not two arbitrary sequences that happen to share a level;
whatever carries the induction must retain that they join. The census (`census-batch33.c`,
output in `census-batch33.log`) enumerates the band's family — forty members, twelve serving
`A`, twelve serving `B`, none serving both — and finds exactly ten such pairs of arms at span
six, every one from two different basepoints, while all seventy-one basepoints of `bing 0 6`
are served.

The last section supplies what COMMISSION-batch33 §3 asks for on the family side: the **dual of
`isZigFree_cons`**, appending a pair of outer legs to a member of the family of the inner band
`[L+1, H−1]` to make a member of the family of `[L, H]` (`isZigFree_append_outer`). The census
of the trimming itself is reported in `REPORT-batch33.md`: the span drops by exactly one at
every step and never stalls, but the maximal stretch is not unique — the two greedy expansion
orders disagree at most basepoints — and at about a third of the basepoints the level of the
basepoint is extreme for an inner band, which is the range batch 29 already covers.

English proofs: COMMISSION-batch33.md §2–§3.
-/

namespace HPC.Fold

/-! ## The two stretches -/

/-- The forward stretch of `bing 0 6` from index 57. -/
def pairA : Fin 14 → ℤ := ![3, 2, 3, 4, 3, 4, 5, 4, 3, 4, 5, 4, 5, 6]

/-- The backward stretch of `bing 0 6` from index 13. -/
def pairB : Fin 14 → ℤ := ![3, 4, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 0]

set_option maxRecDepth 100000 in
theorem pairA_isLip : IsLip pairA := by
  unfold IsLip
  decide +kernel

set_option maxRecDepth 100000 in
theorem pairB_isLip : IsLip pairB := by
  unfold IsLip
  decide +kernel

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- `A` is faithful and crooked in its own right, by the decidable criterion of batch 22. -/
theorem pairA_faithful : IsCrookedIvF pairA pairA := by
  refine isCrookedIvF_of_check ?_
  unfold IsCrookedIvFCheck
  decide +kernel

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem pairB_faithful : IsCrookedIvF pairB pairB := by
  refine isCrookedIvF_of_check ?_
  unfold IsCrookedIvFCheck
  decide +kernel

/-! ## The opposite-arms obstruction

A fold assigns to each link of the arm a time of the walk, starting at time `0` and moving by at
most one time per link. The times it uses therefore form a contiguous stretch: whatever time the
token ends at, it has stood at every earlier time. -/

/-- **A fold visits every time below one it reaches.** -/
theorem exists_index_of_time {m : ℕ} {β : Fin m → ℕ}
    (hlip : ∀ j j' : Fin m, j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1)
    (h0 : ∀ j : Fin m, j.val = 0 → β j = 0) :
    ∀ (j0 : Fin m) (u : ℕ), u ≤ β j0 → ∃ j : Fin m, β j = u := by
  have H : ∀ (k : ℕ) (hk : k < m) (u : ℕ), u ≤ β ⟨k, hk⟩ → ∃ j : Fin m, β j = u := by
    intro k
    induction k with
    | zero =>
        intro hk u hu
        rw [h0 ⟨0, hk⟩ rfl] at hu
        exact ⟨⟨0, hk⟩, by rw [h0 ⟨0, hk⟩ rfl]; omega⟩
    | succ k ih =>
        intro hk u hu
        have hk' : k < m := by omega
        have hstep := hlip ⟨k, hk'⟩ ⟨k + 1, hk⟩ rfl
        rw [abs_le] at hstep
        rcases le_or_gt u (β ⟨k, hk'⟩) with h | h
        · exact ih hk' u h
        · exact ⟨⟨k + 1, hk⟩, by omega⟩
  intro j0 u hu
  exact H j0.val j0.isLt u (by simpa using hu)

/-- **Two arms that open in opposite directions and reach opposite extremes fold onto no common
walk.** Both arms start at the base level `b`; `f` dips to `b − 1` at its first step and never
goes lower elsewhere, `g` rises to `b + 1` at its first step and never goes higher elsewhere,
and `f` reaches `b + 3` while `g` reaches `b − 3`. No walk of unit steps takes both — no
hypothesis on the walk beyond moving one level per step, so this covers the whole free family
and everything outside it. -/
theorem no_common_walk_of_opposite_arms {m len : ℕ} {f g : Fin m → ℤ} {c : ℕ → ℤ} {b : ℤ}
    (hm : 1 < m)
    (hc : ∀ u, u + 1 < len → |c (u + 1) - c u| ≤ 1)
    (hf0 : ∀ j : Fin m, j.val = 0 → f j = b)
    (hf1 : ∀ j : Fin m, j.val = 1 → f j = b - 1)
    (hg1 : ∀ j : Fin m, j.val = 1 → g j = b + 1)
    (hfdip : ∀ j : Fin m, f j ≤ b - 1 → j.val = 1)
    (hgrise : ∀ j : Fin m, b + 1 ≤ g j → j.val = 1)
    (hfhigh : ∃ j : Fin m, b + 3 ≤ f j)
    (hglow : ∃ j : Fin m, g j ≤ b - 3)
    (hf : FoldsOnto f len c) (hg : FoldsOnto g len c) : False := by
  obtain ⟨bf, hbflt, hbflip, hbf0, hbfw⟩ := hf
  obtain ⟨bg, hbglt, hbglip, hbg0, hbgw⟩ := hg
  have hz : (0 : ℕ) < m := by omega
  set z : Fin m := ⟨0, hz⟩ with hzdef
  set o : Fin m := ⟨1, hm⟩ with hodef
  have hbfz : bf z = 0 := hbf0 z rfl
  have hbgz : bg z = 0 := hbg0 z rfl
  have hbfo : bf o ≤ 1 := by
    have := hbflip z o rfl
    rw [hbfz, abs_le] at this
    omega
  have hbgo : bg o ≤ 1 := by
    have := hbglip z o rfl
    rw [hbgz, abs_le] at this
    omega
  have hc0 : |b - c 0| ≤ 1 := by
    have := hbfw z
    rwa [hf0 z rfl, hbfz] at this
  rw [abs_le] at hc0
  have hstep : |c 1 - c 0| ≤ 1 ∨ len ≤ 1 := by
    rcases Nat.lt_or_ge 1 len with h | h
    · exact Or.inl (by simpa using hc 0 (by omega))
    · exact Or.inr h
  obtain ⟨jh, hjh⟩ := hfhigh
  obtain ⟨jl, hjl⟩ := hglow
  have hp : b + 2 ≤ c (bf jh) := by
    have := hbfw jh
    rw [abs_le] at this
    omega
  have hq : c (bg jl) ≤ b - 2 := by
    have := hbgw jl
    rw [abs_le] at this
    omega
  rcases le_total (bg jl) (bf jh) with hle | hle
  · -- the low time comes first, so `f`'s token must cross it
    obtain ⟨j, hj⟩ := exists_index_of_time hbflip hbf0 jh _ hle
    have hw := hbfw j
    rw [hj, abs_le] at hw
    have hj1 : j.val = 1 := hfdip j (by omega)
    have hjo : j = o := Fin.ext hj1
    have hqle : bg jl ≤ 1 := by rw [← hj, hjo]; exact hbfo
    have hq1 : bg jl = 1 := by
      rcases Nat.eq_zero_or_pos (bg jl) with h0' | h0'
      · rw [h0'] at hq; omega
      · omega
    have hqlt : bg jl < len := hbglt jl
    rw [hq1] at hq
    have hs : |c 1 - c 0| ≤ 1 := by
      rcases hstep with h | h
      · exact h
      · omega
    rw [abs_le] at hs
    have hgw := hbgw o
    rw [hg1 o rfl, abs_le] at hgw
    have hcase : bg o = 0 ∨ bg o = 1 := by omega
    rcases hcase with h | h <;> rw [h] at hgw <;> omega
  · -- the high time comes first, so `g`'s token must cross it
    obtain ⟨j, hj⟩ := exists_index_of_time hbglip hbg0 jl _ hle
    have hw := hbgw j
    rw [hj, abs_le] at hw
    have hj1 : j.val = 1 := hgrise j (by omega)
    have hjo : j = o := Fin.ext hj1
    have hple : bf jh ≤ 1 := by rw [← hj, hjo]; exact hbgo
    have hp1 : bf jh = 1 := by
      rcases Nat.eq_zero_or_pos (bf jh) with h0' | h0'
      · rw [h0'] at hp; omega
      · omega
    have hplt : bf jh < len := hbflt jh
    rw [hp1] at hp
    have hs : |c 1 - c 0| ≤ 1 := by
      rcases hstep with h | h
      · exact h
      · omega
    rw [abs_le] at hs
    have hfw := hbfw o
    rw [hf1 o rfl, abs_le] at hfw
    have hcase : bf o = 0 ∨ bf o = 1 := by omega
    rcases hcase with h | h <;> rw [h] at hfw <;> omega

/-- **No walk at all takes both stretches.** Not merely no member of the free family: the walk
is an arbitrary `zigWalk`, and the only property of it used is that it moves one level per
step. -/
theorem no_common_walk_pairA_pairB (ts : List ℤ)
    (hA : FoldsOnto pairA (zigWalk ts).1 (zigWalk ts).2)
    (hB : FoldsOnto pairB (zigWalk ts).1 (zigWalk ts).2) : False := by
  refine no_common_walk_of_opposite_arms (b := 3) (by norm_num)
    (fun u hu => le_of_eq (zigWalk_step ts u hu)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hA hB
  · intro j hj; rw [show j = ⟨0, by norm_num⟩ from Fin.ext hj]; rfl
  · intro j hj; rw [show j = ⟨1, by norm_num⟩ from Fin.ext hj]; rfl
  · intro j hj; rw [show j = ⟨1, by norm_num⟩ from Fin.ext hj]; rfl
  · decide
  · decide
  · exact ⟨⟨13, by norm_num⟩, by norm_num [pairA]⟩
  · exact ⟨⟨13, by norm_num⟩, by norm_num [pairB]⟩

/-! ## The pair statement, and its refutation -/

/-- **The pair statement.** Two faithful crooked sequences confined to a band and starting
within one of a common centre fold onto a common member of the family. -/
def PairAtLevel : Prop :=
  ∀ (m m' : ℕ) (f : Fin m → ℤ) (g : Fin m' → ℤ) (σf : Fin m → ℤ) (σg : Fin m' → ℤ) (L H : ℤ),
    0 < m → 0 < m' → IsCrookedIvF f σf → IsCrookedIvF g σg →
    (∀ j, L ≤ f j) → (∀ j, f j ≤ H) → (∀ j, L ≤ g j) → (∀ j, g j ≤ H) → L + 3 ≤ H →
    (∀ j : Fin m, j.val = 0 → ∀ j' : Fin m', j'.val = 0 → f j = g j') →
    ∃ ts : List ℤ, IsZigFree L H ts ∧
      FoldsOnto f (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto g (zigWalk ts).1 (zigWalk ts).2

/-- **`PairAtLevel` is false.** -/
theorem not_pairAtLevel : ¬ PairAtLevel := by
  intro h
  obtain ⟨ts, -, hA, hB⟩ :=
    h 14 14 pairA pairB pairA pairB 0 6 (by norm_num) (by norm_num) pairA_faithful pairB_faithful
      (by decide) (by decide) (by decide) (by decide) (by norm_num) (by decide)
  exact no_common_walk_pairA_pairB ts hA hB

/-! ## Each stretch alone is served

So the failure is in the pairing and not in either sequence. The census finds twelve members of
the band's family serving `A` and twelve serving `B`; the two exhibited here are the shortest of
each. (The commission names `[3, 2, 4, 1, 5]` for `A` and `[3, 4, 2, 5, 1]` for `B`; the census
has those two the other way round — `[3, 2, 4, 1, 5]` serves `B` and `[3, 4, 2, 5, 1]` serves
`A`.) -/

set_option maxRecDepth 10000 in
theorem pairA_served :
    ∃ ts : List ℤ, IsZigFree 0 6 ts ∧ FoldsOnto pairA (zigWalk ts).1 (zigWalk ts).2 := by
  have hlev : zigLevels [(3 : ℤ), 5, 1] = [3, 4, 5, 4, 3, 2, 1] := by
    simp [zigLevels, zigTail, stepRun]
  have hlen : (zigWalk [(3 : ℤ), 5, 1]).1 = 7 := by simp [zigWalk, hlev]
  have hval : ∀ u, (zigWalk [(3 : ℤ), 5, 1]).2 u = [(3 : ℤ), 4, 5, 4, 3, 2, 1].getD u 0 := by
    intro u; simp [zigWalk, hlev]
  refine ⟨[3, 5, 1], ?_, ?_⟩
  · refine ⟨?_, by simp, ?_, ?_, ?_⟩
    · intro t ht; fin_cases ht <;> norm_num
    · intro j hj
      simp only [List.length_cons, List.length_nil] at hj
      obtain rfl : j = 0 := by omega
      norm_num
    · intro j _ hj'
      simp only [List.length_cons, List.length_nil] at hj'
      omega
    · right; norm_num
  · refine ⟨![0, 0, 0, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2], ?_, ?_, ?_, ?_⟩
    · intro j; rw [hlen]; fin_cases j <;> decide
    · decide
    · decide
    · intro j; rw [hval]; fin_cases j <;> decide

set_option maxRecDepth 10000 in
theorem pairB_served :
    ∃ ts : List ℤ, IsZigFree 0 6 ts ∧ FoldsOnto pairB (zigWalk ts).1 (zigWalk ts).2 := by
  have hlev : zigLevels [(3 : ℤ), 1, 5] = [3, 2, 1, 2, 3, 4, 5] := by
    simp [zigLevels, zigTail, stepRun]
  have hlen : (zigWalk [(3 : ℤ), 1, 5]).1 = 7 := by simp [zigWalk, hlev]
  have hval : ∀ u, (zigWalk [(3 : ℤ), 1, 5]).2 u = [(3 : ℤ), 2, 1, 2, 3, 4, 5].getD u 0 := by
    intro u; simp [zigWalk, hlev]
  refine ⟨[3, 1, 5], ?_, ?_⟩
  · refine ⟨?_, by simp, ?_, ?_, ?_⟩
    · intro t ht; fin_cases ht <;> norm_num
    · intro j hj
      simp only [List.length_cons, List.length_nil] at hj
      obtain rfl : j = 0 := by omega
      norm_num
    · intro j _ hj'
      simp only [List.length_cons, List.length_nil] at hj'
      omega
    · left; norm_num
  · refine ⟨![0, 0, 0, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2], ?_, ?_, ?_, ?_⟩
    · intro j; rw [hlen]; fin_cases j <;> decide
    · decide
    · decide
    · intro j; rw [hval]; fin_cases j <;> decide

/-! ## Appending the outer legs

The dual of `isZigFree_cons`: where that prefixes a sweep at the base, this appends a pair of
legs at the far end, turning a member of the family of the inner band `[L+1, H−1]` into a member
of the family of `[L, H]`. It is what the outside-in induction of COMMISSION-batch33 §3 needs on
the family side. The `ends` clause of `IsZigFree` pins the last two targets of the inner member
to `L + 2` and `H − 2` in one order or the other, so the two appended legs have amplitudes
`H − L − 3` and `H − L − 2`, both larger than every amplitude inside the inner member, and they
alternate with its last leg. -/

theorem getElem!_append2_left {l : List ℤ} {x y : ℤ} {j : ℕ} (hj : j < l.length) :
    (l ++ [x, y])[j]! = l[j]! := by
  rw [getElem!_pos (l ++ [x, y]) j (by simp; omega), getElem!_pos l j hj,
    List.getElem_append_left hj]

theorem getElem!_append2_fst {l : List ℤ} {x y : ℤ} : (l ++ [x, y])[l.length]! = x := by
  rw [getElem!_pos (l ++ [x, y]) l.length (by simp)]; simp

theorem getElem!_append2_snd {l : List ℤ} {x y : ℤ} : (l ++ [x, y])[l.length + 1]! = y := by
  rw [getElem!_pos (l ++ [x, y]) (l.length + 1) (by simp)]; simp

/-- Appending the legs `L + 1`, `H − 1` to an inner member whose last two targets are
`L + 2, H − 2`. -/
theorem isZigFree_append_two {L H x y : ℤ} {ts : List ℤ} (hLH : L + 5 ≤ H)
    (hb : ∀ t ∈ ts, L + 2 ≤ t ∧ t ≤ H - 2)
    (hlen : 3 ≤ ts.length)
    (halt : ∀ j, j + 2 < ts.length → (ts[j+1]! - ts[j]!) * (ts[j+2]! - ts[j+1]!) < 0)
    (hamp : ∀ j, 1 ≤ j → j + 2 < ts.length → |ts[j+1]! - ts[j]!| < |ts[j+2]! - ts[j+1]!|)
    (hp : ts[ts.length - 2]! = L + 2) (hq : ts[ts.length - 1]! = H - 2)
    (hx : x = L + 1) (hy : y = H - 1) :
    IsZigFree L H (ts ++ [x, y]) := by
  have hlenA : (ts ++ [x, y]).length = ts.length + 2 := by simp
  subst hx; subst hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have := hb t ht; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> omega
  · omega
  · intro j hj
    rw [hlenA] at hj
    rcases Nat.lt_or_ge (j + 2) ts.length with hc | hc
    · rw [getElem!_append2_left (j := j) (by omega),
        getElem!_append2_left (j := j + 1) (by omega),
        getElem!_append2_left (j := j + 2) (by omega)]
      exact halt j hc
    · rcases Nat.lt_or_ge (j + 1) ts.length with hc2 | hc2
      · have e1 : ts[j]! = L + 2 := by rw [show j = ts.length - 2 by omega]; exact hp
        have e2 : ts[j + 1]! = H - 2 := by rw [show j + 1 = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega),
          getElem!_append2_left (j := j + 1) (by omega), e1, e2,
          show j + 2 = ts.length by omega, getElem!_append2_fst]
        nlinarith
      · have e2 : ts[j]! = H - 2 := by rw [show j = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega), e2,
          show j + 2 = ts.length + 1 by omega, show j + 1 = ts.length by omega,
          getElem!_append2_fst, getElem!_append2_snd]
        nlinarith
  · intro j hj1 hj
    rw [hlenA] at hj
    rcases Nat.lt_or_ge (j + 2) ts.length with hc | hc
    · rw [getElem!_append2_left (j := j) (by omega),
        getElem!_append2_left (j := j + 1) (by omega),
        getElem!_append2_left (j := j + 2) (by omega)]
      exact hamp j hj1 hc
    · rcases Nat.lt_or_ge (j + 1) ts.length with hc2 | hc2
      · have e1 : ts[j]! = L + 2 := by rw [show j = ts.length - 2 by omega]; exact hp
        have e2 : ts[j + 1]! = H - 2 := by rw [show j + 1 = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega),
          getElem!_append2_left (j := j + 1) (by omega), e1, e2,
          show j + 2 = ts.length by omega, getElem!_append2_fst]
        rw [abs_of_nonneg (by omega), abs_of_nonpos (by omega)]
        omega
      · have e2 : ts[j]! = H - 2 := by rw [show j = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega), e2,
          show j + 2 = ts.length + 1 by omega, show j + 1 = ts.length by omega,
          getElem!_append2_fst, getElem!_append2_snd]
        rw [abs_of_nonpos (by omega), abs_of_nonneg (by omega)]
        omega
  · left
    rw [hlenA, show ts.length + 2 - 2 = ts.length by omega,
      show ts.length + 2 - 1 = ts.length + 1 by omega, getElem!_append2_fst,
      getElem!_append2_snd]

/-- The mirror: appending the legs `H − 1`, `L + 1` to an inner member whose last two targets
are `H − 2, L + 2`. -/
theorem isZigFree_append_two' {L H x y : ℤ} {ts : List ℤ} (hLH : L + 5 ≤ H)
    (hb : ∀ t ∈ ts, L + 2 ≤ t ∧ t ≤ H - 2)
    (hlen : 3 ≤ ts.length)
    (halt : ∀ j, j + 2 < ts.length → (ts[j+1]! - ts[j]!) * (ts[j+2]! - ts[j+1]!) < 0)
    (hamp : ∀ j, 1 ≤ j → j + 2 < ts.length → |ts[j+1]! - ts[j]!| < |ts[j+2]! - ts[j+1]!|)
    (hp : ts[ts.length - 2]! = H - 2) (hq : ts[ts.length - 1]! = L + 2)
    (hx : x = H - 1) (hy : y = L + 1) :
    IsZigFree L H (ts ++ [x, y]) := by
  have hlenA : (ts ++ [x, y]).length = ts.length + 2 := by simp
  subst hx; subst hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have := hb t ht; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> omega
  · omega
  · intro j hj
    rw [hlenA] at hj
    rcases Nat.lt_or_ge (j + 2) ts.length with hc | hc
    · rw [getElem!_append2_left (j := j) (by omega),
        getElem!_append2_left (j := j + 1) (by omega),
        getElem!_append2_left (j := j + 2) (by omega)]
      exact halt j hc
    · rcases Nat.lt_or_ge (j + 1) ts.length with hc2 | hc2
      · have e1 : ts[j]! = H - 2 := by rw [show j = ts.length - 2 by omega]; exact hp
        have e2 : ts[j + 1]! = L + 2 := by rw [show j + 1 = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega),
          getElem!_append2_left (j := j + 1) (by omega), e1, e2,
          show j + 2 = ts.length by omega, getElem!_append2_fst]
        nlinarith
      · have e2 : ts[j]! = L + 2 := by rw [show j = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega), e2,
          show j + 2 = ts.length + 1 by omega, show j + 1 = ts.length by omega,
          getElem!_append2_fst, getElem!_append2_snd]
        nlinarith
  · intro j hj1 hj
    rw [hlenA] at hj
    rcases Nat.lt_or_ge (j + 2) ts.length with hc | hc
    · rw [getElem!_append2_left (j := j) (by omega),
        getElem!_append2_left (j := j + 1) (by omega),
        getElem!_append2_left (j := j + 2) (by omega)]
      exact hamp j hj1 hc
    · rcases Nat.lt_or_ge (j + 1) ts.length with hc2 | hc2
      · have e1 : ts[j]! = H - 2 := by rw [show j = ts.length - 2 by omega]; exact hp
        have e2 : ts[j + 1]! = L + 2 := by rw [show j + 1 = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega),
          getElem!_append2_left (j := j + 1) (by omega), e1, e2,
          show j + 2 = ts.length by omega, getElem!_append2_fst]
        rw [abs_of_nonpos (by omega), abs_of_nonneg (by omega)]
        omega
      · have e2 : ts[j]! = L + 2 := by rw [show j = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega), e2,
          show j + 2 = ts.length + 1 by omega, show j + 1 = ts.length by omega,
          getElem!_append2_fst, getElem!_append2_snd]
        rw [abs_of_nonneg (by omega), abs_of_nonpos (by omega)]
        omega
  · right
    rw [hlenA, show ts.length + 2 - 2 = ts.length by omega,
      show ts.length + 2 - 1 = ts.length + 1 by omega, getElem!_append2_fst,
      getElem!_append2_snd]

/-- **The dual of `isZigFree_cons`.** A member of the free family of the inner band
`[L+1, H−1]` becomes a member of the free family of `[L, H]` when the two outer legs are
appended; which pair is appended is decided by the orientation of the inner member's end. -/
theorem isZigFree_append_outer {L H : ℤ} {ts : List ℤ} (hLH : L + 5 ≤ H)
    (h : IsZigFree (L + 1) (H - 1) ts) :
    IsZigFree L H (ts ++ [L + 1, H - 1]) ∨ IsZigFree L H (ts ++ [H - 1, L + 1]) := by
  have hb : ∀ t ∈ ts, L + 2 ≤ t ∧ t ≤ H - 2 := by
    intro t ht
    have := h.bounds t ht
    omega
  rcases h.ends with he | he
  · have h1 : ts[ts.length - 2]! = L + 2 := by
      have := congrArg Prod.fst he
      simp only at this
      omega
    have h2 : ts[ts.length - 1]! = H - 2 := by
      have := congrArg Prod.snd he
      simp only at this
      omega
    exact Or.inl (isZigFree_append_two hLH hb h.len h.alt h.amp h1 h2 rfl rfl)
  · have h1 : ts[ts.length - 2]! = H - 2 := by
      have := congrArg Prod.fst he
      simp only at this
      omega
    have h2 : ts[ts.length - 1]! = L + 2 := by
      have := congrArg Prod.snd he
      simp only at this
      omega
    exact Or.inr (isZigFree_append_two' hLH hb h.len h.alt h.amp h1 h2 rfl rfl)

end HPC.Fold
