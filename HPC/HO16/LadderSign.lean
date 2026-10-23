import HPC.HO16.LadderDefs

/-!
# Batch 197, §5: sign sequences, their lists of heights, and one flip

Commission 197 §5, steps 3–4, in combinatorial form. A sign sequence `σ : ℕ → Bool` on the levels
`t_q = q / N` (`true` for `u > 0`) gives the list `sgnList N σ` of the midpoints
`midH N q = (t_q + t_{q+1}) / 2` of its sign changes (`chg N σ`); it has odd length when
`σ 0 = false` and `σ N = true` (`odd_length_chg`). Two sign sequences differing only at one level
`q` (a *flip*) have change lists `A ++ X₁ ++ B` and `A ++ X₂ ++ B` (`chg_flip`) with
`X₁, X₂ ⊆ [q - 1, q]` (`chgPair_cases`). On an edge whose ends carry the two lists, with the event
read off the lists (`wedgeEv`: a wedge at the second end iff the second list is two longer),
every point of every piece has a height that is either the midpoint of a sign change at one of
the ends, or within `1 / (2N)` of `t_q` with the sign at `q` different at the two ends
(`heightOK_of_mem_piece`). This is what puts the sheets into `U` (`LadderExists.lean`).
-/

namespace HPC.HO16

open Set

noncomputable section

/-- The sign changes of `σ` among the levels `0, …, N`. -/
def chg (N : ℕ) (σ : ℕ → Bool) : List ℕ := (List.range N).filter fun q => σ q != σ (q + 1)

/-- The midpoint of the levels `q / N` and `(q + 1) / N`. -/
def midH (N q : ℕ) : ℝ := (2 * q + 1) / (2 * N)

/-- The list of heights of a sign sequence. -/
def sgnList (N : ℕ) (σ : ℕ → Bool) : List ℝ := (chg N σ).map (midH N)

/-- The index of the first difference of two lists. -/
def firstDiff : List ℝ → List ℝ → ℕ
  | a :: l, b :: l' => if a = b then firstDiff l l' + 1 else 0
  | _, _ => 0

/-- The event of an edge read off the lists at its ends: a wedge at the second end, at the first
difference, tip at parameter `½`, at the mean height of the two new entries, iff the second list
is two longer. -/
def wedgeEv (l l' : List ℝ) : Option (ℕ × ℝ × ℝ) :=
  if l'.length = l.length + 2 then
    some (firstDiff l l' + 1, 1 / 2, (l'.getD (firstDiff l l') 0 + l'.getD (firstDiff l l' + 1) 0) / 2)
  else none

/-- The sign changes next to the level `q`. -/
def chgPair (σ : ℕ → Bool) (q : ℕ) : List ℕ :=
  (if σ (q - 1) != σ q then [q - 1] else []) ++ (if σ q != σ (q + 1) then [q] else [])

theorem mem_chg {N : ℕ} {σ : ℕ → Bool} {q : ℕ} : q ∈ chg N σ ↔ q < N ∧ σ q ≠ σ (q + 1) := by
  simp [chg]

theorem chg_congr {N : ℕ} {σ σ' : ℕ → Bool} (h : ∀ q ≤ N, σ q = σ' q) : chg N σ = chg N σ' := by
  unfold chg
  apply List.filter_congr
  intro q hq
  rw [List.mem_range] at hq
  rw [h q hq.le, h (q + 1) hq]

theorem sgnList_congr {N : ℕ} {σ σ' : ℕ → Bool} (h : ∀ q ≤ N, σ q = σ' q) :
    sgnList N σ = sgnList N σ' := by
  rw [sgnList, sgnList, chg_congr h]

theorem chg_succ (n : ℕ) (σ : ℕ → Bool) :
    chg (n + 1) σ = chg n σ ++ (if σ n != σ (n + 1) then [n] else []) := by
  simp only [chg, List.range_succ, List.filter_append]
  congr 1
  simp only [List.filter_cons, List.filter_nil]

theorem length_chg_mod (σ : ℕ → Bool) :
    ∀ n, (chg n σ).length % 2 = if σ 0 = σ n then 0 else 1
  | 0 => by simp [chg]
  | n + 1 => by
    have ih := length_chg_mod σ n
    rw [chg_succ, List.length_append]
    cases h0 : σ 0 <;> cases hn : σ n <;> cases hn1 : σ (n + 1) <;> simp_all <;> omega

theorem odd_length_chg {N : ℕ} {σ : ℕ → Bool} (h0 : σ 0 = false) (hN : σ N = true) :
    Odd (chg N σ).length := by
  rw [Nat.odd_iff, length_chg_mod, h0, hN]
  rfl

theorem midH_mem {N q : ℕ} (hq : q < N) : midH N q ∈ Ioo (0 : ℝ) 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq' : (q : ℝ) + 1 ≤ N := by exact_mod_cast hq
  unfold midH
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]; linarith

theorem midH_inj {N : ℕ} (hN : 0 < N) {a b : ℕ} (h : midH N a = midH N b) : a = b := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold midH at h
  rw [div_left_inj' (by positivity)] at h
  exact_mod_cast (by linarith : (a : ℝ) = b)

theorem abs_midH_pred {N q : ℕ} (hN : 0 < N) (hq : 0 < q) :
    |midH N (q - 1) - q / N| = 1 / (2 * N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : ((q - 1 : ℕ) : ℝ) = q - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [midH, this]
  rw [show (2 * ((q : ℝ) - 1) + 1) / (2 * N) - q / N = -(1 / (2 * N)) by field_simp; ring]
  rw [abs_neg, abs_of_pos (by positivity)]

theorem abs_midH_self {N q : ℕ} (hN : 0 < N) : |midH N q - q / N| = 1 / (2 * N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [midH, show (2 * (q : ℝ) + 1) / (2 * N) - q / N = 1 / (2 * N) by field_simp; ring]
  rw [abs_of_pos (by positivity)]

theorem midH_mean {N q : ℕ} (hN : 0 < N) (hq : 0 < q) :
    (midH N (q - 1) + midH N q) / 2 = q / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : ((q - 1 : ℕ) : ℝ) = q - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [midH, midH, this]
  field_simp
  ring

/-! ### One flip -/

theorem range_split {N q : ℕ} (hq0 : 0 < q) (hqN : q < N) :
    List.range N = List.range (q - 1) ++ [q - 1, q] ++ List.range' (q + 1) (N - (q + 1)) := by
  have h2 : [q - 1, q] = List.range' (0 + 1 * (q - 1)) 2 := by
    simp only [List.range', zero_add, one_mul, List.cons.injEq, and_true, true_and]
    omega
  rw [h2, List.range_eq_range', List.range_eq_range', List.range'_append]
  have h3 : q + 1 = 0 + 1 * (q - 1 + 2) := by omega
  rw [h3, List.range'_append]
  congr 1
  omega

theorem chg_split (N : ℕ) (σ : ℕ → Bool) {q : ℕ} (hq0 : 0 < q) (hqN : q < N) :
    chg N σ = (List.range (q - 1)).filter (fun r => σ r != σ (r + 1)) ++ chgPair σ q ++
      (List.range' (q + 1) (N - (q + 1))).filter (fun r => σ r != σ (r + 1)) := by
  rw [chg, range_split hq0 hqN, List.filter_append, List.filter_append]
  congr 2
  have hq : q - 1 + 1 = q := by omega
  simp only [List.filter_cons, List.filter_nil, chgPair, hq]
  split_ifs <;> simp_all

/-- **One flip**: two sign sequences differing only at the level `q` have change lists
`A ++ X₁ ++ B` and `A ++ X₂ ++ B`. -/
theorem chg_flip {N q : ℕ} (hq0 : 0 < q) (hqN : q < N) {σ₁ σ₂ : ℕ → Bool}
    (hag : ∀ r ≤ N, r ≠ q → σ₁ r = σ₂ r) :
    ∃ A B : List ℕ, (∀ x ∈ A, x + 1 < q) ∧ (∀ x ∈ B, q < x) ∧
      chg N σ₁ = A ++ chgPair σ₁ q ++ B ∧ chg N σ₂ = A ++ chgPair σ₂ q ++ B := by
  refine ⟨(List.range (q - 1)).filter (fun r => σ₁ r != σ₁ (r + 1)),
    (List.range' (q + 1) (N - (q + 1))).filter (fun r => σ₁ r != σ₁ (r + 1)), ?_, ?_,
    chg_split N σ₁ hq0 hqN, ?_⟩
  · intro x hx
    rw [List.mem_filter, List.mem_range] at hx
    omega
  · intro x hx
    rw [List.mem_filter, List.mem_range'_1] at hx
    omega
  · have hA2 : (List.range (q - 1)).filter (fun r => σ₂ r != σ₂ (r + 1)) =
        (List.range (q - 1)).filter (fun r => σ₁ r != σ₁ (r + 1)) := by
      apply List.filter_congr
      intro r hr
      rw [List.mem_range] at hr
      rw [hag r (by omega) (by omega), hag (r + 1) (by omega) (by omega)]
    have hB2 : (List.range' (q + 1) (N - (q + 1))).filter (fun r => σ₂ r != σ₂ (r + 1)) =
        (List.range' (q + 1) (N - (q + 1))).filter (fun r => σ₁ r != σ₁ (r + 1)) := by
      apply List.filter_congr
      intro r hr
      rw [List.mem_range'_1] at hr
      rw [hag r (by omega) (by omega), hag (r + 1) (by omega) (by omega)]
    rw [chg_split N σ₂ hq0 hqN, hA2, hB2]

theorem chgPair_cases (σ₁ σ₂ : ℕ → Bool) (q : ℕ) (hm : σ₁ (q - 1) = σ₂ (q - 1))
    (hp : σ₁ (q + 1) = σ₂ (q + 1)) :
    (σ₁ q = σ₂ q ∧ chgPair σ₁ q = chgPair σ₂ q) ∨
    (σ₁ q ≠ σ₂ q ∧ ((chgPair σ₁ q = [q - 1] ∧ chgPair σ₂ q = [q]) ∨
      (chgPair σ₁ q = [q] ∧ chgPair σ₂ q = [q - 1]))) ∨
    (σ₁ q ≠ σ₂ q ∧ chgPair σ₁ q = [] ∧ chgPair σ₂ q = [q - 1, q]) ∨
    (chgPair σ₁ q = [q - 1, q] ∧ chgPair σ₂ q = []) := by
  unfold chgPair
  rw [← hm, ← hp]
  generalize σ₁ (q - 1) = a
  generalize σ₁ (q + 1) = c
  generalize σ₁ q = b
  generalize σ₂ q = b'
  cases a <;> cases b <;> cases b' <;> cases c <;> simp

/-! ### Heights on a flip edge -/

/-- The heights allowed on an edge whose ends carry the sign sequences `σ₁`, `σ₂`, differing at
most at the level `q`. -/
def HeightOK (N : ℕ) (σ₁ σ₂ : ℕ → Bool) (q : ℕ) (h : ℝ) : Prop :=
  (∃ r, (r ∈ chg N σ₁ ∨ r ∈ chg N σ₂) ∧ h = midH N r) ∨
    (σ₁ q ≠ σ₂ q ∧ |h - q / N| ≤ 1 / (2 * N))

theorem snd_mem_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b p : E × ℝ}
    (hp : p ∈ segment ℝ a b) : p.2 ∈ segment ℝ a.2 b.2 := by
  obtain ⟨c, d, hc, hd, hcd, rfl⟩ := hp
  exact ⟨c, d, hc, hd, hcd, by simp⟩

theorem heightOK_of_segment {N : ℕ} {σ₁ σ₂ : ℕ → Bool} {q : ℕ} {c c' h : ℝ}
    (hcc : (c = c' ∧ HeightOK N σ₁ σ₂ q c) ∨
      (σ₁ q ≠ σ₂ q ∧ |c - q / N| ≤ 1 / (2 * N) ∧ |c' - q / N| ≤ 1 / (2 * N)))
    (hh : h ∈ segment ℝ c c') : HeightOK N σ₁ σ₂ q h := by
  rcases hcc with ⟨rfl, hc⟩ | ⟨hσ, h1, h2⟩
  · rw [segment_same, Set.mem_singleton_iff] at hh
    rwa [hh]
  · right
    refine ⟨hσ, ?_⟩
    rw [segment_eq_uIcc, mem_uIcc] at hh
    rw [abs_le] at h1 h2 ⊢
    rcases hh with ⟨k1, k2⟩ | ⟨k1, k2⟩ <;> constructor <;> linarith

theorem getD_map_lt {f : ℕ → ℝ} {L : List ℕ} {n : ℕ} (hn : n < L.length) :
    (L.map f).getD n 0 = f (L.getD n 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hn), List.getD_eq_getElem _ _ hn,
    List.getElem_map]

theorem getD_mem_of_lt {L : List ℕ} {n : ℕ} (hn : n < L.length) : L.getD n 0 ∈ L := by
  rw [List.getD_eq_getElem _ _ hn]; exact List.getElem_mem hn

theorem firstDiff_append_left (A l l' : List ℝ) :
    firstDiff (A ++ l) (A ++ l') = A.length + firstDiff l l' := by
  induction A with
  | nil => simp
  | cons a A ih =>
    rw [List.cons_append, List.cons_append, firstDiff, if_pos rfl, ih, List.length_cons]; ring

theorem firstDiff_le : ∀ l l' : List ℝ, firstDiff l l' ≤ l.length
  | a :: l, b :: l' => by
    simp only [firstDiff, List.length_cons]
    split_ifs
    · exact Nat.succ_le_succ (firstDiff_le l l')
    · exact Nat.zero_le _
  | [], _ => by simp [firstDiff]
  | _ :: _, [] => by simp [firstDiff]

/-- **Heights on a flip edge.** -/
theorem heightOK_of_mem_piece {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N q : ℕ}
    (hN : 0 < N) (hq0 : 0 < q) (hqN : q < N) {σ₁ σ₂ : ℕ → Bool}
    (hag : ∀ r ≤ N, r ≠ q → σ₁ r = σ₂ r) {y : E → List ℝ} {s : E × E}
    (h1 : y s.1 = sgnList N σ₁) (h2 : y s.2 = sgnList N σ₂)
    (hlen : ¬ (y s.1).length = (y s.2).length + 2) {i : ℕ} {p : E × ℝ}
    (hp : p ∈ ladderPiece y s (wedgeEv (y s.1) (y s.2)) i) : HeightOK N σ₁ σ₂ q p.2 := by
  obtain ⟨A, B, hA, hB, e1, e2⟩ := chg_flip hq0 hqN hag
  have hcases := chgPair_cases σ₁ σ₂ q (hag _ (by omega) (by omega)) (hag _ (by omega) (by omega))
  have hl1 : y s.1 = (A ++ chgPair σ₁ q ++ B).map (midH N) := by rw [h1, sgnList, e1]
  have hl2 : y s.2 = (A ++ chgPair σ₂ q ++ B).map (midH N) := by rw [h2, sgnList, e2]
  have hmem1 : ∀ r ∈ A ++ chgPair σ₁ q ++ B, r ∈ chg N σ₁ := fun r hr => e1 ▸ hr
  have hmem2 : ∀ r ∈ A ++ chgPair σ₂ q ++ B, r ∈ chg N σ₂ := fun r hr => e2 ▸ hr
  -- reading entries of the three-part lists
  have hget : ∀ (X : List ℕ) (n : ℕ), n < (A ++ X ++ B).length →
      ((A ++ X ++ B).map (midH N)).getD n 0 = midH N ((A ++ X ++ B).getD n 0) :=
    fun X n hn => getD_map_lt hn
  have hA' : ∀ (X : List ℕ) (n : ℕ), n < A.length → (A ++ X ++ B).getD n 0 = A.getD n 0 := by
    intro X n hn
    rw [List.append_assoc, List.getD_append _ _ _ _ hn]
  have hB' : ∀ (X : List ℕ) (n : ℕ), A.length + X.length ≤ n →
      (A ++ X ++ B).getD n 0 = B.getD (n - (A.length + X.length)) 0 := by
    intro X n hn
    rw [List.getD_append_right _ _ _ _ (by simpa using hn)]
    simp
  have hX' : ∀ (X : List ℕ) (n : ℕ), A.length ≤ n → n < A.length + X.length →
      (A ++ X ++ B).getD n 0 = X.getD (n - A.length) 0 := by
    intro X n hn hn'
    rw [List.getD_append _ _ _ _ (by simpa using hn'), List.getD_append_right _ _ _ _ hn]
  have noneCase : (chgPair σ₁ q).length = (chgPair σ₂ q).length →
      (∀ n < (chgPair σ₁ q).length,
        (midH N ((chgPair σ₁ q).getD n 0) = midH N ((chgPair σ₂ q).getD n 0) ∧
          HeightOK N σ₁ σ₂ q (midH N ((chgPair σ₁ q).getD n 0))) ∨
        (σ₁ q ≠ σ₂ q ∧ |midH N ((chgPair σ₁ q).getD n 0) - q / N| ≤ 1 / (2 * N) ∧
          |midH N ((chgPair σ₂ q).getD n 0) - q / N| ≤ 1 / (2 * N))) →
      HeightOK N σ₁ σ₂ q p.2 := by
    intro hXl hXc
    have hlen12 : (y s.1).length = (y s.2).length := by
      rw [hl1, hl2]; simp only [List.length_map, List.length_append]; omega
    have hev : wedgeEv (y s.1) (y s.2) = none := by
      unfold wedgeEv; rw [if_neg]; omega
    rw [hev] at hp
    simp only [ladderPiece] at hp
    split_ifs at hp with hi
    swap; · exact absurd hp (notMem_empty _)
    have hh := snd_mem_segment hp
    simp only at hh
    refine heightOK_of_segment ?_ hh
    have hn1 : i - 1 < (A ++ chgPair σ₁ q ++ B).length := by
      have := hi.2; rw [hl1, List.length_map] at this; omega
    have hn2 : i - 1 < (A ++ chgPair σ₂ q ++ B).length := by
      have := hi.2; rw [hlen12, hl2, List.length_map] at this; omega
    unfold ladderY
    rw [hl1, hl2, hget _ _ hn1, hget _ _ hn2]
    by_cases ha : i - 1 < A.length
    · rw [hA' _ _ ha, hA' _ _ ha]
      exact Or.inl ⟨rfl, Or.inl ⟨_, Or.inl (hmem1 _ (by
        simp only [List.mem_append]; exact Or.inl (Or.inl (getD_mem_of_lt ha)))), rfl⟩⟩
    by_cases hb : A.length + (chgPair σ₁ q).length ≤ i - 1
    · rw [hB' _ _ hb, hB' _ _ (hXl ▸ hb), hXl]
      have hb' : i - 1 - (A.length + (chgPair σ₂ q).length) < B.length := by
        simp only [List.length_append] at hn2; omega
      exact Or.inl ⟨rfl, Or.inl ⟨_, Or.inl (hmem1 _ (by
        simp only [List.mem_append]; exact Or.inr (getD_mem_of_lt (hXl ▸ hb')))), rfl⟩⟩
    rw [hX' _ _ (by omega) (by omega), hX' _ _ (by omega) (by omega)]
    exact hXc _ (by omega)
  rcases hcases with ⟨hσ, hX⟩ | ⟨hσ, hX⟩ | ⟨hσ, hX1, hX2⟩ | ⟨hX1, hX2⟩
  · refine noneCase (by rw [hX]) fun n hn => Or.inl ⟨by rw [hX], Or.inl ⟨_, Or.inr (hmem2 _ ?_), rfl⟩⟩
    rw [← hX]
    simp only [List.mem_append]; exact Or.inl (Or.inr (getD_mem_of_lt hn))
  · refine noneCase (by rcases hX with ⟨e, e'⟩ | ⟨e, e'⟩ <;> rw [e, e'] <;> rfl) fun n hn => ?_
    right
    refine ⟨hσ, ?_⟩
    rcases hX with ⟨e, e'⟩ | ⟨e, e'⟩ <;> rw [e] at hn ⊢ <;> rw [e'] <;>
      simp only [List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff] at hn <;> subst hn <;>
      simp only [List.getD_cons_zero]
    · exact ⟨(abs_midH_pred hN hq0).le, (abs_midH_self hN).le⟩
    · exact ⟨(abs_midH_self hN).le, (abs_midH_pred hN hq0).le⟩
  rotate_left
  · -- a wedge at the first end is excluded by the orientation
    exfalso; apply hlen
    rw [hl1, hl2, hX1, hX2]; simp; omega
  -- the wedge at the second end
  have hX1l : (chgPair σ₁ q).length = 0 := by rw [hX1]; rfl
  have hX2l : (chgPair σ₂ q).length = 2 := by rw [hX2]; rfl
  have hlen1 : (y s.1).length = A.length + B.length := by
    rw [hl1]; simp only [List.length_map, List.length_append]; omega
  have hlen2 : (y s.2).length = A.length + B.length + 2 := by
    rw [hl2]; simp only [List.length_map, List.length_append]; omega
  have hfd : firstDiff (y s.1) (y s.2) = A.length := by
    rw [hl1, hl2, hX1, hX2, List.append_nil, List.map_append, List.map_append, List.map_append,
      List.append_assoc, firstDiff_append_left, List.length_map]
    rcases B with _ | ⟨b, B'⟩
    · simp [firstDiff]
    · have hb := hB b (by simp)
      have hne : midH N b ≠ midH N (q - 1) := fun h => by have := midH_inj hN h; omega
      simp [firstDiff, hne]
  have e2A : (y s.2).getD A.length 0 = midH N (q - 1) := by
    rw [hl2, hget _ _ (by simp only [List.length_append]; omega),
      hX' _ _ le_rfl (by omega), Nat.sub_self, hX2]
    rfl
  have e2B : (y s.2).getD (A.length + 1) 0 = midH N q := by
    rw [hl2, hget _ _ (by simp only [List.length_append]; omega),
      hX' _ _ (by omega) (by omega), hX2, show A.length + 1 - A.length = 1 by omega]
    rfl
  have hev : wedgeEv (y s.1) (y s.2) = some (A.length + 1, 1 / 2, (q : ℝ) / N) := by
    unfold wedgeEv
    rw [if_pos (by omega), hfd, e2A, e2B, midH_mean hN hq0]
  have eL : ∀ n < A.length, (y s.1).getD n 0 = midH N (A.getD n 0) ∧
      (y s.2).getD n 0 = midH N (A.getD n 0) := by
    intro n hn
    constructor
    · rw [hl1, hget _ _ (by simp only [List.length_append]; omega), hA' _ _ hn]
    · rw [hl2, hget _ _ (by simp only [List.length_append]; omega), hA' _ _ hn]
  have eU : ∀ k, A.length + 1 ≤ k → k ≤ A.length + B.length →
      ladderY y s.1 k = midH N (B.getD (k - 1 - A.length) 0) ∧
      ladderY y s.2 (k + 2) = midH N (B.getD (k - 1 - A.length) 0) := by
    intro k hk1 hk2
    unfold ladderY
    constructor
    · rw [hl1, hget _ _ (by simp only [List.length_append]; omega), hB' _ _ (by omega), hX1l,
        add_zero]
    · rw [hl2, hget _ _ (by simp only [List.length_append]; omega), hB' _ _ (by omega), hX2l,
        show k + 2 - 1 - (A.length + 2) = k - 1 - A.length by omega]
  have hBmem : ∀ k, A.length + 1 ≤ k → k ≤ A.length + B.length →
      B.getD (k - 1 - A.length) 0 ∈ chg N σ₁ := by
    intro k hk1 hk2
    exact hmem1 _ (by simp only [List.mem_append]; exact Or.inr (getD_mem_of_lt (by omega)))
  have hzz : ∀ k μ, A.length + 1 ≤ k → k ≤ A.length + B.length →
      (zzLine y s k μ).2 = midH N (B.getD (k - 1 - A.length) 0) := by
    intro k μ hk1 hk2
    rw [zzLine, lineMap_prod, (eU k hk1 hk2).1, (eU k hk1 hk2).2,
      AffineMap.lineMap_same_apply]
  have zzCase : ∀ k (a b : E × ℝ) μ₁ μ₂, A.length + 1 ≤ k → k ≤ A.length + B.length →
      a = zzLine y s k μ₁ → b = zzLine y s k μ₂ → p ∈ segment ℝ a b →
      HeightOK N σ₁ σ₂ q p.2 := by
    rintro k a b μ₁ μ₂ hk1 hk2 rfl rfl hpab
    have hh := snd_mem_segment hpab
    rw [hzz k μ₁ hk1 hk2, hzz k μ₂ hk1 hk2] at hh
    exact heightOK_of_segment (Or.inl ⟨rfl, Or.inl ⟨_, Or.inl (hBmem k hk1 hk2), rfl⟩⟩) hh
  rw [hev] at hp
  simp only [ladderPiece] at hp
  rw [hlen1] at hp
  rcases hp with ((((hp | hp) | hp) | hp) | hp) <;> split_ifs at hp with hc <;>
    try exact absurd hp (notMem_empty _)
  · have hh := snd_mem_segment hp
    simp only at hh
    unfold ladderY at hh
    rw [(eL (i - 1) (by omega)).1, (eL (i - 1) (by omega)).2] at hh
    exact heightOK_of_segment (Or.inl ⟨rfl, Or.inl ⟨_, Or.inl (hmem1 _ (by
      simp only [List.mem_append]; exact Or.inl (Or.inl (getD_mem_of_lt (by omega))))), rfl⟩⟩) hh
  · exact zzCase i _ _ _ _ hc.1 hc.2 rfl rfl hp
  · exact zzCase (i - 1) _ _ _ _ (by omega) (by omega) rfl rfl hp
  · exact zzCase (i - 2) _ _ _ _ (by omega) (by omega) rfl rfl hp
  · have hh := snd_mem_segment hp
    simp only at hh
    refine heightOK_of_segment (Or.inr ⟨hσ, by simp, ?_⟩) hh
    unfold ladderY
    rcases hc with rfl | rfl
    · rw [show A.length + 1 - 1 = A.length by omega, e2A]; exact (abs_midH_pred hN hq0).le
    · rw [show A.length + 1 + 1 - 1 = A.length + 1 by omega, e2B]; exact (abs_midH_self hN).le

end

end HPC.HO16
