import HPC.HO16.LadderSubdiv
import HPC.HO16.LadderSign
import HPC.HO16.LadderSep

/-!
# Batch 197, §5: a ladder inside `U` (`exists_ladder`, replacing H–O's Claim 15.1)

Commission 197 §5, steps 2–4. Given the sign function `u` of `LadderSep.lean` and a
decomposition `S₁` of `G` with short edges, put `N` levels `t_q = q / N`; at a vertex `v` the
sign sequence is `q ↦ (0 < u (v, t_q))` (`lσV`). Each edge `s` of `S₁` is cut into `N - 1` pieces;
at its `k`-th point the sign sequence is that of `s.2` at the levels `≤ k` and that of `s.1` above
(`lσE`), so consecutive points differ at the level `k + 1` only (one flip per piece). The list at a
point is `sgnList` of its sign sequence (`ly`); a piece is oriented backwards when its first end
carries two more heights than its second (`lo`), and its event is read off the two lists
(`wedgeEv`). This is a ladder (`lS_isLadder`), and by `heightOK_of_mem_piece` every point of a
sheet lies near two corners of an edge of `S₁` at which `u` has both signs (`lS_sheet_corners`),
hence in `U ∩ G × (0, 1)`.
-/

namespace HPC.HO16

open Set Metric

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Construction

variable (u : E × ℝ → ℝ) (N : ℕ) (S₁ : Finset (E × E))

/-- The sign sequence at a vertex. -/
def lσV (v : E) (q : ℕ) : Bool := decide (0 < u (v, (q : ℝ) / N))

/-- The sign sequence at the `k`-th point of the edge `s`. -/
def lσE (s : E × E) (k q : ℕ) : Bool := if q ≤ k then lσV u N s.2 q else lσV u N s.1 q

open Classical in
/-- The list of heights at a point. -/
def ly (x : E) : List ℝ :=
  if h : ∃ sk : (E × E) × ℕ, sk.1 ∈ S₁ ∧ sk.2 ≤ N - 1 ∧ subPt (N - 1) sk.1 sk.2 = x then
    sgnList N (lσE u N h.choose.1 h.choose.2) else []

/-- The orientation of the pieces. -/
def lo (s : E × E) (p : ℕ) : Bool :=
  decide ((ly u N S₁ (subPt (N - 1) s p)).length =
    (ly u N S₁ (subPt (N - 1) s (p + 1))).length + 2)

/-- The edges of the ladder. -/
def lS : Finset (E × E) := subdiv S₁ (N - 1) (lo u N S₁)

/-- The events of the ladder. -/
def lev (e : E × E) : Option (ℕ × ℝ × ℝ) := wedgeEv (ly u N S₁ e.1) (ly u N S₁ e.2)

end Construction

/-- The standing hypotheses of the construction. -/
structure LData (G : Set E) (u : E × ℝ → ℝ) (N : ℕ) (S₁ : Finset (E × E)) : Prop where
  hN : 2 ≤ N
  ne : ∀ s ∈ S₁, s.1 ≠ s.2
  G_eq : G = ⋃ s ∈ S₁, segment ℝ s.1 s.2
  dis : PairwiseEndpoints S₁
  u0 : ∀ x ∈ G, u (x, 0) ≤ 0
  u1 : ∀ x ∈ G, 0 < u (x, 1)

section Props

variable {G : Set E} {u : E × ℝ → ℝ} {N : ℕ} {S₁ : Finset (E × E)}

theorem LData.fst_mem (hd : LData G u N S₁) {s : E × E} (hs : s ∈ S₁) : s.1 ∈ G :=
  segment_subset_of_mem hd.G_eq hs (left_mem_segment ℝ _ _)

theorem LData.snd_mem (hd : LData G u N S₁) {s : E × E} (hs : s ∈ S₁) : s.2 ∈ G :=
  segment_subset_of_mem hd.G_eq hs (right_mem_segment ℝ _ _)

theorem LData.σV_zero (hd : LData G u N S₁) {x : E} (hx : x ∈ G) : lσV u N x 0 = false := by
  simp only [lσV, Nat.cast_zero, zero_div, decide_eq_false_iff_not, not_lt]
  exact hd.u0 x hx

theorem LData.σV_N (hd : LData G u N S₁) {x : E} (hx : x ∈ G) : lσV u N x N = true := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hd.hN; omega)
  simp only [lσV, div_self hN, decide_eq_true_eq]
  exact hd.u1 x hx

theorem LData.σE_zero (hd : LData G u N S₁) {s : E × E} (hs : s ∈ S₁) (k : ℕ) :
    lσE u N s k 0 = false := by
  simp only [lσE, Nat.zero_le, if_true]
  exact hd.σV_zero (hd.snd_mem hs)

theorem LData.σE_N (hd : LData G u N S₁) {s : E × E} (hs : s ∈ S₁) {k : ℕ} (hk : k ≤ N - 1) :
    lσE u N s k N = true := by
  have := hd.hN
  simp only [lσE, if_neg (show ¬ N ≤ k by omega)]
  exact hd.σV_N (hd.fst_mem hs)

theorem subPt_eq_fst_iff {s : E × E} (hs : s.1 ≠ s.2) {n k : ℕ} (hn : n ≠ 0) :
    subPt n s k = s.1 ↔ k = 0 := by
  rw [subPt, lineMap_eq_left_iff hs]
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  constructor
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact_mod_cast h
    · exact absurd h this
  · rintro rfl; simp

theorem subPt_eq_snd_iff {s : E × E} (hs : s.1 ≠ s.2) {n k : ℕ} (hn : n ≠ 0) :
    subPt n s k = s.2 ↔ k = n := by
  rw [subPt, lineMap_eq_right_iff hs]
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [div_eq_one_iff_eq this]
  exact_mod_cast Iff.rfl

theorem LData.sgnList_vertex (hd : LData G u N S₁) {s : E × E} (hs : s ∈ S₁) {k : ℕ}
    (hk : k ≤ N - 1) {x : E} (hx : subPt (N - 1) s k = x) (hxv : x = s.1 ∨ x = s.2) :
    sgnList N (lσE u N s k) = sgnList N (lσV u N x) := by
  have hN := hd.hN
  apply sgnList_congr
  intro q hq
  rcases hxv with rfl | rfl
  · have hk0 : k = 0 := (subPt_eq_fst_iff (hd.ne s hs) (by omega)).1 hx
    subst hk0
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · rw [hd.σE_zero hs, hd.σV_zero (hd.fst_mem hs)]
    · simp only [lσE, if_neg (show ¬ q ≤ 0 by omega)]
  · have hk1 : k = N - 1 := (subPt_eq_snd_iff (hd.ne s hs) (by omega)).1 hx
    subst hk1
    by_cases hqN : q ≤ N - 1
    · simp only [lσE, if_pos hqN]
    · have : q = N := by omega
      subst this
      rw [hd.σE_N hs le_rfl, hd.σV_N (hd.snd_mem hs)]

theorem LData.sgnList_wd (hd : LData G u N S₁) {s s' : E × E} (hs : s ∈ S₁) (hs' : s' ∈ S₁)
    {k k' : ℕ} (hk : k ≤ N - 1) (hk' : k' ≤ N - 1) (h : subPt (N - 1) s k = subPt (N - 1) s' k') :
    sgnList N (lσE u N s k) = sgnList N (lσE u N s' k') := by
  have hN := hd.hN
  by_cases hss : s = s'
  · subst hss
    have := lineMap_inj (hd.ne s hs) h
    have hN' : ((N - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [div_left_inj' hN'] at this
    have : k = k' := by exact_mod_cast this
    rw [this]
  · have h1 : subPt (N - 1) s k ∈ segment ℝ s.1 s.2 := by
      rw [subPt, segment_eq_image_lineMap]
      refine ⟨_, ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩, rfl⟩
      rw [div_le_one (by exact_mod_cast (show 0 < N - 1 by omega))]
      exact_mod_cast hk
    have h2 : subPt (N - 1) s k ∈ segment ℝ s'.1 s'.2 := by
      rw [h, subPt, segment_eq_image_lineMap]
      refine ⟨_, ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩, rfl⟩
      rw [div_le_one (by exact_mod_cast (show 0 < N - 1 by omega))]
      exact_mod_cast hk'
    obtain ⟨k1, k2⟩ := hd.dis s hs s' hs' hss ⟨h1, h2⟩
    have e1 := hd.sgnList_vertex hs hk rfl (by
      rcases k1 with k1 | k1
      · exact Or.inl k1
      · exact Or.inr (Set.mem_singleton_iff.1 k1))
    have e2 := hd.sgnList_vertex hs' hk' h.symm (by
      rcases k2 with k2 | k2
      · exact Or.inl k2
      · exact Or.inr (Set.mem_singleton_iff.1 k2))
    rw [e1, e2]

theorem LData.ly_eq (hd : LData G u N S₁) {s : E × E} (hs : s ∈ S₁) {k : ℕ} (hk : k ≤ N - 1) :
    ly u N S₁ (subPt (N - 1) s k) = sgnList N (lσE u N s k) := by
  have hex : ∃ sk : (E × E) × ℕ, sk.1 ∈ S₁ ∧ sk.2 ≤ N - 1 ∧
      subPt (N - 1) sk.1 sk.2 = subPt (N - 1) s k := ⟨(s, k), hs, hk, rfl⟩
  unfold ly
  rw [dif_pos hex]
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  exact hd.sgnList_wd h1 hs h2 hk h3

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem lσE_flip (u : E × ℝ → ℝ) (N : ℕ) (s : E × E) (p : ℕ) :
    ∀ r ≤ N, r ≠ p + 1 → lσE u N s p r = lσE u N s (p + 1) r := by
  intro r _ hr
  unfold lσE
  by_cases h : r ≤ p
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem length_chg_flip {N q : ℕ} (hq0 : 0 < q) (hqN : q < N) {σ₁ σ₂ : ℕ → Bool}
    (hag : ∀ r ≤ N, r ≠ q → σ₁ r = σ₂ r) :
    (chg N σ₁).length = (chg N σ₂).length ∨ (chg N σ₂).length = (chg N σ₁).length + 2 ∨
      (chg N σ₁).length = (chg N σ₂).length + 2 := by
  obtain ⟨A, B, -, -, e1, e2⟩ := chg_flip hq0 hqN hag
  rw [e1, e2]
  simp only [List.length_append]
  rcases chgPair_cases σ₁ σ₂ q (hag _ (by omega) (by omega)) (hag _ (by omega) (by omega)) with
    ⟨-, h⟩ | ⟨-, ⟨h, h'⟩ | ⟨h, h'⟩⟩ | ⟨-, h, h'⟩ | ⟨h, h'⟩
  · rw [h]; left; rfl
  all_goals rw [h, h']; simp <;> omega

/-- The two ends of a piece, with their sign sequences. -/
theorem LData.piece_ends (hd : LData G u N S₁) {s : E × E} (hs : s ∈ S₁) {p : ℕ}
    (hp : p < N - 1) :
    ∃ σ₁ σ₂ : ℕ → Bool, ly u N S₁ (subEdge (N - 1) (lo u N S₁) s p).1 = sgnList N σ₁ ∧
      ly u N S₁ (subEdge (N - 1) (lo u N S₁) s p).2 = sgnList N σ₂ ∧
      (∀ r ≤ N, r ≠ p + 1 → σ₁ r = σ₂ r) ∧
      ¬ (ly u N S₁ (subEdge (N - 1) (lo u N S₁) s p).1).length =
        (ly u N S₁ (subEdge (N - 1) (lo u N S₁) s p).2).length + 2 ∧
      ((σ₁ = lσE u N s p ∧ σ₂ = lσE u N s (p + 1)) ∨
        (σ₁ = lσE u N s (p + 1) ∧ σ₂ = lσE u N s p)) := by
  have hN := hd.hN
  have e0 := hd.ly_eq hs (k := p) (by omega)
  have e1 := hd.ly_eq hs (k := p + 1) (by omega)
  have hlr := length_chg_flip (N := N) (q := p + 1) (by omega) (by omega) (lσE_flip u N s p)
  unfold subEdge
  by_cases ho : lo u N S₁ s p = true
  · rw [if_pos ho]
    have ho' := of_decide_eq_true ho
    refine ⟨lσE u N s (p + 1), lσE u N s p, e1, e0, fun r hr hr' => (lσE_flip u N s p r hr hr').symm,
      ?_, Or.inr ⟨rfl, rfl⟩⟩
    simp only at ho' ⊢
    omega
  · rw [if_neg ho]
    have ho' : ¬ _ := fun h => ho (decide_eq_true h)
    exact ⟨lσE u N s p, lσE u N s (p + 1), e0, e1, lσE_flip u N s p, ho', Or.inl ⟨rfl, rfl⟩⟩

theorem LData.mem_ly (hd : LData G u N S₁) {s : E × E} (hs : s ∈ S₁) {k : ℕ} (hk : k ≤ N - 1) :
    Odd (ly u N S₁ (subPt (N - 1) s k)).length ∧
      ∀ t ∈ ly u N S₁ (subPt (N - 1) s k), t ∈ Ioo (0 : ℝ) 1 := by
  rw [hd.ly_eq hs hk, sgnList, List.length_map]
  refine ⟨odd_length_chg (hd.σE_zero hs k) (hd.σE_N hs hk), ?_⟩
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ht
  exact midH_mem (mem_chg.1 hq).1

theorem wedgeEv_eq_some {l l' : List ℝ} {m : ℕ} {lam h : ℝ}
    (he : wedgeEv l l' = some (m, lam, h)) :
    l'.length = l.length + 2 ∧ m = firstDiff l l' + 1 ∧ lam = 1 / 2 ∧
      h = (l'.getD (firstDiff l l') 0 + l'.getD (firstDiff l l' + 1) 0) / 2 := by
  unfold wedgeEv at he
  split_ifs at he with hl
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  exact ⟨hl, he.1.symm, he.2.1.symm, he.2.2.symm⟩

theorem wedgeEv_eq_none {l l' : List ℝ} (he : wedgeEv l l' = none) :
    ¬ l'.length = l.length + 2 := by
  unfold wedgeEv at he
  split_ifs at he with hl
  exact hl

theorem getD_mem_list {l : List ℝ} {n : ℕ} (hn : n < l.length) : l.getD n 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hn]; exact List.getElem_mem hn

/-- **The construction is a ladder.** -/
theorem LData.isLadder (hd : LData G u N S₁) : IsLadder G (lS u N S₁) (ly u N S₁) (lev u N S₁) := by
  have hN := hd.hN
  have hmem : ∀ e ∈ lS u N S₁, ∃ s ∈ S₁, ∃ p < N - 1, subEdge (N - 1) (lo u N S₁) s p = e :=
    fun e he => mem_subdiv.1 he
  -- the ends of a piece are subdivision points
  have hends : ∀ s ∈ S₁, ∀ p < N - 1, ∃ k₁ k₂, k₁ ≤ N - 1 ∧ k₂ ≤ N - 1 ∧
      (subEdge (N - 1) (lo u N S₁) s p).1 = subPt (N - 1) s k₁ ∧
      (subEdge (N - 1) (lo u N S₁) s p).2 = subPt (N - 1) s k₂ := by
    intro s hs p hp
    unfold subEdge
    split_ifs
    · exact ⟨p + 1, p, by omega, by omega, rfl, rfl⟩
    · exact ⟨p, p + 1, by omega, by omega, rfl, rfl⟩
  refine ⟨subdiv_ne hd.ne _, ?_, pairwiseEndpoints_subdiv hd.ne hd.dis _, ?_, ?_, ?_⟩
  · rw [lS, biUnion_subdiv (by omega), hd.G_eq]
  · intro e he
    obtain ⟨s, hs, p, hp, rfl⟩ := hmem e he
    obtain ⟨k₁, k₂, hk₁, hk₂, e1, e2⟩ := hends s hs p hp
    rw [e1, e2]
    exact ⟨(hd.mem_ly hs hk₁).1, (hd.mem_ly hs hk₂).1, (hd.mem_ly hs hk₁).2, (hd.mem_ly hs hk₂).2⟩
  · intro e he hev
    obtain ⟨s, hs, p, hp, rfl⟩ := hmem e he
    obtain ⟨σ₁, σ₂, h1, h2, hag, hlen, -⟩ := hd.piece_ends hs hp
    have h3 := wedgeEv_eq_none hev
    have hlr := length_chg_flip (N := N) (q := p + 1) (by omega) (by omega) hag
    rw [h1, h2, sgnList, sgnList, List.length_map, List.length_map] at *
    omega
  · intro e he m lam h hev
    obtain ⟨s, hs, p, hp, rfl⟩ := hmem e he
    obtain ⟨k₁, k₂, hk₁, hk₂, e1, e2⟩ := hends s hs p hp
    obtain ⟨hl, hm, hlam, hh⟩ := wedgeEv_eq_some hev
    have hfd := firstDiff_le (ly u N S₁ (subEdge (N - 1) (lo u N S₁) s p).1)
      (ly u N S₁ (subEdge (N - 1) (lo u N S₁) s p).2)
    have hin : ∀ t ∈ ly u N S₁ (subEdge (N - 1) (lo u N S₁) s p).2, t ∈ Ioo (0 : ℝ) 1 := by
      rw [e2]; exact (hd.mem_ly hs hk₂).2
    refine ⟨hl, by omega, by omega, by rw [hlam]; norm_num, ?_⟩
    rw [hh]
    set l₁ := ly u N S₁ (subEdge (N - 1) (lo u N S₁) s p).1
    set l₂ := ly u N S₁ (subEdge (N - 1) (lo u N S₁) s p).2
    have a1 := hin _ (getD_mem_list (l := l₂) (n := firstDiff l₁ l₂) (by omega))
    have a2 := hin _ (getD_mem_list (l := l₂) (n := firstDiff l₁ l₂ + 1) (by omega))
    constructor
    · linarith [a1.1, a2.1]
    · linarith [a1.2, a2.2]

theorem abs_midH_succ {N r : ℕ} (hN : 0 < N) :
    |midH N r - ((r + 1 : ℕ) : ℝ) / N| = 1 / (2 * N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [midH, show (2 * (r : ℝ) + 1) / (2 * N) - ((r + 1 : ℕ) : ℝ) / N = -(1 / (2 * N)) by
    push_cast; field_simp; ring]
  rw [abs_neg, abs_of_pos (by positivity)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem lσV_ne {u : E × ℝ → ℝ} {N : ℕ} {v₁ v₂ : E} {r₁ r₂ : ℕ}
    (h : lσV u N v₁ r₁ ≠ lσV u N v₂ r₂) :
    (u (v₁, (r₁ : ℝ) / N) ≤ 0 ∧ 0 < u (v₂, (r₂ : ℝ) / N)) ∨
      (u (v₂, (r₂ : ℝ) / N) ≤ 0 ∧ 0 < u (v₁, (r₁ : ℝ) / N)) := by
  unfold lσV at h
  by_cases h1 : 0 < u (v₁, (r₁ : ℝ) / N) <;> by_cases h2 : 0 < u (v₂, (r₂ : ℝ) / N) <;>
    simp_all

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem lσE_corner (u : E × ℝ → ℝ) (N : ℕ) (s : E × E) (k r : ℕ) :
    ∃ v, (v = s.1 ∨ v = s.2) ∧ lσE u N s k r = lσV u N v r := by
  unfold lσE
  split_ifs
  · exact ⟨s.2, Or.inr rfl, rfl⟩
  · exact ⟨s.1, Or.inl rfl, rfl⟩

/-- **Every point of a sheet lies near two corners of an edge of `S₁` with both signs.** -/
theorem LData.sheet_corners (hd : LData G u N S₁) {i : ℕ} {pt : E × ℝ}
    (hpt : pt ∈ ladderSheet (lS u N S₁) (ly u N S₁) (lev u N S₁) i) :
    ∃ s ∈ S₁, pt.1 ∈ segment ℝ s.1 s.2 ∧ pt ∈ G ×ˢ Icc (0 : ℝ) 1 ∧
      ∃ (v₁ v₂ : E) (t₁ t₂ : ℝ), (v₁ = s.1 ∨ v₁ = s.2) ∧ (v₂ = s.1 ∨ v₂ = s.2) ∧
        |pt.2 - t₁| ≤ 1 / N ∧ |pt.2 - t₂| ≤ 1 / N ∧ u (v₁, t₁) ≤ 0 ∧ 0 < u (v₂, t₂) := by
  have hN := hd.hN
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hhalf : 1 / (2 * (N : ℝ)) ≤ 1 / N := by
    rw [div_le_div_iff₀ (by positivity) hNr]; linarith
  obtain ⟨e, he, hpe⟩ := mem_iUnion₂.1 hpt
  have hL := hd.isLadder
  have hptG := hL.piece_subset he i hpe
  have hseg := (ladderPiece_subset (hL.evOK he) (fun t ht => Ioo_subset_Icc_self
    ((hL.2.2.2.1 e he).2.2.1 t ht)) (fun t ht => Ioo_subset_Icc_self
    ((hL.2.2.2.1 e he).2.2.2 t ht)) (fun m lam h hev => Ioo_subset_Icc_self
    (hL.2.2.2.2.2 e he m lam h hev).2.2.2.2) hpe).1
  obtain ⟨s, hs, p, hp, rfl⟩ := mem_subdiv.1 he
  refine ⟨s, hs, segment_subEdge_subset hp _ s hseg, hptG, ?_⟩
  obtain ⟨σ₁, σ₂, h1, h2, hag, hlen, hor⟩ := hd.piece_ends hs hp
  have hok := heightOK_of_mem_piece (N := N) (q := p + 1) hN0 (by omega) (by omega) hag h1 h2
    hlen hpe
  have hσ : ∀ σ, (σ = σ₁ ∨ σ = σ₂) → ∃ k, σ = lσE u N s k := by
    rintro σ (rfl | rfl) <;> rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨_, rfl⟩
  -- two corners with different signs give the conclusion
  have fin : ∀ (v₁ v₂ : E) (r₁ r₂ : ℕ), (v₁ = s.1 ∨ v₁ = s.2) → (v₂ = s.1 ∨ v₂ = s.2) →
      |pt.2 - (r₁ : ℝ) / N| ≤ 1 / N → |pt.2 - (r₂ : ℝ) / N| ≤ 1 / N →
      lσV u N v₁ r₁ ≠ lσV u N v₂ r₂ →
      ∃ (v₁ v₂ : E) (t₁ t₂ : ℝ), (v₁ = s.1 ∨ v₁ = s.2) ∧ (v₂ = s.1 ∨ v₂ = s.2) ∧
        |pt.2 - t₁| ≤ 1 / N ∧ |pt.2 - t₂| ≤ 1 / N ∧ u (v₁, t₁) ≤ 0 ∧ 0 < u (v₂, t₂) := by
    intro v₁ v₂ r₁ r₂ hv₁ hv₂ hr₁ hr₂ hne
    rcases lσV_ne hne with ⟨a, b⟩ | ⟨a, b⟩
    · exact ⟨v₁, v₂, _, _, hv₁, hv₂, hr₁, hr₂, a, b⟩
    · exact ⟨v₂, v₁, _, _, hv₂, hv₁, hr₂, hr₁, a, b⟩
  rcases hok with ⟨r, hr, hpt2⟩ | ⟨hne, hpt2⟩
  · obtain ⟨σ, hσσ, hrσ⟩ : ∃ σ, (σ = σ₁ ∨ σ = σ₂) ∧ r ∈ chg N σ := by
      rcases hr with hr | hr
      · exact ⟨σ₁, Or.inl rfl, hr⟩
      · exact ⟨σ₂, Or.inr rfl, hr⟩
    obtain ⟨k, rfl⟩ := hσ σ hσσ
    obtain ⟨-, hrne⟩ := mem_chg.1 hrσ
    obtain ⟨va, hva, ea⟩ := lσE_corner u N s k r
    obtain ⟨vb, hvb, eb⟩ := lσE_corner u N s k (r + 1)
    rw [ea, eb] at hrne
    refine fin va vb r (r + 1) hva hvb ?_ ?_ hrne
    · rw [hpt2, abs_midH_self hN0]; exact hhalf
    · rw [hpt2, abs_midH_succ hN0]; exact hhalf
  · obtain ⟨k₁, rfl⟩ := hσ σ₁ (Or.inl rfl)
    obtain ⟨k₂, rfl⟩ := hσ σ₂ (Or.inr rfl)
    obtain ⟨va, hva, ea⟩ := lσE_corner u N s k₁ (p + 1)
    obtain ⟨vb, hvb, eb⟩ := lσE_corner u N s k₂ (p + 1)
    rw [ea, eb] at hne
    exact fin va vb (p + 1) (p + 1) hva hvb (hpt2.trans hhalf) (hpt2.trans hhalf) hne

end Props

theorem dist_le_of_mem_segment_ends {a b x v : E} (hx : x ∈ segment ℝ a b) (hv : v = a ∨ v = b) :
    dist x v ≤ dist a b := by
  have hsub : segment ℝ a b ⊆ closedBall v (dist a b) :=
    (convex_closedBall v _).segment_subset
      (by rcases hv with rfl | rfl <;> simp [dist_comm])
      (by rcases hv with rfl | rfl <;> simp [dist_comm])
  exact hsub hx

/-- **§5. Claim 15.1, replaced**: inside any open `U` containing a separator there is a
ladder. -/
theorem exists_ladder_aux {G : Set E} (hG : IsPLGraph G) (hconn : IsConnected G)
    {M : Set (E × ℝ)} (hM : M ⊆ G ×ˢ Ioo (0 : ℝ) 1)
    (hsep : SeparatesIn (G ×ˢ Icc (0 : ℝ) 1) M (G ×ˢ ({0} : Set ℝ)) (G ×ˢ ({1} : Set ℝ)))
    {U : Set (E × ℝ)} (hU : IsOpen U) (hMU : M ⊆ U) :
    ∃ (S : Finset (E × E)) (y : E → List ℝ) (ev : E × E → Option (ℕ × ℝ × ℝ)),
      IsLadder G S y ev ∧ S.Nonempty ∧ ∀ i, ladderSheet S y ev i ⊆ U ∩ G ×ˢ Ioo (0 : ℝ) 1 := by
  obtain ⟨u, δ, hδ, hu0, hu1, hgood⟩ :=
    exists_sign_fn hG.isCompact hconn.nonempty hM hsep hU hMU
  obtain ⟨S₀, hne₀, hG₀, hdis₀⟩ := hG
  set D := ∑ s ∈ S₀, dist s.1 s.2 with hD
  set n₀ := ⌈D / δ⌉₊ + 1 with hn₀def
  have hn₀ : n₀ ≠ 0 := by omega
  set S₁ := subdiv S₀ n₀ (fun _ _ => false) with hS₁
  have hS₁short : ∀ s ∈ S₁, dist s.1 s.2 < δ := by
    intro s hs
    obtain ⟨s₀, hs₀, p, hp, rfl⟩ := mem_subdiv.1 hs
    rw [dist_subEdge hn₀]
    have hle : dist s₀.1 s₀.2 ≤ D := Finset.single_le_sum (fun s _ => dist_nonneg) hs₀
    have hc : D / δ < n₀ := by
      have := Nat.le_ceil (D / δ)
      rw [hn₀def]; push_cast; linarith
    have hn₀r : (0 : ℝ) < n₀ := by exact_mod_cast Nat.pos_of_ne_zero hn₀
    rw [div_lt_iff₀ hn₀r]
    rw [div_lt_iff₀ hδ] at hc
    nlinarith
  set N := ⌈1 / δ⌉₊ + 2 with hNdef
  have hNδ : 1 / (N : ℝ) < δ := by
    have h1 := Nat.le_ceil (1 / δ)
    have hN : (0 : ℝ) < N := by positivity
    have : 1 / δ < N := by rw [hNdef]; push_cast; linarith
    rw [div_lt_iff₀ hN]
    rw [div_lt_iff₀ hδ] at this
    linarith
  have hd : LData G u N S₁ := ⟨by omega, subdiv_ne hne₀ _, by rw [biUnion_subdiv hn₀, hG₀],
    pairwiseEndpoints_subdiv hne₀ hdis₀ _, hu0, hu1⟩
  refine ⟨lS u N S₁, ly u N S₁, lev u N S₁, hd.isLadder, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hconn.nonempty
    rw [hG₀] at hx
    obtain ⟨s₀, hs₀, -⟩ := mem_iUnion₂.1 hx
    have hs₁ : subEdge n₀ (fun _ _ => false) s₀ 0 ∈ S₁ :=
      mem_subdiv.2 ⟨s₀, hs₀, 0, Nat.pos_of_ne_zero hn₀, rfl⟩
    exact ⟨_, mem_subdiv.2 ⟨_, hs₁, 0, by omega, rfl⟩⟩
  · intro i pt hpt
    obtain ⟨s, hs, hpt1, hptG, v₁, v₂, t₁, t₂, hv₁, hv₂, ht₁, ht₂, hu₁', hu₂'⟩ :=
      hd.sheet_corners hpt
    have hdist : ∀ v t, (v = s.1 ∨ v = s.2) → |pt.2 - t| ≤ 1 / N → dist pt (v, t) < δ := by
      intro v t hv ht
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq]
      exact ⟨lt_of_le_of_lt (dist_le_of_mem_segment_ends hpt1 hv) (hS₁short s hs),
        lt_of_le_of_lt ht hNδ⟩
    exact hgood pt hptG (v₁, t₁) (v₂, t₂) (hdist v₁ t₁ hv₁ ht₁) (hdist v₂ t₂ hv₂ ht₂) hu₁' hu₂'

end

end HPC.HO16
