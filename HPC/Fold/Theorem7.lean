import HPC.PseudoArc.Theorem13
import HPC.Fold.T7Assemble
import HPC.Fold.T8Tight
import HPC.Fold.T9Main

/-!
# Bing 1948, Theorems 7, 8, 9 in full

Batch 82, from the commissioned skeleton. All proved, no `sorry` (the only `sorry` below is inside
the commented-out skeleton form of Theorem 8, which is false: `theorem8_skeleton_false` in
`HPC/Fold/Theorem8Counter.lean`). Changes to the skeleton: `bingPattern`'s length proof written out;
`theorem8` reshaped (orientation, and the union chain quantified in the conclusion);
`theorem7_minimal` added. `theorem7` and `theorem9` are as skeletoned.

Conventions: `E` fine (Bing's `D`), `D` coarse (Bing's `E`) with `m` links; Bing's pattern
`P(m)`, `(1, y(1)), …, (z(m−1), y(z(m−1)))`, is the level sequence `bingPath 0 (m − 1)` of
`HPC/Fold/OffCenter.lean` (its length is `z (m − 1)`, `bingPath_length`), read `0`-indexed.
-/

namespace HPC.Fold

open HPC.Chain

variable {X : Type*} [MetricSpace X]

theorem bingPattern_len (m : ℕ) (hm : 1 ≤ m) (i : Fin (z (m - 1))) :
    i.val < (bingPath 0 (m - 1 : ℤ)).length := by
  rw [bingPath_length, show (|(m : ℤ) - 1 - 0|).toNat = m - 1 by
    rw [sub_zero, abs_of_nonneg (by omega)]; omega]
  exact i.isLt

/-- `bingPath 0 (m - 1)` read at index `u` is `bingF (m - 1) u`. -/
theorem bingPath_get_eq (m : ℕ) (hm : 1 ≤ m) (u : ℕ) (hu : u < (bingPath 0 (m - 1 : ℤ)).length) :
    (bingPath 0 (m - 1 : ℤ)).get ⟨u, hu⟩ = bingF (m - 1) u := by
  have key : ∀ x : ℤ, x = ((m - 1 : ℕ) : ℤ) → ∀ hu' : u < (bingPath 0 x).length,
      (bingPath 0 x).get ⟨u, hu'⟩ = bingF (m - 1) u := by
    intro x hx hu'
    subst hx
    exact bingPath_zero_getElem (m - 1) u hu'
  exact key _ (by omega) hu

/-- The canonical pattern of Bing's Theorem 7 as a map from `Fin (z (m-1))` to the links of an
`m`-link chain: position `i` goes to link `bingPath 0 (m-1)` at `i`.

Batch 82: the placeholder bound of the skeleton is proved (`bingPath_get_eq`, `bingF_le`); the
length proof is written out (the skeleton's `simpa` did not close it). -/
def bingPattern (m : ℕ) (hm : 1 ≤ m) : Fin (z (m - 1)) → Fin m :=
  fun i => ⟨((bingPath 0 (m - 1 : ℤ)).get ⟨i.val, bingPattern_len m hm i⟩).toNat, by
    rw [bingPath_get_eq m hm]
    have := bingF_le (m - 1) i.val
    have := bingF_nonneg (m - 1) i.val
    omega⟩

theorem bingPattern_val (m : ℕ) (hm : 1 ≤ m) (i : Fin (z (m - 1))) :
    ((bingPattern m hm i : ℕ) : ℤ) = bingF (m - 1) i := by
  simp only [bingPattern]
  rw [bingPath_get_eq m hm]
  have := bingF_nonneg (m - 1) i.val
  omega

/-- **Bing 1948, Theorem 7, in full** (block reading). If `E` is crooked in `D` (`m ≥ 3` links),
some link of `E` lies in the first link of `D` and some in the last, then `E` has a block
consolidation `F` with exactly `z (m − 1)` links, whose first link lies in `D.link 0`, whose last
lies in `D.link (m−1)`, which is crooked in `D`, and which follows the pattern `bingPattern m` in
`D`. (Minimality — no consolidation with fewer links has these properties — is `minimality`.) -/
theorem theorem7 {n m : ℕ} (hm : 3 ≤ m) {E : Chain X n} {D : Chain X m} (hcr : E.IsCrookedIn' D)
    (hlo : ∃ t, E.link t ⊆ D.link ⟨0, by omega⟩) (hhi : ∃ t, E.link t ⊆ D.link ⟨m - 1, by omega⟩) :
    ∃ (β : Fin n → Fin (z (m - 1))) (hβ : IsBlockMap β),
      (E.ofBlocks β hβ).IsCrookedIn' D ∧
      (E.ofBlocks β hβ).FollowsPattern (bingPattern m (by omega)) D := by
  obtain ⟨β, hβ, h1, h2⟩ := exists_blocks_bingF hm hcr hlo hhi
  refine ⟨β, hβ, ofBlocks_crooked_of_tight β hβ h1 h2, fun u x hx => ?_⟩
  rw [ofBlocks_link] at hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨i, hi, hsub⟩ := h1 t
  have : i = bingPattern m (by omega) u := Fin.ext (by
    have := bingPattern_val m (by omega) u
    rw [ht] at hi; omega)
  rw [← this]; exact hsub hxt

/-- **Minimality in Theorem 7** (Bing: "no proper consolidation of `F` has these properties"):
a chain crooked in `D` with a link in the first link of `D` and a link in the last has at least
`z (m − 1)` links. The consolidation of `theorem7` has exactly `z (m − 1)`, so no consolidation
of it with fewer links — in particular no proper one — has the properties. From `minGap`. -/
theorem theorem7_minimal {p m : ℕ} (hm : 3 ≤ m) {F : Chain X p} {D : Chain X m}
    (hcr : F.IsCrookedIn' D) (hlo : ∃ t, F.link t ⊆ D.link ⟨0, by omega⟩)
    (hhi : ∃ t, F.link t ⊆ D.link ⟨m - 1, by omega⟩) : z (m - 1) ≤ p := by
  obtain ⟨t0, h0⟩ := hlo
  obtain ⟨t1, h1⟩ := hhi
  have hne : t0 ≠ t1 := by
    rintro rfl
    obtain ⟨x, hx⟩ := F.link_nonempty t0
    have := (D.adjacent_iff ⟨0, by omega⟩ ⟨m - 1, by omega⟩).1 ⟨x, h0 hx, h1 hx⟩
    simp at this; omega
  have hmin := minIdx_le hcr.1 t0 h0
  have hmax := le_maxIdx hcr.1 t1 h1
  have hmax' := (hcr.1.maxIdx t1).isLt
  refine minGap (m - 1) (isCrookedIvF_minIdx_maxIdx hcr) t0 t1 0 ?_ ?_ ?_ ?_ hne
  · have h' : ((hcr.1.minIdx t0 : Fin m) : ℕ) = 0 := by simpa [Fin.le_def] using hmin
    omega
  · dsimp only; omega
  · dsimp only; have := (hcr.1.minIdx t1).isLt; omega
  · rw [Fin.le_def, Fin.val_mk] at hmax; omega

-- Commented-out statement `theorem8` (skeleton form) removed in batch 103; see `LEDGER.md`.

/-- Following `bingPattern m` is following `bingF (m − 1)` level by level. -/
theorem followsPattern_bingPattern_iff {m : ℕ} (hm : 1 ≤ m) {F : Chain X (z (m - 1))}
    {D : Chain X m} :
    F.FollowsPattern (bingPattern m hm) D ↔
      ∀ u : Fin (z (m - 1)), ∃ i : Fin m, (i : ℤ) = bingF (m - 1) u ∧ F.link u ⊆ D.link i := by
  constructor
  · intro h u
    exact ⟨bingPattern m hm u, bingPattern_val m hm u, h u⟩
  · intro h u
    obtain ⟨i, hi, hsub⟩ := h u
    have : i = bingPattern m hm u := Fin.ext (by have := bingPattern_val m hm u; omega)
    rw [← this]; exact hsub

/-- **Theorem 8, orientation clause.** A chain with `z (m − 1)` links crooked in `D` with a link
in each end link of `D` follows `bingPattern m` in `D`, read forwards or backwards. -/
theorem followsPattern_or_reverse {m : ℕ} (hm : 3 ≤ m) {D : Chain X m}
    {F : Chain X (z (m - 1))} (hcr : F.IsCrookedIn' D)
    (hlo : ∃ t, F.link t ⊆ D.link ⟨0, by omega⟩) (hhi : ∃ t, F.link t ⊆ D.link ⟨m - 1, by omega⟩) :
    F.FollowsPattern (bingPattern m (by omega)) D ∨
      F.reverse.FollowsPattern (bingPattern m (by omega)) D := by
  obtain ⟨β, hβ, -, hfol⟩ := theorem7 hm hcr hlo hhi
  have hin : ∀ t u, β t = u → F.link t ⊆ (F.ofBlocks β hβ).link u := by
    intro t u htu x hx
    rw [ofBlocks_link]
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨t, htu, hx⟩
  rcases blockMap_self hβ with h | h
  · left
    intro u
    exact (hin u u (h u)).trans (hfol u)
  · right
    intro u
    rw [reverse_link]
    refine (hin _ u (Fin.ext ?_)).trans (hfol u)
    rw [h, Fin.val_rev]
    have := u.isLt
    omega

/-- **Bing 1948, Theorem 8**, corrected (the skeleton's form is refuted by
`theorem8_skeleton_false`). Two chains with `z (m − 1)` links (Bing: no proper consolidation has
the properties; `theorem7_minimal`), crooked in `D`, each with a link in each end link of `D`:
each follows `bingPattern m` in `D` forwards or backwards; and a chain whose links are the unions
of corresponding links of the two, when they are oriented alike, is crooked in `D`. -/
theorem theorem8 {m : ℕ} (hm : 3 ≤ m) {D : Chain X m} (F₁ F₂ : Chain X (z (m - 1)))
    (h₁ : F₁.IsCrookedIn' D) (h₂ : F₂.IsCrookedIn' D)
    (hlo₁ : ∃ t, F₁.link t ⊆ D.link ⟨0, by omega⟩) (hhi₁ : ∃ t, F₁.link t ⊆ D.link ⟨m - 1, by omega⟩)
    (hlo₂ : ∃ t, F₂.link t ⊆ D.link ⟨0, by omega⟩) (hhi₂ : ∃ t, F₂.link t ⊆ D.link ⟨m - 1, by omega⟩) :
    (F₁.FollowsPattern (bingPattern m (by omega)) D ∨
      F₁.reverse.FollowsPattern (bingPattern m (by omega)) D) ∧
    (F₂.FollowsPattern (bingPattern m (by omega)) D ∨
      F₂.reverse.FollowsPattern (bingPattern m (by omega)) D) ∧
    ∀ C : Chain X (z (m - 1)), (∀ i, C.link i = F₁.link i ∪ F₂.link i) →
      (F₁.FollowsPattern (bingPattern m (by omega)) D ∧
          F₂.FollowsPattern (bingPattern m (by omega)) D) ∨
        (F₁.reverse.FollowsPattern (bingPattern m (by omega)) D ∧
          F₂.reverse.FollowsPattern (bingPattern m (by omega)) D) →
      C.IsCrookedIn' D := by
  refine ⟨followsPattern_or_reverse hm h₁ hlo₁ hhi₁, followsPattern_or_reverse hm h₂ hlo₂ hhi₂,
    fun C hC hor => ?_⟩
  rcases hor with ⟨f₁, f₂⟩ | ⟨f₁, f₂⟩
  · exact crooked_union_of_bingF h₁ h₂ ((followsPattern_bingPattern_iff _).1 f₁)
      ((followsPattern_bingPattern_iff _).1 f₂) hC
  · have hCr : C.reverse.IsCrookedIn' D :=
      crooked_union_of_bingF h₁.reverse_left h₂.reverse_left
        ((followsPattern_bingPattern_iff _).1 f₁)
        ((followsPattern_bingPattern_iff _).1 f₂) (fun i => by simp [hC])
    have := hCr.reverse_left
    rwa [reverse_reverse] at this

/-- **Bing 1948, Theorem 9** (block reading, three-link form for the mesh clause as in
`theorem4`). `E` crooked in `D`; `E.link 0 ⊆ D.link 0`, `E.link (n−1) ⊆ D.link (m−1)`,
`E.link r ⊆ D.link (m−1)`, `E.link s ⊆ D.link 0` with `r < s`. Then for every `t < s` there is a
block consolidation `F` of `E` whose first block contains `0`, whose last block contains `n−1`,
every block in three consecutive links of `D`, and such that every run of consecutive blocks
whose end blocks contain `t` and `n−1` contains all of `E.link r … E.link n−1` — Bing: "any
subchain of `F` whose end links contain `d_t` and `d_n` respectively contains `D(r, n)`".

Batch 82: proved as stated. Bing's chains `D` and `E` are this statement's `E` and `D`; Bing's
mesh clause has two adjacent links, and that form is not formalized. For `t ≤ r` the trivial consolidation (every block a single link)
works; for `r < t` the construction is Bing's (`theorem9_core`). The hypothesis `hrs : r < s` of
Bing's statement is kept but is not needed by the proof (for `r < t` it follows from `t < s`). -/
theorem theorem9 {n m : ℕ} (hm : 3 ≤ m) {E : Chain X n} {D : Chain X m} (hcr : E.IsCrookedIn' D)
    (hn : 0 < n) (r s : Fin n) (hrs : r < s)
    (h0 : E.link ⟨0, hn⟩ ⊆ D.link ⟨0, by omega⟩)
    (hlast : E.link ⟨n - 1, by omega⟩ ⊆ D.link ⟨m - 1, by omega⟩)
    (hr : E.link r ⊆ D.link ⟨m - 1, by omega⟩) (hs : E.link s ⊆ D.link ⟨0, by omega⟩)
    (t : Fin n) (hts : t < s) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β ⟨0, hn⟩).val = 0 ∧ (β ⟨n - 1, by omega⟩).val = q - 1 ∧
      (∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 3) ∧
      ∀ u : Fin n, r ≤ u → β t ≤ β u := by
  by_cases htr : t ≤ r
  · -- the trivial consolidation: every block a single link
    have hβ : IsBlockMap (id : Fin n → Fin n) :=
      ⟨Function.surjective_id, fun a b h => by simp only [id]; omega⟩
    refine ⟨n, id, hβ, rfl, rfl, fun u => ?_, fun u hu => htr.trans hu⟩
    obtain ⟨i, hi⟩ := hcr.1 u
    exact ⟨i.val, ofBlocks_link_subset E hβ u _ (fun t ht => by
      rw [show t = u from ht]; exact hi.trans (link_subset_unionRange D i))⟩
  · obtain ⟨q, β, hβ, h1, h2, h3, h4⟩ := theorem9_core hm hcr hn r.val s.val t.val
      (by rw [Fin.le_def] at htr; omega) hts s.isLt h0 hlast hr hs
    exact ⟨q, β, hβ, h1, h2, h3, fun u hu => h4 u hu⟩

end HPC.Fold
