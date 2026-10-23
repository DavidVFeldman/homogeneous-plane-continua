import HPC.HO16.LadderParam

/-!
# Batch 197: the pieces of a ladder sheet over one edge

Every piece of `ladderPiece y s e i` is the image of a parameter interval `eI … k` under an affine
map `pieceLine … k` whose first coordinate is the point of parameter `μ` of the edge. From this:
`π` of a piece is the image of `eP` (`image_fst_ladderPiece`), `π` is injective on a piece
(`injOn_fst_ladderPiece`), the points over the ends of the edge (`ladderPiece_fst_eq_*`), the
points of `α` (`ladderAlpha`), and the points over the vertices (`mem_ladderPiece_*`).
-/

namespace HPC.HO16

open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine lines carrying the five kinds of pieces (commission 197 §2). -/
def pieceLine (y : E → List ℝ) (s : E × E) : Option (ℕ × ℝ × ℝ) → ℕ → ℕ → ℝ → E × ℝ
  | none, i, _ => AffineMap.lineMap (s.1, ladderY y s.1 i) (s.2, ladderY y s.2 i)
  | some (_, lam, h), i, k =>
    match k with
    | 0 => AffineMap.lineMap (s.1, ladderY y s.1 i) (s.2, ladderY y s.2 i)
    | 1 => zzLine y s i
    | 2 => zzLine y s (i - 1)
    | 3 => zzLine y s (i - 2)
    | _ => AffineMap.lineMap (s.1, h - lam * (ladderY y s.2 i - h) / (1 - lam))
        (s.2, ladderY y s.2 i)

/-- The parameter intervals of the pieces. -/
def eI (j : ℕ) : Option (ℕ × ℝ × ℝ) → ℕ → ℕ → Set ℝ
  | none, i, k => if k = 0 ∧ 1 ≤ i ∧ i ≤ j then Icc 0 1 else ∅
  | some (m, lam, _), i, k => wI j m lam i k

/-- The points of `αᵢ` over an edge (commission 197 §3, "The `α`"). -/
def ladderAlpha (y : E → List ℝ) (s : E × E) : Option (ℕ × ℝ × ℝ) → ℕ → Set (E × ℝ)
  | none, _ => ∅
  | some (m, lam, h), i =>
    (if m + 1 ≤ i ∧ i ≤ (y s.1).length + 1 then
      {zzLine y s (i - 1) (zzR (y s.1).length m lam (i - 1))} else ∅) ∪
    (if m + 2 ≤ i ∧ i ≤ (y s.1).length + 2 then
      {zzLine y s (i - 2) (zzL (y s.1).length m lam (i - 2))} else ∅) ∪
    (if i = m + 1 then {(AffineMap.lineMap s.1 s.2 lam, h)} else ∅)

theorem zzLine_eq (y : E → List ℝ) (s : E × E) (i : ℕ) (μ : ℝ) :
    zzLine y s i μ = (AffineMap.lineMap s.1 s.2 μ,
      AffineMap.lineMap (ladderY y s.1 i) (ladderY y s.2 (i + 2)) μ) := by
  rw [zzLine, lineMap_prod]

theorem pieceLine_fst (y : E → List ℝ) (s : E × E) (e : Option (ℕ × ℝ × ℝ)) (i k : ℕ) (μ : ℝ) :
    (pieceLine y s e i k μ).1 = AffineMap.lineMap s.1 s.2 μ := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp [pieceLine, lineMap_prod]
  · rcases k with _ | _ | _ | _ | k <;> simp [pieceLine, lineMap_prod, zzLine_eq]

theorem segment_lineMap_Icc {P : Type*} [AddCommGroup P] [Module ℝ P] (a b : P) {u v : ℝ}
    (huv : u ≤ v) :
    segment ℝ (AffineMap.lineMap a b u) (AffineMap.lineMap a b v) =
      AffineMap.lineMap a b '' Icc u v := by
  rw [← segment_eq_Icc huv, image_segment]

theorem eI_sub_eP {j i k : ℕ} {e : Option (ℕ × ℝ × ℝ)} (hk : k < 5) : eI j e i k ⊆ eP j e i := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp only [eI, eP]
    split_ifs with h1 h2 <;> first | exact subset_rfl | exact empty_subset _ | omega
  · simp only [eI, eP, wP]
    interval_cases k
    · exact subset_union_left.trans (subset_union_left.trans (subset_union_left.trans
        subset_union_left))
    · exact subset_union_right.trans (subset_union_left.trans (subset_union_left.trans
        subset_union_left))
    · exact subset_union_right.trans (subset_union_left.trans subset_union_left)
    · exact subset_union_right.trans subset_union_left
    · exact subset_union_right

theorem eP_eq_iUnion {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)} :
    eP j e i = ⋃ k < 5, eI j e i k := by
  apply Subset.antisymm
  · rcases e with _ | ⟨m, lam, h⟩
    · intro μ hμ
      exact mem_iUnion₂.2 ⟨0, by norm_num, by simpa [eI, eP] using hμ⟩
    · intro μ hμ
      simp only [eP, wP, mem_union] at hμ
      rcases hμ with (((h0 | h0) | h0) | h0) | h0
      · exact mem_iUnion₂.2 ⟨0, by norm_num, h0⟩
      · exact mem_iUnion₂.2 ⟨1, by norm_num, h0⟩
      · exact mem_iUnion₂.2 ⟨2, by norm_num, h0⟩
      · exact mem_iUnion₂.2 ⟨3, by norm_num, h0⟩
      · exact mem_iUnion₂.2 ⟨4, by norm_num, h0⟩
  · exact iUnion₂_subset fun k hk => eI_sub_eP hk

/-- A piece is the union of the images of the parameter intervals. -/
theorem ladderPiece_eq {y : E → List ℝ} {s : E × E} {e : Option (ℕ × ℝ × ℝ)} {i : ℕ}
    (he : EvOK (y s.1).length e) :
    ladderPiece y s e i = ⋃ k < 5, pieceLine y s e i k '' eI (y s.1).length e i k := by
  rcases e with _ | ⟨m, lam, h⟩
  · ext p
    simp only [mem_iUnion, exists_prop, ladderPiece, eI, pieceLine]
    constructor
    · intro hp
      split_ifs at hp with hc
      · refine ⟨0, by norm_num, ?_⟩
        rw [if_pos ⟨rfl, hc⟩, ← segment_eq_image_lineMap]
        exact hp
      · exact absurd hp (notMem_empty _)
    · rintro ⟨k, -, hp⟩
      split_ifs at hp with hc
      · rw [if_pos hc.2, segment_eq_image_lineMap]
        exact hp
      · rw [image_empty] at hp; exact absurd hp (notMem_empty _)
  · obtain ⟨hm, hmj, hl0, hl1⟩ := he
    have hlam : (AffineMap.lineMap (s.1, h - lam * (ladderY y s.2 i - h) / (1 - lam))
        (s.2, ladderY y s.2 i) lam : E × ℝ) = (AffineMap.lineMap s.1 s.2 lam, h) := by
      rw [lineMap_prod]
      congr 1
      rw [AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
      have : (1 - lam) ≠ 0 := by linarith
      field_simp
      ring
    have hseg : ∀ (c : Prop) [Decidable c] (a b : E × ℝ) (L : ℝ → E × ℝ) (u v : ℝ),
        (c → segment ℝ a b = L '' Icc u v) →
        (if c then segment ℝ a b else ∅) = L '' (if c then Icc u v else ∅) := by
      intro c _ a b L u v H
      split_ifs with hc
      · exact H hc
      · simp
    have hzU := zU_pos (j := (y s.1).length) (m := m) hl0
    simp only [ladderPiece]
    rw [hseg _ (s.1, ladderY y s.1 i) (s.2, ladderY y s.2 i) (pieceLine y s (some (m, lam, h)) i 0)
        0 1 (fun _ => segment_eq_image_lineMap ℝ (s.1, ladderY y s.1 i) (s.2, ladderY y s.2 i))]
    rw [hseg _ (zzLine y s i 0) (zzLine y s i (zzR (y s.1).length m lam i))
        (pieceLine y s (some (m, lam, h)) i 1) 0 (zzR (y s.1).length m lam i) (fun _ => by
          have := zz_lr (y s.1).length m lam i
          have := zzL_ge (j := (y s.1).length) (m := m) hl0 i
          exact segment_lineMap_Icc _ _ (by linarith))]
    rw [hseg _ (zzLine y s (i - 1) (zzL (y s.1).length m lam (i - 1)))
        (zzLine y s (i - 1) (zzR (y s.1).length m lam (i - 1)))
        (pieceLine y s (some (m, lam, h)) i 2) (zzL (y s.1).length m lam (i - 1))
        (zzR (y s.1).length m lam (i - 1)) (fun _ => by
          have := zz_lr (y s.1).length m lam (i - 1)
          exact segment_lineMap_Icc _ _ (by linarith))]
    rw [hseg _ (zzLine y s (i - 2) (zzL (y s.1).length m lam (i - 2))) (zzLine y s (i - 2) 1)
        (pieceLine y s (some (m, lam, h)) i 3) (zzL (y s.1).length m lam (i - 2)) 1 (fun hc => by
          have h1 := zz_lr (y s.1).length m lam (i - 2)
          have h2 := zz_lam (j := (y s.1).length) (m := m) (c := i - 2) hl0 (by omega) (by omega)
          exact segment_lineMap_Icc _ _ (by linarith))]
    rw [hseg _ (AffineMap.lineMap s.1 s.2 lam, h) (s.2, ladderY y s.2 i)
        (pieceLine y s (some (m, lam, h)) i 4) lam 1 (fun _ => by
          have e4 := segment_lineMap_Icc ((s.1, h - lam * (ladderY y s.2 i - h) /
            (1 - lam)) : E × ℝ) (s.2, ladderY y s.2 i) hl1.le
          rw [hlam, AffineMap.lineMap_apply_one] at e4
          exact e4)]
    ext p
    simp only [mem_union, mem_iUnion, exists_prop]
    constructor
    · rintro ((((hp | hp) | hp) | hp) | hp)
      · exact ⟨0, by norm_num, hp⟩
      · exact ⟨1, by norm_num, hp⟩
      · exact ⟨2, by norm_num, hp⟩
      · exact ⟨3, by norm_num, hp⟩
      · exact ⟨4, by norm_num, hp⟩
    · rintro ⟨k, hk, hp⟩
      interval_cases k
      · exact Or.inl (Or.inl (Or.inl (Or.inl hp)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr hp)))
      · exact Or.inl (Or.inl (Or.inr hp))
      · exact Or.inl (Or.inr hp)
      · exact Or.inr hp

theorem eI_sub_Icc {j i k : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hk : k < 5) :
    eI j e i k ⊆ Icc 0 1 :=
  (eI_sub_eP hk).trans (e_P_sub he)

theorem eI_disj {j i k k' : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hi : 1 ≤ i)
    (hkk : k ≠ k') (hk : k < 5) (hk' : k' < 5) {μ : ℝ} (h1 : μ ∈ eI j e i k)
    (h2 : μ ∈ eI j e i k') : False := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp only [eI] at h1 h2
    split_ifs at h1 h2 with c1 c2 <;> first | omega | exact absurd h1 (notMem_empty _) |
      exact absurd h2 (notMem_empty _)
  · obtain ⟨hm, hmj, hl0, hl1⟩ := he
    rcases lt_or_gt_of_ne hkk with hlt | hlt
    · exact w_I_disj hi hm hmj hl0 hl1 hlt hk' h1 h2
    · exact w_I_disj hi hm hmj hl0 hl1 hlt hk h2 h1

theorem eI_zero {j i k : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hk : k < 5)
    (h0 : (0 : ℝ) ∈ eI j e i k) : k ≤ 1 := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp only [eI] at h0
    split_ifs at h0 with c <;> first | omega | exact absurd h0 (notMem_empty _)
  · obtain ⟨hm, hmj, hl0, hl1⟩ := he
    have h1 := zzL_ge (j := j) (m := m) hl0 (i - 1)
    have h2 := zzL_ge (j := j) (m := m) hl0 (i - 2)
    have h3 := zU_pos (j := j) (m := m) hl0
    simp only [eI] at h0
    interval_cases k <;> simp only [wI] at h0 <;> split_ifs at h0 <;>
      first | omega | exact absurd h0 (notMem_empty _) | (rw [mem_Icc] at h0; linarith)

theorem eI_one {j i k : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hk : k < 5)
    (h0 : (1 : ℝ) ∈ eI j e i k) : k = 0 ∨ k = 3 ∨ k = 4 := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp only [eI] at h0
    split_ifs at h0 with c <;> first | omega | exact absurd h0 (notMem_empty _)
  · obtain ⟨hm, hmj, hl0, hl1⟩ := he
    simp only [eI] at h0
    interval_cases k <;> simp only [wI] at h0 <;> split_ifs at h0 with c <;>
      first | omega | exact absurd h0 (notMem_empty _) | skip
    · rw [mem_Icc] at h0
      have := zz_lam (j := j) (m := m) (c := i) hl0 c.1 c.2
      have := zU_pos (j := j) (m := m) hl0
      linarith
    · rw [mem_Icc] at h0
      have := zz_lam (j := j) (m := m) (c := i - 1) hl0 (by omega) (by omega)
      have := zU_pos (j := j) (m := m) hl0
      linarith

/-- Membership in a piece. -/
theorem mem_ladderPiece {y : E → List ℝ} {s : E × E} {e : Option (ℕ × ℝ × ℝ)} {i : ℕ}
    (he : EvOK (y s.1).length e) {p : E × ℝ} :
    p ∈ ladderPiece y s e i ↔
      ∃ k < 5, ∃ μ ∈ eI (y s.1).length e i k, pieceLine y s e i k μ = p := by
  rw [ladderPiece_eq he]
  simp only [mem_iUnion, mem_image, exists_prop]

/-- **`π` of a piece** is the image of the parameter set `eP`. -/
theorem image_fst_ladderPiece {y : E → List ℝ} {s : E × E} {e : Option (ℕ × ℝ × ℝ)} {i : ℕ}
    (he : EvOK (y s.1).length e) :
    Prod.fst '' ladderPiece y s e i = AffineMap.lineMap s.1 s.2 '' eP (y s.1).length e i := by
  ext x
  simp only [mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨k, hk, μ, hμ, rfl⟩ := (mem_ladderPiece he).1 hp
    exact ⟨μ, eI_sub_eP hk hμ, (pieceLine_fst _ _ _ _ _ _).symm⟩
  · rintro ⟨μ, hμ, rfl⟩
    rw [eP_eq_iUnion] at hμ
    obtain ⟨k, hk, hμk⟩ := mem_iUnion₂.1 hμ
    exact ⟨_, (mem_ladderPiece he).2 ⟨k, hk, μ, hμk, rfl⟩, pieceLine_fst _ _ _ _ _ _⟩

theorem lineMap_inj {a b : E} (hab : a ≠ b) {μ ν : ℝ}
    (h : AffineMap.lineMap a b μ = AffineMap.lineMap a b ν) : μ = ν :=
  AffineMap.lineMap_injective ℝ hab h

/-- **`π` is injective on a piece.** -/
theorem injOn_fst_ladderPiece {y : E → List ℝ} {s : E × E} {e : Option (ℕ × ℝ × ℝ)} {i : ℕ}
    (hs : s.1 ≠ s.2) (he : EvOK (y s.1).length e) (hi : 1 ≤ i) :
    InjOn Prod.fst (ladderPiece y s e i) := by
  intro p hp q hq hpq
  obtain ⟨k, hk, μ, hμ, rfl⟩ := (mem_ladderPiece he).1 hp
  obtain ⟨k', hk', μ', hμ', rfl⟩ := (mem_ladderPiece he).1 hq
  rw [pieceLine_fst, pieceLine_fst] at hpq
  have hμμ := lineMap_inj hs hpq
  subst hμμ
  by_cases hkk : k = k'
  · subst hkk; rfl
  · exact (eI_disj he hi hkk hk hk' hμ hμ').elim

theorem pieceLine_zero {y : E → List ℝ} {s : E × E} {e : Option (ℕ × ℝ × ℝ)} {i k : ℕ}
    (hk : k ≤ 1) : pieceLine y s e i k 0 = (s.1, ladderY y s.1 i) := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp [pieceLine]
  · interval_cases k
    · simp [pieceLine]
    · simp [pieceLine, zzLine]

theorem pieceLine_one {y : E → List ℝ} {s : E × E} {e : Option (ℕ × ℝ × ℝ)} {i k : ℕ}
    (hk : k = 0 ∨ k = 3 ∨ k = 4) (h3 : k = 3 → i - 2 + 2 = i) :
    pieceLine y s e i k 1 = (s.2, ladderY y s.2 i) := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp [pieceLine]
  · rcases hk with rfl | rfl | rfl
    · simp [pieceLine]
    · simp [pieceLine, zzLine, h3 rfl]
    · simp [pieceLine]

/-- The point of a piece over the first end of the edge. -/
theorem ladderPiece_snd_of_fst {y : E → List ℝ} {s : E × E} {e : Option (ℕ × ℝ × ℝ)} {i : ℕ}
    (hs : s.1 ≠ s.2) (he : EvOK (y s.1).length e) {p : E × ℝ} (hp : p ∈ ladderPiece y s e i)
    (h1 : p.1 = s.1) : p = (s.1, ladderY y s.1 i) := by
  obtain ⟨k, hk, μ, hμ, rfl⟩ := (mem_ladderPiece he).1 hp
  rw [pieceLine_fst] at h1
  have := lineMap_inj hs (h1.trans (AffineMap.lineMap_apply_zero (k := ℝ) s.1 s.2).symm)
  subst this
  exact pieceLine_zero (eI_zero he hk hμ)

/-- The point of a piece over the second end of the edge. -/
theorem ladderPiece_snd_of_snd {y : E → List ℝ} {s : E × E} {e : Option (ℕ × ℝ × ℝ)} {i : ℕ}
    (hs : s.1 ≠ s.2) (he : EvOK (y s.1).length e) {p : E × ℝ} (hp : p ∈ ladderPiece y s e i)
    (h1 : p.1 = s.2) : p = (s.2, ladderY y s.2 i) := by
  obtain ⟨k, hk, μ, hμ, rfl⟩ := (mem_ladderPiece he).1 hp
  rw [pieceLine_fst] at h1
  have := lineMap_inj hs (h1.trans (AffineMap.lineMap_apply_one (k := ℝ) s.1 s.2).symm)
  subst this
  refine pieceLine_one (eI_one he hk hμ) fun h3 => ?_
  subst h3
  rcases e with _ | ⟨m, lam, h⟩
  · simp [eI] at hμ
  · simp only [eI, wI] at hμ
    split_ifs at hμ with c
    · omega
    · exact absurd hμ (notMem_empty _)

/-- The point over the first end belongs to the `i`-th piece when `i ≤ j(s.1)`. -/
theorem mem_ladderPiece_fst {y : E → List ℝ} {s : E × E} {e : Option (ℕ × ℝ × ℝ)} {i : ℕ}
    (he : EvOK (y s.1).length e) (hi : 1 ≤ i) (hij : i ≤ (y s.1).length) :
    (s.1, ladderY y s.1 i) ∈ ladderPiece y s e i := by
  rw [mem_ladderPiece he]
  rcases e with _ | ⟨m, lam, h⟩
  · exact ⟨0, by norm_num, 0, by simp [eI, hi, hij], pieceLine_zero (by norm_num)⟩
  · obtain ⟨hm, hmj, hl0, hl1⟩ := he
    by_cases him : i < m
    · exact ⟨0, by norm_num, 0, by simp [eI, wI, hi, hij, him], pieceLine_zero (by norm_num)⟩
    · refine ⟨1, by norm_num, 0, ?_, pieceLine_zero (by norm_num)⟩
      simp only [eI, wI, if_pos (show m ≤ i ∧ i ≤ (y s.1).length by omega), mem_Icc, le_refl,
        true_and]
      have := zz_lr (y s.1).length m lam i
      have := zzL_ge (j := (y s.1).length) (m := m) hl0 i
      have := zU_pos (j := (y s.1).length) (m := m) hl0
      linarith

/-- The point over the second end belongs to the `i`-th piece when `i ≤ j(s.2)`. -/
theorem mem_ladderPiece_snd {y : E → List ℝ} {s : E × E} {e : Option (ℕ × ℝ × ℝ)} {i : ℕ}
    (he : EvOK (y s.1).length e) (hi : 1 ≤ i) (hij : i ≤ eJ2 (y s.1).length e) :
    (s.2, ladderY y s.2 i) ∈ ladderPiece y s e i := by
  rw [mem_ladderPiece he]
  rcases e with _ | ⟨m, lam, h⟩
  · simp only [eJ2] at hij
    exact ⟨0, by norm_num, 1, by simp [eI, hi, hij], pieceLine_one (Or.inl rfl) (by omega)⟩
  · obtain ⟨hm, hmj, hl0, hl1⟩ := he
    simp only [eJ2] at hij
    by_cases him : i < m
    · exact ⟨0, by norm_num, 1, by simp [eI, wI, hi, him, show i ≤ (y s.1).length by omega],
        pieceLine_one (Or.inl rfl) (by omega)⟩
    by_cases him' : i = m ∨ i = m + 1
    · exact ⟨4, by norm_num, 1, by simp [eI, wI, him', hl1.le],
        pieceLine_one (Or.inr (Or.inr rfl)) (by omega)⟩
    · refine ⟨3, by norm_num, 1, ?_, pieceLine_one (Or.inr (Or.inl rfl)) (fun _ => by omega)⟩
      simp only [eI, wI, if_pos (show m + 2 ≤ i ∧ i ≤ (y s.1).length + 2 by omega), mem_Icc,
        le_refl, and_true]
      have h1 := zz_lr (y s.1).length m lam (i - 2)
      have h2 := zz_lam (j := (y s.1).length) (m := m) (c := i - 2) hl0 (by omega) (by omega)
      have := zU_pos (j := (y s.1).length) (m := m) hl0
      linarith

theorem pieceLine_tip {y : E → List ℝ} {s : E × E} {m i : ℕ} {lam h : ℝ} (hl1 : lam < 1) :
    pieceLine y s (some (m, lam, h)) i 4 lam = (AffineMap.lineMap s.1 s.2 lam, h) := by
  simp only [pieceLine]
  rw [lineMap_prod]
  congr 1
  rw [AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
  have : (1 - lam) ≠ 0 := by linarith
  field_simp
  ring

theorem image_fst_ladderAlpha (y : E → List ℝ) (s : E × E) (e : Option (ℕ × ℝ × ℝ)) (i : ℕ) :
    Prod.fst '' ladderAlpha y s e i = AffineMap.lineMap s.1 s.2 '' eA (y s.1).length e i := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp [ladderAlpha, eA]
  · simp only [ladderAlpha, eA, wA, image_union]
    congr 1
    · congr 1 <;> split_ifs <;> simp [zzLine_eq]
    · split_ifs <;> simp

theorem ladderAlpha_finite (y : E → List ℝ) (s : E × E) (e : Option (ℕ × ℝ × ℝ)) (i : ℕ) :
    (ladderAlpha y s e i).Finite := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp [ladderAlpha]
  · simp only [ladderAlpha]
    refine ((Finite.union ?_ ?_).union ?_) <;> split_ifs <;> simp

theorem ladderAlpha_one {y : E → List ℝ} {s : E × E} {e : Option (ℕ × ℝ × ℝ)}
    (he : EvOK (y s.1).length e) : ladderAlpha y s e 1 = ∅ := by
  rcases e with _ | ⟨m, lam, h⟩
  · rfl
  · have := he.1
    simp only [ladderAlpha]
    simp (disch := omega) only [if_neg, union_empty]

theorem ladderAlpha_top {y : E → List ℝ} {s : E × E} {e : Option (ℕ × ℝ × ℝ)} {i : ℕ}
    (he : EvOK (y s.1).length e) (hi : eJ2 (y s.1).length e < i) : ladderAlpha y s e i = ∅ := by
  rcases e with _ | ⟨m, lam, h⟩
  · rfl
  · have := he.2.1
    simp only [eJ2] at hi
    simp only [ladderAlpha]
    simp (disch := omega) only [if_neg, union_empty]

/-- The points of `αᵢ` and of `αᵢ₊₁` over an edge lie on the `i`-th piece. -/
theorem ladderAlpha_subset {y : E → List ℝ} {s : E × E} {e : Option (ℕ × ℝ × ℝ)} {i : ℕ}
    (he : EvOK (y s.1).length e) (hi : 1 ≤ i) :
    ladderAlpha y s e i ∪ ladderAlpha y s e (i + 1) ⊆ ladderPiece y s e i := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp [ladderAlpha]
  have he' := he
  obtain ⟨hm, hmj, hl0, hl1⟩ := he
  have hz := zU_pos (j := (y s.1).length) (m := m) hl0
  intro p hp
  rw [mem_ladderPiece he']
  simp only [ladderAlpha, mem_union] at hp
  rcases hp with ((hp | hp) | hp) | ((hp | hp) | hp) <;> split_ifs at hp with c <;>
    first | exact absurd hp (notMem_empty _) | rw [mem_singleton_iff] at hp <;> subst hp
  · refine ⟨2, by norm_num, zzR (y s.1).length m lam (i - 1), ?_, rfl⟩
    simp only [eI, wI, if_pos c, mem_Icc, le_refl, and_true]
    have := zz_lr (y s.1).length m lam (i - 1); linarith
  · refine ⟨3, by norm_num, zzL (y s.1).length m lam (i - 2), ?_, rfl⟩
    simp only [eI, wI, if_pos c, mem_Icc, le_refl, true_and]
    have := zz_lr (y s.1).length m lam (i - 2)
    have := zz_lam (j := (y s.1).length) (m := m) (c := i - 2) hl0 (by omega) (by omega)
    linarith
  · refine ⟨4, by norm_num, lam, ?_, pieceLine_tip hl1⟩
    simp only [eI, wI, if_pos (Or.inr c), mem_Icc, le_refl, true_and]; exact hl1.le
  · refine ⟨1, by norm_num, zzR (y s.1).length m lam i, ?_, by simp [pieceLine]⟩
    simp only [eI, wI, if_pos (show m ≤ i ∧ i ≤ (y s.1).length by omega), mem_Icc, le_refl, and_true]
    have := zz_lr (y s.1).length m lam i
    have := zzL_ge (j := (y s.1).length) (m := m) hl0 i
    linarith
  · refine ⟨2, by norm_num, zzL (y s.1).length m lam (i - 1), ?_, by
      simp [pieceLine, show i + 1 - 2 = i - 1 by omega]⟩
    simp only [eI, wI, if_pos (show m + 1 ≤ i ∧ i ≤ (y s.1).length + 1 by omega), mem_Icc, le_refl, true_and]
    have := zz_lr (y s.1).length m lam (i - 1); linarith
  · refine ⟨4, by norm_num, lam, ?_, pieceLine_tip hl1⟩
    simp only [eI, wI, if_pos (Or.inl (show i = m by omega)), mem_Icc, le_refl, true_and]
    exact hl1.le

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem ladderY_mem {y : E → List ℝ} {v : E} (hy : ∀ t ∈ y v, t ∈ Icc (0 : ℝ) 1) (i : ℕ) :
    ladderY y v i ∈ Icc (0 : ℝ) 1 := by
  unfold ladderY
  rw [List.getD_eq_getElem?_getD]
  rcases h : (y v)[i - 1]? with _ | t
  · simp
  · simpa using hy t (List.mem_of_getElem? h)

/-- A piece lies over its edge, at heights in `[0, 1]`. -/
theorem ladderPiece_subset {y : E → List ℝ} {s : E × E} {e : Option (ℕ × ℝ × ℝ)} {i : ℕ}
    (he : EvOK (y s.1).length e) (hy1 : ∀ t ∈ y s.1, t ∈ Icc (0 : ℝ) 1)
    (hy2 : ∀ t ∈ y s.2, t ∈ Icc (0 : ℝ) 1)
    (hh : ∀ m lam h, e = some (m, lam, h) → h ∈ Icc (0 : ℝ) 1) :
    ladderPiece y s e i ⊆ segment ℝ s.1 s.2 ×ˢ Icc 0 1 := by
  have hK : Convex ℝ (segment ℝ s.1 s.2 ×ˢ Icc (0 : ℝ) 1) :=
    (convex_segment _ _).prod (convex_Icc _ _)
  have hA : ∀ c, ((s.1, ladderY y s.1 c) : E × ℝ) ∈ segment ℝ s.1 s.2 ×ˢ Icc (0 : ℝ) 1 :=
    fun c => ⟨left_mem_segment ℝ _ _, ladderY_mem hy1 c⟩
  have hB : ∀ c, ((s.2, ladderY y s.2 c) : E × ℝ) ∈ segment ℝ s.1 s.2 ×ˢ Icc (0 : ℝ) 1 :=
    fun c => ⟨right_mem_segment ℝ _ _, ladderY_mem hy2 c⟩
  rcases e with _ | ⟨m, lam, h⟩
  · simp only [ladderPiece]
    split_ifs
    · exact hK.segment_subset (hA i) (hB i)
    · exact empty_subset _
  · simp only [ladderPiece]
    have hT : ((AffineMap.lineMap s.1 s.2 lam, h) : E × ℝ) ∈
        segment ℝ s.1 s.2 ×ˢ Icc (0 : ℝ) 1 := by
      refine ⟨?_, hh m lam h rfl⟩
      rw [segment_eq_image_lineMap]
      exact ⟨lam, ⟨he.2.2.1.le, he.2.2.2.le⟩, rfl⟩
    have hZ : ∀ c μ, μ ∈ Icc (0 : ℝ) 1 → zzLine y s c μ ∈ segment ℝ s.1 s.2 ×ˢ Icc (0 : ℝ) 1 :=
      fun c μ hμ => hK.lineMap_mem (hA c) (hB (c + 2)) hμ
    have hP := e_P_sub (j := (y s.1).length) (i := i) he
    refine union_subset (union_subset (union_subset (union_subset ?_ ?_) ?_) ?_) ?_ <;>
      split_ifs with c <;> try exact empty_subset _
    · exact hK.segment_subset (hA i) (hB i)
    · refine hK.segment_subset (hZ _ _ ?_) (hZ _ _ ?_)
      · have := hP (eI_sub_eP (j := (y s.1).length) (e := some (m, lam, h)) (k := 1) (by norm_num)
          (show (0 : ℝ) ∈ eI (y s.1).length (some (m, lam, h)) i 1 by
            simp only [eI, wI, if_pos c, mem_Icc, le_refl, true_and]
            have := zz_lr (y s.1).length m lam i
            have := zzL_ge (j := (y s.1).length) (m := m) he.2.2.1 i
            have := zU_pos (j := (y s.1).length) (m := m) he.2.2.1
            linarith))
        exact this
      · exact hP (eI_sub_eP (j := (y s.1).length) (e := some (m, lam, h)) (k := 1) (by norm_num)
          (show zzR (y s.1).length m lam i ∈ eI (y s.1).length (some (m, lam, h)) i 1 by
            simp only [eI, wI, if_pos c, mem_Icc, le_refl, and_true]
            have := zz_lr (y s.1).length m lam i
            have := zzL_ge (j := (y s.1).length) (m := m) he.2.2.1 i
            have := zU_pos (j := (y s.1).length) (m := m) he.2.2.1
            linarith))
    · refine hK.segment_subset (hZ _ _ ?_) (hZ _ _ ?_)
      · exact hP (eI_sub_eP (j := (y s.1).length) (e := some (m, lam, h)) (k := 2) (by norm_num)
          (show zzL (y s.1).length m lam (i - 1) ∈ eI (y s.1).length (some (m, lam, h)) i 2 by
            simp only [eI, wI, if_pos c, mem_Icc, le_refl, true_and]
            have := zz_lr (y s.1).length m lam (i - 1)
            have := zU_pos (j := (y s.1).length) (m := m) he.2.2.1
            linarith))
      · exact hP (eI_sub_eP (j := (y s.1).length) (e := some (m, lam, h)) (k := 2) (by norm_num)
          (show zzR (y s.1).length m lam (i - 1) ∈ eI (y s.1).length (some (m, lam, h)) i 2 by
            simp only [eI, wI, if_pos c, mem_Icc, le_refl, and_true]
            have := zz_lr (y s.1).length m lam (i - 1)
            have := zU_pos (j := (y s.1).length) (m := m) he.2.2.1
            linarith))
    · refine hK.segment_subset (hZ _ _ ?_) (hZ _ _ ⟨zero_le_one, le_rfl⟩)
      exact hP (eI_sub_eP (j := (y s.1).length) (e := some (m, lam, h)) (k := 3) (by norm_num)
          (show zzL (y s.1).length m lam (i - 2) ∈ eI (y s.1).length (some (m, lam, h)) i 3 by
            simp only [eI, wI, if_pos c, mem_Icc, le_refl, true_and]
            have := zz_lr (y s.1).length m lam (i - 2)
            have := zz_lam (j := (y s.1).length) (m := m) (c := i - 2) he.2.2.1 (by omega)
              (by omega)
            have := zU_pos (j := (y s.1).length) (m := m) he.2.2.1
            have := he.2.2.2
            linarith))
    · exact hK.segment_subset hT (hB i)

theorem eI_shape {j i k : ℕ} {e : Option (ℕ × ℝ × ℝ)} (he : EvOK j e) (hk : k < 5) :
    eI j e i k = ∅ ∨ ∃ a b : ℝ, a < b ∧ eI j e i k = Icc a b := by
  rcases e with _ | ⟨m, lam, h⟩
  · simp only [eI]
    split_ifs
    · exact Or.inr ⟨0, 1, zero_lt_one, rfl⟩
    · exact Or.inl rfl
  · obtain ⟨hm, hmj, hl0, hl1⟩ := he
    have hz := zU_pos (j := j) (m := m) hl0
    simp only [eI]
    interval_cases k <;> simp only [wI] <;> split_ifs with c <;> first | exact Or.inl rfl | skip
    · exact Or.inr ⟨0, 1, zero_lt_one, rfl⟩
    · refine Or.inr ⟨0, _, ?_, rfl⟩
      have := zz_lr j m lam i
      have := zzL_ge (j := j) (m := m) hl0 i
      linarith
    · refine Or.inr ⟨_, _, ?_, rfl⟩
      have := zz_lr j m lam (i - 1)
      linarith
    · refine Or.inr ⟨_, 1, ?_, rfl⟩
      have := zz_lr j m lam (i - 2)
      have := zz_lam (j := j) (m := m) (c := i - 2) hl0 (by omega) (by omega)
      linarith
    · exact Or.inr ⟨lam, 1, hl1, rfl⟩

/-- `π` of a piece is a PL graph. -/
theorem isPLGraph_image_eP {s : E × E} (hs : s.1 ≠ s.2) {j i : ℕ} {e : Option (ℕ × ℝ × ℝ)}
    (he : EvOK j e) : IsPLGraph (AffineMap.lineMap s.1 s.2 '' eP j e i) := by
  rw [eP_eq_iUnion, image_iUnion₂]
  change IsPLGraph (⋃ k ∈ {k : ℕ | k < 5}, AffineMap.lineMap s.1 s.2 '' eI j e i k)
  refine IsPLGraph.biUnion_finite (Set.finite_lt_nat 5) fun k hk => ?_
  rcases eI_shape (i := i) he hk with h0 | ⟨a, b, hab, h0⟩
  · rw [h0, image_empty]; exact isPLGraph_empty
  · rw [h0, ← segment_lineMap_Icc _ _ hab.le]
    exact isPLGraph_segment fun h => hab.ne (lineMap_inj hs h)

theorem isCompact_ite_Icc (c : Prop) [Decidable c] (a b : ℝ) :
    IsCompact (if c then Icc a b else (∅ : Set ℝ)) := by
  split_ifs
  · exact isCompact_Icc
  · exact isCompact_empty

theorem isCompact_eQA (j : ℕ) (e : Option (ℕ × ℝ × ℝ)) (i : ℕ) : IsCompact (eQA j e i) := by
  rcases e with _ | ⟨m, lam, h⟩
  · exact isCompact_ite_Icc _ _ _
  · simp only [eQA, wQA]
    exact ((((isCompact_ite_Icc _ _ _).union (isCompact_ite_Icc _ _ _)).union
      (isCompact_ite_Icc _ _ _)).union (isCompact_ite_Icc _ _ _)).union (isCompact_ite_Icc _ _ _)

theorem isCompact_eQB (j : ℕ) (e : Option (ℕ × ℝ × ℝ)) (i : ℕ) : IsCompact (eQB j e i) := by
  rcases e with _ | ⟨m, lam, h⟩
  · exact isCompact_ite_Icc _ _ _
  · simp only [eQB, wQB]
    exact ((((isCompact_ite_Icc _ _ _).union (isCompact_ite_Icc _ _ _)).union
      (isCompact_ite_Icc _ _ _)).union (isCompact_ite_Icc _ _ _)).union (isCompact_ite_Icc _ _ _)

theorem isCompact_eP (j : ℕ) (e : Option (ℕ × ℝ × ℝ)) (i : ℕ) : IsCompact (eP j e i) := by
  rcases e with _ | ⟨m, lam, h⟩
  · exact isCompact_ite_Icc _ _ _
  · simp only [eP, wP]
    exact ((((isCompact_ite_Icc _ _ _).union (isCompact_ite_Icc _ _ _)).union
      (isCompact_ite_Icc _ _ _)).union (isCompact_ite_Icc _ _ _)).union (isCompact_ite_Icc _ _ _)

theorem isCompact_ite_segment (c : Prop) [Decidable c] (a b : E × ℝ) :
    IsCompact (if c then segment ℝ a b else (∅ : Set (E × ℝ))) := by
  split_ifs
  · exact Subdiv.isCompact_segment' a b
  · exact isCompact_empty

theorem isCompact_ladderPiece (y : E → List ℝ) (s : E × E) (e : Option (ℕ × ℝ × ℝ)) (i : ℕ) :
    IsCompact (ladderPiece y s e i) := by
  rcases e with _ | ⟨m, lam, h⟩
  · exact isCompact_ite_segment _ _ _
  · simp only [ladderPiece]
    exact ((((isCompact_ite_segment _ _ _).union (isCompact_ite_segment _ _ _)).union
      (isCompact_ite_segment _ _ _)).union (isCompact_ite_segment _ _ _)).union
      (isCompact_ite_segment _ _ _)

end

end HPC.HO16
