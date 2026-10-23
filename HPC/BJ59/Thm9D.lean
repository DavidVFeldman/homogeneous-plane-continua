import HPC.BJ59.Thm9Class
import HPC.Plane.EndPointsT15

/-!
# Batch 200, §5: Bing–Jones's chain `D′` (Theorem 9, second simplification, p. 180)

Route: commission 200 §5, step 2 (numbering from 0). `D` has `m` links, each with a private point
(only the end ones are used); `G` is a fine chain in Bing–Jones's sense properly covering `P` and
refining `D`, with mesh `δ` below a fifth of the separation of nonadjacent links of `D`. A link of
`G` meeting `d_k ∩ d_{k+1}` goes to `d′_{4k+2}`; any other lies in a single `d_l` and goes to
`d′_{4l−1}`, `d′_{4l+1}` or `d′_{4l}` according as it meets a link of `d′_{4l−2}`, of `d′_{4l+2}`,
or neither. `D′` has `4m − 3` links.

* `Allowed j i`: the indices `i` of links of `D` that a point of `P ∩ d′_j` may lie in;
* `exists_fine_bjChain`;
* `bj9_Dside`.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

/-- The links of `D` (resp. `E`) that the `j`-th link of `D′` (resp. `E′`) is attached to. -/
def Allowed (j i : ℕ) : Prop :=
  ((j % 4 = 0 ∨ j % 4 = 1) ∧ i = j / 4) ∨ (j % 4 = 3 ∧ i = j / 4 + 1) ∨
    (j % 4 = 2 ∧ (i = j / 4 ∨ i = j / 4 + 1))

section Dside

variable {X : Type*} [MetricSpace X]

theorem exists_dist_ge_of_notMem_closure {s : Set X} {p : X} (hp : p ∉ closure s) :
    ∃ r > 0, ∀ y ∈ s, r ≤ dist p y := by
  by_contra h
  push_neg at h
  exact hp (Metric.mem_closure_iff.2 fun ε hε => h ε hε)

/-- A private point is at positive distance from the other links. -/
theorem exists_private_radius {n : ℕ} (D : Chain X n) {i : Fin n} {p : X}
    (hp : ∀ j, j ≠ i → p ∉ closure (D.link j)) :
    ∃ r > 0, ∀ j, j ≠ i → ∀ y ∈ D.link j, r ≤ dist p y := by
  classical
  have h : ∀ j : Fin n, ∃ r > 0, j ≠ i → ∀ y ∈ D.link j, r ≤ dist p y := by
    intro j
    by_cases hj : j = i
    · exact ⟨1, one_pos, fun h => absurd hj h⟩
    · obtain ⟨r, hr, hd⟩ := exists_dist_ge_of_notMem_closure (hp j hj)
      exact ⟨r, hr, fun _ => hd⟩
  choose r hr hrd using h
  obtain ⟨r0, hr0, hr0le⟩ := exists_pos_forall_le r hr
  exact ⟨r0, hr0, fun j hj y hy => (hr0le j).trans (hrd j hj y hy)⟩

/-- **Fine chains in Bing–Jones's sense** properly covering a snake-like continuum. -/
theorem exists_fine_bjChain {K : Set X} (hK : IsSnakeLike K) {ε : ℝ} (hε : 0 < ε)
    (hKne : K.Nonempty) :
    ∃ (n : ℕ) (G : Chain X n), IsBJChain G ∧ IsEpsChain G ε ∧ K ⊆ G.union ∧
      ∀ i, (G.link i ∩ K).Nonempty := by
  obtain ⟨n, G0, hG0ε, hKG0, hG0K⟩ := exists_cover_meeting hK.1.2.isPreconnected hKne hK.2 hε
  obtain ⟨G, hGbj, hKG, hGK, hG⟩ := exists_bjChain_shrink hK.1 G0 hKG0 hG0K (fun _ => ∅)
    (fun _ => ⟨isCompact_empty, empty_subset _⟩)
  refine ⟨n, G, hGbj, fun i => ⟨?_, ?_⟩, hKG, hGK⟩
  · exact (hG0ε i).1.subset (subset_closure.trans (hG i).1)
  · calc diam (G.link i) ≤ diam (G0.link i) :=
          diam_mono (subset_closure.trans (hG i).1) (hG0ε i).1
      _ < ε := (hG0ε i).2

/-- Points of a link of an `ε`-chain are less than `ε` apart. -/
theorem dist_lt_of_mem_link {n : ℕ} {G : Chain X n} {ε : ℝ} (hG : IsEpsChain G ε) (a : Fin n)
    {x y : X} (hx : x ∈ G.link a) (hy : y ∈ G.link a) : dist x y < ε :=
  lt_of_le_of_lt (dist_le_diam_of_mem (hG a).1 hx hy) (hG a).2

/-- **Bing–Jones's `D′`** (p. 180, repaired as in commission 200 §5). -/
theorem bj9_Dside {P : Set X} (hP : IsPseudoArc P) {m : ℕ} (hm : 0 < m) (D : Chain X m)
    (hD : IsBJChain D) (hDP : P ⊆ D.union)
    (hpr : ∀ i, ∃ p ∈ P ∩ D.link i, ∀ j, j ≠ i → p ∉ closure (D.link j)) :
    ∃ D' : Chain X (4 * m - 3), IsBJChain D' ∧ P ⊆ D'.union ∧ (∀ j, (D'.link j ∩ P).Nonempty) ∧
      ∀ (j : Fin (4 * m - 3)) (i : ℕ) (p : X), p ∈ P → p ∈ D.linkN i → p ∈ D'.link j →
        Allowed j i := by
  classical
  have hPc : IsCompact P := hP.1.1.1
  have hPconn : IsConnected P := hP.1.1.2
  obtain ⟨δ1, hδ1, hsep⟩ := hD.exists_uniform
  obtain ⟨lam, hlam, hleb⟩ := lebesgue_number_lemma_of_metric hPc D.isOpen hDP
  set i0 : Fin m := ⟨0, hm⟩ with hi0
  set i1 : Fin m := ⟨m - 1, by omega⟩ with hi1
  obtain ⟨p0, ⟨hp0P, hp0D⟩, hp0⟩ := hpr i0
  obtain ⟨p1, ⟨hp1P, hp1D⟩, hp1⟩ := hpr i1
  obtain ⟨r0, hr0, hr0d⟩ := exists_private_radius D hp0
  obtain ⟨r1, hr1, hr1d⟩ := exists_private_radius D hp1
  set δ := min (min (δ1 / 5) (lam / 2)) (min (r0 / 3) (r1 / 3)) with hδdef
  have hδ : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith)
    (by linarith))
  have hδ1' : 5 * δ ≤ δ1 := by
    have := min_le_left (min (δ1 / 5) (lam / 2)) (min (r0 / 3) (r1 / 3))
    have := min_le_left (δ1 / 5) (lam / 2)
    linarith
  have hδlam : δ < lam := by
    have := min_le_left (min (δ1 / 5) (lam / 2)) (min (r0 / 3) (r1 / 3))
    have := min_le_right (δ1 / 5) (lam / 2)
    linarith
  have hδr0 : 3 * δ ≤ r0 := by
    have := min_le_right (min (δ1 / 5) (lam / 2)) (min (r0 / 3) (r1 / 3))
    have := min_le_left (r0 / 3) (r1 / 3)
    linarith
  have hδr1 : 3 * δ ≤ r1 := by
    have := min_le_right (min (δ1 / 5) (lam / 2)) (min (r0 / 3) (r1 / 3))
    have := min_le_right (r0 / 3) (r1 / 3)
    linarith
  obtain ⟨K, G, hGbj, hGε, hPG, hGP⟩ := exists_fine_bjChain hP.1 hδ hPconn.nonempty
  -- basic facts
  have hGd : ∀ a {x y}, x ∈ G.link a → y ∈ G.link a → dist x y < δ := fun a x y hx hy =>
    dist_lt_of_mem_link hGε a hx hy
  have hGref : ∀ a, ∃ l : Fin m, G.link a ⊆ D.link l := by
    intro a
    obtain ⟨z, hz, hzP⟩ := hGP a
    obtain ⟨l, hl⟩ := hleb z hzP
    exact ⟨l, fun y hy => hl (by rw [mem_ball]; linarith [hGd a hy hz])⟩
  have hsepD : ∀ i j : ℕ, i + 2 ≤ j → ∀ x ∈ D.linkN i, ∀ y ∈ D.linkN j, 5 * δ ≤ dist x y :=
    fun i j hij x hx y hy => hδ1'.trans (hsep i j hij x hx y hy)
  have hsepD' : ∀ i j : ℕ, ∀ x ∈ D.linkN i, ∀ y ∈ D.linkN j, dist x y < 5 * δ →
      i ≤ j + 1 ∧ j ≤ i + 1 := by
    intro i j x hx y hy hd
    constructor
    · by_contra h
      have := hsepD j i (by omega) y hy x hx
      rw [dist_comm] at this
      linarith
    · by_contra h
      have := hsepD i j (by omega) x hx y hy
      linarith
  -- the predicates
  set Ov : ℕ → Fin K → Prop := fun k a => (G.link a ∩ D.linkN k ∩ D.linkN (k + 1)).Nonempty
    with hOv
  set InOnly : ℕ → Fin K → Prop := fun l a => G.link a ⊆ D.linkN l ∧ ∀ k, ¬ Ov k a
    with hInOnly
  set Lft : ℕ → Fin K → Prop := fun l a => 1 ≤ l ∧ ∃ b, Ov (l - 1) b ∧
    (G.link a ∩ G.link b).Nonempty with hLft
  set Rgt : ℕ → Fin K → Prop := fun l a => ∃ b, Ov l b ∧ (G.link a ∩ G.link b).Nonempty
    with hRgt
  set Cls : ℕ → Fin K → Prop := fun c a =>
    if c % 4 = 0 then InOnly (c / 4) a ∧ ¬ Lft (c / 4) a ∧ ¬ Rgt (c / 4) a
    else if c % 4 = 1 then InOnly (c / 4) a ∧ Rgt (c / 4) a
    else if c % 4 = 2 then Ov (c / 4) a
    else InOnly (c / 4 + 1) a ∧ Lft (c / 4 + 1) a with hCls
  -- the lemmas
  have LA : ∀ k k' a b, Ov k a → Ov k' b → (G.link a ∩ G.link b).Nonempty → k = k' := by
    intro k k' a b ⟨y, ⟨hya, hyk⟩, hyk1⟩ ⟨z, ⟨hzb, hzk⟩, hzk1⟩ ⟨w, hwa, hwb⟩
    have hd : dist y z < 5 * δ := by
      linarith [dist_triangle y w z, hGd a hya hwa, hGd b hwb hzb]
    have h1 := hsepD' _ _ y hyk z hzk1 hd
    have h2 := hsepD' _ _ y hyk1 z hzk hd
    omega
  have LB : ∀ l l' a b, InOnly l a → InOnly l' b → (G.link a ∩ G.link b).Nonempty → l = l' := by
    intro l l' a b ha hb ⟨x, hxa, hxb⟩
    have hl := ha.1 hxa
    have hl' := hb.1 hxb
    have := linkN_adj D hl hl'
    by_contra hne
    rcases (by omega : l' = l + 1 ∨ l = l' + 1) with h | h
    · exact ha.2 l ⟨x, ⟨hxa, hl⟩, h ▸ hl'⟩
    · exact ha.2 l' ⟨x, ⟨hxa, hl'⟩, h ▸ hl⟩
  have LC : ∀ l k a b, InOnly l a → Ov k b → (G.link a ∩ G.link b).Nonempty →
      (k = l ∧ Rgt l a) ∨ (k + 1 = l ∧ Lft l a) := by
    intro l k a b ha hb hab
    obtain ⟨y, ⟨hyb, hyk⟩, hyk1⟩ := hb
    obtain ⟨x, hxa, hxb⟩ := hab
    have hxl := ha.1 hxa
    have hd : dist x y < 5 * δ := by linarith [hGd b hxb hyb]
    have h1 := hsepD' _ _ x hxl y hyk hd
    have h2 := hsepD' _ _ x hxl y hyk1 hd
    rcases (by omega : l = k ∨ l = k + 1) with h | h
    · left; subst h; exact ⟨rfl, b, ⟨y, ⟨hyb, hyk⟩, hyk1⟩, x, hxa, hxb⟩
    · right; subst h
      refine ⟨rfl, by omega, b, ?_, x, hxa, hxb⟩
      simp only [Nat.add_sub_cancel]
      exact ⟨y, ⟨hyb, hyk⟩, hyk1⟩
  have LE : ∀ l a b, Lft l a → Rgt l b → (G.link a ∩ G.link b).Nonempty → False := by
    rintro l a b ⟨hl1, b0, ⟨y0, ⟨hy0b, hy0k⟩, -⟩, ⟨w0, hw0a, hw0b⟩⟩ ⟨b1, ⟨y1, ⟨hy1b, -⟩, hy1k⟩,
      ⟨w1, hw1b, hw1b1⟩⟩ ⟨w, hwa, hwb⟩
    have hd : dist y0 y1 < 4 * δ := by
      linarith [dist_triangle4 y0 w0 w w1, dist_triangle (y0) w1 y1, hGd b0 hy0b hw0b,
        hGd a hw0a hwa, hGd b hwb hw1b, hGd b1 hw1b1 hy1b,
        dist_triangle y0 w1 y1, dist_triangle4 y0 w0 w y1, dist_triangle w w1 y1]
    have := hsepD (l - 1) (l + 1) (by omega) y0 hy0k y1 hy1k
    linarith
  have hInOnly_idx : ∀ l a p i, InOnly l a → p ∈ G.link a → p ∈ D.linkN i → i = l := by
    intro l a p i ha hpa hpi
    have hpl := ha.1 hpa
    have := linkN_adj D hpi hpl
    by_contra hne
    rcases (by omega : i = l + 1 ∨ l = i + 1) with h | h
    · exact ha.2 l ⟨p, ⟨hpa, hpl⟩, h ▸ hpi⟩
    · exact ha.2 i ⟨p, ⟨hpa, hpi⟩, h ▸ hpl⟩
  -- unfolding the classes
  have hCls0 : ∀ c a, c % 4 = 0 → (Cls c a ↔ InOnly (c / 4) a ∧ ¬ Lft (c / 4) a ∧
      ¬ Rgt (c / 4) a) := fun c a h => by simp only [hCls, if_pos h]
  have hCls1 : ∀ c a, c % 4 = 1 → (Cls c a ↔ InOnly (c / 4) a ∧ Rgt (c / 4) a) :=
    fun c a h => by simp only [hCls, if_neg (show c % 4 ≠ 0 by omega), if_pos h]
  have hCls2 : ∀ c a, c % 4 = 2 → (Cls c a ↔ Ov (c / 4) a) := fun c a h => by
    simp only [hCls, if_neg (show c % 4 ≠ 0 by omega), if_neg (show c % 4 ≠ 1 by omega),
      if_pos h]
  have hCls3 : ∀ c a, c % 4 = 3 → (Cls c a ↔ InOnly (c / 4 + 1) a ∧ Lft (c / 4 + 1) a) :=
    fun c a h => by
      simp only [hCls, if_neg (show c % 4 ≠ 0 by omega), if_neg (show c % 4 ≠ 1 by omega),
        if_neg (show c % 4 ≠ 2 by omega)]
  -- separation
  have hsepC : ∀ a b c c', Cls c a → Cls c' b → (G.link a ∩ G.link b).Nonempty →
      c ≤ c' + 1 ∧ c' ≤ c + 1 := by
    intro a b c c' ha hb hab
    have hba : (G.link b ∩ G.link a).Nonempty := by rw [inter_comm]; exact hab
    rcases (by omega : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3) with hc | hc | hc | hc <;>
    rcases (by omega : c' % 4 = 0 ∨ c' % 4 = 1 ∨ c' % 4 = 2 ∨ c' % 4 = 3) with hc' | hc' | hc' | hc'
    -- (0, *)
    · have := LB _ _ a b ((hCls0 c a hc).1 ha).1 ((hCls0 c' b hc').1 hb).1 hab; omega
    · have := LB _ _ a b ((hCls0 c a hc).1 ha).1 ((hCls1 c' b hc').1 hb).1 hab; omega
    · have ha' := (hCls0 c a hc).1 ha
      rcases LC _ _ a b ha'.1 ((hCls2 c' b hc').1 hb) hab with ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd h ha'.2.2
      · exact absurd h ha'.2.1
    · have := LB _ _ a b ((hCls0 c a hc).1 ha).1 ((hCls3 c' b hc').1 hb).1 hab; omega
    -- (1, *)
    · have := LB _ _ a b ((hCls1 c a hc).1 ha).1 ((hCls0 c' b hc').1 hb).1 hab; omega
    · have := LB _ _ a b ((hCls1 c a hc).1 ha).1 ((hCls1 c' b hc').1 hb).1 hab; omega
    · have ha' := (hCls1 c a hc).1 ha
      rcases LC _ _ a b ha'.1 ((hCls2 c' b hc').1 hb) hab with ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · exact (LE _ a a h ha'.2 ⟨_, (hab.mono inter_subset_left).some_mem, (hab.mono
          inter_subset_left).some_mem⟩).elim
    · have ha' := (hCls1 c a hc).1 ha
      have hb' := (hCls3 c' b hc').1 hb
      have := LB _ _ a b ha'.1 hb'.1 hab
      rw [← this] at hb'
      exact (LE _ b a hb'.2 ha'.2 hba).elim
    -- (2, *)
    · have hb' := (hCls0 c' b hc').1 hb
      rcases LC _ _ b a hb'.1 ((hCls2 c a hc).1 ha) hba with ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd h hb'.2.2
      · exact absurd h hb'.2.1
    · have hb' := (hCls1 c' b hc').1 hb
      rcases LC _ _ b a hb'.1 ((hCls2 c a hc).1 ha) hba with ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · exact (LE _ b b h hb'.2 ⟨_, (hab.mono inter_subset_right).some_mem, (hab.mono
          inter_subset_right).some_mem⟩).elim
    · have := LA _ _ a b ((hCls2 c a hc).1 ha) ((hCls2 c' b hc').1 hb) hab; omega
    · have hb' := (hCls3 c' b hc').1 hb
      rcases LC _ _ b a hb'.1 ((hCls2 c a hc).1 ha) hba with ⟨-, h⟩ | ⟨h, -⟩
      · exact (LE _ b b hb'.2 h ⟨_, (hab.mono inter_subset_right).some_mem, (hab.mono
          inter_subset_right).some_mem⟩).elim
      · omega
    -- (3, *)
    · have := LB _ _ a b ((hCls3 c a hc).1 ha).1 ((hCls0 c' b hc').1 hb).1 hab; omega
    · have ha' := (hCls3 c a hc).1 ha
      have hb' := (hCls1 c' b hc').1 hb
      have := LB _ _ a b ha'.1 hb'.1 hab
      rw [this] at ha'
      exact (LE _ a b ha'.2 hb'.2 hab).elim
    · have ha' := (hCls3 c a hc).1 ha
      rcases LC _ _ a b ha'.1 ((hCls2 c' b hc').1 hb) hab with ⟨-, h⟩ | ⟨h, -⟩
      · exact (LE _ a a ha'.2 h ⟨_, (hab.mono inter_subset_left).some_mem, (hab.mono
          inter_subset_left).some_mem⟩).elim
      · omega
    · have := LB _ _ a b ((hCls3 c a hc).1 ha).1 ((hCls3 c' b hc').1 hb).1 hab; omega
  -- cover
  have hcovC : ∀ a, ∃ c < 4 * m - 3, Cls c a := by
    intro a
    by_cases hov : ∃ k, Ov k a
    · obtain ⟨k, hk⟩ := hov
      have hkm : k + 1 < m := by
        obtain ⟨y, -, hy⟩ := hk
        exact lt_of_mem_linkN D hy
      refine ⟨4 * k + 2, by omega, (hCls2 _ a (by omega)).2 ?_⟩
      rw [show (4 * k + 2) / 4 = k by omega]
      exact hk
    · push_neg at hov
      obtain ⟨l, hl⟩ := hGref a
      have hIn : InOnly l.val a := ⟨fun y hy => mem_linkN_of_mem D l (hl hy), hov⟩
      by_cases hL : Lft l.val a
      · refine ⟨4 * l.val - 1, by have := l.isLt; have := hL.1; omega,
          (hCls3 _ a (by have := hL.1; omega)).2 ?_⟩
        rw [show (4 * l.val - 1) / 4 + 1 = l.val by have := hL.1; omega]
        exact ⟨hIn, hL⟩
      · by_cases hR : Rgt l.val a
        · have hlm : l.val + 1 < m := by
            obtain ⟨b, ⟨y, -, hy⟩, -⟩ := hR
            exact lt_of_mem_linkN D hy
          refine ⟨4 * l.val + 1, by omega, (hCls1 _ a (by omega)).2 ?_⟩
          rw [show (4 * l.val + 1) / 4 = l.val by omega]
          exact ⟨hIn, hR⟩
        · refine ⟨4 * l.val, by have := l.isLt; omega, (hCls0 _ a (by omega)).2 ?_⟩
          rw [show (4 * l.val) / 4 = l.val by omega]
          exact ⟨hIn, hL, hR⟩
  -- the end classes
  have hend : ∀ (i : Fin m) (p : X) (r : ℝ), p ∈ D.link i → 3 * δ ≤ r →
      (∀ j, j ≠ i → ∀ y ∈ D.link j, r ≤ dist p y) → ∀ a, p ∈ G.link a →
      InOnly i.val a ∧ (∀ b y, (G.link a ∩ G.link b).Nonempty → y ∈ G.link b →
        ∀ k : ℕ, y ∈ D.linkN k → k = i.val) := by
    intro i p r hpi hr hpd a hpa
    have hfar : ∀ y k, dist p y < r → y ∈ D.linkN k → k = i.val := by
      intro y k hd hy
      obtain ⟨hk, hy⟩ := (mem_linkN_iff D).1 hy
      by_contra hne
      have := hpd ⟨k, hk⟩ (fun h => hne (congrArg Fin.val h)) y hy
      linarith
    refine ⟨⟨fun y hy => ?_, fun k hk => ?_⟩, fun b y hab hy k hyk => ?_⟩
    · obtain ⟨l, hl⟩ := hGref a
      have := hfar p l.val (by rw [dist_self]; linarith) (mem_linkN_of_mem D l (hl hpa))
      have hli : l = i := Fin.ext this
      rw [← hli]
      exact mem_linkN_of_mem D l (hl hy)
    · obtain ⟨y, ⟨hya, hyk⟩, hyk1⟩ := hk
      have h1 := hfar y k (by linarith [hGd a hpa hya]) hyk
      have h2 := hfar y (k + 1) (by linarith [hGd a hpa hya]) hyk1
      omega
    · obtain ⟨w, hwa, hwb⟩ := hab
      exact hfar y k (by linarith [dist_triangle p w y, hGd a hpa hwa, hGd b hwb hy]) hyk
  obtain ⟨a0, ha0⟩ := mem_iUnion.1 (hPG hp0P)
  obtain ⟨a1, ha1⟩ := mem_iUnion.1 (hPG hp1P)
  have hE0 := hend i0 p0 r0 hp0D hδr0 hr0d a0 ha0
  have hE1 := hend i1 p1 r1 hp1D hδr1 hr1d a1 ha1
  have hc0 : Cls 0 a0 := by
    refine (hCls0 0 a0 rfl).2 ⟨hE0.1, fun h => absurd h.1 (by norm_num), ?_⟩
    rintro ⟨b, ⟨y, ⟨hyb, -⟩, hy1⟩, hab⟩
    have := hE0.2 b y hab hyb 1 hy1
    simp [hi0] at this
  have hc1 : Cls (4 * m - 3 - 1) a1 := by
    have e : (4 * m - 3 - 1) / 4 = m - 1 := by omega
    refine (hCls0 _ a1 (by omega)).2 ?_
    rw [e]
    refine ⟨hE1.1, ?_, ?_⟩
    · rintro ⟨hl1, b, ⟨y, ⟨hyb, hyk⟩, -⟩, hab⟩
      have := hE1.2 b y hab hyb _ hyk
      simp only [hi1] at this
      omega
    · rintro ⟨b, ⟨y, -, hy⟩, -⟩
      have := lt_of_mem_linkN D hy
      omega
  obtain ⟨D', hD'bj, hPD', hD'P, hD'link⟩ := chain_of_classes hPconn.isPreconnected G hGbj hPG
    hGP Cls hcovC hsepC (by omega) ⟨a0, hc0⟩ ⟨a1, hc1⟩
  refine ⟨D', hD'bj, hPD', hD'P, fun j i p hpP hpi hpj => ?_⟩
  rw [hD'link j] at hpj
  obtain ⟨a, ha, hpa⟩ := mem_iUnion₂.1 hpj
  unfold Allowed
  rcases (by omega : j.val % 4 = 0 ∨ j.val % 4 = 1 ∨ j.val % 4 = 2 ∨ j.val % 4 = 3) with
    hc | hc | hc | hc
  · exact Or.inl ⟨Or.inl hc, hInOnly_idx _ a p i ((hCls0 _ a hc).1 ha).1 hpa hpi⟩
  · exact Or.inl ⟨Or.inr hc, hInOnly_idx _ a p i ((hCls1 _ a hc).1 ha).1 hpa hpi⟩
  · refine Or.inr (Or.inr ⟨hc, ?_⟩)
    obtain ⟨y, ⟨hya, hyk⟩, hyk1⟩ := (hCls2 _ a hc).1 ha
    have hd : dist p y < 5 * δ := by linarith [hGd a hpa hya]
    have h1 := hsepD' _ _ p hpi y hyk hd
    have h2 := hsepD' _ _ p hpi y hyk1 hd
    omega
  · exact Or.inr (Or.inl ⟨hc, hInOnly_idx _ a p i ((hCls3 _ a hc).1 ha).1 hpa hpi⟩)

end Dside

end HPC.BJ59
