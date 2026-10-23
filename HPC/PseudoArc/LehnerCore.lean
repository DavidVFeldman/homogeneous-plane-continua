import HPC.PseudoArc.Recon86

/-!
# Batch 114: the combinatorial core of Lehner's Lemma 3 (`n = 2`)

Auxiliary file for `HPC/PseudoArc/Lehner.lean` (COMMISSION-batch114.md §1–2). It contains the
chain combinatorics of Lehner's proof on p. 376 (Trans. AMS 98 (1961)), with the second
continuum `H_2` and its chain `E_2` dropped: in the covering step only the initial segment
`D(P_1, Q_1)` is asked for, and the last link of `G` already contains `Q'` only.

* `Lehner.exists_eq_of_lip`: discrete intermediate values for a `1`-Lipschitz `ℕ`-valued function
  on `Fin v`.
* `Lehner.dist_le_of_near`: two points in links at index distance `≤ 2` are at distance `≤ 3δ`.
* `Lehner.core`: Lehner's construction of `D` from `E_1`, `F` and `G` (`G` crooked in `F`).

*Batch 115* (recorded in REPORT-batch115.md): `indices` takes the hypothesis that the second link
of `F` lies in the first link of `E` and also returns Lehner's `y_1` (a link of `G` after `z_1`,
inside `f_2 ⊆ e_1`, all links of `G` up to it in links of `E`); `blocks` also returns the block
structure after `z` (single links of `G`, at index `m - 1 + (l - z)`) and the block `m - 1`
containing `R`; `core` returns the index `a` of the block of `y_1`. The earlier conclusions are
unchanged.
-/

namespace HPC

open Set Metric

variable {X : Type*} [MetricSpace X]

namespace Lehner

/-- **Discrete intermediate values.** A function `Fin v → ℕ` moving by at most one between
adjacent indices takes every value between its values at `a ≤ b` somewhere in `[a, b]`. -/
theorem exists_eq_of_lip {v : ℕ} (f : Fin v → ℕ)
    (hlip : ∀ l l' : Fin v, l'.val = l.val + 1 → f l' ≤ f l + 1 ∧ f l ≤ f l' + 1)
    (a b : Fin v) (hab : a ≤ b) (c : ℕ) (hc : (f a ≤ c ∧ c ≤ f b) ∨ (f b ≤ c ∧ c ≤ f a)) :
    ∃ l, a ≤ l ∧ l ≤ b ∧ f l = c := by
  obtain ⟨d, hd⟩ : ∃ d, b.val = a.val + d := ⟨b.val - a.val, by have : a.val ≤ b.val := hab; omega⟩
  induction d generalizing b with
  | zero =>
      have hba : b = a := Fin.ext (by omega)
      subst hba
      exact ⟨b, le_rfl, le_rfl, by omega⟩
  | succ d ih =>
      by_cases hcb : f b = c
      · exact ⟨b, hab, le_rfl, hcb⟩
      · set b' : Fin v := ⟨b.val - 1, by omega⟩ with hb'
        have hl := hlip b' b (by simp only [hb']; omega)
        have hc' : (f a ≤ c ∧ c ≤ f b') ∨ (f b' ≤ c ∧ c ≤ f a) := by omega
        obtain ⟨l, h1, h2, h3⟩ := ih b' (show a.val ≤ b'.val by simp only [hb']; omega) hc'
          (by simp only [hb']; omega)
        exact ⟨l, h1, le_trans h2 (show b'.val ≤ b.val by simp only [hb']; omega), h3⟩

/-- Points of two links at index distance at most two, in a chain of mesh `≤ δ`, are at distance
at most `3δ`. -/
theorem dist_le_of_near {u : ℕ} (F : Chain X u) {δ : ℝ}
    (hbdd : ∀ l, Bornology.IsBounded (F.link l)) (hδ : ∀ l, diam (F.link l) ≤ δ)
    {l l' : Fin u} (h1 : l.val ≤ l'.val + 2) (h2 : l'.val ≤ l.val + 2) {z y : X}
    (hz : z ∈ F.link l) (hy : y ∈ F.link l') : dist z y ≤ 3 * δ := by
  set c : Fin u := ⟨(l.val + l'.val) / 2, by omega⟩ with hc
  obtain ⟨a, ha1, ha2⟩ := (F.adjacent_iff l c).mpr (by simp only [hc]; omega)
  obtain ⟨b, hb1, hb2⟩ := (F.adjacent_iff c l').mpr (by simp only [hc]; omega)
  have e1 := (dist_le_diam_of_mem (hbdd l) hz ha1).trans (hδ l)
  have e2 := (dist_le_diam_of_mem (hbdd c) ha2 hb1).trans (hδ c)
  have e3 := (dist_le_diam_of_mem (hbdd l') hb2 hy).trans (hδ l')
  have := dist_triangle4 z a b y
  linarith

/-- **Lehner's chain `D` from the index `z_1`** (the last paragraph of the proof on p. 376, with
`E_2` dropped). If every link of `G` up to `z` lies in a link of `E`, the link `z` in the last link
of `E`, and the links up to `z` cover `W ∋ R`, then the consolidation of `G` whose first `m` links
are the unions of the links `g_l` (`l ≤ z`) assigned to the links of `E`, followed by the links
`g_{z+1}, …, g_{v-1}` unchanged, is a chain from `P'` to `Q'` covering `W` up to `R`. -/
theorem blocks {m v : ℕ} {P' Q' R : X} {W : Set X} (hRW : R ∈ W)
    (E : Chain X m) (hE : E.IsFrom P' R) (G : Chain X v) (hG : G.IsFrom P' Q')
    (z : Fin v) (hzv : z.val + 1 < v) (hGE : ∀ l, l ≤ z → ∃ i, G.link l ⊆ E.link i)
    (hzE : G.link z ⊆ E.link ⟨m - 1, by obtain ⟨h, -⟩ := hE; omega⟩)
    (hWz : ∀ q ∈ W, ∃ l, l ≤ z ∧ q ∈ G.link l) :
    ∃ (p : ℕ) (β : Fin v → Fin p) (hβ : Chain.IsBlockMap β),
      (G.ofBlocks β hβ).IsFrom P' Q' ∧ Description.CoversUpTo (G.ofBlocks β hβ) P' R W ∧
      (∀ w, (∃ i, (G.ofBlocks β hβ).link w ⊆ E.link i) ∨
        (∃ l, (G.ofBlocks β hβ).link w = G.link l)) ∧
      (∃ hp : m - 1 < p, R ∈ (G.ofBlocks β hβ).link ⟨m - 1, hp⟩) ∧
      (∀ w : Fin p, (hw : w.val < m) → (G.ofBlocks β hβ).link w ⊆ E.link ⟨w.val, hw⟩) ∧
      (∀ l : Fin v, z < l → ∃ w : Fin p, w.val = m - 1 + (l.val - z.val) ∧
        (G.ofBlocks β hβ).link w = G.link l) ∧
      (∀ w : Fin p, m ≤ w.val → ∃ l : Fin v, z < l ∧ w.val = m - 1 + (l.val - z.val)) := by
  classical
  obtain ⟨hm0, hP'E0, hRE, hP'Eu, hREu⟩ := hE
  obtain ⟨hv, hP'G0, hQ'Gl, hP'Gu, hQ'Gu⟩ := hG
  -- a container `γ l` in `E` for each `l ≤ z`, the last link of `E` at `z`
  have hγex : ∀ l : Fin v, ∃ i : Fin m, (l ≤ z → G.link l ⊆ E.link i) ∧ (l = z → i.val = m - 1) := by
    intro l
    by_cases hlz : l = z
    · subst hlz
      exact ⟨⟨m - 1, by omega⟩, fun _ => hzE, fun _ => rfl⟩
    · by_cases hle : l ≤ z
      · obtain ⟨i, hi⟩ := hGE l hle
        exact ⟨i, fun _ => hi, fun h => absurd h hlz⟩
      · exact ⟨⟨0, hm0⟩, fun h => absurd h hle, fun h => absurd h hlz⟩
  choose γ hγsub hγz using hγex
  have hγ0 : (γ ⟨0, hv⟩).val = 0 := by
    have := hP'Eu _ (hγsub ⟨0, hv⟩ (Fin.le_def.mpr (Nat.zero_le _)) hP'G0)
    rw [this]
  -- the schedule
  set β : Fin v → ℕ := fun l => if l ≤ z then (γ l).val else m - 1 + (l.val - z.val) with hβdef
  have hβle : ∀ l : Fin v, l ≤ z → β l = (γ l).val := fun l hl => by simp only [hβdef, if_pos hl]
  have hβgt : ∀ l : Fin v, ¬ l ≤ z → β l = m - 1 + (l.val - z.val) :=
    fun l hl => by simp only [hβdef, if_neg hl]
  have hsched : Chain.IsSchedule β := by
    refine ⟨fun l l' hll' => ?_, ⟨⟨0, hv⟩, by rw [hβle _ (Fin.le_def.mpr (Nat.zero_le _)), hγ0]⟩⟩
    by_cases hl' : l' ≤ z
    · have hl : l ≤ z := Fin.le_def.mpr (by have := Fin.le_def.mp hl'; omega)
      rw [hβle _ hl, hβle _ hl']
      obtain ⟨q, hq1, hq2⟩ := (G.adjacent_iff l' l).mpr (by omega)
      exact (E.adjacent _ _).mp ⟨q, hγsub l' hl' hq1, hγsub l hl hq2⟩
    · rw [hβgt _ hl']
      by_cases hl : l ≤ z
      · have hlz : l = z := Fin.ext (by
          have := Fin.le_def.mp hl; have := Fin.not_le.mp hl'; simp only [Fin.lt_def] at this
          omega)
        rw [hβle _ hl, hγz l hlz]
        have := Fin.not_le.mp hl'; simp only [Fin.lt_def] at this
        omega
      · rw [hβgt _ hl]
        have := Fin.not_le.mp hl; simp only [Fin.lt_def] at this
        omega
  obtain ⟨p, β', hβ', hβval⟩ := hsched.exists_blockMap
  set F := G.ofBlocks β' hβ' with hFdef
  have hlinkF : ∀ (u : Fin p) (q : X), q ∈ F.link u ↔ ∃ l, β' l = u ∧ q ∈ G.link l := by
    intro u q
    rw [hFdef, Chain.ofBlocks_link]
    simp only [mem_iUnion, mem_setOf_eq, exists_prop]
  have hβm : ∀ l : Fin v, l ≤ z → β l < m := fun l hl => by rw [hβle _ hl]; exact (γ l).isLt
  have hβm' : ∀ l : Fin v, ¬ l ≤ z → m ≤ β l := fun l hl => by
    rw [hβgt _ hl]; have := Fin.not_le.mp hl; simp only [Fin.lt_def] at this; omega
  -- the last index carries the largest value
  set lst : Fin v := ⟨v - 1, by omega⟩ with hlst
  have hlstz : ¬ lst ≤ z := fun h => by have := Fin.le_def.mp h; simp only [hlst] at this; omega
  have hmax : ∀ l, β l ≤ β lst := by
    intro l
    by_cases hl : l ≤ z
    · have := hβm l hl; have := hβm' lst hlstz; omega
    · rw [hβgt _ hl, hβgt _ hlstz]; have := l.isLt; simp only [hlst]; omega
  have hp0 : 0 < p := (β' ⟨0, hv⟩).pos
  have hplast : β' lst = ⟨p - 1, by omega⟩ := by
    obtain ⟨t, ht⟩ := hβ'.surj ⟨p - 1, by omega⟩
    have h1 : (β' t).val = p - 1 := by rw [ht]
    have h2 := hmax t
    rw [← hβval, ← hβval, h1] at h2
    have h3 := (β' lst).isLt
    exact Fin.ext (by simp only; omega)
  have hmp : m - 1 < p := by
    have := hβval z
    rw [hβle _ le_rfl, hγz z rfl] at this
    have := (β' z).isLt
    omega
  -- a block below `m` lies in the link of `E` of the same index
  have hsmall : ∀ u : Fin p, (hu : u.val < m) → F.link u ⊆ E.link ⟨u.val, hu⟩ := by
    intro u hu q hq
    obtain ⟨l, rfl, hql⟩ := (hlinkF _ q).mp hq
    have hl : l ≤ z := by
      by_contra hl
      have := hβm' l hl; rw [← hβval] at this; omega
    have h1 : (β' l).val = (γ l).val := by rw [hβval, hβle _ hl]
    have h2 : (⟨(β' l).val, by omega⟩ : Fin m) = γ l := Fin.ext h1
    rw [h2]
    exact hγsub l hl hql
  have hsingle : ∀ l : Fin v, ¬ l ≤ z → F.link (β' l) = G.link l := by
    intro l₀ hl₀z
    refine Set.Subset.antisymm (fun q hq => ?_) (fun q hq => (hlinkF _ _).mpr ⟨l₀, rfl, hq⟩)
    obtain ⟨l, hl, hql⟩ := (hlinkF _ _).mp hq
    have h1 := hβval l
    have h2 := hβval l₀
    rw [hl] at h1
    have hlz : ¬ l ≤ z := fun h => by have := hβm l h; have := hβm' l₀ hl₀z; omega
    rw [hβgt _ hlz] at h1
    rw [hβgt _ hl₀z] at h2
    have hzl := Fin.not_le.mp hlz
    have hzl₀ := Fin.not_le.mp hl₀z
    simp only [Fin.lt_def] at hzl hzl₀
    have : l = l₀ := Fin.ext (by omega)
    rwa [this] at hql
  refine ⟨p, β', hβ', ?_, ?_, ?_, ⟨hmp, ?_⟩, fun w hw => hsmall w hw,
    fun l hl => ⟨β' l, ?_, hsingle l (not_le.mpr hl)⟩, fun w hw => ?_⟩
  · -- `F` is a chain from `P'` to `Q'`
    refine ⟨hp0, ?_, ?_, ?_, ?_⟩
    · refine (hlinkF _ _).mpr ⟨⟨0, hv⟩, Fin.ext ?_, hP'G0⟩
      rw [hβval, hβle _ (Fin.le_def.mpr (Nat.zero_le _)), hγ0]
    · exact (hlinkF _ _).mpr ⟨lst, hplast, hQ'Gl⟩
    · intro u hu
      obtain ⟨l, rfl, hl⟩ := (hlinkF u P').mp hu
      rw [hP'Gu l hl]
      exact Fin.ext (by rw [hβval, hβle _ (Fin.le_def.mpr (Nat.zero_le _)), hγ0])
    · intro u hu
      obtain ⟨l, rfl, hl⟩ := (hlinkF u Q').mp hu
      rw [hQ'Gu l hl]
      exact hplast
  · -- `F` covers `W` up to `R`
    refine ⟨hp0, ⟨m - 1, hmp⟩, Fin.le_def.mpr (Nat.zero_le _), ⟨by simp only; omega, ?_, ?_, ?_, ?_⟩,
      ?_⟩
    · show P' ∈ F.link ⟨0 + 0, _⟩
      refine (hlinkF _ _).mpr ⟨⟨0, hv⟩, Fin.ext ?_, hP'G0⟩
      rw [hβval, hβle _ (Fin.le_def.mpr (Nat.zero_le _)), hγ0]
    · show R ∈ F.link ⟨0 + (m - 1 - 0 + 1 - 1), _⟩
      obtain ⟨l, hl, hRl⟩ := hWz R hRW
      refine (hlinkF _ _).mpr ⟨l, Fin.ext ?_, hRl⟩
      have := hREu _ (hγsub l hl hRl)
      rw [hβval, hβle _ hl, this]
      simp only
      omega
    · intro i hi
      have hi' : P' ∈ F.link ⟨0 + i.val, _⟩ := hi
      obtain ⟨l, hl, hPl⟩ := (hlinkF _ _).mp hi'
      have h1 := hP'Gu l hPl
      subst h1
      have h2 := congrArg Fin.val hl
      rw [hβval, hβle _ (Fin.le_def.mpr (Nat.zero_le _)), hγ0] at h2
      exact Fin.ext (by simp only at h2 ⊢; omega)
    · intro i hi
      have hi' : R ∈ F.link ⟨0 + i.val, _⟩ := hi
      have hlt : 0 + i.val < m := by have := i.isLt; simp only at this; omega
      have := hREu _ (hsmall _ hlt hi')
      exact Fin.ext (by have := congrArg Fin.val this; simp only at this ⊢; omega)
    · intro q hq
      obtain ⟨l, hl, hql⟩ := hWz q hq
      refine Chain.mem_span.mpr ⟨β' l, Fin.le_def.mpr (Nat.zero_le _), ?_, (hlinkF _ _).mpr
        ⟨l, rfl, hql⟩⟩
      have := hβm l hl
      rw [← hβval] at this
      exact Fin.le_def.mpr (by simp only; omega)
  · -- every block is small or a single link of `G`
    intro u
    by_cases hu : u.val < m
    · exact Or.inl ⟨_, hsmall u hu⟩
    · right
      obtain ⟨l₀, hl₀⟩ := hβ'.surj u
      refine ⟨l₀, Set.Subset.antisymm (fun q hq => ?_) (fun q hq => (hlinkF _ _).mpr
        ⟨l₀, hl₀, hq⟩)⟩
      obtain ⟨l, hl, hql⟩ := (hlinkF _ _).mp hq
      have hl₀z : ¬ l₀ ≤ z := fun h => by
        have := hβm l₀ h; rw [← hβval, hl₀] at this; omega
      have hlz : ¬ l ≤ z := fun h => by
        have := hβm l h; rw [← hβval, hl] at this; omega
      have h1 := hβval l
      have h2 := hβval l₀
      rw [hl, hβgt _ hlz] at h1
      rw [hl₀, hβgt _ hl₀z] at h2
      have hzl := Fin.not_le.mp hlz
      have hzl₀ := Fin.not_le.mp hl₀z
      simp only [Fin.lt_def] at hzl hzl₀
      have : l = l₀ := Fin.ext (by omega)
      rwa [this] at hql
  · -- `R` lies in the block `m - 1`
    obtain ⟨l, hl, hRl⟩ := hWz R hRW
    refine (hlinkF _ _).mpr ⟨l, Fin.ext ?_, hRl⟩
    have := hREu _ (hγsub l hl hRl)
    rw [hβval, hβle _ hl, this]
  · rw [hβval, hβgt _ (not_le.mpr hl)]
  · obtain ⟨l₀, hl₀⟩ := hβ'.surj w
    have hl₀z : ¬ l₀ ≤ z := fun h => by
      have := hβm l₀ h; rw [← hβval, hl₀] at this; omega
    refine ⟨l₀, Fin.not_le.mp hl₀z, ?_⟩
    rw [← hl₀, hβval, hβgt _ hl₀z]

/-- **Lehner's indices** (p. 376, second to fifth paragraphs, with `E_2` dropped). `E` is a chain
from `P'` to `R` with `m ≥ 2` links, not containing `Q'`; `F` and `G` are chains from `P'` to `Q'`
covering the connected set `W ∋ P', R`, `G` crooked (1948 sense) in `F`, and every link of `F`
within two links of a link meeting `W` lies in a link of `E` (Lehner's "4-linked subchain"
condition). Then there is a link `g_z`, not the last, such that the links of `G` up to `z` lie in
links of `E`, `g_z` lies in the last link of `E`, and the links up to `z` cover `W`. -/
theorem indices {m u v : ℕ} {P' Q' R : X} {W : Set X} (hWc : IsPreconnected W) (hP'W : P' ∈ W)
    (hRW : R ∈ W) (E : Chain X m) (hm : 2 ≤ m) (hE : E.IsFrom P' R) (hQE : Q' ∉ E.union)
    (F : Chain X u) (hF : F.IsFrom P' Q') (hWF : W ⊆ F.union)
    (hwin : ∀ l l' : Fin u, l.val ≤ l'.val + 2 → l'.val ≤ l.val + 2 →
      (F.link l' ∩ W).Nonempty → ∃ i, F.link l ⊆ E.link i)
    (G : Chain X v) (hG : G.IsFrom P' Q') (hGF : G.IsCrookedIn' F) (hWG : W ⊆ G.union)
    (hF1 : ∀ h1 : 1 < u, F.link ⟨1, h1⟩ ⊆ E.link ⟨0, by omega⟩) :
    ∃ z : Fin v, z.val + 1 < v ∧ (∀ l, l ≤ z → ∃ i, G.link l ⊆ E.link i) ∧
      G.link z ⊆ E.link ⟨m - 1, by omega⟩ ∧ (∀ q ∈ W, ∃ l, l ≤ z ∧ q ∈ G.link l) ∧
      ∃ y : Fin v, z < y ∧ (∀ l, l ≤ y → ∃ i, G.link l ⊆ E.link i) ∧
        G.link y ⊆ E.link ⟨0, by omega⟩ := by
  classical
  obtain ⟨hm0, hP'E0, hRE, hP'Eu, hREu⟩ := hE
  obtain ⟨hu, hP'F0, hQ'Fl, hP'Fu, hQ'Fu⟩ := hF
  obtain ⟨hv, hP'G0, hQ'Gl, hP'Gu, hQ'Gu⟩ := hG
  -- `s₁`: the last link of `F` meeting `W`
  set S : Finset (Fin u) := Finset.univ.filter (fun l => (F.link l ∩ W).Nonempty) with hSdef
  have hS : S.Nonempty := ⟨⟨0, hu⟩, (by
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨P', hP'F0, hP'W⟩)⟩
  set s₁ := S.max' hS with hs₁def
  have hs₁ : (F.link s₁ ∩ W).Nonempty := (Finset.mem_filter.mp (S.max'_mem hS)).2
  have hs₁max : ∀ l, (F.link l ∩ W).Nonempty → l ≤ s₁ := fun l hl =>
    S.le_max' l (by simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]; exact hl)
  have hle_s₁ : ∀ l : Fin u, l ≤ s₁ → (F.link l ∩ W).Nonempty := fun l hl =>
    Chain.meet_ordConnected F hWc hWF (Fin.le_def.mpr (Nat.zero_le _)) hl ⟨P', hP'F0, hP'W⟩ hs₁
  -- `f_0` lies in `e_0`, so does not contain `R`
  obtain ⟨i₀, hi₀⟩ := hwin ⟨0, hu⟩ ⟨0, hu⟩ (by simp only; omega) (by simp only; omega)
    ⟨P', hP'F0, hP'W⟩
  have hi₀' : i₀ = ⟨0, hm0⟩ := hP'Eu i₀ (hi₀ hP'F0)
  have hRF0 : R ∉ F.link ⟨0, hu⟩ := fun h => by
    have := congrArg Fin.val (hREu _ (hi₀ h))
    rw [hi₀'] at this
    simp only at this
    omega
  -- `r₁`: a link of `F` containing `R`
  obtain ⟨r, hr⟩ := mem_iUnion.mp (hWF hRW)
  have hr_s₁ : r ≤ s₁ := hs₁max r ⟨R, hr, hRW⟩
  have hr1 : 1 ≤ r.val := by
    by_contra hc
    exact hRF0 (by rwa [show r = ⟨0, hu⟩ from Fin.ext (by simp only; omega)] at hr)
  have hrs : r.val ≤ s₁.val := hr_s₁
  -- `t₁ = s₁ + 2` is a link of `F`
  have ht : s₁.val + 2 < u := by
    by_contra hcon
    obtain ⟨i, hi⟩ := hwin ⟨u - 1, by omega⟩ s₁ (by simp only; omega)
      (by have := s₁.isLt; simp only; omega) hs₁
    exact hQE (mem_iUnion.mpr ⟨i, hi hQ'Fl⟩)
  set t : Fin u := ⟨s₁.val + 2, ht⟩ with htdef
  -- the minimal containing link of `F` along `G`
  have hGref := hGF.1
  set μ := hGref.minIdx with hμdef
  have hμsub : ∀ l, G.link l ⊆ F.link (μ l) := Chain.minIdx_subset hGref
  have hμlip : ∀ l l' : Fin v, l'.val = l.val + 1 →
      (μ l').val ≤ (μ l).val + 1 ∧ (μ l).val ≤ (μ l').val + 1 := fun l l' h => by
    have := Chain.minIdx_lip hGref l l' h
    rw [← hμdef] at this
    omega
  have hμ0 : μ ⟨0, hv⟩ = ⟨0, hu⟩ := hP'Fu _ (hμsub _ hP'G0)
  have hμlast : μ ⟨v - 1, by omega⟩ = ⟨u - 1, by omega⟩ := hQ'Fu _ (hμsub _ hQ'Gl)
  have hsubeq : ∀ l (c : Fin u), (μ l).val = c.val → G.link l ⊆ F.link c := fun l c h => by
    have := hμsub l; rwa [show μ l = c from Fin.ext h] at this
  -- `w₁`: the first link of `G` meeting `f_{t₁}`
  obtain ⟨l₀, -, -, hl₀⟩ := exists_eq_of_lip (fun l => (μ l).val) hμlip ⟨0, hv⟩ ⟨v - 1, by omega⟩
    (Fin.le_def.mpr (Nat.zero_le _)) t.val
    (Or.inl ⟨by simp only [hμ0]; omega, by simp only [hμlast, htdef]; omega⟩)
  set T : Finset (Fin v) := Finset.univ.filter (fun l => (G.link l ∩ F.link t).Nonempty) with hTdef
  have hT : T.Nonempty := ⟨l₀, by
    simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (G.link_nonempty l₀).mono fun q hq => ⟨hq, hsubeq l₀ t hl₀ hq⟩⟩
  set w := T.min' hT with hwdef
  have hw : (G.link w ∩ F.link t).Nonempty := (Finset.mem_filter.mp (T.min'_mem hT)).2
  have hwmin : ∀ l, (G.link l ∩ F.link t).Nonempty → w ≤ l := fun l hl =>
    T.min'_le l (by simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and]; exact hl)
  -- crookedness of `G` in `F` between `f_0` and `f_{t₁}`
  obtain ⟨x, y, hxy, hx, hy⟩ := hGF.2 ⟨0, hu⟩ t (by simp only [htdef]; omega) ⟨0, hv⟩ w
    ⟨P', hP'G0, hP'F0⟩ hw
  have hxy' : 0 < x.val ∧ x.val < y.val ∧ y.val < w.val := by
    rcases hxy with ⟨h1, h2, h3⟩ | ⟨h1, -, -⟩
    · exact ⟨h1, h2, h3⟩
    · exact absurd h1 (by simp only [gt_iff_lt, Fin.lt_def]; omega)
  -- before `w₁`, the links of `G` lie in links of `F` before `f_{t₁}`
  have hμlt : ∀ l : Fin v, l < w → (μ l).val < t.val := by
    intro l hl
    by_contra hc
    push_neg at hc
    obtain ⟨l', -, hl'l, hl'⟩ := exists_eq_of_lip (fun l => (μ l).val) hμlip ⟨0, hv⟩ l
      (Fin.le_def.mpr (Nat.zero_le _)) t.val (Or.inl ⟨by simp only [hμ0]; omega, hc⟩)
    have hmeet : (G.link l' ∩ F.link t).Nonempty :=
      (G.link_nonempty l').mono fun q hq => ⟨hq, hsubeq l' t hl' hq⟩
    exact absurd (hwmin l' hmeet) (not_le.mpr (lt_of_le_of_lt hl'l hl))
  have hμx : s₁.val ≤ (μ x).val := by
    obtain ⟨q, hq⟩ := G.link_nonempty x
    have := (F.adjacent_iff (μ x) _).mp ⟨q, hμsub x hq, hx hq⟩
    simp only [htdef] at this
    omega
  have hμy : (μ y).val ≤ 1 := by
    have := Chain.minIdx_le hGref y hy
    rw [← hμdef] at this
    exact Fin.le_def.mp this
  -- `z₁`: a link of `G` between `g_{x₁}` and `g_{y₁}` inside `f_{r₁}`
  obtain ⟨z, hxz, hzy, hz⟩ := exists_eq_of_lip (fun l => (μ l).val) hμlip x y
    (Fin.le_def.mpr hxy'.2.1.le) r.val (Or.inr ⟨by dsimp only; omega, by dsimp only; omega⟩)
  have hzw : z < w := Fin.lt_def.mpr (by have := Fin.le_def.mp hzy; omega)
  -- the links of `G` up to `w₁` lie in links of `E`
  have hGE : ∀ l : Fin v, l < w → ∃ i, G.link l ⊆ E.link i := by
    intro l hl
    have h1 := hμlt l hl
    by_cases hc : μ l ≤ s₁
    · obtain ⟨i, hi⟩ := hwin (μ l) (μ l) (by omega) (by omega) (hle_s₁ _ hc)
      exact ⟨i, (hμsub l).trans hi⟩
    · have hc' : s₁.val < (μ l).val := Fin.not_le.mp hc
      obtain ⟨i, hi⟩ := hwin (μ l) s₁ (by simp only [htdef] at h1; omega) (by omega) hs₁
      exact ⟨i, (hμsub l).trans hi⟩
  -- `f_{r₁}` lies in the last link of `E`
  obtain ⟨ir, hir⟩ := hwin r r (by omega) (by omega) (hle_s₁ r hr_s₁)
  have hir' : ir = ⟨m - 1, by omega⟩ := hREu _ (hir hr)
  -- the links of `G` meeting `W` come before `g_{x₁}`
  have hWlt : ∀ l : Fin v, (G.link l ∩ W).Nonempty → l < x := by
    intro l hl
    by_contra hc
    push_neg at hc
    obtain ⟨q, hq1, hq2⟩ := Chain.meet_ordConnected G hWc hWG (Fin.le_def.mpr (Nat.zero_le _)) hc
      ⟨P', hP'G0, hP'W⟩ hl
    have := hs₁max _ ⟨q, hx hq1, hq2⟩
    have := Fin.le_def.mp this
    simp only [htdef] at this
    omega
  -- Lehner's `y_1`: the return of `G` into `f_2 ⊆ e_1`, after `z_1`
  have hu1 : 1 < u := by simp only [htdef] at ht; omega
  have hyE : G.link y ⊆ E.link ⟨0, hm0⟩ := hy.trans (hF1 hu1)
  have hyw : y < w := Fin.lt_def.mpr hxy'.2.2
  have hzy' : z < y := by
    rcases eq_or_lt_of_le hzy with he | hlt
    · exfalso
      have hz' : (μ z).val = r.val := hz
      rw [he] at hz'
      have hr1' : r.val = 1 := by omega
      have hRE0 := hF1 hu1 (by rwa [show r = ⟨1, hu1⟩ from Fin.ext hr1'] at hr)
      have := congrArg Fin.val (hREu _ hRE0)
      simp only at this
      omega
    · exact hlt
  refine ⟨z, by have := w.isLt; have := Fin.lt_def.mp hzw; omega,
    fun l hl => hGE l (lt_of_le_of_lt hl hzw), ?_, fun q hq => ?_,
    y, hzy', fun l hl => hGE l (lt_of_le_of_lt hl hyw), hyE⟩
  · rw [← hir']
    exact (hsubeq z r hz).trans hir
  · obtain ⟨l, hl⟩ := mem_iUnion.mp (hWG hq)
    exact ⟨l, (le_of_lt (hWlt l ⟨q, hl, hq⟩)).trans hxz, hl⟩

/-- **Lehner's construction** (p. 376), assembled: `indices` and `blocks`. -/
theorem core {m u v : ℕ} {P' Q' R : X} {W : Set X} (hWc : IsPreconnected W) (hP'W : P' ∈ W)
    (hRW : R ∈ W) (E : Chain X m) (hm : 2 ≤ m) (hE : E.IsFrom P' R) (hQE : Q' ∉ E.union)
    (F : Chain X u) (hF : F.IsFrom P' Q') (hWF : W ⊆ F.union)
    (hwin : ∀ l l' : Fin u, l.val ≤ l'.val + 2 → l'.val ≤ l.val + 2 →
      (F.link l' ∩ W).Nonempty → ∃ i, F.link l ⊆ E.link i)
    (G : Chain X v) (hG : G.IsFrom P' Q') (hGF : G.IsCrookedIn' F) (hWG : W ⊆ G.union)
    (hF1 : ∀ h1 : 1 < u, F.link ⟨1, h1⟩ ⊆ E.link ⟨0, by omega⟩) :
    ∃ (p : ℕ) (β : Fin v → Fin p) (hβ : Chain.IsBlockMap β),
      (G.ofBlocks β hβ).IsFrom P' Q' ∧ Description.CoversUpTo (G.ofBlocks β hβ) P' R W ∧
      (∀ w, (∃ i, (G.ofBlocks β hβ).link w ⊆ E.link i) ∨
        (∃ l, (G.ofBlocks β hβ).link w = G.link l)) ∧
      (∃ hp : m - 1 < p, R ∈ (G.ofBlocks β hβ).link ⟨m - 1, hp⟩) ∧
      ∃ a : Fin p, m - 1 ≤ a.val ∧ (∀ w : Fin p, w ≤ a → ∃ i, (G.ofBlocks β hβ).link w ⊆ E.link i) ∧
        (G.ofBlocks β hβ).link a ⊆ E.link ⟨0, by omega⟩ := by
  obtain ⟨z, hzv, hGE, hzE, hWz, y, hzy, hGy, hyE⟩ :=
    indices hWc hP'W hRW E hm hE hQE F hF hWF hwin G hG hGF hWG hF1
  obtain ⟨p, β, hβ, h1, h2, h3, h4, h5, h6, h7⟩ := blocks hRW E hE G hG z hzv hGE hzE hWz
  obtain ⟨a, ha, hay⟩ := h6 y hzy
  refine ⟨p, β, hβ, h1, h2, h3, h4, a, by omega, fun w hw => ?_, by rw [hay]; exact hyE⟩
  by_cases hwm : w.val < m
  · exact ⟨_, h5 w hwm⟩
  · obtain ⟨l, hzl, hwl⟩ := h7 w (by omega)
    obtain ⟨w', hw', hw'l⟩ := h6 l hzl
    have hww : w' = w := Fin.ext (by omega)
    have hly : l ≤ y := by
      have : w.val ≤ a.val := hw
      have := Fin.lt_def.mp hzl
      have := Fin.lt_def.mp hzy
      exact Fin.le_def.mpr (by omega)
    obtain ⟨i, hi⟩ := hGy l hly
    exact ⟨i, by rw [← hww, hw'l]; exact hi⟩

end Lehner

end HPC
