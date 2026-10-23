import HPC.BJ59.Thm10Lib
import HPC.BJ59.Thm10Runs
import HPC.BJ59.Thm10Window
import HPC.BJ59.Thm8Cor
import HPC.BJ59.Transfer
import HPC.BJ59.Arc

/-!
# Batch 201, §3: the corollary to Theorem 8 on a sub-arc (pp. 178, 187)

`bj_theorem8_cor_sub` (statement as in the skeleton). Route: commission 201 §3.

* `n ≥ 3`: the batch-200 corollary `bj_theorem8_cor`, applied on the window `Q = g ⁻¹' [a, b]`
  (`window_transfer`) to the restriction of `E` and of the run of `F` meeting `Q`
  (`exists_run_meeting`); `R` is clamped outside the run.
* `n = 1`: a zigzag `0, …, ℓ − 1, ℓ − 1, …, 0` with every value repeated three times; a covering
  run of an `ε`-chain over a fibre is long because the fibres have a uniform spread
  (`exists_fibre_spread`).
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Restrict

variable {Y : Type*} [MetricSpace Y]

/-- A chain whose links all meet a preconnected set `S` covered by it restricts to a chain on
`S`. -/
theorem exists_chain_subtype {S : Set Y} (hS : IsPreconnected S) {N : ℕ} (F : Chain Y N)
    (hcov : S ⊆ F.union) (hmeet : ∀ k, (F.link k ∩ S).Nonempty) :
    ∃ F' : Chain S N, ∀ k, F'.link k = Subtype.val ⁻¹' F.link k := by
  haveI : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.1 hS
  let L : Fin N → Set S := fun k => Subtype.val ⁻¹' F.link k
  have hLo : ∀ k, IsOpen (L k) := fun k => (F.isOpen k).preimage continuous_subtype_val
  have hLK : ∀ k, (L k ∩ univ).Nonempty := fun k => by
    obtain ⟨y, hyF, hyS⟩ := hmeet k
    exact ⟨⟨y, hyS⟩, hyF, mem_univ _⟩
  have hKL : (univ : Set S) ⊆ ⋃ k, L k := fun x _ => by
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov x.2)
    exact mem_iUnion.2 ⟨k, hk⟩
  have hLdisj : ∀ i j : Fin N, 1 < ((i : ℤ) - j).natAbs → L i ∩ L j = ∅ := by
    intro i j hij
    refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
    have := (F.adjacent i j).1 ⟨x.1, hx.1, hx.2⟩
    omega
  refine ⟨{ link := L, isOpen := hLo, adjacent := fun i j => ⟨fun ⟨x, hxi, hxj⟩ =>
    (F.adjacent i j).1 ⟨x.1, hxi, hxj⟩, fun hij => ?_⟩ }, fun k => rfl⟩
  have hK := (isPreconnected_univ : IsPreconnected (univ : Set S))
  by_cases h : i.val = j.val
  · obtain rfl : i = j := Fin.ext h
    obtain ⟨x, hx, -⟩ := hLK i
    exact ⟨x, hx, hx⟩
  · rcases (show j.val = i.val + 1 ∨ i.val = j.val + 1 by omega) with h' | h'
    · exact adjacent_meet_of_cover hK L hLo hKL hLK hLdisj i j h'
    · rw [inter_comm]; exact adjacent_meet_of_cover hK L hLo hKL hLK hLdisj j i h'

/-- Restricting the links of an `ε`-chain to a subspace keeps an `ε`-chain. -/
theorem isEpsChain_subtype {S : Set Y} {N : ℕ} {F : Chain Y N} {F' : Chain S N} {ε : ℝ}
    (hF : IsEpsChain F ε) (hF' : ∀ k, F'.link k = Subtype.val ⁻¹' F.link k) :
    IsEpsChain F' ε := by
  intro k
  have hd : ∀ x ∈ F'.link k, ∀ y ∈ F'.link k, dist x y ≤ diam (F.link k) := by
    intro x hx y hy
    rw [hF'] at hx hy
    rw [Subtype.dist_eq]
    exact dist_le_diam_of_mem (hF k).1 hx hy
  refine ⟨Metric.isBounded_iff.2 ⟨_, hd⟩, lt_of_le_of_lt ?_ (hF k).2⟩
  exact Metric.diam_le_of_forall_dist_le diam_nonneg hd

end Restrict

section Zig

/-- The zigzag `0, 0, 0, 1, 1, 1, …, ℓ − 1, ℓ − 1, ℓ − 1, ℓ − 1, …, 0, 0, 0, 0, …`. -/
def zigN (ℓ k : ℕ) : ℕ :=
  if (k / 3) % (2 * ℓ) < ℓ then (k / 3) % (2 * ℓ) else 2 * ℓ - 1 - (k / 3) % (2 * ℓ)

theorem zigN_lt {ℓ : ℕ} (hℓ : 0 < ℓ) (k : ℕ) : zigN ℓ k < ℓ := by
  have := Nat.mod_lt (k / 3) (show 0 < 2 * ℓ by omega)
  unfold zigN
  split_ifs <;> omega

theorem mod_eq_of_decomp {n b Q r : ℕ} (h : n = b * Q + r) (hr : r < b) : n % b = r := by
  subst h
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

theorem zigN_step {ℓ : ℕ} (hℓ : 0 < ℓ) (k : ℕ) :
    zigN ℓ (k + 1) ≤ zigN ℓ k + 1 ∧ zigN ℓ k ≤ zigN ℓ (k + 1) + 1 := by
  have hdm := Nat.div_add_mod (k / 3) (2 * ℓ)
  have hml := Nat.mod_lt (k / 3) (show 0 < 2 * ℓ by omega)
  rcases (show (k + 1) / 3 = k / 3 ∨ (k + 1) / 3 = k / 3 + 1 by omega) with h | h
  · unfold zigN; rw [h]; omega
  · have hm : ((k + 1) / 3) % (2 * ℓ) = if (k / 3) % (2 * ℓ) + 1 < 2 * ℓ then
        (k / 3) % (2 * ℓ) + 1 else 0 := by
      split_ifs with h'
      · exact mod_eq_of_decomp (Q := (k / 3) / (2 * ℓ)) (by omega) h'
      · exact mod_eq_of_decomp (Q := (k / 3) / (2 * ℓ) + 1) (by rw [mul_add]; omega) (by omega)
    unfold zigN
    rw [hm]
    split_ifs <;> omega

theorem zigN_hits {ℓ : ℕ} (hℓ : 0 < ℓ) {d : ℕ} (hd : d < ℓ) (v : ℕ) :
    ∃ k, v ≤ k ∧ k + 2 ≤ v + 6 * ℓ + 1 ∧ ∀ c ≤ 2, zigN ℓ (k + c) = d := by
  set q₀ := (v + 2) / 3 with hq₀
  have hdm := Nat.div_add_mod q₀ (2 * ℓ)
  have hml := Nat.mod_lt q₀ (show 0 < 2 * ℓ by omega)
  have key : ∃ q, q₀ ≤ q ∧ q + 1 ≤ q₀ + 2 * ℓ ∧ q % (2 * ℓ) = d := by
    by_cases h : q₀ % (2 * ℓ) ≤ d
    · refine ⟨2 * ℓ * (q₀ / (2 * ℓ)) + d, by omega, by omega,
        mod_eq_of_decomp rfl (by omega)⟩
    · refine ⟨2 * ℓ * (q₀ / (2 * ℓ) + 1) + d, by rw [mul_add]; omega, by rw [mul_add]; omega,
        mod_eq_of_decomp rfl (by omega)⟩
  obtain ⟨q, hq1, hq2, hqd⟩ := key
  refine ⟨3 * q, by omega, by omega, fun c hc => ?_⟩
  unfold zigN
  rw [show (3 * q + c) / 3 = q by omega, hqd, if_pos hd]

end Zig

section SubArc

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]

/-- The case `n ≥ 3` of `bj_theorem8_cor_sub`. -/
theorem bj_theorem8_cor_sub_three {g : Y → unitInterval} (hg : IsContArcPA g)
    (hS : IsSnakeLike (univ : Set Y)) {a b : unitInterval} (hab : a < b) {n ℓ : ℕ}
    (hn : 3 ≤ n) (E : Chain Y n) (hE : g ⁻¹' Icc a b ⊆ E.union)
    (hEf : ∀ t ∈ Icc a b, ∀ j, (E.link j ∩ g ⁻¹' {t}).Nonempty)
    (H₁ : Fin ℓ → Fin n) (hH₁ : IsChainMap H₁) (hH₁s : Function.Surjective H₁) :
    ∃ ε > 0, ∀ (N : ℕ) (F : Chain Y N), IsEpsChain F ε → g ⁻¹' Icc a b ⊆ F.union →
      ∃ R : Fin N → Fin ℓ, IsChainMap R ∧
        (∀ k, F.link k ∩ g ⁻¹' Icc a b ⊆ E.link (H₁ (R k))) ∧
        ∀ t ∈ Icc a b, ∀ (v w : ℕ) (hw : w < N), v ≤ w →
          g ⁻¹' {t} ⊆ ⋃ (k : Fin N) (_ : v ≤ k.val ∧ k.val ≤ w), F.link k →
          ∀ d : Fin ℓ, ∃ k : ℕ, ∃ hk : k + 2 ≤ w, v ≤ k ∧
            ∀ (c : ℕ) (hc : c ≤ 2), R ⟨k + c, by omega⟩ = d := by
  classical
  obtain ⟨hcs, hfib, hg', hSQ⟩ := window_transfer hg hS hab
  obtain ⟨g', hg'def⟩ : ∃ g' : g ⁻¹' Icc a b → unitInterval,
      g' = fun y => winScale a b (g y.1) := ⟨_, rfl⟩
  rw [← hg'def] at hfib hg'
  have hg'eq : ∀ (x : g ⁻¹' Icc a b) (s' : unitInterval), g' x = s' ↔
      g x.1 = winInv a b hab.le s' := fun x s' => by
    rw [hg'def]; exact winScale_eq_iff hab x.2 s'
  have hQpc : IsPreconnected (g ⁻¹' Icc a b) :=
    isPreconnected_preimage_Icc hg.1 hg.2.2.1 (fun t => (hg.2.2.2 t).1.1.2.isPreconnected) a b
  have hQne : (g ⁻¹' Icc a b).Nonempty := by
    obtain ⟨y, hy⟩ := hg.2.2.1 a
    exact ⟨y, by simp only [mem_preimage, hy]; exact ⟨le_rfl, hab.le⟩⟩
  -- `E` on the window
  obtain ⟨E', hE'⟩ := exists_chain_subtype hQpc E hE fun j => by
    obtain ⟨y, hyE, hya⟩ := hEf a ⟨le_rfl, hab.le⟩ j
    refine ⟨y, hyE, ?_⟩
    simp only [mem_preimage, mem_singleton_iff] at hya
    simp only [mem_preimage, hya]; exact ⟨le_rfl, hab.le⟩
  have hE'cov : univ ⊆ E'.union := fun x _ => by
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hE x.2)
    exact mem_iUnion.2 ⟨j, by rw [hE']; exact hj⟩
  have hE'f : ∀ s' j, (E'.link j ∩ g' ⁻¹' {s'}).Nonempty := by
    intro s' j
    obtain ⟨y, hyE, hys⟩ := hEf _ (winInv_mem hab.le s') j
    have hy : y ∈ Subtype.val '' (g' ⁻¹' {s'}) := by rw [hfib]; exact hys
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨y', by rw [hE']; exact hyE, hy'⟩
  haveI := hcs
  obtain ⟨ε, hε, hmain⟩ := bj_theorem8_cor hg' hSQ hn E' hE'cov hE'f H₁ hH₁ hH₁s
  refine ⟨ε, hε, fun N F hFε hFcov => ?_⟩
  -- the run of `F` meeting the window, on the window
  obtain ⟨p, q, hpq, hqN, hmeetF, hcovF, honlyF⟩ := exists_run_meeting F hQpc hQne hFcov
  let ix : Fin (q - p + 1) → Fin N := fun j => ⟨p + j.val, by omega⟩
  let F₁ : Chain Y (q - p + 1) :=
    { link := fun j => F.link (ix j)
      isOpen := fun j => F.isOpen _
      adjacent := fun i j => by
        rw [F.adjacent_iff]
        simp only [ix]
        omega }
  obtain ⟨F', hF'⟩ := exists_chain_subtype hQpc F₁
    (fun y hy => by
      obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.1 (hcovF hy)
      refine mem_iUnion.2 ⟨⟨k.val - p, by omega⟩, ?_⟩
      show y ∈ F.link (ix _)
      rwa [show ix ⟨k.val - p, by omega⟩ = k from Fin.ext (by simp only [ix]; omega)])
    (fun j => hmeetF (ix j) (by simp [ix]) (by simp [ix]; omega))
  have hF'ε : IsEpsChain F' ε := isEpsChain_subtype (F := F₁) (fun j => hFε (ix j)) hF'
  -- membership in the restricted links
  have hmemF' : ∀ (x : g ⁻¹' Icc a b) (k : Fin N), x.1 ∈ F.link k →
      ∃ h : p ≤ k.val ∧ k.val ≤ q, x ∈ F'.link ⟨k.val - p, by omega⟩ := by
    intro x k hxk
    have h := honlyF k ⟨x.1, hxk, x.2⟩
    refine ⟨h, ?_⟩
    rw [hF']
    show x.1 ∈ F.link (ix _)
    rwa [show ix ⟨k.val - p, by omega⟩ = k from Fin.ext (by simp only [ix]; omega)]
  have hF'cov : univ ⊆ F'.union := fun x _ => by
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hFcov x.2)
    obtain ⟨_, hx⟩ := hmemF' x k hk
    exact mem_iUnion.2 ⟨_, hx⟩
  obtain ⟨R', hR', -, hR'E, hR'3⟩ := hmain _ F' hF'ε hF'cov
  set R : Fin N → Fin ℓ := fun k => R' ⟨min (k.val - p) (q - p), by omega⟩ with hRdef
  have hRk : ∀ (k : Fin N) (j : ℕ) (hj : j < q - p + 1), p ≤ k.val → k.val ≤ q →
      j = k.val - p → R k = R' ⟨j, hj⟩ := by
    intro k j hj h1 h2 h3
    simp only [hRdef]
    congr 1
    ext
    simp only
    omega
  refine ⟨R, fun i j hij => hR' _ _ (by simp only; omega), fun k y ⟨hyk, hyQ⟩ => ?_, ?_⟩
  · obtain ⟨⟨h1, h2⟩, hx⟩ := hmemF' ⟨y, hyQ⟩ k hyk
    have := hR'E _ hx
    rw [hE'] at this
    rwa [hRk k (k.val - p) (by omega) h1 h2 rfl]
  · intro t ht v w hw hvw hcov d
    have hss : t = winInv a b hab.le (winScale a b t) := (winScale_eq_iff hab ht _).1 rfl
    -- the fibre meets the run of `F`
    obtain ⟨y₀, hy₀⟩ := hg.2.2.1 t
    have hy₀Q : y₀ ∈ g ⁻¹' Icc a b := by simp only [mem_preimage, hy₀]; exact ht
    obtain ⟨k₀, ⟨hk₀v, hk₀w⟩, hy₀k⟩ := mem_iUnion₂.1 (hcov (show y₀ ∈ g ⁻¹' {t} from hy₀))
    obtain ⟨⟨hk₀p, hk₀q⟩, -⟩ := hmemF' ⟨y₀, hy₀Q⟩ k₀ hy₀k
    have hcov' : g' ⁻¹' {winScale a b t} ⊆ ⋃ (k : Fin (q - p + 1))
        (_ : max v p - p ≤ k.val ∧ k.val ≤ min w q - p), F'.link k := by
      intro x hx
      have hxt : g x.1 = t := by
        rw [(hg'eq x _).1 hx, ← hss]
      obtain ⟨k, ⟨hkv, hkw⟩, hxk⟩ := mem_iUnion₂.1 (hcov (show x.1 ∈ g ⁻¹' {t} from hxt))
      obtain ⟨⟨h1, h2⟩, hx'⟩ := hmemF' x k hxk
      exact mem_iUnion₂.2 ⟨_, ⟨by simp only; omega, by simp only; omega⟩, hx'⟩
    obtain ⟨k', hk', hvk', hk'd⟩ := hR'3 (winScale a b t) (max v p - p) (min w q - p)
      (by omega) (by omega) hcov' d
    refine ⟨k' + p, by omega, by omega, fun c hc => ?_⟩
    rw [hRk _ (k' + c) (by omega) (by simp only; omega) (by simp only; omega) (by simp only; omega)]
    exact hk'd c hc

/-- The case `n = 1` of `bj_theorem8_cor_sub`. -/
theorem bj_theorem8_cor_sub_one {g : Y → unitInterval} (hg : IsContArcPA g)
    {a b : unitInterval} {ℓ : ℕ} (E : Chain Y 1) (hE : g ⁻¹' Icc a b ⊆ E.union)
    (H₁ : Fin ℓ → Fin 1) (hH₁s : Function.Surjective H₁) :
    ∃ ε > 0, ∀ (N : ℕ) (F : Chain Y N), IsEpsChain F ε → g ⁻¹' Icc a b ⊆ F.union →
      ∃ R : Fin N → Fin ℓ, IsChainMap R ∧
        (∀ k, F.link k ∩ g ⁻¹' Icc a b ⊆ E.link (H₁ (R k))) ∧
        ∀ t ∈ Icc a b, ∀ (v w : ℕ) (hw : w < N), v ≤ w →
          g ⁻¹' {t} ⊆ ⋃ (k : Fin N) (_ : v ≤ k.val ∧ k.val ≤ w), F.link k →
          ∀ d : Fin ℓ, ∃ k : ℕ, ∃ hk : k + 2 ≤ w, v ≤ k ∧
            ∀ (c : ℕ) (hc : c ≤ 2), R ⟨k + c, by omega⟩ = d := by
  have hℓ : 0 < ℓ := by
    obtain ⟨i, -⟩ := hH₁s 0
    exact lt_of_le_of_lt (Nat.zero_le _) i.isLt
  obtain ⟨κ, hκ, hκf⟩ := exists_fibre_spread hg.2.1 fun t => (hg.2.2.2 t).2.2
  have hden : (0 : ℝ) < 6 * ℓ + 2 := by positivity
  refine ⟨κ / (6 * ℓ + 2), div_pos hκ hden, fun N F hFε hFcov => ?_⟩
  set R : Fin N → Fin ℓ := fun k => ⟨zigN ℓ k.val, zigN_lt hℓ _⟩ with hRdef
  refine ⟨R, fun i j hij => ?_, fun k y ⟨_, hyQ⟩ => ?_, ?_⟩
  · simp only [hRdef]
    rcases (show j.val = i.val ∨ j.val = i.val + 1 ∨ i.val = j.val + 1 by omega) with h | h | h
    · rw [h]; simp
    · have := zigN_step hℓ i.val; rw [h]; omega
    · have := zigN_step hℓ j.val; rw [h]; omega
  · obtain ⟨j, hj⟩ := mem_iUnion.1 (hE hyQ)
    rwa [Subsingleton.elim (H₁ (R k)) j]
  · intro t _ v w hw hvw hcov d
    have hlong : v + 6 * ℓ + 1 ≤ w := by
      by_contra hlt
      obtain ⟨x, hx, x', hx', hxx'⟩ := hκf t
      obtain ⟨k, ⟨hkv, hkw⟩, hxk⟩ := mem_iUnion₂.1 (hcov hx)
      obtain ⟨k', ⟨hk'v, hk'w⟩, hx'k'⟩ := mem_iUnion₂.1 (hcov hx')
      have hd := dist_lt_of_mem_closure_link' hFε k k' (subset_closure hxk) (subset_closure hx'k')
      have hnat : (((k : ℤ) - k').natAbs : ℝ) + 1 ≤ 6 * ℓ + 1 := by
        have : ((k : ℤ) - k').natAbs ≤ 6 * ℓ := by omega
        exact_mod_cast Nat.add_le_add_right this 1
      have h1 : (((k : ℤ) - k').natAbs + 1 : ℝ) * (κ / (6 * ℓ + 2)) ≤
          (6 * ℓ + 1) * (κ / (6 * ℓ + 2)) :=
        mul_le_mul_of_nonneg_right hnat (div_pos hκ hden).le
      have h2 : (6 * ℓ + 1 : ℝ) * (κ / (6 * ℓ + 2)) < κ := by
        rw [mul_div_assoc', div_lt_iff₀ hden]; nlinarith
      linarith
    obtain ⟨k, hk1, hk2, hk⟩ := zigN_hits hℓ d.isLt v
    exact ⟨k, by omega, hk1, fun c hc => Fin.ext (hk c hc)⟩

/-- **The corollary to Theorem 8 on a sub-arc** `Q(a, b)` (pp. 178, 187), for a chain of one link
or of at least three. -/
theorem bj_theorem8_cor_sub {g : Y → unitInterval} (hg : IsContArcPA g)
    (hS : IsSnakeLike (univ : Set Y)) {a b : unitInterval} (hab : a < b) {n ℓ : ℕ}
    (hn : n = 1 ∨ 3 ≤ n) (E : Chain Y n) (hE : g ⁻¹' Icc a b ⊆ E.union)
    (hEf : ∀ t ∈ Icc a b, ∀ j, (E.link j ∩ g ⁻¹' {t}).Nonempty)
    (H₁ : Fin ℓ → Fin n) (hH₁ : IsChainMap H₁) (hH₁s : Function.Surjective H₁) :
    ∃ ε > 0, ∀ (N : ℕ) (F : Chain Y N), IsEpsChain F ε → g ⁻¹' Icc a b ⊆ F.union →
      ∃ R : Fin N → Fin ℓ, IsChainMap R ∧
        (∀ k, F.link k ∩ g ⁻¹' Icc a b ⊆ E.link (H₁ (R k))) ∧
        ∀ t ∈ Icc a b, ∀ (v w : ℕ) (hw : w < N), v ≤ w →
          g ⁻¹' {t} ⊆ ⋃ (k : Fin N) (_ : v ≤ k.val ∧ k.val ≤ w), F.link k →
          ∀ d : Fin ℓ, ∃ k : ℕ, ∃ hk : k + 2 ≤ w, v ≤ k ∧
            ∀ (c : ℕ) (hc : c ≤ 2), R ⟨k + c, by omega⟩ = d := by
  rcases hn with rfl | hn
  · exact bj_theorem8_cor_sub_one hg E hE H₁ hH₁s
  · exact bj_theorem8_cor_sub_three hg hS hab hn E hE hEf H₁ hH₁ hH₁s

end SubArc

end HPC.BJ59
