import HPC.Fold.Recon122
import HPC.Fold.Theorem4TwoModel

/-!
# Batch 123: Bing 1948, Theorem 4 in Bing's two-link form; the only-clauses

COMMISSION-batch123.md, items 2 and 3. The skeleton of the commission, with its two `sorry`s
replaced by proofs. Changes of shape (recorded in REPORT-batch123, item 2):

* `theorem4_two` carries the extra hypothesis `hdeg : r < s ∨ k ≠ 3`. Without it the statement is
  false: with three coarse links and `r = s` the conclusion forces a single block, i.e. all of `E`
  in two adjacent links of `D` (`theorem4_two_degenerate_false`, `not_theorem4Literal`). Bing's
  Theorem 4 as printed fails in the same case.
* The import of `Recon122` is kept (it brings `Theorem3Bing`, the new home of the bridge); the
  model construction is in `HPC/Fold/Theorem4TwoModel.lean`.

**Theorem 4 (p. 733).** *If D = [d₁, d₂, ⋯, d_n] is a chain crooked in the chain E =
[e₁, e₂, ⋯, e_m] and D(r, s) is a subchain of D such that a link of D(r, s) intersects e₁ and a
link of D(r, s) intersects e_m, then there is a chain F such that F is a consolidation of D, each
element of F is a subset of the sum of two adjacent links of E, d_r is contained in only the first
link of F, and d_s is contained in only the last.*

*Proof* (Bing). Let D(h, k) be a subchain of D(r, s) such that d_h intersects e₁ and d_k
intersects e_m. For convenience, suppose that h < k and that d_r and d_s are links of D(1, h) and
D(k, n) respectively. By Theorem 3, there is a chain H which is a consolidation of D(1, h) such
that each link of H is a subset of the sum of two adjacent elements of E, d_r is contained in only
the first link of H, and any link of H containing d_h is a subset of either e₁ + e₂ or
e_{m−1} + e_m; also, there is a chain G such that G is a consolidation of D(k, n), each link of G
is a subset of the sum of two adjacent elements of E, d_s is contained in only the first link of
G, and any link of G containing d_k is a subset of e₁ + e₂ or e_{m−1} + e_m. Let h_u and g_v be
the first elements of H and G containing d_h and d_k respectively. Since the case of our theorem
where m ≤ 4 is easily established, we suppose that h_u and g_v are subsets of e₁ + e₂ and
e_{m−1} + e_m respectively. The required chain F is defined as follows: The first links of F are
the links of H(1, u − 1); the last links of F are the links of G(v − 1, 1); if D′ denotes the links
of D in neither H(1, u − 1) nor G(v − 1, 1), the sum of the links of D′ in e₁ + e₂ is a link of F,
the sum of the links of D′ in e₃ but not in e₂ is another link, ⋯, and the sum of the links of D′
in e_{m−1} + e_m is another link of F.

Conventions as in `HPC/Fold/Theorem4.lean`: `E` is the fine chain (Bing's D), `D` the coarse chain
(Bing's E); "a subset of the sum of two adjacent links" is `⊆ D.unionRange j 2`. The repository's
`theorem4` is the three-link form; this file states Bing's.
-/

namespace HPC.Fold

open HPC.Chain HPC.Fold.Recon122 HPC.Fold.Recon123

/-! ### From the model to chains -/

/-- A solution of `TwoConcl` for the data of `E` gives a block consolidation with `E.link r` in
the first block, `E.link s` in the last, and every block in two adjacent links of `D`. -/
theorem chain_of_twoConcl {X : Type*} [MetricSpace X] {n k : ℕ} {E : Chain X n} {D : Chain X k}
    (hcr : E.IsCrookedIn' D) (r s : Fin n) (hrs : r ≤ s)
    (hc : TwoConcl n (chainRho hcr.1) (chainSig hcr.1) r s) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β r).val = 0 ∧ (β s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 2 := by
  have hB := bHyp_of_crooked hcr
  obtain ⟨b, hb0, hmax, hlip, hwid⟩ := hc
  have hrs' : r.val ≤ s.val := Fin.le_def.mp hrs
  have hlt : ∀ t, t < n → b t < b s + 1 := fun t ht => Nat.lt_succ_of_le (hmax t ht)
  have hlip' : ∀ t, t + 1 < n → (b (t + 1) : ℤ) - b t ≤ 1 ∧ (b t : ℤ) - b (t + 1) ≤ 1 := by
    intro t ht; have := hlip t (Nat.zero_le _) (by omega); omega
  have hsurj : ∀ j, j < b s + 1 → ∃ t, t < n ∧ b t = j := by
    intro j hj
    obtain ⟨t, h1, h2, h3⟩ := nat_ivt b r.val (s.val - r.val)
      (fun t h1 h2 => hlip' t (by have := s.isLt; omega)) j
      (Or.inl ⟨by rw [hb0]; omega, by rw [show r.val + (s.val - r.val) = s.val by omega]; omega⟩)
    exact ⟨t, by have := s.isLt; omega, h3⟩
  have hβ := isBlockMap_natBlock b hlt hlip' hsurj
  have hblock : ∀ (v : Fin (b s + 1)) (S : Set X), (∀ t : Fin n, b t = v → E.link t ⊆ S) →
      (E.ofBlocks _ hβ).link v ⊆ S := by
    intro v S hS x hx
    rw [natBlock_link] at hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    exact hS t ht hxt
  have hρ : ∀ t : Fin n, chainRho hcr.1 t = (hcr.1.minIdx t : ℕ) := fun t => by simp [chainRho]
  have hσ : ∀ t : Fin n, chainSig hcr.1 t = (hcr.1.maxIdx t : ℕ) := fun t => by simp [chainSig]
  refine ⟨b s + 1, natBlock b hlt, hβ, by simp [natBlock, hb0], by simp [natBlock], fun v => ?_⟩
  obtain ⟨j, hj⟩ := hwid v.val
  refine ⟨j, hblock v _ fun t htv => ?_⟩
  obtain ⟨h1, h2⟩ := hj t (Nat.zero_le _) (by omega) htv
  have hw := hB.wid t t.isLt
  have e1 := hρ t
  have e2 := hσ t
  rw [e1, e2] at hw
  rw [e2] at h1
  rw [e1] at h2
  by_cases hjr : j ≤ (hcr.1.minIdx t : ℕ)
  · exact (minIdx_subset hcr.1 t).trans (link_subset_unionRange D _ (by omega) (by omega))
  · exact (maxIdx_subset hcr.1 t).trans (link_subset_unionRange D _ (by omega) (by omega))

/-! ### Theorem 4, two-link form (without the only-clauses) -/

/-- **Bing 1948, Theorem 4, two-link form** (block reading): if some link of `E` between `r` and
`s` meets the first link of `D` and some link between `r` and `s` meets the last, then `E` has a
block consolidation, every block in two adjacent links of `D`, in which `E.link r` is in the
first block and `E.link s` in the last.

Bing's proof, in the model (`HPC.Fold.Recon123.two_model`): Theorem 3 (`bing_main`) on `D(1, h)`
with `d_r` first and on `D(k, n)` with `d_s` first, cut at the blocks of `d_h` and `d_k`, the rest
grouped by least level from the bottom (`two_core`, at least five coarse links); at most four
coarse links by an explicit grouping into at most three blocks (`two_small`); `k < h` by mirroring
the coarse chain.

**Change of shape:** the hypothesis `hdeg : r < s ∨ k ≠ 3` is added. It is necessary
(`theorem4_two_degenerate_false`): with `k = 3` and `r = s` a single link may meet both end links
of `D`, and the conclusion then asks for one block holding all of `E` in two adjacent links. -/
theorem theorem4_two {X : Type*} [MetricSpace X] {n k : ℕ} (hk : 0 < k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (r s : Fin n) (hrs : r ≤ s)
    (hlow : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, hk⟩).Nonempty)
    (hhigh : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty)
    (hdeg : r < s ∨ k ≠ 3) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β r).val = 0 ∧ (β s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 2 := by
  obtain ⟨hl, hrl, hls, hlm⟩ := hlow
  obtain ⟨hh, hrh, hhs, hhm⟩ := hhigh
  refine chain_of_twoConcl hcr r s hrs ?_
  exact two_model (bHyp_of_crooked hcr) (Fin.le_def.mp hrs) s.isLt
    ⟨hl.val, Fin.le_def.mp hrl, Fin.le_def.mp hls, hl.isLt, hk, hlm⟩
    ⟨hh.val, Fin.le_def.mp hrh, Fin.le_def.mp hhs, hh.isLt, by omega, hhm⟩
    (hdeg.imp (fun h => Fin.lt_def.mp h) id)

/-- The three-link `theorem4` follows from the two-link one (a two-link window is a three-link
window; in the degenerate case `k = 3`, `r = s`, one block: the three links of `D` are all of
`D`). Not to replace `theorem4`; a consistency check. The hypothesis `hn` of the commissioned
statement is not needed. -/
theorem theorem4_of_two {X : Type*} [MetricSpace X] {n k : ℕ} (hk : 3 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (r s : Fin n) (hrs : r ≤ s)
    (hlow : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, by omega⟩).Nonempty)
    (hhigh : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' r).val = 0 ∧ (β' s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  by_cases hdeg : r < s ∨ k ≠ 3
  · obtain ⟨q, β, hβ, h0, hq, hblk⟩ := theorem4_two (by omega) hcr r s hrs hlow hhigh hdeg
    refine ⟨q, β, hβ, h0, hq, fun u => ?_⟩
    obtain ⟨j, hj⟩ := hblk u
    refine ⟨j, hj.trans fun x hx => ?_⟩
    rw [mem_unionRange] at hx ⊢
    obtain ⟨a, ha1, ha2, ha3, ha4⟩ := hx
    exact ⟨a, ha1, by omega, ha3, ha4⟩
  · push_neg at hdeg
    obtain ⟨-, hk3⟩ := hdeg
    have hβ : IsBlockMap (fun _ : Fin n => (0 : Fin 1)) :=
      ⟨fun j => ⟨r, Subsingleton.elim _ _⟩, fun t t' _ => by simp⟩
    refine ⟨1, fun _ => 0, hβ, rfl, rfl, fun u => ⟨0, fun x hx => ?_⟩⟩
    rw [ofBlocks_link] at hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
    obtain ⟨t, -, hxt⟩ := hx
    obtain ⟨j, hj⟩ := hcr.1 t
    exact link_subset_unionRange D j (by omega) (by have := j.isLt; omega) (hj hxt)

/-! ### The degenerate case: three coarse links and `r = s` -/

/-- The coarse chain of the degenerate example: `(0, 2), (1, 4), (3, 5)`. -/
noncomputable def degCoarseLink : Fin 3 → Set ℝ := ![Set.Ioo 0 2, Set.Ioo 1 4, Set.Ioo 3 5]

/-- The fine chain of the degenerate example: `(1/10, 3/2), (6/5, 19/5), (7/2, 49/10)`; the middle
link meets the first and the last coarse link. -/
noncomputable def degFineLink : Fin 3 → Set ℝ :=
  ![Set.Ioo (1/10) (3/2), Set.Ioo (6/5) (19/5), Set.Ioo (7/2) (49/10)]

/-- The coarse chain of the degenerate example. -/
noncomputable def degCoarse : Chain ℝ 3 where
  link := degCoarseLink
  isOpen t := by fin_cases t <;> simp [degCoarseLink, isOpen_Ioo]
  adjacent s t := by
    fin_cases s <;> fin_cases t <;>
      simp [degCoarseLink, Set.Ioo_inter_Ioo, Set.nonempty_Ioo, min_def] <;> norm_num

/-- The fine chain of the degenerate example. -/
noncomputable def degFine : Chain ℝ 3 where
  link := degFineLink
  isOpen t := by fin_cases t <;> simp [degFineLink, isOpen_Ioo]
  adjacent s t := by
    fin_cases s <;> fin_cases t <;>
      simp [degFineLink, Set.Ioo_inter_Ioo, Set.nonempty_Ioo, max_def, min_def] <;> norm_num

theorem degFine_crooked : degFine.IsCrookedIn' degCoarse := by
  refine ⟨fun t => ?_, fun h k hk => by have := k.isLt; omega⟩
  fin_cases t
  · exact ⟨0, fun x hx => by
      have hx' : x ∈ Set.Ioo (1/10 : ℝ) (3/2) := hx
      show x ∈ Set.Ioo (0 : ℝ) 2
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩⟩
  · exact ⟨1, fun x hx => by
      have hx' : x ∈ Set.Ioo (6/5 : ℝ) (19/5) := hx
      show x ∈ Set.Ioo (1 : ℝ) 4
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩⟩
  · exact ⟨2, fun x hx => by
      have hx' : x ∈ Set.Ioo (7/2 : ℝ) (49/10) := hx
      show x ∈ Set.Ioo (3 : ℝ) 5
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩⟩

/-- The middle fine link meets the first coarse link. -/
theorem degFine_meets_first : (degFine.link 1 ∩ degCoarse.link ⟨0, by norm_num⟩).Nonempty :=
  ⟨3/2, show (3/2 : ℝ) ∈ Set.Ioo (6/5) (19/5) from ⟨by norm_num, by norm_num⟩,
    show (3/2 : ℝ) ∈ Set.Ioo 0 2 from ⟨by norm_num, by norm_num⟩⟩

/-- The middle fine link meets the last coarse link. -/
theorem degFine_meets_last : (degFine.link 1 ∩ degCoarse.link ⟨3 - 1, by norm_num⟩).Nonempty :=
  ⟨7/2, show (7/2 : ℝ) ∈ Set.Ioo (6/5) (19/5) from ⟨by norm_num, by norm_num⟩,
    show (7/2 : ℝ) ∈ Set.Ioo 3 5 from ⟨by norm_num, by norm_num⟩⟩

/-- No set containing the first and the last fine link lies in two adjacent coarse links. -/
theorem degFine_not_two (S : Set ℝ) (h0 : degFine.link 0 ⊆ S) (h2 : degFine.link 2 ⊆ S) (j : ℕ) :
    ¬ S ⊆ degCoarse.unionRange j 2 := by
  intro hS
  have hA : (1/5 : ℝ) ∈ degCoarse.unionRange j 2 :=
    hS (h0 (show (1/5 : ℝ) ∈ Set.Ioo (1/10) (3/2) from ⟨by norm_num, by norm_num⟩))
  have hB : (9/2 : ℝ) ∈ degCoarse.unionRange j 2 :=
    hS (h2 (show (9/2 : ℝ) ∈ Set.Ioo (7/2) (49/10) from ⟨by norm_num, by norm_num⟩))
  rw [mem_unionRange] at hA hB
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := hA
  obtain ⟨b, hb1, hb2, hb3, hb4⟩ := hB
  have ha0 : a = 0 := by
    interval_cases a
    · rfl
    · exfalso
      have : (1/5 : ℝ) ∈ Set.Ioo 1 4 := ha4
      norm_num at this
    · exfalso
      have : (1/5 : ℝ) ∈ Set.Ioo 3 5 := ha4
      norm_num at this
  have hb2' : b = 2 := by
    interval_cases b
    · exfalso
      have : (9/2 : ℝ) ∈ Set.Ioo 0 2 := hb4
      norm_num at this
    · exfalso
      have : (9/2 : ℝ) ∈ Set.Ioo 1 4 := hb4
      norm_num at this
    · rfl
  omega

/-- **`theorem4_two` without `hdeg` is false**: three coarse links, `r = s` the middle fine link,
which meets the first and the last coarse link. A block map with `E.link r` in the first and in the
last block has one block, and the union of all of `E` is in no two adjacent links of `D`. -/
theorem theorem4_two_degenerate_false :
    ∃ (E : Chain ℝ 3) (D : Chain ℝ 3), E.IsCrookedIn' D ∧
      (E.link 1 ∩ D.link ⟨0, by norm_num⟩).Nonempty ∧
      (E.link 1 ∩ D.link ⟨3 - 1, by norm_num⟩).Nonempty ∧
      ∀ (q : ℕ) (β : Fin 3 → Fin q) (hβ : IsBlockMap β), (β 1).val = 0 → (β 1).val = q - 1 →
        ¬ ∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 2 := by
  refine ⟨degFine, degCoarse, degFine_crooked, degFine_meets_first, degFine_meets_last, ?_⟩
  intro q β hβ h0 hq hall
  have hq1 : q = 1 := by have := (β 1).isLt; omega
  subst hq1
  obtain ⟨j, hj⟩ := hall 0
  have hsub : ∀ t : Fin 3, degFine.link t ⊆ (degFine.ofBlocks β hβ).link 0 := by
    intro t x hx
    rw [ofBlocks_link]
    exact Set.mem_biUnion (show β t = 0 from Subsingleton.elim _ _) hx
  exact degFine_not_two _ (hsub 0) (hsub 2) j hj

/-! ### The only-clauses -/

/-- Bing's clause "`d_i` is contained in only the first link of `F`", for a block map `β` with
`β i` the first block: `E.link i` lies in no other block. -/
def OnlyIn {X : Type*} [MetricSpace X] {n q : ℕ} (E : Chain X n) (β : Fin n → Fin q)
    (hβ : IsBlockMap β) (i : Fin n) : Prop :=
  ∀ v, v ≠ β i → ¬ E.link i ⊆ (E.ofBlocks β hβ).link v

/-- **Theorem 4 as printed**: `theorem4_two` with the only-clauses at `r` and `s`. Recorded as a
`Prop`; **refuted** in the degenerate case (`not_theorem4Literal`). -/
def Theorem4Literal : Prop :=
  ∀ (X : Type) [MetricSpace X] (n k : ℕ) (hk : 0 < k) (E : Chain X n) (D : Chain X k),
    E.IsCrookedIn' D → ∀ r s : Fin n, r ≤ s →
    (∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, hk⟩).Nonempty) →
    (∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty) →
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β r).val = 0 ∧ (β s).val = q - 1 ∧ OnlyIn E β hβ r ∧ OnlyIn E β hβ s ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 2

/-- **Bing's Theorem 4 as printed is false in the degenerate case** `m = 3`, `r = s`
(`theorem4_two_degenerate_false`; the only-clauses play no role). -/
theorem not_theorem4Literal : ¬ Theorem4Literal := by
  intro h
  obtain ⟨E, D, hcr, h1, h2, hno⟩ := theorem4_two_degenerate_false
  obtain ⟨q, β, hβ, h0, hq, -, -, hblk⟩ :=
    h ℝ 3 3 (by norm_num) E D hcr 1 1 le_rfl ⟨1, le_rfl, le_rfl, h1⟩ ⟨1, le_rfl, le_rfl, h2⟩
  exact hno q β hβ h0 hq hblk

/-- **Theorem 4 as printed, outside the degenerate case**: `Theorem4Literal` with the hypothesis
`r < s ∨ k ≠ 3` of `theorem4_two`. Open (REPORT-batch123, item 3): it is `theorem4_two` plus the
only-clauses. -/
def Theorem4LiteralND : Prop :=
  ∀ (X : Type) [MetricSpace X] (n k : ℕ) (hk : 0 < k) (E : Chain X n) (D : Chain X k),
    E.IsCrookedIn' D → ∀ r s : Fin n, r ≤ s →
    (∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, hk⟩).Nonempty) →
    (∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty) →
    (r < s ∨ k ≠ 3) →
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β r).val = 0 ∧ (β s).val = q - 1 ∧ OnlyIn E β hβ r ∧ OnlyIn E β hβ s ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 2

/-- **The only-clause holds as soon as a neighbour shares the block**: if a link adjacent to
`E.link i` lies in the block of `i`, then `E.link i` lies in no other block. (A link in another
block `v` could only be covered by its neighbours in `v`, `link_subset_neighbours`; with one
neighbour in its own block that leaves one neighbour, and a point of `E.link i` common with the
neighbour in its own block would lie in two links two apart.) -/
theorem onlyIn_of_neighbour {X : Type*} [MetricSpace X] {n q : ℕ} (E : Chain X n)
    {β : Fin n → Fin q} (hβ : IsBlockMap β) {i t₀ : Fin n}
    (ht₀ : ((t₀ : ℤ) - (i : ℤ)).natAbs = 1) (hβt₀ : β t₀ = β i) : OnlyIn E β hβ i := by
  intro v hv hsub
  have hcov := Recon121.link_subset_neighbours E hβ hv hsub
  obtain ⟨x, hx0, hxi⟩ := (E.adjacent t₀ i).mpr (by omega)
  have hx := hcov hxi
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
  obtain ⟨t₁, ⟨hβt₁, ht₁⟩, hxt₁⟩ := hx
  have hne : t₁ ≠ t₀ := fun e => hv (by rw [← hβt₁, e, hβt₀])
  have hne' : (t₁ : ℤ) ≠ (t₀ : ℤ) := fun e => hne (Fin.ext (by exact_mod_cast e))
  have := (E.adjacent t₀ t₁).mp ⟨x, hx0, hxt₁⟩
  omega

/-- **The only-clause holds for a link not covered by its two neighbours** (`n ≥ 2`). -/
theorem onlyIn_of_not_covered {X : Type*} [MetricSpace X] {n q : ℕ} (E : Chain X n)
    {β : Fin n → Fin q} (hβ : IsBlockMap β) {i : Fin n}
    (hnc : ¬ E.link i ⊆ ⋃ t ∈ {t : Fin n | ((t : ℤ) - (i : ℤ)).natAbs = 1}, E.link t) :
    OnlyIn E β hβ i := by
  intro v hv hsub
  apply hnc
  refine (Recon121.link_subset_neighbours E hβ hv hsub).trans ?_
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx ⊢
  obtain ⟨t, ⟨-, ht⟩, hxt⟩ := hx
  exact ⟨t, ht, hxt⟩

/-- **The pair form of Theorem 3** (the obstruction of item 3, open): for two adjacent links of `E`
lying in a common link of `D`, a consolidation as in `theorem3_bing` with both in the first block.
By `onlyIn_of_neighbour` it gives the only-clause at `i` whenever `E.link i` and one of its
neighbours lie in a common link of `D`. Not proved; the model census of batch 123 finds no
counterexample (REPORT-batch123, item 3). -/
def Theorem3Pair : Prop :=
  ∀ (X : Type) [MetricSpace X] (n k : ℕ) (hk : 0 < k) (E : Chain X n) (D : Chain X k),
    E.IsCrookedIn' D → ∀ (i i' : Fin n), ((i' : ℤ) - (i : ℤ)).natAbs = 1 →
    (∃ j, E.link i ⊆ D.link j ∧ E.link i' ⊆ D.link j) →
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β i).val = 0 ∧ β i' = β i ∧
      (∀ v, ∃ j : ℕ, (E.ofBlocks β hβ).link v ⊆ D.unionRange j 2) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, hk⟩).Nonempty ∨ (E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty) →
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange 0 2 ∨
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange (k - 2) 2)

end HPC.Fold
