import HPC.BJ59.BJ59A
import HPC.BJ59.NonVac199

/-!
# Batch 199 (optional item BJ.5 of commission 199 §7): the general certificate against Bing–Jones
# Theorem 5 as printed

From any instance of Theorem 5's printed hypotheses with a chain of `n ≥ 3` links, we produce one
(same space, same map, a chain with the same number of links) in which the printed conclusion fails
and no fibre lies in `U`. The construction is the one of commission 198 §6, with one refinement:

* `E'`: the last-but-one link `e_{n−1}` of `E` is enlarged to `e_{n−1} ∪ e_n`, the other links are
  kept (`chainMergePenult`);
* `c = 1/2`, `K = cl(g_c · e_n)`; then `K ⊆ e_{n−1} ∪ e_n`, `K` is compact and misses `g₀ + g₁`;
* `U = N_δ(K) − cl(e₁)` for a small `δ > 0`: `Ū` lies in the merged link and misses `g₀ + g₁`,
  `U ⊇ g_c · e_n`, so `g_c − U` misses the last link of `E'`; and `U` misses `e₁`, which meets every
  fibre, so no fibre lies in `U`. (Removing `cl(e₁)` handles `n = 3`, where `e₁` meets the merged
  link.)

Bing–Jones's indices `e₁, …, e_n` are `0, …, n − 1` here.
-/

namespace HPC.BJ59

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- The chain `E` with its last-but-one link enlarged by the last one: links
`e₁, …, e_{n−2}, e_{n−1} ∪ e_n, e_n` (Bing–Jones's indices). -/
def chainMergePenult {n : ℕ} (E : Chain X n) (hn : 3 ≤ n) : Chain X n where
  link i := if i.val = n - 2 then E.link i ∪ E.link ⟨n - 1, by omega⟩ else E.link i
  isOpen i := by
    split_ifs
    · exact (E.isOpen _).union (E.isOpen _)
    · exact E.isOpen _
  adjacent i j := by
    have hA : ∀ k : Fin n, (E.link k ∩ E.link ⟨n - 1, by omega⟩).Nonempty ↔
        ((k : ℤ) - ((n - 1 : ℕ) : ℤ)).natAbs ≤ 1 := fun k => E.adjacent k _
    have hi := i.2
    have hj := j.2
    split_ifs with h1 h2 h2
    · obtain rfl : i = j := Fin.ext (by omega)
      obtain ⟨x, hx⟩ := E.link_nonempty i
      simp only [sub_self, Int.natAbs_zero, zero_le_one, iff_true]
      exact ⟨x, Or.inl hx, Or.inl hx⟩
    · rw [union_inter_distrib_right, union_nonempty, E.adjacent i j, inter_comm, hA j]
      omega
    · rw [inter_union_distrib_left, union_nonempty, E.adjacent i j, hA i]
      omega
    · exact E.adjacent i j

theorem chainMergePenult_link_of_ne {n : ℕ} (E : Chain X n) (hn : 3 ≤ n) {i : Fin n}
    (hi : i.val ≠ n - 2) : (chainMergePenult E hn).link i = E.link i := by
  simp [chainMergePenult, hi]

theorem chainMergePenult_link_penult {n : ℕ} (E : Chain X n) (hn : 3 ≤ n) :
    (chainMergePenult E hn).link ⟨n - 2, by omega⟩ =
      E.link ⟨n - 2, by omega⟩ ∪ E.link ⟨n - 1, by omega⟩ := by
  simp [chainMergePenult]

theorem subset_chainMergePenult_link {n : ℕ} (E : Chain X n) (hn : 3 ≤ n) (i : Fin n) :
    E.link i ⊆ (chainMergePenult E hn).link i := by
  unfold chainMergePenult
  dsimp only
  split_ifs
  · exact subset_union_left
  · exact subset_rfl

theorem chainMergePenult_union {n : ℕ} (E : Chain X n) (hn : 3 ≤ n) :
    (chainMergePenult E hn).union = E.union := by
  apply Subset.antisymm
  · refine iUnion_subset fun i => ?_
    unfold chainMergePenult
    dsimp only
    split_ifs
    · exact union_subset (subset_iUnion _ _) (subset_iUnion _ _)
    · exact subset_iUnion _ _
  · exact iUnion_mono fun i => subset_chainMergePenult_link E hn i

/-- A point of the closure of the last link of a chain covering the space lies in one of the last
two links. -/
theorem closure_last_subset {n : ℕ} (E : Chain X n) (hn : 3 ≤ n) (hE : univ ⊆ E.union) :
    closure (E.link ⟨n - 1, by omega⟩) ⊆ E.link ⟨n - 2, by omega⟩ ∪ E.link ⟨n - 1, by omega⟩ := by
  intro x hx
  obtain ⟨k, hk⟩ := mem_iUnion.1 (hE (mem_univ x))
  have hmeet : (E.link k ∩ E.link ⟨n - 1, by omega⟩).Nonempty :=
    mem_closure_iff.1 hx _ (E.isOpen k) hk
  have : ((k : ℤ) - ((n - 1 : ℕ) : ℤ)).natAbs ≤ 1 := (E.adjacent _ _).1 hmeet
  have hk2 := k.2
  rcases (show k.val = n - 2 ∨ k.val = n - 1 by omega) with h | h
  · exact Or.inl (by convert hk using 2; exact Fin.ext h.symm)
  · exact Or.inr (by convert hk using 2; exact Fin.ext h.symm)

/-- **BJ.5, the general certificate against Theorem 5 as printed** (commission 199 §7, optional).
From any instance of the printed hypotheses with `n ≥ 3` links (only those used are assumed: a
compact space, a continuous map to `[0, 1]`, a chain covering the space and meeting every fibre in
every link), we get a chain `E'` with `n` links satisfying the same hypotheses and an open `U`
satisfying the printed hypotheses on `U` (nonempty, missing `g₀ + g₁`, `Ū` in a link of `E'`), such
that no fibre lies in `U`, and some fibre meets some link of `E'` only inside `U`; hence for every
expression `G − U = A + B` neither `A · g_c` nor `B · g_c` meets every link, and the printed
conclusion fails. -/
theorem bj_theorem5_printed_false_general [CompactSpace X] {f : X → unitInterval}
    (hfc : Continuous f) {n : ℕ} (hn : 3 ≤ n) (E : Chain X n)
    (hE : univ ⊆ E.union) (hEf : ∀ t i, (E.link i ∩ f ⁻¹' {t}).Nonempty) :
    ∃ E' : Chain X n, univ ⊆ E'.union ∧ (∀ t i, (E'.link i ∩ f ⁻¹' {t}).Nonempty) ∧
      ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ Disjoint U (f ⁻¹' {0, 1}) ∧
        (∃ i, closure U ⊆ E'.link i) ∧ (∀ t, ¬ f ⁻¹' {t} ⊆ U) ∧
        (∃ t i, E'.link i ∩ f ⁻¹' {t} ⊆ U) ∧
        ∀ A B : Set X, A ∪ B = Uᶜ → ∃ t, (∃ i, E'.link i ∩ (A ∩ f ⁻¹' {t}) = ∅) ∧
          (∃ i, E'.link i ∩ (B ∩ f ⁻¹' {t}) = ∅) := by
  set E' := chainMergePenult E hn
  set a : Fin n := ⟨n - 1, by omega⟩
  set b : Fin n := ⟨n - 2, by omega⟩
  set z : Fin n := ⟨0, by omega⟩
  set c : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hc0 : c ≠ 0 := fun h => by
    have := congrArg Subtype.val h; norm_num [c] at this
  have hc1 : c ≠ 1 := fun h => by
    have := congrArg Subtype.val h; norm_num [c] at this
  set K := closure (E.link a ∩ f ⁻¹' {c})
  have hKc : K ⊆ f ⁻¹' {c} :=
    closure_minimal inter_subset_right ((isClosed_singleton).preimage hfc)
  have hKab : K ⊆ E.link b ∪ E.link a :=
    (closure_mono inter_subset_left).trans (closure_last_subset E hn hE)
  have hKcpt : IsCompact K := isClosed_closure.isCompact
  set V := (E.link b ∪ E.link a) ∩ (f ⁻¹' {0, 1})ᶜ
  have hV : IsOpen V := ((E.isOpen b).union (E.isOpen a)).inter
    ((((Set.finite_singleton 1).insert 0).isClosed.preimage hfc).isOpen_compl)
  have hKV : K ⊆ V := fun x hx => ⟨hKab hx, fun h01 => by
    have hxc : f x = c := hKc hx
    rcases h01 with h | h
    · exact hc0 (hxc ▸ h)
    · exact hc1 (hxc ▸ h)⟩
  obtain ⟨δ, hδ, hδV⟩ := hKcpt.exists_cthickening_subset_open hV hKV
  set U := thickening δ K \ closure (E.link z)
  have hUo : IsOpen U := isOpen_thickening.sdiff isClosed_closure
  have haz : E.link a ∩ E.link z = ∅ := by
    rw [← not_nonempty_iff_eq_empty, E.adjacent]
    simp only [a, z]
    omega
  have hsub : E.link a ∩ f ⁻¹' {c} ⊆ U := fun x hx =>
    ⟨self_subset_thickening hδ _ (subset_closure hx), fun hxz => by
      obtain ⟨y, hy⟩ := mem_closure_iff.1 hxz _ (E.isOpen a) hx.1
      exact (haz.subset ⟨hy.1, hy.2⟩ : y ∈ (∅ : Set X))⟩
  have hclU : closure U ⊆ V :=
    (closure_mono diff_subset).trans ((closure_thickening_subset_cthickening _ _).trans hδV)
  have hE'a : E'.link a = E.link a := chainMergePenult_link_of_ne E hn (by simp [a]; omega)
  refine ⟨E', (chainMergePenult_union E hn).symm ▸ hE,
    fun t i => (hEf t i).mono (inter_subset_inter_left _ (subset_chainMergePenult_link E hn i)),
    U, hUo, (hEf c a).mono hsub, ?_, ⟨b, hclU.trans (inter_subset_left.trans_eq
      (chainMergePenult_link_penult E hn).symm)⟩, ?_, ⟨c, a, hE'a ▸ hsub⟩, ?_⟩
  · exact disjoint_left.2 fun x hx h01 => (hclU (subset_closure hx)).2 h01
  · intro t ht
    obtain ⟨x, hxz, hxt⟩ := hEf t z
    exact (ht hxt).2 (subset_closure hxz)
  · intro A B hAB
    refine ⟨c, ⟨a, ?_⟩, ⟨a, ?_⟩⟩ <;>
    · rw [eq_empty_iff_forall_notMem]
      rintro x ⟨hxa, hxS, hxc⟩
      have hxU : x ∈ U := hsub ⟨hE'a ▸ hxa, hxc⟩
      have : x ∈ A ∪ B := by first | exact Or.inl hxS | exact Or.inr hxS
      rw [hAB] at this
      exact this hxU

/-! ### Non-vacuity of the certificate's hypotheses

The unit square with the first projection and three horizontal strips (the pull-back of
`real3Chain` under `p ↦ 1 + 2 p₂`). -/

theorem mem_real3Chain_clamp {x : ℝ} {i : Fin 3} (hx : x ∈ real3Chain.link i) :
    max 1 (min x 3) ∈ real3Chain.link i := by
  have hx' : x ∈ Ioo ((i : ℕ) : ℝ) ((i : ℕ) + 2) := hx
  show max 1 (min x 3) ∈ Ioo ((i : ℕ) : ℝ) ((i : ℕ) + 2)
  fin_cases i <;> simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mem_Ioo] at hx' ⊢ <;>
    constructor <;>
    first
    | exact lt_max_of_lt_right (lt_min hx'.1 (by linarith))
    | exact lt_max_of_lt_left (by norm_num)
    | exact max_lt (by norm_num) (min_lt_of_left_lt hx'.2)

/-- Three horizontal strips of the unit square: `1 + 2 p₂ ∈ (i, i + 2)`. -/
def squareStrips : Chain (unitInterval × unitInterval) 3 where
  link i := (fun p : unitInterval × unitInterval => 1 + 2 * (p.2 : ℝ)) ⁻¹' real3Chain.link i
  isOpen i := (real3Chain.isOpen i).preimage (continuous_const.add (continuous_const.mul
    (continuous_subtype_val.comp continuous_snd)))
  adjacent i j := by
    rw [← real3Chain.adjacent i j]
    constructor
    · rintro ⟨p, hi, hj⟩
      exact ⟨_, hi, hj⟩
    · rintro ⟨x, hi, hj⟩
      set y := max 1 (min x 3)
      have h1 : 1 ≤ y := le_max_left _ _
      have h3 : y ≤ 3 := max_le (by norm_num) (min_le_right _ _)
      have hy : 1 + 2 * ((y - 1) / 2) = y := by ring
      refine ⟨(0, ⟨(y - 1) / 2, by constructor <;> linarith⟩), ?_, ?_⟩
      · show 1 + 2 * ((y - 1) / 2) ∈ real3Chain.link i
        rw [hy]; exact mem_real3Chain_clamp hi
      · show 1 + 2 * ((y - 1) / 2) ∈ real3Chain.link j
        rw [hy]; exact mem_real3Chain_clamp hj

/-- **Non-vacuity of `bj_theorem5_printed_false_general`**: the unit square, the first
projection and `squareStrips` meet its hypotheses (with non-degenerate fibres, the vertical
segments). -/
theorem nonvac_bj_theorem5_printed_false_general :
    Continuous (Prod.fst : unitInterval × unitInterval → unitInterval) ∧
    univ ⊆ squareStrips.union ∧ ∀ t i, (squareStrips.link i ∩ Prod.fst ⁻¹' {t}).Nonempty := by
  refine ⟨continuous_fst, fun p _ => ?_, fun t i => ?_⟩
  · have h0 := p.2.2.1
    have h1 := p.2.2.2
    rcases lt_or_ge (p.2 : ℝ) (1 / 2) with h | h
    · exact mem_iUnion.2 ⟨0, show 1 + 2 * (p.2 : ℝ) ∈ Ioo ((0 : ℕ) : ℝ) ((0 : ℕ) + 2) from
        ⟨by push_cast; linarith, by push_cast; linarith⟩⟩
    rcases lt_or_ge (p.2 : ℝ) (3 / 4) with h' | h'
    · exact mem_iUnion.2 ⟨1, show 1 + 2 * (p.2 : ℝ) ∈ Ioo ((1 : ℕ) : ℝ) ((1 : ℕ) + 2) from
        ⟨by push_cast; linarith, by push_cast; linarith⟩⟩
    · exact mem_iUnion.2 ⟨2, show 1 + 2 * (p.2 : ℝ) ∈ Ioo ((2 : ℕ) : ℝ) ((2 : ℕ) + 2) from
        ⟨by push_cast; linarith, by push_cast; linarith⟩⟩
  · have hi3 : ((i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show (i : ℕ) ≤ 2 by omega)
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨(t, ⟨((i : ℕ) : ℝ) / 2, by constructor <;> linarith⟩), ?_, rfl⟩
    show 1 + 2 * (((i : ℕ) : ℝ) / 2) ∈ Ioo ((i : ℕ) : ℝ) ((i : ℕ) + 2)
    constructor <;> linarith

end HPC.BJ59
