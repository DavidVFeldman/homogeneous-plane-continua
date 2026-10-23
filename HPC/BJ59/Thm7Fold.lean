import HPC.BJ59.BJChains
import HPC.BJ59.Defs
import HPC.PseudoArc.Statements79

/-!
# Batch 199, library: folding a chain along an index map; the unfolded pattern of a chain map
(commission 199, §6, Theorem 7)

For a chain map `H : Fin m → Fin n` onto `Fin n` with `H r = 0`, `H s = n − 1`, `r ≤ s`, the
sequence `r, r − 1, …, 1, 0, 1, …, m − 1, m − 2, …, s` (Bing–Jones's `X′` without `y′`, `z′`,
p. 177) is a walk in `Fin m` from `r` to `s` with steps of at most one; composed with `H` it is a
pattern from the first link of `D` to the last (`IsPattern`). A chain following it in `D` folds back
(`foldChain`, Bing–Jones's `e_i = e′_i + f_i + g_i`) to a chain following `H`.
-/

namespace HPC.BJ59

open Set Topology Metric

/-! ### Folding -/

section Fold

variable {Y : Type*} [MetricSpace Y]

/-- **Folding a chain** along an index map `π` that moves adjacent indices to adjacent indices and
has a section `main` that keeps adjacent indices adjacent: link `i` is the union of the links over
`i`. -/
def foldChain {N m : ℕ} (E : Chain Y N) (π : Fin N → Fin m)
    (hπ : ∀ k l : Fin N, ((k : ℤ) - l).natAbs ≤ 1 → ((π k : ℤ) - π l).natAbs ≤ 1)
    (main : Fin m → Fin N) (hmain : ∀ i, π (main i) = i)
    (hmainadj : ∀ i j : Fin m, ((i : ℤ) - j).natAbs ≤ 1 → ((main i : ℤ) - main j).natAbs ≤ 1) :
    Chain Y m where
  link i := ⋃ (k : Fin N) (_ : π k = i), E.link k
  isOpen i := isOpen_iUnion fun k => isOpen_iUnion fun _ => E.isOpen k
  adjacent i j := by
    constructor
    · rintro ⟨x, hxi, hxj⟩
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hxi
      obtain ⟨l, hl, hxl⟩ := mem_iUnion₂.1 hxj
      have := hπ k l ((E.adjacent k l).1 ⟨x, hxk, hxl⟩)
      rwa [hk, hl] at this
    · intro h
      obtain ⟨x, hx1, hx2⟩ := (E.adjacent (main i) (main j)).2 (hmainadj i j h)
      exact ⟨x, mem_iUnion₂.2 ⟨main i, hmain i, hx1⟩, mem_iUnion₂.2 ⟨main j, hmain j, hx2⟩⟩

theorem foldChain_link {N m : ℕ} (E : Chain Y N) (π : Fin N → Fin m) (hπ) (main) (hmain)
    (hmainadj) (i : Fin m) :
    (foldChain E π hπ main hmain hmainadj).link i = ⋃ (k : Fin N) (_ : π k = i), E.link k := rfl

theorem link_subset_foldChain {N m : ℕ} (E : Chain Y N) (π : Fin N → Fin m) (hπ) (main) (hmain)
    (hmainadj) (k : Fin N) :
    E.link k ⊆ (foldChain E π hπ main hmain hmainadj).link (π k) :=
  fun _ hx => mem_iUnion₂.2 ⟨k, rfl, hx⟩

end Fold

/-! ### The unfolded walk -/

/-- The walk `r, r − 1, …, 1, 0, 1, …, m − 1, m − 2, …, s` (positions `0, …, N − 1` with
`N = r + m + (m − 1 − s)`). -/
def unfoldIdx (m r : ℕ) (k : ℕ) : ℕ :=
  if k < r then r - k else if k < r + m then k - r else m - 2 - (k - r - m)

/-- The length of the walk. -/
def unfoldLen (m r s : ℕ) : ℕ := r + m + (m - 1 - s)

theorem unfoldIdx_lt {m r : ℕ} (hr : r < m) (k : ℕ) : unfoldIdx m r k < m := by
  unfold unfoldIdx
  split_ifs <;> omega

theorem unfoldIdx_zero (m r : ℕ) (hm : 0 < m) : unfoldIdx m r 0 = r := by
  unfold unfoldIdx; split_ifs <;> omega

theorem unfoldIdx_last {m r s : ℕ} (hrs : r ≤ s) (hs : s < m) :
    unfoldIdx m r (unfoldLen m r s - 1) = s := by
  unfold unfoldIdx unfoldLen; split_ifs <;> omega

theorem unfoldIdx_main (m r i : ℕ) (hi : i < m) : unfoldIdx m r (r + i) = i := by
  unfold unfoldIdx; split_ifs <;> omega

theorem unfoldIdx_step (m r : ℕ) (hm : 0 < m) (k l : ℕ) (hkl : (k : ℤ) - l ≤ 1 ∧ (l : ℤ) - k ≤ 1) :
    ((unfoldIdx m r k : ℤ) - unfoldIdx m r l ≤ 1) ∧ ((unfoldIdx m r l : ℤ) - unfoldIdx m r k ≤ 1) := by
  unfold unfoldIdx; split_ifs <;> omega

/-- The unfolded index map as a map of `Fin`s. -/
def unfoldFin {m : ℕ} (r s : ℕ) (hr : r < m) : Fin (unfoldLen m r s) → Fin m :=
  fun k => ⟨unfoldIdx m r k, unfoldIdx_lt hr k⟩

theorem unfoldFin_adj {m : ℕ} (r s : ℕ) (hr : r < m) (k l : Fin (unfoldLen m r s))
    (h : ((k : ℤ) - l).natAbs ≤ 1) :
    ((unfoldFin r s hr k : ℤ) - unfoldFin r s hr l).natAbs ≤ 1 := by
  have := unfoldIdx_step m r (by omega) k l (by omega)
  simp only [unfoldFin]
  omega

/-- The main copy of index `i`. -/
def unfoldMain {m : ℕ} (r s : ℕ) : Fin m → Fin (unfoldLen m r s) :=
  fun i => ⟨r + i, by unfold unfoldLen; omega⟩

theorem unfoldFin_main {m : ℕ} (r s : ℕ) (hr : r < m) (i : Fin m) :
    unfoldFin r s hr (unfoldMain r s i) = i :=
  Fin.ext (unfoldIdx_main m r i i.2)

theorem unfoldMain_adj {m : ℕ} (r s : ℕ) (i j : Fin m) (h : ((i : ℤ) - j).natAbs ≤ 1) :
    ((unfoldMain r s i : ℤ) - (unfoldMain (m := m) r s j)).natAbs ≤ 1 := by
  simp only [unfoldMain]; push_cast; omega

/-- **The unfolded pattern**: `H` along the walk is a pattern from the first link to the last. -/
theorem isPattern_unfold {m n : ℕ} (H : Fin m → Fin n) (hH : IsChainMap H) {r s : Fin m}
    (hrs : r ≤ s) (hr : (H r).val = 0) (hs : (H s).val = n - 1) :
    Description.IsPattern (H ∘ unfoldFin r s r.2) := by
  have hm : 0 < m := r.pos
  have hn : 0 < n := (H r).pos
  have hN : 0 < unfoldLen m r s := by unfold unfoldLen; omega
  refine ⟨hN, hn, ?_, ?_, fun t t' htt' => hH _ _ (unfoldFin_adj r s r.2 t' t (by omega))⟩
  · have : unfoldFin r s r.2 ⟨0, hN⟩ = r := Fin.ext (unfoldIdx_zero m r hm)
    simp only [Function.comp, this]
    exact Fin.ext hr
  · have : unfoldFin r s r.2 ⟨unfoldLen m r s - 1, by omega⟩ = s :=
      Fin.ext (unfoldIdx_last (m := m) hrs s.2)
    simp only [Function.comp, this]
    exact Fin.ext hs

end HPC.BJ59
