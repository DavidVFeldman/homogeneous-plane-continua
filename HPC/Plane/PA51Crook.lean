import HPC.Plane.EndPoints51

/-!
# Batch 88: crookedness eventually (Bing 1951, *Concerning hereditarily indecomposable
# continua*, proof of Theorem 1, first paragraph)

In a compact metric space `X` that is hereditarily indecomposable (every subcontinuum of `X` is
indecomposable), a chain `C` covering `X`, and chains `E m` refining `C` with mesh tending to zero:
from some `m` on, `E m` is crooked in `C` in the 1948 sense (`IsCrookedIn'`, links *meeting*
`C.link h`, `C.link k`).

The argument is Bing's, with the witnesses chosen so that the two limit continua are visibly not
nested (COMMISSION-batch88.md §3.2). For a failure at `(h, k, i, j)` with `i < j`, let `r` be the
first index after `i` with `E_r ⊆ C_{k-1}`. The span `W` of `E_i, …, E_{r-1}` has *no* link inside
`C_{k-1}`; the span `V` of `E_{r+1}, …, E_j` (or `E_j` alone when `r = j`) has no link inside
`C_{h+1}` (this is the failure). In the limit, `W` misses the open set `C_{k-1}` and `V` misses the
open set `C_{h+1}`; by connectedness `W` meets `C_{h+1}` and `V` meets `C_{k-1}`; so neither
contains the other, and `W ∪ V` is a decomposable subcontinuum.
-/

namespace HPC.Plane

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

namespace PA51

/-! ### Unions of initial and final segments of a chain -/

/-- The union of the links of index below `a`. -/
def lowU {n : ℕ} (C : Chain X n) (a : ℕ) : Set X := ⋃ (l : Fin n) (_ : l.val < a), C.link l

/-- The union of the links of index above `b`. -/
def highU {n : ℕ} (C : Chain X n) (b : ℕ) : Set X := ⋃ (l : Fin n) (_ : b < l.val), C.link l

theorem isOpen_lowU {n : ℕ} (C : Chain X n) (a : ℕ) : IsOpen (lowU C a) :=
  isOpen_iUnion fun l => isOpen_iUnion fun _ => C.isOpen l

theorem isOpen_highU {n : ℕ} (C : Chain X n) (b : ℕ) : IsOpen (highU C b) :=
  isOpen_iUnion fun l => isOpen_iUnion fun _ => C.isOpen l

theorem disjoint_lowU_highU {n : ℕ} (C : Chain X n) {a b : ℕ} (hab : a ≤ b) :
    Disjoint (lowU C a) (highU C b) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [lowU, highU, mem_iUnion] at hx hx'
  obtain ⟨l, hl, hxl⟩ := hx
  obtain ⟨l', hl', hxl'⟩ := hx'
  have := (C.adjacent_iff l l').mp ⟨x, hxl, hxl'⟩
  omega

/-- A preconnected set covered by the chain and missing the link `c` lies on one side of it:
the side of any of its points. -/
theorem subset_side_of_miss {n : ℕ} (C : Chain X n) (hcov : ∀ x : X, ∃ l, x ∈ C.link l)
    {S : Set X} (hS : IsPreconnected S) (c : Fin n) (hmiss : ∀ x ∈ S, x ∉ C.link c) {y : X}
    (hyS : y ∈ S) {l : Fin n} (hyl : y ∈ C.link l) :
    (l.val < c.val → S ⊆ lowU C c.val) ∧ (c.val < l.val → S ⊆ highU C c.val) := by
  have hcover : S ⊆ lowU C c.val ∪ highU C c.val := by
    intro x hx
    obtain ⟨l', hl'⟩ := hcov x
    have hne : l' ≠ c := fun e => hmiss x hx (e ▸ hl')
    have hne' : l'.val ≠ c.val := fun e => hne (Fin.ext e)
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact Or.inl (mem_iUnion₂.mpr ⟨l', by omega, hl'⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨l', by omega, hl'⟩)
  have hdisj := disjoint_lowU_highU C (a := c.val) (b := c.val) le_rfl
  rcases hS.subset_or_subset (isOpen_lowU C _) (isOpen_highU C _) hdisj hcover with h | h
  · refine ⟨fun _ => h, fun hcl => ?_⟩
    exact absurd (mem_iUnion₂.mpr ⟨l, hcl, hyl⟩ : y ∈ highU C c.val)
      (Set.disjoint_left.mp hdisj (h hyS))
  · refine ⟨fun hlc => ?_, fun _ => h⟩
    exact absurd (h hyS) (Set.disjoint_left.mp hdisj
      (mem_iUnion₂.mpr ⟨l, hlc, hyl⟩ : y ∈ lowU C c.val))

/-! ### The data of a failure of crookedness -/

/-- The data extracted from a failure of crookedness of a fine chain in `C` at `(h, k)`: two
`ε`-chained sets `W`, `V` with points `ε` apart, `W` meeting `C_h` and made of pieces of
diameter `≤ ε` none inside `C_{k-1}`, `V` meeting `C_k` and made of pieces none inside
`C_{h+1}`. -/
def FailData {n : ℕ} (C : Chain X n) (h k : Fin n) (hhk : h.val + 2 < k.val) (ε : ℝ) : Prop :=
  ∃ (W V : Set X) (x x' y z : X), T13.ChainedAt W ε ∧ T13.ChainedAt V ε ∧ x ∈ W ∧ x' ∈ V ∧
    dist x x' ≤ ε ∧ y ∈ W ∩ C.link h ∧ z ∈ V ∩ C.link k ∧
    (∀ u ∈ W, ∃ S : Set X, u ∈ S ∧ Bornology.IsBounded S ∧ diam S ≤ ε ∧
      ¬ S ⊆ C.link ⟨k.val - 1, by omega⟩) ∧
    (∀ u ∈ V, ∃ S : Set X, u ∈ S ∧ Bornology.IsBounded S ∧ diam S ≤ ε ∧
      ¬ S ⊆ C.link ⟨h.val + 1, by omega⟩)

/-- The oriented case `i < j` of a failure of crookedness. -/
theorem failData_of_fail_lt {m n : ℕ} {E : Chain X m} {C : Chain X n} (href : E.Refines C)
    {ε : ℝ} (hbdd : ∀ t, Bornology.IsBounded (E.link t)) (hdiam : ∀ t, diam (E.link t) ≤ ε)
    (h k : Fin n) (hhk : h.val + 2 < k.val) (i j : Fin m) (hij : i < j)
    (hi : (E.link i ∩ C.link h).Nonempty) (hj : (E.link j ∩ C.link k).Nonempty)
    (hfail : ∀ r s : Fin m, Chain.Between i r s j → E.link r ⊆ C.link ⟨k.val - 1, by omega⟩ →
      ¬ E.link s ⊆ C.link ⟨h.val + 1, by omega⟩) :
    FailData C h k hhk ε := by
  classical
  set φ := Chain.refineIdx href with hφ
  have hφs : ∀ t, E.link t ⊆ C.link (φ t) := Chain.refineIdx_subset href
  -- `φ i ≤ h + 1` and `k - 1 ≤ φ j`
  have hφi : (φ i).val ≤ h.val + 1 := by
    have := (C.adjacent_iff (φ i) h).mp (hi.mono (inter_subset_inter_left _ (hφs i)))
    omega
  have hφj : k.val - 1 ≤ (φ j).val := by
    have := (C.adjacent_iff (φ j) k).mp (hj.mono (inter_subset_inter_left _ (hφs j)))
    omega
  -- a link after `i`, up to `j`, inside `C_{k-1}`
  have hex : ∃ t : ℕ, i.val < t ∧ ∃ ht : t ≤ j.val,
      E.link ⟨t, by have := j.isLt; omega⟩ ⊆ C.link ⟨k.val - 1, by omega⟩ := by
    obtain ⟨x, y, hxy, hx, -⟩ := Chain.exists_value_between φ hφs (r := j) (s := i)
      (p := ⟨k.val - 1, by omega⟩) (q := φ i) (by simpa using hφj) le_rfl
      (by simp only; omega)
    have hxy' : i.val < x.val ∧ x.val ≤ j.val := by
      rcases hxy with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact absurd (lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)) (not_lt.mpr hij.le)
      · exact ⟨lt_of_le_of_lt h1 h2, h3⟩
    refine ⟨x.val, hxy'.1, hxy'.2, ?_⟩
    have : (⟨x.val, _⟩ : Fin m) = x := rfl
    rw [this, ← hx]
    exact hφs x
  set r := Nat.find hex with hr
  obtain ⟨hir, hrj, hrk⟩ := Nat.find_spec hex
  have hrmin : ∀ t : ℕ, i.val < t → t < r → ∀ ht : t < m,
      ¬ E.link ⟨t, ht⟩ ⊆ C.link ⟨k.val - 1, by omega⟩ := by
    intro t hit htr ht hsub
    exact Nat.find_min hex htr ⟨hit, by omega, hsub⟩
  have hjm := j.isLt
  -- the two index intervals
  set a : Fin m := i
  set b : Fin m := ⟨r - 1, by omega⟩
  set c : Fin m := ⟨min (r + 1) j.val, by omega⟩
  set rr : Fin m := ⟨r, by omega⟩
  have hab : a ≤ b := Fin.le_def.mpr (by simp only [a, b]; omega)
  -- `C_h` and `C_{k-1}`, `C_k` and `C_{h+1}` are disjoint
  have hdis1 : ∀ t : Fin m, (E.link t ∩ C.link h).Nonempty →
      ¬ E.link t ⊆ C.link ⟨k.val - 1, by omega⟩ := by
    intro t ht hsub
    have := (C.adjacent_iff ⟨k.val - 1, by omega⟩ h).mp (ht.mono (inter_subset_inter_left _ hsub))
    simp only at this; omega
  have hdis2 : ∀ t : Fin m, (E.link t ∩ C.link k).Nonempty →
      ¬ E.link t ⊆ C.link ⟨h.val + 1, by omega⟩ := by
    intro t ht hsub
    have := (C.adjacent_iff ⟨h.val + 1, by omega⟩ k).mp (ht.mono (inter_subset_inter_left _ hsub))
    simp only at this; omega
  obtain ⟨x, hxb, hxr⟩ := (E.adjacent_iff b rr).mpr (by simp only [b, rr]; omega)
  obtain ⟨x', hx'r, hx'c⟩ := (E.adjacent_iff rr c).mpr (by simp only [rr, c]; omega)
  obtain ⟨y, hyi, hyh⟩ := hi
  obtain ⟨z, hzj, hzk⟩ := hj
  refine ⟨E.span a b, E.span c j, x, x', y, z,
    Chain.chainedAt_span _ _ _ hbdd hdiam, Chain.chainedAt_span _ _ _ hbdd hdiam,
    Chain.mem_span.mpr ⟨b, hab, le_rfl, hxb⟩, Chain.mem_span.mpr ⟨c, Fin.le_def.mpr
      (by simp only [c]; omega), Fin.le_def.mpr (by simp only [c]; omega), hx'c⟩, ?_,
    ⟨Chain.mem_span.mpr ⟨a, le_rfl, hab, hyi⟩, hyh⟩,
    ⟨Chain.mem_span.mpr ⟨j, Fin.le_def.mpr (by simp only [c]; omega), le_rfl, hzj⟩, hzk⟩,
    ?_, ?_⟩
  · have := dist_le_diam_of_mem (hbdd rr) hxr hx'r
    linarith [hdiam rr]
  · intro u hu
    obtain ⟨t, hat, htb, hut⟩ := Chain.mem_span.mp hu
    refine ⟨E.link t, hut, hbdd t, hdiam t, ?_⟩
    rw [Fin.le_def] at hat htb
    simp only [a, b] at hat htb
    rcases Nat.eq_or_lt_of_le hat with he | hlt
    · have : t = i := Fin.ext he.symm
      rw [this]
      exact hdis1 i ⟨y, hyi, hyh⟩
    · exact hrmin t.val hlt (by omega) t.isLt
  · intro u hu
    obtain ⟨t, hct, htj, hut⟩ := Chain.mem_span.mp hu
    refine ⟨E.link t, hut, hbdd t, hdiam t, ?_⟩
    rw [Fin.le_def] at hct htj
    simp only [c] at hct
    rcases Nat.eq_or_lt_of_le htj with he | hlt
    · have : t = j := Fin.ext he
      rw [this]
      exact hdis2 j ⟨z, hzj, hzk⟩
    · exact hfail rr t (Or.inl ⟨Fin.lt_def.mpr (by simp only [rr]; omega),
        Fin.lt_def.mpr (by simp only [rr]; omega), hlt⟩) hrk

/-- **A failure of crookedness yields `FailData`** at some pair `(h, k)`. -/
theorem failData_of_not_crooked {m n : ℕ} {E : Chain X m} {C : Chain X n} (href : E.Refines C)
    {ε : ℝ} (hbdd : ∀ t, Bornology.IsBounded (E.link t)) (hdiam : ∀ t, diam (E.link t) ≤ ε)
    (hnot : ¬ E.IsCrookedIn' C) :
    ∃ (h k : Fin n) (hhk : h.val + 2 < k.val), FailData C h k hhk ε := by
  simp only [Chain.IsCrookedIn', href, true_and, not_forall, not_exists, not_and] at hnot
  obtain ⟨h, k, hhk, i, j, hi, hj, hfail⟩ := hnot
  refine ⟨h, k, hhk, ?_⟩
  have hφs := Chain.refineIdx_subset href
  rcases lt_trichotomy i j with hij | hij | hij
  · exact failData_of_fail_lt href hbdd hdiam h k hhk i j hij hi hj
      (fun r s hb hr hs => hfail r s hb hr hs)
  · subst hij
    have c1 := (C.adjacent_iff _ h).mp (hi.mono (inter_subset_inter_left _ (hφs i)))
    have c2 := (C.adjacent_iff _ k).mp (hj.mono (inter_subset_inter_left _ (hφs i)))
    omega
  · -- reverse the fine chain
    have hlt : ∀ x y : Fin m, x < y → Fin.rev y < Fin.rev x := by
      intro x y hxy
      have hx := x.isLt
      have hy := y.isLt
      have hxy' : x.val < y.val := hxy
      show (Fin.rev y).val < (Fin.rev x).val
      simp only [Fin.val_rev]
      omega
    refine failData_of_fail_lt (E := E.reverse) href.reverse_left (fun t => hbdd _)
      (fun t => hdiam _) h k hhk (Fin.rev i) (Fin.rev j) (hlt _ _ hij)
      (by rw [Chain.reverse_link, Fin.rev_rev]; exact hi)
      (by rw [Chain.reverse_link, Fin.rev_rev]; exact hj) ?_
    intro r s hb hr hs
    rw [Chain.reverse_link] at hr hs
    refine hfail (Fin.rev r) (Fin.rev s) ?_ hr hs
    rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · refine Or.inr ⟨?_, hlt _ _ h2, ?_⟩
      · have g := hlt _ _ h1; rwa [Fin.rev_rev] at g
      · have g := hlt _ _ h3; rwa [Fin.rev_rev] at g
    · refine Or.inl ⟨?_, hlt _ _ h2, ?_⟩
      · have g := hlt _ _ h1; rwa [Fin.rev_rev] at g
      · have g := hlt _ _ h3; rwa [Fin.rev_rev] at g


/-! ### The limit argument -/

theorem chainedAt_mono {A : Set X} {e e' : ℝ} (h : T13.ChainedAt A e) (hee : e ≤ e') :
    T13.ChainedAt A e' :=
  fun U V hUV hsep => h U V hUV (fun x hx y hy => lt_of_le_of_lt hee (hsep x hx y hy))

/-- Adding a point near a point of a chained set. -/
theorem chainedAt_union_singleton {A : Set X} {e : ℝ} (he : 0 ≤ e) (h : T13.ChainedAt A e)
    {a R : X} (ha : a ∈ A) : T13.ChainedAt (A ∪ {R}) (e + dist a R) := by
  intro U V hUV hsep
  have hA := h U V (subset_union_left.trans hUV) (fun x hx y hy => by
    have := hsep x hx y hy; have := dist_nonneg (x := a) (y := R); linarith)
  have hR := hUV (Or.inr rfl)
  rcases hA with hA | hA
  · rcases hR with hR | hR
    · exact Or.inl (union_subset hA (singleton_subset_iff.mpr hR))
    · exfalso; have := hsep a (hA ha) R hR; linarith
  · rcases hR with hR | hR
    · exfalso; have := hsep R hR a (hA ha); rw [dist_comm] at this; linarith
    · exact Or.inr (union_subset hA (singleton_subset_iff.mpr hR))

/-- Points of the limit superior of `A j ∪ {R}` are approximated by points of the `A j`, when
some points of the `A j` converge to `R`. -/
theorem approx_of_mem_limSup {A : ℕ → Set X} {R : X} {pt : ℕ → X} (hpt : ∀ j, pt j ∈ A j)
    (hlim : Tendsto pt atTop (𝓝 R)) {w : X} (hw : w ∈ T13.limSup univ (fun j => A j ∪ {R}))
    {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) : ∃ j, N ≤ j ∧ ∃ u ∈ A j, dist u w < ρ := by
  obtain ⟨N', hN'⟩ : ∃ N', ∀ j, N' ≤ j → dist (pt j) R < ρ / 2 :=
    eventually_atTop.mp ((tendsto_iff_dist_tendsto_zero.mp hlim).eventually
      (gt_mem_nhds (by linarith)))
  have hw' := T13.limSup_subset_closure (max N N') hw
  obtain ⟨v, hv, hvw⟩ := Metric.mem_closure_iff.mp hw' (ρ / 2) (by linarith)
  obtain ⟨j, -, hv⟩ := mem_iUnion₂.mp hv
  obtain ⟨hj, hv⟩ := mem_iUnion.mp hv
  rcases hv with hv | hv
  · exact ⟨j, le_of_max_le_left hj, v, hv, by rw [dist_comm]; linarith⟩
  · rw [mem_singleton_iff] at hv
    subst hv
    refine ⟨j, le_of_max_le_left hj, pt j, hpt j, ?_⟩
    have := hN' j (le_of_max_le_right hj)
    have := dist_triangle (pt j) v w
    rw [dist_comm w v] at hvw
    linarith

/-- The limit superior misses an open set inside which no small piece of the `A j` lies. -/
theorem limSup_miss {A : ℕ → Set X} {R : X} {pt : ℕ → X} (hpt : ∀ j, pt j ∈ A j)
    (hlim : Tendsto pt atTop (𝓝 R)) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {O : Set X}
    (hO : IsOpen O)
    (hloc : ∀ j, ∀ u ∈ A j, ∃ S : Set X, u ∈ S ∧ Bornology.IsBounded S ∧ diam S ≤ ε j ∧ ¬ S ⊆ O) :
    ∀ w ∈ T13.limSup univ (fun j => A j ∪ {R}), w ∉ O := by
  intro w hw hwO
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hO w hwO
  obtain ⟨N, hN⟩ : ∃ N, ∀ j, N ≤ j → ε j < ρ / 2 :=
    eventually_atTop.mp (hε.eventually (gt_mem_nhds (by linarith)))
  obtain ⟨j, hj, u, hu, huw⟩ := approx_of_mem_limSup hpt hlim hw (half_pos hρ) N
  obtain ⟨S, huS, hSb, hSd, hSO⟩ := hloc j u hu
  apply hSO
  intro s hs
  apply hball
  rw [mem_ball]
  have := dist_le_diam_of_mem hSb hs huS
  have := hN j hj
  linarith [dist_triangle s u w]

/-- A cluster point of points `y j ∈ A j ∩ O` lies in the limit superior, and every open set
containing it meets `O`. -/
theorem exists_limSup_near [CompactSpace X] {A : ℕ → Set X} (R : X) {y : ℕ → X}
    (hy : ∀ j, y j ∈ A j) {O : Set X} (hyO : ∀ j, y j ∈ O) :
    ∃ Y ∈ T13.limSup univ (fun j => A j ∪ {R}), ∀ U, IsOpen U → Y ∈ U → (U ∩ O).Nonempty := by
  obtain ⟨Y, ψ, hψ, hlim⟩ := CompactSpace.tendsto_subseq y
  refine ⟨Y, ?_, fun U hU hYU => ?_⟩
  · simp only [T13.limSup, mem_iInter]
    intro N
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop N] with i hi
    have hψi : N ≤ ψ i := le_trans hi (hψ.id_le i)
    exact mem_iUnion₂.mpr ⟨ψ i, mem_univ _, mem_iUnion.mpr ⟨hψi, Or.inl (hy (ψ i))⟩⟩
  · obtain ⟨i, hi⟩ := (hlim.eventually (hU.mem_nhds hYU)).exists
    exact ⟨y (ψ i), hi, hyO _⟩

/-- **The limit argument.** Sequences of `FailData` at a fixed pair `(h, k)` with the constant
tending to zero contradict hereditary indecomposability. -/
theorem limit_false [CompactSpace X]
    (hHI : ∀ K : Set X, Fold.Q78.IsContinuum K → Fold.Q78.IsIndecomposable K)
    {n : ℕ} (C : Chain X n) (hcov : ∀ x : X, ∃ l, x ∈ C.link l) (h k : Fin n)
    (hhk : h.val + 2 < k.val) (ε : ℕ → ℝ) (hε0 : ∀ j, 0 ≤ ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hdata : ∀ j, FailData C h k hhk (ε j)) : False := by
  choose W V x x' y z hWc hVc hx hx' hxx hy hz hWl hVl using hdata
  obtain ⟨R, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq x
  have hεφ : Tendsto (ε ∘ φ) atTop (𝓝 0) := hε.comp hφ.tendsto_atTop
  have hdx : Tendsto (fun j => dist (x (φ j)) R) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hlim
  have hlim' : Tendsto (x' ∘ φ) atTop (𝓝 R) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hsum : Tendsto (fun j => ε (φ j) + dist (x (φ j)) R) atTop (𝓝 0) := by
      simpa using hεφ.add hdx
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hsum
    have h0 := hxx (φ j)
    have h1 := dist_triangle (x' (φ j)) (x (φ j)) R
    have h2 := dist_comm (x (φ j)) (x' (φ j))
    simp only [Function.comp]
    linarith
  set δ : ℕ → ℝ := fun j => 2 * ε (φ j) + dist (x (φ j)) R with hδ
  have hδt : Tendsto δ atTop (𝓝 0) := by
    simpa [hδ] using (hεφ.const_mul 2).add hdx
  set A : ℕ → Set X := fun j => W (φ j) ∪ {R}
  set B : ℕ → Set X := fun j => V (φ j) ∪ {R}
  have hAch : ∀ j ∈ (univ : Set ℕ), T13.ChainedAt (A j) (δ j) := by
    intro j _
    refine chainedAt_mono (chainedAt_union_singleton (hε0 _) (hWc (φ j)) (hx (φ j))) ?_
    linarith [hε0 (φ j)]
  have hBch : ∀ j ∈ (univ : Set ℕ), T13.ChainedAt (B j) (δ j) := by
    intro j _
    refine chainedAt_mono (chainedAt_union_singleton (hε0 _) (hVc (φ j)) (hx' (φ j))) ?_
    have := hxx (φ j)
    have := dist_triangle (x' (φ j)) (x (φ j)) R
    rw [dist_comm (x' (φ j)) (x (φ j))] at this
    linarith
  set WL := T13.limSup univ A
  set VL := T13.limSup univ B
  have hRA : ∀ j ∈ (univ : Set ℕ), R ∈ A j := fun j _ => Or.inr rfl
  have hRB : ∀ j ∈ (univ : Set ℕ), R ∈ B j := fun j _ => Or.inr rfl
  have hWLc : IsPreconnected WL := T13.isPreconnected_limSup hδt hAch hRA infinite_univ
  have hVLc : IsPreconnected VL := T13.isPreconnected_limSup hδt hBch hRB infinite_univ
  have hRW : R ∈ WL := T13.mem_limSup infinite_univ hRA
  have hRV : R ∈ VL := T13.mem_limSup infinite_univ hRB
  -- `W` misses `C_{k-1}`, `V` misses `C_{h+1}`
  have hWmiss : ∀ w ∈ WL, w ∉ C.link ⟨k.val - 1, by omega⟩ :=
    limSup_miss (A := fun j => W (φ j)) (fun j => hx (φ j)) hlim hεφ (C.isOpen _)
      (fun j => hWl (φ j))
  have hVmiss : ∀ w ∈ VL, w ∉ C.link ⟨h.val + 1, by omega⟩ :=
    limSup_miss (A := fun j => V (φ j)) (fun j => hx' (φ j)) hlim' hεφ (C.isOpen _)
      (fun j => hVl (φ j))
  -- a point of `W` near `C_h`, a point of `V` near `C_k`
  obtain ⟨Y, hYW, hYnear⟩ := exists_limSup_near (A := fun j => W (φ j)) R
    (fun j => (hy (φ j)).1) (fun j => (hy (φ j)).2)
  obtain ⟨Z, hZV, hZnear⟩ := exists_limSup_near (A := fun j => V (φ j)) R
    (fun j => (hz (φ j)).1) (fun j => (hz (φ j)).2)
  obtain ⟨l₁, hl₁⟩ := hcov Y
  obtain ⟨l₂, hl₂⟩ := hcov Z
  have hl₁h : l₁.val ≤ h.val + 1 := by
    have := (C.adjacent_iff l₁ h).mp (hYnear _ (C.isOpen l₁) hl₁); omega
  have hl₂k : k.val ≤ l₂.val + 1 := by
    have := (C.adjacent_iff l₂ k).mp (hZnear _ (C.isOpen l₂) hl₂); omega
  set c₁ : Fin n := ⟨h.val + 1, by omega⟩
  set c₂ : Fin n := ⟨k.val - 1, by omega⟩
  -- `W` meets `C_{h+1}`
  have hWmeet : ∃ w ∈ WL, w ∈ C.link c₁ := by
    by_contra hcon
    push_neg at hcon
    have hl₁' : l₁.val < c₁.val := by
      rcases Nat.lt_or_ge l₁.val c₁.val with hlt | hge
      · exact hlt
      · have hc : c₁.val = h.val + 1 := rfl
        have he : l₁ = c₁ := Fin.ext (by omega)
        exact absurd (he ▸ hl₁) (hcon Y hYW)
    have hW1 := (subset_side_of_miss C hcov hWLc c₁ hcon hYW hl₁).1 hl₁'
    have hV1 := (subset_side_of_miss C hcov hVLc c₁ hVmiss hZV hl₂).2
      (show h.val + 1 < l₂.val by omega)
    exact Set.disjoint_left.mp (disjoint_lowU_highU C (a := c₁.val) (b := c₁.val)
      le_rfl) (hW1 hRW) (hV1 hRV)
  -- `V` meets `C_{k-1}`
  have hVmeet : ∃ w ∈ VL, w ∈ C.link c₂ := by
    by_contra hcon
    push_neg at hcon
    have hl₂' : c₂.val < l₂.val := by
      rcases Nat.lt_or_ge c₂.val l₂.val with hlt | hge
      · exact hlt
      · have hc : c₂.val = k.val - 1 := rfl
        have he : l₂ = c₂ := Fin.ext (by omega)
        exact absurd (he ▸ hl₂) (hcon Z hZV)
    have hV2 := (subset_side_of_miss C hcov hVLc c₂ hcon hZV hl₂).2 hl₂'
    have hW2 := (subset_side_of_miss C hcov hWLc c₂ hWmiss hYW hl₁).1
      (show l₁.val < k.val - 1 by omega)
    exact Set.disjoint_left.mp (disjoint_lowU_highU C (a := c₂.val) (b := c₂.val)
      le_rfl) (hW2 hRW) (hV2 hRV)
  -- the decomposable continuum `W ∪ V`
  have hWcont : Fold.Q78.IsContinuum WL :=
    ⟨(T13.isClosed_limSup _ _).isCompact, ⟨R, hRW⟩, hWLc⟩
  have hVcont : Fold.Q78.IsContinuum VL :=
    ⟨(T13.isClosed_limSup _ _).isCompact, ⟨R, hRV⟩, hVLc⟩
  have hU : Fold.Q78.IsContinuum (WL ∪ VL) :=
    ⟨hWcont.1.union hVcont.1, IsConnected.union ⟨R, hRW, hRV⟩ hWcont.2 hVcont.2⟩
  rcases (hHI _ hU).2 WL VL hWcont hVcont subset_union_left subset_union_right rfl with he | he
  · obtain ⟨w, hwV, hwc⟩ := hVmeet
    have : w ∈ WL := he ▸ Or.inr hwV
    exact hWmiss w this hwc
  · obtain ⟨w, hwW, hwc⟩ := hWmeet
    have : w ∈ VL := he ▸ Or.inl hwW
    exact hVmiss w this hwc

/-- **Crookedness eventually** (Bing 1951, proof of Theorem 1, first paragraph). In a compact
hereditarily indecomposable metric space, chains refining a chain `C` that covers the space, with
mesh tending to zero, are eventually crooked (1948 sense) in `C`. -/
theorem eventually_crookedIn [CompactSpace X]
    (hHI : ∀ K : Set X, Fold.Q78.IsContinuum K → Fold.Q78.IsIndecomposable K)
    {n : ℕ} (C : Chain X n) (hcov : ∀ x : X, ∃ l, x ∈ C.link l) {N : ℕ → ℕ}
    (E : ∀ m, Chain X (N m)) (href : ∀ m, (E m).Refines C) (ε : ℕ → ℝ) (hε0 : ∀ m, 0 ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (hbdd : ∀ m t, Bornology.IsBounded ((E m).link t))
    (hdiam : ∀ m t, diam ((E m).link t) ≤ ε m) :
    ∀ᶠ m in atTop, (E m).IsCrookedIn' C := by
  classical
  by_contra hne
  have hfreq : ∃ᶠ m in atTop, ¬ (E m).IsCrookedIn' C := by
    rwa [Filter.not_eventually] at hne
  set J : Fin n × Fin n → Set ℕ := fun p => {m | ∃ hhk : p.1.val + 2 < p.2.val,
    FailData C p.1 p.2 hhk (ε m)}
  have hsub : {m | ¬ (E m).IsCrookedIn' C} ⊆ ⋃ p, J p := by
    intro m hm
    obtain ⟨h, k, hhk, hd⟩ := failData_of_not_crooked (href m) (hbdd m) (hdiam m) hm
    exact mem_iUnion.mpr ⟨(h, k), hhk, hd⟩
  have hinf : {m | ¬ (E m).IsCrookedIn' C}.Infinite := by
    rw [Set.infinite_iff_exists_gt]
    intro a
    obtain ⟨m, hm, hma⟩ := (Filter.frequently_atTop.mp hfreq) (a + 1)
    exact ⟨m, hma, by omega⟩
  obtain ⟨p, hp⟩ : ∃ p, (J p).Infinite := by
    by_contra hall
    push_neg at hall
    exact hinf ((Set.finite_iUnion hall).subset hsub)
  set μ := Nat.nth (· ∈ J p)
  have hμ : StrictMono μ := Nat.nth_strictMono hp
  have hμmem : ∀ j, μ j ∈ J p := Nat.nth_mem_of_infinite hp
  obtain ⟨hhk, -⟩ := hμmem 0
  refine limit_false hHI C hcov p.1 p.2 hhk (ε ∘ μ) (fun j => hε0 _)
    (hε.comp hμ.tendsto_atTop) (fun j => ?_)
  exact (hμmem j).2

end PA51

end HPC.Plane
