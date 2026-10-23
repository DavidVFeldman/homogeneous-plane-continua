import HPC.PseudoArc.Theorem5
import HPC.PseudoArc.T13Topo

/-!
# Batch 81: chains between two points, and reaching both end links

* `Chain.span D a b`: the union of the links of `D` with index in `[a, b]`; it is `ε`-chained
  when every link has diameter at most `ε` (`Chain.chainedAt_span`).
* `Description.isConnected_M`: the described continuum is connected (the repository did not have
  this; it is the limit of the chained sets `(D i)^*`).
* `Chain.exists_isSubchainFrom`: two points in the union of a chain, lying in no common link, are
  joined by a subchain.
* `Description.exists_subchain_meets_ends'`: Bing's first paragraph of the proof of Theorem 13.
-/

namespace HPC

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

namespace Chain

variable {n : ℕ}

/-- The union of the links of `D` with index in `[a, b]`. -/
def span (D : Chain X n) (a b : Fin n) : Set X := ⋃ (t : Fin n) (_ : a ≤ t ∧ t ≤ b), D.link t

theorem mem_span {D : Chain X n} {a b : Fin n} {x : X} :
    x ∈ D.span a b ↔ ∃ t : Fin n, a ≤ t ∧ t ≤ b ∧ x ∈ D.link t := by
  simp only [span, mem_iUnion, exists_prop, and_assoc]

theorem span_subset_union (D : Chain X n) (a b : Fin n) : D.span a b ⊆ D.union := by
  intro x hx
  obtain ⟨t, -, -, hx⟩ := mem_span.mp hx
  exact mem_iUnion.mpr ⟨t, hx⟩

theorem union_eq_span (D : Chain X n) (hn : 0 < n) :
    D.union = D.span ⟨0, hn⟩ ⟨n - 1, by omega⟩ := by
  ext x
  simp only [union, mem_iUnion, mem_span]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, Fin.le_def.mpr (Nat.zero_le _), Fin.le_def.mpr (by simp only; omega), ht⟩
  · rintro ⟨t, -, -, ht⟩
    exact ⟨t, ht⟩

/-- A span of a chain whose links have diameter at most `ε` is `ε`-chained. -/
theorem chainedAt_span (D : Chain X n) (a b : Fin n) {ε : ℝ}
    (hbdd : ∀ t, Bornology.IsBounded (D.link t)) (hdiam : ∀ t, diam (D.link t) ≤ ε) :
    T13.ChainedAt (D.span a b) ε := by
  intro U V hUV hsep
  have hε : 0 ≤ ε := le_trans diam_nonneg (hdiam a)
  -- each link of the span lies on one side
  have side : ∀ t : Fin n, a ≤ t → t ≤ b → D.link t ⊆ U ∨ D.link t ⊆ V := by
    intro t hat htb
    by_cases h : D.link t ⊆ U
    · exact Or.inl h
    · right
      obtain ⟨x, hxt, hxU⟩ := not_subset.mp h
      have hxV : x ∈ V := by
        rcases hUV (mem_span.mpr ⟨t, hat, htb, hxt⟩) with h' | h'
        · exact absurd h' hxU
        · exact h'
      intro y hyt
      rcases hUV (mem_span.mpr ⟨t, hat, htb, hyt⟩) with h' | h'
      · have h1 := hsep y h' x hxV
        have h2 := dist_le_diam_of_mem (hbdd t) hyt hxt
        linarith [hdiam t]
      · exact h'
  have hUV0 : ∀ z, z ∈ U → z ∉ V := fun z hzU hzV => by
    have := hsep z hzU z hzV
    simp at this
    linarith
  -- propagate the side of the first link along the span
  have prop : ∀ W W' : Set X, (∀ z, z ∈ W → z ∉ W') →
      (∀ t : Fin n, a ≤ t → t ≤ b → D.link t ⊆ W ∨ D.link t ⊆ W') →
      D.link a ⊆ W → ∀ t : Fin n, a ≤ t → t ≤ b → D.link t ⊆ W := by
    intro W W' hWW' hside ha
    have key : ∀ m : ℕ, ∀ ht : a.val + m < n, a.val + m ≤ b.val →
        D.link ⟨a.val + m, ht⟩ ⊆ W := by
      intro m
      induction m with
      | zero => intro ht _; simpa using ha
      | succ m ih =>
        intro ht hmb
        have ih' := ih (by omega) (by omega)
        rcases hside ⟨a.val + (m + 1), ht⟩ (Fin.le_def.mpr (by simp)) (Fin.le_def.mpr hmb)
          with h | h
        · exact h
        · exfalso
          obtain ⟨z, hz1, hz2⟩ := (D.adjacent_iff ⟨a.val + m, by omega⟩ ⟨a.val + (m + 1), ht⟩).mpr
            (by simp only; omega)
          exact hWW' z (ih' hz1) (h hz2)
    intro t hat htb
    have := key (t.val - a.val) (by omega) (by rw [Fin.le_def] at hat htb; omega)
    have heq : (⟨a.val + (t.val - a.val), by omega⟩ : Fin n) = t := by
      ext; simp only; rw [Fin.le_def] at hat; omega
    rwa [heq] at this
  by_cases hab : a ≤ b
  · rcases side a le_rfl hab with h | h
    · left
      intro x hx
      obtain ⟨t, hat, htb, hxt⟩ := mem_span.mp hx
      exact prop U V hUV0 side h t hat htb hxt
    · right
      intro x hx
      obtain ⟨t, hat, htb, hxt⟩ := mem_span.mp hx
      exact prop V U (fun z hzV hzU => hUV0 z hzU hzV)
        (fun t h1 h2 => (side t h1 h2).symm) h t hat htb hxt
  · left
    intro x hx
    obtain ⟨t, hat, htb, -⟩ := mem_span.mp hx
    exact absurd (le_trans hat htb) hab

/-- Two links containing the same point are adjacent. -/
theorem val_close_of_mem (D : Chain X n) {x : X} {s t : Fin n} (hs : x ∈ D.link s)
    (ht : x ∈ D.link t) : s.val ≤ t.val + 1 ∧ t.val ≤ s.val + 1 :=
  (D.adjacent_iff s t).mp ⟨x, hs, ht⟩

/-- Two points of the union of a chain lying in no common link are joined by a subchain. -/
theorem exists_isSubchainFrom (D : Chain X n) {R S : X} (hR : R ∈ D.union) (hS : S ∈ D.union)
    (hRS : ∀ t, R ∈ D.link t → S ∉ D.link t) : ∃ a b : Fin n, D.IsSubchainFrom a b R S := by
  classical
  obtain ⟨r0, hr0⟩ := mem_iUnion.mp hR
  obtain ⟨s0, hs0⟩ := mem_iUnion.mp hS
  set IR := Finset.univ.filter (fun t => R ∈ D.link t)
  set IS := Finset.univ.filter (fun t => S ∈ D.link t)
  have hIR : IR.Nonempty := ⟨r0, by simp [IR, hr0]⟩
  have hIS : IS.Nonempty := ⟨s0, by simp [IS, hs0]⟩
  have memR : ∀ t, t ∈ IR ↔ R ∈ D.link t := fun t => by simp [IR]
  have memS : ∀ t, t ∈ IS ↔ S ∈ D.link t := fun t => by simp [IS]
  -- the two index sets are separated
  have hsep : (∀ r ∈ IR, ∀ s ∈ IS, r < s) ∨ (∀ r ∈ IR, ∀ s ∈ IS, s < r) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨r1, hr1, s1, hs1, h1⟩, ⟨r2, hr2, s2, hs2, h2⟩⟩ := hcon
    rw [memR] at hr1 hr2
    rw [memS] at hs1 hs2
    have c1 := D.val_close_of_mem hr1 hr2
    have c2 := D.val_close_of_mem hs1 hs2
    have n11 : r1 ≠ s1 := fun h => hRS r1 hr1 (h ▸ hs1)
    have n12 : r1 ≠ s2 := fun h => hRS r1 hr1 (h ▸ hs2)
    have n21 : r2 ≠ s1 := fun h => hRS r2 hr2 (h ▸ hs1)
    have n22 : r2 ≠ s2 := fun h => hRS r2 hr2 (h ▸ hs2)
    rw [Fin.le_def] at h1 h2
    rw [Ne, Fin.ext_iff] at n11 n12 n21 n22
    omega
  rcases hsep with h | h
  · set a := IR.max' hIR
    set b := IS.min' hIS
    have ha : R ∈ D.link a := (memR a).mp (IR.max'_mem hIR)
    have hb : S ∈ D.link b := (memS b).mp (IS.min'_mem hIS)
    have hab : a < b := h a (IR.max'_mem hIR) b (IS.min'_mem hIS)
    refine ⟨a, b, hab.le, Or.inl ⟨by omega, ?_, ?_, ?_, ?_⟩⟩
    · simpa [sub] using ha
    · have : (⟨a.val + (b.val - a.val + 1 - 1), by omega⟩ : Fin n) = b := by
        ext; simp only; rw [Fin.lt_def] at hab; omega
      simp only [sub]; rw [this]; exact hb
    · intro i hi
      simp only [sub] at hi
      have := IR.le_max' _ ((memR _).mpr hi)
      rw [Fin.le_def] at this
      ext; simp only at this ⊢; omega
    · intro i hi
      simp only [sub] at hi
      have := IS.min'_le _ ((memS _).mpr hi)
      rw [Fin.le_def] at this
      ext; simp only at this ⊢; have := i.isLt; omega
  · set a := IS.max' hIS
    set b := IR.min' hIR
    have ha : S ∈ D.link a := (memS a).mp (IS.max'_mem hIS)
    have hb : R ∈ D.link b := (memR b).mp (IR.min'_mem hIR)
    have hab : a < b := h b (IR.min'_mem hIR) a (IS.max'_mem hIS)
    refine ⟨a, b, hab.le, Or.inr ⟨by omega, ?_, ?_, ?_, ?_⟩⟩
    · simpa [sub] using ha
    · have : (⟨a.val + (b.val - a.val + 1 - 1), by omega⟩ : Fin n) = b := by
        ext; simp only; rw [Fin.lt_def] at hab; omega
      simp only [sub]; rw [this]; exact hb
    · intro i hi
      simp only [sub] at hi
      have := IS.le_max' _ ((memS _).mpr hi)
      rw [Fin.le_def] at this
      ext; simp only at this ⊢; omega
    · intro i hi
      simp only [sub] at hi
      have := IR.min'_le _ ((memR _).mpr hi)
      rw [Fin.le_def] at this
      ext; simp only at this ⊢; have := i.isLt; omega

/-- The span of a subchain from `R` to `S` contains `R` and `S`. -/
theorem IsSubchainFrom.mem_span {D : Chain X n} {a b : Fin n} {R S : X}
    (h : D.IsSubchainFrom a b R S) : R ∈ D.span a b ∧ S ∈ D.span a b := by
  obtain ⟨hab, h | h⟩ := h
  · obtain ⟨hn, hR, hS, -, -⟩ := h
    refine ⟨HPC.Chain.mem_span.mpr ⟨_, le_rfl, hab, hR⟩, HPC.Chain.mem_span.mpr ⟨⟨a.val + (b.val - a.val + 1 - 1),
      by omega⟩, Fin.le_def.mpr (by simp), Fin.le_def.mpr (by simp only; omega), hS⟩⟩
  · obtain ⟨hn, hS, hR, -, -⟩ := h
    refine ⟨HPC.Chain.mem_span.mpr ⟨⟨a.val + (b.val - a.val + 1 - 1),
      by omega⟩, Fin.le_def.mpr (by simp), Fin.le_def.mpr (by simp only; omega), hR⟩,
      HPC.Chain.mem_span.mpr ⟨_, le_rfl, hab, hS⟩⟩

end Chain

namespace Description

variable {P Q : X} (Δ : Description X P Q)

theorem M_eq_iInter_closure : Δ.M = ⋂ i, closure (Δ.D i).union := by
  refine Subset.antisymm ?_ ?_
  · intro z hz
    simp only [M, mem_iInter] at hz ⊢
    exact fun i => subset_closure (hz i)
  · intro z hz
    simp only [M, mem_iInter] at hz ⊢
    exact fun i => Δ.closure_union_subset (Nat.lt_succ_self i) (hz (i + 1))

theorem chainedAt_union (i : ℕ) : T13.ChainedAt (Δ.D i).union (Δ.ε i) := by
  rw [(Δ.D i).union_eq_span (Δ.isFrom i).1]
  exact Chain.chainedAt_span _ _ _ (Δ.bdd i) (Δ.diam_le i)

theorem P_mem_union (i : ℕ) : P ∈ (Δ.D i).union := by
  obtain ⟨hn, hP, -⟩ := Δ.isFrom i
  exact mem_iUnion.mpr ⟨_, hP⟩

/-- **The described continuum is connected.** -/
theorem isConnected_M [CompactSpace X] : IsConnected Δ.M := by
  refine ⟨⟨P, Δ.P_mem_M⟩, ?_⟩
  have heq : Δ.M = T13.limSup univ (fun i => (Δ.D i).union) := by
    rw [M_eq_iInter_closure]
    simp only [T13.limSup]
    congr 1
    ext N : 1
    congr 1
    ext z
    simp only [mem_univ, mem_iUnion, exists_prop, true_and]
    constructor
    · intro hz; exact ⟨N, le_rfl, hz⟩
    · rintro ⟨k, hk, hz⟩
      exact Chain.union_subset_of_refines (Δ.refines_of_le hk) hz
  rw [heq]
  exact T13.isPreconnected_limSup Δ.ε_tendsto (fun i _ => Δ.chainedAt_union i)
    (fun i _ => Δ.P_mem_union i) infinite_univ

theorem isContinuum_M [CompactSpace X] : Fold.Q78.IsContinuum Δ.M :=
  ⟨Δ.isCompact_M, Δ.isConnected_M⟩

/-- **The limit step of Bing's first paragraph.** Chained sets through `R` and `S` inside the
levels, all missing a fixed open set that meets `M`, would give a proper subcontinuum of `M`
containing `R` and `S`. -/
theorem false_of_disjoint_limit [CompactSpace X] {R S : X}
    (hcomp : S ∉ composant Δ.M R) {I : Set ℕ} (hI : I.Infinite) (A : ℕ → Set X)
    (hch : ∀ k ∈ I, T13.ChainedAt (A k) (Δ.ε k)) (hRA : ∀ k ∈ I, R ∈ A k)
    (hSA : ∀ k ∈ I, S ∈ A k) (hAD : ∀ k ∈ I, A k ⊆ (Δ.D k).union) {O : Set X} (hO : IsOpen O)
    (hOM : (O ∩ Δ.M).Nonempty) (hdisj : ∀ k ∈ I, Disjoint (A k) O) : False := by
  set Z := T13.limSup I A
  have hZc : IsClosed Z := T13.isClosed_limSup I A
  have hZpc : IsPreconnected Z := T13.isPreconnected_limSup Δ.ε_tendsto hch hRA hI
  have hRZ : R ∈ Z := T13.mem_limSup hI hRA
  have hSZ : S ∈ Z := T13.mem_limSup hI hSA
  have hZM : Z ⊆ Δ.M := by
    intro z hz
    simp only [M, mem_iInter]
    intro i
    refine Δ.closure_union_subset (Nat.lt_succ_self i) ?_
    refine closure_mono ?_ (T13.limSup_subset_closure (i + 1) hz)
    intro y hy
    simp only [mem_iUnion] at hy
    obtain ⟨k, hk, hik, hy⟩ := hy
    exact Chain.union_subset_of_refines (Δ.refines_of_le hik) (hAD k hk hy)
  have hZne : Z ≠ Δ.M := by
    obtain ⟨w, hwO, hwM⟩ := hOM
    intro heq
    have hwZ : w ∈ Z := heq ▸ hwM
    have := T13.limSup_subset_closure 0 hwZ
    obtain ⟨y, hyO, hy⟩ := mem_closure_iff.mp this O hO hwO
    simp only [mem_iUnion] at hy
    obtain ⟨k, hk, -, hy⟩ := hy
    exact (hdisj k hk).le_bot ⟨hy, hyO⟩
  apply hcomp
  exact mem_sUnion.mpr ⟨Z, ⟨⟨hZc.isCompact, ⟨R, hRZ⟩, hZpc⟩, hZM, hZne, hRZ⟩, hSZ⟩

/-- A point of a nontrivial `M` lies in its own composant (`{R}` is a proper subcontinuum). -/
theorem mem_composant_self {R : X} (hR : R ∈ Δ.M) (hPQ : P ≠ Q) : R ∈ composant Δ.M R := by
  refine mem_sUnion.mpr ⟨{R}, ⟨⟨isCompact_singleton, isConnected_singleton⟩,
    singleton_subset_iff.mpr hR, ?_, rfl⟩, rfl⟩
  intro h
  have hP : P ∈ ({R} : Set X) := h ▸ Δ.P_mem_M
  have hQ : Q ∈ ({R} : Set X) := h ▸ Δ.Q_mem_M
  exact hPQ ((mem_singleton_iff.mp hP).trans (mem_singleton_iff.mp hQ).symm)

theorem ne_of_not_mem_composant {R S : X} (hR : R ∈ Δ.M) (hPQ : P ≠ Q)
    (hcomp : S ∉ composant Δ.M R) : R ≠ S := by
  rintro rfl
  exact hcomp (Δ.mem_composant_self hR hPQ)

/-- For every level deep enough (mesh below `dist R S`) there is a subchain from `R` to `S`. -/
theorem exists_isSubchainFrom_of_lt {R S : X} (hR : R ∈ Δ.M) (hS : S ∈ Δ.M) {k : ℕ}
    (hk : Δ.ε k < dist R S) : ∃ a b : Fin (Δ.n k), (Δ.D k).IsSubchainFrom a b R S := by
  refine (Δ.D k).exists_isSubchainFrom (Δ.M_subset_union k hR) (Δ.M_subset_union k hS) ?_
  intro t hRt hSt
  have := dist_le_diam_of_mem (Δ.bdd k t) hRt hSt
  linarith [Δ.diam_le k t]

/-- **Reaching both ends** (Bing p. 740, first paragraph), with the placeholder index bounds of
the skeleton discharged. -/
theorem exists_subchain_meets_ends' [CompactSpace X] (hPQ : P ≠ Q)
    {R S : X} (hR : R ∈ Δ.M) (hS : S ∈ Δ.M) (hcomp : S ∉ composant Δ.M R) (j : ℕ) :
    ∃ k, j < k ∧ ∃ a b : Fin (Δ.n k), (Δ.D k).IsSubchainFrom a b R S ∧
      (∃ t : Fin (Δ.n k), a ≤ t ∧ t ≤ b ∧
        ((Δ.D k).link t ∩ (Δ.D j).link ⟨0, (Δ.isFrom j).1⟩).Nonempty) ∧
      (∃ t : Fin (Δ.n k), a ≤ t ∧ t ≤ b ∧
        ((Δ.D k).link t ∩ (Δ.D j).link ⟨Δ.n j - 1, by have := (Δ.isFrom j).1; omega⟩).Nonempty) := by
  classical
  have hRS : 0 < dist R S := dist_pos.mpr (Δ.ne_of_not_mem_composant hR hPQ hcomp)
  obtain ⟨k0, hk0⟩ : ∃ k0, ∀ k, k0 ≤ k → Δ.ε k < dist R S :=
    eventually_atTop.mp (Δ.ε_tendsto.eventually (gt_mem_nhds hRS))
  by_contra hcon
  -- the chosen subchains
  have hex : ∀ k, max k0 (j + 1) ≤ k → ∃ ab : Fin (Δ.n k) × Fin (Δ.n k),
      (Δ.D k).IsSubchainFrom ab.1 ab.2 R S := fun k hk => by
    obtain ⟨a, b, h⟩ := Δ.exists_isSubchainFrom_of_lt hR hS (hk0 k (le_of_max_le_left hk))
    exact ⟨(a, b), h⟩
  let A : ℕ → Set X := fun k =>
    if h : max k0 (j + 1) ≤ k then (Δ.D k).span (hex k h).choose.1 (hex k h).choose.2 else ∅
  have hAspec : ∀ k (h : max k0 (j + 1) ≤ k), A k = (Δ.D k).span (hex k h).choose.1
      (hex k h).choose.2 := fun k h => by simp only [A, dif_pos h]
  set O₁ := (Δ.D j).link ⟨0, (Δ.isFrom j).1⟩
  set O₂ := (Δ.D j).link ⟨Δ.n j - 1, by have := (Δ.isFrom j).1; omega⟩
  let I₁ := {k | max k0 (j + 1) ≤ k ∧ Disjoint (A k) O₁}
  let I₂ := {k | max k0 (j + 1) ≤ k ∧ Disjoint (A k) O₂}
  have hcov : Ici (max k0 (j + 1)) ⊆ I₁ ∪ I₂ := by
    intro k hk
    have hk' : max k0 (j + 1) ≤ k := hk
    by_contra hk2
    simp only [mem_union, mem_setOf_eq, not_or, not_and, I₁, I₂] at hk2
    have d1 := hk2.1 hk'
    have d2 := hk2.2 hk'
    rw [hAspec k hk', not_disjoint_iff] at d1 d2
    obtain ⟨x, hx, hx1⟩ := d1
    obtain ⟨y, hy, hy2⟩ := d2
    obtain ⟨t, ht1, ht2, hxt⟩ := Chain.mem_span.mp hx
    obtain ⟨u, hu1, hu2, hyu⟩ := Chain.mem_span.mp hy
    exact hcon ⟨k, by omega, _, _, (hex k hk').choose_spec, ⟨t, ht1, ht2, x, hxt, hx1⟩,
      ⟨u, hu1, hu2, y, hyu, hy2⟩⟩
  have main : ∀ I : Set ℕ, I ⊆ Ici (max k0 (j + 1)) → I.Infinite → ∀ O : Set X, IsOpen O →
      (O ∩ Δ.M).Nonempty → (∀ k ∈ I, Disjoint (A k) O) → False := by
    intro I hI hinf O hO hOM hdisj
    refine Δ.false_of_disjoint_limit hcomp hinf A (fun k hk => ?_) (fun k hk => ?_)
      (fun k hk => ?_) (fun k hk => ?_) hO hOM hdisj
    · rw [hAspec k (hI hk)]
      exact Chain.chainedAt_span _ _ _ (Δ.bdd k) (Δ.diam_le k)
    · rw [hAspec k (hI hk)]
      exact ((hex k (hI hk)).choose_spec.mem_span).1
    · rw [hAspec k (hI hk)]
      exact ((hex k (hI hk)).choose_spec.mem_span).2
    · rw [hAspec k (hI hk)]
      exact Chain.span_subset_union _ _ _
  rcases infinite_union.mp ((Ici_infinite _).mono hcov) with h | h
  · exact main I₁ (fun k hk => hk.1) h O₁ ((Δ.D j).isOpen _) (Δ.link_inter_M_nonempty j _)
      (fun k hk => hk.2)
  · exact main I₂ (fun k hk => hk.1) h O₂ ((Δ.D j).isOpen _) (Δ.link_inter_M_nonempty j _)
      (fun k hk => hk.2)

end Description

end HPC
