import HPC.Plane.Theorem11Nec

/-!
# Batch 96, §2–3: chain constructions for the sufficiency half of Theorem 11

* `EpsCoverable` (moved here from the skeleton so that the general lemmas can use it).
* Chain constructions: `chainSingle` (one link), `chainRestrict` (intersect every link with an
  open set), `chainAppend` (concatenate two chains that meet only at the junction).
* `consec_meet`: in a chain all of whose links meet a preconnected set `C` it covers, consecutive
  links meet *inside* `C` (the fact needed for item 7 of the commission).
* `trim_first`: a chain covering a preconnected `C` with `p` in the first link only (and in no
  other link's closure) can be cut down to the links meeting `C`, keeping these properties.
* `epsCoverable_amalgam_gen`: Bing's amalgamation, for `Z ⊆ H ∪ K` with `H ∩ K = {p}`.
* `exists_minimal_notCoverable'`: the minimal non-coverable subcontinuum.
-/

namespace HPC.Plane

open Set Topology Metric

section Constructions

variable {X : Type*} [MetricSpace X]

/-- `M` is covered by some `ε`-chain. -/
def EpsCoverable (M : Set X) (ε : ℝ) : Prop :=
  ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ M ⊆ D.union

theorem natAbs_le_one_iff {n : ℕ} (i j : Fin n) :
    ((i : ℤ) - (j : ℤ)).natAbs ≤ 1 ↔ (i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1) := by
  omega

/-- A chain with one link. -/
def chainSingle (U : Set X) (hU : IsOpen U) (hne : U.Nonempty) : Chain X 1 where
  link _ := U
  isOpen _ := hU
  adjacent i j := by
    rw [natAbs_le_one_iff, inter_self]
    have hi := i.isLt
    have hj := j.isLt
    simp only [hne, true_iff]
    omega

/-- Intersect every link of a chain with an open set; a chain provided consecutive links still
meet (and every link stays nonempty). -/
def chainRestrict {n : ℕ} (D : Chain X n) (O : Set X) (hO : IsOpen O)
    (hcons : ∀ i j : Fin n, i.val ≤ j.val + 1 → j.val ≤ i.val + 1 →
      (D.link i ∩ D.link j ∩ O).Nonempty) : Chain X n where
  link i := D.link i ∩ O
  isOpen i := (D.isOpen i).inter hO
  adjacent i j := by
    rw [natAbs_le_one_iff]
    constructor
    · rintro ⟨x, ⟨hxi, -⟩, ⟨hxj, -⟩⟩
      exact (D.adjacent_iff i j).mp ⟨x, hxi, hxj⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨x, ⟨hxi, hxj⟩, hxO⟩ := hcons i j h1 h2
      exact ⟨x, ⟨hxi, hxO⟩, ⟨hxj, hxO⟩⟩

/-- Concatenation of two chains meeting only at the junction (last link of `A`, first of `B`). -/
def chainAppend {a b : ℕ} (A : Chain X a) (B : Chain X b) (ha : 0 < a) (hb : 0 < b)
    (hmeet : (A.link ⟨a - 1, by omega⟩ ∩ B.link ⟨0, hb⟩).Nonempty)
    (hdisj : ∀ i j, (A.link i ∩ B.link j).Nonempty → i.val = a - 1 ∧ j.val = 0) :
    Chain X (a + b) where
  link t := if h : t.val < a then A.link ⟨t.val, h⟩ else B.link ⟨t.val - a, by omega⟩
  isOpen t := by
    by_cases h : t.val < a
    · rw [dif_pos h]; exact A.isOpen _
    · rw [dif_neg h]; exact B.isOpen _
  adjacent i j := by
    rw [natAbs_le_one_iff]
    by_cases hi : i.val < a <;> by_cases hj : j.val < a
    · rw [dif_pos hi, dif_pos hj, A.adjacent_iff]
    · rw [dif_pos hi, dif_neg hj]
      constructor
      · intro h
        have := hdisj _ _ h
        simp only at this
        omega
      · rintro ⟨h1, h2⟩
        have e1 : (⟨i.val, hi⟩ : Fin a) = ⟨a - 1, by omega⟩ := Fin.ext (by simp only; omega)
        have e2 : (⟨j.val - a, by omega⟩ : Fin b) = ⟨0, hb⟩ := Fin.ext (by simp only; omega)
        rw [e1, e2]; exact hmeet
    · rw [dif_neg hi, dif_pos hj]
      constructor
      · intro h
        rw [inter_comm] at h
        have := hdisj _ _ h
        simp only at this
        omega
      · rintro ⟨h1, h2⟩
        have e1 : (⟨j.val, hj⟩ : Fin a) = ⟨a - 1, by omega⟩ := Fin.ext (by simp only; omega)
        have e2 : (⟨i.val - a, by omega⟩ : Fin b) = ⟨0, hb⟩ := Fin.ext (by simp only; omega)
        rw [e1, e2, inter_comm]; exact hmeet
    · rw [dif_neg hi, dif_neg hj, B.adjacent_iff]
      simp only
      omega

theorem chainAppend_link_lt {a b : ℕ} {A : Chain X a} {B : Chain X b} {ha : 0 < a} {hb : 0 < b}
    {hmeet} {hdisj} (t : Fin (a + b)) (h : t.val < a) :
    (chainAppend A B ha hb hmeet hdisj).link t = A.link ⟨t.val, h⟩ := dif_pos h

theorem chainAppend_link_ge {a b : ℕ} {A : Chain X a} {B : Chain X b} {ha : 0 < a} {hb : 0 < b}
    {hmeet} {hdisj} (t : Fin (a + b)) (h : ¬ t.val < a) :
    (chainAppend A B ha hb hmeet hdisj).link t = B.link ⟨t.val - a, by omega⟩ := dif_neg h

theorem chainAppend_link_cases {a b : ℕ} {A : Chain X a} {B : Chain X b} {ha : 0 < a}
    {hb : 0 < b} {hmeet} {hdisj} (t : Fin (a + b)) :
    (∃ i, (chainAppend A B ha hb hmeet hdisj).link t = A.link i) ∨
      (∃ j, (chainAppend A B ha hb hmeet hdisj).link t = B.link j) := by
  by_cases h : t.val < a
  · exact Or.inl ⟨_, chainAppend_link_lt t h⟩
  · exact Or.inr ⟨_, chainAppend_link_ge t h⟩

theorem chainAppend_isEpsChain {a b : ℕ} {A : Chain X a} {B : Chain X b} {ha : 0 < a}
    {hb : 0 < b} {hmeet} {hdisj} {ε : ℝ} (hA : IsEpsChain A ε) (hB : IsEpsChain B ε) :
    IsEpsChain (chainAppend A B ha hb hmeet hdisj) ε := by
  intro t
  rcases chainAppend_link_cases (hmeet := hmeet) (hdisj := hdisj) t with ⟨i, hi⟩ | ⟨j, hj⟩
  · rw [hi]; exact hA i
  · rw [hj]; exact hB j

theorem union_chainAppend {a b : ℕ} {A : Chain X a} {B : Chain X b} {ha : 0 < a}
    {hb : 0 < b} {hmeet} {hdisj} :
    A.union ∪ B.union ⊆ (chainAppend A B ha hb hmeet hdisj).union := by
  rintro x (hx | hx)
  · obtain ⟨i, hi⟩ := exists_link_of_mem_union hx
    simp only [Chain.union, mem_iUnion]
    refine ⟨⟨i.val, by omega⟩, ?_⟩
    rw [chainAppend_link_lt _ i.isLt]
    exact hi
  · obtain ⟨j, hj⟩ := exists_link_of_mem_union hx
    simp only [Chain.union, mem_iUnion]
    refine ⟨⟨a + j.val, by omega⟩, ?_⟩
    rw [chainAppend_link_ge _ (by simp only; omega)]
    convert hj using 2
    ext; simp only; omega

/-- **Consecutive links meet inside the covered set.** If every link of a chain meets a
preconnected set `C` it covers, then consecutive links meet inside `C`. -/
theorem consec_meet {n : ℕ} (D : Chain X n) {C : Set X} (hC : IsPreconnected C)
    (hCD : C ⊆ D.union) (hall : ∀ i, (C ∩ D.link i).Nonempty) (i : ℕ) (hi : i + 1 < n) :
    (C ∩ (D.link ⟨i, by omega⟩ ∩ D.link ⟨i + 1, hi⟩)).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  set U : Set X := ⋃ t : Fin n, ⋃ (_ : t.val ≤ i), D.link t with hU
  set V : Set X := ⋃ t : Fin n, ⋃ (_ : i + 1 ≤ t.val), D.link t with hV
  have hUo : IsOpen U := isOpen_iUnion fun t => isOpen_iUnion fun _ => D.isOpen t
  have hVo : IsOpen V := isOpen_iUnion fun t => isOpen_iUnion fun _ => D.isOpen t
  have hcov : C ⊆ U ∪ V := by
    intro z hz
    obtain ⟨t, ht⟩ := exists_link_of_mem_union (hCD hz)
    by_cases hti : t.val ≤ i
    · exact Or.inl (mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨hti, ht⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨by omega, ht⟩⟩)
  obtain ⟨u, huC, hu⟩ := hall ⟨i, by omega⟩
  obtain ⟨v, hvC, hv⟩ := hall ⟨i + 1, hi⟩
  obtain ⟨z, hzC, hzU, hzV⟩ := hC U V hUo hVo hcov
    ⟨u, huC, mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨le_refl i, hu⟩⟩⟩
    ⟨v, hvC, mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨le_refl (i + 1), hv⟩⟩⟩
  simp only [hU, hV, mem_iUnion] at hzU hzV
  obtain ⟨t1, h1, hz1⟩ := hzU
  obtain ⟨t2, h2, hz2⟩ := hzV
  have := (D.adjacent_iff t1 t2).mp ⟨z, hz1, hz2⟩
  have e1 : t1 = ⟨i, by omega⟩ := Fin.ext (by simp only; omega)
  have e2 : t2 = ⟨i + 1, hi⟩ := Fin.ext (by simp only; omega)
  rw [e1] at hz1
  rw [e2] at hz2
  have : z ∈ C ∩ (D.link ⟨i, by omega⟩ ∩ D.link ⟨i + 1, hi⟩) := ⟨hzC, hz1, hz2⟩
  rw [h] at this
  exact this

/-- The links meeting a nonempty preconnected set covered by a chain form an interval `[a, b]`. -/
theorem exists_trim {n : ℕ} (D : Chain X n) {C : Set X} (hC : IsPreconnected C)
    (hCne : C.Nonempty) (hCD : C ⊆ D.union) :
    ∃ a b : Fin n, a ≤ b ∧ ∀ t : Fin n, (C ∩ D.link t).Nonempty ↔ (a.val ≤ t.val ∧ t.val ≤ b.val) := by
  classical
  set I := Finset.univ.filter (fun i : Fin n => (C ∩ D.link i).Nonempty) with hI
  obtain ⟨x, hx⟩ := hCne
  obtain ⟨i0, hi0⟩ := exists_link_of_mem_union (hCD hx)
  have hmem : ∀ t, t ∈ I ↔ (C ∩ D.link t).Nonempty := fun t => by
    simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]
  have hIne : I.Nonempty := ⟨i0, (hmem i0).mpr ⟨x, hx, hi0⟩⟩
  refine ⟨I.min' hIne, I.max' hIne, Finset.min'_le_max' I hIne, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · exact ⟨Fin.le_def.mp (Finset.min'_le I t ((hmem t).mpr ht)),
      Fin.le_def.mp (Finset.le_max' I t ((hmem t).mpr ht))⟩
  · have ha := (hmem _).mp (Finset.min'_mem I hIne)
    have hb := (hmem _).mp (Finset.max'_mem I hIne)
    exact meets_between D hC hCD ha hb t (by have := ht.1; omega) (by have := ht.2; omega)

/-- **Trimming a chain with an end at `p`.** -/
theorem trim_first {n : ℕ} (D : Chain X n) {ε : ℝ} (hD : IsEpsChain D ε) {C : Set X}
    (hC : IsPreconnected C) (hCD : C ⊆ D.union) {p : X} (hpC : p ∈ C) (hn : 0 < n)
    (hp0 : p ∈ D.link ⟨0, hn⟩) (hpcl : ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (D.link j)) :
    ∃ (m : ℕ) (E : Chain X m) (hm : 0 < m), IsEpsChain E ε ∧ C ⊆ E.union ∧
      (∀ i, (C ∩ E.link i).Nonempty) ∧ p ∈ E.link ⟨0, hm⟩ ∧
      ∀ j : Fin m, j.val ≠ 0 → p ∉ closure (E.link j) := by
  obtain ⟨a, b, hab, hiff⟩ := exists_trim D hC ⟨p, hpC⟩ hCD
  have ha0 : a.val = 0 := by have := ((hiff ⟨0, hn⟩).mp ⟨p, hpC, hp0⟩).1; simp only at this; omega
  have hlink : ∀ s : Fin (b.val - a.val + 1), (D.sub a b hab).link s = D.link ⟨a.val + s.val, by omega⟩ :=
    fun s => rfl
  refine ⟨b.val - a.val + 1, D.sub a b hab, by omega, fun s => hD _, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨t, ht⟩ := exists_link_of_mem_union (hCD hy)
    have := (hiff t).mp ⟨y, hy, ht⟩
    simp only [Chain.union, mem_iUnion]
    refine ⟨⟨t.val - a.val, by omega⟩, ?_⟩
    rw [hlink]
    convert ht using 2
    ext; simp only; omega
  · intro s
    rw [hlink]
    exact (hiff _).mpr ⟨by simp only; omega, by simp only; omega⟩
  · rw [hlink]
    convert hp0 using 2
    ext; simp only; omega
  · intro j hj
    rw [hlink]
    exact hpcl _ (by simp only; omega)

theorem isEpsChain_chainRestrict {n : ℕ} {D : Chain X n} {O : Set X} {hO : IsOpen O} {hcons}
    {ε : ℝ} (hD : IsEpsChain D ε) : IsEpsChain (chainRestrict D O hO hcons) ε := fun i =>
  ⟨(hD i).1.subset inter_subset_left,
    lt_of_le_of_lt (Metric.diam_mono inter_subset_left (hD i).1) (hD i).2⟩

/-- Every point of an open set has a ball inside it of radius at most any prescribed `r₀ > 0`. -/
theorem exists_ball_subset_small {W : Set X} (hW : IsOpen W) {p : X} (hp : p ∈ W) {r₀ : ℝ}
    (hr₀ : 0 < r₀) : ∃ r > 0, r ≤ r₀ ∧ ball p r ⊆ W := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hW p hp
  exact ⟨min r r₀, lt_min hr hr₀, min_le_right _ _, (ball_subset_ball (min_le_left _ _)).trans hsub⟩

/-- **Bing's amalgamation** (item 7), for `Z ⊆ H ∪ K` with `H ∩ K = {p}`: an `ε`-chain covering
`H` with `p` in its last link only (and in no other link's closure) and an `ε`-chain covering `K`
with `p` in its first link only give an `ε`-chain covering `Z`. Construction: trim both chains to
the links meeting `H`, resp. `K` (`trim_first`); take a ball `N = B(p, ρ)` missing the closures of
all links but the two end links and contained in both; separate `H ∖ B(p, ρ/2)` from
`K ∖ B(p, ρ/2)` by disjoint open sets `O_H`, `O_K`; the chain is
`h₁ ∩ O_H, …, h_m ∩ O_H, N, k₁ ∩ O_K, …, k_n ∩ O_K`. Consecutive links meet because consecutive
links of a trimmed chain meet inside the covered set (`consec_meet`) away from `B(p, ρ/2)`, and
because `H`, `K` have points at distance exactly `3ρ/4` from `p`. -/
theorem epsCoverable_amalgam_gen {H K Z : Set X} (hH : Fold.Q78.IsContinuum H)
    (hK : Fold.Q78.IsContinuum K) {p : X} (hHK : H ∩ K = {p}) (hZ : Z ⊆ H ∪ K) {ε : ℝ}
    (hε : 0 < ε)
    (hh : ∃ (m : ℕ) (h : Chain X m) (hm : 0 < m), IsEpsChain h ε ∧ H ⊆ h.union ∧
      p ∈ h.link ⟨m - 1, by omega⟩ ∧ ∀ j : Fin m, j.val ≠ m - 1 → p ∉ closure (h.link j))
    (hk : ∃ (n : ℕ) (k : Chain X n) (hn : 0 < n), IsEpsChain k ε ∧ K ⊆ k.union ∧
      p ∈ k.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (k.link j)) :
    EpsCoverable Z ε := by
  have hpH : p ∈ H := (hHK.symm ▸ mem_singleton p : p ∈ H ∩ K).1
  have hpK : p ∈ K := (hHK.symm ▸ mem_singleton p : p ∈ H ∩ K).2
  obtain ⟨m₀, h₀, hm₀, hh₀, hHh₀, hph₀, hpcl₀⟩ := hh
  obtain ⟨n₀, k₀, hn₀, hk₀, hKk₀, hpk₀, hpclk₀⟩ := hk
  -- degenerate sides
  by_cases hHnt : H.Nontrivial
  swap
  · refine ⟨n₀, k₀, hk₀, fun x hx => hKk₀ ?_⟩
    rcases hZ hx with hxH | hxK
    · rw [(Set.not_nontrivial_iff.mp hHnt).eq_singleton_of_mem hpH] at hxH
      rw [mem_singleton_iff.mp hxH]; exact hpK
    · exact hxK
  by_cases hKnt : K.Nontrivial
  swap
  · refine ⟨m₀, h₀, hh₀, fun x hx => hHh₀ ?_⟩
    rcases hZ hx with hxH | hxK
    · exact hxH
    · rw [(Set.not_nontrivial_iff.mp hKnt).eq_singleton_of_mem hpK] at hxK
      rw [mem_singleton_iff.mp hxK]; exact hpH
  -- trim both chains (the `H`-chain reversed so that `p` is in its first link)
  obtain ⟨ma, Ea, hma, hEa, hHEa, hallA, hpA, hpclA⟩ := trim_first h₀.reverse
    (fun i => hh₀ _) hH.2.isPreconnected
    (fun x hx => by
      obtain ⟨i, hi⟩ := exists_link_of_mem_union (hHh₀ hx)
      simp only [Chain.union, mem_iUnion, Chain.reverse_link]
      exact ⟨Fin.rev i, by rw [Fin.rev_rev]; exact hi⟩) hpH hm₀
    (by rw [Chain.reverse_link]; convert hph₀ using 2)
    (fun j hj => by
      rw [Chain.reverse_link]
      exact hpcl₀ _ (by rw [Fin.val_rev]; omega))
  obtain ⟨mb, B, hmb, hB, hKB, hallB, hpB, hpclB⟩ := trim_first k₀ hk₀ hK.2.isPreconnected hKk₀
    hpK hn₀ hpk₀ hpclk₀
  set A := Ea.reverse with hAdef
  have hAlink : ∀ i, A.link i = Ea.link (Fin.rev i) := fun i => rfl
  have hA : IsEpsChain A ε := fun i => hEa _
  have hHA : H ⊆ A.union := fun x hx => by
    obtain ⟨i, hi⟩ := exists_link_of_mem_union (hHEa hx)
    simp only [Chain.union, mem_iUnion, hAlink]
    exact ⟨Fin.rev i, by rw [Fin.rev_rev]; exact hi⟩
  have hallA' : ∀ i, (H ∩ A.link i).Nonempty := fun i => by rw [hAlink]; exact hallA _
  have hrev0 : Fin.rev (⟨ma - 1, by omega⟩ : Fin ma) = ⟨0, hma⟩ := Fin.ext (by simp [Fin.val_rev]; omega)
  have hpAl : p ∈ A.link ⟨ma - 1, by omega⟩ := by rw [hAlink, hrev0]; exact hpA
  have hpclA' : ∀ j : Fin ma, j.val ≠ ma - 1 → p ∉ closure (A.link j) := fun j hj => by
    rw [hAlink]; exact hpclA _ (by rw [Fin.val_rev]; omega)
  -- the ball around `p`
  set W : Set X := A.link ⟨ma - 1, by omega⟩ ∩ B.link ⟨0, hmb⟩ ∩
    (⋂ j : Fin ma, if j.val = ma - 1 then univ else (closure (A.link j))ᶜ) ∩
    (⋂ j : Fin mb, if j.val = 0 then univ else (closure (B.link j))ᶜ) with hW
  have hWo : IsOpen W := by
    refine (((A.isOpen _).inter (B.isOpen _)).inter (isOpen_iInter_of_finite fun j => ?_)).inter
      (isOpen_iInter_of_finite fun j => ?_)
    · split_ifs
      · exact isOpen_univ
      · exact isClosed_closure.isOpen_compl
    · split_ifs
      · exact isOpen_univ
      · exact isClosed_closure.isOpen_compl
  have hpW : p ∈ W := by
    refine ⟨⟨⟨hpAl, hpB⟩, mem_iInter.mpr fun j => ?_⟩, mem_iInter.mpr fun j => ?_⟩
    · split_ifs with hj
      · trivial
      · exact hpclA' j hj
    · split_ifs with hj
      · trivial
      · exact hpclB j hj
  obtain ⟨xH, hxH, hxHp⟩ := hHnt.exists_ne p
  obtain ⟨xK, hxK, hxKp⟩ := hKnt.exists_ne p
  have hdH : 0 < dist p xH := dist_pos.mpr (Ne.symm hxHp)
  have hdK : 0 < dist p xK := dist_pos.mpr (Ne.symm hxKp)
  obtain ⟨ρ, hρ, hρle, hball⟩ := exists_ball_subset_small hWo hpW
    (lt_min (by linarith : 0 < ε / 4) (lt_min hdH hdK))
  have hρε : ρ ≤ ε / 4 := hρle.trans (min_le_left _ _)
  have hρH : ρ ≤ dist p xH := hρle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρK : ρ ≤ dist p xK := hρle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hballA : ∀ j : Fin ma, j.val ≠ ma - 1 → ∀ x ∈ ball p ρ, x ∉ A.link j := by
    intro j hj x hx hxj
    have := (mem_iInter.mp (hball hx).1.2) j
    rw [if_neg hj] at this
    exact this (subset_closure hxj)
  have hballB : ∀ j : Fin mb, j.val ≠ 0 → ∀ x ∈ ball p ρ, x ∉ B.link j := by
    intro j hj x hx hxj
    have := (mem_iInter.mp (hball hx).2) j
    rw [if_neg hj] at this
    exact this (subset_closure hxj)
  have hballAl : ball p ρ ⊆ A.link ⟨ma - 1, by omega⟩ := fun x hx => (hball hx).1.1.1
  have hballB0 : ball p ρ ⊆ B.link ⟨0, hmb⟩ := fun x hx => (hball hx).1.1.2
  -- points at distance `3ρ/4`
  have hmid : ∀ {C : Set X} {x : X}, IsPreconnected C → p ∈ C → x ∈ C → ρ ≤ dist p x →
      ∃ y ∈ C, dist p y = 3 * ρ / 4 := by
    intro C x hC hpC hxC hρx
    have := hC.intermediate_value hpC hxC (continuous_const.dist continuous_id).continuousOn
      (show 3 * ρ / 4 ∈ Icc (dist p p) (dist p x) by
        rw [dist_self]; constructor <;> linarith)
    obtain ⟨y, hy, hyd⟩ := this
    exact ⟨y, hy, hyd⟩
  obtain ⟨aH, haH, haHd⟩ := hmid hH.2.isPreconnected hpH hxH hρH
  obtain ⟨aK, haK, haKd⟩ := hmid hK.2.isPreconnected hpK hxK hρK
  -- separating `H ∖ N'` and `K ∖ N'`
  set N' := ball p (ρ / 2) with hN'
  have hsepHK : Disjoint (H \ N') (K \ N') := by
    rw [Set.disjoint_left]
    rintro x ⟨hxH, hxN⟩ ⟨hxK, -⟩
    have : x ∈ H ∩ K := ⟨hxH, hxK⟩
    rw [hHK, mem_singleton_iff] at this
    exact hxN (this ▸ mem_ball_self (by linarith))
  obtain ⟨OH, OK, hOH, hOK, hHOH, hKOK, hOHK⟩ := normal_separation
    (hH.1.isClosed.sdiff isOpen_ball) (hK.1.isClosed.sdiff isOpen_ball) hsepHK
  have hfar : ∀ {C O : Set X}, C \ N' ⊆ O → ∀ y ∈ C, ρ / 2 ≤ dist y p → y ∈ O := by
    intro C O hCO y hy hyd
    exact hCO ⟨hy, fun hyN => by rw [hN', mem_ball] at hyN; linarith⟩
  have haHO : aH ∈ OH := hfar hHOH aH haH (by rw [dist_comm, haHd]; linarith)
  have haKO : aK ∈ OK := hfar hKOK aK haK (by rw [dist_comm, haKd]; linarith)
  have haHball : aH ∈ ball p ρ := by rw [mem_ball, dist_comm, haHd]; linarith
  have haKball : aK ∈ ball p ρ := by rw [mem_ball, dist_comm, haKd]; linarith
  -- points of non-end links are far from `p`
  have hfarA : ∀ j : Fin ma, j.val ≠ ma - 1 → ∀ y ∈ A.link j, ρ / 2 ≤ dist y p := by
    intro j hj y hy
    by_contra hlt
    push_neg at hlt
    exact hballA j hj y (by rw [mem_ball]; linarith) hy
  have hfarB : ∀ j : Fin mb, j.val ≠ 0 → ∀ y ∈ B.link j, ρ / 2 ≤ dist y p := by
    intro j hj y hy
    by_contra hlt
    push_neg at hlt
    exact hballB j hj y (by rw [mem_ball]; linarith) hy
  -- restricted chains
  have hconsA : ∀ i j : Fin ma, i.val ≤ j.val + 1 → j.val ≤ i.val + 1 →
      (A.link i ∩ A.link j ∩ OH).Nonempty := by
    have one : ∀ i : Fin ma, (A.link i ∩ OH).Nonempty := by
      intro i
      by_cases hi : i.val = ma - 1
      · have e : i = ⟨ma - 1, by omega⟩ := Fin.ext hi
        exact ⟨aH, e ▸ hballAl haHball, haHO⟩
      · obtain ⟨y, hyH, hyi⟩ := hallA' i
        exact ⟨y, hyi, hfar hHOH y hyH (hfarA i hi y hyi)⟩
    have two : ∀ (i : ℕ) (hi : i + 1 < ma),
        (A.link ⟨i, by omega⟩ ∩ A.link ⟨i + 1, hi⟩ ∩ OH).Nonempty := by
      intro i hi
      obtain ⟨y, hyH, hyi, hyi'⟩ := consec_meet A hH.2.isPreconnected hHA hallA' i hi
      exact ⟨y, ⟨hyi, hyi'⟩, hfar hHOH y hyH (hfarA _ (by simp only; omega) y hyi)⟩
    intro i j h1 h2
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · have ei : i = ⟨i.val, by omega⟩ := rfl
      have ej : j = ⟨i.val + 1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [ej]; exact two i.val (by omega)
    · have e : i = j := Fin.ext hij
      rw [e, inter_self]; exact one j
    · have ei : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [ei, inter_comm (A.link _)]; exact two j.val (by omega)
  have hconsB : ∀ i j : Fin mb, i.val ≤ j.val + 1 → j.val ≤ i.val + 1 →
      (B.link i ∩ B.link j ∩ OK).Nonempty := by
    have one : ∀ i : Fin mb, (B.link i ∩ OK).Nonempty := by
      intro i
      by_cases hi : i.val = 0
      · have e : i = ⟨0, hmb⟩ := Fin.ext hi
        exact ⟨aK, e ▸ hballB0 haKball, haKO⟩
      · obtain ⟨y, hyK, hyi⟩ := hallB i
        exact ⟨y, hyi, hfar hKOK y hyK (hfarB i hi y hyi)⟩
    have two : ∀ (i : ℕ) (hi : i + 1 < mb),
        (B.link ⟨i, by omega⟩ ∩ B.link ⟨i + 1, hi⟩ ∩ OK).Nonempty := by
      intro i hi
      obtain ⟨y, hyK, hyi, hyi'⟩ := consec_meet B hK.2.isPreconnected hKB hallB i hi
      exact ⟨y, ⟨hyi, hyi'⟩, hfar hKOK y hyK (hfarB _ (by simp only; omega) y hyi')⟩
    intro i j h1 h2
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · have ej : j = ⟨i.val + 1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [ej]; exact two i.val (by omega)
    · have e : i = j := Fin.ext hij
      rw [e, inter_self]; exact one j
    · have ei : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [ei, inter_comm (B.link _)]; exact two j.val (by omega)
  set A' := chainRestrict A OH hOH hconsA with hA'
  set B' := chainRestrict B OK hOK hconsB with hB'
  set Mid := chainSingle (ball p ρ) isOpen_ball ⟨p, mem_ball_self hρ⟩ with hMid
  -- first junction
  have hmeet1 : (A'.link ⟨ma - 1, by omega⟩ ∩ Mid.link ⟨0, one_pos⟩).Nonempty :=
    ⟨aH, ⟨hballAl haHball, haHO⟩, haHball⟩
  have hdisj1 : ∀ i j, (A'.link i ∩ Mid.link j).Nonempty → i.val = ma - 1 ∧ j.val = 0 := by
    rintro i j ⟨x, ⟨hxi, -⟩, hxN⟩
    refine ⟨?_, by have := j.isLt; omega⟩
    by_contra hi
    exact hballA i hi x hxN hxi
  set C1 := chainAppend A' Mid hma one_pos hmeet1 hdisj1 with hC1
  have hC1last : C1.link ⟨ma + 1 - 1, by omega⟩ = ball p ρ := by
    rw [chainAppend_link_ge _ (by simp only; omega)]; rfl
  have hmeet2 : (C1.link ⟨ma + 1 - 1, by omega⟩ ∩ B'.link ⟨0, hmb⟩).Nonempty := by
    rw [hC1last]; exact ⟨aK, haKball, hballB0 haKball, haKO⟩
  have hdisj2 : ∀ i j, (C1.link i ∩ B'.link j).Nonempty → i.val = ma + 1 - 1 ∧ j.val = 0 := by
    rintro i j ⟨x, hxi, hxj, hxOK⟩
    by_cases hi : i.val < ma
    · rw [chainAppend_link_lt _ hi] at hxi
      exact absurd hxOK (Set.disjoint_left.mp hOHK hxi.2)
    · rw [chainAppend_link_ge _ hi] at hxi
      refine ⟨by omega, ?_⟩
      by_contra hj
      exact hballB j hj x hxi hxj
  set C2 := chainAppend C1 B' (by omega) hmb hmeet2 hdisj2 with hC2
  refine ⟨_, C2, ?_, ?_⟩
  · refine chainAppend_isEpsChain (chainAppend_isEpsChain (isEpsChain_chainRestrict hA) ?_)
      (isEpsChain_chainRestrict hB)
    intro _
    refine ⟨isBounded_ball, lt_of_le_of_lt (diam_ball hρ.le) (by linarith)⟩
  · intro x hx
    apply union_chainAppend
    by_cases hxN : x ∈ N'
    · left; apply union_chainAppend; right
      simp only [Chain.union, mem_iUnion]
      exact ⟨⟨0, one_pos⟩, ball_subset_ball (by linarith) hxN⟩
    rcases hZ hx with hxH | hxK
    · left; apply union_chainAppend; left
      obtain ⟨i, hi⟩ := exists_link_of_mem_union (hHA hxH)
      simp only [Chain.union, mem_iUnion]
      exact ⟨i, hi, hHOH ⟨hxH, hxN⟩⟩
    · right
      obtain ⟨i, hi⟩ := exists_link_of_mem_union (hKB hxK)
      simp only [Chain.union, mem_iUnion]
      exact ⟨i, hi, hKOK ⟨hxK, hxN⟩⟩

end Constructions

end HPC.Plane
