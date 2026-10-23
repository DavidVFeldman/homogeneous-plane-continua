import HPC.Chains.Consolidation

/-!
# Schedules: block consolidations as Lipschitz functions into ℕ

A block consolidation of `E` refining `D` with every block inside `w` consecutive links of
`D` is the same as a 1-Lipschitz function `β : Fin m → ℕ` attaining `0`, whose fibers have
minimal-index range less than `w` (up to a shift of one in the converse). This removes `D`
and all set theory from Bing's Theorems 3 and 4, which become statements about the
1-Lipschitz sequence `minIdx`.

Also: the range-covering lemma — reading a crooked chain outward from any link in both
directions, one arm's range of minimal indices covers the other's up to a bounded slack.

English proofs: COMMISSION-batch5.md §2.
-/

namespace HPC

open Set

variable {X : Type*} [MetricSpace X]

/-! ### A discrete intermediate value theorem on `Fin m`

A function on `Fin m` moving by at most one between adjacent indices attains every value
between two of its values. -/

/-- Increasing form: the two indices are given in order. -/
private theorem exists_eq_of_lip_mono {m : ℕ} {β : Fin m → ℕ}
    (hlip : ∀ t t' : Fin m, t'.val = t.val + 1 → ((β t' : ℤ) - (β t : ℤ)).natAbs ≤ 1)
    (v : ℕ) : ∀ (d : ℕ) (a b : Fin m), b.val = a.val + d → β a ≤ v → v ≤ β b →
      ∃ t, β t = v := by
  intro d
  induction d with
  | zero =>
      intro a b hb h1 h2
      have hba : b = a := Fin.ext (by omega)
      subst hba
      exact ⟨b, by omega⟩
  | succ d ih =>
      intro a b hb h1 h2
      have hlt : a.val + 1 < m := by have := b.isLt; omega
      have hstep := hlip a ⟨a.val + 1, hlt⟩ rfl
      by_cases hv : β ⟨a.val + 1, hlt⟩ ≤ v
      · exact ih ⟨a.val + 1, hlt⟩ b (by simp; omega) hv h2
      · exact ⟨a, by omega⟩

/-- Decreasing form: the two indices are given in reverse order. -/
private theorem exists_eq_of_lip_anti {m : ℕ} {β : Fin m → ℕ}
    (hlip : ∀ t t' : Fin m, t'.val = t.val + 1 → ((β t' : ℤ) - (β t : ℤ)).natAbs ≤ 1)
    (v : ℕ) : ∀ (d : ℕ) (a b : Fin m), a.val = b.val + d → β a ≤ v → v ≤ β b →
      ∃ t, β t = v := by
  intro d
  induction d with
  | zero =>
      intro a b hb h1 h2
      have hba : b = a := Fin.ext (by omega)
      subst hba
      exact ⟨b, by omega⟩
  | succ d ih =>
      intro a b hb h1 h2
      have hlt : a.val - 1 < m := by have := a.isLt; omega
      have hstep := hlip ⟨a.val - 1, hlt⟩ a (by simp; omega)
      by_cases hv : β ⟨a.val - 1, hlt⟩ ≤ v
      · exact ih ⟨a.val - 1, hlt⟩ b (by simp; omega) hv h2
      · exact ⟨a, by omega⟩

/-- Unoriented form. -/
private theorem exists_eq_of_lip {m : ℕ} {β : Fin m → ℕ}
    (hlip : ∀ t t' : Fin m, t'.val = t.val + 1 → ((β t' : ℤ) - (β t : ℤ)).natAbs ≤ 1)
    {a b : Fin m} {v : ℕ} (h1 : β a ≤ v) (h2 : v ≤ β b) : ∃ t, β t = v := by
  rcases le_total a.val b.val with hab | hab
  · exact exists_eq_of_lip_mono hlip v (b.val - a.val) a b (by omega) h1 h2
  · exact exists_eq_of_lip_anti hlip v (a.val - b.val) a b (by omega) h1 h2

namespace Chain

variable {n m : ℕ} {E : Chain X m} {D : Chain X n}

/-- The union of the links of `D` with index in `[j, j + w)`. -/
def unionRange (D : Chain X n) (j w : ℕ) : Set X :=
  ⋃ j' ∈ Finset.Ico j (j + w), ⋃ (hj' : j' < n), D.link ⟨j', hj'⟩

theorem mem_unionRange {j w : ℕ} {x : X} :
    x ∈ D.unionRange j w ↔
      ∃ j' : ℕ, j ≤ j' ∧ j' < j + w ∧ ∃ hj' : j' < n, x ∈ D.link ⟨j', hj'⟩ := by
  simp only [unionRange, Set.mem_iUnion, Finset.mem_Ico, exists_prop]
  constructor
  · rintro ⟨j', ⟨hj1, hj2⟩, hj3, hx⟩
    exact ⟨j', hj1, hj2, hj3, hx⟩
  · rintro ⟨j', hj1, hj2, hj3, hx⟩
    exact ⟨j', ⟨hj1, hj2⟩, hj3, hx⟩

theorem link_subset_unionRange (D : Chain X n) {j w : ℕ} (k : Fin n) (h1 : j ≤ k.val)
    (h2 : k.val < j + w) : D.link k ⊆ D.unionRange j w := by
  intro x hx
  rw [mem_unionRange]
  exact ⟨k.val, h1, h2, k.isLt, by simpa using hx⟩

/-- A schedule: a 1-Lipschitz function on the link indices attaining `0`. -/
structure IsSchedule (β : Fin m → ℕ) : Prop where
  lip : ∀ t t' : Fin m, t'.val = t.val + 1 → ((β t' : ℤ) - (β t : ℤ)).natAbs ≤ 1
  zero : ∃ t, β t = 0

/-- A schedule is a block map onto an initial segment of `ℕ`: it is surjective onto
`[0, sup β]` by the discrete intermediate value theorem. -/
theorem IsSchedule.exists_blockMap {β : Fin m → ℕ} (hβ : IsSchedule β) :
    ∃ (p : ℕ) (β' : Fin m → Fin p), IsBlockMap β' ∧ ∀ t, (β' t).val = β t := by
  classical
  obtain ⟨t0, ht0⟩ := hβ.zero
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨t0, Finset.mem_univ _⟩
  obtain ⟨tM, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m)) β hne
  refine ⟨β tM + 1, fun t => ⟨β t, by have := hmax t (Finset.mem_univ t); omega⟩, ⟨?_, ?_⟩,
    fun t => rfl⟩
  · intro u
    have h1 : β t0 ≤ u.val := by omega
    have h2 : u.val ≤ β tM := by have := u.isLt; omega
    obtain ⟨t, ht⟩ := exists_eq_of_lip hβ.lip h1 h2
    exact ⟨t, Fin.ext ht⟩
  · intro t t' htt'
    exact hβ.lip t t' htt'

/-- **Reformulation, (b) ⇒ (a).** A schedule whose fibers have minimal-index range at most
`w − 1` yields a block consolidation with every block inside `w` consecutive links of `D`. -/
theorem exists_blocks_of_schedule (h : E.Refines D) {β : Fin m → ℕ} (hβ : IsSchedule β)
    (w : ℕ) (hw : 1 ≤ w)
    (hwin : ∀ t t', β t = β t' → ((h.minIdx t : ℤ) - (h.minIdx t' : ℤ)).natAbs ≤ w - 1) :
    ∃ (p : ℕ) (β' : Fin m → Fin p) (hβ' : IsBlockMap β'),
      (∀ t, (β' t).val = β t) ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j w := by
  classical
  obtain ⟨p, β', hβ', hval⟩ := hβ.exists_blockMap
  refine ⟨p, β', hβ', hval, ?_⟩
  intro u
  obtain ⟨t0, ht0⟩ := hβ'.surj u
  have hSne : (Finset.univ.filter (fun t : Fin m => β' t = u)).Nonempty :=
    ⟨t0, by simp [ht0]⟩
  obtain ⟨tmin, htminS, htmin⟩ :=
    Finset.exists_min_image (Finset.univ.filter (fun t : Fin m => β' t = u))
      (fun t => (h.minIdx t).val) hSne
  have htminu : β' tmin = u := by simpa using htminS
  refine ⟨(h.minIdx tmin).val, ?_⟩
  rw [ofBlocks_link]
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  have hbeq : β t = β tmin := by
    rw [← hval t, ← hval tmin, ht, htminu]
  have hb := hwin t tmin hbeq
  have hge : (h.minIdx tmin).val ≤ (h.minIdx t).val := htmin t (by simp [ht])
  exact link_subset_unionRange D (h.minIdx t) hge (by omega) (minIdx_subset h t hxt)

/-- **Reformulation, (a) ⇒ (b).** A block consolidation with every block inside `w`
consecutive links of `D` gives a schedule whose fibers have minimal-index range at most
`w`. (The bound is `w`, not `w − 1`: a link inside `e_j ∩ e_{j−1}` has minimal index `j − 1`
while lying in the block's window starting at `j`.) -/
theorem schedule_of_blocks (h : E.Refines D) (hm : 0 < m) {p : ℕ} {β' : Fin m → Fin p}
    (hβ' : IsBlockMap β') (w : ℕ)
    (hblk : ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j w) :
    IsSchedule (fun t => (β' t).val) ∧
      ∀ t t', β' t = β' t' → ((h.minIdx t : ℤ) - (h.minIdx t' : ℤ)).natAbs ≤ w := by
  classical
  have hp : 0 < p := by
    have := (β' ⟨0, hm⟩).isLt; omega
  -- the key window claim, for a single link of a block
  have key : ∀ (t : Fin m) (u : Fin p) (j : ℕ), β' t = u →
      (E.ofBlocks β' hβ').link u ⊆ D.unionRange j w →
      ((j : ℤ) - 1 ≤ (h.minIdx t : ℤ) ∧ ((h.minIdx t : ℤ) : ℤ) ≤ (j : ℤ) + (w : ℤ) - 1) := by
    intro t u j htu hsub
    have hlink : E.link t ⊆ D.unionRange j w := by
      refine subset_trans ?_ hsub
      rw [ofBlocks_link]
      exact Set.subset_biUnion_of_mem (u := fun t => E.link t) (show β' t = u from htu)
    -- every point of `E.link t` lies in a link of the window
    obtain ⟨z, hz⟩ := E.link_nonempty t
    obtain ⟨j0, hj01, hj02, hj03, hj04⟩ := mem_unionRange.mp (hlink hz)
    have hnear : ((h.minIdx t : ℤ) - (j0 : ℤ)).natAbs ≤ 1 :=
      minIdx_near_of_inter h t ⟨j0, hj03⟩ ⟨z, hz, by simpa using hj04⟩
    -- the upper end `j + w` is excluded
    have hup : (h.minIdx t).val ≠ j + w := by
      intro hcontra
      have hw1 : 0 < w := by omega
      have hsub2 : E.link t ⊆ D.link ⟨j + w - 1, by
          have := (h.minIdx t).isLt; omega⟩ := by
        intro y hy
        obtain ⟨j1, hj11, hj12, hj13, hj14⟩ := mem_unionRange.mp (hlink hy)
        have hne1 : ((h.minIdx t : ℤ) - (j1 : ℤ)).natAbs ≤ 1 :=
          minIdx_near_of_inter h t ⟨j1, hj13⟩ ⟨y, hy, by simpa using hj14⟩
        have : j1 = j + w - 1 := by omega
        subst this
        simpa using hj14
      have := minIdx_le h t hsub2
      rw [Fin.le_def] at this
      simp only [] at this
      omega
    have hlt : (h.minIdx t).val ≤ j + w := by omega
    refine ⟨by omega, ?_⟩
    have : (h.minIdx t).val < j + w := by omega
    omega
  refine ⟨⟨fun t t' htt' => hβ'.lip t t' htt', ?_⟩, ?_⟩
  · obtain ⟨t, ht⟩ := hβ'.surj ⟨0, hp⟩
    exact ⟨t, by rw [ht]⟩
  · intro t t' htt'
    obtain ⟨j, hj⟩ := hblk (β' t)
    have h1 := key t (β' t) j rfl hj
    have h2 := key t' (β' t) j htt'.symm hj
    omega

/-- **The three-link form.** A schedule together with a walk `b` such that every link's
minimal index is within one of `b` at its time gives a block consolidation with every block
inside three consecutive links of `D`. This is the form in which Theorems 3 and 4 will be
stated. -/
theorem exists_blocks_of_walk (h : E.Refines D) {β : Fin m → ℕ} (hβ : IsSchedule β)
    (b : ℕ → ℤ) (hb : ∀ t, ((h.minIdx t : ℤ) - b (β t)).natAbs ≤ 1) :
    ∃ (p : ℕ) (β' : Fin m → Fin p) (hβ' : IsBlockMap β'),
      (∀ t, (β' t).val = β t) ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  refine exists_blocks_of_schedule h hβ 3 (by norm_num) ?_
  intro t t' hβtt'
  have h1 := hb t
  have h2 := hb t'
  rw [hβtt'] at h1
  omega

/-- **The range-covering lemma.** Let `E` be crooked in `D` (1948 sense) and `i` a link of
`E`. Read `E` outward from `i` in both directions: the *tail* `t ≤ i` and the *guide* `g ≥ i`.
Then one arm covers the other's range of minimal indices, up to a slack of one below and
two above. Precisely: either every tail level is within one above some guide level and within
two below some guide level, or the same with the arms exchanged. -/
theorem range_covering (h : E.IsCrookedIn' D) (i : Fin m) :
    let ρ := h.1.minIdx
    ((∀ t, t ≤ i → ∃ g, i ≤ g ∧ (ρ g).val ≤ (ρ t).val + 1) ∧
     (∀ t, t ≤ i → ∃ g, i ≤ g ∧ (ρ t).val ≤ (ρ g).val + 2)) ∨
    ((∀ g, i ≤ g → ∃ t, t ≤ i ∧ (ρ t).val ≤ (ρ g).val + 1) ∧
     (∀ g, i ≤ g → ∃ t, t ≤ i ∧ (ρ g).val ≤ (ρ t).val + 2)) := by
  classical
  intro ρ
  -- the four extremal indices
  have hTne : (Finset.univ.filter (fun t : Fin m => t ≤ i)).Nonempty := ⟨i, by simp⟩
  have hGne : (Finset.univ.filter (fun g : Fin m => i ≤ g)).Nonempty := ⟨i, by simp⟩
  obtain ⟨tlo, htloS, htlo⟩ :=
    Finset.exists_min_image _ (fun t => (ρ t).val) hTne
  obtain ⟨thi, hthiS, hthi⟩ :=
    Finset.exists_max_image _ (fun t => (ρ t).val) hTne
  obtain ⟨glo, hgloS, hglo⟩ :=
    Finset.exists_min_image _ (fun g => (ρ g).val) hGne
  obtain ⟨ghi, hghiS, hghi⟩ :=
    Finset.exists_max_image _ (fun g => (ρ g).val) hGne
  have htloi : tlo ≤ i := by simpa using htloS
  have hthii : thi ≤ i := by simpa using hthiS
  have hgloi : i ≤ glo := by simpa using hgloS
  have hghii : i ≤ ghi := by simpa using hghiS
  have hmemT : i ∈ Finset.univ.filter (fun t : Fin m => t ≤ i) := by simp
  have hmemG : i ∈ Finset.univ.filter (fun g : Fin m => i ≤ g) := by simp
  have hloT_i : (ρ tlo).val ≤ (ρ i).val := htlo i hmemT
  have hhiT_i : (ρ i).val ≤ (ρ thi).val := hthi i hmemT
  have hloG_i : (ρ glo).val ≤ (ρ i).val := hglo i hmemG
  have hhiG_i : (ρ i).val ≤ (ρ ghi).val := hghi i hmemG
  -- nonemptiness of the intersections used to invoke crookedness
  have hmeet : ∀ t : Fin m, (E.link t ∩ D.link (ρ t)).Nonempty := by
    intro t
    obtain ⟨z, hz⟩ := E.link_nonempty t
    exact ⟨z, hz, minIdx_subset h.1 t hz⟩
  -- Claim A
  have claimA : ¬ ((ρ tlo).val + 2 ≤ (ρ glo).val ∧ (ρ thi).val + 3 ≤ (ρ ghi).val) := by
    rintro ⟨hA1, hA2⟩
    have hk : (ρ tlo).val + 2 < (ρ ghi).val := by omega
    obtain ⟨r, s, hbtw, hr, hs⟩ :=
      h.2 (ρ tlo) (ρ ghi) hk tlo ghi (hmeet tlo) (hmeet ghi)
    have htg : tlo ≤ ghi := le_trans htloi hghii
    have horder : tlo < r ∧ r < s ∧ s < ghi := by
      rcases hbtw with hb | hb
      · exact hb
      · exact absurd htg (not_le.mpr (lt_trans (lt_trans hb.2.2 hb.2.1) hb.1))
    -- `ρ r` is high, so `r` is not on the tail side
    have hrnear : (((ρ r).val : ℤ) - (((ρ ghi).val - 1 : ℕ) : ℤ)).natAbs ≤ 1 :=
      subset_adjacent_of_subset h.1 r (minIdx_subset h.1 r) hr
    have hrbig : (ρ thi).val < (ρ r).val := by omega
    have hri : i < r := by
      by_contra hcon
      push_neg at hcon
      have : (ρ r).val ≤ (ρ thi).val := hthi r (by simp [hcon])
      omega
    have hsi : i ≤ s := le_of_lt (lt_trans hri horder.2.1)
    have hslo : (ρ glo).val ≤ (ρ s).val := hglo s (by simp [hsi])
    have hsle : (ρ s).val ≤ (ρ tlo).val + 1 := minIdx_le h.1 s hs
    omega
  -- Claim B
  have claimB : ¬ ((ρ glo).val + 2 ≤ (ρ tlo).val ∧ (ρ ghi).val + 3 ≤ (ρ thi).val) := by
    rintro ⟨hB1, hB2⟩
    have hk : (ρ glo).val + 2 < (ρ thi).val := by omega
    obtain ⟨r, s, hbtw, hr, hs⟩ :=
      h.2 (ρ glo) (ρ thi) hk glo thi (hmeet glo) (hmeet thi)
    have htg : thi ≤ glo := le_trans hthii hgloi
    have horder : glo > r ∧ r > s ∧ s > thi := by
      rcases hbtw with hb | hb
      · exact absurd htg (not_le.mpr (lt_trans (lt_trans hb.1 hb.2.1) hb.2.2))
      · exact hb
    have hrnear : (((ρ r).val : ℤ) - (((ρ thi).val - 1 : ℕ) : ℤ)).natAbs ≤ 1 :=
      subset_adjacent_of_subset h.1 r (minIdx_subset h.1 r) hr
    have hrbig : (ρ ghi).val < (ρ r).val := by omega
    have hri : r < i := by
      by_contra hcon
      push_neg at hcon
      have : (ρ r).val ≤ (ρ ghi).val := hghi r (by simp [hcon])
      omega
    have hsi : s ≤ i := le_of_lt (lt_trans horder.2.1 hri)
    have hslo : (ρ tlo).val ≤ (ρ s).val := htlo s (by simp [hsi])
    have hsle : (ρ s).val ≤ (ρ glo).val + 1 := minIdx_le h.1 s hs
    omega
  -- assembling the disjunction
  by_cases hc : (ρ tlo).val + 2 ≤ (ρ glo).val
  · right
    have hA : ¬ ((ρ thi).val + 3 ≤ (ρ ghi).val) := fun hcon => claimA ⟨hc, hcon⟩
    refine ⟨fun g hg => ⟨tlo, htloi, ?_⟩, fun g hg => ⟨thi, hthii, ?_⟩⟩
    · have hgle : (ρ glo).val ≤ (ρ g).val := hglo g (by simp [hg])
      omega
    · have hgle : (ρ g).val ≤ (ρ ghi).val := hghi g (by simp [hg])
      omega
  · push_neg at hc
    by_cases hd : (ρ ghi).val + 3 ≤ (ρ thi).val
    · right
      have hB : ¬ ((ρ glo).val + 2 ≤ (ρ tlo).val) := fun hcon => claimB ⟨hcon, hd⟩
      refine ⟨fun g hg => ⟨tlo, htloi, ?_⟩, fun g hg => ⟨thi, hthii, ?_⟩⟩
      · have hgle : (ρ glo).val ≤ (ρ g).val := hglo g (by simp [hg])
        omega
      · have hgle : (ρ g).val ≤ (ρ ghi).val := hghi g (by simp [hg])
        omega
    · push_neg at hd
      left
      refine ⟨fun t ht => ⟨glo, hgloi, ?_⟩, fun t ht => ⟨ghi, hghii, ?_⟩⟩
      · have hle : (ρ tlo).val ≤ (ρ t).val := htlo t (by simp [ht])
        omega
      · have hle : (ρ t).val ≤ (ρ thi).val := hthi t (by simp [ht])
        omega

end Chain

end HPC
