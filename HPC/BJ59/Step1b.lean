import HPC.BJ59.Defs

/-!
# Batch 200, §3: Step 1(b) of Theorem 10 (Bing–Jones p. 182)

The skeleton's `bj_step1b` (statement verbatim). The proof is a neighbourhood form of commission
200 §3's compactness argument, without sequences:

* `exists_nhd_step1b`: about each `c ∈ [0, 1]` there is an open `N` such that every point over
  `N` lies in a link that meets every fibre over `N` (upper semicontinuity, as `f` is closed, and
  lower semicontinuity, as `f` is open, over the finitely many links meeting the fibre over `c`);
* a Lebesgue number of these neighbourhoods is `2δ`;
* the end-link case analysis of commission §3 then shows that each fibre over `[a, b]` meets both
  end links, and a connected set covered by a subchain and meeting both its end links meets all of
  its links (`meets_all_of_meets_ends`).
-/

namespace HPC.BJ59

open Set Topology Metric Filter

section Step1b

variable {X : Type*} [MetricSpace X]

/-- A preconnected set covered by the links `u, …, v` of a chain and meeting the links `u` and `v`
meets every link between them. -/
theorem meets_all_of_meets_ends {N : ℕ} (E : Chain X N) {S : Set X} (hS : IsPreconnected S)
    (u v : Fin N) (hcov : S ⊆ ⋃ (k : Fin N) (_ : u.val ≤ k.val ∧ k.val ≤ v.val), E.link k)
    (hu : (E.link u ∩ S).Nonempty) (hv : (E.link v ∩ S).Nonempty) (k : Fin N)
    (huk : u.val ≤ k.val) (hkv : k.val ≤ v.val) : (E.link k ∩ S).Nonempty := by
  by_contra hno
  rw [not_nonempty_iff_eq_empty] at hno
  have hku : u.val < k.val := by
    rcases eq_or_lt_of_le huk with h | h
    · exact absurd (Fin.ext h ▸ hu) (hno ▸ not_nonempty_empty)
    · exact h
  have hkv' : k.val < v.val := by
    rcases eq_or_lt_of_le hkv with h | h
    · exact absurd ((Fin.ext h).symm ▸ hv) (hno ▸ not_nonempty_empty)
    · exact h
  set A : Set X := ⋃ (j : Fin N) (_ : j.val < k.val), E.link j
  set B : Set X := ⋃ (j : Fin N) (_ : k.val < j.val), E.link j
  have hA : IsOpen A := isOpen_iUnion fun j => isOpen_iUnion fun _ => E.isOpen j
  have hB : IsOpen B := isOpen_iUnion fun j => isOpen_iUnion fun _ => E.isOpen j
  have hSAB : S ⊆ A ∪ B := by
    intro x hx
    obtain ⟨j, -, hxj⟩ := mem_iUnion₂.1 (hcov hx)
    rcases lt_trichotomy j.val k.val with h | h | h
    · exact Or.inl (mem_iUnion₂.2 ⟨j, h, hxj⟩)
    · have hj : j = k := Fin.ext h
      subst hj
      exact absurd (⟨x, hxj, hx⟩ : (E.link j ∩ S).Nonempty) (by rw [hno]; exact not_nonempty_empty)
    · exact Or.inr (mem_iUnion₂.2 ⟨j, h, hxj⟩)
  obtain ⟨a, hau, haS⟩ := hu
  obtain ⟨b, hbv, hbS⟩ := hv
  obtain ⟨x, -, hxA, hxB⟩ := hS A B hA hB hSAB ⟨a, haS, mem_iUnion₂.2 ⟨u, hku, hau⟩⟩
    ⟨b, hbS, mem_iUnion₂.2 ⟨v, hkv', hbv⟩⟩
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hxA
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hxB
  have := (E.adjacent i j).1 ⟨x, hxi, hxj⟩
  omega

/-- About each point `c` of `[0, 1]`, an open neighbourhood `N` such that each point over `N` lies
in a link meeting every fibre over `N`. -/
theorem exists_nhd_step1b [CompactSpace X] {f : X → unitInterval} (hfc : Continuous f)
    (hfo : IsOpenMap f) {N : ℕ} (E : Chain X N) (hE : univ ⊆ E.union) (c : unitInterval) :
    ∃ U : Set unitInterval, IsOpen U ∧ c ∈ U ∧ ∀ x ∈ U, ∀ z, f z ∈ U →
      ∃ w, z ∈ E.link w ∧ (E.link w ∩ f ⁻¹' {x}).Nonempty := by
  classical
  set J : Set (Fin N) := {w | (E.link w ∩ f ⁻¹' {c}).Nonempty}
  set O : Set X := ⋃ w ∈ J, E.link w
  have hO : IsOpen O := isOpen_biUnion fun w _ => E.isOpen w
  have hFO : f ⁻¹' {c} ⊆ O := by
    intro z hz
    obtain ⟨w, hw⟩ := mem_iUnion.1 (hE (mem_univ z))
    exact mem_iUnion₂.2 ⟨w, ⟨z, hw, hz⟩, hw⟩
  set U₁ : Set unitInterval := (f '' Oᶜ)ᶜ
  have hU₁ : IsOpen U₁ := (hfc.isClosedMap _ hO.isClosed_compl).isOpen_compl
  set U₂ : Set unitInterval := ⋂ w ∈ J, f '' E.link w
  refine ⟨U₁ ∩ U₂, hU₁.inter ?_, ⟨?_, ?_⟩, ?_⟩
  · exact J.toFinite.isOpen_biInter fun w _ => hfo _ (E.isOpen w)
  · rintro ⟨z, hz, hzc⟩
    exact hz (hFO hzc)
  · refine mem_iInter₂.2 fun w hw => ?_
    obtain ⟨z, hzw, hzc⟩ := hw
    exact ⟨z, hzw, hzc⟩
  · rintro x ⟨-, hx₂⟩ z ⟨hz₁, -⟩
    have hzO : z ∈ O := by
      by_contra h
      exact hz₁ ⟨z, h, rfl⟩
    obtain ⟨w, hwJ, hzw⟩ := mem_iUnion₂.1 hzO
    obtain ⟨y, hyw, hyx⟩ := mem_iInter₂.1 hx₂ w hwJ
    exact ⟨w, hzw, y, hyw, hyx⟩

/-- **Bing–Jones p. 182, Step 1(b)**, for any chain covering a continuous arc of continua: over a
short enough interval, a covering subchain from which neither end link can be dropped has every
link meeting every fibre. For the connected set `f ⁻¹' Icc a b` this is Bing–Jones's "irreducibly
covers" (p. 172). -/
theorem bj_step1b {X : Type*} [MetricSpace X] [CompactSpace X] {f : X → unitInterval}
    (hf : IsArcOfContinua f) (hfo : IsOpenMap f) {N : ℕ} (E : Chain X N) (hE : univ ⊆ E.union) :
    ∃ δ > 0, ∀ a b : unitInterval, a ≤ b → (b : ℝ) - a ≤ δ → ∀ u v : ℕ, u ≤ v →
      f ⁻¹' Icc a b ⊆ ⋃ (k : Fin N) (_ : u ≤ k.val ∧ k.val ≤ v), E.link k →
      ¬ f ⁻¹' Icc a b ⊆ ⋃ (k : Fin N) (_ : u + 1 ≤ k.val ∧ k.val ≤ v), E.link k →
      ¬ f ⁻¹' Icc a b ⊆ ⋃ (k : Fin N) (_ : u ≤ k.val ∧ k.val + 1 ≤ v), E.link k →
      ∀ x ∈ Icc a b, ∀ k : Fin N, u ≤ k.val → k.val ≤ v → (E.link k ∩ f ⁻¹' {x}).Nonempty := by
  classical
  choose U hUo hcU hU using exists_nhd_step1b hf.1 hfo E hE
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_univ (X := unitInterval))
    (c := U) hUo (fun c _ => mem_iUnion.2 ⟨c, hcU c⟩)
  refine ⟨δ / 2, by linarith, ?_⟩
  intro a b hab hba u v huv hcov hnu hnv x hx k huk hkv
  obtain ⟨c, hc⟩ := hleb a (mem_univ a)
  have hIcc : ∀ y ∈ Icc a b, y ∈ U c := fun y hy => hc (by
    have hy1 : (a : ℝ) ≤ y := hy.1
    have hy2 : (y : ℝ) ≤ b := hy.2
    rw [mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
    constructor <;> linarith)
  have hFx : f ⁻¹' {x} ⊆ ⋃ (k : Fin N) (_ : u ≤ k.val ∧ k.val ≤ v), E.link k := fun z hz =>
    hcov (show f z ∈ Icc a b from (mem_singleton_iff.1 hz) ▸ hx)
  -- the fibre over `x` meets the first link
  obtain ⟨z₁, hz₁, hz₁n⟩ := not_subset.1 hnu
  obtain ⟨t₁, ht₁, hzt₁⟩ := mem_iUnion₂.1 (hcov hz₁)
  have ht₁u : t₁.val = u := by
    by_contra h
    exact hz₁n (mem_iUnion₂.2 ⟨t₁, ⟨by omega, ht₁.2⟩, hzt₁⟩)
  have hmeet₁ : (E.link t₁ ∩ f ⁻¹' {x}).Nonempty := by
    by_contra hno
    obtain ⟨w, hzw, y, hyw, hyx⟩ := hU c x (hIcc x hx) z₁ (hIcc _ hz₁)
    obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.1 (hFx hyx)
    have hju : j ≠ t₁ := fun e => hno ⟨y, e ▸ hyj, hyx⟩
    have hju' : j.val ≠ u := fun e => hju (Fin.ext (e.trans ht₁u.symm))
    have h1 := (E.adjacent w j).1 ⟨y, hyw, hyj⟩
    have h2 := (E.adjacent w t₁).1 ⟨z₁, hzw, hzt₁⟩
    by_cases hwu : w = t₁
    · subst hwu; exact hno ⟨y, hyw, hyx⟩
    · have hwu' : w.val ≠ u := fun e => hwu (Fin.ext (e.trans ht₁u.symm))
      by_cases hw : u + 1 ≤ w.val ∧ w.val ≤ v
      · exact hz₁n (mem_iUnion₂.2 ⟨w, hw, hzw⟩)
      · omega
  -- the fibre over `x` meets the last link
  obtain ⟨z₂, hz₂, hz₂n⟩ := not_subset.1 hnv
  obtain ⟨t₂, ht₂, hzt₂⟩ := mem_iUnion₂.1 (hcov hz₂)
  have ht₂v : t₂.val = v := by
    by_contra h
    exact hz₂n (mem_iUnion₂.2 ⟨t₂, ⟨ht₂.1, by omega⟩, hzt₂⟩)
  have hmeet₂ : (E.link t₂ ∩ f ⁻¹' {x}).Nonempty := by
    by_contra hno
    obtain ⟨w, hzw, y, hyw, hyx⟩ := hU c x (hIcc x hx) z₂ (hIcc _ hz₂)
    obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.1 (hFx hyx)
    have hjv : j ≠ t₂ := fun e => hno ⟨y, e ▸ hyj, hyx⟩
    have hjv' : j.val ≠ v := fun e => hjv (Fin.ext (e.trans ht₂v.symm))
    have h1 := (E.adjacent w j).1 ⟨y, hyw, hyj⟩
    have h2 := (E.adjacent w t₂).1 ⟨z₂, hzw, hzt₂⟩
    by_cases hwv : w = t₂
    · subst hwv; exact hno ⟨y, hyw, hyx⟩
    · have hwv' : w.val ≠ v := fun e => hwv (Fin.ext (e.trans ht₂v.symm))
      by_cases hw : u ≤ w.val ∧ w.val + 1 ≤ v
      · exact hz₂n (mem_iUnion₂.2 ⟨w, hw, hzw⟩)
      · omega
  refine meets_all_of_meets_ends E (hf.2.2 x).2.2 t₁ t₂ ?_ hmeet₁ hmeet₂ k (by omega) (by omega)
  intro z hz
  obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.1 (hFx hz)
  exact mem_iUnion₂.2 ⟨j, ⟨by omega, by omega⟩, hzj⟩

end Step1b

end HPC.BJ59
