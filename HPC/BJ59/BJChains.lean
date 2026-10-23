import HPC.Plane.Ingram68

/-!
# Batch 199, library: chains in Bing–Jones's sense (commission 199, §6)

* `IsBJChain` (Bing–Jones p. 172: nonadjacent links at positive distance);
* `exists_bjChain_shrink`: a chain covering a continuum `K`, each link meeting `K`, shrinks to a
  chain in Bing–Jones's sense with the same properties, the closure of each new link inside the old
  link, and given compact subsets of the old links kept inside the new ones (Lebesgue number,
  thickenings of compact sets; adjacent links still meet because `K` is connected).
-/

namespace HPC.BJ59

open Set Topology Metric Filter

variable {X : Type*} [MetricSpace X]

/-- **A chain in Bing–Jones's sense** (p. 172): nonadjacent links are at positive distance. -/
def IsBJChain {n : ℕ} (D : Chain X n) : Prop :=
  ∀ i j : Fin n, 1 < ((i : ℤ) - j).natAbs →
    ∃ δ > 0, ∀ x ∈ D.link i, ∀ y ∈ D.link j, δ ≤ dist x y

/-- Open sets indexed by `Fin n`, covering a preconnected `K`, each meeting `K`, with nonadjacent
ones disjoint: adjacent ones meet. -/
theorem adjacent_meet_of_cover {K : Set X} (hK : IsPreconnected K) {n : ℕ} (U : Fin n → Set X)
    (hU : ∀ i, IsOpen (U i)) (hKU : K ⊆ ⋃ i, U i) (hUK : ∀ i, (U i ∩ K).Nonempty)
    (hdisj : ∀ i j : Fin n, 1 < ((i : ℤ) - j).natAbs → U i ∩ U j = ∅) (i j : Fin n)
    (hij : j.val = i.val + 1) : (U i ∩ U j).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  set A := ⋃ (k : Fin n) (_ : k.val ≤ i.val), U k
  set B := ⋃ (k : Fin n) (_ : i.val < k.val), U k
  have hA : IsOpen A := isOpen_iUnion fun k => isOpen_iUnion fun _ => hU k
  have hB : IsOpen B := isOpen_iUnion fun k => isOpen_iUnion fun _ => hU k
  have hcov : K ⊆ A ∪ B := fun x hx => by
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hKU hx)
    by_cases h : k.val ≤ i.val
    · exact Or.inl (mem_iUnion₂.2 ⟨k, h, hk⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨k, by omega, hk⟩)
  obtain ⟨a, ha, haK⟩ := hUK i
  obtain ⟨b, hb, hbK⟩ := hUK j
  obtain ⟨x, -, hxA, hxB⟩ := hK A B hA hB hcov ⟨a, haK, mem_iUnion₂.2 ⟨i, le_rfl, ha⟩⟩
    ⟨b, hbK, mem_iUnion₂.2 ⟨j, by omega, hb⟩⟩
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hxA
  obtain ⟨l, hl, hxl⟩ := mem_iUnion₂.1 hxB
  by_cases h : 1 < ((k : ℤ) - l).natAbs
  · have := hdisj k l h
    exact (this ▸ ⟨hxk, hxl⟩ : x ∈ (∅ : Set X))
  · have hk' : k = i := Fin.ext (by omega)
    have hl' : l = j := Fin.ext (by omega)
    subst hk' hl'
    exact (hne ▸ ⟨hxk, hxl⟩ : x ∈ (∅ : Set X))

/-- **Shrinking a family of open sets to a chain in Bing–Jones's sense.** Open sets `V i` covering a
continuum `K`, each meeting `K`, with the traces on `K` (enlarged by given compact sets `C i ⊆ V i`)
of nonadjacent ones disjoint, shrink to a chain in Bing–Jones's sense. -/
theorem exists_bjChain_shrink' {K : Set X} (hK : Fold.Q78.IsContinuum K) {n : ℕ}
    (V : Fin n → Set X) (hV : ∀ i, IsOpen (V i)) (hKD : K ⊆ ⋃ i, V i)
    (hDK : ∀ i, (V i ∩ K).Nonempty) (C : Fin n → Set X)
    (hC : ∀ i, IsCompact (C i) ∧ C i ⊆ V i)
    (hdisj : ∀ i j : Fin n, 1 < ((i : ℤ) - j).natAbs →
      Disjoint ((V i ∩ K) ∪ C i) ((V j ∩ K) ∪ C j)) :
    ∃ D' : Chain X n, IsBJChain D' ∧ K ⊆ D'.union ∧ (∀ i, (D'.link i ∩ K).Nonempty) ∧
      ∀ i, closure (D'.link i) ⊆ V i ∧ C i ⊆ D'.link i := by
  classical
  -- a Lebesgue number and compact pieces `Ki i ⊆ D.link i` covering `K`
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hK.1 hV hKD
  choose p hpD hpK using hDK
  set Ki : Fin n → Set X := fun i => (K \ thickening (δ / 2) (V i)ᶜ) ∪ C i ∪ {p i}
  have hKic : ∀ i, IsCompact (Ki i) := fun i =>
    ((hK.1.diff isOpen_thickening).union (hC i).1).union isCompact_singleton
  have hKiD : ∀ i, Ki i ⊆ V i := fun i x hx => by
    rcases hx with (⟨-, hx⟩ | hx) | hx
    · by_contra h
      exact hx (self_subset_thickening (by linarith) _ h)
    · exact (hC i).2 hx
    · rw [mem_singleton_iff.1 hx]; exact hpD i
  have hKcov : K ⊆ ⋃ i, Ki i := fun x hx => by
    obtain ⟨i, hi⟩ := hleb x hx
    refine mem_iUnion.2 ⟨i, Or.inl (Or.inl ⟨hx, fun h => ?_⟩)⟩
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 h
    exact hy (hi (mem_ball'.2 (by linarith)))
  have hKiV : ∀ i, Ki i ⊆ (V i ∩ K) ∪ C i := fun i x hx => by
    rcases hx with (⟨hxK, hxT⟩ | hx) | hx
    · exact Or.inl ⟨hKiD i (Or.inl (Or.inl ⟨hxK, hxT⟩)), hxK⟩
    · exact Or.inr hx
    · rw [mem_singleton_iff.1 hx]; exact Or.inl ⟨hpD i, hpK i⟩
  have hdisjD : ∀ i j : Fin n, 1 < ((i : ℤ) - j).natAbs → Disjoint (Ki i) (Ki j) :=
    fun i j hij => (hdisj i j hij).mono (hKiV i) (hKiV j)
  -- radii
  choose ρi hρi hρiD using fun i => (hKic i).exists_cthickening_subset_open (hV i) (hKiD i)
  have hsep : ∀ i j : Fin n, ∃ ε > 0, 1 < ((i : ℤ) - j).natAbs →
      Disjoint (thickening ε (Ki i)) (thickening ε (Ki j)) := by
    intro i j
    by_cases h : 1 < ((i : ℤ) - j).natAbs
    · obtain ⟨ε, hε, hd⟩ := (hdisjD i j h).exists_thickenings (hKic i) (hKic j).isClosed
      exact ⟨ε, hε, fun _ => hd⟩
    · exact ⟨1, one_pos, fun h' => absurd h' h⟩
  choose εs hεs hεsd using hsep
  obtain ⟨ρ, hρ, hρle⟩ : ∃ ρ > 0, (∀ i, ρ ≤ ρi i) ∧ ∀ i j, 2 * ρ ≤ εs i j := by
    have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ i, ρ ≤ ρi i := eventually_all.2 fun i =>
      Filter.eventually_of_mem (Ioo_mem_nhdsGT (hρi i)) fun _ h => h.2.le
    have h2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ i j, 2 * ρ ≤ εs i j := eventually_all.2 fun i =>
      eventually_all.2 fun j => Filter.eventually_of_mem (Ioo_mem_nhdsGT (by linarith [hεs i j] :
        (0 : ℝ) < εs i j / 2)) fun _ h => by linarith [h.2]
    have h0 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ := self_mem_nhdsWithin
    obtain ⟨ρ, hρ, h1, h2⟩ := (h0.and (h1.and h2)).exists
    exact ⟨ρ, hρ, h1, h2⟩
  set L : Fin n → Set X := fun i => thickening ρ (Ki i)
  have hLo : ∀ i, IsOpen (L i) := fun i => isOpen_thickening
  have hsub : ∀ i, Ki i ⊆ L i := fun i => self_subset_thickening hρ _
  have hpL : ∀ i, p i ∈ L i := fun i => hsub i (Or.inr rfl)
  have hBJ : ∀ i j : Fin n, 1 < ((i : ℤ) - j).natAbs →
      ∀ x ∈ L i, ∀ y ∈ L j, ρ ≤ dist x y := by
    intro i j hij x hx y hy
    by_contra hlt
    push_neg at hlt
    obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.1 hx
    obtain ⟨w, hw, hyw⟩ := mem_thickening_iff.1 hy
    have h1 : y ∈ thickening (εs i j) (Ki i) :=
      mem_thickening_iff.2 ⟨z, hz, by linarith [dist_triangle y x z, dist_comm x y, hρle.2 i j]⟩
    have h2 : y ∈ thickening (εs i j) (Ki j) :=
      mem_thickening_iff.2 ⟨w, hw, by linarith [hρle.2 i j]⟩
    exact Set.disjoint_left.1 (hεsd i j hij) h1 h2
  have hLdisj : ∀ i j : Fin n, 1 < ((i : ℤ) - j).natAbs → L i ∩ L j = ∅ := by
    intro i j hij
    refine eq_empty_of_forall_notMem fun x ⟨hxi, hxj⟩ => ?_
    have := hBJ i j hij x hxi x hxj
    rw [dist_self] at this
    linarith
  have hKL : K ⊆ ⋃ i, L i := fun x hx => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hKcov hx)
    exact mem_iUnion.2 ⟨i, hsub i hi⟩
  have hLK : ∀ i, (L i ∩ K).Nonempty := fun i => ⟨p i, hpL i, hpK i⟩
  let D' : Chain X n :=
    { link := L
      isOpen := hLo
      adjacent := fun i j => by
        constructor
        · intro h
          by_contra h'
          push_neg at h'
          rw [hLdisj i j h'] at h
          exact not_nonempty_empty h
        · intro h
          rcases lt_trichotomy i.val j.val with hlt | heq | hgt
          · exact adjacent_meet_of_cover hK.2.2 L hLo hKL hLK hLdisj i j (by omega)
          · have : i = j := Fin.ext heq
            subst this
            exact ⟨p i, hpL i, hpL i⟩
          · rw [inter_comm]
            exact adjacent_meet_of_cover hK.2.2 L hLo hKL hLK hLdisj j i (by omega) }
  refine ⟨D', fun i j hij => ⟨ρ, hρ, hBJ i j hij⟩, hKL, hLK, fun i => ⟨?_, ?_⟩⟩
  · exact (closure_thickening_subset_cthickening _ _).trans
      ((cthickening_mono (hρle.1 i) _).trans (hρiD i))
  · exact (subset_union_right.trans subset_union_left).trans (hsub i)


/-- **Shrinking to a chain in Bing–Jones's sense** (Barrett's argument, as in
`exists_taut_epsChain`), keeping given compact sets inside given links. -/
theorem exists_bjChain_shrink {K : Set X} (hK : Fold.Q78.IsContinuum K) {n : ℕ} (D : Chain X n)
    (hKD : K ⊆ D.union) (hDK : ∀ i, (D.link i ∩ K).Nonempty) (C : Fin n → Set X)
    (hC : ∀ i, IsCompact (C i) ∧ C i ⊆ D.link i) :
    ∃ D' : Chain X n, IsBJChain D' ∧ K ⊆ D'.union ∧ (∀ i, (D'.link i ∩ K).Nonempty) ∧
      ∀ i, closure (D'.link i) ⊆ D.link i ∧ C i ⊆ D'.link i := by
  refine exists_bjChain_shrink' hK D.link D.isOpen hKD hDK C hC fun i j hij => ?_
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hi : x ∈ D.link i := by rcases hxi with h | h; exacts [h.1, (hC i).2 h]
  have hj : x ∈ D.link j := by rcases hxj with h | h; exacts [h.1, (hC j).2 h]
  have := (D.adjacent i j).1 ⟨x, hi, hj⟩
  omega

end HPC.BJ59
