import HPC.Plane.Atriodic51BElt

/-!
# Bing 1951, §4: supporting facts for Theorem 9 (batch 93)

* `exists_minimal_of_seq` — the Brouwer reduction theorem in the form Theorem 9 needs: a property
  of closed sets of a second-countable space that passes to intersections of decreasing
  *sequences* has minimal members below each member (Bing states inductiveness for sequences; the
  chains needed by Zorn are reduced to sequences by the Lindelöf property).
-/

namespace HPC.Plane

open Set Topology

/-- A nonempty chain of closed sets in a second-countable space has the same intersection as some
decreasing sequence of its members. -/
theorem exists_antitone_of_chain {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    {c : Set (Set X)} (hcl : ∀ s ∈ c, IsClosed s) (hch : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    ∃ d : ℕ → Set X, (∀ n, d n ∈ c) ∧ Antitone d ∧ ⋂ n, d n = ⋂₀ c := by
  classical
  obtain ⟨T, hTc, hTS, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable (compl '' c)
    (by rintro _ ⟨s, hs, rfl⟩; exact (hcl s hs).isOpen_compl)
  obtain ⟨c₀, hc₀⟩ := hne
  have hpre : compl ⁻¹' T ⊆ c := by
    intro s hs
    obtain ⟨t, ht, hts⟩ := hTS hs
    rw [compl_inj_iff] at hts
    exact hts ▸ ht
  obtain ⟨f, hf⟩ := ((hTc.preimage compl_injective).insert c₀).exists_eq_range
    (insert_nonempty _ _)
  have hfc : ∀ n, f n ∈ c := fun n => by
    have : f n ∈ insert c₀ (compl ⁻¹' T) := hf ▸ mem_range_self n
    rcases this with h | h
    · exact h ▸ hc₀
    · exact hpre h
  let d : ℕ → Set X := fun n => Nat.rec (f 0) (fun k dk => if f (k + 1) ⊆ dk then f (k + 1) else dk) n
  have hd0 : d 0 = f 0 := rfl
  have hds : ∀ k, d (k + 1) = if f (k + 1) ⊆ d k then f (k + 1) else d k := fun k => rfl
  have hdc : ∀ n, d n ∈ c := by
    intro n
    induction n with
    | zero => exact hfc 0
    | succ k ih => rw [hds]; split_ifs; exacts [hfc _, ih]
  have hdstep : ∀ k, d (k + 1) ⊆ d k := by
    intro k
    rw [hds]; split_ifs with h; exacts [h, subset_rfl]
  have hdf : ∀ n, d n ⊆ f n := by
    intro n
    cases n with
    | zero => exact subset_rfl
    | succ k =>
      rw [hds]; split_ifs with h
      · exact subset_rfl
      · rcases hch.total (hdc k) (hfc (k + 1)) with h' | h'
        · exact h'
        · exact absurd h' h
  have hanti : Antitone d := antitone_nat_of_succ_le hdstep
  refine ⟨d, hdc, hanti, Subset.antisymm ?_ (subset_iInter fun n => sInter_subset_of_mem (hdc n))⟩
  intro x hx
  rw [mem_sInter]
  intro s hs
  by_contra hxs
  have : x ∈ ⋃₀ (compl '' c) := ⟨sᶜ, ⟨s, hs, rfl⟩, hxs⟩
  rw [← hTU] at this
  obtain ⟨u, hu, hxu⟩ := this
  have huc : uᶜ ∈ range f := by
    rw [← hf]; exact Or.inr (by simpa using hu)
  obtain ⟨k, hk⟩ := huc
  exact (hk ▸ hdf k) (mem_iInter.mp hx k) hxu

/-- **Brouwer reduction** for a property of closed sets that passes to intersections of decreasing
sequences: below each member there is a minimal member. -/
theorem exists_minimal_of_seq {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (P : Set X → Prop) (hcl : ∀ s, P s → IsClosed s)
    (hseq : ∀ h : ℕ → Set X, (∀ n, P (h n)) → Antitone h → P (⋂ n, h n)) {s₀ : Set X}
    (h₀ : P s₀) : ∃ m ⊆ s₀, P m ∧ ∀ m', P m' → m' ⊆ m → m' = m := by
  obtain ⟨m, hms₀, hmin⟩ := zorn_superset_nonempty {s | P s ∧ s ⊆ s₀} (fun c hc hch hne => by
    obtain ⟨d, hdc, hanti, hd⟩ := exists_antitone_of_chain (fun s hs => hcl s (hc hs).1) hch hne
    obtain ⟨c₀, hc₀⟩ := hne
    refine ⟨⋂₀ c, ⟨hd ▸ hseq d (fun n => (hc (hdc n)).1) hanti,
      (sInter_subset_of_mem hc₀).trans (hc hc₀).2⟩, fun s hs => sInter_subset_of_mem hs⟩)
    s₀ ⟨h₀, subset_rfl⟩
  exact ⟨m, hms₀, hmin.prop.1, fun m' hm' hm'm =>
    Subset.antisymm hm'm (hmin.le_of_le ⟨hm', hm'm.trans hms₀⟩ hm'm)⟩

end HPC.Plane
