import HPC.Plane.Fugate66

/-!
# Batch 101: the union of two hereditarily unicoherent continua along a continuum

The consequence of Miller's theorem that Fugate's Theorem 1 uses (`hu_union_of_snakeLike` in
`Fugate66B.lean`), proved directly: if `A`, `B` are hereditarily unicoherent continua and `A ∩ B`
is connected, then `A ∪ B` is hereditarily unicoherent. The key step
(`isPreconnected_inter_of_hu`) is that every subcontinuum `H` of `A ∪ B` meets `A` in a connected
set; it needs only that `B` is hereditarily unicoherent, and uses the separation theorem for
compact sets (`exists_closed_split_of_no_connected`, Moore's Theorem 44 form).
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **Separation of two closed sets in a compact set** (Moore, Theorem 44): if no preconnected
subset of the compact set `K` meets both of the closed sets `P, Q ⊆ K`, then `K` is the union of
two disjoint closed sets, one containing `P` and the other containing `Q`. -/
theorem exists_closed_split_of_no_connected {K P Q : Set S} (hK : IsCompact K)
    (hP : IsClosed P) (hQ : IsClosed Q) (hPK : P ⊆ K) (hQK : Q ⊆ K)
    (hno : ∀ Z ⊆ K, IsPreconnected Z → (Z ∩ P).Nonempty → (Z ∩ Q).Nonempty → False) :
    ∃ H L : Set S, IsClosed H ∧ IsClosed L ∧ H ∪ L = K ∧ Disjoint H L ∧ P ⊆ H ∧ Q ⊆ L := by
  classical
  have hsplit : ∀ p ∈ P, ∃ H L : Set S, IsCompact H ∧ IsCompact L ∧ H ∪ L = K ∧ Disjoint H L ∧
      p ∈ H ∧ H ⊆ Qᶜ := fun p hp =>
    exists_clopen_split hK (hPK hp) hQ.isOpen_compl fun Z hZ hZK hpZ z hzZ hzQ =>
      hno Z hZK hZ ⟨p, hpZ, hp⟩ ⟨z, hzZ, hzQ⟩
  choose! Hp Lp hHc hLc hHL hdisj hpH hHQ using hsplit
  obtain ⟨t, hcov⟩ := (hP.isCompact).elim_finite_subcover (fun p : P => (Lp p)ᶜ)
    (fun p => (hLc p p.2).isClosed.isOpen_compl)
    (fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, fun h => Set.disjoint_left.mp (hdisj p hp) (hpH p hp) h⟩)
  refine ⟨⋃ p ∈ t, Hp p, K ∩ ⋂ p ∈ t, Lp p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact t.finite_toSet.isClosed_biUnion fun p _ => (hHc p p.2).isClosed
  · exact hK.isClosed.inter (isClosed_biInter fun p _ => (hLc p p.2).isClosed)
  · apply Subset.antisymm
    · refine union_subset (iUnion₂_subset fun p _ => ?_) inter_subset_left
      rw [← hHL p p.2]; exact subset_union_left
    · intro x hxK
      by_cases hx : ∃ p ∈ t, x ∈ Hp p
      · obtain ⟨p, hp, hx⟩ := hx
        exact Or.inl (mem_iUnion₂.mpr ⟨p, hp, hx⟩)
      · push_neg at hx
        refine Or.inr ⟨hxK, mem_iInter₂.mpr fun p hp => ?_⟩
        rw [← hHL p p.2] at hxK
        exact hxK.resolve_left (hx p hp)
  · rw [Set.disjoint_left]
    rintro x hx ⟨-, hx'⟩
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
    exact Set.disjoint_left.mp (hdisj p p.2) hxp (mem_iInter₂.mp hx' p hp)
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hcov hx)
    refine mem_iUnion₂.mpr ⟨p, hp, ?_⟩
    have hxK := hPK hx
    rw [← hHL p p.2] at hxK
    exact hxK.resolve_right hxp
  · intro x hx
    refine ⟨hQK hx, mem_iInter₂.mpr fun p _ => ?_⟩
    have hxK := hQK hx
    rw [← hHL p p.2] at hxK
    exact hxK.resolve_left fun h => hHQ p p.2 h hx

omit [CompactSpace S] in
/-- A closed set that is not preconnected splits into two disjoint nonempty closed pieces. -/
theorem exists_closed_pieces_of_not_isPreconnected {X : Set S} (hX : IsClosed X)
    (h : ¬ IsPreconnected X) :
    ∃ P Q : Set S, IsClosed P ∧ IsClosed Q ∧ P ∪ Q = X ∧ Disjoint P Q ∧ P.Nonempty ∧
      Q.Nonempty := by
  rw [isPreconnected_closed_iff] at h
  push_neg at h
  obtain ⟨t, t', ht, ht', hXt, h1, h2, h3⟩ := h
  refine ⟨X ∩ t, X ∩ t', hX.inter ht, hX.inter ht', ?_, ?_, h1, h2⟩
  · rw [← inter_union_distrib_left]; exact inter_eq_left.mpr hXt
  · rw [Set.disjoint_left]
    rintro x ⟨hxX, hxt⟩ ⟨-, hxt'⟩
    exact (eq_empty_iff_forall_notMem.mp h3) x ⟨hxX, hxt, hxt'⟩

omit [CompactSpace S] in
/-- A preconnected set covered by two disjoint closed sets, meeting both, is impossible. -/
theorem preconnected_closed_split_false {Z P Q : Set S} (hZ : IsPreconnected Z)
    (hP : IsClosed P) (hQ : IsClosed Q) (hPQ : Disjoint P Q) (hZPQ : Z ⊆ P ∪ Q)
    (hZP : (Z ∩ P).Nonempty) (hZQ : (Z ∩ Q).Nonempty) : False := by
  obtain ⟨x, -, hxP, hxQ⟩ := isPreconnected_closed_iff.mp hZ P Q hP hQ hZPQ hZP hZQ
  exact Set.disjoint_left.mp hPQ hxP hxQ

/-- **Every subcontinuum of `A ∪ B` meets `A` in a connected set**, when `B` is hereditarily
unicoherent and `A ∩ B` is connected. If `H ∩ A = P ⊔ Q`, no continuum in `H ∩ B` meets both
`P ∩ B` and `Q ∩ B` (it would meet the continuum `A ∩ B` of `B` in a connected subset of `P ⊔ Q`);
so `H ∩ B = H₁ ⊔ L₁` with `P ∩ B ⊆ H₁`, `Q ∩ B ⊆ L₁`, and `H = (P ∪ H₁) ⊔ (Q ∪ L₁)`. -/
theorem isPreconnected_inter_of_hu {A B H : Set S} (hA : IsClosed A) (hB : Fold.Q78.IsContinuum B)
    (hBhu : IsHereditarilyUnicoherent B) (hC : IsConnected (A ∩ B)) (hH : Fold.Q78.IsContinuum H)
    (hHAB : H ⊆ A ∪ B) : IsPreconnected (H ∩ A) := by
  by_contra hcon
  obtain ⟨P, Q, hP, hQ, hPQ, hdisj, hPne, hQne⟩ :=
    exists_closed_pieces_of_not_isPreconnected (hH.1.isClosed.inter hA) hcon
  have hPA : P ⊆ H ∩ A := hPQ ▸ subset_union_left
  have hQA : Q ⊆ H ∩ A := hPQ ▸ subset_union_right
  have hCc : Fold.Q78.IsContinuum (A ∩ B) := ⟨hB.1.inter_left hA, hC⟩
  obtain ⟨H₁, L₁, hH₁, hL₁, hHL, hHLd, hPH, hQL⟩ :=
    exists_closed_split_of_no_connected (K := H ∩ B) (P := P ∩ B) (Q := Q ∩ B)
      (hH.1.inter_right hB.1.isClosed) (hP.inter hB.1.isClosed) (hQ.inter hB.1.isClosed)
      (fun x hx => ⟨(hPA hx.1).1, hx.2⟩) (fun x hx => ⟨(hQA hx.1).1, hx.2⟩)
      (fun Z hZK hZ hZP hZQ => by
        obtain ⟨p, hpZ, hpP, hpB⟩ := hZP
        obtain ⟨q, hqZ, hqQ, hqB⟩ := hZQ
        have hZc : Fold.Q78.IsContinuum (closure Z) :=
          ⟨isClosed_closure.isCompact, ⟨p, subset_closure hpZ⟩, hZ.closure⟩
        have hZB : closure Z ⊆ B :=
          closure_minimal (hZK.trans inter_subset_right) hB.1.isClosed
        have hZH : closure Z ⊆ H :=
          closure_minimal (hZK.trans inter_subset_left) hH.1.isClosed
        have hI := isContinuum_inter_of_hu hBhu hZc hCc hZB inter_subset_right
          ⟨p, subset_closure hpZ, (hPA hpP).2, hpB⟩
        refine preconnected_closed_split_false hI.2.isPreconnected hP hQ hdisj ?_
          ⟨p, ⟨subset_closure hpZ, (hPA hpP).2, hpB⟩, hpP⟩
          ⟨q, ⟨subset_closure hqZ, (hQA hqQ).2, hqB⟩, hqQ⟩
        rintro x ⟨hxZ, hxA, -⟩
        have : x ∈ H ∩ A := ⟨hZH hxZ, hxA⟩
        rwa [← hPQ] at this)
  have hHL' : H ⊆ (P ∪ H₁) ∪ (Q ∪ L₁) := by
    intro x hx
    rcases hHAB hx with hxA | hxB
    · have : x ∈ P ∪ Q := hPQ ▸ ⟨hx, hxA⟩
      rcases this with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    · have : x ∈ H₁ ∪ L₁ := hHL ▸ ⟨hx, hxB⟩
      rcases this with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
  have hL₁B : L₁ ⊆ B := fun x hx => by
    have : x ∈ H₁ ∪ L₁ := Or.inr hx
    rw [hHL] at this; exact this.2
  have hH₁B : H₁ ⊆ B := fun x hx => by
    have : x ∈ H₁ ∪ L₁ := Or.inl hx
    rw [hHL] at this; exact this.2
  refine preconnected_closed_split_false hH.2.isPreconnected (hP.union hH₁) (hQ.union hL₁) ?_ hHL'
    ⟨_, (hPA hPne.some_mem).1, Or.inl hPne.some_mem⟩
    ⟨_, (hQA hQne.some_mem).1, Or.inl hQne.some_mem⟩
  rw [Set.disjoint_left]
  rintro x (hxP | hxH) (hxQ | hxL)
  · exact Set.disjoint_left.mp hdisj hxP hxQ
  · exact Set.disjoint_left.mp hHLd (hPH ⟨hxP, hL₁B hxL⟩) hxL
  · exact Set.disjoint_left.mp hHLd hxH (hQL ⟨hxQ, hH₁B hxH⟩)
  · exact Set.disjoint_left.mp hHLd hxH hxL

omit [CompactSpace S] in
/-- Two closed sets covering a preconnected set, both meeting it, intersect on it. -/
theorem inter_nonempty_of_cover {Z P Q : Set S} (hZ : IsPreconnected Z) (hP : IsClosed P)
    (hQ : IsClosed Q) (hZPQ : Z ⊆ P ∪ Q) (hZP : (Z ∩ P).Nonempty) (hZQ : (Z ∩ Q).Nonempty) :
    (Z ∩ (P ∩ Q)).Nonempty :=
  isPreconnected_closed_iff.mp hZ P Q hP hQ hZPQ hZP hZQ

/-- **The union of two hereditarily unicoherent continua meeting in a connected set is
hereditarily unicoherent.** For subcontinua `H`, `L` of `A ∪ B`, `H ∩ L ∩ A` and `H ∩ L ∩ B` are
connected (`isPreconnected_inter_of_hu`); if they were disjoint, `(H ∩ A) ∪ (L ∩ A)` would meet the
continuum `A ∩ B` in the two disjoint closed sets `H ∩ A ∩ B`, `L ∩ A ∩ B`. -/
theorem isHereditarilyUnicoherent_union {A B : Set S} (hA : Fold.Q78.IsContinuum A)
    (hB : Fold.Q78.IsContinuum B) (hAhu : IsHereditarilyUnicoherent A)
    (hBhu : IsHereditarilyUnicoherent B) (hC : IsConnected (A ∩ B)) :
    IsHereditarilyUnicoherent (A ∪ B) := by
  have hC' : IsConnected (B ∩ A) := by rwa [inter_comm]
  have hCc : Fold.Q78.IsContinuum (A ∩ B) := ⟨hB.1.inter_left hA.1.isClosed, hC⟩
  intro K hKAB hK _ H L hH hL hHL
  have hHK : H ⊆ K := hHL ▸ subset_union_left
  have hLK : L ⊆ K := hHL ▸ subset_union_right
  have hHAB := hHK.trans hKAB
  have hLAB := hLK.trans hKAB
  -- `H ∩ L ≠ ∅`
  obtain ⟨z, -, hzH, hzL⟩ := inter_nonempty_of_cover hK.2.isPreconnected hH.1.isClosed
    hL.1.isClosed hHL.symm.subset (by
      obtain ⟨x, hx⟩ := hH.2.nonempty; exact ⟨x, hHK hx, hx⟩) (by
      obtain ⟨x, hx⟩ := hL.2.nonempty; exact ⟨x, hLK hx, hx⟩)
  -- the four pieces are connected
  have pA : ∀ {X : Set S}, Fold.Q78.IsContinuum X → X ⊆ A ∪ B → (X ∩ A).Nonempty →
      Fold.Q78.IsContinuum (X ∩ A) := fun hX hXAB hne =>
    ⟨hX.1.inter_right hA.1.isClosed, hne, isPreconnected_inter_of_hu hA.1.isClosed hB hBhu hC hX
      hXAB⟩
  have pB : ∀ {X : Set S}, Fold.Q78.IsContinuum X → X ⊆ A ∪ B → (X ∩ B).Nonempty →
      Fold.Q78.IsContinuum (X ∩ B) := fun hX hXAB hne =>
    ⟨hX.1.inter_right hB.1.isClosed, hne, isPreconnected_inter_of_hu hB.1.isClosed hA hAhu hC' hX
      (hXAB.trans (union_comm A B).subset)⟩
  have eA : ∀ {X Y : Set S}, (X ∩ A) ∩ (Y ∩ A) = X ∩ Y ∩ A := fun {X Y} => by
    ext x; simp only [mem_inter_iff]; tauto
  have eB : ∀ {X Y : Set S}, (X ∩ B) ∩ (Y ∩ B) = X ∩ Y ∩ B := fun {X Y} => by
    ext x; simp only [mem_inter_iff]; tauto
  have hsplit : H ∩ L = (H ∩ L ∩ A) ∪ (H ∩ L ∩ B) := by
    ext x
    constructor
    · intro hx
      rcases hHAB hx.1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (h | h); exacts [h.1, h.1]
  by_cases hXA : (H ∩ L ∩ A).Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty] at hXA
    rw [hsplit, hXA, empty_union, ← eB]
    have hXB : (H ∩ L ∩ B).Nonempty := by
      obtain ⟨x, hx⟩ := (⟨z, hzH, hzL⟩ : (H ∩ L).Nonempty)
      rw [hsplit, hXA, empty_union] at hx; exact ⟨x, hx⟩
    rw [← eB] at hXB
    exact (isContinuum_inter_of_hu hBhu (pB hH hHAB (hXB.mono (by
      intro x hx; exact hx.1))) (pB hL hLAB (hXB.mono (by intro x hx; exact hx.2)))
      inter_subset_right inter_subset_right hXB).2
  have hcA : IsConnected (H ∩ L ∩ A) := by
    rw [← eA] at hXA ⊢
    exact (isContinuum_inter_of_hu hAhu (pA hH hHAB (hXA.mono (fun x hx => hx.1)))
      (pA hL hLAB (hXA.mono (fun x hx => hx.2))) inter_subset_right inter_subset_right hXA).2
  by_cases hXB : (H ∩ L ∩ B).Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty] at hXB
    rw [hsplit, hXB, union_empty]; exact hcA
  have hcB : IsConnected (H ∩ L ∩ B) := by
    rw [← eB] at hXB ⊢
    exact (isContinuum_inter_of_hu hBhu (pB hH hHAB (hXB.mono (fun x hx => hx.1)))
      (pB hL hLAB (hXB.mono (fun x hx => hx.2))) inter_subset_right inter_subset_right hXB).2
  by_cases hXAB : ((H ∩ L ∩ A) ∩ (H ∩ L ∩ B)).Nonempty
  · rw [hsplit]
    obtain ⟨x, hxA, hxB⟩ := hXAB
    exact ⟨⟨x, Or.inl hxA⟩, hcA.2.union x hxA hxB hcB.2⟩
  exfalso
  -- `H` and `L` each meet `A ∩ B`, in disjoint sets
  obtain ⟨a, ⟨haH, haL⟩, haA⟩ := hXA
  obtain ⟨b, ⟨hbH, hbL⟩, hbB⟩ := hXB
  have meetC : ∀ {X : Set S}, Fold.Q78.IsContinuum X → X ⊆ A ∪ B → (X ∩ A).Nonempty →
      (X ∩ B).Nonempty → (X ∩ (A ∩ B)).Nonempty := fun hX hXAB h1 h2 =>
    inter_nonempty_of_cover hX.2.isPreconnected hA.1.isClosed hB.1.isClosed hXAB h1 h2
  obtain ⟨h₀, hh₀H, hh₀C⟩ := meetC hH hHAB ⟨a, haH, haA⟩ ⟨b, hbH, hbB⟩
  obtain ⟨l₀, hl₀L, hl₀C⟩ := meetC hL hLAB ⟨a, haL, haA⟩ ⟨b, hbL, hbB⟩
  have hHA := pA hH hHAB ⟨a, haH, haA⟩
  have hLA := pA hL hLAB ⟨a, haL, haA⟩
  have hU : Fold.Q78.IsContinuum ((H ∩ A) ∪ (L ∩ A)) :=
    isContinuum_union hHA hLA ⟨a, ⟨haH, haA⟩, haL, haA⟩
  have hI := isContinuum_inter_of_hu hAhu hU hCc (union_subset inter_subset_right
    inter_subset_right) inter_subset_left ⟨h₀, Or.inl ⟨hh₀H, hh₀C.1⟩, hh₀C⟩
  refine preconnected_closed_split_false hI.2.isPreconnected (hH.1.isClosed.inter hCc.1.isClosed)
    (hL.1.isClosed.inter hCc.1.isClosed) ?_ ?_ ⟨h₀, ⟨Or.inl ⟨hh₀H, hh₀C.1⟩, hh₀C⟩, hh₀H, hh₀C⟩
    ⟨l₀, ⟨Or.inr ⟨hl₀L, hl₀C.1⟩, hl₀C⟩, hl₀L, hl₀C⟩
  · rw [Set.disjoint_left]
    rintro x ⟨hxH, hxA, hxB⟩ ⟨hxL, -, -⟩
    exact hXAB ⟨x, ⟨⟨hxH, hxL⟩, hxA⟩, ⟨hxH, hxL⟩, hxB⟩
  · rintro x ⟨hxU | hxU, hxC⟩
    · exact Or.inl ⟨hxU.1, hxC⟩
    · exact Or.inr ⟨hxU.1, hxC⟩

end HPC.Plane
