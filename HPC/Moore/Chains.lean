import HPC.Moore.Basic

/-!
# Moore, F.A. (1916), §3: Theorem 10 (simple chains) (batch 137, item B)

Moore's proof of Theorem 10 joins `A` to a point `A₁` by a simple chain, appends a region `R`
through `A₁` and `B₁`, and keeps "the first link of this chain that intersects `R`". As written
this can fail to be simple (`A ∈ R`, or `B₁` in an earlier link). We separate the two steps:

* a *weak chain* from `A` to `B` (`IsWeakChain`): a nonempty list of sets, `A` in the first, `B`
  in the last, consecutive members meeting;
* `exists_simpleChain_sublist`: every weak chain of regions from `A` to `B ≠ A` has a sublist
  which is a simple chain — a shortest such sublist is simple, since any violation of (1)–(3)
  gives a shorter one by cutting off a head, a tail, or a middle segment.

Theorem 10 is then Moore's argument for weak chains. *Axioms used: none.* The sublist form (with
the order of the links preserved) is also what Theorem 15 needs.
-/

namespace HPC.Moore

open Set

variable {S : Type*} {σ : Space S}

/-- A *weak chain from `A` to `B`*: a nonempty list of sets, `A` in the first, `B` in the last,
consecutive sets meeting. -/
def IsWeakChain (A B : S) (l : List (Set S)) : Prop :=
  ∃ h : 0 < l.length, A ∈ l[0] ∧ B ∈ l[l.length - 1] ∧
    ∀ i (hi : i + 1 < l.length), (l[i] ∩ l[i + 1]).Nonempty

theorem IsWeakChain.append_single {A B C : S} {l : List (Set S)} (hl : IsWeakChain A B l)
    {R : Set S} (hBR : B ∈ R) (hCR : C ∈ R) : IsWeakChain A C (l ++ [R]) := by
  obtain ⟨hpos, hA, hB, hch⟩ := hl
  refine ⟨by simp, ?_, ?_, ?_⟩
  · rw [List.getElem_append_left hpos]; exact hA
  · simpa using hCR
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases h : i + 1 < l.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left h]
      exact hch i h
    · have hi' : i = l.length - 1 := by omega
      subst hi'
      rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
      refine ⟨B, hB, ?_⟩
      simpa [show l.length - 1 + 1 - l.length = 0 by omega] using hBR

/-- **Simplification.** A weak chain of regions from `A` to `B ≠ A` has a sublist which is a
simple chain from `A` to `B`. Stated for a list `E` of labelled sets `f a`, so that labels
(Theorem 15's "owners") travel with the links. -/
theorem exists_simpleChain_sublist {α : Type*} (f : α → Set S) {A B : S} (hAB : A ≠ B)
    {E : List α} (hreg : ∀ a ∈ E, f a ∈ σ.region) (hE : IsWeakChain A B (E.map f)) :
    ∃ l : List α, l.Sublist E ∧ σ.IsSimpleChain A B (l.map f) := by
  classical
  have hex : ∃ n, ∃ l : List α, l.Sublist E ∧ l.length = n ∧ IsWeakChain A B (l.map f) :=
    ⟨_, E, List.Sublist.refl _, rfl, hE⟩
  obtain ⟨l, hlE, hlen, hl⟩ := Nat.find_spec hex
  have hmin : ∀ l' : List α, l'.Sublist E → IsWeakChain A B (l'.map f) →
      l.length ≤ l'.length := fun l' h₁ h₂ => hlen ▸ Nat.find_min' hex ⟨l', h₁, rfl, h₂⟩
  obtain ⟨hpos, hA0, hBl, hch⟩ := hl
  simp only [List.length_map, List.getElem_map] at hpos hA0 hBl hch
  refine ⟨l, hlE, hAB, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using List.ne_nil_of_length_pos hpos
  · intro X hX
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hX
    exact hreg a (hlE.subset ha)
  · intro i hi
    simp only [List.length_map, List.get_eq_getElem, List.getElem_map] at hi ⊢
    refine ⟨fun hA => ?_, fun h => by subst h; exact hA0⟩
    by_contra hi0
    have := hmin (l.drop i) ((List.drop_sublist _ _).trans hlE) ⟨by simp; omega, by simpa using hA,
      by
        simp only [List.length_map, List.length_drop, List.getElem_map, List.getElem_drop]
        convert hBl using 3; omega,
      by
        intro k hk
        simp only [List.length_map, List.length_drop] at hk
        simp only [List.getElem_map, List.getElem_drop]
        exact hch (i + k) (by omega)⟩
    simp at this
    omega
  · intro i hi
    simp only [List.length_map, List.get_eq_getElem, List.getElem_map] at hi ⊢
    refine ⟨fun hB => ?_, fun h => by
      have : i = l.length - 1 := by omega
      subst this; exact hBl⟩
    by_contra hil
    have := hmin (l.take (i + 1)) ((List.take_sublist _ _).trans hlE) ⟨by simp; omega,
      by simpa using hA0,
      by
        simp only [List.length_map, List.length_take, List.getElem_map, List.getElem_take]
        convert hB using 3; omega,
      by
        intro k hk
        simp only [List.length_map, List.length_take] at hk
        simp only [List.getElem_map, List.getElem_take]
        exact hch k (by omega)⟩
    simp at this
    omega
  · intro i j hi hj hij
    simp only [List.length_map, List.get_eq_getElem, List.getElem_map] at hi hj ⊢
    refine ⟨fun hmeet => ?_, fun h => by subst h; exact hch i hj⟩
    by_contra hji
    have hsub : (l.take (i + 1) ++ l.drop j).Sublist l := by
      have := (List.Sublist.refl (l.take (i + 1))).append
        (List.drop_sublist_drop_left l (show i + 1 ≤ j by omega))
      rwa [List.take_append_drop] at this
    have hlen' : (l.take (i + 1) ++ l.drop j).length = i + 1 + (l.length - j) := by
      simp; omega
    set L := l.take (i + 1) ++ l.drop j with hL
    have hget1 : ∀ k (hk : k < i + 1) (hk' : k < L.length), L[k] = l[k]'(by omega) := by
      intro k hk hk'
      show (l.take (i + 1) ++ l.drop j)[k] = _
      rw [List.getElem_append_left (by simp; omega), List.getElem_take]
    have hget2 : ∀ k (hk : i + 1 ≤ k) (hk' : k < L.length),
        L[k] = l[j + (k - (i + 1))]'(by rw [hlen'] at hk'; omega) := by
      intro k hk hk'
      show (l.take (i + 1) ++ l.drop j)[k] = _
      rw [List.getElem_append_right (by simp; omega), List.getElem_drop]
      congr 1; simp; omega
    have := hmin L (hsub.trans hlE) ⟨by simp [hlen'], ?_, ?_, ?_⟩
    · rw [hlen'] at this
      omega
    · simp only [List.getElem_map]
      rw [hget1 0 (by omega)]; exact hA0
    · have hml : (List.map f L).length = i + 1 + (l.length - j) := by
        rw [List.length_map, hlen']
      simp only [List.getElem_map]
      rw [hget2 _ (by rw [hml]; omega)]
      convert hBl using 3; rw [hml]; omega
    · intro k hk
      have hml : (List.map f L).length = i + 1 + (l.length - j) := by
        rw [List.length_map, hlen']
      rw [hml] at hk
      simp only [List.getElem_map]
      by_cases hk1 : k + 1 < i + 1
      · rw [hget1 k (by omega), hget1 (k + 1) hk1]
        exact hch k (by omega)
      · by_cases hk2 : k = i
        · subst hk2
          rw [hget1 k (by omega), hget2 (k + 1) (by omega)]
          convert hmeet using 3; congr 1; omega
        · rw [hget2 k (by omega), hget2 (k + 1) (by omega)]
          convert hch (j + (k - (i + 1))) (by omega) using 3; congr 1; omega

/-- **Theorem 10.** If `M` is connected, `A ≠ B` are in `M`, and `G` is a set of regions covering
`M`, there is a simple chain from `A` to `B` with every link in `G`. *Axioms used: none.*
Moore's proof, run with weak chains: the points joined to `A` by a weak `G`-chain form a set `S_A`
which, if `B ∉ S_A`, is separated from the rest of `M`; then `exists_simpleChain_sublist`. -/
theorem fa_theorem10 {M : Set S} (hM : σ.IsConn M) {A B : S} (hA : A ∈ M) (hB : B ∈ M)
    (hAB : A ≠ B) {G : Set (Set S)} (hG : σ.Covers G M) :
    ∃ R : List (Set S), σ.IsSimpleChain A B R ∧ ∀ X ∈ R, X ∈ G := by
  obtain ⟨hGreg, hMG⟩ := hG
  set SA : Set S := {P ∈ M | ∃ l : List (Set S), (∀ X ∈ l, X ∈ G) ∧ IsWeakChain A P l}
  have hAS : A ∈ SA := by
    obtain ⟨R, hRG, hAR⟩ := hMG hA
    exact ⟨hA, [R], by simpa using hRG, by simp, by simpa using hAR, by simpa using hAR,
      fun i hi => by simp at hi⟩
  have hBS : B ∈ SA := by
    by_contra hBS
    rcases hM SA (M \ SA) (union_diff_cancel fun x hx => hx.1) disjoint_sdiff_right ⟨A, hAS⟩
        ⟨B, hB, hBS⟩ with ⟨X, hX, hlim⟩ | ⟨X, hX, hlim⟩
    · obtain ⟨R, hRG, hXR⟩ := hMG hX.1
      obtain ⟨Y, ⟨hYM, hYS⟩, hYR, -⟩ := hlim R (hGreg hRG) hXR
      obtain ⟨l, hlG, hl⟩ := hX.2
      refine hYS ⟨hYM, l ++ [R], fun Z hZ => ?_, hl.append_single hXR hYR⟩
      rcases List.mem_append.mp hZ with hZ | hZ
      · exact hlG Z hZ
      · rw [List.mem_singleton.mp hZ]; exact hRG
    · obtain ⟨R, hRG, hXR⟩ := hMG hX.1
      obtain ⟨Y, hYS, hYR, -⟩ := hlim R (hGreg hRG) hXR
      obtain ⟨l, hlG, hl⟩ := hYS.2
      refine hX.2 ⟨hX.1, l ++ [R], fun Z hZ => ?_, hl.append_single hYR hXR⟩
      rcases List.mem_append.mp hZ with hZ | hZ
      · exact hlG Z hZ
      · rw [List.mem_singleton.mp hZ]; exact hRG
  obtain ⟨-, l, hlG, hl⟩ := hBS
  obtain ⟨l', hl'l, hl'⟩ := exists_simpleChain_sublist (σ := σ) id hAB
    (fun a ha => hGreg (hlG a ha)) (by simpa using hl)
  exact ⟨l', by simpa using hl', fun X hX => hlG X (hl'l.subset (by simpa using hX))⟩

end HPC.Moore
