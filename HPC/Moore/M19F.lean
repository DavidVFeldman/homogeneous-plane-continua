import HPC.Moore.M19CD2

/-!
# Moore 1919, Theorem F (batch 143, item C)

Theorem F (p. 176): there is a sequence of closed curves `J₁, J₂, …` such that every point lies
within one of them and `Jₙ₊₁` encloses `Jₙ`.

The proof follows Moore's ingredients (Theorems 36, 15/16 and 42), organised as:

* `preconnectedSpace` — the space is connected (Axioms 1, 3, 5₁);
* `exists_curve_about_compact` — every compact (closed and bounded) set lies within some closed
  curve. A finite family of curve interiors from Theorem 36 covers the set; arcs (Theorem 15) tie
  them to a base point, giving a compact connected set; a second finite family of interiors, each
  meeting that set, has connected union, and Theorem 42 encloses it. This is the point recorded in
  the ledger: Theorem 42 needs the union of the interiors to be connected;
* `m19_theoremF_proof` — the sequence, built on Axiom 1's fundamental regions `Kₙ`: `Jₙ₊₁` is a
  curve about `Jₙ + Iₙ + Kₙ₊₁'`.
-/

namespace HPC.Moore

open Set Topology

variable {S : Type*} {σ : Space S}

section M19F

variable (h1 : σ.Axiom1) (h3 : σ.Axiom3)
include h1 h3

/-- The space is connected. *Axioms used: 1, 3, 5₁.* A region `R'` about `x` whose closure misses
a second point `x'` of a region inside one part of a separation would have a disconnected
exterior, against Axiom 3. -/
theorem preconnectedSpace (h51 : Space.Axiom5₁ (S := S)) : @PreconnectedSpace S σ.topology := by
  letI := σ.topology
  haveI := t2Space h1
  refine ⟨?_⟩
  rintro u v hu hv huv ⟨x, -, hxu⟩ ⟨y, -, hyv⟩
  by_contra hne
  have hdisj : u ∩ v = ∅ := by
    by_contra h'
    obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.mpr h'
    exact hne ⟨z, mem_univ z, hz⟩
  obtain ⟨R, hR, hxR, hRu⟩ := exists_region_closure_subset h1 hu hxu
  obtain ⟨x', hx'R, hx'x⟩ := exists_ne_of_region h1 h3 h51 hR hxR
  obtain ⟨R', hR', hxR', hR'cl⟩ := exists_region_closure_subset h1
    ((isOpen_region hR).sdiff isClosed_singleton) (show x ∈ R \ {x'} from ⟨hxR, hx'x.symm⟩)
  have hE := hext_region h1 h3 R' hR'
  have hcu : closure R' ⊆ u := hR'cl.trans (diff_subset.trans (subset_closure.trans hRu))
  have hyE : y ∈ (closure R')ᶜ := fun hy => by
    have := hcu hy
    have : y ∈ u ∩ v := ⟨this, hyv⟩
    rw [hdisj] at this; exact this
  have hx'E : x' ∈ (closure R')ᶜ := fun hx' => (hR'cl hx').2 rfl
  obtain ⟨z, -, hz⟩ := hE u v hu hv (fun w _ => huv (mem_univ w))
    ⟨x', hx'E, subset_closure.trans hRu hx'R |> fun h => h⟩ ⟨y, hyE, hyv⟩
  rw [hdisj] at hz; exact hz

variable (h2 : σ.Axiom2) (h4 : σ.Axiom4) (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7)
  (h8 : σ.Axiom8)
include h2 h4 h5 h6 h7 h8

/-- Every compact set lies within a closed curve. *Axioms used: 1–8.* -/
theorem exists_curve_about_compact {M : Set S} (hM : @IsCompact S σ.topology M) :
    ∃ J I, σ.IsInteriorOf J I ∧ M ⊆ I := by
  classical
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  haveI := preconnectedSpace h1 h3 h51
  have harc := arcConn h1 h3 h4 h51 h2
  -- a curve interior about each point (Theorem 36)
  have hg : ∀ P : S, ∃ p : Set S × Set S, σ.IsInteriorOf p.1 p.2 ∧ P ∈ p.2 := fun P => by
    obtain ⟨R, hR, hPR⟩ := Space.exists_region_mem h1 P
    obtain ⟨J, -, I, hJI, hPI⟩ := fa_theorem36 h1 h2 h3 h4 h5 h6 h7 h8 hR hPR
    exact ⟨(J, I), hJI, hPI⟩
  choose g hgI hgP using hg
  obtain ⟨b, -⟩ := (show (univ : Set S).Nonempty by
    obtain ⟨a, -⟩ := h51; exact ⟨a, mem_univ a⟩)
  -- first finite cover, of `M ∪ {b}`
  obtain ⟨t, htcov⟩ := (hM.union (@isCompact_singleton _ _ b)).elim_finite_subcover
    (fun P => (g P).2) (fun P => isOpen_region (hgI P).2.1)
    (fun Q _ => mem_iUnion.mpr ⟨Q, hgP Q⟩)
  -- arcs from `b`
  have hC : ∀ P : S, ∃ C : Set S, IsCompact C ∧ IsPreconnected C ∧ b ∈ C ∧ P ∈ C := fun P => by
    by_cases hbP : b = P
    · exact ⟨{b}, isCompact_singleton, isPreconnected_singleton, rfl, hbP ▸ rfl⟩
    · obtain ⟨C, -, -, f, hf, hfr, hf0, hf1⟩ :=
        harc univ isOpen_univ isPreconnected_univ b (mem_univ b) P (mem_univ P) hbP
      refine ⟨C, hfr ▸ isCompact_range hf.continuous, hfr ▸ isPreconnected_range hf.continuous,
        hfr ▸ hf0 ▸ mem_range_self 0, hfr ▸ hf1 ▸ mem_range_self 1⟩
  choose C hCc hCp hCb hCP using hC
  set M' : Set S := ⋃ P ∈ t, (closure (g P).2 ∪ C P) with hM'
  have hM'c : IsCompact M' := t.isCompact_biUnion fun P _ =>
    (isCompact_closure_region h1 h4 (hgI P).2.1).union (hCc P)
  have hpiece : ∀ P, IsPreconnected (closure (g P).2 ∪ C P) := fun P =>
    ((hpc_region h1 h2 _ (hgI P).2.1).closure).union P (subset_closure (hgP P)) (hCP P)
      (hCp P)
  have hbM' : b ∈ M' := by
    obtain ⟨P, hP, hbP⟩ := mem_iUnion₂.mp (htcov (Or.inr rfl))
    exact mem_iUnion₂.mpr ⟨P, hP, Or.inl (subset_closure hbP)⟩
  have hM'p : IsPreconnected M' := by
    rw [hM', ← Finset.set_biUnion_coe, ← sUnion_image]
    refine isPreconnected_sUnion b _ ?_ ?_
    · rintro _ ⟨P, hP, rfl⟩
      exact Or.inr (hCb P)
    · rintro _ ⟨P, -, rfl⟩; exact hpiece P
  have hMM' : M ⊆ M' := fun Q hQ => by
    obtain ⟨P, hP, hQP⟩ := mem_iUnion₂.mp (htcov (Or.inl hQ))
    exact mem_iUnion₂.mpr ⟨P, hP, Or.inl (subset_closure hQP)⟩
  -- second finite cover, by interiors about points of `M'`
  obtain ⟨b', hb'M', hb'f, hb'cov⟩ := hM'c.elim_finite_subcover_image (b := M')
    (c := fun Q => (g Q).2) (fun Q _ => isOpen_region (hgI Q).2.1)
    (fun Q hQ => mem_iUnion₂.mpr ⟨Q, hQ, hgP Q⟩)
  have hb'ne : b'.Nonempty := by
    obtain ⟨Q, hQ, -⟩ := mem_iUnion₂.mp (hb'cov hbM'); exact ⟨Q, hQ⟩
  set G : Finset (Set S × Set S) := hb'f.toFinset.image g with hG
  have hmemG : ∀ Q ∈ b', g Q ∈ G := fun Q hQ =>
    Finset.mem_image.mpr ⟨Q, hb'f.mem_toFinset.mpr hQ, rfl⟩
  have hU : ⋃ p ∈ G, p.2 = ⋃ Q ∈ b', (g Q).2 := by
    ext z; simp only [hG, Finset.mem_image, Set.Finite.mem_toFinset, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨p, ⟨Q, hQ, rfl⟩, hz⟩; exact ⟨Q, hQ, hz⟩
    · rintro ⟨Q, hQ, hz⟩; exact ⟨g Q, ⟨Q, hQ, rfl⟩, hz⟩
  have hU' : ⋃ Q ∈ b', (g Q).2 = ⋃ Q ∈ b', ((g Q).2 ∪ M') := by
    apply Subset.antisymm
    · exact iUnion₂_mono fun Q _ => subset_union_left
    · refine iUnion₂_subset fun Q hQ => union_subset (subset_biUnion_of_mem (u := fun Q => (g Q).2) hQ) hb'cov
  have hconn : IsPreconnected (⋃ Q ∈ b', (g Q).2) := by
    rw [hU', ← sUnion_image]
    refine isPreconnected_sUnion b _ ?_ ?_
    · rintro _ ⟨Q, -, rfl⟩; exact Or.inr hbM'
    · rintro _ ⟨Q, hQ, rfl⟩
      exact (hpc_region h1 h2 _ (hgI Q).2.1).union Q (hgP Q) (hb'M' hQ) hM'p
  obtain ⟨Q₀, hQ₀⟩ := hb'ne
  obtain ⟨J, I, hJI, -, hsub⟩ := fa_theorem42 h1 h2 h3 h4 h5 h6 h7 h8 G
    (fun p hp => by
      obtain ⟨Q, -, rfl⟩ := Finset.mem_image.mp hp; exact hgI Q)
    ⟨g Q₀, hmemG Q₀ hQ₀⟩ ((isConn_iff h1).mpr (hU ▸ hconn))
  exact ⟨J, I, hJI, hMM'.trans (hb'cov.trans (iUnion₂_subset fun Q hQ => hsub (g Q) (hmemG Q hQ)))⟩

/-- **Theorem F** (p. 176), as shaped in the skeleton (`HPC/Moore/M19EF.lean`). *Axioms used:
1–8.* `Jₙ₊₁` is a closed curve about the compact set `Jₙ + Iₙ + Kₙ₊₁'`, where `K` is Axiom 1's
fundamental sequence; every point lies in some `Kₙ`. -/
theorem m19_theoremF_proof :
    ∃ Jn In : ℕ → Set S, (∀ n, σ.IsInteriorOf (Jn n) (In n)) ∧ (∀ P, ∃ n, P ∈ In n) ∧
      ∀ n, Jn n ∪ In n ⊆ In (n + 1) := by
  classical
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨K, hK, hK1, -⟩ := id h1
  have hex : ∀ M : Set S, ∃ p : Set S × Set S,
      IsCompact M → σ.IsInteriorOf p.1 p.2 ∧ M ⊆ p.2 := fun M => by
    by_cases hM : IsCompact M
    · obtain ⟨J, I, hJI, hMI⟩ := exists_curve_about_compact h1 h3 h2 h4 h5 h6 h7 h8 hM
      exact ⟨(J, I), fun _ => ⟨hJI, hMI⟩⟩
    · exact ⟨(∅, ∅), fun h => absurd h hM⟩
  choose F hF using hex
  let c : ℕ → Set S × Set S := fun n => Nat.rec (F (closure (K 0)))
    (fun n p => F (closure p.2 ∪ closure (K (n + 1)))) n
  have hc0 : c 0 = F (closure (K 0)) := rfl
  have hcs : ∀ n, c (n + 1) = F (closure (c n).2 ∪ closure (K (n + 1))) := fun n => rfl
  have hmain : ∀ n, σ.IsInteriorOf (c n).1 (c n).2 ∧ closure (K n) ⊆ (c n).2 := by
    intro n
    induction n with
    | zero => rw [hc0]; exact hF _ (isCompact_closure_region h1 h4 (hK 0))
    | succ n ih =>
      rw [hcs]
      have := hF (closure (c n).2 ∪ closure (K (n + 1)))
        ((isCompact_closure_region h1 h4 ih.1.2.1).union (isCompact_closure_region h1 h4 (hK _)))
      exact ⟨this.1, subset_union_right.trans this.2⟩
  refine ⟨fun n => (c n).1, fun n => (c n).2, fun n => (hmain n).1, fun P => ?_, fun n => ?_⟩
  · obtain ⟨n, -, hn⟩ := hK1 0 P
    exact ⟨n, (hmain n).2 (subset_closure hn)⟩
  · obtain ⟨-, -, -, -, -, -, -, -, hcl, -⟩ := jordan h1 h2 h3 h4 h51 h7 (hmain n).1
    have := hF (closure (c n).2 ∪ closure (K (n + 1)))
      ((isCompact_closure_region h1 h4 (hmain n).1.2.1).union
        (isCompact_closure_region h1 h4 (hK _)))
    show (c n).1 ∪ (c n).2 ⊆ (c (n + 1)).2
    rw [hcs]
    intro z hz
    apply this.2
    left
    rw [hcl]
    exact hz.symm

end M19F

end HPC.Moore
