import HPC.Jones.Jones49Sep
import HPC.Jones.Moore22
import HPC.Jones.Moore22T4

/-!
# Batch 150: Whyburn's cut point-order theorems; Moore 1922 (property S)

The batch-150 skeleton, with its Whyburn items proved here (statements verbatim). The Moore 1922
items are split off: definitions and Theorems 1–3 in `HPC/Jones/Moore22.lean`, Theorem 4 (open, kept
as a comment; see `OPEN.md`) and its proved parts in `HPC/Jones/Moore22T4.lean`. The original
skeleton is `doc/batches/skeletons/Jones49B-batch150.lean`.

Sources (page images, 150–200 dpi):
* Whyburn, *Analytic Topology* (1942), Ch. III §§1–3 and 8–9, pp. 41–62
  (`doc/sources/whyburn1942.pdf`, PDF pp. 55–76). Quoted below:
  * (3.2), pp. 49–50: "CUT POINT-ORDER THEOREM. All save possibly a countable number of the cut
    points of a {connected set / generalized continuum} `M` are of {potential order / order} 2 in
    `M`."
  * (8.4), p. 60: "SEPARATING POINT-ORDER THEOREM. All save a countable number of the separating
    points of any compact metric space `K` are points of order 2 of `K`."
  * (8.41), p. 61: "All save a countable number of the separating points of any locally compact
    separable metric space `L` are points of order 2 of `L`."
  * (9.2), p. 61, as in batch 149.
* R. L. Moore, *Concerning connectedness im kleinen and a related property*, Fund. Math. 3 (1922),
  232–237 (`doc/sources/moore1922.pdf`, the scan; `doc/sources/moore1922-transcription.pdf`, my
  typeset transcription with Moore's misprints kept and editorial notes in blue).
-/

namespace HPC.Jones

open Set Topology Metric

/-! ## Whyburn, Ch. III -/

section Whyburn

variable {X : Type*} [MetricSpace X]

/-- **Whyburn (3.2) for continua** (the "generalized continuum … order" reading; Whyburn's
"generalized continuum" is a locally compact connected separable metric space, Ch. I; record it).
Here for compact metric continua, which is what (8.4) uses ("the Cut Point-Order Theorem for
continua, (3.2)"). A *cut point* of `X` is a point whose complement is not connected.

*Proof route (batch 150).* Not through Whyburn's §§2–3 as printed: a cut point of a connected space
is a separating point of `univ`, and the separating point-order theorem for open sets
(`countable_sepPoint_not_hasOrder_two`, `Jones49Sep.lean`, via the chains of `Jones49Chain.lean`)
applies. The degenerate case `{p}ᶜ = ∅` (a one-point space) contributes at most one point. -/
theorem whyburn_3_2 [CompactSpace X] [ConnectedSpace X] :
    {p : X | ¬ IsConnected ({p}ᶜ : Set X) ∧ ¬ HasOrder p 2}.Countable := by
  have hsub : {p : X | ({p}ᶜ : Set X) = ∅}.Subsingleton := by
    intro p hp q hq
    by_contra hpq
    have : q ∈ ({p}ᶜ : Set X) := fun h => hpq (h.symm)
    rw [show ({p}ᶜ : Set X) = ∅ from hp] at this
    exact this
  refine ((countable_sepPoint_not_hasOrder_two (X := X) isOpen_univ).union
    hsub.countable).mono ?_
  rintro p ⟨hpc, hno⟩
  by_cases he : ({p}ᶜ : Set X) = ∅
  · exact Or.inr he
  left
  refine ⟨?_, hno⟩
  have hne : ({p}ᶜ : Set X).Nonempty := nonempty_iff_ne_empty.2 he
  have hnp : ¬ IsPreconnected ({p}ᶜ : Set X) := fun h => hpc ⟨hne, h⟩
  simp only [IsPreconnected, not_forall, exists_prop] at hnp
  obtain ⟨u, v, hu, hv, hcov, ⟨a, hau⟩, ⟨b, hbv⟩, huv⟩ := hnp
  have hcc : connectedComponentIn (univ : Set X) p = univ := by
    rw [connectedComponentIn_univ]
    exact eq_univ_of_univ_subset (isPreconnected_univ.subset_connectedComponent (mem_univ p))
  have hc : (univ : Set X) \ {p} = {p}ᶜ := by ext; simp
  refine ⟨mem_univ p, u, v, hu, hv, by rw [hc]; exact hcov, ?_, ?_, ?_⟩
  · rw [hc, disjoint_iff_inter_eq_empty]
    rw [not_nonempty_iff_eq_empty] at huv
    rw [← huv]; ext z; simp only [mem_inter_iff]; tauto
  · rw [hcc, hc]; exact ⟨a, hau.2, hau.1⟩
  · rw [hcc, hc]; exact ⟨b, hbv.2, hbv.1⟩

/-- **Whyburn (8.4).** In a compact metric space, all but countably many separating points (in the
sense of `IsSepPointOf p univ`; compare (8.32)) are of order 2. (The case `R = univ` of
`countable_sepPoint_not_hasOrder_two`.) -/
theorem whyburn_8_4 [CompactSpace X] :
    {p : X | IsSepPointOf p univ ∧ ¬ HasOrder p 2}.Countable :=
  countable_sepPoint_not_hasOrder_two isOpen_univ

/-- **Whyburn (8.41).** The same for a locally compact separable metric space. -/
theorem whyburn_8_41 [LocallyCompactSpace X] [TopologicalSpace.SeparableSpace X] :
    {p : X | IsSepPointOf p univ ∧ ¬ HasOrder p 2}.Countable :=
  countable_sepPoint_not_hasOrder_two isOpen_univ

/-- **Whyburn (9.2)** — the statement left open in batch 149 (`OPEN.md`), restated verbatim.

Whyburn's proof: a local separating point separates every basic open set inside its open set
(`whyburn_9_1`, batch 149), and there are countably many basic open sets; apply the
separating point-order theorem to each. -/
theorem whyburn_9_2 [LocallyCompactSpace X] [TopologicalSpace.SeparableSpace X] :
    {p : X | IsLocalSepPoint p ∧ ¬ HasOrder p 2}.Countable := by
  set 𝓑 := TopologicalSpace.countableBasis X
  have hB := TopologicalSpace.isBasis_countableBasis X
  refine ((TopologicalSpace.countable_countableBasis X).biUnion fun U hU =>
    countable_sepPoint_not_hasOrder_two (TopologicalSpace.isOpen_of_mem_countableBasis hU)).mono ?_
  rintro p ⟨⟨R, hR, hpR⟩, hno⟩
  obtain ⟨U, hU𝓑, hpU, hUR⟩ := hB.exists_subset_of_mem_open hpR.1 hR
  exact mem_biUnion hU𝓑 ⟨whyburn_9_1 (TopologicalSpace.isOpen_of_mem_countableBasis hU𝓑) hpU hUR
    hpR, hno⟩

/-- **What Jones 1949 uses** — left open in batch 149, restated verbatim. From `whyburn_9_2`
through batch 149's `jones49_some_order_two_of_whyburn_9_2` (the hypothesis `ConnectedSpace X`
is not used; it is kept as in the skeleton). -/
theorem jones49_some_order_two [CompactSpace X] [ConnectedSpace X] [Uncountable X]
    (hX : IsHomogeneous X) {p : X} (hp : IsLocalSepPoint p) : ∃ q : X, HasOrder q 2 :=
  jones49_some_order_two_of_whyburn_9_2 hX hp whyburn_9_2

end Whyburn

end HPC.Jones
