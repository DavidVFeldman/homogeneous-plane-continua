import HPC.HO16.SidesLib

/-!
# Batch 195, §3: Definition 9, the observations after it, Propositions 10 and 11

Part of the batch-195 skeleton `HO16C.lean` (commission 195), split under `HPC/HO16/`.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

/-! ## §3. Definition 9, the observations after it, Propositions 10 and 11 -/

section Sides

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **p. 190**: "If B is empty, then σ_B(A) is simply equal to the union of all components of G
which A intersects." -/
theorem ho16_obs9_emptyB {G A : Set E} (hG : IsPLGraph G) :
    sideOf G ∅ A = ⋃ x ∈ G, ⋃ (_ : (connectedComponentIn G x ∩ A).Nonempty),
      connectedComponentIn G x := by
  apply Subset.antisymm
  · intro z hz
    have hzG := sideOf_subset hG.isCompact.isClosed hz
    have := hG.comp_meets_of_mem_sideOf isClosed_empty hz (Set.notMem_empty z)
    rw [diff_empty] at this
    simp only [mem_iUnion]
    exact ⟨z, hzG, this, mem_connectedComponentIn hzG⟩
  · intro z hz
    unfold sideOf
    rw [diff_empty]
    exact subset_closure hz

omit [NormedSpace ℝ E] in
/-- **p. 190**: "In particular, if A = ∅ then σ_B(A) = ∅." -/
theorem ho16_obs9_emptyA (G B : Set E) : sideOf G B ∅ = ∅ := by
  simp [sideOf]

/-- **p. 190, first observation**: for `G` connected, `A`, `B` nonempty, `A` with consistent
complement relative to `B`, and any neighbourhood `V` of `B`, `σ_B(A)` is the closure of the union
of the components of `G \ B` meeting `A ∩ V`.

Shape change (batch 195): the skeleton's hypothesis `A.Nonempty` is not needed and has been
dropped. -/
theorem ho16_obs9_nhds {G A B : Set E} (hG : IsPLGraph G) (hconn : IsConnected G)
    (hA : IsPLGraph A) (hAG : A ⊆ G) (hBne : B.Nonempty)
    (hB : B ⊆ relFrontier G A) (hc : HasConsCompl G A B) {V : Set E} (hV : V ∈ 𝓝ˢ B) :
    sideOf G B A = sideOf G B (A ∩ V) := by
  obtain ⟨-, -, -, -, V', hV', hSV'⟩ := hG.sideOf_char_aux hA hAG hB hc
  have hAc : IsClosed A := hA.isCompact.isClosed
  have hBA : B ⊆ A := fun b hb => by
    have := (hB hb).1
    rwa [hAc.closure_eq] at this
  have hBfin : B.Finite := (hG.relFrontier_finite hA hAG).subset hB
  unfold sideOf
  congr 1
  ext z
  simp only [mem_iUnion]
  constructor
  · rintro ⟨x, hx, hxA, hz⟩
    refine ⟨x, hx, ?_, hz⟩
    obtain ⟨b, hbcl, hb⟩ :=
      hG.closure_comp_inter_nonempty hconn hBfin.isClosed (hBA.trans hAG) hBne hx
    have hW : V ∩ V' ∈ 𝓝 b :=
      inter_mem (mem_nhdsSet_iff_forall.1 hV b hb) (mem_nhdsSet_iff_forall.1 hV' b hb)
    obtain ⟨w, hwW, hwK⟩ := mem_closure_iff_nhds.1 hbcl _ hW
    have hwS : w ∈ sideOf G B A := comp_subset_sideOf hx hxA hwK
    have : w ∈ A ∩ V' := by rw [← hSV']; exact ⟨hwS, hwW.2⟩
    exact ⟨w, hwK, this.1, hwW.1⟩
  · rintro ⟨x, hx, ⟨w, hwK, hwA, -⟩, hz⟩
    exact ⟨x, hx, ⟨w, hwK, hwA⟩, hz⟩

/-- **p. 190, characterization, existence**: `σ_B(A)` is a closed regular set `D ⊆ G` with
`∂D = B` and `D ∩ V = A ∩ V` for some neighbourhood `V` of `B` (and `A ⊆ D`).

Shape change (batch 195): the skeleton's hypotheses `IsConnected G`, `A.Nonempty` and
`B.Nonempty` are not needed and have been dropped. -/
theorem ho16_obs9_char {G A B : Set E} (hG : IsPLGraph G)
    (hA : IsPLGraph A) (hAG : A ⊆ G)
    (hB : B ⊆ relFrontier G A) (hc : HasConsCompl G A B) :
    IsPLGraph (sideOf G B A) ∧ sideOf G B A ⊆ G ∧ A ⊆ sideOf G B A ∧
      relFrontier G (sideOf G B A) = B ∧ ∃ V ∈ 𝓝ˢ B, sideOf G B A ∩ V = A ∩ V := by
  exact hG.sideOf_char_aux hA hAG hB hc

/-- **p. 190, characterization, uniqueness**: a closed `D ⊆ G` with `∂D = B` and `D ∩ V = A ∩ V`
for some neighbourhood `V` of `B` is `σ_B(A)`.

Shape change (batch 195): the skeleton's hypothesis `A.Nonempty` is not needed and has been
dropped. -/
theorem ho16_obs9_unique {G A B : Set E} (hG : IsPLGraph G) (hconn : IsConnected G)
    (hA : IsPLGraph A) (hAG : A ⊆ G) (hBne : B.Nonempty)
    (hB : B ⊆ relFrontier G A) (hc : HasConsCompl G A B) {D : Set E} (hDG : D ⊆ G)
    (hD : IsClosed D) (hDB : relFrontier G D = B) (hDV : ∃ V ∈ 𝓝ˢ B, D ∩ V = A ∩ V) :
    D = sideOf G B A := by
  obtain ⟨-, hSG, hAS, hSB, V', hV', hSV'⟩ := hG.sideOf_char_aux hA hAG hB hc
  obtain ⟨V, hV, hDV⟩ := hDV
  have hAc : IsClosed A := hA.isCompact.isClosed
  have hBA : B ⊆ A := fun b hb => by
    have := (hB hb).1
    rwa [hAc.closure_eq] at this
  have hBfin : B.Finite := (hG.relFrontier_finite hA hAG).subset hB
  have hBG : B ⊆ G := hBA.trans hAG
  have hBc : IsClosed B := hBfin.isClosed
  have key : ∀ z ∈ G \ B, z ∈ D ↔ z ∈ sideOf G B A := by
    intro z hz
    obtain ⟨b, hbcl, hb⟩ := hG.closure_comp_inter_nonempty hconn hBc hBG hBne hz
    have hW : V ∩ V' ∈ 𝓝 b :=
      inter_mem (mem_nhdsSet_iff_forall.1 hV b hb) (mem_nhdsSet_iff_forall.1 hV' b hb)
    obtain ⟨w, hwW, hwK⟩ := mem_closure_iff_nhds.1 hbcl _ hW
    have hwiff : w ∈ D ↔ w ∈ sideOf G B A := by
      constructor
      · intro hwD
        have h1 : w ∈ A ∩ V := by rw [← hDV]; exact ⟨hwD, hwW.1⟩
        have h2 : w ∈ sideOf G B A ∩ V' := by rw [hSV']; exact ⟨h1.1, hwW.2⟩
        exact h2.1
      · intro hwS
        have h1 : w ∈ A ∩ V' := by rw [← hSV']; exact ⟨hwS, hwW.2⟩
        have h2 : w ∈ D ∩ V := by rw [hDV]; exact ⟨h1.1, hwW.1⟩
        exact h2.1
    have hz' := mem_connectedComponentIn hz
    have hD := comp_subset_or_disjoint hBc hD hDG hDB.le z
    have hS := comp_subset_or_disjoint hBc (isClosed_sideOf G B A) hSG hSB.le z
    rcases hD with hD | hD <;> rcases hS with hS | hS
    · exact ⟨fun _ => hS hz', fun _ => hD hz'⟩
    · exact absurd (hwiff.1 (hD hwK)) (Set.disjoint_left.1 hS hwK)
    · exact absurd (hwiff.2 (hS hwK)) (Set.disjoint_left.1 hD hwK)
    · exact ⟨fun h => absurd h (Set.disjoint_left.1 hD hz'),
        fun h => absurd h (Set.disjoint_left.1 hS hz')⟩
  ext z
  by_cases hzG : z ∈ G
  · by_cases hzB : z ∈ B
    · refine ⟨fun _ => hAS (hBA hzB), fun _ => ?_⟩
      have := (hDB.symm ▸ hzB : z ∈ relFrontier G D).1
      rwa [hD.closure_eq] at this
    · exact key z ⟨hzG, hzB⟩
  · exact ⟨fun h => absurd (hDG h) hzG, fun h => absurd (hSG h) hzG⟩

/-- For connected `G` and non-empty `A ⊆ G`, `σ_∅(A) = G`. -/
theorem sideOf_empty_of_connected {G A : Set E} (hG : IsPLGraph G) (hconn : IsConnected G)
    (hAG : A ⊆ G) (hAne : A.Nonempty) : sideOf G ∅ A = G := by
  rw [ho16_obs9_emptyB hG]
  apply Subset.antisymm
  · exact iUnion₂_subset fun x _ => iUnion_subset fun _ => connectedComponentIn_subset _ _
  · intro z hz
    obtain ⟨a, ha⟩ := hAne
    simp only [mem_iUnion]
    refine ⟨z, hz, ⟨a, ?_, ha⟩, mem_connectedComponentIn hz⟩
    rw [hconn.isPreconnected.connectedComponentIn hz]
    exact hAG ha

/-- **H–O Proposition 10** (p. 190). -/
theorem ho16_prop10 {G A A' B : Set E} (hG : IsPLGraph G) (hconn : IsConnected G)
    (hA : IsPLGraph A) (hA' : IsPLGraph A') (hAG : A ⊆ G) (hA'G : A' ⊆ G)
    (hAne : A.Nonempty) (hA'ne : A'.Nonempty) (hB : B ⊆ relFrontier G A ∩ relFrontier G A')
    (hc : HasConsCompl G A B) (hc' : HasConsCompl G A' B) {V : Set E} (hV : V ∈ 𝓝ˢ B)
    (hAV : A ∩ V = A' ∩ V) :
    sideOf G B A = sideOf G B A' ∧
      ∀ x ∈ G \ A, (closure (connectedComponentIn (G \ A) x) ∩ B).Nonempty →
        x ∈ G \ A' ∧ connectedComponentIn (G \ A') x = connectedComponentIn (G \ A) x := by
  have hAc : IsClosed A := hA.isCompact.isClosed
  have hBA : B ⊆ relFrontier G A := fun b hb => (hB hb).1
  have hBA' : B ⊆ relFrontier G A' := fun b hb => (hB hb).2
  have hBsub : B ⊆ A := fun b hb => by
    have := (hB hb).1.1
    rwa [hAc.closure_eq] at this
  have hBsub' : B ⊆ A' := fun b hb => by
    have := (hB hb).2.1
    rwa [hA'.isCompact.isClosed.closure_eq] at this
  have hBfin : B.Finite := (hG.relFrontier_finite hA hAG).subset hBA
  have hBc : IsClosed B := hBfin.isClosed
  have hσ : sideOf G B A = sideOf G B A' := by
    rcases B.eq_empty_or_nonempty with rfl | hBne
    · rw [sideOf_empty_of_connected hG hconn hAG hAne,
        sideOf_empty_of_connected hG hconn hA'G hA'ne]
    · rw [ho16_obs9_nhds hG hconn hA hAG hBne hBA hc hV, hAV,
        ← ho16_obs9_nhds hG hconn hA' hA'G hBne hBA' hc' hV]
  refine ⟨hσ, fun x hx hcl => ?_⟩
  obtain ⟨b, hbcl, hb⟩ := hcl
  have hbfr : b ∈ relFrontier G (_root_.connectedComponentIn (G \ A) x) :=
    ⟨hbcl, subset_closure ⟨hAG (hBsub hb), fun h => (connectedComponentIn_subset _ _ h).2 (hBsub hb)⟩⟩
  have hfr : relFrontier G (_root_.connectedComponentIn (G \ A) x) ⊆ B :=
    (hc x hx).resolve_right fun hd => Set.disjoint_left.1 hd hbfr hb
  have heq := hG.comp_eq_of_relFrontier_subset hAc hBsub hx hfr
  have hdisA : Disjoint (_root_.connectedComponentIn (G \ B) x) A := by
    rw [heq]
    exact Set.disjoint_left.2 fun z hz hzA => (connectedComponentIn_subset _ _ hz).2 hzA
  have hdisS := hG.disjoint_comp_sideOf hBc hdisA
  rw [hσ] at hdisS
  have hdisA' : Disjoint (_root_.connectedComponentIn (G \ B) x) A' :=
    hdisS.mono_right (hA'.subset_sideOf hA'G hBfin)
  have hxB : x ∈ G \ B := ⟨hx.1, fun h => hx.2 (hBsub h)⟩
  have hxA' : x ∈ G \ A' :=
    ⟨hx.1, fun h => Set.disjoint_left.1 hdisA' (mem_connectedComponentIn hxB) h⟩
  refine ⟨hxA', ?_⟩
  rw [← heq]
  apply Subset.antisymm
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hxA')
      ((connectedComponentIn_subset _ _).trans (diff_subset_diff_right hBsub'))
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hxB)
      (fun z hz => ⟨comp_subset_G x hz, fun h => Set.disjoint_left.1 hdisA' hz h⟩)

/-- **H–O Proposition 11** (pp. 190–191): `σ_{B₁}(A)`, `A`, `σ_{B₂}(A)` satisfy (F1)–(F3). -/
theorem ho16_prop11 {G A B₁ B₂ : Set E} (hG : IsPLGraph G) (hconn : IsConnected G)
    (hA : IsPLGraph A) (hAG : A ⊆ G) (hAne : A.Nonempty)
    (hB : B₁ ∪ B₂ = relFrontier G A) (hdis : Disjoint B₁ B₂)
    (hc₁ : HasConsCompl G A B₁) (hc₂ : HasConsCompl G A B₂) :
    IsFoldTriple G (sideOf G B₁ A) A (sideOf G B₂ A) := by
  have hAc : IsClosed A := hA.isCompact.isClosed
  have hGc : IsClosed G := hG.isCompact.isClosed
  have hfrA : relFrontier G A ⊆ A := fun b hb => by
    have := hb.1
    rwa [hAc.closure_eq] at this
  have hB₁fr : B₁ ⊆ relFrontier G A := fun b hb => by rw [← hB]; exact Or.inl hb
  have hB₂fr : B₂ ⊆ relFrontier G A := fun b hb => by rw [← hB]; exact Or.inr hb
  have hB₁fin : B₁.Finite := (hG.relFrontier_finite hA hAG).subset hB₁fr
  have hB₂fin : B₂.Finite := (hG.relFrontier_finite hA hAG).subset hB₂fr
  have hB₁A : B₁ ⊆ A := hB₁fr.trans hfrA
  have hB₂A : B₂ ⊆ A := hB₂fr.trans hfrA
  obtain ⟨hPL₁, hG₁G, hAG₁, -, -⟩ := hG.sideOf_char_aux hA hAG hB₁fr hc₁
  obtain ⟨hPL₃, hG₃G, hAG₃, -, -⟩ := hG.sideOf_char_aux hA hAG hB₂fr hc₂
  obtain ⟨a, ha⟩ := hAne
  have hfrC : ∀ x ∈ G \ A, relFrontier G (_root_.connectedComponentIn (G \ A) x) ⊆ B₁ ∪ B₂ :=
    fun x _ => hB ▸ hG.relFrontier_comp_subset_relFrontier hAc x
  have hneC : ∀ x ∈ G \ A, (relFrontier G (_root_.connectedComponentIn (G \ A) x)).Nonempty :=
    fun x hx => hG.relFrontier_comp_nonempty hconn hAc ⟨a, hAG ha, ha⟩ hx
  have side₁ : ∀ x ∈ G \ A, (_root_.connectedComponentIn (G \ A) x ∩ sideOf G B₁ A).Nonempty →
      relFrontier G (_root_.connectedComponentIn (G \ A) x) ⊆ B₂ := by
    intro x hx hm z hz
    have hd := hG.disjoint_relFrontier_of_meets_sideOf hAc hB₁fin.isClosed hB₁A hc₁ hx hm
    rcases hfrC x hx hz with h | h
    · exact absurd h (Set.disjoint_left.1 hd hz)
    · exact h
  have side₃ : ∀ x ∈ G \ A, (_root_.connectedComponentIn (G \ A) x ∩ sideOf G B₂ A).Nonempty →
      relFrontier G (_root_.connectedComponentIn (G \ A) x) ⊆ B₁ := by
    intro x hx hm z hz
    have hd := hG.disjoint_relFrontier_of_meets_sideOf hAc hB₂fin.isClosed hB₂A hc₂ hx hm
    rcases hfrC x hx hz with h | h
    · exact h
    · exact absurd h (Set.disjoint_left.1 hd hz)
  -- two components meeting `G₁` and `G₃` respectively are disjoint
  have hdisC : ∀ x₁ ∈ G \ A, ∀ x₃ ∈ G \ A,
      (_root_.connectedComponentIn (G \ A) x₁ ∩ sideOf G B₁ A).Nonempty →
      (_root_.connectedComponentIn (G \ A) x₃ ∩ sideOf G B₂ A).Nonempty →
      Disjoint (_root_.connectedComponentIn (G \ A) x₁) (_root_.connectedComponentIn (G \ A) x₃) := by
    intro x₁ hx₁ x₃ hx₃ h₁ h₃
    rw [Set.disjoint_left]
    intro w hw1 hw3
    have heq : _root_.connectedComponentIn (G \ A) x₁ = _root_.connectedComponentIn (G \ A) x₃ :=
      (connectedComponentIn_eq hw1).trans (connectedComponentIn_eq hw3).symm
    obtain ⟨v, hv⟩ := hneC x₁ hx₁
    have hv2 := side₁ x₁ hx₁ h₁ hv
    rw [heq] at hv
    exact Set.disjoint_left.1 hdis (side₃ x₃ hx₃ h₃ hv) hv2
  refine ⟨⟨a, hAG₁ ha⟩, ⟨a, ha⟩, ⟨a, hAG₃ ha⟩, hPL₁, hA, hPL₃, ?_, ?_, ?_⟩
  · apply Subset.antisymm (union_subset hG₁G hG₃G)
    intro z hz
    by_cases hzA : z ∈ A
    · exact Or.inl (hAG₁ hzA)
    · obtain ⟨w, hw⟩ := hneC z ⟨hz, hzA⟩
      rcases hfrC z ⟨hz, hzA⟩ hw with h | h
      · exact Or.inr (hG.mem_sideOf_of_relFrontier hAc hB₂fin.isClosed hB₂A ⟨hz, hzA⟩ hw
          (Set.disjoint_left.1 hdis h))
      · exact Or.inl (hG.mem_sideOf_of_relFrontier hAc hB₁fin.isClosed hB₁A ⟨hz, hzA⟩ hw
          (Set.disjoint_right.1 hdis h))
  · apply Subset.antisymm (subset_inter hAG₁ hAG₃)
    rintro z ⟨hz1, hz3⟩
    by_contra hzA
    have hzGA : z ∈ G \ A := ⟨hG₁G hz1, hzA⟩
    obtain ⟨w, hw⟩ := hneC z hzGA
    exact Set.disjoint_left.1 hdis
      (side₃ z hzGA ⟨z, mem_connectedComponentIn hzGA, hz3⟩ hw)
      (side₁ z hzGA ⟨z, mem_connectedComponentIn hzGA, hz1⟩ hw)
  · rw [Set.disjoint_left]
    intro y hy1 hy3
    obtain ⟨x₁, hx₁, hy1'⟩ := hG.mem_closure_comp hA hAG
      (fun z hz => ⟨hG₁G hz.1, hz.2⟩ : sideOf G B₁ A \ A ⊆ G \ A) hy1
    obtain ⟨x₃, hx₃, hy3'⟩ := hG.mem_closure_comp hA hAG
      (fun z hz => ⟨hG₃G hz.1, hz.2⟩ : sideOf G B₂ A \ A ⊆ G \ A) hy3
    have hx₁' : x₁ ∈ G \ A := ⟨hG₁G hx₁.1, hx₁.2⟩
    have hx₃' : x₃ ∈ G \ A := ⟨hG₃G hx₃.1, hx₃.2⟩
    have hm₁ : (_root_.connectedComponentIn (G \ A) x₁ ∩ sideOf G B₁ A).Nonempty :=
      ⟨x₁, mem_connectedComponentIn hx₁', hx₁.1⟩
    have hm₃ : (_root_.connectedComponentIn (G \ A) x₃ ∩ sideOf G B₂ A).Nonempty :=
      ⟨x₃, mem_connectedComponentIn hx₃', hx₃.1⟩
    have hd := hdisC x₁ hx₁' x₃ hx₃' hm₁ hm₃
    have hyG : y ∈ G := closure_minimal (comp_subset_G x₁) hGc hy1'
    have hy₁ : y ∉ _root_.connectedComponentIn (G \ A) x₁ := fun h => by
      obtain ⟨w, hw1, hw3⟩ := inter_nonempty_of_mem_nhdsWithin
        (hG.compDiff_mem_nhdsWithin hAc h) hy3' (comp_subset_G x₃)
      exact Set.disjoint_left.1 hd hw1 hw3
    have hy₃ : y ∉ _root_.connectedComponentIn (G \ A) x₃ := fun h => by
      obtain ⟨w, hw3, hw1⟩ := inter_nonempty_of_mem_nhdsWithin
        (hG.compDiff_mem_nhdsWithin hAc h) hy1' (comp_subset_G x₁)
      exact Set.disjoint_left.1 hd hw1 hw3
    exact Set.disjoint_left.1 hdis
      (side₃ x₃ hx₃' hm₃ ⟨hy3', subset_closure ⟨hyG, hy₃⟩⟩)
      (side₁ x₁ hx₁' hm₁ ⟨hy1', subset_closure ⟨hyG, hy₁⟩⟩)

/-- The frontiers of the two sides in Proposition 11 (used for (19.1)–(19.2)).

Shape change (batch 195): the skeleton's hypotheses `IsConnected G`, `A.Nonempty` and
`Disjoint B₁ B₂` are not needed and have been dropped. -/
theorem ho16_prop11_frontier {G A B₁ B₂ : Set E} (hG : IsPLGraph G)
    (hA : IsPLGraph A) (hAG : A ⊆ G) (hB : B₁ ∪ B₂ = relFrontier G A)
    (hc₁ : HasConsCompl G A B₁) (hc₂ : HasConsCompl G A B₂) :
    relFrontier G (sideOf G B₁ A) = B₁ ∧ relFrontier G (sideOf G B₂ A) = B₂ := by
  have hB₁fr : B₁ ⊆ relFrontier G A := fun b hb => by rw [← hB]; exact Or.inl hb
  have hB₂fr : B₂ ⊆ relFrontier G A := fun b hb => by rw [← hB]; exact Or.inr hb
  exact ⟨(hG.sideOf_char_aux hA hAG hB₁fr hc₁).2.2.2.1,
    (hG.sideOf_char_aux hA hAG hB₂fr hc₂).2.2.2.1⟩

/-- **p. 191, remark after Proposition 11**: consistent complement relative to `B₁` gives it
relative to `B₂` when `∂A = B₁ ⊔ B₂`.

Shape change (batch 195): the skeleton's hypothesis `A ⊆ G` is not needed and has been
dropped. -/
theorem ho16_prop11_remark {G A B₁ B₂ : Set E} (hG : IsPLGraph G) (hA : IsPLGraph A)
    (hB : B₁ ∪ B₂ = relFrontier G A) (hdis : Disjoint B₁ B₂)
    (hc₁ : HasConsCompl G A B₁) : HasConsCompl G A B₂ := by
  intro x hx
  have h := hG.relFrontier_comp_subset_relFrontier hA.isCompact.isClosed (A := A) x
  rcases hc₁ x hx with h1 | h1
  · exact Or.inr (Set.disjoint_of_subset_left h1 hdis)
  · left
    intro z hz
    have hz' := h hz
    rw [← hB] at hz'
    rcases hz' with h' | h'
    · exact absurd h' (Set.disjoint_left.1 h1 hz)
    · exact h'

end Sides

end HPC.HO16
