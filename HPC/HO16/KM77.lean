import HPC.HO16.Defs
import HPC.Plane.Ingram68Star
import HPC.Jones.Jones49Chain

/-!
# Batch 193, §3: Krasinkiewicz–Minc 1977, Lemma 2

Commission 193, §3; skeleton `HO16A.lean`, statement `km77_lemma2` (unchanged). K–M's proof
(p. 676), with their Lemma 1 replaced by hereditary indecomposability (step 3 of the commission).
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane

section Comp

variable {X : Type*} [TopologicalSpace X]

/-- A preconnected subset of `K` meeting a part `K ∩ G` of `K` that is relatively clopen (`G`
open, `K ∩ G` closed) lies in `G`. -/
theorem IsPreconnected.subset_of_relClopen {s K G : Set X} (hs : IsPreconnected s) (hsK : s ⊆ K)
    (hG : IsOpen G) (hKG : IsClosed (K ∩ G)) (hne : (s ∩ G).Nonempty) : s ⊆ G := by
  rcases isPreconnected_iff_subset_of_disjoint.1 hs G (K ∩ G)ᶜ hG hKG.isOpen_compl
    (fun x _ => by
      by_cases hx : x ∈ G
      · exact Or.inl hx
      · exact Or.inr fun h => hx h.2)
    (Set.eq_empty_iff_forall_notMem.2 fun x ⟨hxs, hxG, h⟩ => h ⟨hsK hxs, hxG⟩) with h | h
  · exact h
  · obtain ⟨x, hxs, hxG⟩ := hne
    exact (h hxs ⟨hsK hxs, hxG⟩).elim

/-- A preconnected subset of `K` meeting the component of `a` in `K` lies in it. -/
theorem IsPreconnected.subset_connectedComponentIn_of_meet {s K : Set X} {a : X}
    (hs : IsPreconnected s) (hsK : s ⊆ K) (hne : (s ∩ connectedComponentIn K a).Nonempty) :
    s ⊆ connectedComponentIn K a := by
  obtain ⟨z, hzs, hza⟩ := hne
  rw [connectedComponentIn_eq hza]
  exact hs.subset_connectedComponentIn hzs hsK

end Comp

section CompClosed

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- In a compact metric space, the union of the components of a closed set `K` that meet a
closed set `C` is closed. -/
theorem isClosed_biUnion_connectedComponentIn {K C : Set X} (hK : IsClosed K) (hC : IsClosed C) :
    IsClosed (⋃ a ∈ C, connectedComponentIn K a) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  by_cases hxK : x ∈ K
  · have hdisj : Disjoint (connectedComponentIn K x) C := by
      rw [Set.disjoint_left]
      intro c hcx hcC
      apply hx
      refine mem_iUnion₂.2 ⟨c, hcC, ?_⟩
      rw [← connectedComponentIn_eq hcx]
      exact mem_connectedComponentIn hxK
    obtain ⟨G, hG, hxG, hKG, hKGC⟩ :=
      HPC.Jones.exists_clopen_of_connectedComponentIn_disjoint hK.isCompact hC hxK hdisj
    refine ⟨G, fun y hyG hy => ?_, hG, hxG⟩
    obtain ⟨c, hcC, hyc⟩ := mem_iUnion₂.1 hy
    have hcK : c ∈ K := connectedComponentIn_nonempty_iff.1 ⟨y, hyc⟩
    have hsub := IsPreconnected.subset_of_relClopen isPreconnected_connectedComponentIn
      (connectedComponentIn_subset K c) hG hKG ⟨y, hyc, hyG⟩
    exact Set.disjoint_left.1 hKGC ⟨hcK, hsub (mem_connectedComponentIn hcK)⟩ hcC
  · refine ⟨Kᶜ, fun y hy hy' => ?_, hK.isOpen_compl, hxK⟩
    obtain ⟨c, -, hyc⟩ := mem_iUnion₂.1 hy'
    exact hy (connectedComponentIn_subset K c hyc)

end CompClosed

/-! ## §3. Krasinkiewicz–Minc, Lemma 2 (commission §3) -/

/-- **Krasinkiewicz–Minc 1977, Lemma 2**, for hereditarily indecomposable compacta, in the form
quoted by H–O on p. 187 (K–M's `F₀, F₁, F₂` are `X₁, X₂, X₃`). -/
theorem km77_lemma2 {X : Type*} [MetricSpace X] [CompactSpace X]
    (hHI : IsHereditarilyIndecomposable (univ : Set X)) {A B U V : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) (hU : IsOpen U) (hV : IsOpen V)
    (hAU : A ⊆ U) (hBV : B ⊆ V) :
    ∃ X₁ X₂ X₃ : Set X, IsClosed X₁ ∧ IsClosed X₂ ∧ IsClosed X₃ ∧ X₁ ∪ X₂ ∪ X₃ = univ ∧
      A ⊆ X₁ ∧ B ⊆ X₃ ∧ Disjoint X₁ X₃ ∧ X₁ ∩ X₂ ⊆ V ∧ X₂ ∩ X₃ ⊆ U := by
  classical
  -- Step 1: `U'`, `V'`.
  obtain ⟨U', hU'o, hAU', hU'cl⟩ := normal_exists_closure_subset hA (hU.inter hB.isOpen_compl)
    (fun x hx => ⟨hAU hx, Set.disjoint_left.1 hAB hx⟩)
  obtain ⟨V', hV'o, hBV', hV'cl⟩ := normal_exists_closure_subset hB
    (hV.inter isClosed_closure.isOpen_compl)
    (fun x hx => ⟨hBV hx, fun h => (hU'cl h).2 hx⟩)
  have hclU : closure U' ⊆ U := fun x hx => (hU'cl hx).1
  have hclV : closure V' ⊆ V := fun x hx => (hV'cl hx).1
  have hUV : Disjoint (closure U') (closure V') :=
    Set.disjoint_right.2 fun x hx => (hV'cl hx).2
  have hU'V' : Disjoint U' V' :=
    hUV.mono subset_closure subset_closure
  have hAV' : ∀ a ∈ A, a ∉ V' := fun a ha h =>
    Set.disjoint_left.1 hU'V' (hAU' ha) h
  have hBU' : ∀ b ∈ B, b ∉ U' := fun b hb h =>
    Set.disjoint_left.1 hU'V' h (hBV' hb)
  -- Step 2: `A*`, `B*`.
  set As := ⋃ a ∈ A, connectedComponentIn V'ᶜ a with hAs
  set Bs := ⋃ b ∈ B, connectedComponentIn U'ᶜ b with hBs
  have hAsc : IsClosed As := isClosed_biUnion_connectedComponentIn hV'o.isClosed_compl hA
  have hBsc : IsClosed Bs := isClosed_biUnion_connectedComponentIn hU'o.isClosed_compl hB
  have hAAs : A ⊆ As := fun a ha => mem_iUnion₂.2 ⟨a, ha, mem_connectedComponentIn (hAV' a ha)⟩
  have hBBs : B ⊆ Bs := fun b hb => mem_iUnion₂.2 ⟨b, hb, mem_connectedComponentIn (hBU' b hb)⟩
  have hAsV : As ⊆ V'ᶜ := iUnion₂_subset fun a _ => connectedComponentIn_subset _ _
  have hBsU : Bs ⊆ U'ᶜ := iUnion₂_subset fun b _ => connectedComponentIn_subset _ _
  -- Step 3: `A* ∩ B* = ∅`.
  have hcont : ∀ (K : Set X) (a : X), IsClosed K → a ∈ K →
      Fold.Q78.IsContinuum (connectedComponentIn K a) := fun K a hK ha =>
    ⟨(HPC.Jones.isClosed_connectedComponentIn' hK a).isCompact,
      isConnected_connectedComponentIn_iff.2 ha⟩
  have hdisj : Disjoint As Bs := by
    rw [Set.disjoint_left]
    intro p hpA hpB
    obtain ⟨a, ha, hpa⟩ := mem_iUnion₂.1 hpA
    obtain ⟨b, hb, hpb⟩ := mem_iUnion₂.1 hpB
    set C₁ := connectedComponentIn V'ᶜ a
    set C₂ := connectedComponentIn U'ᶜ b
    have h1 := hcont V'ᶜ a hV'o.isClosed_compl (hAV' a ha)
    have h2 := hcont U'ᶜ b hU'o.isClosed_compl (hBU' b hb)
    have h12 : Fold.Q78.IsContinuum (C₁ ∪ C₂) :=
      ⟨h1.1.union h2.1, IsConnected.union ⟨p, hpa, hpb⟩ h1.2 h2.2⟩
    rcases (hHI (C₁ ∪ C₂) (subset_univ _) h12).2 C₁ C₂ h1 h2 subset_union_left
      subset_union_right rfl with h | h
    · have : b ∈ C₁ := h ▸ subset_union_right (mem_connectedComponentIn (hBU' b hb))
      exact connectedComponentIn_subset _ _ this (hBV' hb)
    · have : a ∈ C₂ := h ▸ subset_union_left (mem_connectedComponentIn (hAV' a ha))
      exact connectedComponentIn_subset _ _ this (hAU' ha)
  -- a continuum in `K` meeting the union of components lies in it
  have hstar : ∀ (K C Z : Set X), Fold.Q78.IsContinuum Z → Z ⊆ K →
      (Z ∩ ⋃ a ∈ C, connectedComponentIn K a).Nonempty → Z ⊆ ⋃ a ∈ C, connectedComponentIn K a := by
    intro K C Z hZ hZK ⟨z, hzZ, hz⟩
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.1 hz
    have hZc : IsConnected Z := hZ.2
    exact (IsPreconnected.subset_connectedComponentIn_of_meet hZc.isPreconnected hZK
      ⟨z, hzZ, hza⟩).trans
      (subset_iUnion₂ (s := fun a _ => connectedComponentIn K a) a ha)
  -- Step 4: cut wire in `X \ V'`.
  obtain ⟨D₁, D₂, hD₁, hD₂, hD12, hDeq, hAsD₁, hBsD₂⟩ :=
    exists_split_of_no_continuum (F := V'ᶜ) (E₁ := As) (E₂ := Bs ∩ V'ᶜ) hV'o.isClosed_compl
      hAsV inter_subset_right hAsc (hBsc.inter hV'o.isClosed_compl)
      (fun Z hZ hZF h1 h2 => by
        have hZA := hstar V'ᶜ A Z hZ hZF h1
        obtain ⟨z, hzZ, hzB, -⟩ := h2
        exact Set.disjoint_left.1 hdisj (hZA hzZ) hzB)
  have hBsD₁ : Disjoint Bs D₁ := by
    rw [Set.disjoint_left]
    intro z hzB hzD
    have hzV : z ∈ V'ᶜ := hDeq ▸ Or.inl hzD
    exact Set.disjoint_left.1 hD12 hzD (hBsD₂ ⟨hzB, hzV⟩)
  -- Step 5: cut wire in `X \ U'`.
  obtain ⟨E₁, E₂, hE₁, hE₂, hE12, hEeq, hBsE₁, hD₁E₂⟩ :=
    exists_split_of_no_continuum (F := U'ᶜ) (E₁ := Bs) (E₂ := D₁ ∩ U'ᶜ) hU'o.isClosed_compl
      hBsU inter_subset_right hBsc (hD₁.inter hU'o.isClosed_compl)
      (fun Z hZ hZF h1 h2 => by
        have hZB := hstar U'ᶜ B Z hZ hZF h1
        obtain ⟨z, hzZ, hzD, -⟩ := h2
        exact Set.disjoint_left.1 hBsD₁ (hZB hzZ) hzD)
  have hD₁V : D₁ ⊆ V'ᶜ := hDeq ▸ subset_union_left
  have hD₂V : D₂ ⊆ V'ᶜ := hDeq ▸ subset_union_right
  have hE₁U : E₁ ⊆ U'ᶜ := hEeq ▸ subset_union_left
  have hE₂U : E₂ ⊆ U'ᶜ := hEeq ▸ subset_union_right
  -- Step 6.
  refine ⟨D₁ ∪ (E₂ ∩ closure V'), (D₂ ∩ E₂) ∪ (D₂ ∩ closure U') ∪ (E₂ ∩ closure V'),
    E₁ ∪ (D₂ ∩ closure U'), hD₁.union (hE₂.inter isClosed_closure),
    ((hD₂.inter hE₂).union (hD₂.inter isClosed_closure)).union (hE₂.inter isClosed_closure),
    hE₁.union (hD₂.inter isClosed_closure), ?_, hAAs.trans (hAsD₁.trans subset_union_left),
    hBBs.trans (hBsE₁.trans subset_union_left), ?_, ?_, ?_⟩
  · refine eq_univ_of_forall fun x => ?_
    by_cases hxV : x ∈ V'
    · have hxU : x ∈ U'ᶜ := fun h => Set.disjoint_left.1 hU'V' h hxV
      rw [hEeq] at hxU
      rcases hxU with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inl (Or.inr ⟨h, subset_closure hxV⟩))
    · have hxV' : x ∈ V'ᶜ := hxV
      rw [hDeq] at hxV'
      rcases hxV' with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · by_cases hxU : x ∈ U'
        · exact Or.inr (Or.inr ⟨h, subset_closure hxU⟩)
        · have hxU' : x ∈ U'ᶜ := hxU
          rw [hEeq] at hxU'
          rcases hxU' with h' | h'
          · exact Or.inr (Or.inl h')
          · exact Or.inl (Or.inr (Or.inl (Or.inl ⟨h, h'⟩)))
  · rw [Set.disjoint_left]
    rintro x (hx | ⟨hx2, hxV⟩) (hy | ⟨hy2, hyU⟩)
    · have hxU : x ∈ U'ᶜ := hE₁U hy
      exact Set.disjoint_left.1 hE12 hy (hD₁E₂ ⟨hx, hxU⟩)
    · exact Set.disjoint_left.1 hD12 hx hy2
    · exact Set.disjoint_left.1 hE12 hy hx2
    · exact Set.disjoint_left.1 hUV hyU hxV
  · rintro x ⟨hx1 | ⟨-, hxV⟩, hx2⟩
    · rcases hx2 with (⟨hxD, -⟩ | ⟨hxD, -⟩) | ⟨-, hxV⟩
      · exact absurd hxD (Set.disjoint_left.1 hD12 hx1)
      · exact absurd hxD (Set.disjoint_left.1 hD12 hx1)
      · exact hclV hxV
    · exact hclV hxV
  · rintro x ⟨hx2, hx3 | ⟨-, hxU⟩⟩
    · rcases hx2 with (⟨-, hxE⟩ | ⟨-, hxU⟩) | ⟨hxE, -⟩
      · exact absurd hxE (Set.disjoint_left.1 hE12 hx3)
      · exact hclU hxU
      · exact absurd hxE (Set.disjoint_left.1 hE12 hx3)
    · exact hclU hxU

end HPC.HO16
