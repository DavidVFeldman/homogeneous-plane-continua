import HPC.Moore.Sec6Defs

/-!
# Moore, F.A. (1916), §6: the topological setting (batch 138)

Moore's §6 arguments are arguments with arcs, closed curves and regions. They are carried out here
in an arbitrary Hausdorff space `X` with a family `reg` of open sets ("regions"), under named
hypotheses that isolate what each argument uses:

* `ArcConn X`: two distinct points of a connected open set are joined by an arc in it (Theorem 15);
* `Th21Prop reg`: Theorem 21 for the family;
* `Ax8Prop reg`: Axiom 8 for the family;
* `TInt reg J R`: `R` is a region with boundary the simple closed curve `J`.

The bridge to Moore's space (`bdry_eq_frontier`, `ext_eq_compl_closure`, `isArc_iff_tarc`,
`isSCC_iff_tscc`, `isInteriorOf_iff`, `arcConn`, `locallyConnectedSpace`) and Theorems 20, 21, 22
and the unnumbered `existsUnique_interior` are in `HPC/Moore/Sec6A.lean`.

Two constructions recur in Moore's proofs of Theorems 25, 26, 28 and are proved once here:

* `exists_access` (accessibility): from a point `F` of a connected open set `W`, an arc reaches a
  boundary point of `W` inside any prescribed neighbourhood of a given boundary point, running in
  `W` until its last point. Moore uses it without comment ("It can easily be shown that the
  point-set `EG + GA` contains as a subset an arc `FH` such that `H` is in `T` and on the boundary
  of `R₁` … while `FH − H` is a subset of `R₁`", p. 142).
* `exists_cross`: two such arcs glued at `F`: an arc `HK` through `W` with prescribed ends near two
  boundary points.
-/

namespace HPC.Moore

open Set Topology unitInterval

namespace Gen

variable {X : Type*} [TopologicalSpace X]

variable (X) in
/-- **Theorem 15, topologically:** two distinct points of a connected open set are joined by an
arc inside it. -/
def ArcConn : Prop :=
  ∀ U : Set X, IsOpen U → IsPreconnected U → ∀ a ∈ U, ∀ b ∈ U, a ≠ b → ∃ C ⊆ U, TArc a b C

/-- **Theorem 21** for a family of sets. -/
def Th21Prop (reg : Set (Set X)) : Prop :=
  ∀ K ∈ reg, ∀ R ∈ reg, frontier R ⊆ closure K → R ⊆ K

/-- **Axiom 8** for a family of sets. -/
def Ax8Prop (reg : Set (Set X)) : Prop :=
  ∀ J : Set X, TSCC J → ∃ R ∈ reg, frontier R = J

/-- `R` is the interior of the simple closed curve `J`: a member of `reg` with boundary `J`. -/
def TInt (reg : Set (Set X)) (J R : Set X) : Prop := TSCC J ∧ R ∈ reg ∧ frontier R = J

theorem notMem_of_mem_frontier {W : Set X} (hW : IsOpen W) {x : X} (hx : x ∈ frontier W) :
    x ∉ W := fun h => by
  have := hx.2; rw [hW.interior_eq] at this; exact this h

theorem mem_frontier_of_mem_closure {W : Set X} (hW : IsOpen W) {x : X} (hx : x ∈ closure W)
    (hxW : x ∉ W) : x ∈ frontier W := ⟨hx, by rw [hW.interior_eq]; exact hxW⟩

theorem closure_eq_union_frontier {W : Set X} (hW : IsOpen W) : closure W = W ∪ frontier W := by
  rw [frontier, hW.interior_eq, union_diff_self, union_eq_right.mpr subset_closure]

theorem disjoint_frontier {W : Set X} (hW : IsOpen W) : Disjoint W (frontier W) :=
  disjoint_left.mpr fun _ hx hf => notMem_of_mem_frontier hW hf hx

variable [T2Space X]

/-- **Accessibility.** From a point `F` of a connected open set `W`, and for a boundary point `Q`
of `W` and a neighbourhood `N` of `Q`, there is an arc `FH` with `H` on the boundary of `W` and in
`N`, and `FH − H ⊆ W`. -/
theorem exists_access [LocallyConnectedSpace X] (harc : ArcConn X) {W : Set X} (hWo : IsOpen W)
    (hWc : IsPreconnected W) {F Q : X} (hF : F ∈ W) (hQ : Q ∈ frontier W) {N : Set X}
    (hN : N ∈ 𝓝 Q) : ∃ H ∈ frontier W ∩ N, ∃ γ, TArc F H γ ∧ γ \ {H} ⊆ W := by
  obtain ⟨V, hVN, hVo, hQV, hVc⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp ‹_› Q N hN
  have hQW : Q ∉ W := notMem_of_mem_frontier hWo hQ
  obtain ⟨G, hGV, hGW⟩ := mem_closure_iff_nhds.mp hQ.1 V (hVo.mem_nhds hQV)
  have hGQ : G ≠ Q := fun h => hQW (h ▸ hGW)
  obtain ⟨σ₀, hσ₀V, hσ₀⟩ := harc V hVo hVc.isPreconnected G hGV Q hQV hGQ
  obtain ⟨H, hHW, σ', hσ'σ₀, hσ', hσ'W⟩ := hσ₀.first_point hWo.isClosed_compl
    ⟨Q, hσ₀.right_mem, hQW⟩ (fun h => h hGW)
  have hsub : σ' \ {H} ⊆ W := by
    intro x ⟨hx, hxH⟩
    by_contra hxW
    exact hxH (by rw [← hσ'W]; exact ⟨hx, hxW⟩)
  have hHfr : H ∈ frontier W :=
    mem_frontier_of_mem_closure hWo (closure_mono hsub hσ'.mem_closure_diff_right) hHW
  have hHN : H ∈ N := hVN (hσ₀V (hσ'σ₀ hσ'.right_mem))
  by_cases hFG : F = G
  · subst hFG; exact ⟨H, ⟨hHfr, hHN⟩, σ', hσ', hsub⟩
  obtain ⟨α, hαW, hα⟩ := harc W hWo hWc F hF G hGW hFG
  obtain ⟨γ, hγ, hγa⟩ := hα.join hσ'.symm ⟨G, hα.right_mem, hσ'.left_mem⟩
    (fun h => hHW (h ▸ hF))
  refine ⟨H, ⟨hHfr, hHN⟩, γ, hγa, fun x ⟨hx, hxH⟩ => ?_⟩
  rcases hγ hx with h | h
  · exact hαW h
  · exact hsub ⟨h, hxH⟩

/-- **Crossing arcs.** Through a nonempty connected open set `W`, an arc `HK` with `H`, `K` on the
boundary of `W`, `H` near `Q₁`, `K` near `Q₂`, and `HK − H − K ⊆ W`. -/
theorem exists_cross [LocallyConnectedSpace X] (harc : ArcConn X) {W : Set X} (hWo : IsOpen W)
    (hWc : IsPreconnected W) (hne : W.Nonempty) {Q₁ Q₂ : X} (hQ₁ : Q₁ ∈ frontier W)
    (hQ₂ : Q₂ ∈ frontier W) {N₁ N₂ : Set X} (hN₁ : N₁ ∈ 𝓝 Q₁) (hN₂ : N₂ ∈ 𝓝 Q₂)
    (hdis : Disjoint (frontier W ∩ N₁) N₂) :
    ∃ H ∈ frontier W ∩ N₁, ∃ K ∈ frontier W ∩ N₂, ∃ γ, TArc H K γ ∧ γ \ {H, K} ⊆ W := by
  obtain ⟨F, hF⟩ := hne
  obtain ⟨H, hH, γ₁, hγ₁, hγ₁W⟩ := exists_access harc hWo hWc hF hQ₁ hN₁
  obtain ⟨K, hK, γ₂, hγ₂, hγ₂W⟩ := exists_access harc hWo hWc hF hQ₂ hN₂
  have hHK : H ≠ K := fun h => disjoint_left.mp hdis hH (h ▸ hK.2)
  obtain ⟨γ, hγ, hγa⟩ := hγ₁.symm.join hγ₂.symm ⟨F, hγ₁.left_mem, hγ₂.left_mem⟩ hHK
  refine ⟨H, hH, K, hK, γ, hγa, fun x ⟨hx, hxHK⟩ => ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hxHK
  rcases hγ hx with h | h
  · exact hγ₁W ⟨h, hxHK.1⟩
  · exact hγ₂W ⟨h, hxHK.2⟩

end Gen

end HPC.Moore
