import HPC.Jones.Jones49EArc

/-!
# Batch 153: simple closed curves and θ-curves in cyclic Peano continua (item E)

* `tscc_rot`, `tscc_split`: a simple closed curve (two arcs `C₁`, `C₂` from `s` to `t` with only
  `s`, `t` in common) is, for any two distinct points `p`, `q` of it, the union of two arcs from `p`
  to `q` with only `p`, `q` in common.
* `exists_scc_of_cyclic`: a compact, locally connected metric space with no cut points contains a
  simple closed curve (an arc `α` from `a` to `b`, a point `c` inside it, an arc `β` from `a` to `b`
  avoiding `c`, trimmed by first points).
* `exists_theta_of_cyclic`: if moreover the space is not itself a simple closed curve, it contains
  a θ-curve: three arcs with common ends, any two meeting only in the ends (a point `w` off the
  curve `J`, an arc from `w` to its first point `c₁` on `J`, then an arc from `w` to `J` avoiding
  `c₁`, trimmed twice by first points).
-/

namespace HPC.Jones

open Set Topology Metric HPC.Moore.Gen

section Split

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- One-sided rotation: the end `t` may be moved to any point `p` of `C₁`. -/
theorem tscc_rot_left {s t p : X} {C₁ C₂ : Set X} (h₁ : TArc s t C₁) (h₂ : TArc s t C₂)
    (h12 : C₁ ∩ C₂ = {s, t}) (hp : p ∈ C₁) (hps : p ≠ s) :
    ∃ D₁ D₂, TArc s p D₁ ∧ TArc s p D₂ ∧ D₁ ∩ D₂ = {s, p} ∧ D₁ ∪ D₂ = C₁ ∪ C₂ := by
  by_cases hpt : p = t
  · subst hpt; exact ⟨C₁, C₂, h₁, h₂, h12, rfl⟩
  obtain ⟨Γ₁, Γ₂, hΓ₁, hΓ₂, hU, hI⟩ := h₁.split hp hps hpt
  have e1 : ∀ z, z ∈ Γ₁ → z ∈ Γ₂ → z = p := fun z h1 h2 => by
    have : z ∈ Γ₁ ∩ Γ₂ := ⟨h1, h2⟩
    rwa [hI] at this
  have e2 : ∀ z, z ∈ C₁ → z ∈ C₂ → z = s ∨ z = t := fun z h1 h2 => by
    have : z ∈ C₁ ∩ C₂ := ⟨h1, h2⟩
    rwa [h12] at this
  have hΓ₁C : Γ₁ ⊆ C₁ := hU ▸ subset_union_left
  have hΓ₂C : Γ₂ ⊆ C₁ := hU ▸ subset_union_right
  have hsΓ₂ : s ∉ Γ₂ := fun h => hps (e1 s hΓ₁.left_mem h).symm
  have htΓ₁ : t ∉ Γ₁ := fun h => hpt (e1 t h hΓ₂.right_mem).symm
  have hsC₂ := h₂.left_mem
  have htC₂ := h₂.right_mem
  have hD₂ : TArc s p (C₂ ∪ Γ₂) := by
    refine h₂.union hΓ₂.symm (subset_antisymm ?_ ?_)
    · rintro z ⟨hz2, hzΓ⟩
      rcases e2 z (hΓ₂C hzΓ) hz2 with rfl | rfl
      · exact absurd hzΓ hsΓ₂
      · rfl
    · rintro z rfl; exact ⟨htC₂, hΓ₂.right_mem⟩
  refine ⟨Γ₁, C₂ ∪ Γ₂, hΓ₁, hD₂, ?_, ?_⟩
  · apply subset_antisymm
    · rintro z ⟨hz1, hz2 | hz2⟩
      · rcases e2 z (hΓ₁C hz1) hz2 with rfl | rfl
        · exact Or.inl rfl
        · exact absurd hz1 htΓ₁
      · exact Or.inr (e1 z hz1 hz2)
    · rintro z (rfl | rfl)
      · exact ⟨hΓ₁.left_mem, Or.inl hsC₂⟩
      · exact ⟨hΓ₁.right_mem, Or.inr hΓ₂.left_mem⟩
  · rw [← hU]
    ext z; simp only [mem_union]; tauto

/-- **Rotation.** In a simple closed curve `C₁ ∪ C₂` (ends `s`, `t`), the end `t` may be moved to
any point `p ≠ s` of the curve. -/
theorem tscc_rot {s t p : X} {C₁ C₂ : Set X} (h₁ : TArc s t C₁) (h₂ : TArc s t C₂)
    (h12 : C₁ ∩ C₂ = {s, t}) (hp : p ∈ C₁ ∪ C₂) (hps : p ≠ s) :
    ∃ D₁ D₂, TArc s p D₁ ∧ TArc s p D₂ ∧ D₁ ∩ D₂ = {s, p} ∧ D₁ ∪ D₂ = C₁ ∪ C₂ := by
  rcases hp with hp | hp
  · exact tscc_rot_left h₁ h₂ h12 hp hps
  · obtain ⟨D₁, D₂, h1, h2, hI, hU⟩ := tscc_rot_left h₂ h₁ (by rw [inter_comm]; exact h12) hp hps
    exact ⟨D₁, D₂, h1, h2, hI, by rw [hU, union_comm]⟩

/-- **Splitting a simple closed curve at two points.** -/
theorem tscc_split {s t p q : X} {C₁ C₂ : Set X} (h₁ : TArc s t C₁) (h₂ : TArc s t C₂)
    (h12 : C₁ ∩ C₂ = {s, t}) (hp : p ∈ C₁ ∪ C₂) (hq : q ∈ C₁ ∪ C₂) (hpq : p ≠ q) :
    ∃ L₁ L₂, TArc p q L₁ ∧ TArc p q L₂ ∧ L₁ ∩ L₂ = {p, q} ∧ L₁ ∪ L₂ = C₁ ∪ C₂ := by
  by_cases hps : p = s
  · subst hps
    exact tscc_rot h₁ h₂ h12 hq (Ne.symm hpq)
  obtain ⟨D₁, D₂, hD₁, hD₂, hDI, hDU⟩ := tscc_rot h₁ h₂ h12 hp hps
  obtain ⟨L₁, L₂, hL₁, hL₂, hLI, hLU⟩ := tscc_rot hD₁.symm hD₂.symm
    (by rw [hDI, pair_comm]) (hDU ▸ hq) (Ne.symm hpq)
  exact ⟨L₁, L₂, hL₁, hL₂, hLI, hLU.trans hDU⟩

end Split

section Cyclic

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X] [LocallyConnectedSpace X]

/-- **A simple closed curve in a cyclic Peano continuum.** A compact, locally connected metric
space with no cut points contains two arcs with common ends and only the
ends in common. -/
theorem exists_scc_of_cyclic (hcyc : ∀ z : X, IsConnected ({z}ᶜ : Set X)) :
    ∃ (s t : X) (C₁ C₂ : Set X), TArc s t C₁ ∧ TArc s t C₂ ∧ C₁ ∩ C₂ = {s, t} := by
  obtain ⟨b⟩ := (inferInstance : Nonempty X)
  obtain ⟨a, hab⟩ := (hcyc b).nonempty
  have hab : a ≠ b := hab
  obtain ⟨α, -, hα⟩ := exists_tarc_in_open isOpen_univ isPreconnected_univ (mem_univ a)
    (mem_univ b) hab
  obtain ⟨c, hcα, hcab⟩ := hα.nonempty_diff
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hcab
  obtain ⟨hca, hcb⟩ := hcab
  obtain ⟨β, hβc, hβ⟩ := exists_tarc_in_open isOpen_compl_singleton (hcyc c).isPreconnected
    (show a ∈ ({c}ᶜ : Set X) from Ne.symm hca) (show b ∈ ({c}ᶜ : Set X) from Ne.symm hcb) hab
  obtain ⟨α₁, α₂, hα₁, hα₂, hαU, hαI⟩ := hα.split hcα hca hcb
  have e1 : ∀ z, z ∈ α₁ → z ∈ α₂ → z = c := fun z h1 h2 => by
    have : z ∈ α₁ ∩ α₂ := ⟨h1, h2⟩
    rwa [hαI] at this
  have hβc' : ∀ z ∈ β, z ≠ c := fun z hz => hβc hz
  have hbα₁ : b ∉ α₁ := fun h => hcb (e1 b h hα₂.right_mem).symm
  obtain ⟨s, hsα₁, β', hβ'β, hβ', hβ'α₁⟩ := hβ.symm.first_point hα₁.isClosed
    ⟨a, hβ.left_mem, hα₁.left_mem⟩ hbα₁
  have hsc : s ≠ c := hβc' s (hβ'β hβ'.right_mem)
  have hsα₂ : s ∉ α₂ := fun h => hsc (e1 s hsα₁ h)
  obtain ⟨t, htα₂, β'', hβ''β', hβ'', hβ''α₂⟩ := hβ'.symm.first_point hα₂.isClosed
    ⟨b, hβ'.left_mem, hα₂.right_mem⟩ hsα₂
  have htc : t ≠ c := hβc' t (hβ'β (hβ''β' hβ''.right_mem))
  have hst : s ≠ t := fun e => hsc (e1 s hsα₁ (e ▸ htα₂))
  have hαs : s ∈ α := hαU ▸ Or.inl hsα₁
  have hαt : t ∈ α := hαU ▸ Or.inr htα₂
  obtain ⟨α', hα'α, hα'⟩ := hα.exists_sub hαs hαt hst
  refine ⟨s, t, α', β'', hα', hβ'', subset_antisymm ?_ ?_⟩
  · rintro z ⟨hzα', hzβ''⟩
    have hzα : z ∈ α₁ ∪ α₂ := hαU.symm ▸ hα'α hzα'
    rcases hzα with h | h
    · have : z ∈ β' ∩ α₁ := ⟨hβ''β' hzβ'', h⟩
      rw [hβ'α₁] at this
      exact Or.inl this
    · have : z ∈ β'' ∩ α₂ := ⟨hzβ'', h⟩
      rw [hβ''α₂] at this
      exact Or.inr this
  · rintro z (rfl | rfl)
    · exact ⟨hα'.left_mem, hβ''.left_mem⟩
    · exact ⟨hα'.right_mem, hβ''.right_mem⟩

/-- **Item E: a θ-curve in a cyclic Peano continuum that is not a simple closed curve.** A
compact, connected, locally connected metric space with no cut points, and which is
not itself a simple closed curve, contains three arcs with common ends `a ≠ b`, any two of which
have only `a` and `b` in common. -/
theorem exists_theta_of_cyclic (hcyc : ∀ z : X, IsConnected ({z}ᶜ : Set X))
    (hnot : ¬ TSCC (univ : Set X)) :
    ∃ (a b : X) (K₁ K₂ K₃ : Set X), TArc a b K₁ ∧ TArc a b K₂ ∧ TArc a b K₃ ∧
      K₁ ∩ K₂ = {a, b} ∧ K₁ ∩ K₃ = {a, b} ∧ K₂ ∩ K₃ = {a, b} := by
  obtain ⟨s, t, C₁, C₂, h₁, h₂, h12⟩ := exists_scc_of_cyclic hcyc
  set J := C₁ ∪ C₂ with hJ
  have hJc : IsClosed J := h₁.isClosed.union h₂.isClosed
  obtain ⟨w, hwJ⟩ : ∃ w, w ∉ J := by
    by_contra hcon
    push_neg at hcon
    exact hnot ⟨s, t, C₁, C₂, h₁, h₂, h12, (eq_univ_of_forall hcon).symm⟩
  have hsJ : s ∈ J := Or.inl h₁.left_mem
  have htJ : t ∈ J := Or.inl h₁.right_mem
  have hws : w ≠ s := fun e => hwJ (e ▸ hsJ)
  obtain ⟨A₀, -, hA₀⟩ := exists_tarc_in_open isOpen_univ isPreconnected_univ (mem_univ w)
    (mem_univ s) hws
  obtain ⟨c₁, hc₁J, A₁, -, hA₁, hA₁J⟩ := hA₀.first_point hJc ⟨s, hA₀.right_mem, hsJ⟩ hwJ
  have eA : ∀ z, z ∈ A₁ → z ∈ J → z = c₁ := fun z h1 h2 => by
    have : z ∈ A₁ ∩ J := ⟨h1, h2⟩
    rwa [hA₁J] at this
  obtain ⟨d, hdJ, hdc⟩ : ∃ d ∈ J, d ≠ c₁ := by
    by_cases h : c₁ = s
    · exact ⟨t, htJ, fun e => h₁.ne (h.symm.trans e.symm)⟩
    · exact ⟨s, hsJ, Ne.symm h⟩
  have hwd : w ≠ d := fun e => hwJ (e ▸ hdJ)
  have hwc : w ≠ c₁ := fun e => hwJ (e ▸ hc₁J)
  obtain ⟨δ, hδc, hδ⟩ := exists_tarc_in_open isOpen_compl_singleton (hcyc c₁).isPreconnected
    (show w ∈ ({c₁}ᶜ : Set X) from hwc) (show d ∈ ({c₁}ᶜ : Set X) from hdc) hwd
  have hδc' : ∀ z ∈ δ, z ≠ c₁ := fun z hz => hδc hz
  have hdA₁ : d ∉ A₁ := fun h => hdc (eA d h hdJ)
  obtain ⟨s', hs'A₁, δ', hδ'δ, hδ', hδ'A₁⟩ := hδ.symm.first_point hA₁.isClosed
    ⟨w, hδ.left_mem, hA₁.left_mem⟩ hdA₁
  have hs'c : s' ≠ c₁ := hδc' s' (hδ'δ hδ'.right_mem)
  have hs'J : s' ∉ J := fun h => hs'c (eA s' hs'A₁ h)
  obtain ⟨t', ht'J, δ'', hδ''δ', hδ'', hδ''J⟩ := hδ'.symm.first_point hJc
    ⟨d, hδ'.left_mem, hdJ⟩ hs'J
  have ht'c : t' ≠ c₁ := hδc' t' (hδ'δ (hδ''δ' hδ''.right_mem))
  obtain ⟨A₂, hA₂A₁, hA₂⟩ := hA₁.exists_sub hA₁.right_mem hs'A₁ (Ne.symm hs'c)
  have hK₃ : TArc c₁ t' (A₂ ∪ δ'') := by
    refine hA₂.union hδ'' (subset_antisymm ?_ ?_)
    · rintro z ⟨hzA, hzδ⟩
      have : z ∈ δ' ∩ A₁ := ⟨hδ''δ' hzδ, hA₂A₁ hzA⟩
      rwa [hδ'A₁] at this
    · rintro z rfl; exact ⟨hA₂.right_mem, hδ''.left_mem⟩
  have hK₃J : (A₂ ∪ δ'') ∩ J = {c₁, t'} := by
    apply subset_antisymm
    · rintro z ⟨hz | hz, hzJ⟩
      · exact Or.inl (eA z (hA₂A₁ hz) hzJ)
      · have : z ∈ δ'' ∩ J := ⟨hz, hzJ⟩
        rw [hδ''J] at this
        exact Or.inr this
    · rintro z (rfl | rfl)
      · exact ⟨Or.inl hA₂.left_mem, hc₁J⟩
      · exact ⟨Or.inr hδ''.right_mem, ht'J⟩
  obtain ⟨L₁, L₂, hL₁, hL₂, hLI, hLU⟩ := tscc_split h₁ h₂ h12 hc₁J ht'J (Ne.symm ht'c)
  have key : ∀ L, L ⊆ J → c₁ ∈ L → t' ∈ L → L ∩ (A₂ ∪ δ'') = {c₁, t'} := by
    intro L hLJ hc hT
    apply subset_antisymm
    · rintro z ⟨hzL, hzK⟩
      rw [← hK₃J]; exact ⟨hzK, hLJ hzL⟩
    · rintro z (rfl | rfl)
      · exact ⟨hc, Or.inl hA₂.left_mem⟩
      · exact ⟨hT, Or.inr hδ''.right_mem⟩
  refine ⟨c₁, t', L₁, L₂, A₂ ∪ δ'', hL₁, hL₂, hK₃, hLI, ?_, ?_⟩
  · exact key L₁ (subset_union_left.trans hLU.le) hL₁.left_mem hL₁.right_mem
  · exact key L₂ (subset_union_right.trans hLU.le) hL₂.left_mem hL₂.right_mem

end Cyclic

end HPC.Jones
