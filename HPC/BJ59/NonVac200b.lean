import HPC.BJ59.Thm9
import HPC.BJ59.Step1b
import HPC.BJ59.DP61
import HPC.BJ59.NonVac200

/-!
# Batch 200, §8: non-vacuity of §§3, 5, 6

* `nonvac_privatePoint_shrink`, `nonvac_privatePoint_interior`: a plane pseudo-arc and the chain of
  `nonvac_bj_chains` (at least three links);
* `nonvac_step1b`: `[0, 1]`, the identity, the chain `nvChain 0`;
* `nonvac_bj9`: a plane pseudo-arc, `P = Q`, `D = E` the chain of `nonvac_bj_chains` shrunk to
  private points, `H` the identity; `nonvac_bj9_one`: the one-link chain;
* `nonvac_bj_theorem7_proof_n3`: the chain of `nonvac_bj_chains` consolidated to three links,
  `V = univ`, `U = D.link 2`;
* `allowed_small`, `nonvac_bj9Stage`, `oneChain`: the new definitions on small inputs;
* `nonvac_dp22_theorem61`: under `BJThm10` and `BJPlaneExample`, the circle of pseudo-arcs `C`.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

/-- `exists_privatePoint_shrink` on a plane pseudo-arc with a chain of at least three links. -/
theorem nonvac_privatePoint_shrink : ∃ P : Set Pt, IsPseudoArc P ∧ ∃ n, 3 ≤ n ∧
    ∃ D : Chain Pt n, IsBJChain D ∧ P ⊆ D.union ∧ (∀ j, (D.link j ∩ P).Nonempty) ∧
      ∀ j, ∃ p ∈ P ∩ D.link j, ∀ j', j' ≠ j → p ∉ closure (D.link j') := by
  obtain ⟨P, hP, n, hn, D0, hD0, hPD0, hD0P⟩ := nonvac_bj_chains
  obtain ⟨D, hD, hPD, -, hpr⟩ := exists_privatePoint_shrink hP.1.1 hP.2.2 D0 hD0 hPD0 hD0P
  refine ⟨P, hP, n, hn, D, hD, hPD, fun j => ?_, hpr⟩
  obtain ⟨p, ⟨hpP, hpj⟩, -⟩ := hpr j
  exact ⟨p, hpj, hpP⟩

/-- `exists_privatePoint_interior` on a plane pseudo-arc with a chain of at least three links: the
link with index `1`. -/
theorem nonvac_privatePoint_interior : ∃ P : Set Pt, IsPseudoArc P ∧ ∃ n, 3 ≤ n ∧
    ∃ D : Chain Pt n, IsBJChain D ∧ P ⊆ D.union ∧ (∀ j, (D.link j ∩ P).Nonempty) ∧
      ∃ i : Fin n, 0 < i.val ∧ i.val + 1 < n ∧
        ∃ p ∈ P ∩ D.link i, ∀ j, j ≠ i → p ∉ closure (D.link j) := by
  obtain ⟨P, hP, n, hn, D, hD, hPD, hDP⟩ := nonvac_bj_chains
  refine ⟨P, hP, n, hn, D, hD, hPD, hDP, ⟨1, by omega⟩, by simp, by simp; omega, ?_⟩
  exact exists_privatePoint_interior hP.1.1.2 D hD hPD hDP _ (by simp) (by simp; omega)

/-- `bj_step1b` on `[0, 1]` with the identity and the chain `nvChain 0`. -/
theorem nonvac_step1b : ∃ δ > 0, ∀ a b : unitInterval, a ≤ b → (b : ℝ) - a ≤ δ → ∀ u v : ℕ,
    u ≤ v →
      id ⁻¹' Icc a b ⊆ ⋃ (k : Fin (nvN 0 + 1)) (_ : u ≤ k.val ∧ k.val ≤ v), (nvChain 0).link k →
      ¬ id ⁻¹' Icc a b ⊆ ⋃ (k : Fin (nvN 0 + 1)) (_ : u + 1 ≤ k.val ∧ k.val ≤ v),
        (nvChain 0).link k →
      ¬ id ⁻¹' Icc a b ⊆ ⋃ (k : Fin (nvN 0 + 1)) (_ : u ≤ k.val ∧ k.val + 1 ≤ v),
        (nvChain 0).link k →
      ∀ x ∈ Icc a b, ∀ k : Fin (nvN 0 + 1), u ≤ k.val → k.val ≤ v →
        ((nvChain 0).link k ∩ id ⁻¹' {x}).Nonempty :=
  bj_step1b isArcOfContinua_id IsOpenMap.id (nvChain 0) (nvChain_cover 0)

/-- `bj9_base` and `bj_theorem9` on a plane pseudo-arc, `P = Q`, `D = E` a chain of at least three
links with private points, `H` the identity: the hypotheses hold, and so do the conclusions. -/
theorem nonvac_bj9 : ∃ P : Set Pt, IsPseudoArc P ∧ ∃ n, 3 ≤ n ∧ ∃ D : Chain Pt n,
    IsBJChain D ∧ P ⊆ D.union ∧ (∀ i, (D.link i ∩ P).Nonempty) ∧ IsChainMap (id : Fin n → Fin n) ∧
    (∀ j, ∃ i, id i = j ∧ ∃ p ∈ P ∩ D.link i, ∀ i', i' ≠ i → p ∉ closure (D.link i')) ∧
    (∃ (N : ℕ) (D' E' : Chain Pt N), IsBJChain D' ∧ IsBJChain E' ∧ P ⊆ D'.union ∧
      P ⊆ E'.union ∧ ∀ (i : Fin n) (j : Fin N) (p : Pt), p ∈ P → p ∈ D.link i →
        p ∈ D'.link j → closure (E'.link j) ⊆ D.link i) ∧
    ∃ h : P ≃ₜ P, ∀ (i : Fin n) (p : P), (p : Pt) ∈ D.link i → (h p : Pt) ∈ D.link i := by
  obtain ⟨P, hP, n, hn, D, hD, hPD, hDP, hpr⟩ := nonvac_privatePoint_shrink
  have hid : IsChainMap (id : Fin n → Fin n) := fun _ _ h => h
  have hHo : ∀ j, ∃ i, id i = j ∧ ∃ p ∈ P ∩ D.link i, ∀ i', i' ≠ i → p ∉ closure (D.link i') :=
    fun j => ⟨j, rfl, hpr j⟩
  refine ⟨P, hP, n, hn, D, hD, hPD, hDP, hid, hHo, ?_,
    bj_theorem9 hP hP D D hD hD hPD hDP hPD hDP id hid hHo⟩
  obtain ⟨N, D', E', hD', hE', hPD', -, hPE', -, -, -, hcl⟩ :=
    bj9_base hP hP D D hD hD hPD hDP hPD hDP id hid hHo
  exact ⟨N, D', E', hD', hE', hPD', hPE', hcl⟩

/-- The one-link chain whose link is the whole space. -/
def oneChain (X : Type*) [MetricSpace X] [Nonempty X] : Chain X 1 where
  link _ := univ
  isOpen _ := isOpen_univ
  adjacent i j := by
    rw [Subsingleton.elim i j]
    simp [univ_nonempty]

/-- `bj_theorem9` on the one-link chain (a degenerate input). -/
theorem nonvac_bj9_one : ∃ P : Set Pt, IsPseudoArc P ∧ IsBJChain (oneChain Pt) ∧
    P ⊆ (oneChain Pt).union ∧ (∀ i, ((oneChain Pt).link i ∩ P).Nonempty) ∧
    (∀ j, ∃ i, id i = j ∧ ∃ p ∈ P ∩ (oneChain Pt).link i,
      ∀ i', i' ≠ i → p ∉ closure ((oneChain Pt).link i')) ∧
    ∃ h : P ≃ₜ P, ∀ (i : Fin 1) (p : P), (p : Pt) ∈ (oneChain Pt).link i →
      (h p : Pt) ∈ (oneChain Pt).link (id i) := by
  obtain ⟨P, hP⟩ := isPseudoArc_plane
  obtain ⟨p0, hp0⟩ := hP.2.2.nonempty
  have hbj : IsBJChain (oneChain Pt) := fun i j h => by
    rw [Subsingleton.elim i j] at h; simp at h
  have hPU : P ⊆ (oneChain Pt).union := fun x _ => mem_iUnion.2 ⟨0, mem_univ x⟩
  have hPm : ∀ i, ((oneChain Pt).link i ∩ P).Nonempty := fun _ => ⟨p0, mem_univ _, hp0⟩
  have hHo : ∀ j, ∃ i, id i = j ∧ ∃ p ∈ P ∩ (oneChain Pt).link i,
      ∀ i', i' ≠ i → p ∉ closure ((oneChain Pt).link i') :=
    fun j => ⟨j, rfl, p0, ⟨hp0, mem_univ _⟩, fun i' hi' => absurd (Subsingleton.elim i' j) hi'⟩
  exact ⟨P, hP, hbj, hPU, hPm, hHo,
    bj_theorem9 hP hP _ _ hbj hbj hPU hPm hPU hPm id (fun _ _ h => h) hHo⟩

/-- The hypotheses of `bj_theorem7_proof_n3` hold for a plane pseudo-arc with a chain of three
links, `V = univ`, `U = D.link 2`. -/
theorem nonvac_bj_theorem7_proof_n3 : ∃ P : Set Pt, IsPseudoArc P ∧ ∃ D : Chain Pt 3,
    P ⊆ D.union ∧ (∀ j, (D.link j ∩ P).Nonempty) ∧ IsOpen (D.link 2) ∧
    D.link 2 ⊆ D.link 2 ∧ P ∩ (D.link 1 \ D.link 0) ⊆ univ ∧
    P ∩ (D.link 2 \ D.link 1) ⊆ D.link 2 ∧ (D.link 2 ∩ P).Nonempty ∧
    (univ ∩ D.link 2).Nonempty := by
  obtain ⟨P, hP, n, hn, D0, hD0, hPD0, hD0P⟩ := nonvac_bj_chains
  let H : Fin n → Fin 3 := fun k =>
    if k.val = 0 then 0 else if k.val + 1 = n then 2 else 1
  have hH : IsChainMap H := by
    intro a b hab
    simp only [H]
    split_ifs <;> simp <;> omega
  have hHs : Function.Surjective H := by
    intro c
    fin_cases c
    · exact ⟨⟨0, by omega⟩, by simp [H]⟩
    · exact ⟨⟨1, by omega⟩, by simp [H]; omega⟩
    · exact ⟨⟨n - 1, by omega⟩, by simp only [H]; rw [if_neg (by omega), if_pos (by omega)]; rfl⟩
  obtain ⟨D, -, hPD, hDP, -⟩ := exists_consolidation hP.1.1.2.isPreconnected hP.2.2.nonempty D0
    hD0 hPD0 hD0P H hH hHs
  refine ⟨P, hP, D, hPD, hDP, D.isOpen 2, subset_rfl, subset_univ _,
    fun x hx => hx.2.1, hDP 2, ?_⟩
  exact bj_theorem7_proof_n3 hP.1.1.2 D hPD hDP (D.isOpen 2) subset_rfl (subset_univ _)
    (fun x hx => hx.2.1) (hDP 2)

/-- `dp22_theorem61_iff` on the plane circle of pseudo-arcs, under its two inputs. -/
theorem nonvac_dp22_theorem61 (h10 : BJThm10) (hEx : BJPlaneExample) :
    ∃ C : Set Pt, IsCircleOfPA C ∧ ∃ f : C → Circle, IsAtomicCircPAMap f := by
  obtain ⟨C, hC⟩ := hEx
  obtain ⟨f, hf⟩ := isCircleOfPA_iff.1 hC
  haveI := hf.compactSpace
  exact ⟨C, hC, (dp22_theorem61_iff h10 ⟨C, hC⟩).1 hC⟩

/-- `Allowed` on small indices: `d′₀` is attached to `d₀` only, `d′₂` to `d₀` and `d₁`, `d′₃` to
`d₁` only. -/
theorem allowed_small (i : ℕ) : (Allowed 0 i ↔ i = 0) ∧ (Allowed 2 i ↔ i = 0 ∨ i = 1) ∧
    (Allowed 3 i ↔ i = 1) := by
  simp [Allowed]

/-- A matched pair of chains (`BJ9Stage`) exists: the chain of `nonvac_privatePoint_shrink` on
both sides. -/
theorem nonvac_bj9Stage : ∃ P : Set Pt, IsPseudoArc P ∧ ∃ S : BJ9Stage P P, 3 ≤ S.N := by
  obtain ⟨P, hP, n, hn, D, hD, hPD, -, hpr⟩ := nonvac_privatePoint_shrink
  exact ⟨P, hP, ⟨n, D, D, hD, hD, hPD, hPD, hpr, hpr⟩, hn⟩

end HPC.BJ59
