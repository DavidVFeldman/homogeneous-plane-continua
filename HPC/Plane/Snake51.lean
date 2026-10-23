import HPC.PseudoArc.Theorem13
import HPC.Fold.Theorem7
import HPC.Plane.Descr
import HPC.Plane.Transfer
import HPC.Plane.T4

/-!
# Bing 1951, *Snake-like continua*: Theorem 4, and a description in the plane

Batch 84 (COMMISSION-batch84.md). The skeleton's four definitions are kept verbatim. The skeleton's
`exists_rect_chain_following` is **false as stated** (counterexample: `HPC/Plane/Counter.lean`,
`rectStepSkeleton_false`); it is commented out below with the reason, and replaced by a reshaped
statement about *tame* chains (images of a row of standard rectangles under a homeomorphism of the
plane, `IsTame`, `HPC/Plane/StdChain.lean`) along *slow* patterns. `theorem4`,
`exists_description_plane` and `pseudoArc_exists` keep their conclusions.

The plane is `ℝ × ℝ` with its product (sup) metric (`Pt`, defined in `HPC/Plane/StdChain.lean`).
-/

namespace HPC.Plane

open Set

/-- An open axis-parallel rectangle of positive size. -/
def IsOpenRect (S : Set Pt) : Prop :=
  ∃ a b c d : ℝ, a < b ∧ c < d ∧ S = Ioo a b ×ˢ Ioo c d

/-- A chain *has room* if every link contains a point outside the closures of all other links.
(Invariant of the construction; may be replaced, COMMISSION-batch84.md §3.2.) -/
def HasRoom {n : ℕ} (D : Chain Pt n) : Prop :=
  ∀ i, (D.link i \ ⋃ j ∈ ({j | j ≠ i} : Set (Fin n)), closure (D.link j)).Nonempty

/-- A chain of open rectangles with room. -/
def IsRectChain {n : ℕ} (D : Chain Pt n) : Prop :=
  (∀ i, IsOpenRect (D.link i)) ∧ HasRoom D

-- Commented-out statement `exists_rect_chain_following` (skeleton form) removed in batch 103; see `LEDGER.md`.

theorem zone_inter_stdRect_subset {m k j : ℕ} (hk : k < m) (hj : j < m) :
    zone k ∩ stdRect j ⊆ stdRect k ∪ stdRect (min (k + 1) (m - 1)) := by
  rintro ⟨a, b⟩ ⟨⟨⟨h1, h2⟩, -⟩, ⟨h5, h6⟩, h7, h8⟩
  simp only at h1 h2 h5 h6 h7 h8
  rcases Nat.lt_or_ge (k + 1) m with hk1 | hk1
  · rw [min_eq_left (by omega)]
    rcases lt_or_ge a (2 * k + 3) with ha | ha
    · left; exact ⟨⟨by simp only; linarith, ha⟩, h7, h8⟩
    · right; refine ⟨⟨?_, ?_⟩, h7, h8⟩ <;> push_cast <;> linarith
  · left
    have : (j : ℝ) ≤ k := by exact_mod_cast (show j ≤ k by omega)
    exact ⟨⟨by simp only; linarith, by simp only; linarith⟩, h7, h8⟩

/-- **The planar step** (Bing p. 654, "it can be shown that in the plane there is a sequence of
chains …", one level), **reshaped**. Given a tame chain `D` of `m` links and `ε > 0`, there is
`N` such that for every pattern `x : Fin n → Fin m` with unit steps and `N`-slow (values at least
two apart are taken at indices at least `N` apart) there is a tame chain `D'` of `n` links with
the closure of `D'_t` inside `D_{x t}`, *tight* (`D'_t` meets `D_l` only for `l = x t'` with
`t'` within one of `t`), and each link of `D'` bounded and either of diameter at most `ε` or inside
the union of two consecutive links of `D` (the latter happens only near the turns of `x`). -/
theorem exists_rect_chain_following {m : ℕ} (D : Chain Pt m) (hD : IsTame D) (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ) (x : Fin n → Fin m), 0 < n →
      (∀ t t' : Fin n, t'.val = t.val + 1 → ((x t' : ℤ) - (x t : ℤ)).natAbs ≤ 1) →
      (∀ s s' : Fin n, (x s : ℤ) + 2 ≤ x s' → N ≤ ((s : ℤ) - (s' : ℤ)).natAbs) →
      ∃ D' : Chain Pt n, IsTame D' ∧
        (∀ t, closure (D'.link t) ⊆ D.link (x t)) ∧
        (∀ (t : Fin n) (l : Fin m), (D'.link t ∩ D.link l).Nonempty →
          ∃ t' : Fin n, (t'.val ≤ t.val + 1 ∧ t.val ≤ t'.val + 1) ∧ l = x t') ∧
        (∀ t, Bornology.IsBounded (D'.link t) ∧ (Metric.diam (D'.link t) ≤ ε ∨
          ∃ k k' : Fin m, k.val ≤ k'.val ∧ k'.val ≤ k.val + 1 ∧
            D'.link t ⊆ D.link k ∪ D.link k')) := by
  obtain ⟨Φ, hΦ⟩ := hD
  obtain ⟨N, -, hstep⟩ := real_step Φ hm hε
  refine ⟨N, fun n x hn hx hs => ?_⟩
  obtain ⟨Ψ, h1, h2, h3, -, -, -⟩ := hstep n x hn hx hs
  refine ⟨tameChain (Ψ.trans Φ) n, tameChain_isTame _ _, fun t => ?_, fun t l h => ?_,
    fun t => ⟨tameChain_link_bounded _ _ t, ?_⟩⟩
  · rw [hΦ]; exact h1 t
  · rw [hΦ] at h; exact h2 t l h
  · rcases h3 t with h | ⟨k, hk, hz⟩
    · exact Or.inl h
    · right
      refine ⟨⟨k, hk⟩, ⟨min (k + 1) (m - 1), by omega⟩, by simp only; omega,
        by simp only; omega, ?_⟩
      rw [hΦ, hΦ]
      intro p hp
      have hp2 : p ∈ Φ '' stdRect (x t) := h1 t (subset_closure hp)
      obtain ⟨q, hq, rfl⟩ := hz hp
      obtain ⟨q', hq', e⟩ := hp2
      rw [Φ.injective e] at hq'
      rcases zone_inter_stdRect_subset hk (x t).isLt ⟨hq, hq'⟩ with h | h
      · exact Or.inl ⟨q, h, rfl⟩
      · exact Or.inr ⟨q, h, rfl⟩

/-- An `ε`-chain: bounded links of diameter less than `ε` (Bing 1951, §1). -/
def IsEpsChain {X : Type*} [MetricSpace X] {n : ℕ} (D : Chain X n) (ε : ℝ) : Prop :=
  ∀ i, Bornology.IsBounded (D.link i) ∧ Metric.diam (D.link i) < ε

/-- **Snake-like** (Bing 1951, §1): a (compact) continuum that is covered by an `ε`-chain for every
`ε > 0`. -/
def IsSnakeLike {X : Type*} [MetricSpace X] (M : Set X) : Prop :=
  Fold.Q78.IsContinuum M ∧ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ M ⊆ D.union

/-- **Bing 1951, Theorem 4.** Each snake-like continuum is homeomorphic with a plane continuum.
Proof: COMMISSION-batch84.md §2 and §3.5 (Bing 1948 Theorem 11, `MatchingCovers.exists_homeomorph`,
applied to a sequence of minimal covering chains of `M` and a sequence of tame chains in the plane
following the same patterns; `HPC/Plane/T4.lean`). -/
theorem theorem4 {X : Type*} [MetricSpace X] {M : Set X} (hM : IsSnakeLike M) :
    ∃ N : Set Pt, Fold.Q78.IsContinuum N ∧ Nonempty (M ≃ₜ N) := by
  obtain ⟨⟨hMc, hMconn⟩, hsnake⟩ := hM
  obtain ⟨N, hNc, hNconn, hT⟩ := theorem4_of hMc hMconn hsnake
  exact ⟨N, ⟨hNc, hNconn⟩, hT⟩

/-- **A description exists in the plane** (COMMISSION-batch84.md §3.4): tame chains following
stuttered Bing patterns, crooked by tightness (`HPC/Plane/Descr.lean`). -/
theorem exists_description_plane :
    ∃ (P Q : Pt), P ≠ Q ∧ Nonempty (Description Pt P Q) :=
  exists_description_plane'

/-- All links of a description in the plane lie in a compact set: the closure of the (bounded)
union of the links of level `0`. -/
theorem Description.links_subset_compact {P Q : Pt} (Δ : Description Pt P Q) :
    IsCompact (closure (Δ.D 0).union) ∧ ∀ i t, (Δ.D i).link t ⊆ closure (Δ.D 0).union := by
  refine ⟨Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_, fun i t => ?_⟩
  · exact (Bornology.isBounded_iUnion.mpr fun j => Δ.bdd 0 j).closure
  · obtain ⟨s, hs⟩ := Δ.refines_of_le (Nat.zero_le i) t
    exact hs.trans ((subset_iUnion _ s).trans subset_closure)

/-- **The pseudo-arc is a homogeneous hereditarily indecomposable nondegenerate plane continuum.**
From `exists_description_plane` with `Description.isContinuum_M`, `theorem10`, `theorem13`. -/
theorem pseudoArc_exists :
    ∃ M : Set Pt, Fold.Q78.IsContinuum M ∧ M.Nontrivial ∧
      (∀ K : Set Pt, K ⊆ M → Fold.Q78.IsContinuum K → Fold.Q78.IsIndecomposable K) ∧
      ∀ (p q : Pt) (hp : p ∈ M) (hq : q ∈ M), ∃ T : M ≃ₜ M, T ⟨p, hp⟩ = ⟨q, hq⟩ := by
  obtain ⟨P, Q, hPQ, ⟨Δ⟩⟩ := exists_description_plane
  obtain ⟨hKc, hK⟩ := Description.links_subset_compact Δ
  exact ⟨Δ.M, Δ.isContinuum_M_of _ hK hKc, ⟨P, Δ.P_mem_M, Q, Δ.Q_mem_M, hPQ⟩, Description.theorem10 Δ,
    Δ.theorem13_of _ hK hKc hPQ⟩

end HPC.Plane
