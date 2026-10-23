import HPC.Jones.Jones49EArc
import HPC.Jones.Jones49D

/-!
# Batch 153: accessibility of boundary points (item C)

`accessible_of_cyclic'`: for `M` compact, connected, semi-locally connected and cyclic, every
boundary point `p` of a complementary domain `R` is the end of an arc from any point of `R`, lying
except for `p` in `R`.

The route of REPORT-batch152 §8. Batch 152's `local_join_of_noncut` applies at `p` (no point cuts
`M`): for every `ε` there is `δ(ε)` such that two points of `R` within `δ(ε)` of `p` lie in a
connected subset of `R ∩ V_ε(p)`, hence in one component of that open set, hence on a polygonal arc
in it (`exists_tarc_of_isOpen_plane`, item A). Points `xₙ → p` of `R` and radii `ρₙ` are chosen
recursively, with `βₙ` an arc from `xₙ` to `xₙ₊₁` in `R ∩ V_{ρₙ}(p)` and
`ρₙ₊₂ ≤ min (ρₙ₊₁ / 2) (dist (p, βₙ))`; so `βₘ` misses `βₙ` for `m ≥ n + 2`, and Moore's limit-arc
construction `HPC.Moore.Gen.exists_tarc_of_seq` gives an arc from `x₀` to `p` in `R + p`. An arc in
`R` from the given point to `x₀` is attached by `TArc.join`.
-/

namespace HPC.Jones

open Set Topology Metric Filter HPC.Plane HPC.Moore.Gen

/-- **Item C (accessibility).** -/
theorem accessible_of_cyclic' {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    (hS : ∀ z : M, SemiLocConnAt z) (hcyc : ∀ z : M, IsConnected ({z}ᶜ : Set M)) {x : Pt}
    (hx : x ∉ M) {p : Pt} (hp : p ∈ frontier (connectedComponentIn Mᶜ x)) {y : Pt}
    (hy : y ∈ connectedComponentIn Mᶜ x) (hyp : y ≠ p) :
    ∃ C : Set Pt, TArc y p C ∧ C \ {p} ⊆ connectedComponentIn Mᶜ x := by
  set R := connectedComponentIn Mᶜ x with hRdef
  have hRo : IsOpen R := hM.isClosed.isOpen_compl.connectedComponentIn
  have hRc : IsConnected R := isConnected_connectedComponentIn_iff.2 hx
  have hpM : p ∈ M := HPC.Moore.Gen.frontier_connectedComponentIn_subset hM.isClosed x hp
  have hpR : p ∉ R := fun h => connectedComponentIn_subset _ _ h hpM
  have hpcl : p ∈ closure R := frontier_subset_closure hp
  have hLJ := fun (ε : ℝ) (hε : 0 < ε) =>
    Sec14.local_join_of_noncut hM hMc hS (p := ⟨p, hpM⟩) (hcyc ⟨p, hpM⟩) hε x
  choose! δ hδpos hδ using hLJ
  -- points of `R` near `p`, other than a given point
  have hnear : ∀ r > 0, ∀ w : Pt, ∃ z ∈ R, z ∈ ball p r ∧ z ≠ w := by
    intro r hr w
    by_cases hw : w = p
    · obtain ⟨z, hzb, hzR⟩ := mem_closure_iff.1 hpcl (ball p r) isOpen_ball (mem_ball_self hr)
      exact ⟨z, hzR, hzb, fun e => hpR (by rw [← hw, ← e]; exact hzR)⟩
    · obtain ⟨z, ⟨hzb, hzw⟩, hzR⟩ := mem_closure_iff.1 hpcl (ball p r ∩ {w}ᶜ)
        (isOpen_ball.inter isOpen_compl_singleton) ⟨mem_ball_self hr, Ne.symm hw⟩
      exact ⟨z, hzR, hzb, hzw⟩
  -- the step
  have step : ∀ (x₀ : Pt) (ρ ρ' : ℝ), 0 < ρ → 0 < ρ' → x₀ ∈ R → x₀ ∈ ball p (δ ρ) →
      ∃ x₁ : Pt, ∃ β : Set Pt, x₁ ∈ R ∧ x₁ ∈ ball p (δ ρ') ∧ TArc x₀ x₁ β ∧ β ⊆ R ∧
        β ⊆ ball p ρ := by
    intro x₀ ρ ρ' hρ hρ' hx₀R hx₀b
    obtain ⟨x₁, hx₁R, hx₁b, hx₁x₀⟩ := hnear (min (δ ρ) (δ ρ'))
      (lt_min (hδpos ρ hρ) (hδpos ρ' hρ')) x₀
    obtain ⟨C, hCR, hCc, hx₀C, hx₁C, hCb⟩ := hδ ρ hρ x₀ hx₀R x₁ hx₁R hx₀b
      (ball_subset_ball (min_le_left _ _) hx₁b)
    set W := connectedComponentIn (R ∩ ball p ρ) x₀
    have hWo : IsOpen W := (hRo.inter isOpen_ball).connectedComponentIn
    have hWc : IsConnected W := isConnected_connectedComponentIn_iff.2 ⟨hx₀R, hCb hx₀C⟩
    have hCW : C ⊆ W := hCc.subset_connectedComponentIn hx₀C (subset_inter hCR hCb)
    obtain ⟨β, hβW, hβ⟩ := exists_tarc_of_isOpen_plane hWo hWc (hCW hx₀C) (hCW hx₁C)
      (Ne.symm hx₁x₀)
    have hWsub : W ⊆ R ∩ ball p ρ := connectedComponentIn_subset _ _
    exact ⟨x₁, β, hx₁R, ball_subset_ball (min_le_right _ _) hx₁b, hβ,
      hβW.trans (hWsub.trans inter_subset_left), hβW.trans (hWsub.trans inter_subset_right)⟩
  choose! X1 B1 hX1R hX1b hB1arc hB1R hB1b using step
  -- the initial point and radii
  obtain ⟨x₀, hx₀R, hx₀b, -⟩ := hnear (δ 1) (hδpos 1 one_pos) p
  have hx₀p : x₀ ≠ p := fun e => hpR (e ▸ hx₀R)
  have hdx₀ : 0 < dist x₀ p := dist_pos.2 hx₀p
  set ρ₁ : ℝ := min (1 / 2) (dist x₀ p) with hρ₁
  have hρ₁pos : 0 < ρ₁ := lt_min (by norm_num) hdx₀
  let nxt : Pt × ℝ × ℝ → Pt × ℝ × ℝ := fun s =>
    (X1 s.1 s.2.1 s.2.2, s.2.2, min (s.2.2 / 2) (infDist p (B1 s.1 s.2.1 s.2.2)))
  let st : ℕ → Pt × ℝ × ℝ := fun n => Nat.rec (x₀, 1, ρ₁) (fun _ s => nxt s) n
  have hst : ∀ n, st (n + 1) = nxt (st n) := fun n => rfl
  -- invariants
  have hinv : ∀ n, 0 < (st n).2.1 ∧ 0 < (st n).2.2 ∧ (st n).1 ∈ R ∧
      (st n).1 ∈ ball p (δ (st n).2.1) ∧ (st n).2.2 ≤ (st n).2.1 / 2 := by
    intro n
    induction n with
    | zero =>
      refine ⟨one_pos, hρ₁pos, hx₀R, hx₀b, ?_⟩
      show ρ₁ ≤ 1 / 2
      exact min_le_left _ _
    | succ n ih =>
      obtain ⟨h1, h2, h3, h4, -⟩ := ih
      rw [hst]
      have hβR := hB1R _ _ _ h1 h2 h3 h4
      have hβarc := hB1arc _ _ _ h1 h2 h3 h4
      have hpβ : p ∉ B1 (st n).1 (st n).2.1 (st n).2.2 := fun h => hpR (hβR h)
      have hinf : 0 < infDist p (B1 (st n).1 (st n).2.1 (st n).2.2) :=
        (hβarc.isClosed.notMem_iff_infDist_pos ⟨_, hβarc.left_mem⟩).1 hpβ
      refine ⟨h2, lt_min (by linarith) hinf, hX1R _ _ _ h1 h2 h3 h4,
        hX1b _ _ _ h1 h2 h3 h4, min_le_left _ _⟩
  set xs : ℕ → Pt := fun n => (st n).1 with hxs
  set ρ : ℕ → ℝ := fun n => (st n).2.1 with hρ
  set β : ℕ → Set Pt := fun n => B1 (st n).1 (st n).2.1 (st n).2.2 with hβ
  have harc : ∀ n, TArc (xs n) (xs (n + 1)) (β n) := fun n => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hinv n
    exact hB1arc _ _ _ h1 h2 h3 h4
  have hβR : ∀ n, β n ⊆ R := fun n => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hinv n
    exact hB1R _ _ _ h1 h2 h3 h4
  have hβb : ∀ n, β n ⊆ ball p (ρ n) := fun n => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hinv n
    exact hB1b _ _ _ h1 h2 h3 h4
  have hρsucc : ∀ n, ρ (n + 1) ≤ ρ n / 2 := fun n => by
    show (st (n + 1)).2.1 ≤ _
    rw [hst]; exact (hinv n).2.2.2.2
  have hρpos : ∀ n, 0 < ρ n := fun n => (hinv n).1
  have hρanti : Antitone ρ := antitone_nat_of_succ_le fun n => by
    have := hρsucc n; have := hρpos n; linarith
  have hρ2 : ∀ n, ρ (n + 2) ≤ infDist p (β n) := fun n => by
    exact min_le_right _ _
  have hρpow : ∀ n, ρ n ≤ 1 / 2 ^ n := by
    intro n
    induction n with
    | zero => show (1 : ℝ) ≤ 1 / 2 ^ 0; norm_num
    | succ n ih =>
      calc ρ (n + 1) ≤ ρ n / 2 := hρsucc n
        _ ≤ (1 / 2 ^ n) / 2 := by linarith
        _ = 1 / 2 ^ (n + 1) := by rw [pow_succ]; field_simp
  obtain ⟨τ, hτsub, hτ⟩ := exists_tarc_of_seq (x := xs) (β := β) (B := p) harc
    (fun n m hnm => by
      refine disjoint_left.mpr fun z hzn hzm => ?_
      have h1 : dist z p < ρ m := mem_ball.1 (hβb m hzm)
      have h2 : ρ m ≤ ρ (n + 2) := hρanti hnm
      have h3 := hρ2 n
      have h4 : infDist p (β n) ≤ dist p z := infDist_le_dist_of_mem hzn
      rw [dist_comm] at h1
      linarith)
    (fun h => by
      have h1 : dist (xs 0) p < ρ 1 := mem_ball.1 (hβb 1 h)
      have h2 : ρ 1 = ρ₁ := rfl
      have h3 : ρ₁ ≤ dist x₀ p := min_le_right _ _
      have h4 : xs 0 = x₀ := rfl
      rw [h4, h2] at h1
      linarith)
    (fun n h => hpR (hβR n h))
    (fun U hU => by
      obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
      refine eventually_atTop.2 ⟨N, fun n hn => (hβb n).trans ((ball_subset_ball ?_).trans hεU)⟩
      calc ρ n ≤ 1 / 2 ^ n := hρpow n
        _ = (1 / 2) ^ n := by rw [one_div_pow]
        _ ≤ (1 / 2) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
        _ ≤ ε := hN.le)
  have hτR : τ \ {p} ⊆ R := by
    rintro z ⟨hz, hzp⟩
    rcases hτsub hz with h | h
    · exact absurd h hzp
    · obtain ⟨n, hn⟩ := mem_iUnion.1 h
      exact hβR n hn
  have hxs0 : xs 0 = x₀ := rfl
  rw [hxs0] at hτ
  by_cases hyx : y = x₀
  · subst hyx; exact ⟨τ, hτ, hτR⟩
  obtain ⟨α, hαR, hα⟩ := exists_tarc_of_isOpen_plane hRo hRc hy hx₀R hyx
  obtain ⟨γ, hγ, hγarc⟩ := hα.join hτ.symm ⟨x₀, hα.right_mem, hτ.left_mem⟩ hyp
  refine ⟨γ, hγarc, ?_⟩
  rintro z ⟨hz, hzp⟩
  rcases hγ hz with h | h
  · exact hαR h
  · exact hτR ⟨h, hzp⟩

end HPC.Jones
