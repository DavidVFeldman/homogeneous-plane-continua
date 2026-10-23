import HPC.Plane.StdChain

/-!
# Batch 150, item B: Moore 1922, Theorems 1–3

R. L. Moore, *Concerning connectedness im kleinen and a related property*, Fund. Math. 3 (1922),
232–237. The four definitions of the batch-150 skeleton (verbatim) and Theorems 1–3.

* **Theorem 1** (`moore22_theorem1`): Moore's proof takes a "limiting set" of connected sets
  `tₙ ∋ Aₙ, Pₙ`. Here the limiting set is replaced by an explicit chain: connected sets of
  summable diameters joining points `Pₖ → P`, points `Xₖ → X`, and `X₀` to `P₀`; the union, with
  `X` and `P` added, is connected and lies in `M̄`. (The printed proof has `tₙ` "within `K*`";
  it should be within `K̄`, see the ledger.)
* **Theorem 2** (`moore22_theorem2`): Moore's proof (the set `M_s + P`, `P ∈ M̄_s`), run with the
  finitely many pieces whose closure contains `P` rather than with a sequence.
* **Theorem 3** (`moore22_theorem3`): Moore's proof with `ε/3` in place of `ε` (as printed, the
  sets `M_K` have diameter `≤ 2ε`, see the ledger).
-/

namespace HPC.Jones

open Set Topology Metric

section Moore22

open HPC.Plane

/-- **Property S** (Moore 1922, p. 232): "for every positive number `ε`, `M` is the sum of a finite
number of connected point-sets … each of diameter less than `ε`". Connected in Moore's sense
(footnote 2) admits the empty set; bounded is part of "diameter less than `ε`". -/
def PropertyS (M : Set Pt) : Prop :=
  ∀ ε > 0, ∃ s : Finset (Set Pt), (∀ A ∈ s, IsPreconnected A ∧ Bornology.IsBounded A ∧ diam A < ε) ∧
    M = ⋃ A ∈ s, A

/-- *Connected im kleinen at `P`* (p. 233): for every `ε` there is `δ` such that each point `X` of
`M` within `δ` of `P` lies with `P` in a connected subset of `M` of diameter less than `ε`. -/
def CikAt (M : Set Pt) (P : Pt) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ X ∈ M, dist X P < δ → ∃ C ⊆ M, IsPreconnected C ∧ X ∈ C ∧ P ∈ C ∧
    Bornology.IsBounded C ∧ diam C < ε

/-- *Uniformly connected im kleinen* (p. 233). -/
def UniformlyCik (M : Set Pt) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ X ∈ M, ∀ Y ∈ M, dist X Y < δ → ∃ C ⊆ M, IsPreconnected C ∧ X ∈ C ∧ Y ∈ C ∧
    Bornology.IsBounded C ∧ diam C < ε

/-- Moore's *simply connected* bounded domain (p. 235, footnote 2): "`R` contains the whole of every
bounded point-set whose boundary is a subset of `R`". -/
def MooreSimplyConnected (R : Set Pt) : Prop :=
  ∀ H : Set Pt, Bornology.IsBounded H → frontier H ⊆ R → H ⊆ R

/-- A set lying in a closed ball of radius `r` has diameter `≤ 2r`. -/
theorem diam_le_of_subset_closedBall' {S : Set Pt} {c : Pt} {r : ℝ} (hr : 0 ≤ r)
    (h : S ⊆ closedBall c r) : diam S ≤ 2 * r :=
  (diam_mono h isBounded_closedBall).trans (diam_closedBall hr)

/-- **Theorem 1** (p. 233). If `M` is uniformly connected im kleinen, then `M′` (the closure) is
connected im kleinen. -/
theorem moore22_theorem1 {M : Set Pt} (h : UniformlyCik M) : ∀ P ∈ closure M, CikAt (closure M) P := by
  intro P hP ε hε
  choose! d hd0 hd using h
  set e : ℕ → ℝ := fun k => ε / 16 / 2 ^ k with he
  have he0 : ∀ k, 0 < e k := fun k => by positivity
  set D : ℕ → ℝ := fun k => d (e k)
  have hD0 : ∀ k, 0 < D k := fun k => hd0 _ (he0 k)
  set δ := d (ε / 8)
  have hδ : 0 < δ := hd0 _ (by positivity)
  set m : ℕ → ℝ := fun k => min (min (min (D k) (D (k + 1))) δ) (e k) / 4
  have hm0 : ∀ k, 0 < m k := fun k => by
    have := hD0 k; have := hD0 (k + 1); have := he0 k; positivity
  have hmD : ∀ k, m k ≤ D (k + 1) / 4 := fun k =>
    div_le_div_of_nonneg_right ((min_le_left _ _).trans ((min_le_left _ _).trans
      (min_le_right _ _))) (by norm_num)
  have hmD' : ∀ k, m (k + 1) ≤ D (k + 1) / 4 := fun k =>
    div_le_div_of_nonneg_right ((min_le_left _ _).trans ((min_le_left _ _).trans
      (min_le_left _ _))) (by norm_num)
  have hmδ : ∀ k, m k ≤ δ / 4 := fun k =>
    div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) (by norm_num)
  have hme : ∀ k, m k ≤ e k := fun k => by
    have : min (min (min (D k) (D (k + 1))) δ) (e k) ≤ e k := min_le_right _ _
    have := he0 k
    simp only [m]; linarith
  have hesmall : ∀ r > 0, ∃ k, e k < r := by
    intro r hr
    obtain ⟨k, hk⟩ := exists_nat_gt (ε / 16 / r)
    refine ⟨k, ?_⟩
    have h2 : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
    have h3 : ε / 16 / r < 2 ^ k := hk.trans h2
    simp only [he]
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hr] at h3
    linarith
  refine ⟨δ / 2, half_pos hδ, fun X hX hXP => ?_⟩
  have hPk : ∀ k, ∃ Q ∈ M, dist P Q < m k := fun k => Metric.mem_closure_iff.1 hP _ (hm0 k)
  have hXk : ∀ k, ∃ Q ∈ M, dist X Q < m k := fun k => Metric.mem_closure_iff.1 hX _ (hm0 k)
  choose Pk hPkM hPkd using hPk
  choose Xk hXkM hXkd using hXk
  -- links between consecutive points
  have hlinkP : ∀ k, ∃ Ck ⊆ M, IsPreconnected Ck ∧ Pk k ∈ Ck ∧ Pk (k + 1) ∈ Ck ∧
      Bornology.IsBounded Ck ∧ diam Ck < e (k + 1) := by
    intro k
    refine hd _ (he0 _) _ (hPkM k) _ (hPkM (k + 1)) ?_
    calc dist (Pk k) (Pk (k + 1)) ≤ dist (Pk k) P + dist P (Pk (k + 1)) := dist_triangle _ _ _
      _ < m k + m (k + 1) := by rw [dist_comm]; exact add_lt_add (hPkd k) (hPkd (k + 1))
      _ ≤ D (k + 1) / 4 + D (k + 1) / 4 := add_le_add (hmD k) (hmD' k)
      _ ≤ D (k + 1) := by linarith [hD0 (k + 1)]
  have hlinkX : ∀ k, ∃ Ck ⊆ M, IsPreconnected Ck ∧ Xk k ∈ Ck ∧ Xk (k + 1) ∈ Ck ∧
      Bornology.IsBounded Ck ∧ diam Ck < e (k + 1) := by
    intro k
    refine hd _ (he0 _) _ (hXkM k) _ (hXkM (k + 1)) ?_
    calc dist (Xk k) (Xk (k + 1)) ≤ dist (Xk k) X + dist X (Xk (k + 1)) := dist_triangle _ _ _
      _ < m k + m (k + 1) := by rw [dist_comm]; exact add_lt_add (hXkd k) (hXkd (k + 1))
      _ ≤ D (k + 1) / 4 + D (k + 1) / 4 := add_le_add (hmD k) (hmD' k)
      _ ≤ D (k + 1) := by linarith [hD0 (k + 1)]
  choose CP hCPM hCPc hCP1 hCP2 hCPb hCPd using hlinkP
  choose CX hCXM hCXc hCX1 hCX2 hCXb hCXd using hlinkX
  obtain ⟨L, hLM, hLc, hXL, hPL, hLb, hLd⟩ := hd (ε / 8) (by positivity) _ (hXkM 0) _ (hPkM 0) (by
    calc dist (Xk 0) (Pk 0) ≤ dist (Xk 0) X + dist X P + dist P (Pk 0) := dist_triangle4 _ _ _ _
      _ < m 0 + δ / 2 + m 0 := by
          rw [dist_comm (Xk 0)]
          exact add_lt_add (add_lt_add (hXkd 0) hXP) (hPkd 0)
      _ ≤ δ / 4 + δ / 2 + δ / 4 := by linarith [hmδ 0]
      _ = δ := by ring)
  -- distances along the chains
  have hchainP : ∀ k, dist (Pk k) (Pk 0) ≤ ε / 16 - e k := by
    intro k
    induction k with
    | zero => simp [he]
    | succ k ih =>
      have h1 : dist (Pk (k + 1)) (Pk k) ≤ diam (CP k) := by
        rw [dist_comm]; exact dist_le_diam_of_mem (hCPb k) (hCP1 k) (hCP2 k)
      have h2 : e k = 2 * e (k + 1) := by simp only [he, pow_succ]; field_simp
      calc dist (Pk (k + 1)) (Pk 0) ≤ dist (Pk (k + 1)) (Pk k) + dist (Pk k) (Pk 0) :=
            dist_triangle _ _ _
        _ ≤ e (k + 1) + (ε / 16 - e k) := add_le_add (h1.trans (hCPd k).le) ih
        _ = ε / 16 - e (k + 1) := by rw [h2]; ring
  have hchainX : ∀ k, dist (Xk k) (Xk 0) ≤ ε / 16 - e k := by
    intro k
    induction k with
    | zero => simp [he]
    | succ k ih =>
      have h1 : dist (Xk (k + 1)) (Xk k) ≤ diam (CX k) := by
        rw [dist_comm]; exact dist_le_diam_of_mem (hCXb k) (hCX1 k) (hCX2 k)
      have h2 : e k = 2 * e (k + 1) := by simp only [he, pow_succ]; field_simp
      calc dist (Xk (k + 1)) (Xk 0) ≤ dist (Xk (k + 1)) (Xk k) + dist (Xk k) (Xk 0) :=
            dist_triangle _ _ _
        _ ≤ e (k + 1) + (ε / 16 - e k) := add_le_add (h1.trans (hCXd k).le) ih
        _ = ε / 16 - e (k + 1) := by rw [h2]; ring
  have he_le : ∀ k, e (k + 1) ≤ ε / 16 := fun k => by
    simp only [he]
    exact div_le_self (by positivity) (one_le_pow₀ (by norm_num))
  set S := L ∪ (⋃ k, CP k) ∪ (⋃ k, CX k)
  have hSM : S ⊆ M := union_subset (union_subset hLM (iUnion_subset hCPM)) (iUnion_subset hCXM)
  have hSconn : IsPreconnected S := by
    have hUP : IsPreconnected (⋃ k, CP k) :=
      IsPreconnected.iUnion_of_chain hCPc fun k => ⟨Pk (k + 1), hCP2 k, hCP1 (k + 1)⟩
    have hUX : IsPreconnected (⋃ k, CX k) :=
      IsPreconnected.iUnion_of_chain hCXc fun k => ⟨Xk (k + 1), hCX2 k, hCX1 (k + 1)⟩
    have h1 : IsPreconnected (L ∪ ⋃ k, CP k) :=
      hLc.union (Pk 0) hPL (mem_iUnion.2 ⟨0, hCP1 0⟩) hUP
    exact h1.union (Xk 0) (Or.inl hXL) (mem_iUnion.2 ⟨0, hCX1 0⟩) hUX
  -- `S` lies in the closed ball about `P₀` of radius `ε / 4`
  have hLdist : dist (Xk 0) (Pk 0) ≤ ε / 8 := (dist_le_diam_of_mem hLb hXL hPL).trans hLd.le
  have hSball : S ⊆ closedBall (Pk 0) (ε / 4) := by
    rintro z ((hz | hz) | hz)
    · rw [mem_closedBall]
      calc dist z (Pk 0) ≤ diam L := dist_le_diam_of_mem hLb hz hPL
        _ ≤ ε / 4 := by linarith
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hz
      rw [mem_closedBall]
      calc dist z (Pk 0) ≤ dist z (Pk k) + dist (Pk k) (Pk 0) := dist_triangle _ _ _
        _ ≤ e (k + 1) + (ε / 16 - e k) :=
            add_le_add ((dist_le_diam_of_mem (hCPb k) hk (hCP1 k)).trans (hCPd k).le) (hchainP k)
        _ ≤ ε / 4 := by linarith [he_le k, he0 k]
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hz
      rw [mem_closedBall]
      calc dist z (Pk 0) ≤ dist z (Xk k) + dist (Xk k) (Xk 0) + dist (Xk 0) (Pk 0) :=
            dist_triangle4 _ _ _ _
        _ ≤ e (k + 1) + (ε / 16 - e k) + ε / 8 :=
            add_le_add (add_le_add ((dist_le_diam_of_mem (hCXb k) hk (hCX1 k)).trans
              (hCXd k).le) (hchainX k)) hLdist
        _ ≤ ε / 4 := by linarith [he_le k, he0 k]
  -- `P` and `X` are limits of points of `S`
  have hPS : P ∈ closure S := by
    refine Metric.mem_closure_iff.2 fun r hr => ?_
    obtain ⟨k, hk⟩ := hesmall r hr
    exact ⟨Pk k, Or.inl (Or.inr (mem_iUnion.2 ⟨k, hCP1 k⟩)), ((hPkd k).trans_le (hme k)).trans hk⟩
  have hXS : X ∈ closure S := by
    refine Metric.mem_closure_iff.2 fun r hr => ?_
    obtain ⟨k, hk⟩ := hesmall r hr
    exact ⟨Xk k, Or.inr (mem_iUnion.2 ⟨k, hCX1 k⟩), ((hXkd k).trans_le (hme k)).trans hk⟩
  have hTS : insert X (insert P S) ⊆ closure S :=
    insert_subset hXS (insert_subset hPS subset_closure)
  have hclball : closure S ⊆ closedBall (Pk 0) (ε / 4) :=
    closure_minimal hSball isClosed_closedBall
  refine ⟨insert X (insert P S), hTS.trans (closure_mono hSM),
    hSconn.subset_closure ((subset_insert _ _).trans (subset_insert _ _)) hTS,
    mem_insert _ _, mem_insert_of_mem _ (mem_insert _ _),
    isBounded_closedBall.subset (hTS.trans hclball), ?_⟩
  calc diam (insert X (insert P S)) ≤ 2 * (ε / 4) :=
        diam_le_of_subset_closedBall' (by positivity) (hTS.trans hclball)
    _ < ε := by linarith

/-- **Theorem 2** (p. 233). Every point-set with property S is connected im kleinen. -/
theorem moore22_theorem2 {M : Set Pt} (h : PropertyS M) : ∀ P ∈ M, CikAt M P := by
  classical
  intro P hP ε hε
  obtain ⟨s, hs, hM⟩ := h ε hε
  set G : Set Pt := ⋂ A ∈ s.filter (fun A => P ∉ closure A), (closure A)ᶜ
  have hGo : IsOpen G := isOpen_biInter_finset fun A _ => isClosed_closure.isOpen_compl
  have hPG : P ∈ G := mem_iInter₂.2 fun A hA => (Finset.mem_filter.1 hA).2
  obtain ⟨δ, hδ, hδG⟩ := Metric.isOpen_iff.1 hGo P hPG
  refine ⟨δ, hδ, fun X hX hXP => ?_⟩
  rw [hM] at hX
  obtain ⟨A, hAs, hXA⟩ := mem_iUnion₂.1 hX
  obtain ⟨hAc, hAb, hAd⟩ := hs A hAs
  have hPA : P ∈ closure A := by
    by_contra hPA
    have hXG : X ∈ G := hδG (mem_ball.2 hXP)
    exact mem_iInter₂.1 hXG A (Finset.mem_filter.2 ⟨hAs, hPA⟩) (subset_closure hXA)
  have hAM : A ⊆ M := by rw [hM]; exact subset_biUnion_of_mem (u := id) hAs
  have hsub : insert P A ⊆ closure A := insert_subset hPA subset_closure
  refine ⟨insert P A, insert_subset hP hAM, hAc.subset_closure (subset_insert _ _) hsub,
    mem_insert_of_mem _ hXA, mem_insert _ _, hAb.insert P, ?_⟩
  calc diam (insert P A) ≤ diam (closure A) := diam_mono hsub hAb.closure
    _ = diam A := diam_closure A
    _ < ε := hAd

/-- **Theorem 3** (p. 234). A bounded point-set uniformly connected im kleinen has property S. -/
theorem moore22_theorem3 {M : Set Pt} (hb : Bornology.IsBounded M) (h : UniformlyCik M) :
    PropertyS M := by
  classical
  intro ε hε
  obtain ⟨δ, hδ, hU⟩ := h (ε / 3) (by positivity)
  -- `MP P`: the union of the connected subsets of `M` through `P` of diameter `< ε / 3`
  let MP : Pt → Set Pt := fun P => ⋃₀ {C | C ⊆ M ∧ IsPreconnected C ∧ P ∈ C ∧
    Bornology.IsBounded C ∧ diam C < ε / 3}
  have hMP_sub : ∀ P, MP P ⊆ M := fun P => sUnion_subset fun C hC => hC.1
  have hMP_ball : ∀ P, MP P ⊆ closedBall P (ε / 3) := by
    intro P z hz
    obtain ⟨C, ⟨-, -, hPC, hCb, hCd⟩, hzC⟩ := hz
    exact (dist_le_diam_of_mem hCb hzC hPC).trans hCd.le
  have hMP_conn : ∀ P, IsPreconnected (MP P) := fun P =>
    isPreconnected_sUnion P _ (fun C hC => hC.2.2.1) fun C hC => hC.2.1
  have hMP_near : ∀ P ∈ M, ∀ X ∈ M, dist X P < δ → X ∈ MP P := by
    intro P hP X hX hXP
    obtain ⟨C, hCM, hCc, hXC, hPC, hCb, hCd⟩ := hU X hX P hP hXP
    exact ⟨C, ⟨hCM, hCc, hPC, hCb, hCd⟩, hXC⟩
  have htb : TotallyBounded M := hb.isCompact_closure.totallyBounded.subset subset_closure
  obtain ⟨t, htM, htf, hcov⟩ := finite_approx_of_totallyBounded htb δ hδ
  refine ⟨htf.toFinset.image MP, ?_, ?_⟩
  · intro A hA
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.1 hA
    refine ⟨hMP_conn P, isBounded_closedBall.subset (hMP_ball P), ?_⟩
    calc diam (MP P) ≤ 2 * (ε / 3) := diam_le_of_subset_closedBall' (by positivity) (hMP_ball P)
      _ < ε := by linarith
  · apply Subset.antisymm
    · intro X hX
      obtain ⟨P, hPt, hXP⟩ := mem_iUnion₂.1 (hcov hX)
      exact mem_iUnion₂.2 ⟨MP P, Finset.mem_image.2 ⟨P, htf.mem_toFinset.2 hPt, rfl⟩,
        hMP_near P (htM hPt) X hX (mem_ball.1 hXP)⟩
    · refine iUnion₂_subset fun A hA => ?_
      obtain ⟨P, -, rfl⟩ := Finset.mem_image.1 hA
      exact hMP_sub P

end Moore22

end HPC.Jones
