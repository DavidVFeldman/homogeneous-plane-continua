import HPC.Moore.Sec6Th31
import HPC.Moore.Sec6Lim

/-!
# Moore, F.A. (1916), §6: Theorem 32 (batch 138, item B)

**Theorem 32.** If, in a domain `H`, `AB` is an arc, `A₁`, `D`, `B₁` are on `AB` in the order
`A A₁ D B₁ B`, `A₁X₁B₁` is an arc meeting `AB` only in `A₁`, `B₁`, and `C` is in the interior `R` of
`A₁X₁B₁DA₁`, then there is, in `H`, an arc `CB` meeting `AB` only in `B`.

Moore's proof (pp. 147–148) covers the arc from `D` towards `B` by a chain of the closed curves of
Theorem 31 (\"Class I\"), shows by a least-upper-bound argument that every interval `DP` can be so
covered, extracts an infinite chain converging to `B`, and joins `C` to `B` through it by a limit
arc. Here the same argument is organized as follows.

* `sides`: by the construction of Theorem 31 (`th31_pocket`), near a point `P` of the open arc
  there is an open set `N ∋ P` such that `N − AB` lies in two connected open sets `I₁`, `I₂`
  missing `AB`, each having every point of a segment of `AB` about `P` as a limit point.
* `side_propagate` (Moore's covering by chains of closed curves, with his \"Class I/II\"
  least-upper-bound argument replaced by connectedness of an interval): if a component `Q` of
  `O − AB` (`O` open) has a point `P` of the open arc as a limit point, then every point of the
  open arc reachable from `P` inside `O` is a limit point of `Q`.
* `accessible`: if moreover `O` contains the arc near `B`, then every point of `Q` is joined to `B`
  by an arc lying, except for `B`, in `Q`. The chain of components converging to `B` is built by
  dependent choice, the arcs through it are trimmed by first points, and the limit is an arc by
  `Gen.exists_tarc_of_seq` (Moore: \"It is easily seen that … `τ` is connected and contains no proper
  connected subset that contains `B` and `C`\").
-/

namespace HPC.Moore

open Set Topology Filter Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-- The data carried along the construction in `accessible`: an open set `O`, a point `x` of
`O − AB`, a parameter `t` (the arc beyond `t` lies in `O`), the union `Φ` of the arcs chosen so
far, and the last arc `β`. -/
structure AccState (S : Type*) where
  O : Set S
  x : S
  t : unitInterval
  Φ : Set S
  β : Set S

/-- The invariant of the construction in `accessible`. -/
@[reducible] def AccState.Inv {S : Type*} [TopologicalSpace S] (f : unitInterval → S)
    (O₀ Q : Set S) (st : AccState S) : Prop :=
  IsOpen st.O ∧ st.O ⊆ O₀ ∧ st.x ∈ st.O \ range f ∧ st.t < 1 ∧ (∀ u ∈ Ioo st.t 1, f u ∈ st.O) ∧
    (∃ u ∈ Ioo st.t 1, f u ∈ closure (connectedComponentIn (st.O \ range f) st.x)) ∧
    IsCompact st.Φ ∧ f 1 ∉ st.Φ ∧ connectedComponentIn (st.O \ range f) st.x ⊆ Q

/-- **The two sides of an arc** near one of its interior points (from the construction of
Theorem 31). *Axioms used: 1–8.* -/
theorem sides (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {f : unitInterval → S}
    (hf : @IsEmbedding _ _ _ σ.topology f) {b : unitInterval} (hb0 : 0 < b) (hb1 : b < 1)
    {W : Set S} (hW : @IsOpen S σ.topology W) (hbW : f b ∈ W) :
    letI := σ.topology
    ∃ e s : unitInterval, e < b ∧ b < s ∧ ∃ N I₁ I₂ : Set S, IsOpen N ∧ N ⊆ W ∧
      (∀ u ∈ Ioo e s, f u ∈ N) ∧ N \ range f ⊆ I₁ ∪ I₂ ∧ I₁ ⊆ N ∧ I₂ ⊆ N ∧
      IsOpen I₁ ∧ IsOpen I₂ ∧ IsPreconnected I₁ ∧ IsPreconnected I₂ ∧
      Disjoint I₁ (range f) ∧ Disjoint I₂ (range f) ∧
      ∀ u ∈ Icc e s, f u ∈ closure I₁ ∧ f u ∈ closure I₂ := by
  letI := σ.topology
  haveI := t2Space h1
  obtain ⟨R, hR, hbR, hRW⟩ := (mem_nhds_iff_region h1).mp (hW.mem_nhds hbW)
  obtain ⟨e₁, s₁, e₂, s₂, F₁, P, F₂, Pb, I₁, I₂, R₃, -, he₁e₂, he₂b, hbs₂, hs₂s₁, -, -,
    -, -, hP, hPr, -, -, hTI₁, -, -, -, hPb, hPbr, -, -, hTI₂, hR₃o, -, hR₃eq, -, hI₁K, hI₂K,
    hR₃R⟩ := th31_pocket h1 h2 h3 h4 h5 h6 h7 h8 hf hb0 hb1 hR hbR
  have hinj := hf.injective
  refine ⟨e₂, s₂, he₂b, hbs₂, R₃, I₁, I₂, hR₃o, hR₃R.trans hRW, ?_, ?_, ?_, ?_,
    isOpen_region hTI₁.2.1, isOpen_region hTI₂.2.1, hpc_region h1 h2 _ hTI₁.2.1,
    hpc_region h1 h2 _ hTI₂.2.1, hI₁K, hI₂K, ?_⟩
  · intro u hu
    rw [hR₃eq]
    refine Or.inl (Or.inl ⟨image_Icc_subset_of_arc hf hPb hPbr
      (mem_image_of_mem f (Ioo_subset_Icc_self hu)), ?_⟩)
    rintro (e | e)
    · exact hu.1.ne' (hinj e)
    · exact hu.2.ne (hinj e)
  · rintro x ⟨hx, hxK⟩
    rw [hR₃eq] at hx
    rcases hx with (h | h) | h
    · exact absurd (hPbr h.1) hxK
    · exact Or.inl h
    · exact Or.inr h
  · intro x hx; rw [hR₃eq]; exact Or.inl (Or.inr hx)
  · intro x hx; rw [hR₃eq]; exact Or.inr hx
  · intro u hu
    refine ⟨frontier_subset_closure ?_, frontier_subset_closure ?_⟩
    · rw [hTI₁.2.2]
      exact Or.inr (image_Icc_subset_of_arc hf hP hPr
        (mem_image_of_mem f ⟨he₁e₂.le.trans hu.1, hu.2.trans hs₂s₁.le⟩))
    · rw [hTI₂.2.2]
      exact Or.inr (image_Icc_subset_of_arc hf hPb hPbr (mem_image_of_mem f hu))

/-- **Propagation along the arc** (Moore's covering of `DP` by chains of the closed curves of
Theorem 31, with the \"Class I / Class II\" argument replaced by connectedness of an interval): if a
component of `O − AB` has a point of the open arc `AB` as a limit point, then so is every point of
the open arc that is joined to it by an interval of the arc inside `O`. *Axioms used: 1–8.* -/
theorem side_propagate (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {f : unitInterval → S}
    (hf : @IsEmbedding _ _ _ σ.topology f) {O : Set S} (hO : @IsOpen S σ.topology O) {x₀ : S}
    {J : Set unitInterval} (hJ : IsPreconnected J) (hJ01 : J ⊆ Ioo 0 1)
    (hJO : ∀ u ∈ J, f u ∈ O) {u₀ : unitInterval} (hu₀ : u₀ ∈ J)
    (hadj : f u₀ ∈ @closure S σ.topology (@connectedComponentIn S σ.topology (O \ range f) x₀)) :
    ∀ u ∈ J, f u ∈ @closure S σ.topology (@connectedComponentIn S σ.topology (O \ range f) x₀) := by
  letI := σ.topology
  set Q := connectedComponentIn (O \ range f) x₀ with hQ
  set T : Set unitInterval := {u | f u ∈ closure Q} with hT
  have key : ∀ u ∈ J, ∃ e s : unitInterval, e < u ∧ u < s ∧
      (f u ∈ closure Q → ∀ v ∈ Ioo e s, f v ∈ closure Q) ∧
      ((∃ v ∈ Ioo e s, f v ∈ closure Q) → f u ∈ closure Q) := by
    intro u hu
    obtain ⟨e, s, heu, hus, N, I₁, I₂, hNo, hNO, hNf, hNI, hI₁N, hI₂N, -, -, hI₁c, hI₂c, hI₁K,
      hI₂K, hcl⟩ := sides h1 h2 h3 h4 h5 h6 h7 h8 hf (hJ01 hu).1 (hJ01 hu).2 hO (hJO u hu)
    have hmeet : ∀ z ∈ Q, z ∈ N → I₁ ⊆ Q ∨ I₂ ⊆ Q := by
      intro z hzQ hzN
      have hzK : z ∉ range f := (connectedComponentIn_subset _ _ hzQ).2
      have hQz : Q = connectedComponentIn (O \ range f) z := connectedComponentIn_eq hzQ
      rcases hNI ⟨hzN, hzK⟩ with h | h
      · left
        rw [hQz]
        exact hI₁c.subset_connectedComponentIn h fun y hy =>
          ⟨hNO (hI₁N hy), disjoint_left.mp hI₁K hy⟩
      · right
        rw [hQz]
        exact hI₂c.subset_connectedComponentIn h fun y hy =>
          ⟨hNO (hI₂N hy), disjoint_left.mp hI₂K hy⟩
    have hclos : ∀ z ∈ Q, z ∈ N → ∀ v ∈ Icc e s, f v ∈ closure Q := by
      intro z hzQ hzN v hv
      rcases hmeet z hzQ hzN with h | h
      · exact closure_mono h (hcl v hv).1
      · exact closure_mono h (hcl v hv).2
    refine ⟨e, s, heu, hus, fun h v hv => ?_, fun ⟨v, hv, hvQ⟩ => ?_⟩
    · obtain ⟨z, hzN, hzQ⟩ := mem_closure_iff_nhds.mp h N (hNo.mem_nhds (hNf u ⟨heu, hus⟩))
      exact hclos z hzQ hzN v (Ioo_subset_Icc_self hv)
    · obtain ⟨z, hzN, hzQ⟩ := mem_closure_iff_nhds.mp hvQ N (hNo.mem_nhds (hNf v hv))
      exact hclos z hzQ hzN u ⟨heu.le, hus.le⟩
  have hsub : J ⊆ interior T ∪ (closure T)ᶜ := by
    intro u hu
    obtain ⟨e, s, heu, hus, hk1, hk2⟩ := key u hu
    by_cases h : f u ∈ closure Q
    · left
      exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (Ioo_mem_nhds heu hus) (hk1 h))
    · right
      intro hcl
      obtain ⟨v, hv, hvT⟩ := mem_closure_iff_nhds.mp hcl _ (Ioo_mem_nhds heu hus)
      exact h (hk2 ⟨v, hv, hvT⟩)
  have hJT := hJ.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left (interior_subset.trans subset_closure)) hsub
    (by
      obtain ⟨e, s, heu, hus, hk1, -⟩ := key u₀ hu₀
      exact ⟨u₀, hu₀, mem_interior_iff_mem_nhds.mpr
        (mem_of_superset (Ioo_mem_nhds heu hus) (hk1 hadj))⟩)
  intro u hu
  exact (interior_subset (hJT hu) : u ∈ T)

/-- **Accessibility of the end `B`** (the substance of Theorem 32). If `O` is open, the arc
`f` lies in `O` beyond `t₀`, and the component `Q` of `O − AB` containing `x₀` has a point of the
arc beyond `t₀` as a limit point, then `x₀` is joined to `B = f 1` by an arc lying, except for `B`,
in `Q`. *Axioms used: 1–8.* -/
theorem accessible (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {f : unitInterval → S}
    (hf : @IsEmbedding _ _ _ σ.topology f) {O : Set S} (hO : @IsOpen S σ.topology O)
    {t₀ : unitInterval} (ht₀ : t₀ < 1) (hO' : ∀ u ∈ Ioo t₀ 1, f u ∈ O) {x₀ : S}
    (hx₀ : x₀ ∈ O \ range f)
    (hadj : ∃ u ∈ Ioo t₀ 1,
      f u ∈ @closure S σ.topology (@connectedComponentIn S σ.topology (O \ range f) x₀)) :
    ∃ τ, @TArc S σ.topology x₀ (f 1) τ ∧
      τ ⊆ insert (f 1) (@connectedComponentIn S σ.topology (O \ range f) x₀) := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  haveI := metrizable h1 h3 h51
  have harc := arcConn h1 h3 h4 h51 h2
  have hKc : IsClosed (range f) := (isCompact_range hf.continuous).isClosed
  set Q := connectedComponentIn (O \ range f) x₀ with hQ
  obtain ⟨U, hU⟩ := (𝓝 (f 1)).exists_antitone_basis
  have step : ∀ (n : ℕ) (st : AccState S), st.Inv f O Q → ∃ st' : AccState S, st'.Inv f O Q ∧
      st'.O ⊆ st.O ∩ (st.Φ ∪ {st.x})ᶜ ∧ st'.O ⊆ U (n + 1) ∧ TArc st.x st'.x st'.β ∧
      st'.β ⊆ connectedComponentIn (st.O \ range f) st.x ∧ st'.Φ = st.Φ ∪ st'.β := by
    intro n st hst
    obtain ⟨hOo, hOO, hx, ht1, hft, hadj', hΦc, hΦB, hcc⟩ := hst
    set V := connectedComponentIn (st.O \ range f) st.x with hV
    have hVo : IsOpen V := (hOo.sdiff hKc).connectedComponentIn
    have hVpc : IsPreconnected V := isPreconnected_connectedComponentIn
    have hxV : st.x ∈ V := mem_connectedComponentIn hx
    have hFc : IsClosed (st.Φ ∪ {st.x}) := (hΦc.union isCompact_singleton).isClosed
    have hWo : IsOpen (interior (U (n + 1)) ∩ (st.Φ ∪ {st.x})ᶜ) :=
      isOpen_interior.inter hFc.isOpen_compl
    have hBW : f 1 ∈ interior (U (n + 1)) ∩ (st.Φ ∪ {st.x})ᶜ := by
      refine ⟨mem_interior_iff_mem_nhds.mpr (hU.mem (n + 1)), ?_⟩
      rintro (h | h)
      · exact hΦB h
      · exact hx.2 (by rw [← mem_singleton_iff.mp h]; exact mem_range_self 1)
    set O₂ := st.O ∩ (interior (U (n + 1)) ∩ (st.Φ ∪ {st.x})ᶜ) with hO₂
    have hO₂o : IsOpen O₂ := hOo.inter hWo
    obtain ⟨t'', ht''1, ht''⟩ := exists_Ioc_subset_of_mem_nhds
      ((hWo.preimage hf.continuous).mem_nhds hBW) ⟨0, zero_lt_one' _⟩
    set t' := max st.t t'' with ht'
    have ht'1 : t' < 1 := max_lt ht1 ht''1
    have hft' : ∀ u ∈ Ioo t' 1, f u ∈ O₂ := fun u hu =>
      ⟨hft u ⟨(le_max_left _ _).trans_lt hu.1, hu.2⟩,
        ht'' ⟨(le_max_right _ _).trans_lt hu.1, hu.2.le⟩⟩
    obtain ⟨v, hv1, hv2⟩ := exists_between ht'1
    have hvt : v ∈ Ioo st.t 1 := ⟨(le_max_left _ _).trans_lt hv1, hv2⟩
    have hvV : f v ∈ closure V := by
      obtain ⟨u₀, hu₀, hu₀V⟩ := hadj'
      exact side_propagate h1 h2 h3 h4 h5 h6 h7 h8 hf hOo isPreconnected_Ioo
        (fun u hu => ⟨nonneg'.trans_lt hu.1, hu.2⟩) hft hu₀ hu₀V v hvt
    have hv0 : 0 < v := nonneg'.trans_lt hv1
    obtain ⟨e, s, hev, hvs, N, I₁, I₂, hNo, hNO, hNf, hNI, hI₁N, hI₂N, -, -, hI₁c, hI₂c, hI₁K,
      hI₂K, hcl⟩ := sides h1 h2 h3 h4 h5 h6 h7 h8 hf hv0 hv2 hO₂o (hft' v ⟨hv1, hv2⟩)
    obtain ⟨z, hzN, hzV⟩ := mem_closure_iff_nhds.mp hvV N (hNo.mem_nhds (hNf v ⟨hev, hvs⟩))
    have hzK : z ∉ range f := (connectedComponentIn_subset _ _ hzV).2
    obtain ⟨I, hIN, hIc, hIK, hvI, hzI⟩ : ∃ I, I ⊆ N ∧ IsPreconnected I ∧ Disjoint I (range f) ∧
        f v ∈ closure I ∧ z ∈ I := by
      rcases hNI ⟨hzN, hzK⟩ with h | h
      · exact ⟨I₁, hI₁N, hI₁c, hI₁K, (hcl v ⟨hev.le, hvs.le⟩).1, h⟩
      · exact ⟨I₂, hI₂N, hI₂c, hI₂K, (hcl v ⟨hev.le, hvs.le⟩).2, h⟩
    have hzO₂ : z ∈ O₂ \ range f := ⟨hNO hzN, hzK⟩
    have hzx : st.x ≠ z := fun e => (hNO hzN).2.2 (Or.inr e.symm)
    obtain ⟨β, hβV, hβ⟩ := harc V hVo hVpc st.x hxV z hzV hzx
    refine ⟨⟨O₂, z, t', st.Φ ∪ β, β⟩, ⟨hO₂o, fun y hy => hOO hy.1, hzO₂, ht'1, hft',
      ⟨v, ⟨hv1, hv2⟩, ?_⟩, hΦc.union hβ.isCompact, ?_, ?_⟩, fun y hy => ⟨hy.1, hy.2.2⟩,
      fun y hy => interior_subset hy.2.1, hβ, hβV, rfl⟩
    · exact closure_mono (hIc.subset_connectedComponentIn (F := O₂ \ range f) hzI fun y hy =>
        ⟨hNO (hIN hy), disjoint_left.mp hIK hy⟩) hvI
    · rintro (h | h)
      · exact hΦB h
      · exact (connectedComponentIn_subset _ _ (hβV h)).2 (mem_range_self 1)
    · calc connectedComponentIn (O₂ \ range f) z
          ⊆ connectedComponentIn (st.O \ range f) z :=
            connectedComponentIn_mono _ (diff_subset_diff_left fun y hy => hy.1)
        _ = V := (connectedComponentIn_eq hzV).symm
        _ ⊆ Q := hcc
  choose! next hnext using step
  let seq : ℕ → AccState S := fun n => Nat.rec ⟨O, x₀, t₀, ∅, ∅⟩ (fun k s => next k s) n
  have hseq : ∀ n, seq (n + 1) = next n (seq n) := fun n => rfl
  have hinv : ∀ n, (seq n).Inv f O Q := by
    intro n
    induction n with
    | zero => exact ⟨hO, subset_rfl, hx₀, ht₀, hO', hadj, isCompact_empty, notMem_empty _,
        subset_rfl⟩
    | succ n ih => rw [hseq]; exact (hnext n _ ih).1
  have hrel : ∀ n, (seq (n + 1)).O ⊆ (seq n).O ∩ ((seq n).Φ ∪ {(seq n).x})ᶜ ∧
      (seq (n + 1)).O ⊆ U (n + 1) ∧ TArc (seq n).x (seq (n + 1)).x (seq (n + 1)).β ∧
      (seq (n + 1)).β ⊆ connectedComponentIn ((seq n).O \ range f) (seq n).x ∧
      (seq (n + 1)).Φ = (seq n).Φ ∪ (seq (n + 1)).β := fun n => by
    rw [hseq]; exact (hnext n (seq n) (hinv n)).2
  have hanti : ∀ n m, n ≤ m → (seq m).O ⊆ (seq n).O := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact subset_rfl
    | succ m _ ih => exact fun y hy => ih ((hrel m).1 hy).1
  have hβQ : ∀ n, (seq (n + 1)).β ⊆ connectedComponentIn ((seq n).O \ range f) (seq n).x :=
    fun n => (hrel n).2.2.2.1
  have hβO : ∀ n, (seq (n + 1)).β ⊆ (seq n).O := fun n y hy =>
    (connectedComponentIn_subset _ _ (hβQ n hy)).1
  obtain ⟨τ, hτ, hτarc⟩ := exists_tarc_of_seq (x := fun n => (seq n).x)
    (β := fun n => (seq (n + 1)).β) (B := f 1) (fun n => (hrel n).2.2.1)
    (fun n m hnm => by
      rw [disjoint_left]
      intro y hyn hym
      have h1' : y ∈ (seq (n + 1 + 1)).O := hanti (n + 1 + 1) m (by omega) (hβO m hym)
      have h2' := ((hrel (n + 1)).1 h1').2
      exact h2' (Or.inl (by rw [(hrel n).2.2.2.2]; exact Or.inr hyn)))
    (fun h => ((hrel 0).1 (hβO 1 h)).2 (Or.inr rfl))
    (fun n h => (connectedComponentIn_subset _ _ (hβQ n h)).2 (mem_range_self 1))
    (fun W hW => by
      obtain ⟨i, hi⟩ := hU.mem_iff.mp hW
      refine eventually_atTop.mpr ⟨i + 1, fun n hn => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact (hβO (m + 1)).trans ((hrel m).2.1.trans ((hU.antitone (by omega)).trans hi)))
  refine ⟨τ, hτarc, hτ.trans ?_⟩
  rintro y (rfl | hy)
  · exact mem_insert _ _
  · obtain ⟨n, hn⟩ := mem_iUnion.mp hy
    exact Or.inr ((hinv n).2.2.2.2.2.2.2.2 (hβQ n hn))

/-- **Theorem 32.** If, in a domain `H`, `A`, `A₁`, `D`, `B₁`, `B` are points of the arc `AB` in this
order, `R` is the interior of a closed curve `A₁X₁B₁DA₁` (`D` on its boundary), `R ⊆ H`, `R` has no
point in common with `AB`, and `C ∈ R`, then there is in `H` an arc `CB` which has no point except
`B` in common with `AB`. *Axioms used: 1–8.* Proof: `accessible` (Moore's chains of closed curves
and limit arc), applied to the component of `H − AB` containing `R`, which has `D` as a limit
point.

**Shape changes (check 4).** (a) *Added:* `R` has no point in common with `AB` (`hRK`). Without it
the statement can fail: nothing prevents a part of `AB` beyond `A₁` or `B₁` from lying in `R`, and a
point `C` of `AB` in `R` (other than `B`) cannot be joined to `B` by an arc meeting `AB` only in
`B`. Moore's proof uses the pockets of Theorem 31, which miss `AB`; Theorems 33 and 34 below use
Theorem 32 only in that form. (b) *Dropped as unused:* the skeleton's `X₁ ⊆ H` (only `R ⊆ H` is
needed), the arc hypotheses on `A₁X₁B₁` and on the segment `A₁DB₁`, and `IsArc A B K` (implied by
`hord`); only `D ∈ seg` (so `D` is on the boundary of `R`) is used. The axioms are made explicit. -/
theorem fa_theorem32 (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {Hd : Set S}
    (hH : σ.IsDomain Hd) {A B A₁ D B₁ : S} {K : Set S} (hKH : K ⊆ Hd)
    (hord : σ.InOrder K A B [A, A₁, D, B₁, B]) {X₁ seg : Set S} (hDseg : D ∈ seg)
    {R : Set S} (hR : σ.IsInteriorOf (X₁ ∪ seg) R) (hRH : R ⊆ Hd) (hRK : Disjoint R K)
    {C : S} (hC : C ∈ R) :
    ∃ CB : Set S, σ.IsArc C B CB ∧ CB ⊆ Hd ∧ CB ∩ K = {B} := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have hHo : IsOpen Hd := (isOpen_iff_region h1).mpr hH.2
  obtain ⟨φ, hφ, hφr, hφ0, hφ1, ts, hts, hpts⟩ := hord
  obtain _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, _ | ⟨t4, _ | ⟨t5, ts⟩⟩⟩⟩⟩⟩ := ts <;>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, reduceCtorEq, and_false] at hpts
  obtain ⟨-, -, rfl, -, -⟩ := hpts
  rw [← List.isChain_iff_pairwise] at hts
  simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true] at hts
  obtain ⟨h01, h12, h23, h34⟩ := hts
  subst hφr
  have hRK' : R ⊆ Hd \ range φ := fun x hx => ⟨hRH hx, disjoint_left.mp hRK hx⟩
  have hRQ : R ⊆ connectedComponentIn (Hd \ range φ) C :=
    (hpc_region h1 h2 R hR.2.1).subset_connectedComponentIn hC hRK'
  have hDfr : φ t2 ∈ frontier R := by
    rw [← bdry_eq_frontier h1, hR.2.2]; exact Or.inr hDseg
  obtain ⟨τ, hτ, hτQ⟩ := accessible h1 h2 h3 h4 h5 h6 h7 h8 hφ hHo (t₀ := t1)
    (h23.trans h34 |>.trans_le le_one' |> h12.trans) (fun u _ => hKH (mem_range_self u))
    (hRK' hC) ⟨t2, ⟨h12, (h23.trans h34).trans_le le_one'⟩,
      closure_mono hRQ (frontier_subset_closure hDfr)⟩
  rw [hφ1] at hτ hτQ
  refine ⟨τ, (isArc_iff_tarc h1 h3 h4 h51).mpr hτ, fun x hx => ?_, ?_⟩
  · rcases hτQ hx with rfl | h
    · rw [← hφ1]; exact hKH (mem_range_self 1)
    · exact (connectedComponentIn_subset _ _ h).1
  · ext x
    constructor
    · rintro ⟨hx, hxK⟩
      rcases hτQ hx with rfl | h
      · rfl
      · exact absurd hxK (connectedComponentIn_subset _ _ h).2
    · rintro rfl
      exact ⟨hτ.right_mem, hφ1 ▸ mem_range_self 1⟩

end HPC.Moore
