import HPC.Moore.Sec4
import HPC.Moore.Chains
import HPC.Moore.ArcChar

/-!
# Moore, F.A. (1916), §4: Theorem 15 (nested simple chains) and Theorem 16 (batch 137, item C)

**Theorem 15.** Two distinct points `A`, `B` of a domain `M` are joined by an arc in `M`.

Moore's proof (pp. 136–139), formalized:

* **The chains.** A sequence of simple chains `C₁, C₂, …` from `A` to `B` such that (1) each link
  of `Cₙ₊₁` lies, with its limit points, in a single link of `Cₙ`; (2) the links of `Cₙ₊₁` that
  lie in a given link of `Cₙ` come in order (the "owner" map is monotone); (3) the links of `Cₙ`
  are small. Moore takes the links of `Cₙ` from `Kₙ, Kₙ₊₁, …` for (3); here (shape change) the
  links of `Cₙ` lie in balls of radius `1/(n+1)` for a metric compatible with the topology (the
  bridge makes the space metrizable). Each `Cₙ₊₁` is built as Moore does: points `pᵢ` common to
  consecutive links of `Cₙ`, chains of small regions from `pᵢ` to `pᵢ₊₁` inside the `i`-th link
  (Theorem 10), laid end to end, and simplified (`exists_simpleChain_sublist`, which keeps the
  order of the links, hence (2)).
* **I, II.** `C = ⋂ₙ (sum of the links of Cₙ)` is closed and connected: it is the intersection of
  the decreasing continua `⋃ (links of Cₙ)'`.
* **III.** `X₁ ≺ X₂` iff at some stage every link containing `X₁` precedes every link containing
  `X₂`. This persists to later stages (monotone owners). For a point `P ≠ A, B`, the sets `S_A`,
  `S_B` of points before and after `P` separate `C − P`. Moore's step "no region of `Cₙ` that
  contains `P_A` contains any point of `S_B`" is completed here by choosing `n` so large that no
  two links of `Cₙ` that meet contain `P_A` and `P` respectively (smallness); then every point of
  `C` in a link containing `P_A` precedes `P`.

*Axioms used:* 1, 2, 4 for the construction; 3 and 5₁ only through metrizability.
-/

namespace HPC.Moore

open Set Topology Metric

section Generic

variable {X : Type*}

/-- Two weak chains laid end to end. -/
theorem IsWeakChain.append' {A B C : X} {l₁ l₂ : List (Set X)} (h₁ : IsWeakChain A B l₁)
    (h₂ : IsWeakChain B C l₂) : IsWeakChain A C (l₁ ++ l₂) := by
  obtain ⟨hp₁, hA, hB₁, hc₁⟩ := h₁
  obtain ⟨hp₂, hB₂, hC, hc₂⟩ := h₂
  refine ⟨by simp; omega, ?_, ?_, ?_⟩
  · rw [List.getElem_append_left hp₁]; exact hA
  · rw [List.getElem_append_right (by simp; omega)]
    convert hC using 2; simp; omega
  · intro i hi
    simp only [List.length_append] at hi
    by_cases h : i + 1 < l₁.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left h]
      exact hc₁ i h
    by_cases h' : i + 1 = l₁.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
      refine ⟨B, ?_, ?_⟩
      · convert hB₁ using 2; omega
      · convert hB₂ using 2; omega
    · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      have := hc₂ (i - l₁.length) (by omega)
      convert this using 3; omega

variable [TopologicalSpace X]

/-- **Theorem 10, weak form, topologically.** In a preconnected set covered by a family of open
sets, any two points are joined by a weak chain of members of the family. -/
theorem exists_weakChain_of_isPreconnected {M : Set X} (hM : IsPreconnected M)
    {G : Set (Set X)} (hGo : ∀ R ∈ G, IsOpen R) (hMG : M ⊆ ⋃₀ G) {P Q : X} (hP : P ∈ M)
    (hQ : Q ∈ M) : ∃ l : List (Set X), (∀ R ∈ l, R ∈ G) ∧ IsWeakChain P Q l := by
  set T : Set X := {x | ∃ l : List (Set X), (∀ R ∈ l, R ∈ G) ∧ IsWeakChain P x l} with hT
  set V : Set X := ⋃₀ {R ∈ G | Disjoint R T} with hV
  have hTo : IsOpen T := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨l, hlG, hpos, hP0, hxl, hch⟩
    refine ⟨l[l.length - 1], fun y hy => ⟨l, hlG, hpos, hP0, hy, hch⟩,
      hGo _ (hlG _ (List.getElem_mem _)), hxl⟩
  have hVo : IsOpen V := isOpen_sUnion fun R hR => hGo R hR.1
  have hsub : M ⊆ T ∪ V := by
    intro x hx
    obtain ⟨R, hRG, hxR⟩ := hMG hx
    by_cases h : Disjoint R T
    · exact Or.inr ⟨R, ⟨hRG, h⟩, hxR⟩
    · obtain ⟨y, hyR, l, hlG, hl⟩ := not_disjoint_iff.mp h
      refine Or.inl ⟨l ++ [R], fun Z hZ => ?_, hl.append_single hyR hxR⟩
      rcases List.mem_append.mp hZ with hZ | hZ
      · exact hlG Z hZ
      · rw [List.mem_singleton.mp hZ]; exact hRG
  have hPT : P ∈ T := by
    obtain ⟨R, hRG, hPR⟩ := hMG hP
    exact ⟨[R], by simpa using hRG, by simp, by simpa using hPR, by simpa using hPR,
      fun i hi => by simp at hi⟩
  have hdisj : ∀ z, z ∈ T → z ∈ V → False := by
    rintro z hzT ⟨R, ⟨-, hR⟩, hzR⟩
    exact hR.ne_of_mem hzR hzT rfl
  rcases hsub hQ with hQT | hQV
  · exact hQT
  · obtain ⟨z, -, hzT, hzV⟩ := hM T V hTo hVo hsub ⟨P, hP, hPT⟩ ⟨Q, hQ, hQV⟩
    exact (hdisj z hzT hzV).elim

/-- The sum of a weak chain of preconnected sets is preconnected. -/
theorem isPreconnected_biUnion_chain {l : List (Set X)} (hc : ∀ R ∈ l, IsPreconnected R)
    (hmeet : ∀ i (hi : i + 1 < l.length), (l[i] ∩ l[i + 1]).Nonempty) :
    IsPreconnected (⋃ R ∈ l, R) := by
  induction l with
  | nil => simpa using isPreconnected_empty
  | cons R t ih =>
    have ht : IsPreconnected (⋃ R ∈ t, R) := ih (fun R hR => hc R (List.mem_cons_of_mem _ hR))
      fun i hi => by simpa using hmeet (i + 1) (by simp; omega)
    rw [show (⋃ Z ∈ R :: t, Z) = R ∪ ⋃ Z ∈ t, Z by simp]
    rcases t with _ | ⟨R', t'⟩
    · simpa using hc R (by simp)
    · obtain ⟨x, hx1, hx2⟩ := hmeet 0 (by simp)
      exact (hc R (by simp)).union' ⟨x, hx1, mem_biUnion (x := R') List.mem_cons_self hx2⟩ ht

end Generic

section NestedInter

variable {X : Type*} [MetricSpace X]

/-- A nested intersection of compact preconnected sets is preconnected. -/
theorem moore_isPreconnected_sInter_chain {c : Set (Set X)} (hne : c.Nonempty)
    (hch : IsChain (· ⊆ ·) c) (hcpt : ∀ W ∈ c, IsCompact W) (hconn : ∀ W ∈ c, IsPreconnected W) :
    IsPreconnected (⋂₀ c) := by
  obtain ⟨W₀, hW₀⟩ := hne
  have hclosed : IsClosed (⋂₀ c) := isClosed_sInter fun W hW => (hcpt W hW).isClosed
  have hcK : IsCompact (⋂₀ c) := (hcpt W₀ hW₀).of_isClosed_subset hclosed (sInter_subset_of_mem hW₀)
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hclosed]
  intro u v hu hv hsub hdisj
  set u' := u ∩ ⋂₀ c with hu'_def
  set v' := v ∩ ⋂₀ c with hv'_def
  have hu' : IsCompact u' := hcK.inter_left hu
  have hv' : IsClosed v' := hv.inter hclosed
  have hdisj' : Disjoint u' v' := hdisj.mono inter_subset_left inter_subset_left
  have hsub' : ⋂₀ c ⊆ u' ∪ v' := fun x hx =>
    (hsub hx).imp (fun h => ⟨h, hx⟩) (fun h => ⟨h, hx⟩)
  obtain ⟨δ, hδ, hδd⟩ := hdisj'.exists_thickenings hu' hv'
  have hopen : IsOpen (Metric.thickening δ u' ∪ Metric.thickening δ v') :=
    Metric.isOpen_thickening.union Metric.isOpen_thickening
  haveI : Nonempty c := ⟨⟨W₀, hW₀⟩⟩
  obtain ⟨⟨W, hWc⟩, hW⟩ : ∃ i : c, (i : Set X) ⊆ Metric.thickening δ u' ∪
      Metric.thickening δ v' := by
    refine exists_subset_nhds_of_isCompact' (V := fun i : c => (i : Set X)) ?_
      (fun i => hcpt _ i.2) (fun i => (hcpt _ i.2).isClosed) ?_
    · intro i j
      rcases hch.total i.2 j.2 with h | h
      · exact ⟨i, le_rfl, h⟩
      · exact ⟨j, h, le_rfl⟩
    · intro x hx
      refine hopen.mem_nhds ?_
      have hx' : x ∈ ⋂₀ c := by
        rw [sInter_eq_iInter]; simpa using hx
      rcases hsub' hx' with h | h
      · exact Or.inl (Metric.self_subset_thickening hδ _ h)
      · exact Or.inr (Metric.self_subset_thickening hδ _ h)
  have hLW : ⋂₀ c ⊆ W := sInter_subset_of_mem hWc
  rcases isPreconnected_iff_subset_of_disjoint.mp (hconn W hWc) _ _ Metric.isOpen_thickening
      Metric.isOpen_thickening hW (by
        rw [hδd.inter_eq]; exact inter_empty _) with h | h
  · left
    intro z hz
    rcases hsub' hz with h' | h'
    · exact h'.1
    · exact absurd ⟨h (hLW hz), Metric.self_subset_thickening hδ _ h'⟩ (fun h2 => hδd.le_bot h2)
  · right
    intro z hz
    rcases hsub' hz with h' | h'
    · exact absurd ⟨Metric.self_subset_thickening hδ _ h', h (hLW hz)⟩ (fun h2 => hδd.le_bot h2)
    · exact h'.1

/-- A decreasing sequence of compact preconnected sets has preconnected intersection. -/
theorem moore_isPreconnected_iInter {K : ℕ → Set X} (hanti : Antitone K)
    (hcpt : ∀ n, IsCompact (K n)) (hconn : ∀ n, IsPreconnected (K n)) :
    IsPreconnected (⋂ n, K n) := by
  rw [← sInter_range]
  refine moore_isPreconnected_sInter_chain (range_nonempty K) ?_ (by
    rintro _ ⟨n, rfl⟩; exact hcpt n) (by rintro _ ⟨n, rfl⟩; exact hconn n)
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ -
  rcases le_total m n with h | h
  · exact Or.inr (hanti h)
  · exact Or.inl (hanti h)

end NestedInter

section SimpleChain

variable {X : Type*} {σ : Space X}

/-- A simple chain is a weak chain. -/
theorem Space.IsSimpleChain.isWeakChain {A B : X} {l : List (Set X)} (h : σ.IsSimpleChain A B l) :
    IsWeakChain A B l := by
  obtain ⟨-, hne, -, hA, hB, hch⟩ := h
  have hpos : 0 < l.length := List.length_pos_iff.mpr hne
  refine ⟨hpos, (hA 0 hpos).mpr rfl, (hB _ (by omega)).mpr (by omega), fun i hi => ?_⟩
  exact (hch i (i + 1) (by omega) hi (by omega)).mpr rfl

/-- In a simple chain, a point lies only in links with adjacent indices. -/
theorem Space.IsSimpleChain.adjacent {A B : X} {l : List (Set X)} (h : σ.IsSimpleChain A B l)
    {Y : X} {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hYi : Y ∈ l[i]) (hYj : Y ∈ l[j]) :
    i ≤ j + 1 ∧ j ≤ i + 1 := by
  obtain ⟨-, -, -, -, -, hch⟩ := h
  rcases lt_trichotomy i j with hij | rfl | hij
  · have := (hch i j hi hj hij).mp ⟨Y, hYi, hYj⟩
    omega
  · omega
  · have := (hch j i hj hi hij).mp ⟨Y, hYj, hYi⟩
    omega

end SimpleChain

section Refine

variable {X : Type*} [MetricSpace X] {σ : Space X}

/-- **The refinement step** (Moore, p. 137). Given a weak chain `Ls` of connected open sets from
`A` to `B ≠ A`, there is a simple chain of small regions from `A` to `B` each of whose links lies,
with its closure, in a link of `Ls`, the owners coming in order. -/
theorem exists_refine (hopen : ∀ R ∈ σ.region, IsOpen R)
    (hsmall : ∀ U : Set X, IsOpen U → ∀ x ∈ U, ∀ ε > 0,
      ∃ R ∈ σ.region, x ∈ R ∧ closure R ⊆ U ∧ R ⊆ ball x ε)
    {A B : X} (hAB : A ≠ B) {Ls : List (Set X)} (hLo : ∀ L ∈ Ls, IsOpen L)
    (hLc : ∀ L ∈ Ls, IsPreconnected L) (hLw : IsWeakChain A B Ls) {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List (Set X), σ.IsSimpleChain A B l ∧ (∀ L ∈ l, ∃ x, L ⊆ ball x ε) ∧
      ∃ o : ℕ → ℕ, Monotone o ∧
        ∀ j (hj : j < l.length), ∃ ho : o j < Ls.length, closure l[j] ⊆ Ls[o j] := by
  classical
  obtain ⟨hpos, hA0, hBk, hch⟩ := hLw
  set k := Ls.length with hk
  -- the points `p i`
  have hq : ∀ i, ∃ y : X, ∀ h : i + 1 < k, y ∈ Ls[i] ∧ y ∈ Ls[i + 1] := by
    intro i
    by_cases h : i + 1 < k
    · obtain ⟨y, hy⟩ := hch i h
      exact ⟨y, fun _ => hy⟩
    · exact ⟨A, fun h' => absurd h' h⟩
  choose q hq using hq
  set p : ℕ → X := fun i => if i = 0 then A else if i < k then q (i - 1) else B with hp
  have hp1 : ∀ i (hi : i < k), p i ∈ Ls[i] := by
    intro i hi
    by_cases h0 : i = 0
    · subst h0; simpa [hp] using hA0
    · have := (hq (i - 1) (by omega)).2
      simp only [hp, h0, hi, if_false, if_true]
      convert this using 2; omega
  have hp2 : ∀ i (hi : i < k), p (i + 1) ∈ Ls[i] := by
    intro i hi
    by_cases h : i + 1 < k
    · have := (hq i h).1
      simpa [hp, h] using this
    · have hik : i = k - 1 := by omega
      have : ¬ (i + 1 < k) := h
      simp only [hp, Nat.add_one_ne_zero, this, if_false]
      convert hBk using 2
  -- the covers
  set G : ℕ → Set (Set X) := fun i =>
    {R | R ∈ σ.region ∧ (∃ h : i < k, closure R ⊆ Ls[i]) ∧ ∃ x, R ⊆ ball x ε} with hG
  have hW : ∀ i (hi : i < k), ∃ W : List (Set X), (∀ R ∈ W, R ∈ G i) ∧
      IsWeakChain (p i) (p (i + 1)) W := by
    intro i hi
    refine exists_weakChain_of_isPreconnected (hLc _ (List.getElem_mem hi))
      (fun R hR => hopen R hR.1) (fun x hx => ?_) (hp1 i hi) (hp2 i hi)
    obtain ⟨R, hR, hxR, hcl, hball⟩ := hsmall _ (hLo _ (List.getElem_mem hi)) x hx ε hε
    exact ⟨R, ⟨hR, ⟨hi, hcl⟩, x, hball⟩, hxR⟩
  -- laying the chains end to end
  have hE : ∀ n, n < k → ∃ E : List (Set X × ℕ), IsWeakChain A (p (n + 1)) (E.map Prod.fst) ∧
      (∀ e ∈ E, e.1 ∈ G e.2 ∧ e.2 ≤ n) ∧ E.Pairwise (fun e f => e.2 ≤ f.2) := by
    intro n
    induction n with
    | zero =>
      intro h0
      obtain ⟨W, hWG, hWc⟩ := hW 0 h0
      refine ⟨W.map (fun R => (R, 0)), ?_, ?_, ?_⟩
      · rw [show (W.map fun R => (R, 0)).map Prod.fst = W by simp [Function.comp_def]]
        simpa [hp] using hWc
      · intro e he
        obtain ⟨R, hR, rfl⟩ := List.mem_map.mp he
        exact ⟨hWG R hR, le_rfl⟩
      · exact List.pairwise_map.mpr (List.pairwise_of_forall fun _ _ => le_rfl)
    | succ n ih =>
      intro hn
      obtain ⟨E, hEc, hEG, hEp⟩ := ih (by omega)
      obtain ⟨W, hWG, hWc⟩ := hW (n + 1) hn
      refine ⟨E ++ W.map (fun R => (R, n + 1)), ?_, ?_, ?_⟩
      · rw [List.map_append,
          show (W.map fun R => (R, n + 1)).map Prod.fst = W by simp [Function.comp_def]]
        exact hEc.append' hWc
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact ⟨(hEG e he).1, (hEG e he).2.trans (Nat.le_succ n)⟩
        · obtain ⟨R, hR, rfl⟩ := List.mem_map.mp he
          exact ⟨hWG R hR, le_rfl⟩
      · refine List.pairwise_append.mpr ⟨hEp,
          List.pairwise_map.mpr (List.pairwise_of_forall fun _ _ => le_rfl), ?_⟩
        intro e he f hf
        obtain ⟨R, -, rfl⟩ := List.mem_map.mp hf
        exact (hEG e he).2.trans (Nat.le_succ n)
  obtain ⟨E, hEc, hEG, hEp⟩ := hE (k - 1) (by omega)
  have hpk : p (k - 1 + 1) = B := by
    have : ¬ (k - 1 + 1 < k) := by omega
    simp [hp, this]
  rw [hpk] at hEc
  obtain ⟨l, hlE, hl⟩ := exists_simpleChain_sublist (σ := σ) Prod.fst hAB
    (fun e he => (hEG e he).1.1) hEc
  have hlp : l.Pairwise (fun e f => e.2 ≤ f.2) := hEp.sublist hlE
  refine ⟨l.map Prod.fst, hl, ?_, fun j => if h : j < l.length then (l[j]).2 else k, ?_, ?_⟩
  · intro L hL
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hL
    exact (hEG e (hlE.subset he)).1.2.2
  · intro i j hij
    simp only
    by_cases hj : j < l.length
    · have hi : i < l.length := lt_of_le_of_lt hij hj
      rw [dif_pos hi, dif_pos hj]
      rcases eq_or_lt_of_le hij with h | h
      · subst h; exact le_rfl
      · exact List.pairwise_iff_getElem.mp hlp i j hi hj h
    · rw [dif_neg hj]
      split_ifs with hi
      · obtain ⟨⟨hlt, -⟩, -⟩ := (hEG _ (hlE.subset (List.getElem_mem hi))).1.2
        exact hlt.le
      · exact le_rfl
  · intro j hj
    have hj' : j < l.length := by simpa using hj
    obtain ⟨hlt, hcl⟩ := (hEG _ (hlE.subset (List.getElem_mem hj'))).1.2.1
    refine ⟨by simpa [dif_pos hj'] using hlt, ?_⟩
    simp only [List.getElem_map, dif_pos hj']
    exact hcl

/-- **The sequence of chains** `C₁, C₂, …` (Moore, p. 137, conditions (1)–(3)). -/
theorem exists_chains (hopen : ∀ R ∈ σ.region, IsOpen R)
    (hpc : ∀ R ∈ σ.region, IsPreconnected R)
    (hsmall : ∀ U : Set X, IsOpen U → ∀ x ∈ U, ∀ ε > 0,
      ∃ R ∈ σ.region, x ∈ R ∧ closure R ⊆ U ∧ R ⊆ ball x ε)
    {M : Set X} (hMo : IsOpen M) (hMc : IsPreconnected M) {A B : X} (hA : A ∈ M) (hB : B ∈ M)
    (hAB : A ≠ B) :
    ∃ c : ℕ → List (Set X), (∀ m, σ.IsSimpleChain A B (c m)) ∧
      (∀ m, ∀ L ∈ c m, ∃ x, L ⊆ ball x (1 / ((m : ℝ) + 1))) ∧
      (∀ L ∈ c 0, closure L ⊆ M) ∧
      (∀ m, ∃ o : ℕ → ℕ, Monotone o ∧ ∀ j (hj : j < (c (m + 1)).length),
        ∃ ho : o j < (c m).length, closure (c (m + 1))[j] ⊆ (c m)[o j]) := by
  obtain ⟨c₀, hc₀s, hc₀m, o₀, -, hc₀n⟩ := exists_refine hopen hsmall hAB (Ls := [M])
    (by simpa using hMo) (by simpa using hMc)
    ⟨by simp, by simpa using hA, by simpa using hB, fun i hi => by simp at hi⟩
    (ε := 1 / ((0 : ℕ) + 1 : ℝ)) (by positivity)
  have step : ∀ (m : ℕ) (l : List (Set X)), σ.IsSimpleChain A B l →
      ∃ l' : List (Set X), σ.IsSimpleChain A B l' ∧
        (∀ L ∈ l', ∃ x, L ⊆ ball x (1 / (((m + 1 : ℕ) : ℝ) + 1))) ∧
        ∃ o : ℕ → ℕ, Monotone o ∧ ∀ j (hj : j < l'.length),
          ∃ ho : o j < l.length, closure l'[j] ⊆ l[o j] := by
    intro m l hl
    exact exists_refine hopen hsmall hAB (fun L hL => hopen L (hl.2.2.1 L hL))
      (fun L hL => hpc L (hl.2.2.1 L hL)) hl.isWeakChain (by positivity)
  choose! f hf using step
  set c : ℕ → List (Set X) := fun n => Nat.rec c₀ (fun m l => f m l) n with hc
  have hcs : ∀ m, σ.IsSimpleChain A B (c m) := by
    intro m
    induction m with
    | zero => exact hc₀s
    | succ m ih => exact (hf m (c m) ih).1
  refine ⟨c, hcs, ?_, ?_, fun m => (hf m (c m) (hcs m)).2.2⟩
  · intro m
    cases m with
    | zero => simpa using hc₀m
    | succ m => exact (hf m (c m) (hcs m)).2.1
  · intro L hL
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
    obtain ⟨ho, hcl⟩ := hc₀n j hj
    simpa using hcl

end Refine

section Core

variable {X : Type*} [MetricSpace X] {σ : Space X}

/-- **Theorem 15, core** (Moore's proof, parts I–III): in the setting of a metric space whose
regions are connected open sets with compact closures, small regions with closures inside any
open set about any point, two distinct points of a connected open set `M` lie in a compact
connected subset of `M` that is irreducible between them. -/
theorem exists_irreducible (hopen : ∀ R ∈ σ.region, IsOpen R)
    (hpc : ∀ R ∈ σ.region, IsPreconnected R) (hcpt : ∀ R ∈ σ.region, IsCompact (closure R))
    (hsmall : ∀ U : Set X, IsOpen U → ∀ x ∈ U, ∀ ε > 0,
      ∃ R ∈ σ.region, x ∈ R ∧ closure R ⊆ U ∧ R ⊆ ball x ε)
    {M : Set X} (hMo : IsOpen M) (hMc : IsPreconnected M) {A B : X} (hA : A ∈ M) (hB : B ∈ M)
    (hAB : A ≠ B) :
    ∃ C ⊆ M, IsCompact C ∧ IsPreconnected C ∧ A ∈ C ∧ B ∈ C ∧
      ∀ H ⊆ C, IsPreconnected H → A ∈ H → B ∈ H → H = C := by
  obtain ⟨c, hcs, hsm, hc0, hnest⟩ := exists_chains hopen hpc hsmall hMo hMc hA hB hAB
  have hlen : ∀ m, 0 < (c m).length := fun m => List.length_pos_iff.mpr (hcs m).2.1
  have hreg : ∀ m, ∀ L ∈ c m, L ∈ σ.region := fun m => (hcs m).2.2.1
  set C : Set X := {x | ∀ m, ∃ i, ∃ hi : i < (c m).length, x ∈ (c m)[i]} with hC
  set K : ℕ → Set X := fun m => ⋃ L ∈ c m, closure L with hK
  -- I. C is the intersection of the `K m`
  have hCK : C = ⋂ m, K m := by
    ext x
    simp only [hC, hK, mem_setOf_eq, mem_iInter, mem_iUnion]
    constructor
    · intro h m
      obtain ⟨i, hi, hx⟩ := h m
      exact ⟨_, List.getElem_mem hi, subset_closure hx⟩
    · intro h m
      obtain ⟨L, hL, hx⟩ := h (m + 1)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
      obtain ⟨o, -, ho⟩ := hnest m
      obtain ⟨hoj, hcl⟩ := ho j hj
      exact ⟨o j, hoj, hcl hx⟩
  have hKc : ∀ m, IsCompact (K m) := fun m =>
    (List.finite_toSet (c m)).isCompact_biUnion fun L hL => hcpt L (hreg m L hL)
  have hKp : ∀ m, IsPreconnected (K m) := by
    intro m
    have := isPreconnected_biUnion_chain (l := (c m).map closure)
      (fun R hR => by
        obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hR
        exact (hpc L (hreg m L hL)).closure)
      (fun i hi => by
        simp only [List.length_map] at hi
        simp only [List.getElem_map]
        obtain ⟨y, hy⟩ := (hcs m).isWeakChain.2.2.2 i hi
        exact ⟨y, subset_closure hy.1, subset_closure hy.2⟩)
    simpa [hK] using this
  have hKa : Antitone K := by
    refine antitone_nat_of_succ_le fun m => ?_
    simp only [hK]
    refine iUnion₂_subset fun L hL => ?_
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
    obtain ⟨o, -, ho⟩ := hnest m
    obtain ⟨hoj, hcl⟩ := ho j hj
    exact hcl.trans (subset_closure.trans (subset_biUnion_of_mem (List.getElem_mem hoj)))
  have hCc : IsCompact C := by
    rw [hCK]
    exact (hKc 0).of_isClosed_subset (isClosed_iInter fun m => (hKc m).isClosed)
      (iInter_subset _ 0)
  have hCp : IsPreconnected C := by
    rw [hCK]; exact moore_isPreconnected_iInter hKa hKc hKp
  have hAC : A ∈ C := fun m => ⟨0, hlen m, ((hcs m).2.2.2.1 0 (hlen m)).mpr rfl⟩
  have hBC : B ∈ C := fun m => ⟨(c m).length - 1, by have := hlen m; omega,
    ((hcs m).2.2.2.2.1 _ (by have := hlen m; omega)).mpr (by have := hlen m; omega)⟩
  have hCM : C ⊆ M := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hx 0
    exact hc0 _ (List.getElem_mem hi) (subset_closure hxi)
  refine ⟨C, hCM, hCc, hCp, hAC, hBC, ?_⟩
  -- III. irreducibility
  intro H hHC hH hAH hBH
  by_contra hne
  obtain ⟨X₀, hX₀C, hX₀H⟩ : ∃ X₀ ∈ C, X₀ ∉ H := by
    by_contra h
    push_neg at h
    exact hne (subset_antisymm hHC h)
  set I : ℕ → X → ℕ → Prop := fun m Y i => ∃ hi : i < (c m).length, Y ∈ (c m)[i] with hI
  set pre : ℕ → X → X → Prop := fun m Y Z => ∀ i j, I m Y i → I m Z j → i < j with hpre
  -- persistence
  have hpers : ∀ m Y Z, pre m Y Z → pre (m + 1) Y Z := by
    intro m Y Z h i' j' ⟨hi', hYi'⟩ ⟨hj', hZj'⟩
    obtain ⟨o, hom, ho⟩ := hnest m
    obtain ⟨hoi, hcli⟩ := ho i' hi'
    obtain ⟨hoj, hclj⟩ := ho j' hj'
    have := h (o i') (o j') ⟨hoi, hcli (subset_closure hYi')⟩ ⟨hoj, hclj (subset_closure hZj')⟩
    by_contra hle
    push_neg at hle
    exact absurd (hom hle) (not_le.mpr this)
  have hpers' : ∀ m n Y Z, m ≤ n → pre m Y Z → pre n Y Z := by
    intro m n Y Z hmn h
    induction n, hmn using Nat.le_induction with
    | base => exact h
    | succ n _ ih => exact hpers n Y Z ih
  -- closeness of points in meeting links
  have hclose : ∀ m Y Z i j, I m Y i → I m Z j → i ≤ j + 1 → j ≤ i + 1 →
      dist Y Z < 4 / ((m : ℝ) + 1) := by
    intro m Y Z i j ⟨hi, hYi⟩ ⟨hj, hZj⟩ h1 h2
    have hr : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hball : ∀ k (hk : k < (c m).length) (P Q : X), P ∈ (c m)[k] → Q ∈ (c m)[k] →
        dist P Q < 2 * (1 / ((m : ℝ) + 1)) := by
      intro k hk P Q hP hQ
      obtain ⟨x, hx⟩ := hsm m _ (List.getElem_mem hk)
      have h1 := mem_ball.mp (hx hP)
      have h2 := mem_ball.mp (hx hQ)
      calc dist P Q ≤ dist P x + dist Q x := dist_triangle_right _ _ _
        _ < _ := by linarith
    have h4 : 4 / ((m : ℝ) + 1) = 2 * (2 * (1 / ((m : ℝ) + 1))) := by ring
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hj' : j = i + 1 := by omega
      subst hj'
      obtain ⟨w, hw1, hw2⟩ := (hcs m).isWeakChain.2.2.2 i hj
      have := hball i hi Y w hYi hw1
      have := hball (i + 1) hj w Z hw2 hZj
      calc dist Y Z ≤ dist Y w + dist w Z := dist_triangle _ _ _
        _ < _ := by rw [h4]; linarith
    · have := hball i hi Y Z hYi hZj
      rw [h4]; linarith
    · have hi' : i = j + 1 := by omega
      subst hi'
      obtain ⟨w, hw1, hw2⟩ := (hcs m).isWeakChain.2.2.2 j hi
      have := hball (j + 1) hi Y w hYi hw2
      have := hball j hj w Z hw1 hZj
      calc dist Y Z ≤ dist Y w + dist w Z := dist_triangle _ _ _
        _ < _ := by rw [h4]; linarith
  -- a gap stage
  have hgap : ∀ Y Z, Y ≠ Z → ∃ m, ∀ i j, I m Y i → I m Z j → i + 2 ≤ j ∨ j + 2 ≤ i := by
    intro Y Z hYZ
    have hd : 0 < dist Y Z := dist_pos.mpr hYZ
    obtain ⟨m, hm⟩ := exists_nat_gt (4 / dist Y Z)
    refine ⟨m, fun i j hi hj => ?_⟩
    by_contra h
    push_neg at h
    have := hclose m Y Z i j hi hj (by omega) (by omega)
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have : dist Y Z * ((m : ℝ) + 1) < 4 := by
      rwa [lt_div_iff₀ hm1] at this
    have : 4 < dist Y Z * ((m : ℝ) + 1) := by
      rw [div_lt_iff₀ hd] at hm; nlinarith
    linarith
  have hgap2 : ∀ Y ∈ C, ∀ Z ∈ C, Y ≠ Z → ∃ m, (∀ i j, I m Y i → I m Z j → i + 2 ≤ j) ∨
      (∀ i j, I m Y i → I m Z j → j + 2 ≤ i) := by
    intro Y hY Z hZ hYZ
    obtain ⟨m, hm⟩ := hgap Y Z hYZ
    obtain ⟨i₀, hi₀, hYi₀⟩ := hY m
    obtain ⟨j₀, hj₀, hZj₀⟩ := hZ m
    refine ⟨m, ?_⟩
    rcases hm i₀ j₀ ⟨hi₀, hYi₀⟩ ⟨hj₀, hZj₀⟩ with h0 | h0
    · left
      intro i j ⟨hi, hYi⟩ ⟨hj, hZj⟩
      have a1 := (hcs m).adjacent hi hi₀ hYi hYi₀
      have a2 := (hcs m).adjacent hj hj₀ hZj hZj₀
      rcases hm i j ⟨hi, hYi⟩ ⟨hj, hZj⟩ with h | h
      · exact h
      · omega
    · right
      intro i j ⟨hi, hYi⟩ ⟨hj, hZj⟩
      have a1 := (hcs m).adjacent hi hi₀ hYi hYi₀
      have a2 := (hcs m).adjacent hj hj₀ hZj hZj₀
      rcases hm i j ⟨hi, hYi⟩ ⟨hj, hZj⟩ with h | h
      · omega
      · exact h
  -- the separating open sets
  set u : Set X := {w | ∃ m i, ∃ hi : i < (c m).length, w ∈ (c m)[i] ∧
    ∀ Z ∈ C, Z ∈ (c m)[i] → ∃ n, pre n Z X₀} with hu
  set v : Set X := {w | ∃ m i, ∃ hi : i < (c m).length, w ∈ (c m)[i] ∧
    ∀ Z ∈ C, Z ∈ (c m)[i] → ∃ n, pre n X₀ Z} with hv
  have huo : IsOpen u := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨m, i, hi, hw, h⟩
    exact ⟨(c m)[i], fun w' hw' => ⟨m, i, hi, hw', h⟩, hopen _ (hreg m _ (List.getElem_mem hi)),
      hw⟩
  have hvo : IsOpen v := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨m, i, hi, hw, h⟩
    exact ⟨(c m)[i], fun w' hw' => ⟨m, i, hi, hw', h⟩, hopen _ (hreg m _ (List.getElem_mem hi)),
      hw⟩
  have htoU : ∀ Y ∈ C, ∀ m, (∀ i j, I m Y i → I m X₀ j → i + 2 ≤ j) → Y ∈ u := by
    intro Y hY m h
    obtain ⟨i₀, hi₀, hYi₀⟩ := hY m
    refine ⟨m, i₀, hi₀, hYi₀, fun Z _ hZ => ⟨m, fun i j ⟨hi, hZi⟩ hj => ?_⟩⟩
    have a := (hcs m).adjacent hi hi₀ hZi hZ
    have := h i₀ j ⟨hi₀, hYi₀⟩ hj
    omega
  have htoV : ∀ Y ∈ C, ∀ m, (∀ i j, I m Y i → I m X₀ j → j + 2 ≤ i) → Y ∈ v := by
    intro Y hY m h
    obtain ⟨i₀, hi₀, hYi₀⟩ := hY m
    refine ⟨m, i₀, hi₀, hYi₀, fun Z _ hZ => ⟨m, fun i j hi ⟨hj, hZj⟩ => ?_⟩⟩
    have a := (hcs m).adjacent hj hi₀ hZj hZ
    have := h i₀ i ⟨hi₀, hYi₀⟩ hi
    omega
  have hsub : H ⊆ u ∪ v := by
    intro Y hYH
    have hY := hHC hYH
    have hYX : Y ≠ X₀ := fun h => hX₀H (h ▸ hYH)
    obtain ⟨m, h | h⟩ := hgap2 Y hY X₀ hX₀C hYX
    · exact Or.inl (htoU Y hY m h)
    · exact Or.inr (htoV Y hY m h)
  have hAu : A ∈ u := by
    have hAX : A ≠ X₀ := fun h => hX₀H (h ▸ hAH)
    obtain ⟨m, h | h⟩ := hgap2 A hAC X₀ hX₀C hAX
    · exact htoU A hAC m h
    · exfalso
      obtain ⟨j, hj, hXj⟩ := hX₀C m
      have := h 0 j ⟨hlen m, ((hcs m).2.2.2.1 0 (hlen m)).mpr rfl⟩ ⟨hj, hXj⟩
      omega
  have hBv : B ∈ v := by
    have hBX : B ≠ X₀ := fun h => hX₀H (h ▸ hBH)
    obtain ⟨m, h | h⟩ := hgap2 B hBC X₀ hX₀C hBX
    · exfalso
      obtain ⟨j, hj, hXj⟩ := hX₀C m
      have := h ((c m).length - 1) j ⟨by have := hlen m; omega,
        ((hcs m).2.2.2.2.1 _ (by have := hlen m; omega)).mpr (by have := hlen m; omega)⟩
        ⟨hj, hXj⟩
      omega
    · exact htoV B hBC m h
  obtain ⟨z, hzH, ⟨m, i, hi, hzi, hzu⟩, ⟨m', i', hi', hzi', hzv⟩⟩ :=
    hH u v huo hvo hsub ⟨A, hAH, hAu⟩ ⟨B, hBH, hBv⟩
  obtain ⟨n, hn⟩ := hzu z (hHC hzH) hzi
  obtain ⟨n', hn'⟩ := hzv z (hHC hzH) hzi'
  have h1 := hpers' n (max n n') z X₀ (le_max_left _ _) hn
  have h2 := hpers' n' (max n n') X₀ z (le_max_right _ _) hn'
  obtain ⟨a, ha, hza⟩ := hHC hzH (max n n')
  obtain ⟨b, hb, hXb⟩ := hX₀C (max n n')
  have := h1 a b ⟨ha, hza⟩ ⟨hb, hXb⟩
  have := h2 b a ⟨hb, hXb⟩ ⟨ha, hza⟩
  omega

end Core

/-! ### Moore's statements -/

section MooreStatements

variable {S : Type*} {σ : Space S}

/-- **Moore arcs, topologically** (Axioms 1, 4): an arc from `A` to `B` is a compact connected set
containing `A ≠ B` and irreducible between them. -/
theorem isArc_iff_topological (h1 : σ.Axiom1) (h4 : σ.Axiom4) {A B : S} {C : Set S} :
    σ.IsArc A B C ↔ A ≠ B ∧ @IsCompact S σ.topology C ∧ @IsConnected S σ.topology C ∧ A ∈ C ∧
      B ∈ C ∧ ∀ H ⊆ C, H ≠ C → A ∈ H → B ∈ H → ¬ @IsConnected S σ.topology H := by
  letI := σ.topology
  haveI := t2Space h1
  constructor
  · rintro ⟨hAB, hb, hc, hconn, hA, hB, hirr⟩
    exact ⟨hAB, heineBorel_iff.mp (fa_theorem12 h1 h4 hc hb), ⟨⟨A, hA⟩, (isConn_iff h1).mp hconn⟩,
      hA, hB, fun H hHC hne hAH hBH hH =>
        hirr H hHC hne hAH hBH ((isConn_iff h1).mpr hH.isPreconnected)⟩
  · rintro ⟨hAB, hc, hconn, hA, hB, hirr⟩
    exact ⟨hAB, isBoundedM_of_isCompact h1 hc, (isClosedM_iff h1).mpr hc.isClosed,
      (isConn_iff h1).mpr hconn.isPreconnected, hA, hB, fun H hHC hne hAH hBH hH =>
        hirr H hHC hne hAH hBH ⟨⟨A, hAH⟩, (isConn_iff h1).mp hH⟩⟩

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
  (h51 : Space.Axiom5₁ (S := S))
include h1 h2 h3 h4 h51

/-- Two distinct points of a connected open set are joined by an arc inside it. -/
theorem exists_arc_of_isOpen_isPreconnected {M : Set S} (hMo : @IsOpen S σ.topology M)
    (hMc : @IsPreconnected S σ.topology M) {A B : S} (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B) :
    ∃ C ⊆ M, σ.IsArc A B C := by
  letI := σ.topology
  haveI := metrizable h1 h3 h51
  letI := TopologicalSpace.metrizableSpaceMetric S
  have hsmall : ∀ U : Set S, IsOpen U → ∀ x ∈ U, ∀ ε > 0,
      ∃ R ∈ σ.region, x ∈ R ∧ closure R ⊆ U ∧ R ⊆ ball x ε := by
    intro U hU x hx ε hε
    obtain ⟨R₀, hR₀, hxR₀, hR₀U⟩ := (isOpen_iff_region h1).mp (hU.inter isOpen_ball) x
      ⟨hx, mem_ball_self hε⟩
    obtain ⟨R, hR, hxR, hcl⟩ := exists_region_cl_subset h1 hR₀ hxR₀
    rw [cl_eq_closure h1] at hcl
    exact ⟨R, hR, hxR, hcl.trans (hR₀U.trans inter_subset_left),
      subset_closure.trans (hcl.trans (hR₀U.trans inter_subset_right))⟩
  obtain ⟨C, hCM, hCc, hCp, hAC, hBC, hirr⟩ := exists_irreducible (σ := σ)
    (fun R hR => isOpen_region hR) (fun R hR => (isConn_iff h1).mp (h2 R hR))
    (fun R hR => isCompact_closure_region h1 h4 hR) hsmall hMo hMc hA hB hAB
  refine ⟨C, hCM, (isArc_iff_topological h1 h4).mpr ⟨hAB, hCc, ⟨⟨A, hAC⟩, hCp⟩, hAC, hBC,
    fun H hHC hne hAH hBH hH => hne (hirr H hHC hH.isPreconnected hAH hBH)⟩⟩

/-- **Theorem 15.** Two distinct points of a domain are joined by an arc in the domain.
(Moore's proof by nested simple chains, pp. 136–139: `exists_irreducible`.)
*Axioms used: 1, 2, 4; and 3, 5₁ (through metrizability).*
**Shape change:** Axiom 5 is weakened to Axiom 5₁ (which it implies, `axiom5₁_of_axiom5`). -/
theorem fa_theorem15 {M : Set S} (hM : σ.IsDomain M) {A B : S} (hA : A ∈ M) (hB : B ∈ M)
    (hAB : A ≠ B) : ∃ C ⊆ M, σ.IsArc A B C := by
  obtain ⟨hMo, hMc⟩ := (isDomain_iff h1).mp hM
  exact exists_arc_of_isOpen_isPreconnected h1 h2 h3 h4 h51 hMo hMc hA hB hAB

/-- **Theorem 16.** Two points of a region are joined by an arc in the region; two points without
the region are joined by an arc without it. (No proof printed.) The region is a domain by Axiom 2
and Theorem 1; the exterior `S − R'` is a domain: open since `R'` is closed, connected by
Axiom 3. *Axioms used: as Theorem 15.* **Shape change:** Axiom 5 weakened to 5₁. -/
theorem fa_theorem16 {R : Set S} (hR : R ∈ σ.region) :
    (∀ A ∈ R, ∀ B ∈ R, A ≠ B → ∃ C ⊆ R, σ.IsArc A B C) ∧
      (∀ A ∈ σ.ext R, ∀ B ∈ σ.ext R, A ≠ B → ∃ C ⊆ σ.ext R, σ.IsArc A B C) :=
  ⟨fun _ hA _ hB hAB => exists_arc_of_isOpen_isPreconnected h1 h2 h3 h4 h51 (isOpen_region hR)
      ((isConn_iff h1).mp (h2 R hR)) hA hB hAB,
    fun _ hA _ hB hAB => exists_arc_of_isOpen_isPreconnected h1 h2 h3 h4 h51 (isOpen_ext h1 R)
      ((isConn_iff h1).mp (h3 R hR)) hA hB hAB⟩

end MooreStatements

end HPC.Moore
