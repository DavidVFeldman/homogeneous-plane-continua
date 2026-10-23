import HPC.BJ59.Thm56
import HPC.PseudoArc.T13Topo

/-!
# Batch 198, library: Bing–Jones Theorem 5, repaired (commission 198, §6, stretch)

The route of commission 198 §6 (the independent check's sketch), with the limits taken as
topological limits superior (`HPC.T13.limSup`, batch 81) rather than Hausdorff limits:

* the chains `D_k` of Theorem 3 with mesh `δ_k → 0` and a link `d_k ∋ p` inside `U` give the
  separations `A_k = (X − U) ∩ (links before d_k)`, `B_k = (X − U) ∩ (links after d_k)`
  (`theorem4_explicit`);
* if each fails, at `t_k` with failing links `α_k`, `β_k`, pass to a subsequence with `α`, `β`
  fixed and `t_k → c`;
* the parts `P_k = g_{t_k} − (links after d_k)` and `Q_k = g_{t_k} − (links before d_k)` are
  closed, cover `g_{t_k}`, meet only inside `d_k`, and (with the point `p` added) are
  `δ_k`-chained (`chainedAt_union_point`, by clopen boundary bumping);
* their limits superior `P`, `Q` are continua (`HPC.T13.isPreconnected_limSup`), lie in `g_c`
  (`limSup_subset_fibre`, continuity of `f`) and cover `g_c` (`fibre_subset_limSup_union`,
  openness of `f`); so one of them is `g_c` (indecomposability);
* `hEU` gives a point of `g_c ∩ e_α` off `Ū` (resp. `g_c ∩ e_β`); near it `P_k` (resp. `Q_k`)
  meets `e_α` off `U` for some `k`, a point of `A_k ∩ g_{t_k} ∩ e_α`: a contradiction.

The hypotheses `hUE` (`Ū` in a link) and `hE` (`E` covers `X`) of the skeleton's `bj_theorem5` are
not used.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane

variable {X : Type*} [MetricSpace X]

/-- **The parts are finely chained.** If closed `P`, `Q` cover a connected `g`, meet only inside
`d` (of diameter `< ε`) and `P ≠ g`, then `P ∪ {p}` is `ε`-chained for any `p ∈ d`. -/
theorem chainedAt_union_point {g P Q d : Set X} {p : X} {ε : ℝ} (hg : IsPreconnected g)
    (hP : IsClosed P) (hQ : IsClosed Q) (hPQ : P ∪ Q = g) (hPQd : P ∩ Q ⊆ d)
    (hdb : Bornology.IsBounded d) (hdε : diam d < ε) (hp : p ∈ d) (hPg : P ≠ g) :
    T13.ChainedAt (P ∪ {p}) ε := by
  have hε : 0 < ε := lt_of_le_of_lt diam_nonneg hdε
  have core : ∀ S T : Set X, P ∪ {p} ⊆ S ∪ T → (∀ x ∈ S, ∀ y ∈ T, ε < dist x y) → p ∈ S →
      P ∪ {p} ⊆ S := by
    intro S T hcov hsep hpS
    have hdS : ∀ w ∈ P ∩ d, w ∈ S := by
      rintro w ⟨hwP, hwd⟩
      rcases hcov (Or.inl hwP) with h | h
      · exact h
      · exfalso
        have h1 := hsep p hpS w h
        have h2 := dist_le_diam_of_mem hdb hp hwd
        linarith
    have hWeq : P ∩ T = P ∩ (closure S)ᶜ := by
      ext x
      constructor
      · rintro ⟨hxP, hxT⟩
        refine ⟨hxP, fun hxS => ?_⟩
        obtain ⟨s, hs, hxs⟩ := Metric.mem_closure_iff.1 hxS ε hε
        have := hsep s hs x hxT
        rw [dist_comm] at this
        linarith
      · rintro ⟨hxP, hxS⟩
        refine ⟨hxP, ?_⟩
        rcases hcov (Or.inl hxP) with h | h
        · exact absurd (subset_closure h) hxS
        · exact h
    have hWc : IsClosed (P ∩ T) := by
      refine isClosed_of_closure_subset fun x hx => ?_
      have hxP : x ∈ P := closure_minimal inter_subset_left hP hx
      refine ⟨hxP, ?_⟩
      rcases hcov (Or.inl hxP) with h | h
      · exfalso
        obtain ⟨w, ⟨-, hwT⟩, hxw⟩ := Metric.mem_closure_iff.1 hx ε hε
        have := hsep x h w hwT
        linarith
      · exact h
    have hWempty : P ∩ T = ∅ := by
      by_contra hne
      have hWne := nonempty_iff_ne_empty.2 hne
      obtain ⟨z, hzW, hzcl⟩ := T13.clopen_meets_closure_diff hg
        (by rw [← hPQ]; exact subset_union_left) hPg inter_subset_left hWc
        isClosed_closure.isOpen_compl hWeq hWne
      have hgQ : closure (g \ P) ⊆ Q := by
        refine closure_minimal (fun x hx => ?_) hQ
        rw [← hPQ] at hx
        rcases hx.1 with h | h
        · exact absurd h hx.2
        · exact h
      have hzS := hdS z ⟨hzW.1, hPQd ⟨hzW.1, hgQ hzcl⟩⟩
      have := hsep z hzS z hzW.2
      rw [dist_self] at this
      linarith
    intro x hx
    rcases hx with hxP | hxp
    · rcases hcov (Or.inl hxP) with h | h
      · exact h
      · exact absurd (show x ∈ P ∩ T from ⟨hxP, h⟩) (hWempty ▸ notMem_empty x)
    · rw [mem_singleton_iff.1 hxp]
      exact hpS
  intro S T hcov hsep
  rcases hcov (Or.inr rfl) with h | h
  · exact Or.inl (core S T hcov hsep h)
  · exact Or.inr (core T S (fun x hx => Or.symm (hcov hx))
      (fun x hx y hy => by rw [dist_comm]; exact hsep y hy x hx) h)

/-- **The limit lies in the limit fibre** (continuity of `f`). -/
theorem limSup_subset_fibre {f : X → unitInterval} (hfc : Continuous f) {I : Set ℕ}
    {S : ℕ → Set X} {s : ℕ → unitInterval} {c : unitInterval} (hs : Tendsto s atTop (𝓝 c))
    {p : X} (hp : f p = c) (hS : ∀ n ∈ I, S n ⊆ f ⁻¹' {s n} ∪ {p}) :
    T13.limSup I S ⊆ f ⁻¹' {c} := by
  intro z hz
  have key : ∀ η > 0, dist (f z) c ≤ η := by
    intro η hη
    obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hs η hη)
    have hsub : (⋃ k ∈ I, ⋃ (_ : N ≤ k), S k) ⊆ {x | dist (f x) c ≤ η} := by
      intro x hx
      simp only [mem_iUnion] at hx
      obtain ⟨k, hk, hNk, hx⟩ := hx
      rcases hS k hk hx with h | h
      · show dist (f x) c ≤ η
        rw [show f x = s k from h]
        exact (hN k hNk).le
      · rw [mem_singleton_iff.1 h]
        show dist (f p) c ≤ η
        rw [hp, dist_self]
        exact hη.le
    have hcl : IsClosed {x | dist (f x) c ≤ η} :=
      isClosed_le (hfc.dist continuous_const) continuous_const
    exact closure_minimal hsub hcl (T13.limSup_subset_closure N hz)
  by_contra h
  have hpos : 0 < dist (f z) c := dist_pos.2 h
  have := key _ (half_pos hpos)
  linarith

/-- **The limit fibre lies in the union of the limits** (openness of `f`). -/
theorem fibre_subset_limSup_union {f : X → unitInterval} (hfo : IsOpenMap f) {I : Set ℕ}
    {S T : ℕ → Set X} {s : ℕ → unitInterval} {c : unitInterval} (hs : Tendsto s atTop (𝓝 c))
    (hI : ∃ N, Ici N ⊆ I) (hST : ∀ n ∈ I, f ⁻¹' {s n} ⊆ S n ∪ T n) :
    f ⁻¹' {c} ⊆ T13.limSup I S ∪ T13.limSup I T := by
  intro z hz
  by_contra hcon
  rw [mem_union, not_or] at hcon
  obtain ⟨hzS, hzT⟩ := hcon
  simp only [T13.limSup, mem_iInter, not_forall] at hzS hzT
  obtain ⟨N₁, h₁⟩ := hzS
  obtain ⟨N₂, h₂⟩ := hzT
  rw [Metric.mem_closure_iff] at h₁ h₂
  push_neg at h₁ h₂
  obtain ⟨ε₁, hε₁, h₁⟩ := h₁
  obtain ⟨ε₂, hε₂, h₂⟩ := h₂
  obtain ⟨N, hN⟩ := hI
  have hW : IsOpen (f '' ball z (min ε₁ ε₂)) := hfo _ isOpen_ball
  have hcW : c ∈ f '' ball z (min ε₁ ε₂) := ⟨z, mem_ball_self (lt_min hε₁ hε₂), hz⟩
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hs.eventually (hW.mem_nhds hcW))
  obtain ⟨w, hw, hwk⟩ := hM (max (max N N₁) (max N₂ M)) (by omega)
  have hkI : max (max N N₁) (max N₂ M) ∈ I := hN (show N ≤ _ by simp)
  rw [mem_ball, dist_comm] at hw
  rcases hST _ hkI (show w ∈ f ⁻¹' {s _} from hwk) with h | h
  · have := h₁ w (mem_iUnion₂.2 ⟨_, hkI, mem_iUnion.2 ⟨by omega, h⟩⟩)
    linarith [min_le_left ε₁ ε₂]
  · have := h₂ w (mem_iUnion₂.2 ⟨_, hkI, mem_iUnion.2 ⟨by omega, h⟩⟩)
    linarith [min_le_right ε₁ ε₂]

/-- A point of a limit superior has, in each neighbourhood, points of the sets of arbitrarily
large index. -/
theorem exists_mem_of_mem_limSup {I : Set ℕ} {S : ℕ → Set X} {q : X}
    (hq : q ∈ T13.limSup I S) {W : Set X} (hW : IsOpen W) (hqW : q ∈ W) (N : ℕ) :
    ∃ k ∈ I, N ≤ k ∧ (S k ∩ W).Nonempty := by
  obtain ⟨y, hyW, hy⟩ := mem_closure_iff.1 (T13.limSup_subset_closure N hq) W hW hqW
  simp only [mem_iUnion] at hy
  obtain ⟨k, hk, hNk, hy⟩ := hy
  exact ⟨k, hk, hNk, y, hy, hyW⟩

/-- **Bing–Jones, Theorem 5, repaired** (the skeleton's `bj_theorem5` without its unused
hypotheses `hE`, `hUE`). -/
theorem theorem5_repaired [CompactSpace X] {f : X → unitInterval} (hf : IsArcOfContinua f)
    (hfo : IsOpenMap f) (hS : IsSnakeLike (univ : Set X))
    (hind : ∀ t, Fold.Q78.IsIndecomposable (f ⁻¹' {t})) {n : ℕ} (E : Chain X n) {U : Set X}
    (hU : IsOpen U) (hUne : U.Nonempty) (hU01 : Disjoint U (f ⁻¹' {0, 1}))
    (hEU : ∀ t i, ¬ E.link i ∩ f ⁻¹' {t} ⊆ closure U) :
    ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧ A ∪ B = Uᶜ ∧ f ⁻¹' {0} ⊆ A ∧
      f ⁻¹' {1} ⊆ B ∧ ∀ t, (∀ i, (E.link i ∩ (A ∩ f ⁻¹' {t})).Nonempty) ∨
        (∀ i, (E.link i ∩ (B ∩ f ⁻¹' {t})).Nonempty) := by
  classical
  obtain ⟨p, hp⟩ := hUne
  have hg : ∀ t, IsPreconnected (f ⁻¹' {t}) := fun t => (hf.2.2 t).2.isPreconnected
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, δ = fun k : ℕ => min (posFn U p) (1 / ((k : ℝ) + 1)) := ⟨_, rfl⟩
  have hδpos : ∀ k, 0 < δ k := fun k => by
    rw [hδ]; exact lt_min (posFn_pos hU hp) (by positivity)
  have hδle : ∀ k, δ k ≤ 1 / ((k : ℝ) + 1) := fun k => by rw [hδ]; exact min_le_right _ _
  -- the chains of Theorem 3
  have hchain : ∀ k : ℕ, ∃ (m : ℕ) (D : Chain X (m + 1)) (l : Fin (m + 1)), IsEpsChain D (δ k) ∧
      univ ⊆ D.union ∧ (D.link 0 ∩ f ⁻¹' {0}).Nonempty ∧
      (D.link (Fin.last m) ∩ f ⁻¹' {1}).Nonempty ∧ p ∈ D.link l ∧ D.link l ⊆ U := by
    intro k
    obtain ⟨m, D, hD, hcov, h0, h1⟩ := theorem3_arc hf.1 hf.2.1 hg hS (hδpos k)
    obtain ⟨l, hl⟩ := mem_iUnion.1 (hcov (mem_univ p))
    refine ⟨m, D, l, hD, hcov, h0, h1, hl, ?_⟩
    intro y hy
    by_contra hyU
    have hdist : dist p y < posFn U p := by
      refine lt_of_lt_of_le (lt_of_le_of_lt (dist_le_diam_of_mem (hD l).1 hl hy) (hD l).2) ?_
      rw [hδ]; exact min_le_left _ _
    have hpos : posFn U p = infDist p Uᶜ := by unfold posFn; rw [if_pos ⟨y, hyU⟩]
    rw [hpos] at hdist
    exact absurd (infDist_le_dist_of_mem (show y ∈ Uᶜ from hyU)) (not_le.2 hdist)
  choose m D l hD hcov h0 h1 hpl hlU using hchain
  -- the links before and after `d_k`
  obtain ⟨bef, hbef⟩ : ∃ bef : ℕ → Set X,
      bef = fun k => ⋃ t : Fin (m k + 1), ⋃ (_ : t < l k), (D k).link t := ⟨_, rfl⟩
  obtain ⟨aft, haft⟩ : ∃ aft : ℕ → Set X,
      aft = fun k => ⋃ t : Fin (m k + 1), ⋃ (_ : l k < t), (D k).link t := ⟨_, rfl⟩
  have hbef_mem : ∀ k x, x ∈ bef k ↔ ∃ s, s < l k ∧ x ∈ (D k).link s := by
    intro k x; subst hbef; simp
  have haft_mem : ∀ k x, x ∈ aft k ↔ ∃ s, l k < s ∧ x ∈ (D k).link s := by
    intro k x; subst haft; simp
  have hbefo : ∀ k, IsOpen (bef k) := fun k => by
    subst hbef; exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => (D k).isOpen _
  have hafto : ∀ k, IsOpen (aft k) := fun k => by
    subst haft; exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => (D k).isOpen _
  have hba : ∀ k x, x ∈ bef k → x ∉ aft k := by
    intro k x hb ha
    obtain ⟨s, hs, hxs⟩ := (hbef_mem k x).1 hb
    obtain ⟨s', hs', hxs'⟩ := (haft_mem k x).1 ha
    have := ((D k).adjacent s s').1 ⟨x, hxs, hxs'⟩
    rw [Fin.lt_def] at hs hs'
    omega
  have hsep : ∀ k, IsClosed (Uᶜ ∩ bef k) ∧ IsClosed (Uᶜ ∩ aft k) ∧
      Disjoint (Uᶜ ∩ bef k) (Uᶜ ∩ aft k) ∧ (Uᶜ ∩ bef k) ∪ (Uᶜ ∩ aft k) = Uᶜ ∧
      f ⁻¹' {0} ⊆ Uᶜ ∩ bef k ∧ f ⁻¹' {1} ⊆ Uᶜ ∩ aft k := by
    intro k; subst hbef haft
    exact theorem4_explicit hU hU01 (hg 0) (hg 1) (D k) (hcov k) (h0 k) (h1 k) (l k) (hlU k)
  have hsplit : ∀ k x, x ∉ U → x ∈ Uᶜ ∩ bef k ∨ x ∈ Uᶜ ∩ aft k := by
    intro k x hx
    have : x ∈ Uᶜ := hx
    rw [← (hsep k).2.2.2.1] at this
    exact this
  by_contra hcon
  -- each separation fails somewhere
  have hfail : ∀ k, ∃ (t : unitInterval) (α β : Fin n),
      E.link α ∩ ((Uᶜ ∩ bef k) ∩ f ⁻¹' {t}) = ∅ ∧ E.link β ∩ ((Uᶜ ∩ aft k) ∩ f ⁻¹' {t}) = ∅ := by
    intro k
    obtain ⟨hA, hB, hAB, hcup, hA0, hB1⟩ := hsep k
    by_contra hk
    apply hcon
    refine ⟨_, _, hA, hB, hAB, hcup, hA0, hB1, fun t => ?_⟩
    by_contra ht
    rw [not_or] at ht
    obtain ⟨α, hα⟩ := not_forall.1 ht.1
    obtain ⟨β, hβ⟩ := not_forall.1 ht.2
    exact hk ⟨t, α, β, not_nonempty_iff_eq_empty.1 hα, not_nonempty_iff_eq_empty.1 hβ⟩
  choose t α β hα hβ using hfail
  -- extraction
  obtain ⟨ab, hab⟩ := Finite.exists_infinite_fiber (fun k => (α k, β k))
  have hfreq : ∃ᶠ k in atTop, (α k, β k) = ab :=
    Nat.frequently_atTop_iff_infinite.2 (Set.infinite_coe_iff.1 hab)
  obtain ⟨φ₁, hφ₁, hφ₁ab⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨c, -, φ₂, hφ₂, htc⟩ :=
    isCompact_univ.tendsto_subseq (x := t ∘ φ₁) (fun _ => mem_univ _)
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℕ → ℕ, ψ = φ₁ ∘ φ₂ := ⟨_, rfl⟩
  have hψ : StrictMono ψ := hψdef ▸ hφ₁.comp hφ₂
  have hψab : ∀ k, α (ψ k) = ab.1 ∧ β (ψ k) = ab.2 := fun k => by
    have := hφ₁ab (φ₂ k)
    rw [Prod.ext_iff] at this
    rw [hψdef]
    exact this
  have htψ : Tendsto (fun k => t (ψ k)) atTop (𝓝 c) := by rw [hψdef]; exact htc
  -- the points of `hEU`
  obtain ⟨qa, ⟨hqaE, hqac⟩, hqaU⟩ := not_subset.1 (hEU c ab.1)
  obtain ⟨qb, ⟨hqbE, hqbc⟩, hqbU⟩ := not_subset.1 (hEU c ab.2)
  have hlsc : ∀ W : Set X, IsOpen W → ∀ q ∈ W, f q = c →
      ∀ᶠ k in atTop, (W ∩ f ⁻¹' {t (ψ k)}).Nonempty := by
    intro W hW q hqW hqc
    have hmem : f '' W ∈ 𝓝 c := (hfo W hW).mem_nhds ⟨q, hqW, hqc⟩
    filter_upwards [htψ hmem] with k hk
    obtain ⟨x, hxW, hx⟩ := hk
    exact ⟨x, hxW, hx⟩
  have hWa : IsOpen (E.link ab.1 ∩ (closure U)ᶜ) :=
    (E.isOpen _).inter isClosed_closure.isOpen_compl
  have hWb : IsOpen (E.link ab.2 ∩ (closure U)ᶜ) :=
    (E.isOpen _).inter isClosed_closure.isOpen_compl
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hlsc _ hWa qa ⟨hqaE, hqaU⟩ hqac).and
    (hlsc _ hWb qb ⟨hqbE, hqbU⟩ hqbc))
  -- the parts
  set G : ℕ → Set X := fun k => f ⁻¹' {t (ψ k)} with hG
  set P : ℕ → Set X := fun k => G k \ aft (ψ k) with hP
  set Q : ℕ → Set X := fun k => G k \ bef (ψ k) with hQ
  have hGc : ∀ k, IsClosed (G k) := fun k => isClosed_singleton.preimage hf.1
  have hPc : ∀ k, IsClosed (P k) := fun k => (hGc k).sdiff (hafto _)
  have hQc : ∀ k, IsClosed (Q k) := fun k => (hGc k).sdiff (hbefo _)
  have hPQ : ∀ k, P k ∪ Q k = G k := by
    intro k
    ext x
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro hx
      by_cases ha : x ∈ aft (ψ k)
      · exact Or.inr ⟨hx, fun hb => hba _ x hb ha⟩
      · exact Or.inl ⟨hx, ha⟩
  have hPQd : ∀ k, P k ∩ Q k ⊆ (D (ψ k)).link (l (ψ k)) := by
    rintro k x ⟨⟨-, hxa⟩, ⟨-, hxb⟩⟩
    obtain ⟨s, hs⟩ := mem_iUnion.1 (hcov (ψ k) (mem_univ x))
    rcases lt_trichotomy s (l (ψ k)) with h | h | h
    · exact absurd ((hbef_mem _ x).2 ⟨s, h, hs⟩) hxb
    · exact h ▸ hs
    · exact absurd ((haft_mem _ x).2 ⟨s, h, hs⟩) hxa
  have hPne : ∀ k, N ≤ k → P k ≠ G k ∧ Q k ≠ G k ∧ (P k ∩ Q k).Nonempty := by
    intro k hk
    obtain ⟨⟨x, ⟨hxE, hxU⟩, hxG⟩, ⟨y, ⟨hyE, hyU⟩, hyG⟩⟩ := hN k hk
    have hxB : x ∈ Uᶜ ∩ aft (ψ k) := by
      rcases hsplit (ψ k) x (fun h => hxU (subset_closure h)) with h | h
      · exfalso
        have := hα (ψ k)
        rw [(hψab k).1] at this
        exact eq_empty_iff_forall_notMem.1 this x ⟨hxE, h, hxG⟩
      · exact h
    have hyA : y ∈ Uᶜ ∩ bef (ψ k) := by
      rcases hsplit (ψ k) y (fun h => hyU (subset_closure h)) with h | h
      · exact h
      · exfalso
        have := hβ (ψ k)
        rw [(hψab k).2] at this
        exact eq_empty_iff_forall_notMem.1 this y ⟨hyE, h, hyG⟩
    have hxP : x ∉ P k := fun h => h.2 hxB.2
    have hyQ : y ∉ Q k := fun h => h.2 hyA.2
    have hxQ : x ∈ Q k := ⟨hxG, fun h => hba _ x h hxB.2⟩
    have hyP : y ∈ P k := ⟨hyG, hba _ y hyA.2⟩
    refine ⟨fun h => hxP (h ▸ hxG), fun h => hyQ (h ▸ hyG), ?_⟩
    obtain ⟨r, -, hr⟩ := isPreconnected_closed_iff.1 (hg _) (P k) (Q k) (hPc k) (hQc k)
      (by rw [hPQ k]) ⟨y, hyG, hyP⟩ ⟨x, hxG, hxQ⟩
    exact ⟨r, hr⟩
  -- the points `r_k → p`, so `p ∈ g_c`
  have hr : ∀ k, ∃ r, N ≤ k → r ∈ P k ∩ Q k := by
    intro k
    by_cases hk : N ≤ k
    · obtain ⟨r, hr⟩ := (hPne k hk).2.2
      exact ⟨r, fun _ => hr⟩
    · exact ⟨p, fun h => absurd h hk⟩
  choose r hr using hr
  have hψle : ∀ k, δ (ψ k) ≤ 1 / ((k : ℝ) + 1) := fun k =>
    (hδle _).trans (one_div_le_one_div_of_le (by positivity)
      (by have := hψ.id_le k; simp only [id] at this; exact add_le_add_left (Nat.cast_le.mpr this) 1))
  have hrp : Tendsto r atTop (𝓝 p) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hε
    refine ⟨max N n₀, fun k hk => ?_⟩
    have hNk : N ≤ k := le_of_max_le_left hk
    have hd := dist_le_diam_of_mem (hD (ψ k) (l (ψ k))).1 (hPQd k (hr k hNk)) (hpl (ψ k))
    have h1 := (hD (ψ k) (l (ψ k))).2
    have h2 := hψle k
    have h3 : 1 / ((k : ℝ) + 1) ≤ 1 / ((n₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (add_le_add_left (Nat.cast_le.mpr (le_of_max_le_right hk)) 1)
    linarith
  have hfp : f p = c := by
    refine tendsto_nhds_unique ((hf.1.tendsto p).comp hrp) (htψ.congr' ?_)
    exact eventually_atTop.2 ⟨N, fun k hk => ((hr k hk).1.1 : f (r k) = t (ψ k)).symm⟩
  -- the limits
  have hε0 : Tendsto (fun k => δ (ψ k)) atTop (𝓝 0) :=
    squeeze_zero (fun k => (hδpos _).le) hψle tendsto_one_div_add_atTop_nhds_zero_nat
  have hchP : ∀ k ∈ Ici N, T13.ChainedAt (P k ∪ {p}) (δ (ψ k)) := fun k hk =>
    chainedAt_union_point (hg _) (hPc k) (hQc k) (hPQ k) (hPQd k) (hD (ψ k) (l (ψ k))).1
      (hD _ _).2 (hpl _) (hPne k hk).1
  have hchQ : ∀ k ∈ Ici N, T13.ChainedAt (Q k ∪ {p}) (δ (ψ k)) := fun k hk =>
    chainedAt_union_point (hg _) (hQc k) (hPc k) (by rw [union_comm]; exact hPQ k)
      (by rw [inter_comm]; exact hPQd k) (hD (ψ k) (l (ψ k))).1 (hD _ _).2 (hpl _) (hPne k hk).2.1
  have hpP : ∀ k ∈ Ici N, p ∈ P k ∪ {p} := fun _ _ => Or.inr rfl
  have hpQ : ∀ k ∈ Ici N, p ∈ Q k ∪ {p} := fun _ _ => Or.inr rfl
  have hLPc := T13.isPreconnected_limSup hε0 hchP hpP (Set.Ici_infinite N)
  have hLQc := T13.isPreconnected_limSup hε0 hchQ hpQ (Set.Ici_infinite N)
  have hpLP := T13.mem_limSup (Set.Ici_infinite N) hpP
  have hpLQ := T13.mem_limSup (Set.Ici_infinite N) hpQ
  have hLPsub : T13.limSup (Ici N) (fun k => P k ∪ {p}) ⊆ f ⁻¹' {c} :=
    limSup_subset_fibre hf.1 htψ hfp fun k _ x hx => by
      rcases hx with h | h
      · exact Or.inl h.1
      · exact Or.inr h
  have hLQsub : T13.limSup (Ici N) (fun k => Q k ∪ {p}) ⊆ f ⁻¹' {c} :=
    limSup_subset_fibre hf.1 htψ hfp fun k _ x hx => by
      rcases hx with h | h
      · exact Or.inl h.1
      · exact Or.inr h
  have hcov' := fibre_subset_limSup_union (S := fun k => P k ∪ {p}) (T := fun k => Q k ∪ {p})
    hfo htψ ⟨N, subset_rfl⟩ fun k _ x hx => by
      have : x ∈ G k := hx
      rw [← hPQ k] at this
      rcases this with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
  have hLPk : Fold.Q78.IsContinuum (T13.limSup (Ici N) (fun k => P k ∪ {p})) :=
    ⟨(T13.isClosed_limSup _ _).isCompact, ⟨p, hpLP⟩, hLPc⟩
  have hLQk : Fold.Q78.IsContinuum (T13.limSup (Ici N) (fun k => Q k ∪ {p})) :=
    ⟨(T13.isClosed_limSup _ _).isCompact, ⟨p, hpLQ⟩, hLQc⟩
  have heq := Subset.antisymm (union_subset hLPsub hLQsub) hcov'
  rcases (hind c).2 _ _ hLPk hLQk hLPsub hLQsub heq with h | h
  · have hqa : qa ∈ T13.limSup (Ici N) (fun k => P k ∪ {p}) := h ▸ hqac
    obtain ⟨k, -, -, z, hzP', hzW⟩ := exists_mem_of_mem_limSup hqa hWa ⟨hqaE, hqaU⟩ 0
    rcases hzP' with hzP | hzp
    · rcases hsplit (ψ k) z (fun hz => hzW.2 (subset_closure hz)) with hzA | hzB
      · have := hα (ψ k)
        rw [(hψab k).1] at this
        exact eq_empty_iff_forall_notMem.1 this z ⟨hzW.1, hzA, hzP.1⟩
      · exact hzP.2 hzB.2
    · exact hzW.2 (subset_closure (mem_singleton_iff.1 hzp ▸ hp))
  · have hqb : qb ∈ T13.limSup (Ici N) (fun k => Q k ∪ {p}) := h ▸ hqbc
    obtain ⟨k, -, -, z, hzQ', hzW⟩ := exists_mem_of_mem_limSup hqb hWb ⟨hqbE, hqbU⟩ 0
    rcases hzQ' with hzQ | hzp
    · rcases hsplit (ψ k) z (fun hz => hzW.2 (subset_closure hz)) with hzA | hzB
      · exact hzQ.2 hzA.2
      · have := hβ (ψ k)
        rw [(hψab k).2] at this
        exact eq_empty_iff_forall_notMem.1 this z ⟨hzW.1, hzB, hzQ.1⟩
    · exact hzW.2 (subset_closure (mem_singleton_iff.1 hzp ▸ hp))

end HPC.BJ59
