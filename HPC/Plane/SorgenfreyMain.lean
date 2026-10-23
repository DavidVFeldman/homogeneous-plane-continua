import HPC.Plane.SorgenfreyLemmas

/-!
# Batch 102, part 2: the core of Sorgenfrey's theorem (Nadler 11.34 (a))

For `X = Y ⊕ Z` unicoherent and not a weak triod, with `U = X ∖ Z`, there is `p ∈ U` with
`Ū = irr(p, Ū ∩ Z)` (`exists_irrFromTo_point`). Nadler's proof by contradiction, with one
simplification of the induction: instead of choosing `p_{n(j+1)}` as the first point of the dense
sequence outside `K_j`, the step at stage `n` absorbs the `n`-th point `d_n` of the dense sequence
(`K_{n+1} = K_n` if `d_n ∈ K_n` already). All that the rest of the proof uses of the induction is
(7): each `K_n` is a proper subcontinuum of `Ū` containing `Ū ∩ Z`, the `K_n` increase, and every
point of the dense set lies in some `K_n` (`sorgenfrey_contra`). Also `K_0 = Ū ∩ Z` is allowed.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- The sets of the induction in 11.34: proper subcontinua of `Ū` containing `Ū ∩ Z`. -/
def SorgGood (X Z K : Set S) : Prop :=
  Fold.Q78.IsContinuum K ∧ K ⊆ closure (X \ Z) ∧ closure (X \ Z) ∩ Z ⊆ K ∧ K ≠ closure (X \ Z)

variable {X Y Z : Set S}

/-- The supposition "(a) is false", unfolded: every point of `U` lies in a proper subcontinuum of
`Ū` meeting `Z`. -/
theorem exists_proper_of_not_irr (h : IsEssentialSum₂ X Y Z) (hnt : ¬ IsWeakTriod X) {p : S}
    (hp : p ∈ X \ Z) (hna : ¬ IrrFromTo (closure (X \ Z)) {p} (closure (X \ Z) ∩ Z)) :
    ∃ L : Set S, Fold.Q78.IsContinuum L ∧ L ⊆ closure (X \ Z) ∧ p ∈ L ∧ (L ∩ Z).Nonempty ∧
      L ≠ closure (X \ Z) := by
  by_contra hc
  push_neg at hc
  exact hna ⟨isContinuum_closure_diff h hnt, ⟨p, subset_closure hp, rfl⟩,
    by rw [← inter_assoc, inter_self]; exact h.closure_inter_nonempty,
    fun K hK hKT ⟨p', hp', hpp⟩ ⟨z, hzK, _, hzZ⟩ => hc K hK hKT (hpp ▸ hp') ⟨z, hzK, hzZ⟩⟩

/-- The start of the induction: `Ū ∩ Z` (a continuum by unicoherence). -/
theorem sorgGood_base (h : IsEssentialSum₂ X Y Z) (hu : IsUnicoherent X) (hnt : ¬ IsWeakTriod X) :
    SorgGood X Z (closure (X \ Z) ∩ Z) := by
  refine ⟨⟨isClosed_closure.isCompact.inter_right h.2.2.1.1.isClosed,
    hu _ _ (isContinuum_closure_diff h hnt) h.2.2.1 h.eq_closure_union.symm⟩,
    inter_subset_left, Subset.rfl, fun he => ?_⟩
  obtain ⟨u, hu'⟩ := h.diff_nonempty
  have : u ∈ closure (X \ Z) ∩ Z := by rw [he]; exact subset_closure hu'
  exact hu'.2 this.2

/-- The step of the induction (Nadler, via 11.30 and 11.31): a good `K` can be enlarged to a good
`K'` containing a given point of `U`. -/
theorem sorgGood_step (h : IsEssentialSum₂ X Y Z) (hnt : ¬ IsWeakTriod X)
    (hna : ∀ p ∈ X \ Z, ¬ IrrFromTo (closure (X \ Z)) {p} (closure (X \ Z) ∩ Z)) {K : Set S}
    (hK : SorgGood X Z K) {d : S} (hd : d ∈ X \ Z) :
    ∃ K' : Set S, SorgGood X Z K' ∧ K ⊆ K' ∧ d ∈ K' := by
  by_cases hdK : d ∈ K
  · exact ⟨K, hK, Subset.rfl, hdK⟩
  have hT := isContinuum_closure_diff h hnt
  obtain ⟨k, hk⟩ := hK.1.2.nonempty
  obtain ⟨C, hCT, hC⟩ := exists_irrFromTo hT isCompact_singleton hK.1.1
    ⟨d, rfl, subset_closure hd⟩ ⟨k, hk, hK.2.1 hk⟩
  obtain ⟨c, hcC, hcK⟩ := hC.2.2.1
  obtain ⟨d', hd'C, hd'⟩ := hC.2.1
  rw [mem_singleton_iff] at hd'
  subst hd'
  refine ⟨K ∪ C, ⟨isContinuum_union hK.1 hC.1 ⟨c, hcK, hcC⟩, union_subset hK.2.1 hCT,
    hK.2.2.1.trans subset_union_left, fun he => ?_⟩, subset_union_left, Or.inr hd'C⟩
  exact hna d' hd (nadler_11_31 h hnt hK.1 hC.1 hK.2.1 ⟨hd, hdK⟩ hK.2.2.1 hC
    (subset_closure.trans he.symm.subset))

/-- **The body of Nadler's proof of 11.34 (a)**: under the supposition that (a) is false, an
increasing sequence of good continua absorbing a dense sequence of `U` leads to a contradiction
(facts (8), (9), (12), (*), (20)–(25) of the text). -/
theorem sorgenfrey_contra (h : IsEssentialSum₂ X Y Z) (hu : IsUnicoherent X)
    (hnt : ¬ IsWeakTriod X)
    (hna : ∀ p ∈ X \ Z, ¬ IrrFromTo (closure (X \ Z)) {p} (closure (X \ Z) ∩ Z))
    (d : ℕ → S) (hd : ∀ n, d n ∈ X \ Z) (hdense : X \ Z ⊆ closure (range d))
    (K : ℕ → Set S) (hK : ∀ n, SorgGood X Z (K n)) (hKs : ∀ n, K n ⊆ K (n + 1))
    (hdK : ∀ n, d n ∈ K (n + 1)) : False := by
  set T := closure (X \ Z) with hT_def
  have hT : Fold.Q78.IsContinuum T := isContinuum_closure_diff h hnt
  have hTX : T ⊆ X := h.closure_diff_subset
  have hTY : T ⊆ Y := h.closure_diff_subset_left
  have hZcl : IsClosed Z := h.2.2.1.1.isClosed
  obtain ⟨w, hwT, hwZ⟩ := h.closure_inter_nonempty
  obtain ⟨q, hqZ, hqY⟩ := h.right_diff_nonempty
  have hqT : q ∉ T := fun h' => hqY (hTY h')
  have hmono : Monotone K := monotone_nat_of_le_succ hKs
  have hKT : ∀ n, K n ⊆ T := fun n => (hK n).2.1
  have hTZK : ∀ n, T ∩ Z ⊆ K n := fun n => (hK n).2.2.1
  have hKX : ∀ n, K n ⊆ X := fun n => (hKT n).trans hTX
  have hwK : ∀ n, w ∈ K n := fun n => hTZK n ⟨hwT, hwZ⟩
  -- `U_n = U ∖ K_n`
  set Ui : ℕ → Set S := fun n => (X \ Z) \ K n with hUi_def
  have hUiU : ∀ n, Ui n ⊆ X \ Z := fun n => diff_subset
  have hUiK : ∀ n x, x ∈ Ui n → x ∉ K n := fun n x hx => hx.2
  have hUine : ∀ n, (Ui n).Nonempty := fun n => by
    by_contra hc
    rw [not_nonempty_iff_eq_empty, diff_eq_empty] at hc
    exact (hK n).2.2.2 (Subset.antisymm (hKT n) (closure_minimal hc (hK n).1.1.isClosed))
  have hUic : ∀ n, Fold.Q78.IsContinuum (closure (Ui n)) := fun n =>
    ⟨isClosed_closure.isCompact, (isConnected_diff_of_superset' h hnt (hK n).1 (hKT n) (hTZK n)
      (hUine n)).closure⟩
  have hUiT : ∀ n, closure (Ui n) ⊆ T := fun n => closure_mono diff_subset
  -- (8)
  have h8 : ∀ n, closure (Ui n) ⊆ Ui n ∪ K n := fun n x hx => by
    by_cases hxK : x ∈ K n
    · exact Or.inr hxK
    · by_cases hxZ : x ∈ Z
      · exact Or.inr (hTZK n ⟨hUiT n hx, hxZ⟩)
      · exact Or.inl ⟨⟨hTX (hUiT n hx), hxZ⟩, hxK⟩
  have hUanti : ∀ {i j}, i ≤ j → Ui j ⊆ Ui i := fun hij x hx => ⟨hx.1, fun h' => hx.2 (hmono hij h')⟩
  have hUsplit : ∀ n x, x ∈ X \ Z → x ∈ K n ∨ x ∈ Ui n := fun n x hx => by
    by_cases hxK : x ∈ K n
    · exact Or.inl hxK
    · exact Or.inr ⟨hx, hxK⟩
  have hXsplit : ∀ n x, x ∈ X → x ∈ Z ∨ x ∈ K n ∨ x ∈ Ui n := fun n x hx => by
    by_cases hxZ : x ∈ Z
    · exact Or.inl hxZ
    · exact Or.inr (hUsplit n x ⟨hx, hxZ⟩)
  -- (9)
  have h9 : ∀ n, IsConnected (closure (Ui n) ∩ K n) := fun n => by
    have hZK : Fold.Q78.IsContinuum (Z ∪ K n) :=
      isContinuum_union h.2.2.1 (hK n).1 ⟨w, hwZ, hwK n⟩
    have hcov : closure (Ui n) ∪ (Z ∪ K n) = X := by
      apply Subset.antisymm
      · exact union_subset ((hUiT n).trans hTX) (union_subset h.right_subset (hKX n))
      · intro x hx
        rcases hXsplit n x hx with h' | h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
        · exact Or.inl (subset_closure h')
    have := hu _ _ (hUic n) hZK hcov
    have heq : closure (Ui n) ∩ (Z ∪ K n) = closure (Ui n) ∩ K n := by
      apply Subset.antisymm
      · rintro x ⟨hx1, hx2 | hx2⟩
        · exact ⟨hx1, hTZK n ⟨hUiT n hx1, hx2⟩⟩
        · exact ⟨hx1, hx2⟩
      · exact inter_subset_inter_right _ subset_union_right
    rwa [heq] at this
  -- (12): each `Ū_n` is decomposable
  have h12 : ∀ m, ∃ E F : Set S, IsEssentialSum₂ (closure (Ui m)) E F := by
    intro m
    by_contra hdec
    push_neg at hdec
    have hI : Fold.Q78.IsIndecomposable (closure (Ui m)) := by
      refine ⟨hUic m, fun A B hA hB hAI hBI hAB => ?_⟩
      by_contra hc
      push_neg at hc
      exact hdec A B ⟨hUic m, hA, hB, hAB.symm, hc.1, hc.2⟩
    set I := closure (Ui m) with hI_def
    set P := I ∩ K m with hP_def
    have hPc : Fold.Q78.IsContinuum P :=
      ⟨isClosed_closure.isCompact.inter_right (hK m).1.1.isClosed, h9 m⟩
    obtain ⟨a, ha⟩ := hPc.2.nonempty
    obtain ⟨r, hrI, hr⟩ := T13.exists_not_mem_proper_subcontinua (M := I) hI ha.1
    obtain ⟨u, hu'⟩ := hUine m
    have hPne : P ≠ I := fun he => hu'.2 (he ▸ subset_closure hu' : u ∈ P).2
    have key : ∀ C : Set S, Fold.Q78.IsContinuum C → C ⊆ I → r ∈ C → (C ∩ P).Nonempty →
        C = I := by
      intro C hC hCI hrC hCP
      have hCPc := isContinuum_union hC hPc hCP
      have hCPI : C ∪ P = I := by
        by_contra hne
        exact hr _ hCPc (union_subset hCI inter_subset_left) hne (Or.inr ha) (Or.inl hrC)
      rcases hI.2 C P hC hPc hCI inter_subset_left hCPI with h' | h'
      · exact h'
      · exact absurd h' hPne
    have hrK : r ∉ K m := fun hrK => by
      have := key {r} ⟨isCompact_singleton, isConnected_singleton⟩
        (singleton_subset_iff.mpr hrI) rfl ⟨r, rfl, hrI, hrK⟩
      have hu'' : u ∈ ({r} : Set S) := this ▸ subset_closure hu'
      rw [mem_singleton_iff] at hu''
      exact hu'.2 (hu'' ▸ hrK)
    have hrU : r ∈ Ui m := (h8 m hrI).resolve_right hrK
    obtain ⟨L, hL, hLT, hrL, ⟨z, hzL, hzZ⟩, hLne⟩ :=
      exists_proper_of_not_irr h hnt (hUiU m hrU) (hna r (hUiU m hrU))
    obtain ⟨C, hC, hCL, hCcl, hrC, x, hxC, hxO⟩ := exists_continuum_bump_open hL
      (hZcl.union (hK m).1.1.isClosed).isOpen_compl hrL
      (fun h' => by rcases h' with h' | h'; exacts [(hUiU m hrU).2 h', hrK h'])
      (fun hs => hs hzL (Or.inl hzZ))
    rw [Set.notMem_compl_iff] at hxO
    have hCI : C ⊆ I := hCcl.trans (closure_mono fun y ⟨hyL, hyO⟩ =>
      ⟨⟨hTX (hLT hyL), fun h' => hyO (Or.inl h')⟩, fun h' => hyO (Or.inr h')⟩)
    have hxP : x ∈ P := by
      refine ⟨hCI hxC, ?_⟩
      rcases hxO with h' | h'
      · exact hTZK m ⟨hUiT m (hCI hxC), h'⟩
      · exact h'
    have hCeq := key C hC hCI hrC ⟨x, hxC, hxP⟩
    have hIL : I ⊆ L := hCeq ▸ hCL
    obtain ⟨k, hkK, hk⟩ := not_subset.mp fun hs : K m ⊆ Z ∪ L => hLne (Subset.antisymm hLT
      (closure_minimal (fun y hy => by
        rcases hUsplit m y hy with h' | h'
        · exact (hs h').resolve_left hy.2
        · exact hIL (subset_closure h')) hL.1.isClosed))
    rw [mem_union, not_or] at hk
    refine hnt (isWeakTriod_of h.2.2.1 hL (hK m).1 ?_ ⟨q, hqZ, fun h' => hqT (hLT h'),
      fun h' => hqT (hKT m h')⟩ ⟨u, hIL (subset_closure hu'), hu'.1.2, hu'.2⟩ ⟨k, hkK, hk.1, hk.2⟩
      ⟨z, hzZ, hzL, hTZK m ⟨hLT hzL, hzZ⟩⟩)
    apply Subset.antisymm
    · intro y hy
      rcases hXsplit m y hy with h' | h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr (hIL (subset_closure h')))
    · exact union_subset (union_subset h.right_subset (hLT.trans hTX)) (hKX m)
  -- (*)
  have hstar : ∀ ℓ, ∃ n, ℓ < n ∧ K ℓ ∩ closure (Ui n) = ∅ := by
    intro ℓ
    by_contra hc
    push_neg at hc
    have side : ∀ E F : Set S, IsEssentialSum₂ (closure (Ui ℓ)) E F → (E ∩ K ℓ).Nonempty →
        F ∩ K ℓ = ∅ → False := by
      intro E F hEF hEK hFK
      have hE : E ⊆ closure (Ui ℓ) := hEF.left_subset
      have hF : F ⊆ closure (Ui ℓ) := hEF.right_subset
      have hEFeq : closure (Ui ℓ) = E ∪ F := hEF.2.2.2.1
      have hFnK : ∀ x ∈ F, x ∉ K ℓ := fun x hx hxK => by
        have : x ∈ F ∩ K ℓ := ⟨hx, hxK⟩
        rw [hFK] at this; exact this
      have hFU : F ⊆ Ui ℓ := fun x hx => (h8 ℓ (hF hx)).resolve_right (hFnK x hx)
      have hUEF : Ui ℓ ⊆ E ∪ F := fun x hx => hEFeq ▸ subset_closure hx
      obtain ⟨y, hyW, hyE⟩ := hEF.symm.diff_nonempty
      have hyF : y ∈ F := (hEFeq ▸ hyW : y ∈ E ∪ F).resolve_left hyE
      have hyU : y ∈ Ui ℓ := hFU hyF
      obtain ⟨_, ⟨hoE, hoK⟩, ⟨k, rfl⟩⟩ := mem_closure_iff.mp (hdense (hUiU ℓ hyU))
        (Eᶜ ∩ (K ℓ)ᶜ) (hEF.2.1.1.isClosed.isOpen_compl.inter (hK ℓ).1.1.isClosed.isOpen_compl)
        ⟨hyE, hUiK ℓ y hyU⟩
      have hdkF : d k ∈ F := (hUEF ⟨hd k, hoK⟩).resolve_left hoE
      set j := max (k + 1) (ℓ + 1) with hj
      have hℓj : ℓ < j := lt_of_lt_of_le (Nat.lt_succ_self ℓ) (le_max_right _ _)
      have hdkj : d k ∈ K j := hmono (le_max_left _ _) (hdK k)
      have hKℓj : K ℓ ⊆ K j := hmono hℓj.le
      obtain ⟨a, ha⟩ := (hK ℓ).1.2.nonempty
      obtain ⟨J₀, hJ₀, hJ₀K, hJ₀cl, haJ₀, f, hfJ₀, hfF⟩ := exists_continuum_bump_open (hK j).1
        hEF.2.2.1.1.isClosed.isOpen_compl (hKℓj ha) (hFnK a · ha)
        (fun hs => hs hdkj hdkF)
      rw [Set.notMem_compl_iff] at hfF
      set J := J₀ ∪ K ℓ with hJ_def
      have hJc : Fold.Q78.IsContinuum J := isContinuum_union hJ₀ (hK ℓ).1 ⟨a, haJ₀, ha⟩
      have hJK : J ⊆ K j := union_subset hJ₀K hKℓj
      have hJFE : ∀ x ∈ J, x ∈ F → x ∉ E → False := by
        rintro x (hx | hx) hxF hxE
        · have hxU := hFU hxF
          obtain ⟨y, ⟨hyO, hyE'⟩, hyKj, hyF'⟩ := mem_closure_iff.mp (hJ₀cl hx) _
            (((hZcl.union (hK ℓ).1.1.isClosed).isOpen_compl).inter hEF.2.1.1.isClosed.isOpen_compl)
            ⟨fun h' => by rcases h' with h' | h'; exacts [hxU.1.2 h', hUiK ℓ x hxU h'], hxE⟩
          have hyU : y ∈ Ui ℓ := ⟨⟨hKX j hyKj, fun h' => hyO (Or.inl h')⟩,
            fun h' => hyO (Or.inr h')⟩
          rcases hUEF hyU with h' | h'
          · exact hyE' h'
          · exact hyF' h'
        · exact hFnK x hxF hx
      have hA1 : Fold.Q78.IsContinuum (Z ∪ J) :=
        isContinuum_union h.2.2.1 hJc ⟨w, hwZ, Or.inr (hwK ℓ)⟩
      have hB1 : Fold.Q78.IsContinuum (E ∪ J) := by
        obtain ⟨e, heE, heK⟩ := hEK
        exact isContinuum_union hEF.2.1 hJc ⟨e, heE, Or.inr heK⟩
      have hC1 : Fold.Q78.IsContinuum (F ∪ J) :=
        isContinuum_union hEF.2.2.1 hJc ⟨f, hfF, Or.inl hfJ₀⟩
      obtain ⟨v, hv⟩ := h.symm.diff_nonempty
      have hvT : v ∉ T := fun h' => hv.2 (hTY h')
      have hJT : J ⊆ T := hJK.trans (hKT j)
      obtain ⟨z, hzB, hz⟩ := not_subset.mp fun hs : E ∪ J ⊆ (Z ∪ J) ∪ (F ∪ J) => by
        have hEFK : ∀ x ∈ E, x ∉ F → x ∈ K j := fun x hxE hxF => by
          rcases hs (Or.inl hxE) with (h' | h') | (h' | h')
          · exact hTZK j ⟨hUiT ℓ (hE hxE), h'⟩
          · exact hJK h'
          · exact absurd h' hxF
          · exact hJK h'
        have hUjF : Ui j ⊆ F := fun x hx => by
          rcases hUEF (hUanti hℓj.le hx) with h' | h'
          · by_contra hxF
            exact hUiK j x hx (hEFK x h' hxF)
          · exact h'
        obtain ⟨x, hxK, hxcl⟩ := hc j hℓj
        exact hFnK x (closure_minimal hUjF hEF.2.2.1.1.isClosed hxcl) hxK
      simp only [mem_union, not_or] at hz
      refine hnt (isWeakTriod_of hA1 hB1 hC1 ?_ ⟨v, Or.inl (h.symm.diff_subset_left hv),
        fun h' => by rcases h' with h' | h'; exacts [hvT (hUiT ℓ (hE h')), hvT (hJT h')],
        fun h' => by rcases h' with h' | h'; exacts [hvT (hUiT ℓ (hF h')), hvT (hJT h')]⟩
        ⟨z, hzB, fun h' => by rcases h' with h' | h'; exacts [hz.1.1 h', hz.1.2 h'],
          fun h' => by rcases h' with h' | h'; exacts [hz.2.1 h', hz.2.2 h']⟩
        ⟨y, Or.inl hyF, fun h' => by
          rcases h' with h' | h'
          · exact (hUiU ℓ hyU).2 h'
          · exact hJFE y h' hyF hyE, fun h' => by
          rcases h' with h' | h'
          · exact hyE h'
          · exact hJFE y h' hyF hyE⟩
        ⟨a, Or.inr (Or.inr ha), Or.inr (Or.inr ha), Or.inr (Or.inr ha)⟩)
      apply Subset.antisymm
      · intro x hx
        rcases hXsplit ℓ x hx with h' | h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inl (Or.inl (Or.inr (Or.inr h')))
        · rcases hUEF h' with h'' | h''
          · exact Or.inl (Or.inr (Or.inl h''))
          · exact Or.inr (Or.inl h'')
      · refine union_subset (union_subset (union_subset h.right_subset (hJT.trans hTX))
          (union_subset ((hE.trans (hUiT ℓ)).trans hTX) (hJT.trans hTX)))
          (union_subset ((hF.trans (hUiT ℓ)).trans hTX) (hJT.trans hTX))
    obtain ⟨E, F, hEF⟩ := h12 ℓ
    rcases nadler_11_32 h hu hnt (hK ℓ).1 (hKT ℓ) (hTZK ℓ) hEF with ⟨hE, hF⟩ | ⟨hF, hE⟩
    · exact side F E hEF.symm hF hE
    · exact side E F hEF hE hF
  -- (20): a point `t` of `⋂ Ū_i`; by (*) it lies in no `K_ℓ`
  obtain ⟨t, ht⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => closure (Ui n)) (fun n => closure_mono (hUanti (Nat.le_succ n)))
    (fun n => (hUine n).closure) (hUic 0).1 (fun n => isClosed_closure)
  rw [mem_iInter] at ht
  have htK : ∀ ℓ, t ∉ K ℓ := fun ℓ htK => by
    obtain ⟨n, -, hn⟩ := hstar ℓ
    have : t ∈ K ℓ ∩ closure (Ui n) := ⟨htK, ht n⟩
    rw [hn] at this; exact this
  have htU : t ∈ X \ Z := hUiU 0 ((h8 0 (ht 0)).resolve_right (htK 0))
  obtain ⟨Q, hQ, hQT, htQ, ⟨y, hyQ, hyZ⟩, hQne⟩ := exists_proper_of_not_irr h hnt htU (hna t htU)
  -- (21)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ¬ K ℓ \ Z ⊆ Q := by
    by_contra hc
    push_neg at hc
    have hdQ : range d ⊆ Q := by rintro _ ⟨k, rfl⟩; exact hc (k + 1) ⟨hdK k, (hd k).2⟩
    exact hQne (Subset.antisymm hQT
      (closure_minimal (hdense.trans (closure_minimal hdQ hQ.1.isClosed)) hQ.1.isClosed))
  obtain ⟨x, ⟨hxK, hxZ⟩, hxQ⟩ := not_subset.mp hℓ
  -- (22)
  obtain ⟨n, hℓn, hn⟩ := hstar ℓ
  have hxcl : x ∉ closure (Ui n) := fun h' => by
    have : x ∈ K ℓ ∩ closure (Ui n) := ⟨hxK, h'⟩
    rw [hn] at this; exact this
  have hQU : Fold.Q78.IsContinuum (Q ∪ closure (Ui n)) :=
    isContinuum_union hQ (hUic n) ⟨t, htQ, ht n⟩
  -- (23)–(25): `X = Z ⊕ K_n ⊕ (Q ∪ Ū_n)` with a common point
  refine hnt (isWeakTriod_of h.2.2.1 (hK n).1 hQU ?_
    ⟨q, hqZ, fun h' => hqT (hKT n h'),
      fun h' => by rcases h' with h' | h'; exacts [hqT (hQT h'), hqT (hUiT n h')]⟩
    ⟨x, hmono hℓn.le hxK, hxZ, fun h' => by rcases h' with h' | h'; exacts [hxQ h', hxcl h']⟩
    ⟨t, Or.inl htQ, htU.2, htK n⟩ ⟨y, hyZ, hTZK n ⟨hQT hyQ, hyZ⟩, Or.inl hyQ⟩)
  apply Subset.antisymm
  · intro z hz
    rcases hXsplit n z hz with h' | h' | h'
    · exact Or.inl (Or.inl h')
    · exact Or.inl (Or.inr h')
    · exact Or.inr (Or.inr (subset_closure h'))
  · exact union_subset (union_subset h.right_subset (hKX n))
      (union_subset (hQT.trans hTX) ((hUiT n).trans hTX))

/-- **Nadler 11.34 (a).** If `X = Y ⊕ Z` is unicoherent and not a weak triod, then
`Ū = irr(p, Ū ∩ Z)` for some `p ∈ U = X ∖ Z`. -/
theorem exists_irrFromTo_point (h : IsEssentialSum₂ X Y Z) (hu : IsUnicoherent X)
    (hnt : ¬ IsWeakTriod X) :
    ∃ p ∈ X \ Z, IrrFromTo (closure (X \ Z)) {p} (closure (X \ Z) ∩ Z) := by
  by_contra hna
  push_neg at hna
  -- a dense sequence in `U`
  obtain ⟨D, hDU, hDc, hUD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (X \ Z)).exists_countable_dense_subset
  have hDne : D.Nonempty := by
    obtain ⟨u, hu'⟩ := h.diff_nonempty
    by_contra hc
    rw [not_nonempty_iff_eq_empty] at hc
    have := hUD hu'
    rw [hc, closure_empty] at this
    exact this
  obtain ⟨d, rfl⟩ := hDc.exists_eq_range hDne
  have hd : ∀ n, d n ∈ X \ Z := fun n => hDU ⟨n, rfl⟩
  -- the induction
  have hstep : ∀ (K : Set S) (x : S), ∃ K' : Set S,
      SorgGood X Z K → x ∈ X \ Z → SorgGood X Z K' ∧ K ⊆ K' ∧ x ∈ K' := by
    intro K x
    by_cases hK : SorgGood X Z K
    · by_cases hx : x ∈ X \ Z
      · obtain ⟨K', hK'⟩ := sorgGood_step h hnt hna hK hx
        exact ⟨K', fun _ _ => hK'⟩
      · exact ⟨K, fun _ h' => absurd h' hx⟩
    · exact ⟨K, fun h' => absurd h' hK⟩
  choose G hG using hstep
  let K : ℕ → Set S := fun n => Nat.rec (closure (X \ Z) ∩ Z) (fun k Kk => G Kk (d k)) n
  have hKgood : ∀ n, SorgGood X Z (K n) := by
    intro n
    induction n with
    | zero => exact sorgGood_base h hu hnt
    | succ k ih => exact (hG (K k) (d k) ih (hd k)).1
  exact sorgenfrey_contra h hu hnt hna d hd hUD K hKgood
    (fun n => (hG (K n) (d n) (hKgood n) (hd n)).2.1)
    (fun n => (hG (K n) (d n) (hKgood n) (hd n)).2.2)

end HPC.Plane
