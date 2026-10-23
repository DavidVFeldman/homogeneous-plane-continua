import HPC.Plane.RealStep
import HPC.Plane.CSide
import HPC.PseudoArc.Uniqueness

/-!
# Bing 1951, Theorem 4: the construction

Batch 84 (COMMISSION-batch84.md §2, §3.5). Level by level: a minimal covering chain `C_i` of `M`
of mesh `< 1/2^i` and a tame rectangle chain `D_i = Φ_i(stdRect j)` in the plane. The refinement
pattern of `C_{i+1}` in `C_i` is chosen slow enough for the planar step `real_step` at level `i`,
and `D_{i+1}` follows it. Bing 1948 Theorem 11 (`MatchingCovers.exists_homeomorph`) then gives
`M ≃ₜ ⋂ D_i^*`.
-/

namespace HPC.Plane

open Set Metric

section Nested

variable {X : Type*} [MetricSpace X] {n : ℕ → ℕ} (D : (i : ℕ) → Chain X (n i))

theorem union_antitone_of_closure
    (hcl' : ∀ i (t : Fin (n (i + 1))), ∃ s : Fin (n i), closure ((D (i + 1)).link t) ⊆ (D i).link s) :
    Antitone fun i => (D i).union := by
  refine antitone_nat_of_succ_le fun i => ?_
  intro p hp
  obtain ⟨t, ht⟩ := mem_iUnion.mp hp
  obtain ⟨s, hs⟩ := hcl' i t
  exact mem_iUnion.mpr ⟨s, hs (subset_closure ht)⟩

/-- The intersection of a nested sequence of chains with compact link closures is compact. -/
theorem isCompact_iInter_union
    (hcl' : ∀ i (t : Fin (n (i + 1))), ∃ s : Fin (n i), closure ((D (i + 1)).link t) ⊆ (D i).link s)
    (hc : ∀ i (s : Fin (n i)), IsCompact (closure ((D i).link s))) :
    IsCompact (⋂ j, (D j).union) := by
  set K : ℕ → Set X := fun j => ⋃ t, closure ((D j).link t) with hK
  have hKc : ∀ j, IsCompact (K j) := fun j => isCompact_iUnion fun t => hc j t
  have hUK : ∀ j, (D j).union ⊆ K j := fun j =>
    iUnion_mono fun t => subset_closure
  have hKU : ∀ j, K (j + 1) ⊆ (D j).union := by
    intro j p hp
    obtain ⟨t, ht⟩ := mem_iUnion.mp hp
    obtain ⟨s, hs⟩ := hcl' j t
    exact mem_iUnion.mpr ⟨s, hs ht⟩
  have heq : (⋂ j, (D j).union) = ⋂ j, K j := by
    apply Subset.antisymm
    · exact iInter_mono hUK
    · intro p hp
      rw [mem_iInter] at hp ⊢
      exact fun j => hKU j (hp (j + 1))
  rw [heq]
  exact (hKc 0).of_isClosed_subset (isClosed_iInter fun j => (hKc j).isClosed) (iInter_subset _ 0)

/-- Every link of a nested sequence of chains, each link containing the closure of a link of the
next level, meets the intersection. -/
theorem link_inter_iInter_union_nonempty
    (hcl : ∀ i (s : Fin (n i)), ∃ t : Fin (n (i + 1)), closure ((D (i + 1)).link t) ⊆ (D i).link s)
    (hcl' : ∀ i (t : Fin (n (i + 1))), ∃ s : Fin (n i), closure ((D (i + 1)).link t) ⊆ (D i).link s)
    (hc : ∀ i (s : Fin (n i)), IsCompact (closure ((D i).link s))) (i : ℕ) (s : Fin (n i)) :
    ((D i).link s ∩ ⋂ j, (D j).union).Nonempty := by
  classical
  choose g hg using fun (k : ℕ) (u : Fin (n (i + k))) => hcl (i + k) u
  set F : (k : ℕ) → Fin (n (i + k)) :=
    fun k => Nat.rec (motive := fun k => Fin (n (i + k))) s (fun k u => g k u) k with hF
  set K : ℕ → Set X := fun k => closure ((D (i + k)).link (F k)) with hK
  have hstep : ∀ k, K (k + 1) ⊆ (D (i + k)).link (F k) := fun k => hg k (F k)
  have hnested : ∀ k, K (k + 1) ⊆ K k := fun k => (hstep k).trans subset_closure
  have hne : ∀ k, (K k).Nonempty :=
    fun k => ((D (i + k)).link_nonempty (F k)).mono subset_closure
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hnested
    hne (hc _ _) (fun k => isClosed_closure)
  simp only [mem_iInter] at hz
  have hz0 : z ∈ (D i).link s := hstep 0 (hz 1)
  refine ⟨z, hz0, ?_⟩
  have hzi : z ∈ (D i).union := mem_iUnion.mpr ⟨s, hz0⟩
  rw [mem_iInter]
  intro j
  rcases le_or_gt i j with hij | hij
  · obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
    exact mem_iUnion.mpr ⟨F k, hstep k (hz (k + 1))⟩
  · exact union_antitone_of_closure D hcl' hij.le hzi

end Nested

variable {X : Type*} [MetricSpace X]

/-- A level of the construction of Theorem 4: a minimal covering chain `C` of `M` and a tame
chain `Φ(stdRect j)`, `j < m`, in the plane, with the same number of links. -/
structure TStage (M : Set X) where
  m : ℕ
  C : Chain X m
  Φ : Pt ≃ₜ Pt
  hm : 0 < m
  hC : MinCover C M

/-- One step of the construction of Theorem 4. -/
theorem t4_step {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (S : TStage M) {ε : ℝ} (hε : 0 < ε) :
    ∃ S' : TStage M, ∃ x : Fin S'.m → Fin S.m,
      (∀ t, S'.C.link t ⊆ S.C.link (x t)) ∧
      (∀ t, closure ((tameChain S'.Φ S'.m).link t) ⊆ (tameChain S.Φ S.m).link (x t)) ∧
      Function.Surjective x ∧
      (∀ t, Bornology.IsBounded (S'.C.link t) ∧ diam (S'.C.link t) < ε) ∧
      (∀ t, diam ((tameChain S'.Φ S'.m).link t) ≤ ε ∨
        ∃ k : ℕ, k < S.m ∧ (tameChain S'.Φ S'.m).link t ⊆ S.Φ '' zone k) ∧
      (∀ k : ℕ, k < S'.m → Bornology.IsBounded (S'.Φ '' zone k) ∧ diam (S'.Φ '' zone k) ≤ ε) := by
  obtain ⟨N, hN, hstep⟩ := real_step S.Φ S.hm hε
  obtain ⟨m', C', x, hC', hmesh, hsub, hus, hslow, hsurj⟩ :=
    refine_step S.hC hMc hMconn hsnake N (by omega) hε
  have hm' : 0 < m' := by
    obtain ⟨z, hz⟩ := hMconn.nonempty
    obtain ⟨j, -⟩ := mem_iUnion.mp (hC'.1 hz)
    exact Nat.pos_of_ne_zero fun h => by subst h; exact j.elim0
  obtain ⟨Ψ, h1, -, h3, h4, -, -⟩ := hstep m' x hm' hus hslow
  exact ⟨⟨m', C', Ψ.trans S.Φ, hm', hC'⟩, x, hsub, h1, hsurj, hmesh, h3, h4⟩

section Construction

variable {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)

include hMconn hsnake in
/-- The base level: a minimal covering chain of mesh `< 1`, and the standard rectangles. -/
theorem exists_t4_base : ∃ S : TStage M, S.Φ = Homeomorph.refl Pt ∧
    ∀ t, Bornology.IsBounded (S.C.link t) ∧ diam (S.C.link t) < 1 := by
  obtain ⟨n, E, hE, hEcov⟩ := hsnake 1 one_pos
  obtain ⟨m, C, hC, hlinks⟩ := exists_minCover E hMconn.nonempty hEcov
  have hm : 0 < m := by
    obtain ⟨z, hz⟩ := hMconn.nonempty
    obtain ⟨j, -⟩ := mem_iUnion.mp (hC.1 hz)
    exact Nat.pos_of_ne_zero fun h => by subst h; exact j.elim0
  refine ⟨⟨m, C, Homeomorph.refl Pt, hm, hC⟩, rfl, fun t => ?_⟩
  obtain ⟨j, hj⟩ := hlinks t
  show Bornology.IsBounded (C.link t) ∧ diam (C.link t) < 1
  rw [hj]; exact hE j

/-- The levels of the construction. -/
noncomputable def tstage : ℕ → TStage M
  | 0 => Classical.choose (exists_t4_base hMconn hsnake)
  | i + 1 => Classical.choose (t4_step hMc hMconn hsnake (tstage i) (ε := 1 / 2 ^ i) (by positivity))

theorem tstage_zero :
    (tstage hMc hMconn hsnake 0).Φ = Homeomorph.refl Pt ∧
    ∀ t, Bornology.IsBounded ((tstage hMc hMconn hsnake 0).C.link t) ∧
      diam ((tstage hMc hMconn hsnake 0).C.link t) < 1 :=
  Classical.choose_spec (exists_t4_base hMconn hsnake)

theorem tstage_spec (i : ℕ) :
    ∃ x : Fin (tstage hMc hMconn hsnake (i + 1)).m → Fin (tstage hMc hMconn hsnake i).m,
      (∀ t, (tstage hMc hMconn hsnake (i + 1)).C.link t ⊆ (tstage hMc hMconn hsnake i).C.link (x t)) ∧
      (∀ t, closure ((tameChain (tstage hMc hMconn hsnake (i + 1)).Φ
          (tstage hMc hMconn hsnake (i + 1)).m).link t) ⊆
        (tameChain (tstage hMc hMconn hsnake i).Φ (tstage hMc hMconn hsnake i).m).link (x t)) ∧
      Function.Surjective x ∧
      (∀ t, Bornology.IsBounded ((tstage hMc hMconn hsnake (i + 1)).C.link t) ∧
        diam ((tstage hMc hMconn hsnake (i + 1)).C.link t) < 1 / 2 ^ i) ∧
      (∀ t, diam ((tameChain (tstage hMc hMconn hsnake (i + 1)).Φ
          (tstage hMc hMconn hsnake (i + 1)).m).link t) ≤ 1 / 2 ^ i ∨
        ∃ k : ℕ, k < (tstage hMc hMconn hsnake i).m ∧
          (tameChain (tstage hMc hMconn hsnake (i + 1)).Φ (tstage hMc hMconn hsnake (i + 1)).m).link t
            ⊆ (tstage hMc hMconn hsnake i).Φ '' zone k) ∧
      (∀ k : ℕ, k < (tstage hMc hMconn hsnake (i + 1)).m →
        Bornology.IsBounded ((tstage hMc hMconn hsnake (i + 1)).Φ '' zone k) ∧
        diam ((tstage hMc hMconn hsnake (i + 1)).Φ '' zone k) ≤ 1 / 2 ^ i) :=
  Classical.choose_spec (t4_step hMc hMconn hsnake (tstage hMc hMconn hsnake i) (ε := 1 / 2 ^ i)
    (by positivity))

/-- The plane chains of the construction. -/
noncomputable def tchain (i : ℕ) : Chain Pt (tstage hMc hMconn hsnake i).m :=
  tameChain (tstage hMc hMconn hsnake i).Φ (tstage hMc hMconn hsnake i).m

theorem tzone_diam (i : ℕ) (k : ℕ) (hk : k < (tstage hMc hMconn hsnake i).m) :
    Bornology.IsBounded ((tstage hMc hMconn hsnake i).Φ '' zone k) ∧
      diam ((tstage hMc hMconn hsnake i).Φ '' zone k) ≤ 2 / 2 ^ i := by
  cases i with
  | zero =>
      have e : (tstage hMc hMconn hsnake 0).Φ '' zone k = zone k := by
        rw [(tstage_zero hMc hMconn hsnake).1]; ext p; simp
      rw [e]
      refine ⟨(isCompact_zone k).isBounded, ?_⟩
      refine diam_le_of_forall_dist_le (by norm_num) ?_
      rintro ⟨a, b⟩ ⟨⟨h1, h2⟩, h3, h4⟩ ⟨c, d⟩ ⟨⟨h5, h6⟩, h7, h8⟩
      apply dist_le_of_abs_le
      · rw [abs_le]; simp only at *; constructor <;> linarith
      · rw [abs_le]; simp only at *; constructor <;> linarith
  | succ i =>
      obtain ⟨-, -, -, -, -, -, h⟩ := tstage_spec hMc hMconn hsnake i
      obtain ⟨b, d⟩ := h k hk
      refine ⟨b, d.trans (le_of_eq ?_)⟩
      rw [pow_succ]; field_simp

theorem tlink_diam (i : ℕ) (t : Fin (tstage hMc hMconn hsnake i).m) :
    diam ((tchain hMc hMconn hsnake i).link t) ≤ 4 / 2 ^ i := by
  cases i with
  | zero =>
      have e : (tchain hMc hMconn hsnake 0).link t = stdRect t := by
        simp only [tchain, tameChain_link, (tstage_zero hMc hMconn hsnake).1]; ext p; simp
      rw [e]; simp only [pow_zero, div_one]
      refine (diam_le_of_forall_dist_le (by norm_num) ?_).trans (by norm_num : (3 : ℝ) ≤ 4)
      rintro ⟨a, b⟩ ⟨⟨h1, h2⟩, h3, h4⟩ ⟨c, d⟩ ⟨⟨h5, h6⟩, h7, h8⟩
      apply dist_le_of_abs_le
      · rw [abs_le]; simp only at *; constructor <;> linarith
      · rw [abs_le]; simp only at *; constructor <;> linarith
  | succ i =>
      obtain ⟨-, -, -, -, -, h, -⟩ := tstage_spec hMc hMconn hsnake i
      rcases h t with h | ⟨k, hk, hs⟩
      · refine h.trans ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
        nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) i]
      · obtain ⟨b, d⟩ := tzone_diam hMc hMconn hsnake i k hk
        refine (diam_mono hs b).trans (d.trans (le_of_eq ?_))
        rw [pow_succ]; field_simp; norm_num

theorem tC_diam (i : ℕ) (t : Fin (tstage hMc hMconn hsnake i).m) :
    Bornology.IsBounded ((tstage hMc hMconn hsnake i).C.link t) ∧
      diam ((tstage hMc hMconn hsnake i).C.link t) < 8 / 2 ^ i := by
  cases i with
  | zero =>
      obtain ⟨b, d⟩ := (tstage_zero hMc hMconn hsnake).2 t
      exact ⟨b, by simp only [pow_zero, div_one]; linarith⟩
  | succ i =>
      obtain ⟨-, -, -, -, h, -, -⟩ := tstage_spec hMc hMconn hsnake i
      obtain ⟨b, d⟩ := h t
      refine ⟨b, d.trans ?_⟩
      rw [div_lt_div_iff₀ (by positivity) (by positivity), pow_succ]
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) i]

theorem tchain_closure_compact (i : ℕ) (t : Fin (tstage hMc hMconn hsnake i).m) :
    IsCompact (closure ((tchain hMc hMconn hsnake i).link t)) := by
  rw [tchain, closure_tameChain_link]
  exact (isCompact_closure_stdRect t).image (tstage hMc hMconn hsnake i).Φ.continuous

/-- The plane continuum `⋂ D_i^*`. -/
def tN : Set Pt := ⋂ i, (tchain hMc hMconn hsnake i).union

theorem isCompact_tN : IsCompact (tN hMc hMconn hsnake) := by
  refine isCompact_iInter_union (tchain hMc hMconn hsnake) (fun i t => ?_)
    (tchain_closure_compact hMc hMconn hsnake)
  obtain ⟨x, -, h, -⟩ := tstage_spec hMc hMconn hsnake i
  exact ⟨x t, h t⟩

theorem tchain_meets (i : ℕ) (s : Fin (tstage hMc hMconn hsnake i).m) :
    ((tchain hMc hMconn hsnake i).link s ∩ tN hMc hMconn hsnake).Nonempty := by
  refine link_inter_iInter_union_nonempty (tchain hMc hMconn hsnake) (fun i s => ?_)
    (fun i t => ?_) (tchain_closure_compact hMc hMconn hsnake) i s
  · obtain ⟨x, -, h, hs, -⟩ := tstage_spec hMc hMconn hsnake i
    obtain ⟨t, rfl⟩ := hs s
    exact ⟨t, h t⟩
  · obtain ⟨x, -, h, -⟩ := tstage_spec hMc hMconn hsnake i
    exact ⟨x t, h t⟩

/-- **The construction of Theorem 4.** `M` is homeomorphic to the plane set `tN`. -/
theorem exists_homeomorph_tN : Nonempty (M ≃ₜ tN hMc hMconn hsnake) := by
  have hεpos : ∀ i : ℕ, (0 : ℝ) < 8 / 2 ^ i := fun i => by positivity
  have hsum : Summable (fun i : ℕ => (8 : ℝ) / 2 ^ i) := by
    have := (summable_geometric_two).mul_left 8
    refine this.congr fun i => ?_
    rw [one_div, inv_pow]; ring
  have htl : ∀ i t, diam ((tchain hMc hMconn hsnake i).link t) < 8 / 2 ^ i := fun i t => by
    have := tlink_diam hMc hMconn hsnake i t
    have : (4 : ℝ) / 2 ^ i < 8 / 2 ^ i := by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num
    linarith
  obtain ⟨T, -⟩ := MatchingCovers.exists_homeomorph
    (M₁ := M) (M₂ := tN hMc hMconn hsnake) (ε := fun i => 8 / 2 ^ i)
    { N := fun i => (tstage hMc hMconn hsnake i).m
      x₁ := fun i => (tstage hMc hMconn hsnake i).C.link
      x₂ := fun i => (tchain hMc hMconn hsnake i).link
      open₁ := fun i => (tstage hMc hMconn hsnake i).C.isOpen
      open₂ := fun i => (tchain hMc hMconn hsnake i).isOpen
      cover₁ := fun i => (tstage hMc hMconn hsnake i).hC.1
      cover₂ := fun i => iInter_subset _ i
      meet₁ := fun i k => (tstage hMc hMconn hsnake i).hC.meets hMconn k
      meet₂ := fun i k => tchain_meets hMc hMconn hsnake i k
      bdd₁ := fun i k => (tC_diam hMc hMconn hsnake i k).1
      bdd₂ := fun i k => tameChain_link_bounded _ _ k
      diam₁ := fun i k => (tC_diam hMc hMconn hsnake i k).2.le
      diam₂ := fun i k => (htl i k).le
      match₁ := by
        intro i j k hjk
        obtain ⟨x, h1, h2, -⟩ := tstage_spec hMc hMconn hsnake i
        exact Chain.pattern_matching (Y₂ := tchain hMc hMconn hsnake (i + 1))
          (Z₂ := tchain hMc hMconn hsnake i) x h1
          (fun t => subset_closure.trans (h2 t)) (htl i)
          (fun s => tameChain_link_bounded _ _ s) j k hjk
      match₂ := by
        intro i j k hjk
        obtain ⟨x, h1, h2, -⟩ := tstage_spec hMc hMconn hsnake i
        exact Chain.pattern_matching (Y₁ := tchain hMc hMconn hsnake (i + 1))
          (Z₁ := tchain hMc hMconn hsnake i) x
          (fun t => subset_closure.trans (h2 t)) h1 (fun s => (tC_diam hMc hMconn hsnake i s).2)
          (fun s => (tC_diam hMc hMconn hsnake i s).1) j k hjk }
    hMc (isCompact_tN hMc hMconn hsnake) hεpos hsum
  exact ⟨T⟩

end Construction

/-- **Theorem 4, unbundled.** A compact connected set covered by chains of arbitrarily small mesh
is homeomorphic to a compact connected subset of the plane. -/
theorem theorem4_of {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union) :
    ∃ N : Set Pt, IsCompact N ∧ IsConnected N ∧ Nonempty (M ≃ₜ N) := by
  obtain ⟨T⟩ := exists_homeomorph_tN hMc hMconn hsnake
  refine ⟨_, isCompact_tN hMc hMconn hsnake, ?_, ⟨T⟩⟩
  haveI : ConnectedSpace M := isConnected_iff_connectedSpace.mp hMconn
  have h := isConnected_univ.image (fun p : M => (T p : Pt))
    ((continuous_subtype_val.comp T.continuous).continuousOn)
  convert h using 1
  ext q
  constructor
  · intro hq
    refine ⟨T.symm ⟨q, hq⟩, mem_univ _, ?_⟩
    simp
  · rintro ⟨p, -, rfl⟩
    exact (T p).2

end HPC.Plane
