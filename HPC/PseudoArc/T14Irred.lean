import HPC.PseudoArc.Theorem13
import HPC.PseudoArc.T13Step

/-!
# Batch 83: nested intersections of continua

Topological support for `exists_irreducible` (`Theorem14.lean`): the intersection of a nonempty
chain (under inclusion) of compact connected sets in a compact metric space is compact and
connected.
-/

namespace HPC

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

namespace T14

/-- The intersection of a nonempty chain of compact preconnected sets is preconnected. -/
theorem isPreconnected_sInter_chain [CompactSpace X] {c : Set (Set X)} (hne : c.Nonempty)
    (hch : IsChain (· ⊆ ·) c) (hcpt : ∀ W ∈ c, IsCompact W) (hconn : ∀ W ∈ c, IsPreconnected W) :
    IsPreconnected (⋂₀ c) := by
  have hclosed : IsClosed (⋂₀ c) := isClosed_sInter fun W hW => (hcpt W hW).isClosed
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hclosed]
  intro u v hu hv hsub hdisj
  obtain ⟨δ, hδ, hδd⟩ := hdisj.exists_thickenings hu.isCompact hv
  have hopen : IsOpen (thickening δ u ∪ thickening δ v) :=
    isOpen_thickening.union isOpen_thickening
  haveI : Nonempty c := hne.to_subtype
  obtain ⟨⟨W, hWc⟩, hW⟩ : ∃ i : c, (i : Set X) ⊆ thickening δ u ∪ thickening δ v := by
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
      rcases hsub hx' with h | h
      · exact Or.inl (self_subset_thickening hδ _ h)
      · exact Or.inr (self_subset_thickening hδ _ h)
  have hLW : ⋂₀ c ⊆ W := sInter_subset_of_mem hWc
  rcases isPreconnected_iff_subset_of_disjoint.mp (hconn W hWc) _ _ isOpen_thickening
      isOpen_thickening hW (by
        rw [hδd.inter_eq]; exact inter_empty _) with h | h
  · left
    intro z hz
    rcases hsub hz with h' | h'
    · exact h'
    · exact absurd ⟨h (hLW hz), self_subset_thickening hδ _ h'⟩ (fun h2 => hδd.le_bot h2)
  · right
    intro z hz
    rcases hsub hz with h' | h'
    · exact absurd ⟨self_subset_thickening hδ _ h', h (hLW hz)⟩ (fun h2 => hδd.le_bot h2)
    · exact h'

/-! ## Transport of subsets of `M` by a self-homeomorphism of `M` -/

/-- The image, read in `X`, of the part of `S` in `M` under a self-homeomorphism `T` of `M`. -/
def homImage {M : Set X} (T : M ≃ₜ M) (S : Set X) : Set X :=
  (fun w : M => (T w : X)) '' {w | (w : X) ∈ S}

theorem homImage_subset {M : Set X} (T : M ≃ₜ M) (S : Set X) : homImage T S ⊆ M := by
  rintro _ ⟨w, -, rfl⟩; exact (T w).2

theorem homImage_mono {M : Set X} (T : M ≃ₜ M) {S S' : Set X} (h : S ⊆ S') :
    homImage T S ⊆ homImage T S' := by
  rintro _ ⟨w, hw, rfl⟩; exact ⟨w, h hw, rfl⟩

theorem mem_homImage {M : Set X} (T : M ≃ₜ M) (S : Set X) (w : M) :
    (T w : X) ∈ homImage T S ↔ (w : X) ∈ S := by
  constructor
  · rintro ⟨v, hv, e⟩
    have : v = w := T.injective (Subtype.ext e)
    exact this ▸ hv
  · intro h; exact ⟨w, h, rfl⟩

theorem homImage_symm {M : Set X} (T : M ≃ₜ M) {S : Set X} (hS : S ⊆ M) :
    homImage T.symm (homImage T S) = S := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    have := (mem_homImage T S (T.symm v)).mp (by simpa using hv)
    exact this
  · intro hx
    refine ⟨T ⟨x, hS hx⟩, (mem_homImage T S ⟨x, hS hx⟩).mpr hx, by simp⟩

theorem isContinuum_homImage {M : Set X} (T : M ≃ₜ M) {S : Set X} (hSM : S ⊆ M)
    (hS : Fold.Q78.IsContinuum S) : Fold.Q78.IsContinuum (homImage T S) := by
  have heq : (Subtype.val : M → X) '' {w | (w : X) ∈ S} = S := by
    rw [show {w : M | (w : X) ∈ S} = Subtype.val ⁻¹' S from rfl, Subtype.image_preimage_coe]
    exact inter_eq_right.mpr hSM
  have hc : Continuous (fun w : M => (T w : X)) := continuous_subtype_val.comp T.continuous
  have hcpt : IsCompact {w : M | (w : X) ∈ S} :=
    Topology.IsInducing.subtypeVal.isCompact_iff.mpr (by rw [heq]; exact hS.1)
  have hpc : IsPreconnected {w : M | (w : X) ∈ S} :=
    Topology.IsInducing.subtypeVal.isPreconnected_image.mp (by rw [heq]; exact hS.2.2)
  obtain ⟨x, hx⟩ := hS.2.1
  exact ⟨hcpt.image hc, ⟨_, ⟨⟨x, hSM hx⟩, hx, rfl⟩⟩, hpc.image _ hc.continuousOn⟩

end T14

namespace Chain

variable {n : ℕ}

/-- The end links of a subchain from `R` to `S` contain `R` and `S` (in one of the two orders). -/
theorem IsSubchainFrom.ends {D : Chain X n} {a b : Fin n} {R S : X}
    (h : D.IsSubchainFrom a b R S) :
    a ≤ b ∧ ((R ∈ D.link a ∧ S ∈ D.link b) ∨ (S ∈ D.link a ∧ R ∈ D.link b)) := by
  obtain ⟨hab, h | h⟩ := h
  · obtain ⟨hn, hR, hS, -, -⟩ := h
    have e : (⟨a.val + (b.val - a.val + 1 - 1), by omega⟩ : Fin n) = b := by
      ext; simp only; rw [Fin.le_def] at hab; omega
    refine ⟨hab, Or.inl ⟨by simpa [sub] using hR, ?_⟩⟩
    simp only [sub] at hS; rwa [e] at hS
  · obtain ⟨hn, hS, hR, -, -⟩ := h
    have e : (⟨a.val + (b.val - a.val + 1 - 1), by omega⟩ : Fin n) = b := by
      ext; simp only; rw [Fin.le_def] at hab; omega
    refine ⟨hab, Or.inr ⟨by simpa [sub] using hS, ?_⟩⟩
    simp only [sub] at hR; rwa [e] at hR

/-- A preconnected set inside the union of a chain containing `R` and `S` meets every link of a
subchain from `R` to `S`. -/
theorem IsSubchainFrom.inter_link_nonempty {D : Chain X n} {a b : Fin n} {R S : X}
    (h : D.IsSubchainFrom a b R S) {K : Set X} (hK : IsPreconnected K) (hKD : K ⊆ D.union)
    (hRK : R ∈ K) (hSK : S ∈ K) {t : Fin n} (hat : a ≤ t) (htb : t ≤ b) :
    (K ∩ D.link t).Nonempty := by
  obtain ⟨-, hends⟩ := h.ends
  have ha : (K ∩ D.link a).Nonempty := by
    rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨R, hRK, h1⟩
    · exact ⟨S, hSK, h1⟩
  have hb : (K ∩ D.link b).Nonempty := by
    rcases hends with ⟨-, h1⟩ | ⟨-, h1⟩
    · exact ⟨S, hSK, h1⟩
    · exact ⟨R, hRK, h1⟩
  rcases eq_or_lt_of_le hat with e | hat'
  · exact e ▸ ha
  rcases eq_or_lt_of_le htb with e | htb'
  · exact e ▸ hb
  exact D.inter_link_nonempty_between hK hKD hat' htb' ha hb

end Chain

namespace Description

variable {P Q : X} (Δ : Description X P Q)

/-- **Bing's limiting set** (p. 742): for distinct `A`, `B` in `M` there is a closed connected
`L ⊆ M` through `A` and `B` contained in every closed connected subset of `M` through `A`
and `B`. `L` is the limit superior of the spans of the subchains `D_k(A, B)`. -/
theorem exists_least_connected [CompactSpace X] {A B : X} (hA : A ∈ Δ.M) (hB : B ∈ Δ.M)
    (hAB : A ≠ B) : ∃ L : Set X, IsClosed L ∧ IsPreconnected L ∧ A ∈ L ∧ B ∈ L ∧ L ⊆ Δ.M ∧
      ∀ K : Set X, IsClosed K → IsPreconnected K → K ⊆ Δ.M → A ∈ K → B ∈ K → L ⊆ K := by
  classical
  have hAB' : 0 < dist A B := dist_pos.mpr hAB
  obtain ⟨k0, hk0⟩ : ∃ k0, ∀ k, k0 ≤ k → Δ.ε k < dist A B :=
    eventually_atTop.mp (Δ.ε_tendsto.eventually (gt_mem_nhds hAB'))
  have hex : ∀ k, ∃ ab : Fin (Δ.n k) × Fin (Δ.n k), k0 ≤ k → (Δ.D k).IsSubchainFrom ab.1 ab.2 A B := by
    intro k
    by_cases hk : k0 ≤ k
    · obtain ⟨a, b, h⟩ := Δ.exists_isSubchainFrom_of_lt hA hB (hk0 k hk)
      exact ⟨(a, b), fun _ => h⟩
    · have hn := (Δ.isFrom k).1
      exact ⟨(⟨0, hn⟩, ⟨0, hn⟩), fun h => absurd h hk⟩
  choose ab hab using hex
  set I : Set ℕ := {k | k0 ≤ k}
  have hI : I.Infinite := Set.infinite_of_forall_exists_gt fun m => ⟨max k0 (m + 1),
    show k0 ≤ max k0 (m + 1) from le_max_left _ _, by omega⟩
  set S : ℕ → Set X := fun k => (Δ.D k).span (ab k).1 (ab k).2
  set L := T13.limSup I S
  have hAS : ∀ k ∈ I, A ∈ S k := fun k hk => ((hab k hk).mem_span).1
  have hBS : ∀ k ∈ I, B ∈ S k := fun k hk => ((hab k hk).mem_span).2
  refine ⟨L, T13.isClosed_limSup I S, ?_, T13.mem_limSup hI hAS, T13.mem_limSup hI hBS, ?_, ?_⟩
  · exact T13.isPreconnected_limSup Δ.ε_tendsto
      (fun k _ => Chain.chainedAt_span _ _ _ (Δ.bdd k) (Δ.diam_le k)) hAS hI
  · intro z hz
    simp only [M, mem_iInter]
    intro i
    refine Δ.closure_union_subset (Nat.lt_succ_self i) ?_
    refine closure_mono ?_ (T13.limSup_subset_closure (i + 1) hz)
    intro y hy
    simp only [mem_iUnion] at hy
    obtain ⟨k, -, hik, hy⟩ := hy
    exact Chain.union_subset_of_refines (Δ.refines_of_le hik) (Chain.span_subset_union _ _ _ hy)
  · intro K hKc hK hKM hAK hBK z hz
    rw [← hKc.closure_eq, Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨N, hN⟩ : ∃ N, ∀ k, N ≤ k → Δ.ε k < δ / 2 :=
      eventually_atTop.mp (Δ.ε_tendsto.eventually (gt_mem_nhds (by linarith)))
    obtain ⟨y, hy, hzy⟩ := Metric.mem_closure_iff.mp (T13.limSup_subset_closure N hz) (δ / 2)
      (by linarith)
    simp only [mem_iUnion] at hy
    obtain ⟨k, hk, hNk, hy⟩ := hy
    obtain ⟨t, hat, htb, hyt⟩ := Chain.mem_span.mp hy
    obtain ⟨x, hxK, hxt⟩ := (hab k hk).inter_link_nonempty hK ((hKM).trans (Δ.M_subset_union k))
      hAK hBK hat htb
    refine ⟨x, hxK, ?_⟩
    have h1 := dist_le_diam_of_mem (Δ.bdd k t) hyt hxt
    have h2 := Δ.diam_le k t
    have h3 := hN k hNk
    have h4 := dist_triangle z y x
    linarith

/-- **Assembly of a description from steps, carrying a property.** The construction of
`exists_description_from'` (Theorem 13), with an arbitrary property `G` of the chains produced at
each step carried to every level of the resulting description. Crookedness of the new levels is
automatic (Theorems 1 and 2): no step needs to be crooked in anything. -/
theorem exists_description_of_steps [CompactSpace X] {R S : X} (G : (N : ℕ) → Chain X N → Prop)
    (hstep : ∀ L, ∃ k, L < k ∧ ∃ N, ∃ F : Chain X N, F.IsFrom R S ∧ F.IsConsolidationOf (Δ.D k) ∧
      (∀ u, ∃ t, closure (F.link u) ⊆ (Δ.D L).link t) ∧
      (∀ u, diam (F.link u) ≤ 1 / ((L : ℝ) + 1)) ∧ G N F) :
    ∃ Δ' : Description X R S, Δ'.M = Δ.M ∧ ∀ i, G (Δ'.n i) (Δ'.D i) := by
  choose K hK N F hF1 hF2 hF3 hF4 hG using hstep
  let lev : ℕ → ℕ := fun i => Nat.rec 0 (fun _ l => K l + 1) i
  have hlev0 : lev 0 = 0 := rfl
  have hlevs : ∀ i, lev (i + 1) = K (lev i) + 1 := fun i => rfl
  have hlevge : ∀ i, i ≤ lev i := by
    intro i
    induction i with
    | zero => simp [hlev0]
    | succ i ih => rw [hlevs]; have := hK (lev i); omega
  have hbdd : ∀ L (u : Fin (N L)), Bornology.IsBounded ((F L).link u) := by
    intro L u
    obtain ⟨t, ht⟩ := hF3 L u
    exact (Δ.bdd L t).subset (subset_closure.trans ht)
  refine ⟨{
    n := fun i => N (lev i)
    D := fun i => F (lev i)
    isFrom := fun i => hF1 (lev i)
    crooked := fun i => ?_
    closure_subset := fun i t => ?_
    ε := fun i => 1 / ((i : ℝ) + 1)
    ε_pos := fun i => by positivity
    ε_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
    bdd := fun i t => hbdd (lev i) t
    diam_le := fun i t => ?_ }, ?_, fun i => hG (lev i)⟩
  · show (F (lev (i + 1))).IsCrookedIn' (F (lev i))
    have href : (F (lev (i + 1))).Refines (Δ.D (K (lev i) + 1)) := by
      intro u
      obtain ⟨t, ht⟩ := hF3 (lev (i + 1)) u
      exact ⟨t, subset_closure.trans ht⟩
    exact Chain.isCrookedIn'_of_refines href
      (Chain.isCrookedIn'_of_isConsolidationOf (hF2 (lev i)) (Δ.crooked (K (lev i))))
  · show ∃ s, closure ((F (lev (i + 1))).link t) ⊆ (F (lev i)).link s
    obtain ⟨s1, hs1⟩ := hF3 (lev (i + 1)) t
    obtain ⟨s2, hs2⟩ := Δ.closure_subset (K (lev i)) s1
    obtain ⟨s3, hs3⟩ := (hF2 (lev i)).1 s2
    exact ⟨s3, hs1.trans (subset_closure.trans (hs2.trans hs3))⟩
  · show diam ((F (lev i)).link t) ≤ 1 / ((i : ℝ) + 1)
    refine (hF4 (lev i) t).trans ?_
    gcongr
    exact_mod_cast hlevge i
  · show (⋂ i, (F (lev i)).union) = Δ.M
    refine Subset.antisymm ?_ ?_
    · intro z hz
      simp only [mem_iInter] at hz
      simp only [M, mem_iInter]
      intro j
      have := hz j
      rw [(hF2 (lev j)).union_eq] at this
      exact Chain.union_subset_of_refines (Δ.refines_of_le
        (le_trans (hlevge j) (hK (lev j)).le)) this
    · intro z hz
      simp only [mem_iInter]
      intro i
      rw [(hF2 (lev i)).union_eq]
      exact Δ.M_subset_union _ hz

/-- **Composants and a third point.** If `R` is in the composant of `P'` and `Q'` is not, then
`Q'` is not in the composant of `R` either (the union of two proper subcontinua through `R` is a
proper subcontinuum, `M` being indecomposable by Theorem 10). -/
theorem not_mem_composant_of_mem_composant [CompactSpace X] {P' Q' R : X}
    (hRc : R ∈ composant Δ.M P') (hQc : Q' ∉ composant Δ.M P') : Q' ∉ composant Δ.M R := by
  intro hQR
  have hind : Fold.Q78.IsIndecomposable Δ.M := theorem10 Δ Δ.M subset_rfl Δ.isContinuum_M
  obtain ⟨K, ⟨hK, hKM, hKne, hPK⟩, hRK⟩ := mem_sUnion.mp hRc
  obtain ⟨K', ⟨hK', hK'M, hK'ne, hRK'⟩, hQK'⟩ := mem_sUnion.mp hQR
  have hU : Fold.Q78.IsContinuum (K ∪ K') :=
    ⟨hK.1.union hK'.1, IsConnected.union ⟨R, hRK, hRK'⟩ hK.2 hK'.2⟩
  have hUne : K ∪ K' ≠ Δ.M := by
    intro h
    rcases hind.2 K K' hK hK' hKM hK'M h with h' | h'
    · exact hKne h'
    · exact hK'ne h'
  exact hQc (mem_sUnion.mpr ⟨K ∪ K', ⟨hU, union_subset hKM hK'M, hUne, Or.inl hPK⟩,
    Or.inr hQK'⟩)

/-- **The spans of the subchains `D_k(A, B)` converge to Bing's limiting set** (from inside). If
`W` lies in every closed connected subset of `M` through `A` and `B` (as the irreducible
subcontinuum does), then for every `η > 0`, from some level on, `W` lies in the open
`η`-neighbourhood of the span of *every* subchain of `D_k` from `A` to `B`. (Containment itself
is not claimed and fails in general.) -/
theorem subset_thickening_span [CompactSpace X] {A B : X} {W : Set X}
    (hWmin : ∀ K : Set X, IsClosed K → IsPreconnected K → K ⊆ Δ.M → A ∈ K → B ∈ K → W ⊆ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ N, ∀ k, N ≤ k → ∀ a b : Fin (Δ.n k), (Δ.D k).IsSubchainFrom a b A B →
      W ⊆ thickening η ((Δ.D k).span a b) := by
  classical
  by_contra hcon
  push_neg at hcon
  choose kf hkf a b hab hW using hcon
  choose z hzW hz using fun N => not_subset.mp (hW N)
  have hcW : IsCompact (closure W) := isClosed_closure.isCompact
  obtain ⟨zs, hzs, φ, hφ, hlim⟩ := hcW.tendsto_subseq (fun N => subset_closure (hzW N))
  set A' : ℕ → Set X := fun j => (Δ.D (kf (φ j))).span (a (φ j)) (b (φ j))
  have hkj : ∀ j, j ≤ kf (φ j) := fun j => (hφ.id_le j).trans (hkf (φ j))
  have hktend : Tendsto (fun j => kf (φ j)) atTop atTop :=
    tendsto_atTop_mono hkj tendsto_id
  have hAA : ∀ j ∈ (univ : Set ℕ), A ∈ A' j := fun j _ => (hab (φ j)).mem_span.1
  have hBA : ∀ j ∈ (univ : Set ℕ), B ∈ A' j := fun j _ => (hab (φ j)).mem_span.2
  set L := T13.limSup univ A'
  have hLp : IsPreconnected L := T13.isPreconnected_limSup (Δ.ε_tendsto.comp hktend)
    (fun j _ => Chain.chainedAt_span _ _ _ (Δ.bdd _) (Δ.diam_le _)) hAA infinite_univ
  have hLM : L ⊆ Δ.M := by
    intro x hx
    simp only [M, mem_iInter]
    intro i
    refine Δ.closure_union_subset (Nat.lt_succ_self i) ?_
    refine closure_mono ?_ (T13.limSup_subset_closure (i + 1) hx)
    intro y hy
    simp only [mem_iUnion] at hy
    obtain ⟨j, -, hij, hy⟩ := hy
    exact Chain.union_subset_of_refines (Δ.refines_of_le (hij.trans (hkj j)))
      (Chain.span_subset_union _ _ _ hy)
  have hWL : W ⊆ L := hWmin L (T13.isClosed_limSup _ _) hLp hLM
    (T13.mem_limSup infinite_univ hAA) (T13.mem_limSup infinite_univ hBA)
  have hzsL : zs ∈ L := (T13.isClosed_limSup _ _).closure_subset_iff.mpr hWL hzs
  obtain ⟨J, hJ⟩ : ∃ J, ∀ j, J ≤ j → dist (z (φ j)) zs < η / 2 := by
    have := (Metric.tendsto_atTop.mp hlim) (η / 2) (by linarith)
    obtain ⟨J, hJ⟩ := this
    exact ⟨J, fun j hj => hJ j hj⟩
  obtain ⟨y, hy, hzy⟩ := Metric.mem_closure_iff.mp (T13.limSup_subset_closure J hzsL) (η / 2)
    (by linarith)
  simp only [mem_iUnion] at hy
  obtain ⟨j, -, hJj, hy⟩ := hy
  apply hz (φ j)
  rw [mem_thickening_iff]
  refine ⟨y, hy, ?_⟩
  have := hJ j hJj
  linarith [dist_triangle (z (φ j)) zs y]

/-- **The other direction:** the span of a subchain of `D_k` from `A` to `B` lies within `ε_k` of
any connected subset of `M` through `A` and `B`. -/
theorem span_subset_cthickening {A B : X} {K : Set X} (hK : IsPreconnected K) (hKM : K ⊆ Δ.M)
    (hAK : A ∈ K) (hBK : B ∈ K) {k : ℕ} {a b : Fin (Δ.n k)}
    (hab : (Δ.D k).IsSubchainFrom a b A B) : (Δ.D k).span a b ⊆ cthickening (Δ.ε k) K := by
  intro y hy
  obtain ⟨t, hat, htb, hyt⟩ := Chain.mem_span.mp hy
  obtain ⟨x, hxK, hxt⟩ := hab.inter_link_nonempty hK (hKM.trans (Δ.M_subset_union k)) hAK hBK
    hat htb
  refine mem_cthickening_of_dist_le y x _ K hxK ?_
  exact (dist_le_diam_of_mem (Δ.bdd k t) hyt hxt).trans (Δ.diam_le k t)

end Description

end HPC
