import HPC.Span.OT82B
import HPC.HO16.Defs
import HPC.HO16.KM77
import HPC.HO16.Thm8
import HPC.HO16.Thm4
import HPC.HO16.Plane
import HPC.Plane.PseudoArc51
import HPC.Plane.EpsMap98
import HPC.Plane.Ingram68Star
import HPC.Plane.Most51

/-!
# Hoehn–Oversteegen Theorem 1, I (batch 193)

The assembly (commission 193, §7). All items of the batch are proved; the statements are the
skeleton's (`doc/batches/skeletons/HO16A.lean`). The pieces are split under `HPC/HO16/`:
`Defs` (§2), `KM77` (§3), `Thm8` (§4), `Thm4` (§5), `Grid` and `Plane` (§6).

Sources: Hoehn–Oversteegen 2016 (`doc/sources/hoehn-oversteegen2016.pdf`), Theorems 1, 4, 8 and
20; Krasinkiewicz–Minc 1977 (`doc/sources/krasinkiewicz-minc1977.pdf`), Lemma 2. Route:
commission 193. The target is `homeomorph_pseudoArc_of_indec_homogeneous`, whose only open input
is the named `Prop` `HOThm20` (H–O Theorem 20, forward direction, for PL graphs).
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

/-! ## §7. The assembly (commission §7) -/

/-- **H–O Theorem 1, "if" direction, for plane continua**, from `HOThm20`: a hereditarily
indecomposable plane continuum with span zero is snake-like. -/
theorem ho16_theorem1_plane (h20 : HOThm20) (M : Set Pt) [CompactSpace M] [ConnectedSpace M]
    (hHI : IsHereditarilyIndecomposable (univ : Set M)) (hspan : HOSpanZero M) :
    IsSnakeLike (univ : Set M) := by
  have hMc : IsCompact M := isCompact_iff_compactSpace.2 ‹_›
  have hMconn : IsConnected M := isConnected_iff_connectedSpace.2 ‹_›
  refine isSnakeLike_univ_of_epsMap fun ε hε => ?_
  obtain ⟨δ₀, hδ₀, h4⟩ := ho16_theorem4 hMc hspan (ε := ε / 6) (by linarith)
  set δ := min δ₀ (ε / 6) with hδdef
  have hδ : 0 < δ := lt_min hδ₀ (by linarith)
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδε : δ ≤ ε / 6 := min_le_right _ _
  obtain ⟨G, hG, hGM, f, hfc, hf⟩ :=
    exists_plGraph_approx hMc (interior_eq_empty_of_hi hHI) hδ
  obtain ⟨γ, hγc, hγM, hMγ⟩ := exists_path_approx hMc hMconn hδ
  have hsep := h4 G hG.isCompact (hGM.trans (thickening_mono hδδ₀ _)) γ hγc
    (hγM.trans (thickening_mono hδδ₀ _)) (hMγ.trans (thickening_mono hδδ₀ _))
  set U : Set (Pt × ℝ) := {p | p.2 ∈ Ioo (0 : ℝ) 1 ∧ dist p.1 (γ p.2) < ε / 6} with hUdef
  have hUo : IsOpen U :=
    (isOpen_Ioo.preimage continuous_snd).inter
      (isOpen_lt (continuous_fst.dist (hγc.comp continuous_snd)) continuous_const)
  obtain ⟨h, hhc, hhU, hhf⟩ := h20 M hHI Pt G hG (fun x => f x)
    (hfc.comp_continuous continuous_subtype_val fun x => x.2) (fun x => (hf x x.2).1)
    {p : Pt × ℝ | p.1 ∈ G ∧ p.2 ∈ Ioo (0 : ℝ) 1 ∧ dist p.1 (γ p.2) < ε / 6}
    (fun p hp => ⟨hp.1, hp.2.1⟩) hsep U hUo (fun p hp => ⟨hp.2.1, hp.2.2⟩) (ε / 6)
    (by linarith)
  refine ⟨fun x => (h x).2, continuous_snd.comp hhc, fun x x' hxx' => ?_⟩
  have key : ∀ y : M, dist (y : Pt) (γ (h y).2) < ε / 2 := by
    intro y
    have h1 : dist (y : Pt) (f y) < δ := by rw [dist_comm]; exact (hf y y.2).2
    have h2 := hhf y
    have h3 := (hhU y).1.2
    calc dist (y : Pt) (γ (h y).2)
        ≤ dist (y : Pt) (f y) + dist (f y) (h y).1 + dist (h y).1 (γ (h y).2) :=
          dist_triangle4 _ _ _ _
      _ < δ + ε / 6 + ε / 6 := by gcongr
      _ ≤ ε / 2 := by linarith
  have k1 := key x
  have k2 := key x'
  simp only at hxx'
  rw [hxx'] at k1
  rw [Subtype.dist_eq]
  calc dist (x : Pt) (x' : Pt) ≤ dist (x : Pt) (γ (h x').2) + dist (x' : Pt) (γ (h x').2) :=
        dist_triangle_right _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add k1 k2
    _ = ε := by ring

/-- H–O p. 180: "every indecomposable non-degenerate homogeneous plane continuum is a
pseudo-arc", from Theorems B and C and `HOThm20`. -/
theorem isPseudoArc_of_indec_homogeneous (h20 : HOThm20) (M : Set Pt) [CompactSpace M]
    [ConnectedSpace M] (hhom : IsHomogeneous M) (hind : ¬ IsDecomposableSpace M)
    (hnt : (univ : Set M).Nontrivial) : IsPseudoArc (univ : Set M) := by
  have hHI := HPC.Hagopian.hagopian76_theorem1 M hhom hind
  exact ⟨ho16_theorem1_plane h20 M hHI (theoremC M hhom hind), hHI, hnt⟩

/-- The same, as a homeomorphism onto a plane pseudo-arc (`pseudoArc_unique`). -/
theorem homeomorph_pseudoArc_of_indec_homogeneous (h20 : HOThm20) (M : Set Pt) [CompactSpace M]
    [ConnectedSpace M] (hhom : IsHomogeneous M) (hind : ¬ IsDecomposableSpace M)
    (hnt : (univ : Set M).Nontrivial) :
    ∃ M₀ : Set Pt, IsPseudoArc M₀ ∧ Nonempty (M ≃ₜ M₀) := by
  obtain ⟨M₀, hM₀, huniq⟩ := pseudoArc_unique
  obtain ⟨e⟩ := huniq M univ (isPseudoArc_of_indec_homogeneous h20 M hhom hind hnt)
  exact ⟨M₀, hM₀, ⟨(Homeomorph.Set.univ M).symm.trans e⟩⟩

end HPC.HO16
