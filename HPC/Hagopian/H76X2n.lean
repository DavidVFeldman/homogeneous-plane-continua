import HPC.Hagopian.H76Pocket

/-!
# Batch 175, item B: `x₂ₙ = 1`, reduced to one cutting step (supporting file)

Commission 175 §1 P4. `G` is an extension of `E` away from `k⁻¹(0)` with map `d`, irreducible with
respect to separating `p` from `q` in `O` (T13, `hagopian76_T13_uncond`).

* `TailCutKeepsSep` (named `Prop`): cutting `G` at a layer `d⁻¹(t)`, `t < 1`, beyond every interval
  of `I` keeps the separation. This is the plane-topology step of P4 (the tail beyond the last
  crossing block cannot be needed to separate two points of `O`); it is not proved.
* `x2n_eq_one_of_cut`: given `TailCutKeepsSep`, irreducibility forces an interval of `I` to end at
  `1` (`LastIntervalReachesOne`). The cut `d⁻¹[[0, t]]` (with `t` above the finitely many right
  endpoints and above the parameter of `k⁻¹(1)`) is a proper extension of `E` away from `k⁻¹(0)`
  (`piece_map`, Lemma 5) that still separates.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **Named `Prop` for the cutting step of `x₂ₙ = 1`** (commission 175 §1 P4): if `G` separates `p`
from `q` in `O`, then so does every initial segment `d⁻¹[[0, t]]`, `t < 1`, that contains `E` and
lies beyond every interval of `I` (every `[x, y] ∈ I` has `y < t`). Open. -/
def TailCutKeepsSep {M : Set Pt} (E : Set M) {G : Set M} (d : G → unitInterval) (π : Pt → Pt)
    (F : ℝ × ℝ → Pt) (c₁ : ℝ) (D' : Set (ℝ × ℝ)) (O : Set Pt) (p q : Pt) : Prop :=
  SepIn O (toPt G) p q → ∀ t : unitInterval, t < 1 → E ⊆ layerSet d (Icc 0 t) →
    (∀ r ∈ crossingIntervals d π F c₁ D', r.2 < t) → SepIn O (toPt (layerSet d (Icc 0 t))) p q

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **`x₂ₙ = 1` from the cutting step.** For an extension `G ≠ E` of `E` away from `k⁻¹(0)` that
separates `p` from `q` in `O` and contains no other such extension (T13), with `I` finite: if
`TailCutKeepsSep` holds, some interval of `I` ends at `1`. -/
theorem x2n_eq_one_of_cut (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G) (hX0 : layer d 0 = layer k 0) (hne : G ≠ E)
    {π : Pt → Pt} {F : ℝ × ℝ → Pt} {c₁ : ℝ} {D' : Set (ℝ × ℝ)}
    (hfin : (crossingIntervals d π F c₁ D').Finite) {O : Set Pt} {p q : Pt}
    (hsep : SepIn O (toPt G) p q)
    (hirr : ∀ F', IsExtensionAway E (layer k 0) F' → SepIn O (toPt F') p q → F' ⊆ G → F' = G)
    (hcut : TailCutKeepsSep E d π F c₁ D' O p q) : LastIntervalReachesOne d π F c₁ D' := by
  by_contra hno
  have hlt : ∀ r ∈ crossingIntervals d π F c₁ D', r.2 < 1 := fun r hr =>
    lt_of_le_of_ne unitInterval.le_one' fun h => hno ⟨r, hr, h⟩
  obtain ⟨s, -, hs1, -, hsE, -, -⟩ := ext_layers hX hi hE hG hEG hX0 hne
  set A := insert (s, s) (crossingIntervals d π F c₁ D') with hA
  obtain ⟨m, hmA, hmax⟩ := Set.exists_max_image A (fun r => (r.2 : ℝ)) (hfin.insert _)
    ⟨_, mem_insert _ _⟩
  have hm1 : (m.2 : ℝ) < 1 := by
    rcases hmA with rfl | hm
    · exact hs1
    · exact hlt m hm
  set t : unitInterval := ⟨((m.2 : ℝ) + 1) / 2, by constructor <;> linarith [m.2.2.1]⟩ with ht
  have hmt : (m.2 : ℝ) < t := by show (m.2 : ℝ) < ((m.2 : ℝ) + 1) / 2; linarith
  have ht1 : t < 1 := by show ((m.2 : ℝ) + 1) / 2 < 1; linarith
  have ht0 : 0 < t := lt_of_le_of_lt m.2.2.1 hmt
  have hst : s ≤ t := by
    have := hmax (s, s) (mem_insert _ _)
    exact le_of_lt (lt_of_le_of_lt this hmt)
  have hEcut : E ⊆ layerSet d (Icc 0 t) := by
    rw [← hsE]
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, ⟨hy.1, hy.2.trans hst⟩, rfl⟩
  have hIt : ∀ r ∈ crossingIntervals d π F c₁ D', r.2 < t := fun r hr =>
    lt_of_le_of_lt (hmax r (mem_insert_of_mem _ hr)) hmt
  have hsep' := hcut hsep t ht1 hEcut hIt
  haveI : CompactSpace G := isCompact_iff_compactSpace.mp hG.isCompact
  obtain ⟨p', hp', hp'0, -⟩ := piece_map hG (lsc_of_minimalAdmissible hX hi hG) ht0
    (P := layerSet d (Icc 0 t)) rfl
  have hsub : layerSet d (Icc 0 t) ⊆ G := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have heq := hirr _ ⟨hEcut, p', hp', hp'0.trans hX0⟩ hsep' hsub
  obtain ⟨g, hg⟩ := hG.2.1.2.1 1
  have hgm : (g : M) ∈ layerSet d (Icc 0 t) := by rw [heq]; exact g.2
  obtain ⟨g', hg', hgg'⟩ := hgm
  have : g' = g := Subtype.ext hgg'
  subst this
  have h1 : (1 : unitInterval) ≤ t := hg ▸ hg'.2
  exact absurd (lt_of_lt_of_le ht1 h1) (lt_irrefl _)

end HPC.Hagopian
