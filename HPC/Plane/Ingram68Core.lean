import HPC.Plane.Fugate66Cor1Proof
import HPC.Plane.Fugate66Lemma1
import HPC.Plane.Arcs48

/-!
# Batch 132, Part II (1): Ingram's Lemmas 1–2 and the property (∗∗), without Sorgenfrey

Source: W. T. Ingram, *Decomposable circle-like continua*, Fund. Math. 63 (1968), 193–198
(`doc/sources/ingram1968.pdf`), Lemmas 1 and 2, and COMMISSION-batch132 §§2–3.

Every appeal Ingram makes to Sorgenfrey's Theorem 1.8 in Lemmas 1–2 is replaced by one lemma,
`isTriod_of_core`: three continua that meet a continuum `N`, pairwise meet only inside `N`, and do
not lie in `N`, form a triod with core `N`. Ingram's "components of `B − (B ∩ D)`" become arms from
boundary bumping (`exists_arm`).

* `ingram_lemma1` — Lemma 1, used form (`not_isAtriodic_of_three`: three pieces give a triod with
  core `A`).
* `eq_of_subset_of_split`, `ingram_lemma2` — Lemma 2 (irreducibility needs no extra hypothesis;
  terminality is proved for a hereditarily unicoherent `A`).
* `ingramStarWeak_holds` — the property (∗∗) used in Part I.
-/

namespace HPC.Plane

open Set Metric

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ### A triod with a given core

The one triod-producing device of the direct route. If three continua `X₁`, `X₂`, `X₃` each meet a
continuum `N`, pairwise meet only inside `N`, and none lies in `N`, then `N ∪ X₁ ∪ X₂ ∪ X₃` is a
triod with core `N`: the three sets `Xᵢ ∖ N` are mutually separated, since `closure (Xᵢ ∖ N) ⊆ Xᵢ`.
Every use of Sorgenfrey's theorem in Ingram's Lemmas 1–2 and in the proof of (∗∗) below is
replaced by this lemma. -/

omit [CompactSpace S] in
/-- **A triod with a given core.** -/
theorem isTriod_of_core {N X₁ X₂ X₃ : Set S} (hN : Fold.Q78.IsContinuum N)
    (h₁ : Fold.Q78.IsContinuum X₁) (h₂ : Fold.Q78.IsContinuum X₂) (h₃ : Fold.Q78.IsContinuum X₃)
    (m₁ : (X₁ ∩ N).Nonempty) (m₂ : (X₂ ∩ N).Nonempty) (m₃ : (X₃ ∩ N).Nonempty)
    (o₁₂ : X₁ ∩ X₂ ⊆ N) (o₁₃ : X₁ ∩ X₃ ⊆ N) (o₂₃ : X₂ ∩ X₃ ⊆ N)
    (n₁ : ¬ X₁ ⊆ N) (n₂ : ¬ X₂ ⊆ N) (n₃ : ¬ X₃ ⊆ N) : IsTriod (N ∪ X₁ ∪ X₂ ∪ X₃) := by
  have c₁ : Fold.Q78.IsContinuum (N ∪ X₁) := by
    obtain ⟨x, hx1, hxN⟩ := m₁
    exact isContinuum_union hN h₁ ⟨x, hxN, hx1⟩
  have c₂ : Fold.Q78.IsContinuum (N ∪ X₁ ∪ X₂) := by
    obtain ⟨x, hx2, hxN⟩ := m₂
    exact isContinuum_union c₁ h₂ ⟨x, Or.inl hxN, hx2⟩
  have c₃ : Fold.Q78.IsContinuum (N ∪ X₁ ∪ X₂ ∪ X₃) := by
    obtain ⟨x, hx3, hxN⟩ := m₃
    exact isContinuum_union c₂ h₃ ⟨x, Or.inl (Or.inl hxN), hx3⟩
  have cl₁ : closure (X₁ \ N) ⊆ X₁ := closure_minimal diff_subset h₁.1.isClosed
  have cl₂ : closure (X₂ \ N) ⊆ X₂ := closure_minimal diff_subset h₂.1.isClosed
  have cl₃ : closure (X₃ \ N) ⊆ X₃ := closure_minimal diff_subset h₃.1.isClosed
  refine ⟨c₃, N, hN, subset_union_left.trans (subset_union_left.trans subset_union_left),
    X₁ \ N, X₂ \ N, X₃ \ N, diff_nonempty.mpr n₁, diff_nonempty.mpr n₂, diff_nonempty.mpr n₃,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x; simp only [mem_diff, mem_union]; tauto
  · exact disjoint_left.mpr fun x hx hx' => hx'.2 (o₁₂ ⟨cl₁ hx, hx'.1⟩)
  · exact disjoint_left.mpr fun x hx hx' => hx.2 (o₁₂ ⟨hx.1, cl₂ hx'⟩)
  · exact disjoint_left.mpr fun x hx hx' => hx'.2 (o₁₃ ⟨cl₁ hx, hx'.1⟩)
  · exact disjoint_left.mpr fun x hx hx' => hx.2 (o₁₃ ⟨hx.1, cl₃ hx'⟩)
  · exact disjoint_left.mpr fun x hx hx' => hx'.2 (o₂₃ ⟨cl₂ hx, hx'.1⟩)
  · exact disjoint_left.mpr fun x hx hx' => hx.2 (o₂₃ ⟨hx.1, cl₃ hx'⟩)

omit [CompactSpace S] in
/-- **The core lemma inside an atriodic set**: the configuration of `isTriod_of_core` cannot
occur inside an atriodic set. -/
theorem not_core_of_isAtriodic {Z N X₁ X₂ X₃ : Set S} (hZ : IsAtriodic Z)
    (hN : Fold.Q78.IsContinuum N)
    (h₁ : Fold.Q78.IsContinuum X₁) (h₂ : Fold.Q78.IsContinuum X₂) (h₃ : Fold.Q78.IsContinuum X₃)
    (hNZ : N ⊆ Z) (s₁ : X₁ ⊆ Z) (s₂ : X₂ ⊆ Z) (s₃ : X₃ ⊆ Z)
    (m₁ : (X₁ ∩ N).Nonempty) (m₂ : (X₂ ∩ N).Nonempty) (m₃ : (X₃ ∩ N).Nonempty)
    (o₁₂ : X₁ ∩ X₂ ⊆ N) (o₁₃ : X₁ ∩ X₃ ⊆ N) (o₂₃ : X₂ ∩ X₃ ⊆ N)
    (n₁ : ¬ X₁ ⊆ N) (n₂ : ¬ X₂ ⊆ N) (n₃ : ¬ X₃ ⊆ N) : False :=
  hZ _ (union_subset (union_subset (union_subset hNZ s₁) s₂) s₃)
    (isTriod_of_core hN h₁ h₂ h₃ m₁ m₂ m₃ o₁₂ o₁₃ o₂₃ n₁ n₂ n₃)

omit [CompactSpace S] in
/-- Two disjoint closed sets: an open neighbourhood of the first whose closure misses the
second. -/
theorem exists_open_closure_disjoint {E F : Set S} (hE : IsClosed E) (hF : IsClosed F)
    (h : Disjoint E F) : ∃ D : Set S, IsOpen D ∧ E ⊆ D ∧ Disjoint (closure D) F := by
  obtain ⟨U, V, hU, hV, hEU, hFV, hUV⟩ := normal_separation hE hF h
  exact ⟨U, hU, hEU, (hUV.closure_left hV).mono_right hFV⟩

/-- **An arm** (boundary bumping, Nadler 5.4). Let `A` be a continuum, `E`, `F` disjoint closed
sets with `Y ∩ A ⊆ E ∪ F`, `f ∈ A ∩ F`, and `A` meeting `E`. Then a subcontinuum `C ⊆ A` through `f`
misses `E` and is not contained in `Y`. (Ingram's "component of `B − (B ∩ D)` containing `H`,
which meets `B − (A ∩ B)`".) -/
theorem exists_arm {A Y E F : Set S} (hA : Fold.Q78.IsContinuum A) (hE : IsClosed E)
    (hF : IsClosed F) (hEF : Disjoint E F) (hYA : Y ∩ A ⊆ E ∪ F) {f : S} (hfA : f ∈ A)
    (hfF : f ∈ F) (hAE : (A ∩ E).Nonempty) :
    ∃ C : Set S, Fold.Q78.IsContinuum C ∧ C ⊆ A ∧ f ∈ C ∧ Disjoint C E ∧ ¬ C ⊆ Y := by
  obtain ⟨D, hD, hED, hDF⟩ := exists_open_closure_disjoint hE hF hEF
  have hfD : f ∉ D := fun h => disjoint_left.mp hDF (subset_closure h) hfF
  have hne : A \ D ≠ A := by
    obtain ⟨a, haA, haE⟩ := hAE
    intro h
    have : a ∈ A \ D := h.symm ▸ haA
    exact this.2 (hED haE)
  obtain ⟨C, hC, hCF, hfC, c, hcC, hccl⟩ :=
    exists_continuum_bump_closed hA (hA.1.isClosed.sdiff hD) diff_subset hne ⟨hfA, hfD⟩
  have hccl' : c ∈ closure D :=
    closure_mono (fun x hx => by_contra fun h => hx.2 ⟨hx.1, h⟩) hccl
  refine ⟨C, hC, hCF.trans diff_subset, hfC,
    disjoint_left.mpr fun x hx hxE => (hCF hx).2 (hED hxE), fun hCY => ?_⟩
  rcases hYA ⟨hCY hcC, (hCF hcC).1⟩ with h | h
  · exact (hCF hcC).2 (hED h)
  · exact disjoint_left.mp hDF hccl' h

/-- **Ingram, Lemma 1, the three-piece form.** If `Y ∩ A` is the union of three disjoint nonempty
closed sets, then `Y ∪ A` contains a triod (here: is not atriodic). Ingram's three arms
`C₁, C₂, C₃ ⊆ A`, built one after the other, are disjoint, and the core is `Y`. -/
theorem not_isAtriodic_of_three {Y A F₁ F₂ F₃ : Set S} (hY : Fold.Q78.IsContinuum Y)
    (hA : Fold.Q78.IsContinuum A) (c₁ : IsClosed F₁) (c₂ : IsClosed F₂) (c₃ : IsClosed F₃)
    (e₁ : F₁.Nonempty) (e₂ : F₂.Nonempty) (e₃ : F₃.Nonempty)
    (d₁₂ : Disjoint F₁ F₂) (d₁₃ : Disjoint F₁ F₃) (d₂₃ : Disjoint F₂ F₃)
    (hYA : Y ∩ A = F₁ ∪ F₂ ∪ F₃) : ¬ IsAtriodic (Y ∪ A) := by
  intro hat
  obtain ⟨f₁, hf₁⟩ := e₁
  obtain ⟨f₂, hf₂⟩ := e₂
  obtain ⟨f₃, hf₃⟩ := e₃
  have hFA : ∀ {x}, x ∈ F₁ ∪ F₂ ∪ F₃ → x ∈ Y ∩ A := fun hx => hYA ▸ hx
  have a₁ : f₁ ∈ Y ∩ A := hFA (Or.inl (Or.inl hf₁))
  have a₂ : f₂ ∈ Y ∩ A := hFA (Or.inl (Or.inr hf₂))
  have a₃ : f₃ ∈ Y ∩ A := hFA (Or.inr hf₃)
  -- the first arm
  obtain ⟨C₁, hC₁, hC₁A, hf₁C, hC₁E, hC₁Y⟩ := exists_arm (Y := Y) hA (c₂.union c₃) c₁
    (disjoint_union_left.mpr ⟨d₁₂.symm, d₁₃.symm⟩)
    (fun x hx => by rw [hYA] at hx; rcases hx with (h | h) | h <;> simp [h]) a₁.2 hf₁
    ⟨f₂, a₂.2, Or.inl hf₂⟩
  -- the second arm
  have hC₁F₂ : Disjoint C₁ F₂ := hC₁E.mono_right subset_union_left
  have hC₁F₃ : Disjoint C₁ F₃ := hC₁E.mono_right subset_union_right
  obtain ⟨C₂, hC₂, hC₂A, hf₂C, hC₂E, hC₂Y⟩ := exists_arm (Y := Y)
    (E := C₁ ∪ F₁ ∪ F₃) hA ((hC₁.1.isClosed.union c₁).union c₃) c₂
    (disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hC₁F₂, d₁₂⟩, d₂₃.symm⟩)
    (fun x hx => by rw [hYA] at hx; rcases hx with (h | h) | h <;> simp [h]) a₂.2 hf₂
    ⟨f₁, a₁.2, Or.inl (Or.inr hf₁)⟩
  -- the third arm
  have hC₂F₃ : Disjoint C₂ F₃ := hC₂E.mono_right subset_union_right
  obtain ⟨C₃, hC₃, hC₃A, hf₃C, hC₃E, hC₃Y⟩ := exists_arm (Y := Y)
    (E := C₁ ∪ C₂ ∪ F₁ ∪ F₂) hA
    (((hC₁.1.isClosed.union hC₂.1.isClosed).union c₁).union c₂) c₃
    (disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨disjoint_union_left.mpr
      ⟨hC₁F₃, hC₂F₃⟩, d₁₃⟩, d₂₃⟩)
    (fun x hx => by rw [hYA] at hx; rcases hx with (h | h) | h <;> simp [h]) a₃.2 hf₃
    ⟨f₁, a₁.2, Or.inl (Or.inr hf₁)⟩
  have d12 : Disjoint C₁ C₂ :=
    (hC₂E.mono_right (subset_union_left.trans subset_union_left)).symm
  have d13 : Disjoint C₁ C₃ :=
    (hC₃E.mono_right (subset_union_left.trans (subset_union_left.trans subset_union_left))).symm
  have d23 : Disjoint C₂ C₃ :=
    (hC₃E.mono_right (subset_union_right.trans (subset_union_left.trans subset_union_left))).symm
  refine not_core_of_isAtriodic hat hY hC₁ hC₂ hC₃ subset_union_left
    (hC₁A.trans subset_union_right) (hC₂A.trans subset_union_right)
    (hC₃A.trans subset_union_right) ⟨f₁, hf₁C, a₁.1⟩ ⟨f₂, hf₂C, a₂.1⟩ ⟨f₃, hf₃C, a₃.1⟩
    ?_ ?_ ?_ hC₁Y hC₂Y hC₃Y
  · rw [d12.inter_eq]; exact empty_subset _
  · rw [d13.inter_eq]; exact empty_subset _
  · rw [d23.inter_eq]; exact empty_subset _

/-! ### Ingram's Lemma 1 -/

/-- **Ingram, Lemma 1.** If `A ∩ B` has at least three components, then `A ∪ B` contains a triod.
Used form: in an atriodic `A ∪ B`, a nonempty disconnected `A ∩ B` is the union of two disjoint
continua. (Proof: `not_isAtriodic_of_three`; Ingram's appeal to Sorgenfrey is replaced by
`isTriod_of_core` with core `A`.) -/
theorem ingram_lemma1 {A B : Set S} (hA : Fold.Q78.IsContinuum A) (hB : Fold.Q78.IsContinuum B)
    (hat : IsAtriodic (A ∪ B)) (hne : (A ∩ B).Nonempty) (hnc : ¬ IsConnected (A ∩ B)) :
    ∃ H K : Set S, Fold.Q78.IsContinuum H ∧ Fold.Q78.IsContinuum K ∧ Disjoint H K ∧
      A ∩ B = H ∪ K := by
  obtain ⟨Z₁, Z₂, c₁, c₂, e₁, e₂, d, hZ⟩ :=
    exists_split_of_not_isConnected (hA.1.isClosed.inter hB.1.isClosed) hne hnc
  by_cases h₁ : IsConnected Z₁
  · by_cases h₂ : IsConnected Z₂
    · exact ⟨Z₁, Z₂, ⟨c₁.isCompact, h₁⟩, ⟨c₂.isCompact, h₂⟩, d, hZ⟩
    · exfalso
      obtain ⟨G₁, G₂, g₁, g₂, f₁, f₂, dG, hG⟩ := exists_split_of_not_isConnected c₂ e₂ h₂
      refine not_isAtriodic_of_three hA hB c₁ g₁ g₂ e₁ f₁ f₂
        (d.mono_right (hG ▸ subset_union_left)) (d.mono_right (hG ▸ subset_union_right)) dG ?_ hat
      rw [hZ, hG, union_assoc]
  · exfalso
    obtain ⟨G₁, G₂, g₁, g₂, f₁, f₂, dG, hG⟩ := exists_split_of_not_isConnected c₁ e₁ h₁
    refine not_isAtriodic_of_three hA hB g₁ g₂ c₂ f₁ f₂ e₂ dG
      (d.mono_left (hG ▸ subset_union_left)) (d.mono_left (hG ▸ subset_union_right)) ?_ hat
    rw [hZ, hG]

/-! ### Ingram's Lemma 2 -/

/-- **Ingram, Lemma 2, irreducibility, in the form used.** Suppose `Y ∩ A` is the union of two
disjoint nonempty closed sets `H`, `K`, and `Y ∪ A` is atriodic. Then every subcontinuum of `Y`
containing `H ∪ K` is `Y`. (`H`, `K` need not be connected. Ingram's two arms `C`, `E ⊆ A` and the
core `Y₀`.) -/
theorem eq_of_subset_of_split {Y A H K Y₀ : Set S} (hY : Fold.Q78.IsContinuum Y)
    (hA : Fold.Q78.IsContinuum A) (hH : IsClosed H) (hK : IsClosed K) (hHne : H.Nonempty)
    (hKne : K.Nonempty) (hHK : Disjoint H K) (hYA : Y ∩ A = H ∪ K) (hat : IsAtriodic (Y ∪ A))
    (hY₀ : Fold.Q78.IsContinuum Y₀) (hY₀Y : Y₀ ⊆ Y) (hHKY₀ : H ∪ K ⊆ Y₀) : Y₀ = Y := by
  by_contra hne
  have hYY₀ : ¬ Y ⊆ Y₀ := fun h => hne (Subset.antisymm hY₀Y h)
  obtain ⟨h, hh⟩ := hHne
  obtain ⟨k, hk⟩ := hKne
  have hhYA : h ∈ Y ∩ A := hYA ▸ Or.inl hh
  have hkYA : k ∈ Y ∩ A := hYA ▸ Or.inr hk
  obtain ⟨C, hC, hCA, hhC, hCK, hCY⟩ := exists_arm (Y := Y) hA hK hH hHK.symm
    (fun x hx => by rw [hYA] at hx; rcases hx with h | h <;> simp [h]) hhYA.2 hh ⟨k, hkYA.2, hk⟩
  obtain ⟨E, hE, hEA, hkE, hECH, hEY⟩ := exists_arm (Y := Y) (E := C ∪ H) hA
    (hC.1.isClosed.union hH) hK (disjoint_union_left.mpr ⟨hCK, hHK⟩)
    (fun x hx => by rw [hYA] at hx; rcases hx with h | h <;> simp [h]) hkYA.2 hk
    ⟨h, hhYA.2, Or.inr hh⟩
  have oY : ∀ {D : Set S}, D ⊆ A → Y ∩ D ⊆ Y₀ := fun hD x hx =>
    hHKY₀ (hYA ▸ (⟨hx.1, hD hx.2⟩ : x ∈ Y ∩ A))
  refine not_core_of_isAtriodic hat hY₀ hY hC hE (hY₀Y.trans subset_union_left) subset_union_left
    (hCA.trans subset_union_right) (hEA.trans subset_union_right)
    ⟨h, hhYA.1, hHKY₀ (Or.inl hh)⟩ ⟨h, hhC, hHKY₀ (Or.inl hh)⟩ ⟨k, hkE, hHKY₀ (Or.inr hk)⟩
    (oY hCA) (oY hEA) ?_ hYY₀ (fun h' => hCY (h'.trans hY₀Y)) (fun h' => hEY (h'.trans hY₀Y))
  intro x hx
  exact absurd (Or.inl hx.1) (disjoint_left.mp hECH hx.2)

/-- **Ingram, Lemma 2.** Suppose `A ∩ B` is the union of two disjoint continua `H`, `K`, and
`A ∪ B` is atriodic. Then `H` and `K` are terminal subcontinua of `A`, and `A` is irreducible
about `H ∪ K`.

(Shape change: the hypothesis `hAhu : IsHereditarilyUnicoherent A` is added; it is used only for
terminality, where Ingram's appeal to Sorgenfrey is replaced by `isTriod_of_core` with core
`(H ∪ L₁) ∩ (H ∪ L₂)`, a continuum when `A` is hereditarily unicoherent. In the application `A`
is snake-like. Irreducibility is `eq_of_subset_of_split` and needs no extra hypothesis.) -/
theorem ingram_lemma2 {A B H K : Set S} (hA : Fold.Q78.IsContinuum A)
    (hB : Fold.Q78.IsContinuum B) (hH : Fold.Q78.IsContinuum H) (hK : Fold.Q78.IsContinuum K)
    (hHK : Disjoint H K) (hAB : A ∩ B = H ∪ K) (hat : IsAtriodic (A ∪ B))
    (hAhu : IsHereditarilyUnicoherent A) :
    IsTerminalSub A H ∧ IsTerminalSub A K ∧ IrreducibleAbout A (H ∪ K) := by
  have hHA : H ⊆ A := fun x hx => (hAB ▸ (Or.inl hx : x ∈ H ∪ K) : x ∈ A ∩ B).1
  have hKA : K ⊆ A := fun x hx => (hAB ▸ (Or.inr hx : x ∈ H ∪ K) : x ∈ A ∩ B).1
  -- terminality of the first piece, for either order
  have term : ∀ {H K : Set S}, Fold.Q78.IsContinuum H → Fold.Q78.IsContinuum K → Disjoint H K →
      A ∩ B = H ∪ K → IsTerminalSub A H := by
    intro H K hH hK hHK hAB
    have hHA : H ⊆ A := fun x hx => (hAB ▸ (Or.inl hx : x ∈ H ∪ K) : x ∈ A ∩ B).1
    refine ⟨hH, hHA, fun L₁ L₂ hL₁ hL₂ hL₁A hL₂A hL₁H hL₂H => ?_⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨n₂, n₃⟩ := hcon
    obtain ⟨h, hh⟩ := hH.2.nonempty
    obtain ⟨k, hk⟩ := hK.2.nonempty
    have hhAB : h ∈ A ∩ B := hAB ▸ Or.inl hh
    have hkAB : k ∈ A ∩ B := hAB ▸ Or.inr hk
    obtain ⟨C, hC, hCB, hhC, hCK, hCA⟩ := exists_arm (Y := A) hB hK.1.isClosed hH.1.isClosed
      hHK.symm (fun x hx => by rw [hAB] at hx; rcases hx with h | h <;> simp [h]) hhAB.2 hh
      ⟨k, hkAB.2, hk⟩
    have c₁ : Fold.Q78.IsContinuum (H ∪ L₁) := by
      obtain ⟨x, hx1, hxH⟩ := hL₁H; exact isContinuum_union hH hL₁ ⟨x, hxH, hx1⟩
    have c₂ : Fold.Q78.IsContinuum (H ∪ L₂) := by
      obtain ⟨x, hx1, hxH⟩ := hL₂H; exact isContinuum_union hH hL₂ ⟨x, hxH, hx1⟩
    have hN := isContinuum_inter_of_hu hAhu c₁ c₂ (union_subset hHA hL₁A) (union_subset hHA hL₂A)
      ⟨h, Or.inl hh, Or.inl hh⟩
    have oC : ∀ {D : Set S}, D ⊆ A → H ⊆ D → C ∩ D ⊆ (H ∪ L₁) ∩ (H ∪ L₂) := by
      intro D hD hHD x hx
      have : x ∈ H ∪ K := hAB ▸ (⟨hD hx.2, hCB hx.1⟩ : x ∈ A ∩ B)
      rcases this with h' | h'
      · exact ⟨Or.inl h', Or.inl h'⟩
      · exact absurd h' (disjoint_left.mp hCK hx.1)
    refine not_core_of_isAtriodic hat hN hC c₁ c₂
      (inter_subset_left.trans ((union_subset hHA hL₁A).trans subset_union_left))
      (hCB.trans subset_union_right) ((union_subset hHA hL₁A).trans subset_union_left)
      ((union_subset hHA hL₂A).trans subset_union_left)
      ⟨h, hhC, Or.inl hh, Or.inl hh⟩ ⟨h, Or.inl hh, Or.inl hh, Or.inl hh⟩
      ⟨h, Or.inl hh, Or.inl hh, Or.inl hh⟩
      (oC (union_subset hHA hL₁A) subset_union_left) (oC (union_subset hHA hL₂A) subset_union_left)
      Subset.rfl (fun h' => hCA (h'.trans (inter_subset_left.trans (union_subset hHA hL₁A))))
      ?_ ?_
    · intro h'
      obtain ⟨x, hx1, hx2⟩ := not_subset.mp n₂
      exact hx2 (by
        rcases (h' (Or.inr hx1)).2 with h'' | h''
        · exact Or.inl h''
        · exact Or.inr h'')
    · intro h'
      obtain ⟨x, hx1, hx2⟩ := not_subset.mp n₃
      exact hx2 (by
        rcases (h' (Or.inr hx1)).1 with h'' | h''
        · exact Or.inr h''
        · exact Or.inl h'')
  refine ⟨term hH hK hHK hAB, term hK hH hHK.symm (by rw [hAB, union_comm]), hA,
    union_subset hHA hKA, fun A₀ hA₀ hA₀A hHKA₀ => ?_⟩
  exact eq_of_subset_of_split hA hB hH.1.isClosed hK.1.isClosed hH.2.nonempty hK.2.nonempty hHK
    hAB hat hA₀ hA₀A hHKA₀

/-! ### The property (∗∗) -/

/-- **(∗∗) holds** (the direct route of COMMISSION-batch132 §2, without circle-likeness). Suppose
`Y`, `A` are snake-like and meet, `Y ∪ A` is atriodic, and `Y ∩ A` is not connected. If `P ⊆ Y`
and `Q ⊆ A` are continua meeting in a nonempty disconnected set, then `P ∪ Q = Y ∪ A`.

Proof. By Lemma 1, `Y ∩ A = H ⊔ K` with `H`, `K` continua. As `Y` and `A` are hereditarily
unicoherent, `P ∩ Q ∩ H` and `P ∩ Q ∩ K` are each connected or empty, so both are nonempty;
pick `h`, `k`. By Lemma 2 (irreducibility), `P ∪ H ∪ K = Y` and `Q ∪ H ∪ K = A`. It remains to
see `H ⊆ P ∪ Q` (and likewise `K`). If `z ∈ H ∖ (P ∪ Q)`, take arms `P' ⊆ P`, `Q' ⊆ Q` through
`h`, missing `K`, not inside `H`. Then `H`, `P'`, `Q'` with core `(H ∩ P') ∪ (H ∩ Q')` (a continuum,
by hereditary unicoherence of `Y` and of `A`) form a triod in `Y ∪ A`. -/
theorem ingramStarWeak_holds : IngramStarWeak S := by
  intro Y A hY hA hne hat hnc P Q hP hQ hPY hQA hPQne hPQnc
  obtain ⟨H, K, hH, hK, hHK, hYA⟩ := ingram_lemma1 hY.1 hA.1 hat hne hnc
  have hYhu := isHereditarilyUnicoherent_of_isSnakeLike hY
  have hAhu := isHereditarilyUnicoherent_of_isSnakeLike hA
  have hHY : H ⊆ Y := fun x hx => (hYA ▸ (Or.inl hx : x ∈ H ∪ K) : x ∈ Y ∩ A).1
  have hHA : H ⊆ A := fun x hx => (hYA ▸ (Or.inl hx : x ∈ H ∪ K) : x ∈ Y ∩ A).2
  have hKY : K ⊆ Y := fun x hx => (hYA ▸ (Or.inr hx : x ∈ H ∪ K) : x ∈ Y ∩ A).1
  have hKA : K ⊆ A := fun x hx => (hYA ▸ (Or.inr hx : x ∈ H ∪ K) : x ∈ Y ∩ A).2
  -- `P ∩ Q ∩ G` is connected when nonempty, for `G = H, K`
  have conn : ∀ {G : Set S}, Fold.Q78.IsContinuum G → G ⊆ Y → G ⊆ A →
      (P ∩ Q ∩ G).Nonempty → IsConnected (P ∩ Q ∩ G) := by
    intro G hG hGY hGA ⟨x, ⟨hxP, hxQ⟩, hxG⟩
    have hPG := isContinuum_inter_of_hu hYhu hP hG hPY hGY ⟨x, hxP, hxG⟩
    have hQG := isContinuum_inter_of_hu hAhu hQ hG hQA hGA ⟨x, hxQ, hxG⟩
    have := isContinuum_inter_of_hu hYhu hPG hQG (inter_subset_right.trans hGY)
      (inter_subset_right.trans hGY) ⟨x, ⟨hxP, hxG⟩, hxQ, hxG⟩
    convert this.2 using 1
    ext y; simp only [mem_inter_iff]; tauto
  have hsplit : P ∩ Q = (P ∩ Q ∩ H) ∪ (P ∩ Q ∩ K) := by
    rw [← inter_union_distrib_left, ← hYA]
    exact (inter_eq_left.mpr fun x hx => (⟨hPY hx.1, hQA hx.2⟩ : x ∈ Y ∩ A)).symm
  have hHne : (P ∩ Q ∩ H).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [hsplit, h, empty_union] at hPQnc hPQne
    exact hPQnc (conn hK hKY hKA hPQne)
  have hKne : (P ∩ Q ∩ K).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [hsplit, h, union_empty] at hPQnc hPQne
    exact hPQnc (conn hH hHY hHA hPQne)
  obtain ⟨h, ⟨hhP, hhQ⟩, hhH⟩ := hHne
  obtain ⟨k, ⟨hkP, hkQ⟩, hkK⟩ := hKne
  -- irreducibility: `Y = P ∪ H ∪ K`, `A = Q ∪ H ∪ K`
  have eY : P ∪ H ∪ K = Y :=
    eq_of_subset_of_split hY.1 hA.1 hH.1.isClosed hK.1.isClosed ⟨h, hhH⟩ ⟨k, hkK⟩ hHK hYA hat
      (isContinuum_union (isContinuum_union hP hH ⟨h, hhP, hhH⟩) hK ⟨k, Or.inl hkP, hkK⟩)
      (union_subset (union_subset hPY hHY) hKY)
      (union_subset (subset_union_right.trans subset_union_left) subset_union_right)
  have eA : Q ∪ H ∪ K = A :=
    eq_of_subset_of_split hA.1 hY.1 hH.1.isClosed hK.1.isClosed ⟨h, hhH⟩ ⟨k, hkK⟩ hHK
      (by rw [inter_comm, hYA]) (by rw [union_comm]; exact hat)
      (isContinuum_union (isContinuum_union hQ hH ⟨h, hhQ, hhH⟩) hK ⟨k, Or.inl hkQ, hkK⟩)
      (union_subset (union_subset hQA hHA) hKA)
      (union_subset (subset_union_right.trans subset_union_left) subset_union_right)
  -- the key step: each piece lies in `P ∪ Q`
  have key : ∀ {H K : Set S} {h k : S}, Fold.Q78.IsContinuum H → Fold.Q78.IsContinuum K →
      Disjoint H K → Y ∩ A = H ∪ K → h ∈ P → h ∈ Q → h ∈ H → k ∈ P → k ∈ Q → k ∈ K →
      H ⊆ P ∪ Q := by
    intro H K h k hH hK hHK hYA hhP hhQ hhH hkP hkQ hkK z hzH
    by_contra hz
    have hHY : H ⊆ Y := fun x hx => (hYA ▸ (Or.inl hx : x ∈ H ∪ K) : x ∈ Y ∩ A).1
    have hHA : H ⊆ A := fun x hx => (hYA ▸ (Or.inl hx : x ∈ H ∪ K) : x ∈ Y ∩ A).2
    obtain ⟨P', hP', hP'P, hhP', hP'K, hP'H⟩ := exists_arm (Y := H) hP hK.1.isClosed
      hH.1.isClosed hHK.symm (fun x hx => Or.inr hx.1) hhP hhH ⟨k, hkP, hkK⟩
    obtain ⟨Q', hQ', hQ'Q, hhQ', hQ'K, hQ'H⟩ := exists_arm (Y := H) hQ hK.1.isClosed
      hH.1.isClosed hHK.symm (fun x hx => Or.inr hx.1) hhQ hhH ⟨k, hkQ, hkK⟩
    have hN₁ := isContinuum_inter_of_hu hYhu hH hP' hHY (hP'P.trans hPY) ⟨h, hhH, hhP'⟩
    have hN₂ := isContinuum_inter_of_hu hAhu hH hQ' hHA (hQ'Q.trans hQA) ⟨h, hhH, hhQ'⟩
    have hN := isContinuum_union hN₁ hN₂ ⟨h, ⟨hhH, hhP'⟩, hhH, hhQ'⟩
    have hNH : (H ∩ P') ∪ (H ∩ Q') ⊆ H := union_subset inter_subset_left inter_subset_left
    refine not_core_of_isAtriodic hat hN hH hP' hQ'
      (hNH.trans (hHY.trans subset_union_left)) (hHY.trans subset_union_left)
      ((hP'P.trans hPY).trans subset_union_left) ((hQ'Q.trans hQA).trans subset_union_right)
      ⟨h, hhH, Or.inl ⟨hhH, hhP'⟩⟩ ⟨h, hhP', Or.inl ⟨hhH, hhP'⟩⟩ ⟨h, hhQ', Or.inr ⟨hhH, hhQ'⟩⟩
      (fun x hx => Or.inl hx) (fun x hx => Or.inr hx) ?_ ?_
      (fun h' => hP'H (fun x hx => hNH (h' hx))) (fun h' => hQ'H (fun x hx => hNH (h' hx)))
    · intro x ⟨hxP', hxQ'⟩
      have : x ∈ H ∪ K := hYA ▸ (⟨hPY (hP'P hxP'), hQA (hQ'Q hxQ')⟩ : x ∈ Y ∩ A)
      rcases this with h' | h'
      · exact Or.inl ⟨h', hxP'⟩
      · exact absurd h' (disjoint_left.mp hP'K hxP')
    · intro h'
      rcases h' hzH with ⟨-, h''⟩ | ⟨-, h''⟩
      · exact hz (Or.inl (hP'P h''))
      · exact hz (Or.inr (hQ'Q h''))
  have hHPQ : H ⊆ P ∪ Q := key hH hK hHK hYA hhP hhQ hhH hkP hkQ hkK
  have hKPQ : K ⊆ P ∪ Q :=
    key hK hH hHK.symm (by rw [hYA, union_comm]) hkP hkQ hkK hhP hhQ hhH
  refine Subset.antisymm (union_subset_union hPY hQA) (union_subset ?_ ?_)
  · rw [← eY]
    exact union_subset (union_subset subset_union_left hHPQ) hKPQ
  · rw [← eA]
    exact union_subset (union_subset subset_union_right hHPQ) hKPQ

end HPC.Plane
