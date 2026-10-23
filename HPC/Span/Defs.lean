import HPC.Fold.Questions78

/-!
# Batch 191, §2: span (Oversteegen–Tymchatyn 1982, p. 129; Hoehn–Oversteegen 2016, p. 184)

The definitions of the skeleton (`HPC/Span/OT82A.lean` in the commission), and the elementary
lemmas §2.1–§2.4. Only positivity of span matters, so the span notions are topological: a
continuum `Z ⊆ A × A` missing the diagonal.
-/

namespace HPC.Span

open Set Topology Metric Filter

section Defs

variable {X : Type*} [MetricSpace X]

/-- The off-diagonal condition. -/
def OffDiag (Z : Set (X × X)) : Prop := ∀ p ∈ Z, p.1 ≠ p.2

/-- **Positive surjective span** of `A` (O–T p. 129, `σ*(A) > 0`), topological form: a continuum
`Z ⊆ A × A` missing the diagonal, with both projections onto `A`. -/
def SurjSpanPos (A : Set X) : Prop :=
  ∃ Z ⊆ A ×ˢ A, Fold.Q78.IsContinuum Z ∧ OffDiag Z ∧ Prod.fst '' Z = A ∧ Prod.snd '' Z = A

/-- **Positive surjective semi-span** of `A` (`σ₀*(A) > 0`): the first projection onto `A`. -/
def SurjSemiSpanPos (A : Set X) : Prop :=
  ∃ Z ⊆ A ×ˢ A, Fold.Q78.IsContinuum Z ∧ OffDiag Z ∧ Prod.fst '' Z = A

/-- **Span zero** (`σ(X) = 0`). -/
def SpanZero (X : Type*) [MetricSpace X] : Prop :=
  ∀ A : Set X, Fold.Q78.IsContinuum A → ¬ SurjSpanPos A

/-- **Semi-span zero** (`σ₀(X) = 0`). -/
def SemiSpanZero (X : Type*) [MetricSpace X] : Prop :=
  ∀ A : Set X, Fold.Q78.IsContinuum A → ¬ SurjSemiSpanPos A

/-- **Span zero in the sense of Hoehn–Oversteegen** (2016, p. 184): every subcontinuum
`Z ⊆ X × X` with `π₁(Z) ⊆ π₂(Z)` meets the diagonal. -/
def HOSpanZero (X : Type*) [MetricSpace X] : Prop :=
  ∀ Z : Set (X × X), Fold.Q78.IsContinuum Z → Prod.fst '' Z ⊆ Prod.snd '' Z → ∃ p ∈ Z, p.1 = p.2

/-- O–T's definition of `σ₀(X) > 0`, read literally (p. 129): a nonempty connected `A ⊆ X`, a
connected `C ⊆ A × A` and `α > 0` with `d(x, y) ≥ α` on `C` and `π₁(C) = A`. -/
def OTSemiSpanPos (X : Type*) [MetricSpace X] : Prop :=
  ∃ A : Set X, A.Nonempty ∧ IsConnected A ∧ ∃ C ⊆ A ×ˢ A, IsConnected C ∧ ∃ α > 0,
    (∀ p ∈ C, α ≤ dist p.1 p.2) ∧ Prod.fst '' C = A

/-- O–T's definition of `σ(X) > 0`, read literally. -/
def OTSpanPos (X : Type*) [MetricSpace X] : Prop :=
  ∃ A : Set X, A.Nonempty ∧ IsConnected A ∧ ∃ C ⊆ A ×ˢ A, IsConnected C ∧ ∃ α > 0,
    (∀ p ∈ C, α ≤ dist p.1 p.2) ∧ Prod.fst '' C = A ∧ Prod.snd '' C = A

end Defs

section SpanLemmas

variable {X : Type*} [MetricSpace X]

/-- Closure step of §2.1: a connected `C` with `d ≥ α > 0` gives its closure, a continuum off the
diagonal, with `πᵢ(cl C) = cl πᵢ(C)`. -/
private theorem closure_data [CompactSpace X] {C : Set (X × X)} (hC : IsConnected C) {α : ℝ}
    (hα : 0 < α) (hd : ∀ p ∈ C, α ≤ dist p.1 p.2) :
    Fold.Q78.IsContinuum (closure C) ∧ OffDiag (closure C) ∧
      Prod.fst '' closure C = closure (Prod.fst '' C) ∧
      Prod.snd '' closure C = closure (Prod.snd '' C) := by
  have hcl : IsClosed {p : X × X | α ≤ dist p.1 p.2} :=
    isClosed_le continuous_const (continuous_fst.dist continuous_snd)
  have himg : ∀ {g : X × X → X}, Continuous g → g '' closure C = closure (g '' C) := by
    intro g hg
    apply Subset.antisymm (image_closure_subset_closure_image hg)
    exact closure_minimal (image_mono subset_closure)
      ((isClosed_closure.isCompact.image hg).isClosed)
  refine ⟨⟨isClosed_closure.isCompact, hC.closure⟩, fun p hp => ?_, himg continuous_fst,
    himg continuous_snd⟩
  have : α ≤ dist p.1 p.2 := closure_minimal hd hcl hp
  intro h
  rw [h, dist_self] at this
  linarith

/-- Minimum step of §2.1: on a compact nonempty set off the diagonal, `d` has a positive lower
bound. -/
theorem exists_pos_le_dist {Z : Set (X × X)} (hZ : Fold.Q78.IsContinuum Z)
    (hoff : OffDiag Z) : ∃ α > 0, ∀ p ∈ Z, α ≤ dist p.1 p.2 := by
  obtain ⟨p₀, hp₀, hmin⟩ := hZ.1.exists_isMinOn hZ.2.nonempty
    (continuous_fst.dist continuous_snd).continuousOn
  exact ⟨dist p₀.1 p₀.2, dist_pos.2 (hoff p₀ hp₀), fun p hp => hmin hp⟩

/-- **§2.1**: the literal definition agrees with the continuum form (closures). -/
theorem otSemiSpanPos_iff [CompactSpace X] :
    OTSemiSpanPos X ↔ ∃ A : Set X, Fold.Q78.IsContinuum A ∧ SurjSemiSpanPos A := by
  constructor
  · rintro ⟨A, -, hA, C, hCA, hC, α, hα, hd, h1⟩
    obtain ⟨hcont, hoff, h1', -⟩ := closure_data hC hα hd
    refine ⟨closure A, ⟨isClosed_closure.isCompact, hA.closure⟩, closure C, ?_, hcont, hoff, ?_⟩
    · exact (closure_mono hCA).trans (closure_prod_eq).subset
    · rw [h1', h1]
  · rintro ⟨A, hA, Z, hZA, hZ, hoff, h1⟩
    obtain ⟨α, hα, hd⟩ := exists_pos_le_dist hZ hoff
    exact ⟨A, hA.2.nonempty, hA.2, Z, hZA, hZ.2, α, hα, hd, h1⟩

/-- **§2.1**, for span. -/
theorem otSpanPos_iff [CompactSpace X] :
    OTSpanPos X ↔ ∃ A : Set X, Fold.Q78.IsContinuum A ∧ SurjSpanPos A := by
  constructor
  · rintro ⟨A, -, hA, C, hCA, hC, α, hα, hd, h1, h2⟩
    obtain ⟨hcont, hoff, h1', h2'⟩ := closure_data hC hα hd
    refine ⟨closure A, ⟨isClosed_closure.isCompact, hA.closure⟩, closure C, ?_, hcont, hoff, ?_,
      ?_⟩
    · exact (closure_mono hCA).trans (closure_prod_eq).subset
    · rw [h1', h1]
    · rw [h2', h2]
  · rintro ⟨A, hA, Z, hZA, hZ, hoff, h1, h2⟩
    obtain ⟨α, hα, hd⟩ := exists_pos_le_dist hZ hoff
    exact ⟨A, hA.2.nonempty, hA.2, Z, hZA, hZ.2, α, hα, hd, h1, h2⟩

/-- **§2.2**. -/
theorem SurjSpanPos.surjSemiSpanPos {A : Set X} (h : SurjSpanPos A) : SurjSemiSpanPos A := by
  obtain ⟨Z, hZA, hZ, hoff, h1, -⟩ := h
  exact ⟨Z, hZA, hZ, hoff, h1⟩

/-- The image of a continuum off the diagonal under `f × f`, `f` injective on `A ⊇ πᵢ(Z)`. -/
private theorem image_prodMap_data {Y : Type*} [MetricSpace Y] {A : Set X} {Z : Set (X × X)}
    (hZA : Z ⊆ A ×ˢ A) (hZ : Fold.Q78.IsContinuum Z) (hoff : OffDiag Z) {f : X → Y}
    (hf : Continuous f) (hinj : InjOn f A) :
    Prod.map f f '' Z ⊆ (f '' A) ×ˢ (f '' A) ∧ Fold.Q78.IsContinuum (Prod.map f f '' Z) ∧
      OffDiag (Prod.map f f '' Z) ∧ Prod.fst '' (Prod.map f f '' Z) = f '' (Prod.fst '' Z) ∧
      Prod.snd '' (Prod.map f f '' Z) = f '' (Prod.snd '' Z) := by
  have hc : Continuous (Prod.map f f) := hf.prodMap hf
  refine ⟨?_, ⟨hZ.1.image hc, hZ.2.image _ hc.continuousOn⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨mem_image_of_mem f (hZA hp).1, mem_image_of_mem f (hZA hp).2⟩
  · rintro _ ⟨p, hp, rfl⟩ h
    exact hoff p hp (hinj (hZA hp).1 (hZA hp).2 h)
  · rw [image_image, image_image]; rfl
  · rw [image_image, image_image]; rfl

/-- **§2.2**: positivity is carried by maps injective on `A`. -/
theorem SurjSpanPos.image {Y : Type*} [MetricSpace Y] {A : Set X} (h : SurjSpanPos A)
    {f : X → Y} (hf : Continuous f) (hinj : InjOn f A) : SurjSpanPos (f '' A) := by
  obtain ⟨Z, hZA, hZ, hoff, h1, h2⟩ := h
  obtain ⟨hs, hc, ho, e1, e2⟩ := image_prodMap_data hZA hZ hoff hf hinj
  exact ⟨_, hs, hc, ho, by rw [e1, h1], by rw [e2, h2]⟩

/-- **§2.2**. -/
theorem SurjSemiSpanPos.image {Y : Type*} [MetricSpace Y] {A : Set X} (h : SurjSemiSpanPos A)
    {f : X → Y} (hf : Continuous f) (hinj : InjOn f A) : SurjSemiSpanPos (f '' A) := by
  obtain ⟨Z, hZA, hZ, hoff, h1⟩ := h
  obtain ⟨hs, hc, ho, e1, -⟩ := image_prodMap_data hZA hZ hoff hf hinj
  exact ⟨_, hs, hc, ho, by rw [e1, h1]⟩

/-- The swap of a continuum is a continuum. -/
theorem isContinuum_swap {Z : Set (X × X)} (hZ : Fold.Q78.IsContinuum Z) :
    Fold.Q78.IsContinuum (Prod.swap '' Z) :=
  ⟨hZ.1.image continuous_swap, hZ.2.image _ continuous_swap.continuousOn⟩

omit [MetricSpace X] in
/-- The swap of a set off the diagonal is off the diagonal. -/
theorem offDiag_swap {Z : Set (X × X)} (hoff : OffDiag Z) : OffDiag (Prod.swap '' Z) := by
  rintro _ ⟨p, hp, rfl⟩ h
  exact hoff p hp h.symm

omit [MetricSpace X] in
theorem fst_image_swap (Z : Set (X × X)) : Prod.fst '' (Prod.swap '' Z) = Prod.snd '' Z := by
  rw [image_image]; rfl

omit [MetricSpace X] in
theorem snd_image_swap (Z : Set (X × X)) : Prod.snd '' (Prod.swap '' Z) = Prod.fst '' Z := by
  rw [image_image]; rfl

/-- **§2.3**: O–T's semi-span zero is H–O's span zero.

*Shape change:* the skeleton's `[CompactSpace X]` is not needed and has been removed. -/
theorem semiSpanZero_iff_hoSpanZero : SemiSpanZero X ↔ HOSpanZero X := by
  constructor
  · intro h Z hZ hsub
    by_contra hcon
    push_neg at hcon
    refine h (Prod.snd '' Z) ⟨hZ.1.image continuous_snd, hZ.2.image _ continuous_snd.continuousOn⟩
      ⟨Prod.swap '' Z, ?_, isContinuum_swap hZ, offDiag_swap hcon, fst_image_swap Z⟩
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨mem_image_of_mem _ hp, hsub (mem_image_of_mem _ hp)⟩
  · rintro h A - ⟨Z, hZA, hZ, hoff, h1⟩
    obtain ⟨p, hp, hpd⟩ := h (Prod.swap '' Z) (isContinuum_swap hZ) (by
      rw [fst_image_swap, snd_image_swap, h1]
      rintro _ ⟨p, hp, rfl⟩
      exact (hZA hp).2)
    exact offDiag_swap hoff p hp hpd

end SpanLemmas

/-- **§2.4**: H–O's definition with maps of continua (p. 184, first sentence).

*Shape change:* the skeleton's `[CompactSpace X]` is not needed and has been removed. -/
theorem hoSpanZero_iff_maps {X : Type} [MetricSpace X] :
    HOSpanZero X ↔ ∀ (C : Type) [MetricSpace C] [CompactSpace C] [ConnectedSpace C] (f g : C → X),
      Continuous f → Continuous g → range f ⊆ range g → ∃ c, f c = g c := by
  constructor
  · intro h C _ _ _ f g hf hg hfg
    have hc : Continuous fun c => (f c, g c) := hf.prodMk hg
    obtain ⟨_, ⟨c, rfl⟩, hc'⟩ := h (range fun c => (f c, g c))
      ⟨isCompact_range hc, isConnected_range hc⟩ (by
        rw [← range_comp, ← range_comp]; exact hfg)
    exact ⟨c, hc'⟩
  · intro h Z hZ hsub
    haveI : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.1
    haveI : ConnectedSpace Z := isConnected_iff_connectedSpace.mp hZ.2
    obtain ⟨c, hc⟩ := h Z (fun z => z.1.1) (fun z => z.1.2)
      (continuous_fst.comp continuous_subtype_val) (continuous_snd.comp continuous_subtype_val)
      (by
        rintro _ ⟨z, rfl⟩
        obtain ⟨w, hw, hw'⟩ := hsub (mem_image_of_mem _ z.2)
        exact ⟨⟨w, hw⟩, hw'⟩)
    exact ⟨c.1, c.2, hc⟩

end HPC.Span
