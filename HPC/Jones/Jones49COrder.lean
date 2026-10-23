import HPC.Jones.Jones49CStrip

/-!
# Batch 151, item A (part 2): the order of disjoint crossing sets; sectors

For disjoint crossing sets `L`, `L'` of the strip, `Prec a b L L'` (`L'` lies in the right side of
`L`) is a strict total order (`prec_total`, `prec_asymm`, `prec_trans`), compatible with
translation (`prec_sh_iff`), with `L` below its disjoint right translates (`prec_sh_self`).
For a family closed under translation by a period `T` (`LiftFam`), the *sectors*
`Sec a b A B = Rc A ∩ NotR B` between `A < B ≤ A' < B' ≤ A + T` are disjoint from every translate
of each other (`LiftFam.sec_disjoint`), miss every member weakly outside `(A, B)`
(`LiftFam.sec_disjoint_mem`), and the translates of the sectors `(A, B)` and `(B, A + T)` cover the
strip off the family (`LiftFam.sec_cover`).
-/

namespace HPC.Jones.Sector

open Set Topology Metric HPC.Plane

/-! ### The order of disjoint crossing sets -/

section Order

variable {a b : ℝ}

/-- `L'` lies to the right of `L`. -/
def Prec (a b : ℝ) (L L' : Set (ℝ × ℝ)) : Prop := L' ⊆ Rc a b L

/-- Horizontal translation by `c`. -/
def sh (c : ℝ) (L : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := (fun x : ℝ × ℝ => (x.1 + c, x.2)) '' L

theorem rc_sub {L : Set (ℝ × ℝ)} : Rc a b L ⊆ Strip a b \ L := sideOf_subset
theorem lc_sub {L : Set (ℝ × ℝ)} : Lc a b L ⊆ Strip a b \ L := sideOf_subset

theorem rc_absorb {L X : Set (ℝ × ℝ)} (hX : IsPreconnected X) (hXs : X ⊆ Strip a b \ L)
    (hne : (X ∩ Rc a b L).Nonempty) : X ⊆ Rc a b L := sideOf_absorb hX hXs hne

theorem lc_absorb {L X : Set (ℝ × ℝ)} (hX : IsPreconnected X) (hXs : X ⊆ Strip a b \ L)
    (hne : (X ∩ Lc a b L).Nonempty) : X ⊆ Lc a b L := sideOf_absorb hX hXs hne

theorem notR_absorb {L X : Set (ℝ × ℝ)} (hX : IsPreconnected X) (hXs : X ⊆ Strip a b \ L)
    (hne : (X ∩ NotR a b L).Nonempty) : X ⊆ NotR a b L := by
  obtain ⟨y, hyX, hy⟩ := hne
  intro w hw
  refine ⟨(hXs hw).1, ?_⟩
  rintro (hwL | hwR)
  · exact (hXs hw).2 hwL
  · exact hy.2 (Or.inr (rc_absorb hX hXs ⟨w, hw, hwR⟩ hyX))

theorem sub_rc_or_notR {L X : Set (ℝ × ℝ)} (hX : IsPreconnected X) (hXs : X ⊆ Strip a b \ L) :
    X ⊆ Rc a b L ∨ X ⊆ NotR a b L := by
  by_cases h : (X ∩ Rc a b L).Nonempty
  · exact Or.inl (rc_absorb hX hXs h)
  · refine Or.inr fun w hw => ⟨(hXs hw).1, ?_⟩
    rintro (hwL | hwR)
    · exact (hXs hw).2 hwL
    · exact h ⟨w, hw, hwR⟩

theorem cross_sub_strip_diff {L L' : Set (ℝ × ℝ)} (hL' : IsCross a b L') (hd : Disjoint L L') :
    L' ⊆ Strip a b \ L := fun _ hz => ⟨hL'.sub hz, fun h => disjoint_left.1 hd h hz⟩

theorem exists_far2 {L L' : Set (ℝ × ℝ)} (hL : IsCross a b L) (hL' : IsCross a b L') :
    (∃ x ∈ Strip a b, FarR L x ∧ FarR L' x) ∧ (∃ x ∈ Strip a b, FarL L x ∧ FarL L' x) := by
  obtain ⟨M₁, hM₁⟩ := (hL.compact.image continuous_fst).isBounded.bddAbove
  obtain ⟨M₂, hM₂⟩ := (hL'.compact.image continuous_fst).isBounded.bddAbove
  obtain ⟨N₁, hN₁⟩ := (hL.compact.image continuous_fst).isBounded.bddBelow
  obtain ⟨N₂, hN₂⟩ := (hL'.compact.image continuous_fst).isBounded.bddBelow
  refine ⟨⟨(max M₁ M₂ + 1, a), ⟨le_rfl, hL.le⟩, fun z hz => ?_, fun z hz => ?_⟩,
    ⟨(min N₁ N₂ - 1, a), ⟨le_rfl, hL.le⟩, fun z hz => ?_, fun z hz => ?_⟩⟩
  · have := hM₁ (mem_image_of_mem Prod.fst hz); simp only
    linarith [le_max_left M₁ M₂]
  · have := hM₂ (mem_image_of_mem Prod.fst hz); simp only
    linarith [le_max_right M₁ M₂]
  · have := hN₁ (mem_image_of_mem Prod.fst hz); simp only
    linarith [min_le_left N₁ N₂]
  · have := hN₂ (mem_image_of_mem Prod.fst hz); simp only
    linarith [min_le_right N₁ N₂]

variable (hab : a < b)
include hab

theorem lc_sub_notR {L : Set (ℝ × ℝ)} (hL : IsCross a b L) : Lc a b L ⊆ NotR a b L :=
  fun z hz => ⟨(lc_sub hz).1, by
    rintro (h | h)
    · exact (lc_sub hz).2 h
    · exact disjoint_left.1 (lc_disjoint_rc hab hL) hz h⟩

omit hab in
/-- If `L'` is not to the right of `L`, then `L` is to the right of `L'`. -/
theorem prec_of_notR {L L' : Set (ℝ × ℝ)} (hL : IsCross a b L) (hL' : IsCross a b L')
    (hd : Disjoint L L') (h : L' ⊆ NotR a b L) : Prec a b L' L := by
  have hX := (goodSide_farR hL).union_isPreconnected hL
  obtain ⟨⟨x, hx, hx1, hx2⟩, -⟩ := exists_far2 hL hL'
  have hsub : Rc a b L ∪ L ⊆ Strip a b \ L' := by
    rintro z (hz | hz)
    · refine ⟨(rc_sub hz).1, fun hzL' => ?_⟩
      exact (h hzL').2 (Or.inr hz)
    · exact ⟨hL.sub hz, fun hzL' => disjoint_left.1 hd hz hzL'⟩
  have := rc_absorb hX hsub ⟨x, Or.inl ((goodSide_farR hL).mem hx hx1),
    (goodSide_farR hL').mem hx hx2⟩
  exact fun z hz => this (Or.inr hz)

theorem prec_asymm {L L' : Set (ℝ × ℝ)} (hL : IsCross a b L) (hL' : IsCross a b L')
    (hd : Disjoint L L') (h1 : Prec a b L L') (h2 : Prec a b L' L) : False := by
  have hX := (goodSide_farL hL).union_isPreconnected hL
  obtain ⟨-, ⟨x, hx, hx1, hx2⟩⟩ := exists_far2 hL hL'
  have hsub : Lc a b L ∪ L ⊆ Strip a b \ L' := by
    rintro z (hz | hz)
    · refine ⟨(lc_sub hz).1, fun hzL' => ?_⟩
      exact disjoint_left.1 (lc_disjoint_rc hab hL) hz (h1 hzL')
    · exact ⟨hL.sub hz, fun hzL' => disjoint_left.1 hd hz hzL'⟩
  have := lc_absorb hX hsub ⟨x, Or.inl ((goodSide_farL hL).mem hx hx1),
    (goodSide_farL hL').mem hx hx2⟩
  obtain ⟨z, hz⟩ := hL.conn.nonempty
  exact disjoint_left.1 (lc_disjoint_rc hab hL') (this (Or.inr hz)) (h2 hz)

omit hab in
theorem prec_total {L L' : Set (ℝ × ℝ)} (hL : IsCross a b L) (hL' : IsCross a b L')
    (hd : Disjoint L L') : Prec a b L L' ∨ Prec a b L' L := by
  rcases sub_rc_or_notR hL'.conn.isPreconnected (cross_sub_strip_diff hL' hd) with h | h
  · exact Or.inl h
  · exact Or.inr (prec_of_notR hL hL' hd h)

/-- What lies to the left of `L` is in `NotR L`. -/
theorem notR_of_prec {L X : Set (ℝ × ℝ)} (hL : IsCross a b L) (hX : IsCross a b X)
    (hd : Disjoint X L) (h : Prec a b X L) : X ⊆ NotR a b L := by
  rcases sub_rc_or_notR hX.conn.isPreconnected (cross_sub_strip_diff hX hd.symm) with h' | h'
  · exact (prec_asymm hab hX hL hd h h').elim
  · exact h'

/-- The right side shrinks to the right. -/
theorem rc_mono {L L' : Set (ℝ × ℝ)} (hL : IsCross a b L) (hL' : IsCross a b L')
    (hd : Disjoint L L') (h : Prec a b L L') : Rc a b L' ⊆ Rc a b L := by
  have hLn := notR_of_prec hab hL' hL hd h
  have hX := (goodSide_farR hL').union_isPreconnected hL'
  obtain ⟨⟨x, hx, hx1, hx2⟩, -⟩ := exists_far2 hL hL'
  have hsub : Rc a b L' ∪ L' ⊆ Strip a b \ L := by
    rintro z (hz | hz)
    · refine ⟨(rc_sub hz).1, fun hzL => ?_⟩
      exact (hLn hzL).2 (Or.inr hz)
    · exact ⟨hL'.sub hz, fun hzL => disjoint_left.1 hd hzL hz⟩
  have := rc_absorb hX hsub ⟨x, Or.inl ((goodSide_farR hL').mem hx hx2),
    (goodSide_farR hL).mem hx hx1⟩
  exact fun z hz => this (Or.inl hz)

theorem notR_mono {L L' : Set (ℝ × ℝ)} (hL : IsCross a b L) (hL' : IsCross a b L')
    (hd : Disjoint L L') (h : Prec a b L L') : NotR a b L ⊆ NotR a b L' := by
  rintro z ⟨hzs, hz⟩
  refine ⟨hzs, ?_⟩
  rintro (hzL' | hzR)
  · exact hz (Or.inr (h hzL'))
  · exact hz (Or.inr (rc_mono hab hL hL' hd h hzR))

theorem prec_trans {L L' L'' : Set (ℝ × ℝ)} (hL : IsCross a b L) (hL' : IsCross a b L')
    (hd : Disjoint L L') (h1 : Prec a b L L') (h2 : Prec a b L' L'') : Prec a b L L'' :=
  h2.trans (rc_mono hab hL hL' hd h1)

/-- The leftmost points of `L` are at most those of anything to its right. -/
theorem prec_min {L L' : Set (ℝ × ℝ)} (hL : IsCross a b L) (h : Prec a b L L') :
    ∀ z' ∈ L', ∃ z ∈ L, z.1 ≤ z'.1 := by
  intro z' hz'
  by_contra hcon
  push_neg at hcon
  have hzs : z' ∈ Strip a b := (rc_sub (h hz')).1
  exact disjoint_left.1 (lc_disjoint_rc hab hL) ((goodSide_farL hL).mem hzs hcon) (h hz')

end Order

/-! ### Translation -/

section Shift

variable {a b : ℝ}

/-- The translation homeomorphism. -/
def shH (c : ℝ) : ℝ × ℝ ≃ₜ ℝ × ℝ :=
  (Homeomorph.addRight c).prodCongr (Homeomorph.refl ℝ)

theorem shH_apply (c : ℝ) (x : ℝ × ℝ) : shH c x = (x.1 + c, x.2) := rfl

theorem sh_eq_image (c : ℝ) (L : Set (ℝ × ℝ)) : sh c L = shH c '' L := rfl

theorem mem_sh {c : ℝ} {L : Set (ℝ × ℝ)} {x : ℝ × ℝ} : x ∈ sh c L ↔ (x.1 - c, x.2) ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by ext <;> simp⟩

theorem sh_sh (c d : ℝ) (L : Set (ℝ × ℝ)) : sh c (sh d L) = sh (d + c) L := by
  ext x; simp only [mem_sh]; ring_nf

theorem sh_zero (L : Set (ℝ × ℝ)) : sh 0 L = L := by
  ext x; simp [mem_sh]

theorem sh_strip (c : ℝ) : sh c (Strip a b) = Strip a b := by
  ext x; simp [mem_sh, Strip]

theorem sh_diff (c : ℝ) (S L : Set (ℝ × ℝ)) : sh c (S \ L) = sh c S \ sh c L := by
  ext x; simp [mem_sh]

theorem sh_inter (c : ℝ) (S L : Set (ℝ × ℝ)) : sh c (S ∩ L) = sh c S ∩ sh c L := by
  ext x; simp [mem_sh]

theorem sh_mono {c : ℝ} {S L : Set (ℝ × ℝ)} (h : S ⊆ L) : sh c S ⊆ sh c L := image_mono h

theorem sh_subset_iff {c : ℝ} {S L : Set (ℝ × ℝ)} : sh c S ⊆ sh c L ↔ S ⊆ L := by
  constructor
  · intro h x hx
    have := h (show ((x.1 + c, x.2) : ℝ × ℝ) ∈ sh c S from mem_sh.2 (by simpa using hx))
    rw [mem_sh] at this
    simpa using this
  · exact sh_mono

theorem disjoint_sh_iff {c : ℝ} {S L : Set (ℝ × ℝ)} : Disjoint (sh c S) (sh c L) ↔ Disjoint S L := by
  rw [sh_eq_image, sh_eq_image, disjoint_image_iff (shH c).injective]

theorem IsCross.sh {L : Set (ℝ × ℝ)} (hL : IsCross a b L) (c : ℝ) : IsCross a b (sh c L) where
  compact := hL.compact.image (shH c).continuous
  conn := hL.conn.image _ (shH c).continuous.continuousOn
  sub := by rw [← sh_strip (a := a) (b := b) c]; exact sh_mono hL.sub
  bot := by
    obtain ⟨z, hz, hza⟩ := hL.bot
    exact ⟨_, mem_image_of_mem _ hz, hza⟩
  top := by
    obtain ⟨z, hz, hza⟩ := hL.top
    exact ⟨_, mem_image_of_mem _ hz, hza⟩

theorem rc_sh {L : Set (ℝ × ℝ)} (hL : IsCross a b L) (c : ℝ) :
    Rc a b (sh c L) = sh c (Rc a b L) := by
  obtain ⟨x, hx, hfx⟩ := (goodSide_farR hL).ex
  have hx' : shH c x ∈ Strip a b := by
    rw [← sh_strip (a := a) (b := b) c]; exact mem_image_of_mem _ hx
  have hfx' : FarR (sh c L) (shH c x) := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [shH_apply]
    linarith [hfx z hz]
  unfold Rc
  rw [(goodSide_farR (hL.sh c)).eq hx' hfx', (goodSide_farR hL).eq hx hfx]
  have hmem : x ∈ Strip a b \ L := ⟨hx, (goodSide_farR hL).miss x hfx⟩
  have := (shH c).image_connectedComponentIn hmem
  calc connectedComponentIn (Strip a b \ sh c L) (shH c x)
      = connectedComponentIn (shH c '' (Strip a b \ L)) (shH c x) := by
        rw [← sh_eq_image, sh_diff, sh_strip]
    _ = shH c '' connectedComponentIn (Strip a b \ L) x := this.symm
    _ = sh c (connectedComponentIn (Strip a b \ L) x) := rfl

theorem notR_sh {L : Set (ℝ × ℝ)} (hL : IsCross a b L) (c : ℝ) :
    NotR a b (sh c L) = sh c (NotR a b L) := by
  rw [NotR, NotR, rc_sh hL, sh_diff, sh_strip]
  congr 1
  ext x; simp [mem_sh]

theorem prec_sh_iff {L L' : Set (ℝ × ℝ)} (hL : IsCross a b L) (c : ℝ) :
    Prec a b (sh c L) (sh c L') ↔ Prec a b L L' := by
  rw [Prec, Prec, rc_sh hL, sh_subset_iff]

/-- A crossing set lies to the left of its translates to the right, if disjoint from them. -/
theorem prec_sh_self {L : Set (ℝ × ℝ)} (hL : IsCross a b L) {c : ℝ} (hc : 0 < c)
    (hd : Disjoint L (sh c L)) : Prec a b L (sh c L) := by
  obtain ⟨z, hz, hmax⟩ := hL.compact.exists_isMaxOn hL.conn.nonempty continuous_fst.continuousOn
  have hzs : shH c z ∈ Strip a b := by
    rw [← sh_strip (a := a) (b := b) c]; exact mem_image_of_mem _ (hL.sub hz)
  have hfar : FarR L (shH c z) := fun w hw => by
    have : w.1 ≤ z.1 := hmax hw
    simp only [shH_apply]; linarith
  exact rc_absorb (hL.sh c).conn.isPreconnected (cross_sub_strip_diff (hL.sh c) hd)
    ⟨_, mem_image_of_mem _ hz, (goodSide_farR hL).mem hzs hfar⟩

end Shift

/-! ### Families of disjoint crossing sets closed under a translation; sectors -/

section Family

variable {a b T : ℝ}

/-- A family of pairwise disjoint crossing sets, closed under the translations by multiples of
`T`, with no set equal to a proper translate of itself. -/
structure LiftFam (a b T : ℝ) (F : Set (Set (ℝ × ℝ))) : Prop where
  cross : ∀ L ∈ F, IsCross a b L
  disj : ∀ L ∈ F, ∀ L' ∈ F, L ≠ L' → Disjoint L L'
  shift : ∀ L ∈ F, ∀ j : ℤ, sh (T * j) L ∈ F
  ne : ∀ L ∈ F, ∀ j : ℤ, j ≠ 0 → sh (T * j) L ≠ L

/-- `L ≤ L'` in the order of a family. -/
def PrecLe (a b : ℝ) (L L' : Set (ℝ × ℝ)) : Prop := L = L' ∨ Prec a b L L'

/-- The sector between `A` and `B`. -/
def Sec (a b : ℝ) (A B : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := Rc a b A ∩ NotR a b B

theorem rc_disjoint_notR {L : Set (ℝ × ℝ)} : Disjoint (Rc a b L) (NotR a b L) :=
  disjoint_left.2 fun _ h1 h2 => h2.2 (Or.inr h1)

theorem sec_sh {A B : Set (ℝ × ℝ)} (hA : IsCross a b A) (hB : IsCross a b B) (c : ℝ) :
    sh c (Sec a b A B) = Sec a b (sh c A) (sh c B) := by
  rw [Sec, Sec, sh_inter, rc_sh hA, notR_sh hB]

theorem sec_subset {A B : Set (ℝ × ℝ)} : Sec a b A B ⊆ Strip a b := fun _ h => (rc_sub h.1).1

namespace LiftFam

variable {F : Set (Set (ℝ × ℝ))} (hF : LiftFam a b T F) (hab : a < b)
include hF hab

omit hab in
theorem prec_irrefl {L : Set (ℝ × ℝ)} (hL : L ∈ F) : ¬ Prec a b L L := fun h => by
  obtain ⟨z, hz⟩ := (hF.cross L hL).conn.nonempty
  exact (rc_sub (h hz)).2 hz

theorem asymm {L L' : Set (ℝ × ℝ)} (hL : L ∈ F) (hL' : L' ∈ F) (h1 : Prec a b L L')
    (h2 : Prec a b L' L) : False := by
  by_cases he : L = L'
  · subst he; exact hF.prec_irrefl hL h1
  · exact prec_asymm hab (hF.cross L hL) (hF.cross L' hL') (hF.disj L hL L' hL' he) h1 h2

omit hab in
theorem total {L L' : Set (ℝ × ℝ)} (hL : L ∈ F) (hL' : L' ∈ F) (he : L ≠ L') :
    Prec a b L L' ∨ Prec a b L' L :=
  prec_total (hF.cross L hL) (hF.cross L' hL') (hF.disj L hL L' hL' he)

theorem trans {L L' L'' : Set (ℝ × ℝ)} (hL : L ∈ F) (hL' : L' ∈ F) (h1 : Prec a b L L')
    (h2 : Prec a b L' L'') : Prec a b L L'' := by
  by_cases he : L = L'
  · subst he; exact (hF.prec_irrefl hL h1).elim
  · exact prec_trans hab (hF.cross L hL) (hF.cross L' hL') (hF.disj L hL L' hL' he) h1 h2

theorem le_trans' {L L' L'' : Set (ℝ × ℝ)} (hL : L ∈ F) (hL' : L' ∈ F) (h1 : PrecLe a b L L')
    (h2 : PrecLe a b L' L'') : PrecLe a b L L'' := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact Or.inr h1
  · exact Or.inr (hF.trans hab hL hL' h1 h2)

theorem lt_of_le_of_lt {L L' L'' : Set (ℝ × ℝ)} (hL : L ∈ F) (hL' : L' ∈ F)
    (h1 : PrecLe a b L L') (h2 : Prec a b L' L'') : Prec a b L L'' := by
  rcases h1 with rfl | h1
  · exact h2
  · exact hF.trans hab hL hL' h1 h2

theorem lt_of_lt_of_le {L L' L'' : Set (ℝ × ℝ)} (hL : L ∈ F) (hL' : L' ∈ F)
    (h1 : Prec a b L L') (h2 : PrecLe a b L' L'') : Prec a b L L'' := by
  rcases h2 with rfl | h2
  · exact h1
  · exact hF.trans hab hL hL' h1 h2

theorem rc_anti {L L' : Set (ℝ × ℝ)} (hL : L ∈ F) (hL' : L' ∈ F) (h : PrecLe a b L L') :
    Rc a b L' ⊆ Rc a b L := by
  rcases h with rfl | h
  · exact le_rfl
  by_cases he : L = L'
  · subst he; exact le_rfl
  · exact rc_mono hab (hF.cross L hL) (hF.cross L' hL') (hF.disj L hL L' hL' he) h

theorem notR_mono' {L L' : Set (ℝ × ℝ)} (hL : L ∈ F) (hL' : L' ∈ F) (h : PrecLe a b L L') :
    NotR a b L ⊆ NotR a b L' := by
  rcases h with rfl | h
  · exact le_rfl
  by_cases he : L = L'
  · subst he; exact le_rfl
  · exact notR_mono hab (hF.cross L hL) (hF.cross L' hL') (hF.disj L hL L' hL' he) h

theorem sub_notR {L X : Set (ℝ × ℝ)} (hL : L ∈ F) (hX : X ∈ F) (h : Prec a b X L) :
    X ⊆ NotR a b L := by
  by_cases he : X = L
  · subst he; exact (hF.prec_irrefl hL h).elim
  · exact notR_of_prec hab (hF.cross L hL) (hF.cross X hX) (hF.disj X hX L hL he) h

omit hab in
theorem prec_sh_iff' {L L' : Set (ℝ × ℝ)} (hL : L ∈ F) (c : ℝ) :
    Prec a b (sh c L) (sh c L') ↔ Prec a b L L' := prec_sh_iff (hF.cross L hL) c

omit hab in
theorem le_sh_iff {L L' : Set (ℝ × ℝ)} (hL : L ∈ F) (c : ℝ) :
    PrecLe a b (sh c L) (sh c L') ↔ PrecLe a b L L' := by
  unfold PrecLe
  rw [hF.prec_sh_iff' hL c]
  constructor
  · rintro (h | h)
    · left
      have := congrArg (sh (-c)) h
      rwa [sh_sh, sh_sh, add_neg_cancel, sh_zero, sh_zero] at this
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (h ▸ rfl)
    · exact Or.inr h

omit hab in
theorem prec_shift_one (hT : 0 < T) {L : Set (ℝ × ℝ)} (hL : L ∈ F) : Prec a b L (sh T L) := by
  have h1 : sh (T * (1 : ℤ)) L ∈ F := hF.shift L hL 1
  have hne : sh (T * (1 : ℤ)) L ≠ L := hF.ne L hL 1 one_ne_zero
  simp only [Int.cast_one, mul_one] at h1 hne
  exact prec_sh_self (hF.cross L hL) hT (hF.disj L hL _ h1 hne.symm)

theorem prec_shift_nat (hT : 0 < T) {L : Set (ℝ × ℝ)} (hL : L ∈ F) (n : ℕ) :
    Prec a b L (sh (T * (n + 1 : ℕ)) L) := by
  induction n with
  | zero => simpa using hF.prec_shift_one hT hL
  | succ n ih =>
    have h1 : sh (T * (n + 1 : ℕ)) L ∈ F := by
      have := hF.shift L hL (n + 1); push_cast at this ⊢; exact this
    have h2 := hF.prec_shift_one hT h1
    rw [sh_sh] at h2
    have e : T * ((n + 1 : ℕ) : ℝ) + T = T * ((n + 1 + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e] at h2
    exact hF.trans hab hL h1 ih h2

/-- Translating to the right moves up in the order. -/
theorem prec_shift_pos (hT : 0 < T) {L : Set (ℝ × ℝ)} (hL : L ∈ F) {j : ℤ} (hj : 0 < j) :
    Prec a b L (sh (T * j) L) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = (n + 1 : ℕ) := ⟨j.toNat - 1, by omega⟩
  have := hF.prec_shift_nat hab hT hL n
  push_cast at this ⊢
  exact this

theorem le_shift_nonneg (hT : 0 < T) {L : Set (ℝ × ℝ)} (hL : L ∈ F) {j : ℤ} (hj : 0 ≤ j) :
    PrecLe a b L (sh (T * j) L) := by
  rcases hj.lt_or_eq with hj | rfl
  · exact Or.inr (hF.prec_shift_pos hab hT hL hj)
  · left; simp [sh_zero]

theorem shift_le_nonpos (hT : 0 < T) {L : Set (ℝ × ℝ)} (hL : L ∈ F) {j : ℤ} (hj : j ≤ 0) :
    PrecLe a b (sh (T * j) L) L := by
  have h := hF.le_shift_nonneg hab hT (hF.shift L hL j) (j := -j) (by omega)
  rwa [sh_sh, show T * (j : ℝ) + T * ((-j : ℤ) : ℝ) = 0 by push_cast; ring, sh_zero] at h

/-- **Disjoint sectors.** If `A < B ≤ A' < B' ≤ A + T` cyclically, the sector `(A, B)` misses
every translate of the sector `(A', B')`. -/
theorem sec_disjoint (hT : 0 < T) {A B A' B' : Set (ℝ × ℝ)} (hA : A ∈ F) (hB : B ∈ F)
    (hA' : A' ∈ F) (hB' : B' ∈ F) (h1 : PrecLe a b B A') (h2 : PrecLe a b B' (sh T A))
    (j : ℤ) : Disjoint (Sec a b A B) (sh (T * j) (Sec a b A' B')) := by
  rw [sec_sh (hF.cross A' hA') (hF.cross B' hB')]
  rcases le_or_gt 0 j with hj | hj
  · -- the translate lies to the right of `B`
    have hle : PrecLe a b B (sh (T * j) A') :=
      hF.le_trans' hab hB hA' h1 (hF.le_shift_nonneg hab hT hA' hj)
    refine disjoint_left.2 fun z hz hz' => ?_
    exact disjoint_left.1 rc_disjoint_notR (hF.rc_anti hab hB (hF.shift A' hA' j) hle hz'.1) hz.2
  · -- the translate lies to the left of `A`
    have hle1 : PrecLe a b (sh (T * j) B') (sh (T * (j + 1 : ℤ)) A) := by
      have := (hF.le_sh_iff hB' (T * j)).2 h2
      rwa [sh_sh, show T + T * (j : ℝ) = T * ((j + 1 : ℤ) : ℝ) by push_cast; ring] at this
    have hle : PrecLe a b (sh (T * j) B') A :=
      hF.le_trans' hab (hF.shift B' hB' j) (hF.shift A hA (j + 1)) hle1
        (hF.shift_le_nonpos hab hT hA (by omega))
    refine disjoint_left.2 fun z hz hz' => ?_
    exact disjoint_left.1 rc_disjoint_notR hz.1
      (hF.notR_mono' hab (hF.shift B' hB' j) hA hle hz'.2)

/-- A member of the family lying weakly outside `(A, B)` misses the sector. -/
theorem sec_disjoint_mem {A B X : Set (ℝ × ℝ)} (hA : A ∈ F) (hX : X ∈ F)
    (h : PrecLe a b X A ∨ PrecLe a b B X) : Disjoint (Sec a b A B) X := by
  refine disjoint_left.2 fun z hz hzX => ?_
  rcases h with (rfl | h) | (rfl | h)
  · exact (rc_sub hz.1).2 hzX
  · exact disjoint_left.1 rc_disjoint_notR hz.1 (hF.sub_notR hab hA hX h hzX)
  · exact hz.2.2 (Or.inl hzX)
  · exact hz.2.2 (Or.inr (h hzX))

/-- A member strictly between `A` and `B` lies in the sector. -/
theorem sub_sec {A B X : Set (ℝ × ℝ)} (hB : B ∈ F) (hX : X ∈ F) (h1 : Prec a b A X)
    (h2 : Prec a b X B) : X ⊆ Sec a b A B :=
  fun _ hz => ⟨h1 hz, hF.sub_notR hab hB hX h2 hz⟩

/-- **The sectors cover.** If `A < B < A + T`, every point of the strip off the translates of `A`
and `B` lies in a translate of the sector `(A, B)` or of the sector `(B, A + T)`. -/
theorem sec_cover (hT : 0 < T) {A B : Set (ℝ × ℝ)} (hA : A ∈ F) (hB : B ∈ F)
    {y : ℝ × ℝ} (hy : y ∈ Strip a b) (hyA : ∀ j : ℤ, y ∉ sh (T * j) A)
    (hyB : ∀ j : ℤ, y ∉ sh (T * j) B) :
    ∃ j : ℤ, y ∈ sh (T * j) (Sec a b A B) ∨ y ∈ sh (T * j) (Sec a b B (sh T A)) := by
  classical
  have hAc := hF.cross A hA
  obtain ⟨M₁, hM₁⟩ := (hAc.compact.image continuous_fst).isBounded.bddBelow
  obtain ⟨M₂, hM₂⟩ := (hAc.compact.image continuous_fst).isBounded.bddAbove
  set J : ℤ → Prop := fun j => y ∈ Rc a b (sh (T * j) A)
  have hbdd : ∃ N : ℤ, ∀ j, J j → j ≤ N := by
    refine ⟨⌈(y.1 - M₁) / T⌉, fun j hj => ?_⟩
    by_contra hcon
    push_neg at hcon
    have hlt : (y.1 - M₁) / T < j := (Int.le_ceil _).trans_lt (by exact_mod_cast hcon)
    have hfar : FarL (sh (T * j) A) y := by
      rintro _ ⟨z, hz, rfl⟩
      have := hM₁ (mem_image_of_mem Prod.fst hz)
      rw [div_lt_iff₀ hT] at hlt
      simp only
      linarith
    exact disjoint_left.1 (lc_disjoint_rc hab (hAc.sh _)) ((goodSide_farL (hAc.sh _)).mem hy hfar) hj
  have hinh : ∃ j, J j := by
    refine ⟨⌊(y.1 - M₂) / T⌋ - 1, ?_⟩
    have hlt : ((⌊(y.1 - M₂) / T⌋ - 1 : ℤ) : ℝ) < (y.1 - M₂) / T := by
      push_cast; linarith [Int.floor_le ((y.1 - M₂) / T)]
    have hfar : FarR (sh (T * ((⌊(y.1 - M₂) / T⌋ - 1 : ℤ) : ℝ)) A) y := by
      rintro _ ⟨z, hz, rfl⟩
      have := hM₂ (mem_image_of_mem Prod.fst hz)
      rw [lt_div_iff₀ hT] at hlt
      simp only
      linarith
    exact (goodSide_farR (hAc.sh _)).mem hy hfar
  obtain ⟨j₀, hj₀, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
  have hnot : y ∉ Rc a b (sh (T * (j₀ + 1 : ℤ)) A) := fun h => by
    have := hmax _ h; omega
  have hyN : y ∈ NotR a b (sh (T * (j₀ + 1 : ℤ)) A) := ⟨hy, by
    rintro (h | h)
    · exact hyA _ h
    · exact hnot h⟩
  have e : sh (T * (j₀ + 1 : ℤ)) A = sh (T * j₀) (sh T A) := by
    rw [sh_sh]; congr 1; push_cast; ring
  refine ⟨j₀, ?_⟩
  by_cases hyB' : y ∈ Rc a b (sh (T * j₀) B)
  · right
    rw [sec_sh (hF.cross B hB) (hAc.sh T), ← e]
    exact ⟨hyB', hyN⟩
  · left
    rw [sec_sh hAc (hF.cross B hB)]
    exact ⟨hj₀, hy, by
      rintro (h | h)
      · exact hyB _ h
      · exact hyB' h⟩

end LiftFam

end Family

section SecOpen

variable {a b T : ℝ}

theorem notR_open_rel {L : Set (ℝ × ℝ)} (hL : IsClosed L) {y : ℝ × ℝ} (hy : y ∈ NotR a b L) :
    ∃ η > 0, ball y η ∩ Strip a b ⊆ NotR a b L := by
  obtain ⟨η, hη, hc, hdisj⟩ := exists_ball_strip (a := a) (b := b) hL (fun h => hy.2 (Or.inl h))
  refine ⟨η, hη, notR_absorb hc (fun w hw => ⟨hw.2, fun hwL => ?_⟩)
    ⟨y, (⟨mem_ball_self hη, hy.1⟩ : y ∈ ball y η ∩ Strip a b), hy⟩⟩
  have : w ∈ ball y η ∩ L := ⟨hw.1, hwL⟩
  rw [hdisj] at this
  exact this

theorem sec_open_rel {A B : Set (ℝ × ℝ)} (hA : IsClosed A) (hB : IsClosed B) {y : ℝ × ℝ}
    (hy : y ∈ Sec a b A B) : ∃ η > 0, ball y η ∩ Strip a b ⊆ Sec a b A B := by
  obtain ⟨η₁, hη₁, h₁⟩ := sideOf_open_rel hA hy.1
  obtain ⟨η₂, hη₂, h₂⟩ := notR_open_rel hB hy.2
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun w hw => ⟨h₁ ⟨?_, hw.2⟩, h₂ ⟨?_, hw.2⟩⟩⟩
  · exact ball_subset_ball (min_le_left _ _) hw.1
  · exact ball_subset_ball (min_le_right _ _) hw.1

theorem LiftFam.sec_nonempty {F : Set (Set (ℝ × ℝ))} (hF : LiftFam a b T F) (hab : a < b)
    {A B : Set (ℝ × ℝ)} (hA : A ∈ F) (hB : B ∈ F) (h : Prec a b A B) :
    (Sec a b A B).Nonempty := by
  have hAc := hF.cross A hA
  obtain ⟨x, hxA, hxcl⟩ := (goodSide_farR hAc).exists_mem_closure hAc
  have hxN : x ∈ NotR a b B := hF.sub_notR hab hB hA h hxA
  obtain ⟨η, hη, hsub⟩ := notR_open_rel (hF.cross B hB).compact.isClosed hxN
  obtain ⟨w, hwR, hwd⟩ := Metric.mem_closure_iff.1 hxcl η hη
  exact ⟨w, hwR, hsub ⟨by rw [mem_ball, dist_comm]; exact hwd, (rc_sub hwR).1⟩⟩

end SecOpen

end HPC.Jones.Sector
