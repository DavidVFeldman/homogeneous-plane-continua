import HPC.Plane.EndPoints51

/-!
# Batch 193, §2: PL graphs, fans, separation, `HOThm20`

Part of the batch-193 skeleton `HO16A.lean` (commission 193, §2), split off unchanged. The
definitions and statements are the skeleton's.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane

/-! ## §2. Definitions (commission §2) -/

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **PL graph** (H–O p. 183, "graph", in piecewise linear form): a finite union of
nondegenerate segments, two different ones meeting at most in common endpoints. -/
def IsPLGraph (G : Set E) : Prop :=
  ∃ S : Finset (E × E), (∀ s ∈ S, s.1 ≠ s.2) ∧ G = ⋃ s ∈ S, segment ℝ s.1 s.2 ∧
    ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' →
      segment ℝ s.1 s.2 ∩ segment ℝ s'.1 s'.2 ⊆ ({s.1, s.2} : Set E) ∩ {s'.1, s'.2}

/-- **A fan at `y` in `A` of diameter `< r`** (H–O p. 187): finitely many segments `[y, z k]`,
pairwise meeting only at `y`, whose union with `{y}` lies in `A`, is a neighbourhood of `y` in
`A`, and has diameter `< r`. -/
def IsFanAt (A : Set E) (y : E) (r : ℝ) (Y : Set E) : Prop :=
  ∃ (n : ℕ) (z : Fin n → E), (∀ k, z k ≠ y) ∧ Y = insert y (⋃ k, segment ℝ y (z k)) ∧ Y ⊆ A ∧
    (∀ k l, k ≠ l → segment ℝ y (z k) ∩ segment ℝ y (z l) = {y}) ∧ Y ∈ 𝓝[A] y ∧
    Metric.diam Y < r

end Defs

/-- **`M` separates `P` from `Q` in `Y`**: two open sets cover `Y \ M`, are disjoint on `Y \ M`,
and contain `P` and `Q` respectively. -/
def SeparatesIn {α : Type*} [TopologicalSpace α] (Y M P Q : Set α) : Prop :=
  ∃ U V : Set α, IsOpen U ∧ IsOpen V ∧ Y \ M ⊆ U ∪ V ∧ U ∩ V ∩ (Y \ M) = ∅ ∧ P ⊆ U ∧ Q ⊆ V

/-- **H–O Theorem 20, forward direction ("only if"), for PL graphs** (p. 209). A map `f` of a
hereditarily indecomposable compactum to a PL graph `G` is approximated by the first coordinate
of a map into any open `U` containing a separator `M ⊆ G × (0, 1)` of `G × {0}` from `G × {1}`.
The open input of this batch's assembly; to be proved in later batches. -/
def HOThm20 : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X], IsHereditarilyIndecomposable (univ : Set X) →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Set E), IsPLGraph G →
    ∀ f : X → E, Continuous f → (∀ x, f x ∈ G) →
    ∀ M : Set (E × ℝ), M ⊆ G ×ˢ Ioo (0 : ℝ) 1 →
      SeparatesIn (G ×ˢ Icc (0 : ℝ) 1) M (G ×ˢ ({0} : Set ℝ)) (G ×ˢ ({1} : Set ℝ)) →
    ∀ U : Set (E × ℝ), IsOpen U → M ⊆ U →
    ∀ ε : ℝ, 0 < ε → ∃ h : X → E × ℝ, Continuous h ∧ (∀ x, h x ∈ U ∩ (G ×ˢ Icc (0 : ℝ) 1)) ∧
      ∀ x, dist (f x) (h x).1 < ε

section Lemmas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A PL graph is compact. -/
theorem IsPLGraph.isCompact {G : Set E} (hG : IsPLGraph G) : IsCompact G := by
  obtain ⟨S, -, rfl, -⟩ := hG
  exact S.isCompact_biUnion fun s _ => by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (AffineMap.lineMap_continuous)

/-- Segment parametrization `x + u • (y - x)`, `u ∈ [0, 1]`. -/
theorem mem_segment_iff_param {x y p : E} :
    p ∈ segment ℝ x y ↔ ∃ u ∈ Icc (0 : ℝ) 1, p = x + u • (y - x) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩

/-- A segment through `y` is the union of its two halves at `y`. -/
theorem segment_subset_union_of_mem {a b y : E} (hy : y ∈ segment ℝ a b) :
    segment ℝ a b ⊆ segment ℝ y a ∪ segment ℝ y b := by
  intro p hp
  obtain ⟨l, ⟨hl0, hl1⟩, rfl⟩ := mem_segment_iff_param.1 hy
  obtain ⟨u, ⟨hu0, hu1⟩, rfl⟩ := mem_segment_iff_param.1 hp
  rcases le_total u l with h | h
  · left
    rcases eq_or_lt_of_le hl0 with h0 | h0
    · subst h0
      have : u = 0 := le_antisymm h hu0
      subst this
      exact left_mem_segment _ _ _
    · refine mem_segment_iff_param.2 ⟨(l - u) / l, ⟨div_nonneg (by linarith) h0.le,
        (div_le_one h0).2 (by linarith)⟩, ?_⟩
      have : a - (a + l • (b - a)) = (-l) • (b - a) := by
        rw [neg_smul]; abel
      rw [this, smul_smul, add_assoc, ← add_smul]
      congr 2
      field_simp
      ring
  · right
    rcases eq_or_lt_of_le hl1 with h1 | h1
    · subst h1
      have : u = 1 := le_antisymm hu1 h
      subst this
      exact left_mem_segment _ _ _
    · refine mem_segment_iff_param.2 ⟨(u - l) / (1 - l), ⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith)⟩, ?_⟩
      have : b - (a + l • (b - a)) = (1 - l) • (b - a) := by
        rw [sub_smul, one_smul]; abel
      rw [this, smul_smul, add_assoc, ← add_smul]
      have h1' : (1 : ℝ) - l ≠ 0 := by linarith
      congr 2
      field_simp
      ring

/-- Two halves of a segment at an inner point `y` meet only at `y`. -/
theorem eq_of_mem_segment_halves {a b y p : E} (hy : y ∈ segment ℝ a b) (hya : y ≠ a)
    (hyb : y ≠ b) (hpa : p ∈ segment ℝ y a) (hpb : p ∈ segment ℝ y b) : p = y := by
  obtain ⟨l, ⟨hl0, hl1⟩, rfl⟩ := mem_segment_iff_param.1 hy
  obtain ⟨u, ⟨hu0, hu1⟩, hu⟩ := mem_segment_iff_param.1 hpa
  obtain ⟨v, ⟨hv0, hv1⟩, hv⟩ := mem_segment_iff_param.1 hpb
  have hl0' : l ≠ 0 := by rintro rfl; simp at hya
  have hl1' : l ≠ 1 := by rintro rfl; apply hyb; simp
  have hab : b - a ≠ 0 := by
    intro h; apply hya; rw [h, smul_zero, add_zero]
  have e1 : a - (a + l • (b - a)) = (-l) • (b - a) := by rw [neg_smul]; abel
  have e2 : b - (a + l • (b - a)) = (1 - l) • (b - a) := by rw [sub_smul, one_smul]; abel
  rw [e1, smul_smul] at hu
  rw [e2, smul_smul] at hv
  have h3 : (u * -l) • (b - a) = (v * (1 - l)) • (b - a) := add_left_cancel (hu.symm.trans hv)
  have key : (u * l + v * (1 - l)) • (b - a) = 0 := by
    rw [show u * l + v * (1 - l) = v * (1 - l) - u * (-l) by ring, sub_smul, h3, sub_self]
  rcases smul_eq_zero.1 key with h | h
  · have hul : u * l = 0 := by nlinarith [mul_nonneg hu0 hl0, mul_nonneg hv0 (sub_nonneg.2 hl1)]
    have hu' : u = 0 := by
      rcases mul_eq_zero.1 hul with h' | h'
      · exact h'
      · exact absurd h' hl0'
    rw [hu, hu', zero_mul, zero_smul, add_zero]
  · exact absurd h hab
/-- Every point of a PL graph has fans of every diameter (commission §2). -/
theorem IsPLGraph.exists_fan {G : Set E} (hG : IsPLGraph G) {y : E} (hy : y ∈ G) {r : ℝ}
    (hr : 0 < r) : ∃ Y, IsFanAt G y r Y := by
  classical
  obtain ⟨S, -, rfl, hdis⟩ := hG
  set V : Finset E := S.image Prod.fst ∪ S.image Prod.snd with hVdef
  have hV : ∀ s ∈ S, s.1 ∈ V ∧ s.2 ∈ V := fun s hs =>
    ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)⟩
  set Z : Finset E := V.filter
    (fun w => w ≠ y ∧ ∃ s ∈ S, y ∈ segment ℝ s.1 s.2 ∧ (w = s.1 ∨ w = s.2)) with hZdef
  have hc_ev : ∀ᶠ c in 𝓝[>] (0 : ℝ), c < r / 2 ∧ (∀ v ∈ V, v ≠ y → c < ‖v - y‖) ∧
      (∀ s ∈ S, y ∉ segment ℝ s.1 s.2 → c < infDist y (segment ℝ s.1 s.2)) := by
    refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)
    · exact nhdsWithin_le_nhds (eventually_lt_nhds (by linarith))
    · refine (Filter.eventually_all_finset _).2 fun v _ => ?_
      by_cases hv : v = y
      · exact Filter.Eventually.of_forall fun _ h => absurd hv h
      · have : 0 < ‖v - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hv)
        exact nhdsWithin_le_nhds ((eventually_lt_nhds this).mono fun _ h _ => h)
    · refine (Filter.eventually_all_finset _).2 fun s _ => ?_
      by_cases hs : y ∈ segment ℝ s.1 s.2
      · exact Filter.Eventually.of_forall fun _ h => absurd hs h
      · have hcl : IsClosed (segment ℝ s.1 s.2) := by
          rw [segment_eq_image_lineMap]
          exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
        have : 0 < infDist y (segment ℝ s.1 s.2) :=
          (hcl.notMem_iff_infDist_pos ⟨s.1, left_mem_segment _ _ _⟩).1 hs
        exact nhdsWithin_le_nhds ((eventually_lt_nhds this).mono fun _ h _ => h)
  obtain ⟨c, ⟨hcr, hcV, hcS⟩, hc0⟩ := (hc_ev.and self_mem_nhdsWithin).exists
  have hc0 : (0 : ℝ) < c := hc0
  set zf : E → E := fun w => y + (c / ‖w - y‖) • (w - y) with hzf
  -- facts about `w ∈ Z`
  have hZ : ∀ w ∈ Z, w ≠ y ∧ c < ‖w - y‖ ∧ ∃ s ∈ S, segment ℝ y w ⊆ segment ℝ s.1 s.2 ∧
      y ∈ segment ℝ s.1 s.2 ∧ (w = s.1 ∨ w = s.2) := by
    intro w hw
    rw [hZdef, Finset.mem_filter] at hw
    obtain ⟨hwV, hwy, s, hs, hys, hws⟩ := hw
    refine ⟨hwy, hcV w hwV hwy, s, hs, ?_, hys, hws⟩
    have hwseg : w ∈ segment ℝ s.1 s.2 := by
      rcases hws with rfl | rfl
      · exact left_mem_segment _ _ _
      · exact right_mem_segment _ _ _
    exact (convex_segment _ _).segment_subset hys hwseg
  have hz_seg : ∀ w ∈ Z, zf w ∈ segment ℝ y w := by
    intro w hw
    obtain ⟨-, hcw, -⟩ := hZ w hw
    have hpos : 0 < ‖w - y‖ := hc0.trans hcw
    exact mem_segment_iff_param.2 ⟨c / ‖w - y‖, ⟨(div_pos hc0 hpos).le,
      (div_le_one hpos).2 hcw.le⟩, rfl⟩
  have hz_norm : ∀ w ∈ Z, ‖zf w - y‖ = c := by
    intro w hw
    obtain ⟨-, hcw, -⟩ := hZ w hw
    have hpos : 0 < ‖w - y‖ := hc0.trans hcw
    simp only [hzf, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hc0 hpos)]
    field_simp
  have hzz : ∀ w ∈ Z, segment ℝ y (zf w) ⊆ segment ℝ y w := fun w hw =>
    (convex_segment _ _).segment_subset (left_mem_segment _ _ _) (hz_seg w hw)
  have hz_ball : ∀ w ∈ Z, segment ℝ y (zf w) ⊆ closedBall y c := fun w hw =>
    (convex_closedBall y c).segment_subset (mem_closedBall_self hc0.le)
      (by rw [mem_closedBall, dist_eq_norm, hz_norm w hw])
  -- the set equality
  have hYeq : (⋃ s ∈ S, segment ℝ s.1 s.2) ∩ closedBall y c =
      insert y (⋃ w ∈ Z, segment ℝ y (zf w)) := by
    ext p
    constructor
    · rintro ⟨hpG, hpc⟩
      rw [mem_closedBall, dist_eq_norm] at hpc
      obtain ⟨s, hs, hps⟩ := mem_iUnion₂.1 hpG
      by_cases hys : y ∈ segment ℝ s.1 s.2
      · have key : ∀ w, (w = s.1 ∨ w = s.2) → p ∈ segment ℝ y w →
            p ∈ insert y (⋃ w ∈ Z, segment ℝ y (zf w)) := by
          intro w hw hpw
          by_cases hwy : w = y
          · subst hwy
            rw [segment_same] at hpw
            exact Or.inl hpw
          · have hwZ : w ∈ Z := by
              rw [hZdef, Finset.mem_filter]
              refine ⟨?_, hwy, s, hs, hys, hw⟩
              rcases hw with rfl | rfl
              · exact (hV s hs).1
              · exact (hV s hs).2
            obtain ⟨-, hcw, -⟩ := hZ w hwZ
            have hpos : 0 < ‖w - y‖ := hc0.trans hcw
            obtain ⟨u, ⟨hu0, hu1⟩, rfl⟩ := mem_segment_iff_param.1 hpw
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu0] at hpc
            refine Or.inr (mem_iUnion₂.2 ⟨w, hwZ, mem_segment_iff_param.2
              ⟨u * ‖w - y‖ / c, ⟨div_nonneg (mul_nonneg hu0 hpos.le) hc0.le,
                (div_le_one hc0).2 hpc⟩, ?_⟩⟩)
            simp only [hzf, add_sub_cancel_left, smul_smul]
            congr 2
            field_simp
        rcases segment_subset_union_of_mem hys hps with h | h
        · exact key _ (Or.inl rfl) h
        · exact key _ (Or.inr rfl) h
      · exfalso
        have h1 := hcS s hs hys
        have h2 : infDist y (segment ℝ s.1 s.2) ≤ dist y p := infDist_le_dist_of_mem hps
        rw [dist_comm, dist_eq_norm] at h2
        linarith
    · rintro (rfl | hp)
      · exact ⟨hy, mem_closedBall_self hc0.le⟩
      · obtain ⟨w, hw, hpw⟩ := mem_iUnion₂.1 hp
        obtain ⟨-, -, s, hs, hsub, -⟩ := hZ w hw
        exact ⟨mem_iUnion₂.2 ⟨s, hs, hsub (hzz w hw hpw)⟩, hz_ball w hw hpw⟩
  -- indexing
  set e := Z.equivFin
  refine ⟨(⋃ s ∈ S, segment ℝ s.1 s.2) ∩ closedBall y c, Z.card, fun k => zf (e.symm k),
    fun k => ?_, ?_, inter_subset_left, fun k l hkl => ?_,
    inter_mem_nhdsWithin _ (closedBall_mem_nhds y hc0), ?_⟩
  · intro h
    have := hz_norm _ (e.symm k).2
    simp only at h
    rw [h, sub_self, norm_zero] at this
    exact hc0.ne this
  · rw [hYeq]
    ext p
    simp only [mem_insert_iff, mem_iUnion]
    constructor
    · rintro (h | ⟨w, hw, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨e ⟨w, hw⟩, by simpa using h⟩
    · rintro (h | ⟨k, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨_, (e.symm k).2, h⟩
  · set w := (e.symm k : E)
    set w' := (e.symm l : E)
    have hww : w ≠ w' := by
      intro h
      exact hkl (e.symm.injective (Subtype.ext h))
    have hw : w ∈ Z := (e.symm k).2
    have hw' : w' ∈ Z := (e.symm l).2
    obtain ⟨hwy, -, s, hs, hsub, hys, hws⟩ := hZ w hw
    obtain ⟨hwy', -, s', hs', hsub', hys', hws'⟩ := hZ w' hw'
    ext p
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hp1, hp2⟩
      by_contra hpy
      have hps : p ∈ segment ℝ s.1 s.2 := hsub (hzz w hw hp1)
      have hps' : p ∈ segment ℝ s'.1 s'.2 := hsub' (hzz w' hw' hp2)
      have hpc : ‖p - y‖ ≤ c := by
        have := hz_ball w hw hp1
        rwa [mem_closedBall, dist_eq_norm] at this
      by_cases hss : s = s'
      · subst hss
        have hhalf : ∀ a b, y ∈ segment ℝ a b → y ≠ a → y ≠ b → p ∈ segment ℝ y a →
            p ∈ segment ℝ y b → False := fun a b h1 h2 h3 h4 h5 =>
          hpy (eq_of_mem_segment_halves h1 h2 h3 h4 h5)
        rcases hws with h1 | h1 <;> rcases hws' with h2 | h2
        · exact hww (h1.trans h2.symm)
        · have hys2 : y ∈ segment ℝ w w' := by rw [h1, h2]; exact hys
          exact hhalf _ _ hys2 (Ne.symm hwy) (Ne.symm hwy') (hzz _ hw hp1) (hzz _ hw' hp2)
        · have hys2 : y ∈ segment ℝ w w' := by rw [h1, h2, segment_symm]; exact hys
          exact hhalf _ _ hys2 (Ne.symm hwy) (Ne.symm hwy') (hzz _ hw hp1) (hzz _ hw' hp2)
        · exact hww (h1.trans h2.symm)
      · have := (hdis s hs s' hs' hss ⟨hps, hps'⟩).1
        have hpV : p ∈ V := by
          rcases this with h | h
          · rw [h]; exact (hV s hs).1
          · rw [mem_singleton_iff] at h; rw [h]; exact (hV s hs).2
        have := hcV p hpV hpy
        linarith
    · rintro rfl
      exact ⟨left_mem_segment _ _ _, left_mem_segment _ _ _⟩
  · calc Metric.diam ((⋃ s ∈ S, segment ℝ s.1 s.2) ∩ closedBall y c)
        ≤ Metric.diam (closedBall y c) :=
          Metric.diam_mono inter_subset_right isBounded_closedBall
      _ ≤ 2 * c := Metric.diam_closedBall hc0.le
      _ < r := by linarith

end Lemmas

/-- Separation from a closed splitting (take `U = R₁ᶜ`, `V = R₀ᶜ`). -/
theorem separatesIn_of_closed {α : Type*} [TopologicalSpace α] {Y M P Q R₀ R₁ : Set α}
    (h₀ : IsClosed R₀) (h₁ : IsClosed R₁) (hdisj : Disjoint R₀ R₁) (hcov : Y \ M ⊆ R₀ ∪ R₁)
    (hP : P ⊆ R₀) (hQ : Q ⊆ R₁) : SeparatesIn Y M P Q := by
  refine ⟨R₁ᶜ, R₀ᶜ, h₁.isOpen_compl, h₀.isOpen_compl, fun x _ => ?_, ?_,
    fun x hx => Set.disjoint_left.1 hdisj (hP hx), fun x hx => Set.disjoint_right.1 hdisj (hQ hx)⟩
  · by_contra h
    simp only [mem_union, mem_compl_iff, not_or, not_not] at h
    exact Set.disjoint_left.1 hdisj h.2 h.1
  · ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_diff, mem_empty_iff_false, iff_false]
    rintro ⟨⟨h1, h0⟩, hY, hM⟩
    rcases hcov ⟨hY, hM⟩ with h | h
    · exact h0 h
    · exact h1 h

end HPC.HO16
