import HPC.Moore.M25Plane

/-!
# Batch 151, item A (part 1): the two sides of a continuum crossing a strip

The universal cover of the closed square annulus is the closed strip `Strip a b` (`a ≤ y ≤ b`). A
*crossing set* (`IsCross`) is a continuum in the strip meeting both edges. Its *right side* `Rc`
and *left side* `Lc` are the components of `Strip a b \ L` containing the points of the strip to
the right, resp. to the left, of `L`; `NotR` is the rest of `Strip a b \ L` (the left component
and the pockets).

* `GoodSide.union_isPreconnected`: each side together with `L` is connected (the side reaches `L`);
* `lc_disjoint_rc` — **strip separation**: the two sides are disjoint. The proof closes a compact
  connected set joining the far left to the far right into a loop below the strip; `L` joins a
  point below the strip to a point above it off the loop, so by the component criterion
  `HPC.Moore.exists_log_of_mem_component` the loop carries a continuous argument about the lower
  point, which is impossible where the loop crosses the downward ray from it.
-/

namespace HPC.Jones.Sector

open Set Topology Metric HPC.Plane

/-- The closed horizontal strip `a ≤ y ≤ b` of `ℝ × ℝ`. -/
def Strip (a b : ℝ) : Set (ℝ × ℝ) := {x | a ≤ x.2 ∧ x.2 ≤ b}

theorem convex_strip (a b : ℝ) : Convex ℝ (Strip a b) := by
  intro x hx y hy s t hs ht hst
  simp only [Strip, mem_setOf_eq, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at *
  have e1 : s * a + t * a = a := by rw [← add_mul, hst, one_mul]
  have e2 : s * b + t * b = b := by rw [← add_mul, hst, one_mul]
  constructor
  · linarith [mul_le_mul_of_nonneg_left hx.1 hs, mul_le_mul_of_nonneg_left hy.1 ht]
  · linarith [mul_le_mul_of_nonneg_left hx.2 hs, mul_le_mul_of_nonneg_left hy.2 ht]

theorem isClosed_strip (a b : ℝ) : IsClosed (Strip a b) :=
  (isClosed_le continuous_const continuous_snd).inter (isClosed_le continuous_snd continuous_const)

/-- A **crossing set** of the strip: a continuum in the strip meeting both edges. -/
structure IsCross (a b : ℝ) (L : Set (ℝ × ℝ)) : Prop where
  compact : IsCompact L
  conn : IsConnected L
  sub : L ⊆ Strip a b
  bot : ∃ z ∈ L, z.2 = a
  top : ∃ z ∈ L, z.2 = b

theorem IsCross.le {a b : ℝ} {L : Set (ℝ × ℝ)} (h : IsCross a b L) : a ≤ b := by
  obtain ⟨z, hz, hza⟩ := h.bot
  have := h.sub hz
  exact hza ▸ this.2

/-- The component of `Strip a b \ L` containing the points of the strip satisfying `P`. -/
def SideOf (a b : ℝ) (L : Set (ℝ × ℝ)) (P : ℝ × ℝ → Prop) : Set (ℝ × ℝ) :=
  {y | ∃ x ∈ Strip a b, P x ∧ y ∈ connectedComponentIn (Strip a b \ L) x}

/-- Points to the right of `L`. -/
def FarR (L : Set (ℝ × ℝ)) (x : ℝ × ℝ) : Prop := ∀ z ∈ L, z.1 < x.1

/-- Points to the left of `L`. -/
def FarL (L : Set (ℝ × ℝ)) (x : ℝ × ℝ) : Prop := ∀ z ∈ L, x.1 < z.1

/-- The **right side** of `L`: the component of `Strip a b \ L` reaching to the right. -/
def Rc (a b : ℝ) (L : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := SideOf a b L (FarR L)

/-- The **left side** of `L`: the component of `Strip a b \ L` reaching to the left. -/
def Lc (a b : ℝ) (L : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := SideOf a b L (FarL L)

/-- Everything of `Strip a b \ L` not on the right side (the left component and the pockets). -/
def NotR (a b : ℝ) (L : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := Strip a b \ (L ∪ Rc a b L)

/-- A side predicate: its points in the strip form a preconnected set missing `L`. -/
structure GoodSide (a b : ℝ) (L : Set (ℝ × ℝ)) (P : ℝ × ℝ → Prop) : Prop where
  conn : IsPreconnected {x | x ∈ Strip a b ∧ P x}
  miss : ∀ x, P x → x ∉ L
  ex : ∃ x ∈ Strip a b, P x

section Generic

variable {a b : ℝ} {L : Set (ℝ × ℝ)} {P : ℝ × ℝ → Prop}

theorem GoodSide.mem_comp (h : GoodSide a b L P) {x y : ℝ × ℝ} (hx : x ∈ Strip a b) (hPx : P x)
    (hy : y ∈ Strip a b) (hPy : P y) : y ∈ connectedComponentIn (Strip a b \ L) x :=
  h.conn.subset_connectedComponentIn (show x ∈ {x | x ∈ Strip a b ∧ P x} from ⟨hx, hPx⟩)
    (fun w hw => show w ∈ Strip a b \ L from ⟨hw.1, h.miss w hw.2⟩) (show y ∈ {x | x ∈ Strip a b ∧ P x} from ⟨hy, hPy⟩)

theorem GoodSide.eq (h : GoodSide a b L P) {x : ℝ × ℝ} (hx : x ∈ Strip a b) (hPx : P x) :
    SideOf a b L P = connectedComponentIn (Strip a b \ L) x := by
  ext y
  constructor
  · rintro ⟨x', hx', hPx', hy⟩
    rwa [connectedComponentIn_eq (h.mem_comp hx' hPx' hx hPx)] at hy
  · intro hy
    exact ⟨x, hx, hPx, hy⟩

theorem sideOf_subset : SideOf a b L P ⊆ Strip a b \ L := by
  rintro y ⟨x, -, -, hy⟩
  exact connectedComponentIn_subset _ _ hy

theorem GoodSide.mem (h : GoodSide a b L P) {x : ℝ × ℝ} (hx : x ∈ Strip a b) (hPx : P x) :
    x ∈ SideOf a b L P :=
  ⟨x, hx, hPx, mem_connectedComponentIn (show x ∈ Strip a b \ L from ⟨hx, h.miss x hPx⟩)⟩

theorem GoodSide.nonempty (h : GoodSide a b L P) : (SideOf a b L P).Nonempty := by
  obtain ⟨x, hx, hPx⟩ := h.ex
  exact ⟨x, h.mem hx hPx⟩

theorem GoodSide.isPreconnected (h : GoodSide a b L P) : IsPreconnected (SideOf a b L P) := by
  obtain ⟨x, hx, hPx⟩ := h.ex
  rw [h.eq hx hPx]
  exact isPreconnected_connectedComponentIn

/-- A preconnected subset of `Strip a b \ L` meeting a side lies in it. -/
theorem sideOf_absorb {X : Set (ℝ × ℝ)} (hX : IsPreconnected X) (hXs : X ⊆ Strip a b \ L)
    (hne : (X ∩ SideOf a b L P).Nonempty) : X ⊆ SideOf a b L P := by
  obtain ⟨y, hyX, x, hx, hPx, hy⟩ := hne
  intro w hw
  refine ⟨x, hx, hPx, ?_⟩
  rw [connectedComponentIn_eq hy]
  exact hX.subset_connectedComponentIn hyX hXs hw

/-- Small balls (intersected with the strip) about a point off a closed set are preconnected and
miss the set. -/
theorem exists_ball_strip (hL : IsClosed L) {y : ℝ × ℝ} (hy : y ∉ L) :
    ∃ η > 0, IsPreconnected (ball y η ∩ Strip a b) ∧ ball y η ∩ L = ∅ := by
  obtain ⟨η, hη, hsub⟩ := Metric.isOpen_iff.1 hL.isOpen_compl y hy
  refine ⟨η, hη, ((convex_ball y η).inter (convex_strip a b)).isPreconnected, ?_⟩
  ext w
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  exact fun hw => hsub hw

theorem sideOf_open_rel (hL : IsClosed L) {y : ℝ × ℝ} (hy : y ∈ SideOf a b L P) :
    ∃ η > 0, ball y η ∩ Strip a b ⊆ SideOf a b L P := by
  have hyL := sideOf_subset hy
  obtain ⟨η, hη, hc, hdisj⟩ := exists_ball_strip (a := a) (b := b) hL hyL.2
  refine ⟨η, hη, sideOf_absorb hc (fun w hw => ⟨hw.2, fun hwL => ?_⟩)
    ⟨y, (⟨mem_ball_self hη, hyL.1⟩ : y ∈ ball y η ∩ Strip a b), hy⟩⟩
  have : w ∈ ball y η ∩ L := ⟨hw.1, hwL⟩
  rw [hdisj] at this
  exact this

/-- The side reaches `L`: some point of `L` is in its closure. -/
theorem GoodSide.exists_mem_closure (h : GoodSide a b L P) (hL : IsCross a b L) :
    ∃ x ∈ L, x ∈ closure (SideOf a b L P) := by
  set S := SideOf a b L P
  have hLc : IsClosed L := hL.compact.isClosed
  have hex : ∃ x ∈ L, x ∈ closure S := by
    by_contra hcon
    push_neg at hcon
    -- `S` is closed
    have hScl : closure S ⊆ S := by
      intro y hy
      have hyst : y ∈ Strip a b := closure_minimal (sideOf_subset.trans diff_subset)
        (isClosed_strip a b) hy
      have hyL : y ∉ L := fun h' => hcon y h' hy
      obtain ⟨η, hη, hc, hdisj⟩ := exists_ball_strip (a := a) (b := b) hLc hyL
      obtain ⟨w, hwS, hwd⟩ := Metric.mem_closure_iff.1 hy η hη
      have hsub := sideOf_absorb hc (L := L) (P := P) (fun w' hw' => ⟨hw'.2, fun hwL => by
        have : w' ∈ ball y η ∩ L := ⟨hw'.1, hwL⟩
        rw [hdisj] at this; exact this⟩)
        ⟨w, ⟨by rw [mem_ball, dist_comm]; exact hwd, (sideOf_subset hwS).1⟩, hwS⟩
      exact hsub ⟨mem_ball_self hη, hyst⟩
    have hSc : IsClosed S := closure_subset_iff_isClosed.1 hScl
    have hU : IsOpen (S ∪ (Strip a b)ᶜ) := by
      rw [Metric.isOpen_iff]
      rintro y (hy | hy)
      · obtain ⟨η, hη, hsub⟩ := sideOf_open_rel hLc hy
        refine ⟨η, hη, fun w hw => ?_⟩
        by_cases hws : w ∈ Strip a b
        · exact Or.inl (hsub ⟨hw, hws⟩)
        · exact Or.inr hws
      · obtain ⟨η, hη, hsub⟩ := Metric.isOpen_iff.1 (isClosed_strip a b).isOpen_compl y hy
        exact ⟨η, hη, fun w hw => Or.inr (hsub hw)⟩
    have hconn : IsPreconnected (Strip a b) := (convex_strip a b).isPreconnected
    rcases isPreconnected_iff_subset_of_disjoint.1 hconn _ _ hU hSc.isOpen_compl
      (fun w _ => by by_cases hw : w ∈ S <;> simp [hw])
      (by ext w; simp only [mem_inter_iff, mem_union, mem_compl_iff, mem_empty_iff_false,
            iff_false, not_and]; tauto) with h1 | h1
    · obtain ⟨z, hz⟩ := hL.conn.nonempty
      rcases h1 (hL.sub hz) with h2 | h2
      · exact (sideOf_subset h2).2 hz
      · exact h2 (hL.sub hz)
    · obtain ⟨z, hz⟩ := h.nonempty
      exact h1 ((sideOf_subset hz).1) hz
  exact hex

/-- The side together with `L` is preconnected (the side reaches `L`). -/
theorem GoodSide.union_isPreconnected (h : GoodSide a b L P) (hL : IsCross a b L) :
    IsPreconnected (SideOf a b L P ∪ L) := by
  set S := SideOf a b L P
  have hex := h.exists_mem_closure hL
  obtain ⟨x, hxL, hxS⟩ := hex
  have h1 : IsPreconnected (S ∪ {x}) :=
    h.isPreconnected.subset_closure subset_union_left
      (union_subset subset_closure (singleton_subset_iff.2 hxS))
  have h2 := h1.union x (Or.inr rfl) hxL hL.conn.isPreconnected
  have : S ∪ {x} ∪ L = S ∪ L := by
    ext w; simp only [mem_union, mem_singleton_iff]
    constructor
    · rintro ((h | rfl) | h) <;> tauto
    · tauto
  rwa [this] at h2

end Generic

/-! ### The two good sides of a crossing set -/

section Sides

variable {a b : ℝ} {L : Set (ℝ × ℝ)}

theorem goodSide_farR (hL : IsCross a b L) : GoodSide a b L (FarR L) where
  conn := by
    refine Convex.isPreconnected ?_
    intro x hx y hy s t hs ht hst
    refine ⟨convex_strip a b hx.1 hy.1 hs ht hst, fun z hz => ?_⟩
    have h1 := hx.2 z hz
    have h2 := hy.2 z hz
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    have e1 : s * z.1 + t * z.1 = z.1 := by rw [← add_mul, hst, one_mul]
    rcases hs.lt_or_eq with hs' | hs'
    · nlinarith [mul_pos hs' (sub_pos.2 h1), mul_nonneg ht (sub_nonneg.2 h2.le)]
    · subst hs'
      simp only [zero_add] at hst
      subst hst
      simp only [zero_mul, one_mul, zero_add]
      exact h2
  miss := fun x hx hxL => lt_irrefl _ (hx x hxL)
  ex := by
    obtain ⟨M, hM⟩ := (hL.compact.image continuous_fst).isBounded.bddAbove
    refine ⟨(M + 1, a), ⟨le_rfl, hL.le⟩, fun z hz => ?_⟩
    have := hM (mem_image_of_mem Prod.fst hz)
    simp only
    linarith

theorem goodSide_farL (hL : IsCross a b L) : GoodSide a b L (FarL L) where
  conn := by
    refine Convex.isPreconnected ?_
    intro x hx y hy s t hs ht hst
    refine ⟨convex_strip a b hx.1 hy.1 hs ht hst, fun z hz => ?_⟩
    have h1 := hx.2 z hz
    have h2 := hy.2 z hz
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    have e1 : s * z.1 + t * z.1 = z.1 := by rw [← add_mul, hst, one_mul]
    rcases hs.lt_or_eq with hs' | hs'
    · nlinarith [mul_pos hs' (sub_pos.2 h1), mul_nonneg ht (sub_nonneg.2 h2.le)]
    · subst hs'
      simp only [zero_add] at hst
      subst hst
      simp only [zero_mul, one_mul, zero_add]
      exact h2
  miss := fun x hx hxL => lt_irrefl _ (hx x hxL)
  ex := by
    obtain ⟨M, hM⟩ := (hL.compact.image continuous_fst).isBounded.bddBelow
    refine ⟨(M - 1, a), ⟨le_rfl, hL.le⟩, fun z hz => ?_⟩
    have := hM (mem_image_of_mem Prod.fst hz)
    simp only
    linarith

end Sides


/-! ### The strip separation theorem -/

section Separation

open Complex

variable {a b : ℝ} {L : Set (ℝ × ℝ)}

/-- An integer-valued continuous function on a preconnected set is constant. -/
theorem eq_of_int_valued {S : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ} (hS : IsPreconnected S)
    (hf : ContinuousOn f S) (hint : ∀ z ∈ S, ∃ n : ℤ, f z = n) {z₁ z₂ : ℝ × ℝ} (h₁ : z₁ ∈ S)
    (h₂ : z₂ ∈ S) : f z₁ = f z₂ := by
  have himg : IsPreconnected (f '' S) := hS.image f hf
  have key : ∀ {u v : ℝ × ℝ}, u ∈ S → v ∈ S → ¬ f u < f v := by
    intro u v hu hv hlt
    obtain ⟨m, hm⟩ := hint u hu
    obtain ⟨n, hn⟩ := hint v hv
    have hmn : m < n := by rw [hm, hn] at hlt; exact_mod_cast hlt
    have hmem : ((m : ℝ) + 1 / 2) ∈ f '' S :=
      himg.Icc_subset (mem_image_of_mem f hu) (mem_image_of_mem f hv)
        ⟨by rw [hm]; linarith, by
          rw [hn]
          have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
          linarith⟩
    obtain ⟨w, hw, hfw⟩ := hmem
    obtain ⟨k, hk⟩ := hint w hw
    rw [hk] at hfw
    have h1 : (m : ℝ) < k := by linarith
    have h2 : (k : ℝ) < m + 1 := by linarith
    have h1' : m < k := by exact_mod_cast h1
    have h2' : k < m + 1 := by exact_mod_cast h2
    omega
  exact le_antisymm (not_lt.1 (key h₂ h₁)) (not_lt.1 (key h₁ h₂))

/-- Points of a component of `Strip a b \ L` (`L` closed) are joined by a compact connected subset
of `Strip a b \ L`. -/
theorem exists_compact_join (hL : IsClosed L) {x y : ℝ × ℝ} (hx : x ∈ Strip a b)
    (hy : y ∈ connectedComponentIn (Strip a b \ L) x) :
    ∃ Γ : Set (ℝ × ℝ), IsCompact Γ ∧ IsPreconnected Γ ∧ Γ ⊆ Strip a b \ L ∧ x ∈ Γ ∧ y ∈ Γ := by
  have hxL : x ∉ L := by
    by_contra hxL
    rw [connectedComponentIn_eq_empty (fun h => h.2 hxL)] at hy
    exact hy
  set π : ℝ × ℝ → ℝ × ℝ := fun z => (z.1, max a (min z.2 b)) with hπ
  have hab : a ≤ b := hx.1.trans hx.2
  have hπc : Continuous π := by fun_prop
  have hπs : ∀ z, π z ∈ Strip a b := fun z =>
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hπid : ∀ z ∈ Strip a b, π z = z := by
    intro z hz
    simp only [hπ]
    rw [min_eq_left hz.2, max_eq_right hz.1]
  set O := π ⁻¹' Lᶜ
  have hO : IsOpen O := hL.isOpen_compl.preimage hπc
  have hsub : Strip a b \ L ⊆ O := fun z hz => by
    show π z ∈ Lᶜ
    rw [hπid z hz.1]; exact hz.2
  have hyO : y ∈ connectedComponentIn O x := connectedComponentIn_mono x hsub hy
  have hxO : x ∈ O := hsub ⟨hx, hxL⟩
  have hC : IsPathConnected (connectedComponentIn O x) :=
    (hO.connectedComponentIn).isConnected_iff_isPathConnected.1
      (isConnected_connectedComponentIn_iff.2 hxO)
  have hj := hC.joinedIn x (mem_connectedComponentIn hxO) y hyO
  set γ := hj.somePath
  refine ⟨range (π ∘ γ), isCompact_range (hπc.comp γ.continuous),
    isPreconnected_range (hπc.comp γ.continuous), ?_, ⟨0, ?_⟩, ⟨1, ?_⟩⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨hπs _, connectedComponentIn_subset _ _ (hj.somePath_mem t)⟩
  · simp only [Function.comp_apply, Path.source, γ]; exact hπid x hx
  · simp only [Function.comp_apply, Path.target, γ]
    exact hπid y ((connectedComponentIn_subset _ _ hy).1)

/-- **No compact connected set in `Strip a b \ L` joins the far left to the far right**, `L` a
crossing set. The loop formed by it and three segments below the strip would carry a continuous
argument around a point below the strip (the component criterion `exists_log_of_mem_component`,
since `L` joins that point to a point above the strip), which is impossible at the point where the
loop crosses the downward ray. -/
theorem no_cross_join (hab : a < b) (hL : IsCross a b L) {α β : ℝ} (hα : FarL L (α, a))
    (hβ : FarR L (β, a)) {Γ : Set (ℝ × ℝ)} (hΓc : IsCompact Γ) (hΓp : IsPreconnected Γ)
    (hΓs : Γ ⊆ Strip a b \ L) (hx : (α, a) ∈ Γ) (hy : (β, a) ∈ Γ) : False := by
  obtain ⟨p₀, hp₀L, hp₀a⟩ := hL.bot
  obtain ⟨q₀, hq₀L, hq₀b⟩ := hL.top
  set θp := p₀.1
  set θq := q₀.1
  have hαp : α < θp := hα p₀ hp₀L
  have hpβ : θp < β := hβ p₀ hp₀L
  have hαq : α < θq := hα q₀ hq₀L
  have hqβ : θq < β := hβ q₀ hq₀L
  set σl : Set (ℝ × ℝ) := {α} ×ˢ Icc (a - 1) a
  set σb : Set (ℝ × ℝ) := Icc α β ×ˢ {a - 1}
  set σr : Set (ℝ × ℝ) := {β} ×ˢ Icc (a - 1) a
  set Y := Γ ∪ σl ∪ σb ∪ σr with hY
  set p : ℝ × ℝ := (θp, a - 1 / 2)
  set q : ℝ × ℝ := (θq, b + 1)
  set m : ℝ × ℝ := (θp, a - 1)
  have hYc : IsCompact Y :=
    ((hΓc.union (isCompact_singleton.prod isCompact_Icc)).union
      (isCompact_Icc.prod isCompact_singleton)).union (isCompact_singleton.prod isCompact_Icc)
  have hYle : ∀ z ∈ Y, z.2 ≤ b := by
    rintro z (((hz | hz) | hz) | hz)
    · exact (hΓs hz).1.2
    · exact hz.2.2.trans hab.le
    · rw [hz.2]; linarith
    · exact hz.2.2.trans hab.le
  -- the connected set `Z` joins `p` to `q` off `Y`
  set Z := L ∪ ({θp} ×ˢ Icc (a - 1 / 2) a) ∪ ({θq} ×ˢ Icc b (b + 1))
  have hp₀ : p₀ = (θp, a) := by ext <;> simp [θp, hp₀a]
  have hq₀ : q₀ = (θq, b) := by ext <;> simp [θq, hq₀b]
  have hZ : IsPreconnected Z := by
    have h1 : IsPreconnected (L ∪ ({θp} ×ˢ Icc (a - 1 / 2) a)) :=
      hL.conn.isPreconnected.union p₀ hp₀L (by rw [hp₀]; exact ⟨rfl, by constructor <;> linarith⟩)
        (isPreconnected_singleton.prod isPreconnected_Icc)
    exact h1.union q₀ (Or.inl hq₀L) (by rw [hq₀]; exact ⟨rfl, by constructor <;> linarith⟩)
      (isPreconnected_singleton.prod isPreconnected_Icc)
  have hZY : Z ⊆ Yᶜ := by
    rintro z ((hzL | hz) | hz) hzY
    · have hzs := hL.sub hzL
      rcases hzY with ((hz' | hz') | hz') | hz'
      · exact (hΓs hz').2 hzL
      · have h1 := hα z hzL
        have h2 : z.1 = α := hz'.1
        simp only at h1; linarith
      · have := hz'.2; simp only [mem_singleton_iff] at this; linarith [hzs.1]
      · have h1 := hβ z hzL
        have h2 : z.1 = β := hz'.1
        simp only at h1; linarith
    · obtain ⟨hz1, hz2⟩ := hz
      simp only [mem_singleton_iff] at hz1
      rcases hzY with ((hz' | hz') | hz') | hz'
      · have hzs := (hΓs hz').1
        have hza : z.2 = a := le_antisymm hz2.2 hzs.1
        have : z = p₀ := by rw [hp₀]; ext <;> simp [hz1, hza]
        exact (hΓs hz').2 (this ▸ hp₀L)
      · have := hz'.1; simp only [mem_singleton_iff] at this; linarith
      · have := hz'.2; simp only [mem_singleton_iff] at this; linarith [hz2.1]
      · have := hz'.1; simp only [mem_singleton_iff] at this; linarith
    · obtain ⟨hz1, hz2⟩ := hz
      simp only [mem_singleton_iff] at hz1
      rcases hzY with ((hz' | hz') | hz') | hz'
      · have hzs := (hΓs hz').1
        have hzb : z.2 = b := le_antisymm hzs.2 hz2.1
        have : z = q₀ := by rw [hq₀]; ext <;> simp [hz1, hzb]
        exact (hΓs hz').2 (this ▸ hq₀L)
      · have := hz'.1; simp only [mem_singleton_iff] at this; linarith
      · have := hz'.2; simp only [mem_singleton_iff] at this; linarith [hz2.1]
      · have := hz'.1; simp only [mem_singleton_iff] at this; linarith
  have hpZ : p ∈ Z := Or.inl (Or.inr ⟨rfl, show (a - 1 / 2 : ℝ) ∈ Icc (a - 1 / 2) a from
    ⟨le_rfl, by linarith⟩⟩)
  have hqZ : q ∈ Z := Or.inr ⟨rfl, show (b + 1 : ℝ) ∈ Icc b (b + 1) from ⟨by linarith, le_rfl⟩⟩
  have hcomp : q ∈ connectedComponentIn Yᶜ p := hZ.subset_connectedComponentIn hpZ hZY hqZ
  obtain ⟨g, hgc, hge⟩ := HPC.Moore.exists_log_of_mem_component hYc.isClosed (hZY hpZ) hcomp
  -- a continuous argument of `z - p` on `Y`
  set h : ℝ × ℝ → ℂ := fun z => g z + Complex.log (toCpx z - toCpx q)
  have hqim : ∀ z ∈ Y, (toCpx z - toCpx q).im < 0 := by
    intro z hz
    simp only [toCpx, Complex.sub_im, q]
    linarith [hYle z hz]
  have hhc : ContinuousOn h Y := by
    refine hgc.add (ContinuousOn.clog ?_ ?_)
    · exact (continuous_toCpx.sub continuous_const).continuousOn
    · intro z hz
      exact Complex.mem_slitPlane_iff.2 (Or.inr (hqim z hz).ne)
  have hhe : ∀ z ∈ Y, Complex.exp (h z) = toCpx z - toCpx p := by
    intro z hz
    have hne : toCpx z - toCpx q ≠ 0 := fun h0 => by
      have := hqim z hz; rw [h0] at this; simp at this
    simp only [h, Complex.exp_add, hge z hz, Complex.exp_log hne]
    exact div_mul_cancel₀ _ hne
  -- the branch of the argument cut along the downward ray from `p`
  set φ : ℝ × ℝ → ℝ := fun z => Complex.arg (-I * (toCpx z - toCpx p))
  set Y' := Γ ∪ σl ∪ (Ico α θp ×ˢ {a - 1}) ∪ (Ioc θp β ×ˢ {a - 1}) ∪ σr
  have hY'Y : Y' ⊆ Y := by
    rintro z ((((hz | hz) | hz) | hz) | hz)
    · exact Or.inl (Or.inl (Or.inl hz))
    · exact Or.inl (Or.inl (Or.inr hz))
    · exact Or.inl (Or.inr ⟨⟨hz.1.1, hz.1.2.le.trans hpβ.le⟩, hz.2⟩)
    · exact Or.inl (Or.inr ⟨⟨hαp.le.trans hz.1.1.le, hz.1.2⟩, hz.2⟩)
    · exact Or.inr hz
  have hcalc : ∀ z : ℝ × ℝ, -I * (toCpx z - toCpx p) = ⟨z.2 - (a - 1 / 2), -(z.1 - θp)⟩ := by
    intro z
    apply Complex.ext <;> simp [toCpx, p]
  have hslit : ∀ z ∈ Y', -I * (toCpx z - toCpx p) ∈ slitPlane := by
    intro z hz
    rw [hcalc, Complex.mem_slitPlane_iff]
    rcases hz with ((((hz | hz) | hz) | hz) | hz)
    · left; simp only; linarith [(hΓs hz).1.1]
    · right; simp only [ne_eq, neg_eq_zero]
      have := hz.1; simp only [mem_singleton_iff] at this; rw [this]; linarith
    · right; simp only [ne_eq, neg_eq_zero]; linarith [hz.1.2]
    · right; simp only [ne_eq, neg_eq_zero]; linarith [hz.1.1]
    · right; simp only [ne_eq, neg_eq_zero]
      have := hz.1; simp only [mem_singleton_iff] at this; rw [this]; linarith
  have hφc : ContinuousOn φ Y' := by
    intro z hz
    exact ((Complex.continuousAt_arg (hslit z hz)).comp (f := fun z => -I * (toCpx z - toCpx p))
      (continuous_const.mul (continuous_toCpx.sub continuous_const)).continuousAt).continuousWithinAt
  have hpne : ∀ z ∈ Y, toCpx z - toCpx p ≠ 0 := fun z hz h0 => by
    have := hhe z hz; rw [h0] at this; exact Complex.exp_ne_zero _ this
  have hint : ∀ z ∈ Y', ∃ n : ℤ, ((h z).im - φ z - Real.pi / 2) / (2 * Real.pi) = n := by
    intro z hz
    have hzY := hY'Y hz
    set w := toCpx z - toCpx p
    have hw : w ≠ 0 := hpne z hzY
    obtain ⟨n, hn⟩ := Complex.log_exp_exists (h z)
    rw [hhe z hzY] at hn
    have harg : Complex.arg w = (h z).im + n * (2 * Real.pi) := by
      have := congrArg Complex.im hn
      rw [Complex.log_im] at this
      rw [this]; simp
    have hang := Complex.arg_mul_coe_angle (x := -I) (y := w) (by simp) hw
    rw [Complex.arg_neg_I, harg] at hang
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1
      (hang.trans (by rfl : _ = ((-(Real.pi / 2) + ((h z).im + n * (2 * Real.pi)) : ℝ) :
        Real.Angle)))
    refine ⟨-n - k, ?_⟩
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    field_simp
    push_cast
    simp only [φ]
    linarith
  -- the function is constant on `Y'`
  have hY'conn : IsPreconnected Y' := by
    have hl : IsPreconnected (Γ ∪ σl) :=
      hΓp.union (α, a) hx ⟨rfl, by constructor <;> linarith⟩
        (isPreconnected_singleton.prod isPreconnected_Icc)
    have hl2 : IsPreconnected (Γ ∪ σl ∪ (Ico α θp ×ˢ {a - 1})) :=
      hl.union (α, a - 1) (Or.inr ⟨rfl, by constructor <;> linarith⟩) ⟨⟨le_rfl, hαp⟩, rfl⟩
        (isPreconnected_Ico.prod isPreconnected_singleton)
    have hr : IsPreconnected ((Ioc θp β ×ˢ {a - 1}) ∪ σr) :=
      (isPreconnected_Ioc.prod isPreconnected_singleton).union (β, a - 1) ⟨⟨hpβ, le_rfl⟩, rfl⟩
        ⟨rfl, by constructor <;> linarith⟩ (isPreconnected_singleton.prod isPreconnected_Icc)
    have := hl2.union (β, a) (Or.inl (Or.inl hy)) (Or.inr ⟨rfl, by constructor <;> linarith⟩) hr
    simpa only [Y', union_assoc] using this
  set F : ℝ × ℝ → ℝ := fun z => ((h z).im - φ z - Real.pi / 2) / (2 * Real.pi)
  have hFc : ContinuousOn F Y' :=
    ((((Complex.continuous_im.comp_continuousOn (hhc.mono hY'Y))).sub hφc).sub
      continuousOn_const).div_const _
  -- approach the crossing point `m` from both sides along the bottom segment
  set δ := min (θp - α) (β - θp)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  set zl : ℝ → ℝ × ℝ := fun t => (θp - t, a - 1)
  set zr : ℝ → ℝ × ℝ := fun t => (θp + t, a - 1)
  have hzl : ∀ t, 0 < t → t < δ → zl t ∈ Y' := fun t ht htδ =>
    Or.inl (Or.inl (Or.inr ⟨⟨by linarith [min_le_left (θp - α) (β - θp)], by linarith⟩, rfl⟩))
  have hzr : ∀ t, 0 < t → t < δ → zr t ∈ Y' := fun t ht htδ =>
    Or.inl (Or.inr ⟨⟨by linarith, by linarith [min_le_right (θp - α) (β - θp)]⟩, rfl⟩)
  set c := F (zl (δ / 2))
  have hcl : ∀ t, 0 < t → t < δ → F (zl t) = c := fun t ht htδ =>
    eq_of_int_valued hY'conn hFc hint (hzl t ht htδ) (hzl _ (half_pos hδ) (half_lt_self hδ))
  have hcr : ∀ t, 0 < t → t < δ → F (zr t) = c := fun t ht htδ =>
    eq_of_int_valued hY'conn hFc hint (hzr t ht htδ) (hzl _ (half_pos hδ) (half_lt_self hδ))
  have hmY : m ∈ Y := Or.inl (Or.inr ⟨⟨hαp.le, hpβ.le⟩, rfl⟩)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < δ :=
    (eventually_nhdsWithin_of_forall fun t ht => ht).and
      (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ))
  have hlim_h : ∀ z : ℝ → ℝ × ℝ, Continuous z → z 0 = m → (∀ t, 0 < t → t < δ → z t ∈ Y) →
      Filter.Tendsto (fun t => (h (z t)).im) (𝓝[>] 0) (𝓝 (h m).im) := by
    intro z hz hz0 hzY
    have h1 : Filter.Tendsto z (𝓝[>] 0) (𝓝[Y] m) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, hev.mono fun t ht => hzY t ht.1 ht.2⟩
      rw [← hz0]; exact hz.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact (Complex.continuous_im.tendsto _).comp ((hhc m hmY).tendsto.comp h1)
  have hzlc : Continuous zl := by fun_prop
  have hzrc : Continuous zr := by fun_prop
  have hl := hlim_h zl hzlc (by simp [zl, m]) fun t ht htδ => hY'Y (hzl t ht htδ)
  have hr := hlim_h zr hzrc (by simp [zr, m]) fun t ht htδ => hY'Y (hzr t ht htδ)
  -- the argument tends to `π` from the left and to `-π` from the right
  have hφl : Filter.Tendsto (fun t => φ (zl t)) (𝓝[>] 0) (𝓝 Real.pi) := by
    have hw : ∀ t, -I * (toCpx (zl t) - toCpx p) = ⟨-1 / 2, t⟩ := by
      intro t; rw [hcalc]; apply Complex.ext <;> simp [zl]; ring
    simp only [φ, hw]
    refine (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
      (z := ⟨-1 / 2, 0⟩) (by norm_num) rfl).comp ?_
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht => ?_⟩
    · have : Continuous fun t : ℝ => (⟨-1 / 2, t⟩ : ℂ) :=
        Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)
      exact (this.tendsto' 0 _ rfl).mono_left nhdsWithin_le_nhds
    · show (0 : ℝ) ≤ t
      exact le_of_lt ht
  have hφr : Filter.Tendsto (fun t => φ (zr t)) (𝓝[>] 0) (𝓝 (-Real.pi)) := by
    have hw : ∀ t, -I * (toCpx (zr t) - toCpx p) = ⟨-1 / 2, -t⟩ := by
      intro t; rw [hcalc]; apply Complex.ext <;> simp [zr]; ring
    simp only [φ, hw]
    refine (Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero
      (z := ⟨-1 / 2, 0⟩) (by norm_num) rfl).comp ?_
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht => ?_⟩
    · have : Continuous fun t : ℝ => (⟨-1 / 2, -t⟩ : ℂ) :=
        Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_neg)
      exact (this.tendsto' 0 _ (by simp)).mono_left nhdsWithin_le_nhds
    · show (-t) < 0
      exact neg_neg_of_pos ht
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have eql : ∀ t, 0 < t → t < δ → (h (zl t)).im = φ (zl t) + Real.pi / 2 + 2 * Real.pi * c := by
    intro t ht htδ
    have := hcl t ht htδ
    simp only [F] at this
    field_simp at this
    linarith
  have eqr : ∀ t, 0 < t → t < δ → (h (zr t)).im = φ (zr t) + Real.pi / 2 + 2 * Real.pi * c := by
    intro t ht htδ
    have := hcr t ht htδ
    simp only [F] at this
    field_simp at this
    linarith
  have L1 : Filter.Tendsto (fun t => (h (zl t)).im) (𝓝[>] 0)
      (𝓝 (Real.pi + Real.pi / 2 + 2 * Real.pi * c)) :=
    ((hφl.add_const _).add_const _).congr' (hev.mono fun t ht => (eql t ht.1 ht.2).symm)
  have L2 : Filter.Tendsto (fun t => (h (zr t)).im) (𝓝[>] 0)
      (𝓝 (-Real.pi + Real.pi / 2 + 2 * Real.pi * c)) :=
    ((hφr.add_const _).add_const _).congr' (hev.mono fun t ht => (eqr t ht.1 ht.2).symm)
  have e1 := tendsto_nhds_unique hl L1
  have e2 := tendsto_nhds_unique hr L2
  linarith [Real.pi_pos]

/-- **Strip separation.** A crossing set separates the far left of the strip from the far right:
its left and right sides are disjoint. -/
theorem lc_disjoint_rc (hab : a < b) (hL : IsCross a b L) : Disjoint (Lc a b L) (Rc a b L) := by
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
  rintro w ⟨hwl, hwr⟩
  obtain ⟨M₁, hM₁⟩ := (hL.compact.image continuous_fst).isBounded.bddBelow
  obtain ⟨M₂, hM₂⟩ := (hL.compact.image continuous_fst).isBounded.bddAbove
  have hfl : FarL L (M₁ - 1, a) := fun z hz => by
    have := hM₁ (mem_image_of_mem Prod.fst hz); simp only; linarith
  have hfr : FarR L (M₂ + 1, a) := fun z hz => by
    have := hM₂ (mem_image_of_mem Prod.fst hz); simp only; linarith
  have hxs : ((M₁ - 1, a) : ℝ × ℝ) ∈ Strip a b := ⟨le_rfl, hab.le⟩
  have hys : ((M₂ + 1, a) : ℝ × ℝ) ∈ Strip a b := ⟨le_rfl, hab.le⟩
  have h1 : Lc a b L = connectedComponentIn (Strip a b \ L) (M₁ - 1, a) :=
    (goodSide_farL hL).eq hxs hfl
  have h2 : Rc a b L = connectedComponentIn (Strip a b \ L) (M₂ + 1, a) :=
    (goodSide_farR hL).eq hys hfr
  rw [h1] at hwl
  rw [h2] at hwr
  have hy : ((M₂ + 1, a) : ℝ × ℝ) ∈ connectedComponentIn (Strip a b \ L) (M₁ - 1, a) := by
    rw [connectedComponentIn_eq hwl, ← connectedComponentIn_eq hwr]
    exact mem_connectedComponentIn ⟨hys, (goodSide_farR hL).miss _ hfr⟩
  obtain ⟨Γ, hΓc, hΓp, hΓs, hxΓ, hyΓ⟩ := exists_compact_join hL.compact.isClosed hxs hy
  exact no_cross_join hab hL hfl hfr hΓc hΓp hΓs hxΓ hyΓ

end Separation

end HPC.Jones.Sector
