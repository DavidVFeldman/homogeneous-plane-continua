import HPC.Hagopian.H76Eps1
import HPC.Hagopian.H76Lemma8Sep

/-!
# Batch 161, item T5: `Wₓ`, `Gₓ`, the chain `{Gᵢ}`, its refinement `L`, and Property 1

Hagopian 1976, p. 346:
"For each point `x` of `E`, let `Wₓ` be the open set `{y ∈ M : an ε₁-homeomorphism of M onto M takes
x to y}` (Lemma 2), and let `Gₓ` be an open set in `{z ∈ R² : ρ(x, z) < ε₁}` such that
`Wₓ = M ∩ Gₓ`. For each `i` (`1 ≤ i ≤ 11`), let `Gᵢ = ⋃{Gₓ : x ∈ k⁻¹[[(i − 1)/11, i/11]]}`. Using the
method described in the proof of Lemma 8, we define an ordered refinement `L = {Lᵢ : 1 ≤ i ≤ 11}`
of the chain `{Gᵢ : 1 ≤ i ≤ 11}` that follows `E` and is free relative to `M` having the following
property: PROPERTY 1. For each point `y` of `M ∩ ⋃{Lᵢ : 2 ≤ i ≤ 10}`, there exists an
`ε₁`-homeomorphism `h` of `M` onto `M` such that `y` belongs to `h[E]` and `L` follows `h[E]`. (Here
the open sets `A` and `B` in the proof of Lemma 8 are in `G₁ − G₂` and `G₁₁ − G₁₀` respectively.)"

Indices: Hagopian's `Gᵢ`, `Lᵢ` (`1 ≤ i ≤ 11`) are `chainG k ε₁ (i − 1)`, `L (i − 1)` here
(`Fin 11`).

* `Gset M ε x`: the largest open set of the plane inside the `ε`-ball about `x` whose trace on `M`
  lies in `Wₓ`; `toPt_Wset_eq`: its trace is `Wₓ` (Lemma 2: `Wₓ` is open).
* `follows_of_elev`: a chain of eleven links follows a type A′ continuum `F` (map `b`) as soon as
  the `i`-th eleventh of `F` lies in the `i`-th link.
* `chainG_isPlaneChain`, `chainG_follows`: `{Gᵢ}` is a chain following `h[E]` for every
  `ε₁`-homeomorphism `h`; `thickChain_follows`: the same for the chain of `ε₁`-neighbourhoods of
  the elevenths (ledger check 161.2, with the family `IsEps1.sep`).
* `property1_aux`: `L` and Property 1. The caps are `U = G₁ − Cl G₂`, `V = G₁₁ − Cl G₁₀`
  (`IsEps1.ends` puts the end sets in them). For `y ∈ Lᵢ ∩ M` (`2 ≤ i ≤ 10`), `y ∈ Gₓ ∩ M = Wₓ`
  gives `h` with `h(x) = y`; `h[k⁻¹[[1/11, 10/11]]]` is connected, misses the caps, and meets `C` at
  `y`, so lies in `C`; hence the `j`-th eleventh of `h[E]` lies in `Lⱼ` for every `j`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Prop1

variable {M : Set Pt}

/-- **T5, `Wₓ`** (p. 346). -/
def Wset (M : Set Pt) (ε : ℝ) (x : M) : Set M :=
  {y | ∃ h : M ≃ₜ M, h x = y ∧ ∀ v, dist v (h v) < ε}

/-- **T5, `Gₓ`**: the largest open set of the plane in the `ε`-ball about `x` whose trace on `M`
lies in `Wₓ`. -/
def Gset (M : Set Pt) (ε : ℝ) (x : M) : Set Pt :=
  ⋃₀ {O : Set Pt | IsOpen O ∧ O ⊆ ball (x : Pt) ε ∧ M ∩ O ⊆ toPt (Wset M ε x)}

theorem isOpen_Gset {ε : ℝ} {x : M} : IsOpen (Gset M ε x) := isOpen_sUnion fun _ hO => hO.1

theorem Gset_subset_ball {ε : ℝ} {x : M} : Gset M ε x ⊆ ball (x : Pt) ε :=
  sUnion_subset fun _ hO => hO.2.1

theorem inter_Gset_subset {ε : ℝ} {x : M} : M ∩ Gset M ε x ⊆ toPt (Wset M ε x) := by
  rintro z ⟨hzM, O, hO, hzO⟩
  exact hO.2.2 ⟨hzM, hzO⟩

theorem toPt_Wset_eq [CompactSpace M] (hX : IsHomogeneous M) {ε : ℝ} (hε : 0 < ε) (x : M) :
    toPt (Wset M ε x) = M ∩ Gset M ε x := by
  refine Subset.antisymm ?_ inter_Gset_subset
  obtain ⟨hWo, -⟩ := lemma2_aux hX hε x
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.1 hWo
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y.2, O ∩ ball (x : Pt) ε, ⟨hO.inter isOpen_ball, inter_subset_right, ?_⟩, ?_, ?_⟩
  · rintro z ⟨hzM, hzO, -⟩
    have : (⟨z, hzM⟩ : M) ∈ Wset M ε x := by
      have : (⟨z, hzM⟩ : M) ∈ Subtype.val ⁻¹' O := hzO
      rw [hOW] at this
      exact this
    exact ⟨_, this, rfl⟩
  · have : y ∈ Subtype.val ⁻¹' O := by rw [hOW]; exact hy
    exact this
  · obtain ⟨h, rfl, hh⟩ := hy
    rw [mem_ball, ← Subtype.dist_eq, dist_comm]
    exact hh x

/-- An `ε`-homeomorphism takes `x` into `Gₓ`. -/
theorem mem_Gset_of_homeo [CompactSpace M] (hX : IsHomogeneous M) {ε : ℝ} (hε : 0 < ε)
    (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < ε) (x : M) : ((h x : M) : Pt) ∈ Gset M ε x := by
  have : ((h x : M) : Pt) ∈ toPt (Wset M ε x) := ⟨h x, ⟨h, rfl, hh⟩, rfl⟩
  rw [toPt_Wset_eq hX hε x] at this
  exact this.2

/-- **T5, `Gₓ`**: an open set in the `ε`-ball about `x` with `Wₓ = M ∩ Gₓ`. -/
theorem exists_Gset_aux [CompactSpace M] (hX : IsHomogeneous M) {ε : ℝ} (hε : 0 < ε) (x : M) :
    ∃ G : Set Pt, IsOpen G ∧ G ⊆ Metric.ball (x : Pt) ε ∧ toPt (Wset M ε x) = M ∩ G :=
  ⟨Gset M ε x, isOpen_Gset, Gset_subset_ball, toPt_Wset_eq hX hε x⟩

/-! ### Elevenths, 0-indexed -/

/-- The parameter interval `[m/11, (m + 1)/11]` (the `(m + 1)`-st eleventh). -/
def elev (m : ℕ) : Set unitInterval := {t | (m : ℝ) / 11 ≤ (t : ℝ) ∧ (t : ℝ) ≤ ((m : ℝ) + 1) / 11}

theorem piece_succ {E : Set M} (k : E → unitInterval) (m : ℕ) :
    piece k (m + 1) = layerSet k (elev m) := by
  unfold piece elev
  congr 2
  ext t
  push_cast
  simp

theorem exists_elev (t : unitInterval) : ∃ i : Fin 11, t ∈ elev i := by
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  by_cases h : (t : ℝ) ≤ 10 / 11
  · refine ⟨⟨⌊11 * (t : ℝ)⌋₊, ?_⟩, ?_, ?_⟩
    · have : ⌊11 * (t : ℝ)⌋₊ ≤ 10 := Nat.floor_le_of_le (by norm_num; linarith)
      omega
    · have := Nat.floor_le (show (0 : ℝ) ≤ 11 * t by positivity)
      simp only
      linarith
    · have := Nat.lt_floor_add_one (11 * (t : ℝ))
      simp only
      linarith
  · refine ⟨⟨10, by norm_num⟩, ?_, ?_⟩ <;> simp only <;> push_cast <;> linarith

/-- Interpolation: a parameter between parameters in the elevenths `a` and `c` lies in an eleventh
between `a` and `c`. -/
theorem exists_elev_between {a c : ℕ} {r s t : unitInterval} (hr : r ∈ elev a) (hs : s ∈ elev c)
    (hrt : r ≤ t) (hts : t ≤ s) (hc : c ≤ 10) :
    ∃ m : ℕ, m ≤ 10 ∧ t ∈ elev m ∧ (m = a ∨ m = c ∨ (a < m ∧ m < c)) := by
  have hrt' : (r : ℝ) ≤ t := hrt
  have hts' : (t : ℝ) ≤ s := hts
  by_cases h2 : (c : ℝ) / 11 ≤ t
  · exact ⟨c, hc, ⟨h2, hts'.trans hs.2⟩, Or.inr (Or.inl rfl)⟩
  by_cases h1 : (t : ℝ) ≤ ((a : ℝ) + 1) / 11
  · have ha : a < c := by
      have : (a : ℝ) < c := by
        have := hr.1
        push_neg at h2
        linarith
      exact_mod_cast this
    exact ⟨a, by omega, ⟨hr.1.trans hrt', h1⟩, Or.inl rfl⟩
  push_neg at h1 h2
  have ht0 : (0 : ℝ) ≤ 11 * t := by have := t.2.1; positivity
  refine ⟨⌊11 * (t : ℝ)⌋₊, ?_, ⟨?_, ?_⟩, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
  · have : ⌊11 * (t : ℝ)⌋₊ < c := (Nat.floor_lt ht0).2 (by linarith)
    omega
  · have := Nat.floor_le ht0
    linarith
  · have := Nat.lt_floor_add_one (11 * (t : ℝ))
    linarith
  · have : a + 1 ≤ ⌊11 * (t : ℝ)⌋₊ := Nat.le_floor (by push_cast; linarith)
    omega
  · exact (Nat.floor_lt ht0).2 (by linarith)

theorem layer_subset_layerSet {X : Type*} {F : Set X} (b : F → unitInterval) {t : unitInterval}
    {S : Set unitInterval} (ht : t ∈ S) : layer b t ⊆ layerSet b S := by
  rintro _ ⟨e, he, rfl⟩
  exact ⟨e, by rw [mem_preimage, mem_singleton_iff.1 he]; exact ht, rfl⟩

/-- **Following by elevenths.** A chain of eleven links follows `F` (map `b`, onto) when the
`(i + 1)`-st eleventh of `F` lies in the `i`-th link. -/
theorem follows_of_elev {F : Set M} {b : F → unitInterval} (hb : Function.Surjective b)
    {L : Fin 11 → Set Pt} (hL : IsPlaneChain L)
    (hsub : ∀ i : Fin 11, toPt (layerSet b (elev i)) ⊆ L i) : Follows L b := by
  have hlay : ∀ t : unitInterval, ∃ i : Fin 11, t ∈ elev i ∧ toPt (layer b t) ⊆ L i := by
    intro t
    obtain ⟨i, hi⟩ := exists_elev t
    exact ⟨i, hi, (toPt_mono (layer_subset_layerSet b hi)).trans (hsub i)⟩
  refine ⟨?_, ?_, ?_, fun t => (hlay t).imp fun i hi => hi.2, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, -, hi⟩ := hlay (b ⟨x, hx⟩)
    exact mem_iUnion.2 ⟨i, hi ⟨x, ⟨⟨x, hx⟩, rfl, rfl⟩, rfl⟩⟩
  · refine (toPt_mono (layer_subset_layerSet b (t := 0) (S := elev 0) ?_)).trans (hsub 0)
    simp [elev]
  · refine (toPt_mono (layer_subset_layerSet b (t := 1) (S := elev 10) ?_)).trans
      (hsub (Fin.last 10))
    simp [elev]
    norm_num
  · intro r s hrs i hi
    obtain ⟨a, ha, haL⟩ := hlay r
    obtain ⟨c, hc, hcL⟩ := hlay s
    obtain ⟨er, rfl⟩ := hb r
    obtain ⟨es, rfl⟩ := hb s
    have hai : (L a ∩ L i).Nonempty :=
      ⟨_, haL ⟨er, ⟨er, rfl, rfl⟩, rfl⟩, hi ⟨er, Or.inl ⟨er, rfl, rfl⟩, rfl⟩⟩
    have hci : (L c ∩ L i).Nonempty :=
      ⟨_, hcL ⟨es, ⟨es, rfl, rfl⟩, rfl⟩, hi ⟨es, Or.inr ⟨es, rfl, rfl⟩, rfl⟩⟩
    have hai' := (hL.meets a i).1 hai
    have hci' := (hL.meets c i).1 hci
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    obtain ⟨m, hm10, hm, hmac⟩ := exists_elev_between ha hc he.1 he.2 (by omega)
    set m' : Fin 11 := ⟨m, by omega⟩
    have hmi : (L m' ∩ L i).Nonempty := (hL.meets m' i).2 (by simp only [m']; omega)
    exact mem_iUnion₂.2 ⟨m', hmi, hsub m' ⟨e, ⟨e, hm, rfl⟩, rfl⟩⟩

/-! ### The chain `{Gᵢ}` -/

/-- **T5, the chain `{Gᵢ}`** (p. 346), 0-indexed: `chainG k ε i = ⋃{Gₓ : x ∈ k⁻¹[[i/11, (i+1)/11]]}`. -/
def chainG {E : Set M} (k : E → unitInterval) (ε : ℝ) (i : Fin 11) : Set Pt :=
  ⋃ x ∈ piece k ((i : ℕ) + 1), Gset M ε x

theorem isOpen_chainG {E : Set M} (k : E → unitInterval) (ε : ℝ) (i : Fin 11) :
    IsOpen (chainG k ε i) :=
  isOpen_biUnion fun _ _ => isOpen_Gset

theorem chainG_subset_thickening {E : Set M} (k : E → unitInterval) (ε : ℝ) (i : Fin 11) :
    chainG k ε i ⊆ thickening ε (toPt (piece k ((i : ℕ) + 1))) := by
  intro z hz
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 hz
  exact mem_thickening_iff.2 ⟨x, ⟨x, hx, rfl⟩, Gset_subset_ball hzx⟩

theorem image_piece_subset_chainG [CompactSpace M] (hX : IsHomogeneous M) {E : Set M}
    (k : E → unitInterval) {ε : ℝ} (hε : 0 < ε) (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < ε)
    (i : Fin 11) : toPt (h '' piece k ((i : ℕ) + 1)) ⊆ chainG k ε i := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact mem_iUnion₂.2 ⟨x, hx, mem_Gset_of_homeo hX hε h hh x⟩

theorem piece_subset_chainG [CompactSpace M] (hX : IsHomogeneous M) {E : Set M}
    (k : E → unitInterval) {ε : ℝ} (hε : 0 < ε) (i : Fin 11) :
    toPt (piece k ((i : ℕ) + 1)) ⊆ chainG k ε i := by
  have := image_piece_subset_chainG hX k hε (Homeomorph.refl M) (fun v => by simpa using hε) i
  simpa using this

/-- Consecutive (or equal) elevenths meet. -/
theorem elev_inter_nonempty {E : Set M} {k : E → unitInterval} (hk : Function.Surjective k)
    (i j : Fin 11) (hij : (i : ℕ) ≤ j + 1) (hji : (j : ℕ) ≤ i + 1) :
    (toPt (piece k ((i : ℕ) + 1)) ∩ toPt (piece k ((j : ℕ) + 1))).Nonempty := by
  have hi := i.2
  have hj := j.2
  set m : ℕ := max (i : ℕ) j
  have hm : (m : ℝ) / 11 ∈ Icc (0 : ℝ) 1 := by
    have : m ≤ 10 := by simp only [m]; omega
    have : (m : ℝ) ≤ 10 := by exact_mod_cast this
    constructor <;> [positivity; linarith]
  obtain ⟨e, he⟩ := hk ⟨(m : ℝ) / 11, hm⟩
  have hmi : (i : ℝ) ≤ m := by exact_mod_cast le_max_left (i : ℕ) j
  have hmj : (j : ℝ) ≤ m := by exact_mod_cast le_max_right (i : ℕ) j
  have hmi' : (m : ℝ) ≤ i + 1 := by
    have : m ≤ (i : ℕ) + 1 := by simp only [m]; omega
    exact_mod_cast this
  have hmj' : (m : ℝ) ≤ j + 1 := by
    have : m ≤ (j : ℕ) + 1 := by simp only [m]; omega
    exact_mod_cast this
  refine ⟨((e : M) : Pt), ⟨e, ?_, rfl⟩, ⟨e, ?_, rfl⟩⟩
  · rw [piece_succ]
    refine ⟨e, ?_, rfl⟩
    show (i : ℝ) / 11 ≤ (k e : ℝ) ∧ (k e : ℝ) ≤ ((i : ℝ) + 1) / 11
    rw [he]
    constructor <;> simp only <;> linarith
  · rw [piece_succ]
    refine ⟨e, ?_, rfl⟩
    show (j : ℝ) / 11 ≤ (k e : ℝ) ∧ (k e : ℝ) ≤ ((j : ℝ) + 1) / 11
    rw [he]
    constructor <;> simp only <;> linarith

/-- **A chain from the elevenths.** Open sets `Lᵢ` containing the `(i + 1)`-st eleventh and inside
its `ε₁`-neighbourhood form a chain. -/
theorem isPlaneChain_of_pieces {E : Set M} {k : E → unitInterval} (hk : Function.Surjective k)
    {ε₁ : ℝ} (he : IsEps1 k ε₁) {L : Fin 11 → Set Pt} (hLo : ∀ i, IsOpen (L i))
    (hcore : ∀ i : Fin 11, toPt (piece k ((i : ℕ) + 1)) ⊆ L i)
    (hthick : ∀ i : Fin 11, L i ⊆ thickening ε₁ (toPt (piece k ((i : ℕ) + 1)))) :
    IsPlaneChain L := by
  refine ⟨hLo, fun i j => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨z, hzi, hzj⟩ := h
    obtain ⟨_, ⟨a, ha, rfl⟩, hza⟩ := mem_thickening_iff.1 (hthick i hzi)
    obtain ⟨_, ⟨b, hb, rfl⟩, hzb⟩ := mem_thickening_iff.1 (hthick j hzj)
    have hab : dist a b < 2 * ε₁ := by
      rw [Subtype.dist_eq]
      have := dist_triangle (a : Pt) z (b : Pt)
      rw [dist_comm (a : Pt) z] at this
      linarith
    have hpos := he.pos
    by_contra hcon
    rcases not_and_or.1 hcon with h1 | h1
    · have := he.sep ((j : ℕ) + 1) ((i : ℕ) + 1) (by omega) (by omega) b hb a ha
      rw [dist_comm] at this
      linarith
    · have := he.sep ((i : ℕ) + 1) ((j : ℕ) + 1) (by omega) (by omega) a ha b hb
      linarith
  · obtain ⟨z, hzi, hzj⟩ := elev_inter_nonempty hk i j h.1 h.2
    exact ⟨z, hcore i hzi, hcore j hzj⟩

theorem chainG_isPlaneChain [CompactSpace M] (hX : IsHomogeneous M) {E : Set M}
    {k : E → unitInterval} (hk : Function.Surjective k) {ε₁ : ℝ} (he : IsEps1 k ε₁) :
    IsPlaneChain (chainG k ε₁) :=
  isPlaneChain_of_pieces hk he (isOpen_chainG k ε₁) (piece_subset_chainG hX k he.pos)
    (chainG_subset_thickening k ε₁)

/-- The elevenths of `h[E]`, for the transported map. -/
theorem toPt_layerSet_elev {E : Set M} {k : E → unitInterval} {h : M ≃ₜ M}
    {b : (h '' E) → unitInterval} (hb : ∀ S, layerSet b S = h '' layerSet k S) (i : ℕ) :
    toPt (layerSet b (elev i)) = toPt (h '' piece k (i + 1)) := by
  rw [hb, piece_succ]

/-- **`{Gᵢ}` follows `h[E]`** for every `ε₁`-homeomorphism `h` (in particular it follows `E`). -/
theorem chainG_follows [CompactSpace M] (hX : IsHomogeneous M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < ε₁) {b : (h '' E) → unitInterval}
    (hbE : IsMinimalAdmissible (h '' E) b) (hb : ∀ S, layerSet b S = h '' layerSet k S) :
    Follows (chainG k ε₁) b :=
  follows_of_elev hbE.2.1.2.1 (chainG_isPlaneChain hX hE.2.1.2.1 he) fun i => by
    rw [toPt_layerSet_elev hb]
    exact image_piece_subset_chainG hX k he.pos h hh i

theorem chainG_follows_self [CompactSpace M] (hX : IsHomogeneous M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁) :
    Follows (chainG k ε₁) k :=
  follows_of_elev hE.2.1.2.1 (chainG_isPlaneChain hX hE.2.1.2.1 he) fun i => by
    rw [← piece_succ]
    exact piece_subset_chainG hX k he.pos i

/-- The chain of `ε₁`-neighbourhoods of the elevenths (p. 346). -/
def thickChain {E : Set M} (k : E → unitInterval) (ε : ℝ) (i : Fin 11) : Set Pt :=
  thickening ε (toPt (piece k ((i : ℕ) + 1)))

/-- **Ledger check 161.2**: "if `h` is an `ε₁`-homeomorphism of `M` onto `M`, then the chain formed
by taking `ε₁`-neighborhoods in `R²` of the elements of `{k⁻¹[[(i − 1)/11, i/11]] : 1 ≤ i ≤ 11}`
follows `h[E]`" — with `ε₁` satisfying `IsEps1.sep` (not among Hagopian's four families). -/
theorem thickChain_follows {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {ε₁ : ℝ} (he : IsEps1 k ε₁) (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < ε₁)
    {b : (h '' E) → unitInterval} (hbE : IsMinimalAdmissible (h '' E) b)
    (hb : ∀ S, layerSet b S = h '' layerSet k S) :
    IsPlaneChain (thickChain k ε₁) ∧ Follows (thickChain k ε₁) b := by
  have hch : IsPlaneChain (thickChain k ε₁) :=
    isPlaneChain_of_pieces hE.2.1.2.1 he (fun _ => isOpen_thickening)
      (fun _ => self_subset_thickening he.pos _) (fun _ => subset_rfl)
  refine ⟨hch, follows_of_elev hbE.2.1.2.1 hch fun i => ?_⟩
  rw [toPt_layerSet_elev hb]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  refine mem_thickening_iff.2 ⟨x, ⟨x, hx, rfl⟩, ?_⟩
  rw [← Subtype.dist_eq, dist_comm]
  exact hh x

/-! ### Property 1 -/

theorem piece_subset_middle {E : Set M} (k : E → unitInterval) {i : ℕ} (h1 : 1 ≤ i) (h9 : i ≤ 9) :
    piece k (i + 1) ⊆ middle k := by
  rw [piece_succ]
  rintro _ ⟨e, he, rfl⟩
  refine ⟨e, ?_, rfl⟩
  have : (1 : ℝ) ≤ i := by exact_mod_cast h1
  have : (i : ℝ) ≤ 9 := by exact_mod_cast h9
  have h1' := he.1
  have h2' := he.2
  constructor <;> linarith

theorem middle_subset_pieces {E : Set M} (k : E → unitInterval) :
    middle k ⊆ ⋃ (i : Fin 11) (_ : 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ 9), piece k ((i : ℕ) + 1) := by
  rintro _ ⟨e, he, rfl⟩
  have h1 : (1 : ℝ) / 11 ≤ k e := he.1
  have h2 : (k e : ℝ) ≤ 10 / 11 := he.2
  have ht0 : (0 : ℝ) ≤ 11 * (k e : ℝ) := by have := (k e).2.1; positivity
  by_cases h : (k e : ℝ) = 10 / 11
  · refine mem_iUnion₂.2 ⟨⟨9, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [piece_succ]
    refine ⟨e, ?_, rfl⟩
    show ((9 : ℕ) : ℝ) / 11 ≤ (k e : ℝ) ∧ (k e : ℝ) ≤ (((9 : ℕ) : ℝ) + 1) / 11
    rw [h]; norm_num
  have h2' : (k e : ℝ) < 10 / 11 := lt_of_le_of_ne h2 h
  set m := ⌊11 * (k e : ℝ)⌋₊
  have hm1 : 1 ≤ m := Nat.le_floor (by push_cast; linarith)
  have hm9 : m ≤ 9 := by
    have : m < 10 := (Nat.floor_lt ht0).2 (by push_cast; linarith)
    omega
  refine mem_iUnion₂.2 ⟨⟨m, by omega⟩, ⟨hm1, hm9⟩, ?_⟩
  rw [piece_succ]
  refine ⟨e, ?_, rfl⟩
  have := Nat.floor_le ht0
  have := Nat.lt_floor_add_one (11 * (k e : ℝ))
  show (m : ℝ) / 11 ≤ (k e : ℝ) ∧ (k e : ℝ) ≤ ((m : ℝ) + 1) / 11
  constructor <;> linarith

theorem isPreconnected_middle {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    IsPreconnected (middle k) := by
  have hS : {t : unitInterval | 1 / 11 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 10 / 11} =
      Icc (⟨1 / 11, by norm_num, by norm_num⟩ : unitInterval) ⟨10 / 11, by norm_num, by norm_num⟩ := by
    ext t
    simp only [mem_setOf_eq, mem_Icc]
    rfl
  have := isContinuum_img hE.isCompact hE.2.1 (S := Icc
    (⟨1 / 11, by norm_num, by norm_num⟩ : unitInterval) ⟨10 / 11, by norm_num, by norm_num⟩)
    isClosed_Icc isPreconnected_Icc ⟨_, left_mem_Icc.2 (by
      show (1 / 11 : ℝ) ≤ 10 / 11; norm_num)⟩
  unfold middle
  rw [hS]
  exact this.2.2

/-- **T5 and Property 1** (p. 346), in full. -/
theorem property1_aux [CompactSpace M] [ConnectedSpace M] (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁) :
    ∃ (L : Fin 11 → Set Pt) (C : Set Pt), IsOpen C ∧ toPt E ⊆ C ∧
      L 0 = chainG k ε₁ 0 ∧ L (Fin.last 10) = chainG k ε₁ (Fin.last 10) ∧
      (∀ i, i ≠ 0 → i ≠ Fin.last 10 → L i = C ∩ chainG k ε₁ i) ∧
      IsOrderedRefinement L (chainG k ε₁) ∧ Follows L k ∧ IsFree M L ∧
      ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
        ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
          (∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) ∧
          ∃ b : (h '' E) → unitInterval, IsMinimalAdmissible (h '' E) b ∧
            (∀ S, layerSet b S = h '' layerSet k S) ∧ Follows L b := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  have hk := hE.2.1.2.1
  have hε := he.pos
  set G := chainG k ε₁ with hGdef
  have hG : IsPlaneChain G := chainG_isPlaneChain hX hk he
  have hGE : Follows G k := chainG_follows_self hX hE he
  set U := G 0 \ closure (G 1) with hU
  set V := G (Fin.last 10) \ closure (G 9) with hV
  -- a point of the plane near `G 1` (or `G 9`) is far from the end sets
  have hfar : ∀ (j : Fin 11), 1 ≤ (j : ℕ) → (j : ℕ) ≤ 9 → ∀ x ∈ layer k 0 ∪ layer k 1,
      (x : Pt) ∉ closure (G j) := by
    intro j hj1 hj9 x hx hxcl
    obtain ⟨w, hw, hxw⟩ := Metric.mem_closure_iff.1 hxcl ε₁ hε
    obtain ⟨_, ⟨y, hy, rfl⟩, hwy⟩ := mem_thickening_iff.1 (chainG_subset_thickening k ε₁ j hw)
    have := he.ends x hx y (piece_subset_middle k hj1 hj9 hy)
    rw [Subtype.dist_eq] at this
    have := dist_triangle (x : Pt) w (y : Pt)
    linarith
  have hUo : IsOpen U := (isOpen_chainG k ε₁ 0).sdiff isClosed_closure
  have hVo : IsOpen V := (isOpen_chainG k ε₁ _).sdiff isClosed_closure
  have hXU : toPt (layer k 0) ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hGE.2.1 ⟨x, hx, rfl⟩, hfar 1 le_rfl (by norm_num) x (Or.inl hx)⟩
  have hZV : toPt (layer k 1) ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hGE.2.2.1 ⟨x, hx, rfl⟩, hfar 9 (by norm_num) (by norm_num) x (Or.inr hx)⟩
  obtain ⟨L, C, D, hC, hD, hCD, hMCD, hEC, hL0, hLn, hLi, hLG, hLE, hLfree⟩ :=
    lemma8_caps_sep hHU hAT hE G hG hGE hUo hVo hXU hZV diff_subset diff_subset
  refine ⟨L, C, hC, hEC, hL0, hLn, hLi, hLG, hLE, hLfree, ?_⟩
  intro y i hi1 hi9 hyL
  have hi0 : i ≠ 0 := fun h => by subst h; simp at hi1
  have hin : i ≠ Fin.last 10 := fun h => by subst h; simp at hi9
  rw [hLi i hi0 hin] at hyL
  obtain ⟨hyC, hyG⟩ := hyL
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hyG
  obtain ⟨w, ⟨h, hxw, hh⟩, hw⟩ := inter_Gset_subset ⟨y.2, hyx⟩
  have hwy : h x = y := hxw.trans (Subtype.val_injective hw)
  -- the middle of `h[E]` lies in `C`
  have hmidC : toPt (h '' middle k) ⊆ C := by
    have hpc : IsPreconnected (toPt (h '' middle k)) :=
      ((isPreconnected_middle hE).image _ h.continuous.continuousOn).image _
        continuous_subtype_val.continuousOn
    refine hpc.subset_left_of_subset_union hC hD hCD ?_ ?_
    · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      refine hMCD (h z) ?_
      obtain ⟨j, ⟨hj1, hj9⟩, hzj⟩ := mem_iUnion₂.1 (middle_subset_pieces k hz)
      have hzG : ((h z : M) : Pt) ∈ G j :=
        image_piece_subset_chainG hX k hε h hh j ⟨_, ⟨z, hzj, rfl⟩, rfl⟩
      rintro (⟨hU0, -⟩ | ⟨hV0, -⟩)
      · obtain ⟨hz0, hzcl⟩ := hU0
        by_cases hj : (j : ℕ) = 1
        · have : j = 1 := Fin.ext hj
          subst this
          exact hzcl (subset_closure hzG)
        · have := (hG.meets 0 j).1 ⟨_, hz0, hzG⟩
          simp at this
          omega
      · obtain ⟨hz0, hzcl⟩ := hV0
        by_cases hj : (j : ℕ) = 9
        · have : j = 9 := Fin.ext hj
          subst this
          exact hzcl (subset_closure hzG)
        · have := (hG.meets (Fin.last 10) j).1 ⟨_, hz0, hzG⟩
          simp at this
          omega
    · refine ⟨(y : Pt), ⟨_, ⟨x, ?_, hwy⟩, rfl⟩, hyC⟩
      exact piece_subset_middle k hi1 hi9 hx
  have hpieceL : ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j := by
    intro j
    by_cases hj0 : j = 0
    · subst hj0
      rw [hL0]
      exact image_piece_subset_chainG hX k hε h hh 0
    by_cases hjn : j = Fin.last 10
    · subst hjn
      rw [hLn]
      exact image_piece_subset_chainG hX k hε h hh _
    rw [hLi j hj0 hjn]
    refine subset_inter ?_ (image_piece_subset_chainG hX k hε h hh j)
    refine (toPt_mono (image_mono (piece_subset_middle k ?_ ?_))).trans hmidC
    · rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
      · exact absurd (Fin.ext h0) hj0
      · exact h0
    · have := j.2
      have : (j : ℕ) ≠ 10 := fun h' => hjn (Fin.ext h')
      omega
  obtain ⟨b, hbE, hb⟩ := exists_image_map h hE
  refine ⟨h, hh, ⟨x, ?_, hwy⟩, hpieceL, b, hbE, hb, ?_⟩
  · obtain ⟨e, -, rfl⟩ : x ∈ Subtype.val '' _ := hx
    exact e.2
  · exact follows_of_elev hbE.2.1.2.1 hLG.1 fun j => by
      rw [toPt_layerSet_elev hb]
      exact hpieceL j

end Prop1

end HPC.Hagopian
