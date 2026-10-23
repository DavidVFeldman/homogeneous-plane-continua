import HPC.Chains.Basic

/-!
# Theorem 5: the coarse reading with end zones

Batch 80. For Bing's Theorem 5 the coarse reading of the middle chain `R` (a deep level) has two
extra *end values*: positions of `R` within `W` of a link meeting `d(2)_u` read `h - 1`, those
within `W` of a link meeting `d(2)_v` read `k + 1`; a ring of width `W` around each of these zones
reads `h` (resp. `k`); elsewhere a position reads the link of `D_1` named by a `W`-thick reading
`τ1` of `R` in `D_2`, transported to `D_1` by `ρ`. (In the code `D0`, `D1` are Bing's `D_1`, `D_2`.)

The facts proved here (`Setup.sound`, `Setup.force_u`, `Setup.force_v`, `Setup.slow_rel`) are what
the lift over runs needs: soundness of every value read near a link of the fine chain `F` lying
in `D_2(u, v)`, the forcing of the end values near `d(2)_u`, `d(2)_v`, and slowness between
positions that are near such links.
-/

namespace HPC.T5

open Set

variable {X : Type*} [MetricSpace X] {n0 n1 nR nF : ℕ}

/-- Position `p` of `R` is within `d` of a link of `R` meeting `A`. -/
def Near (R : Chain X nR) (A : Set X) (d : ℕ) (p : Fin nR) : Prop :=
  ∃ q : Fin nR, (R.link q ∩ A).Nonempty ∧ ((p : ℤ) - q).natAbs ≤ d

theorem Near.mono {R : Chain X nR} {A : Set X} {d d' : ℕ} {p : Fin nR} (h : Near R A d p)
    (hd : d ≤ d') : Near R A d' p := by
  obtain ⟨q, hq, hd'⟩ := h
  exact ⟨q, hq, by omega⟩

theorem Near.shift {R : Chain X nR} {A : Set X} {d e : ℕ} {p p' : Fin nR} (h : Near R A d p)
    (hpp : ((p : ℤ) - p').natAbs ≤ e) : Near R A (d + e) p' := by
  obtain ⟨q, hq, hd'⟩ := h
  exact ⟨q, hq, by omega⟩

/-- A link of `F` lies in `D_2(u, v)` (in a link of `D1` with index between `u` and `v`). -/
def InS (D1 : Chain X n1) (F : Chain X nF) (u v : Fin n1) (t : Fin nF) : Prop :=
  ∃ s : Fin n1, u ≤ s ∧ s ≤ v ∧ F.link t ⊆ D1.link s

/-- The hypotheses on the chains and readings used by the end-zone reading. -/
structure Setup (D0 : Chain X n0) (D1 : Chain X n1) (R : Chain X nR) (F : Chain X nF)
    (h k : Fin n0) (u v : Fin n1) (W : ℕ) (σ0 : Fin nF → Fin nR) (τ1 : Fin nR → Fin n1)
    (ρ : Fin n1 → Fin n0) : Prop where
  hk : h ≤ k
  σ0_sub : ∀ t, F.link t ⊆ R.link (σ0 t)
  thick : ∀ p p' : Fin nR, ((p : ℤ) - p').natAbs ≤ W → R.link p' ⊆ D1.link (τ1 p)
  ρ_sub : ∀ t : Fin n1, u < t → t < v → D1.link t ⊆ D0.link (ρ t)
  ρ_range : ∀ t, h ≤ ρ t ∧ ρ t ≤ k
  zoneU : ∀ q p' : Fin nR, (R.link q ∩ D1.link u).Nonempty → ((q : ℤ) - p').natAbs ≤ 4 * W →
    R.link p' ⊆ D0.link h
  zoneV : ∀ q p' : Fin nR, (R.link q ∩ D1.link v).Nonempty → ((q : ℤ) - p').natAbs ≤ 4 * W →
    R.link p' ⊆ D0.link k
  sep : ∀ q q' : Fin nR, (R.link q ∩ D1.link u).Nonempty → (R.link q' ∩ D1.link v).Nonempty →
    10 * W < ((q : ℤ) - q').natAbs

variable {D0 : Chain X n0} {D1 : Chain X n1} {R : Chain X nR} {F : Chain X nF}
  {h k : Fin n0} {u v : Fin n1} {W : ℕ} {σ0 : Fin nF → Fin nR} {τ1 : Fin nR → Fin n1}
  {ρ : Fin n1 → Fin n0}

open Classical in
/-- The end-zone reading. -/
noncomputable def rd (D1 : Chain X n1) (R : Chain X nR) (h k : Fin n0) (u v : Fin n1) (W : ℕ)
    (τ1 : Fin nR → Fin n1) (ρ : Fin n1 → Fin n0) (p : Fin nR) : ℤ :=
  if Near R (D1.link u) W p then (h : ℤ) - 1
  else if Near R (D1.link v) W p then (k : ℤ) + 1
  else if Near R (D1.link u) (2 * W) p then (h : ℤ)
  else if Near R (D1.link v) (2 * W) p then (k : ℤ)
  else (ρ (τ1 p) : ℤ)

/-- A value read near the link `f` of `F` is *sound* for `f`. -/
def Sound (D0 : Chain X n0) (D1 : Chain X n1) (F : Chain X nF) (h k : Fin n0) (u v : Fin n1)
    (f : Fin nF) (val : ℤ) : Prop :=
  (val = (h : ℤ) - 1 → F.link f ⊆ D0.link h) ∧ (val = (k : ℤ) + 1 → F.link f ⊆ D0.link k) ∧
  ((h : ℤ) ≤ val → val ≤ (k : ℤ) → ∀ c : Fin n0, (c : ℤ) = val →
    F.link f ⊆ D0.link c ∧ Disjoint (F.link f) (D1.link u ∪ D1.link v))

namespace Setup

variable (H : Setup D0 D1 R F h k u v W σ0 τ1 ρ)
include H

theorem near_of_meet {f : Fin nF} {p : Fin nR} {A : Set X} (hA : (F.link f ∩ A).Nonempty)
    (hp : ((p : ℤ) - σ0 f).natAbs ≤ W) : Near R A W p := by
  obtain ⟨z, hz1, hz2⟩ := hA
  exact ⟨σ0 f, ⟨z, H.σ0_sub f hz1, hz2⟩, hp⟩

theorem not_near_both {p p' : Fin nR} {a b : ℕ} (hu : Near R (D1.link u) a p)
    (hv : Near R (D1.link v) b p') (hpp : ((p : ℤ) - p').natAbs ≤ W) (hab : a + b + W ≤ 10 * W) :
    False := by
  obtain ⟨q, hq, hq'⟩ := hu
  obtain ⟨q', hq2, hq2'⟩ := hv
  have := H.sep q q' hq hq2
  omega

/-- Away from the end zones, the thick reading near a link in `D_2(u, v)` is strictly between
`u` and `v`. -/
theorem normal_range {f : Fin nF} {p : Fin nR} (hf : InS D1 F u v f)
    (hp : ((p : ℤ) - σ0 f).natAbs ≤ W) (hnu : ¬ Near R (D1.link u) W p)
    (hnv : ¬ Near R (D1.link v) W p) : u < τ1 p ∧ τ1 p < v := by
  obtain ⟨s, hus, hsv, hFs⟩ := hf
  have hth : R.link (σ0 f) ⊆ D1.link (τ1 p) := H.thick p (σ0 f) hp
  obtain ⟨z, hz⟩ := F.link_nonempty f
  have hzR := H.σ0_sub f hz
  have hadj := (D1.adjacent_iff s (τ1 p)).mp ⟨z, hFs hz, hth hzR⟩
  constructor
  · by_contra hcon
    push_neg at hcon
    apply hnu
    refine ⟨σ0 f, ⟨z, hzR, ?_⟩, hp⟩
    rcases eq_or_lt_of_le hcon with he | hlt
    · rw [← he]; exact hth hzR
    · have : s = u := Fin.ext (by
        have := hadj.1; have := hadj.2
        simp only [Fin.lt_def, Fin.le_def] at hlt hus hsv; omega)
      rw [← this]; exact hFs hz
  · by_contra hcon
    push_neg at hcon
    apply hnv
    refine ⟨σ0 f, ⟨z, hzR, ?_⟩, hp⟩
    rcases eq_or_lt_of_le hcon with he | hlt
    · rw [he]; exact hth hzR
    · have : s = v := Fin.ext (by
        have := hadj.1; have := hadj.2
        simp only [Fin.lt_def, Fin.le_def] at hlt hus hsv; omega)
      rw [← this]; exact hFs hz

theorem disjoint_of_not_near {f : Fin nF} {p : Fin nR} (hp : ((p : ℤ) - σ0 f).natAbs ≤ W)
    (hnu : ¬ Near R (D1.link u) W p) (hnv : ¬ Near R (D1.link v) W p) :
    Disjoint (F.link f) (D1.link u ∪ D1.link v) := by
  rw [Set.disjoint_left]
  rintro z hz (hzu | hzv)
  · exact hnu (H.near_of_meet ⟨z, hz, hzu⟩ hp)
  · exact hnv (H.near_of_meet ⟨z, hz, hzv⟩ hp)

/-- **Soundness** of the end-zone reading. -/
theorem sound {f : Fin nF} {p : Fin nR} (hf : InS D1 F u v f)
    (hp : ((p : ℤ) - σ0 f).natAbs ≤ W) :
    Sound D0 D1 F h k u v f (rd D1 R h k u v W τ1 ρ p) := by
  have hhk : (h : ℕ) ≤ k := H.hk
  have hFR := H.σ0_sub f
  unfold rd
  split_ifs with h1 h2 h3 h4
  · refine ⟨fun _ => ?_, fun he => by omega, fun h1 h2 c hc => by omega⟩
    obtain ⟨q, hq, hq'⟩ := h1
    exact hFR.trans (H.zoneU q (σ0 f) hq (by omega))
  · refine ⟨fun he => by omega, fun _ => ?_, fun h1 h2 c hc => by omega⟩
    obtain ⟨q, hq, hq'⟩ := h2
    exact hFR.trans (H.zoneV q (σ0 f) hq (by omega))
  · refine ⟨fun he => by omega, fun he => by omega, fun _ _ c hc => ⟨?_, ?_⟩⟩
    · have : c = h := Fin.ext (by omega)
      subst this
      obtain ⟨q, hq, hq'⟩ := h3
      exact hFR.trans (H.zoneU q (σ0 f) hq (by omega))
    · exact H.disjoint_of_not_near hp h1 h2
  · refine ⟨fun he => by omega, fun he => by omega, fun _ _ c hc => ⟨?_, ?_⟩⟩
    · have : c = k := Fin.ext (by omega)
      subst this
      obtain ⟨q, hq, hq'⟩ := h4
      exact hFR.trans (H.zoneV q (σ0 f) hq (by omega))
    · exact H.disjoint_of_not_near hp h1 h2
  · have hr := H.ρ_range (τ1 p)
    have hr1 : (h : ℕ) ≤ ρ (τ1 p) := hr.1
    have hr2 : (ρ (τ1 p) : ℕ) ≤ k := hr.2
    refine ⟨fun he => by omega, fun he => by omega, fun _ _ c hc => ⟨?_, ?_⟩⟩
    · have : c = ρ (τ1 p) := Fin.ext (by omega)
      subst this
      obtain ⟨hu, hv⟩ := H.normal_range hf hp h1 h2
      exact hFR.trans ((H.thick p (σ0 f) hp).trans (H.ρ_sub _ hu hv))
    · exact H.disjoint_of_not_near hp h1 h2

/-- Near `d(2)_u` only the end value `h - 1` is read. -/
theorem force_u {f : Fin nF} {p : Fin nR} (hA : (F.link f ∩ D1.link u).Nonempty)
    (hp : ((p : ℤ) - σ0 f).natAbs ≤ W) : rd D1 R h k u v W τ1 ρ p = (h : ℤ) - 1 := by
  unfold rd
  rw [if_pos (H.near_of_meet hA hp)]

/-- Near `d(2)_v` only the end value `k + 1` is read. -/
theorem force_v {f : Fin nF} {p : Fin nR} (hA : (F.link f ∩ D1.link v).Nonempty)
    (hp : ((p : ℤ) - σ0 f).natAbs ≤ W) : rd D1 R h k u v W τ1 ρ p = (k : ℤ) + 1 := by
  have hv := H.near_of_meet hA hp
  have hnu : ¬ Near R (D1.link u) W p := fun hu =>
    H.not_near_both hu hv (by simp) (by omega)
  unfold rd
  rw [if_neg hnu, if_pos hv]

/-- The reading takes values between `h - 1` and `k + 1`. -/
theorem range (p : Fin nR) :
    (h : ℤ) - 1 ≤ rd D1 R h k u v W τ1 ρ p ∧ rd D1 R h k u v W τ1 ρ p ≤ (k : ℤ) + 1 := by
  have hhk : (h : ℕ) ≤ k := H.hk
  have hr := H.ρ_range (τ1 p)
  have hr1 : (h : ℕ) ≤ ρ (τ1 p) := hr.1
  have hr2 : (ρ (τ1 p) : ℕ) ≤ k := hr.2
  unfold rd
  split_ifs <;> constructor <;> omega

/-- Position `p` is *relevant*: within `W` of the reading of a link of `F` in `D_2(u, v)`. -/
def Rel (D1 : Chain X n1) (F : Chain X nF) (u v : Fin n1) (W : ℕ) (σ0 : Fin nF → Fin nR)
    (p : Fin nR) : Prop :=
  ∃ f : Fin nF, InS D1 F u v f ∧ ((p : ℤ) - σ0 f).natAbs ≤ W

omit H in
theorem normal_meet {D0 : Chain X n0} {D1 : Chain X n1} {R : Chain X nR} {a b : Fin n0}
    {t : Fin n1} {p : Fin nR} (h1 : R.link p ⊆ D0.link a) (h2 : R.link p ⊆ D1.link t)
    (h3 : D1.link t ⊆ D0.link b) : |(a : ℤ) - (b : ℤ)| ≤ 1 := by
  obtain ⟨z, hz⟩ := R.link_nonempty p
  have := (D0.adjacent a b).mp ⟨z, h1 hz, h3 (h2 hz)⟩
  rw [abs_le]; omega

/-- A ring position next to a normal relevant position: the readings differ by at most one. -/
theorem ring_normal_u {p p' : Fin nR} (hpp : ((p : ℤ) - p').natAbs ≤ W)
    (hp : Near R (D1.link u) (2 * W) p) (hrel : Rel D1 F u v W σ0 p')
    (h1 : ¬ Near R (D1.link u) W p') (h2 : ¬ Near R (D1.link v) W p') :
    |(h : ℤ) - (ρ (τ1 p') : ℤ)| ≤ 1 := by
  obtain ⟨f, hf, hfp⟩ := hrel
  obtain ⟨hu, hv⟩ := H.normal_range hf hfp h1 h2
  obtain ⟨q, hq, hq'⟩ := hp
  exact normal_meet (H.zoneU q p' hq (by omega)) (H.thick p' p' (by simp)) (H.ρ_sub _ hu hv)

theorem ring_normal_v {p p' : Fin nR} (hpp : ((p : ℤ) - p').natAbs ≤ W)
    (hp : Near R (D1.link v) (2 * W) p) (hrel : Rel D1 F u v W σ0 p')
    (h1 : ¬ Near R (D1.link u) W p') (h2 : ¬ Near R (D1.link v) W p') :
    |(k : ℤ) - (ρ (τ1 p') : ℤ)| ≤ 1 := by
  obtain ⟨f, hf, hfp⟩ := hrel
  obtain ⟨hu, hv⟩ := H.normal_range hf hfp h1 h2
  obtain ⟨q, hq, hq'⟩ := hp
  exact normal_meet (H.zoneV q p' hq (by omega)) (H.thick p' p' (by simp)) (H.ρ_sub _ hu hv)

theorem normal_normal {p p' : Fin nR} (hpp : ((p : ℤ) - p').natAbs ≤ W)
    (hrel : Rel D1 F u v W σ0 p) (hrel' : Rel D1 F u v W σ0 p')
    (h1 : ¬ Near R (D1.link u) W p) (h2 : ¬ Near R (D1.link v) W p)
    (h1' : ¬ Near R (D1.link u) W p') (h2' : ¬ Near R (D1.link v) W p') :
    |(ρ (τ1 p) : ℤ) - (ρ (τ1 p') : ℤ)| ≤ 1 := by
  obtain ⟨f, hf, hfp⟩ := hrel
  obtain ⟨hu, hv⟩ := H.normal_range hf hfp h1 h2
  obtain ⟨f', hf', hfp'⟩ := hrel'
  obtain ⟨hu', hv'⟩ := H.normal_range hf' hfp' h1' h2'
  exact normal_meet ((H.thick p p' hpp).trans (H.ρ_sub _ hu hv)) (H.thick p' p' (by simp))
    (H.ρ_sub _ hu' hv')

omit H in
theorem rd_cases (p : Fin nR) :
    (Near R (D1.link u) W p ∧ rd D1 R h k u v W τ1 ρ p = (h : ℤ) - 1) ∨
    (¬ Near R (D1.link u) W p ∧ Near R (D1.link v) W p ∧
      rd D1 R h k u v W τ1 ρ p = (k : ℤ) + 1) ∨
    (¬ Near R (D1.link u) W p ∧ ¬ Near R (D1.link v) W p ∧ Near R (D1.link u) (2 * W) p ∧
      rd D1 R h k u v W τ1 ρ p = (h : ℤ)) ∨
    (¬ Near R (D1.link u) W p ∧ ¬ Near R (D1.link v) W p ∧ ¬ Near R (D1.link u) (2 * W) p ∧
      Near R (D1.link v) (2 * W) p ∧ rd D1 R h k u v W τ1 ρ p = (k : ℤ)) ∨
    (¬ Near R (D1.link u) W p ∧ ¬ Near R (D1.link v) W p ∧ ¬ Near R (D1.link u) (2 * W) p ∧
      ¬ Near R (D1.link v) (2 * W) p ∧ rd D1 R h k u v W τ1 ρ p = (ρ (τ1 p) : ℤ)) := by
  unfold rd
  split_ifs <;> tauto

/-- **Slowness** of the end-zone reading between relevant positions. -/
theorem slow_rel {p p' : Fin nR} (hpp : ((p : ℤ) - p').natAbs ≤ W)
    (hrel : Rel D1 F u v W σ0 p) (hrel' : Rel D1 F u v W σ0 p') :
    |rd D1 R h k u v W τ1 ρ p - rd D1 R h k u v W τ1 ρ p'| ≤ 1 := by
  have hhk : (h : ℕ) ≤ k := H.hk
  have hp'p : ((p' : ℤ) - p).natAbs ≤ W := by omega
  rcases rd_cases (D1 := D1) (R := R) (u := u) (v := v) (W := W) (τ1 := τ1) (ρ := ρ) (h := h) (k := k) p with ⟨nu1, e⟩ | ⟨xu1, nv1, e⟩ | ⟨xu1, xv1, nu2, e⟩ |
    ⟨xu1, xv1, xu2, nv2, e⟩ | ⟨xu1, xv1, xu2, xv2, e⟩ <;>
  rcases rd_cases (D1 := D1) (R := R) (u := u) (v := v) (W := W) (τ1 := τ1) (ρ := ρ) (h := h) (k := k) p' with ⟨mu1, e'⟩ | ⟨yu1, mv1, e'⟩ | ⟨yu1, yv1, mu2, e'⟩ |
    ⟨yu1, yv1, yu2, mv2, e'⟩ | ⟨yu1, yv1, yu2, yv2, e'⟩
  all_goals rw [e, e']
  · (rw [abs_le]; constructor <;> linarith)
  · (exfalso; exact H.not_near_both nu1 mv1 hpp (by omega))
  · (rw [abs_le]; constructor <;> linarith)
  · (exfalso; exact H.not_near_both nu1 mv2 hpp (by omega))
  · (exfalso; exact yu2 ((nu1.shift hpp).mono (by omega)))
  · (exfalso; exact H.not_near_both mu1 nv1 hp'p (by omega))
  · (rw [abs_le]; constructor <;> linarith)
  · (exfalso; exact H.not_near_both mu2 nv1 hp'p (by omega))
  · (rw [abs_le]; constructor <;> linarith)
  · (exfalso; exact yv2 ((nv1.shift hpp).mono (by omega)))
  · (rw [abs_le]; constructor <;> linarith)
  · (exfalso; exact H.not_near_both nu2 mv1 hpp (by omega))
  · (rw [abs_le]; constructor <;> linarith)
  · (exfalso; exact H.not_near_both nu2 mv2 hpp (by omega))
  · exact H.ring_normal_u hpp nu2 hrel' yu1 yv1
  · (exfalso; exact H.not_near_both mu1 nv2 hp'p (by omega))
  · (rw [abs_le]; constructor <;> linarith)
  · (exfalso; exact H.not_near_both mu2 nv2 hp'p (by omega))
  · (rw [abs_le]; constructor <;> linarith)
  · exact H.ring_normal_v hpp nv2 hrel' yu1 yv1
  · (exfalso; exact xu2 ((mu1.shift hp'p).mono (by omega)))
  · (exfalso; exact xv2 ((mv1.shift hp'p).mono (by omega)))
  · (rw [abs_sub_comm]; exact H.ring_normal_u hp'p mu2 hrel xu1 xv1)
  · (rw [abs_sub_comm]; exact H.ring_normal_v hp'p mv2 hrel xu1 xv1)
  · exact H.normal_normal hpp hrel hrel' xu1 xv1 yu1 yv1

end Setup

end HPC.T5
