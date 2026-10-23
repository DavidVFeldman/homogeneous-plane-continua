import HPC.PseudoArc.T5Runs
import HPC.PseudoArc.Statements79

/-!
# Theorem 5: assembling the lifts over the runs

Batch 80. The links of the fine chain `F` lying in `D_2(u, v)` fall into maximal runs of
consecutive links; each run begins and ends at a link meeting `d(2)_u ∪ d(2)_v`, and the extended
pattern is lifted over each run (`run_lift_geom`). The lifts, shifted down by one and clamped,
define a block assignment of the links in `D_2(u, v)`, and the unions of the blocks form the chain
`E` of Theorem 5. A run crossing from `d(2)_u` to `d(2)_v` makes the blocks consecutive.
-/

namespace HPC.T5

open Set

/-! ## Maximal runs of a predicate on `ℕ` -/

section Runs

variable (Sn : ℕ → Prop)

/-- `[a, b]` is a maximal run of `Sn`. -/
def IsRun (a b : ℕ) : Prop :=
  a ≤ b ∧ (∀ g, a ≤ g → g ≤ b → Sn g) ∧ (a = 0 ∨ ¬ Sn (a - 1)) ∧ ¬ Sn (b + 1)

variable {Sn}

theorem exists_run {f : ℕ} (hf : Sn f) (hbd : ∃ B, ∀ g, B ≤ g → ¬ Sn g) :
    ∃ a b, a ≤ f ∧ f ≤ b ∧ IsRun Sn a b := by
  classical
  have hA : ∃ a, a ≤ f ∧ ∀ g, a ≤ g → g ≤ f → Sn g :=
    ⟨f, le_rfl, fun g h1 h2 => by rwa [show g = f by omega]⟩
  obtain ⟨B, hB⟩ := hbd
  have hD : ∃ d, ¬ Sn (f + d + 1) := ⟨B, hB _ (by omega)⟩
  set a := Nat.find hA
  set d := Nat.find hD
  have ha := Nat.find_spec hA
  have hd := Nat.find_spec hD
  have hdmin : ∀ d' < d, Sn (f + d' + 1) := fun d' hd' => by
    have := Nat.find_min hD hd'
    push_neg at this
    exact this
  refine ⟨a, f + d, ha.1, by omega, by omega, fun g h1 h2 => ?_, ?_, hd⟩
  · rcases Nat.lt_or_ge f g with hfg | hfg
    · have := hdmin (g - f - 1) (by omega)
      rwa [show f + (g - f - 1) + 1 = g by omega] at this
    · exact ha.2 g h1 hfg
  · by_contra hcon
    push_neg at hcon
    obtain ⟨ha0, hSa⟩ := hcon
    have : a - 1 ∈ {a' | a' ≤ f ∧ ∀ g, a' ≤ g → g ≤ f → Sn g} := by
      refine ⟨by omega, fun g h1 h2 => ?_⟩
      rcases Nat.eq_or_lt_of_le h1 with he | hlt
      · rw [← he]; exact hSa
      · exact ha.2 g (by omega) h2
    exact Nat.find_min hA (show a - 1 < a by omega) this

theorem run_unique {a b a' b' f : ℕ} (h1 : IsRun Sn a b) (h2 : IsRun Sn a' b')
    (hf : a ≤ f ∧ f ≤ b) (hf' : a' ≤ f ∧ f ≤ b') : a = a' ∧ b = b' := by
  obtain ⟨-, hS, ha, hb⟩ := h1
  obtain ⟨-, hS', ha', hb'⟩ := h2
  constructor
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · rcases ha' with h0 | h0
      · omega
      · exact h0 (hS (a' - 1) (by omega) (by omega))
    · rcases ha with h0 | h0
      · omega
      · exact h0 (hS' (a - 1) (by omega) (by omega))
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hb (hS' (b + 1) (by omega) (by omega))
    · exact hb' (hS (b' + 1) (by omega) (by omega))

end Runs

/-! ## The crossing run -/

section Crossing

variable {X : Type*} [MetricSpace X] {n1 nF : ℕ}

/-- A chain `F` from `P` to `Q` refining a chain `D1` from `P` to `Q` crosses from `d(2)_u` to
`d(2)_v` inside `D_2(u, v)`. -/
theorem exists_crossing {D1 : Chain X n1} {F : Chain X nF} {P Q : X} (hF : F.IsFrom P Q)
    (hD1 : D1.IsFrom P Q) (σ1 : Fin nF → Fin n1) (hσ1 : ∀ t, F.link t ⊆ D1.link (σ1 t))
    {u v : Fin n1} (huv : u < v) :
    ∃ tu tv, ∃ _ : tu ≤ tv, ∃ htv : tv < nF,
      (∀ g (hg : g < nF), tu ≤ g → g ≤ tv → InS D1 F u v ⟨g, hg⟩) ∧
      F.link ⟨tu, by omega⟩ ⊆ D1.link u ∧ F.link ⟨tv, htv⟩ ⊆ D1.link v := by
  classical
  obtain ⟨hnF, hP, hQ, -, -⟩ := hF
  obtain ⟨hn1, hP1, hQ1, hPu1, hQu1⟩ := hD1
  let s : ℕ → ℕ := fun f => σ1 ⟨min f (nF - 1), by omega⟩
  have hsv : ∀ f (hf : f < nF), s f = σ1 ⟨f, hf⟩ := fun f hf => by
    simp only [s]; rw [show (⟨min f (nF - 1), by omega⟩ : Fin nF) = ⟨f, hf⟩ from
      Fin.ext (by simp; omega)]
  have hs0 : s 0 = 0 := by
    rw [hsv 0 hnF]
    have := hPu1 _ (hσ1 _ hP)
    rw [this]
  have hsT : s (nF - 1) = n1 - 1 := by
    rw [hsv (nF - 1) (by omega)]
    have := hQu1 _ (hσ1 _ hQ)
    rw [this]
  have hslip : ∀ f, s (f + 1) ≤ s f + 1 ∧ s f ≤ s (f + 1) + 1 := by
    intro f
    have := Chain.pattern_lipschitz hσ1 ⟨min (f + 1) (nF - 1), by omega⟩
      ⟨min f (nF - 1), by omega⟩ ((F.adjacent_iff _ _).mpr (by simp only; omega))
    simp only [s]; omega
  have hvlt : (v : ℕ) < n1 := v.isLt
  have hex : ∃ f, (v : ℕ) ≤ s f := ⟨nF - 1, by rw [hsT]; omega⟩
  set tv := Nat.find hex with htv_def
  have htv : (v : ℕ) ≤ s tv := Nat.find_spec hex
  have htvmin : ∀ g < tv, s g < v := fun g hg => by
    have := Nat.find_min hex hg; omega
  have hu : (u : ℕ) < v := huv
  have htv0 : 0 < tv := by
    by_contra h0
    have : tv = 0 := by omega
    rw [this, hs0] at htv; omega
  have htvn : tv < nF := by
    have := Nat.find_min' hex (show (v : ℕ) ≤ s (nF - 1) by rw [hsT]; omega)
    omega
  have hstv : s tv = v := by
    have h1 := htvmin (tv - 1) (by omega)
    have h2 := hslip (tv - 1)
    rw [show tv - 1 + 1 = tv by omega] at h2
    omega
  set tu := Nat.findGreatest (fun f => s f ≤ u) tv with htu_def
  have htu : s tu ≤ u := by
    have := Nat.findGreatest_spec (P := fun f => s f ≤ (u : ℕ)) (m := 0) (n := tv) (by omega)
      (by simp [hs0])
    exact this
  have htule : tu ≤ tv := Nat.findGreatest_le tv
  have htugt : ∀ g, tu < g → g ≤ tv → (u : ℕ) < s g := fun g h1 h2 => by
    have := Nat.findGreatest_is_greatest (P := fun f => s f ≤ (u : ℕ)) h1 h2
    simp only [not_le] at this
    exact this
  have htultv : tu < tv := by
    rcases Nat.eq_or_lt_of_le htule with he | hlt
    · rw [he] at htu; omega
    · exact hlt
  have hstu : s tu = u := by
    have h1 := htugt (tu + 1) (by omega) (by omega)
    have h2 := hslip tu
    omega
  refine ⟨tu, tv, htule, htvn, fun g hg h1 h2 => ?_, ?_, ?_⟩
  · refine ⟨σ1 ⟨g, hg⟩, ?_, ?_, hσ1 _⟩
    · rw [Fin.le_def, ← hsv g hg]
      rcases Nat.eq_or_lt_of_le h1 with he | hlt
      · rw [← he, hstu]
      · exact (htugt g hlt h2).le
    · rw [Fin.le_def, ← hsv g hg]
      rcases Nat.eq_or_lt_of_le h2 with he | hlt
      · rw [he, hstv]
      · exact (htvmin g hlt).le
  · have : σ1 ⟨tu, by omega⟩ = u := Fin.ext (by rw [← hsv tu (by omega), hstu])
    rw [← this]; exact hσ1 _
  · have : σ1 ⟨tv, htvn⟩ = v := Fin.ext (by rw [← hsv tv htvn, hstv])
    rw [← this]; exact hσ1 _

/-- At a boundary of `D_2(u, v)` along `F`, the link inside lies in `d(2)_u` or `d(2)_v`. -/
theorem touch_of_boundary {D1 : Chain X n1} {F : Chain X nF} (σ1 : Fin nF → Fin n1)
    (hσ1 : ∀ t, F.link t ⊆ D1.link (σ1 t)) {u v : Fin n1} {t t' : Fin nF}
    (hadj : t'.val = t.val + 1 ∨ t.val = t'.val + 1) (ht : InS D1 F u v t)
    (ht' : ¬ InS D1 F u v t') : F.link t ⊆ D1.link u ∨ F.link t ⊆ D1.link v := by
  obtain ⟨s, hus, hsv, hts⟩ := ht
  obtain ⟨z, hz1, hz2⟩ := (F.adjacent_iff t t').mpr (by omega)
  have hadj1 := (D1.adjacent_iff s (σ1 t')).mp ⟨z, hts hz1, hσ1 t' hz2⟩
  have hout : ¬ (u ≤ σ1 t' ∧ σ1 t' ≤ v) := fun h => ht' ⟨σ1 t', h.1, h.2, hσ1 t'⟩
  simp only [Fin.le_def] at hout hus hsv
  by_cases hsu : (s : ℕ) = u
  · left; rw [show s = u from Fin.ext hsu] at hts; exact hts
  · right
    have : (s : ℕ) = v := by omega
    rw [show s = v from Fin.ext this] at hts; exact hts

end Crossing

end HPC.T5
