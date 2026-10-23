import HPC.BJ59.Thm10Lib

/-!
# Batch 201, §3: the pattern of a map of a fibre (Step 2(b), p. 184)

`exists_pattern`, with the clause on links strengthened (shape change, recorded in the report):
the values lie in the run `[w₁, w₂]` for *every* link, and the inclusion holds for every link
whose closure meets `Q`. Route: commission 201 §3.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Pattern

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- **The pattern of a map of a fibre** (Step 2(b), p. 184): a fine chain covering `Q` maps into
a run of `D` covering `φ(Q)`, following `φ` on closures, with each link of the run the image of
three consecutive links meeting `Q`. (Shape change: the second clause is stated for every link,
with values in the run, and with the closure condition.) -/
theorem exists_pattern {Q : Set Y} (hQ : IsCompact Q) (hQc : IsPreconnected Q)
    (hQn : Q.Nontrivial) (φ : Q → X) (hφ : Continuous φ) {n : ℕ} (D : Chain X n)
    {w₁ w₂ : ℕ} (hw : w₁ ≤ w₂) (hw₂ : w₂ < n)
    (hcov : ∀ z, φ z ∈ ⋃ (j : Fin n) (_ : w₁ ≤ j.val ∧ j.val ≤ w₂), D.link j)
    (hpriv : ∀ j : Fin n, w₁ ≤ j.val → j.val ≤ w₂ → ∃ z, φ z ∈ D.link j ∧
      ∀ j' : Fin n, w₁ ≤ j'.val → j'.val ≤ w₂ → j' ≠ j → φ z ∉ D.link j') :
    ∃ ε > 0, ∀ (N : ℕ) (F : Chain Y N), IsEpsChain F ε → Q ⊆ F.union →
      ∃ R : Fin N → Fin n, IsChainMap R ∧
        (∀ a : Fin N, w₁ ≤ (R a).val ∧ (R a).val ≤ w₂) ∧
        (∀ a : Fin N, ∀ z : Q, (z : Y) ∈ closure (F.link a) → φ z ∈ D.link (R a)) ∧
        ∀ j : Fin n, w₁ ≤ j.val → j.val ≤ w₂ → ∃ a : ℕ, ∃ ha : a + 2 < N,
          ∀ (c : ℕ) (hc : c ≤ 2), (F.link ⟨a + c, by omega⟩ ∩ Q).Nonempty ∧
            R ⟨a + c, by omega⟩ = j := by
  classical
  haveI : CompactSpace Q := isCompact_iff_compactSpace.1 hQ
  -- links of `D` on natural indices
  set Dl : ℕ → Set X := fun j => if h : j < n then D.link ⟨j, h⟩ else ∅ with hDl
  have hDl_fin : ∀ j : Fin n, Dl j.val = D.link j := fun j => by simp [hDl, j.isLt]
  -- Lebesgue number of the cover of `φ(Q)` by the links of the run
  set c : Fin n → Set X := fun j => if w₁ ≤ j.val ∧ j.val ≤ w₂ then D.link j else ∅ with hc
  have hco : ∀ j, IsOpen (c j) := fun j => by
    simp only [hc]; split_ifs; exacts [D.isOpen j, isOpen_empty]
  have hcov' : range φ ⊆ ⋃ j, c j := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨j, hj, hz⟩ := mem_iUnion₂.1 (hcov z)
    exact mem_iUnion.2 ⟨j, by simp only [hc, if_pos hj]; exact hz⟩
  obtain ⟨lam, hlam, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_range hφ) hco hcov'
  obtain ⟨ρ, hρ, hρφ⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hφ) lam hlam
  -- a nonempty part of `Q` of small diameter maps into one link of the run
  have key : ∀ S : Set Y, (∃ z : Q, (z : Y) ∈ S) → (∀ x ∈ S, ∀ y ∈ S, dist x y < ρ) →
      ∃ j : ℕ, w₁ ≤ j ∧ j ≤ w₂ ∧ ∀ z : Q, (z : Y) ∈ S → φ z ∈ Dl j := by
    rintro S ⟨z₀, hz₀⟩ hS
    obtain ⟨j, hj⟩ := hleb (φ z₀) (mem_range_self z₀)
    have hjW : w₁ ≤ j.val ∧ j.val ≤ w₂ := by
      by_contra h
      have : φ z₀ ∈ c j := hj (mem_ball_self hlam)
      simp only [hc, if_neg h] at this
      exact this
    refine ⟨j.val, hjW.1, hjW.2, fun z hz => ?_⟩
    have : φ z ∈ c j := hj (by
      rw [mem_ball]; exact hρφ (by rw [Subtype.dist_eq]; exact hS _ hz _ hz₀))
    rw [hDl_fin]
    simpa [hc, if_pos hjW] using this
  -- the diameter of `Q`
  have hdQ : 0 < Metric.diam Q := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hQn
    exact lt_of_lt_of_le (dist_pos.2 hxy) (dist_le_diam_of_mem hQ.isBounded hx hy)
  refine ⟨min (ρ / 5) (Metric.diam Q / 4), lt_min (by linarith) (by linarith), ?_⟩
  intro N F hF hQF
  set ε := min (ρ / 5) (Metric.diam Q / 4) with hε
  have hε1 : ε ≤ ρ / 5 := min_le_left _ _
  have hε2 : ε ≤ Metric.diam Q / 4 := min_le_right _ _
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  -- links of `F` on natural indices
  set L : ℕ → Set Y := fun a => if h : a < N then F.link ⟨a, h⟩ else ∅ with hL
  have hL_fin : ∀ a : Fin N, L a.val = F.link a := fun a => by simp [hL, a.isLt]
  have hL_lt : ∀ a, (closure (L a)).Nonempty → a < N := by
    intro a ⟨x, hx⟩
    by_contra h
    simp only [hL, dif_neg h, closure_empty] at hx
    exact hx
  have hdistL : ∀ a b x y, x ∈ closure (L a) → y ∈ closure (L b) →
      dist x y < (((a : ℤ) - b).natAbs + 1) * ε := by
    intro a b x y hx hy
    have ha := hL_lt a ⟨x, hx⟩
    have hb := hL_lt b ⟨y, hy⟩
    have := dist_lt_of_mem_closure_link' hF ⟨a, ha⟩ ⟨b, hb⟩
      (by rw [← hL_fin ⟨a, ha⟩]; exact hx) (by rw [← hL_fin ⟨b, hb⟩]; exact hy)
    simpa using this
  -- `T`: links whose closure meets `Q`; `T₀`: links meeting `Q`
  set inT : ℕ → Prop := fun a => (closure (L a) ∩ Q).Nonempty with hinT
  set inT₀ : ℕ → Prop := fun a => (L a ∩ Q).Nonempty with hinT₀
  have hT₀T : ∀ a, inT₀ a → inT a := fun a ⟨z, hz1, hz2⟩ => ⟨z, subset_closure hz1, hz2⟩
  have hQL : ∀ z ∈ Q, ∃ a, z ∈ L a ∧ a < N := by
    intro z hz
    obtain ⟨a, ha⟩ := mem_iUnion.1 (hQF hz)
    exact ⟨a.val, by rw [hL_fin]; exact ha, a.isLt⟩
  have hTnear : ∀ a, inT a → ∃ a', inT₀ a' ∧ a' ≤ a + 1 ∧ a ≤ a' + 1 := by
    intro a ⟨z, hz1, hz2⟩
    obtain ⟨a', ha', ha'N⟩ := hQL z hz2
    have ha := hL_lt a ⟨z, hz1⟩
    refine ⟨a', ⟨z, ha', hz2⟩, ?_⟩
    have hopen : IsOpen (L a') := by
      rw [show L a' = F.link ⟨a', ha'N⟩ from hL_fin ⟨a', ha'N⟩]; exact F.isOpen _
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hz1 (L a') hopen ha'
    rw [show L a = F.link ⟨a, ha⟩ from hL_fin ⟨a, ha⟩] at hw2
    rw [show L a' = F.link ⟨a', ha'N⟩ from hL_fin ⟨a', ha'N⟩] at hw1
    have := (F.adjacent_iff ⟨a, ha⟩ ⟨a', ha'N⟩).1 ⟨w, hw2, hw1⟩
    simp only at this
    omega
  have hT₀conv : ∀ a b c, inT₀ a → inT₀ c → a ≤ b → b ≤ c → inT₀ b := by
    intro a b c ha hc hab hbc
    have haN : a < N := hL_lt a ⟨ha.some, subset_closure ha.some_mem.1⟩
    have hcN : c < N := hL_lt c ⟨hc.some, subset_closure hc.some_mem.1⟩
    have hmb := meets_between F hQc hQF (i := ⟨a, haN⟩) (j := ⟨c, hcN⟩)
      (by obtain ⟨z, hz1, hz2⟩ := ha; exact ⟨z, hz2, by rw [← hL_fin]; exact hz1⟩)
      (by obtain ⟨z, hz1, hz2⟩ := hc; exact ⟨z, hz2, by rw [← hL_fin]; exact hz1⟩)
      ⟨b, by omega⟩ (by simp only; omega) (by simp only; omega)
    obtain ⟨z, hz1, hz2⟩ := hmb
    exact ⟨z, by rw [show L b = F.link ⟨b, by omega⟩ from hL_fin ⟨b, by omega⟩]; exact hz2, hz1⟩
  have hTconv : ∀ a b c, inT a → inT c → a ≤ b → b ≤ c → inT b := by
    intro a b c ha hc hab hbc
    obtain ⟨a', ha', h1, h2⟩ := hTnear a ha
    obtain ⟨c', hc', h3, h4⟩ := hTnear c hc
    by_cases hb1 : b = a
    · exact hb1 ▸ ha
    by_cases hb2 : b = c
    · exact hb2 ▸ hc
    apply hT₀T
    rcases le_total a' c' with h | h
    · exact hT₀conv a' b c' ha' hc' (by omega) (by omega)
    · exact hT₀conv c' b a' hc' ha' (by omega) (by omega)
  -- `T₀` has at least four elements
  obtain ⟨z₀, hz₀⟩ := hQn.nonempty
  obtain ⟨a₀, ha₀, ha₀N⟩ := hQL z₀ hz₀
  have hT₀a₀ : inT₀ a₀ := ⟨z₀, ha₀, hz₀⟩
  have hT₀N : ∀ a, inT₀ a → a < N := fun a ha =>
    hL_lt a ⟨ha.some, subset_closure ha.some_mem.1⟩
  have hTN : ∀ a, inT a → a < N := fun a ha => hL_lt a ⟨ha.some, ha.some_mem.1⟩
  have hex₀ : ∃ a, inT₀ a := ⟨a₀, hT₀a₀⟩
  set p := Nat.find hex₀ with hp
  have hpT : inT₀ p := Nat.find_spec hex₀
  have hp_le : ∀ a, inT₀ a → p ≤ a := fun a ha => Nat.find_min' hex₀ ha
  have hbdd : ∃ q, inT₀ q ∧ ∀ a, inT₀ a → a ≤ q := by
    have hfin : (Finset.range N).filter inT₀ |>.Nonempty :=
      ⟨a₀, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha₀N, hT₀a₀⟩⟩
    refine ⟨((Finset.range N).filter inT₀).max' hfin, (Finset.mem_filter.1
      (Finset.max'_mem _ hfin)).2, fun a ha => Finset.le_max' _ a ?_⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hT₀N a ha), ha⟩
  obtain ⟨q, hqT, hq_ge⟩ := hbdd
  have hpq : p + 3 ≤ q := by
    by_contra hlt
    have hdle : Metric.diam Q ≤ 3 * ε := by
      apply Metric.diam_le_of_forall_dist_le (by linarith)
      intro x hx y hy
      obtain ⟨a, hxa, -⟩ := hQL x hx
      obtain ⟨b, hyb, -⟩ := hQL y hy
      have ha1 := hp_le a ⟨x, hxa, hx⟩
      have ha2 := hq_ge a ⟨x, hxa, hx⟩
      have hb1 := hp_le b ⟨y, hyb, hy⟩
      have hb2 := hq_ge b ⟨y, hyb, hy⟩
      have h := hdistL a b x y (subset_closure hxa) (subset_closure hyb)
      have : (((a : ℤ) - b).natAbs : ℝ) ≤ 2 := by
        have : ((a : ℤ) - b).natAbs ≤ 2 := by omega
        exact_mod_cast this
      nlinarith
    linarith
  -- the sets `S a`
  set S : ℕ → ℕ → Prop := fun a j => w₁ ≤ j ∧ j ≤ w₂ ∧
    ∀ z : Q, (z : Y) ∈ closure (L a) → φ z ∈ Dl j with hS
  have hSnear : ∀ a j j', inT a → S a j → S a j' → j ≤ j' + 1 ∧ j' ≤ j + 1 := by
    intro a j j' ⟨z, hz1, hz2⟩ hj hj'
    have h1 := hj.2.2 ⟨z, hz2⟩ hz1
    have h2 := hj'.2.2 ⟨z, hz2⟩ hz1
    have hjn : j < n := by omega
    have hj'n : j' < n := by omega
    rw [show Dl j = D.link ⟨j, hjn⟩ from hDl_fin ⟨j, hjn⟩] at h1
    rw [show Dl j' = D.link ⟨j', hj'n⟩ from hDl_fin ⟨j', hj'n⟩] at h2
    have := (D.adjacent_iff ⟨j, hjn⟩ ⟨j', hj'n⟩).1 ⟨_, h1, h2⟩
    simpa using this
  -- five consecutive links: a common index
  have hcommon : ∀ a a', inT a → a ≤ a' → a' ≤ a + 4 →
      ∃ j, ∀ b, a ≤ b → b ≤ a' → S b j := by
    intro a a' ha haa' ha'
    set U : Set Y := ⋃ (b : ℕ) (_ : a ≤ b ∧ b ≤ a'), closure (L b) with hU
    obtain ⟨z, hz1, hz2⟩ := ha
    obtain ⟨j, hj1, hj2, hj⟩ := key U ⟨⟨z, hz2⟩, mem_iUnion₂.2 ⟨a, ⟨le_rfl, haa'⟩, hz1⟩⟩
      (by
        intro x hx y hy
        obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.1 hx
        obtain ⟨b', hb', hyb'⟩ := mem_iUnion₂.1 hy
        have h := hdistL b b' x y hxb hyb'
        have : (((b : ℤ) - b').natAbs : ℝ) ≤ 4 := by
          have : ((b : ℤ) - b').natAbs ≤ 4 := by omega
          exact_mod_cast this
        nlinarith)
    exact ⟨j, fun b hb1 hb2 => ⟨hj1, hj2, fun w hw => hj w (mem_iUnion₂.2 ⟨b, ⟨hb1, hb2⟩, hw⟩)⟩⟩
  have hcommon' : ∀ a a', inT a → inT a' → ((a : ℤ) - a').natAbs ≤ 4 →
      ∃ j, S a j ∧ S a' j := by
    intro a a' ha ha' h
    rcases le_total a a' with hle | hle
    · obtain ⟨j, hj⟩ := hcommon a a' ha hle (by omega)
      exact ⟨j, hj a le_rfl hle, hj a' hle le_rfl⟩
    · obtain ⟨j, hj⟩ := hcommon a' a ha' hle (by omega)
      exact ⟨j, hj a hle le_rfl, hj a' le_rfl hle⟩
  have hSne : ∀ a, inT a → ∃ j, S a j := fun a ha => by
    obtain ⟨j, hj, -⟩ := hcommon' a a ha ha (by simp)
    exact ⟨j, hj⟩
  -- decided positions
  set Dec : ℕ → Prop := fun b => inT b ∧ ∃ j, S b j ∧ ∀ j', S b j' → j' = j with hDec
  set val : ℕ → ℕ := fun b => if h : Dec b then h.2.choose else 0 with hval
  have hval_spec : ∀ b, Dec b → S b (val b) ∧ ∀ j', S b j' → j' = val b := by
    intro b hb
    simp only [hval, dif_pos hb]
    exact hb.2.choose_spec
  have hdec_mem : ∀ b a, Dec b → inT a → ((b : ℤ) - a).natAbs ≤ 4 → S a (val b) := by
    intro b a hb ha h
    obtain ⟨j, hj1, hj2⟩ := hcommon' b a hb.1 ha h
    have := (hval_spec b hb).2 j hj1
    rw [← this]; exact hj2
  have hdec_eq : ∀ b b', Dec b → Dec b' → ((b : ℤ) - b').natAbs ≤ 4 → val b = val b' := by
    intro b b' hb hb' h
    have := hdec_mem b b' hb hb'.1 h
    exact ((hval_spec b' hb').2 _ this)
  -- the map on `T`
  set R₀ : ℕ → ℕ := fun a : ℕ =>
    if h : ∃ b, Dec b ∧ ((a : ℤ) - b).natAbs ≤ 2 then val h.choose
    else if h' : ∃ j, S a j then Nat.find h' else 0 with hR₀
  have hR₀_mem : ∀ a, inT a → S a (R₀ a) := by
    intro a ha
    simp only [hR₀]
    split_ifs with h h'
    · exact hdec_mem _ a h.choose_spec.1 ha (by have := h.choose_spec.2; omega)
    · exact Nat.find_spec h'
    · exact absurd (hSne a ha) h'
  have hR₀_dec : ∀ a b : ℕ, Dec b → ((a : ℤ) - b).natAbs ≤ 2 → R₀ a = val b := by
    intro a b hb hab
    have h : ∃ b, Dec b ∧ ((a : ℤ) - b).natAbs ≤ 2 := ⟨b, hb, hab⟩
    simp only [hR₀, dif_pos h]
    exact hdec_eq _ _ h.choose_spec.1 hb (by have := h.choose_spec.2; omega)
  have hR₀_chain : ∀ a, inT a → inT (a + 1) → R₀ a ≤ R₀ (a + 1) + 1 ∧ R₀ (a + 1) ≤ R₀ a + 1 := by
    intro a ha ha1
    by_cases h1 : ∃ b, Dec b ∧ ((a : ℤ) - b).natAbs ≤ 2
    · obtain ⟨b, hb, hab⟩ := h1
      rw [hR₀_dec a b hb hab]
      exact hSnear (a + 1) _ _ ha1 (hdec_mem b (a + 1) hb ha1 (by omega)) (hR₀_mem _ ha1)
    by_cases h2 : ∃ b, Dec b ∧ (((a + 1 : ℕ) : ℤ) - b).natAbs ≤ 2
    · obtain ⟨b, hb, hab⟩ := h2
      rw [hR₀_dec (a + 1) b hb (by push_cast at hab ⊢; omega)]
      have := hSnear a _ _ ha (hdec_mem b a hb ha (by push_cast at hab; omega)) (hR₀_mem _ ha)
      omega
    -- both are least elements
    have e1 : R₀ a = Nat.find (hSne a ha) := by simp only [hR₀, dif_neg h1, dif_pos (hSne a ha)]
    have e2 : R₀ (a + 1) = Nat.find (hSne (a + 1) ha1) := by
      simp only [hR₀]; rw [dif_neg h2, dif_pos (hSne (a + 1) ha1)]
    obtain ⟨j, hj1, hj2⟩ := hcommon' a (a + 1) ha ha1 (by omega)
    have m1 := Nat.find_min' (hSne a ha) hj1
    have m2 := Nat.find_min' (hSne (a + 1) ha1) hj2
    have n1 := hSnear a _ _ ha (Nat.find_spec (hSne a ha)) hj1
    have n2 := hSnear (a + 1) _ _ ha1 (Nat.find_spec (hSne (a + 1) ha1)) hj2
    rw [e1, e2]
    omega
  -- the bounds of `T`
  have hexT : ∃ a, inT a := ⟨p, hT₀T p hpT⟩
  set t₁ := Nat.find hexT with ht₁
  have ht₁T : inT t₁ := Nat.find_spec hexT
  have ht₁_le : ∀ a, inT a → t₁ ≤ a := fun a ha => Nat.find_min' hexT ha
  have hbddT : ∃ t₂, inT t₂ ∧ ∀ a, inT a → a ≤ t₂ := by
    have hfin : (Finset.range N).filter inT |>.Nonempty :=
      ⟨p, Finset.mem_filter.2 ⟨Finset.mem_range.2 (hTN p (hT₀T p hpT)), hT₀T p hpT⟩⟩
    refine ⟨((Finset.range N).filter inT).max' hfin, (Finset.mem_filter.1
      (Finset.max'_mem _ hfin)).2, fun a ha => Finset.le_max' _ a ?_⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hTN a ha), ha⟩
  obtain ⟨t₂, ht₂T, ht₂_ge⟩ := hbddT
  have ht₁₂ : t₁ ≤ t₂ := ht₁_le t₂ ht₂T
  have hTiff : ∀ a, t₁ ≤ a → a ≤ t₂ → inT a := fun a h1 h2 => hTconv t₁ a t₂ ht₁T ht₂T h1 h2
  set cl : ℕ → ℕ := fun a => max t₁ (min a t₂) with hcl
  have hclT : ∀ a, inT (cl a) := fun a => hTiff _ (le_max_left _ _) (by simp only [hcl]; omega)
  have hcl_id : ∀ a, inT a → cl a = a := fun a ha => by
    have := ht₁_le a ha; have := ht₂_ge a ha; simp only [hcl]; omega
  have hR₀W : ∀ a, w₁ ≤ R₀ (cl a) ∧ R₀ (cl a) ≤ w₂ := fun a =>
    ⟨(hR₀_mem _ (hclT a)).1, (hR₀_mem _ (hclT a)).2.1⟩
  -- the map
  refine ⟨fun a => ⟨R₀ (cl a.val), by have := (hR₀W a.val).2; omega⟩, ?_, ?_, ?_, ?_⟩
  · -- chain map
    intro a b hab
    simp only
    have key2 : ∀ a b : ℕ, b = a + 1 → ((R₀ (cl a) : ℤ) - R₀ (cl b)).natAbs ≤ 1 := by
      intro a b hb
      subst hb
      by_cases h : cl (a + 1) = cl a
      · rw [h]; simp
      · have hc : cl (a + 1) = cl a + 1 := by simp only [hcl] at h ⊢; omega
        rw [hc]
        have := hR₀_chain (cl a) (hclT a) (hc ▸ hclT (a + 1))
        omega
    rcases lt_trichotomy a.val b.val with h | h | h
    · exact key2 a.val b.val (by omega)
    · rw [h]; simp
    · have := key2 b.val a.val (by omega)
      omega
  · intro a
    exact hR₀W a.val
  · intro a z hz
    have ha : inT a.val := ⟨z, by rw [hL_fin]; exact hz, z.2⟩
    have hlt : R₀ a.val < n := by have := (hR₀_mem a.val ha).2.1; omega
    have he : (⟨R₀ (cl a.val), by have := (hR₀W a.val).2; omega⟩ : Fin n) = ⟨R₀ a.val, hlt⟩ :=
      Fin.ext (by simp only; rw [hcl_id _ ha])
    show φ z ∈ D.link ⟨R₀ (cl a.val), _⟩
    rw [he]
    have := (hR₀_mem a.val ha).2.2 z (by rw [hL_fin]; exact hz)
    rw [show Dl (R₀ a.val) = D.link ⟨R₀ a.val, hlt⟩ from hDl_fin ⟨_, hlt⟩] at this
    exact this
  · -- the pattern
    intro j hj1 hj2
    obtain ⟨z, hzj, hzo⟩ := hpriv j hj1 hj2
    obtain ⟨a, hza, haN⟩ := hQL z z.2
    have haT₀ : inT₀ a := ⟨z, hza, z.2⟩
    have haT : inT a := hT₀T a haT₀
    have hdec : Dec a := by
      refine ⟨haT, j.val, ⟨hj1, hj2, fun w hw => ?_⟩, fun j' hj' => ?_⟩
      · obtain ⟨j₀, hj₀⟩ := hSne a haT
        have h1 := hj₀.2.2 z (subset_closure hza)
        have hj₀n : j₀ < n := by omega
        rw [show Dl j₀ = D.link ⟨j₀, hj₀n⟩ from hDl_fin ⟨j₀, hj₀n⟩] at h1
        have : (⟨j₀, hj₀n⟩ : Fin n) = j := by
          by_contra hne
          exact hzo ⟨j₀, hj₀n⟩ hj₀.1 hj₀.2.1 hne h1
        have h2 := hj₀.2.2 w hw
        rw [show Dl j₀ = D.link ⟨j₀, hj₀n⟩ from hDl_fin ⟨j₀, hj₀n⟩, this] at h2
        rw [hDl_fin]; exact h2
      · have h1 := hj'.2.2 z (subset_closure hza)
        have hj'n : j' < n := by omega
        rw [show Dl j' = D.link ⟨j', hj'n⟩ from hDl_fin ⟨j', hj'n⟩] at h1
        by_contra hne
        exact hzo ⟨j', hj'n⟩ hj'.1 hj'.2.1 (fun h => hne (by rw [← h])) h1
    have hva : val a = j.val := by
      have := (hval_spec a hdec).2 j.val ⟨hj1, hj2, fun w hw => ?_⟩
      · exact this.symm
      · have h1 := (hval_spec a hdec).1.2.2 w hw
        have h0 := (hval_spec a hdec).1.2.2 z (subset_closure hza)
        have hvn : val a < n := by have := (hval_spec a hdec).1.2.1; omega
        rw [show Dl (val a) = D.link ⟨val a, hvn⟩ from hDl_fin ⟨_, hvn⟩] at h0 h1
        have : (⟨val a, hvn⟩ : Fin n) = j := by
          by_contra hne
          exact hzo ⟨val a, hvn⟩ (hval_spec a hdec).1.1 (hval_spec a hdec).1.2.1 hne h0
        rw [this] at h1
        rw [hDl_fin]; exact h1
    have hap := hp_le a haT₀
    have haq := hq_ge a haT₀
    have hqN := hT₀N q hqT
    set k := max p (min (a - 1) (q - 2)) with hk
    refine ⟨k, by omega, fun c hc => ⟨?_, ?_⟩⟩
    · have : inT₀ (k + c) := hT₀conv p (k + c) q hpT hqT (by omega) (by omega)
      obtain ⟨w, hw1, hw2⟩ := this
      exact ⟨w, by rw [← hL_fin]; exact hw1, hw2⟩
    · have hkc : inT (k + c) := hT₀T _ (hT₀conv p (k + c) q hpT hqT (by omega) (by omega))
      apply Fin.ext
      simp only
      rw [hcl_id _ hkc, hR₀_dec (k + c) a hdec (by omega), hva]

/-- `exists_pattern` in the skeleton's form (a consequence of the strengthened statement). -/
theorem exists_pattern_skeleton {Q : Set Y} (hQ : IsCompact Q) (hQc : IsPreconnected Q)
    (hQn : Q.Nontrivial) (φ : Q → X) (hφ : Continuous φ) {n : ℕ} (D : Chain X n)
    {w₁ w₂ : ℕ} (hw : w₁ ≤ w₂) (hw₂ : w₂ < n)
    (hcov : ∀ z, φ z ∈ ⋃ (j : Fin n) (_ : w₁ ≤ j.val ∧ j.val ≤ w₂), D.link j)
    (hpriv : ∀ j : Fin n, w₁ ≤ j.val → j.val ≤ w₂ → ∃ z, φ z ∈ D.link j ∧
      ∀ j' : Fin n, w₁ ≤ j'.val → j'.val ≤ w₂ → j' ≠ j → φ z ∉ D.link j') :
    ∃ ε > 0, ∀ (N : ℕ) (F : Chain Y N), IsEpsChain F ε → Q ⊆ F.union →
      ∃ R : Fin N → Fin n, IsChainMap R ∧
        (∀ a : Fin N, (F.link a ∩ Q).Nonempty → w₁ ≤ (R a).val ∧ (R a).val ≤ w₂ ∧
          ∀ z : Q, (z : Y) ∈ closure (F.link a) → φ z ∈ D.link (R a)) ∧
        ∀ j : Fin n, w₁ ≤ j.val → j.val ≤ w₂ → ∃ a : ℕ, ∃ ha : a + 2 < N,
          ∀ (c : ℕ) (hc : c ≤ 2), (F.link ⟨a + c, by omega⟩ ∩ Q).Nonempty ∧
            R ⟨a + c, by omega⟩ = j := by
  obtain ⟨ε, hε, h⟩ := exists_pattern hQ hQc hQn φ hφ D hw hw₂ hcov hpriv
  refine ⟨ε, hε, fun N F hF hQF => ?_⟩
  obtain ⟨R, hR, h1, h2, h3⟩ := h N F hF hQF
  exact ⟨R, hR, fun a _ => ⟨(h1 a).1, (h1 a).2, h2 a⟩, h3⟩

end Pattern

end HPC.BJ59
