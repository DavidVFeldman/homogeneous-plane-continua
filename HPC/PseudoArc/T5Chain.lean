import HPC.PseudoArc.T5Assemble

/-!
# Theorem 5: the chain `E`

Batch 80. `lift_all` combines the lifts over the maximal runs of links of `F` in `D_2(u, v)` into
one function of the times; `assemble` builds the chain `E` of Theorem 5 from it.

*Batch 115:* `assemble` also states that every link of `F` in the stretch meeting `d(2)_u` lies in
the first link of `E` and every one meeting `d(2)_v` in the last (read off the construction: the
lift is `0`, resp. `N + 1`, there). Used by `theorem5_gen` (`T5Gen.lean`).
-/

namespace HPC.T5

open Set

variable {X : Type*} [MetricSpace X] {n0 n1 nR nF : ℕ}
  {D0 : Chain X n0} {D1 : Chain X n1} {R : Chain X nR} {F : Chain X nF}
  {h k : Fin n0} {u v : Fin n1} {W : ℕ} {σ0 : Fin nF → Fin nR} {τ1 : Fin nR → Fin n1}
  {ρ : Fin n1 → Fin n0}

theorem touch_of_subset {t : Fin nF} (h1 : F.link t ⊆ D1.link u ∨ F.link t ⊆ D1.link v) :
    Touch D1 F u v t := by
  obtain ⟨z, hz⟩ := F.link_nonempty t
  rcases h1 with h1 | h1
  · exact Or.inl ⟨z, hz, h1 hz⟩
  · exact Or.inr ⟨z, hz, h1 hz⟩

/-- The lifts over all runs, as one function of the times. -/
theorem lift_all (H : Setup D0 D1 R F h k u v W σ0 τ1 ρ) (hnF : 0 < nF)
    (hS : PatCore.Setting (sigN σ0 hnF) (nF - 1)) {N : ℕ} {x : Fin N → Fin n0}
    (hx : Pat x h k) (hW : 4 * (N + 2) + 10 ≤ W) {P Q : X} (hF : F.IsFrom P Q)
    (hD1 : D1.IsFrom P Q) (σ1 : Fin nF → Fin n1) (hσ1 : ∀ t, F.link t ⊆ D1.link (σ1 t)) :
    ∃ φ : ℕ → ℕ,
      (∀ f (hf : f < nF), InS D1 F u v ⟨f, hf⟩ → φ f ≤ N + 1 ∧
        ∃ p : Fin nR, ((p : ℤ) - σ0 ⟨f, hf⟩).natAbs ≤ W ∧
          rd D1 R h k u v W τ1 ρ p = xext x h k (φ f)) ∧
      (∀ f (hf : f + 1 < nF), InS D1 F u v ⟨f, by omega⟩ → InS D1 F u v ⟨f + 1, hf⟩ →
        (φ (f + 1) : ℤ) - φ f ≤ 1 ∧ (φ f : ℤ) - φ (f + 1) ≤ 1) := by
  classical
  let Sn : ℕ → Prop := fun g => ∃ hg : g < nF, InS D1 F u v ⟨g, hg⟩
  have hbd : ∃ B, ∀ g, B ≤ g → ¬ Sn g := ⟨nF, fun g hg ⟨hg', _⟩ => by omega⟩
  obtain ⟨hnF', hP, hQ, _, _⟩ := hF
  obtain ⟨hn1, _, _, hPu1, hQu1⟩ := hD1
  have htouch : ∀ a b, IsRun Sn a b →
      ∃ ha : a < nF, ∃ hb : b < nF, Touch D1 F u v ⟨a, ha⟩ ∧ Touch D1 F u v ⟨b, hb⟩ := by
    intro a b ⟨hab, hS', ha, hb⟩
    obtain ⟨ha', hSa⟩ := hS' a le_rfl hab
    obtain ⟨hb', hSb⟩ := hS' b hab le_rfl
    refine ⟨ha', hb', touch_of_subset ?_, touch_of_subset ?_⟩
    · rcases ha with ha0 | ha0
      · left
        subst ha0
        obtain ⟨s, hus, hsv, hts⟩ := hSa
        have hs0 := hPu1 s (hts hP)
        have hus' : (u : ℕ) ≤ s := hus
        have hs0' : (s : ℕ) = 0 := by rw [hs0]
        have hu0 : u = s := Fin.ext (by omega)
        rw [hu0]; exact hts
      · have hapos : 0 < a := by
          rcases Nat.eq_zero_or_pos a with h0 | h0
          · subst h0; exact absurd ⟨ha', hSa⟩ ha0
          · exact h0
        exact touch_of_boundary σ1 hσ1 (t := ⟨a, ha'⟩) (t' := ⟨a - 1, by omega⟩)
          (Or.inr (by simp only; omega)) hSa (fun h' => ha0 ⟨by omega, h'⟩)
    · by_cases hbT : b + 1 < nF
      · exact touch_of_boundary σ1 hσ1 (t := ⟨b, hb'⟩) (t' := ⟨b + 1, hbT⟩)
          (Or.inl rfl) hSb (fun h' => hb ⟨hbT, h'⟩)
      · right
        have hbe : (⟨b, hb'⟩ : Fin nF) = ⟨nF - 1, by omega⟩ := Fin.ext (by simp only; omega)
        obtain ⟨s, hus, hsv, hts⟩ := hSb
        rw [hbe] at hts
        have hs1 := hQu1 s (hts hQ)
        have hsv' : (s : ℕ) ≤ v := hsv
        have hs1' : (s : ℕ) = n1 - 1 := by rw [hs1]
        have := v.isLt
        have hv0 : v = s := Fin.ext (by omega)
        rw [hbe, hv0]; exact hts
  have hΦ : ∀ a b, ∃ φ : ℕ → ℕ, IsRun Sn a b →
      (∀ f, a ≤ f → f < b → (φ (f + 1) : ℤ) - φ f ≤ 1 ∧ (φ f : ℤ) - φ (f + 1) ≤ 1) ∧
      ∀ f (hf : f < nF), a ≤ f → f ≤ b → φ f ≤ N + 1 ∧
        ∃ p : Fin nR, ((p : ℤ) - σ0 ⟨f, hf⟩).natAbs ≤ W ∧
          rd D1 R h k u v W τ1 ρ p = xext x h k (φ f) := by
    intro a b
    by_cases hr : IsRun Sn a b
    · obtain ⟨ha', hb', hta, htb⟩ := htouch a b hr
      obtain ⟨φ, h1, h2⟩ := run_lift_geom H hnF hS hx hW hr.1 hb'
        (fun g hg h1 h2 => by obtain ⟨_, hg'⟩ := hr.2.1 g h1 h2; exact hg') hta htb
      exact ⟨φ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' hr⟩
  choose Φ hΦ using hΦ
  have hrun : ∀ f, ∃ a b, Sn f → a ≤ f ∧ f ≤ b ∧ IsRun Sn a b := by
    intro f
    by_cases hf : Sn f
    · obtain ⟨a, b, h⟩ := exists_run hf hbd
      exact ⟨a, b, fun _ => h⟩
    · exact ⟨0, 0, fun h' => absurd h' hf⟩
  choose A B hAB using hrun
  refine ⟨fun f => Φ (A f) (B f) f, fun f hf hSf => ?_, fun f hf hS1 hS2 => ?_⟩
  · obtain ⟨h1, h2, hr⟩ := hAB f ⟨hf, hSf⟩
    exact ((hΦ _ _ hr).2 f hf h1 h2)
  · obtain ⟨h1, h2, hr⟩ := hAB f ⟨by omega, hS1⟩
    obtain ⟨h1', h2', hr'⟩ := hAB (f + 1) ⟨hf, hS2⟩
    have hfB : f + 1 ≤ B f := by
      by_contra hcon
      have : B f = f := by omega
      exact hr.2.2.2 (by rw [this]; exact ⟨hf, hS2⟩)
    obtain ⟨hA, hB⟩ := run_unique hr hr' ⟨by omega, hfB⟩ ⟨h1', h2'⟩
    simp only
    rw [← hA, ← hB]
    exact (hΦ _ _ hr).1 f h1 (by omega)

/-- **The chain `E` of Theorem 5**, at the level of the fine chain `F`. -/
theorem assemble (H : Setup D0 D1 R F h k u v W σ0 τ1 ρ) (hnF : 0 < nF)
    (hS : PatCore.Setting (sigN σ0 hnF) (nF - 1)) {N : ℕ} {x : Fin N → Fin n0}
    (hx : Pat x h k) (hW : 4 * (N + 2) + 10 ≤ W) {P Q : X} (hF : F.IsFrom P Q)
    (hD1 : D1.IsFrom P Q) (σ1 : Fin nF → Fin n1) (hσ1 : ∀ t, F.link t ⊆ D1.link (σ1 t))
    (huv : u < v) :
    ∃ E : Chain X N, E.FollowsPattern x D0 ∧ E.IsConsolidationOn F {t | InS D1 F u v t} ∧
      (∀ e : Fin N, 0 < e.val → e.val < N - 1 →
        Disjoint (E.link e) (D1.link u ∪ D1.link v)) ∧
      (∀ t, InS D1 F u v t → (F.link t ∩ D1.link u).Nonempty →
        F.link t ⊆ E.link ⟨0, hx.pos⟩) ∧
      (∀ t, InS D1 F u v t → (F.link t ∩ D1.link v).Nonempty →
        F.link t ⊆ E.link ⟨N - 1, by have := hx.pos; omega⟩) := by
  classical
  have hN := hx.pos
  obtain ⟨φ, hL1, hL2⟩ := lift_all H hnF hS hx hW hF hD1 σ1 hσ1
  obtain ⟨tu, tv, htuv, htv, hcrossS, htuU, htvV⟩ := exists_crossing hF hD1 σ1 hσ1 huv
  have hφtu : φ tu = 0 := by
    obtain ⟨hle, p, hp, hpv⟩ := hL1 tu (by omega) (hcrossS tu (by omega) le_rfl htuv)
    obtain ⟨z, hz⟩ := F.link_nonempty ⟨tu, by omega⟩
    rw [H.force_u ⟨z, hz, htuU hz⟩ hp] at hpv
    exact xext_eq_low hx hle hpv.symm
  have hφtv : φ tv = N + 1 := by
    obtain ⟨hle, p, hp, hpv⟩ := hL1 tv htv (hcrossS tv htv htuv le_rfl)
    obtain ⟨z, hz⟩ := F.link_nonempty ⟨tv, htv⟩
    rw [H.force_v ⟨z, hz, htvV hz⟩ hp] at hpv
    exact xext_eq_high hx hle hpv.symm
  have hcons : ∀ c, c ≤ N → ∃ g, tu ≤ g ∧ g < tv ∧ φ g = c ∧ φ (g + 1) = c + 1 := by
    intro c hc
    set G := Nat.findGreatest (fun g => φ g ≤ c) tv with hG
    have hGge : tu ≤ G := Nat.le_findGreatest htuv (show φ tu ≤ c by rw [hφtu]; omega)
    have hGspec : φ G ≤ c := Nat.findGreatest_spec (P := fun g => φ g ≤ c) htuv
      (show φ tu ≤ c by rw [hφtu]; omega)
    have hGle : G ≤ tv := Nat.findGreatest_le tv
    have hGlt : G < tv := by
      rcases Nat.eq_or_lt_of_le hGle with he | hlt
      · rw [he, hφtv] at hGspec; omega
      · exact hlt
    have hG1 : ¬ φ (G + 1) ≤ c := Nat.findGreatest_is_greatest (P := fun g => φ g ≤ c) (n := tv) (k := G + 1)
      (by omega) (by omega)
    have := hL2 G (by omega) (hcrossS G (by omega) hGge (by omega))
      (hcrossS (G + 1) (by omega) (by omega) (by omega))
    exact ⟨G, hGge, hGlt, by omega, by omega⟩
  let β : Fin nF → ℕ := fun t => min (φ t - 1) (N - 1)
  have hβlt : ∀ t, β t < N := fun t => by simp only [β]; omega
  let L : Fin N → Set X := fun e => ⋃ t ∈ {t : Fin nF | InS D1 F u v t ∧ β t = e}, F.link t
  have hmemL : ∀ (e : Fin N) (z : X), z ∈ L e ↔
      ∃ t : Fin nF, (InS D1 F u v t ∧ β t = e) ∧ z ∈ F.link t := by
    intro e z; simp only [L, mem_iUnion, mem_setOf_eq, exists_prop]
  have hblock : ∀ c, c ≤ N → 1 ≤ c → ∃ t : Fin nF, InS D1 F u v t ∧ φ t = c ∧
      ∃ t' : Fin nF, t'.val = t.val + 1 ∧ InS D1 F u v t' ∧ φ t' = c + 1 := by
    intro c hc _
    obtain ⟨g, h1, h2, h3, h4⟩ := hcons c hc
    exact ⟨⟨g, by omega⟩, hcrossS g (by omega) h1 (by omega), h3, ⟨g + 1, by omega⟩, rfl,
      hcrossS (g + 1) (by omega) (by omega) (by omega), h4⟩
  let E : Chain X N :=
    { link := L
      isOpen := fun e => isOpen_biUnion fun t _ => F.isOpen t
      adjacent := by
        intro e e'
        constructor
        · rintro ⟨z, hz1, hz2⟩
          obtain ⟨t, ⟨ht, hte⟩, hzt⟩ := (hmemL e z).mp hz1
          obtain ⟨t', ⟨ht', hte'⟩, hzt'⟩ := (hmemL e' z).mp hz2
          have hadj := (F.adjacent_iff t t').mp ⟨z, hzt, hzt'⟩
          rcases Nat.lt_trichotomy t.val t'.val with hlt | heq | hgt
          · have := hL2 t.val (by have := t'.isLt; omega) ht
              (by rw [show (⟨t.val + 1, _⟩ : Fin nF) = t' from Fin.ext (by simp only; omega)];
                  exact ht')
            have htt : (t' : ℕ) = t + 1 := by omega
            simp only [β] at hte hte'
            rw [htt] at hte'
            omega
          · have : t = t' := Fin.ext heq
            subst this
            omega
          · have := hL2 t'.val (by have := t.isLt; omega) ht'
              (by rw [show (⟨t'.val + 1, _⟩ : Fin nF) = t from Fin.ext (by simp only; omega)];
                  exact ht)
            have htt : (t : ℕ) = t' + 1 := by omega
            simp only [β] at hte hte'
            rw [htt] at hte
            omega
        · intro hee
          rcases Nat.lt_trichotomy e.val e'.val with hlt | heq | hgt
          · obtain ⟨t, ht, hφt, t', htt', ht', hφt'⟩ := hblock (e.val + 1) (by omega) (by omega)
            obtain ⟨z, hz1, hz2⟩ := (F.adjacent_iff t t').mpr (by omega)
            refine ⟨z, (hmemL e z).mpr ⟨t, ⟨ht, ?_⟩, hz1⟩, (hmemL e' z).mpr ⟨t', ⟨ht', ?_⟩, hz2⟩⟩
            · simp only [β]; omega
            · simp only [β]; omega
          · have : e = e' := Fin.ext heq
            subst this
            obtain ⟨t, ht, hφt, -⟩ := hblock (e.val + 1) (by omega) (by omega)
            obtain ⟨z, hz⟩ := F.link_nonempty t
            have hm := (hmemL e z).mpr ⟨t, ⟨ht, by simp only [β]; omega⟩, hz⟩
            exact ⟨z, hm, hm⟩
          · obtain ⟨t, ht, hφt, t', htt', ht', hφt'⟩ := hblock (e'.val + 1) (by omega) (by omega)
            obtain ⟨z, hz1, hz2⟩ := (F.adjacent_iff t t').mpr (by omega)
            refine ⟨z, (hmemL e z).mpr ⟨t', ⟨ht', ?_⟩, hz2⟩, (hmemL e' z).mpr ⟨t, ⟨ht, ?_⟩, hz1⟩⟩
            · simp only [β]; omega
            · simp only [β]; omega }
  refine ⟨E, ?_, ⟨fun t ht => ⟨⟨β t, hβlt t⟩, fun z hz => (hmemL _ z).mpr ⟨t, ⟨ht, rfl⟩, hz⟩⟩,
    fun e => ⟨{t | InS D1 F u v t ∧ β t = e}, fun t ht => ht.1, rfl⟩⟩, ?_, ?_, ?_⟩
  · intro e z hz
    obtain ⟨t, ⟨ht, hte⟩, hzt⟩ := (hmemL e z).mp hz
    obtain ⟨hle, p, hp, hpv⟩ := hL1 t.val t.isLt ht
    have hsnd := H.sound ht hp
    rw [hpv] at hsnd
    obtain ⟨s1, s2, s3⟩ := hsnd
    rcases Nat.eq_zero_or_pos (φ t) with h0 | h0
    · have he : e = ⟨0, hN⟩ := Fin.ext (by rw [← hte]; simp only [β, h0]; omega)
      rw [he, hx.first]
      exact s1 (by rw [h0, xext_zero]) hzt
    · rcases Nat.lt_or_ge N (φ t) with hNt | hNt
      · have hφ : φ t = N + 1 := by omega
        have he : e = ⟨N - 1, by omega⟩ := Fin.ext (by rw [← hte]; simp only [β, hφ]; omega)
        rw [he, hx.last]
        exact s2 (by rw [hφ, xext_top]) hzt
      · have hr := xext_mid_range hx h0 hNt
        have he : e = ⟨φ t - 1, by omega⟩ := Fin.ext (by rw [← hte]; simp only [β]; omega)
        rw [he]
        exact (s3 hr.1 hr.2 _ (by rw [xext_mid h0 hNt])).1 hzt
  · intro e he1 he2
    rw [Set.disjoint_left]
    intro z hz hzA
    obtain ⟨t, ⟨ht, hte⟩, hzt⟩ := (hmemL e z).mp hz
    obtain ⟨hle, p, hp, hpv⟩ := hL1 t.val t.isLt ht
    have hsnd := H.sound ht hp
    rw [hpv] at hsnd
    obtain ⟨-, -, s3⟩ := hsnd
    have hφ1 : 1 ≤ φ t := by
      by_contra hcon
      have : φ t = 0 := by omega
      simp only [β, this] at hte
      omega
    have hφ2 : φ t ≤ N := by simp only [β] at hte; omega
    have hr := xext_mid_range hx hφ1 hφ2
    exact Set.disjoint_left.mp (s3 hr.1 hr.2 _ (by rw [xext_mid hφ1 hφ2])).2 hzt hzA
  · intro t ht hmeet z hz
    obtain ⟨hle, p, hp, hpv⟩ := hL1 t.val t.isLt ht
    rw [H.force_u hmeet hp] at hpv
    have h0 := xext_eq_low hx hle hpv.symm
    exact (hmemL _ z).mpr ⟨t, ⟨ht, by show min (φ t - 1) (N - 1) = 0; rw [h0]; omega⟩, hz⟩
  · intro t ht hmeet z hz
    obtain ⟨hle, p, hp, hpv⟩ := hL1 t.val t.isLt ht
    rw [H.force_v hmeet hp] at hpv
    have h0 := xext_eq_high hx hle hpv.symm
    exact (hmemL _ z).mpr ⟨t, ⟨ht, by show min (φ t - 1) (N - 1) = N - 1; rw [h0]; omega⟩, hz⟩

end HPC.T5
