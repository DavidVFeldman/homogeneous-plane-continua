import HPC.Moore.Borsuk

/-!
# Batch 146: Mullikin 1922, Theorem 5, corrected

A. M. Mullikin, *Certain theorems relating to plane connected point sets*, Trans. AMS 24 (1922),
Theorem 5, p. 160 (`doc/sources/mullikin1922.pdf`). As printed, with `K₁`, `K₂` merely mutually
exclusive connected sets, it is false (`not_mullikin_theorem5_printed`, `M25BRefute.lean`). With
`K₁`, `K₂` closed it holds (`mullikin_theorem5`), by logarithms rather than Mullikin's polygons:

* **at least two domains** (`not_isConnected_compl_union`): the function `1` on `M₁`,
  `exp (2πiφ)` on `M₂` has no logarithm on `M₁ ∪ M₂`; Borsuk's theorem (`borsuk_exists_log`,
  `Borsuk.lean`) gives one if the complement is connected;
* **at most two** (`compl_union_two_components`, Eilenberg's bound): of three components, two are
  bounded, say those of `p` and `q`; logarithms of `(z − p)/(z − y)` and `(z − q)/(z − y)` on `M₁` and
  on `M₂` jump by integers across `K₁` and `K₂`; a suitable product of integer powers of the two
  functions then has a logarithm on `M₁ ∪ M₂`, against `no_log_pow_of_bounded_component`.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane Complex

theorem closure_component_subset {M : Set Pt} (hM : IsClosed M) (x : Pt) :
    closure (connectedComponentIn Mᶜ x) ⊆ connectedComponentIn Mᶜ x ∪ M := by
  intro z hz
  rw [closure_eq_self_union_frontier] at hz
  rcases hz with h | h
  · exact Or.inl h
  · right
    simpa using frontier_connectedComponentIn_subset hM.isOpen_compl x h

theorem exists_log_quot {N : Set Pt} (hN : IsCompact N) (hNc : IsConnected Nᶜ) {x y : Pt}
    (hx : x ∉ N) (hy : y ∉ N) :
    ∃ g : Pt → ℂ, ContinuousOn g N ∧
      ∀ z ∈ N, Complex.exp (g z) = (toCpx z - toCpx x) / (toCpx z - toCpx y) :=
  exists_log_of_mem_component hN.isClosed hx
    (hNc.isPreconnected.subset_connectedComponentIn hx subset_rfl hy)

/-- Jumps across one piece of `M₁ ∩ M₂`. -/
theorem exists_jump {M₁ M₂ K : Set Pt} (hKM : K ⊆ M₁ ∩ M₂) (hKc : IsConnected K) {g₁ g₂ : Pt → ℂ}
    (hg₁ : ContinuousOn g₁ M₁) (hg₂ : ContinuousOn g₂ M₂) {h : Pt → ℂ}
    (he₁ : ∀ z ∈ M₁, Complex.exp (g₁ z) = h z) (he₂ : ∀ z ∈ M₂, Complex.exp (g₂ z) = h z) :
    ∃ n : ℤ, ∀ z ∈ K, g₁ z = g₂ z + n * (2 * Real.pi * Complex.I) := by
  obtain ⟨k, hk⟩ := hKc.nonempty
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1
    ((he₁ k (hKM hk).1).trans (he₂ k (hKM hk).2).symm)
  refine ⟨n, fun z hz => ?_⟩
  have := sub_const_of_exp_eq hKc.isPreconnected (hg₁.mono fun w hw => (hKM hw).1)
    (hg₂.mono fun w hw => (hKM hw).2)
    (fun w hw => (he₁ w (hKM hw).1).trans (he₂ w (hKM hw).2).symm) hz hk
  linear_combination this + hn

/-- **Bounded component ⇒ no logarithm, with powers.** If the component `U` of `x` in `Kᶜ` is
bounded, `a ≠ 0`, and `u` is continuous and nonvanishing on `Ū`, then `(z − x)^a · u z` has no
continuous logarithm on `K`. (The proof of `no_log_of_bounded_component`, with `(z − x)^a`.) -/
theorem no_log_pow_of_bounded_component {K : Set Pt} (hK : IsCompact K) {x : Pt} (hx : x ∉ K)
    (hb : Bornology.IsBounded (connectedComponentIn Kᶜ x)) {a : ℤ} (ha : a ≠ 0) {u : Pt → ℂ}
    (hu : ContinuousOn u (closure (connectedComponentIn Kᶜ x)))
    (hu0 : ∀ z ∈ closure (connectedComponentIn Kᶜ x), u z ≠ 0) :
    ¬ ∃ g : Pt → ℂ, ContinuousOn g K ∧
      ∀ z ∈ K, Complex.exp (g z) = (toCpx z - toCpx x) ^ a * u z := by
  rintro ⟨g, hgc, hge⟩
  classical
  set U := connectedComponentIn Kᶜ x with hU
  have hxU : x ∈ U := mem_connectedComponentIn hx
  have hUo : IsOpen U := hK.isClosed.isOpen_compl.connectedComponentIn
  have hfrU : frontier U ⊆ K := fun a ha => by
    simpa using frontier_connectedComponentIn_subset hK.isClosed.isOpen_compl x ha
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hK.isClosed ⟨K.restrict g, hgc.restrict⟩
  have hGg : ∀ z ∈ K, G z = g z := fun z hz => by
    have := congrArg (fun F : C(K, ℂ) => F ⟨z, hz⟩) hG
    simpa using this
  have hbase : ∀ z, z ∉ U → toCpx z - toCpx x ≠ 0 := fun z hz =>
    toCpx_sub_ne_zero (fun h => hz (h ▸ hxU))
  set Ψ : Pt → ℂ := fun z => if z ∈ U then Complex.exp (G z) / u z
    else (toCpx z - toCpx x) ^ a with hΨ
  have hΨc : Continuous Ψ := by
    refine continuous_if (fun z hz => ?_) ?_ ?_
    · have hzK := hfrU hz
      rw [hGg z hzK, hge z hzK]
      field_simp [hu0 z (frontier_subset_closure hz)]
    · exact (Complex.continuous_exp.comp G.continuous).continuousOn.div hu hu0
    · refine ContinuousOn.zpow₀ (continuous_toCpx.sub continuous_const).continuousOn a
        (fun z hz => Or.inl (hbase z ?_))
      have : closure {z | z ∉ U} = Uᶜ := hUo.isClosed_compl.closure_eq
      rw [this] at hz
      exact hz
  have hΨne : ∀ z, Ψ z ≠ 0 := by
    intro z
    by_cases hz : z ∈ U
    · simp only [hΨ, hz, if_true]
      exact div_ne_zero (Complex.exp_ne_zero _) (hu0 z (subset_closure hz))
    · simp only [hΨ, hz, if_false]
      exact zpow_ne_zero _ (hbase z hz)
  obtain ⟨L, hLc, hLe⟩ := exists_log_pt hΨc hΨne
  obtain ⟨R0, hR0⟩ := hb.subset_closedBall x
  set R : ℝ := 2 * |R0| + 2 with hR
  have hRpos : 0 < R := by positivity
  set c : ℝ → Pt := fun t => x + (R * Real.cos t, R * Real.sin t) with hc
  have hcc : Continuous c := by fun_prop
  have hcU : ∀ t, c t ∉ U := by
    intro t ht
    have h1 := hR0 ht
    rw [mem_closedBall] at h1
    have h2 := half_le_dist_circle x hRpos.le t
    have : R0 ≤ |R0| := le_abs_self R0
    linarith
  have hΨc' : ∀ t : ℝ, Ψ (c t) = Complex.exp (a * (Real.log R + t * Complex.I)) := by
    intro t
    simp only [hΨ, hcU t, if_false]
    rw [Complex.exp_int_mul, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hRpos,
      Complex.exp_mul_I]
    congr 1
    apply Complex.ext <;> simp [toCpx, hc, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hkey := sub_const_of_exp_eq (S := Icc 0 (2 * Real.pi)) isPreconnected_Icc
    (f := fun t : ℝ => L (c t)) (g := fun t : ℝ => (a : ℂ) * ((Real.log R : ℂ) + t * Complex.I))
    (hLc.comp hcc).continuousOn (by fun_prop) (fun t _ => by simp only [hLe, hΨc'])
    (x := 0) (y := 2 * Real.pi) ⟨le_rfl, by positivity⟩ ⟨by positivity, le_rfl⟩
  have hc0 : c (2 * Real.pi) = c 0 := by simp [hc]
  simp only [hc0] at hkey
  have : (a : ℂ) * (2 * Real.pi * Complex.I) = 0 := by
    push_cast at hkey; linear_combination hkey
  simp [Real.pi_ne_zero, ha] at this

theorem not_two_bounded_components {M₁ M₂ K₁ K₂ : Set Pt} (hM₁ : IsCompact M₁)
    (hM₂ : IsCompact M₂) (hs₁ : IsConnected M₁ᶜ) (hs₂ : IsConnected M₂ᶜ)
    (hK : M₁ ∩ M₂ = K₁ ∪ K₂) (hK₁c : IsConnected K₁) (hK₂c : IsConnected K₂)
    {p q y : Pt} (hp : p ∉ M₁ ∪ M₂) (hq : q ∉ M₁ ∪ M₂) (hy : y ∉ M₁ ∪ M₂)
    (hpb : Bornology.IsBounded (connectedComponentIn (M₁ ∪ M₂)ᶜ p))
    (hqb : Bornology.IsBounded (connectedComponentIn (M₁ ∪ M₂)ᶜ q))
    (hqp : q ∉ connectedComponentIn (M₁ ∪ M₂)ᶜ p) (hyp : y ∉ connectedComponentIn (M₁ ∪ M₂)ᶜ p)
    (hpq : p ∉ connectedComponentIn (M₁ ∪ M₂)ᶜ q) (hyq : y ∉ connectedComponentIn (M₁ ∪ M₂)ᶜ q) :
    False := by
  set M := M₁ ∪ M₂ with hMdef
  have hM : IsCompact M := hM₁.union hM₂
  have hK₁M : K₁ ⊆ M₁ ∩ M₂ := hK ▸ subset_union_left
  have hK₂M : K₂ ⊆ M₁ ∩ M₂ := hK ▸ subset_union_right
  set hf : Pt → Pt → ℂ := fun x z => (toCpx z - toCpx x) / (toCpx z - toCpx y) with hhf
  have nm₁ : ∀ {x}, x ∉ M → x ∉ M₁ := fun h h' => h (Or.inl h')
  have nm₂ : ∀ {x}, x ∉ M → x ∉ M₂ := fun h h' => h (Or.inr h')
  obtain ⟨g₁p, hg₁pc, hg₁pe⟩ := exists_log_quot hM₁ hs₁ (nm₁ hp) (nm₁ hy)
  obtain ⟨g₂p, hg₂pc, hg₂pe⟩ := exists_log_quot hM₂ hs₂ (nm₂ hp) (nm₂ hy)
  obtain ⟨g₁q, hg₁qc, hg₁qe⟩ := exists_log_quot hM₁ hs₁ (nm₁ hq) (nm₁ hy)
  obtain ⟨g₂q, hg₂qc, hg₂qe⟩ := exists_log_quot hM₂ hs₂ (nm₂ hq) (nm₂ hy)
  obtain ⟨n1p, hn1p⟩ := exists_jump hK₁M hK₁c hg₁pc hg₂pc hg₁pe hg₂pe
  obtain ⟨n2p, hn2p⟩ := exists_jump hK₂M hK₂c hg₁pc hg₂pc hg₁pe hg₂pe
  obtain ⟨n1q, hn1q⟩ := exists_jump hK₁M hK₁c hg₁qc hg₂qc hg₁qe hg₂qe
  obtain ⟨n2q, hn2q⟩ := exists_jump hK₂M hK₂c hg₁qc hg₂qc hg₁qe hg₂qe
  obtain ⟨a, b, hab0, habrel⟩ : ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧
      a * (n1p - n2p) + b * (n1q - n2q) = 0 := by
    by_cases h : n1p - n2p = 0 ∧ n1q - n2q = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by rw [h.1, h.2]; ring⟩
    · refine ⟨n1q - n2q, -(n1p - n2p), ?_, by ring⟩
      by_contra hc
      push_neg at hc
      exact h ⟨neg_eq_zero.1 hc.2, hc.1⟩
  set C : ℂ := ((a * n1p + b * n1q : ℤ) : ℂ) * (2 * Real.pi * Complex.I) with hC
  classical
  set G : Pt → ℂ := fun z => if z ∈ M₁ then a * g₁p z + b * g₁q z
    else a * g₂p z + b * g₂q z + C with hG
  have hGc : ContinuousOn G M := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ hM₁.isClosed hM₂.isClosed
    · refine (((continuousOn_const (c := (a : ℂ))).mul hg₁pc).add
        ((continuousOn_const (c := (b : ℂ))).mul hg₁qc)).congr
        (fun z hz => ?_)
      simp [G, hz]
    · refine ((((continuousOn_const (c := (a : ℂ))).mul hg₂pc).add
        ((continuousOn_const (c := (b : ℂ))).mul hg₂qc)).add
        (continuousOn_const (c := C))).congr (fun z hz => ?_)
      show G z = (a : ℂ) * g₂p z + (b : ℂ) * g₂q z + C
      by_cases h : z ∈ M₁
      · simp only [G, h, if_true]
        have hz' : z ∈ K₁ ∪ K₂ := hK ▸ ⟨h, hz⟩
        rcases hz' with h1 | h2
        · rw [hn1p z h1, hn1q z h1, hC]; push_cast; ring
        · rw [hn2p z h2, hn2q z h2, hC]
          have habC : ((a * n2p + b * n2q : ℤ) : ℂ) = ((a * n1p + b * n1q : ℤ) : ℂ) := by
            congr 1; linear_combination (-1 : ℤ) * habrel
          push_cast at habC ⊢
          linear_combination (2 * Real.pi * Complex.I) * habC
      · simp [G, h]
  have hGe : ∀ z ∈ M, Complex.exp (G z) = hf p z ^ a * hf q z ^ b := by
    intro z hz
    by_cases h : z ∈ M₁
    · simp only [G, h, if_true, Complex.exp_add, Complex.exp_int_mul, hg₁pe z h, hg₁qe z h, hf]
    · have hz2 : z ∈ M₂ := hz.resolve_left h
      simp only [G, h, if_false, Complex.exp_add, Complex.exp_int_mul, hg₂pe z hz2, hg₂qe z hz2,
        hC, Complex.exp_two_pi_mul_I, one_zpow, mul_one, hf]
  have hcl : ∀ {x w : Pt}, w ∉ connectedComponentIn Mᶜ x → w ∉ M →
      ∀ z ∈ closure (connectedComponentIn Mᶜ x), toCpx z - toCpx w ≠ 0 := by
    intro x w hw hwM z hz
    refine toCpx_sub_ne_zero fun e => ?_
    rcases closure_component_subset hM.isClosed x hz with h | h
    · exact hw (e ▸ h)
    · exact hwM (e ▸ h)
  rcases hab0 with ha | hb
  · refine no_log_pow_of_bounded_component hM hp hpb ha
      (u := fun z => (toCpx z - toCpx y) ^ (-a) * hf q z ^ b) ?_ ?_ ⟨G, hGc, fun z hz => ?_⟩
    · refine ContinuousOn.mul ?_ ?_
      · exact (continuous_toCpx.sub continuous_const).continuousOn.zpow₀ _
          (fun z hz => Or.inl (hcl hyp hy z hz))
      · refine ContinuousOn.zpow₀ ?_ _ (fun z hz => Or.inl (div_ne_zero (hcl hqp hq z hz)
          (hcl hyp hy z hz)))
        exact ((continuous_toCpx.sub continuous_const).continuousOn).div
          (continuous_toCpx.sub continuous_const).continuousOn (fun z hz => hcl hyp hy z hz)
    · intro z hz
      exact mul_ne_zero (zpow_ne_zero _ (hcl hyp hy z hz))
        (zpow_ne_zero _ (div_ne_zero (hcl hqp hq z hz) (hcl hyp hy z hz)))
    · rw [hGe z hz]
      simp only [hf, div_zpow, zpow_neg]
      ring
  · refine no_log_pow_of_bounded_component hM hq hqb hb
      (u := fun z => (toCpx z - toCpx y) ^ (-b) * hf p z ^ a) ?_ ?_ ⟨G, hGc, fun z hz => ?_⟩
    · refine ContinuousOn.mul ?_ ?_
      · exact (continuous_toCpx.sub continuous_const).continuousOn.zpow₀ _
          (fun z hz => Or.inl (hcl hyq hy z hz))
      · refine ContinuousOn.zpow₀ ?_ _ (fun z hz => Or.inl (div_ne_zero (hcl hpq hp z hz)
          (hcl hyq hy z hz)))
        exact ((continuous_toCpx.sub continuous_const).continuousOn).div
          (continuous_toCpx.sub continuous_const).continuousOn (fun z hz => hcl hyq hy z hz)
    · intro z hz
      exact mul_ne_zero (zpow_ne_zero _ (hcl hyq hy z hz))
        (zpow_ne_zero _ (div_ne_zero (hcl hpq hp z hz) (hcl hyq hy z hz)))
    · rw [hGe z hz]
      simp only [hf, div_zpow, zpow_neg]
      ring

/-- **Separation** (the Janiszewski direction, via Borsuk's theorem). If `M₁ ∩ M₂` is the union of
two disjoint nonempty closed sets, `M₁ ∪ M₂` separates the plane: on `M₁ ∪ M₂` the function equal
to `1` on `M₁` and to `exp (2πiφ)` on `M₂` (`φ` an Urysohn function, `0` on `K₁`, `1` on `K₂`) has no
continuous logarithm, while `borsuk_exists_log` gives one if the complement is connected. -/
theorem not_isConnected_compl_union {M₁ M₂ K₁ K₂ : Set Pt} (hM₁ : IsCompact M₁)
    (hM₁c : IsConnected M₁) (hM₂ : IsCompact M₂) (hM₂c : IsConnected M₂) (hK : M₁ ∩ M₂ = K₁ ∪ K₂)
    (hK₁ : IsClosed K₁) (hK₁n : K₁.Nonempty) (hK₂ : IsClosed K₂) (hK₂n : K₂.Nonempty)
    (hd : Disjoint K₁ K₂) :
    ¬ IsConnected (M₁ ∪ M₂)ᶜ := by
  intro hc
  obtain ⟨φ, hφ0, hφ1, -⟩ := exists_continuous_zero_one_of_isClosed hK₁ hK₂ hd
  classical
  set e : Pt → ℂ := fun z => Complex.exp (2 * Real.pi * Complex.I * (φ z : ℂ)) with he
  have hec : Continuous e :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp φ.continuous))
  have heK : ∀ z ∈ M₁ ∩ M₂, e z = 1 := by
    intro z hz
    rw [hK] at hz
    rcases hz with h | h
    · have : φ z = 0 := hφ0 h
      simp [e, this]
    · have : φ z = 1 := hφ1 h
      simp [e, this]
  set f : Pt → ℂ := fun z => if z ∈ M₁ then 1 else e z with hf
  have hfc : ContinuousOn f (M₁ ∪ M₂) := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ hM₁.isClosed hM₂.isClosed
    · exact (continuousOn_const (c := (1 : ℂ))).congr (fun z hz => by simp [f, hz])
    · refine hec.continuousOn.congr (fun z hz => ?_)
      by_cases h : z ∈ M₁
      · simp [f, h, heK z ⟨h, hz⟩]
      · simp [f, h]
  have hf0 : ∀ z ∈ M₁ ∪ M₂, f z ≠ 0 := fun z _ => by
    by_cases h : z ∈ M₁
    · simp [f, h]
    · simp [f, h, e, Complex.exp_ne_zero]
  obtain ⟨g, hgc, hge⟩ := borsuk_exists_log (hM₁.union hM₂) hc hfc hf0
  obtain ⟨k₁, hk₁⟩ := hK₁n
  obtain ⟨k₂, hk₂⟩ := hK₂n
  have hk₁M : k₁ ∈ M₁ ∩ M₂ := hK ▸ Or.inl hk₁
  have hk₂M : k₂ ∈ M₁ ∩ M₂ := hK ▸ Or.inr hk₂
  have h1 := sub_const_of_exp_eq hM₁c.isPreconnected (hgc.mono subset_union_left)
    (continuousOn_const (c := (0 : ℂ)))
    (fun z hz => by rw [hge z (Or.inl hz)]; simp [f, hz]) hk₁M.1 hk₂M.1
  have h2 := sub_const_of_exp_eq hM₂c.isPreconnected (hgc.mono subset_union_right)
    (g := fun z => 2 * Real.pi * Complex.I * (φ z : ℂ))
    (continuous_const.mul (Complex.continuous_ofReal.comp φ.continuous)).continuousOn
    (fun z hz => by
      rw [hge z (Or.inr hz)]
      by_cases h : z ∈ M₁
      · simp only [f, h, if_true]; exact (heK z ⟨h, hz⟩).symm
      · simp [f, h, e]) hk₁M.2 hk₂M.2
  have e1 : φ k₁ = 0 := hφ0 hk₁
  have e2 : φ k₂ = 1 := hφ1 hk₂
  simp only [e1, e2] at h2
  have : 2 * (Real.pi : ℂ) * Complex.I = 0 := by
    push_cast at h1 h2; linear_combination h2 - h1
  simp [Real.pi_ne_zero] at this

theorem mem_connectedComponentIn_symm {F : Set Pt} {x y : Pt} (hx : x ∈ F)
    (h : y ∈ connectedComponentIn F x) : x ∈ connectedComponentIn F y := by
  rw [← connectedComponentIn_eq h]; exact mem_connectedComponentIn hx

/-- **At most two components** (Eilenberg's bound for two pieces). -/
theorem compl_union_two_components {M₁ M₂ K₁ K₂ : Set Pt} (hM₁ : IsCompact M₁)
    (hM₂ : IsCompact M₂) (hs₁ : IsConnected M₁ᶜ) (hs₂ : IsConnected M₂ᶜ)
    (hK : M₁ ∩ M₂ = K₁ ∪ K₂) (hK₁c : IsConnected K₁) (hK₂c : IsConnected K₂)
    {x₀ x₁ z : Pt} (h₀ : x₀ ∉ M₁ ∪ M₂) (h₁ : x₁ ∉ M₁ ∪ M₂) (hz : z ∉ M₁ ∪ M₂)
    (h₁₀ : x₁ ∉ connectedComponentIn (M₁ ∪ M₂)ᶜ x₀) :
    z ∈ connectedComponentIn (M₁ ∪ M₂)ᶜ x₀ ∨ z ∈ connectedComponentIn (M₁ ∪ M₂)ᶜ x₁ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hz₀, hz₁⟩ := hcon
  have hM := hM₁.union hM₂
  have symm : ∀ {x y : Pt}, y ∉ connectedComponentIn (M₁ ∪ M₂)ᶜ x →
      x ∉ connectedComponentIn (M₁ ∪ M₂)ᶜ y := fun {x y} h h' => h (by
    have hy : y ∈ (M₁ ∪ M₂)ᶜ := connectedComponentIn_nonempty_iff.1 ⟨x, h'⟩
    rw [← connectedComponentIn_eq h']; exact mem_connectedComponentIn hy)
  by_cases b₀ : Bornology.IsBounded (connectedComponentIn (M₁ ∪ M₂)ᶜ x₀)
  · by_cases b₁ : Bornology.IsBounded (connectedComponentIn (M₁ ∪ M₂)ᶜ x₁)
    · exact not_two_bounded_components hM₁ hM₂ hs₁ hs₂ hK hK₁c hK₂c h₀ h₁ hz b₀ b₁ h₁₀ hz₀ (symm h₁₀) hz₁
    · by_cases bz : Bornology.IsBounded (connectedComponentIn (M₁ ∪ M₂)ᶜ z)
      · exact not_two_bounded_components hM₁ hM₂ hs₁ hs₂ hK hK₁c hK₂c h₀ hz h₁ b₀ bz hz₀ h₁₀ (symm hz₀) (symm hz₁)
      · exact hz₁ (mem_component_of_unbounded hM h₁ hz b₁ bz)
  · by_cases b₁ : Bornology.IsBounded (connectedComponentIn (M₁ ∪ M₂)ᶜ x₁)
    · by_cases bz : Bornology.IsBounded (connectedComponentIn (M₁ ∪ M₂)ᶜ z)
      · exact not_two_bounded_components hM₁ hM₂ hs₁ hs₂ hK hK₁c hK₂c h₁ hz h₀ b₁ bz hz₁ (symm h₁₀) (symm hz₁) (symm hz₀)
      · exact hz₀ (mem_component_of_unbounded hM h₀ hz b₀ bz)
    · exact h₁₀ (mem_component_of_unbounded hM h₀ h₁ b₀ b₁)

/-- **Mullikin 1922, Theorem 5, corrected** (`K₁`, `K₂` closed). This is the form Moore uses in
Theorem 11, with `K₁ = p̄`, `K₂ = q̄`. Proof: `not_isConnected_compl_union` (at least two
components) and `compl_union_two_components` (at most two). -/
theorem mullikin_theorem5 {M₁ M₂ K₁ K₂ : Set Pt} (hM₁ : IsCompact M₁) (hM₁c : IsConnected M₁)
    (hM₂ : IsCompact M₂) (hM₂c : IsConnected M₂) (hs₁ : ¬ SeparatesPlane M₁)
    (hs₂ : ¬ SeparatesPlane M₂) (hK : M₁ ∩ M₂ = K₁ ∪ K₂) (hK₁ : IsClosed K₁) (hK₁c : IsConnected K₁)
    (hK₂ : IsClosed K₂) (hK₂c : IsConnected K₂) (hd : Disjoint K₁ K₂) :
    ∃ U V : Set Pt, IsOpen U ∧ IsConnected U ∧ IsOpen V ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = (M₁ ∪ M₂)ᶜ := by
  rw [SeparatesPlane, not_not] at hs₁ hs₂
  have hM := hM₁.union hM₂
  have hnc := not_isConnected_compl_union hM₁ hM₁c hM₂ hM₂c hK hK₁ hK₁c.nonempty hK₂ hK₂c.nonempty hd
  have hO : IsOpen (M₁ ∪ M₂)ᶜ := hM.isClosed.isOpen_compl
  obtain ⟨x₀, h₀⟩ : ((M₁ ∪ M₂)ᶜ).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h
    exact NormedSpace.unbounded_univ ℝ Pt (h ▸ hM.isBounded)
  set U := connectedComponentIn (M₁ ∪ M₂)ᶜ x₀
  obtain ⟨x₁, h₁, h₁₀⟩ : ∃ x₁ ∈ (M₁ ∪ M₂)ᶜ, x₁ ∉ U := by
    by_contra h
    push_neg at h
    apply hnc
    have : U = (M₁ ∪ M₂)ᶜ := (connectedComponentIn_subset _ _).antisymm h
    rw [← this]
    exact isConnected_connectedComponentIn_iff.2 h₀
  set V := connectedComponentIn (M₁ ∪ M₂)ᶜ x₁
  refine ⟨U, V, hO.connectedComponentIn, isConnected_connectedComponentIn_iff.2 h₀,
    hO.connectedComponentIn, isConnected_connectedComponentIn_iff.2 h₁, ?_, ?_⟩
  · rw [disjoint_left]
    intro w hwU hwV
    apply h₁₀
    have e : U = V := (connectedComponentIn_eq hwU).trans (connectedComponentIn_eq hwV).symm
    rw [e]
    exact mem_connectedComponentIn h₁
  · refine (union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)).antisymm
      fun z hz => ?_
    exact compl_union_two_components hM₁ hM₂ hs₁ hs₂ hK hK₁c hK₂c h₀ h₁ hz h₁₀

end HPC.Moore
