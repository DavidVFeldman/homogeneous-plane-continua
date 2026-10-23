import HPC.Fold.Questions78

/-!
# Bing 1948, Theorem 10: every subcontinuum of `M` is indecomposable

Batch 79, target 2. `theorem10` proves `Q78.Theorem10Statement Δ` for every description `Δ`.

Bing's proof (pp. 737–738), in the form used here. Suppose a subcontinuum `K ⊆ M` is `A ∪ B`
with `A`, `B` proper subcontinua. Pick `p ∈ K ∖ A` and `q ∈ K ∖ B`; as `A`, `B` are closed there
is `δ > 0` with `ball p δ` missing `A` and `ball q δ` missing `B`. Take a level `j` of mesh
`< δ / 3` and let `p ∈ d(j)_h`, `q ∈ d(j)_k`. Then `|h - k| > 2` (else `dist p q < δ`, but
`q ∈ A`); say `h < k`. The link `d(j)_{h+1}` lies within `2 ε_j < δ` of `p`, so misses `A`, and
`d(j)_{k-1}` misses `B`. Crookedness of `D_{j+1}` in `D_j` between a link of `D_{j+1}` holding
`p` and one holding `q` gives `r`, `s`, in this order between them, with
`d(j+1)_r ⊆ d(j)_{k-1}` and `d(j+1)_s ⊆ d(j)_{h+1}`.

The chain facts used (`Chain.inter_link_nonempty_between`): a preconnected set inside the union
of a chain that meets two links meets every link between them — the union of the links before a
link and the union after it are disjoint open sets. So `K` meets `d(j+1)_r`, which misses `B`,
so `A` meets `d(j+1)_r`; `A` also meets the link holding `q`; `s` lies between them, so `A`
meets `d(j+1)_s ⊆ d(j)_{h+1}`: a contradiction.

Only closedness of `A` and `B` and connectedness of `K` and `A` (resp. `B`) are used; no
compactness of `X` is needed.
-/

namespace HPC

open Set Metric

variable {X : Type*} [MetricSpace X]

namespace Chain

/-- **Separation by a link.** A preconnected set inside the union of a chain that meets the links
`a` and `c` meets every link strictly between them. -/
theorem inter_link_nonempty_between {m : ℕ} (E : Chain X m) {C : Set X} (hC : IsPreconnected C)
    (hCE : C ⊆ E.union) {a b c : Fin m} (hab : a < b) (hbc : b < c)
    (ha : (C ∩ E.link a).Nonempty) (hc : (C ∩ E.link c).Nonempty) :
    (C ∩ E.link b).Nonempty := by
  by_contra hb
  rw [not_nonempty_iff_eq_empty] at hb
  set U : Set X := ⋃ t : Fin m, ⋃ (_ : t < b), E.link t with hU
  set V : Set X := ⋃ t : Fin m, ⋃ (_ : b < t), E.link t with hV
  have hUo : IsOpen U := isOpen_iUnion fun t => isOpen_iUnion fun _ => E.isOpen t
  have hVo : IsOpen V := isOpen_iUnion fun t => isOpen_iUnion fun _ => E.isOpen t
  have hcov : C ⊆ U ∪ V := by
    intro z hz
    have hz' := hCE hz
    simp only [union, mem_iUnion] at hz'
    obtain ⟨t, ht⟩ := hz'
    rcases lt_trichotomy t b with h | h | h
    · exact Or.inl (mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨h, ht⟩⟩)
    · subst h
      have : z ∈ C ∩ E.link t := ⟨hz, ht⟩
      rw [hb] at this; exact this.elim
    · exact Or.inr (mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨h, ht⟩⟩)
  have hCU : (C ∩ U).Nonempty := by
    obtain ⟨z, hzC, hz⟩ := ha
    exact ⟨z, hzC, mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨hab, hz⟩⟩⟩
  have hCV : (C ∩ V).Nonempty := by
    obtain ⟨z, hzC, hz⟩ := hc
    exact ⟨z, hzC, mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨hbc, hz⟩⟩⟩
  obtain ⟨z, -, hzU, hzV⟩ := hC U V hUo hVo hcov hCU hCV
  simp only [hU, hV, mem_iUnion] at hzU hzV
  obtain ⟨t1, h1, hz1⟩ := hzU
  obtain ⟨t2, h2, hz2⟩ := hzV
  have := (E.adjacent_iff t1 t2).mp ⟨z, hz1, hz2⟩
  rw [Fin.lt_def] at h1 h2
  omega

/-- **Distance along a chain.** If every link has diameter at most `ε`, points of the links `a`
and `a + d` are at distance at most `(d + 1) ε`. -/
theorem dist_le_of_mem_link {n : ℕ} (D : Chain X n) {ε : ℝ}
    (hbdd : ∀ t, Bornology.IsBounded (D.link t)) (hdiam : ∀ t, Metric.diam (D.link t) ≤ ε) :
    ∀ (d : ℕ) (a b : Fin n), b.val = a.val + d → ∀ z ∈ D.link a, ∀ w ∈ D.link b,
      dist z w ≤ (d + 1) * ε := by
  intro d
  induction d with
  | zero =>
    intro a b hab z hz w hw
    have : b = a := Fin.ext (by omega)
    subst this
    have := dist_le_diam_of_mem (hbdd b) hz hw
    have := hdiam b
    push_cast; linarith
  | succ d ih =>
    intro a b hab z hz w hw
    set b' : Fin n := ⟨a.val + d, by omega⟩
    obtain ⟨y, hy1, hy2⟩ := (D.adjacent_iff b' b).mpr (by simp only [b']; omega)
    have h1 := ih a b' rfl z hz y hy1
    have h2 := dist_le_diam_of_mem (hbdd b) hy2 hw
    have h3 := hdiam b
    have := dist_triangle z y w
    push_cast; linarith

end Chain

namespace Description

/-- **The core of Theorem 10**, for one ordering of the two points. `K` is preconnected and
covered by the fine chain `E`, crooked in `D`; `K ⊆ A ∪ B` with `A ⊆ K` preconnected; `p ∈ K`
lies in `D.link h`, `q ∈ A` in `D.link k`, `h + 2 < k`; `D.link (h+1)` misses `A` and
`D.link (k-1)` misses `B`. This is impossible. -/
theorem theorem10_core {m N : ℕ} {E : Chain X m} {D : Chain X N} (hcr : E.IsCrookedIn' D)
    {K A B : Set X} (hKE : K ⊆ E.union) (hK : IsPreconnected K) (hA : IsPreconnected A)
    (hAK : A ⊆ K) (hKAB : K ⊆ A ∪ B) {p q : X} (hp : p ∈ K) (hq : q ∈ A) (h k : Fin N)
    (hhk : h.val + 2 < k.val) (hph : p ∈ D.link h) (hqk : q ∈ D.link k)
    (hnA : ∀ z ∈ D.link ⟨h.val + 1, by omega⟩, z ∉ A)
    (hnB : ∀ z ∈ D.link ⟨k.val - 1, by omega⟩, z ∉ B) : False := by
  have hpE := hKE hp
  have hqE := hKE (hAK hq)
  simp only [Chain.union, mem_iUnion] at hpE hqE
  obtain ⟨i, hi⟩ := hpE
  obtain ⟨j, hj⟩ := hqE
  obtain ⟨r, s, hbet, hr, hs⟩ := hcr.2 h k hhk i j ⟨p, hi, hph⟩ ⟨q, hj, hqk⟩
  have hAE : A ⊆ E.union := hAK.trans hKE
  -- `K` meets `E.link r`, which misses `B`; so `A` meets `E.link r`
  have hKr : (K ∩ E.link r).Nonempty := by
    rcases hbet with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact E.inter_link_nonempty_between hK hKE h1 (h2.trans h3) ⟨p, hp, hi⟩
        ⟨q, hAK hq, hj⟩
    · have := E.inter_link_nonempty_between hK hKE (h3.trans h2) h1 ⟨q, hAK hq, hj⟩
        ⟨p, hp, hi⟩
      exact this
  have hAr : (A ∩ E.link r).Nonempty := by
    obtain ⟨z, hzK, hzr⟩ := hKr
    refine ⟨z, ?_, hzr⟩
    rcases hKAB hzK with hzA | hzB
    · exact hzA
    · exact absurd hzB (hnB z (hr hzr))
  -- `A` meets `E.link r` and `E.link j`, hence `E.link s`, which misses `A`
  have hAs : (A ∩ E.link s).Nonempty := by
    rcases hbet with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact E.inter_link_nonempty_between hA hAE h2 h3 hAr ⟨q, hq, hj⟩
    · exact E.inter_link_nonempty_between hA hAE h3 h2 ⟨q, hq, hj⟩ hAr
  obtain ⟨z, hzA, hzs⟩ := hAs
  exact hnA z (hs hzs) hzA

/-- **Bing 1948, Theorem 10.** Every subcontinuum of the described continuum `M` is
indecomposable. -/
theorem theorem10 {P Q : X} (Δ : Description X P Q) : Fold.Q78.Theorem10Statement Δ := by
  intro K hKM hK
  refine ⟨hK, fun A B hA hB hAK hBK hAB => ?_⟩
  by_contra hne
  push_neg at hne
  obtain ⟨hAne, hBne⟩ := hne
  -- points of `K` off `A` and off `B`
  obtain ⟨p, hpK, hpA⟩ : ∃ p ∈ K, p ∉ A := by
    by_contra h; push_neg at h; exact hAne (Subset.antisymm hAK h)
  obtain ⟨q, hqK, hqB⟩ : ∃ q ∈ K, q ∉ B := by
    by_contra h; push_neg at h; exact hBne (Subset.antisymm hBK h)
  have hqA : q ∈ A := by
    have : q ∈ A ∪ B := hAB ▸ hqK
    exact this.resolve_right hqB
  have hpB : p ∈ B := by
    have : p ∈ A ∪ B := hAB ▸ hpK
    exact this.resolve_left hpA
  -- balls around `p` and `q` missing `A` and `B`
  obtain ⟨δ1, hδ1, hb1⟩ := Metric.isOpen_iff.mp hA.1.isClosed.isOpen_compl p hpA
  obtain ⟨δ2, hδ2, hb2⟩ := Metric.isOpen_iff.mp hB.1.isClosed.isOpen_compl q hqB
  set δ := min δ1 δ2 with hδ
  have hδpos : 0 < δ := lt_min hδ1 hδ2
  -- a level of small mesh
  obtain ⟨j, hj⟩ : ∃ j, Δ.ε j < δ / 3 :=
    (Filter.Tendsto.eventually_lt_const (by positivity) Δ.ε_tendsto).exists
  have hKE : K ⊆ (Δ.D (j + 1)).union := hKM.trans (Δ.M_subset_union (j + 1))
  have hpD := Δ.M_subset_union j (hKM hpK)
  have hqD := Δ.M_subset_union j (hKM hqK)
  simp only [Chain.union, mem_iUnion] at hpD hqD
  obtain ⟨h, hph⟩ := hpD
  obtain ⟨k, hqk⟩ := hqD
  have hdist := (Δ.D j).dist_le_of_mem_link (Δ.bdd j) (Δ.diam_le j)
  have hεpos := Δ.ε_pos j
  have hpq : δ ≤ dist p q := by
    by_contra hlt
    push_neg at hlt
    have : q ∈ ball p δ1 := by
      rw [mem_ball, dist_comm]; exact lt_of_lt_of_le hlt (min_le_left _ _)
    exact hb1 this hqA
  -- points of links next to `p`'s link are close to `p`
  have hnear : ∀ (a b : Fin (Δ.n j)) (x y : X), x ∈ (Δ.D j).link a → y ∈ (Δ.D j).link b →
      a.val ≤ b.val + 2 → b.val ≤ a.val + 2 → dist x y < δ := by
    intro a b x y hx hy h1 h2
    rcases le_total a.val b.val with hab | hab
    · have := hdist (b.val - a.val) a b (by omega) x hx y hy
      have hc : ((b.val - a.val : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : b.val - a.val ≤ 2)
      nlinarith
    · have := hdist (a.val - b.val) b a (by omega) y hy x hx
      have hc : ((a.val - b.val : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : a.val - b.val ≤ 2)
      rw [dist_comm]; nlinarith
  have hfar : h.val + 2 < k.val ∨ k.val + 2 < h.val := by
    by_contra hc
    push_neg at hc
    have := hnear h k p q hph hqk (by omega) (by omega)
    linarith
  have hcr := Δ.crooked j
  rcases hfar with hhk | hkh
  · refine theorem10_core hcr hKE hK.2.isPreconnected hA.2.isPreconnected hAK hAB.symm.subset
      hpK hqA h k hhk hph hqk ?_ ?_
    · intro z hz hzA
      have := hnear h ⟨h.val + 1, by omega⟩ p z hph hz (by simp only; omega) (by simp only; omega)
      exact hb1 (by rw [mem_ball, dist_comm]; exact lt_of_lt_of_le this (min_le_left _ _)) hzA
    · intro z hz hzB
      have := hnear k ⟨k.val - 1, by omega⟩ q z hqk hz (by simp only; omega) (by simp only; omega)
      exact hb2 (by rw [mem_ball, dist_comm]; exact lt_of_lt_of_le this (min_le_right _ _)) hzB
  · have hKBA : K ⊆ B ∪ A := by rw [← hAB, union_comm]
    refine theorem10_core hcr hKE hK.2.isPreconnected hB.2.isPreconnected hBK hKBA
      hqK hpB k h hkh hqk hph ?_ ?_
    · intro z hz hzB
      have := hnear k ⟨k.val + 1, by omega⟩ q z hqk hz (by simp only; omega) (by simp only; omega)
      exact hb2 (by rw [mem_ball, dist_comm]; exact lt_of_lt_of_le this (min_le_right _ _)) hzB
    · intro z hz hzA
      have := hnear h ⟨h.val - 1, by omega⟩ p z hph hz (by simp only; omega) (by simp only; omega)
      exact hb1 (by rw [mem_ball, dist_comm]; exact lt_of_lt_of_le this (min_le_left _ _)) hzA

end Description

end HPC
