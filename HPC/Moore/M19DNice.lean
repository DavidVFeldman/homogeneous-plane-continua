import HPC.Moore.M19DLens

/-!
# Moore 1919, Theorem D: a nice closed curve about a compact set

**Theorem** (`exists_nice_curve`). If `F` is a compact subset of the interior `V` of a closed curve,
there is a closed curve `h`, with interior `W ⊇ F`, lying with `W` in `V`, meeting `ABCDA` in
finitely many points, none of them `A, B, C, D`, and crossing `ABCDA` at each of them.

`F` is enlarged to a connected compact set `K ⊆ V` (`exists_conn_compact`). The points of `K` on
`J` are covered by finitely many lenses whose ends are all distinct (`lens_family`), the rest of
`K` by finitely many closed curves missing `J` (Theorem 36). Theorem 42 merges these curves into one
curve `h ⊆ ⋃ curves` whose interior contains theirs; near each of its points on `J`, `h` lies on a
single lens, so it crosses `J` there.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-- **A finite family of lenses with distinct ends.** -/
theorem lens_family {J I V : Set S} (Os : Finset S) (φ : S → unitInterval → S)
    (a b : S → unitInterval) (hφ : ∀ O ∈ Os, Function.Injective (φ O))
    (ha : ∀ O ∈ Os, 0 < a O) (hb : ∀ O ∈ Os, b O < 1) (hO : ∀ O ∈ Os, O ∈ φ O '' Ioo (a O) (b O))
    (hlens : ∀ O ∈ Os, ∀ x y : unitInterval, 0 < x → x < y → y < 1 →
      ∃ k Wk, σ.IsInteriorOf k Wk ∧ k ∪ Wk ⊆ V ∧ k ∩ J = {φ O x, φ O y} ∧
        φ O '' Ioo x y ⊆ Wk ∧ σ.Crosses I k (φ O x) ∧ σ.Crosses I k (φ O y)) :
    ∀ Φ : Set S, Φ.Finite → ∃ G : Finset (Set S × Set S),
      (∀ p ∈ G, σ.IsInteriorOf p.1 p.2 ∧ p.1 ∪ p.2 ⊆ V ∧ (p.1 ∩ J).Finite ∧
        Disjoint (p.1 ∩ J) Φ ∧ (∀ z ∈ p.1 ∩ J, σ.Crosses I p.1 z) ∧ ∃ O ∈ Os, O ∈ p.2) ∧
      (∀ p ∈ G, ∀ p' ∈ G, p ≠ p' → Disjoint (p.1 ∩ J) (p'.1 ∩ J)) ∧
      ∀ O ∈ Os, φ O '' Ioo (a O) (b O) ⊆ ⋃ p ∈ G, p.2 := by
  classical
  induction Os using Finset.induction_on with
  | empty =>
    intro Φ _
    exact ⟨∅, by simp, by simp, by simp⟩
  | insert O Os hOs ih =>
    intro Φ hΦ
    have mem : O ∈ insert O Os := Finset.mem_insert_self _ _
    have sub : ∀ {P : S → Prop}, (∀ O' ∈ insert O Os, P O') → ∀ O' ∈ Os, P O' :=
      fun h O' hO' => h O' (Finset.mem_insert_of_mem hO')
    obtain ⟨s, hs, -⟩ := hO O mem
    have hab : a O < b O := hs.1.trans hs.2
    have avoid : ∀ {l r : unitInterval}, l < r → ∀ Ψ : Set S, Ψ.Finite →
        ∃ x ∈ Ioo l r, φ O x ∉ Ψ := by
      intro l r hlr Ψ hΨ
      have hne := ((Set.Ioo_infinite hlr).diff (hΨ.preimage (hφ O mem).injOn)).nonempty
      obtain ⟨x, hx, hxΨ⟩ := hne
      exact ⟨x, hx, hxΨ⟩
    obtain ⟨x, hx, hxΦ⟩ := avoid (ha O mem) Φ hΦ
    obtain ⟨y, hy, hyΦ⟩ := avoid (hb O mem) Φ hΦ
    obtain ⟨k, Wk, hk, hkV, hkJ, hkW, hcx, hcy⟩ :=
      hlens O mem x y hx.1 (hx.2.trans (hab.trans hy.1)) hy.2
    obtain ⟨G, hG, hGd, hGc⟩ := ih (sub hφ) (sub ha) (sub hb) (sub hO) (sub hlens)
      (Φ ∪ {φ O x, φ O y}) (hΦ.union (toFinite _))
    have hOW : φ O '' Ioo (a O) (b O) ⊆ Wk :=
      (image_mono fun t (ht : t ∈ Ioo (a O) (b O)) => (⟨hx.2.trans ht.1, ht.2.trans hy.1⟩ : t ∈ Ioo x y)).trans hkW
    have hnew : Disjoint (k ∩ J) Φ := by
      rw [hkJ, disjoint_left]
      rintro z (rfl | rfl)
      exacts [hxΦ, hyΦ]
    have hold : ∀ p ∈ G, Disjoint (p.1 ∩ J) (k ∩ J) := fun p hp => by
      rw [hkJ]; exact (hG p hp).2.2.2.1.mono_right subset_union_right
    refine ⟨insert (k, Wk) G, ?_, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · refine ⟨hk, hkV, by rw [hkJ]; exact toFinite _, hnew, ?_, O, mem, ?_⟩
        · intro z hz
          rw [hkJ] at hz
          rcases hz with rfl | rfl
          exacts [hcx, hcy]
        · exact hOW (hO O mem)
      · obtain ⟨h₁, h₂, h₃, h₄, h₅, O', hO', hO'p⟩ := hG p hp
        exact ⟨h₁, h₂, h₃, h₄.mono_right subset_union_left, h₅, O',
          Finset.mem_insert_of_mem hO', hO'p⟩
    · intro p hp p' hp' hne
      rcases Finset.mem_insert.mp hp with rfl | hp <;>
        rcases Finset.mem_insert.mp hp' with rfl | hp'
      · exact absurd rfl hne
      · exact (hold p' hp').symm
      · exact hold p hp
      · exact hGd p hp p' hp' hne
    · intro O' hO'
      rcases Finset.mem_insert.mp hO' with rfl | hO'
      · exact hOW.trans fun z hz => mem_iUnion₂.mpr ⟨(k, Wk), Finset.mem_insert_self _ _, hz⟩
      · exact (hGc O' hO').trans (iUnion₂_subset fun p hp z hz =>
          mem_iUnion₂.mpr ⟨p, Finset.mem_insert_of_mem hp, hz⟩)

/-- **A connected compact set between `F` and `V`.** -/
theorem exists_conn_compact (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) {V F : Set S} (hVo : @IsOpen S σ.topology V)
    (hVc : @IsPreconnected S σ.topology V) {z₀ : S} (hz₀ : z₀ ∈ V)
    (hF : @IsCompact S σ.topology F) (hFV : F ⊆ V) :
    ∃ K, @IsCompact S σ.topology K ∧ @IsPreconnected S σ.topology K ∧ z₀ ∈ K ∧ F ⊆ K ∧ K ⊆ V := by
  classical
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have harc := arcConn h1 h3 h4 h51 h2
  have hreg : ∀ z ∈ F, ∃ R ∈ σ.region, z ∈ R ∧ closure R ⊆ V :=
    fun z hz => exists_region_closure_subset h1 hVo (hFV hz)
  choose! R hR hzR hRV using hreg
  have hpath : ∀ z ∈ V, ∃ C ⊆ V, IsCompact C ∧ IsPreconnected C ∧ z₀ ∈ C ∧ z ∈ C := by
    intro z hz
    by_cases e : z₀ = z
    · subst e
      exact ⟨{z₀}, singleton_subset_iff.mpr hz, isCompact_singleton, isPreconnected_singleton,
        rfl, rfl⟩
    · obtain ⟨C, hCV, hC⟩ := harc V hVo hVc z₀ hz₀ z hz e
      exact ⟨C, hCV, hC.isCompact, hC.isPreconnected, hC.left_mem, hC.right_mem⟩
  choose! Cp hCpV hCpc hCpp hCp₀ hCpz using hpath
  obtain ⟨t, htF, hcov⟩ := hF.elim_nhds_subcover R fun z hz => (isOpen_region (hR z hz)).mem_nhds (hzR z hz)
  set c : Set (Set S) := insert {z₀} ((fun z => closure (R z) ∪ Cp z) '' (t : Set S))
  refine ⟨⋃₀ c, ?_, ?_, ⟨{z₀}, mem_insert _ _, rfl⟩, ?_, ?_⟩
  · refine (Finite.insert _ ((t.finite_toSet).image _)).isCompact_sUnion ?_
    rintro s (rfl | ⟨z, hz, rfl⟩)
    · exact isCompact_singleton
    · exact (isCompact_closure_region h1 h4 (hR z (htF z hz))).union
        (hCpc z (hFV (htF z hz)))
  · refine isPreconnected_sUnion z₀ c ?_ ?_
    · rintro s (rfl | ⟨z, hz, rfl⟩)
      · rfl
      · exact Or.inr (hCp₀ z (hFV (htF z hz)))
    · rintro s (rfl | ⟨z, hz, rfl⟩)
      · exact isPreconnected_singleton
      · have hzt := htF z hz
        exact (hpc_region h1 h2 _ (hR z hzt)).closure.union z (subset_closure (hzR z hzt))
          (hCpz z (hFV hzt)) (hCpp z (hFV hzt))
  · intro w hw
    obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.mp (hcov hw)
    exact ⟨_, mem_insert_of_mem _ ⟨z, hz, rfl⟩, Or.inl (subset_closure hwz)⟩
  · rintro w ⟨s, (rfl | ⟨z, hz, rfl⟩), hws⟩
    · rw [mem_singleton_iff.mp hws]; exact hz₀
    · rcases hws with h | h
      · exact hRV z (htF z hz) h
      · exact hCpV z (hFV (htF z hz)) h


section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S}

/-- **Merging curves.** Finitely many closed curves within `V`, each meeting `J` in finitely many
points (none of them `A, B, C, D`) and crossing `J` at each of them, no two with a common point on
`J`, whose interiors cover a connected set `K` and meet it, merge (Theorem 42) into one such curve
whose interior contains `K`. -/
theorem merge_nice {V K : Set S} (hVr : V ∈ σ.region) (hKc : @IsPreconnected S σ.topology K)
    (hKne : K.Nonempty) (G : Finset (Set S × Set S))
    (hG : ∀ p ∈ G, σ.IsInteriorOf p.1 p.2 ∧ p.1 ∪ p.2 ⊆ V ∧ (p.1 ∩ J).Finite ∧
      Disjoint p.1 {A, B, C, D} ∧ (∀ z ∈ p.1 ∩ J, σ.Crosses I p.1 z) ∧ (p.2 ∩ K).Nonempty)
    (hGd : ∀ p ∈ G, ∀ p' ∈ G, p ≠ p' → Disjoint (p.1 ∩ J) (p'.1 ∩ J))
    (hcov : K ⊆ ⋃ p ∈ G, p.2) :
    ∃ h W, σ.IsInteriorOf h W ∧ K ⊆ W ∧ h ∪ W ⊆ V ∧ (h ∩ J).Finite ∧
      Disjoint h {A, B, C, D} ∧ ∀ p ∈ h ∩ J, σ.Crosses I h p := by
  classical
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨z, hz⟩ := hKne
  obtain ⟨p₀, hp₀, -⟩ := mem_iUnion₂.mp (hcov hz)
  have hconn : σ.IsConn (⋃ p ∈ G, p.2) := by
    rw [isConn_iff h1]
    have heq : (⋃ p ∈ G, p.2) = ⋃₀ ((fun p : Set S × Set S => p.2 ∪ K) '' (G : Set _)) := by
      apply subset_antisymm
      · exact iUnion₂_subset fun p hp w hw => ⟨_, ⟨p, hp, rfl⟩, Or.inl hw⟩
      · rintro w ⟨_, ⟨p, hp, rfl⟩, hw | hw⟩
        · exact mem_iUnion₂.mpr ⟨p, hp, hw⟩
        · exact hcov hw
    rw [heq]
    refine isPreconnected_sUnion z _ ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩; exact Or.inr hz
    · rintro _ ⟨p, hp, rfl⟩
      have hpc := (jordan h1 h2 h3 h4 h51 h7 (hG p hp).1).2.1
      exact hpc.union' (hG p hp).2.2.2.2.2 hKc
  obtain ⟨h, W, hW, hhG, hWG⟩ := fa_theorem42 h1 h2 h3 h4 h5 h6 h7 h8 G (fun p hp => (hG p hp).1)
    ⟨p₀, hp₀⟩ hconn
  obtain ⟨hWo, -, -, hfrW, -, -, -, -, -, -, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hW
  have hhV : h ⊆ V := hhG.trans (iUnion₂_subset fun p hp => subset_union_left.trans (hG p hp).2.1)
  have hWV : W ⊆ V := fa_theorem21 h1 h3 h4 h5 h7 hVr hW.2.1
    (by rw [hW.2.2, cl_eq_closure h1]; exact hhV.trans subset_closure)
  have hhW : Disjoint h W := by rw [← hfrW]; exact (disjoint_frontier hWo).symm
  refine ⟨h, W, hW, hcov.trans (iUnion₂_subset fun p hp => hWG p hp), union_subset hhV hWV, ?_,
    ?_, ?_⟩
  · refine ((G.finite_toSet).biUnion fun p hp => (hG p hp).2.2.1).subset ?_
    rintro w ⟨hwh, hwJ⟩
    obtain ⟨p, hp, hwp⟩ := mem_iUnion₂.mp (hhG hwh)
    exact mem_iUnion₂.mpr ⟨p, hp, hwp, hwJ⟩
  · rw [disjoint_left]
    intro w hwh hwc
    obtain ⟨p, hp, hwp⟩ := mem_iUnion₂.mp (hhG hwh)
    exact disjoint_left.mp (hG p hp).2.2.2.1 hwp hwc
  · rintro w ⟨hwh, hwJ⟩
    obtain ⟨p, hp, hwp⟩ := mem_iUnion₂.mp (hhG hwh)
    -- the other curves stay away from `w`
    set Z := ⋃ p' ∈ G.erase p, closure p'.2
    have hZc : IsClosed Z := (G.erase p).finite_toSet.isClosed_biUnion fun _ _ => isClosed_closure
    have hwZ : w ∉ Z := by
      intro hwZ
      obtain ⟨p', hp', hw'⟩ := mem_iUnion₂.mp hwZ
      have hne : p' ≠ p := Finset.ne_of_mem_erase hp'
      have hp'G : p' ∈ G := Finset.mem_of_mem_erase hp'
      obtain ⟨-, -, -, -, -, -, -, -, hcl', -⟩ := jordan h1 h2 h3 h4 h51 h7 (hG p' hp'G).1
      rw [hcl'] at hw'
      rcases hw' with hw' | hw'
      · exact disjoint_left.mp hhW hwh (hWG p' hp'G hw')
      · exact disjoint_left.mp (hGd p hp p' hp'G hne.symm) ⟨hwp, hwJ⟩ ⟨hw', hwJ⟩
    obtain ⟨N, hN, u, v, t, t', ht, ht', htI, ht'E, hsub⟩ := (hG p hp).2.2.2.2.1 w ⟨hwp, hwJ⟩
    refine ⟨N ∩ Zᶜ, Filter.inter_mem hN (hZc.isOpen_compl.mem_nhds hwZ), u, v, t, t', ht, ht',
      htI, ht'E, ?_⟩
    rintro y ⟨hyh, hyN, hyZ⟩
    obtain ⟨p', hp', hyp'⟩ := mem_iUnion₂.mp (hhG hyh)
    by_cases e : p' = p
    · subst e; exact hsub ⟨hyp', hyN⟩
    · exfalso
      obtain ⟨-, -, -, hfr', -⟩ := jordan h1 h2 h3 h4 h51 h7 (hG p' hp').1
      exact hyZ (mem_iUnion₂.mpr ⟨p', Finset.mem_erase.mpr ⟨e, hp'⟩,
        frontier_subset_closure (hfr'.symm ▸ hyp')⟩)

end Ax


section Final

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **A nice closed curve about a compact set.** -/
theorem exists_nice_curve (q : σ.Quad J I A B C D sAB sBC sCD sDA) {g V : Set S}
    (hV : σ.IsInteriorOf g V) {F : Set S} (hF : @IsCompact S σ.topology F) (hFV : F ⊆ V) :
    ∃ h W, σ.IsInteriorOf h W ∧ F ⊆ W ∧ h ∪ W ⊆ V ∧ (h ∩ J).Finite ∧ Disjoint h {A, B, C, D} ∧
      ∀ p ∈ h ∩ J, σ.Crosses I h p := by
  classical
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨hVo, hVc, ⟨z₀, hz₀⟩, -⟩ := jordan h1 h2 h3 h4 h51 h7 hV
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hJcpt, -⟩ := jordan h1 h2 h3 h4 h51 h7 q.interior
  have hJcl : IsClosed J := hJcpt.isClosed
  have hcorJ : ∀ w ∈ ({A, B, C, D} : Set S), w ∈ J := by
    intro w hw
    rw [← q.union]
    simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inl q.ab.left_mem))
    · exact Or.inl (Or.inl (Or.inl q.ab.right_mem))
    · exact Or.inl (Or.inr q.cd.left_mem)
    · exact Or.inl (Or.inr q.cd.right_mem)
  obtain ⟨K, hKc, hKp, hz₀K, hFK, hKV⟩ := exists_conn_compact h1 h2 h3 h4 h5 hVo hVc hz₀ hF hFV
  haveI : Nonempty S := ⟨z₀⟩
  -- lenses about the points of `K` on `J`
  have hL := fun O (hO : O ∈ J ∩ V) =>
    lens_data h1 h2 h3 h4 h5 h6 h7 h8 q.interior hVo hO.1 hO.2
  choose! U hUo hOU φ hφ hφJ a b ha hab hb hUJ hlens using hL
  obtain ⟨t, htKJ, hcovJ⟩ := (hKc.inter_right hJcl).elim_nhds_subcover U
    (fun O hO => (hUo O ⟨hO.2, hKV hO.1⟩).mem_nhds (hOU O ⟨hO.2, hKV hO.1⟩))
  have htJV : ∀ O ∈ t, O ∈ J ∩ V := fun O hO => ⟨(htKJ O hO).2, hKV (htKJ O hO).1⟩
  obtain ⟨G₁, hG₁, hG₁d, hG₁c⟩ := lens_family (J := J) (I := I) (V := V) t φ a b
    (fun O hO => (hφ O (htJV O hO)).injective) (fun O hO => ha O (htJV O hO))
    (fun O hO => hb O (htJV O hO))
    (fun O hO => hUJ O (htJV O hO) ⟨hOU O (htJV O hO), (htJV O hO).1⟩)
    (fun O hO => hlens O (htJV O hO)) {A, B, C, D} (toFinite _)
  have hKJcov : K ∩ J ⊆ ⋃ p ∈ G₁, p.2 := by
    intro z hz
    obtain ⟨O, hO, hzU⟩ := mem_iUnion₂.mp (hcovJ hz)
    exact hG₁c O hO (hUJ O (htJV O hO) ⟨hzU, hz.2⟩)
  -- closed curves missing `J` about the other points of `K`
  set K' := K \ ⋃ p ∈ G₁, p.2
  have hK'c : IsCompact K' := hKc.diff (isOpen_biUnion fun p hp =>
    (jordan h1 h2 h3 h4 h51 h7 (hG₁ p hp).1).1)
  have hK'J : ∀ z ∈ K', z ∈ V \ J := fun z hz =>
    ⟨hKV hz.1, fun hzJ => hz.2 (hKJcov ⟨hz.1, hzJ⟩)⟩
  have hD : ∀ z ∈ V \ J, ∃ D ID, σ.IsInteriorOf D ID ∧ z ∈ ID ∧ D ∪ ID ⊆ V \ J := by
    intro z hz
    obtain ⟨R, hR, hzR, hRsub⟩ := (isOpen_iff_region h1).mp (hVo.sdiff hJcl) z hz
    obtain ⟨D, hDR, ID, hID, hzID, hIDR⟩ :=
      fa_theorem36_interior_subset h1 h2 h3 h4 h5 h6 h7 h8 hR hzR
    exact ⟨D, ID, hID, hzID, union_subset (hDR.trans hRsub) (hIDR.trans hRsub)⟩
  choose! Dk IDk hIDk hzIDk hDsub using hD
  obtain ⟨t₂, ht₂, hcov₂⟩ := hK'c.elim_nhds_subcover IDk fun z hz =>
    (jordan h1 h2 h3 h4 h51 h7 (hIDk z (hK'J z hz))).1.mem_nhds (hzIDk z (hK'J z hz))
  set G₂ := t₂.image fun z => (Dk z, IDk z)
  have hG₂ : ∀ p ∈ G₂, ∃ z ∈ t₂, p = (Dk z, IDk z) := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨z, hz, rfl⟩
  have hG₂J : ∀ p ∈ G₂, p.1 ∩ J = ∅ := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := hG₂ p hp
    exact eq_empty_of_forall_notMem fun w hw =>
      (hDsub z (hK'J z (ht₂ z hz)) (Or.inl hw.1)).2 hw.2
  have hGa : ∀ p ∈ G₁ ∪ G₂, σ.IsInteriorOf p.1 p.2 ∧ p.1 ∪ p.2 ⊆ V ∧ (p.1 ∩ J).Finite ∧
      Disjoint p.1 {A, B, C, D} ∧ (∀ z ∈ p.1 ∩ J, σ.Crosses I p.1 z) ∧ (p.2 ∩ K).Nonempty := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨h₁, h₂, h₃, h₄, h₅, O, hO, hOp⟩ := hG₁ p hp
      refine ⟨h₁, h₂, h₃, disjoint_left.mpr fun w hw hwc => ?_, h₅, O, hOp, (htKJ O hO).1⟩
      exact disjoint_left.mp h₄ ⟨hw, hcorJ w hwc⟩ hwc
    · have hJ := hG₂J p hp
      obtain ⟨z, hz, rfl⟩ := hG₂ p hp
      have hzV := hK'J z (ht₂ z hz)
      refine ⟨hIDk z hzV, (hDsub z hzV).trans diff_subset, by rw [hJ]; exact finite_empty,
        disjoint_left.mpr fun w hw hwc => ?_, fun w hw => ?_, z, hzIDk z hzV, (ht₂ z hz).1⟩
      · exact (eq_empty_iff_forall_notMem.mp hJ) w ⟨hw, hcorJ w hwc⟩
      · exact absurd (hJ ▸ hw) (notMem_empty w)
  have hGb : ∀ p ∈ G₁ ∪ G₂, ∀ p' ∈ G₁ ∪ G₂, p ≠ p' → Disjoint (p.1 ∩ J) (p'.1 ∩ J) := by
    intro p hp p' hp' hne
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp' with hp' | hp'
      · exact hG₁d p hp p' hp' hne
      · rw [hG₂J p' hp']; exact disjoint_empty _
    · rw [hG₂J p hp]; exact empty_disjoint _
  have hGc : K ⊆ ⋃ p ∈ G₁ ∪ G₂, p.2 := by
    intro z hz
    by_cases hz1 : z ∈ ⋃ p ∈ G₁, p.2
    · obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp hz1
      exact mem_iUnion₂.mpr ⟨p, Finset.mem_union_left _ hp, hzp⟩
    · obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hcov₂ ⟨hz, hz1⟩)
      exact mem_iUnion₂.mpr ⟨(Dk w, IDk w), Finset.mem_union_right _
        (Finset.mem_image_of_mem _ hw), hzw⟩
  obtain ⟨h, W, hW, hKW, hrest⟩ := merge_nice h1 h2 h3 h4 h5 h6 h7 h8 (J := J) (I := I)
    (A := A) (B := B) (C := C) (D := D) hV.2.1 hKp ⟨z₀, hz₀K⟩ (G₁ ∪ G₂) hGa hGb hGc
  exact ⟨h, W, hW, hFK.trans hKW, hrest⟩

end Final


end HPC.Moore
