import HPC.Plane.Theorem11B

/-!
# Batch 106: Bing 1951 (Duke) Theorem 12 (B ⇒ A), Theorem 13 in full, and the unnumbered
# "two end points" claim of §5

Saved from the uploaded skeleton as `HPC/Plane/Thm12B.lean`; `import HPC.Plane.Thm12B` is added at
the end of `HPC.lean`. Every item is proved, with no `sorry`; no statement was changed.

Bing's proof of B ⇒ A cites "Theorem 5 of [4]" (his arcs paper, not available). The repository
has what replaces it: condition B at `p` says `{p}` is a terminal subcontinuum of `M'`
(`isTerminalSub_singleton_iff`), and Fugate's Lemma 3 (⇒) (`isTerminalSub_iff_irreducible`, for
atriodic hereditarily unicoherent `M'`) makes `M' = {p} ∪ M'` irreducible between a point of `{p}`
and another point. Snake-like continua are atriodic and hereditarily unicoherent (batch 96), and
subcontinua of snake-like continua are snake-like.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **Theorem 12, B ⇒ A** (Bing 1951, p. 661), for snake-like `M`. -/
theorem condA_of_condB {M : Set S} (hM : IsSnakeLike M) {p : S} (hp : CondB M p) : CondA M p := by
  refine ⟨hp.1, fun W hWM hW hnt hpW => ?_⟩
  have hWs : IsSnakeLike W := isSnakeLike_of_subcontinuum hM hW hWM
  have hBW : CondB W p := ⟨hpW, fun H K hHW hKW hH hK hpH hpK =>
    hp.2 H K (hHW.trans hWM) (hKW.trans hWM) hH hK hpH hpK⟩
  have hT : IsTerminalSub W {p} := (isTerminalSub_singleton_iff W p).mpr hBW
  obtain ⟨p', q, hp', hirr⟩ := (isTerminalSub_iff_irreducible (isAtriodic_of_isSnakeLike hWs)
    (isHereditarilyUnicoherent_of_isSnakeLike hWs) (isContinuum_singleton' p)
    (singleton_subset_iff.mpr hpW)).mp hT W hW subset_rfl ⟨p, hpW, rfl⟩
  rw [mem_singleton_iff.mp hp', singleton_union, insert_eq_of_mem hpW] at hirr
  refine ⟨q, fun hqp => ?_, hirr⟩
  subst hqp
  have h1 : ({q} : Set S) = W := hirr.2.2.2 {q} (isContinuum_singleton' q)
    (singleton_subset_iff.mpr hpW) rfl rfl
  exact (h1 ▸ hnt).ne_singleton rfl

/-- **Theorem 12** (both directions; A ⇒ B is batch 85's `condB_of_condA`). -/
theorem theorem12_1951 {M : Set S} (hM : IsSnakeLike M) (p : S) : CondA M p ↔ CondB M p :=
  ⟨condB_of_condA, condA_of_condB hM⟩

/-- **Theorem 13** (Bing 1951, p. 661): a point of a snake-like continuum is an end point iff it
satisfies condition A iff it satisfies condition B. Necessity is batch 85's `condB_of_endPoint`;
sufficiency for A is `endPoint_of_condA` (batch 99); B via Theorem 12. -/
theorem theorem13_1951 {M : Set S} (hM : IsSnakeLike M) (p : S) :
    IsEndPoint M p ↔ CondA M p :=
  ⟨fun h => condA_of_condB hM (condB_of_endPoint h), endPoint_of_condA hM⟩

theorem theorem13_1951' {M : Set S} (hM : IsSnakeLike M) (p : S) :
    IsEndPoint M p ↔ CondB M p :=
  (theorem13_1951 hM p).trans (theorem12_1951 hM p)

/-- **The unnumbered claim after Theorem 13** (p. 661): "We find from Theorems 8, 9, and 13 that
each hereditarily decomposable snake-like continuum contains two end points between which it is
irreducible." For the whole space: `S` snake-like and hereditarily decomposable (hence `BingS`),
there are end points `p ≠ q` with `S` irreducible between them. (Route: two end elements
(`exists_two_endElts`), a condition-A point in each (`theorem9_1951`), end points by Theorem 13,
irreducibility by Theorem 8 (c) (`bingElt_irreducible`).) -/
theorem exists_two_endPoints_irreducible [ConnectedSpace S] [Nontrivial S]
    (hsn : IsSnakeLike (univ : Set S)) (hd : IsHereditarilyDecomposable (univ : Set S)) :
    ∃ p q : S, p ≠ q ∧ IsEndPoint (univ : Set S) p ∧ IsEndPoint (univ : Set S) q ∧
      IsIrreducibleBetween (univ : Set S) p q := by
  have hS : BingS S := ⟨inferInstance, inferInstance, isAtriodic_of_isSnakeLike hsn,
    isHereditarilyUnicoherent_of_isSnakeLike hsn, hd⟩
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_endElts hS
  obtain ⟨p, hpa, hpA⟩ := theorem9_1951 hS ha
  obtain ⟨q, hqb, hqA⟩ := theorem9_1951 hS hb
  have ep := (mem_bingElt_iff hS).mp hpa
  have eq := (mem_bingElt_iff hS).mp hqb
  have hpq : p ≠ q := fun e => disjoint_left.mp (bingElt_disjoint hS hab) hpa (e ▸ hqb)
  refine ⟨p, q, hpq, endPoint_of_condA hsn hpA, endPoint_of_condA hsn hqA,
    hsn.1, mem_univ p, mem_univ q, fun K hK _ hpK hqK => ?_⟩
  exact bingElt_irreducible hS p q (ha.of_eq ep) (hb.of_eq eq) (by rw [ep, eq]; exact hab)
    K hK hpK hqK

/-- With Theorem 14 (batch 85, `theorem14_1951`): such `p`, `q` are opposite end points. -/
theorem exists_oppositeEndPoints_of_hd [ConnectedSpace S] [Nontrivial S]
    (hsn : IsSnakeLike (univ : Set S)) (hd : IsHereditarilyDecomposable (univ : Set S)) :
    ∃ p q : S, p ≠ q ∧ OppositeEndPoints (univ : Set S) p q := by
  obtain ⟨p, q, hpq, hp, hq, hirr⟩ := exists_two_endPoints_irreducible hsn hd
  exact ⟨p, q, hpq, theorem14_1951 hsn hp hq hirr⟩

end HPC.Plane
