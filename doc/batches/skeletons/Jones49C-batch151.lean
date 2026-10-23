import HPC.Jones.Jones49B

/-!
# Batch 151 skeleton: crossing continua; Moore 1922 Theorem 4 (local form and both directions);
complementary domains of plane continua; Whyburn 1939 (6.22) in the §14 form

Save as `HPC/Jones/Jones49C.lean` (splitting under `HPC/Jones/` is expected); add
`import HPC.Jones.Jones49C` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be
adjusted, each change recorded at the statement and in the report.

Sources (page images, 150–200 dpi): Moore 1922 pp. 235–237 (`doc/sources/moore1922.pdf`); Whyburn,
*Semi-locally-connected sets*, Amer. J. Math. 61 (1939), §14, pp. 747–749
(`doc/sources/whyburn1939.pdf`). Whyburn's §14 proof begins: "Let `R` be a complementary domain of
`M`. Clearly we may suppose `R` bounded, since an inversion of the plane can be used to throw `R`
into a bounded region complementary to the image of `M`. We shall show that `R` has property `S`
… If this is not so, there exists a sequence of points `p₁, p₂, …` of `R` converging to a point
`p ∈ M` and an `ε > 0` such that for no `i, j` can `pᵢ` and `pⱼ` be joined by a connected subset of
`R` of diameter `< 4ε`."
-/

namespace HPC.Jones

open Set Topology Metric Filter HPC.Plane

/-! ## Continua crossing an annulus -/

/-- **The sector theorem** (REPORT-batch150 §2; the step behind Moore 1922 p. 236 "must clearly
contain a point either of `kₙ₋₁` or of `kₙ₊₁`" and p. 237 "It can easily be seen that no two of the
sets `R̄₂, R̄₄, …` …"). Two disjoint continua crossing a closed annulus (each in the annulus, each
meeting both boundary circles) cut it into two pieces; a connected subset of the open annulus
joining points of different pieces meets one of the two continua. Together with it, the cyclic
order on the middle circle of infinitely many mutually exclusive crossing continua. *The shape is
left to you*; the annulus may be taken with squares (sup metric) as in `exists_crossing_continua`. -/
theorem sector_theorem : True := by
  sorry

/-! ## Moore 1922 Theorem 4 -/

/-- **Moore's sufficiency, local form** (REPORT-batch150 §5 (a)). A connected open plane set `R`,
bounded or not, with connected boundary, such that no boundary point `p` is the limit of a sequence
of points of `R` no two of which can be joined in `R` by a connected set of diameter `< ε` (Whyburn's
§14 condition), has a locally connected boundary. Moore's p. 236 argument, which uses neither
boundedness nor simple connectivity. -/
theorem moore22_sufficiency_local {R : Set Pt} (hR : IsOpen R) (hRc : IsConnected R)
    (hB : IsConnected (frontier R))
    (hloc : ∀ p ∈ frontier R, ∀ ε > 0, ¬ ∃ u : ℕ → Pt, (∀ n, u n ∈ R) ∧ Tendsto u atTop (𝓝 p) ∧
      ∀ i j, i ≠ j → ¬ ∃ C ⊆ R, IsPreconnected C ∧ u i ∈ C ∧ u j ∈ C ∧ Bornology.IsBounded C ∧
        diam C < ε) :
    LocallyConnectedSpace (frontier R) := by
  sorry

/-- **Moore 1922, Theorem 4** — left open in batch 150, restated verbatim. When proved, delete the
commented copy at the end of `HPC/Jones/Moore22T4.lean` and update `OPEN.md`. -/
theorem moore22_theorem4 {R : Set Pt} (hR : IsOpen R) (hRc : IsConnected R)
    (hRb : Bornology.IsBounded R) (hsc : MooreSimplyConnected R) :
    PropertyS R ↔ (IsConnected (frontier R) ∧ LocallyConnectedSpace (frontier R)) := by
  sorry

/-! ## Complementary domains of plane continua -/

/-- The boundary of every complementary domain of a plane continuum is a continuum (bounded or
unbounded domain). -/
theorem isConnected_frontier_complDomain {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    {x : Pt} (hx : x ∉ M) : IsConnected (frontier (connectedComponentIn Mᶜ x)) := by
  sorry

/-- A bounded complementary domain of a plane continuum is simply connected in Moore's sense
(REPORT-batch150 §5 (b)). -/
theorem mooreSimplyConnected_complDomain {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    {x : Pt} (hx : x ∉ M) (hb : Bornology.IsBounded (connectedComponentIn Mᶜ x)) :
    MooreSimplyConnected (connectedComponentIn Mᶜ x) := by
  sorry

/-! ## Whyburn 1939 (6.22), in the form §14 uses -/

/-- **(6.22), §14 form** (p. 747: "Then by (6.22) there exists a `δ > 0` and a component `N` of
`M − M·V_δ(p)` which contains `M − M·V_ε(p)`"). For a compact semi-locally-connected continuum `M`
and a non-cut point `p`, stated in the subtype `M`. -/
theorem whyburn39_6_22_sec14 {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    (hS : ∀ z : X, SemiLocConnAt z) {p : X} (hp : IsConnected ({p}ᶜ : Set X)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, δ < ε ∧ ∃ c ∈ (ball p δ)ᶜ,
      (ball p ε)ᶜ ⊆ connectedComponentIn (ball p δ)ᶜ c := by
  sorry

end HPC.Jones
