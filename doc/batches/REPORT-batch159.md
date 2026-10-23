Commission read: `doc/batches/COMMISSION-batch159.md` (batch 159 — Part E, Hagopian 1976 IV: Lemma 6, Lemma 7; plane Schoenflies and collars; Lemma 9).

# Report, batch 159

**Status.**
* **Proved:**
  * item C: `plane_schoenflies` (the plane Schoenflies theorem, one side of the square sent onto a
    prescribed arc of `J`) and `exists_collar` (every arc of the plane has a two-sided collar), both
    in the skeleton's shapes, unchanged;
  * item D: `hagopian76_lemma8_caps` (Lemma 8 with prescribed caps), shape chosen (§1.D);
  * item E, first part: the definition `DecompAccessibleC` is in the build as given.
* **Open** (commented out with `OPEN (batch 159)` notes, no `sorry`; obstructions in `OPEN.md`,
  batch-159 section):
  * A. `hagopian76_closure_extUnion`, `hagopian76_lemma6`, `hagopian76_Rset_composant`,
    `hagopian76_essential_typeA'`;
  * B. `hagopian76_lemma7`;
  * E. `hagopian76_lemma9`.
* **Refuted:** nothing.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76D` at the end of `HPC.lean`. Every new
theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (§3).

**Files** (all under `HPC/Hagopian/`, namespace `HPC.Hagopian`).

| file | content |
|---|---|
| `Hagopian76D.lean` | the skeleton: items C, D and `DecompAccessibleC` proved / defined; items A, B, Lemma 9 commented out with `OPEN (batch 159)` notes |
| `H76Schoen.lean` | item C: `plane_schoenflies_aux` (transport of `m19_schoenflies_boundary_proof` to `Pt` through `mooreDecomp_ptSetoid`), `image_eq_sccInterior`, `region_restricted_pt`, `plane_split` (the cross-cut theorem in the plane, transported from Moore 1919), `quad_split_pt`, `eq_or_eq_of_frontier` |
| `H76Invert.lean` | `IsHalfCollar`; `isHalfCollar_bounded` (a half-collar of an arc of a simple closed curve inside its bounded side, by Schoenflies); inversion about a point (`nsq`, `inv0`, `invc`, `invcInv`, …), `tarc_image_of_injOn`, `tscc_image_of_injOn`; `isHalfCollar_unbounded` (the same on the unbounded side, by inversion) |
| `H76Collar.lean` | `accessible_of_noncut`, `semiLocConnAt_of_locallyConnected`, `locallyConnectedSpace_unitInterval`; `TArc.semiLocConnAt`, `TArc.isConnected_compl`, `TArc.interior_eq_empty`, `TArc.isConnected_compl_end`, `TArc.exists_closing_arc` (every arc lies on a simple closed curve); `IsCollar` (moved here from the skeleton, unchanged); `exists_collar_aux` |
| `H76Lemma8Caps.lean` | item D: `lemma8_caps_aux` |

Housekeeping: the commission and the skeleton are in `doc/batches/COMMISSION-batch159.md` and
`doc/batches/skeletons/Hagopian76D.lean`; a stray scheduling note found at the root was moved to
`doc/notes/`, and a duplicate root copy of `REPORT-batch158.md` removed (identical to the one in
`doc/batches/`). Nothing is left at the root. In `Hagopian76C.lean` the docstring of `AbutSameSide`
gets the line "Superseded (batch 159) by the collar form `DecompAccessibleC`"; no statement of
`Hagopian76C.lean` was proved here, so no commented-out copy needed a pointer.

## 1. The items

### A. Lemma 6 and the unnumbered claims: open

Not formalized. Step 5 was examined first, as asked. Its formalization needs three things the
repository does not yet have:
1. **The exhausting sequence.** "Since `M` is second countable, there exists a monotone strictly
   increasing sequence `{Fᵢ}` of elements of `F` such that `R(X, E) = ⋃ Fᵢ` (Lemma 4)." Lemma 4
   (batches 156–158) gives that extensions away from `X` have no maximal element and that `E` is an
   initial segment of each (`hagopian76_initial_segment`). A cofinal *sequence* needs, in addition,
   that any two extensions away from `X` are comparable by inclusion (they are both irreducible from
   `X`, both contain `E`, and `M` is hereditarily unicoherent and atriodic — a triod argument that
   Hagopian does not write and that is not yet formalized), and then second countability.
2. **The limit `c`.** The far ends `zᵢ` converge (after a subsequence) to some `c`; that
   `c ∈ Cl R(X, E) − R(X, E)` uses that `c ∈ Fⱼ` for some `j` would make `Fⱼ` contain points beyond
   all `Fᵢ`, again via the linear order.
3. **The two sentences on `L` and `f[L]`.** "Since `M` is hereditarily unicoherent and `f[L]`
   contains `zᵢ` and misses `w`, and since `Fᵢ` is irreducible, the sets `L` and `f[L]` are
   disjoint. Since `M` is atriodic, it follows that `f[L]` is a subset of `R(X, E)`." The
   `δ`-homeomorphism `f` with `f(c) = zᵢ` is Lemma 2 (proved); the two triods are not written out.

`hagopian76_essential_typeA'` needs the containment of an essential continuum in one extension
(report 158 §1.C), which rests on (2); after it, `isTypeA'_of_subcontinuum` (batch 158) and Lemma 5
give the claim. `hagopian76_Rset_composant` and `hagopian76_closure_extUnion` sit inside Lemma 6's
proof. The obstruction is the linear order of extensions and the limit `c`; it is a pure continuum
theory obstruction (no plane topology).

### B. Lemma 7: open

Uses Lemma 6 (the essential continuum `F` of `fhᵢ[R(E)]`); unchanged from batch 158. The two
sentences ("By Lemma 2, an integer `i` and a homeomorphism `f` … exist such that a continuum `F`
essential to `fhᵢ[R(E)]` contains `u`, misses `t`, and intersects `A`"; "Note that `g[F] ∪ Hⱼ` is a
triod in `M`") are recorded in the ledger, check 3.

### C. Plane topology: proved

**`plane_schoenflies`** (shape unchanged): for a simple closed curve `J` with bounded complementary
domain `D` and an embedding `φ` of `[0, 1]` into `J`, there is an embedding `f` of the closed square
onto `J ∪ D` with `f(t, 0) = φ(t)` and the open square onto `D`. Route: `m19_schoenflies_boundary_proof`
(Moore 1919) holds in any model of Moore's axioms; the plane is one (`mooreDecomp_ptSetoid`); the
model's points are the classes of the trivial setoid on `Pt`, and `ptHomeo` identifies the restricted
space with `Pt`. `image_eq_sccInterior` identifies Moore's interior of `J` with `D`. The prescribed
bottom side is obtained by composing Moore's parametrization with a homeomorphism of the boundary
square (`quad_split_pt`).

**`exists_collar`** (shape unchanged). The skeleton's suggested route (glue two Schoenflies
embeddings along `γ`) is the one taken, with the θ-curve made explicit:
1. `TArc.exists_closing_arc`: the ends of `γ` are accessible from the connected complement of the arc
   (`accessible_of_noncut`, `TArc.isConnected_compl`), so there is an arc `β` from end to end meeting
   `γ` only in its ends; `J₁ = γ ∪ β` is a simple closed curve.
2. `exists_side_arc` (batch 158) gives a cross-cut `β₂` of the bounded side `I` of `J₁` between the
   ends; `plane_split` splits `I` into the bounded sides `R₁` of `γ ∪ β₂` and `R₂` of `β ∪ β₂`.
3. A half-collar of `γ` in `R₁ ∪ J` (`isHalfCollar_bounded`, Schoenflies on `γ ∪ β₂`) and one in the
   unbounded side of `J₁` (`isHalfCollar_unbounded`, Schoenflies after an inversion about a point of
   `I`, restricted to a strip along `γ`) are glued along `γ`.
4. The image of the open rectangle is open: near a point of the open arc the plane is covered by the
   two closed sides, since only `R₂` is missing and `Cl R₂` misses the open arc.
The one-sided alternative of the commission was not needed.

### D. Lemma 8 with prescribed caps: proved

**Shape chosen** (the skeleton left it `True`). For open `U ⊆ G₀`, `V ⊆ Gₙ` with `k⁻¹(0) ⊆ U`,
`k⁻¹(1) ⊆ V`, the caps are `A = U − E`, `B = V − E`. The conclusion: `E` is a component of
`M − (A ∪ B)` (every continuum `K ⊇ E` missing `A ∪ B` is `E`), and there are an open `C ⊇ E` and an
ordered refinement `L` of `G`, following `E`, free relative to `M`, with `L₀ = G₀`, `Lₙ = Gₙ`,
`Lᵢ = C ∩ Gᵢ` otherwise. The only uses of `A`, `B` in the proof of Lemma 8 are that `E` is a component
of `M − (A ∪ B)` and `A ∪ B ⊆ G₀ ∪ Gₙ`.
* For **Property 1** (p. 346: "`A` and `B` … are in `G₁ − G₂` and `G₁₁ − G₁₀`"), take
  `U ⊆ G₀ − Cl G₁`, `V ⊆ Gₙ − Cl Gₙ₋₁` (0-indexed), possible when the end sets lie there.
* For **Lemma 9**, take `U = G₀`, `V = Gₙ`.

### E. `DecompAccessibleC`; Lemma 9: definition given, Lemma 9 open

**Comparison of the collar form with Bing's (p. 215).** Bing: `Cl A`, `Cl B` *abut on the same side*
of the arc `π[E]` if a homeomorphism of the plane takes `π[E]` to a straight segment and `Cl A`,
`Cl B` to arcs that, near their ends on the segment, lie on one side of it (straightening the arc and
the two abutting arcs simultaneously). The collar form (`DecompAccessibleC`): for some collar `F` of
`γ` and some sign `σ`, the vertical segments `F({u} × σ(0, h₁])`, `F({y} × σ(0, h₂])` miss `π[M]`.
* *Collar ⇒ Bing.* The vertical segments are arc segments in `R² − π[M]` ending at `π[U]`, `π[Y]`, on
  side `σ`. A homeomorphism of the whole plane extending the collar coordinates exists by
  Schoenflies applied to the sides of the θ-curve of `exists_collar_aux` and to the exterior after an
  inversion — not formalized.
* *Bing ⇒ collar.* Given `A`, `B` abutting on one side, the collar can be re-chosen so that `Cl A`,
  `Cl B` become vertical near their feet (Schoenflies on the quadrilaterals cut off by `A`, `B` in the
  half-collar) — not formalized.
* The collar form is what the proof on pp. 345–346 uses: "`π[E]` is lying on a horizontal line … and
  `π[I − {y}]` is below `B` on a vertical line".

**Lemma 9: open.** What is needed:
1. **The vertical arc in the same collar.** The collar of `γ` (`exists_collar`) makes `π[E]`
   horizontal but prescribes no second arc. Making `π[I − {y}]` vertical in the same coordinates needs
   Schoenflies with *two* sides of the square prescribed (bottom on a sub-arc of `π[E]`, a vertical
   side on `π[I]`), applied to the simple closed curve formed by `π[E]`, `π[I]` and a closing arc
   (`TArc.exists_closing_arc` supplies the latter). `plane_schoenflies` prescribes one side; the
   two-side version follows from it by a homeomorphism of the square fixing the bottom side that
   straightens a second boundary arc — a reparametrization of the boundary, which Moore's theorem
   (any boundary homeomorphism extends) gives, but which is not yet stated.
2. **The chain `G`.** In collar coordinates `π[Gᵢ]` = open rectangles about the three thirds of
   `[0, 1] × {0}`; condition (1) ("each point of `Gᵢ` is within `ε` of `Hᵢ`") needs that preimages
   under `π` of small neighbourhoods of `π[Hᵢ]` are small — upper semicontinuity of the decomposition
   (batch 157) in metric form, not yet stated.
3. **The application of Theorem 28.** Reconstructed configuration (ledger check 5): simple domain
   `π[L₂]`, continua `π[C ∪ I]` and `πh[D]`; Hagopian does not name the four boundary points, and
   `π[L₂] = π[C ∩ G₂]` need not be a disk, whereas Theorem 28 is for simple domains. The fix proposed
   for batch 160: apply Theorem 28 to the rectangle `π[G₂]` and use freeness of `L` only to locate
   the continua's boundary points.

## 2. Ledger entries

`LEDGER.md` §6, "Hagopian 1976 IV … (batch 159)", checks 1–6. In summary:

| check | place | outcome |
|---|---|---|
| 1 | pp. 342–343, Lemma 6, steps 1–8 | steps 1, 2, 6 true; step 3 unargued, true as checked; step 4 needs the linear order of extensions (unargued); step 5 two unargued triod sentences; steps 7–8 not checked in detail; not formalized |
| 2 | p. 343, the unnumbered claims | containment of an essential continuum in one extension unargued (follows from step 5); open |
| 3 | pp. 343–344, Lemma 7, two sentences | unchanged: unargued details; depends on Lemma 6; open |
| 4 | p. 344, decomposably accessible [2, p. 215] | collar form recorded (`DecompAccessibleC`); comparison with Bing's form (§1.E); equivalence not formalized |
| 5 | pp. 344–345, Lemma 9, four sentences | WLOG: first half (horizontal `π[E]`) supplied by `exists_collar`, second half needs two-sided Schoenflies; the chain `G`: rectangles in collar coordinates, the `ε` condition needs u.s.c. in metric form; "`I` intersects `Bd G₂` …": true; [13, Theorem 28]: configuration reconstructed, four points unnamed by Hagopian, `π[L₂]` need not be a disk |
| 6 | p. 346, Lemma 8 with caps | true; proved in the chosen shape (`hagopian76_lemma8_caps`) |

No statement of Hagopian's is refuted; the count of defective proofs stays at fourteen.

## 3. Axioms

`doc/batches/audits/axioms-batch159.txt` lists `#print axioms` for the new theorems (the three
skeleton theorems and 37 supporting ones). Every line is `[propext, Classical.choice, Quot.sound]`
and `sorryAx` appears in none (40 lines). `axioms.txt` is regenerated with the group
"Hagopian 1976 IV (batch 159)", and `sorryAx` appears in no line.

| theorem | axioms |
|---|---|
| `plane_schoenflies` | standard three |
| `exists_collar` | standard three |
| `hagopian76_lemma8_caps` | standard three |
| supporting (`H76Schoen`, `H76Invert`, `H76Collar`, `H76Lemma8Caps`) | standard three |

## 4. Dependency map of Theorem 1, updated

| step (page) | content | status after batch 159 |
|---|---|---|
| T0–T2 (345) | type A′ `E`; accessibility; `S`, `π`, the arc `π[E]` | proved (batches 155, 157, 158) |
| T3 (345) | each point of `π[E]` an end of an arc segment below `π[E]` | Lemma 9 (open: two-sided Schoenflies, u.s.c. in metric form, the Theorem 28 configuration); collar, Schoenflies, Lemma 8 with caps, Theorem 28 now proved |
| T4 (345–346) | `ε₁` | unblocked; continuity of `k` and compactness; collar coordinates available |
| T5 (346) | `Wₓ`, `Gₓ`, `Gᵢ`; ordered free refinement `L`; **Property 1** | unblocked: Lemma 2, **Lemma 8 with caps (proved)**, Lemma 1 |
| T6 (346) | `I₁` below `(p₁, p₅)` | needs Lemma 9 (or its proof) |
| T7 (346) | `I₂` above; the region between in `π[St L]` | Property 1, Lemma 9 |
| T8 (346) | the bounded domain `D` | Jordan curve theorem; **Schoenflies now available** to give `D` collar-like coordinates |
| T9 (346) | components `B` of `M ∩ π⁻¹[D]` | Lemma 5 (proved); Property 1 |
| T10 (346) | `ε₂`, `ε₃`; **Property 2** | Lemma 7 (open, via Lemma 6) |
| T11 (347) | `K` separates in `π⁻¹[D]` | unblocked: Theorem 28, Property 1 |
| T12 (347) | `p ∈ K`, `f = h₁h⁻¹` | Lemma 6 |
| T13 (347) | `F` irreducible w.r.t. (1), (2) | Lemma 6 (proof); Lemma 4 |
| T14 (347) | **Property 3** | unblocked: Lemmas 1–3, Property 1 |
| T15 (347–348) | `e`, `J`, `xᵢ` | `d⁻¹[[0, e]] = E` proved; Property 3 |
| T16 (348) | **Property 4** | Property 2 / Lemma 7 |
| T17 (348–349) | the induction | Lemma 6, Property 3, Lemma 4, Lemma 5, Property 2 |

**Gateways now.** (i) Lemma 6 (T10, T12, T13, T16, T17), whose obstruction is the linear order of
extensions away from `X` and the limit `c`; (ii) Lemma 9 (T3, T6, T7), whose obstructions are
two-sided Schoenflies, u.s.c. in metric form and the Theorem 28 configuration; (iii) Property 1 (T5,
T7, T11, T14), now unblocked.

## 5. Skeleton proposal for batch 160: Property 1, T4–T9, T11, T14 (collar coordinates)

Common context: `M : Set Pt` compact connected homogeneous indecomposable; `E`, `k` with
`IsMinimalAdmissible E k`; `π`, `γ` as in `exists_quotient_plane'`; `F` with `IsCollar γ F`;
`Q := Icc 0 1 ×ˢ Icc (-1) 1`, `F` an embedding on `Q`. An `ε`-homeomorphism is
`h : M ≃ₜ M` with `∀ v, dist v (h v) < ε` (as in `hagopian76_lemma2`). Write
`piece i := layerSet k (Icc ((i-1)/11) (i/11))` for `i = 1, …, 11`. Collar rectangles:
`rect a b c := F '' (Ioo a b ×ˢ Ioo (-c) c)`.

```lean
/-- Two-sided Schoenflies (input to Lemma 9 and T6): bottom side on `φ`, left side on `ψ`. -/
theorem plane_schoenflies₂ {J D : Set Pt} (hJ : TSCC J) (hD : IsOpen D) (hDc : IsConnected D)
    (hDb : Bornology.IsBounded D) (hDJ : frontier D = J) {φ ψ : unitInterval → Pt}
    (hφ : IsEmbedding φ) (hψ : IsEmbedding ψ) (hφJ : range φ ⊆ J) (hψJ : range ψ ⊆ J)
    (h0 : φ 0 = ψ 0) (hφψ : range φ ∩ range ψ = {φ 0}) :
    ∃ f : unitInterval × unitInterval → Pt, IsEmbedding f ∧ range f = J ∪ D ∧
      (∀ t, f (t, 0) = φ t) ∧ (∀ t, f (0, t) = ψ t) ∧
      f '' {p | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1} = D

/-- u.s.c. in metric form (input to the `ε`-conditions on chains). -/
theorem layer_nbhd_small (hE : IsMinimalAdmissible E k) (hπ …) {ε : ℝ} (hε : 0 < ε)
    (s : unitInterval) : ∃ δ > 0, ∀ t, dist t s < δ →
      toPt (layer k t) ⊆ Metric.thickening ε (toPt (layer k s))

/-- **T4, `ε₁`** (pp. 345–346). -/
theorem hagopian76_eps1 (hX) (hi) (hE : IsMinimalAdmissible E k) :
    ∃ ε₁ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) →
      ∀ i ∈ Finset.Icc 1 11, ∀ j ∈ Finset.Icc 1 11, (i : ℤ) + 1 < j →
        Disjoint (Metric.thickening ε₁ (toPt (h '' piece i)))
                 (Metric.thickening ε₁ (toPt (h '' piece j)))

/-- **T5, `Wₓ`** (p. 346): `Wₓ = {y ∈ M | ∃ ε₁-homeomorphism h, h x = y}`; open by Lemma 2. -/
def Wset (M : Set Pt) (ε : ℝ) (x : M) : Set M :=
  {y | ∃ h : M ≃ₜ M, h x = y ∧ ∀ v, dist v (h v) < ε}

/-- **T5, `Gₓ`**: an open set of the plane with `Wₓ = M ∩ Gₓ`. -/
theorem exists_Gset (hX) {ε : ℝ} (hε : 0 < ε) (x : M) :
    ∃ G : Set Pt, IsOpen G ∧ toPt (Wset M ε x) = M ∩ G

/-- **T5, the chain `{Gᵢ}`** (`i = 0, …, 11`), in collar coordinates: `π[Gᵢ]` the rectangle over
the `i`-th eleventh of `γ`, slightly widened, intersected with `π[St Gₓ]`; following `E`. -/
theorem hagopian76_chain11 (…) (hF : IsCollar γ F) {ε₁ : ℝ} (hε₁ : 0 < ε₁) :
    ∃ G : Fin 12 → Set Pt, IsPlaneChain G ∧ Follows G k ∧
      (∀ i, π '' G i = rect ((i - 1/2) / 11) ((i + 1/2) / 11) (c i)) ∧
      (∀ i, ∀ p ∈ G i, ∃ q ∈ toPt (piece i), dist p q < ε₁)

/-- **T5, `L`**: from `hagopian76_lemma8_caps` with `U ⊆ G₀ − Cl G₁`, `V ⊆ G₁₁ − Cl G₁₀`. -/
-- (obtained, not a new statement: `obtain ⟨L, C, …⟩ := hagopian76_lemma8_caps … `)

/-- **Property 1** (p. 346): every component of `M ∩ St L` that meets `L₆` is the image under an
`ε₁`-homeomorphism of a subcontinuum of `E` meeting both end sets' caps, and meets `L₁`, `L₁₁`. -/
theorem hagopian76_property1 (…) (hL : IsOrderedRefinement L G) (hLf : Follows L k)
    (hLfree : IsFree M L) :
    ∀ K : Set M, K ∈ connectedComponentsIn (M ∩ ⋃ i, L i) → (toPt K ∩ L 6).Nonempty →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ h '' E ⊆ K ∧
        (toPt K ∩ L 0).Nonempty ∧ (toPt K ∩ L 11).Nonempty

/-- **T6, `I₁`**: an arc segment of `R² − π[M]` from `π[k⁻¹(1/11)]`-region below `(p₁, p₅)`,
in collar coordinates the vertical segment `F({t₁} × [-h, 0))`. -/
def Iarc₁ (F : ℝ × ℝ → Pt) (t₁ h : ℝ) : Set Pt := F '' ({t₁} ×ˢ Ico (-h) 0)

/-- **T7, `I₂`**: the arc above, `F({t₂} × (0, h])`, missing `π[M]`, with the region between `I₁`
and `I₂` inside `π[St L]`. -/
def Iarc₂ (F : ℝ × ℝ → Pt) (t₂ h : ℝ) : Set Pt := F '' ({t₂} ×ˢ Ioc 0 h)

/-- **T8, `D`**: the bounded domain of `I₂ ∪ (p₁, p₅) ∪ (p₁, r) ∪ (p₅, s)`; in collar coordinates
the open rectangle `F((t₁, t₅) × (0, h))` when the side arcs are vertical. -/
def Dom (F : ℝ × ℝ → Pt) (t₁ t₅ h : ℝ) : Set Pt := F '' (Ioo t₁ t₅ ×ˢ Ioo 0 h)

/-- **T9**: components of `M ∩ π⁻¹[D]` meeting `L₄ ∪ … ∪ L₈` have closures that are
`ε₁`-images of continua essential to `R(E)`. -/

/-- **T11**: `K`, the component of `π⁻¹[D ∩ (p₃, q₃)]`, separates `π⁻¹[D]` (Theorem 28 on the
rectangle `D`, Property 1). -/

/-- **Property 3** (p. 347): if `h` is an `ε₂`-homeomorphism and `h[E]` meets `K` then
`h[E] ∩ π⁻¹[Cl D]` lies in one component `B` as in T9 and `h[layer k 0] ∩ L₆ = ∅`. -/
theorem hagopian76_property3 (…) :
    ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₂) → (toPt (h '' E) ∩ toPt K).Nonempty →
      ∃ B, B ∈ connectedComponentsIn (M ∩ π ⁻¹' Dom F t₁ t₅ hh) ∧
        toPt (h '' E) ∩ π ⁻¹' closure (Dom F t₁ t₅ hh) ⊆ closure (toPt B)
```

The shapes of T9, T11 are left in prose: they depend on whether Lemma 6 (essential continua) is in
place; Property 1 and Property 3 can be proved without it. Order proposed: `plane_schoenflies₂` and
`layer_nbhd_small` first (they unblock both Lemma 9 and T4–T8), then T4, T5/Property 1, T14/Property
3, then Lemma 9 with the Theorem 28 configuration applied to the rectangle `π[G₂]`.
