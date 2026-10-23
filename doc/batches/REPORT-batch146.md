Commission read: `doc/batches/COMMISSION-batch146.md` (batch 146, Part E, Moore 1925 II: arcs and closed curves of elements, Theorems 5–12; Mullikin).

# Report, batch 146

All items A–G are **proved**; the refutations of items A and B1 are proved as negations. Nothing
is left open, so `OPEN.md` is unchanged. `lake build HPC` succeeds with `import HPC.Moore.M25B` at
the end of `HPC.lean`; no new file contains `sorry`, and every new theorem uses only `propext`,
`Classical.choice` and `Quot.sound` (`doc/batches/audits/axioms-batch146.txt`, 118 theorems).
`axioms.txt` is regenerated (1057 lines, `sorryAx` in none; the previous version is kept as
`doc/batches/audits/axioms-before-batch146.txt`), with the new group *Moore 1925 §I, Theorems 5–12
(batch 146)* in `Axioms.lean`.

**Files.** The skeleton (kept verbatim at `doc/batches/skeletons/Moore1925II.lean`) is split:

| file | content |
|---|---|
| `HPC/Moore/CutArc.lean` | cut-point arcs (`IsCutArc`): irreducible, an embedded `[0, 1]` in a metrizable space; Nadler 6.7; the circle characterization `circle_char` (Moore 1920 Theorem 4) |
| `HPC/Moore/M25BDefs.lean` | the skeleton's four definitions, verbatim |
| `HPC/Moore/M25B5.lean` | `not_separatesPlane_ptsOf`, Theorems 5–8 |
| `HPC/Moore/M25B9.lean` | Theorems 9, 10, 12 |
| `HPC/Moore/Borsuk.lean` | Borsuk's logarithm theorem for the plane (`borsuk_exists_log`) |
| `HPC/Moore/Mullikin.lean` | Mullikin's Theorem 5, corrected |
| `HPC/Moore/Mullikin4.lean` | Mullikin's Theorem 4 at `M₁ ∩ M₂ = ∅` |
| `HPC/Moore/M25B11.lean` | Theorem 11 |
| `HPC/Moore/M25BPts.lean`, `M25BRefute.lean` | the decomposition into points; the refutations |
| `HPC/Moore/M25B.lean` | umbrella |

**Statements.** Every skeleton statement is verbatim, except `not_m25_theorem7_printed`: its
placeholder `True` is replaced by the negation of the printed Theorem 7 (shape change recorded at
the statement). Added: `not_m25_theorem11_singleton`, `not_moore1920_theorem4_singleton`,
`mullikin_theorem4_disjoint`, `not_mullikin_theorem4_disjoint_mathlib`, and the general results of
`CutArc.lean`, `Borsuk.lean`.

## The items

**A. Refutations of the printed definitions** (decomposition into points, `mooreDecomp_ptSetoid`).
1. `not_m25_theorem2_printed`: **proved**. `M` the closed unit disc, `D` the open disc minus the
   radius `T = [0, 1/2] × {0}`, `E` the plane minus `T`; the omission of `(1/4, 0)` disconnects
   `∂E = T`.
2. `not_m25_theorem10_printed`, `not_m25_theorem11_printed`: **proved** with two disjoint parallel
   segments. A single element satisfies Moore 1920's Definition 4 vacuously, and **1920 Theorem 4 is
   false for a one-point set** as printed (`not_moore1920_theorem4_singleton`); 1925 Theorem 11
   fails for a single element too (`not_m25_theorem11_singleton`), which justifies `J.Nontrivial`
   in `IsSCCElt`.

**B. Mullikin.**
1. `not_mullikin_theorem5_printed`: **proved**, with the commission's candidate (`M₁ = M₂` a
   segment, `K₁` the half-open half, `K₂` the closed other half).
2. `mullikin_theorem5`: **proved** by logarithms (shorter than Mullikin's polygons, which are not
   followed). *Separation* (`not_isConnected_compl_union`): the function equal to `1` on `M₁` and
   `exp (2πiφ)` on `M₂`, with `φ` a Urysohn function `0` on `K₁`, `1` on `K₂`, has no logarithm on
   `M₁ ∪ M₂`, while Borsuk's theorem gives one if the complement is connected. *"Just two"*
   (`compl_union_two_components`, Eilenberg's bound): of three components two are bounded, and a
   product of integer powers of `(z − p)/(z − y)`, `(z − q)/(z − y)` would have a logarithm on
   `M₁ ∪ M₂`, against `no_log_pow_of_bounded_component`. Borsuk's theorem (`borsuk_exists_log`: on
   a compact set with connected complement, every nonvanishing map has a logarithm) is proved by
   smooth approximation (Stone–Weierstrass), Sard's theorem, and removal of the finitely many
   good zeros.
   *Her Theorem 4 at `M₁ ∩ M₂ = ∅`*: under her convention (p. 144) the empty set is connected, and
   the theorem then says the union does not disconnect the plane: **true**
   (`mullikin_theorem4_disjoint`). Under Mathlib's convention the sentence would claim the opposite,
   which is false (`not_mullikin_theorem4_disjoint_mathlib`).

**C. Theorems 5–8.** **Proved**, as instances in the space of elements (metrizable by
`quotient_metrizable_plane`) of `CutArc.lean`: Theorem 5 from the embedding into `[0, 1]`; Theorem 6
from `eq_image_Icc_of_subset_range` and `isCutArc_image_Icc`; Theorem 7 (with `x` for the printed
`p`) from the sub-arcs `f [s, t]`, `s < u < t`, which form a neighbourhood base of `x` in `pq`;
Theorem 8 from Nadler 6.7 (`exists_nonCut_diff`). For Theorem 8, Moore's proof is followed in
substance, with batch 94's non-cut point theorem in place of the appeal to Theorem 5.
`not_m25_theorem7_printed` (optional) is **proved**.

**D. Theorem 9.** **Proved** (`m25_theorem9`). The domain `D` of an element `x ∉ pq` cannot be
bounded: otherwise let `E` be the unbounded complementary domain of `∂D` and `K′ = ∂E`; by Theorem 2,
`K′` is a continuum and `K′ − r` is connected for each `r ∈ K′`; `K′` has at least two elements
(since `G − r` is connected); `K′ ⊆ ∂D ⊆ pq`, so by Theorem 6 `K′` is an arc, and its interior
elements disconnect it. *The unbounded case:* every complementary domain of `pq` is then unbounded,
and two unbounded ones coincide (`m25_unbounded_unique`), so `G − pq` is connected. *What Lemma 8 of
P.C.S. argues:* see ledger, "Further outcomes": a bounded complementary domain, its outer boundary
with respect to prime parts, Lemma 6 makes it an arc with uncountably many cut prime parts,
contradicting Lemma 3; the passage from "separates" to "has a bounded complementary domain" is
tacit there.

**E. Theorem 10.** **Proved** (`m25_theorem10`) from `circle_char`, applied to the compact
`J` (closed with bounded point set) in the Hausdorff quotient.

**F. Theorem 11.** **Proved** (`m25_theorem11`), Moore's proof with `not_separatesPlane_ptsOf` and
`mullikin_theorem5` (`K₁ = p̄`, `K₂ = q̄`). The gap of check 4 is real and is repaired as the
commission proposes (`frontier_eq_of_scc`).

**G. Theorem 12.** **Proved** (`m25_theorem12`), Moore's proof as printed, with "domain" read as
nonempty.

## Ledger entries (`LEDGER.md` §6, new subsection "batch 146")

1. Theorem 8's proof: both sentences confirmed; the conditions for "`K₂ + p` would be a simple
   continuous arc" (`p ≠ q`, boundedness, cut elements) are supplied from the negated supposition.
2. Theorem 11's proof: (a) confirmed (`not_separatesPlane_ptsOf`); (b) supplied (uniqueness of the
   unbounded domain; boundedness of the plane otherwise); (c) supplied (each element off `J̄` lies in
   one domain).
3. "In a similar way … boundary of `E`": confirmed, one lemma for both.
4. The main gap: confirmed; the commission's repair confirmed and used.
5. Theorem 12: "domain" read as nonempty.
6. P.C.S. Lemma 5 erratum: recorded; Lemma 5 not used.
7. Moore 1920 Theorem 4: the general proof needs only Hausdorff + compact connected (metrizability
   only for embeddings); the 1925 instance needs compactness of `J` and Hausdorffness of the
   quotient. False for a one-point set. Definition 4 is on p. 342 of our copy (commission: p. 340).

The batch-145 entry 9 is corrected as asked (Axiom 5₁ in the Math. Z. paper); the rest of it is
unchanged.

## Axioms per theorem

Every theorem below depends exactly on `[propext, Classical.choice, Quot.sound]` (full list:
`doc/batches/audits/axioms-batch146.txt`):
`not_m25_theorem2_printed`, `not_m25_theorem7_printed`, `not_m25_theorem10_printed`,
`not_m25_theorem11_printed`, `not_m25_theorem11_singleton`, `not_moore1920_theorem4_singleton`,
`not_mullikin_theorem5_printed`, `mullikin_theorem5`, `mullikin_theorem4_disjoint`,
`not_mullikin_theorem4_disjoint_mathlib`, `borsuk_exists_log`, `not_separatesPlane_ptsOf`,
`m25_theorem5` … `m25_theorem12`, `frontier_eq_of_scc`, `circle_char`,
`IsCutArc.exists_embedding`, `isCutArc_image_Icc`, `IsCutArc.isConnected_diff_ends`,
`mooreDecomp_ptSetoid`.

## Reading plan for batch 147 (Theorems 13–22, pp. 422–425)

* **Theorem 13** (a region minus an element or an arc of elements, with at most one end on the
  boundary, is a domain). Moore's proof: Theorem 9, `not_separatesPlane_ptsOf`, then Janiszewski
  (`janiszewski_compact`; the intersection of `k̄` and `B̄` is empty or one element, hence connected
  or empty). Short.
* **Theorem 14** (every region contains a simple closed curve of elements): F.A. Theorem 15 for
  `S(G)` (`m25_fa_theorem15`, arcs in regions) and Theorem 13; "contains as a subset a simple closed
  curve" needs a sub-arc argument (first and last meeting points), which `CutArc.lean` supports.
* **Theorems 15–18** (analogues of F.A. 24–27). Batches 138's proofs of F.A. 24–27 exist in a
  *topological* form (`Gen.th24_*`, `Gen.th25`, `Gen.th26`, `Gen.th27`, `Sec6Th24`–`Sec6Th27.lean`),
  stated for a Hausdorff, locally connected space `T` and a family `reg` of open sets, with
  hypotheses: members open and preconnected; `Th21Prop reg` (F.A. Theorem 21); `ArcConn T`; Axiom 8
  for `reg` (`Ax8Prop`, with topological simple closed curves `TSCC`); exteriors preconnected;
  closures compact; `T` noncompact. **These transfer** to `S(G)` with `reg` = interiors of simple
  closed curves of elements, the hypotheses coming from what is now available:
  open/preconnected and exteriors preconnected (Theorem 11: `I`, and `(cl I)ᶜ = E`);
  `Th21Prop` (Theorem 12, the boundary `J` being connected); `ArcConn` (`m25_fa_theorem15`);
  `Ax8Prop` (Theorem 11, once `TSCC J ↔ IsSCCElt J` is proved: `circle_char` and
  `IsCutArc.exists_embedding` one way, `isCutArc_range` the other); compact closures (closed with
  bounded point set); noncompactness (Axiom 5, `m25_axiom5`). Moore's remark that F.A. Theorem 21 *"may
  be easily proved with the help of Theorem 11"* is exactly `Th21Prop` via Theorem 12.
  The proofs in σ-form (`fa_theorem24` …, which assume Axioms 1–8 for an abstract space) do **not**
  transfer directly, since Axioms 3, 7, 8 are not yet available for `S(G)`.
* **Theorem 19** (analogue of F.A. 36). `fa_theorem36` is proved only in σ-form (Axioms 1–8); its
  `Gen` helpers (`Sec7B.lean`) cover part of it. Plan: either restate the remaining steps (F.A.
  Theorems 33, 35, 20) in the `Gen` form, or prove Theorem 19 directly in the plane: a small circle
  about `p̄` inside `R̄`, made into a curve of elements by Theorem 3's construction (polygon about the
  tube, as in `m25_theorem3`), whose element-image contains a simple closed curve of elements
  (Theorem 14's sub-arc argument). The direct route looks shorter.
* **Theorem 20** (restricted regions give the same limit elements): from Theorems 4 and 19, as Moore
  writes; it says the restricted regions form a basis of the quotient topology.
* **Theorem 21** (Axioms 1–8 for restricted regions). Axioms 1, 2, 4, 5: from `m25_axioms1245`
  through Theorems 19, 20 (restricted regions refine the original ones). **Axiom 3** (`S − R′`
  connected): Theorem 11 (`cl I = I ∪ J`, complement `E`). **Axioms 6′, 7′, 6, 7** (not yet defined
  in the project; to be transcribed from F.A. p. 135 and 1925 p. 425): for a restricted region `R`
  (interior of `J`) and an element `P ∈ J`, the regions `K ⊆ R`, `L ⊆ ext R` are built from
  Theorems 15–18 (a cross-cut of `J` near `P` through `R`, respectively through the exterior), using
  Theorem 7 for the sub-arcs of `J` about `P`. **Axiom 8**: Theorem 11, with `TSCC ↔ IsSCCElt` as above.
* **Theorem 22** (`Quotient r ≃ₜ ℝ²`): with `σ` = `S(G)` with restricted regions, Theorem 21 gives
  Axioms 1–8 and `m19_plane` a homeomorphism `(S(G), σ.topology) ≃ₜ ℝ²`; by Theorem 20 the restricted
  regions are a basis of the quotient topology, so `σ.topology` is the quotient topology (as
  `spaceOfElts_topology` for the original regions), and the homeomorphism is `Quotient r ≃ₜ ℝ²`.
