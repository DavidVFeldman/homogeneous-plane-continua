Commission read: `doc/batches/COMMISSION-batch160.md` (batch 160 — Part E, Hagopian 1976 V: Lemma 6 in full, Lemma 7; two-sided Schoenflies; Lemma 9).

# Report, batch 160

**Status.**
* **Proved** (all in the skeleton's shapes, unchanged):
  * item A: `hagopian76_lemma6_X` (`Cl R(X, E)` is indecomposable), `hagopian76_closure_extUnion`
    (`Cl R(X, E) = Cl R(E)`), `hagopian76_lemma6` (`Cl R(E)` is indecomposable), and the unnumbered
    claims `hagopian76_Rset_composant` (`R(E)` is a composant of `Cl R(E)`) and
    `hagopian76_essential_typeA'` (every continuum essential to `R(E)` is of type A′);
  * item C: `layer_nbhd_small` (upper semicontinuity in metric form);
  * item D: `plane_schoenflies₂` (Schoenflies with two adjacent sides prescribed).
* **Open** (commented out with `OPEN (batch 160, item …)` notes, no `sorry`; obstructions in
  `OPEN.md`, batch-160 section):
  * B. `hagopian76_lemma7`;
  * E. `hagopian76_lemma9`.
* **Refuted:** nothing.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76E` at the end of `HPC.lean`. Every new
theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (§3).

**Files** (all under `HPC/Hagopian/`, namespace `HPC.Hagopian`).

| file | content |
|---|---|
| `Hagopian76E.lean` | the skeleton: items A, C, D proved (each a one-line application of the supporting theorem below); Lemma 7 and Lemma 9 commented out with `OPEN (batch 160)` notes |
| `H76USC.lean` | item C: `layer_nbhd_small_aux` |
| `H76Schoen2.lean` | item D: `quad_split_two_pt`, `plane_schoenflies₂_aux` |
| `H76Absorb.lean` | absorption: `ext_of_irreducible_union_eq`, `absorb_point`, `subset_extUnion_of_meets` |
| `H76Lemma6.lean` | Lemma 6, steps 1–5: generalities (`exists_pos_le_dist`, `layer_zero_subset_closure`, `layer_zero_subset_of_meets`, `subset_of_meets_ends`, `IsExtensionAway.isContinuum`, `IsExtensionAway.subset_extUnion`, `IsExtensionAway.end_subset`, `exists_mem_ext_not_mem`, `isContinuum_closure_extUnion`, `ext_upper`), `lemma6_step1`, `lemma6_step2`, `lemma6_step3`, `lemma6_main`, `lemma6_X_aux` |
| `H76Step8.lean` | step 8 and Lemma 6: `mem_layerSet_val`, `mem_layer_val`, `false_of_indec_subset_layers`, `extUnion_one_subset`, `closure_extUnion_aux`, `lemma6_aux` |
| `H76Composant.lean` | `not_indec_of_minimalAdmissible`, `closure_extUnion_one`, `not_isClosed_extUnion`, `subset_union_of_escape`, `exists_ext_of_subset`, `ext_inter_subset`, `Rset_composant_aux` |
| `H76Essential.lean` | `lsc_of_minimalAdmissible`, `Rset_symm_comp`, `IsEssential.symm_comp`, `end_layer_param`, `essential_typeA'_of_subset`, `not_isClosed_Rset`, `exists_ext_cover`, `essential_typeA'_two_sided`, `essential_typeA'_aux` |

Housekeeping: the commission and the skeleton are in `doc/batches/COMMISSION-batch160.md` and
`doc/batches/skeletons/Hagopian76E.lean`; a stray scheduling note found at the root was moved to
`doc/notes/theorems-3-4-scheduling(6).md`, and a duplicate root copy of `REPORT-batch159.md` removed
(identical to the one in `doc/batches/`). Nothing is left at the root. In `Hagopian76D.lean` the
commented-out copies of `hagopian76_closure_extUnion`, `hagopian76_lemma6`,
`hagopian76_Rset_composant`, `hagopian76_essential_typeA'` are replaced by one-line pointers to
`Hagopian76E.lean`; the batch-159 note above them and the commented-out Lemma 7 and Lemma 9 are kept
(both still open).

## 1. The items

### A. Lemma 6 and the unnumbered claims: proved

Notation: `X = k⁻¹(0)`, `Z = k⁻¹(1)`, `𝓕` the extensions of `E` away from `X`, `Fᵢ` the sequence
of `hagopian76_lemma4_seq`, `R = R(X, E) = ⋃ Fᵢ`.

**The commission's reading of steps 1–5 was checked and is correct**, with one simplification that
changes the shape of the proof.

**Absorption** (`H76Absorb.lean`, `subset_extUnion_of_meets`). *A continuum `G` that misses `X` and
meets some `F ∈ 𝓕` lies in `R(X, E)`.* For `g ∈ G`, take an irreducible continuum `H` from a point of
`X` to `g` inside `F ∪ G`. Through a point of `F ∩ G` pass three continua: `H ∩ F`, the tail of `F`
beyond that point, and `H ∩ G`; by atriodicity (`three_continua`) `H ⊇ F`, so `H = F ∪ (H ∩ G)`, and
the extension step (`ext_of_irreducible_union_eq`, the batch-156 lemma with a stronger conclusion)
makes `H` an extension away from `X`. This is exactly Hagopian's sentence "Since `M` is atriodic, it
follows that `f[L]` is a subset of `R(X, E)`" (step 5), in a form that does not mention `f`.

**Steps 1–5** (`H76Lemma6.lean`), under `Cl R = B ∪ C` with `B`, `C` proper subcontinua:
1. `lemma6_step1`: one of `B`, `C` contains `X` (as in the commission, via `E ∩ B`, `E ∩ C` and the
   interval lemma at `0`, `layer_zero_subset_of_meets`).
2. `lemma6_step2`: `X ∩ C = ∅` (as in the commission; `subset_of_meets_ends`).
3. `lemma6_step3`: if `K ∈ 𝓕` meets `C − B`, then `Cl R − C ⊆ K` (stronger than `B − C ⊆ K`; the
   points outside `R` are handled by closure, as in the commission).
4.–5. `lemma6_main`. *The simplification:* `C` misses `X` (step 2) and meets `K`, so by absorption
   `C ⊆ R`. Hence the cluster point `c` of the far-end points `zᵢ ∈ C` lies in `R`. Step 5 then gives
   the contradiction directly: `L ∈ 𝓕` containing `K ∪ {c}`, `w ∈ R − L`,
   `δ = min(ρ(X, C), ρ(w, L))`, Lemma 2 gives `i` and a `δ`-homeomorphism `f` with `f(c) = zᵢ`,
   `w ∈ Fᵢ`; `L ∩ f[L] = ∅` (the commission's argument: `f[L] ∩ Fᵢ` is a continuum through `zᵢ`,
   and if it met `L = d⁻¹[[0, ℓ]]` it would contain `d⁻¹((ℓ, 1))`, which contains `w`); `f[L] ⊆ R`
   (absorption: `f[L]` misses `X` since `f[L] ∩ L = ∅`, and meets `Fᵢ` at `zᵢ`); and
   `f[X] ⊆ (B ∪ C) − C ⊆ K ⊆ L`, against `L ∩ f[L] = ∅`. On "if `c` is not in an interior layer of
   `L`, say what changes": nothing changes. The proof uses only `c ∈ L` (with `L = F_ℓ`, `ℓ` large),
   because the disjointness argument needs only `zᵢ = f(c) ∈ f[L]` and `w ∉ f[L]`.

**Steps 6–7 are not needed.** Hagopian proves in step 5 that `c ∉ R(X, E)` and then derives a
contradiction from `c ∉ R(X, E)` in steps 6–7 (homeomorphisms `h₁`, `h₂`, the triod
`C ∪ N ∪ h₁⁻¹[N] ∪ h₂⁻¹[P]`). Since absorption gives `C ⊆ R(X, E)` outright, the case `c ∉ R(X, E)`
is empty. Steps 6–7 were not formalized and not checked further (ledger check 1.6–1.7). The
"subcollection" premise of step 6 (`hagopian76_initial_segment`) is used elsewhere: in steps 2–3 and in
the type A′ claim.

**Step 8** (`H76Step8.lean`, `closure_extUnion_aux`): `Cl R(X, E) = Cl R(E)`, proved with the
1975 ¶2 argument directly (`hagopian75_no_indecomposable_interior`), without the homeomorphisms
`f₁`, `f₂`. Let `I = Cl R(X, E)` (indecomposable by steps 1–5) and suppose an extension `Q` away from
`Z` has a point `c ∉ I`. If `I ⊆ Q`, then `I` meets two layers of `Q` (it contains `X` and `Z`), and
a continuum meeting two layers inside a continuum with a minimal admissible map is decomposable
(`false_of_indec_subset_layers`). Otherwise take `b ∈ I` in no proper subcontinuum of `I` through a
point `p ∈ X` (`T13.exists_not_mem_proper_subcontinua`); then `b ∉ Q`, an irreducible continuum `E'`
from `b` to `c` in `I ∪ Q` contains `I`, and `I` has interior in `E'` — against the 1975 lemma.
`lemma6_aux` (= `hagopian76_lemma6`) follows.

**`hagopian76_Rset_composant`** (`H76Composant.lean`). `⊆`: for `y ∈ R(E)`, take extensions `F₁ ∋ x`,
`F₂ ∋ y` (each away from `X` or from `Z`, both containing `E`); `F₁ ∪ F₂` is a subcontinuum of
`Cl R(E)`, and it is proper because `Cl R(E)` is indecomposable while each extension is decomposable
(`not_indec_of_minimalAdmissible`). `⊇`: a proper subcontinuum `P` of
`Cl R(E)` through `x ∈ F` gives the proper subcontinuum `A = P ∪ F ⊇ E`. By step 8 (and its mirror
`closure_extUnion_one`) there are extensions `K`, `Q` away from `X`, `Z` not inside `A`. Of the three
continua `A`, `K`, `Q` through a point of `X`, one lies in the union of the other two (atriodicity).
Since `K ∩ Q ⊆ E ⊆ A` (`ext_inter_subset`: the two sides meet only in `E`), that one is `A`, so
`P ⊆ A ⊆ K ∪ Q ⊆ R(E)`.

**`hagopian76_essential_typeA'`** (`H76Essential.lean`).
* *The containment of report 158 §1.C* is `exists_ext_of_subset`: a continuum `G ⊆ R(X, E)` lies in
  one extension away from `X`. Otherwise `G ∪ F_{i₀}` contains all of `R(X, E)` (the interval lemma
  in a large `F_m`), so `R(X, E)` is closed (`not_isClosed_extUnion` refutes this). Then
  `R(X, E) = Cl R(X, E)` would be indecomposable (Lemma 6) and the increasing union of the proper
  subcontinua `Fᵢ` through a point of `X`, which a composant argument excludes. **It does not use
  `c ∉ R(X, E)`**; that statement is never proved (§1.A above: under the hypothesis of Lemma 6 it is
  in fact `c ∈ R(X, E)` that holds). It uses Lemma 6 through `not_isClosed_extUnion`.
* `H ⊆ R(X, E)`: `H` lies in one extension `G'`, meets two of its layers (the layers of smaller
  extensions are layers of larger ones, `hagopian76_initial_segment`; if the given extension is away
  from `Z`, the two points lie in `E` by `ext_inter_subset`), and `isTypeA'_of_subcontinuum` with
  Lemma 5 applies (`essential_typeA'_of_subset`). `H ⊆ R(Z, E)`: the same for the reversed map.
* Otherwise (`essential_typeA'_two_sided`): by absorption `H` meets `X` and `Z`, so `H ⊇ E`.
  `H ∩ R(X, E)` lies in one extension `K` away from `X` and `H ∩ R(Z, E)` in one extension `Q` away
  from `Z` (`exists_ext_cover`; otherwise `H ∪ F₀ = Cl R(E)`, and then `H = Cl R(E)` by
  indecomposability, against `not_isClosed_Rset`). With `b` the farthest point of `H ∩ K` in `K` and
  `a` the farthest point of `H ∩ Q` in `Q`, `H` is irreducible between `a` and `b` (Lemma 5 in `K` and
  `Q`: `H ∩ K`, `H ∩ Q` are initial segments), and `H ⊆ (H ∩ Q) ∪ (H ∩ K)` with `a ∉ K`, `b ∉ Q`.
  The 1975 ¶2 argument (`no_indecomposable_interior_aux`) makes `H` decomposable, and
  `isTypeA'_of_decomposable` gives type A′.

### B. Lemma 7: open

Lemma 6 and the type A′ claim, the two dependencies named in batch 159, are now proved. The
obstruction is in the proof itself (p. 343):
1. "By Lemma 2, an integer `i` and a homeomorphism `f` of `M` onto `M` exist such that a continuum
   `F` essential to `fhᵢ[R(E)]` contains `u`, misses `t`, and intersects `A`." Here `t`, `u`, `p` are
   limit points in `Cl R(E)` of `tᵢ ∈ Tᵢ`, `uᵢ ∈ Uᵢ`, `pᵢ ∈ R(E)`, and `A = {x ∈ M : ρ(x, p) < ε/4}`.
   Lemma 2 moves single points. Producing a continuum essential to a translate of `R(E)` that passes
   through `u`, misses `t` and meets `A` is not argued. The composant property (now proved) joins
   points of `R(E)` by proper subcontinua, but `u` and `t` are only limit points, and the separation
   from `t` is not addressed.
2. "Note that `g[F] ∪ Hⱼ` is a triod in `M`." The three arms are not written out: `g[F]` from `uⱼ`
   towards `A` (which `Hⱼ` misses), and the two parts of the type A′ continuum `Hⱼ` from `uⱼ` to `Tⱼ`
   and to `Vⱼ`.
The statement stays commented out in `Hagopian76E.lean` (and, unchanged, in `Hagopian76D.lean`).

### C. `layer_nbhd_small`: proved

`layer_nbhd_small_aux`. The points of `E` outside the open `ε`-neighbourhood of `k⁻¹(s)` form a
compact set. Its image under `k` is compact and misses `s`, so it misses an interval `(s − δ, s + δ)`.
The shape is the skeleton's. Its section variables `[CompactSpace M] [ConnectedSpace M]` are omitted
for this theorem, since the proof does not use them (the statement is otherwise unchanged).

### D. `plane_schoenflies₂`: proved

`plane_schoenflies₂_aux`, shape unchanged. **Route different from the commission's suggestion:** no
homeomorphism of the square is needed. Moore's form (`m19_schoenflies_boundary_proof`) already
prescribes all four sides of the quadrilateral. The quadrilateral is chosen with side `AB = ψ` and
side `DA = φ`: the arc `range ψ ∪ range φ` from `ψ 1` to `φ 1` has a complementary arc in `J`, which
is cut once at a point `C` (`quad_split_two_pt`). The transport to `Pt` is the one of batch 159
(`plane_schoenflies_aux`).

### E. Lemma 9: open

Its two inputs from report 159 §1.E (1)–(2) are now proved: `plane_schoenflies₂` puts `π[I − {y}]`
vertical in the same coordinates as `π[E]`, and `layer_nbhd_small` gives the `ε` conditions on the
chain. Not formalized: the chain `{G₁, G₂, G₃}` built from collar rectangles, the application of
Lemma 8 with caps (`U = G₁`, `V = G₃`), and the application of Theorem 28 to the rectangle `π[G₂]`.
The configuration proposed for it, with the four boundary points named, is:
* `J = Bd π[G₂]`, the boundary rectangle of the simple domain;
* `a₁`: where `π[E]` leaves `π[G₂]` towards `π[G₁]` (left side);
* `a₂`: where `π[I]` crosses the bottom side;
* `b₁`: where `πh[D]` leaves towards `π[G₃]` (right side);
* `b₂`: the foot of the vertical segment `A` on the bottom side.

`π[C ∪ I]` joins `a₁` to `a₂` and `πh[D]` joins `b₁` to `b₂`, inside `Cl π[G₂]`. The interlacing
`a₁, b₂, a₂, b₁` around `J` is what Theorem 28 forbids for disjoint continua. Freeness of `L` is
needed to keep `πh[D]` off the left side. This is a reconstruction; it has not been checked formally.

## 2. Ledger entries

`LEDGER.md` §6, "Hagopian 1976 V … (batch 160)", checks 1–4. In summary:

| check | place | outcome |
|---|---|---|
| 1.1 | p. 342, step 1 ("… it follows that `B` contains `X`") | true; proved (`lemma6_step1`) |
| 1.2 | p. 342, step 2 ("The sets `X` and `C` are disjoint") | true; proved (`lemma6_step2`) |
| 1.3 | p. 342, step 3 ("Note that `B − C` is contained in `K`") | unargued; true; proved in a stronger form (`lemma6_step3`) |
| 1.4 | p. 342, step 4 ("Since `M` is second countable …") | true (`hagopian76_lemma4_seq`); proved |
| 1.5 | p. 342, step 5 ("… the sets `L` and `f[L]` are disjoint. Since `M` is atriodic, it follows that `f[L]` is a subset of `R(X, E)`") | unargued; true; proved; the second sentence is *absorption*, which also gives `C ⊆ R(X, E)` and so `c ∈ R(X, E)` |
| 1.6 | p. 342, step 6 ("… the point `c` belongs to `R(E)`") | not needed (case `c ∉ R(X, E)` empty); not checked further |
| 1.7 | p. 343, step 7 ("Thus `C ∪ N ∪ h₁⁻¹[N] ∪ h₂⁻¹[P]` is a triod") | not needed; not checked further |
| 1.8 | p. 343, step 8 ("… is a triod (see the second paragraph in the proof of Theorem 1 of [5])") | citation correct; proved without homeomorphisms (`closure_extUnion_aux`) |
| 2 | p. 343, the unnumbered claims | unargued; true; proved; the containment uses "`R(X, E)` is not closed", not `c` |
| 3 | pp. 343–344, Lemma 7, two sentences | unargued; open (§1.B) |
| 4 | pp. 344–345, Lemma 9 | WLOG: both inputs now proved; Theorem 28 application: configuration proposed (§1.E); open |

No statement of Hagopian's is refuted, and no defective proof is added: the count stays at fourteen.
Steps 6–7 of Lemma 6 turn out to be superfluous, but they are not wrong as far as checked.

## 3. Axioms

`doc/batches/audits/axioms-batch160.txt` lists `#print axioms` for the new theorems: the seven
skeleton theorems and 43 supporting ones, 50 lines. Every line is
`[propext, Classical.choice, Quot.sound]`, and `sorryAx` appears in none. `axioms.txt` is regenerated
with the group "Hagopian 1976 V (batch 160)", and `sorryAx` appears in no line.

| theorem | axioms |
|---|---|
| `hagopian76_lemma6_X` | standard three |
| `hagopian76_closure_extUnion` | standard three |
| `hagopian76_lemma6` | standard three |
| `hagopian76_Rset_composant` | standard three |
| `hagopian76_essential_typeA'` | standard three |
| `layer_nbhd_small` | standard three |
| `plane_schoenflies₂` | standard three |
| supporting (`H76USC`, `H76Schoen2`, `H76Absorb`, `H76Lemma6`, `H76Step8`, `H76Composant`, `H76Essential`) | standard three |

## 4. Dependency map of Theorem 1, updated

| step (page) | content | status after batch 160 |
|---|---|---|
| T0–T2 (345) | type A′ `E`; accessibility; `S`, `π`, the arc `π[E]` | proved (batches 155, 157, 158) |
| T3 (345) | each point of `π[E]` an end of an arc segment below `π[E]` | Lemma 9 (open: the chain and the Theorem 28 configuration); **two-sided Schoenflies and u.s.c. in metric form now proved** |
| T4 (345–346) | `ε₁` | unblocked; `layer_nbhd_small` available |
| T5 (346) | `Wₓ`, `Gₓ`, `Gᵢ`; ordered free refinement `L`; **Property 1** | unblocked: Lemma 2, Lemma 8 with caps, Lemma 1 |
| T6 (346) | `I₁` below `(p₁, p₅)` | needs Lemma 9 (or its proof) |
| T7 (346) | `I₂` above; the region between in `π[St L]` | Property 1, Lemma 9 |
| T8 (346) | the bounded domain `D` | Jordan curve theorem; Schoenflies (one or two sides) available |
| T9 (346) | components `B` of `M ∩ π⁻¹[D]`, closures `ε₁`-images of essential continua | **unblocked**: Lemma 5, `hagopian76_essential_typeA'` (proved); Property 1 |
| T10 (346) | `ε₂`, `ε₃`; **Property 2** | Lemma 7 (open; Lemma 6 no longer the obstruction) |
| T11 (347) | `K` separates in `π⁻¹[D]` | unblocked: Theorem 28, Property 1 |
| T12 (347) | `p ∈ K`, `f = h₁h⁻¹` | **Lemma 6 proved**; unblocked |
| T13 (347) | `F` irreducible w.r.t. (1), (2) | **Lemma 6 proved**, composant property proved; Lemma 4 |
| T14 (347) | **Property 3** | unblocked: Lemmas 1–3, Property 1 |
| T15 (347–348) | `e`, `J`, `xᵢ` | `d⁻¹[[0, e]] = E` proved; Property 3 |
| T16 (348) | **Property 4** | Property 2 / Lemma 7 |
| T17 (348–349) | the induction | Lemma 6 (proved), Property 3, Lemma 4, Lemma 5, Property 2 |

**Gateways now.** (i) Lemma 7 / Property 2 (T10, T16, T17); (ii) Lemma 9 (T3, T6, T7), now reduced to
the chain and the Theorem 28 configuration; (iii) Property 1 (T5, T7, T9, T11, T14), unblocked.

## 5. Skeleton proposal for batch 161: Property 1, T4–T9, T11, T14 (collar coordinates)

Revised from report 159 §5. `plane_schoenflies₂` and `layer_nbhd_small` are proved and drop out.
T9 can now be stated, since essential continua are of type A′.

Common context: `M : Set Pt` compact connected homogeneous indecomposable; `E`, `k` with
`IsMinimalAdmissible E k`; `π`, `γ` as in `exists_quotient_plane'`; `F` with `IsCollar γ F`. An
`ε`-homeomorphism is `h : M ≃ₜ M` with `∀ v, dist v (h v) < ε`. Write
`piece i := layerSet k (Icc ((i-1)/11) (i/11))` for `i = 1, …, 11`, and
`rect a b c := F '' (Ioo a b ×ˢ Ioo (-c) c)`.

```lean
/-- **T4, `ε₁`** (pp. 345–346): non-adjacent elevenths stay apart under `ε₁`-homeomorphisms. -/
theorem hagopian76_eps1 (hX) (hi) (hE : IsMinimalAdmissible E k) :
    ∃ ε₁ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) →
      ∀ i ∈ Finset.Icc 1 11, ∀ j ∈ Finset.Icc 1 11, (i : ℤ) + 1 < j →
        Disjoint (Metric.thickening ε₁ (toPt (h '' piece i)))
                 (Metric.thickening ε₁ (toPt (h '' piece j)))

/-- **T5, `Wₓ`** (p. 346). -/
def Wset (M : Set Pt) (ε : ℝ) (x : M) : Set M :=
  {y | ∃ h : M ≃ₜ M, h x = y ∧ ∀ v, dist v (h v) < ε}

/-- **T5, `Gₓ`**: an open set of the plane with `Wₓ = M ∩ Gₓ` (Lemma 2: `Wₓ` is open in `M`). -/
theorem exists_Gset (hX) {ε : ℝ} (hε : 0 < ε) (x : M) :
    ∃ G : Set Pt, IsOpen G ∧ toPt (Wset M ε x) = M ∩ G

/-- **T5, the chain `{Gᵢ}`**: collar rectangles over the elevenths of `γ`, intersected with
`π[St Gₓ]`, following `E`; the `ε₁` condition from `layer_nbhd_small`. -/
theorem hagopian76_chain11 (…) (hF : IsCollar γ F) {ε₁ : ℝ} (hε₁ : 0 < ε₁) :
    ∃ G : Fin 12 → Set Pt, IsPlaneChain G ∧ Follows G k ∧
      (∀ i, π '' G i = rect ((i - 1/2) / 11) ((i + 1/2) / 11) (c i)) ∧
      (∀ i, ∀ p ∈ G i, ∃ q ∈ toPt (piece i), dist p q < ε₁)

/-- **Property 1** (p. 346). `L` from `hagopian76_lemma8_caps` with `U ⊆ G₀ − Cl G₁`,
`V ⊆ G₁₁ − Cl G₁₀`. -/
theorem hagopian76_property1 (…) (hL : IsOrderedRefinement L G) (hLf : Follows L k)
    (hLfree : IsFree M L) :
    ∀ K : Set M, K ∈ connectedComponentsIn (M ∩ ⋃ i, L i) → (toPt K ∩ L 6).Nonempty →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ h '' E ⊆ K ∧
        (toPt K ∩ L 0).Nonempty ∧ (toPt K ∩ L 11).Nonempty

/-- **T6–T8**: `I₁`, `I₂`, `D` in collar coordinates (definitions as in report 159 §5). -/
def Iarc₁ (F : ℝ × ℝ → Pt) (t₁ h : ℝ) : Set Pt := F '' ({t₁} ×ˢ Ico (-h) 0)
def Iarc₂ (F : ℝ × ℝ → Pt) (t₂ h : ℝ) : Set Pt := F '' ({t₂} ×ˢ Ioc 0 h)
def Dom (F : ℝ × ℝ → Pt) (t₁ t₅ h : ℝ) : Set Pt := F '' (Ioo t₁ t₅ ×ˢ Ioo 0 h)

/-- **T9** (p. 346), now statable: the closure of a component of `M ∩ π⁻¹[D]` meeting
`L₄ ∪ … ∪ L₈` is the image under an `ε₁`-homeomorphism of a continuum essential to `R(E)`
(hence of type A′, `hagopian76_essential_typeA'`). -/
theorem hagopian76_T9 (…) :
    ∀ B : Set M, B ∈ connectedComponentsIn (M ∩ π ⁻¹' Dom F t₁ t₅ hh) →
      (toPt B ∩ ⋃ i ∈ Finset.Icc 4 8, L i).Nonempty →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ IsEssential k (h ⁻¹' closure B)

/-- **T11** (p. 347): `K`, the component of `π⁻¹[D ∩ (p₃, q₃)]`, separates `π⁻¹[D]` (Theorem 28 on
the rectangle `D`, Property 1). -/
theorem hagopian76_T11 (…) :
    ¬ IsPreconnected (M ∩ π ⁻¹' Dom F t₁ t₅ hh \ toPt K)

/-- **Property 3** (p. 347). -/
theorem hagopian76_property3 (…) :
    ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₂) → (toPt (h '' E) ∩ toPt K).Nonempty →
      ∃ B, B ∈ connectedComponentsIn (M ∩ π ⁻¹' Dom F t₁ t₅ hh) ∧
        toPt (h '' E) ∩ π ⁻¹' closure (Dom F t₁ t₅ hh) ⊆ closure (toPt B)
```

Order proposed: T4, T5 / Property 1, T9, T14 / Property 3, T11. Then Lemma 9 with the configuration of
§1.E. Lemma 7 / Property 2 last, starting from the two sentences of §1.B.
