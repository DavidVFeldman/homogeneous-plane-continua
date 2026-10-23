Commission read: `doc/batches/COMMISSION-batch162.md` (batch 162 — Part E, Hagopian 1976 VII: Lemma 7 by half-ray density; Lemma 9's proof; T6–T9, T11, Property 3).

# Report, batch 162

**Status.**
* **Proved:** item A in full.
  * `halfray_dense`, in the skeleton's shape, unchanged.
  * `halfray_inter` (new): the two half-rays meet only in the layer.
  * **Lemma 7** (`hagopian76_lemma7`), in the skeleton's shape, unchanged.
* **Also proved, outside the batch's items:** T10, **Property 2** (`hagopian76_property2`). It is
  immediate from Lemma 7 (§1.6).
* **Open** (commented out with `OPEN (batch 162, …)` notes, no `sorry`; obstructions in `OPEN.md`,
  batch-162 section): item B (Lemma 9, so T3 and T6), T7, T8, T9 in full, T11, Property 3.
* **Refuted:** nothing.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76G` at the end of `HPC.lean`. Every new
theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (§3).

**Files** (all under `HPC/Hagopian/`, namespace `HPC.Hagopian`).

| file | content |
|---|---|
| `Hagopian76G.lean` | the skeleton: `halfray_dense`, `halfray_inter`, `hagopian76_lemma7`, `hagopian76_property2` proved; Lemma 9, T6, T7, T8, T9 in full, T11, Property 3 commented out with `OPEN (batch 162)` notes and proposed shapes |
| `H76HalfRay.lean` | `piece_end_layers`, `piece_map`, `Rset_eq_of_maps`, `extUnion_eq_of_subset`, `closure_Rset_eq_of_subset`, `closure_Rset_piece`, `closure_Rset_of_common`, `closure_Rset_essential`, `halfray_inter_subset`, `halfray_dense_aux` |
| `H76Lemma7Ray.lean` | `exists_F_halfray` (steps 3–4), `lemma7_aux` (Lemma 7) |

The skeleton's `True` placeholders for the items marked *shape left to you* (T6, T7, T8,
`hagopian76_T9_full`, T11, Property 3) are not kept as declarations, since none of these items is
proved. Each is a block comment that quotes the printed sentence, states the obstruction, and
proposes a shape.

**Edits to existing files** (all allowed by the commission):
* `HPC.lean`: one import added.
* `Axioms.lean`, `axioms.txt`: the new group.
* `README.md`, `LEDGER.md` §6, `OPEN.md`.
* `Hagopian76D.lean`, `Hagopian76E.lean`, `Hagopian76F.lean`: the commented-out copies of
  `hagopian76_lemma7` are replaced by the one-line pointer
  ``-- `hagopian76_lemma7`: proved in batch 162, `Hagopian76G.lean`.``

**Housekeeping.**
* The commission is `doc/batches/COMMISSION-batch162.md`, and the uploaded skeleton is kept unchanged
  in `doc/batches/skeletons/Hagopian76G.lean`.
* The root copy of `REPORT-batch161.md` was removed; it is byte-identical to
  `doc/batches/REPORT-batch161.md`.
* The scheduling note `theorems-3-4-scheduling(9).md` was moved to `doc/notes/`.

Nothing is left at the root.

## 1. The items

### 1.1 Item A: `halfray_dense` and Lemma 7 — proved

**Your reading of Hagopian's sentence (commission §1, steps 1–5) is confirmed, and it is the formal
proof.** `lemma7_aux` follows `lemma7_of_F` (batch 161): sequences, a convergent subsequence in
`M³`, the limits `t`, `u`, `p`, then `ε′`, `j`, and the triod. The only change is that the hypothesis
`Lemma7F` is replaced by a construction of `F` from the sequences.

1. **Step 1.** Lemma 2 at `u`, with `η = ε/12`, gives `g` with `g(u) = uᵢ` and displacement `< η`,
   for `i` large; `f = g⁻¹`. Also `ρ(tᵢ, t) < ε/2` and `1/(i + 1) < η`.
2. **Step 2.** Put `G = hᵢ⁻¹[Hᵢ]`, which is essential to `R(E)`. Its map `b` is the transport of `dᵢ`
   (`exists_image_map`), and its layer `W = hᵢ⁻¹[Uᵢ]` is interior. Then `y = hᵢ⁻¹(g(t)) ∉ W`:
   * otherwise `g(t) ∈ Uᵢ`;
   * but `ρ(tᵢ, g(t)) ≤ ρ(tᵢ, t) + ρ(t, g(t)) < ε/2 + ε/12`, while `ρ(tᵢ, Uᵢ) > ε`.
3. **Step 3.** `halfray_inter_subset`: let `K₊` be an extension of `d⁻¹[[c, 1]]` away from `d⁻¹(c)`,
   and `K₋` an extension of `d⁻¹[[0, c]]` away from `d⁻¹(c)`. Then `K₊ ∩ K₋ ⊆ d⁻¹(c)`. The proof:
   * `G` is an extension of `d⁻¹[[c, 1]]` away from `d⁻¹(1)`, and of `d⁻¹[[0, c]]` away from
     `d⁻¹(0)`. So `ext_inter_subset` gives `K₋ ∩ G ⊆ d⁻¹[[0, c]]`.
   * Suppose a point off `d⁻¹(c)` lay in `K₊ ∩ K₋`. That set is a continuum (hereditary
     unicoherence), and it meets the end layer `d⁻¹(c)` of `K₊`. So it contains a band of layers of
     `K₊` next to `d⁻¹(c)` (`layerSet_Ioo_subset`).
   * Since `d⁻¹[[c, 1]]` is an initial segment of `K₊` (`hagopian76_initial_segment`), that band
     contains points of `d⁻¹((c, 1])`. These points lie in `K₋ ∩ G ⊆ d⁻¹[[0, c]]`, which is a
     contradiction.
4. **Step 4.** By `halfray_dense_aux`, each half-ray is dense in `Cl R(E)`. So there are extensions
   `K₊`, `K₋` with points within `η` of `p`. By step 3, at least one of them misses `y`; call it `K`.
   It contains the point `hᵢ⁻¹(uᵢ)` of `W` (`exists_F_halfray`). Set `F = f[hᵢ[K]]`. Then:
   * `u = f(uᵢ) ∈ F`;
   * `t ∉ F`, because `t ∈ F` would give `y ∈ K`;
   * `F` meets `A`, since `ρ(fhᵢ(z), p) < η + 1/(i + 1) + η < ε/4`.
5. **Step 5.** As in `lemma7_of_F`, ending with `lemma7_triod`.

The commission's step 3 ("If `t` lies on the line at all, its layer is on one side") is used in the
form of step 3 above: the two half-rays meet only in the layer, so a point off the layer misses at
least one of them. Which half-ray `t` "lies on" is never decided; the proof just takes one that
misses it.

**Half-ray density: the argument written out.** The commission's sentence was: "Both are composants
of their closures and they share `E′`". Two composants of two indecomposable continua that share a
continuum need not have the same closure in general, so the formal argument does not use
composants. It uses extensions and Lemma 6, step 8:

1. **End layers of a piece** (`piece_end_layers`). Let `G` be of type A′ with continuous
   decomposition (Lemma 5) and `a < b`. Then *every* minimal admissible map `p` of the piece
   `P = d⁻¹[[a, b]]` has end layers `d⁻¹(a)` and `d⁻¹(b)`, in one order or the other. The proof:
   * take `x ∈ d⁻¹(a)` and `z ∈ d⁻¹(b)`. The piece `p⁻¹[[min, max]]` of `P` between them meets
     `d⁻¹(a)` and `d⁻¹(b)`, so it is `P` (`eq_layerSet_of_subcontinuum`). Hence
     `{p(x), p(z)} = {0, 1}`;
   * if some `w ∈ d⁻¹(a)` had `p(w) > 0`, then `p⁻¹[[p(w), 1]]` would meet `d⁻¹(a)` and `d⁻¹(b)`
     but miss `x`;
   * if some `w` had `p(w) = 0` and `d(w) > a`, then `d⁻¹[[d(w), b]]` would meet both end layers of
     `p` but miss `x` (`end_sets_aux`).

   Consequences:
   * `piece_map`: a piece carries a minimal admissible map with end layers `d⁻¹(a)`, `d⁻¹(b)`;
   * `Rset_eq_of_maps`: `R(·)` does not depend on the minimal admissible map, since the end layers
     are intrinsic.
2. **Same end, larger continuum** (`extUnion_eq_of_subset`). If `P ⊆ Q` and both have the same layer
   `X` over `0`, then `R(X, P) = R(X, Q)`. One inclusion is immediate: an extension of `Q` away from
   `X` is one of `P`. For the other, an extension `K` of `P` away from `X` is comparable with `Q`
   (`ext_chain`): either `K ⊆ Q`, or `K` is an extension of `Q`. With Lemma 6, step 8, this gives
   `Cl R(P) = Cl R(Q)` (`closure_Rset_eq_of_subset`).
3. **Pieces** (`closure_Rset_piece`). `Cl R(d⁻¹[[a, b]]) = Cl R(G)`. The proof goes through
   `d⁻¹[[0, b]]`:
   * it has the same far end as `d⁻¹[[a, b]]` (reversed maps, step 2);
   * it has the same near end as `G` (step 2).
4. **A common piece** (`closure_Rset_of_common`). Suppose a continuum `J` lies in `G` and in `K` and
   meets two layers of each. Then `J` is a piece of both, and steps 1 and 3 give
   `Cl R(G) = Cl R(J) = Cl R(K)`.
5. **Essential continua** (`closure_Rset_essential`): `Cl R(G) = Cl R(E)`. There are three cases.
   * If `G ⊆ R(X, E)`, then `G` lies in an extension of `E` and meets two of its layers. This is the
     argument of `essential_typeA'_of_subset`. Take `J = G` and apply step 2 to `E ⊆` that extension.
   * If `G ⊆ R(Z, E)`: the same, for the reversed map.
   * Otherwise (two-sided, as in `essential_typeA'_two_sided`), `E ⊆ G ⊆ K ∪ Q` with `K` an extension
     away from `X` and `Q` one away from `Z`. Then `G ∩ K` meets two layers of `K` (`X` and a point
     outside `E`), and similarly for `G ∩ Q`. One of `G ∩ K`, `G ∩ Q` meets two layers of `G`: if
     both lay in single layers of `G`, those layers would share `E`, so `G` would lie in one layer.
     Apply step 4.
6. `halfray_dense_aux` then follows. By Lemma 6, step 8 (`closure_extUnion_aux`, or
   `closure_extUnion_one` for the lower half), `Cl` of the half-ray is `Cl R(d⁻¹[[u, 1]])`. That
   equals `Cl R(G)` by step 3 and `Cl R(E)` by step 5.

**Shape changes.** None. `halfray_inter` is new and is the content of the commission's step 3.

**`Lemma7F`.** It is not needed, and the skeleton no longer refers to it. It is neither proved nor
refuted. A Knaster-type counterexample is not cheap here: refuting it would need a space satisfying
the standing hypotheses, which is what Theorem 1 says does not exist. `Lemma7F`,
`hagopian76_lemma7_of_F` and `lemma7_of_F_composant` stay in the build (batch 161) and are now
superseded.

### 1.2 Item B: Lemma 9's proof in collar rectangles (T3, T6) — open

Not formalized. The configuration of report 161 §1.6 stands. Three constructions are missing; none
was done:
1. the chain `{G₁, G₂, G₃}` of collar rectangles about `π[E]` with `π[I − {y}]` vertical (the inputs
   are available: `exists_collar`, `plane_schoenflies₂`, `layer_nbhd_small`);
2. its lift to `M` and a Lemma-8 refinement whose links are again rectangles in the quotient
   (`lemma8_caps_sep` gives `C ∩ G₂`, whose image is not a rectangle, and the exit point `b₁` is on
   the right side only for rectangles);
3. the application of `moore62_theorem28`.

T3 and T6 wait on this. A shape for T6 is proposed in the comment in `Hagopian76G.lean`.

### 1.3 T7, T8, T9 in full — open

* **T7.** The printed sentence is unargued (ledger check 4). It needs three things:
  * an accessible point `y ∈ M ∩ L₆` with `π(y)` above `π[E]`;
  * Property 1 at `y` (proved);
  * that the Jordan domain between `⟨p₁, p₅⟩` and a subarc of `π[A]` lies in `π[St L]`. This needs
    the links of `L` in collar coordinates, as in item B.
* **T8 and T9.** Both need `I₂`. Given `I₂`:
  * `D` comes from the Jordan curve theorem in the repository;
  * property (D) of `hagopian76_T9` follows from "every point between `I₂` and `⟨p₁, p₅⟩` is in
    `π[St L]`", once the verticals are known to lie in `L₂ ∪ L₁₀`;
  * the first sentence of T9 is then `hagopian76_T9`.

  "`L − {L₁, L₁₁}` follows `Cl B`" needs `Cl B` to reach both verticals.

### 1.4 T11 — open

It needs `D`. The batch-161 obstruction still holds: the printed `ε₁` does not decide the sides of
`K`. In collar coordinates the sides would be decided by abscissae, which again needs the links
controlled.

### 1.5 Property 3 — open

It needs `D`.
* (i) "the first point `v`": unargued (ledger check 7). Closedness of the set of such `v` is a
  crossing property of `D` for limits.
* (ii) Unchanged from batch 161.

"By Lemmas 2 and 3" stays proved (`hagopian76_property3_shift`).

### 1.6 T10, Property 2 — proved (added)

p. 346: "Define `ε₂` to be the minimum of `ε₁` and `ρ(M, π⁻¹[I₁ ∪ I₂])`. By Lemma 7, there exists a
positive number `ε₃` less than `ε₂` such that if `h` is an `ε₃`-homeomorphism of `M` onto `M`, then
`h[R(E)]` has the following property: PROPERTY 2. If `H` is a continuum essential to `h[R(E)]` with
end sets `T` and `V` such that `ρ(T, V) < ε₃` and if there exists an element `U` of the decomposition
of `H` such that `ρ(T, U) > ε₂`, then each point of `R(E)` is within `ε₂` of `H`."

`hagopian76_property2`: for every `ε₂ > 0` there is `ε₃ ∈ (0, ε₂)` with Property 2, rendered as in
Lemma 7. It is Lemma 7 at `ε = ε₂` with `ε₃ = min(δ, ε₂/2)`. It is stated for arbitrary `ε₂`, because
Hagopian's `ε₂` depends on `I₁`, `I₂` (T6, T7), which are open; the instance at his `ε₂` follows once
they exist.

## 2. Ledger entries

`LEDGER.md` §6, "Hagopian 1976 VII … (batch 162)", checks 1–7:

| check | place | outcome |
|---|---|---|
| 1 | pp. 343–344, Lemma 7, "By Lemma 2, an integer `i` and a homeomorphism `f` … exist such that a continuum `F` …" | unargued; **true; proved** by steps 1–5. Whether `F` is essential was not checked, and it is not used. `Lemma7F` is too strong and not needed |
| 2 | pp. 344–345, Lemma 9, the Theorem 28 configuration | not formalized; configuration as in report 161; open |
| 3 | p. 346, T6, "It follows from the proof of Lemma 9 …" | depends on item B; open |
| 4 | p. 346, T7, "By choosing `y` sufficiently close to `E` …" | unargued; open |
| 5 | p. 346, T8, T9, "Note that the chain `L − {L₁, L₁₁}` follows `Cl B`" | depends on `D`; open |
| 6 | p. 347, T11, "Note that `K` separates …" | unargued; open (as in batch 161) |
| 7 | p. 347, Property 3, "Let `v` be the first point of `[0, 1]` such that …" | unargued; open |

No statement is refuted, and no defective proof is added. The count stays at fourteen.

## 3. Axioms

`doc/batches/audits/axioms-batch162.txt` lists `#print axioms` for the 16 new theorems: the 4
skeleton theorems and 12 supporting ones. Every line is `[propext, Classical.choice, Quot.sound]`,
and `sorryAx` appears in none. `axioms.txt` is regenerated with the group "Hagopian 1976 VII (batch
162)" (1572 lines), and `sorryAx` appears in no line.

| theorem | axioms |
|---|---|
| `halfray_dense`, `halfray_inter`, `hagopian76_lemma7`, `hagopian76_property2` | standard three |
| `piece_end_layers`, `piece_map`, `Rset_eq_of_maps` | standard three |
| `extUnion_eq_of_subset`, `closure_Rset_eq_of_subset`, `closure_Rset_piece`, `closure_Rset_of_common` | standard three |
| `closure_Rset_essential`, `halfray_inter_subset`, `halfray_dense_aux` | standard three |
| `exists_F_halfray`, `lemma7_aux` | standard three |

## 4. Dependency map of Theorem 1, updated

| step (page) | content | status after batch 162 |
|---|---|---|
| T0–T2 (345) | type A′ `E`; accessibility; `S`, `π`, the arc `π[E]` | proved (batches 155, 157, 158) |
| T3 (345) | each point of `π[E]` is an end of an arc segment below `π[E]` | Lemma 9 (open: collar-rectangle chain, Lemma-8 refinement by rectangles, Theorem 28) |
| T4 (345–346) | `ε₁` | proved (`hagopian76_eps1`); the collar families still to be added with T6–T8 |
| T5 (346) | `Wₓ`, `Gₓ`, `Gᵢ`; `L`; Property 1 | proved |
| T6 (346) | `I₁` below `⟨p₁, p₅⟩` | needs the proof of Lemma 9 |
| T7 (346) | `I₂` above; the region between in `π[St L]` | open (unargued sentence; collar control of `L`) |
| T8 (346) | the bounded domain `D` | needs T7 (Jordan curve theorem available) |
| T9 (346) | components of `M ∩ π⁻¹[D]` | first sentence proved for `D` with (D); rest needs T8 |
| T10 (346) | `ε₂`, `ε₃`; **Property 2** | **proved** (`hagopian76_property2`, for every `ε₂ > 0`; Hagopian's `ε₂` needs `I₁`, `I₂`) |
| T11 (347) | `K` separates in `π⁻¹[D]` | open: needs T8 and the sides of `K` |
| T12 (347) | `p ∈ K`, `f = h₁h⁻¹` | Lemma 6 (proved), Lemma 2; needs T11 |
| T13 (347) | `F` irreducible w.r.t. (1), (2) | Lemma 6 (proved), Lemma 4; needs T12 |
| T14 (347) | Property 3 | "By Lemmas 2 and 3" proved; the least `v` and the crossing property open |
| T15 (347–348) | `e`, `J`, `xᵢ` | `d⁻¹[[0, e]] = E` proved; Property 3 |
| T16 (348) | Property 4 | Property 2 |
| T17 (348–349) | the induction | Property 2 (twice), Property 3, Lemma 6 (proved), Lemma 4, Lemma 5 |

**Gateways now.**
1. The collar geometry: Lemma 9's proof, then T6–T8 and `D`. T9 (rest), T11, Property 3, and from
   them T12–T17, all wait on `D`.
2. Property 2 (T10) is proved. Lemma 7 is no longer a gateway.

## 5. Skeleton proposal for the rest of Theorem 1

Common context, as in report 161 §5:
* `M : Set Pt`, compact, connected, homogeneous and indecomposable;
* `E`, `k` with `IsMinimalAdmissible E k`;
* `π`, `γ` as in `exists_quotient_plane'`, and `F` with `IsCollar γ F`;
* `ε₁` with `IsEps1 k ε₁`;
* `L` from `hagopian76_property1`;
* `D`, `K` from T8 and T11 (still open).

The shapes below are proposals. The exact quantifiers of Property 4 are to be checked against
p. 348.

```lean
-- T10, Property 2: proved in this batch (`hagopian76_property2`).

/-- **T12** (p. 347): a point `p ∈ K` and `ε₃/2`-homeomorphisms `h`, `h₁` with (1) `p ∈ h[E] ∩ h₁[E]`,
(2) `Cl` of the component of `M ∩ π⁻¹[D]` at `p` is essential to `h[R(E)]`, (3) `D − K` separates
`p` from `f(p)`, `f = h₁ h⁻¹`. -/
theorem hagopian76_T12 … : ∃ (p : M) (h h₁ : M ≃ₜ M), (p : Pt) ∈ K ∧ (∀ v, dist v (h v) < ε₃ / 2) ∧
    (∀ v, dist v (h₁ v) < ε₃ / 2) ∧ IsEssential (transport h k)
      (closure (connectedComponentIn (M ∩ π ⁻¹' D) p)) ∧
    connectedComponentIn (π ⁻¹' D \ K) p ≠ connectedComponentIn (π ⁻¹' D \ K) ((h₁.trans h.symm) p)

/-- **T13** (p. 347): `F` irreducible with respect to (1) being an extension of `E` away from
`k⁻¹(0)` and (2) containing a component of `M ∩ π⁻¹[D]` that separates `p` from `f(p)`. Existence: the
extensions away from `k⁻¹(0)` form a chain (`ext_chain`), and their union is dense
(`hagopian76_closure_extUnion`); irreducibility by a minimum over the chain (`hagopian76_lemma4_seq`). -/
theorem hagopian76_T13 … : ∃ F d, IsExtensionAway E (layer k 0) F ∧ IsMinimalAdmissible F d ∧
    layer d 0 = layer k 0 ∧ Sep F p (f p) ∧ ∀ F', IsExtensionAway E (layer k 0) F' → Sep F' p (f p) → F ⊆ F'

/-- **T14, Property 3**: no crossing component of `F ∩ π⁻¹[D]` lies in a layer of `F`. -/
theorem hagopian76_property3 … : ∀ Q ∈ crossingComponents F D, ∀ t, ¬ Q ⊆ layer d t

/-- **T15** (pp. 347–348): `e` with `d⁻¹[[0, e]] = E`; the finite collection `I` of minimal intervals
`[a, b]` such that `d⁻¹[[a, b]]` contains a crossing component; `J = I ∪ {[0, e]}`; the increasing
`x₁ < … < x₂ₙ` of their end points. -/
theorem hagopian76_T15 … : ∃ (n : ℕ) (x : ℕ → unitInterval), StrictMonoOn x (Finset.range (2 * n)) ∧
    x 0 = 0 ∧ (∀ i < n, MinCrossing F d D (x (2 * i)) (x (2 * i + 1))) ∧ …

/-- **T16, Property 4** for `[x₂ᵢ₋₁, x₂ᵢ]`. -/
def Property4 (F d D K f x) (i : ℕ) : Prop :=
  ∃ y ∈ K, IsEssential' (layerSet d (Icc (x (2 * i)) (x (2 * i + 1)))) ∧
    connectedComponentIn (π ⁻¹' D \ K) y ≠ connectedComponentIn (π ⁻¹' D \ K) (f y)

/-- **T17** (pp. 348–349): Property 4 passes down (Cases 1 and 2, each using Property 2 once), and
fails for `[x₁, x₂]`. -/
theorem hagopian76_T17_step … (h4 : Property4 … (i + 1)) : Property4 … i
theorem hagopian76_T17_base … : ¬ Property4 … 0

/-- **Theorem 1** (p. 345). -/
theorem hagopian76_theorem1 : Hagopian76Thm1
```

**The assembly.** Assume `M` has a decomposable subcontinuum.
1. T0 (`hagopian75_typeA'`) gives the type A′ `E`, and T1–T2 give `π` and the arc.
2. T3–T8 give `D`. T9–T11 give `K`, and T10 gives `ε₃`.
3. T12–T15 give `n`, the `xᵢ`, and Property 4 for the last interval (T16).
4. T17 descends to `[x₁, x₂]`, which contradicts the base case.

**Proposed order for batch 163:**
1. Lemma 9's proof in collar rectangles (item B, carried over).
2. T7 and T8, which give `D`.
3. T11 and Property 3.
4. T12 and T13.
