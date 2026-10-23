# Commission: batch 196 — H–O Theorem 1, IV: Proposition 19; Theorem 20 from Theorem 15

**Go!** This batch runs on top of the batch-195 work. Two files come with it, as separate uploads:

* `COMMISSION-batch196.md`: this text, also pasted into the prompt.
* `HO16D.lean`: the skeleton.
  * Save it as `HPC/HO16/HO16D.lean`. You may split it under `HPC/HO16/`.
  * Add `import HPC.HO16.HO16D` at the end of `HPC.lean`. It imports `HPC.HO16.HO16C`.
  * **Also save both files under `doc/batches/`** (`doc/batches/COMMISSION-batch196.md`,
    `doc/batches/skeletons/HO16D.lean`) and include them in the tarball (§0).

No new sources. Page numbers are the journal's; PDF page `n` of
`doc/sources/hoehn-oversteegen2016.pdf` is journal page `176 + n`. H–O print the star as a
subscript; the quotations below write it on the line.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule)**, as before: for every theorem whose hypotheses include a named
  `Prop` or a structure, the two checks in the report. **New:** test every named `Prop` on
  degenerate inputs (empty graph, empty sets, one point) and say in the report that it survives.
* **Quotations (standing rule).** Check every quotation and every reading of a formula against
  page images rendered at 200 dpi or more (400 dpi for subscripts, primes, tildes and bars), not
  against the text layer.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "H–O Theorem 1, IV (batch 196)");
  * `README.md`;
  * `LEDGER.md`: the section "Hoehn–Oversteegen 2016 and Krasinkiewicz–Minc 1977 (batch 193)",
    and the count of defective proofs if §7 changes it;
  * `OPEN.md`;
  * `doc/notes/ho16.md`.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 195

* **Delivery.** The first download I received (`aristotle_72`) was the batch-194 download
  unchanged; the second (`aristotle_74`) is current: its `axioms.txt` equals the tarball's.
  The commission and the skeleton were at the top level of the download, not under
  `doc/batches/` as the report and `HO16C.lean`'s header say, and the tarball does not contain
  them. Please save this batch's copies under `doc/batches/` and put them in the tarball.
* **Copies.** The commission and skeleton in the download are byte-identical to what I sent.
* **Audit.** `axioms.txt` has 2942 lines (2824 + 118 for 116 theorems, none removed), with
  `sorryAx` in none; 115 theorems use exactly the three standard axioms, one only `propext`. The
  nine new files contain no `sorry`, `admit` or `axiom` outside comments. Every definition and
  statement matches the skeleton, except the eight recorded removals of hypotheses, which are
  accepted (each changed statement implies the skeleton's).
* **Results.** Everything proved, including the stretch item `ho16_prop19_fold`.
* **Ledger.** HO.13–HO.22 adopted. HO.15 (Proposition 10, second part): classified as a gap,
  statement true, not counted, as you proposed. Your proof through the first part of the
  proposition is a better repair than mine. HO.18: not counted.
* **Your §6 comments** are taken up: Proposition 19 is done in the full fold and restricted to a
  component at the end, as H–O do (§3), which makes the referee's `G′ᵢ` warning moot; genericity
  in `F` is §2; the interface for Theorem 20 is `ho16_lift_stairwell` (§5).

## 1. The plan

After this batch the only open input of `homeomorph_pseudoArc_of_indec_homogeneous` should be
H–O Theorem 15:

1. Library: ordinary points of a fold (§2).
2. **Proposition 19** (pp. 202–209): first in the full fold, with H–O's sets written out
   (`ho16_prop19_full`), then for a connected fold (`ho16_prop19`) (§3).
3. A certificate for a false sentence on p. 208 (§4).
4. **Stretch:** Theorem 20 (forward direction) from a named `Prop` `HOThm15` (Theorem 15), and the
   classification step of batch 193 from `HOThm15` (§5).

If the whole does not fit, do §2 and §3 first.

## 2. Ordinary points of a fold

H–O p. 208: "Since ∂π(P₂) is disjoint from the set Z of branch points and endpoints of G, we have
that the set of branch points and endpoints of F is φ⁻¹(Z)." `IsSimpleFoldOf.isOrdinaryPt_iff`:
if every point of `∂G₂` is ordinary in `G`, then `z ∈ F` is ordinary in `F` iff `π(z)` is ordinary
in `G`. Sketch:
* Off `∂F₂`, `φ` is a local homeomorphism (Lemma 6 (7), and `Fᵢ \ ∂Fᵢ` is open in `F`). Near `z`,
  `Fᵢ` is a fan of segments (`IsPLGraph.exists_fan`), `π` maps each spoke onto a segment, and a
  short segment of `G` from `π(z)` lies in the image of one spoke; so two-segment neighbourhoods
  correspond.
* At `z ∈ ∂F₁ = F₁ ∩ F₂` (over `y ∈ ∂G₁`, ordinary): near `y`, `G` is `[a, y] ∪ [y, b]`; `G₂` is
  one side, say `[a′, y]` (it is a neighbourhood of `y` in neither `G` nor `{y}`), and
  `G₁ = G₂` near `y` (`y ∉ cl(G₁ \ G₂)` by (F3)). So `F₁` and `F₂` near `z` are one spoke each,
  meeting only at `z` (`F₁ ∩ F₂` is finite): `z` is ordinary. Symmetrically at `∂F₃`.

H–O also use, at p. 207, "If z∈∂F₃, then by (S5′) for S, φ(z) is not a branch point of G, so there
is a neighborhood of z in F which is homeomorphic to an open arc J. Note that J\{z} is the union of
two open arcs J₁ and J₂, where J₁⊂int(F₁∪F₂) and J₂⊂int(F₃)": the two spokes of the previous
bullet. Other library lemmas are yours (preimages: `π(foldPre F X) = F ∩ φ⁻¹(π(X))` exists as
`image_foldPre`, and its version with `∩ T⋆` as `image_foldPre_inter`).

## 3. Proposition 19

**Statement** (p. 202): "Let G be a connected graph, and let S⊂G⋆ have a broken stairwell
structure ⟨S₁, ..., S_k; P₁, P₂⟩ of height k with a pit at level i₀⩽k, in which γ_{i₀}≠∅ and
𝓔(P₁)≠∅. Then there exists a simple fold φ: F→G such that F is connected, and φ⋆⁻¹(S) contains a
set S′ with a broken stairwell structure of height k with a pit at level i₀+1 if i₀<k, or simply
a stairwell structure of height k if i₀=k."

**The fold** is batch 195's `ho16_prop19_fold`: `G₁ = π(P₁)`, `G₂ = π(P₂)`,
`G₃ = σ_{π(γ)}(π(S_{i₀}))`, with (19.1)–(19.3); `exists_simpleFold` gives `F₁, F₂, F₃`.

**The sets** (p. 203): "For each i∉{i₀, i₀+1}, define S′ᵢ=φ⋆⁻¹(Sᵢ), α′ᵢ=φ⋆⁻¹(αᵢ), β′ᵢ=φ⋆⁻¹(βᵢ).
For level i₀, define S′_{i₀}=[φ⋆⁻¹(P₁)∩(F₁)⋆]∪[φ⋆⁻¹(P₂)∩(F₂)⋆]∪[φ⋆⁻¹(S_{i₀})∩(F₃)⋆] and
α′_{i₀}=φ⋆⁻¹(α_{i₀}), β′_{i₀}=φ⋆⁻¹(β_{i₀})∩(F₃)⋆. If i₀<k, then further define
S′_{i₀+1}=φ⋆⁻¹(S_{i₀+1}), α′_{i₀+1}=φ⋆⁻¹(α_{i₀+1})∩(F₃)⋆, β′_{i₀+1}=φ⋆⁻¹(β_{i₀+1}),
γ′_{i₀+1}=φ⋆⁻¹(α_{i₀+1})∩(F₁∪F₂)⋆, as well as P′₁=φ⋆⁻¹(P₂)∩(F₁∪F₂)⋆ and
P′₂=φ⋆⁻¹(S_{i₀})∩(F₁∪F₂)⋆."

In the one-`α` encoding (`βᵢ = α (i + 1)`) these are `p19T` and `p19α`: `α′ᵢ = φ⋆⁻¹(αᵢ)` except
`α′_{i₀+1} = φ⋆⁻¹(α_{i₀+1}) ∩ (F₃)⋆`. Then `β′_{i₀} = α′_{i₀+1}` holds by construction (H–O check
it on p. 206), `α′₁ = ∅`, and `α′_{k+1} = ∅`. Note `S′_{i₀+1}` has H–O's formula for `i ≠ i₀`.

**Two theorems.**
1. `ho16_prop19_full`: for **any** simple fold `F` with these `Gᵢ` (connected or not), the sets
   lie in `φ⋆⁻¹(S)`, form a broken stairwell structure in `F⋆` of height `k` with a pit at level
   `i₀ + 1` if `i₀ < k`, and a stairwell structure of height `k` if `i₀ = k`. This is H–O's proof
   on pp. 203–208.
2. `ho16_prop19`: the connected version, by H–O's last paragraph (p. 209): "there is a component K
   of π(P₂)=φ(F₂) such that K meets both π(𝓔(P₁))=∂φ(F₁) and π(γ_{i₀})=∂φ(F₃). By Proposition 7,
   (φ|F₂)⁻¹(K) is contained in a component C of F such that φ(C)=G". Any component `C` with
   `φ(C)` meeting `∂G₁` and `∂G₃` will do (`ho16_prop7` gives one, its first part; H–O's `K`
   gives another): `φ(C) = G` and the pieces `Fᵢ ∩ C` form a connected simple fold. Every set of
   the structure meets `C⋆`: for `i ≠ i₀` because `φ(C) = G`; `S′_{i₀}`, `P′₁`, `P′₂` because each
   contains `φ⋆⁻¹(γ) ∩ (∂F₃)⋆` and `C` meets `∂F₃`. H–O: "clearly C meets ∂F₃ by Lemma 6 (6)",
   and this is right (the referee of this commission): `φ(C) = G`, `G \ G₃ = G₁ \ G₂ ≠ ∅` (else
   `∂G₃ = ∅`) and `G \ G₁ = G₃ \ G₂ ≠ ∅` (else `∂G₁ = ∅`), so `C` meets both `F₁ \ F₂` and
   `F₃ \ ∂F₃`, and the separation of Lemma 6 (6) (in `ho16_lemma6`) forces `C ∩ ∂F₃ ≠ ∅`.
   Restrict with
   `ho16_obs16_comp` / `ho16_obs13_comp` (with `G := F`, relative to `C`), and note
   `foldPre F S ∩ C⋆ = foldPre C S` when `C ⊆ F`. Working in the full fold and restricting at the
   end (H–O's order) means that (19.1)–(19.3) are only ever used for the full `Gᵢ`.

**Proof of `ho16_prop19_full`** (H–O pp. 203–208; my reading, step by step):
* **Straightness and end sets, `i ≠ i₀`** (19.4): `∂π(Sᵢ) = π(αᵢ) ∪ π(βᵢ)` misses
  `∂G₂ = π(𝓔(P₁)) ∪ π(γ)` by (S5′), so Lemma 18 (1), first alternative, gives `S′ᵢ` straight with
  `𝓔(S′ᵢ) = φ⋆⁻¹(𝓔(Sᵢ))`, which misses `(∂F₂)⋆`.
* **Level `i₀`** ((19.5), (19.6)): the three pieces lie over `F₁`, `F₂`, `F₃ ∩ φ⁻¹(π(S_{i₀}))`
  (`φ(F₁) = π(P₁)`, `φ(F₂) = π(P₂)`, `φ(F₃) = σ_{π(γ)}(π(S_{i₀})) ⊇ π(S_{i₀})`). `π` is injective
  on `S′_{i₀}` because over `∂F₁` the pieces from `P₁` and `P₂` coincide
  ("φ⋆⁻¹(P₁)∩(∂F₁)⋆=φ⋆⁻¹(𝓔(P₁))∩(∂F₁)⋆=φ⋆⁻¹(P₂)∩(∂F₁)⋆"; `𝓔(P₁) ⊆ 𝓔(P₂) ⊆ P₂` and `π` is
  injective on `P₂`), and likewise over `∂F₃` with `γ ⊆ 𝓔(P₂) ∩ 𝓔(S_{i₀})`. `π(S′_{i₀})` is
  `F₁ ∪ F₂ ∪ (F₃ ∩ φ⁻¹(π(S_{i₀})))`, a PL graph (§2.3 of batch 195). Then
  `F₁ ∪ F₂ ⊆ int π(S′_{i₀})` and `𝓔(S′_{i₀}) ⊆ int(F₃)⋆` "because π(S_{i₀}) agrees with
  φ(F₃)=σ_{π(γ_{i₀})}(π(S_{i₀})) near π(γ_{i₀}) in G" (`ho16_obs9_char`), whence (19.6)
  `𝓔(S′_{i₀}) = φ⋆⁻¹(𝓔(S_{i₀})) ∩ int(F₃)⋆` and (19.7).
* **`P′₁`** ((19.8), `𝓔(P′₁) = φ⋆⁻¹(γ)`): Lemma 18 (2) with `S = P₂` (second alternative of `hV` in
  `ho16_lemma18` with `V = univ`, since `G₂ = π(P₂)`), and H–O's three "straightforward
  observations": `φ⁻¹(π(𝓔(P₁)))` meets `F₁ ∪ F₂` exactly in `∂F₁` (the points of `F₁` and of `F₂`
  over `∂G₁ = φ(F₁ ∩ F₂)` lie in `F₁ ∩ F₂`); `φ⁻¹(π(γ)) ⊆ F₁ ∪ F₂` (a point of `F₃` over `∂G₃` lies
  in `F₂ ∩ F₃`) and misses `∂F₁`; `P′₁ ∩ (∂F₃)⋆ = φ⋆⁻¹(γ) ∩ (∂F₃)⋆`. H–O print the last one as
  "P′₁∩(∂F₃)⋆=φ⋆⁻¹(γ_{i₀}) by (19.2)", which is false whenever `γ ≠ ∅` (a misprint; §7.1): `φ⋆⁻¹(γ)`
  also contains the points over the `F₁`-copies of `π(γ)`, which lie in `F₁ \ F₂`, outside `(∂F₃)⋆`.
  Their next clause uses only `⊆`. Those points are end points of `P′₁` too (Figure 11 shows both
  kinds).
* **`P′₂`** ((19.9), `𝓔(P′₂) = 𝓔(P′₁) ∪ γ′_{i₀+1}`): Lemma 18 (2) with `S = S_{i₀}`; the
  hypothesis holds because `∂G₂ ∩ ∂π(S_{i₀}) = π(γ)` and (S3′) gives the `W`. Simplify with
  (S6′) (`φ⁻¹(π(α_{i₀})) ∩ (F₁ ∪ F₂) = ∅`) and `φ⁻¹(π(β_{i₀})) ∩ ∂F₁ = ∅`.
* **(S2)/(S2′)** (p. 206): as printed; `α′_{i₀+1} ∩ γ′_{i₀+1} ⊆ (∂F₃)⋆` is empty by (19.7);
  `α′_{i₀} = φ⋆⁻¹(α_{i₀}) ⊆ (F₃)⋆` by (S6′). Finiteness: a point of `G` has at most three
  preimages in `F`.
* **(S3)/(S3′)** (p. 207): off `∂F₂`, `φ` is a local homeomorphism and the neighbourhoods of
  (S3′) for `S` pull back; at level `i₀`, through `(φ|F₃)⁻¹`; for `P′₁`, `P′₂` at
  `z ∈ π(𝓔(P′₁))`: off `∂F₃` as before, at `z ∈ ∂F₃` by the two spokes of §2.
* **(S4)/(S4′)** (pp. 207–208): for a component `C` of `F \ π(S′ᵢ)`, `φ(C)` lies in a component
  `C̃` of `G \ π(Sᵢ)`, and `φ(∂C) ⊆ ∂C̃ ∩ φ(cl C)`; consistency of `π(Sᵢ)` puts `∂C̃` inside one of
  `π(αᵢ)`, `π(βᵢ)` (and `π(γ)` at level `i₀`). At level `i₀`: `C̄ ⊆ int(F₃)` by (19.5), and
  `φ⁻¹(π(γ)) ∩ F₃ = ∂F₃`. At level `i₀ + 1`: Proposition 10, second part (`ho16_prop10`), then
  Lemma 6 (6): `C ⊆ F₁ ∪ F₂` or `C ⊆ F₃`. For `P′₂`: Lemma 6 (6) again, and **the step of §4
  below needs a different argument**: if `∂D = ∅` there is nothing to show; otherwise a point
  `z ∈ ∂D` has `φ(z) ∈ ∂D̃ ∩ π(P₁ ∪ P₂)`, which misses `π(α_{i₀})` by (S6′), so `∂D̃` meets
  `π(β_{i₀}) ∪ π(γ)` and consistency puts `∂D̃` inside one of them.
* **(S5)/(S5′)** (p. 208): by §2 (`∂G₂ = π(𝓔(P₁)) ∪ π(γ)` consists of ordinary points by (S5′)
  for `S`); preimages of pairwise disjoint sets are pairwise disjoint; `α′_{i₀+1}` and
  `γ′_{i₀+1}` are disjoint as above. (H–O's new list on p. 208 has `π(γ′_{i₀+1})` before
  `π(𝓔(P′₁))`, the reverse of Definition 16's order; in Lean the order is fixed by
  `IsBrokenStairwellStr`, and pairwise disjointness does not depend on it.)
* **(S6′)** (p. 208): `α′_{i₀+1} ⊆ int(F₃)⋆` by (19.5).

## 4. A false sentence on p. 208

H–O p. 208 (the (S4′) argument for `P′₂`): "If D⊂F₁∪F₂, then since π(P′₂)=φ⁻¹(π(S_{i₀}))∩(F₁∪F₂),
we have that φ(D) is contained in a component D̃ of G\π(S_{i₀}). Moreover, φ(D)⊂π(P₁∪P₂), so
∂D̃∩π(α_{i₀})=∅ by (S6′) for S. This means that either ∂D̃⊂π(β_{i₀}) or ∂D̃⊂π(γ_{i₀})."

**My reading: the middle sentence is false in a legitimate configuration**, and with it the
next one; the conclusion of the step ("it follows that ∂D⊂π(𝓔(P′₁)) or ∂D⊂π(γ′_{i₀+1})") is
right, by the case split of §3. Example (`k = 3`, `i₀ = 2`, `G = [0, 10]`, `5 < a < 6`):
* `S₁ = [4, 10] × {0.1}`; `S₂` the segment from `(4, 0.1)` to `(6, 0.5)`; `S₃ = [0, 10] × {0.9}`;
* `α₂ = {(4, 0.1)}` (`= β₁`), `γ₂ = {(6, 0.5)}`, all other `αᵢ` empty (so `β₂ = α₃ = ∅`);
* `P₂ = [1, 2] × {0.3}` ∪ the segment from `(a, 0.3)` to `(6, 0.5)`;
* `P₁` = a path over `[1, 2]` from `(1, 0.3)` to `(2, 0.3)` with interior heights `≠ 0.3` (say
  through `(1.5, 0.2)`) ∪ the segment from `(a, 0.3)` to `(10, 0.2)`;
* so `π(P₁) = [1, 2] ∪ [a, 10]`, `π(P₂) = [1, 2] ∪ [a, 6]`, `π(S₂) = [4, 6]`,
  `𝓔(P₁) = {(1, 0.3), (2, 0.3), (a, 0.3)}`, `𝓔(P₂) = 𝓔(P₁) ∪ γ₂`.

I checked (S1′)–(S6′) by hand, and so did the referee: (S3′) near `4`, `{1, 2, a}`, `6`; (S4′): the
complements are `[0, 4)` for `π(S₁) = [4, 10]`, `[0, 4)`, `(6, 10]` for `π(S₂)`, `[0, 1)`, `(2, a)`,
`(6, 10]` for `π(P₂)`, each with a frontier inside one of the given sets; (S5′): `{4}`, `∅`, `{1, 2,
a}`, `{6}` are pairwise disjoint sets of ordinary points; (S6′): `4 ∉ π(P₁ ∪ P₂)`. Now `x = 1.5 ∈
π(P₂) \ π(S₂)`, its component in `G \ π(S₂)` is `D̃ = [0, 4)`, and `∂D̃ = {4} = π(α₂)`. In any fold
of Proposition 19 for this `S`
(`G₁ = [1, 2] ∪ [a, 10]`, `G₂ = [1, 2] ∪ [a, 6]`, `G₃ = σ_{{6}}([4, 6]) = [0, 6]`), the copies of
`[1, 2]` in `F₁` and `F₂`, glued over `1` and `2`, form a circle that is a component `D` of `F`,
lies in `F₁ ∪ F₂`, misses `π(P′₂)`, and has `φ(D) = [1, 2] ⊆ D̃`. So H–O's `D̃` has
`∂D̃ ∩ π(α_{i₀}) ≠ ∅`, and `∂D̃` lies in neither `π(β_{i₀}) = ∅` nor `π(γ) = {6}`; the conclusion
holds because `∂D = ∅`.

Prove the certificate `ho16_p208_false` (the `G`-level statement: a point of `π(P₂) \ π(S₂)` whose
component in `G \ π(S₂)` has a frontier point in `π(α₂)`). In general, every `x ∈ π(P₂) \ π(S_{i₀})`
is `φ(z)` for the `F₂`-copy `z`, whose component `D` in `F \ π(P′₂)` lies in `F₁ ∪ F₂` (it cannot
cross `∂F₃ ⊆ π(P′₂)`; Lemma 6 (6)), so the certificate refutes H–O's sentence for every fold. If
you find an error in my example, refute the certificate and say so.

## 5. Stretch: Theorem 20 from Theorem 15

**Theorem 15** (p. 194): "Let G be a graph. For any set M⊆G×(0,1) which separates G×{0} from
G×{1} in G⋆, and any open set U⊆G×(0,1) with M⊆U, there exists a set S⊂U with a stairwell
structure of odd height." `HOThm15` states it for **connected** PL graphs in any real normed
space (`U` open in `E × ℝ`; `S ⊆ U ∩ G × (0, 1)`), as a named `Prop`; its proof is a later batch.
Connectedness also makes `G` nonempty, which H–O's graphs are (p. 183: "the union of finitely many
arcs"): the referee of this commission found that without it the formal statement is refutable
(`G = ∅`, `M = ∅`: `SeparatesIn` holds with empty open sets, and no stairwell structure lives in
`∅`). Theorem 20 uses Theorem 15 only for connected `G`, after its reduction.

**Theorem 20** (p. 209), forward direction, is batch 193's `HOThm20`. Prove
`ho16_theorem20_of_thm15 : HOThm15 → HOThm20` and the corollary
`homeomorph_pseudoArc_of_indec_homogeneous_of_thm15`. H–O's proof (pp. 209–210), restructured:
1. **Reduction to connected `G`** ("By treating the components of G one at a time, and because the
   inverse image of any component under f is a hereditarily indecomposable closed and open subset
   of X, we may assume without loss of generality that G is connected"): `G` has finitely many
   components, each clopen; `M ∩ C⋆` separates `C × {0}` from `C × {1}` in `C⋆` (same open sets);
   apply the connected case on each `f⁻¹(C)` (a clopen, possibly empty, hereditarily
   indecomposable compactum) and glue.
2. **`ho16_lift_stairwell`**, by strong induction on a measure, quantified over `E : Type` (the
   induction passes from `E` to `E × ℝ`): for a stairwell of odd height `k` on connected `G`,
   every `f` has, for every `ε`, an `h : X → S` with `dist (f x) (h x).1 < ε`. Prove alongside it
   the same statement for broken structures of odd height (pit at any level).
   * Height 1: `h = θ ∘ f` with `θ` the section of `ho16_height_one`; exact.
   * Height `k ≥ 3`: `ho16_prop17` gives a broken structure of height `k − 2`, pit at level 1.
   * Broken: if `γ = ∅` or `𝓔(P₁) = ∅`, the remarks of p. 201 (`ho16_rem17_gamma`,
     `ho16_rem17_P1`) give a stairwell structure on a subset of `S` (height `k`, or 1). Otherwise
     `ho16_prop19` gives a connected fold `F` and `S′ ⊆ foldPre F S`; `ho16_theorem8` gives
     `g : X → F` with `dist (f x) (g x).1 < ε/2`; the induction hypothesis in `E × ℝ`, for `F`,
     `S′`, `g` and `ε/2`, gives `h′ : X → S′`; put `h = phiStar ∘ h′`, which maps into `S`, and
     use `dist p.1 q.1 ≤ dist p q` on `E × ℝ`.
   * A measure that decreases at every step: `(k + 1)²` for a stairwell of height `k`, and
     `(k + 1)² + k + 1 − i₀` for a broken structure of height `k` with pit at `i₀` (any measure
     will do). Oddness is preserved and excludes `k = 2`, where Proposition 17 does not apply.
3. **Assembly**: for connected `G`, `HOThm15` gives `S ⊆ U` with a stairwell of odd height;
   `ho16_lift_stairwell` gives `h` into `S ⊆ U ∩ G⋆`. (Steps 1 and 3 together: `HOThm15` is
   applied to each component.) H–O compose the folds explicitly
   ("h=(φ₁)⋆∘…∘(φₙ)⋆∘θ∘gₙ"); the recursion above does the same without indexing them.

## 6. Non-vacuity

* `ho16_prop19_full`, `ho16_prop19` with `i₀ = k`: batch 195's `prop19_fold_example` (height 1,
  pit at level 1) and the fold `exists_simpleFold` gives for it.
* With `i₀ < k`: the structure of §4 (height 3, pit at level 2) meets every hypothesis.
* `ho16_lift_stairwell`: a non-vacuous instance is `G = [0, 1]`, `S = G × {½}`, `X` a point.
* `ho16_theorem20_of_thm15`: `HOThm15` is its hypothesis. Check it on degenerate inputs (empty
  `G` is excluded by connectedness; a segment `G` with `M = G × {½}` should be an instance) and
  say that the proof uses Propositions 17 and 19 and Theorem 8, not a shortcut through
  `HOThm15`.

## 7. Places to check (ledger)

New items from HO.23 on, in the same section:
1. **pp. 203–206, straightness and end sets.** Unargued and to be supplied: "clearly each of
   φ⋆⁻¹(P₁)∩(F₁)⋆, φ⋆⁻¹(P₂)∩(F₂)⋆, and φ⋆⁻¹(S_{i₀})∩(F₃)⋆ is straight" (regularity of
   `F₃ ∩ φ⁻¹(π(S_{i₀}))`); the "straightforward observations" of pp. 205–206. Misprints:
   "S′_{i₀}∩(F₃)⋆=φ⁻¹(S_{i₀})∩(F₃)⋆" (p. 205, and again on p. 207) and
   "φ⋆⁻¹(α_{i₀})∩(F₃)⋆=φ⁻¹(α_{i₀})=α′_{i₀}" (p. 206), `φ⁻¹` for `φ⋆⁻¹` (400 dpi); and
   "P′₁∩(∂F₃)⋆=φ⋆⁻¹(γ_{i₀}) by (19.2)" (p. 205), false as printed whenever `γ ≠ ∅`, for
   `φ⋆⁻¹(γ_{i₀}) ∩ (∂F₃)⋆` (the next clause uses only `⊆`): a misprint, not a defect of the
   proof.
2. **p. 207, (S3).** "It is then straightforward to see from property (S3′) for S and from the
   definition of S′ᵢ that there exists a neighborhood V": unargued, supplied. Slips on p. 207:
   "neighborhood of β_{i₀}=α_{i₀+1} in G" and "neighborhood of β′_{i₀}=α′_{i₀+1}" for `π(β_{i₀})`,
   `π(β′_{i₀})`; "P′₂=φ⁻¹(π(S_{i₀}))∩(F₁∪F₂)" for `π(P′₂)`.
3. **p. 208, (S4′) for `P′₂`.** The sentences of §4. My proposal, which the referee shares: a
   false inference with a missing case inside the proof of a true proposition (certificate
   `ho16_p208_false`); **count it as a defective proof** (the seventeenth), as the ledger counts
   Moore 1925 Theorem 11 ("B" asserted to be an arc) and Jones 1955 Theorem 1, and unlike the
   gaps HO.15 and the Hagopian `ε₁` (nothing printed false) and the misprints of item 1 (a formula
   misprinted, the argument intact). Annotate: the sentence fails only for components `D` of `F`
   (`∂D = ∅`), which the restriction of p. 209 discards (they miss `∂F₃ ⊆ π(P′₂)`, while `C`
   meets it); when `∂D ≠ ∅` it is true, by (S6′) together with the consistency of `π(S_{i₀})`;
   the proposition and the paragraph's conclusion are unaffected. Give your view; if you would
   not count it, argue it.
4. **p. 208, (S5′).** "the set of branch points and endpoints of F is φ⁻¹(Z)" and "It is then
   trivial to see …": unargued, supplied by §2.
5. **p. 209.** The existence of `K`: unargued; H–O's reason, consistent complement, works (group
   the components of `π(P₂)` and of `G \ π(P₂)` by the frontier set they meet). "clearly C meets
   ∂F₃ by Lemma 6 (6)": right, as §3 explains; unargued.
6. **(Stretch) pp. 209–210, Theorem 20.** The reduction to connected `G` (unargued details); "In
   this way, after a sequence of at most (k₀−1)+(k₀−3)+...+1 simple folds": check the count (each
   pass from height `k` to `k − 2` uses at most `k − 2` folds, and the printed sum mixes parities
   for odd `k₀`; an upper bound either way; the referee counts at most `((k₀ − 1)/2)²`); "We
   further assume that the numbers εᵢ are chosen small enough so that h(X)⊂U" (already recorded
   as unneeded); Step 2's "if γ_{i₀}=∅, then in fact S has a stairwell structure of height k−2"
   (already recorded: only `S₁ ∪ … ∪ S_{k−2} ⊆ S` has one).

## 8. Order

§2, then §3 (`ho16_prop19_full`, then `ho16_prop19`); §4 any time; §5 last.

## 9. Deliverables

1. **The items of §2–§5.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch196.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. **`LEDGER.md`:** §7.
3. **Notes:** `doc/notes/ho16.md`: the proof of Proposition 19 as formalized, and (if §5 is done)
   the induction of Theorem 20, in a few paragraphs.
4. **Publish the changes, as in batch 195.** At the end of the run:
   * create `doc/batches/batch196-files.tar.gz` with every file added or changed in this run,
     including `doc/batches/COMMISSION-batch196.md` and `doc/batches/skeletons/HO16D.lean`;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch196-MANIFEST.txt`;
   * publish both, as you published the report.
5. **The report.** Its first line names the commission it read. It covers:
   * the items in order;
   * the non-vacuity notes;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of `homeomorph_pseudoArc_of_indec_homogeneous` (and of the `_of_thm15`
     version, if §5 is done);
   * comments on the plan for Theorem 15 (pp. 194–198): what the library lacks, and the route of
     my design notes (a piecewise linear approximation of a sign function `u = d(·, R₀′) −
     d(·, R₁′)` on `G⋆` with `R₀′`, `R₁′` the two sides of the separator outside `U`, its zero set
     inside `U` in general position, and the sheets of a stairwell read off between consecutive
     points of a finite set `Z′`): whether you see an obstruction to it, and what you would
     prove first.
