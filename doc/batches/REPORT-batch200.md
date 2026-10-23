Commission read: `doc/batches/COMMISSION-batch200.md` ("Commission: batch 200 — Part G, III: Bing–Jones's homeomorphism (pp. 188–189), Theorems 8 and 9").

# Report, batch 200

## 0. Summary, omissions, shape changes

**Every declaration of the skeleton is proved, with the skeleton's statement**, including the main
item `zigzag_homeomorph`, Theorem 8 and its corollary, and Theorem 9 (`bj9_base`, `bj_theorem9`).
Nothing is commented out and no new file contains `sorry`, `admit` or `axiom`. The skeleton is split
under `HPC/BJ59/` (fourteen files, collected by `HPC/BJ59/BJ59C.lean`, imported at the end of
`HPC.lean`); a script check confirms that each of the 13 declarations of the skeleton occurs in the
library with the skeleton's text up to `:=`. The 86 new theorems are audited in
`doc/batches/audits/axioms-batch200.txt`; none depends on `sorryAx`.

```
STATUS: starImage defined; tested on degenerate inputs
STATUS: zigzag_homeomorph proved
STATUS: zigzag_fibre proved
STATUS: exists_privatePoint_interior proved
STATUS: exists_privatePoint_shrink proved
STATUS: bj_step1b proved
STATUS: bj_theorem8 proved (continuous arcs, n ≥ 3, as in the skeleton)
STATUS: bj_theorem8_cor proved
STATUS: bj9_base proved
STATUS: bj_theorem9 proved
STATUS: dp22_theorem61_iff proved (from BJThm10, BJPlaneExample)
STATUS: bj_theorem7_proof_n3 proved
STATUS: nonvac_zigzag proved
```

**Omissions.**
* Non-vacuity of `bj_theorem8` and `bj_theorem8_cor` (commission §8): no witness, conditional or
  not, is given. A continuous snake-like arc of pseudo-arcs is known here only under
  `BJPlaneExample`; not attempted. Recorded in `OPEN.md`.
* Quotation checks (standing rule): pp. 178–181 and the quotation of p. 189 were checked on page
  images at 200 dpi; pp. 182 and 188 were not re-rendered in this batch, and no 400-dpi crops were
  made (see §8).

**Shape changes.** None to the skeleton's statements. Two textual points:
* `bj_step1b` carries its own binders `{X : Type*} [MetricSpace X]`, as in the skeleton (the file's
  section variable is not used by it).
* The skeleton's single file is split; `HPC/BJ59/BJ59C.lean` is a collector module with a
  docstring mapping each declaration to its file.

**Unused hypotheses.** The unused-variables linter reports none in the new files; every hypothesis of
the skeleton's statements is used by its proof. As the commission notes, compactness of `K` is not
used in `exists_privatePoint_shrink` beyond connectedness and non-degeneracy (kept as stated).

**Sources.** The eight sources of commission §0 are under `doc/sources/` (`bing-jones1959.pdf`,
`cook1967.pdf`, `domokos-prajs2022.pdf`, `hagopian1984.pdf`, `hoehn-oversteegen2016.pdf`,
`jones1975.pdf`, `lelek1979.pdf`, `oversteegen-tymchatyn1982.pdf`). PDFs are excluded from git by
`.gitignore`; they are in the tarball.

## 1. §2: the homeomorphism of pp. 188–189 (`HPC/BJ59/Zigzag.lean`)

`starImage D E H p` is `H_i d(p, i)`. `zigzag_homeomorph` follows Bing–Jones's five steps:
nestedness from B and B′ (`starImage_succ_subset`, `starImage_antitone`), smallness
(`starImage_dist_le`, diameter `≤ 2ε_i`), `h p` the one point of `Q` in every closure, continuity,
injectivity (chains `E_i` in Bing–Jones's sense: `IsBJChain.adjacent_of_closure`; the bound
`4ε_{i−1}`, BJ.14), and surjectivity by density and compactness. `zigzag_fibre`: `h p` lies in the
closure of one link `E_{H j}` with `p ∈ D_j` (`mem_closure_starImage`), and `hA` gives points of the
fibre within `ε_i`; the fibre is closed.

## 2. §3: private points, Step 1(b) (`Private.lean`, `Step1b.lean`)

* `exists_privatePoint_interior`: as in the commission (the two closed pieces of `P`).
* `exists_privatePoint_shrink`: the commission's proof (distinct points `z_i` by
  `exists_injective_choice`, a common radius `exists_pos_forall_le`, closed balls removed from the
  neighbouring links).
* `bj_step1b`: a neighbourhood form of the commission's compactness argument, without sequences:
  `exists_nhd_step1b` (about each `c` an open `N` such that every point over `N` lies in a link
  meeting every fibre over `N`; upper semicontinuity from `f` closed, lower from `f` open), a Lebesgue
  number `2δ`, the end-link case analysis, and `meets_all_of_meets_ends`.

## 3. §4: Theorem 8 and its corollary (`Thm8Lib.lean`, `Thm8.lean`, `Thm8Cor.lean`)

* `bj_theorem8_ends`: the commission's repair, steps 1–7, with two changes of route: the intervals
  `I_a` are the complements of the images of closed "bad" sets, and a uniform grid of `T` segments
  under a Lebesgue number of `{I_a}` replaces the minimal subcover; the cover `U_0, …, U_{T−1}` comes
  from Theorem 4 in the located form `bj_cut` at the `T − 1` cuts. `U_A`, `U_B` from
  `exists_deep_radius`, `exists_deep_sets`.
* `bj_theorem8_le` (the general case `r ≤ s`, folding along the walk, `isBJChain_foldChain`) and
  `bj_theorem8` (reversing `D` when `s < r`).
* `bj_theorem8_cor`: `G` from Theorem 8 for the pattern `4i + c ↦ H₁(i)`; `ε` below a Lebesgue number
  of `G` and below half the uniform spread `κ` of the fibres (`exists_fibre_spread`); `R(f) = ⌊a/4⌋`;
  the three consecutive links by `walk_core`, `walk_any`, `walk_any'` (a walk with steps of at most
  one from `≤ b + 1` to `≥ b + 4` spends three consecutive steps in `[b, b + 3]`); `ℓ = 1` by the
  spread.

## 4. §5: Theorem 9 (`Thm9Class.lean`, `Thm9D.lean`, `Thm9E.lean`, `Thm9Base.lean`, `Thm9.lean`)

1. **First simplification.** `exists_consolidation` (from `chain_of_classes`: links sorted into
   classes with meeting links in adjacent classes give a chain in Bing–Jones's sense); private points
   of `D″` from the hypothesis `hHo` through `closure_biUnion_links`; `E` shrunk with
   `exists_privatePoint_shrink`.
2. **Second simplification.** `bj9_Dside` (the chain `D′` of `4m − 3` links; `Allowed j i` lists the
   links of `D` a point of `P ∩ d′_j` may lie in) and `bj9_Eside` (the chain `E′`; for `Allowed j i`,
   `closure e′_j ⊆ e_i`). The separation for `E′` is argued through a Lebesgue number `λ` of `E` on
   `Q`: `F` has mesh `λ/5`, and two links joined through at most two further links lie in the ball of
   radius `λ` about a point of `Q`, inside one link of `E`; this replaces the commission's convergent
   subsequences. `bj9_core` combines them and shrinks both chains to private points; `bj9_base`
   adds step 1.
3. **Alternation.** `BJ9Stage` (a matched pair: same number of links, chains in Bing–Jones's sense,
   covering, private points); `bj9_half` (a fine chain on one side under a Lebesgue number of the
   old chain; the refinement map `π` is a chain map, onto by the private points; Theorem 7 with
   pattern `π` on the other side; both shrunk); `bj9_step` (two half-steps with the roles exchanged,
   both meshes `< δ`, refinement map `π₁ ∘ π₂`).
4. **Assembly.** The stages are iterated with `δ = (1/2)^k`; `zigzag_homeomorph` is applied from
   stage 1 on, with `H_i` the identity and `K_i = π`; then `h p ∈ closure e¹_j` with `p ∈ d¹_j`,
   `d¹_j ⊆ d⁰_{π j}`, `e¹_j ⊆ e⁰_{π j}`, and the last clause of `bj9_base` gives
   `h p ∈ e_{H(i)}`. Composants are not used.

## 5. §6: two small items (`DP61.lean`, `Private.lean`)

* `IsAtomicCircPAMap.comp_homeomorph` (the transport lemma: fibres, openness, atomicity);
  `exists_atomic_of_plane_isCircleOfPA` (the argument of `nonvac_atomic` for a given plane circle of
  pseudo-arcs); `dp22_theorem61_iff`: "⇐" by `isCircleOfPA_of_atomic`, "⇒" by
  `homeomorph_of_isCircleOfPA` and transport.
* `bj_theorem7_proof_n3`: the commission's proof (the two cases `P·(d₃ − d₂)` empty or not).

## 6. Non-vacuity (`NonVac200.lean`, `NonVac200b.lean`)

* `starImage`: `starImage_eq_empty_of_notMem` (`p` in no link), `starImage_zero` (`n = 0`),
  `starImage_self_id` (`D = E`, `H = id`: the union of the links through `p`).
* `zigzag_homeomorph`: `nonvac_zigzag` (verbatim; `N i = 2 · 3^i`, links the intervals of radius
  `3/(4 N i)` about `k / N i`, `K i k = ⌊(k + 1)/3⌋`) and `nonvac_zigzag_homeomorph` (the lemma
  applied, with `zigzag_fibre` for `φ = ψ = id`: the homeomorphism is the identity).
* `exists_privatePoint_interior`, `exists_privatePoint_shrink`: a plane pseudo-arc with the chain of
  `nonvac_bj_chains` (`nonvac_privatePoint_interior`, `nonvac_privatePoint_shrink`).
* `bj_step1b`: `[0, 1]`, the identity, the chain `nvChain 0` (`nonvac_step1b`).
* `bj9_base`, `bj_theorem9`: a plane pseudo-arc, `P = Q`, `D = E` shrunk to private points, `H = id`
  (`nonvac_bj9`, hypotheses and both conclusions); the one-link chain (`oneChain`, `nonvac_bj9_one`).
* `bj_theorem7_proof_n3`: the chain of `nonvac_bj_chains` consolidated to three links, `V = univ`,
  `U = D.link 2` (`nonvac_bj_theorem7_proof_n3`).
* `dp22_theorem61_iff`: under `BJThm10` and `BJPlaneExample`, the plane circle `C`
  (`nonvac_dp22_theorem61`).
* New definitions on small inputs: `allowed_small` (`Allowed`), `nonvac_bj9Stage` (`BJ9Stage`),
  `oneChain`.
* `bj_theorem8`, `bj_theorem8_cor`: none (§0).

## 7. Shape and route notes for the next batch

* `bj_theorem9` needs `D`, `E` to be chains in Bing–Jones's sense (as the skeleton states); in
  Theorem 10, Step 2(i), the chains in hand are such chains by Theorems 7 and 8.
* `bj_theorem8_cor` is for the arc as the whole space; the transfer to sub-arcs
  `Q(i/k, (i+1)/k)` of a larger space is not done.

## 8. Ledger

New section "Bing–Jones §§4–6 (batch 200)" of `LEDGER.md`, with the convention ("printed X, read Y")
stated once at its head. Entries BJ.21–BJ.29 cover the commission's items 1–9:
BJ.21 (Theorem 8, `U_A`, `U_B`; printed `d₂`, read `d_n`), BJ.22 (the cover from Theorem 4), BJ.23
(the chain `E`; repaired), BJ.24 (the general case; folding), BJ.25 (the corollary; printed
"4i+1, …, 4i+4", read `4i−3, …, 4i`), BJ.26 (Step 1(b)), BJ.27 (pp. 188–189: "Of course", the slip
`H_i(d_k^{i+1})`, `4/2^i`), BJ.28 (Theorem 9: BJ.8, BJ.9 confirmed on the page images; the choice of
`F`; private points of interior links; deleting points from `e₂`, `e_{n−1}`; composants not needed),
BJ.29 (the certificate for BJ.19 (e), verified). Quotations: pp. 178, 179, 180, 181 and 189 checked on
200-dpi page images (agreeing with the commission's quotations); pp. 182 and 188 not re-rendered.

Which I would count: **BJ.19** as a defective proof, now that its certificate is verified (BJ.29).
None of the new items: BJ.23 and BJ.28 (b) are defective constructions repaired in place (as BJ.4).
The counts are left unchanged (twenty-four false printed statements, seventeen defective proofs).

## 9. Axioms

`doc/batches/audits/axioms-batch200.txt` (86 lines, one per new theorem; added to `Axioms.lean` as
the group "Bing–Jones 1959, III (batch 200)"): 82 depend on `[propext, Classical.choice, Quot.sound]`,
1 on `[propext, Quot.sound]` (`nvK_chainMap`), 1 on `[propext]` (`allowed_small`), 2 on none
(`IsChainMap.comp'`, `meets_of_private`). `sorryAx`: none. `axioms.txt` is regenerated (3710 lines;
the first 3624 are unchanged from batch 199). The theorems of the skeleton:

| theorem | axioms |
| --- | --- |
| `zigzag_homeomorph`, `zigzag_fibre` | `propext`, `Classical.choice`, `Quot.sound` |
| `exists_privatePoint_interior`, `exists_privatePoint_shrink` | the same |
| `bj_step1b`, `bj_theorem8`, `bj_theorem8_cor` | the same |
| `bj9_base`, `bj_theorem9` | the same |
| `dp22_theorem61_iff`, `bj_theorem7_proof_n3`, `nonvac_zigzag` | the same |

## 10. What remains for Theorem 10

Available now: Step 1(b) (`bj_step1b`), Theorems 5 (repaired), 6, 7, 8, 9, the corollary to
Theorem 8, and the homeomorphism of pp. 188–189 with Condition A (`zigzag_homeomorph`,
`zigzag_fibre`). Remaining:
* Steps 2 and 3 of the proof (pp. 182–188): the chains `D_i`, `E_i` of Theorem 10 and the chain maps
  `H_i`, `K_i`, with Conditions A, B, B′ and C;
* the transfer of the corollary to Theorem 8 to the sub-arcs `Q(i/k, (i+1)/k)` of a larger space;
* the extension of the given homeomorphisms of the end fibres (Condition C) through Theorem 9;
* the induction and the assembly into `BJThm10`;
* then the plane example (§7 of the paper, `BJPlaneExample`).
