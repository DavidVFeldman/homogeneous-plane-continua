Commission read: `doc/batches/COMMISSION-batch151.md` (batch 151, Part F, Jones 1949 III: crossing continua; Moore 1922 Theorem 4; complementary domains).

# Report, batch 151

**Outcome.**

| item | outcome |
|---|---|
| A: `sector_theorem` | **proved** (shape chosen, recorded at the statement and in §1) |
| A: `sector_cyclic_order` (the cyclic order) | **proved** |
| B: `moore22_sufficiency_local` | **proved** (statement as in the skeleton; `hRc` unused) |
| C: `moore22_theorem4` (open in batch 150), both directions | **proved** (statement verbatim) |
| D: `isConnected_frontier_complDomain` | **proved** (statement as in the skeleton) |
| D: `mooreSimplyConnected_complDomain` | **proved** (statement as in the skeleton; `hx` unused) |
| E: `whyburn39_6_22_sec14` | **proved** (statement as in the skeleton) |

Nothing is left open in this batch.

**Build and axioms.**
* `lake build HPC` succeeds with `import HPC.Jones.Jones49C` at the end of `HPC.lean`.
* No new file contains `sorry` (the word occurs only in the skeleton's module docstring). The only
  warnings in the new files are the two unused hypotheses `hRc` and `hx`, which are kept because the
  statements are the skeleton's.
* Every theorem of the five new files (163 theorems) uses exactly `propext`, `Classical.choice` and
  `Quot.sound`. The audit is `doc/batches/audits/axioms-batch151.txt`.
* `axioms.txt` is regenerated from `Axioms.lean` (1174 lines, one per `#print axioms`), with `sorryAx` in no line and only standard axioms. The previous version is
  kept as `doc/batches/audits/axioms-before-batch151.txt` (1155 lines).
* `Axioms.lean` has the new group *Crossing continua; Moore 1922 Theorem 4; complementary domains
  (batch 151)* (21 names), before the group of `*_false` helper names. The batch-150 comment calling
  Theorem 4 open is updated in place.

**Uploads.** The commission is at `doc/batches/COMMISSION-batch151.md`; the skeleton is kept verbatim
at `doc/batches/skeletons/Jones49C-batch151.lean`.

**Files.**
* `HPC/Jones/Jones49CStrip.lean`: crossing continua of a strip (the universal cover of the square
  annulus); sides of a crossing continuum (`GoodSide`, `lc_disjoint_rc`, `no_cross_join`).
* `HPC/Jones/Jones49COrder.lean`: lifts of crossing continua of the annulus (`exists_lift`), the order
  of lifts and its translates.
* `HPC/Jones/Jones49CAnn.lean`: the two pieces of the annulus (`sector_two`) and the cyclic order
  (`sector_cyclic`).
* `HPC/Jones/Jones49CMoore.lean`: Moore's sufficiency in local form (`sufficiency_local`), the
  necessity (`propertyS_of_locallyConnected`), the pigeonhole step (`hloc_of_propertyS`), and helpers
  (`exists_crossing_continua_closed`, `exists_cross_sub`, `cikAt_of_locallyConnectedSpace`,
  `sphere_walk`).
* `HPC/Jones/Jones49C.lean`: the skeleton, with every item proved.

**Edits to existing files.**
* `HPC.lean`: one import.
* `HPC/Jones/Moore22T4.lean`: the commented copy of Theorem 4 is deleted.
* `HPC/Jones/Jones49A.lean`: the stale docstring sentence on (9.2) and `jones49_some_order_two` is
  corrected.
* `Axioms.lean`, `axioms.txt`, `README.md`, `LEDGER.md` §6 (new subsection at the end) and `OPEN.md`
  (Theorem 4 moved to "closed").
* Two lint fixes inside new files of this batch only (unused arguments); no other existing file is
  touched.

---

## 1. Item A: the sector theorem and the cyclic order

**Shape.** The annulus is the closed square annulus `Sector.Ann P r₁ r₂` (`r₁ ≤ d(z, P) ≤ r₂`, sup
metric, `0 < r₁ < r₂`), as in `exists_crossing_continua`. A crossing continuum is
`Sector.IsCrossA P r₁ r₂ K`: compact, connected, contained in the annulus, meeting both squares.
For disjoint crossing `K`, `K'`, `sector_theorem` gives `V₁`, `V₂`, nonempty, disjoint, relatively
open in the annulus (`Sector.RelOpenAnn`), with `V₁ ∪ V₂ = Ann \ (K ∪ K')`, such that every
preconnected `C ⊆ Ann` meeting `V₁` and `V₂` meets `K ∪ K'`. The commission asked for `C` in the open
annulus; the closed annulus is a stronger statement.

`sector_cyclic_order`: for pairwise disjoint crossing continua `k n`, there is a strictly increasing
`g` and pieces `V n` (`n ≥ 1`) with `k (g n) ⊆ V n`; `V n` misses every `k (g m)`, `m ≠ n`, and every
`V m` with `|n − m| ≥ 2`; and a preconnected subset of the annulus that misses `k (g (n − 1))` and
`k (g (n + 1))` and meets `V n` lies in `V n`.

**Route.** The annulus minus a crossing continuum is lifted to a strip through a continuous logarithm
(the component criterion `HPC.Moore.exists_log_of_mem_component`). In the strip a crossing continuum
has a left and a right side (`lc_disjoint_rc`), and a preconnected set cannot pass from one to the
other off the continuum (`no_cross_join`). Lifts are linearly ordered and invariant under the
translation by `2π`; the two pieces of the annulus are the images of the region between a lift of
`K` and the next lift of `K'`, and between that and the next lift of `K`. For infinitely many
continua the lifts in one fundamental domain have a monotone subsequence, which gives the cyclic
order.

**Tools used:** the component criterion for a continuous logarithm, and the connectedness of the
outside of a square (`isConnected_compl_closedBall_pt`). **Not used:** `janiszewski_compact`,
`plane_unicoherent`, `jordan_curve_theorem`, the θ-curve theorems of F.A. §6.

## 2. Item B: Moore's sufficiency, local form

`moore22_sufficiency_local` follows Moore's p. 236 argument. If the boundary `M` is not locally
connected at some point, `exists_crossing_continua_closed` (batch 150's construction, for closed
connected `M`) gives infinitely many disjoint continua of `M` crossing a square annulus about that
point. Item A orders them; in each piece `Vₙ` (odd `n`) a point of `R` near `kₙ` is chosen in a small
ball about a point of `kₙ` (check 2). These points converge to a boundary point. By Whyburn's
condition, two of them are joined by a small connected subset of `R`; it lies in the annulus, misses
`M`, and meets two different pieces, against item A. The proof uses neither boundedness, nor simple
connectivity, nor the connectedness of `R` (`hRc` is unused).

## 3. Item C: Moore 1922 Theorem 4

* **Sufficiency.** Property S gives Whyburn's local condition by pigeonhole (`hloc_of_propertyS`,
  check 3). Item B gives local connectedness, and batch 150's
  `isConnected_frontier_of_mooreSimplyConnected` gives connectedness.
* **Necessity.** `propertyS_of_locallyConnected`: Moore's pp. 236–237 argument with the repaired last
  step (check 4). It does not use simple connectivity.

The statement is the batch-150 one, verbatim.

## 4. Item D: complementary domains

* `isConnected_frontier_complDomain`: immediate from Brouwer's boundary theorem
  `HPC.Moore.brouwer_boundary` (closed connected `M`). That theorem uses unicoherence of the plane;
  this is the only use of unicoherence in the batch. It covers bounded and unbounded domains.
* `mooreSimplyConnected_complDomain`: the complement of the domain `U` is connected
  (`isPreconnected_compl_connectedComponentIn_compl`: `M` together with the closures of the other
  domains, each meeting `M`) and unbounded. If `H` is bounded with `frontier H ⊆ U`, then `Uᶜ` lies in
  `interior H ∪ (closure H)ᶜ`, hence in the exterior of `H`, and `H ⊆ U`. The hypothesis `hx` is not
  needed: for `x ∈ M` the domain is empty.

## 5. Item E: (6.22) in the §14 form

`whyburn39_6_22_sec14` is proved from `whyburn_6_2` (batch 136) and aposyndesis (from semi-local
connectedness, `isAposyndetic_of_semiLocConn`). Fix `q ≠ p`. For each `a ≠ p`, `whyburn_6_2` (in the
connected set `M − {p}`) gives a continuum joining `q` to `a` that misses `p`, and aposyndesis gives a
continuum missing `p` with `a` in its interior; their union `L a` is a continuum containing `q`,
missing `p`, with an open `U a ∋ a` inside it. Finitely many `U a` cover the compact set
`M − V_ε(p)`; the union `W` of the corresponding `L a` is closed and misses `p`, so some `δ < ε` has
`V_δ(p) ∩ W = ∅` and `q ∉ V_δ(p)`. Then every `L a` lies in `M − V_δ(p)` and contains `q`, so
`M − V_ε(p)` lies in the component of `M − V_δ(p)` containing `q`.

## 6. Ledger entries

All are in `LEDGER.md` §6, subsection *Jones 1949 III … (batch 151)*, with the printed sentences
quoted.
1. Moore p. 236, the sequence `B₁, B₂, …` in order on `K*`: true; the proof needs the cyclic order of
   the *continua*, not only of the points; the formalization orders the continua through lifts.
   Whether the point order alone suffices is not settled. Harmless.
2. Moore p. 236, the circles about `Bₙ`: needs `Bₙ ∉ kₙ₋₁ ∪ kₙ₊₁`, which holds by disjointness.
   Harmless.
3. Moore p. 236, "not the sum of a finite collection": pigeonhole. Harmless.
4. Moore's necessity, last step: defective proof (the points `Yₘ`, `Yₙ` lie in `R`, not `M`), repaired
   as stated in the ledger; theorem true. Counted now that Theorem 4 is verified.
5. Whyburn 1939 p. 747, the inversion sentence: false as stated, counterexample a closed disk; the
   theorem is not affected (the local form needs no boundedness). Counted once Theorem 14 is verified
   (batch 152), as the commission specifies.

## 7. Axioms by theorem

Every theorem of the batch uses exactly `propext`, `Classical.choice`, `Quot.sound`:
`sector_theorem`, `sector_cyclic_order`, `moore22_sufficiency_local`, `moore22_theorem4`,
`isConnected_frontier_complDomain`, `mooreSimplyConnected_complDomain`,
`isPreconnected_compl_connectedComponentIn_compl`, `whyburn39_6_22_sec14`, and the 155 helpers listed
in `doc/batches/audits/axioms-batch151.txt`.

## 8. Reading plan for batch 152: Whyburn 1939 §14

**Transport or build the F.A. curve `C` directly?** Build it directly in `ℝ²`. The repository has no
instance of F.A. Axioms 1–8 (`HPC.Moore.Space`, `Defs.lean`) for `ℝ²` with Jordan-curve regions; only
the converse direction (`m19_plane`) exists. Verifying Axioms 1–8 for `ℝ²` would itself need the
Jordan curve theorem in a strong form for every axiom, which is more work than the direct
construction. Directly: `C` is the component of `I · V_δ(p)` containing `O`, with the sector machinery
of this batch and `jordan_curve_theorem` for the regions.

**The Jordan curve `K` from order 2.** By `whyburn_3_2` (batch 150) all but countably many points of
`M` near `p` are of order 2 relative to the relevant set, so two frontier points `x`, `y` of
`V_δ(p)` in `M` can be chosen of order 2. Join them by an arc in the complement of `M` inside the
domain `R` and by an arc in another complementary domain (or through `p`'s side), and close up to a
Jordan curve `K` through `x` and `y` meeting `M` only in `x` and `y`. `jordan_curve_theorem` then
separates `M − {x, y}` into the parts inside and outside `K`.

**Formal shape of Theorem 14** (every complementary domain, bounded or not):

```lean
theorem whyburn39_theorem14 {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    (hS : ∀ z : M, SemiLocConnAt z) {x : Pt} (hx : x ∉ M) :
    LocallyConnectedSpace (frontier (connectedComponentIn Mᶜ x))
```

with `SemiLocConnAt` taken in the subtype `M`. Proof: Whyburn's condition at every boundary point
(the §14 argument, with `whyburn39_6_22_sec14` and `K`), then `moore22_sufficiency_local`, with
connectedness of the boundary from `isConnected_frontier_complDomain`. No inversion is used (check 5).
