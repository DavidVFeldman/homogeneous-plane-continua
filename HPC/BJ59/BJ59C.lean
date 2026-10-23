import HPC.BJ59.Zigzag
import HPC.BJ59.NonVac200
import HPC.BJ59.Private
import HPC.BJ59.Step1b
import HPC.BJ59.Thm8
import HPC.BJ59.Thm8Cor
import HPC.BJ59.Thm9
import HPC.BJ59.DP61
import HPC.BJ59.NonVac200b

/-!
# Batch 200: Part G, III — Bing–Jones's homeomorphism of pp. 188–189, private points,
# Step 1(b), Theorem 8 and its corollary, Theorem 9

The skeleton of commission 200 (`doc/batches/skeletons/BJ59C.lean`), split under `HPC/BJ59/`.
Every declaration of the skeleton is delivered, with its statement as in the skeleton:

* §2 `starImage`, `zigzag_homeomorph`, `zigzag_fibre`: `Zigzag.lean`;
* §3 `exists_privatePoint_interior`, `exists_privatePoint_shrink`: `Private.lean`;
  `bj_step1b`: `Step1b.lean`;
* §4 `bj_theorem8`: `Thm8.lean` (tools in `Thm8Lib.lean`); `bj_theorem8_cor`: `Thm8Cor.lean`;
* §5 `bj9_base`: `Thm9Base.lean` (tools in `Thm9Class.lean`, `Thm9D.lean`, `Thm9E.lean`);
  `bj_theorem9`: `Thm9.lean`;
* §6 `dp22_theorem61_iff`: `DP61.lean`; `bj_theorem7_proof_n3`: `Private.lean`;
* §8 `nonvac_zigzag` and the other non-vacuity witnesses: `NonVac200.lean`, `NonVac200b.lean`.

Source: R. H. Bing and F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959),
§§4–6 (`doc/sources/bing-jones1959.pdf`). Route: commission 200.
-/
