import HPC.Census.Census87
import HPC.Census.Census87Checks

/-!
# Census: the `native_decide` theorems

`HPC/Census/Census87.lean` (the checker and its soundness proof) and
`HPC/Census/Census87Checks.lean` (the census theorems themselves, proved by `native_decide`).

**Axiom profile.** The theorems of `Census87Checks` depend, besides the standard axioms
`propext`, `Classical.choice` and `Quot.sound`, on `Lean.ofReduceBool` and `Lean.trustCompiler`
(the axioms through which `native_decide` trusts the compiled evaluator).

**Nothing depends on them.** No file imported by `HPC.lean` imports these files, so no theorem of
the main line rests on `native_decide`. Build with `lake build HPCCensus`.
-/
