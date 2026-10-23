# Report — batch 77: `S3` at every span, and Bing's Theorem 3 unconditionally

No new commission was issued for this batch; the request was to continue. `lake build HPC RequestProject` is clean (8190 jobs).
**The two standing `sorry`s are closed.** They were `s3_general` (`HPC/Fold/General.lean`) and
`theorem3` (`HPC/Fold/Open.lean`). No other `sorry` is left outside comment blocks anywhere in the repository.

```
#print axioms HPC.Fold.theorem3      -- [propext, Classical.choice, Quot.sound]
#print axioms HPC.Fold.s3_general    -- [propext, Classical.choice, Quot.sound]
#print axioms HPC.Fold.Z77.s3_zig    -- [propext, Classical.choice, Quot.sound]
```

`theorem3` is proved as `theorem3_of_S3 Z77.s3_zig hn hcr i`, and `s3_general` as `Z77.s3_zig`. The
statements of both are unchanged.

## 1. The idea: jump zigzags

`FoldsOnto` puts no restriction on the walk `c`, and every walk tried in earlier batches moved one
level per step. The walk used here is a **jump zigzag**. It is given by a start level `T0` and a list of
turning levels `t₁, t₂, …`. Each leg `a → b` (with `|b − a| ≥ 3`) starts at `a` and then jumps
straight to `a ± 3` (skipping `a ± 1` and `a ± 2`). It then continues one level per step up to `b`
(`jwalk`, `jlen`, `HPC/Fold/Zig77Walk.lean`). Because of the skip, an arm that is on leg `a → b`
switches to the next leg exactly when it reaches level `arr a b = b ∓ 1`, and there is no timing
constraint. This is `Fit`, and `fold_of_fit` turns it into a fold. The condition for a leg is:

* the arm stays within one level of the range of the leg from now on, **or**
* it stays within one level of that range until it reaches `arr a b`, and from there it fits the rest.

## 2. The greedy choice, and why it never gets stuck

An **up phase** starts from bottom `b`, with previous top `a`. Its target `t` is the least value, over
the live arms, of (the arm's maximum before it first drops to `b − 2`) + 1. Every arm switches to the
next leg when it first reaches `t − 1` (`up_step`, `HPC/Fold/Zig77Step.lean`). A **down phase**
mirrors this (`down_step`). A phase is stuck when some arm drops to `b − 2` (or rises to `a + 2`)
before reaching the old extreme. Both such configurations contradict crookedness (`HPC/Fold/Zig77Crook.lean`):

* up phase: `up_core` gives the contradiction, reading crookedness once across the basepoint (`nofail_up`);
* down phase: `down_core` gives the contradiction, reading crookedness once across the basepoint and once more inside
  the failing arm (`nofail_down`);
* first phase: at least one of the two directions is not stuck (`first_direction`, which also uses `up_core`).

Each phase widens the zigzag by at least one level at each end, and the band `[L, H]` is bounded.
So an induction on `(H + 1 − a) + (b − L + 1)` finishes the construction (`main_up`, `greedy_fit`,
`HPC/Fold/Zig77Main.lean`). Finally, `s3_zig` applies this to the arms `armG ρ i` and `armT ρ i`. It
uses the crookedness of `ρ` read on levels at the basepoint (`crkOn_of_isCrookedIvF`) and converts the
fold to `FoldsOnto`.

## 3. Files

| file | content |
|---|---|
| `HPC/Fold/Zig77Walk.lean` | `Env`, `arr`, `Fit`, `jlen`, `jwalk`, `fold_of_fit` |
| `HPC/Fold/Zig77Crook.lean` | `CrkOn`, `reindex`, `crkOn_of_isCrookedIvF`, `up_core`, `down_core` |
| `HPC/Fold/Zig77Step.lean` | `up_step`, `down_step` (one greedy phase for both arms) |
| `HPC/Fold/Zig77Main.lean` | `nofail_up`, `nofail_down`, `first_direction`, `main_up`, `greedy_fit`, `s3_zig : S3` |
| `HPC/Fold/General.lean` | `s3_general : S3 := Z77.s3_zig` |
| `HPC/Fold/Open.lean` | `theorem3 := theorem3_of_S3 Z77.s3_zig hn hcr i` |

The exploration scripts `zig77.py` and `greedy77.c` ran the greedy construction on many basepoints
before the proof was written, and it never got stuck on them. That run is not a verification. The
proof above is what establishes the result.

The commented-out `s3` block at the end of `HPC/Fold/Span.lean`, and the historical notes in other
files that describe `S3` as open, have been left as they were. `Span.lean` cannot import the new files,
because they import it.
