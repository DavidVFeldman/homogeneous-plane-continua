import HPC.Archive.CoverL5
import HPC.Fold.Leaf

/-!
# The branch hypothesis is one of the three announcements of a walk of the branch `L + 5`

`foldsOnto_walk63718` (`HPC/Fold/CoverL5.lean`) gives the walk `L+6 → L+3 → L+7 → L+1 → L+8` — the
wide four-leg engine at `(P, K, M) = (L + 4, L + 6, L + 2)`, read through the reflection of an arm
— an exact criterion in three announcements: the ascents to `L + 8`, the ascents to `L + 9`, and
the descents to `L + 1`.

The third of these is *exactly* the branch hypothesis. `LowAt g (L + 1) (L + 8)` says that before
`g` ever falls to `L + 1` it has either reached `L + 8` or been at `L + 2` and after that at
`L + 6`; the walk's third announcement offers those two disjuncts and one more. So at the branch
`L + 5` of span nine — where both arms carry `LowAt (L + 1) (L + 8)` — this walk asks for two
announcements, not three (`foldsOnto_walk63718_of_lowAt`), and the two it still asks for are both
about ascents.

This is the shape of what the branch has left to prove, and the census of batch 58 measures it:
over 3 091 444 arms of the branch the walk's descent announcement fails **never** — it is the
hypothesis — while the announcement of the ascents to `L + 8` fails at 313 046 arms and that of
the ascents to `L + 9` at 511 199. The criterion as a whole holds on both arms at 933 197 of the
1 545 722 basepoints of the branch, more than any other parameter set of the window; what stops it
from closing the branch is the two ascent clauses, and `not_leg4CritClosesL5`
(`HPC/Fold/Audit58.lean`) shows that no other parameter set repairs them.
-/

namespace HPC.Fold

/-- **The descents to `L + 1`, announced by the branch hypothesis.** The third announcement of
`foldsOnto_walk63718` is the first two disjuncts of `LowAt (L + 1) (L + 8)`, verbatim. -/
theorem down1_of_lowAt {m : ℕ} {g : Fin m → ℤ} {L : ℤ} (h : LowAt g (L + 1) (L + 8)) :
    ∀ d : Fin m, g d ≤ L + 1 →
      (∃ k : Fin m, k.val < d.val ∧ L + 8 ≤ g k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ g k ≤ L + 2 ∧ L + 6 ≤ g k') ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        L + 7 ≤ g k ∧ g k' ≤ L + 3 ∧ L + 6 ≤ g k'') := by
  intro d hd
  rcases h d hd with ⟨j, hj, hjv⟩ | ⟨j, j', h1, h2, h3, h4⟩
  · exact Or.inl ⟨j, hj, by omega⟩
  · exact Or.inr (Or.inl ⟨j, j', h1, h2, by omega, by omega⟩)

/-- **The walk `L+6 → L+3 → L+7 → L+1 → L+8` asks the branch for two announcements, not three.**
An arm of the branch `L + 5` — based at `L + 5` or `L + 6` inside the band `[L, L + 9]` and
carrying the branch hypothesis `LowAt (L + 1) (L + 8)` — folds onto the walk as soon as its ascents
to `L + 8` and its ascents to `L + 9` are announced; the third announcement of
`foldsOnto_walk63718`, the one about its descents to `L + 1`, is the hypothesis itself. -/
theorem foldsOnto_walk63718_of_lowAt {m : ℕ} (hm : 0 < m) (g : Fin m → ℤ) (hg : IsLip g) (L : ℤ)
    (h0lo : L + 5 ≤ g ⟨0, hm⟩) (h0hi : g ⟨0, hm⟩ ≤ L + 6)
    (hL : ∀ j, L ≤ g j) (hH : ∀ j, g j ≤ L + 9)
    (hlow : LowAt g (L + 1) (L + 8))
    (hup8 : ∀ d : Fin m, L + 8 ≤ g d →
      (∃ k : Fin m, k.val < d.val ∧ g k ≤ L + 3) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ L + 7 ≤ g k ∧ g k' ≤ L + 4))
    (hup9 : ∀ d : Fin m, L + 9 ≤ g d →
      (∃ k : Fin m, k.val < d.val ∧ g k ≤ L + 1) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ L + 8 ≤ g k ∧ g k' ≤ L + 2) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        g k ≤ L + 2 ∧ L + 7 ≤ g k' ∧ g k'' ≤ L + 2)) :
    FoldsOnto g (leg4Len L (L + 9) (L + 6) (L + 2) (L + 4))
      (leg4Walk' L (L + 9) (L + 6) (L + 2) (L + 4)) :=
  foldsOnto_walk63718 hm g hg L h0lo h0hi hL hH hup8 hup9 (down1_of_lowAt hlow)

/-- **Both arms of a basepoint of the branch, on the same walk.** If the two arms of a basepoint
of the branch `L + 5` both announce their ascents, the pair folds onto a common walk, so the
conclusion of `s3_span_nine_mid5` holds there. -/
theorem s3_span_nine_mid5_of_ascents {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5)
    (hG : LowAt (armG ρ i) (L + 1) (L + 8)) (hT : LowAt (armT ρ i) (L + 1) (L + 8))
    (hupG : (∀ d : Fin (n - i.val), L + 8 ≤ armG ρ i d →
        (∃ k : Fin (n - i.val), k.val < d.val ∧ armG ρ i k ≤ L + 3) ∨
        (∃ k k' : Fin (n - i.val), k.val < k'.val ∧ k'.val < d.val ∧
          L + 7 ≤ armG ρ i k ∧ armG ρ i k' ≤ L + 4)) ∧
      (∀ d : Fin (n - i.val), L + 9 ≤ armG ρ i d →
        (∃ k : Fin (n - i.val), k.val < d.val ∧ armG ρ i k ≤ L + 1) ∨
        (∃ k k' : Fin (n - i.val), k.val < k'.val ∧ k'.val < d.val ∧
          L + 8 ≤ armG ρ i k ∧ armG ρ i k' ≤ L + 2) ∨
        (∃ k k' k'' : Fin (n - i.val), k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
          armG ρ i k ≤ L + 2 ∧ L + 7 ≤ armG ρ i k' ∧ armG ρ i k'' ≤ L + 2)))
    (hupT : (∀ d : Fin (i.val + 1), L + 8 ≤ armT ρ i d →
        (∃ k : Fin (i.val + 1), k.val < d.val ∧ armT ρ i k ≤ L + 3) ∨
        (∃ k k' : Fin (i.val + 1), k.val < k'.val ∧ k'.val < d.val ∧
          L + 7 ≤ armT ρ i k ∧ armT ρ i k' ≤ L + 4)) ∧
      (∀ d : Fin (i.val + 1), L + 9 ≤ armT ρ i d →
        (∃ k : Fin (i.val + 1), k.val < d.val ∧ armT ρ i k ≤ L + 1) ∨
        (∃ k k' : Fin (i.val + 1), k.val < k'.val ∧ k'.val < d.val ∧
          L + 8 ≤ armT ρ i k ∧ armT ρ i k' ≤ L + 2) ∨
        (∃ k k' k'' : Fin (i.val + 1), k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
          armT ρ i k ≤ L + 2 ∧ L + 7 ≤ armT ρ i k' ∧ armT ρ i k'' ≤ L + 2))) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hmG : 0 < n - i.val := by have := i.isLt; omega
  have hmT : 0 < i.val + 1 := by omega
  have h0G : armG ρ i ⟨0, hmG⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have h0T : armT ρ i ⟨0, hmT⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  refine ⟨leg4Len L (L + 9) (L + 6) (L + 2) (L + 4),
    leg4Walk' L (L + 9) (L + 6) (L + 2) (L + 4), ?_, ?_⟩
  · exact foldsOnto_walk63718_of_lowAt hmG (armG ρ i) (armG_isLip hlip i) L
      h0G.ge (by rw [h0G]; omega) (fun j => hLb _) (fun j => hHb _) hG
      hupG.1 hupG.2
  · exact foldsOnto_walk63718_of_lowAt hmT (armT ρ i) (armT_isLip hlip i) L
      h0T.ge (by rw [h0T]; omega) (fun j => hLb _) (fun j => hHb _) hT
      hupT.1 hupT.2

end HPC.Fold
