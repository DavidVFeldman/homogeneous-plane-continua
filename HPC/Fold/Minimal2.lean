import HPC.Fold.CutRoute
import HPC.Fold.ValleyFWitness

/-!
# Shortest serving walks

Batch 34 refuted the step in the form "every serving walk extends" and proved the mechanism:
an inner member's targets lie at `L + 2` or above, a fold pins time zero and moves the token
one time per link, so an arm reaching `L` early cannot be folded (`no_fold_of_early_low`).
COMMISSION-batch36.md §1 proposed to repair the step by restricting it to the *shortest*
serving walks, and gated the batch on a census of that form at spans nine to twelve.

**The gate fails, and it fails at span six.** At basepoint `5` of `bing 0 6` — the chain
`hlSeq` of `HPC/Fold/ValleyFWitness.lean`, seventy-one links on levels `0 … 6` — there is no
inner trim whose shortest serving members all extend. The census (`census-batch36.c`) decides
this exhaustively over *every* inner trim, not only the maximal stretches, at spans six, seven
and eight, and over the maximal stretches at spans nine to twelve; the commission's claim that
the form passes at spans six, seven and eight (25 of 25, 104 of 104, 319 of 319) is not
reproduced. `not_extendStepMin` below is the refutation, in Lean, at that basepoint.

The reason is uniform and is the content of the refutation. Only two bands can carry a trim at
that basepoint, `[1, 4]` and `[1, 5]`; the band `[2, 5]` has no stretch attaining its top. In
each of the two, the member `[2, 3, 2]` respectively `[3, 2, 4]` is *as short as any member of
the band can be* (`zigWalk_length_ge`: a member of `[L', H']` has walk length at least
`H' − L'`), it folds both arms of every stretch of that band at the basepoint, and its only
possible extension is a member of the free family of `[0, 6]` whose walk stays at level `2` or
above until time five — while the backward arm is at level `0` at index five. So the extension
cannot fold it (`no_fold_of_low_early`), and the shortest serving walks do not all extend, at
any trim.

What survives, and is delivered: the finiteness of a band's family (`finite_isZigFree`), the
existence of a shortest serving walk (`exists_shortest_serving`, by least-element on the walk
lengths — `Nat.find`, not the finiteness), and the induction the step would carry
(`s3ZigFreeInterior_of_extendStepMin`), which is proved outright rather than vacuously.

The commissioned `ExtendStepMin` does not elaborate: the `Fin n` indices `⟨a + j.val, by omega⟩`
in its body need `a ≤ i.val`, `i.val ≤ b` and `b < n`, which batch 34's `ExtendStepZF` carries as
explicit binders and which the commissioned statement drops. The statement below restores them;
the commissioned text is kept, commented out, at the end.

English proofs: COMMISSION-batch36.md §2–§3.
-/

namespace HPC.Fold

/-! ## The length of a walk through a turning sequence -/

/-- The total amplitude is at least the last amplitude. -/
theorem ampSum_ge_last : ∀ (a : ℤ) (l : List ℤ), 2 ≤ l.length →
    (l[l.length - 1]! - l[l.length - 2]!).natAbs ≤ ampSum a l := by
  intro a l
  induction l generalizing a with
  | nil => intro h; simp at h
  | cons x rest ih =>
      intro h
      simp only [List.length_cons] at h
      rcases Nat.lt_or_ge rest.length 2 with hr | hr
      · obtain ⟨y, rfl⟩ : ∃ y, rest = [y] := by
          match rest with
          | [] => simp at h
          | [y] => exact ⟨y, rfl⟩
          | y :: z :: t => simp at hr; omega
        simp [ampSum]
      · obtain ⟨m, hm⟩ : ∃ m, rest.length = m + 2 := ⟨rest.length - 2, by omega⟩
        have e1 : (x :: rest)[rest.length + 1 - 1]! = rest[rest.length - 1]! := by
          rw [hm]; simp
        have e2 : (x :: rest)[rest.length + 1 - 2]! = rest[rest.length - 2]! := by
          rw [hm]; simp
        simp only [List.length_cons]
        rw [e1, e2, ampSum]
        have := ih x hr
        omega

/-- The total amplitude is at least the first amplitude plus the last. -/
theorem ampSum_ge_first_add_last : ∀ (a : ℤ) (l : List ℤ), 2 ≤ l.length →
    (l[0]! - a).natAbs + (l[l.length - 1]! - l[l.length - 2]!).natAbs ≤ ampSum a l := by
  intro a l hl
  match l with
  | [] => simp at hl
  | x :: rest =>
      simp only [List.length_cons] at hl
      rcases Nat.lt_or_ge rest.length 2 with hr | hr
      · obtain ⟨y, rfl⟩ : ∃ y, rest = [y] := by
          match rest with
          | [] => simp at hl
          | [y] => exact ⟨y, rfl⟩
          | y :: z :: t => simp at hr; omega
        simp [ampSum]
      · obtain ⟨m, hm⟩ : ∃ m, rest.length = m + 2 := ⟨rest.length - 2, by omega⟩
        have e1 : (x :: rest)[rest.length + 1 - 1]! = rest[rest.length - 1]! := by
          rw [hm]; simp
        have e2 : (x :: rest)[rest.length + 1 - 2]! = rest[rest.length - 2]! := by
          rw [hm]; simp
        simp only [List.length_cons]
        rw [e1, e2, ampSum]
        have := ampSum_ge_last x rest hr
        simp only [List.getElem!_cons_zero]
        omega

/-- **A member of a band is at least as long as the band is wide.** Its last leg runs from one
extreme of the band to the other, `H − L − 2` steps, and at least one step precedes it. -/
theorem zigWalk_length_ge {L H : ℤ} {ts : List ℤ} (h : IsZigFree L H ts) :
    H - L ≤ (zigWalk ts).1 := by
  have hlen := h.len
  match ts, hlen with
  | t :: rest, hlen =>
    simp only [List.length_cons] at hlen
    have hr : 2 ≤ rest.length := by omega
    obtain ⟨m, hm⟩ : ∃ m, rest.length = m + 2 := ⟨rest.length - 2, by omega⟩
    have key := ampSum_ge_first_add_last t rest hr
    have e1 : (t :: rest)[(t :: rest).length - 1]! = rest[rest.length - 1]! := by
      simp only [List.length_cons]; rw [hm]; simp
    have e2 : (t :: rest)[(t :: rest).length - 2]! = rest[rest.length - 2]! := by
      simp only [List.length_cons]; rw [hm]; simp
    have hends := h.ends
    rw [e1, e2] at hends
    have halt := h.alt 0 (by simp only [List.length_cons]; omega)
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at halt
    have hne : rest[0]! ≠ t := by
      intro he; rw [he] at halt; simp at halt
    have hq1 : rest[rest.length - 1]! = rest[rest.length - 1] := getElem!_pos _ _ (by omega)
    have hb1 := h.bounds rest[rest.length - 1] (List.mem_cons_of_mem _ (List.getElem_mem _))
    rw [hq1] at hends
    have hwide : L + 2 ≤ H := by
      rcases hends with he | he <;> rw [Prod.mk.injEq] at he <;> omega
    have hlast : (H - L - 2).natAbs ≤
        (rest[rest.length - 1]! - rest[rest.length - 2]!).natAbs := by
      rw [hq1]
      rcases hends with he | he <;> rw [Prod.mk.injEq] at he <;> rw [he.1, he.2] <;> omega
    have hfirst : 1 ≤ (rest[0]! - t).natAbs := by omega
    rw [zigWalk_length]
    omega

/-! ## Finiteness of the family -/

/-- The amplitudes grow by at least one from the second on. -/
theorem zigFree_amp_ge {L H : ℤ} {ts : List ℤ} (h : IsZigFree L H ts) :
    ∀ j, 1 ≤ j → j + 1 < ts.length → (j : ℤ) ≤ |ts[j+1]! - ts[j]!| := by
  intro j
  induction j with
  | zero => intro h1; omega
  | succ k ih =>
      intro _ hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · have halt := h.alt 0 (by omega)
        have hne : ts[2]! ≠ ts[1]! := by
          intro he; rw [he] at halt; simp at halt
        have h1 : (1 : ℤ) ≤ |ts[2]! - ts[1]!| := by
          rcases abs_cases (ts[2]! - ts[1]!) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
        simpa using h1
      · have hprev := ih hkpos (by omega)
        have hamp := h.amp k hkpos (by omega)
        have e : k + 1 + 1 = k + 2 := by omega
        rw [e]
        push_cast
        omega

/-- **A member of a band has at most `H − L` targets.** -/
theorem zigFree_length_le {L H : ℤ} {ts : List ℤ} (h : IsZigFree L H ts) :
    (ts.length : ℤ) ≤ H - L := by
  have hlen := h.len
  obtain ⟨m, hm⟩ : ∃ m, ts.length = m + 3 := ⟨ts.length - 3, by omega⟩
  have hj := zigFree_amp_ge h (ts.length - 2) (by omega) (by omega)
  have e1 : ts.length - 2 + 1 = ts.length - 1 := by omega
  rw [e1] at hj
  have q1 : ts[ts.length - 1]! = ts[ts.length - 1] := getElem!_pos _ _ (by omega)
  have q2 : ts[ts.length - 2]! = ts[ts.length - 2] := getElem!_pos _ _ (by omega)
  rw [q1, q2] at hj
  have hb1 := h.bounds _ (List.getElem_mem (show ts.length - 1 < ts.length by omega))
  have hb2 := h.bounds _ (List.getElem_mem (show ts.length - 2 < ts.length by omega))
  have habs : |ts[ts.length - 1] - ts[ts.length - 2]| ≤ H - L - 2 := by
    rw [abs_le]; omega
  have hcast : ((ts.length - 2 : ℕ) : ℤ) = (ts.length : ℤ) - 2 := by
    rw [hm]; push_cast; omega
  rw [hcast] at hj
  omega

/-- Lists of bounded length over a finite set of levels form a finite set. -/
theorem finite_lists_of_bounded (s : Set ℤ) (hs : s.Finite) : ∀ N : ℕ,
    {l : List ℤ | l.length ≤ N ∧ ∀ x ∈ l, x ∈ s}.Finite := by
  intro N
  induction N with
  | zero =>
      refine Set.Finite.subset (Set.finite_singleton ([] : List ℤ)) ?_
      rintro l ⟨hl, -⟩
      simp only [Set.mem_singleton_iff]
      exact List.length_eq_zero_iff.mp (by omega)
  | succ N ih =>
      refine Set.Finite.subset
        (Set.Finite.union (Set.finite_singleton ([] : List ℤ))
          (Set.Finite.image2 (fun (a : ℤ) (l : List ℤ) => a :: l) hs ih)) ?_
      rintro l ⟨hl, hmem⟩
      match l with
      | [] => exact Or.inl rfl
      | x :: rest =>
          refine Or.inr ⟨x, hmem x (by simp), rest, ⟨?_, ?_⟩, rfl⟩
          · simp only [List.length_cons] at hl; omega
          · intro y hy; exact hmem y (by simp [hy])

/-- **The walks of a band, as a finite set**: what makes "a shortest serving walk" well defined.
The bound on the number of targets is the route: the amplitudes strictly increase after the
first, so a member has at most `H − L` targets, each in `[L+1, H−1]`. -/
theorem finite_isZigFree (L H : ℤ) :
    {ts : List ℤ | IsZigFree L H ts}.Finite := by
  refine Set.Finite.subset
    (finite_lists_of_bounded (Set.Icc (L + 1) (H - 1)) (Set.finite_Icc _ _) (H - L).toNat) ?_
  intro ts hts
  simp only [Set.mem_setOf_eq] at hts
  refine ⟨?_, ?_⟩
  · have := zigFree_length_le hts
    omega
  · intro x hx
    exact Set.mem_Icc.mpr (hts.bounds x hx)

/-! ## A shortest serving walk -/

open Classical in
/-- **A serving walk of least length exists whenever one serves.** By least element on the set
of lengths of serving members (`Nat.find`); the finiteness of the family is not needed. -/
theorem exists_shortest_serving {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L H : ℤ)
    (h : ∃ ts : List ℤ, IsZigFree L H ts ∧
      FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2) :
    ∃ ts : List ℤ, IsZigFree L H ts ∧
      FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
      ∀ ts' : List ℤ, IsZigFree L H ts' →
        FoldsOnto (armG ρ i) (zigWalk ts').1 (zigWalk ts').2 →
        FoldsOnto (armT ρ i) (zigWalk ts').1 (zigWalk ts').2 →
        (zigWalk ts).1 ≤ (zigWalk ts').1 := by
  have hP : ∃ k : ℕ, ∃ ts : List ℤ, IsZigFree L H ts ∧
      FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧ (zigWalk ts).1 = k := by
    obtain ⟨ts, h1, h2, h3⟩ := h
    exact ⟨(zigWalk ts).1, ts, h1, h2, h3, rfl⟩
  obtain ⟨ts, h1, h2, h3, h4⟩ := Nat.find_spec hP
  refine ⟨ts, h1, h2, h3, ?_⟩
  intro ts' h1' h2' h3'
  have : Nat.find hP ≤ (zigWalk ts').1 :=
    Nat.find_le ⟨ts', h1', h2', h3', rfl⟩
  omega

/-! ## The step, and the induction it carries -/

/-- **`ExtendStepMin`.** Some inner trim has every *shortest* serving walk extending. The trim is
an `IsInnerTrim` — strictly inside at both ends — as batch 34 proved it must be. The binders
`a ≤ i.val`, `i.val ≤ b`, `b < n` are those of batch 34's `ExtendStepZF`, without which the
`Fin n` indices of the body do not elaborate. -/
def ExtendStepMin : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 6 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) → L + 3 ≤ ρ i → ρ i ≤ H - 3 →
    ∃ (a b : ℕ) (_hai : a ≤ i.val) (_hib : i.val ≤ b) (_hbn : b < n) (L' H' : ℤ),
      IsInnerTrim ρ i L H a b L' H' ∧
      ∀ ts : List ℤ, IsZigFree L' H' ts →
        FoldsOnto (armG (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩)
          ⟨i.val - a, by omega⟩) (zigWalk ts).1 (zigWalk ts).2 →
        FoldsOnto (armT (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩)
          ⟨i.val - a, by omega⟩) (zigWalk ts).1 (zigWalk ts).2 →
        (∀ ts' : List ℤ, IsZigFree L' H' ts' →
          FoldsOnto (armG (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩)
            ⟨i.val - a, by omega⟩) (zigWalk ts').1 (zigWalk ts').2 →
          FoldsOnto (armT (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩)
            ⟨i.val - a, by omega⟩) (zigWalk ts').1 (zigWalk ts').2 →
          (zigWalk ts).1 ≤ (zigWalk ts').1) →
        ∃ x y : ℤ, ((x, y) = (L + 1, H - 1) ∨ (x, y) = (H - 1, L + 1)) ∧
          IsZigFree L H (ts ++ [x, y]) ∧
          FoldsOnto (armG ρ i) (zigWalk (ts ++ [x, y])).1 (zigWalk (ts ++ [x, y])).2 ∧
          FoldsOnto (armT ρ i) (zigWalk (ts ++ [x, y])).1 (zigWalk (ts ++ [x, y])).2

/-- **The induction the step carries.** Batch 34's induction with one change: the walk the
induction hypothesis supplies for the inner stretch is replaced by a shortest one
(`exists_shortest_serving`) before the step is invoked. -/
theorem s3ZigFreeInterior_of_extendStepMin (h : ExtendStepMin) : S3ZigFreeInterior := by
  have key : ∀ d : ℕ, ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
      (H - L).toNat ≤ d → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
      (∃ t, ρ t = L) → (∃ t, ρ t = H) → L + 3 ≤ ρ i → ρ i ≤ H - 3 →
      ∃ ts : List ℤ, IsZigFree L H ts ∧
        FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
        FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2 := by
    intro d
    induction d with
    | zero =>
        intro n ρ σ i H L hd _ _ _ hLH _ _ _ _
        exact absurd hd (by omega)
    | succ d ih =>
        intro n ρ σ i H L hd hcr hLb hHb _ heL heH hlo hhi
        have hi0 := hLb i
        have h6 : L + 6 ≤ H := by omega
        obtain ⟨a, b, hai, hib, hbn, L', H', htrim, hevery⟩ :=
          h n ρ σ i H L hcr hLb hHb h6 heL heH hlo hhi
        obtain ⟨-, -, -, hband, ⟨jL, hjL1, hjL2, hjL3⟩, ⟨jH, hjH1, hjH2, hjH3⟩, hLL, hHH, h3⟩ :=
          htrim
        -- the stretch, its faithfulness, its band and its basepoint
        have hcr' : IsCrookedIvF (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩)
            (fun j : Fin (b - a + 1) => σ ⟨a + j.val, by omega⟩) :=
          isCrookedIvF_restrict hcr a b (by omega) hbn
        have hLb' : ∀ t : Fin (b - a + 1), L' ≤ ρ ⟨a + t.val, by omega⟩ := by
          intro t
          have ht := t.isLt
          exact (hband _ (by simp) (by simp; omega)).1
        have hHb' : ∀ t : Fin (b - a + 1), ρ (⟨a + t.val, by omega⟩ : Fin n) ≤ H' := by
          intro t
          have ht := t.isLt
          exact (hband _ (by simp) (by simp; omega)).2
        have heL' : ∃ t : Fin (b - a + 1), ρ (⟨a + t.val, by omega⟩ : Fin n) = L' := by
          refine ⟨⟨jL.val - a, by omega⟩, ?_⟩
          rw [show (⟨a + (jL.val - a), by omega⟩ : Fin n) = jL from Fin.ext (by simp; omega)]
          exact hjL3
        have heH' : ∃ t : Fin (b - a + 1), ρ (⟨a + t.val, by omega⟩ : Fin n) = H' := by
          refine ⟨⟨jH.val - a, by omega⟩, ?_⟩
          rw [show (⟨a + (jH.val - a), by omega⟩ : Fin n) = jH from Fin.ext (by simp; omega)]
          exact hjH3
        have hbase : ρ (⟨a + (i.val - a), by omega⟩ : Fin n) = ρ i := by
          rw [show (⟨a + (i.val - a), by omega⟩ : Fin n) = i from Fin.ext (by simp; omega)]
        -- an inner walk: by the induction hypothesis if the basepoint is still interior,
        -- and by `s3ZigFree_near_extreme` if it is not
        have hinner : ∃ ts : List ℤ, IsZigFree L' H' ts ∧
            FoldsOnto (armG (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩)
              ⟨i.val - a, by omega⟩) (zigWalk ts).1 (zigWalk ts).2 ∧
            FoldsOnto (armT (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩)
              ⟨i.val - a, by omega⟩) (zigWalk ts).1 (zigWalk ts).2 := by
          by_cases hint : L' + 3 ≤ ρ i ∧ ρ i ≤ H' - 3
          · refine ih (b - a + 1) _ (fun j : Fin (b - a + 1) => σ ⟨a + j.val, by omega⟩)
              ⟨i.val - a, by omega⟩ H' L' (by omega) hcr' hLb' hHb' (by omega) heL' heH'
              ?_ ?_
            · show L' + 3 ≤ ρ ⟨a + (i.val - a), _⟩
              rw [hbase]; exact hint.1
            · show ρ (⟨a + (i.val - a), _⟩ : Fin n) ≤ H' - 3
              rw [hbase]; exact hint.2
          · refine s3ZigFree_near_extreme _ ⟨i.val - a, by omega⟩ H' L' hcr'.isLip hLb' hHb'
              (by omega) ?_
            have h1 : L' ≤ ρ i := by
              have := hLb' ⟨i.val - a, by omega⟩
              rwa [hbase] at this
            have h2 : ρ i ≤ H' := by
              have := hHb' ⟨i.val - a, by omega⟩
              rwa [hbase] at this
            show ρ (⟨a + (i.val - a), _⟩ : Fin n) ≤ L' + 2 ∨
              H' - 2 ≤ ρ (⟨a + (i.val - a), _⟩ : Fin n)
            rw [hbase]
            omega
        obtain ⟨ts, hzf, hG, hT, hshort⟩ :=
          exists_shortest_serving (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩)
            ⟨i.val - a, by omega⟩ L' H' hinner
        obtain ⟨x, y, -, hmem, hfG, hfT⟩ := hevery ts hzf hG hT hshort
        exact ⟨ts ++ [x, y], hmem, hfG, hfT⟩
  intro n ρ σ i H L hcr hLb hHb hLH heL heH hlo hhi
  exact key (H - L).toNat n ρ σ i H L le_rfl hcr hLb hHb hLH heL heH hlo hhi

/-! ## The refutation

The gate of COMMISSION-batch36.md §1 fails at basepoint `5` of `bing 0 6`, which is `hlSeq`.
Two bands can carry an inner trim there, `[1, 4]` and `[1, 5]`; in each the shortest member of
the band serves every stretch and does not extend.
-/

/-- Restricting a fold to a prefix of the sequence. -/
theorem foldsOnto_restrict {m m' : ℕ} {f : Fin m → ℤ} {g : Fin m' → ℤ} {len : ℕ} {c : ℕ → ℤ}
    (hle : m' ≤ m) (hg : ∀ j : Fin m', g j = f ⟨j.val, lt_of_lt_of_le j.isLt hle⟩)
    (h : FoldsOnto f len c) : FoldsOnto g len c := by
  obtain ⟨β, hlt, hlip, h0, hw⟩ := h
  refine ⟨fun j => β ⟨j.val, lt_of_lt_of_le j.isLt hle⟩, fun j => hlt _, ?_, ?_, ?_⟩
  · intro j j' hjj'
    exact hlip _ _ (by simpa using hjj')
  · intro j hj
    exact h0 _ (by simpa using hj)
  · intro j
    rw [hg j]
    exact hw _

/-! ### The two shortest members, and their walks -/

theorem zigLevels_232 : zigLevels [2, 3, 2] = [2, 3, 2] := by
  simp [zigLevels, zigTail, stepRun]

theorem zigLevels_324 : zigLevels [3, 2, 4] = [3, 2, 3, 4] := by
  simp [zigLevels, zigTail, stepRun]

theorem zigWalk_232_length : (zigWalk [2, 3, 2]).1 = 3 := by
  simp [zigWalk, zigLevels_232]

theorem zigWalk_324_length : (zigWalk [3, 2, 4]).1 = 4 := by
  simp [zigWalk, zigLevels_324]

/-- `[2, 3, 2]` is a member of the free family of `[1, 4]`, and by `zigWalk_length_ge` no member
of that band is shorter. -/
theorem isZigFree_232 : IsZigFree 1 4 [2, 3, 2] := by
  refine ⟨by decide, by decide, ?_, ?_, by decide⟩
  · intro j hj
    have h3 : j < 1 := by simp at hj; omega
    interval_cases j
    decide
  · intro j hj1 hj
    simp only [List.length_cons, List.length_nil] at hj
    omega

/-- `[3, 2, 4]` is a member of the free family of `[1, 5]`, and no member of that band is
shorter. -/
theorem isZigFree_324 : IsZigFree 1 5 [3, 2, 4] := by
  refine ⟨by decide, by decide, ?_, ?_, by decide⟩
  · intro j hj
    have h3 : j < 1 := by simp at hj; omega
    interval_cases j
    decide
  · intro j hj1 hj
    simp only [List.length_cons, List.length_nil] at hj
    omega

/-- **Any sequence inside the band `[1, 4]` folds onto `[2, 3, 2]`**, provided it starts at
level `3` or below: a level at `4` is served at time one and every other level at time zero. -/
theorem foldsOnto_232_of_band {m : ℕ} {f : Fin m → ℤ}
    (hb : ∀ j, 1 ≤ f j ∧ f j ≤ 4) (h0 : ∀ j : Fin m, j.val = 0 → f j ≤ 3) :
    FoldsOnto f (zigWalk [2, 3, 2]).1 (zigWalk [2, 3, 2]).2 := by
  refine ⟨fun j => if f j = 4 then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro j
    simp only [zigWalk, zigLevels_232, List.length_cons, List.length_nil]
    split <;> omega
  · intro j j' _
    simp only
    split <;> split <;> norm_num
  · intro j hj
    have := h0 j hj
    simp only [if_neg (by omega : ¬ f j = 4)]
  · intro j
    have hbj := hb j
    simp only [zigWalk, zigLevels_232]
    split
    · rename_i he
      rw [he]
      norm_num
    · rename_i he
      have h3 : f j ≤ 3 := by omega
      simp only [List.getD_cons_zero]
      rw [abs_le]
      omega

/-- The time assignment folding the forward arm at basepoint `5` onto the walk of `[3, 2, 4]`. -/
def beta324G : List ℕ :=
  [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 2, 1, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 1, 2, 3, 2, 1, 2,
   3, 2, 3]

/-- The same for the backward arm, which reaches index one. -/
def beta324T : List ℕ := [0, 0, 1, 0, 1]

set_option maxRecDepth 100000 in
/-- The forward arm of `hlSeq` at basepoint `5`, as far as index sixty-nine, folds onto the
walk of `[3, 2, 4]`. -/
theorem folds_324_armG :
    FoldsOnto (fun j : Fin 65 => hlSeq ⟨5 + j.val, by omega⟩)
      (zigWalk [3, 2, 4]).1 (zigWalk [3, 2, 4]).2 := by
  refine ⟨fun j => beta324G.getD j.val 0, ?_, ?_, ?_, ?_⟩ <;>
    simp only [zigWalk, zigLevels_324] <;> decide

/-- The backward arm, as far as index one, folds onto the same walk. -/
theorem folds_324_armT :
    FoldsOnto (fun j : Fin 5 => hlSeq ⟨5 - j.val, by omega⟩)
      (zigWalk [3, 2, 4]).1 (zigWalk [3, 2, 4]).2 := by
  refine ⟨fun j => beta324T.getD j.val 0, ?_, ?_, ?_, ?_⟩ <;>
    simp only [zigWalk, zigLevels_324] <;> decide

/-! ### The extensions -/

/-- The other order of the outer legs is not a member: the alternation fails at the join. -/
theorem not_isZigFree_232_15 : ¬ IsZigFree 0 6 [2, 3, 2, 1, 5] := by
  intro hh
  have := hh.alt 1 (by decide)
  norm_num at this

theorem not_isZigFree_324_51 : ¬ IsZigFree 0 6 [3, 2, 4, 5, 1] := by
  intro hh
  have := hh.alt 1 (by decide)
  norm_num at this

/-- Neither extension folds the whole backward arm at basepoint `5`: the arm is at level `0` at
index five, while the extension's centres are at `2` or above up to time five. This is batch
34's mechanism, `no_fold_of_low_early`. -/
theorem not_folds_232_51 :
    ¬ FoldsOnto (armT hlSeq ⟨5, by omega⟩) (zigWalk [2, 3, 2, 5, 1]).1
      (zigWalk [2, 3, 2, 5, 1]).2 := by
  have hlev : zigLevels [2, 3, 2, 5, 1] = [2, 3, 2, 3, 4, 5, 4, 3, 2, 1] := by
    simp [zigLevels, zigTail, stepRun]
  refine no_fold_of_low_early (v := 0) (d := ⟨5, by simp⟩) (by decide) ?_
  intro u hu
  simp only [zigWalk, hlev]
  simp only at hu
  interval_cases u <;> decide

theorem not_folds_324_15 :
    ¬ FoldsOnto (armT hlSeq ⟨5, by omega⟩) (zigWalk [3, 2, 4, 1, 5]).1
      (zigWalk [3, 2, 4, 1, 5]).2 := by
  have hlev : zigLevels [3, 2, 4, 1, 5] = [3, 2, 3, 4, 3, 2, 1, 2, 3, 4, 5] := by
    simp [zigLevels, zigTail, stepRun]
  refine no_fold_of_low_early (v := 0) (d := ⟨5, by simp⟩) (by decide) ?_
  intro u hu
  simp only [zigWalk, hlev]
  simp only at hu
  interval_cases u <;> decide

/-! ### The chain at the basepoint -/

theorem hlSeq_at_zero : hlSeq ⟨0, by omega⟩ = 0 := by decide

theorem hlSeq_at_three : hlSeq ⟨3, by omega⟩ = 1 := by decide

theorem hlSeq_at_four : hlSeq ⟨4, by omega⟩ = 2 := by decide

theorem hlSeq_at_five : hlSeq ⟨5, by omega⟩ = 3 := by decide

theorem hlSeq_at_six : hlSeq ⟨6, by omega⟩ = 2 := by decide

theorem hlSeq_at_seven : hlSeq ⟨7, by omega⟩ = 1 := by decide

theorem hlSeq_at_twentynine : hlSeq ⟨29, by omega⟩ = 5 := by decide

theorem hlSeq_at_seventy : hlSeq ⟨70, by omega⟩ = 6 := by decide

/-- **`ExtendStepMin` is false**, at basepoint `5` of `bing 0 6`. Only the bands `[1, 4]` and
`[1, 5]` carry an inner trim there; in each, the band's shortest member folds both arms of every
one of its stretches at that basepoint, and its only extension that is a member of the free
family of `[0, 6]` fails to fold the whole backward arm. -/
theorem not_extendStepMin : ¬ ExtendStepMin := by
  intro h
  obtain ⟨a, b, hai, hib, hbn, L', H', htrim, hstep⟩ :=
    h 71 hlSeq hlSeq ⟨5, by omega⟩ 6 0 hlSeq_isCrookedIvF (by decide) (by decide) (by norm_num)
      ⟨⟨0, by omega⟩, by decide⟩ ⟨⟨70, by omega⟩, by decide⟩ (by decide) (by decide)
  obtain ⟨-, -, -, hband, -, hattH, hL1, hH5, hwide⟩ := htrim
  have hai5 : a ≤ 5 := hai
  have hib5 : 5 ≤ b := hib
  have hcases : (L' = 1 ∧ H' = 4) ∨ (L' = 1 ∧ H' = 5) ∨ (L' = 2 ∧ H' = 5) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- the band `[1, 4]`: its shortest member is `[2, 3, 2]`
    have harmG : FoldsOnto (armG (fun j : Fin (b - a + 1) => hlSeq ⟨a + j.val, by omega⟩)
        ⟨5 - a, by omega⟩) (zigWalk [2, 3, 2]).1 (zigWalk [2, 3, 2]).2 := by
      refine foldsOnto_232_of_band ?_ ?_
      · intro j
        have hj : j.val < b - a + 1 - (5 - a) := j.isLt
        exact hband ⟨a + ((5 - a) + j.val), by omega⟩ (by simp) (by simp; omega)
      · intro j hj
        have hj0 : j.val = 0 := hj
        have e : (⟨a + ((5 - a) + j.val), by omega⟩ : Fin 71) = ⟨5, by omega⟩ :=
          Fin.ext (by simp [hj0]; omega)
        show hlSeq ⟨a + ((5 - a) + j.val), by omega⟩ ≤ 3
        rw [e, hlSeq_at_five]
    have harmT : FoldsOnto (armT (fun j : Fin (b - a + 1) => hlSeq ⟨a + j.val, by omega⟩)
        ⟨5 - a, by omega⟩) (zigWalk [2, 3, 2]).1 (zigWalk [2, 3, 2]).2 := by
      refine foldsOnto_232_of_band ?_ ?_
      · intro j
        have hj : j.val < (5 - a) + 1 := j.isLt
        exact hband ⟨a + ((5 - a) - j.val), by omega⟩ (by simp) (by simp; omega)
      · intro j hj
        have hj0 : j.val = 0 := hj
        have e : (⟨a + ((5 - a) - j.val), by omega⟩ : Fin 71) = ⟨5, by omega⟩ :=
          Fin.ext (by simp [hj0]; omega)
        show hlSeq ⟨a + ((5 - a) - j.val), by omega⟩ ≤ 3
        rw [e, hlSeq_at_five]
    have hmin : ∀ ts' : List ℤ, IsZigFree 1 4 ts' →
        FoldsOnto (armG (fun j : Fin (b - a + 1) => hlSeq ⟨a + j.val, by omega⟩)
          ⟨5 - a, by omega⟩) (zigWalk ts').1 (zigWalk ts').2 →
        FoldsOnto (armT (fun j : Fin (b - a + 1) => hlSeq ⟨a + j.val, by omega⟩)
          ⟨5 - a, by omega⟩) (zigWalk ts').1 (zigWalk ts').2 →
        (zigWalk [2, 3, 2]).1 ≤ (zigWalk ts').1 := by
      intro ts' hts' _ _
      rw [zigWalk_232_length]
      have := zigWalk_length_ge hts'
      omega
    obtain ⟨x, y, hxy, hmem, -, hfT⟩ := hstep [2, 3, 2] isZigFree_232 harmG harmT hmin
    rcases hxy with he | he <;> rw [Prod.mk.injEq] at he <;> obtain ⟨rfl, rfl⟩ := he
    · refine not_isZigFree_232_15 ?_
      have e : [(2 : ℤ), 3, 2] ++ [(0 : ℤ) + 1, (6 : ℤ) - 1] = [2, 3, 2, 1, 5] := by norm_num
      rw [e] at hmem
      exact hmem
    · refine not_folds_232_51 ?_
      have e : [(2 : ℤ), 3, 2] ++ [(6 : ℤ) - 1, (0 : ℤ) + 1] = [2, 3, 2, 5, 1] := by norm_num
      rw [e] at hfT
      exact hfT
  · -- the band `[1, 5]`: its shortest member is `[3, 2, 4]`
    have ha1 : 1 ≤ a := by
      by_contra hc
      have h0 := (hband ⟨0, by omega⟩ (show a ≤ 0 by omega) (show 0 ≤ b by omega)).1
      rw [hlSeq_at_zero] at h0
      omega
    have hb69 : b ≤ 69 := by
      by_contra hc
      have h0 := (hband ⟨70, by omega⟩ (show a ≤ 70 by omega) (show 70 ≤ b by omega)).2
      rw [hlSeq_at_seventy] at h0
      omega
    have harmG : FoldsOnto (armG (fun j : Fin (b - a + 1) => hlSeq ⟨a + j.val, by omega⟩)
        ⟨5 - a, by omega⟩) (zigWalk [3, 2, 4]).1 (zigWalk [3, 2, 4]).2 := by
      refine foldsOnto_restrict (f := fun j : Fin 65 => hlSeq ⟨5 + j.val, by omega⟩)
        (show b - a + 1 - (5 - a) ≤ 65 by omega) ?_ folds_324_armG
      intro j
      have hj : j.val < b - a + 1 - (5 - a) := j.isLt
      show hlSeq ⟨a + ((5 - a) + j.val), by omega⟩ = hlSeq ⟨5 + j.val, by omega⟩
      congr 1
      exact Fin.ext (by simp; omega)
    have harmT : FoldsOnto (armT (fun j : Fin (b - a + 1) => hlSeq ⟨a + j.val, by omega⟩)
        ⟨5 - a, by omega⟩) (zigWalk [3, 2, 4]).1 (zigWalk [3, 2, 4]).2 := by
      refine foldsOnto_restrict (f := fun j : Fin 5 => hlSeq ⟨5 - j.val, by omega⟩)
        (show (5 - a) + 1 ≤ 5 by omega) ?_ folds_324_armT
      intro j
      have hj : j.val < (5 - a) + 1 := j.isLt
      show hlSeq ⟨a + ((5 - a) - j.val), by omega⟩ = hlSeq ⟨5 - j.val, by omega⟩
      congr 1
      exact Fin.ext (by simp; omega)
    have hmin : ∀ ts' : List ℤ, IsZigFree 1 5 ts' →
        FoldsOnto (armG (fun j : Fin (b - a + 1) => hlSeq ⟨a + j.val, by omega⟩)
          ⟨5 - a, by omega⟩) (zigWalk ts').1 (zigWalk ts').2 →
        FoldsOnto (armT (fun j : Fin (b - a + 1) => hlSeq ⟨a + j.val, by omega⟩)
          ⟨5 - a, by omega⟩) (zigWalk ts').1 (zigWalk ts').2 →
        (zigWalk [3, 2, 4]).1 ≤ (zigWalk ts').1 := by
      intro ts' hts' _ _
      rw [zigWalk_324_length]
      have := zigWalk_length_ge hts'
      omega
    obtain ⟨x, y, hxy, hmem, -, hfT⟩ := hstep [3, 2, 4] isZigFree_324 harmG harmT hmin
    rcases hxy with he | he <;> rw [Prod.mk.injEq] at he <;> obtain ⟨rfl, rfl⟩ := he
    · refine not_folds_324_15 ?_
      have e : [(3 : ℤ), 2, 4] ++ [(0 : ℤ) + 1, (6 : ℤ) - 1] = [3, 2, 4, 1, 5] := by norm_num
      rw [e] at hfT
      exact hfT
    · refine not_isZigFree_324_51 ?_
      have e : [(3 : ℤ), 2, 4] ++ [(6 : ℤ) - 1, (0 : ℤ) + 1] = [3, 2, 4, 5, 1] := by norm_num
      rw [e] at hmem
      exact hmem
  · -- the band `[2, 5]` carries no trim at this basepoint
    have ha4 : 4 ≤ a := by
      by_contra hc
      have h0 := (hband ⟨3, by omega⟩ (show a ≤ 3 by omega) (show 3 ≤ b by omega)).1
      rw [hlSeq_at_three] at h0
      omega
    have hb6 : b ≤ 6 := by
      by_contra hc
      have h0 := (hband ⟨7, by omega⟩ (show a ≤ 7 by omega) (show 7 ≤ b by omega)).1
      rw [hlSeq_at_seven] at h0
      omega
    obtain ⟨j, hj1, hj2, hj3⟩ := hattH
    have hj : j = (⟨4, by omega⟩ : Fin 71) ∨ j = ⟨5, by omega⟩ ∨ j = ⟨6, by omega⟩ := by
      rcases (show j.val = 4 ∨ j.val = 5 ∨ j.val = 6 by omega) with hv | hv | hv
      exacts [Or.inl (Fin.ext hv), Or.inr (Or.inl (Fin.ext hv)), Or.inr (Or.inr (Fin.ext hv))]
    rcases hj with hv | hv | hv
    · rw [hv, hlSeq_at_four] at hj3; omega
    · rw [hv, hlSeq_at_five] at hj3; omega
    · rw [hv, hlSeq_at_six] at hj3; omega

-- Commented-out statement `ExtendStepMin`, `extendStepMin` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
