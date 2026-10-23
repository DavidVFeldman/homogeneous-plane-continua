import HPC.Fold.Recon87End
import HPC.Chains.Schedule

/-!
# Batch 87: Lean-checked census in the faithful model

Part of the batch-87 census, redone in Lean with a completeness proof for the enumeration.

* `gen K n` lists every sequence of `n` coarse intervals `[ρ, σ]` with `0 ≤ ρ ≤ σ ≤ ρ + 1 < K + 1`,
  `σ < K`, satisfying the adjacency clause of `IsCrookedIvF`; `mem_gen` proves that every such
  sequence is listed.
* A fold search (`foldSearch`) proposes a time function; a decidable certificate checks it, and
  `CertT3.toModel` / `CertF3.toModel` turn a checked certificate into the model statements.
* The finite checks over `gen K n` are run by `native_decide`.
-/

namespace HPC.Fold.Census87

open HPC.Chain

/-! ## Enumeration -/

/-- The admissible coarse intervals over `K` coarse links. -/
def cells (K : ℕ) : List (ℤ × ℤ) :=
  List.flatMap (fun (r : ℕ) => ((r : ℤ), (r : ℤ)) ::
    (if r + 1 < K then [((r : ℤ), (r : ℤ) + 1)] else [])) (List.range K)

/-- The adjacency clause of `IsCrookedIvF` for two neighbouring intervals. -/
def adjOK (x y : ℤ × ℤ) : Bool := decide (max x.2 y.2 ≤ min x.1 y.1 + 1)

/-- All adjacency-respecting sequences of `n` admissible intervals (built from the right). -/
def gen (K : ℕ) : ℕ → List (List (ℤ × ℤ))
  | 0 => [[]]
  | n + 1 => (gen K n).flatMap fun l =>
      ((cells K).filter fun c => match l with
        | [] => true
        | y :: _ => adjOK c y).map (· :: l)

theorem mem_cells {K : ℕ} {r s : ℤ} (h0 : 0 ≤ r) (hrs : r ≤ s) (hsr : s ≤ r + 1)
    (hsK : s < K) : (r, s) ∈ cells K := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  simp only [cells, List.mem_flatMap, List.mem_range]
  refine ⟨m, by omega, ?_⟩
  rcases (show s = m ∨ s = (m : ℤ) + 1 by omega) with rfl | rfl
  · simp
  · have : m + 1 < K := by omega
    simp [this]

theorem mem_gen {K : ℕ} : ∀ (n : ℕ) (l : List (ℤ × ℤ)), l.length = n →
    (∀ x ∈ l, x ∈ cells K) → l.IsChain (fun x y => adjOK x y = true) → l ∈ gen K n := by
  intro n
  induction n with
  | zero =>
    intro l hl _ _
    rw [List.length_eq_zero_iff] at hl
    subst hl; simp [gen]
  | succ n ih =>
    intro l hl hc hch
    obtain ⟨x, l', rfl⟩ : ∃ x l', l = x :: l' := by
      cases l with
      | nil => simp at hl
      | cons x l' => exact ⟨x, l', rfl⟩
    have hl' : l'.length = n := by simpa using hl
    have hch' : l'.IsChain (fun x y => adjOK x y = true) := hch.tail
    have ih' := ih l' hl' (fun y hy => hc y (List.mem_cons_of_mem _ hy)) hch'
    simp only [gen, List.mem_flatMap, List.mem_map, List.mem_filter]
    refine ⟨l', ih', x, ⟨hc x (List.mem_cons_self), ?_⟩, rfl⟩
    cases l' with
    | nil => rfl
    | cons y l'' => exact (List.isChain_cons_cons.mp hch).1

/-- The sequence read from a list. -/
def rhoOf (l : List (ℤ × ℤ)) (n : ℕ) : Fin n → ℤ := fun t => (l.getD t.val (0, 0)).1
/-- The upper ends read from a list. -/
def sigOf (l : List (ℤ × ℤ)) (n : ℕ) : Fin n → ℤ := fun t => (l.getD t.val (0, 0)).2

theorem ofFn_mem_gen {K n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ) (h0 : ∀ t, 0 ≤ ρ t)
    (hK : ∀ t, σ t < K) : List.ofFn (fun t => (ρ t, σ t)) ∈ gen K n := by
  refine mem_gen n _ (by simp) ?_ ?_
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact mem_cells (h0 i) (hf.le i) (hf.width i) (hK i)
  · rw [List.isChain_ofFn]
    intro i hi
    simpa [adjOK] using hf.adj ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl

theorem rhoOf_ofFn {n : ℕ} (ρ σ : Fin n → ℤ) :
    rhoOf (List.ofFn (fun t => (ρ t, σ t))) n = ρ := by
  funext t
  have ht : t.val < (List.ofFn (fun t => (ρ t, σ t))).length := by simp
  rw [rhoOf, List.getD_eq_getElem _ _ ht]; simp

theorem sigOf_ofFn {n : ℕ} (ρ σ : Fin n → ℤ) :
    sigOf (List.ofFn (fun t => (ρ t, σ t))) n = σ := by
  funext t
  have ht : t.val < (List.ofFn (fun t => (ρ t, σ t))).length := by simp
  rw [sigOf, List.getD_eq_getElem _ _ ht]; simp

theorem check_of_crooked {n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ) :
    IsCrookedIvFCheck ρ σ := by
  refine ⟨hf.le, hf.width, hf.adj, ?_⟩
  intro s t hst u v hu hv b b' habs
  have hb : ∀ (c : Bool) (w : Fin n), ρ w ≤ ivEnd ρ σ c w ∧ ivEnd ρ σ c w ≤ σ w := by
    intro c w; have := hf.le w; cases c <;> simp [ivEnd, this]
  exact hf.crooked s t hst _ _ ⟨u, hu, hb b u⟩ ⟨v, hv, hb b' v⟩ habs

/-! ## From a checked time function to a block map -/

/-- A `1`-Lipschitz time function attaining `0`, whose fibres satisfy the pairwise three-link
window condition, is a three-link block map; its maximal time is `p - 1`. -/
theorem exists_blockMap_of_times {n : ℕ} {ρ σ : Fin n → ℤ} (bt : Fin n → ℕ)
    (hlip : ∀ t t' : Fin n, t'.val = t.val + 1 → ((bt t' : ℤ) - (bt t : ℤ)).natAbs ≤ 1)
    (hzero : ∃ t, bt t = 0) (hwin : ∀ t t', bt t = bt t' → ρ t ≤ σ t' + 2) :
    ∃ p, ∃ β : Fin n → Fin p, IsBlockMap β ∧ (∀ t, (β t).val = bt t) ∧
      (∀ u, ∃ j : ℤ, ∀ t, β t = u → j ≤ σ t ∧ ρ t ≤ j + 2) ∧
      (∀ t, (β t).val = p - 1 ↔ ∀ t', bt t' ≤ bt t) := by
  classical
  obtain ⟨p, β, hβ, hv⟩ := (IsSchedule.mk hlip hzero).exists_blockMap
  refine ⟨p, β, hβ, hv, fun u => ?_, fun t => ?_⟩
  · by_cases hne : (Finset.univ.filter fun t => β t = u).Nonempty
    · obtain ⟨t0, ht0, hmin⟩ := Finset.exists_min_image _ σ hne
      have ht0' : β t0 = u := (Finset.mem_filter.mp ht0).2
      refine ⟨σ t0, fun t ht => ⟨hmin t (by simp [ht]), hwin t t0 ?_⟩⟩
      rw [← hv, ← hv, ht, ht0']
    · refine ⟨0, fun t ht => absurd ⟨t, by simp [ht]⟩ hne⟩
  · constructor
    · intro h t'
      rw [← hv, ← hv, h]
      have := (β t').isLt
      omega
    · intro h
      have hp : 0 < p := Fin.pos (β t)
      obtain ⟨t'', ht''⟩ := hβ.surj ⟨p - 1, by omega⟩
      have h1 := h t''
      rw [← hv, ← hv, ht''] at h1
      have := (β t).isLt
      simp only at h1
      omega

/-! ## The model statements checked here -/

/-- Link `t` meets coarse level `j` through a neighbour (the forced meetings of the model). -/
def MeetsLevel {n : ℕ} (ρ σ : Fin n → ℤ) (t : Fin n) (j : ℤ) : Prop :=
  ∃ u : Fin n, ((u : ℤ) - t).natAbs ≤ 1 ∧ ρ u ≤ j ∧ j ≤ σ u

/-- **The model reading of `theorem3_end`** (the statement decided by the census class `T3END`):
a three-link block map with basepoint `i` at time `0`, and, for each end link meeting coarse level
`0` (resp. `K - 1`), every member of its block has `ρ ≤ 2` (resp. `σ ≥ K - 3`). -/
def ModelT3End {n : ℕ} (ρ σ : Fin n → ℤ) (K : ℤ) (i : Fin n) : Prop :=
  ∃ q, ∃ β : Fin n → Fin q, IsBlockMap β ∧
    (∀ u, ∃ j : ℤ, ∀ t, β t = u → j ≤ σ t ∧ ρ t ≤ j + 2) ∧ (β i).val = 0 ∧
    ∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
      (MeetsLevel ρ σ t 0 → ∀ t', β t' = β t → ρ t' ≤ 2) ∧
      (MeetsLevel ρ σ t (K - 1) → ∀ t', β t' = β t → K - 3 ≤ σ t')

/-- The decidable certificate for `ModelT3End`, on a time function. -/
def CertT3 {n : ℕ} (ρ σ : Fin n → ℤ) (K : ℤ) (i : Fin n) (bt : Fin n → ℕ) : Prop :=
  (∀ t t' : Fin n, t'.val = t.val + 1 → ((bt t' : ℤ) - (bt t : ℤ)).natAbs ≤ 1) ∧ bt i = 0 ∧
  (∀ t t', bt t = bt t' → ρ t ≤ σ t' + 2) ∧
  ∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
    (MeetsLevel ρ σ t 0 → ∀ t', bt t' = bt t → ρ t' ≤ 2) ∧
    (MeetsLevel ρ σ t (K - 1) → ∀ t', bt t' = bt t → K - 3 ≤ σ t')

theorem CertT3.toModel {n : ℕ} {ρ σ : Fin n → ℤ} {K : ℤ} {i : Fin n} {bt : Fin n → ℕ}
    (h : CertT3 ρ σ K i bt) : ModelT3End ρ σ K i := by
  obtain ⟨hlip, hi, hwin, hend⟩ := h
  obtain ⟨p, β, hβ, hv, hsm, -⟩ := exists_blockMap_of_times (ρ := ρ) (σ := σ) bt hlip ⟨i, hi⟩ hwin
  have heq : ∀ t t', β t' = β t → bt t' = bt t := fun t t' h => by rw [← hv, ← hv, h]
  refine ⟨p, β, hβ, hsm, by rw [hv, hi], fun t ht => ⟨fun hm t' h' => ?_, fun hm t' h' => ?_⟩⟩
  · exact (hend t ht).1 hm t' (heq t t' h')
  · exact (hend t ht).2 hm t' (heq t t' h')

/-- The decidable certificate for the three-link time-ordering fold, on a time function:
basepoint `a` at `0`, `q` at the maximal time, every link of `[lo, hi]` at a time `≤` that of
`c`. -/
def CertF3 {n : ℕ} (ρ σ : Fin n → ℤ) (a c q lo hi : Fin n) (bt : Fin n → ℕ) : Prop :=
  (∀ t t' : Fin n, t'.val = t.val + 1 → ((bt t' : ℤ) - (bt t : ℤ)).natAbs ≤ 1) ∧ bt a = 0 ∧
  (∀ t t', bt t = bt t' → ρ t ≤ σ t' + 2) ∧ (∀ t, bt t ≤ bt q) ∧
  (∀ t : Fin n, lo ≤ t → t ≤ hi → bt t ≤ bt c)

theorem CertF3.toModel {n : ℕ} {ρ σ : Fin n → ℤ} {a c q lo hi : Fin n} {bt : Fin n → ℕ}
    (h : CertF3 ρ σ a c q lo hi bt) :
    ModelCoveringFold₃ ρ σ {a} {c} {q} (Finset.Icc lo hi) := by
  obtain ⟨hlip, ha, hwin, hmax, hI⟩ := h
  obtain ⟨p, β, hβ, hv, hsm, hiff⟩ :=
    exists_blockMap_of_times (ρ := ρ) (σ := σ) bt hlip ⟨a, ha⟩ hwin
  refine ⟨p, β, β c, hβ, hsm, ?_, ?_, ?_, ?_⟩
  · intro t ht; rw [Finset.mem_singleton.mp ht, hv, ha]
  · intro t ht; rw [Finset.mem_singleton.mp ht]; exact (hiff q).mpr hmax
  · intro t ht; rw [Finset.mem_singleton.mp ht]
  · intro t ht
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ht
    rw [Fin.le_def, hv, hv]; exact hI t h1 h2

/-! ## The search and the finite checks -/

set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 400000 in
instance instDecCrookedCheck {n : ℕ} (ρ σ : Fin n → ℤ) : Decidable (IsCrookedIvFCheck ρ σ) := by
  unfold IsCrookedIvFCheck; infer_instance

instance instDecMeetsLevel {n : ℕ} (ρ σ : Fin n → ℤ) (t : Fin n) (j : ℤ) :
    Decidable (MeetsLevel ρ σ t j) := by
  unfold MeetsLevel; infer_instance

instance instDecCertT3 {n : ℕ} (ρ σ : Fin n → ℤ) (K : ℤ) (i : Fin n) (bt : Fin n → ℕ) :
    Decidable (CertT3 ρ σ K i bt) := by
  unfold CertT3; infer_instance

instance instDecCertF3 {n : ℕ} (ρ σ : Fin n → ℤ) (a c q lo hi : Fin n) (bt : Fin n → ℕ) :
    Decidable (CertF3 ρ σ a c q lo hi bt) := by
  unfold CertF3; infer_instance

/-- Depth-first search for a time function. `order` lists `(t, prev)`: link `t` is given a time
within one of the time of `prev`; `ok t t'` is the pairwise condition for two links in one block;
the first complete assignment accepted by `final` is returned. Only its output is trusted, and
only through `final`. -/
def foldSearch (ok : ℕ → ℕ → Bool) (final : Array ℕ → Bool) :
    List (ℕ × ℕ) → Array ℕ → List ℕ → Option (Array ℕ)
  | [], b, _ => if final b then some b else none
  | (t, p) :: rest, b, asg =>
    let v := b.getD p 0
    ((if v = 0 then [] else [v - 1]) ++ [v, v + 1]).findSome? fun u =>
      if asg.all (fun t' => b.getD t' 0 != u || ok t t') then
        foldSearch ok final rest (b.set! t u) (t :: asg)
      else none

/-- The sweep from basepoint `i`: rightwards, then leftwards. -/
def sweep (n i : ℕ) : List (ℕ × ℕ) :=
  ((List.range n).filter (fun t => i < t)).map (fun t => (t, t - 1)) ++
  ((List.range n).reverse.filter (fun t => t < i)).map (fun t => (t, t + 1))

/-- The time function read from an array. -/
def timesOf (b : Array ℕ) (n : ℕ) : Fin n → ℕ := fun t => b.getD t.val 0

/-- Lower end of link `t` of a list (indices in `ℕ`). -/
def rN (l : List (ℤ × ℤ)) (t : ℕ) : ℤ := (l.getD t (0, 0)).1
/-- Upper end of link `t` of a list. -/
def sN (l : List (ℤ × ℤ)) (t : ℕ) : ℤ := (l.getD t (0, 0)).2

/-- Pairwise three-link window, in both orders. -/
def winOK (l : List (ℤ × ℤ)) (t t' : ℕ) : Bool :=
  decide (rN l t ≤ sN l t' + 2) && decide (rN l t' ≤ sN l t + 2)

/-- The certificate check for `ModelT3End` at basepoint `i`. -/
def certT3OK (K n : ℕ) (l : List (ℤ × ℤ)) (i : Fin n) : Bool :=
  let final := fun b => decide (CertT3 (rhoOf l n) (sigOf l n) K i (timesOf b n))
  match foldSearch (winOK l) final (sweep n i) (Array.replicate n 0) [i.val] with
  | some b => final b
  | none => false

theorem certT3OK_sound {K n : ℕ} {l : List (ℤ × ℤ)} {i : Fin n} (h : certT3OK K n l i = true) :
    ∃ bt, CertT3 (rhoOf l n) (sigOf l n) K i bt := by
  unfold certT3OK at h
  dsimp only at h
  generalize foldSearch _ _ _ _ _ = r at h
  cases r with
  | some b => exact ⟨_, of_decide_eq_true h⟩
  | none => exact absurd h (by simp)

/-- The finite check behind `ModelT3End`: every basepoint of a crooked sequence has a certificate. -/
def checkT3 (K n : ℕ) (l : List (ℤ × ℤ)) : Bool :=
  !decide (IsCrookedIvFCheck (rhoOf l n) (sigOf l n)) || (List.finRange n).all (certT3OK K n l)

theorem modelT3End_of_check {K n : ℕ} (h : (gen K n).all (checkT3 K n) = true)
    {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ) (h0 : ∀ t, 0 ≤ ρ t) (hK : ∀ t, σ t < K)
    (i : Fin n) : ModelT3End ρ σ K i := by
  have hl := List.all_eq_true.mp h _ (ofFn_mem_gen hf h0 hK)
  have hc : decide (IsCrookedIvFCheck (rhoOf (List.ofFn fun t => (ρ t, σ t)) n)
      (sigOf (List.ofFn fun t => (ρ t, σ t)) n)) = true := by
    rw [rhoOf_ofFn, sigOf_ofFn]; exact decide_eq_true (check_of_crooked hf)
  simp only [checkT3, hc, Bool.not_true, Bool.false_or, List.all_eq_true] at hl
  obtain ⟨bt, hbt⟩ := certT3OK_sound (hl i (List.mem_finRange i))
  rw [rhoOf_ofFn, sigOf_ofFn] at hbt
  exact hbt.toModel

/-- The certificate check for the three-link fold. -/
def certF3OK (n : ℕ) (l : List (ℤ × ℤ)) (a c q lo hi : Fin n) : Bool :=
  let final := fun b => decide (CertF3 (rhoOf l n) (sigOf l n) a c q lo hi (timesOf b n))
  match foldSearch (winOK l) final (sweep n a) (Array.replicate n 0) [a.val] with
  | some b => final b
  | none => false

theorem certF3OK_sound {n : ℕ} {l : List (ℤ × ℤ)} {a c q lo hi : Fin n}
    (h : certF3OK n l a c q lo hi = true) :
    ∃ bt, CertF3 (rhoOf l n) (sigOf l n) a c q lo hi bt := by
  unfold certF3OK at h
  dsimp only at h
  generalize foldSearch _ _ _ _ _ = r at h
  cases r with
  | some b => exact ⟨_, of_decide_eq_true h⟩
  | none => exact absurd h (by simp)

/-- The window property, in decidable form. -/
def WindowD {n : ℕ} (ρ σ : Fin n → ℤ) (a c lo hi : Fin n) : Prop :=
  ∀ u : Fin n, lo ≤ u → u ≤ hi → ∃ v : Fin n, min a c ≤ v ∧ v ≤ max a c ∧
    max (ρ u) (ρ v) ≤ min (σ u) (σ v)

/-- `S2`, in decidable form. -/
def FarD {n : ℕ} (ρ σ : Fin n → ℤ) (q lo hi : Fin n) : Prop :=
  ∀ t : Fin n, lo ≤ t → t ≤ hi → 3 ≤ levelGap ρ σ t q

instance instDecWindowD {n : ℕ} (ρ σ : Fin n → ℤ) (a c lo hi : Fin n) :
    Decidable (WindowD ρ σ a c lo hi) := by
  unfold WindowD; infer_instance

instance instDecFarD {n : ℕ} (ρ σ : Fin n → ℤ) (q lo hi : Fin n) :
    Decidable (FarD ρ σ q lo hi) := by
  unfold FarD levelGap; infer_instance

/-- The finite check behind the three-link fold under `S2`. -/
def checkF3 (n : ℕ) (l : List (ℤ × ℤ)) : Bool :=
  !decide (IsCrookedIvFCheck (rhoOf l n) (sigOf l n)) ||
  (List.finRange n).all fun q => (List.finRange n).all fun lo => (List.finRange n).all fun hi =>
    if decide (¬ (lo ≤ q ∧ q ≤ hi) ∧ FarD (rhoOf l n) (sigOf l n) q lo hi) then
      (List.finRange n).all fun a => (List.finRange n).all fun c =>
        if decide (a ≠ c ∧ lo ≤ a ∧ a ≤ hi ∧ lo ≤ c ∧ c ≤ hi ∧
            WindowD (rhoOf l n) (sigOf l n) a c lo hi) then certF3OK n l a c q lo hi
        else true
    else true

theorem fold3_of_check {K n : ℕ} (h : (gen K n).all (checkF3 n) = true)
    {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ) (h0 : ∀ t, 0 ≤ ρ t) (hK : ∀ t, σ t < K)
    {a c q lo hi : Fin n} (hac : a ≠ c) (ha : lo ≤ a ∧ a ≤ hi) (hc : lo ≤ c ∧ c ≤ hi)
    (hq : ¬ (lo ≤ q ∧ q ≤ hi))
    (hw : ModelWindow ρ σ (min a c) (max a c) (Finset.Icc lo hi))
    (hfar : ModelFar ρ σ q (Finset.Icc lo hi)) :
    ModelCoveringFold₃ ρ σ {a} {c} {q} (Finset.Icc lo hi) := by
  have hl := List.all_eq_true.mp h _ (ofFn_mem_gen hf h0 hK)
  have hc' : decide (IsCrookedIvFCheck (rhoOf (List.ofFn fun t => (ρ t, σ t)) n)
      (sigOf (List.ofFn fun t => (ρ t, σ t)) n)) = true := by
    rw [rhoOf_ofFn, sigOf_ofFn]; exact decide_eq_true (check_of_crooked hf)
  simp only [checkF3, hc', Bool.not_true, Bool.false_or, List.all_eq_true] at hl
  have h1 := hl q (List.mem_finRange q) lo (List.mem_finRange lo) hi (List.mem_finRange hi)
  rw [rhoOf_ofFn, sigOf_ofFn] at h1
  have hF : FarD ρ σ q lo hi := fun t h1 h2 => hfar t (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  rw [if_pos (decide_eq_true ⟨hq, hF⟩), List.all_eq_true] at h1
  have h2 := List.all_eq_true.mp (h1 a (List.mem_finRange a)) c (List.mem_finRange c)
  have hW : WindowD ρ σ a c lo hi := by
    intro u h1 h2
    obtain ⟨v, hv1, hv2, s, hs1, hs2, hs3, hs4⟩ := hw u (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    exact ⟨v, hv1, hv2, max_le (by omega) (by omega)⟩
  rw [if_pos (decide_eq_true ⟨hac, ha.1, ha.2, hc.1, hc.2, hW⟩)] at h2
  obtain ⟨bt, hbt⟩ := certF3OK_sound h2
  rw [rhoOf_ofFn, sigOf_ofFn] at hbt
  exact hbt.toModel

end HPC.Fold.Census87
