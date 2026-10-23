import HPC.Fold.Span

/-!
# A counterexample to `F2PrimeOff` at span ten

Batch 25 scored `OffDichotomy` on `bing 0 10` but scored `F2PrimeOff` itself only through
`bing 0 9`. Scored on all 2 379 basepoints of `bing 0 10` it fails, at eight of them — 343,
347, 349, 351, 2027, 2029, 2031, 2035, all of level five. This file proves the failure at the
first of them, basepoint `343`, so the one-bump family of batch 24 is refuted and the repair
batch 25 proposed — keep the family, restore the free peak and valley — is not available.

The failure is thirty instances of `¬ FoldsOnto`, one for each member of the family with
`c₀ ∈ {4, 5, 6}`: six Λ-ladders and four V-ladders at `c₀ = 4`, five and five at `c₀ = 5`,
four and six at `c₀ = 6`. Each is certified by forward reachability: the set of times a fold
could occupy at a given link is propagated along the arm as a bitmask, and the certificate is
that it becomes empty. `not_foldsOnto_of_reachUpto` is the soundness of that propagation, and
is general: it refutes folding onto any walk, from any arm.

The chain is carried as one natural number in base sixteen, as in
`HPC/Fold/DichotomyFaithful.lean`, so a link costs a shift and a mask. Reachability dies within
343 links on every one of the thirty members — on the V-ladders with `l = 2` exactly at the
backward arm's last link, which is the near-miss the commission describes — so one bound
serves for all.

`IsCrookedIvF ceSeq10 ceSeq10` is an explicit hypothesis of `not_f2PrimeOff_of_faithful`, as
in batch 25's first form of its refutation. The far-index check of
`HPC/Fold/DichotomyFaithful.lean` discharges the same hypothesis for the 409-link chain in a
few minutes, but at 2 379 links it exhausted the machine's memory; REPORT-batch26.md §2
records the numbers and what a feasible check would have to look like. The chain is Bing's
`bing 0 10` — `ce10_eq_bingPath` — and the check has been run outside Lean, where it
passes.
-/

namespace HPC.Fold

/-! ## The chain as a numeral -/

/-- Bing's chain `bing 0 10`: the 2 379 links of the recursive construction from level `0` to
level `10`, as the base-sixteen digits of one natural number. -/
def ce10Nat : ℕ := 264523245095285394519027183581010909285922698245035763513624125742215148228732588826582752140672998124184822476882055984794103118453737787324509751987467074834262940023391968350702562226792859720945725220030657405950315757145868428455998533844053751826311488999590474771946532279577738472732761203178159063035921714304946798604603459220380308006663843646681204987529345823679921205387777568012234467244385061426512856257848871495217365766826638854953916886175967012970071294015545204409818411700785723132737820695986806123174172752214109335547338174912868288612816354622604040825505268119572382946115823964170293781503025546410555298753159253465666822198358098268485138920256392817855001995364001545978696191560166454242032346320917973556248782357316690436137233919820847384259596401598545697316806237569439805887728414460656368563935874445171648347396866917451535338321762824555825413327191900625080469833158073965218622232939197363712487567460665091718880242433709244366582354664977248428709982405830368338890342772491013268846099151906401529984734110612739679893800932932166074770307711962438558418525452559407208802929551081731128247190987193692972385473405860874841027082491286660225758964988849992378070711048454683899414331610865800633660340830679759938386690207799549460805117384086113651035858643098932468312771383769854190877229017544162869970571219272495463804066919570254921491616409103598654636690125099403651397522303696667350516022717532568107068895094903186505896936999374037503737537491821617064344827692087390024097532619056859894819691611241733773805618681426573650558424394945545215239528503797780271952801775228413618593448891733968442571297949298191458060600676577798694004996972514836875235688288961255376606198015273301156052973856042071538871203182007249564154512219478619603251074519781301426448480402018663640357330980830772024957925807572897204294917380557652331038464157690954103348291072057071529464745235235357021763666336522516586364035199850337233927915684976298141704561418493561374228495060338042550344067894035399103219721434028994272361494579573185408087757665449701508076679566173141724983779397232599989369862604107023307817370736929382426715235961197103210715012117374767766813048300375780435099275110657509607881719606719476120348961257312526529786485698841780556277775005694458486466645604110806840317396755372381085225077183756656257599787444828497748379052207681751745527021496814556325101851403059703136265442870974159049677207237539281387942336484496063464592140295654756394207160099556481558558395505001477860675359686892236002020995745424865915150097910306857754155006641444229440284698186098604076025150731980795030410358737467914219208711711406845342401579959698557285476321800920326018310299020878176791011804935153482841024873857634482281066463351189479752160080115310861751808311792276161043994352533584340980240

/-- Reading a link off the numeral. -/
def rho10 (i : ℕ) : ℕ := (ce10Nat >>> (4 * i)) &&& 15

/-- The chain, as a sequence. -/
def ceSeq10 : Fin 2379 → ℤ := fun t => (rho10 t.val : ℤ)

/-- The basepoint: index `343`, of level five. -/
def ceBase10 : Fin 2379 := ⟨343, by norm_num⟩

@[simp] theorem ceBase10_val : ceBase10.val = 343 := rfl

/-- A linear check for the Lipschitz condition: one comparison per link. -/
def lipCheck10 : Bool :=
  (List.range 2378).all fun k => decide (|(rho10 (k + 1) : ℤ) - (rho10 k : ℤ)| ≤ 1)

set_option maxRecDepth 100000 in
theorem lipCheck10_true : lipCheck10 = true := by decide +kernel

/-- A linear check for the upper bound. -/
def ubCheck10 : Bool := (List.range 2379).all fun k => decide (rho10 k ≤ 10)

set_option maxRecDepth 100000 in
theorem ubCheck10_true : ubCheck10 = true := by decide +kernel

theorem ceSeq10_isLip : IsLip ceSeq10 := by
  intro j j' hjj'
  have h := lipCheck10_true
  rw [lipCheck10, List.all_eq_true] at h
  have hj : j.val < 2378 := by have := j'.isLt; omega
  have := h j.val (List.mem_range.2 hj)
  simp only [decide_eq_true_eq] at this
  show |(rho10 j'.val : ℤ) - (rho10 j.val : ℤ)| ≤ 1
  rwa [hjj']

theorem ceSeq10_lb : ∀ t, (0 : ℤ) ≤ ceSeq10 t := fun _ => Int.natCast_nonneg _

theorem ceSeq10_ub : ∀ t, ceSeq10 t ≤ 10 := by
  intro t
  have h := ubCheck10_true
  rw [ubCheck10, List.all_eq_true] at h
  have := h t.val (List.mem_range.2 t.isLt)
  simp only [decide_eq_true_eq] at this
  show (rho10 t.val : ℤ) ≤ 10
  exact_mod_cast this

set_option maxRecDepth 10000 in
theorem ceSeq10_attains_bot : ∃ t, ceSeq10 t = 0 := ⟨⟨0, by norm_num⟩, by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem ceSeq10_attains_top : ∃ t, ceSeq10 t = 10 := ⟨⟨2378, by norm_num⟩, by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem ceSeq10_base : ceSeq10 ceBase10 = 5 := by decide +kernel

/-! ## Refuting a fold by forward reachability

A fold is a Lipschitz time-assignment; the set of times it could occupy at a link is obtained
from the set at the previous link by one step in either direction, intersected with the times
whose centre is within one of the level. If that set is ever empty there is no fold. The set
is a bitmask, so a link costs three shifts and two masks.
-/

/-- The times `u < len` whose centre `c u` is within one of `v`, as a bitmask. -/
def winMask (c : ℕ → ℤ) : ℕ → ℤ → ℕ
  | 0, _ => 0
  | len + 1, v => winMask c len v ||| (if |v - c len| ≤ 1 then 1 <<< len else 0)

/-- One link of the propagation. -/
def reachStep (c : ℕ → ℤ) (len : ℕ) (v : ℤ) (R : ℕ) : ℕ :=
  ((R <<< 1) ||| R ||| (R >>> 1)) &&& winMask c len v

/-- The set of times reachable at link `j` of the arm `g`, folding onto `c`. -/
def reachUpto (g : ℕ → ℤ) (c : ℕ → ℤ) (len : ℕ) : ℕ → ℕ
  | 0 => 1 &&& winMask c len (g 0)
  | j + 1 => reachStep c len (g (j + 1)) (reachUpto g c len j)

theorem winMask_testBit {c : ℕ → ℤ} {len u : ℕ} {v : ℤ} (hu : u < len) (hw : |v - c u| ≤ 1) :
    (winMask c len v).testBit u = true := by
  induction len with
  | zero => omega
  | succ n ih =>
    rw [winMask, Nat.testBit_or]
    rcases Nat.lt_or_ge u n with h | h
    · rw [ih h]; simp
    · have hun : u = n := by omega
      subst hun
      rw [if_pos hw]
      simp

theorem reachUpto_testBit_of_folds {m : ℕ} {f : Fin m → ℤ} {len : ℕ} {c : ℕ → ℤ} {g : ℕ → ℤ}
    (hg : ∀ j : Fin m, g j.val = f j) {β : Fin m → ℕ} (hlt : ∀ j, β j < len)
    (hlip : ∀ j j' : Fin m, j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1)
    (h0 : ∀ j : Fin m, j.val = 0 → β j = 0) (hw : ∀ j, |f j - c (β j)| ≤ 1) :
    ∀ (j : ℕ) (hj : j < m), (reachUpto g c len j).testBit (β ⟨j, hj⟩) = true := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hb : β ⟨0, hj⟩ = 0 := h0 _ rfl
    rw [reachUpto, hb, Nat.testBit_and]
    have h1 : (1 : ℕ).testBit 0 = true := rfl
    have h2 : (winMask c len (g 0)).testBit 0 = true := by
      refine winMask_testBit (by have := hlt ⟨0, hj⟩; omega) ?_
      have := hw ⟨0, hj⟩
      rw [hb] at this
      rwa [hg ⟨0, hj⟩]
    rw [h1, h2]
    rfl
  | succ k ih =>
    intro hj
    have hk : k < m := by omega
    have hik := ih hk
    set b := β ⟨k, hk⟩ with hb
    set b' := β ⟨k + 1, hj⟩ with hb'
    rw [reachUpto, reachStep, Nat.testBit_and]
    have hmask : (winMask c len (g (k + 1))).testBit b' = true := by
      refine winMask_testBit (hlt _) ?_
      have := hw ⟨k + 1, hj⟩
      rwa [hg ⟨k + 1, hj⟩]
    rw [hmask, Bool.and_true]
    have hstep := hlip ⟨k, hk⟩ ⟨k + 1, hj⟩ rfl
    rw [abs_le] at hstep
    have hcase : b' = b + 1 ∨ b' = b ∨ b' + 1 = b := by omega
    rw [Nat.testBit_or, Nat.testBit_or]
    rcases hcase with hc | hc | hc
    · have : ((reachUpto g c len k) <<< 1).testBit b' = true := by
        rw [Nat.testBit_shiftLeft, hc]
        simpa using hik
      rw [this]
      simp
    · rw [hc, hik]
      simp
    · have : ((reachUpto g c len k) >>> 1).testBit b' = true := by
        rw [Nat.testBit_shiftRight, show 1 + b' = b by omega]
        exact hik
      rw [this]
      simp

/-- **Soundness of the certificate.** If the reachable set is empty at some link, the arm does
not fold onto the walk. -/
theorem not_foldsOnto_of_reachUpto {m : ℕ} (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) (g : ℕ → ℤ)
    (hg : ∀ j : Fin m, g j.val = f j) (d : ℕ) (hd : d < m) (h : reachUpto g c len d = 0) :
    ¬ FoldsOnto f len c := by
  rintro ⟨β, hlt, hlip, h0, hw⟩
  have := reachUpto_testBit_of_folds hg hlt hlip h0 hw d hd
  rw [h] at this
  simp at this

/-! ## The thirty refutations -/

/-- The forward arm, read off the numeral. -/
def ceG10 : ℕ → ℤ := fun k => (rho10 (343 + k) : ℤ)

/-- The backward arm, read off the numeral. -/
def ceT10 : ℕ → ℤ := fun k => (rho10 (343 - k) : ℤ)

theorem ceG10_eq : ∀ j : Fin (2379 - ceBase10.val), ceG10 j.val = armG ceSeq10 ceBase10 j :=
  fun _ => rfl

theorem ceT10_eq : ∀ j : Fin (ceBase10.val + 1), ceT10 j.val = armT ceSeq10 ceBase10 j :=
  fun _ => rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`F2PrimeOff` fails at basepoint 343 of `bing 0 10`.** None of the thirty members of the
one-bump family takes both arms. -/
theorem ce10_not_f2PrimeOffAt :
    ¬ ∃ c₀ : ℤ, (c₀ = ceSeq10 ceBase10 - 1 ∨ c₀ = ceSeq10 ceBase10 ∨ c₀ = ceSeq10 ceBase10 + 1) ∧
      0 + 1 ≤ c₀ ∧ c₀ ≤ 10 - 1 ∧
      ((∃ h, c₀ ≤ h ∧ h ≤ 10 - 1 ∧
          FoldsOnto (armG ceSeq10 ceBase10) (offLam c₀ h 0 10).1 (offLam c₀ h 0 10).2 ∧
          FoldsOnto (armT ceSeq10 ceBase10) (offLam c₀ h 0 10).1 (offLam c₀ h 0 10).2) ∨
       (∃ l, 0 + 1 ≤ l ∧ l ≤ c₀ ∧
          FoldsOnto (armG ceSeq10 ceBase10) (offVee c₀ l 0 10).1 (offVee c₀ l 0 10).2 ∧
          FoldsOnto (armT ceSeq10 ceBase10) (offVee c₀ l 0 10).1 (offVee c₀ l 0 10).2)) := by
  rintro ⟨c₀, hc₀, hcL, hcH, hcase⟩
  rw [ceSeq10_base] at hc₀
  have kill : ∀ (len : ℕ) (c : ℕ → ℤ),
      (decide (reachUpto ceG10 c len 343 = 0) || decide (reachUpto ceT10 c len 343 = 0)) = true →
      ¬ (FoldsOnto (armG ceSeq10 ceBase10) len c ∧ FoldsOnto (armT ceSeq10 ceBase10) len c) := by
    rintro len c h ⟨hG, hT⟩
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    rcases h with h | h
    · exact not_foldsOnto_of_reachUpto _ len c ceG10 ceG10_eq 343 (by decide) h hG
    · exact not_foldsOnto_of_reachUpto _ len c ceT10 ceT10_eq 343 (by decide) h hT
  have hc : c₀ = 4 ∨ c₀ = 5 ∨ c₀ = 6 := by
    rcases hc₀ with h | h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by rw [h]; norm_num))
  rcases hcase with ⟨h, hh1, hh2, hG, hT⟩ | ⟨l, hl1, hl2, hG, hT⟩
  · rcases hc with rfl | rfl | rfl <;> interval_cases h <;>
      exact kill _ _ (by decide +kernel) ⟨hG, hT⟩
  · rcases hc with rfl | rfl | rfl <;> interval_cases l <;>
      exact kill _ _ (by decide +kernel) ⟨hG, hT⟩

/-- **`F2PrimeOff` is false**, given the faithfulness of `bing 0 10`. -/
theorem not_f2PrimeOff_of_faithful (hcr : IsCrookedIvF ceSeq10 ceSeq10) : ¬ F2PrimeOff := by
  intro hF2
  exact ce10_not_f2PrimeOffAt
    (hF2 2379 ceSeq10 ceSeq10 ceBase10 10 0 ceSeq10_isLip hcr ceSeq10_lb ceSeq10_ub
      (by norm_num) ceSeq10_attains_bot ceSeq10_attains_top)

set_option maxRecDepth 1000000 in
/-- The numeral really is Bing's chain: the recursive construction from level `0` to level
`10` of `HPC/Fold/OffCenter.lean`. -/
theorem ce10_eq_bingPath : bingPath 0 10 = List.ofFn ceSeq10 := by
  rw [bingPath_eq_aux 10 0 10 (by decide)]
  decide +kernel

end HPC.Fold
