import HPC.Hagopian.H76D1
import HPC.Hagopian.H75KurMap

/-!
# Batch 169, item D: T13 — the intersection of a chain of separating extensions

* `SepIn O A p q`: `A` separates `p` from `q` in the open set `O ⊆ R²` (both points lie in `O − A`,
  and no connected subset of `O − A` contains both).
* `sepIn_iInter_of_directed`: a directed (for `⊇`) intersection of compact sets, each separating
  `p` from `q` in `O`, still separates them. An arc from `p` to `q` in the component of `O − ⋂` is
  compact, so it misses one member.
* `iInter_chain_isContinuum`: the intersection of a nonempty chain of extensions of `E` is a
  continuum containing `E`.
* `ExtChainInter`: the statement that the intersection of a nonempty chain of separating extensions
  away from `X₀` is again an extension away from `X₀` (open; the point Hagopian does not argue).
* `T13_of_chainInter`: under `ExtChainInter`, Zorn's lemma gives a separating extension that is
  irreducible (minimal) among separating extensions — T13's `F`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

/-- `A` **separates `p` from `q` in `O`**: `p`, `q ∈ O − A`, and no connected subset of `O − A`
contains both. -/
def SepIn (O A : Set Pt) (p q : Pt) : Prop :=
  p ∈ O \ A ∧ q ∈ O \ A ∧ ∀ S : Set Pt, IsPreconnected S → S ⊆ O \ A → p ∈ S → q ∉ S

/-- **A directed intersection of compact separators separates** (commission 169 §2.D, the
compactness half). -/
theorem sepIn_iInter_of_directed {ι : Type*} [Nonempty ι] {O : Set Pt} (hO : IsOpen O)
    (C : ι → Set Pt) (hdir : Directed (· ⊇ ·) C) (hc : ∀ i, IsCompact (C i)) {p q : Pt}
    (hsep : ∀ i, ∀ S : Set Pt, IsPreconnected S → S ⊆ O \ C i → p ∈ S → q ∉ S)
    {S : Set Pt} (hS : IsPreconnected S) (hSO : S ⊆ O \ ⋂ i, C i) (hp : p ∈ S) (hq : q ∈ S) :
    False := by
  have hcl : IsClosed (⋂ i, C i) := isClosed_iInter fun i => (hc i).isClosed
  have hU : IsOpen (O \ ⋂ i, C i) := hO.sdiff hcl
  have hpU : p ∈ O \ ⋂ i, C i := hSO hp
  have hV : IsOpen (connectedComponentIn (O \ ⋂ i, C i) p) := hU.connectedComponentIn
  have hVc : IsConnected (connectedComponentIn (O \ ⋂ i, C i) p) :=
    isConnected_connectedComponentIn_iff.2 hpU
  have hSV : S ⊆ connectedComponentIn (O \ ⋂ i, C i) p := hS.subset_connectedComponentIn hp hSO
  have hVp := (hV.isConnected_iff_isPathConnected).1 hVc
  obtain ⟨γ, hγ⟩ := hVp.joinedIn p (hSV hp) q (hSV hq)
  have hK : IsCompact (range γ) := isCompact_range γ.continuous
  have hKU : range γ ⊆ O \ ⋂ i, C i := by
    rintro _ ⟨t, rfl⟩; exact connectedComponentIn_subset _ _ (hγ t)
  have hKI : range γ ∩ ⋂ i, C i = ∅ := by
    ext z; simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    exact fun hz => (hKU hz).2
  obtain ⟨i, hi⟩ := hK.elim_directed_family_closed C (fun i => (hc i).isClosed) hKI hdir
  refine hsep i (range γ) (isPreconnected_range γ.continuous)
    (fun z hz => ⟨(hKU hz).1, fun hzC => ?_⟩) ⟨0, γ.source⟩ ⟨1, γ.target⟩
  exact (eq_empty_iff_forall_notMem.1 hi) z ⟨hz, hzC⟩

variable {M : Set Pt}

/-- A chain for `⊆`, viewed as a family indexed by itself, is directed for `⊇`. -/
theorem directed_supset_of_isChain {α : Type*} {c : Set (Set α)} (hc : IsChain (· ⊆ ·) c) :
    Directed (· ⊇ ·) (fun F : c => (F : Set α)) := by
  intro F G
  rcases eq_or_ne F G with h | h
  · exact ⟨F, le_rfl, h ▸ le_rfl⟩
  rcases hc F.2 G.2 (fun h' => h (Subtype.ext h')) with hFG | hGF
  · exact ⟨F, le_rfl, hFG⟩
  · exact ⟨G, hGF, le_rfl⟩

/-- `toPt` commutes with intersections of nonempty families. -/
theorem toPt_sInter {c : Set (Set M)} (hne : c.Nonempty) :
    toPt (⋂₀ c) = ⋂ F : c, toPt (F : Set M) := by
  haveI : Nonempty c := hne.to_subtype
  rw [sInter_eq_iInter]
  exact Subtype.val_injective.injOn.image_iInter_eq

variable [CompactSpace M]

omit [CompactSpace M] in
/-- **The intersection of a separating chain separates** (commission 169 §2.D, in `π⁻¹[D]`
form): for a nonempty chain `c` of subsets of `M`, each compact and separating `p` from `q` in the
open set `O`, the intersection `⋂ c` separates `p` from `q` in `O`. -/
theorem sepIn_sInter_chain {O : Set Pt} (hO : IsOpen O) {c : Set (Set M)} (hne : c.Nonempty)
    (hch : IsChain (· ⊆ ·) c) (hcpt : ∀ F ∈ c, IsCompact F) {p q : Pt}
    (hsep : ∀ F ∈ c, SepIn O (toPt F) p q) : SepIn O (toPt (⋂₀ c)) p q := by
  haveI : Nonempty c := hne.to_subtype
  obtain ⟨F₀, hF₀⟩ := hne
  have hsub : toPt (⋂₀ c) ⊆ toPt F₀ := image_mono (sInter_subset_of_mem hF₀)
  refine ⟨⟨(hsep F₀ hF₀).1.1, fun h => (hsep F₀ hF₀).1.2 (hsub h)⟩,
    ⟨(hsep F₀ hF₀).2.1.1, fun h => (hsep F₀ hF₀).2.1.2 (hsub h)⟩, fun S hS hSO hp hq => ?_⟩
  rw [toPt_sInter ⟨F₀, hF₀⟩] at hSO
  have hdir : Directed (· ⊇ ·) (fun F : c => toPt (F : Set M)) := by
    intro F G
    obtain ⟨H, hFH, hGH⟩ := directed_supset_of_isChain hch F G
    exact ⟨H, image_mono hFH, image_mono hGH⟩
  exact sepIn_iInter_of_directed hO (fun F : c => toPt (F : Set M)) hdir
    (fun F => (hcpt F F.2).image continuous_subtype_val)
    (fun F => (hsep F F.2).2.2) hS hSO hp hq

/-- **The intersection of a chain of extensions is a continuum containing `E`** (commission 169
§2.D, the continuum half). Whether it is again of type A′ with end set `X₀` is `ExtChainInter`. -/
theorem iInter_chain_isContinuum {E X₀ : Set M} (hEne : E.Nonempty) {c : Set (Set M)}
    (hne : c.Nonempty) (hch : IsChain (· ⊆ ·) c) (hext : ∀ F ∈ c, IsExtensionAway E X₀ F) :
    E ⊆ ⋂₀ c ∧ Fold.Q78.IsContinuum (⋂₀ c) := by
  haveI : Nonempty c := hne.to_subtype
  have hEsub : E ⊆ ⋂₀ c := fun x hx F hF => (hext F hF).1 hx
  have hcpt : ∀ F ∈ c, IsCompact F := fun F hF => by
    obtain ⟨-, d, hd, -⟩ := hext F hF
    exact hd.isCompact
  have hconn : ∀ F ∈ c, IsConnected F := fun F hF => by
    obtain ⟨-, d, ⟨⟨a, b, hab⟩, -, -⟩, -⟩ := hext F hF
    exact hab.1.2
  refine ⟨hEsub, ?_, hEne.mono hEsub, ?_⟩
  · obtain ⟨F₀, hF₀⟩ := hne
    exact (hcpt F₀ hF₀).of_isClosed_subset (isClosed_sInter fun F hF => (hcpt F hF).isClosed)
      (sInter_subset_of_mem hF₀)
  · rw [sInter_eq_iInter]
    exact isPreconnected_iInter_directed _ (directed_supset_of_isChain hch)
      (fun F => (hcpt F F.2).isClosed) (fun F => (hconn F F.2).isPreconnected)

/-- **The unproved half of T13's existence sentence**, as a `Prop` (commission 169 §2.D): the
intersection of every nonempty chain of extensions of `E` away from `X₀`, each separating `p` from
`q` in `O`, is again an extension of `E` away from `X₀`. -/
def ExtChainInter (E X₀ : Set M) (O : Set Pt) (p q : Pt) : Prop :=
  ∀ c : Set (Set M), c.Nonempty → IsChain (· ⊆ ·) c →
    (∀ F ∈ c, IsExtensionAway E X₀ F ∧ SepIn O (toPt F) p q) → IsExtensionAway E X₀ (⋂₀ c)

omit [CompactSpace M] in
/-- **T13, conditional on `ExtChainInter`** (p. 347): "Let `F` be a continuum that is irreducible
with respect to the following properties: 1. `F` is an extension of `E` in `M` away from `k⁻¹(0)`.
2. `F` separates `p` from `f(p)` in `π⁻¹[D]`." Given one separating extension `H`, there is a
separating extension `F ⊆ H` that contains no other separating extension. -/
theorem T13_of_chainInter {E X₀ : Set M} {O : Set Pt} (hO : IsOpen O) {p q : Pt}
    (hci : ExtChainInter E X₀ O p q) {H : Set M} (hH : IsExtensionAway E X₀ H)
    (hHs : SepIn O (toPt H) p q) :
    ∃ F ⊆ H, IsExtensionAway E X₀ F ∧ SepIn O (toPt F) p q ∧
      ∀ F', IsExtensionAway E X₀ F' → SepIn O (toPt F') p q → F' ⊆ F → F' = F := by
  set S : Set (Set M) := {F | IsExtensionAway E X₀ F ∧ SepIn O (toPt F) p q}
  have hZ : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s := by
    intro c hcS hch hne
    have hcpt : ∀ F ∈ c, IsCompact F := fun F hF => by
      obtain ⟨⟨-, d, hd, -⟩, -⟩ := hcS hF
      exact hd.isCompact
    exact ⟨⋂₀ c, ⟨hci c hne hch fun F hF => hcS hF,
      sepIn_sInter_chain hO hne hch hcpt fun F hF => (hcS hF).2⟩,
      fun s hs => sInter_subset_of_mem hs⟩
  obtain ⟨F, hFH, hFmin⟩ := zorn_superset_nonempty S hZ H ⟨hH, hHs⟩
  exact ⟨F, hFH, hFmin.1.1, hFmin.1.2, fun F' hF' hF's hF'F =>
    Subset.antisymm hF'F (hFmin.2 ⟨hF', hF's⟩ hF'F)⟩

end HPC.Hagopian
