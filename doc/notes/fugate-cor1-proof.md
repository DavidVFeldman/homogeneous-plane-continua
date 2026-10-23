# Fugate 1966, Corollary 1: a proof

Hand proof, not machine-checked. It derives Corollary 1 from Fugate's Theorem 1 (in the
repository: `fugate_cor1'` and `isHereditarilyUnicoherent_union`), together with two published
facts about circle-like continua:

* Ingram, *Decomposable circle-like continua*, Fund. Math. 63 (1968), Theorem 2(2);
* Nadler, *Continuum Theory* (1992), Exercise 12.51.

## Conventions

A *continuum* is a nonempty compact connected metric space. A continuum T is *unicoherent* if
P ∩ Q is connected whenever P and Q are subcontinua of T with P ∪ Q = T. T is *hereditarily
unicoherent* if every subcontinuum of T is unicoherent. T is *atriodic* if no subcontinuum of T is
a triod.

Fact 0 below holds by definition. Facts 1–4 are the inputs to the proof.

**Fact 0 (heredity).** Every subcontinuum of an atriodic continuum is atriodic. Every
subcontinuum of a hereditarily unicoherent continuum is hereditarily unicoherent.

**Fact 1 (union lemma; repository `isHereditarilyUnicoherent_union`).** Suppose P and Q are
hereditarily unicoherent continua and P ∩ Q is connected. Then P ∪ Q is hereditarily unicoherent.

**Fact 2 (Fugate, Theorem 1, finite-chain form; repository `fugate_cor1'`).** Suppose
A₀, …, A_k are chainable continua with A_{i} ∩ A_{i+1} ≠ ∅ for every i. If their union is
atriodic and hereditarily unicoherent, then the union is chainable.

**Fact 3 (Ingram 1968, Theorem 2(2)).** Suppose Y and A are chainable continua that intersect,
Y ∪ A is atriodic, and Y ∩ A is not connected. Then Y ∪ A is circle-like (and not chainable).

**Fact 4 (Nadler, Exercise 12.51).** Each nondegenerate proper subcontinuum of a circle-like
continuum is chainable. Chainable continua are hereditarily unicoherent, and a point is
unicoherent. So every proper subcontinuum of a circle-like continuum is unicoherent.

## Theorem (Fugate's Corollary 1, sufficiency)

Let A₀, …, A_k be chainable continua in a metric space with A_i ∩ A_{i+1} ≠ ∅ for
0 ≤ i < k, and put X = A₀ ∪ ⋯ ∪ A_k. If X is atriodic and unicoherent, then X is chainable.

(The necessity half is already proved in the repository as `fugate_cor1_necessity`.)

## Proof

The proof is by strong induction on k. Assume the theorem holds for every chain of fewer than
k + 1 chainable continua. For q ≤ k, write U_q = A₀ ∪ ⋯ ∪ A_q. Each U_q is a continuum, since
consecutive pieces meet.

**Step 1 (reduction to some partial union failing).** Suppose every U_q is unicoherent. We show
by induction on q that each U_q is hereditarily unicoherent.

* U₀ = A₀ is chainable, hence hereditarily unicoherent.
* Suppose U_q is hereditarily unicoherent. Then U_{q+1} = U_q ∪ A_{q+1} is unicoherent and is
  the union of the two continua U_q and A_{q+1}, so U_q ∩ A_{q+1} is connected. By Fact 1,
  U_{q+1} is hereditarily unicoherent.

In particular X = U_k is hereditarily unicoherent. It is atriodic by hypothesis, so it is
chainable by Fact 2.

So assume from now on that some U_q is not unicoherent, and let p be the least such q. Since
U₀ = A₀ is chainable, p ≥ 1. Since U_k = X is unicoherent, p ≤ k − 1. Put

* Y = U_{p−1};
* A = A_p;
* C = U_p = Y ∪ A;
* B = A_{p+1} ∪ ⋯ ∪ A_k.

B is a continuum, since consecutive pieces meet. B meets A, because A_p ∩ A_{p+1} ≠ ∅.
X = C ∪ B.

**Step 2 (the pieces).** Every U_q with q < p is unicoherent, by the choice of p. The argument
of Step 1 therefore shows that Y is hereditarily unicoherent. Y is atriodic by Fact 0, so Y is
chainable by Fact 2 applied to A₀, …, A_{p−1}. Y meets A, because A_{p−1} ⊆ Y and
A_{p−1} ∩ A_p ≠ ∅.

If Y ∩ A were connected, Fact 1 would make C hereditarily unicoherent, hence unicoherent,
contrary to the choice of p. So Y ∩ A is not connected. Write Y ∩ A = H ∪ K with H and K
nonempty, disjoint and closed.

C is atriodic by Fact 0. So C is circle-like by Fact 3, and every proper subcontinuum of C is
unicoherent by Fact 4. Call this (∗).

**Step 3 (two connected intersections).** A ∪ B is a continuum, since A meets B.

* X = Y ∪ (A ∪ B) and X is unicoherent, so M₁ := Y ∩ (A ∪ B) = H ∪ K ∪ (Y ∩ B) is connected.
  M₁ is also closed, so M₁ is a continuum.
* H meets B. If not, then H and K ∪ (Y ∩ B) are disjoint, nonempty and closed, and their union
  is M₁, contradicting connectedness. Likewise K meets B.
* Hence Y meets B, so Y ∪ B is a continuum. X = (Y ∪ B) ∪ A, so
  M₂ := A ∩ (Y ∪ B) = H ∪ K ∪ (A ∩ B) is a continuum.

**Step 4 (Y and A are each covered by the other together with B).**

* M₁ ∩ M₂ = Y ∩ A ∩ (A ∪ B) ∩ (Y ∪ B) = Y ∩ A = H ∪ K. This set is nonempty, so
  M := M₁ ∪ M₂ is connected.
* M₁ ∩ M₂ is not connected. So M is a subcontinuum of C that is not unicoherent. By (∗), M = C.
* M = (Y ∩ A) ∪ (Y ∩ B) ∪ (A ∩ B) = (Y ∩ A) ∪ (C ∩ B). So C ⊆ (Y ∩ A) ∪ B.
* Therefore X = C ∪ B ⊆ (Y ∩ A) ∪ B. Hence X = Y ∪ B and X = A ∪ B.

**Step 5 (C lies in B).**

* X = Y ∪ B is unicoherent, so D_Y := Y ∩ B is a continuum. Likewise X = A ∪ B makes
  D_A := A ∩ B a continuum.
* D_Y ∩ D_A = Y ∩ A ∩ B = (H ∩ B) ∪ (K ∩ B). The two parts are disjoint and closed, and both are
  nonempty by Step 3.
* So D := D_Y ∪ D_A = C ∩ B is a continuum (D_Y and D_A meet), and it is not unicoherent.
* D ⊆ C, so by (∗), D = C. That is, C ⊆ B.

**Step 6 (the induction).** By Step 5, X = C ∪ B = B = A_{p+1} ∪ ⋯ ∪ A_k.

* This is a chain of k − p chainable continua, with consecutive pieces meeting, and
  k − p ≤ k − 1 < k + 1.
* X is atriodic and unicoherent, so by the induction hypothesis X is chainable.
* Hence X is hereditarily unicoherent, so its subcontinuum C is unicoherent. This contradicts the
  choice of p.

So the case "some U_q is not unicoherent" is impossible, and Step 1 applies. ∎

## Remarks

1. **Where the obvious argument stops.** Fugate gives no proof of Corollary 1. The one-line
   induction through Theorem 1 needs each partial union U_q to be unicoherent. That is condition
   (U), and the repository shows it is exactly the missing step (`fugateU_iff_cor1Sufficiency`).
   The proof above establishes (U). If the first partial union to fail were not unicoherent, it
   would be circle-like (Ingram), and the rest of the chain would have to swallow it entirely
   (Steps 3–5). That reduces the number of pieces.

2. **The new ingredient is (∗).** It needs Ingram's Theorem 2(2) and the chainability of proper
   subcontinua of circle-like continua. Ingram 1968 postdates Fugate 1966, and Ingram cites
   Fugate's Theorem 1 and Lemma 1, but not Corollary 1. Steps 1, 3, 4, 5 and 6 use only the
   definitions, Facts 0–2 and unicoherence of X applied to four decompositions:
   * X = Y ∪ (A ∪ B);
   * X = (Y ∪ B) ∪ A;
   * X = Y ∪ B;
   * X = A ∪ B.

3. **For the formalization.** The proof splits into two parts.
   * The combinatorial part (Steps 1–6) can be checked now, with (∗) as a hypothesis:
     ```lean
     theorem fugate_cor1_of_star
         (hstar : ∀ Y A : Set S, IsSnakeLike Y → IsSnakeLike A → (Y ∩ A).Nonempty →
           IsAtriodic (Y ∪ A) → ¬ IsConnected (Y ∩ A) →
           ∀ M ⊆ Y ∪ A, Fold.Q78.IsContinuum M → M ≠ Y ∪ A → IsUnicoherent M) :
         FugateCor1Sufficiency S
     ```
   * Then (∗) needs to be discharged: Ingram's Theorem 2(2), built with circular chains
     (`IsCircularChain` exists in `Tree67.lean`), plus Nadler 12.51. A direct proof of (∗) that
     avoids circle-likeness may exist. I have not looked for one.
