/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Comparison
import Categorification.TwoRep.RouqLocTransport
import Categorification.TwoRep.CyclotomicAbsentAdjunction

/-!
# Kang–Kashiwara Theorem 5.2 on the cyclotomic block functors

Kang–Kashiwara (arXiv:1102.4677v4, Theorem 5.2) prove that for `λ = Λ - β` the commutator
of `E_i^Λ` and `F_i^Λ` on `R^Λ(β)`-modules is given by `⟨h_i, λ⟩` copies of the identity:
`F_i E_i ⊕ Id^{⊕ ⟨h_i, λ⟩} ≅ E_i F_i` if `⟨h_i, λ⟩ ≥ 0` and
`F_i E_i ≅ E_i F_i ⊕ Id^{⊕ -⟨h_i, λ⟩}` if `⟨h_i, λ⟩ ≤ 0`, the maps being Rouquier's
(Brundan, arXiv:1501.00350v1, (1.8), (1.9)). This file states it in the form used by the
weight-indexed cyclotomic 2-representation (KL III Thm. 1.2), on the block functors
`indA`, `resA` of `CyclotomicAction`, whose target block is tied to the source block only by a
proof `h : {i} + β = δ`:

* `blockLoc` : Rouquier's data at the middle block `β = {i} + γ` (`TwoRep.RouqLoc`), with
  Brundan weight `-⟨h_i, Λ - β⟩`, dots `dotA` and same-colour crossing `sameCrossA = -ψ`.
* `blockBoundary` : for `i ∉ β`, the decomposition of `E_i F_i` on `R^Λ(β)`-modules into
  `⟨h_i, Λ - β⟩` copies of the identity through the dotted units
  (`TwoRep.RouqBoundary.Coefficients`).

Hypotheses (Kang–Kashiwara §3, ungraded): `k` is any commutative ring;
`Q_ij(u, v) = Q_ji(v, u)` (`KLRSymm Q`); for `j ≠ l` the leading coefficient of `Q_jl` in the
second variable is a unit constant; the cyclotomic polynomials `a_j` are monic, of degree
`⟨h_j, Λ⟩`; and `deg_v Q_ji = -⟨h_i, α_j⟩` for `j ≠ i`. Kang–Kashiwara work with a graded
ring `k` and graded functors; the grading is not part of these statements.

Both are proved by transporting the corresponding statements for
`KLRAlgebra.AbsentColour.inductionFunctor` (`ConcreteAdjunction.loc`,
`BoundaryAdjunction.coefficients`) along the comparison isomorphisms of
`CyclotomicAction.Comparison`.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory TwoRep KLRAlgebra.AbsentColour

universe u v w

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

/-- **Kang–Kashiwara, Theorem 5.2** (interior blocks): Rouquier's data at the middle block
`β = {i} + γ`. The Brundan weight is minus the Kang–Kashiwara weight `⟨h_i, Λ - β⟩`; the
invertibility of Rouquier's maps (Brundan (1.8), (1.9)) is the content of the theorem. -/
def blockLoc (i : I) {γ β δ : Multiset I} (h₁ : {i} + γ = β) (h₂ : {i} + β = δ) :
    RouqLoc (adjA.{u, v, w} Q a i h₁) (adjA Q a i h₂) (dotA Q a i h₁) (dotA Q a i h₂)
      (sameCrossA Q a i h₁ h₂) (-(RD.pair (RD.iY i) (Λ - (β.map RD.iX).sum))) := by
  subst h₁ h₂
  exact AdditiveCat.RouqLoc.transport
    (ConcreteAdjunction.loc.{u, v, w} Q i a γ hQ hlead ha RD Λ (hΛ i) (hdeg i))
    (indIsoA Q a i γ) (indIsoA Q a i ({i} + γ)) (resIsoA Q a i γ) (resIsoA Q a i ({i} + γ))
    (unit_compat Q a i ({i} + γ)) (counit_compat Q a i γ) (dot_compat Q a i γ)
    (dot_compat Q a i ({i} + γ)) (cross_compat Q a i γ)

/-- **Kang–Kashiwara, Theorem 5.2** (boundary blocks): for `i ∉ β`, `E_i F_i` on
`R^Λ(β)`-modules is the sum of `⟨h_i, Λ - β⟩` copies of the identity, through the dotted
units. -/
def blockBoundary (i : I) {β δ : Multiset I} (hi : i ∉ β) (h : {i} + β = δ) :
    RouqBoundary.Coefficients (adjA.{u, v, w} Q a i h) (dotA Q a i h)
      (RD.pair (RD.iY i) (Λ - (β.map RD.iX).sum)).toNat := by
  subst h
  exact (BoundaryAdjunction.coefficients.{u, v, w} Q i a β hQ hlead ha RD Λ (hΛ i) (hdeg i)
    hi).transport (indIsoA Q a i β) (resIsoA Q a i β) (unit_compat Q a i β) (dot_compat Q a i β)

end

end Categorification.KLR.CyclotomicAction
