/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.DiagR
import Categorification.WeightedKLR.RedStrands.SingleBlack
import Categorification.WeightedKLR.RedStrands.TensorProjection
import Categorification.WeightedKLR.RedStrands.AffineCoverGrading
import Categorification.WeightedKLR.RedStrands.CyclotomicProjection

/-!
# An ordinary corner detecting the quadratic scalar obstruction

Webster, arXiv:1309.3796v3, §4.3, Theorem 4.18 identifies the one-red block
with the cyclotomic KLR algebra. In the two-colour disconnected case with
mixed parameter 2 and both coroot multiplicities 1, the ordinary red-left
idempotent with one black strand is the unit in the quotient by the first
dot. This detects the idempotent in the ordinary algebra for the comparison
of Webster v3, §4.6, Lemma 4.29.
-/

noncomputable section

namespace Categorification.Stendhal.DisconnectedCounterexample

open KLR KLRAlgebra QuantumGroup QuantumGroup.UDot

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- The two colours are orthogonal. -/
def cartan : CartanDatum Bool := CartanDatum.ofGraph (⊥ : SimpleGraph Bool)

/-- The black quadratic parameter in Webster v3, Definition 2.4, for the example. -/
def parameters (i j : Bool) : MvPolynomial (Fin 2) ℚ :=
  if i = j then 0 else MvPolynomial.C 2

/-- The single red strand has multiplicity one at each colour. -/
def exponents (_ : Fin 1) : Bool →₀ ℕ :=
  Finsupp.single false 1 + Finsupp.single true 1

@[simp] theorem exponents_apply (r : Fin 1) (i : Bool) : exponents r i = 1 := by
  cases i <;> simp [exponents]

/-- The ordinary weight lattice with coordinate coroot pairings. -/
def weightDatum : WeightDatum cartan (Bool → ℤ) ((Bool → ℤ) →+ ℤ) where
  pair := AddMonoidHom.id _
  iX j i := A cartan i j
  iY i := { toFun := fun x => x i, map_zero' := rfl, map_add' := fun _ _ => rfl }
  pair_iY_iX _ _ := rfl

/-- The red weight evaluates to one on both simple coroots. -/
def highest : Bool → ℤ := fun _ => 1

@[simp] theorem pair_highest (i : Bool) : weightDatum.pair (weightDatum.iY i) highest = 1 := rfl

/-- The single red label as a dominant weight. -/
def redWeights (_ : Fin 1) : {x : Bool → ℤ // ∀ i, 0 ≤ weightDatum.pair (weightDatum.iY i) x} :=
  ⟨highest, fun i => by rw [pair_highest]; decide⟩

/-- The ordinary label is the coroot multiplicity of the dominant red weight. -/
theorem redWeights_exponents (r : Fin 1) (i : Bool) :
    weightDatum.pair (weightDatum.iY i) (redWeights r).val = (exponents r i : ℤ) := by
  rw [exponents_apply]
  exact pair_highest i

/-- Passing the other black colour leaves the first red coroot coordinate at one. -/
theorem pair_other_root :
    weightDatum.pair (weightDatum.iY false) (highest - weightDatum.iX true) = 1 := rfl

/-- The ordinary block contains one black strand of the second colour. -/
abbrev content : Multiset Bool := {true}

/-- The ordinary boundary consists of the red strand followed by the black strand. -/
abbrev boundary : Seq (stendhalWeight 1 content) := SingleBlack.word true

/-- The loading as a word, with its red strand at the far left. -/
theorem boundary_word :
    KLR.Diagram.word boundary = [.inr 0, .inl true] := rfl

private theorem ordinary_idem_eq_one :
    SingleRed.mk parameters exponents content (StendhalAlgebraAllOrders.e boundary) = 1 := by
  let s : Seq content := default
  have hword : SingleRed.insertWord content s = boundary := by
    apply Subtype.ext
    funext a
    have ha : a.val < 2 := a.isLt
    have hp : (a : ℕ) = 0 ∨ (a : ℕ) = 1 := by omega
    rcases hp with h | h
    · obtain rfl : a = ⟨0, by simp [stendhalWeight]⟩ := Fin.ext h
      exact SingleRed.insertWord_head content s
    · obtain rfl : a = SingleRed.blackPos content ⟨0, by simp⟩ := Fin.ext h
      have hb := SingleRed.insertWord_black content s ⟨0, by simp⟩
      exact hb
  rw [← hword, ← SingleRed.insertRed_e, e_eq_one, map_one]

/-- The red-black loading has nonzero identity in the ordinary Stendhal algebra. -/
theorem ordinary_idem_ne_zero :
    SingleRed.mk parameters exponents content (StendhalAlgebraAllOrders.e boundary) ≠ 0 := by
  rw [ordinary_idem_eq_one]
  have hn : Nontrivial (AdjoinRoot (Polynomial.X ^ exponents 0 true : Polynomial ℚ)) := by
    apply AdjoinRoot.nontrivial
    rw [exponents_apply, pow_one, Polynomial.degree_X]
    decide
  have := (SingleBlack.oneBlackOneRedEquiv true parameters exponents).symm.injective.nontrivial
  exact one_ne_zero

/-- The same red-black idempotent, as the image of the affine cover generator. -/
theorem affine_idem_ne_zero :
    affineTensorProjection (Q := parameters) exponents content (KLRAlgebra.e boundary) ≠ 0 := by
  unfold affineTensorProjection
  rw [AlgHom.comp_apply, AlgHom.comp_apply, affineCover_e]
  have hEq :
      orderProjection parameters exponents content (StendhalAlgebraAllOrders.e boundary) =
        SingleRed.orderedEquiv parameters exponents content (StendhalAlgebraAllOrders.e boundary) := by
    apply Subtype.ext
    change StendhalAlgebraAllOrders.e boundary *
      StendhalAlgebraAllOrders.redOrderedIdem ℚ parameters exponents content =
        StendhalAlgebraAllOrders.e boundary
    rw [SingleRed.redOrderedIdem_eq_one, mul_one]
  rw [hEq]
  exact ordinary_idem_ne_zero

end Categorification.Stendhal.DisconnectedCounterexample
