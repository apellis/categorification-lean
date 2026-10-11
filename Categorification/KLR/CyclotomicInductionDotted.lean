import Categorification.KLR.CyclotomicInductionCalculus
import Categorification.TwoRep.AdjointPositive

/-!
# Categorical dotted units and counits of cyclotomic induction

Powers of the natural dot on the original induction functor are right multiplication
by powers of the final dot on the balanced tensor coefficient. The ordinary dotted
unit and counit agree, under the existing tensor presentations, with
`cyclotomicDotUnit (Polynomial.monomial d 1)` and `cyclotomicDotCounit d`.
These comparisons hold over any commutative ground ring; no commutator inversion
hypotheses are needed here. Induction remains left adjoint to restriction.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.InductionCalculus
open CategoryTheory
open CategoryTheory.Functor (whiskerLeft whiskerRight)
open scoped ModuleCat.Algebra
open TwoRep
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (a : I → Polynomial k) (β : Multiset I)
local notation "R" => CycKLR k Q a β
local notation "β₁" => ((Singleton.singleton i : Multiset I) + β)
local notation "S" => CycKLR k Q a β₁

def dotPowCorner (d : ℕ) (z : IndCorner Q i a β) : IndCorner Q i a β :=
  ⟨z.1 * dotElement Q i a β ^ d, by
    change (z.1 * _) * cyclotomicLast Q i a β 1 = _
    rw [mul_assoc, ((dot_commute Q i a β 1).pow_left d).eq, ← mul_assoc]
    exact congrArg (· * dotElement Q i a β ^ d) z.2⟩

@[simp] theorem dotPowCorner_zero (z : IndCorner Q i a β) :
    dotPowCorner Q i a β 0 z = z := Subtype.ext (by change z.1 * dotElement Q i a β ^ 0 = z.1; rw [pow_zero, mul_one])

theorem dotPowCorner_succ (d : ℕ) (z : IndCorner Q i a β) :
    dotCorner Q i a β (dotPowCorner Q i a β d z) = dotPowCorner Q i a β (d+1) z :=
  Subtype.ext (by
    change (z.1 * dotElement Q i a β ^ d) * dotElement Q i a β = z.1 * dotElement Q i a β ^ (d+1)
    rw [pow_succ, mul_assoc])

/-- Powers of the original natural dot multiply the tensor coefficient on the right. -/
theorem powComp_dotNat_tmul (N : ModuleCat.{max u v w} R) (d : ℕ)
    (z : IndCorner Q i a β) (n : N) :
    (powComp (dotNat Q i a β) d).app N (BalancedTensor.tmul z n) =
      BalancedTensor.tmul (dotPowCorner Q i a β d z) n := by
  induction d with
  | zero => simp only [powComp_zero, dotPowCorner_zero]; rfl
  | succ d hd =>
    change dot Q i a β N ((powComp (dotNat Q i a β) d).app N (BalancedTensor.tmul z n)) = _
    rw [hd, dot_tmul, dotPowCorner_succ]

/-- The categorical dotted ordinary unit, using the original adjunction and dot. -/
def dottedUnit (d : ℕ) : 𝟭 (ModuleCat.{max u v w} R) ⟶
    inductionFunctor Q i a β ⋙ restrictionFunctor Q i a β :=
  (cyclotomicAdjunction Q i a β).unit ≫
    whiskerRight (powComp (dotNat Q i a β) d) (restrictionFunctor Q i a β)

/-- The categorical dotted ordinary counit, with the same dot order. -/
def dottedCounit (d : ℕ) : restrictionFunctor Q i a β ⋙ inductionFunctor Q i a β ⟶
    𝟭 (ModuleCat.{max u v w} S) :=
  whiskerLeft (restrictionFunctor Q i a β) (powComp (dotNat Q i a β) d) ≫
    (cyclotomicAdjunction Q i a β).counit

theorem dottedUnit_val (N : ModuleCat.{max u v w} R) (d : ℕ) (n : N) :
    ((dottedUnit Q i a β d).app N n).1 =
      BalancedTensor.tmul (dotPowCorner Q i a β d (indGenerator Q i a β)) n := by
  change (powComp (dotNat Q i a β) d).app N (BalancedTensor.tmul (indGenerator Q i a β) n) = _
  exact powComp_dotNat_tmul Q i a β N d _ n

theorem dottedCounit_tmul (M : ModuleCat.{max u v w} S) (d : ℕ)
    (z : IndCorner Q i a β) (m : (restrictionFunctor Q i a β).obj M) :
    (dottedCounit Q i a β d).app M (BalancedTensor.tmul z m) =
      (z.1 * dotElement Q i a β ^ d) • m.1 := by
  change (cyclotomicAdjunction Q i a β).counit.app M
    ((powComp (dotNat Q i a β) d).app ((restrictionFunctor Q i a β).obj M)
      (BalancedTensor.tmul z m)) = _
  rw [powComp_dotNat_tmul]
  rfl

/-- The actual categorical cup is the original dot-unit in the middle tensor presentation. -/
theorem dottedUnit_comparison (M : ModuleCat.{max u v w} S) (d : ℕ) (m : M) :
    PresentColour.efMiddleEquiv Q i β a M ((dottedUnit Q i a β₁ d).app M m) =
      BalancedTensor.tmul (cyclotomicDotUnit Q i β a (Polynomial.monomial d 1)) m := by
  change cutTensor Q i a β₁ M ((dottedUnit Q i a β₁ d).app M m).1 = _
  rw [dottedUnit_val, cutTensor_tmul]
  congr 1
  apply Subtype.ext
  rw [cyclotomicDotUnit_monomial_canonical, map_pow]
  change cyclotomicLast Q i a β₁ 1 *
    (cyclotomicLast Q i a β₁ 1 * dotElement Q i a β₁ ^ d) =
    cyclotomicLast Q i a β₁ 1 * dotElement Q i a β₁ ^ d * cyclotomicLast Q i a β₁ 1
  rw [← mul_assoc, ← map_mul, one_mul, mul_assoc,
    ((dot_commute Q i a β₁ 1).pow_left d).eq, ← mul_assoc, ← map_mul, one_mul]

/-- The categorical cap agrees with dotted multiplication on every lower tensor. -/
theorem dottedCounit_comparison (M : ModuleCat.{max u v w} S) (d : ℕ)
    (l : LowerCyclotomic Q i β a) (m : M) :
    (dottedCounit Q i a β d).app M
      (feRebase Q i a β M (PresentColour.lowerToFE Q i β a M (BalancedTensor.tmul l m))) =
      cyclotomicDotCounit Q i β a d l • m := by
  induction l using BalancedTensor.induction_on with
  | zero => simp only [BalancedTensor.zero_tmul, map_zero, zero_smul]
  | add l l' hl hl' => simp only [BalancedTensor.add_tmul, map_add, hl, hl', add_smul]
  | tmul x y =>
    change (dottedCounit Q i a β d).app M
      (BalancedTensor.tmul (PresentColour.leftToInd Q i β a x)
        (PresentColour.coeffAct Q i β a M y m)) = _
    have h := dottedCounit_tmul Q i a β M d (PresentColour.leftToInd Q i β a x)
      (show (restrictionFunctor Q i a β).obj M from PresentColour.coeffAct Q i β a M y m)
    change _ = (x.1 * dotElement Q i a β ^ d) • (y.1 • m) at h
    rw [cyclotomicDotCounit_tmul, map_pow]
    exact h.trans (mul_smul (x.1 * dotElement Q i a β ^ d) y.1 m).symm

/-- At zero dots the original ordinary unit is unchanged. -/
@[simp] theorem dottedUnit_zero : dottedUnit.{u,v,w} Q i a β 0 =
    (cyclotomicAdjunction Q i a β).unit := by
  ext M n
  rfl

/-- At zero dots the original ordinary counit is unchanged. -/
@[simp] theorem dottedCounit_zero : dottedCounit.{u,v,w} Q i a β 0 =
    (cyclotomicAdjunction Q i a β).counit := by
  ext M t
  rfl

end Categorification.KLR.KLRAlgebra.AbsentColour.InductionCalculus
