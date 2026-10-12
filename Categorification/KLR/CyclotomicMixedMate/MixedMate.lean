/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.MixedCrossing
import Categorification.KLR.CyclotomicMixedMate.MixedTransport

/-!
# The original ordinary-adjunction mixed mate

`mate` is the original Hom-equivalence mate of the crossing and lifted counit.
`mate_tmul` proves its value on arbitrary modules with the actual weight transport.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.MixedMate
open MulOpposite
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  (γ : Multiset I) (i j : I)
local notation "R" => CycKLR k Q a γ
local notation "A" => CycKLR k Q a ((Singleton.singleton j : Multiset I) + γ)
local notation "C" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)
local notation "U" => CycKLR k Q a
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton j : Multiset I) + γ))
local notation "V" => CycKLR k Q a
  ((Singleton.singleton j : Multiset I) + ((Singleton.singleton i : Multiset I) + γ))
local notation "α" => cyclotomicLast Q i a ((Singleton.singleton j : Multiset I) + γ)
local notation "β" => cyclotomicLast Q j a ((Singleton.singleton i : Multiset I) + γ)
local notation "ιi" => cyclotomicLast Q i a γ
local notation "ιj" => cyclotomicLast Q j a γ

def κ : V ≃ₐ[k] U := MixedTransport.weightEquiv Q a (MixedCrossing.square γ i j)

def coefficient : U := CycKLR.mk k Q a _ (MixedCrossing.crossingElement Q γ i j)

theorem coefficient_eq : coefficient Q a γ i j =
    -CycKLR.mk k Q a _ (ψ (Multiset.card γ)) * κ Q a γ i j (β (ιi 1)) := by
  rw [coefficient, MixedCrossing.crossingElement, map_mul, map_neg]
  rw [← map_one (CycKLR.mk k Q a γ), cyclotomicLast_mk, cyclotomicLast_mk]
  rw [κ, MixedTransport.weightEquiv_mk]
  rfl

theorem coefficient_intertwine (r : R) :
    α (ιj r) * coefficient Q a γ i j =
      coefficient Q a γ i j * κ Q a γ i j (β (ιi r)) := by
  obtain ⟨r, rfl⟩ := CycKLR.mk_surjective r
  rw [cyclotomicLast_mk, cyclotomicLast_mk, cyclotomicLast_mk, cyclotomicLast_mk]
  rw [κ, MixedTransport.weightEquiv_mk, coefficient, ← map_mul, ← map_mul]
  exact congrArg (CycKLR.mk k Q a _) (MixedCrossing.crossingElement_intertwine Q γ i j r)

theorem coefficient_right :
    coefficient Q a γ i j * κ Q a γ i j (β (ιi 1)) = coefficient Q a γ i j := by
  rw [coefficient_eq, mul_assoc, ← map_mul, ← map_mul, ← map_mul, one_mul]

theorem coefficient_left : α (ιj 1) * coefficient Q a γ i j = coefficient Q a γ i j := by
  rw [coefficient_intertwine, coefficient_right]

theorem coefficient_cut :
    coefficient Q a γ i j * κ Q a γ i j (lastIdem Q j a ({i} + γ)) = coefficient Q a γ i j := by
  rw [coefficient_eq, mul_assoc, ← map_mul]
  change _ * κ Q a γ i j (β (ιi 1) * β 1) = _
  rw [← map_mul, mul_one]

/-- The actual ordered coefficient, transported to the reversed upper algebra. -/
def factor : IndCorner Q j a γ →ₗ[k] IndCorner Q j a ({i} + γ) where
  toFun y := ⟨(κ Q a γ i j).symm (α y.1 * coefficient Q a γ i j), by
    apply (κ Q a γ i j).injective
    change κ Q a γ i j (_ * lastIdem Q j a ({i} + γ)) = _
    simp only [map_mul, AlgEquiv.apply_symm_apply]
    rw [mul_assoc, coefficient_cut]⟩
  map_add' y z := Subtype.ext (by simp only [Submodule.coe_add, map_add, add_mul])
  map_smul' c y := Subtype.ext (by
    change (κ Q a γ i j).symm (α (c • y.1) * coefficient Q a γ i j) = _
    rw [map_smul, smul_mul_assoc, map_smul]
    rfl)

/-- The mate coefficient expanded to the checked signed crossing and original target cut. -/
theorem factor_val_signed (y : IndCorner Q j a γ) :
    (factor Q a γ i j y).1 =
      (κ Q a γ i j).symm
        (α y.1 * (-CycKLR.mk k Q a _ (ψ (Multiset.card γ)) *
          κ Q a γ i j (β (lastIdem Q i a γ)))) := by
  change (κ Q a γ i j).symm (α y.1 * coefficient Q a γ i j) = _
  rw [coefficient_eq]
  rfl

theorem factor_balance (y : IndCorner Q j a γ) (r : R) :
    factor Q a γ i j (op r • y) = op (ιi r) • factor Q a γ i j y := by
  apply Subtype.ext
  apply (κ Q a γ i j).injective
  change κ Q a γ i j ((κ Q a γ i j).symm (α (y.1 * ιj r) * coefficient Q a γ i j)) =
    κ Q a γ i j ((κ Q a γ i j).symm (α y.1 * coefficient Q a γ i j) * β (ιi r))
  simp only [map_mul, AlgEquiv.apply_symm_apply]
  rw [mul_assoc, coefficient_intertwine, ← mul_assoc]

theorem factor_upperCut (y : IndCorner Q j a γ) :
    (κ Q a γ i j).symm (lastIdem Q i a ({j} + γ)) • factor Q a γ i j y =
      factor Q a γ i j y := by
  apply Subtype.ext
  change (κ Q a γ i j).symm (α 1) *
    (κ Q a γ i j).symm (α y.1 * coefficient Q a γ i j) = _
  rw [← map_mul, ← mul_assoc, ← map_mul, one_mul]
  rfl

/-- The tensor coefficient has precisely the original order and the inverse weight cast. -/
theorem factor_mul_val (z : IndCorner Q i a ({j} + γ)) (y : IndCorner Q j a γ) :
    ((κ Q a γ i j).symm z.1 • factor Q a γ i j y).1 =
      (κ Q a γ i j).symm (z.1 * α y.1 * coefficient Q a γ i j) := by
  change (κ Q a γ i j).symm z.1 *
    (κ Q a γ i j).symm (α y.1 * coefficient Q a γ i j) = _
  rw [← map_mul, ← mul_assoc]

variable (N : Type w) [AddCommGroup N] [Module k N] [Module (CycKLR k Q a γ) N]
  [IsScalarTower k (CycKLR k Q a γ) N]
local notation "J" => Ind Q j a ((Singleton.singleton i : Multiset I) + γ) (Ind Q i a γ N)

def innerBil : IndCorner Q j a γ →ₗ[k] N →ₗ[k] J :=
  ((BalancedTensor.mkBil k V C (IndCorner Q j a ({i} + γ)) (Ind Q i a γ N)).comp
    (factor Q a γ i j)).compl₂
      ((BalancedTensor.mkBil k C R (IndCorner Q i a γ) N) (indGenerator Q i a γ))

omit [IsScalarTower k R N] in
theorem innerBil_balance (y : IndCorner Q j a γ) (r : R) (n : N) :
    innerBil Q a γ i j N (op r • y) n = innerBil Q a γ i j N y (r • n) := by
  change BalancedTensor.tmul (factor Q a γ i j (op r • y))
      (BalancedTensor.tmul (indGenerator Q i a γ) n) =
    BalancedTensor.tmul (factor Q a γ i j y) (BalancedTensor.tmul (indGenerator Q i a γ) (r • n))
  rw [factor_balance, BalancedTensor.op_smul_tmul, BalancedTensor.smul_tmul',
    ← indGenerator_balance, BalancedTensor.op_smul_tmul]

def inner : Ind Q j a γ N →ₗ[k] J :=
  BalancedTensor.lift (innerBil Q a γ i j N) (innerBil_balance Q a γ i j N)

omit [IsScalarTower k R N] in
@[simp] theorem inner_tmul (y : IndCorner Q j a γ) (n : N) :
    inner Q a γ i j N (BalancedTensor.tmul y n) =
      BalancedTensor.tmul (factor Q a γ i j y) (BalancedTensor.tmul (indGenerator Q i a γ) n) := rfl

omit [IsScalarTower k R N] in
theorem inner_smul (s : A) (m : Ind Q j a γ N) :
    inner Q a γ i j N (s • m) = (κ Q a γ i j).symm (α s) • inner Q a γ i j N m := by
  induction m using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add m m' hm hm' => simp only [smul_add, map_add, hm, hm']
  | tmul y n =>
    rw [BalancedTensor.smul_tmul', inner_tmul, inner_tmul, BalancedTensor.smul_tmul']
    congr 1
    apply Subtype.ext
    change (κ Q a γ i j).symm (α (s * y.1) * coefficient Q a γ i j) =
      (κ Q a γ i j).symm (α s) * (κ Q a γ i j).symm (α y.1 * coefficient Q a γ i j)
    simp only [map_mul, mul_assoc]

/-- Crossing on original nested induction, with explicit upper weight covariance. -/
def crossing : Ind Q i a ({j} + γ) (Ind Q j a γ N) →ₗ[k] J :=
  BalancedTensor.lift
    (LinearMap.mk₂ k (fun z m => (κ Q a γ i j).symm z.1 • inner Q a γ i j N m)
      (fun z z' m => by rw [Submodule.coe_add, map_add, add_smul])
      (fun c z m => by
        change (κ Q a γ i j).symm (c • z.1) • _ = _
        rw [map_smul, smul_assoc])
      (fun z m m' => by rw [map_add, smul_add])
      (fun c z m => by rw [map_smul, smul_comm]))
    (fun z s m => by
      change (κ Q a γ i j).symm (z.1 * α s) • inner Q a γ i j N m =
        (κ Q a γ i j).symm z.1 • inner Q a γ i j N (s • m)
      rw [map_mul, inner_smul, mul_smul])

omit [IsScalarTower k R N] in
@[simp] theorem crossing_tmul (z : IndCorner Q i a ({j} + γ)) (y : IndCorner Q j a γ) (n : N) :
    crossing Q a γ i j N (BalancedTensor.tmul z (BalancedTensor.tmul y n)) =
      BalancedTensor.tmul ((κ Q a γ i j).symm z.1 • factor Q a γ i j y)
        (BalancedTensor.tmul (indGenerator Q i a γ) n) := by
  change (κ Q a γ i j).symm z.1 • inner Q a γ i j N (BalancedTensor.tmul y n) = _
  rw [inner_tmul, BalancedTensor.smul_tmul']

omit [IsScalarTower k R N] in
/-- The actual original crossing with its full ordered coefficient. -/
theorem crossing_tmul_explicit (z : IndCorner Q i a ({j} + γ))
    (y : IndCorner Q j a γ) (n : N) :
    crossing Q a γ i j N (BalancedTensor.tmul z (BalancedTensor.tmul y n)) =
      BalancedTensor.tmul
        (⟨(κ Q a γ i j).symm (z.1 * α y.1 * coefficient Q a γ i j), by
          rw [← factor_mul_val Q a γ i j z y]
          exact ((κ Q a γ i j).symm z.1 • factor Q a γ i j y).2⟩ :
          IndCorner Q j a ({i} + γ))
        (BalancedTensor.tmul (indGenerator Q i a γ) n) := by
  rw [crossing_tmul]
  congr 1
  exact Subtype.ext (factor_mul_val Q a γ i j z y)

omit [IsScalarTower k R N] in
theorem crossing_smul (s : U) (t : Ind Q i a ({j} + γ) (Ind Q j a γ N)) :
    crossing Q a γ i j N (s • t) =
      (κ Q a γ i j).symm s • crossing Q a γ i j N t := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add t t' ht ht' => simp only [smul_add, map_add, ht, ht']
  | tmul z m =>
    rw [BalancedTensor.smul_tmul']
    change (κ Q a γ i j).symm (s * z.1) • inner Q a γ i j N m =
      (κ Q a γ i j).symm s • ((κ Q a γ i j).symm z.1 • inner Q a γ i j N m)
    rw [map_mul, mul_smul]

/-- The original double induction of an arbitrary lower module morphism. -/
def doubleMap {N' : Type w} [AddCommGroup N'] [Module k N'] [Module R N']
    [IsScalarTower k R N'] (f : N →ₗ[R] N') :
    Ind Q i a ({j} + γ) (Ind Q j a γ N) →ₗ[U]
      Ind Q i a ({j} + γ) (Ind Q j a γ N') :=
  BalancedTensor.mapRight (N := Ind Q j a γ N) (N' := Ind Q j a γ N')
    (indMap Q j a γ N f)


open CategoryTheory
open scoped ModuleCat.Algebra

/-- Only the upper algebra is transported; the original module and all its elements remain. -/
def upperTransport : ModuleCat.{max u v w} V ⥤ ModuleCat.{max u v w} U :=
  ModuleCat.restrictScalars (κ Q a γ i j).symm.toRingHom

/-- Actual reversed induction, viewed over the original upper algebra by κ⁻¹. -/
abbrev crossingTarget := (upperTransport.{u,v,w} Q a γ i j).obj (ModuleCat.of V J)

/-- A genuine upper-linear crossing on the original unbundled induction modules. -/
def crossingLinear : Ind Q i a ({j} + γ) (Ind Q j a γ N) →ₗ[U]
    crossingTarget Q a γ i j N where
  toFun t := crossing Q a γ i j N t
  map_add' := map_add _
  map_smul' := crossing_smul Q a γ i j N

variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)) M]
  [IsScalarTower k (CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)) M]

/-- The original lower ordinary counit, via the original Hom equivalence. -/
def lowerCounit : Ind Q i a γ (Res Q i a γ M) →ₗ[C] M :=
  homFromRes Q i a γ (N := Res Q i a γ M) LinearMap.id

/-- Induction of the original counit before upper scalar transport. -/
def counitInd : Ind Q j a ({i} + γ) (Ind Q i a γ (Res Q i a γ M)) →ₗ[V]
    Ind Q j a ({i} + γ) M :=
  BalancedTensor.mapRight (N := Ind Q i a γ (Res Q i a γ M)) (N' := M)
    (lowerCounit Q a γ i M)

/-- Transport only scalars on induction of the original lower counit. -/
def liftedCounit : crossingTarget Q a γ i j (Res Q i a γ M) →ₗ[U]
    (upperTransport Q a γ i j).obj (ModuleCat.of V (Ind Q j a ({i} + γ) M)) where
  toFun t := counitInd Q a γ i j M t
  map_add' t t' := (counitInd Q a γ i j M).map_add t t'
  map_smul' s t := (counitInd Q a γ i j M).map_smul ((κ Q a γ i j).symm s)
    (show Ind Q j a ({i} + γ) (Ind Q i a γ (Res Q i a γ M)) from t)

/-- Apply the original upper ordinary Hom equivalence to crossing followed by counit. -/
def mate : Ind Q j a γ (Res Q i a γ M) →ₗ[A]
    Res Q i a ({j} + γ)
      ((upperTransport Q a γ i j).obj (ModuleCat.of V (Ind Q j a ({i} + γ) M))) :=
  homToRes Q i a ({j} + γ)
    ((liftedCounit Q a γ i j M).comp (crossingLinear Q a γ i j (Res Q i a γ M)))

/-- Literal original upper-unit evaluation, then crossing, then the original lower counit. -/
theorem mate_val (t : Ind Q j a γ (Res Q i a γ M)) :
    (mate Q a γ i j M t).1 =
      liftedCounit Q a γ i j M
        (crossingLinear Q a γ i j (Res Q i a γ M)
          (BalancedTensor.tmul (indGenerator Q i a ({j} + γ)) t)) := rfl

/-- Applying the original inverse Hom equivalence recovers crossing followed by counit. -/
theorem mate_unmate :
    homFromRes Q i a ({j} + γ) (mate Q a γ i j M) =
      (liftedCounit Q a γ i j M).comp
        (crossingLinear Q a γ i j (Res Q i a γ M)) :=
  homFromRes_homToRes Q i a ({j} + γ) _

/-- Evaluation of the original ordinary-adjunction mate on arbitrary modules. -/
theorem mate_tmul (y : IndCorner Q j a γ) (m : Res Q i a γ M) :
    (mate Q a γ i j M (BalancedTensor.tmul y m)).1 =
      BalancedTensor.tmul (factor Q a γ i j y) m.1 := by
  change counitInd Q a γ i j M
    (crossing Q a γ i j (Res Q i a γ M)
      (BalancedTensor.tmul (indGenerator Q i a ({j} + γ))
        (BalancedTensor.tmul y m))) = _
  rw [crossing_tmul]
  change BalancedTensor.tmul
    ((κ Q a γ i j).symm (lastIdem Q i a ({j} + γ)) • factor Q a γ i j y)
    (lastIdem Q i a γ • m.1) = _
  rw [factor_upperCut, m.2]

/-- The requested formula, with the corner coefficient displayed rather than abbreviated. -/
theorem mate_tmul_explicit (y : IndCorner Q j a γ) (m : Res Q i a γ M) :
    (mate Q a γ i j M (BalancedTensor.tmul y m)).1 =
      BalancedTensor.tmul
        (⟨(κ Q a γ i j).symm (α y.1 * coefficient Q a γ i j),
          (factor Q a γ i j y).2⟩ : IndCorner Q j a ({i} + γ)) m.1 :=
  mate_tmul Q a γ i j M y m

end Categorification.KLR.KLRAlgebra.AbsentColour.MixedMate
