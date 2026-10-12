/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.MixedModule
import Categorification.KLR.CyclotomicMixedMate.Naturality

/-!
# The upper mixed corner comparison

`upperComparison` identifies the actual idempotent restriction of induction with
the rectangular corner tensor. Explicit cut/include inverses require no flatness.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.MixedComparison
open MulOpposite
open MixedMate
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  (γ : Multiset I) (i j : I)
local notation "A" => CycKLR k Q a ((Singleton.singleton j : Multiset I) + γ)
local notation "C" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)
local notation "V" => CycKLR k Q a
  ((Singleton.singleton j : Multiset I) + ((Singleton.singleton i : Multiset I) + γ))
local notation "α" => cyclotomicLast Q i a ((Singleton.singleton j : Multiset I) + γ)
local notation "β" => cyclotomicLast Q j a ((Singleton.singleton i : Multiset I) + γ)

/-- Original upper left inclusion, in the reversed upper algebra. -/
def leftInc : A →ₙₐ[k] V := (κ Q a γ i j).symm.toAlgHom.toNonUnitalAlgHom.comp α

/-- Actual rectangular corner, with both original cuts. -/
def cornerSub : Submodule k V where
  carrier := {z | leftInc Q a γ i j 1 * z = z ∧ z * β 1 = z}
  zero_mem' := by change _ * 0 = 0 ∧ 0 * _ = 0; simp only [mul_zero, zero_mul, and_self]
  add_mem' hx hy := by
    change _ * (_ + _) = _ + _ ∧ (_ + _) * _ = _ + _
    simp only [mul_add, add_mul, hx.1, hx.2, hy.1, hy.2, and_self]
  smul_mem' c z hz := by
    change _ * (c • z) = c • z ∧ (c • z) * _ = c • z
    simp only [mul_smul_comm, smul_mul_assoc, hz.1, hz.2, and_self]
abbrev Corner := ↥(cornerSub Q a γ i j)

instance cornerModule : Module A (Corner Q a γ i j) where
  smul b z := ⟨leftInc Q a γ i j b * z.1, by
    constructor
    · rw [← mul_assoc, ← map_mul, one_mul]
    · rw [mul_assoc, z.2.2]⟩
  one_smul z := Subtype.ext z.2.1
  mul_smul b c z := Subtype.ext (by
    change leftInc Q a γ i j (b * c) * z.1 =
      leftInc Q a γ i j b * (leftInc Q a γ i j c * z.1)
    rw [map_mul, mul_assoc])
  smul_zero b := Subtype.ext (mul_zero _)
  smul_add b z t := Subtype.ext (mul_add _ _ _)
  add_smul b c z := Subtype.ext (by
    change leftInc Q a γ i j (b + c) * z.1 =
      leftInc Q a γ i j b * z.1 + leftInc Q a γ i j c * z.1
    rw [map_add, add_mul])
  zero_smul z := Subtype.ext (by
    change leftInc Q a γ i j 0 * z.1 = 0
    rw [map_zero, zero_mul])

instance cornerTower : IsScalarTower k A (Corner Q a γ i j) where
  smul_assoc c b z := Subtype.ext (by
    change leftInc Q a γ i j (c • b) * z.1 = c • (leftInc Q a γ i j b * z.1)
    rw [map_smul, smul_mul_assoc])

instance cornerOpModule : Module Cᵐᵒᵖ (Corner Q a γ i j) where
  smul c z := ⟨z.1 * β c.unop, by
    constructor
    · rw [← mul_assoc, z.2.1]
    · rw [mul_assoc, ← map_mul, mul_one]⟩
  one_smul z := Subtype.ext z.2.2
  mul_smul b c z := Subtype.ext (by
    change z.1 * β (c.unop * b.unop) = (z.1 * β c.unop) * β b.unop
    rw [map_mul, mul_assoc])
  smul_zero c := Subtype.ext (zero_mul _)
  smul_add c z t := Subtype.ext (add_mul _ _ _)
  add_smul b c z := Subtype.ext (by
    change z.1 * β (b.unop + c.unop) = z.1 * β b.unop + z.1 * β c.unop
    rw [map_add, mul_add])
  zero_smul z := Subtype.ext (by
    change z.1 * β 0 = 0
    rw [map_zero, mul_zero])

instance cornerComm : SMulCommClass A Cᵐᵒᵖ (Corner Q a γ i j) where
  smul_comm b c z := Subtype.ext (mul_assoc (leftInc Q a γ i j b) z.1 (β c.unop)).symm

def cornerToInd : Corner Q a γ i j →ₗ[k] IndCorner Q j a ({i} + γ) where
  toFun z := ⟨z.1, z.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def leftCut : IndCorner Q j a ({i} + γ) →ₗ[k] Corner Q a γ i j where
  toFun z := ⟨leftInc Q a γ i j 1 * z.1, by
    constructor
    · rw [← mul_assoc, ← map_mul, one_mul]
    · rw [mul_assoc]; exact congrArg (leftInc Q a γ i j 1 * ·) z.2⟩
  map_add' z t := Subtype.ext (mul_add _ _ _)
  map_smul' c z := Subtype.ext (mul_smul_comm _ _ _)

variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)) M]
  [IsScalarTower k (CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)) M]
abbrev UpperTensor := BalancedTensor k A C (Corner Q a γ i j) M
open scoped ModuleCat.Algebra in
abbrev Target := Res Q i a ({j} + γ)
  ((upperTransport Q a γ i j).obj (ModuleCat.of V (Ind Q j a ({i} + γ) M)))

def cutTensor : Ind Q j a ({i} + γ) M →ₗ[k] UpperTensor Q a γ i j M :=
  BalancedTensor.lift
    ((BalancedTensor.mkBil k A C (Corner Q a γ i j) M).comp (leftCut Q a γ i j))
    (fun z c m => by
      change BalancedTensor.tmul (leftCut Q a γ i j (op c • z)) m = _
      have h : leftCut Q a γ i j (op c • z) = op c • leftCut Q a γ i j z :=
        Subtype.ext (mul_assoc _ _ _).symm
      rw [h, BalancedTensor.op_smul_tmul]; rfl)

def includeBil : Corner Q a γ i j →ₗ[k] M →ₗ[k] Ind Q j a ({i} + γ) M :=
  LinearMap.mk₂ k (fun z m => BalancedTensor.tmul (cornerToInd Q a γ i j z) m)
    (fun z t m => by rw [map_add, BalancedTensor.add_tmul])
    (fun c z m => by rw [map_smul, BalancedTensor.smul_tmul])
    (fun z m n => BalancedTensor.tmul_add _ m n)
    (fun c z m => BalancedTensor.tmul_smul c _ m)

omit [IsScalarTower k C M] in
theorem includeBil_balance (z : Corner Q a γ i j) (c : C) (m : M) :
    includeBil Q a γ i j M (op c • z) m = includeBil Q a γ i j M z (c • m) := by
  change BalancedTensor.tmul (op c • cornerToInd Q a γ i j z) m =
    BalancedTensor.tmul (cornerToInd Q a γ i j z) (c • m)
  exact BalancedTensor.op_smul_tmul _ _ _

def includeTensor : UpperTensor Q a γ i j M →ₗ[k] Ind Q j a ({i} + γ) M :=
  BalancedTensor.lift (includeBil Q a γ i j M) (includeBil_balance Q a γ i j M)

omit [IsScalarTower k C M] in
@[simp] theorem cutTensor_tmul (z : IndCorner Q j a ({i} + γ)) (m : M) :
    cutTensor Q a γ i j M (BalancedTensor.tmul z m) =
      BalancedTensor.tmul (leftCut Q a γ i j z) m := rfl
omit [IsScalarTower k C M] in
@[simp] theorem includeTensor_tmul (z : Corner Q a γ i j) (m : M) :
    includeTensor Q a γ i j M (BalancedTensor.tmul z m) =
      BalancedTensor.tmul (cornerToInd Q a γ i j z) m := rfl

omit [IsScalarTower k C M] in
theorem cut_include (t : UpperTensor Q a γ i j M) :
    cutTensor Q a γ i j M (includeTensor Q a γ i j M t) = t := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul z m =>
    rw [includeTensor_tmul, cutTensor_tmul]
    have h : leftCut Q a γ i j (cornerToInd Q a γ i j z) = z := Subtype.ext z.2.1
    rw [h]

omit [IsScalarTower k C M] in
theorem include_cut
    (t : BalancedTensor k V C (IndCorner Q j a ({i} + γ)) M) :
    @Eq (Ind Q j a ({i} + γ) M)
      ((includeTensor (k := k) Q a γ i j M).toFun
        ((cutTensor (k := k) Q a γ i j M).toFun t))
      (leftInc Q a γ i j 1 • t) := by
  simp only [LinearMap.toFun_eq_coe]
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add s t hs ht => simp only [map_add, hs, ht, smul_add]
  | tmul z m => rw [cutTensor_tmul, includeTensor_tmul, BalancedTensor.smul_tmul']; rfl

omit [IsScalarTower k C M] in
theorem includeTensor_fixed (t : UpperTensor Q a γ i j M) :
    leftInc Q a γ i j 1 • includeTensor Q a γ i j M t = includeTensor Q a γ i j M t := by
  rw [← include_cut, LinearMap.toFun_eq_coe, LinearMap.toFun_eq_coe, cut_include]

/-- Concrete upper comparison on arbitrary modules, proved by the actual projector. -/
def upperComparison : Target Q a γ i j M ≃ₗ[A] UpperTensor Q a γ i j M where
  toFun z := cutTensor Q a γ i j M z.1
  invFun t := ⟨includeTensor Q a γ i j M t, includeTensor_fixed Q a γ i j M t⟩
  left_inv z := Subtype.ext ((include_cut Q a γ i j M z.1).trans z.2)
  right_inv := cut_include Q a γ i j M
  map_add' z t := map_add _ z.1 t.1
  map_smul' b z := by
    change cutTensor Q a γ i j M (leftInc Q a γ i j b • (show Ind Q j a ({i} + γ) M from z.1)) =
      b • cutTensor Q a γ i j M z.1
    have h : ∀ t : Ind Q j a ({i} + γ) M,
        cutTensor Q a γ i j M (leftInc Q a γ i j b • t) =
          b • cutTensor Q a γ i j M t := by
      intro t
      induction t using BalancedTensor.induction_on with
      | zero => simp only [smul_zero, map_zero]
      | add s t hs ht => simp only [smul_add, map_add, hs, ht]
      | tmul v m =>
        rw [BalancedTensor.smul_tmul', cutTensor_tmul, cutTensor_tmul, BalancedTensor.smul_tmul']
        congr 1
        apply Subtype.ext
        change leftInc Q a γ i j 1 * (leftInc Q a γ i j b * v.1) =
          leftInc Q a γ i j b * (leftInc Q a γ i j 1 * v.1)
        rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, one_mul, mul_one]
    exact h z.1

/-- The actual original mate evaluated after the lower comparison inverse. -/
theorem mate_lower_generator (x : IndCorner Q j a γ)
    (y : MixedModule.Coefficient Q γ i a) (m : M) :
    (mate Q a γ i j M
      ((MixedModule.indResEquiv Q γ i j a M).symm
        (BalancedTensor.tmul (BalancedTensor.tmul x y) m))).1 =
      BalancedTensor.tmul (op y.1 • factor Q a γ i j x) m := by
  change (mate Q a γ i j M (BalancedTensor.tmul x
    (MixedModule.coeffAct Q γ i a M y m))).1 = _
  rw [mate_tmul, BalancedTensor.op_smul_tmul]
  rfl

/-- Balancing removes the original lower cut, preserving the sign and product order. -/
theorem factor_right_signed (x : IndCorner Q j a γ)
    (y : MixedModule.Coefficient Q γ i a) :
    (op y.1 • factor Q a γ i j x).1 =
      (κ Q a γ i j).symm (α x.1 * (-CycKLR.mk k Q a _ (ψ (Multiset.card γ))) *
        κ Q a γ i j (β y.1)) := by
  apply (κ Q a γ i j).injective
  change κ Q a γ i j ((κ Q a γ i j).symm (α x.1 * coefficient Q a γ i j) * β y.1) = _
  simp only [map_mul, AlgEquiv.apply_symm_apply]
  rw [coefficient_eq, mul_assoc, mul_assoc, ← map_mul, ← map_mul]
  have hy : cyclotomicLast Q i a γ 1 * y.1 = y.1 := y.2
  rw [hy, ← mul_assoc]

end Categorification.KLR.KLRAlgebra.AbsentColour.MixedComparison
