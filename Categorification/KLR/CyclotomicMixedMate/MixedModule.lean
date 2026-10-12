/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicAdjunction

/-!
# Lower mixed induction/restriction tensors

`indResEquiv` identifies the original composite with its balanced lower tensor,
naturally in arbitrary modules. This supplies the lower comparison for the mixed mate.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.MixedModule
open MulOpposite
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (γ : Multiset I) (i j : I)
  (a : I → Polynomial k)
local notation "R" => CycKLR k Q a γ
local notation "A" => CycKLR k Q a ((Singleton.singleton j : Multiset I) + γ)
local notation "C" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)
local notation "ι" => cyclotomicLast Q i a γ
local notation "e" => lastIdem Q i a γ

abbrev Coefficient := Res Q i a γ C
abbrev Lower := Ind Q j a γ (Coefficient Q γ i a)

/-- Right multiplication on the actual restriction coefficient. -/
def rightMul (c : C) : Coefficient Q γ i a →ₗ[R] Coefficient Q γ i a where
  toFun y := ⟨y.1 * c, by
    change e * (y.1 * c) = y.1 * c
    rw [← mul_assoc]
    exact congrArg (· * c) y.2⟩
  map_add' y z := Subtype.ext (add_mul _ _ _)
  map_smul' r y := Subtype.ext (mul_assoc _ _ _)

instance lowerOpModule : Module Cᵐᵒᵖ (Lower Q γ i j a) where
  smul c := BalancedTensor.mapRight (rightMul Q γ i a c.unop)
  one_smul z := by
    change BalancedTensor.mapRight (rightMul Q γ i a 1) z = z
    induction z using BalancedTensor.induction_on with
    | zero => exact map_zero _
    | add z t hz ht => simp only [map_add, hz, ht]
    | tmul x y =>
      change BalancedTensor.tmul x (rightMul Q γ i a 1 y) = _
      have h : rightMul Q γ i a 1 y = y := Subtype.ext (mul_one _)
      rw [h]
  mul_smul c d z := by
    change BalancedTensor.mapRight (rightMul Q γ i a (d.unop * c.unop)) z =
      BalancedTensor.mapRight (rightMul Q γ i a c.unop)
        (BalancedTensor.mapRight (rightMul Q γ i a d.unop) z)
    induction z using BalancedTensor.induction_on with
    | zero => simp only [map_zero]
    | add z t hz ht => simp only [map_add, hz, ht]
    | tmul x y =>
      change BalancedTensor.tmul x (rightMul Q γ i a (d.unop * c.unop) y) =
        BalancedTensor.tmul x (rightMul Q γ i a c.unop (rightMul Q γ i a d.unop y))
      congr 1
      exact Subtype.ext (mul_assoc _ _ _).symm
  smul_zero c := map_zero _
  smul_add c := map_add _
  add_smul c d z := by
    change BalancedTensor.mapRight (rightMul Q γ i a (c.unop + d.unop)) z =
      BalancedTensor.mapRight (rightMul Q γ i a c.unop) z +
        BalancedTensor.mapRight (rightMul Q γ i a d.unop) z
    induction z using BalancedTensor.induction_on with
    | zero => simp only [map_zero, add_zero]
    | add z t hz ht => simp only [map_add, hz, ht]; abel
    | tmul x y =>
      change BalancedTensor.tmul x (rightMul Q γ i a (c.unop + d.unop) y) = _
      have h : rightMul Q γ i a (c.unop + d.unop) y =
          rightMul Q γ i a c.unop y + rightMul Q γ i a d.unop y := Subtype.ext (mul_add _ _ _)
      rw [h, BalancedTensor.tmul_add]
      rfl
  zero_smul z := by
    change BalancedTensor.mapRight (rightMul Q γ i a 0) z = 0
    induction z using BalancedTensor.induction_on with
    | zero => exact map_zero _
    | add z t hz ht => simp only [map_add, hz, ht, add_zero]
    | tmul x y =>
      change BalancedTensor.tmul x (rightMul Q γ i a 0 y) = _
      have h : rightMul Q γ i a 0 y = 0 := Subtype.ext (mul_zero _)
      rw [h, BalancedTensor.tmul_zero]

instance lowerComm : SMulCommClass A Cᵐᵒᵖ (Lower Q γ i j a) where
  smul_comm b c z := (map_smul (BalancedTensor.mapRight (rightMul Q γ i a c.unop)) b z).symm

@[simp] theorem lower_op_tmul (c : C) (x : IndCorner Q j a γ) (y : Coefficient Q γ i a) :
    op c • (BalancedTensor.tmul x y : Lower Q γ i j a) =
      BalancedTensor.tmul x (rightMul Q γ i a c y) := rfl

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (CycKLR k Q a ({i} + γ)) N] [IsScalarTower k (CycKLR k Q a ({i} + γ)) N]
abbrev FE := Ind Q j a γ (Res Q i a γ N)
abbrev LowerTensor := BalancedTensor k A C (Lower Q γ i j a) N

def coeffAct : Coefficient Q γ i a →ₗ[k] N →ₗ[k] Res Q i a γ N :=
  LinearMap.mk₂ k (fun y n => ⟨y.1 • n, by
    change e • (y.1 • n) = y.1 • n
    rw [smul_smul]
    exact congrArg (· • n) y.2⟩)
    (fun y z n => Subtype.ext (add_smul _ _ _))
    (fun c y n => Subtype.ext (smul_assoc _ _ _))
    (fun y n m => Subtype.ext (smul_add _ _ _))
    (fun c y n => Subtype.ext (smul_comm _ c _))

def lowerAct (n : N) : Lower Q γ i j a →ₗ[A] FE Q γ i j a N :=
  BalancedTensor.liftB
    ((BalancedTensor.mkBil k A R (IndCorner Q j a γ) (Res Q i a γ N)).compl₂
      ((coeffAct Q γ i a N).flip n))
    (fun x r y => by
      change BalancedTensor.tmul (op r • x) (coeffAct Q γ i a N y n) = _
      rw [BalancedTensor.op_smul_tmul]
      congr 1
      exact Subtype.ext (mul_smul _ _ _).symm)
    (fun b x y => (BalancedTensor.smul_tmul' b x _).symm)

@[simp] theorem lowerAct_tmul (n : N) (x : IndCorner Q j a γ) (y : Coefficient Q γ i a) :
    lowerAct Q γ i j a N n (BalancedTensor.tmul x y) =
      BalancedTensor.tmul x (coeffAct Q γ i a N y n) := rfl

def lowerToFE : LowerTensor Q γ i j a N →ₗ[A] FE Q γ i j a N :=
  BalancedTensor.liftB
    (LinearMap.mk₂ k (fun t n => lowerAct Q γ i j a N n t)
      (fun t s n => map_add _ t s)
      (fun c t n => (lowerAct Q γ i j a N n).map_smul_of_tower c t)
      (fun t n m => by
        induction t using BalancedTensor.induction_on with
        | zero => simp only [map_zero, add_zero]
        | add t s ht hs => simp only [map_add, ht, hs]; abel
        | tmul x y => simp only [lowerAct_tmul, map_add, BalancedTensor.tmul_add])
      (fun c t n => by
        induction t using BalancedTensor.induction_on with
        | zero => simp only [map_zero, smul_zero]
        | add t s ht hs => simp only [map_add, ht, hs, smul_add]
        | tmul x y => rw [lowerAct_tmul, lowerAct_tmul, map_smul, BalancedTensor.tmul_smul]))
    (fun t c n => by
      change lowerAct Q γ i j a N n (op c • t) = lowerAct Q γ i j a N (c • n) t
      induction t using BalancedTensor.induction_on with
      | zero => simp only [smul_zero, map_zero]
      | add t s ht hs => simp only [smul_add, map_add, ht, hs]
      | tmul x y =>
        rw [lower_op_tmul, lowerAct_tmul, lowerAct_tmul]
        congr 1
        exact Subtype.ext (mul_smul _ _ _))
    (fun b t n => (lowerAct Q γ i j a N n).map_smul b t)

@[simp] theorem lowerToFE_tmul (x : IndCorner Q j a γ) (y : Coefficient Q γ i a) (n : N) :
    lowerToFE Q γ i j a N (BalancedTensor.tmul (BalancedTensor.tmul x y) n) =
      BalancedTensor.tmul x (coeffAct Q γ i a N y n) := rfl

def coeffIdem : Coefficient Q γ i a := ⟨e, lastIdem_mul Q i a γ⟩

def insertIdem : IndCorner Q j a γ →ₗ[A] Lower Q γ i j a where
  toFun x := BalancedTensor.tmul x (coeffIdem Q γ i a)
  map_add' x y := BalancedTensor.add_tmul x y _
  map_smul' b x := (BalancedTensor.smul_tmul' b x _).symm

theorem insertIdem_balance (x : IndCorner Q j a γ) (r : R) :
    insertIdem Q γ i j a (op r • x) = op (ι r) • insertIdem Q γ i j a x := by
  change BalancedTensor.tmul (op r • x) (coeffIdem Q γ i a) = _
  rw [BalancedTensor.op_smul_tmul]
  change BalancedTensor.tmul x (r • coeffIdem Q γ i a) =
    BalancedTensor.tmul x (rightMul Q γ i a (ι r) (coeffIdem Q γ i a))
  congr 1
  apply Subtype.ext
  change ι r * ι 1 = ι 1 * ι r
  rw [← map_mul, ← map_mul, mul_one, one_mul]

def feToLower : FE Q γ i j a N →ₗ[A] LowerTensor Q γ i j a N :=
  BalancedTensor.liftB
    (((BalancedTensor.mkBil k A C (Lower Q γ i j a) N).comp
      ((insertIdem Q γ i j a).restrictScalars k)).compl₂ (fixSub k N e).subtype)
    (fun x r n => by
      change BalancedTensor.tmul (insertIdem Q γ i j a (op r • x)) n.1 = _
      rw [insertIdem_balance, BalancedTensor.op_smul_tmul]; rfl)
    (fun b x n => by
      change BalancedTensor.tmul (insertIdem Q γ i j a (b • x)) n.1 =
        b • BalancedTensor.tmul (insertIdem Q γ i j a x) n.1
      rw [map_smul, BalancedTensor.smul_tmul'])

@[simp] theorem feToLower_tmul (x : IndCorner Q j a γ) (n : Res Q i a γ N) :
    feToLower Q γ i j a N (BalancedTensor.tmul x n) =
      BalancedTensor.tmul (insertIdem Q γ i j a x) n.1 := rfl

theorem lowerToFE_feToLower (t : FE Q γ i j a N) :
    lowerToFE Q γ i j a N (feToLower Q γ i j a N t) = t := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul x n =>
    rw [feToLower_tmul]
    change lowerToFE Q γ i j a N (BalancedTensor.tmul
      (BalancedTensor.tmul x (coeffIdem Q γ i a)) n.1) = _
    rw [lowerToFE_tmul]
    congr 1
    exact Subtype.ext n.2

theorem feToLower_lowerToFE (t : LowerTensor Q γ i j a N) :
    feToLower Q γ i j a N (lowerToFE Q γ i j a N t) = t := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul z n =>
    induction z using BalancedTensor.induction_on with
    | zero => simp only [BalancedTensor.zero_tmul, map_zero]
    | add z t hz ht => simp only [BalancedTensor.add_tmul, map_add, hz, ht]
    | tmul x y =>
      rw [lowerToFE_tmul, feToLower_tmul]
      change BalancedTensor.tmul (BalancedTensor.tmul x (coeffIdem Q γ i a)) (y.1 • n) = _
      rw [← BalancedTensor.op_smul_tmul, lower_op_tmul]
      congr 2
      exact Subtype.ext y.2

/-- The original rectangular induction/restriction composite, on every module. -/
def indResEquiv : FE Q γ i j a N ≃ₗ[A] LowerTensor Q γ i j a N :=
  LinearEquiv.ofLinearMap (feToLower Q γ i j a N) (lowerToFE Q γ i j a N)
    (LinearMap.ext (feToLower_lowerToFE Q γ i j a N))
    (LinearMap.ext (lowerToFE_feToLower Q γ i j a N))

variable {N' : Type*} [AddCommGroup N'] [Module k N']
  [Module (CycKLR k Q a ({i} + γ)) N'] [IsScalarTower k (CycKLR k Q a ({i} + γ)) N']
abbrev feMap (f : N →ₗ[C] N') : FE Q γ i j a N →ₗ[A] FE Q γ i j a N' :=
  indMap Q j a γ (Res Q i a γ N) (resMap Q i a γ N f)

theorem indResEquiv_natural (f : N →ₗ[C] N') (t : FE Q γ i j a N) :
    indResEquiv Q γ i j a N' (feMap Q γ i j a N f t) =
      BalancedTensor.mapRight f (indResEquiv Q γ i j a N t) := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul x n => rfl

theorem indResEquiv_symm_natural (f : N →ₗ[C] N') (t : LowerTensor Q γ i j a N) :
    (indResEquiv Q γ i j a N').symm (BalancedTensor.mapRight f t) =
      feMap Q γ i j a N f ((indResEquiv Q γ i j a N).symm t) := by
  apply (indResEquiv Q γ i j a N').injective
  rw [LinearEquiv.apply_symm_apply, indResEquiv_natural, LinearEquiv.apply_symm_apply]

section Bundled
open CategoryTheory
open scoped ModuleCat.Algebra

/-- The coefficient tensor functor on all modules, with the actual right action. -/
def lowerTensorFunctor : ModuleCat.{max u v w} C ⥤ ModuleCat.{max u v w} A where
  obj M := ModuleCat.of A (LowerTensor Q γ i j a M)
  map f := ModuleCat.ofHom (BalancedTensor.mapRight f.hom)
  map_id _ := ModuleCat.hom_ext BalancedTensor.mapRight_id
  map_comp f g := ModuleCat.hom_ext (BalancedTensor.mapRight_comp f.hom g.hom)

/-- Only the canonical ground-ring module presentation is changed here. -/
def feRebase (M : ModuleCat.{max u v w} C) :
    FE Q γ i j a M →ₗ[A] (restrictionFunctor Q i a γ ⋙ inductionFunctor Q j a γ).obj M :=
  BalancedTensor.mapRight (N := Res Q i a γ M) (N' := (restrictionFunctor Q i a γ).obj M)
    (LinearMap.id : Res Q i a γ M →ₗ[R] Res Q i a γ M)

def feUnbase (M : ModuleCat.{max u v w} C) :
    (restrictionFunctor Q i a γ ⋙ inductionFunctor Q j a γ).obj M →ₗ[A] FE Q γ i j a M :=
  BalancedTensor.mapRight (N := (restrictionFunctor Q i a γ).obj M) (N' := Res Q i a γ M)
    (LinearMap.id : Res Q i a γ M →ₗ[R] Res Q i a γ M)

def feRebaseEquiv (M : ModuleCat.{max u v w} C) :
    FE Q γ i j a M ≃ₗ[A] (restrictionFunctor Q i a γ ⋙ inductionFunctor Q j a γ).obj M :=
  LinearEquiv.ofLinearMap (feRebase Q γ i j a M) (feUnbase Q γ i j a M)
    (BalancedTensor.extB fun _ _ => rfl) (BalancedTensor.extB fun _ _ => rfl)

/-- Comparison on the original module functors, not only their regular modules. -/
def indResNatIso :
    restrictionFunctor.{u,v,w} Q i a γ ⋙ inductionFunctor Q j a γ ≅
      lowerTensorFunctor Q γ i j a :=
  NatIso.ofComponents (fun M =>
    { hom := ModuleCat.ofHom ((indResEquiv Q γ i j a M).toLinearMap.comp (feUnbase Q γ i j a M))
      inv := ModuleCat.ofHom
        ((feRebase Q γ i j a M).comp (indResEquiv Q γ i j a M).symm.toLinearMap)
      hom_inv_id := by
        apply ModuleCat.hom_ext
        apply BalancedTensor.extB
        intro x m
        change feRebase Q γ i j a M
          ((indResEquiv Q γ i j a M).symm
            (indResEquiv Q γ i j a M (BalancedTensor.tmul x m))) = _
        rw [LinearEquiv.symm_apply_apply]
        rfl
      inv_hom_id := by
        apply ModuleCat.hom_ext
        ext t
        change indResEquiv Q γ i j a M
          (feUnbase Q γ i j a M
            (feRebase Q γ i j a M ((indResEquiv Q γ i j a M).symm t))) = t
        have h : ∀ s : FE Q γ i j a M,
            feUnbase Q γ i j a M (feRebase Q γ i j a M s) = s :=
          (feRebaseEquiv Q γ i j a M).symm_apply_apply
        rw [h]
        exact (indResEquiv Q γ i j a M).apply_symm_apply t })
    (fun f => by
      apply ModuleCat.hom_ext
      apply BalancedTensor.extB
      intro x m
      rfl)

@[simp] theorem indResNatIso_hom_tmul (M : ModuleCat.{max u v w} C)
    (x : IndCorner Q j a γ) (m : Res Q i a γ M) :
    (indResNatIso Q γ i j a).hom.app M (BalancedTensor.tmul x m) =
      BalancedTensor.tmul (BalancedTensor.tmul x (coeffIdem Q γ i a)) m.1 := rfl

@[simp] theorem indResNatIso_inv_tmul (M : ModuleCat.{max u v w} C)
    (x : IndCorner Q j a γ) (y : Coefficient Q γ i a) (m : M) :
    (indResNatIso Q γ i j a).inv.app M (BalancedTensor.tmul (BalancedTensor.tmul x y) m) =
      feRebase Q γ i j a M (BalancedTensor.tmul x (coeffAct Q γ i a M y m)) := rfl

end Bundled
end Categorification.KLR.KLRAlgebra.AbsentColour.MixedModule
