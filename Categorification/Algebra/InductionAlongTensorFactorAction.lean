/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTensorFactor
import Categorification.Algebra.InductionAlongRes

/-!
# The second-factor action on induction along a map of one tensor factor

Let `φ : A → B` and `ψ : A ⊗ C → B ⊗ C` with `ψ (a ⊗ c) = φ a ⊗ c`. For a left
`A ⊗ C`-module `N`, the factor `C` acts on `N|_A` by `A`-linear maps `1 ⊗ c`
(`leftFactorCAct`). This file records how the identifications of
`Categorification.Algebra.InductionAlongTensorFactor` interact with these actions:

* `indLeftFactorEquivB`: `(Ind_ψ N)|_B ≅ Ind_φ (N|_A)` is `B`-linear, and carries the action of
  `1 ⊗ c` to `Ind_φ` of the action of `1 ⊗ c` (`indLeftFactorEquivB_cAct`);
* `resLeftFactorEquiv`: `(Res_ψ M)|_A ≅ Res_φ (M|_B)` for a `B ⊗ C`-module `M`, compatibly with
  the actions of `C` (`resLeftFactorEquiv_cAct`);
* `linearEquivOfLeftFactor`: an `A`-linear isomorphism `X|_A ≅ Y|_A` commuting with the actions
  of `C` is an isomorphism of `A ⊗ C`-modules.

Together they lift natural isomorphisms between composites of induction and restriction over
one factor to isomorphisms of modules over the tensor product. This is how the commutation
relations between the functors `₁Eⱼ`, `₁Fᵢ` of Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, §5, on modules over `T^{λ₁} ⊗ T^{λ₂}`, are obtained
from those on `T^{λ₁}`-modules, as used in the dimension count of the proof of Proposition 5.5.
The same results are proved for maps of the second factor.
-/

namespace Categorification

open MulOpposite
open scoped TensorProduct

noncomputable section

namespace InductionAlong

universe u w

section IndKMap

variable {k : Type*} [CommRing k] {A : Type u} [Ring A] {B : Type u} [Ring B] [Algebra k B]
  {φ : A →ₙ+* B} {N N' : Type w} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']

/-- Functoriality of `IndK k · φ` in the module. -/
def IndK.map (g : N →ₗ[A] N') : IndK k N φ →ₗ[B] IndK k N' φ := Ind.map g

@[simp] theorem IndK.map_tmul (g : N →ₗ[A] N') (z : Corner φ) (n : N) :
    IndK.map (k := k) g (IndK.tmul z n) = IndK.tmul z (g n) := rfl

end IndKMap

/-! ### The first factor -/

section LeftFactor

variable {k : Type*} [CommRing k] {A : Type u} [Ring A] [Algebra k A] {C : Type u} [Ring C]
  [Algebra k C]

section CAct

variable {N : Type w} [AddCommGroup N] [Module (A ⊗[k] C) N]

/-- The action of `1 ⊗ c` on `N|_A`, an `A`-linear map. -/
def leftFactorCAct (c : C) : LeftFactorRes k A C N →ₗ[A] LeftFactorRes k A C N where
  toFun x := (show N from ((1 : A) ⊗ₜ[k] c) • (show N from x))
  map_add' x y := smul_add (((1 : A) ⊗ₜ[k] c)) (show N from x) (show N from y)
  map_smul' a x := by
    change ((1 : A) ⊗ₜ[k] c) • ((a ⊗ₜ[k] (1 : C)) • (show N from x)) =
      (a ⊗ₜ[k] (1 : C)) • (((1 : A) ⊗ₜ[k] c) • (show N from x))
    rw [← mul_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul, mul_one]

theorem leftFactorCAct_apply (c : C) (x : LeftFactorRes k A C N) :
    leftFactorCAct c x = (show N from ((1 : A) ⊗ₜ[k] c) • (show N from x)) := rfl

variable {X Y : Type w} [AddCommGroup X] [Module (A ⊗[k] C) X] [AddCommGroup Y]
  [Module (A ⊗[k] C) Y]

/-- **An isomorphism of first factors commuting with the second factor**: an `A`-linear
isomorphism `X|_A ≅ Y|_A` commuting with the actions of `C` is `A ⊗ C`-linear. -/
def linearEquivOfLeftFactor (e : LeftFactorRes k A C X ≃ₗ[A] LeftFactorRes k A C Y)
    (he : ∀ (c : C) (x : LeftFactorRes k A C X),
      e (leftFactorCAct c x) = leftFactorCAct c (e x)) : X ≃ₗ[A ⊗[k] C] Y where
  toFun x := (show Y from e x)
  invFun y := (show X from e.symm y)
  map_add' x y := e.map_add x y
  map_smul' t x := by
    induction t using TensorProduct.inductionOn with
    | add s t hs ht =>
      simp only [RingHom.id_apply] at hs ht ⊢
      rw [add_smul]
      exact (map_add e (s • x) (t • x)).trans
        ((congrArg₂ (· + ·) hs ht).trans (add_smul s t (show Y from e x)).symm)
    | tmul a c =>
      have h : a ⊗ₜ[k] c = (a ⊗ₜ[k] (1 : C)) * ((1 : A) ⊗ₜ[k] c) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [RingHom.id_apply, h, mul_smul, mul_smul]
      exact (e.map_smul a (leftFactorCAct c x)).trans
        (congrArg (fun y => a • y) (he c x))
  left_inv x := e.symm_apply_apply x
  right_inv y := e.apply_symm_apply y

theorem linearEquivOfLeftFactor_apply (e : LeftFactorRes k A C X ≃ₗ[A] LeftFactorRes k A C Y)
    (he : ∀ (c : C) (x : LeftFactorRes k A C X),
      e (leftFactorCAct c x) = leftFactorCAct c (e x)) (x : X) :
    linearEquivOfLeftFactor e he x = (show Y from e x) := rfl

end CAct

variable {B : Type u} [Ring B] [Algebra k B] (φ : A →ₙ+* B)
  (hφ : ∀ (c : k) (t : A), φ (c • t) = c • φ t)
  (ψ : A ⊗[k] C →ₙ+* B ⊗[k] C) (hψ : ∀ (a : A) (c : C), ψ (a ⊗ₜ c) = φ a ⊗ₜ c)

section Ind

variable {N : Type w} [AddCommGroup N] [Module k N] [Module (A ⊗[k] C) N]
  [IsScalarTower k (A ⊗[k] C) N]

theorem leftFactorFwdLin_tmul_one_mul (b : B) (y : B ⊗[k] C) (n : N) :
    leftFactorFwdLin φ hφ ((b ⊗ₜ[k] (1 : C)) * y) n = b • leftFactorFwdLin φ hφ y n := by
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' =>
    rw [mul_add, map_add, LinearMap.add_apply, hy, hy', map_add, LinearMap.add_apply, smul_add]
  | tmul b' c =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, leftFactorFwdLin_tmul,
      leftFactorFwdLin_tmul]
    refine Eq.trans ?_ (Ind.smul_tmul b _ _).symm
    change Ind.tmul _ _ = Ind.tmul _ _
    congr 1
    exact Subtype.ext (mul_assoc b b' (φ 1))

theorem leftFactorFwdLin_one_tmul_mul (c : C) (y : B ⊗[k] C) (n : N) :
    leftFactorFwdLin φ hφ (((1 : B) ⊗ₜ[k] c) * y) n =
      IndK.map (leftFactorCAct c) (leftFactorFwdLin φ hφ y n) := by
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' =>
    rw [mul_add, map_add, LinearMap.add_apply, hy, hy', map_add, LinearMap.add_apply, map_add]
  | tmul b c' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, leftFactorFwdLin_tmul,
      leftFactorFwdLin_tmul]
    refine Eq.trans ?_ (IndK.map_tmul _ _ _).symm
    change Ind.tmul _ _ = Ind.tmul _ _
    rw [leftFactorCAct_apply]
    congr 1
    change ((1 : A) ⊗ₜ[k] (c * c')) • n = ((1 : A) ⊗ₜ[k] c) • ((1 : A) ⊗ₜ[k] c') • n
    rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem indLeftFactorEquiv_tmul_one_smul (b : B) (t : IndK k N ψ) :
    indLeftFactorEquiv φ hφ ψ hψ ((b ⊗ₜ[k] (1 : C)) • t) =
      b • indLeftFactorEquiv φ hφ ψ hψ t := by
  induction t using Ind.induction_on with
  | zero =>
    exact (congrArg (indLeftFactorEquiv φ hφ ψ hψ) (smul_zero _)).trans
      ((map_zero _).trans (smul_zero _).symm)
  | tmul z n =>
    refine (congrArg (indLeftFactorEquiv φ hφ ψ hψ) (Ind.smul_tmul _ z n)).trans ?_
    exact leftFactorFwdLin_tmul_one_mul φ hφ b z.1 n
  | add s t hs ht =>
    exact (congrArg (indLeftFactorEquiv φ hφ ψ hψ) (smul_add _ s t)).trans
      ((map_add _ _ _).trans ((congrArg₂ (· + ·) hs ht).trans
        ((smul_add b _ _).symm.trans (congrArg (fun y => b • y) (map_add _ s t).symm))))

theorem indLeftFactorEquiv_one_tmul_smul (c : C) (t : IndK k N ψ) :
    indLeftFactorEquiv φ hφ ψ hψ (((1 : B) ⊗ₜ[k] c) • t) =
      IndK.map (leftFactorCAct c) (indLeftFactorEquiv φ hφ ψ hψ t) := by
  induction t using Ind.induction_on with
  | zero =>
    exact (congrArg (indLeftFactorEquiv φ hφ ψ hψ) (smul_zero _)).trans
      ((map_zero _).trans (map_zero _).symm)
  | tmul z n =>
    refine (congrArg (indLeftFactorEquiv φ hφ ψ hψ) (Ind.smul_tmul _ z n)).trans ?_
    exact leftFactorFwdLin_one_tmul_mul φ hφ c z.1 n
  | add s t hs ht =>
    exact (congrArg (indLeftFactorEquiv φ hφ ψ hψ) (smul_add _ s t)).trans
      ((map_add _ _ _).trans ((congrArg₂ (· + ·) hs ht).trans
        ((map_add _ _ _).symm.trans
          (congrArg (IndK.map (leftFactorCAct c)) (map_add _ s t).symm))))

/-- **Induction along a map of the first factor, as `B`-modules**:
`(Ind_ψ N)|_B ≅ Ind_φ (N|_A)`. -/
def indLeftFactorEquivB :
    LeftFactorRes k B C (IndK k N ψ) ≃ₗ[B] IndK k (LeftFactorRes k A C N) φ where
  toFun t := indLeftFactorEquiv φ hφ ψ hψ (show IndK k N ψ from t)
  invFun t := (show LeftFactorRes k B C (IndK k N ψ) from
    (indLeftFactorEquiv φ hφ ψ hψ).symm t)
  map_add' s t := map_add (indLeftFactorEquiv φ hφ ψ hψ) s t
  map_smul' b t := indLeftFactorEquiv_tmul_one_smul φ hφ ψ hψ b t
  left_inv t := (indLeftFactorEquiv φ hφ ψ hψ).symm_apply_apply t
  right_inv t := (indLeftFactorEquiv φ hφ ψ hψ).apply_symm_apply t

theorem indLeftFactorEquivB_apply (t : LeftFactorRes k B C (IndK k N ψ)) :
    indLeftFactorEquivB φ hφ ψ hψ t =
      indLeftFactorEquiv φ hφ ψ hψ (show IndK k N ψ from t) := rfl

/-- `indLeftFactorEquivB` carries the action of `1 ⊗ c` to `Ind_φ` of the action of
`1 ⊗ c`. -/
theorem indLeftFactorEquivB_cAct (c : C) (t : LeftFactorRes k B C (IndK k N ψ)) :
    indLeftFactorEquivB φ hφ ψ hψ (leftFactorCAct c t) =
      IndK.map (leftFactorCAct c) (indLeftFactorEquivB φ hφ ψ hψ t) :=
  indLeftFactorEquiv_one_tmul_smul φ hφ ψ hψ c t

end Ind

section Res

variable (M : Type w) [AddCommGroup M] [Module (B ⊗[k] C) M]

include hψ in
theorem leftFactor_one_smul_of_res (m : Res ψ M) :
    φ 1 • (show LeftFactorRes k B C M from m.val) = (show LeftFactorRes k B C M from m.val) := by
  change (φ 1 ⊗ₜ[k] (1 : C)) • m.val = m.val
  rw [← leftFactor_one φ ψ hψ]
  exact m.prop

/-- **Restriction along a map of the first factor**: `(Res_ψ M)|_A ≅ Res_φ (M|_B)`. -/
def resLeftFactorEquiv :
    LeftFactorRes k A C (Res ψ M) ≃ₗ[A] Res φ (LeftFactorRes k B C M) where
  toFun x := Res.mk (show LeftFactorRes k B C M from (show Res ψ M from x).val)
    (leftFactor_one_smul_of_res φ ψ hψ M x)
  invFun y := (show LeftFactorRes k A C (Res ψ M) from Res.mk (show M from y.val) (by
    rw [leftFactor_one φ ψ hψ]
    exact y.prop))
  map_add' x y := Res.ext rfl
  map_smul' a x := Res.ext (by
    change ψ (a ⊗ₜ[k] (1 : C)) • (show Res ψ M from x).val =
      (φ a ⊗ₜ[k] (1 : C)) • (show Res ψ M from x).val
    rw [hψ])
  left_inv x := Res.ext rfl
  right_inv y := Res.ext rfl

theorem resLeftFactorEquiv_val (x : LeftFactorRes k A C (Res ψ M)) :
    (resLeftFactorEquiv φ ψ hψ M x).val = (show Res ψ M from x).val := rfl

/-- `resLeftFactorEquiv` carries the action of `1 ⊗ c` to `Res_φ` of the action of `1 ⊗ c`. -/
theorem resLeftFactorEquiv_cAct (c : C) (x : LeftFactorRes k A C (Res ψ M)) :
    resLeftFactorEquiv φ ψ hψ M (leftFactorCAct c x) =
      Res.map (leftFactorCAct c) (resLeftFactorEquiv φ ψ hψ M x) := by
  apply Res.ext
  change ψ ((1 : A) ⊗ₜ[k] c) • (show Res ψ M from x).val =
    ((1 : B) ⊗ₜ[k] c) • (show Res ψ M from x).val
  have hx := (show Res ψ M from x).prop
  rw [leftFactor_one φ ψ hψ] at hx
  rw [hψ]
  conv_rhs => rw [← hx]
  rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

end Res

end LeftFactor

/-! ### The second factor -/

section RightFactor

variable {k : Type*} [CommRing k] {A : Type u} [Ring A] [Algebra k A] {C : Type u} [Ring C]
  [Algebra k C]

section CAct

variable {N : Type w} [AddCommGroup N] [Module (C ⊗[k] A) N]

/-- The action of `c ⊗ 1` on `N|_A`, an `A`-linear map. -/
def rightFactorCAct (c : C) : RightFactorRes k A C N →ₗ[A] RightFactorRes k A C N where
  toFun x := (show N from (c ⊗ₜ[k] (1 : A)) • (show N from x))
  map_add' x y := smul_add ((c ⊗ₜ[k] (1 : A))) (show N from x) (show N from y)
  map_smul' a x := by
    change (c ⊗ₜ[k] (1 : A)) • (((1 : C) ⊗ₜ[k] a) • (show N from x)) =
      ((1 : C) ⊗ₜ[k] a) • ((c ⊗ₜ[k] (1 : A)) • (show N from x))
    rw [← mul_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul, mul_one]

theorem rightFactorCAct_apply (c : C) (x : RightFactorRes k A C N) :
    rightFactorCAct c x = (show N from (c ⊗ₜ[k] (1 : A)) • (show N from x)) := rfl

variable {X Y : Type w} [AddCommGroup X] [Module (C ⊗[k] A) X] [AddCommGroup Y]
  [Module (C ⊗[k] A) Y]

/-- **An isomorphism of second factors commuting with the first factor**: an `A`-linear
isomorphism `X|_A ≅ Y|_A` commuting with the actions of `C` is `C ⊗ A`-linear. -/
def linearEquivOfRightFactor (e : RightFactorRes k A C X ≃ₗ[A] RightFactorRes k A C Y)
    (he : ∀ (c : C) (x : RightFactorRes k A C X),
      e (rightFactorCAct c x) = rightFactorCAct c (e x)) : X ≃ₗ[C ⊗[k] A] Y where
  toFun x := (show Y from e x)
  invFun y := (show X from e.symm y)
  map_add' x y := e.map_add x y
  map_smul' t x := by
    induction t using TensorProduct.inductionOn with
    | add s t hs ht =>
      simp only [RingHom.id_apply] at hs ht ⊢
      rw [add_smul]
      exact (map_add e (s • x) (t • x)).trans
        ((congrArg₂ (· + ·) hs ht).trans (add_smul s t (show Y from e x)).symm)
    | tmul c a =>
      have h : c ⊗ₜ[k] a = ((1 : C) ⊗ₜ[k] a) * (c ⊗ₜ[k] (1 : A)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [RingHom.id_apply, h, mul_smul, mul_smul]
      exact (e.map_smul a (rightFactorCAct c x)).trans
        (congrArg (fun y => a • y) (he c x))
  left_inv x := e.symm_apply_apply x
  right_inv y := e.apply_symm_apply y

theorem linearEquivOfRightFactor_apply (e : RightFactorRes k A C X ≃ₗ[A] RightFactorRes k A C Y)
    (he : ∀ (c : C) (x : RightFactorRes k A C X),
      e (rightFactorCAct c x) = rightFactorCAct c (e x)) (x : X) :
    linearEquivOfRightFactor e he x = (show Y from e x) := rfl

end CAct

variable {B : Type u} [Ring B] [Algebra k B] (φ : A →ₙ+* B)
  (hφ : ∀ (c : k) (t : A), φ (c • t) = c • φ t)
  (ψ : C ⊗[k] A →ₙ+* C ⊗[k] B) (hψ : ∀ (c : C) (a : A), ψ (c ⊗ₜ a) = c ⊗ₜ φ a)

section Ind

variable {N : Type w} [AddCommGroup N] [Module k N] [Module (C ⊗[k] A) N]
  [IsScalarTower k (C ⊗[k] A) N]

theorem rightFactorFwdLin_one_tmul_mul (b : B) (y : C ⊗[k] B) (n : N) :
    rightFactorFwdLin φ hφ (((1 : C) ⊗ₜ[k] b) * y) n = b • rightFactorFwdLin φ hφ y n := by
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' =>
    rw [mul_add, map_add, LinearMap.add_apply, hy, hy', map_add, LinearMap.add_apply, smul_add]
  | tmul c b' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, rightFactorFwdLin_tmul,
      rightFactorFwdLin_tmul]
    refine Eq.trans ?_ (Ind.smul_tmul b _ _).symm
    change Ind.tmul _ _ = Ind.tmul _ _
    congr 1
    exact Subtype.ext (mul_assoc b b' (φ 1))

theorem rightFactorFwdLin_tmul_one_mul (c : C) (y : C ⊗[k] B) (n : N) :
    rightFactorFwdLin φ hφ ((c ⊗ₜ[k] (1 : B)) * y) n =
      IndK.map (rightFactorCAct c) (rightFactorFwdLin φ hφ y n) := by
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' =>
    rw [mul_add, map_add, LinearMap.add_apply, hy, hy', map_add, LinearMap.add_apply, map_add]
  | tmul c' b =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, rightFactorFwdLin_tmul,
      rightFactorFwdLin_tmul]
    refine Eq.trans ?_ (IndK.map_tmul _ _ _).symm
    change Ind.tmul _ _ = Ind.tmul _ _
    rw [rightFactorCAct_apply]
    congr 1
    change ((c * c') ⊗ₜ[k] (1 : A)) • n = (c ⊗ₜ[k] (1 : A)) • (c' ⊗ₜ[k] (1 : A)) • n
    rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem indRightFactorEquiv_one_tmul_smul (b : B) (t : IndK k N ψ) :
    indRightFactorEquiv φ hφ ψ hψ (((1 : C) ⊗ₜ[k] b) • t) =
      b • indRightFactorEquiv φ hφ ψ hψ t := by
  induction t using Ind.induction_on with
  | zero =>
    exact (congrArg (indRightFactorEquiv φ hφ ψ hψ) (smul_zero _)).trans
      ((map_zero _).trans (smul_zero _).symm)
  | tmul z n =>
    refine (congrArg (indRightFactorEquiv φ hφ ψ hψ) (Ind.smul_tmul _ z n)).trans ?_
    exact rightFactorFwdLin_one_tmul_mul φ hφ b z.1 n
  | add s t hs ht =>
    exact (congrArg (indRightFactorEquiv φ hφ ψ hψ) (smul_add _ s t)).trans
      ((map_add _ _ _).trans ((congrArg₂ (· + ·) hs ht).trans
        ((smul_add b _ _).symm.trans (congrArg (fun y => b • y) (map_add _ s t).symm))))

theorem indRightFactorEquiv_tmul_one_smul (c : C) (t : IndK k N ψ) :
    indRightFactorEquiv φ hφ ψ hψ ((c ⊗ₜ[k] (1 : B)) • t) =
      IndK.map (rightFactorCAct c) (indRightFactorEquiv φ hφ ψ hψ t) := by
  induction t using Ind.induction_on with
  | zero =>
    exact (congrArg (indRightFactorEquiv φ hφ ψ hψ) (smul_zero _)).trans
      ((map_zero _).trans (map_zero _).symm)
  | tmul z n =>
    refine (congrArg (indRightFactorEquiv φ hφ ψ hψ) (Ind.smul_tmul _ z n)).trans ?_
    exact rightFactorFwdLin_tmul_one_mul φ hφ c z.1 n
  | add s t hs ht =>
    exact (congrArg (indRightFactorEquiv φ hφ ψ hψ) (smul_add _ s t)).trans
      ((map_add _ _ _).trans ((congrArg₂ (· + ·) hs ht).trans
        ((map_add _ _ _).symm.trans
          (congrArg (IndK.map (rightFactorCAct c)) (map_add _ s t).symm))))

/-- **Induction along a map of the second factor, as `B`-modules**:
`(Ind_ψ N)|_B ≅ Ind_φ (N|_A)`. -/
def indRightFactorEquivB :
    RightFactorRes k B C (IndK k N ψ) ≃ₗ[B] IndK k (RightFactorRes k A C N) φ where
  toFun t := indRightFactorEquiv φ hφ ψ hψ (show IndK k N ψ from t)
  invFun t := (show RightFactorRes k B C (IndK k N ψ) from
    (indRightFactorEquiv φ hφ ψ hψ).symm t)
  map_add' s t := map_add (indRightFactorEquiv φ hφ ψ hψ) s t
  map_smul' b t := indRightFactorEquiv_one_tmul_smul φ hφ ψ hψ b t
  left_inv t := (indRightFactorEquiv φ hφ ψ hψ).symm_apply_apply t
  right_inv t := (indRightFactorEquiv φ hφ ψ hψ).apply_symm_apply t

theorem indRightFactorEquivB_apply (t : RightFactorRes k B C (IndK k N ψ)) :
    indRightFactorEquivB φ hφ ψ hψ t =
      indRightFactorEquiv φ hφ ψ hψ (show IndK k N ψ from t) := rfl

/-- `indRightFactorEquivB` carries the action of `c ⊗ 1` to `Ind_φ` of the action of
`c ⊗ 1`. -/
theorem indRightFactorEquivB_cAct (c : C) (t : RightFactorRes k B C (IndK k N ψ)) :
    indRightFactorEquivB φ hφ ψ hψ (rightFactorCAct c t) =
      IndK.map (rightFactorCAct c) (indRightFactorEquivB φ hφ ψ hψ t) :=
  indRightFactorEquiv_tmul_one_smul φ hφ ψ hψ c t

end Ind

section Res

variable (M : Type w) [AddCommGroup M] [Module (C ⊗[k] B) M]

include hψ in
theorem rightFactor_one_smul_of_res (m : Res ψ M) :
    φ 1 • (show RightFactorRes k B C M from m.val) =
      (show RightFactorRes k B C M from m.val) := by
  change ((1 : C) ⊗ₜ[k] φ 1) • m.val = m.val
  rw [← rightFactor_one φ ψ hψ]
  exact m.prop

/-- **Restriction along a map of the second factor**: `(Res_ψ M)|_A ≅ Res_φ (M|_B)`. -/
def resRightFactorEquiv :
    RightFactorRes k A C (Res ψ M) ≃ₗ[A] Res φ (RightFactorRes k B C M) where
  toFun x := Res.mk (show RightFactorRes k B C M from (show Res ψ M from x).val)
    (rightFactor_one_smul_of_res φ ψ hψ M x)
  invFun y := (show RightFactorRes k A C (Res ψ M) from Res.mk (show M from y.val) (by
    rw [rightFactor_one φ ψ hψ]
    exact y.prop))
  map_add' x y := Res.ext rfl
  map_smul' a x := Res.ext (by
    change ψ ((1 : C) ⊗ₜ[k] a) • (show Res ψ M from x).val =
      ((1 : C) ⊗ₜ[k] φ a) • (show Res ψ M from x).val
    rw [hψ])
  left_inv x := Res.ext rfl
  right_inv y := Res.ext rfl

theorem resRightFactorEquiv_val (x : RightFactorRes k A C (Res ψ M)) :
    (resRightFactorEquiv φ ψ hψ M x).val = (show Res ψ M from x).val := rfl

/-- `resRightFactorEquiv` carries the action of `c ⊗ 1` to `Res_φ` of the action of
`c ⊗ 1`. -/
theorem resRightFactorEquiv_cAct (c : C) (x : RightFactorRes k A C (Res ψ M)) :
    resRightFactorEquiv φ ψ hψ M (rightFactorCAct c x) =
      Res.map (rightFactorCAct c) (resRightFactorEquiv φ ψ hψ M x) := by
  apply Res.ext
  change ψ (c ⊗ₜ[k] (1 : A)) • (show Res ψ M from x).val =
    (c ⊗ₜ[k] (1 : B)) • (show Res ψ M from x).val
  have hx := (show Res ψ M from x).prop
  rw [rightFactor_one φ ψ hψ] at hx
  rw [hψ]
  conv_rhs => rw [← hx]
  rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

end Res

end RightFactor

end InductionAlong

end

end Categorification
