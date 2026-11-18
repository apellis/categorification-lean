/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Restriction
import Categorification.Algebra.Graded.TwistTensor

/-!
# Right graded modules from left graded modules

A graded anti-involution `ψ` of `A` turns a graded left `A`-module `M` into a graded right
`A`-module, that is a graded left `Aᵐᵒᵖ`-module, by `m · a = ψ(a) m`
(Khovanov–Lauda, arXiv:0803.4121v2, §2.5). The right twist is restriction along the graded
algebra isomorphism `Aᵐᵒᵖ ≃ A`, `op a ↦ ψ a`, so it identifies the graded Grothendieck groups of
left and right graded projectives and preserves graded Hom spaces.

## Main definitions and results

* `oppositeGrade`, `GMod.rightTwist`, `GProj.rightTwist` : the right twist.
* `GProj.rightTwistIdempotentIso` : the twist of `Ae` is `eA` when `ψ e = e`.
* `K0.rightTwistEquiv` : `K₀` of left graded projectives `≃` `K₀` of right graded projectives,
  `ℤ[q, q⁻¹]`-linear, `[P] ↦ [P^ψ]`.
* `K0.homForm_rightTwistEquiv` : it preserves the Euler form.
-/

noncomputable section

namespace Categorification.Graded

open MulOpposite

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A}

/-- The grading of an opposite algebra takes the same degree on opposite elements. -/
def oppositeGrade (𝒜 : ℤ → Submodule k A) : ℤ → Submodule k Aᵐᵒᵖ :=
  Graded.comap 𝒜 (opLinearEquiv k).symm.toLinearMap

instance [GradedAlgebra 𝒜] : GradedAlgebra (oppositeGrade 𝒜) := by
  letI : SetLike.GradedMonoid (oppositeGrade 𝒜) := {
    one_mem := show (1 : A) ∈ 𝒜 0 from SetLike.GradedOne.one_mem
    mul_mem {i j} {a b} ha hb := by
      change b.unop * a.unop ∈ 𝒜 (i + j)
      rw [add_comm]
      exact SetLike.GradedMul.mul_mem (show b.unop ∈ 𝒜 j from hb)
        (show a.unop ∈ 𝒜 i from ha) }
  have hin : DirectSum.IsInternal (oppositeGrade 𝒜) :=
    isInternal_comap 𝒜 _ (opLinearEquiv k).symm.injective
      (fun _ _ => (opLinearEquiv k).symm.surjective _)
  exact hin.gradedAlgebra

variable [GradedAlgebra 𝒜] (ψ : GradedAntiInvolution 𝒜)

/-- Regard a graded left module as a graded right module via a graded anti-involution. -/
def GMod.rightTwist (M : GMod 𝒜) : GMod (oppositeGrade 𝒜) :=
  letI : SetLike.GradedSMul (oppositeGrade 𝒜) (twistGrading ψ M.grading) := {
    smul_mem {i j} {a m} ha hm := by
      rw [vadd_eq_add, add_comm]
      exact op_smul_mem_twistGrading ψ hm (show a.unop ∈ 𝒜 i from ha) }
  GMod.of (Twist ψ M) (twistGrading ψ M.grading)

/-- The ring equivalence implementing a right twist. -/
private def GradedAntiInvolution.toOppositeRingEquiv : A ≃+* Aᵐᵒᵖ where
  toFun := fun a => op (ψ a)
  invFun := fun a => ψ a.unop
  left_inv := ψ.invol
  right_inv := fun a => congrArg op (ψ.invol a.unop)
  map_mul' := fun a b => congrArg op (ψ.map_mul a b)
  map_add' := fun a b => congrArg op (ψ.map_add a b)

/-- Twisting a graded projective yields a graded right projective. -/
def GProj.rightTwist (P : GProj 𝒜) : GProj (oppositeGrade 𝒜) := by
  let R := ψ.toOppositeRingEquiv
  letI : RingHomInvPair (R : A →+* Aᵐᵒᵖ) (R.symm : Aᵐᵒᵖ →+* A) := .of_ringEquiv R
  letI : RingHomInvPair (R.symm : Aᵐᵒᵖ →+* A) (R : A →+* Aᵐᵒᵖ) := .of_ringEquiv_symm R
  letI : RingHomSurjective (R : A →+* Aᵐᵒᵖ) := ⟨R.surjective⟩
  let e : P.carrier ≃ₛₗ[(R : A →+* Aᵐᵒᵖ)] (P.toGMod.rightTwist ψ).carrier :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => by
        change a • x = ψ (ψ a) • x
        rw [ψ.invol] }
  exact
    { toGMod := P.toGMod.rightTwist ψ
      finite := Module.Finite.of_surjective e.toLinearMap e.surjective
      projective := Module.Projective.of_equiv e }

/-- Isomorphisms of graded modules induce isomorphisms of their right twists. -/
def GMod.rightTwistIso {M N : GMod 𝒜} (f : M.Iso N) :
    (M.rightTwist ψ).Iso (N.rightTwist ψ) where
  toLinearEquiv :=
    { toFun := fun m => f (show M from m)
      invFun := fun n => f.symm (show N from n)
      left_inv := f.toLinearEquiv.left_inv
      right_inv := f.toLinearEquiv.right_inv
      map_add' := f.toLinearEquiv.map_add
      map_smul' := fun a m => f.toLinearEquiv.map_smul (ψ a.unop) m }
  map_mem' := fun _ _ h => f.map_mem h
  symm_map_mem' := fun _ _ h => f.symm_map_mem' h

/-- Right twisting preserves degree shifts. -/
def GMod.rightTwistShiftIso (M : GMod 𝒜) (d : ℤ) :
    ((M.shift d).rightTwist ψ).Iso ((M.rightTwist ψ).shift d) :=
  GradedEquiv.refl _

/-- Right twisting preserves binary direct sums. -/
def GMod.rightTwistProdIso (M N : GMod 𝒜) :
    ((M.prod N).rightTwist ψ).Iso ((M.rightTwist ψ).prod (N.rightTwist ψ)) where
  toLinearEquiv :=
    { toFun := fun x => ((show M × N from x).1, (show M × N from x).2)
      invFun := fun x => (show M from x.1, show N from x.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_mem' := fun _ _ h => h
  symm_map_mem' := fun _ _ h => h

/-- Reflection identifies the right twist of the left ideal with the right ideal
generated by a fixed homogeneous idempotent. -/
def GProj.rightTwistIdempotentIso {e : A} (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0)
    (hψe : ψ e = e) :
    ((GProj.ofIdempotent e he he0).toGMod.rightTwist ψ).Iso
      (GProj.ofIdempotent (op e) (congrArg op he) (show op e ∈ oppositeGrade 𝒜 0 from he0)).toGMod :=
  let forward (x : leftIdeal e) : leftIdeal (op e) :=
    ⟨op (ψ x.val), congrArg op ((congrArg (· * ψ x.val) hψe).symm.trans
      ((ψ.map_mul x.val e).symm.trans (congrArg ψ x.property)))⟩
  let backward (y : leftIdeal (op e)) : leftIdeal e :=
    ⟨ψ y.val.unop, (congrArg (ψ y.val.unop * ·) hψe).symm.trans
      ((ψ.map_mul e y.val.unop).symm.trans (congrArg (fun a => ψ a.unop) y.property))⟩
  { toLinearEquiv :=
      { toFun := fun x => forward (show leftIdeal e from x)
        invFun := fun y => backward y
        left_inv := fun x => Subtype.ext (ψ.invol x.val)
        right_inv := fun y => Subtype.ext (congrArg op (ψ.invol y.val.unop))
        map_add' := fun x y => Subtype.ext (congrArg op (ψ.map_add x.val y.val))
        map_smul' := fun a x => Subtype.ext (congrArg op (by
          change ψ (ψ a.unop * x.val) = ψ x.val * a.unop
          rw [ψ.map_mul, ψ.invol])) }
    map_mem' := fun _ _ h => ψ.mem_grade h
    symm_map_mem' := fun _ _ h => ψ.mem_grade h }


/-! ### Right twisting as restriction, and `K₀` -/

/-- `ψ` as a `k`-algebra isomorphism `Aᵐᵒᵖ ≃ A`, `op a ↦ ψ a`. -/
def GradedAntiInvolution.unopAlgEquiv : Aᵐᵒᵖ ≃ₐ[k] A where
  toFun a := ψ a.unop
  invFun a := op (ψ a)
  left_inv a := congrArg op (ψ.invol a.unop)
  right_inv := ψ.invol
  map_mul' a b := ψ.map_mul b.unop a.unop
  map_add' a b := ψ.map_add a.unop b.unop
  commutes' c := by
    change ψ (algebraMap k A c) = algebraMap k A c
    rw [Algebra.algebraMap_eq_smul_one, ψ.map_smul, ψ.map_one]

omit [GradedAlgebra 𝒜] in
theorem GradedAntiInvolution.isGradedAlgEquiv_unopAlgEquiv :
    IsGradedAlgEquiv ψ.unopAlgEquiv (oppositeGrade 𝒜) 𝒜 := fun _ b =>
  ⟨fun h => by
    have h' := ψ.mem_grade h
    change ψ (ψ b.unop) ∈ 𝒜 _ at h'
    rw [ψ.invol] at h'
    exact h', fun h => ψ.mem_grade h⟩

/-- The right twist of a graded module is its restriction along `op a ↦ ψ a`. -/
def GMod.rightTwistRestrictIso (M : GMod 𝒜) :
    (M.rightTwist ψ).Iso (M.restrict ψ.isGradedAlgEquiv_unopAlgEquiv) where
  toLinearEquiv :=
    { toFun := fun m => (show M from m)
      invFun := fun m => (show M from m)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_mem' := fun _ _ h => h
  symm_map_mem' := fun _ _ h => h

instance [HasGdim 𝒜] : HasGdim (oppositeGrade 𝒜) :=
  HasGdim.of_linearEquiv (𝒩 := 𝒜) fun _ =>
    { toFun := fun x => ⟨x.1.unop, x.2⟩
      invFun := fun y => ⟨op y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

namespace K0

/-- **Left and right graded projectives.** Right twisting by a graded anti-involution
identifies the graded Grothendieck group of left graded projectives with that of right
graded projectives, as `ℤ[q, q⁻¹]`-modules. -/
def rightTwistEquiv : K0 𝒜 ≃ₗ[LaurentPolynomial ℤ] K0 (oppositeGrade 𝒜) :=
  restrictEquiv ψ.isGradedAlgEquiv_unopAlgEquiv

@[simp] theorem rightTwistEquiv_of (P : GProj 𝒜) :
    rightTwistEquiv ψ (of P) = of (P.rightTwist ψ) :=
  (of_eq_of_iso (P.toGMod.rightTwistRestrictIso ψ)).symm

/-- Right twisting preserves the Euler form `([P], [Q]) ↦ gdim HOM(P, Q)`. -/
theorem homForm_rightTwistEquiv [HasGdim 𝒜] (x y : K0 𝒜) :
    homForm (oppositeGrade 𝒜) (rightTwistEquiv ψ x) (rightTwistEquiv ψ y) = homForm 𝒜 x y :=
  homForm_restrictEquiv _ x y

end K0

end Categorification.Graded
