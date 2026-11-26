/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedRightStandard
import Categorification.WeightedKLR.RedStrands.GradedBraidResolution
import Categorification.WeightedKLR.RedStrands.BraidedIdentityGrading

/-!
# The standard module as a graded right `T^λ`-module

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5.1,
Definition 5.1. For a loading `t` with red order `λ = (1, …, ℓ)`, the standard module
`S_t = e(t) T / U_t` is a right module over the corner `e_λ V e_λ`. Through
`violCornerEquiv : e_λ V e_λ ≃ T^λ` it is a finite-dimensional graded right `T^λ`-module
(`rightStandard t`), and its corner restriction is the standard module itself.

## Main definitions

* `RightStandard Λ hρ hQ t` : `e(t) T / U_t` as a right `T^λ`-module.
* `rightStandard G hρ hQ t ht` : the graded module, an object of `GFin`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Categorification.Graded MulOpposite DirectSum RedBlock

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q)

local notation "μ" => stendhalWeight ℓ ν
local notation "ord" => List.finRange ℓ
local notation "V" => ViolQuotient k Q Λ ν
local notation "𝒞" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
  (List.finRange ℓ))
local notation "𝒯" => TensorProductAlgebra k Q Λ ν

local instance violOrderCornerRingOrd (κ : List (Fin ℓ)) :
    Ring (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ) := _root_.instRingCorner _ _

local notation "𝒞o" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (List.finRange ℓ)

/-- `(T^λ)ᵐᵒᵖ → (e_λ V e_λ)ᵐᵒᵖ`, the inverse of `violCornerEquiv` on opposite rings. -/
def rightCornerHom : 𝒯ᵐᵒᵖ →+* 𝒞oᵐᵒᵖ where
  toFun a := op ((violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).symm a.unop : 𝒞o)
  map_one' := congrArg op (map_one (violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).symm)
  map_mul' a b := congrArg op (map_mul (violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν)
    hρ hQ).symm b.unop a.unop)
  map_zero' := congrArg op
    (map_zero (violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).symm)
  map_add' a b := congrArg op (map_add (violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν)
    hρ hQ).symm a.unop b.unop)

variable (Λ) in
/-- The standard module `e(t) T / U_t` at a loading of the red order `(1, …, ℓ)`, read as a right
`T^λ`-module through `violCornerEquiv`. -/
def RightStandard (_ : TypeA.IsReducedChoice ρ) (_ : KLRSymm Q)
    (t : KLR.Seq (stendhalWeight ℓ ν)) : Type :=
  ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t ord

namespace RightStandard

variable (t : KLR.Seq (stendhalWeight ℓ ν))

instance : AddCommGroup (RightStandard Λ hρ hQ t) :=
  inferInstanceAs (AddCommGroup (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t ord))

instance : Module k (RightStandard Λ hρ hQ t) :=
  loadingStandardModuleK (k := k) (Q := Q) (Λ := Λ) t ord

instance : Module 𝒯ᵐᵒᵖ (RightStandard Λ hρ hQ t) :=
  Module.compHom (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t ord)
    (rightCornerHom (Λ := Λ) (ν := ν) hρ hQ)

theorem smul_mk_val (a : 𝒯ᵐᵒᵖ) (y : violCorner k Q Λ ν t ord) :
    (rightCornerHom hρ hQ a • y).1 =
      y.1 * ((violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).symm a.unop).1 :=
  rfl

include hρ hQ in
/-- `violCornerEquiv⁻¹` is `k`-linear on values. -/
theorem violCornerEquiv_symm_smul_val (c : k) (u : 𝒯) :
    ((violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).symm (c • u)).1 =
      c • ((violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).symm u).1 := by
  have hz := ((Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν ord)).1
    ((violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).symm u).2).1
  rw [Algebra.smul_def, map_mul]
  change ((violCornerEquiv hρ hQ).symm (algebraMap k 𝒯 c)).1 *
    ((violCornerEquiv hρ hQ).symm u).1 = _
  rw [violCornerEquiv_symm_algebraMap_val hρ hQ, mul_assoc, hz, Algebra.smul_def]

instance : IsScalarTower k 𝒯ᵐᵒᵖ (RightStandard Λ hρ hQ t) where
  smul_assoc c a x := by
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      change Submodule.Quotient.mk (rightCornerHom hρ hQ (c • a) • y) =
        c • Submodule.Quotient.mk (rightCornerHom hρ hQ a • y)
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      apply Subtype.ext
      change y.1 * ((violCornerEquiv hρ hQ).symm (c • a).unop).1 =
        c • (y.1 * ((violCornerEquiv hρ hQ).symm a.unop).1)
      rw [MulOpposite.unop_smul, violCornerEquiv_symm_smul_val, mul_smul_comm]

variable (G : KLR.GradingDatum (stendhalQ Q Λ))

instance gradedSMul : SetLike.GradedSMul (oppositeGrade (tensorProductGrade G ν))
    (show ℤ → Submodule k (RightStandard Λ hρ hQ t) from loadingStandardGrade G t ord) where
  smul_mem i j a x ha hx := by
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    have ha' : (violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ)
        ((violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).symm a.unop) ∈
          tensorProductGrade G ν i := by
      rw [RingEquiv.apply_symm_apply]
      exact ha
    have hc := (violCornerEquiv_mem_tensorProductGrade_iff hρ hQ G _).1 ha'
    change (Submodule.Quotient.mk (rightCornerHom hρ hQ a • y) : RightStandard Λ hρ hQ t) ∈
      loadingStandardGrade G t ord (i + j)
    refine Submodule.mem_map_of_mem (f := loadingMkK t ord) (p := violCornerGrade G t ord (i + j))
      ?_
    change y.1 * ((violCornerEquiv hρ hQ).symm a.unop).1 ∈ violAuxiliaryGrade G (i + j)
    rw [add_comm]
    exact SetLike.GradedMul.mul_mem hy hc

end RightStandard

section Finite

variable {t : KLR.Seq (stendhalWeight ℓ ν)}

/-- The cut `e(t) V e_λ` lies in the corner `e_λ V e_λ`, for a loading `t` of the order `λ`. -/
theorem mem_corner_of_mem_violCorner (ht : redWord t = ord) (y : violCorner k Q Λ ν t ord) :
    y.1 ∈ Subsemigroup.corner (violMk k Q Λ ν (redProj k Q Λ ν ord)) := by
  have hy := mem_violCorner_iff.1 y.2
  refine (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν ord)).2
    ⟨?_, hy.2⟩
  have he : violMk k Q Λ ν (redProj k Q Λ ν ord) *
      violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e t)) =
        violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e t)) := by
    rw [redProj, ← map_mul, ← map_mul, redIdem_mul_e, ite_eq_left ht]
  rw [← hy.1, ← mul_assoc, he]

/-- The cut `e(t) V e_λ` as a `k`-subspace of `T^λ`. -/
def violCornerToTensor (ht : redWord t = ord) : violCorner k Q Λ ν t ord →ₗ[k] 𝒯 where
  toFun y := violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ
    ⟨y.1, mem_corner_of_mem_violCorner ht y⟩
  map_add' y z := by
    rw [← map_add]
    rfl
  map_smul' c y := by
    apply (violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).symm.injective
    apply Subtype.ext
    rw [RingHom.id_apply, RightStandard.violCornerEquiv_symm_smul_val, RingEquiv.symm_apply_apply,
      RingEquiv.symm_apply_apply]
    rfl

theorem violCornerToTensor_injective (ht : redWord t = ord) :
    Function.Injective (violCornerToTensor (Λ := Λ) hρ hQ ht) := by
  intro y z h
  have h' := congrArg Subtype.val
    ((violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).injective h)
  exact Subtype.ext h'

variable [Module.Finite k (TensorProductAlgebra k Q Λ ν)]

include hρ hQ in
theorem finite_violLoadingStandard (ht : redWord t = ord) :
    Module.Finite k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t ord) := by
  have : Module.Finite k (violCorner k Q Λ ν t ord) :=
    Module.Finite.of_injective _ (violCornerToTensor_injective (Λ := Λ) hρ hQ ht)
  exact Module.Finite.of_surjective (loadingMkK t ord)
    (Submodule.mkQ_surjective (violStandardUpper (k := k) (Q := Q) (Λ := Λ) t ord))

variable (G : KLR.GradingDatum (stendhalQ Q Λ))

variable (t) in
/-- **The standard module of a loading as a graded right `T^λ`-module** (Webster,
arXiv:1309.3796v2, Definition 5.1): `e(t) T / U_t` with the auxiliary grading, for a loading
`t` of the red order `(1, …, ℓ)`. -/
def rightStandard (ht : redWord t = ord) : GFin (oppositeGrade (tensorProductGrade G ν)) :=
  letI := loadingStandardDecomposition G t ord ht
  { carrier := RightStandard Λ hρ hQ t
    grading := show ℤ → Submodule k (RightStandard Λ hρ hQ t) from loadingStandardGrade G t ord
    finiteDimensional := finite_violLoadingStandard hρ hQ ht }

end Finite

end Categorification.Stendhal.BraidedStendhalAlgebra
