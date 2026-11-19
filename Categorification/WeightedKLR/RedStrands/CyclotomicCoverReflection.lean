/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BoundaryHomReflection
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverQuotient

/-!
# Horizontal reflection through the cyclotomic cover

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The vacuum evaluation detects an
element of the tensor product algebra only after a horizontal reflection. The horizontal flip of
the KLR algebra does not depend on the parameters `Q`: on the free algebra it is the reversal of
words (`KLR.flipFree_eq_reverse`). Hence the projection from the cyclotomic cover to the tensor
product algebra intertwines the flip of the cover with the reflection `tensorReflect`
(`cyclotomicCoverToTensor_hflip`).
-/

noncomputable section

namespace Categorification

namespace KLR

open MulOpposite KLRAlgebra

variable {I k : Type*} [DecidableEq I] [CommRing k] {ν : Multiset I}

variable (k ν) in
/-- The reversal of words in the free algebra on the KLR generators. -/
def freeReverse : FreeAlgebra k (Gen ν) →ₐ[k] (FreeAlgebra k (Gen ν))ᵐᵒᵖ :=
  FreeAlgebra.lift k fun g => op (FreeAlgebra.ι k g)

/-- The horizontal flip of the free algebra is the reversal of words followed by the
quotient map. -/
theorem flipFree_eq_reverse (Q : I → I → MvPolynomial (Fin 2) k) (a : FreeAlgebra k (Gen ν)) :
    flipFree k Q ν a = op (KLRAlgebra.mk k Q ν (freeReverse k ν a).unop) := by
  have h : flipFree k Q ν = (KLRAlgebra.mk k Q ν).op.comp (freeReverse k ν) :=
    FreeAlgebra.hom_ext (funext fun g => by
      simp [flipFree, freeReverse])
  rw [h]
  rfl

/-- The horizontal flip of a class depends only on its representative in the free algebra. -/
theorem hflip_mk (Q : I → I → MvPolynomial (Fin 2) k) (a : FreeAlgebra k (Gen ν)) :
    hflip (KLRAlgebra.mk k Q ν a) = KLRAlgebra.mk k Q ν (freeReverse k ν a).unop := by
  rw [hflip, flipAlgHom_mk, flipFree_eq_reverse, unop_op]

end KLR

namespace Stendhal

open KLR KLRAlgebra MulOpposite

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)
  (C : QuantumGroup.CartanDatum I)

local notation "μ" => stendhalWeight ℓ ν
local notation "S₀" => cyclotomicCoverQ C Λ Q
local notation "p" => cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)
local notation "π" => cyclotomicCoverToTensor (Q := Q) Λ ν C

/-- **The cover projection intertwines the horizontal flips**: projecting the flip of a cover
element gives the horizontal reflection of its projection. -/
theorem cyclotomicCoverToTensor_hflip (a : KLRAlgebra k S₀ μ) :
    π (CycKLR.mk k S₀ p μ (hflip a)) =
      (tensorReflect (Q := Q) (Λ := Λ) (ν := ν) (π (CycKLR.mk k S₀ p μ a))).unop := by
  obtain ⟨v, rfl⟩ := KLRAlgebra.mk_surjective (k := k) (Q := S₀) (ν := μ) a
  rw [hflip_mk, cyclotomicCoverToTensor_mk, cyclotomicCoverToTensor_mk, ← hflip_mk]
  exact (congrArg unop (tensorReflect_projection (Q := Q) (Λ := Λ) (ν := ν) _)).symm

/-- A cover element projects to zero exactly when its horizontal flip does. -/
theorem cyclotomicCoverToTensor_hflip_eq_zero_iff (a : KLRAlgebra k S₀ μ) :
    π (CycKLR.mk k S₀ p μ (hflip a)) = 0 ↔ π (CycKLR.mk k S₀ p μ a) = 0 := by
  rw [cyclotomicCoverToTensor_hflip]
  constructor
  · intro h
    apply tensorReflect_injective (Q := Q) (Λ := Λ) (ν := ν)
    rw [map_zero]
    exact congrArg op h
  · intro h
    rw [h, map_zero]
    rfl

end Stendhal

end Categorification
