/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.BarK0
import Categorification.KLR.CyclotomicAbsentModule
import Categorification.KLR.CyclotomicFinite

/-!
# The cyclotomic horizontal anti-involution

Kang–Kashiwara, arXiv:1102.4677v4, §6, use the anti-involution fixing the KLR
generators to interchange left and right modules. It preserves the cyclotomic
ideal and commutes with adjoining a strand, including for deformed cyclotomic
polynomials.
-/

noncomputable section

namespace Categorification.KLR.CycKLR
open KLRAlgebra KLRAlgebra.AbsentColour MulOpposite

variable {k I : Type*} [CommRing k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
  (a : I → Polynomial k) (ν : Multiset I)

private theorem flip_cycElt (s : Seq ν) : hflip (cycElt Q a s) = cycElt Q a s := by
  by_cases h : 0 < Multiset.card ν
  · rw [cycElt_of_pos _ _ _ h, ← pol_aeval_X, hflip_mul, hflip_e, hflip_pol]
    exact (commute_e_pol _ _).eq
  · simp [cycElt, h]

/-- The algebra map to the opposite cyclotomic algebra induced by the horizontal
flip (Kang–Kashiwara, arXiv:1102.4677v4, §6, following Lemma 6.1). -/
private def flipHom : CycKLR k Q a ν →ₐ[k] (CycKLR k Q a ν)ᵐᵒᵖ :=
  lift (((mk k Q a ν).op).comp (KLRAlgebra.flipH k Q ν).toAlgHom) fun s => by
    change op (mk k Q a ν (hflip (cycElt Q a s))) = 0
    rw [flip_cycElt, mk_cycElt, op_zero]

/-- The horizontal reflection of a cyclotomic KLR element. -/
def flip (z : CycKLR k Q a ν) : CycKLR k Q a ν := (flipHom a ν z).unop

@[simp] theorem flip_mk (r : KLRAlgebra k Q ν) :
    flip a ν (mk k Q a ν r) = mk k Q a ν (hflip r) := by
  rw [flip, flipHom, lift_mk]
  rfl

@[simp] theorem flip_flip (z : CycKLR k Q a ν) : flip a ν (flip a ν z) = z := by
  obtain ⟨r, rfl⟩ := mk_surjective z
  simp

theorem flip_mul (z w : CycKLR k Q a ν) : flip a ν (z * w) = flip a ν w * flip a ν z := by
  simp [flip]

/-- The anti-involution of the ordinary cyclotomic algebra as an algebra
isomorphism with its opposite (Kang–Kashiwara, arXiv:1102.4677v4, §6). -/
def flipEquiv : CycKLR k Q a ν ≃ₐ[k] (CycKLR k Q a ν)ᵐᵒᵖ where
  __ := flipHom a ν
  invFun z := flip a ν z.unop
  left_inv := flip_flip a ν
  right_inv z := unop_injective (flip_flip a ν z.unop)

private theorem hflip_cast {μ μ' : Multiset I} (h : μ = μ') (r : KLRAlgebra k Q μ) :
    hflip (castKLR Q h r) = castKLR Q h (hflip r) := by subst h; rfl

variable (i : I)
local notation "Si" => (Singleton.singleton i : Multiset I)

/-- Horizontal reflection commutes with extension of the diagram by a strand on
the right. -/
theorem flip_cyclotomicLast (z : CycKLR k Q a ν) :
    flip a (Si + ν) (cyclotomicLast Q i a ν z) = cyclotomicLast Q i a ν (flip a ν z) := by
  obtain ⟨r, rfl⟩ := mk_surjective z
  simp only [cyclotomicLast_mk, flip_mk, cL_eq_cast, hflip_cast, hflip_concat_tmul_tmul, hflip_one]

@[simp] theorem flip_lastIdem : flip a (Si + ν) (lastIdem Q i a ν) = lastIdem Q i a ν := by
  rw [lastIdem, flip_cyclotomicLast]
  change cyclotomicLast Q i a ν (flipHom a ν 1).unop = _
  rw [map_one, unop_one]

end Categorification.KLR.CycKLR
