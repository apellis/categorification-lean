/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedAppendFlip
import Categorification.WeightedKLR.RedStrands.BraidingFunctor

/-!
# The horizontal reflection of Webster's braid bimodules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§6.1, p. 65, proof of Lemma 6.11, step `f_n → s_n`. Horizontal reflection reverses
the boundary orders and exchanges the two corner actions of the braid bimodule.
For boundary orders related by `w`, this identifies the reflected bimodule with
the braid bimodule for `w⁻¹`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR MulOpposite CornerEndomorphism

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

theorem violFlip_mul' (a b : ViolQuotient k Q Λ ν) : violFlip (a * b) = violFlip b * violFlip a :=
  congrArg MulOpposite.unop (map_mul (violFlipHom k Q Λ ν) a b)

theorem violFlip_add' (a b : ViolQuotient k Q Λ ν) : violFlip (a + b) = violFlip a + violFlip b :=
  congrArg MulOpposite.unop (map_add (violFlipHom k Q Λ ν) a b)

theorem violFlip_zero' : violFlip (0 : ViolQuotient k Q Λ ν) = 0 :=
  congrArg MulOpposite.unop (map_zero (violFlipHom k Q Λ ν))

theorem violFlip_idem (κ : List (Fin ℓ)) :
    violFlip (violMk k Q Λ ν (redProj k Q Λ ν κ)) =
      violMk k Q Λ ν (redProj k Q Λ ν κ) := by
  rw [violFlip_violMk, flip_redProj]

/-- The top–bottom flip on the corner at a red order `κ`. -/
noncomputable def cornerFlip {κ : List (Fin ℓ)}
    (x : (isIdempotentElem_violMk_redProj k Q Λ ν κ).Corner) :
    (isIdempotentElem_violMk_redProj k Q Λ ν κ).Corner :=
  ⟨violFlip x.1, (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν κ)).2
    ⟨by
      have h := congrArg violFlip
        (corner_mul_right (isIdempotentElem_violMk_redProj k Q Λ ν κ) x)
      rwa [violFlip_mul', violFlip_idem] at h, by
      have h := congrArg violFlip
        (corner_mul_left (isIdempotentElem_violMk_redProj k Q Λ ν κ) x)
      rwa [violFlip_mul', violFlip_idem] at h⟩⟩

theorem cornerFlip_val {κ : List (Fin ℓ)}
    (x : (isIdempotentElem_violMk_redProj k Q Λ ν κ).Corner) :
    (cornerFlip x).1 = violFlip x.1 := rfl

theorem cornerFlip_cornerFlip {κ : List (Fin ℓ)}
    (x : (isIdempotentElem_violMk_redProj k Q Λ ν κ).Corner) : cornerFlip (cornerFlip x) = x :=
  Subtype.ext (violFlip_violFlip x.1)

variable (ν) in
/-- The flip identifies the opposite of a corner with the corner. -/
noncomputable def cornerFlipEquiv (κ : List (Fin ℓ)) :
    (isIdempotentElem_violMk_redProj k Q Λ ν κ).Cornerᵐᵒᵖ ≃+*
      (isIdempotentElem_violMk_redProj k Q Λ ν κ).Corner where
  toFun a := cornerFlip a.unop
  invFun y := op (cornerFlip y)
  left_inv a := by
    change op (cornerFlip (cornerFlip a.unop)) = a
    rw [cornerFlip_cornerFlip]; rfl
  right_inv y := cornerFlip_cornerFlip y
  map_mul' a b := Subtype.ext (violFlip_mul' _ _)
  map_add' a b := Subtype.ext (violFlip_add' _ _)

set_option quotPrecheck false in
local notation "C" κ:arg => (isIdempotentElem_violMk_redProj k Q Λ ν κ).Corner
set_option quotPrecheck false in
local notation "B" κ':arg κ:arg => ↥(braidingBimodule k Q Λ ν κ' κ)

private def flipBraid (κ' κ : List (Fin ℓ)) (x : B κ' κ) : B κ κ' :=
  ⟨violFlip x.val, ⟨by
    have h := congrArg violFlip x.property.2
    rwa [violFlip_mul', violFlip_idem] at h, by
    have h := congrArg violFlip x.property.1
    rwa [violFlip_mul', violFlip_idem] at h⟩⟩

/-- Webster, arXiv:1309.3796v2, §6.1, p. 65, proof of Lemma 6.11.
The reflection identifies `B(κ', κ)` with `B(κ, κ')`, replacing the permutation
by its inverse. The two scalar actions are reversed via `cornerFlip`. -/
def braidingBimoduleFlip (κ' κ : List (Fin ℓ)) : B κ' κ ≃+ B κ κ' where
  toFun := flipBraid κ' κ
  invFun := flipBraid κ κ'
  left_inv x := Subtype.ext (violFlip_violFlip x.val)
  right_inv x := Subtype.ext (violFlip_violFlip x.val)
  map_add' x y := Subtype.ext (violFlip_add' x.val y.val)

@[simp]
theorem braidingBimoduleFlip_val (κ' κ : List (Fin ℓ)) (x : B κ' κ) :
    (braidingBimoduleFlip κ' κ x).val = violFlip x.val := rfl

theorem braidingBimoduleFlip_smul_left (κ' κ : List (Fin ℓ)) (a : C κ') (x : B κ' κ) :
    braidingBimoduleFlip κ' κ (a • x) = op (cornerFlip a) • braidingBimoduleFlip κ' κ x :=
  Subtype.ext (violFlip_mul' a.val x.val)

theorem braidingBimoduleFlip_smul_right (κ' κ : List (Fin ℓ))
    (a : (C κ)ᵐᵒᵖ) (x : B κ' κ) :
    braidingBimoduleFlip κ' κ (a • x) = cornerFlip a.unop • braidingBimoduleFlip κ' κ x :=
  Subtype.ext (violFlip_mul' x.val a.unop.val)

end Categorification.Stendhal.BraidedStendhalAlgebra
