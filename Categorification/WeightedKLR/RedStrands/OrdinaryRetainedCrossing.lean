/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HigherKernelCrossingAt
import Categorification.WeightedKLR.RedStrands.BraidedAppendFlip
import Categorification.WeightedKLR.RedStrands.BlackIdempotent

/-!
# Ordinary crossing tests for retained projectives

Webster, arXiv:1309.3796v2, Lemma 5.23 and the proof of Lemma 6.8 at (6.21).
The ordinary crossing test implies injectivity for the actual retained
right-projective crossing map in the canonical red order.
-/


noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)
local notation "V" => ViolQuotient k Q Λ ν
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "E" => violMk k Q Λ ν (redProj k Q Λ ν (List.finRange ℓ))
local notation "p" => fun s => π (KLRAlgebra.e s)

variable {source higher : Seq (stendhalWeight ℓ ν)}
variable (word : redWord source = List.finRange ℓ)
variable (order : redWord higher = redWord source)
variable (j : ℕ) (step : sadj (Multiset.card (stendhalWeight ℓ ν)) j • source = higher)

private def cornerImage (z : R) : (isIdempotentElem_violRedProj k Q Λ ν).Corner :=
  violCornerHom k Q Λ ν (cornerMk (ofKLR k Q Λ ν z))

include word order in
private theorem cornerImage_idem :
    (cornerImage Q Λ (KLRAlgebra.e higher)).1 = p higher := by
  rw [cornerImage, violCornerHom_val, cornerMk_e_val (order.trans word)]
  rfl

include word order step in
private theorem cornerImage_cross :
    (cornerImage Q Λ (ψ j * KLRAlgebra.e source)).1 = π (ψ j * KLRAlgebra.e source) := by
  let eR := redProj k Q Λ ν (List.finRange ℓ)
  let c := ofKLR k Q Λ ν (ψ j * KLRAlgebra.e source)
  have hc : (ψ j * KLRAlgebra.e source : R) = KLRAlgebra.e higher * ψ j := by
    rw [e_mul_ψ, ← step, ← mul_smul, TypeA.sadj_mul_self, one_smul]
  have hleft : eR * c = c := by
    dsimp [eR, c]
    rw [hc, map_mul, redProj_mul_e_of_eq (order.trans word)]
  have hright : c * eR = c := by
    dsimp [eR, c]
    rw [map_mul, mul_assoc, e_mul_redProj, ite_eq_left word]
  change violMk k Q Λ ν (eR * c * eR) = _
  rw [hleft, hright]
  rfl

private theorem flipMul (x y : V) : violFlip (x * y) = violFlip y * violFlip x :=
  congrArg MulOpposite.unop (map_mul (violFlipHom k Q Λ ν) x y)

private theorem flipE : violFlip E = E := by
  rw [violFlip_violMk, flip_redProj]

private theorem flipHigh : violFlip (p higher) = p higher := by
  change violFlip (violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e higher))) = _
  rw [violFlip_violMk, flip_ofKLR, hflip_e]
  rfl

include step in
private theorem flipCross :
    violFlip (π (ψ j * KLRAlgebra.e higher)) = π (ψ j * KLRAlgebra.e source) := by
  change violFlip (violMk k Q Λ ν (ofKLR k Q Λ ν (ψ j * KLRAlgebra.e higher))) = _
  rw [violFlip_violMk, flip_ofKLR, hflip_mul, hflip_e, hflip_ψ, e_mul_ψ,
    ← step, ← mul_smul, TypeA.sadj_mul_self, one_smul]
  rfl

private theorem ordinaryImage (z : R) :
    identityCornerToTensor k Q Λ ν (cornerMk (ofKLR k Q Λ ν z)) = tensorOfKLR Q Λ ν z := by
  apply congrArg (TensorProductAlgebra.mk Q Λ ν)
  apply Subtype.ext
  rw [identityCornerHom_val, cornerMk_val, map_mul, map_mul,
    toAllOrders_ofKLR]
  change toAllOrders k Q Λ ν (ofKLR k Q Λ ν (redIdem k Q Λ (List.finRange ℓ))) *
      StendhalAlgebraAllOrders.ofKLR k Q Λ ν z *
      toAllOrders k Q Λ ν (ofKLR k Q Λ ν (redIdem k Q Λ (List.finRange ℓ))) = _
  rw [toAllOrders_redIdem]
  let eR := StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
  let a := StendhalAlgebraAllOrders.ofKLR k Q Λ ν z
  change eR * a * eR = a * eR
  rw [(redOrderedIdem_commute Q Λ ν a).eq, mul_assoc,
    StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem.eq]

include word step in
/-- A right multiplication test in the ordinary ordered algebra transports, by
the quotient corner equivalence and diagram flip, to the retained right-projective map. -/
theorem crossingIntoKernelMap_injective_of_ordinary_test
    (a b : Fin ℓ) (hlt : adjacentBlockRoot a b source < adjacentBlockRoot a b higher)
    (hQ : KLRSymm Q)
    (h : ∀ x : TensorProductAlgebra k Q Λ ν,
      x * tensorOfKLR Q Λ ν (KLRAlgebra.e higher) = x →
      x * tensorOfKLR Q Λ ν (ψ j * KLRAlgebra.e source) = 0 →
      x = 0) :
    Function.Injective (crossingIntoKernelMap Q Λ a b order hlt j) := by
  have hswap : sadj (Multiset.card (stendhalWeight ℓ ν)) j • higher = source :=
    by rw [← step, sadj_smul_smul]
  let ρ := TypeA.canWord (Multiset.card (stendhalWeight ℓ ν))
  have hρ : IsReducedChoice ρ := fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩
  let q := violCornerEquiv (ν := ν) (Λ := Λ) hρ hQ
  let projective := rIdeal (orderedLoadingIdemAt Q Λ (redWord source) higher order)
  let : AddCommGroup projective := Submodule.addCommGroup projective
  let : AddCommGroup (blockLoadingKernel Q Λ source a b) := blockKernelAddGroup Q Λ source a b
  suffices hz : ∀ y : projective, crossingIntoKernelMap Q Λ a b order hlt j y = 0 → y = 0 by
    intro y z hyz
    have hs : crossingIntoKernelMap Q Λ a b order hlt j (y - z) = 0 := by rw [map_sub, hyz, sub_self]
    exact sub_eq_zero.mp (hz (y - z) hs)
  intro y hy
  have hY : E * y.1.1 = y.1.1 ∧ y.1.1 * E = y.1.1 := by
    have inner := (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν (redWord source))).1 y.1.2
    have hEeq : violMk k Q Λ ν (redProj k Q Λ ν (redWord source)) = E :=
      congrArg (fun order => violMk k Q Λ ν (redProj k Q Λ ν order)) word
    exact ⟨(congrArg (fun z => z * y.1.1) hEeq).symm.trans inner.1,
      (congrArg (fun z => y.1.1 * z) hEeq).symm.trans inner.2⟩
  let fy : (isIdempotentElem_violRedProj k Q Λ ν).Corner := ⟨violFlip y.1.1,
    (Subsemigroup.mem_corner_iff (isIdempotentElem_violRedProj k Q Λ ν)).2
    ⟨by rw [← flipE Q Λ, ← flipMul Q Λ, hY.2],
     by rw [← flipE Q Λ, ← flipMul Q Λ, hY.1]⟩⟩
  have hf : fy * cornerImage Q Λ (KLRAlgebra.e higher) = fy := by
    apply Subtype.ext
    change violFlip y.1.1 * (cornerImage Q Λ (KLRAlgebra.e higher)).1 = violFlip y.1.1
    have hp : p higher * y.1.1 = y.1.1 := congrArg Subtype.val y.2
    rw [cornerImage_idem Q Λ word order, ← flipHigh Q Λ, ← flipMul Q Λ, hp]
  have hh : fy * cornerImage Q Λ (ψ j * KLRAlgebra.e source) = 0 := by
    apply Subtype.ext
    change violFlip y.1.1 * (cornerImage Q Λ (ψ j * KLRAlgebra.e source)).1 = 0
    have hx : π (ψ j * KLRAlgebra.e higher) * y.1.1 = 0 := by
      rw [← crossingIntoKernelMap_val Q Λ a b order hlt j hswap, hy]
      rfl
    rw [cornerImage_cross Q Λ word order j step, ← flipCross Q Λ j step, ← flipMul Q Λ, hx]
    exact congrArg MulOpposite.unop (map_zero (violFlipHom k Q Λ ν))
  have himg (z : R) : q (cornerImage Q Λ z) = tensorOfKLR Q Λ ν z :=
    (violCornerEquiv_violCornerHom hρ hQ (cornerMk (ofKLR k Q Λ ν z))).trans (ordinaryImage Q Λ z)
  have hq : q fy = 0 := h (q fy) (by rw [← himg, ← map_mul q, hf])
    (by rw [← himg, ← map_mul q, hh, map_zero])
  have hfy : fy = 0 := q.injective (hq.trans (map_zero q).symm)
  apply Subtype.ext; apply Subtype.ext
  have hhf : violFlip y.1.1 = 0 := congrArg Subtype.val hfy
  exact (violFlip_violFlip y.1.1).symm.trans (by
    rw [hhf]
    exact congrArg MulOpposite.unop (map_zero (violFlipHom k Q Λ ν)))

end Categorification.Stendhal.BraidedStendhalAlgebra
