/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OrderedBlockAction
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-!
# Internal crossing in an ordered coefficient

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
The ordered loading-projective injection transfers to the diagonal part of the local
violated diagram quotient. Over a field its exterior tensor with unchanged coefficients
also detects zero on the corresponding loading support.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra TypeA BraidedStendhalAlgebra
open scoped TensorProduct

section Local

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)

section IdentityCrossingInjection

open KLRAlgebra

variable (B : RedBlock I ℓ) (a : ℕ) (t : Seq B.localWeight)

local notation "W" => Λ ∘ B.label
local notation "W₁" => W ∘ (1 : Equiv.Perm (Fin B.size))
local notation "s" => sadj (Multiset.card B.localWeight) a • t
local notation "T" => TensorProductAlgebra k Q W₁ B.black
local notation "V" => quotientAlgebra Q Λ B
local notation "E" => tensorOfKLR Q W₁ B.black (e s)
local notation "c" => tensorOfKLR Q W₁ B.black (ψ a * e t)
local notation "ι" => orderedValue Q Λ hQ (fun _ => 1) B
local notation "p" => ι 1
local notation "π" => AlgHom.comp (violMk k Q W B.black) (ofKLR k Q W B.black)

/-- The injectivity of the oriented crossing on its ordered loading projective transfers to the
same-order corner of the local violated quotient. -/
theorem eq_zero_of_quotient_mul_identity_ψ
    (ht : redWord t = List.finRange B.size) (hs : redWord s = List.finRange B.size)
    (hinj : ∀ y : T, y * E = y → y * c = 0 → y = 0)
    (x : V) (hleft : p * x = x) (hsource : x * π (e s) = x)
    (hzero : x * π (ψ a * e t) = 0) : x = 0 := by
  have he : ι E = π (e s) := orderedValue_identity_e Q Λ hQ B s hs
  have hc : ι c = π (ψ a * e t) := orderedValue_identity_ψ_mul_e Q Λ hQ B a t ht hs
  have hright : x * p = x := by
    have hp : π (e s) * p = π (e s) := by rw [← he, ← map_mul ι, mul_one]
    calc
      x * p = (x * π (e s)) * p := by rw [hsource]
      _ = x := by rw [mul_assoc, hp, hsource]
  let y := orderedRetraction Q Λ hQ (fun _ => 1) B x
  have hy : ι y = x := by
    change ι (orderedRetraction Q Λ hQ (fun _ => 1) B x) = x
    rw [orderedValue_retraction, hleft, hright]
  have hinv : Function.LeftInverse (orderedRetraction Q Λ hQ (fun _ => 1) B) ι :=
    fun z => orderedRetraction_value Q Λ hQ (fun _ => 1) B z
  have hi : Function.Injective ι := hinv.injective
  have hsupp : y * E = y := hi (by rw [map_mul ι, he, hy, hsource])
  have hkill : y * c = 0 := hi (by rw [map_mul ι, hc, hy, map_zero ι, hzero])
  rw [← hy, hinj y hsupp hkill, map_zero]

end IdentityCrossingInjection

end Local

section TensorSupport

variable {k L A R : Type*} [Field k]
  [Ring L] [Algebra k L] [Ring A] [Algebra k A] [Ring R] [Algebra k R]

/-- Right multiplication on a supported middle coefficient stays injective after adjoining
an exterior tensor factor on each side over a field. -/
private theorem eq_zero_of_mul_right_cut_tensor_middle (l : L) (p e c : A) (r : R)
    (hp : p * p = p) (he : e * e = e) (hc : e * c = c)
    (hinj : ∀ a : A, p * a = a → a * e = a → a * c = 0 → a = 0)
    (x : L ⊗[k] (A ⊗[k] R))
    (hleft : ((1 : L) ⊗ₜ[k] (p ⊗ₜ[k] (1 : R))) * x = x)
    (hx : x * (l ⊗ₜ[k] (e ⊗ₜ[k] r)) = x)
    (h0 : x * (l ⊗ₜ[k] (c ⊗ₜ[k] r)) = 0) : x = 0 := by
  let left := LinearMap.ker (LinearMap.mulLeft k p - LinearMap.id)
  let right := LinearMap.ker (LinearMap.mulRight k e - LinearMap.id)
  let P := left ⊓ right
  have fixL (a : P) : p * a.1 = a.1 := sub_eq_zero.mp (LinearMap.mem_ker.mp a.2.1)
  have fixR (a : P) : a.1 * e = a.1 := sub_eq_zero.mp (LinearMap.mem_ker.mp a.2.2)
  let project : A →ₗ[k] P := ((LinearMap.mulRight k e).comp (LinearMap.mulLeft k p)).codRestrict P
    (fun a => by
      refine ⟨?_, ?_⟩
      · change p * (p * a * e) - p * a * e = 0
        rw [← mul_assoc p, ← mul_assoc p p a, hp, sub_self]
      · change p * a * e * e - p * a * e = 0
        rw [mul_assoc (p * a), he, sub_self])
  let f : P →ₗ[k] A := (LinearMap.mulRight k c).comp P.subtype
  have hf : Function.Injective f := (LinearMap.ker_eq_bot (f := f)).1
    (LinearMap.ker_eq_bot'.2 fun a ha => Subtype.ext (hinj a.1 (fixL a) (fixR a) ha))
  let cut : L ⊗[k] (A ⊗[k] R) →ₗ[k] L ⊗[k] (P ⊗[k] R) :=
    TensorProduct.map LinearMap.id (TensorProduct.map project LinearMap.id)
  have apply_cut (d : A) (g : P →ₗ[k] A) (hg : ∀ a, g (project a) = p * a * d)
      (z : L ⊗[k] (A ⊗[k] R)) :
      TensorProduct.map LinearMap.id (TensorProduct.map g LinearMap.id) (cut z) =
        ((1 : L) ⊗ₜ[k] (p ⊗ₜ[k] (1 : R))) * z * ((1 : L) ⊗ₜ[k] (d ⊗ₜ[k] (1 : R))) := by
    induction z using TensorProduct.inductionOn with
    | add y z hy hz => rw [map_add, map_add, hy, hz, mul_add, add_mul]
    | tmul y z =>
      induction z using TensorProduct.inductionOn with
      | add v w hv hw => rw [TensorProduct.tmul_add, map_add, map_add, hv, hw, mul_add, add_mul]
      | tmul a b =>
        simp only [cut, TensorProduct.map_tmul, LinearMap.id_apply, hg,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have hcentral (d : A) (h : e * d = d) :
      x * ((1 : L) ⊗ₜ[k] (d ⊗ₜ[k] (1 : R))) = x * (l ⊗ₜ[k] (d ⊗ₜ[k] r)) := by
    nth_rewrite 1 [← hx]
    rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, mul_one, h]
  have hcut : cut x = 0 := by
    have hmap : Function.Injective
        (TensorProduct.map (LinearMap.id : L →ₗ[k] L)
          (TensorProduct.map f (LinearMap.id : R →ₗ[k] R))) :=
      TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id
        (TensorProduct.map_injective_of_flat_flat _ _ hf Function.injective_id)
    apply hmap
    rw [map_zero, apply_cut c f (fun a => show p * a * e * c = p * a * c by rw [mul_assoc, hc]),
      hleft, hcentral c hc, h0]
  have hinc := apply_cut e P.subtype (fun _ => rfl) x
  rw [hcut, map_zero, hleft, hcentral e he, hx] at hinc
  exact hinc.symm

/-- Tensoring a corner injection with an unchanged left coefficient preserves injectivity.
The source is fixed by the tensor of the two left and right boundary idempotents. -/
theorem eq_zero_of_mul_right_leftTensor_cut (pL eL : L) (p e c : A)
    (hp : p * p = p) (he : e * e = e) (hc : e * c = c)
    (hinj : ∀ a : A, p * a = a → a * e = a → a * c = 0 → a = 0)
    (x : L ⊗[k] A) (hleft : (pL ⊗ₜ[k] p) * x = x)
    (hsource : x * (eL ⊗ₜ[k] e) = x) (hzero : x * (eL ⊗ₜ[k] c) = 0) : x = 0 := by
  let f := Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[k] L)
    (Algebra.TensorProduct.rid k k A).symm
  have hf (l : L) (a : A) : f (l ⊗ₜ[k] a) = l ⊗ₜ[k] (a ⊗ₜ[k] (1 : k)) := rfl
  have hl : ((1 : L) ⊗ₜ[k] p) * x = x := by
    calc
      _ = ((1 : L) ⊗ₜ[k] p) * ((pL ⊗ₜ[k] p) * x) := by rw [hleft]
      _ = x := by rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp, hleft]
  apply f.injective
  rw [map_zero f]
  refine eq_zero_of_mul_right_cut_tensor_middle eL p e c (1 : k) hp he hc hinj (f x) ?_ ?_ ?_
  · simpa only [map_mul f, hf] using congrArg f hl
  · simpa only [map_mul f, hf] using congrArg f hsource
  · simpa only [map_mul f, map_zero f, hf] using congrArg f hzero

/-- Tensoring a corner injection with an unchanged right coefficient preserves injectivity. -/
theorem eq_zero_of_mul_right_rightTensor_cut (pR eR : R) (p e c : A)
    (hp : p * p = p) (he : e * e = e) (hc : e * c = c)
    (hinj : ∀ a : A, p * a = a → a * e = a → a * c = 0 → a = 0)
    (x : A ⊗[k] R) (hleft : (p ⊗ₜ[k] pR) * x = x)
    (hsource : x * (e ⊗ₜ[k] eR) = x) (hzero : x * (c ⊗ₜ[k] eR) = 0) : x = 0 := by
  let f := Algebra.TensorProduct.comm k A R
  have hf (a : A) (b : R) : f (a ⊗ₜ[k] b) = b ⊗ₜ[k] a := rfl
  apply f.injective
  rw [map_zero f]
  refine eq_zero_of_mul_right_leftTensor_cut pR eR p e c hp he hc hinj (f x) ?_ ?_ ?_
  · simpa only [map_mul f, hf] using congrArg f hleft
  · simpa only [map_mul f, hf] using congrArg f hsource
  · simpa only [map_mul f, map_zero f, hf] using congrArg f hzero

/-- The output of right multiplication is fixed by the target loading projector. -/
theorem mul_right_leftTensor_target_cut (eL : L) (c t : A)
    (heL : eL * eL = eL) (ht : c * t = c) (x : L ⊗[k] A) :
    (x * (eL ⊗ₜ[k] c)) * (eL ⊗ₜ[k] t) = x * (eL ⊗ₜ[k] c) := by
  rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, heL, ht]

/-- The output is fixed by the target loading projector with an unchanged right coefficient. -/
theorem mul_right_rightTensor_target_cut (eR : R) (c t : A)
    (heR : eR * eR = eR) (ht : c * t = c) (x : A ⊗[k] R) :
    (x * (c ⊗ₜ[k] eR)) * (t ⊗ₜ[k] eR) = x * (c ⊗ₜ[k] eR) := by
  rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, heR, ht]

end TensorSupport

section Exterior

variable {I : Type} [DecidableEq I] {k L R : Type*} [Field k]
  [Ring L] [Algebra k L] [Ring R] [Algebra k R] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
  (B : RedBlock I ℓ) (a : ℕ) (t : Seq B.localWeight)

local notation "W" => Λ ∘ B.label
local notation "W₁" => W ∘ (1 : Equiv.Perm (Fin B.size))
local notation "s" => sadj (Multiset.card B.localWeight) a • t
local notation "T" => TensorProductAlgebra k Q W₁ B.black
local notation "V" => quotientAlgebra Q Λ B
local notation "E" => tensorOfKLR Q W₁ B.black (e s)
local notation "c" => tensorOfKLR Q W₁ B.black (ψ a * e t)
local notation "ι" => orderedValue Q Λ hQ (fun _ => 1) B
local notation "p" => ι 1
local notation "π" => AlgHom.comp (violMk k Q W B.black) (ofKLR k Q W B.black)

/-- The same-order corner injection stays injective with exterior coefficient algebras
on each side over a field, with the right loading support imposed on the three factors. -/
theorem eq_zero_of_tensor_mul_identity_ψ
    (ht : redWord t = List.finRange B.size) (hs : redWord s = List.finRange B.size)
    (hinj : ∀ y : T, y * E = y → y * c = 0 → y = 0)
    (l : L) (r : R) (x : L ⊗[k] (V ⊗[k] R))
    (hleft : ((1 : L) ⊗ₜ[k] (p ⊗ₜ[k] (1 : R))) * x = x)
    (hsource : x * (l ⊗ₜ[k] (π (e s) ⊗ₜ[k] r)) = x)
    (hzero : x * (l ⊗ₜ[k] (π (ψ a * e t) ⊗ₜ[k] r)) = 0) : x = 0 := by
  refine eq_zero_of_mul_right_cut_tensor_middle l p (π (e s)) (π (ψ a * e t)) r ?_ ?_ ?_
    (fun y => eq_zero_of_quotient_mul_identity_ψ Q Λ hQ B a t ht hs hinj y) x hleft hsource hzero
  · rw [← map_mul ι, one_mul]
  · rw [← map_mul π, e_mul_self]
  · rw [← map_mul π, ψ_mul_e, ← mul_assoc, e_mul_self]

end Exterior

end Categorification.Stendhal.RedBlock
