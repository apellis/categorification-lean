/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OrderProjection
import Categorification.KLR.Symmetries

/-!
# The top–bottom flip of `T̃^λ`

Webster, arXiv:1309.3796v3, §4: reflecting Stendhal diagrams top to bottom fixes the idempotents,
the dots and the crossings and reverses products. The relations of Definition 4.5 are stable
under it (a red dot below an idempotent becomes the same red dot above it, and likewise for a
crossing of two red strands), so it is an anti-automorphism of the algebra of Stendhal diagrams
with red strands in all orders (`StendhalAlgebraAllOrders.flip`). It fixes the central
idempotent of the red-ordered loadings, so it restricts to an anti-automorphism of the corner
`T̃^λ` (`StendhalAlgebra.flip`, `StendhalAlgebra.flipEquiv`). On diagrams it is the flip
`KLRAlgebra.hflip` of the KLR algebra (`StendhalAlgebra.flip_topMap`).

No hypothesis on `Q` or the ground ring is needed.

## Main definitions

* `StendhalAlgebraAllOrders.flip`: the flip of Stendhal diagrams with red strands in all orders.
* `StendhalAlgebra.flip`, `StendhalAlgebra.flipEquiv`: the flip of `T̃^λ`, as a map and as an
  algebra isomorphism `T̃^λ ≃ (T̃^λ)ᵐᵒᵖ`.

## Main results

* `StendhalAlgebra.flip_mul`, `StendhalAlgebra.flip_flip`, `StendhalAlgebra.flip_e`,
  `StendhalAlgebra.flip_topMap`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR TypeA MulOpposite StendhalAlgebraAllOrders

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "A" => StendhalAlgebraAllOrders k Q Λ ν
local notation "π" => ofKLR k Q Λ ν
local notation "K" => KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

namespace StendhalAlgebraAllOrders

variable (k Q Λ ν) in
/-- The flip of the KLR algebra of `stendhalQ Q Λ`, followed by the quotient map. -/
def flipKLRHom : K →ₐ[k] Aᵐᵒᵖ :=
  (π).op.comp (KLRAlgebra.flipH k (stendhalQ Q Λ) (stendhalWeight ℓ ν)).toAlgHom

variable (k Q Λ ν) in
/-- The top–bottom flip of Stendhal diagrams, as a homomorphism to the opposite algebra. -/
def flipHom : A →ₐ[k] Aᵐᵒᵖ :=
  RingQuot.liftAlgHom k ⟨(flipKLRHom k Q Λ ν).comp (KLRAlgebra.mk k (stendhalQ Q Λ) μ),
    fun _ _ h => by
    cases h with
    | klr h => exact congrArg (flipKLRHom k Q Λ ν) (RingQuot.mkAlgHom_rel k h)
    | red_dot a s ha =>
      simp only [AlgHom.comp_apply, map_mul (KLRAlgebra.mk k (stendhalQ Q Λ) μ), map_zero]
      change op (π (KLRAlgebra.hflip (KLRAlgebra.x a * KLRAlgebra.e s))) = 0
      rw [KLRAlgebra.hflip_mul, KLRAlgebra.hflip_x, KLRAlgebra.hflip_e,
        KLRAlgebra.e_mul_x, map_mul]
      exact congrArg op (x_mul_e_of_red a s ha)
    | red_cross j hj s ha hb =>
      simp only [AlgHom.comp_apply, map_mul (KLRAlgebra.mk k (stendhalQ Q Λ) μ), map_zero]
      change op (π (KLRAlgebra.hflip (KLRAlgebra.ψ j * KLRAlgebra.e s))) = 0
      rw [KLRAlgebra.hflip_mul, KLRAlgebra.hflip_ψ, KLRAlgebra.hflip_e,
        KLRAlgebra.e_mul_ψ, map_mul]
      apply congrArg op
      exact ψ_mul_e_of_red j hj _ (by rwa [KLRAlgebra.lbl_sadj_left hj])
        (by rwa [KLRAlgebra.lbl_sadj_right hj])⟩

/-- **The top–bottom flip** of Stendhal diagrams with red strands in all orders. -/
def flip (z : A) : A := (flipHom k Q Λ ν z).unop

theorem flip_ofKLR (z : K) : flip (π z) = π (KLRAlgebra.hflip z) := by
  obtain ⟨f, rfl⟩ := KLRAlgebra.mk_surjective z
  rw [ofKLR_mk]
  exact congrArg unop (show flipHom k Q Λ ν (RingQuot.mkAlgHom k (Rel k Q Λ ν) f) =
    flipKLRHom k Q Λ ν (KLRAlgebra.mk k (stendhalQ Q Λ) μ f) from
      RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _)

theorem flip_flip (z : A) : flip (flip z) = z := by
  obtain ⟨a, rfl⟩ := ofKLR_surjective z
  rw [flip_ofKLR, flip_ofKLR, KLRAlgebra.hflip_hflip]

theorem flip_mul (y z : A) : flip (y * z) = flip z * flip y := by
  change (flipHom k Q Λ ν (y * z)).unop = _
  rw [map_mul, unop_mul]
  rfl

theorem flip_add (y z : A) : flip (y + z) = flip y + flip z := by
  change (flipHom k Q Λ ν (y + z)).unop = _
  rw [map_add, unop_add]
  rfl

theorem flip_smul (c : k) (z : A) : flip (c • z) = c • flip z := by
  change (flipHom k Q Λ ν (c • z)).unop = _
  rw [map_smul, unop_smul]
  rfl

theorem flip_e (s : Seq μ) : flip (e s : A) = e s := by
  rw [e, flip_ofKLR, KLRAlgebra.hflip_e]

theorem flip_redOrderedIdem : flip (redOrderedIdem k Q Λ ν) = redOrderedIdem k Q Λ ν := by
  classical
  have h : ∀ S : Finset (Seq μ), flip (∑ s ∈ S, (e s : A)) = ∑ s ∈ S, (e s : A) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      change (flipHom k Q Λ ν 0).unop = 0
      rw [map_zero, unop_zero]
    | insert a S ha ih => rw [Finset.sum_insert ha, flip_add, ih, flip_e]
  rw [redOrderedIdem]
  convert h _

end StendhalAlgebraAllOrders

namespace StendhalAlgebra

local notation "T" => StendhalAlgebra k Q Λ ν
local notation "E" => redOrderedIdem k Q Λ ν

/-- **The top–bottom flip of `T̃^λ`**: the flip of Stendhal diagrams restricted to the corner of
the red-ordered loadings. -/
def flip (z : T) : T :=
  ⟨StendhalAlgebraAllOrders.flip z.1,
    (Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem).2
      ⟨by
        have h := congrArg StendhalAlgebraAllOrders.flip
          ((Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem).1 z.2).2
        rwa [StendhalAlgebraAllOrders.flip_mul, flip_redOrderedIdem] at h, by
        have h := congrArg StendhalAlgebraAllOrders.flip
          ((Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem).1 z.2).1
        rwa [StendhalAlgebraAllOrders.flip_mul, flip_redOrderedIdem] at h⟩⟩

theorem flip_val (z : T) : (flip z).1 = StendhalAlgebraAllOrders.flip z.1 := rfl

theorem flip_flip (z : T) : flip (flip z) = z :=
  Subtype.ext (StendhalAlgebraAllOrders.flip_flip z.1)

theorem flip_mul (y z : T) : flip (y * z) = flip z * flip y :=
  Subtype.ext (StendhalAlgebraAllOrders.flip_mul y.1 z.1)

theorem flip_add (y z : T) : flip (y + z) = flip y + flip z :=
  Subtype.ext (StendhalAlgebraAllOrders.flip_add y.1 z.1)

theorem flip_smul (c : k) (z : T) : flip (c • z) = c • flip z :=
  Subtype.ext (StendhalAlgebraAllOrders.flip_smul c z.1)

theorem flip_one : flip (1 : T) = 1 :=
  Subtype.ext flip_redOrderedIdem

theorem flip_zero : flip (0 : T) = 0 := by
  have h := flip_add (0 : T) 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

theorem flip_injective : Function.Injective (flip : T → T) :=
  Function.LeftInverse.injective flip_flip

theorem flip_e (s : Seq μ) (hs : IsRedOrdered s) : flip (e s hs : T) = e s hs := by
  apply Subtype.ext
  change StendhalAlgebraAllOrders.flip (StendhalAlgebraAllOrders.e s) = _
  rw [StendhalAlgebraAllOrders.flip_e]
  rfl

/-- On the image of a KLR diagram, the flip of `T̃^λ` is the image of the flipped diagram. -/
theorem flip_orderProjection (z : A) :
    flip (orderProjection Q Λ ν z) = orderProjection Q Λ ν (StendhalAlgebraAllOrders.flip z) := by
  apply Subtype.ext
  change StendhalAlgebraAllOrders.flip (z * E) = StendhalAlgebraAllOrders.flip z * E
  rw [StendhalAlgebraAllOrders.flip_mul, flip_redOrderedIdem,
    (redOrderedIdem_commute Q Λ ν _).eq]

/-- **The flip on diagrams**: the flip of the image of a KLR diagram `a` is the image of
`hflip a`. -/
theorem flip_topMap (a : K) :
    flip (orderProjection Q Λ ν (π a)) = orderProjection Q Λ ν (π (KLRAlgebra.hflip a)) := by
  rw [flip_orderProjection, StendhalAlgebraAllOrders.flip_ofKLR]

variable (k Q Λ ν) in
/-- **The flip of `T̃^λ` as an algebra isomorphism** `T̃^λ ≃ (T̃^λ)ᵐᵒᵖ`. -/
def flipEquiv : T ≃ₐ[k] Tᵐᵒᵖ where
  toFun z := op (flip z)
  invFun z := flip z.unop
  left_inv z := flip_flip z
  right_inv z := by
    change op (flip (flip z.unop)) = z
    rw [flip_flip]
    rfl
  map_mul' y z := by
    change op (flip (y * z)) = op (flip y) * op (flip z)
    rw [flip_mul, op_mul]
  map_add' y z := by
    change op (flip (y + z)) = op (flip y) + op (flip z)
    rw [flip_add, op_add]
  commutes' c := by
    change op (flip (algebraMap k T c)) = op (algebraMap k T c)
    rw [Algebra.algebraMap_eq_smul_one, flip_smul, flip_one]

theorem flipEquiv_apply (z : T) : flipEquiv k Q Λ ν z = op (flip z) := rfl

end StendhalAlgebra

end Categorification.Stendhal
