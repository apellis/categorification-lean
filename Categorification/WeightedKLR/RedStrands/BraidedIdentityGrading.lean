/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidingAuxiliaryDerived
import Categorification.WeightedKLR.RedStrands.BraidedViolatedIdentity
import Categorification.WeightedKLR.RedStrands.StendhalTensorGrading

/-!
# Graded transport from the identity braid corner

Webster, arXiv:1309.3796v2, Lemma 6.5 and Definition 6.6. The identity-order
ring in the graded braid functor identifies with the tensor product algebra.
The equivalence takes each restricted auxiliary grade onto the corresponding
tensor algebra grade.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR TypeA Equiv CornerEndomorphism
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "ord" => List.finRange ℓ
local notation "P" => redProj k Q Λ ν ord
local notation "p" => violMk k Q Λ ν P
local notation "E" => StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
local notation "D" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) ord
local notation "π" => ofKLR k Q Λ ν
local notation "q" => violMk k Q Λ ν

/-- Project an arbitrary affine diagram into the identity braided corner. -/
abbrev affineDiagramInIdentityCorner (a : KLRAlgebra k (stendhalQ Q Λ) μ) : D :=
  violCornerHom k Q Λ ν (cornerMk (π a))

variable {ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q)
local notation "φ" => @violCornerEquiv I _ k _ ℓ Q Λ ν ρ hρ hQ
local notation "diag" => affineDiagramInIdentityCorner (Q := Q) (Λ := Λ) (ν := ν)

include hρ hQ in
/-- Sandwiching an affine diagram by the identity red-order projector and
applying the diagonal equivalence gives its ordinary tensor-algebra projection. -/
theorem violCornerEquiv_diagonal (a : KLRAlgebra k (stendhalQ Q Λ) μ) :
    φ (diag a) = stendhalTensorProjection (Q := Q) Λ ν a := by
  refine (violCornerEquiv_violCornerHom (Λ := Λ) hρ hQ (cornerMk (π a))).trans ?_
  apply congrArg (TensorProductAlgebra.mk Q Λ ν)
  apply Subtype.ext
  rw [identityCornerHom_val, cornerMk_val, map_mul, map_mul, toAllOrders_ofKLR]
  change _ = StendhalAlgebraAllOrders.ofKLR k Q Λ ν a * E
  have hp : toAllOrders k Q Λ ν P = E := toAllOrders_redIdem
  rw [hp, (redOrderedIdem_commute Q Λ ν _).eq, mul_assoc,
    (StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).eq]

private theorem diagonal_val (a : KLRAlgebra k (stendhalQ Q Λ) μ) :
    (diag a).val = p * q (π a) * p := by
  change q (P * π a * P) = _
  rw [map_mul, map_mul]

variable (G : GradingDatum (stendhalQ Q Λ))
local notation "V" => violAuxiliaryGrade (ν := ν) G

include hρ hQ in
/-- The identity braid equivalence preserves and reflects every component
of the augmented KLR grading. -/
theorem violCornerEquiv_mem_tensorProductGrade_iff {d : ℤ} (x : D) :
    φ x ∈ tensorProductGrade G ν d ↔ x.val ∈ V d := by
  constructor
  · intro hx
    obtain ⟨a, ha, he⟩ := stendhalTensorProjection_grade_lift Λ G ν hx
    have heq : diag a = x :=
      (φ).injective ((violCornerEquiv_diagonal hρ hQ a).trans he)
    have hp : p ∈ V 0 := redProj_mem_violAuxiliaryGrade G ord
    have hqa : q (π a) ∈ V d := Graded.mem_map_of_mem _ (q).toLinearMap
      (Graded.mem_map_of_mem _ (π).toLinearMap ha)
    rw [← heq, diagonal_val]
    simpa only [zero_add, add_zero] using
      SetLike.mul_mem_graded (A := V) (SetLike.mul_mem_graded (A := V) hp hqa) hp
  · intro hx
    obtain ⟨b, hb, hee⟩ := Submodule.mem_map.mp hx
    obtain ⟨a, ha, hab⟩ := Submodule.mem_map.mp hb
    have he : q (π a) = x.val := (congrArg q hab).trans hee
    have heq : diag a = x := by
      apply Subtype.ext
      rw [diagonal_val, he, corner_mul_left (isIdempotentElem_violRedProj k Q Λ ν) x,
        corner_mul_right (isIdempotentElem_violRedProj k Q Λ ν) x]
    rw [← heq, violCornerEquiv_diagonal]
    exact stendhalTensorProjection_mem_grade Λ G ν ha

end Categorification.Stendhal.BraidedStendhalAlgebra
