/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicTensorOne

/-!
# Left colour cuts of the cyclotomic induction tensors

The middle row of Kang–Kashiwara, arXiv:1102.4677v4, §5.2 uses `E_i K₀`
and `E_i K₁`, not the uncut induction modules. Restricting the multiplication
comparisons to the left idempotent gives their two-sided corner presentations.
The tensor objects exist also at `β = 0`; the quotient comparisons below retain
the positive-rank hypothesis required by the quotient presentations.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open scoped TensorProduct

private def cutEquiv {k A M N : Type*} [CommRing k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    (e : A) (f : M ≃ₗ[A] N) :
    Graded.idemSubspace k M e ≃ₗ[k] Graded.idemSubspace k N e where
  toFun m := ⟨f m, by
    change e • f m = f m
    rw [← map_smul, m.2]⟩
  invFun n := ⟨f.symm n, by
    change e • f.symm n = f.symm n
    rw [← map_smul, n.2]⟩
  left_inv m := Subtype.ext (f.symm_apply_apply m)
  right_inv n := Subtype.ext (f.apply_symm_apply n)
  map_add' m n := Subtype.ext (map_add f (m : M) (n : M))
  map_smul' c m := Subtype.ext (f.map_smul_of_tower c (m : M))

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (β : Multiset I)
  (a : I → Polynomial k)

local notation "Si" => (Singleton.singleton i : Multiset I)

/-- The actual left `e(β,i)` summand of the right-added balanced induction tensor. -/
abbrev EIKZero : Type _ :=
  Graded.idemSubspace k (KZeroTensor Q i β a) (oneConcat Q β Si)

/-- The actual left `e(β,i)` summand of the left-added balanced induction tensor.
`cL 1` is `e(β,i)` transported to the ambient algebra indexed by `{i} + β`. -/
abbrev EIKOne : Type _ :=
  Graded.idemSubspace k (KOneTensor Q i β a) (cL Q i β 1)

/-- The quotient presentation with both colour cuts, for `E_i K₀`. -/
abbrev EIKZeroCorner (h0 : 0 < Multiset.card (β + Si)) : Type _ :=
  Graded.idemSubspace k (KZeroCorner Q i β a h0) (oneConcat Q β Si)

/-- The quotient presentation with both colour cuts, for `E_i K₁`. -/
abbrev EIKOneCorner (h1 : 1 < Multiset.card (Si + β)) : Type _ :=
  Graded.idemSubspace k (KOneCorner Q i β a h1) (cL Q i β 1)

/-- Multiplication identifies the actual left-cut tensor with the two-sided quotient corner. -/
def eiKZeroEquiv (h0 : 0 < Multiset.card (β + Si)) (hβ : 0 < Multiset.card β) :
    EIKZero Q i β a ≃ₗ[k] EIKZeroCorner Q i β a h0 :=
  cutEquiv (oneConcat Q β Si) (kZeroTensorEquiv Q i β a h0 hβ)

/-- The corresponding multiplication comparison for the left-added induction tensor. -/
def eiKOneEquiv (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) :
    EIKOne Q i β a ≃ₗ[k] EIKOneCorner Q i β a h1 :=
  cutEquiv (cL Q i β 1) (kOneTensorEquiv Q i β a h1 hβ)

/-- The cut comparison is the existing multiplication map, without a new coordinate choice. -/
theorem eiKZeroEquiv_val (h0 : 0 < Multiset.card (β + Si)) (hβ : 0 < Multiset.card β)
    (t : EIKZero Q i β a) :
    (((eiKZeroEquiv Q i β a h0 hβ t : EIKZeroCorner Q i β a h0) :
      KZeroCorner Q i β a h0) : KZero Q (β + Si) a h0) =
      tensorToKZero Q i β a h0 hβ t := rfl

/-- The left-added cut comparison is likewise the specified multiplication map. -/
theorem eiKOneEquiv_val (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β)
    (t : EIKOne Q i β a) :
    (((eiKOneEquiv Q i β a h1 hβ t : EIKOneCorner Q i β a h1) :
      KOneCorner Q i β a h1) : KOne Q (Si + β) a h1) =
      tensorToKOne Q i β a h1 hβ t := rfl

end Categorification.KLR.KLRAlgebra
